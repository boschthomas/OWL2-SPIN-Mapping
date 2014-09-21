package RDFValidation;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.apache.commons.io.IOUtils;
import org.topbraid.spin.constraints.ConstraintViolation;
import org.topbraid.spin.constraints.SPINConstraints;
import org.topbraid.spin.constraints.SimplePropertyPath;
import org.topbraid.spin.inference.SPINInferences;
import org.topbraid.spin.model.TemplateCall;
import org.topbraid.spin.system.SPINLabels;
import org.topbraid.spin.system.SPINModuleRegistry;
import org.topbraid.spin.util.JenaUtil;

import com.hp.hpl.jena.ontology.OntModel;
import com.hp.hpl.jena.ontology.OntModelSpec;
import com.hp.hpl.jena.rdf.model.Model;
import com.hp.hpl.jena.rdf.model.ModelFactory;
import com.hp.hpl.jena.rdf.model.Statement;
import com.hp.hpl.jena.rdf.model.StmtIterator;

/**
 * 
 * @author Thomas Bosch
 *
 */
public class Spin 
{
	// SPIN mappings
	private Set<String> spinMappings = null;
	
	// validation results
	public StringBuilder validationResults = null;
	
	// constraint violation list
	private List<RDFValidation.ConstraintViolation> constraintViolationList = null;
	private RDFValidation.ConstraintViolation constraintViolation = null;
	private List<String> constraintViolationPaths = null;
	private List<String> constraintViolationFixes = null;
	
	// inferred triples
//	public PrintWriter writerInferredTriples = null;
	private String rdfGraphInferred = null;
	
	// locally stored SPIN-related templates and functions
	private OntModel ontModel_TemplatesFunctions = null;
	
	// debugging
	public String debugging = null; 
	
	// SPIN exception
	private SPINException spinException  = null;
	
	/**
	 * 
	 */
	public Spin( String... spinMappings )
	{
		// initialization
		init( spinMappings );
	}
	
	/**
	 * initialization
	 */
	private void init( String... spinMappings )
	{
		// SPIN mappings
		this.spinMappings = new HashSet<String>();
		for ( String spinMapping : spinMappings ) 
		{
		    this.spinMappings.add( spinMapping );
		}
		
		// validation results
		validationResults = new StringBuilder();
		
		// constraint violation list
		constraintViolationList = new ArrayList<RDFValidation.ConstraintViolation>();
        
		// initialize SPIN system functions ( such as sp:gt (>) ) and templates
		SPINModuleRegistry.get().init();
		
		// locally stored SPIN-related templates and functions
		Model graph_TemplatesFunctions = getRDFGraph( "SPIN/functions/functions.ttl", "TTL" ); 
		graph_TemplatesFunctions.add( getRDFGraph( "SPIN/functions/dsp-functions.ttl", "TTL" ) );
		ontModel_TemplatesFunctions = JenaUtil.createOntologyModel( OntModelSpec.OWL_MEM, graph_TemplatesFunctions );			
	}
	
	/**
	 * run inferences and check constraints
	 */
	public void runInferences_checkConstraints( String rdfGraph )
	{
		// fill RDF graph ( namespace declarations, constraints, data, inference rules )
		Model graph = getRDFGraphByString( rdfGraph, "TTL" );
		
//		debugging = "<ul>";
//		
//		debugging = debugging + "<li>";
//		debugging = debugging + "graph size (input): " + graph.size();
//		debugging = debugging + "</li>";
		
		// fill RDF graph ( SPIN mappings )
		for ( String spinMapping : spinMappings ) 
		{
			graph.add( getRDFGraph( "/SPIN/SPIN-mappings/" + spinMapping, "TTL" ) );
		}
		
//		debugging = debugging + "<li>";
//		debugging = debugging + "graph size (SPIN mapping): " + graph.size();
//		debugging = debugging + "</li>";
		
		// create OntModel with imports
		OntModel ontModel = JenaUtil.createOntologyModel( OntModelSpec.OWL_MEM, graph );
		
		// create and add model for inferred triples
		Model newTriples = ModelFactory.createDefaultModel();
		ontModel.addSubModel( newTriples );
		
		// add locally stored SPIN-related templates and functions to model
		ontModel.add( ontModel_TemplatesFunctions );
		
//		debugging = debugging + "<li>";
//		debugging = debugging + "graph size (templates and functions): " + ontModel.size();
//		debugging = debugging + "</li>";
		
		// register locally stored SPIN-related templates and functions
		SPINModuleRegistry.get().registerAll( ontModel, null );
		
		// run all inferences and populated RDF graph containing inferred triples
		try
		{
			SPINInferences.run( ontModel, newTriples, null, null, false, null );
		}
		catch ( Exception e ) 
		{ 
			e.printStackTrace(); 
			
			// create SPIN exception
			spinException = new SPINException();
			spinException.setSource( "SPIN inferencing" );
			spinException.setMessage( e.getMessage().replace( "<", "&lt;" ).replace( ">", "&gt;" ) );
			
			System.out.println( "-----" ); 
			System.out.println( "source: " + "SPIN inferencing" ); 
			System.out.println( "message: " + e.getMessage() ); 
			System.out.println( "-----" ); 
		}
//        try 
//		{
//			writerInferredTriples = new PrintWriter( "UTF-8" );
//		} 
//		catch ( FileNotFoundException e ) { e.printStackTrace(); }
//		newTriples.write( writerInferredTriples, "TTL" );
//		newTriples.write( System.out );
//		System.out.println( writerInferredTriples );
//		System.out.println( "Inferred triples: " + newTriples.size() );
//		newTriples.write( System.out, "TTL" );
//		System.out.println( "-----" );
//		System.out.println( newTriples.toString() );
//		System.out.println( "-----" );
//		System.out.println( writerInferredTriples );
		StringWriter stringWriter = new StringWriter();
		newTriples.write( stringWriter, "TTL" );
		rdfGraphInferred = stringWriter.toString();
		
//		// inferred statements
//		StmtIterator stmtIterator = newTriples.listStatements();
//		while( stmtIterator.hasNext() ) 
//		{
//			Statement statement = stmtIterator.next();
//	        System.out.println( statement );
//	    }
		
//		debugging = rdfGraph;
//		debugging = debugging + "-----" + rdfGraph;
//		debugging = debugging + "-----" + "ontModel (size): " + ontModel.size();
		
//		debugging = debugging + "</ul>";
		
		// check constraints
		try
		{
			List<ConstraintViolation> constraintViolations = SPINConstraints.check( ontModel, null );
		
			// constraint violations
			validationResults.append( "Constraint violations" );
			validationResults.append( "<br/>" );
			validationResults.append( "---------------------" );
			validationResults.append( System.getProperty("line.separator") );
			validationResults.append( System.getProperty("line.separator") );
			for( ConstraintViolation cv : constraintViolations ) 
			{
				constraintViolation = new RDFValidation.ConstraintViolation();
//				constraintViolation.setRoot( SPINLabels.get().getLabel( cv.getRoot() ) );
				constraintViolation.setRoot( cv.getRoot().getURI() );
				constraintViolation.setMessage( cv.getMessage() );
				constraintViolation.setSource( SPINLabels.get().getLabel( cv.getSource() ) );
				
				validationResults.append( " - source: " ).append( SPINLabels.get().getLabel( cv.getSource() ) );
				validationResults.append( System.getProperty("line.separator") );
				validationResults.append( " - root: " ).append( SPINLabels.get().getLabel( cv.getRoot() ) );
				validationResults.append( System.getProperty("line.separator") );
				validationResults.append( " - message: " ).append( cv.getMessage() );
				validationResults.append( System.getProperty("line.separator") );
				
				constraintViolationPaths = new ArrayList<String>();
	//			for ( int i = 0; i <= 5; i++ )
	//			{
	//				constraintViolationPaths.add( String.valueOf( i ) );
	//			}
				if( cv.getPaths().size() == 0 )
				{
					constraintViolationPaths.add( "" );
				}
				for ( SimplePropertyPath violationPath : cv.getPaths() ) 
				{
					constraintViolationPaths.add( violationPath.getPredicate().toString() );
					
					validationResults.append( " - path: " ).append( violationPath.toString() );
					validationResults.append( System.getProperty("line.separator") );
			    }
				constraintViolation.setPaths( constraintViolationPaths );
				
				constraintViolationFixes = new ArrayList<String>();
	//			for ( int i = 0; i <= 5; i++ )
	//			{
	//				constraintViolationFixes.add( String.valueOf( i ) );
	//			}
				if( cv.getFixes().size() == 0 )
				{
					constraintViolationFixes.add( "" );
				}
				for ( TemplateCall violationFix : cv.getFixes() ) 
				{
					constraintViolationFixes.add( violationFix.toString() );
			    }
				constraintViolation.setFixes( constraintViolationFixes );
				
				validationResults.append( " - # fixes: " ).append( cv.getFixes().size() );
		        validationResults.append( System.getProperty("line.separator") );
		        validationResults.append( System.getProperty("line.separator") );
		        
		        constraintViolationList.add( constraintViolation );
			}
			
			validationResults.append( "violation root | violation message | # violation path | # violation fixes" );
			validationResults.append( System.getProperty("line.separator") );
			validationResults.append( "-------------------------------------------------------------------------" );
			validationResults.append( System.getProperty("line.separator") );
			validationResults.append( System.getProperty("line.separator") );
			for( ConstraintViolation cv : constraintViolations ) 
			{
				validationResults.append( SPINLabels.get().getLabel( cv.getRoot() ) ).append( " | " );
				validationResults.append( cv.getMessage() ).append( " | " );
				for ( SimplePropertyPath violationPath : cv.getPaths() ) 
				{
					validationResults.append( violationPath.toString() ).append( " | " );
			    }
				validationResults.append( cv.getFixes().size() );
		        validationResults.append( System.getProperty("line.separator") );
			}
		}
		catch ( Exception e ) 
		{ 
			e.printStackTrace(); 
			
			// create SPIN exception
			spinException = new SPINException();
			spinException.setSource( "SPIN constraint checking" );
			spinException.setMessage( e.getMessage().replace( "<", "&lt;" ).replace( ">", "&gt;" ) );
			
			System.out.println( "-----" ); 
			System.out.println( "source: " + "SPIN constraint checking" ); 
			System.out.println( "message: " + e.getMessage() ); 
			System.out.println( "-----" ); 
		}
	}

	/**
	 * get RDF graph
	 * 
	 * @param rdfGraph_RelativePathAndFileName
	 * @param rdfGraph_ConcreteSyntax
	 */
	public Model getRDFGraph( String rdfGraph_RelativePathAndFileName, String rdfGraph_ConcreteSyntax )
	{
		Model model = ModelFactory.createDefaultModel();
		
		try
		{
			model.read( this.getClass().getClassLoader().getResourceAsStream( "/" + rdfGraph_RelativePathAndFileName ), null, rdfGraph_ConcreteSyntax );
		}
		catch ( Exception e ) 
		{ 
			e.printStackTrace(); 
			
			// create SPIN exception
			spinException = new SPINException();
			spinException.setSource( rdfGraph_RelativePathAndFileName );
			spinException.setMessage( e.getMessage().replace( "<", "&lt;" ).replace( ">", "&gt;" ) );
			
			System.out.println( "-----" ); 
			System.out.println( "source: " + rdfGraph_RelativePathAndFileName ); 
			System.out.println( "message: " + e.getMessage() ); 
			System.out.println( "-----" ); 
		}
		
//		System.out.println(this.getClass().getClassLoader().getResourceAsStream( "/" + rdfGraph_RelativePathAndFileName ));

		return model;
	}
	
	/**
	 * get RDF graph ( by string )
	 * 
	 */
	public Model getRDFGraphByString( String rdfGraph, String rdfGraph_ConcreteSyntax )
	{
		Model model = ModelFactory.createDefaultModel();
		
		try 
		{
			model.read( IOUtils.toInputStream( rdfGraph, "UTF-8" ), null, rdfGraph_ConcreteSyntax );
		} 
		catch ( Exception e ) 
		{ 
			e.printStackTrace(); 
			
			// create SPIN exception
			spinException = new SPINException();
			spinException.setSource( "input RDF graph" );
			spinException.setMessage( e.getMessage().replace( "<", "&lt;" ).replace( ">", "&gt;" ) );
			
			System.out.println( "-----" ); 
			System.out.println( "source: input RDF graph" ); 
			System.out.println( "message: " + e.getMessage() ); 
			System.out.println( "-----" );  
		}
		
		return model;
	}
	
	public List<RDFValidation.ConstraintViolation> getConstraintViolationList() 
	{
		return constraintViolationList;
	}
	
	/**
	 * get RDF graph inferred
	 * 
	 * @return rdfGraphInferred
	 */
	public String getRDFGraphInferred()
	{
		return rdfGraphInferred;
	}
	
	public SPINException getSPINException()
	{
		return spinException;
	}
}
