package test;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.ArrayList;

import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.Node;
import eu.trowl.owlapi3.rel.reasoner.dl.RELReasoner;
import eu.trowl.owlapi3.rel.reasoner.dl.RELReasonerFactory;

public class TestRecall {

	static ArrayList<String> correctOne = new ArrayList<String>();

	public static void trowlTest(String filename) throws Exception {
		File file = new File(filename);
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		OWLOntology ontology = manager.loadOntologyFromOntologyDocument(file);

		RELReasonerFactory relfactory = new RELReasonerFactory();
		RELReasoner reasoner = relfactory.createReasoner(ontology);
		int counter = 0;
		for (OWLClass c : ontology.getClassesInSignature()) {
			for (Node<OWLNamedIndividual> i : reasoner.getIndividuals(c)) {
				for (OWLNamedIndividual ii : i) {
					String individual = "individual_"
							+ ii.getIRI().getFragment();
					String concept = "class_" + c.getIRI().getFragment();
					// System.out.println("('" + individual + "', '" + concept+
					// "')");
					counter++;
				}
			}
		}
		System.out.println(counter);

	}

	public static void hermitTest(String filename) throws Exception {
		// File file = new File("TEST_ONTOLOGIES/00001.owl");
		File file = new File(filename);
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		OWLOntology o = manager.loadOntologyFromOntologyDocument(file);

		Reasoner hermit = new Reasoner(o);
		for (OWLClass c : o.getClassesInSignature()) {
			for (Node<OWLNamedIndividual> i : hermit.getInstances(c, false)) {
				for (OWLNamedIndividual ii : i) {
					String individual = "individual_"
							+ ii.getIRI().getFragment();
					// if(c.isOWLThing()) continue;
					String concept = "class_" + c.getIRI().getFragment();
					// System.out.println("('" + individual + "', '" + concept +
					// "')");
					correctOne.add("('" + individual + "', '" + concept + "')");
				}
			}
		}

		File file2 = new File("output.txt");
		BufferedReader br = new BufferedReader(new FileReader(file2));
		String line = "";
		int sum = 0;
		while ((line = br.readLine()) != null) {
			if (correctOne.contains(line)) {
				// System.out.println(line);
				sum++;
			}
		}
		System.out.println(sum + "," + correctOne.size());

		System.out.println(correctOne.size());

	}

	public static int approxSubsumption() throws Exception {
		File file2 = new File("output.txt");
		BufferedReader br = new BufferedReader(new FileReader(file2));
		String line = "";
		int sum = 0;
		while ((line = br.readLine()) != null) {
			if (line.contains("test_individual_") && line.contains("class")) {
				System.out.println(line);
				sum++;
			}
		}

		return sum;
	}

	public static int hermitSubsumption() throws Exception {
		File file = new File("TEST_ONTOLOGIES/00103.owl");
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		OWLOntology o = manager.loadOntologyFromOntologyDocument(file);
		int test =  1;

		Reasoner hermit = new Reasoner(o);
		long duration = -System.currentTimeMillis();
		for (OWLClass c : o.getClassesInSignature()) {
			for (Node<OWLClass> i : hermit.getSuperClasses(c, false)) {
				for (OWLClass ii : i) {
					correctOne.add("('" + c + "', '" + ii + "')");
				}
			}
		}

		duration += System.currentTimeMillis();
		
		System.out.println("Duration:"+duration);
		return correctOne.size();

	}

	private static String getIRIName(OWLClass c) {
		// TODO Auto-generated method stub
		return null;
	}

	public static void main(String[] args) throws Exception {
		System.out.println(approxSubsumption());
		System.out.println(hermitSubsumption());
		hermitTest("TEST_ONTOLOGIES/00103.owl");
	}
}
