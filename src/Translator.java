import java.util.*;

import org.semanticweb.owlapi.model.*;

public class Translator {

	protected final OWLAxioms m_axioms;
	protected final OWLDataFactory m_factory;
	protected ArrayList<OWLClassAssertionAxiom> normalized_assertions;

	public Translator(OWLDataFactory factory, OWLAxioms axioms) {
		m_axioms = axioms;
		m_factory = factory;
		normalized_assertions = new ArrayList<OWLClassAssertionAxiom>();

	}

	public void translateKB() {
		TranslateELAxioms();
		TranslateABox();
		TranslateRBox();
		TranslateSignature();
	}

	public void TranslateELAxioms() {
		ArrayList<OWLClassExpression[]> inclusions = m_axioms.m_conceptInclusions_approximated;
		//ArrayList<OWLClassExpression[]> inclusions = m_axioms.m_conceptInclusions_normalized;
		for (int i = 0; i < inclusions.size(); i++) {
			OWLClassExpression[] current = inclusions.get(i);
			if (current.length == 2) {
				if (current[0] == null || current[1] == null)
					continue;
				if (current[0] instanceof OWLClass
						&& current[1] instanceof OWLClass)
					rewriteType1(current[0], current[1]);
				if (current[0] instanceof OWLObjectIntersectionOf
						&& current[1] instanceof OWLClass) {
					rewriteType2(current[0], current[1]);
				}
				if (current[0] instanceof OWLObjectSomeValuesFrom
						&& current[1] instanceof OWLClass)
					rewriteType3(current[0], current[1]);
				if (current[0] instanceof OWLClass
						&& current[1] instanceof OWLObjectSomeValuesFrom)
					rewriteType4(current[0], current[1]);
				if (current[0] instanceof OWLObjectHasSelf
						&& current[1] instanceof OWLClass)
					rewriteType5(current[0], current[1]);
				if (current[0] instanceof OWLClass
						&& current[1] instanceof OWLObjectHasSelf)
					rewriteType6(current[0], current[1]);
				if (current[0].isOWLThing() && current[1] instanceof OWLClass)
					rewriteType7(current[1]);
				if (current[0] instanceof OWLClass && current[1].isOWLNothing())
					rewriteType8(current[0]);

			}
			if (current.length == 3) { // disjointness
				if (current[0] instanceof OWLObjectIntersectionOf
						&& current[1] instanceof OWLClass)
					rewriteType2(current[0], current[1]);
			}

		}
	}

	public void TranslateRBox() {

		for (OWLObjectPropertyExpression p : m_axioms.m_functionalObjectProperty) {
			String pname = getIRIName(p);
			m_axioms.m_datalog_rules.add("inst(?z1,?z2) :- nom(?z1), nom(?z2),"
					+ "triple(?x,'" + pname + "',?z1), " + "triple(?x,'"
					+ pname + "',?z2). ");
			m_axioms.m_datalog_rules.add("inst(?z2,?z1) :- nom(?z1), nom(?z2),"
					+ "triple(?x,'" + pname + "',?z1), " + "triple(?x,'"
					+ pname + "',?z2). ");
		}

		for (OWLObjectPropertyExpression[] p : m_axioms.m_inverseObjectPropertyInclusions) {
			m_axioms.m_datalog_rules.add("triple(?y,'" + getIRIName(p[1])
					+ "',?x) :- nom(?x), nom(?y)," + "triple(?x,'"
					+ getIRIName(p[0]) + "',?y).");
			//m_axioms.m_datalog_rules.add("triple(?y,'" + getIRIName(p[1])+ "',?x) :- " + "triple(?x,'"+ getIRIName(p[0]) + "',?y).");
		}

		for (OWLObjectPropertyExpression[] p : m_axioms.m_simpleObjectPropertyInclusions) {
			m_axioms.m_datalog_rules.add("subRole('" + getIRIName(p[0]) + "','"
					+ getIRIName(p[1]) + "').");
		}

		for (OWLAxioms.ComplexObjectPropertyInclusion p : m_axioms.m_complexObjectPropertyInclusions) {
			m_axioms.m_datalog_rules.add("subRChain('"
					+ getIRIName(p.m_subObjectProperties[0]) + "','"
					+ getIRIName(p.m_subObjectProperties[1]) + "','"
					+ getIRIName(p.m_superObjectProperty) + "').");

		}
	}

	private void normalizeClassAssertion() {
		while (!m_axioms.m_class_assertions.isEmpty()) {
			OWLClassAssertionAxiom a = m_axioms.m_class_assertions
					.remove(m_axioms.m_class_assertions.size() - 1);
			OWLClassExpression e = a.getClassExpression();
			OWLIndividual i = a.getIndividual();
			if (e instanceof OWLClass) {
				normalized_assertions.add(a);
				continue;
			}
			if (e instanceof OWLObjectIntersectionOf) {
				List<OWLClassExpression> conjuncts = ((OWLObjectIntersectionOf) e)
						.getOperandsAsList();
				for (OWLClassExpression ee : conjuncts) {
					OWLClassAssertionAxiom newA = m_factory
							.getOWLClassAssertionAxiom(ee, i);
					m_axioms.m_class_assertions.add(newA);
				}
			}
			if (e instanceof OWLObjectHasValue) {
				OWLObjectPropertyExpression p = ((OWLObjectHasValue) e)
						.getProperty();
				OWLIndividual ii = ((OWLObjectHasValue) e).getValue();
				m_axioms.m_property_assertions.add(m_factory
						.getOWLObjectPropertyAssertionAxiom(p, i, ii));
			}
		}
	}

	public void TranslateABox() {
		// Class Assertions, C(a)
		normalizeClassAssertion();
		for (int i = 0; i < normalized_assertions.size(); i++) {
			try{
			OWLClassAssertionAxiom current = normalized_assertions.get(i);
			// System.out.println(current.toString());
			String expression = getIRIName(current.getClassExpression());

			String individual = getIRIName(current.getIndividual());
			m_axioms.m_datalog_rules.add("subClass('" + individual + "','"
					+ expression + "').");
			}catch(Exception e){
				
			}
		}

		// Property Assertions, R(a,b)
		for (int i = 0; i < m_axioms.m_property_assertions.size(); i++) {
			OWLObjectPropertyAssertionAxiom current = m_axioms.m_property_assertions
					.get(i);
			String subject = getIRIName(current.getSubject());
			String object = getIRIName(current.getObject());
			String property = getIRIName(current.getProperty());
			m_axioms.m_datalog_rules.add("supEx('" + subject + "','" + property
					+ "','" + object + "','" + object + "').");
		}
	}

	public void TranslateSignature() {
		// translate individual a to nom(a)
		for (OWLIndividual e : m_axioms.m_namedIndividuals) {
			m_axioms.m_datalog_rules.add("nom('" + getIRIName(e) + "').");

		}
		// translate role s to rol(s)
		for (OWLObjectProperty p : m_axioms.m_objectProperties) {
			m_axioms.m_datalog_rules.add("rol('" + getIRIName(p) + "').");
		}
		// translate concept c to cls(c)
		for (OWLClass e : m_axioms.m_classes) {
			// System.out.println(e);
			m_axioms.m_datalog_rules.add("cls('" + getIRIName(e) + "').");
		}

		/**
		int counter = 1;
		for (OWLClass e : m_axioms.m_named_classes) {
			// System.out.println(e);
			String testIndividual = "test_individual_"+counter++;
			m_axioms.m_datalog_rules.add("nom('" + testIndividual + "').");
			m_axioms.m_datalog_rules.add("subClass('" + testIndividual + "','"
					+ getIRIName(e) + "').");
			
		}*/
		
		
		System.out.println("Property size:"
				+ m_axioms.m_objectProperties.size());
		System.out.println("Class size:" + m_axioms.m_named_classes.size());
	}

	private String getIRIName(OWLIndividual o) {
		if (o.asOWLNamedIndividual().getIRI().getFragment() == null)
			return o.toString();
		else
			return "individual_"
					+ o.asOWLNamedIndividual().getIRI().getFragment();

	}

	private String getIRIName(OWLClassExpression o) {
		// System.out.println(o.asOWLClass().getIRI().getFragment());
		if (o.asOWLClass().getIRI().getFragment() == null) {
			// System.out.println(o);
			return o.toString();
		} else
			return "class_" + o.asOWLClass().getIRI().getFragment();

	}

	private String getIRIName(OWLObjectPropertyExpression o) {
		if (o.asOWLObjectProperty().getIRI().getFragment() == null)
			return o.toString();
		else
			return "role_"
					+ o.asOWLObjectProperty().getIRI().getFragment()
							.replace(">", "");
	}

	// A \subclass B
	private void rewriteType1(OWLClassExpression ex1, OWLClassExpression ex2) {
		// String prefix1 = ex1.asOWLClass().getIRI().getStart();
		// String prefix2 = ex2.asOWLClass().getIRI().getFragment();
		m_axioms.m_datalog_rules.add("subClass('" + getIRIName(ex1) + "','"
				+ getIRIName(ex2) + "').");
	}

	// A \conjunct B \subclass C
	private void rewriteType2(OWLClassExpression ex1, OWLClassExpression ex2) {
		List<OWLClassExpression> conjuncts = ((OWLObjectIntersectionOf) ex1)
				.getOperandsAsList();
		m_axioms.m_datalog_rules.add("subConj('" + getIRIName(conjuncts.get(0))
				+ "','" + getIRIName(conjuncts.get(1)) + "'," + "'"
				+ getIRIName(ex2) + "').");
	}

	// \exists R.A \subclass C
	private void rewriteType3(OWLClassExpression ex1, OWLClassExpression ex2) {
		String concept = getIRIName(((OWLObjectSomeValuesFrom) ex1).getFiller());
		String relation = getIRIName(((OWLObjectSomeValuesFrom) ex1)
				.getProperty());
		m_axioms.m_datalog_rules.add("subEx('" + relation + "','" + concept
				+ "'," + "'" + getIRIName(ex2) + "').");
	}

	// A \subclass \exists R.C
	private void rewriteType4(OWLClassExpression ex1, OWLClassExpression ex2) {
		String concept = getIRIName(((OWLObjectSomeValuesFrom) ex2).getFiller());
		String relation = getIRIName(((OWLObjectSomeValuesFrom) ex2)
				.getProperty());
		String freshname = "FN-"
				+ (ex1.toString() + relation + concept).hashCode();
		m_axioms.m_datalog_rules.add("supEx('" + getIRIName(ex1) + "','"
				+ relation + "'," + "'" + concept + "','" + freshname + "').");
	}

	// \exists R.Self \subclass A
	private void rewriteType5(OWLClassExpression ex1, OWLClassExpression ex2) {
		String relation = getIRIName(((OWLObjectHasSelf) ex1).getProperty());
		m_axioms.m_datalog_rules.add("subSelf('" + relation + "','"
				+ getIRIName(ex2) + "').");
	}

	// A \subclass \exists R.Self
	private void rewriteType6(OWLClassExpression ex1, OWLClassExpression ex2) {
		String relation = getIRIName(((OWLObjectHasSelf) ex2).getProperty());
		m_axioms.m_datalog_rules.add("supSelf('" + getIRIName(ex1) + "','"
				+ relation + "').");
	}

	// Top \subclass A
	private void rewriteType7(OWLClassExpression ex) {
		m_axioms.m_datalog_rules.add("top('" + getIRIName(ex) + "').");
	}

	// A \subclass BOT
	private void rewriteType8(OWLClassExpression ex) {
		m_axioms.m_datalog_rules.add("bot('" + getIRIName(ex) + "').");
	}
}
