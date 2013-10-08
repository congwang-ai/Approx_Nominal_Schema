import java.util.ArrayList;
import java.util.List;
import org.semanticweb.owlapi.model.*;

public class Approximation {

	protected final OWLAxioms m_axioms;
	protected final OWLDataFactory m_factory;

	public OWLAxioms getOWLAxioms() {
		return this.m_axioms;
	}

	public OWLDataFactory getFactory() {
		return this.m_factory;
	}

	public Approximation(OWLDataFactory factory, OWLAxioms axioms) {
		m_axioms = axioms;
		m_factory = factory;
	}

	// substitube negation C by its neg(C).
	public OWLClassExpression[] removeNegation(OWLClassExpression[] ex) {
		OWLClassExpression left = removeNegation(ex[0]);
		OWLClassExpression right = removeNegation(ex[1]);
		if (ex.length == 2) {
			return new OWLClassExpression[] { removeNegation(left),
					removeNegation(right) };
		} else {
			return new OWLClassExpression[] { removeNegation(left),
					removeNegation(right), ex[2] };
		}
	}

	public OWLClassExpression removeNegation(OWLClassExpression ex) {
		if (ex instanceof OWLObjectComplementOf) {
			return m_axioms.c_to_n.get(ex.getComplementNNF());
		} else if (ex instanceof OWLClass) {
			return ex;
		} else if (ex.isOWLThing()) {
			return ex;
		} else if (ex.isOWLNothing()) {
			return ex;
		} else if (ex instanceof OWLObjectSomeValuesFrom) {
			if (((OWLObjectSomeValuesFrom) ex).getFiller() instanceof OWLObjectComplementOf) {
				return m_factory.getOWLObjectSomeValuesFrom(
						((OWLObjectSomeValuesFrom) ex).getProperty(),
						m_axioms.c_to_n.get(((OWLObjectSomeValuesFrom) ex)
								.getFiller().getComplementNNF()));
			} else if (((OWLObjectSomeValuesFrom) ex).getFiller() instanceof OWLClass) {
				return ex;
			}
		} else if (ex instanceof OWLObjectAllValuesFrom) {
			if (((OWLObjectAllValuesFrom) ex).getFiller() instanceof OWLObjectComplementOf) {
				return m_factory.getOWLObjectAllValuesFrom(
						((OWLObjectAllValuesFrom) ex).getProperty(),
						m_axioms.c_to_n.get(((OWLObjectAllValuesFrom) ex)
								.getFiller().getComplementNNF()));
			} else if (((OWLObjectAllValuesFrom) ex).getFiller() instanceof OWLClass) {
				return ex;
			}
		} else if (ex instanceof OWLObjectIntersectionOf) {
			List<OWLClassExpression> conjuncts = ((OWLObjectIntersectionOf) ex)
					.getOperandsAsList();
			OWLClassExpression ex0 = removeNegation(conjuncts.get(0));
			OWLClassExpression ex1 = removeNegation(conjuncts.get(1));
			return m_factory.getOWLObjectIntersectionOf(ex0, ex1);
		} else if (ex instanceof OWLObjectUnionOf) {
			List<OWLClassExpression> conjuncts = ((OWLObjectUnionOf) ex)
					.getOperandsAsList();
			OWLClassExpression ex0 = removeNegation(conjuncts.get(0));
			OWLClassExpression ex1 = removeNegation(conjuncts.get(1));
			return m_factory.getOWLObjectUnionOf(ex0, ex1);
		} else if (ex instanceof OWLObjectMinCardinality) {
			if (((OWLObjectMinCardinality) ex).getFiller() instanceof OWLObjectComplementOf) {
				return m_factory.getOWLObjectMinCardinality(
						((OWLObjectMinCardinality) ex).getCardinality(),
						((OWLObjectMinCardinality) ex).getProperty(),
						m_axioms.c_to_n.get(((OWLObjectMinCardinality) ex)
								.getFiller().getComplementNNF()));
			} else if (((OWLObjectMinCardinality) ex).getFiller() instanceof OWLClass) {
				return ex;
			}
		} else if (ex instanceof OWLObjectMaxCardinality) {
			if (((OWLObjectMaxCardinality) ex).getFiller() instanceof OWLObjectComplementOf) {
				return m_factory.getOWLObjectMaxCardinality(
						((OWLObjectMaxCardinality) ex).getCardinality(),
						((OWLObjectMaxCardinality) ex).getProperty(),
						m_axioms.c_to_n.get(((OWLObjectMaxCardinality) ex)
								.getFiller().getComplementNNF()));
			} else if (((OWLObjectMaxCardinality) ex).getFiller() instanceof OWLClass) {
				return ex;
			}
		} else if (ex instanceof OWLObjectHasSelf) {
			return ex;
		}

		return null;
	}

	protected OWLClass getNegated(OWLClass c) {
		if (isNegated(c)) {
			return m_axioms.n_to_c.get(c);
		} else if (isInternal(c)) {
			String negName = "internal_negated_" + c.toString();
			OWLClass negConcept = m_factory.getOWLClass(IRI.create(negName));
			m_axioms.m_classes.add(negConcept);
			if (m_axioms.c_to_n.containsKey(c)) {
				return negConcept;
			}
			m_axioms.c_to_n.put(c, negConcept);
			m_axioms.n_to_c.put(negConcept, c);
			m_axioms.m_extraKnowledge.add(new OWLClassExpression[] { c,
					negConcept, m_factory.getOWLNothing() });
			return negConcept;
		} else if (m_axioms.c_to_n.containsKey(c)) {
			return m_axioms.c_to_n.get(c);
		}
		return null;

	}

	protected boolean isNegated(OWLClass c) {
		return m_axioms.n_to_c.containsKey(c);
	}

	protected boolean isInternal(OWLClass c) {
		return c.toString().contains("internal_concept");
	}

	protected void printOWLClassExpression(OWLClassExpression[] exs) {
		String s = "";
		for (int i = 0; i < exs.length; i++) {
			s += exs[i] + ",";
		}
		System.out.println(s + ".");
	}

	public void approximateAxioms() {
		ArrayList<OWLClassExpression[]> inclusions = new ArrayList<OWLClassExpression[]>();
		for (OWLClassExpression[] exs : m_axioms.m_conceptInclusions_normalized) {
			inclusions.add(removeNegation(exs));
			// printOWLClassExpression(exs);
			// printOWLClassExpression(removeNegation(exs));
		}
		// Now inclusions contain the expressions without negation.
		// Now let's do approximation

		for (int i = 0; i < inclusions.size(); i++) {
			OWLClassExpression[] current = inclusions.get(i);
			if (current.length == 2) {
				// //System.out.println(current[0] + "," + current[1]);
				OWLClassExpression left = current[0];
				OWLClassExpression right = current[1];
				//System.out.println(left+","+right+",");
				if (left instanceof OWLClass && right instanceof OWLClass) {
					OWLClass neg1 = getNegated((OWLClass) left);
					OWLClass neg2 = getNegated((OWLClass) right);
					m_axioms.m_conceptInclusions_approximated.add(current);
					m_axioms.m_conceptInclusions_approximated
							.add(new OWLClassExpression[] { neg2, neg1 });
				} else if (left instanceof OWLClass
						&& right instanceof OWLObjectUnionOf) {
					List<OWLClassExpression> disjuncts = ((OWLObjectUnionOf) right).getOperandsAsList();
					//m_axioms.m_conceptInclusions_approximated.add(new OWLClassExpression[] { left,disjuncts.get(0), });
					//m_axioms.m_conceptInclusions_approximated.add(new OWLClassExpression[] { left,disjuncts.get(1), });
					OWLClass neg1 = getNegated((OWLClass) disjuncts.get(0));
					OWLClass neg2 = getNegated((OWLClass) disjuncts.get(1));
					OWLClass neg3 = getNegated((OWLClass) left);
					m_axioms.m_conceptInclusions_approximated
							.add(new OWLClassExpression[] {
									m_factory.getOWLObjectIntersectionOf(neg1,
											neg2), neg3 });
				} else if (left instanceof OWLClass
						&& right instanceof OWLObjectSomeValuesFrom) {
					m_axioms.m_conceptInclusions_approximated.add(current);
				} else if (left instanceof OWLClass
						&& right instanceof OWLObjectAllValuesFrom) {
					// Approximate 1
					OWLClassExpression neg1 = ((OWLObjectAllValuesFrom) right)
							.getFiller();
					neg1 = getNegated(neg1.asOWLClass());
					OWLClassExpression neg2 = getNegated(left.asOWLClass());
					OWLObjectProperty p = (OWLObjectProperty) ((OWLObjectAllValuesFrom) right)
							.getProperty();
					m_axioms.m_conceptInclusions_approximated
							.add(new OWLClassExpression[] {
									m_factory.getOWLObjectSomeValuesFrom(p,
											neg1), neg2 });

					// Approximate 2
					OWLObjectProperty ip = m_factory.getOWLObjectProperty(IRI
							.create("internal_inverse_role" + p.toString()));
					m_axioms.m_inverseObjectPropertyInclusions
							.add(new OWLObjectPropertyExpression[] { p, ip });
					m_axioms.m_conceptInclusions_approximated
							.add(new OWLClassExpression[] {
									m_factory.getOWLObjectSomeValuesFrom(p,
											left),
									((OWLObjectAllValuesFrom) right)
											.getFiller() });

				} else if (left instanceof OWLClass
						&& right instanceof OWLObjectHasSelf) {
					m_axioms.m_conceptInclusions_approximated.add(current);
				} else if (left instanceof OWLClass && right.isOWLNothing()) {
					m_axioms.m_conceptInclusions_approximated.add(current);
				} else if (left instanceof OWLClass
						&& right instanceof OWLObjectMinCardinality) {
					OWLObjectProperty p = (OWLObjectProperty) ((OWLObjectMinCardinality) right)
							.getProperty();
					OWLClassExpression c = ((OWLObjectMinCardinality) right)
							.getFiller();
					m_axioms.m_conceptInclusions_approximated
							.add(new OWLClassExpression[] { left,
									m_factory.getOWLObjectSomeValuesFrom(p, c) });
				} else if (left instanceof OWLClass
						&& right instanceof OWLObjectMaxCardinality) {
					// TODO
					OWLObjectProperty p = (OWLObjectProperty) ((OWLObjectMaxCardinality) right)
							.getProperty();
					OWLClassExpression c = ((OWLObjectMaxCardinality) right)
							.getFiller();
					String rule = "" + ":-" + "nom(?z1),nom(?z2),"
							+ p.toString() + "(?x,?z1)," + p.toString()
							+ "(?x,?z2).";
				} else if (left.isOWLThing() && right instanceof OWLClass) {
					m_axioms.m_conceptInclusions_approximated.add(current);
				} else if (left instanceof OWLObjectIntersectionOf
						&& right instanceof OWLClass) {
					m_axioms.m_conceptInclusions_approximated.add(current);
				} else if (left instanceof OWLObjectSomeValuesFrom
						&& right instanceof OWLClass) {
					m_axioms.m_conceptInclusions_approximated.add(current);
				} else if (left instanceof OWLObjectHasSelf
						&& right instanceof OWLClass) {
					m_axioms.m_conceptInclusions_approximated.add(current);
				} else if (left instanceof OWLObjectAllValuesFrom
						&& right instanceof OWLClass) {
					OWLClassExpression neg1 = getNegated((((OWLObjectAllValuesFrom) left)
							.getFiller()).asOWLClass());
					OWLClassExpression neg2 = getNegated(right.asOWLClass());
					OWLObjectProperty p = (OWLObjectProperty) ((OWLObjectAllValuesFrom) left)
							.getProperty();
					
					m_axioms.m_conceptInclusions_approximated
							.add(new OWLClassExpression[] {
									neg2,
									m_factory.getOWLObjectSomeValuesFrom(p,
											neg1) });
				} else if (left instanceof OWLObjectMinCardinality
						&& right instanceof OWLClass) {
					// TODO
				} else if (left instanceof OWLObjectMaxCardinality
						&& right instanceof OWLClass) {
					OWLClassExpression neg1 = getNegated((((OWLObjectMaxCardinality) left)
							.getFiller()).asOWLClass());
					OWLClassExpression neg2 = getNegated(right.asOWLClass());
					OWLObjectProperty p = (OWLObjectProperty) ((OWLObjectMaxCardinality) left)
							.getProperty();
					m_axioms.m_conceptInclusions_approximated
							.add(new OWLClassExpression[] {
									neg2,
									m_factory.getOWLObjectSomeValuesFrom(p,
											neg1) });
				}

			}
			if (current.length == 3) {
				m_axioms.m_conceptInclusions_approximated.add(current);
			}
		}
		m_axioms.m_conceptInclusions_approximated
				.addAll(m_axioms.m_extraKnowledge);
	}
}