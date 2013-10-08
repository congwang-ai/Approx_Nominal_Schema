import java.util.*;

import org.semanticweb.owlapi.model.*;

public class Normalization {

	protected final OWLAxioms m_axioms;
	protected final OWLDataFactory m_factory;
	protected int fresh_role_name_index = 1;

	public Normalization(OWLDataFactory factory, OWLAxioms axioms) {
		m_axioms = axioms;
		m_factory = factory;

	}

	public void processOntology(OWLOntology ontology) {
		m_axioms.m_named_classes.addAll(ontology.getClassesInSignature(true));
		m_axioms.m_classes.addAll(ontology.getClassesInSignature(true));
		m_axioms.m_objectProperties.addAll(ontology
				.getObjectPropertiesInSignature(true));
		m_axioms.m_dataProperties.addAll(ontology
				.getDataPropertiesInSignature(true));
		m_axioms.m_namedIndividuals.addAll(ontology
				.getIndividualsInSignature(true));
		m_axioms.m_ontology = ontology;

		processAxioms(ontology.getLogicalAxioms());
	}

	public void processAxioms(Collection<? extends OWLAxiom> axioms) {
		AxiomVisitor axiomVisitor = new AxiomVisitor();
		for (OWLAxiom axiom : axioms) {
			axiom.accept(axiomVisitor);
		}

		buildMapping();
		normalizeInclusions(axiomVisitor.m_classExpressionInclusions);
	}

	// build mapping between concept and its negation
	// Actually this is part of Approximation
	public void buildMapping() {
		for (OWLClass e : m_axioms.m_named_classes) {
			String negName = "internal_negated_" + e.getIRI().getFragment();
			OWLClass negConcept = m_factory.getOWLClass(IRI.create(negName));
			m_axioms.m_classes.add(negConcept);
			m_axioms.c_to_n.put(e, negConcept);
			m_axioms.n_to_c.put(negConcept, e);
			m_axioms.m_extraKnowledge.add(new OWLClassExpression[] { e,
					negConcept, m_factory.getOWLNothing() });
		}
		m_axioms.c_to_n.put(m_factory.getOWLThing(), m_factory.getOWLNothing());
		m_axioms.c_to_n.put(m_factory.getOWLNothing(), m_factory.getOWLThing());
		m_axioms.n_to_c.put(m_factory.getOWLNothing(), m_factory.getOWLThing());
		m_axioms.n_to_c.put(m_factory.getOWLThing(), m_factory.getOWLNothing());

	}

	public void normalizeInclusions(List<OWLClassExpression[]> inclusions) {
		// Normalize a SROIQ KB
		int m_firstReplacementIndex = 1;
		// add property range and domain

		for (OWLObjectProperty p : m_axioms.m_objectProperties) {
			for (OWLClassExpression e : p.getDomains(m_axioms.m_ontology)) {
				inclusions.add(new OWLClassExpression[] {
						m_factory.getOWLObjectSomeValuesFrom(p,
								m_factory.getOWLThing()), e });
			}
			for (OWLClassExpression e : p.getRanges(m_axioms.m_ontology)) {
				inclusions.add(new OWLClassExpression[] {
						m_factory.getOWLThing(),
						m_factory.getOWLObjectAllValuesFrom(p, e) });
			}

		}

		while (!inclusions.isEmpty()) {
			try {
				OWLClassExpression[] current = inclusions.remove(inclusions
						.size() - 1);
				if (current.length == 2) { // subsumption situation
					if (isObjectExpressionSimple(current[0], current[1])) {
						m_axioms.m_conceptInclusions_normalized
								.add(new OWLClassExpression[] { current[0],
										current[1] });
						continue;
					}
					if (!isLeftSimple(current[0])) {
						// left is Unionof
						if (current[0] instanceof OWLObjectUnionOf) {
							List<OWLClassExpression> conjuncts = ((OWLObjectUnionOf) current[0])
									.getOperandsAsList();
							for (OWLClassExpression e : conjuncts) {
								inclusions.add(new OWLClassExpression[] { e,
										current[1] });
							}
						}
						// left is IntersectionOf
						else if (current[0] instanceof OWLObjectIntersectionOf) {
							List<OWLClassExpression> conjuncts = ((OWLObjectIntersectionOf) current[0])
									.getOperandsAsList();
							if (conjuncts.size() != 2) { // when conjunctions
															// are
															// more than 2
								OWLObjectIntersectionOf newConjunct = m_factory
										.getOWLObjectIntersectionOf(
												conjuncts.get(0),
												conjuncts.get(1));
								OWLClass freshname = m_factory.getOWLClass(IRI
										.create("internal_concept_"
												+ m_firstReplacementIndex++));
								m_axioms.m_classes.add(freshname);
								inclusions.add(new OWLClassExpression[] {
										newConjunct, freshname });
								Set<OWLClassExpression> newconjuncts = new HashSet<OWLClassExpression>();
								conjuncts.remove(0);
								conjuncts.remove(1);
								conjuncts.add(freshname);
								newconjuncts.addAll(conjuncts);
								OWLObjectIntersectionOf newConjunctEx = m_factory
										.getOWLObjectIntersectionOf(newconjuncts);
								inclusions.add(new OWLClassExpression[] {
										newConjunctEx, current[1] });
							} else { // when conjunctions are 2
								if (!(conjuncts.get(0) instanceof OWLClass)) {
									OWLClass freshname = m_factory
											.getOWLClass(IRI
													.create("internal_concept_"
															+ m_firstReplacementIndex++));
									m_axioms.m_classes.add(freshname);
									inclusions.add(new OWLClassExpression[] {
											conjuncts.get(0), freshname });
									OWLObjectIntersectionOf newConjunctEx = m_factory
											.getOWLObjectIntersectionOf(
													freshname, conjuncts.get(1));
									inclusions.add(new OWLClassExpression[] {
											newConjunctEx, current[1] });
								} else if (!isSimpleConcept(conjuncts.get(1))) {
									OWLClass freshname = m_factory
											.getOWLClass(IRI
													.create("internal_concept_"
															+ m_firstReplacementIndex++));
									m_axioms.m_classes.add(freshname);
									inclusions.add(new OWLClassExpression[] {
											conjuncts.get(1), freshname });
									OWLObjectIntersectionOf newConjunctEx = m_factory
											.getOWLObjectIntersectionOf(
													conjuncts.get(0), freshname);
									inclusions.add(new OWLClassExpression[] {
											newConjunctEx, current[1] });
								}
							}
							// left is \exists R.C
						} else if (current[0] instanceof OWLObjectSomeValuesFrom) {
							if (!isObjectSomeValuesFromSimple(current[0])) {
								OWLClassExpression original = ((OWLObjectSomeValuesFrom) current[0])
										.getFiller();
								OWLClass freshname = m_factory.getOWLClass(IRI
										.create("internal_concept_"
												+ m_firstReplacementIndex++));
								m_axioms.m_classes.add(freshname);
								OWLObjectPropertyExpression theProperty = ((OWLObjectSomeValuesFrom) current[0])
										.getProperty();
								OWLObjectSomeValuesFrom newExpression = m_factory
										.getOWLObjectSomeValuesFrom(
												theProperty, freshname);
								inclusions.add(new OWLClassExpression[] {
										newExpression, current[1] });
								inclusions.add(new OWLClassExpression[] {
										original, freshname });
							} else {

							}
							// left is \forall R.C
						} else if (current[0] instanceof OWLObjectAllValuesFrom) {
							if (!isObjectAllValuesFromSimple(current[0])) {
								OWLClassExpression original = ((OWLObjectAllValuesFrom) current[0])
										.getFiller();
								OWLClass freshname = m_factory.getOWLClass(IRI
										.create("internal_concept_"
												+ m_firstReplacementIndex++));
								m_axioms.m_classes.add(freshname);
								OWLObjectPropertyExpression theProperty = ((OWLObjectAllValuesFrom) current[0])
										.getProperty();
								OWLObjectAllValuesFrom newExpression = m_factory
										.getOWLObjectAllValuesFrom(theProperty,
												freshname);
								inclusions.add(new OWLClassExpression[] {
										newExpression, current[1] });
								inclusions.add(new OWLClassExpression[] {
										original, freshname });
							} else {

							}
							// left is \exists >=n R.C
						} else if (current[0] instanceof OWLObjectMinCardinality) {
							if (!isObjectMinCardinalitySimple(current[0])) {
								OWLClassExpression original = ((OWLObjectMinCardinality) current[0])
										.getFiller();
								OWLClass freshname = m_factory.getOWLClass(IRI
										.create("internal_concept_"
												+ m_firstReplacementIndex++));
								m_axioms.m_classes.add(freshname);
								OWLObjectPropertyExpression theProperty = ((OWLObjectMinCardinality) current[0])
										.getProperty();
								int cardinality = ((OWLObjectMinCardinality) current[0])
										.getCardinality();
								OWLObjectMinCardinality newExpression = m_factory
										.getOWLObjectMinCardinality(
												cardinality, theProperty,
												freshname);
								inclusions.add(new OWLClassExpression[] {
										newExpression, current[1] });
								inclusions.add(new OWLClassExpression[] {
										original, freshname });
							} else {

							}
							// left is \exists <=n R.C
						} else if (current[0] instanceof OWLObjectMaxCardinality) {
							if (!isObjectMaxCardinalitySimple(current[0])) {
								OWLClassExpression original = ((OWLObjectMaxCardinality) current[0])
										.getFiller();
								OWLClass freshname = m_factory.getOWLClass(IRI
										.create("internal_concept_"
												+ m_firstReplacementIndex++));
								m_axioms.m_classes.add(freshname);
								OWLObjectPropertyExpression theProperty = ((OWLObjectMaxCardinality) current[0])
										.getProperty();
								int cardinality = ((OWLObjectMaxCardinality) current[0])
										.getCardinality();
								OWLObjectMaxCardinality newExpression = m_factory
										.getOWLObjectMaxCardinality(
												cardinality, theProperty,
												freshname);
								inclusions.add(new OWLClassExpression[] {
										newExpression, current[1] });
								inclusions.add(new OWLClassExpression[] {
										original, freshname });
							} else {

							}
						} else if (current[0] instanceof OWLObjectExactCardinality) {
							OWLClassExpression original = ((OWLObjectExactCardinality) current[0])
									.getFiller();
							OWLObjectPropertyExpression theProperty = ((OWLObjectMaxCardinality) current[0])
									.getProperty();
							int cardinality = ((OWLObjectExactCardinality) current[0])
									.getCardinality();
							OWLObjectMaxCardinality maxExpression = m_factory
									.getOWLObjectMaxCardinality(cardinality,
											theProperty, original);
							OWLObjectMaxCardinality minExpression = m_factory
									.getOWLObjectMaxCardinality(cardinality,
											theProperty, original);
							OWLObjectIntersectionOf conjuncts = m_factory
									.getOWLObjectIntersectionOf(maxExpression,
											minExpression);
							inclusions.add(new OWLClassExpression[] {
									conjuncts, current[1] });
						}
						// right is not simple
					} else if (!isRightSimple(current[1])) {
						if (current[1] instanceof OWLObjectSomeValuesFrom) {
							OWLClassExpression original = ((OWLObjectSomeValuesFrom) current[1])
									.getFiller();
							OWLClass freshname = m_factory.getOWLClass(IRI
									.create("internal_concept_"
											+ m_firstReplacementIndex++));
							m_axioms.m_classes.add(freshname);
							OWLObjectPropertyExpression theProperty = ((OWLObjectSomeValuesFrom) current[1])
									.getProperty();
							OWLObjectSomeValuesFrom newExpression = m_factory
									.getOWLObjectSomeValuesFrom(theProperty,
											freshname);
							inclusions.add(new OWLClassExpression[] {
									current[0], newExpression });
							inclusions.add(new OWLClassExpression[] {
									freshname, original });
						} else if (current[1] instanceof OWLObjectAllValuesFrom) {
							OWLClassExpression original = ((OWLObjectAllValuesFrom) current[1])
									.getFiller();
							OWLClass freshname = m_factory.getOWLClass(IRI
									.create("internal_concept_"
											+ m_firstReplacementIndex++));
							m_axioms.m_classes.add(freshname);
							OWLObjectPropertyExpression theProperty = ((OWLObjectAllValuesFrom) current[1])
									.getProperty();
							OWLObjectAllValuesFrom newExpression = m_factory
									.getOWLObjectAllValuesFrom(theProperty,
											freshname);
							inclusions.add(new OWLClassExpression[] {
									current[0], newExpression });
							inclusions.add(new OWLClassExpression[] {
									freshname, original });
						} else if (current[1] instanceof OWLObjectMaxCardinality) {
							if (!isObjectMaxCardinalitySimple(current[1])) {
								OWLClassExpression original = ((OWLObjectMaxCardinality) current[1])
										.getFiller();
								OWLClass freshname = m_factory.getOWLClass(IRI
										.create("internal_concept_"
												+ m_firstReplacementIndex++));
								m_axioms.m_classes.add(freshname);
								OWLObjectPropertyExpression theProperty = ((OWLObjectMaxCardinality) current[1])
										.getProperty();
								int cardinality = ((OWLObjectMaxCardinality) current[1])
										.getCardinality();
								OWLObjectMaxCardinality newExpression = m_factory
										.getOWLObjectMaxCardinality(
												cardinality, theProperty,
												freshname);
								inclusions.add(new OWLClassExpression[] {
										current[0], newExpression });
								inclusions.add(new OWLClassExpression[] {
										freshname, original });
							} else {

							}
						} else if (current[1] instanceof OWLObjectMinCardinality) {
							if (!isObjectMinCardinalitySimple(current[1])) {
								OWLClassExpression original = ((OWLObjectMinCardinality) current[1])
										.getFiller();
								OWLClass freshname = m_factory.getOWLClass(IRI
										.create("internal_concept_"
												+ m_firstReplacementIndex++));
								m_axioms.m_classes.add(freshname);
								OWLObjectPropertyExpression theProperty = ((OWLObjectMinCardinality) current[1])
										.getProperty();
								int cardinality = ((OWLObjectMinCardinality) current[1])
										.getCardinality();
								OWLObjectMinCardinality newExpression = m_factory
										.getOWLObjectMinCardinality(
												cardinality, theProperty,
												freshname);
								inclusions.add(new OWLClassExpression[] {
										current[0], newExpression });
								inclusions.add(new OWLClassExpression[] {
										freshname, original });
							} else {

							}
						} else if (current[1] instanceof OWLObjectExactCardinality) {
							OWLClassExpression original = ((OWLObjectExactCardinality) current[1])
									.getFiller();
							OWLObjectPropertyExpression theProperty = ((OWLObjectMaxCardinality) current[1])
									.getProperty();
							int cardinality = ((OWLObjectExactCardinality) current[1])
									.getCardinality();
							OWLObjectMaxCardinality maxExpression = m_factory
									.getOWLObjectMaxCardinality(cardinality,
											theProperty, original);
							OWLObjectMaxCardinality minExpression = m_factory
									.getOWLObjectMaxCardinality(cardinality,
											theProperty, original);
							inclusions.add(new OWLClassExpression[] {
									current[0], maxExpression });
							inclusions.add(new OWLClassExpression[] {
									current[0], minExpression });
						} else if (current[1] instanceof OWLObjectIntersectionOf) {
							List<OWLClassExpression> conjuncts = ((OWLObjectIntersectionOf) current[1])
									.getOperandsAsList();
							for (int i = 0; i < conjuncts.size(); i++) {
								inclusions.add(new OWLClassExpression[] {
										current[0], conjuncts.get(i) });
							}
						} else if (current[1] instanceof OWLObjectUnionOf) {
							List<OWLClassExpression> disjuncts = ((OWLObjectUnionOf) current[1])
									.getOperandsAsList();
							if (disjuncts.size() != 2) { // when conjunctions
															// are
															// more than 2
								OWLObjectUnionOf newDisjunct = m_factory
										.getOWLObjectUnionOf(disjuncts.get(0),
												disjuncts.get(1));
								OWLClass freshname = m_factory.getOWLClass(IRI
										.create("internal_concept_"
												+ m_firstReplacementIndex++));
								m_axioms.m_classes.add(freshname);
								inclusions.add(new OWLClassExpression[] {
										freshname, newDisjunct });
								Set<OWLClassExpression> newdisjuncts = new HashSet<OWLClassExpression>();
								disjuncts.remove(0);
								disjuncts.remove(1);
								disjuncts.add(freshname);
								newdisjuncts.addAll(disjuncts);
								OWLObjectUnionOf newDisjunctEx = m_factory
										.getOWLObjectUnionOf(newdisjuncts);
								inclusions.add(new OWLClassExpression[] {
										current[0], newDisjunctEx });
							} else { // when disjunctions are 2
								if (!isSimpleConcept(disjuncts.get(0))) {
									OWLClass freshname = m_factory
											.getOWLClass(IRI
													.create("internal_concept_"
															+ m_firstReplacementIndex++));
									m_axioms.m_classes.add(freshname);
									inclusions.add(new OWLClassExpression[] {
											freshname, disjuncts.get(0) });
									OWLObjectUnionOf newDisjunctEx = m_factory
											.getOWLObjectUnionOf(freshname,
													disjuncts.get(1));
									inclusions.add(new OWLClassExpression[] {
											current[0], newDisjunctEx });
								} else if (!isSimpleConcept(disjuncts.get(1))) {
									OWLClass freshname = m_factory
											.getOWLClass(IRI
													.create("internal_concept_"
															+ m_firstReplacementIndex++));
									m_axioms.m_classes.add(freshname);
									inclusions.add(new OWLClassExpression[] {
											freshname, disjuncts.get(1) });
									OWLObjectUnionOf newDisjunctEx = m_factory
											.getOWLObjectUnionOf(freshname,
													disjuncts.get(0));
									inclusions.add(new OWLClassExpression[] {
											current[0], newDisjunctEx });
								}
							}
						}
					}
				}
				if (current.length == 3) { // which is concept disjointness
											// situation
					if (current[2].isOWLNothing()) {
						if (!(current[0] instanceof OWLClass)) {
							OWLClass freshname = m_factory.getOWLClass(IRI
									.create("internal_concept_"
											+ m_firstReplacementIndex++));
							m_axioms.m_classes.add(freshname);
							inclusions.add(new OWLClassExpression[] {
									current[0], freshname });
							inclusions.add(new OWLClassExpression[] {
									freshname, current[1], current[2] });
						} else if (!(current[1] instanceof OWLClass)) {
							OWLClass freshname = m_factory.getOWLClass(IRI
									.create("internal_concept_"
											+ m_firstReplacementIndex++));
							m_axioms.m_classes.add(freshname);
							inclusions.add(new OWLClassExpression[] {
									current[1], freshname });
							inclusions.add(new OWLClassExpression[] {
									current[0], freshname, current[2] });
						}
					}
				}
			} catch (Exception e) {

			}
		}

	}

	public boolean isObjectSomeValuesFromSimple(OWLClassExpression ex) {
		if (ex instanceof OWLObjectSomeValuesFrom) {
			if (isSimpleConcept(((OWLObjectSomeValuesFrom) ex).getFiller())) {
				return true;
			}
		}
		return false;
	}

	public boolean isObjectAllValuesFromSimple(OWLClassExpression ex) {
		if (ex instanceof OWLObjectAllValuesFrom) {
			if (isSimpleConcept(((OWLObjectAllValuesFrom) ex).getFiller())) {
				return true;
			}
		}
		return false;
	}

	public boolean isObjectMaxCardinalitySimple(OWLClassExpression ex) {
		if (ex instanceof OWLObjectMaxCardinality) {
			if (isSimpleConcept(((OWLObjectMaxCardinality) ex).getFiller())) {
				return true;
			}
		}
		return false;
	}

	public boolean isObjectMinCardinalitySimple(OWLClassExpression ex) {
		if (ex instanceof OWLObjectMinCardinality) {
			if (isSimpleConcept(((OWLObjectMinCardinality) ex).getFiller())) {
				return true;
			}
		}
		return false;
	}

	public boolean isSimpleConcept(OWLClassExpression concept) {
		if (concept instanceof OWLClass) {

			return true;
		} else if (concept instanceof OWLObjectComplementOf) {
			if (concept.getComplementNNF() instanceof OWLClass) {
				return true;
			}
		}
		return false;
	}

	public boolean isObjectExpressionSimple(OWLClassExpression left,
			OWLClassExpression right) {
		if (isSimpleConcept(left)) {
			// A \subclass C
			if (isSimpleConcept(right))
				return true;
			// A \subclass \exists R.C
			else if (right instanceof OWLObjectSomeValuesFrom) {
				if (isSimpleConcept(((OWLObjectSomeValuesFrom) right)
						.getFiller()))
					return true;
				else
					return false;
			} else if (right.isOWLThing())
				return true;
			// A \subclass \exists R.Self
			else if (right instanceof OWLObjectHasSelf)
				return true;
			// A \subclass \forall R.C
			else if (right instanceof OWLObjectAllValuesFrom) {
				if (isSimpleConcept(((OWLObjectAllValuesFrom) right)
						.getFiller()))
					return true;
				else
					return false;
			}
			// A \subclass B or C
			else if (right instanceof OWLObjectUnionOf) {
				List<OWLClassExpression> disjuncts = ((OWLObjectUnionOf) right)
						.getOperandsAsList();
				if (disjuncts.size() != 2)
					return false;
				for (int i = 0; i < 2; i++) {
					if (!isSimpleConcept(disjuncts.get(i))) {
						return false;
					}
				}
				return true;
				// A \subclass <=n R.C
			} else if (right instanceof OWLObjectMaxCardinality) {
				if (isSimpleConcept(((OWLObjectMaxCardinality) right)
						.getFiller()))
					return true;
				else
					return false;
				// A \subclass >= n R.C
			} else if (right instanceof OWLObjectMinCardinality) {
				if (isSimpleConcept(((OWLObjectMinCardinality) right)
						.getFiller()))
					return true;
				else
					return false;
			} else
				return false;
			// A and B \subclass C
		} else if (left instanceof OWLObjectIntersectionOf) {
			if (!isSimpleConcept(right))
				return false;
			List<OWLClassExpression> conjuncts = ((OWLObjectIntersectionOf) left)
					.getOperandsAsList();
			if (conjuncts.size() != 2)
				return false;
			for (int i = 0; i < 2; i++) {
				if (!isSimpleConcept(conjuncts.get(i))) {
					return false;
				}
			}
			return true;
			// \exists R.A \subclass C
		} else if (left instanceof OWLObjectSomeValuesFrom) {
			if (isSimpleConcept(((OWLObjectSomeValuesFrom) left).getFiller())) {
				if (isSimpleConcept(right))
					return true;
			}
			return false;
			// \forall R.A \subclass C
		} else if (left instanceof OWLObjectAllValuesFrom) {
			if (isSimpleConcept(((OWLObjectAllValuesFrom) left).getFiller())) {
				if (isSimpleConcept(right))
					return true;
			}
			return false;
			// \top \subclass C
		} else if (left.isOWLThing() && isSimpleConcept(right))
			return true;
		// \exists R.self \subclass C
		else if (left instanceof OWLObjectHasSelf && isSimpleConcept(right))
			return true;
		// <= n R.A \subclass C
		else if (left instanceof OWLObjectMaxCardinality) {
			if (isSimpleConcept(((OWLObjectMaxCardinality) left).getFiller())) {
				if (isSimpleConcept(right))
					return true;
			}
			return false;
		}
		// >= n R.A \subclass C
		else if (left instanceof OWLObjectMinCardinality) {
			if (isSimpleConcept(((OWLObjectMinCardinality) left).getFiller())) {
				if (isSimpleConcept(right))
					return true;
			}
			return false;
		} else
			return false;
	}

	public boolean isLeftSimple(OWLClassExpression left) {
		if (isSimpleConcept(left) || left.isOWLThing()) {
			return true;
		} else if (left instanceof OWLObjectIntersectionOf) {
			List<OWLClassExpression> conjuncts = ((OWLObjectIntersectionOf) left)
					.getOperandsAsList();
			if (conjuncts.size() != 2)
				return false;
			for (int i = 0; i < 2; i++) {
				if (!isSimpleConcept(conjuncts.get(i))) {
					return false;
				}
			}
			return true;
		} else if (left instanceof OWLObjectSomeValuesFrom) {
			if (isSimpleConcept(((OWLObjectSomeValuesFrom) left).getFiller())) {
				return true;
			} else
				return false;
		} else if (left instanceof OWLObjectAllValuesFrom) {
			if (isSimpleConcept(((OWLObjectAllValuesFrom) left).getFiller())) {
				return true;
			} else
				return false;
		} else if (left instanceof OWLObjectMinCardinality) {
			if (isSimpleConcept(((OWLObjectMinCardinality) left).getFiller())) {
				return true;
			} else
				return false;
		} else if (left instanceof OWLObjectMaxCardinality) {
			if (isSimpleConcept(((OWLObjectMaxCardinality) left).getFiller())) {
				return true;
			} else
				return false;
		} else if (left instanceof OWLObjectHasSelf)
			return true;
		else
			return false;
	}

	public boolean isRightSimple(OWLClassExpression right) {
		if (isSimpleConcept(right) || right.isOWLNothing()) {
			return true;
		} else if (right instanceof OWLObjectSomeValuesFrom) {
			if (isSimpleConcept(((OWLObjectSomeValuesFrom) right).getFiller())) {
				return true;
			} else
				return false;
		} else if (right instanceof OWLObjectAllValuesFrom) {
			if (isSimpleConcept(((OWLObjectAllValuesFrom) right).getFiller())) {
				return true;
			} else
				return false;
		} else if (right instanceof OWLObjectMaxCardinality) {
			if (isSimpleConcept(((OWLObjectMaxCardinality) right).getFiller())) {
				return true;
			} else
				return false;
		} else if (right instanceof OWLObjectMinCardinality) {
			if (isSimpleConcept(((OWLObjectMinCardinality) right).getFiller())) {
				return true;
			} else
				return false;
		} else if (right instanceof OWLObjectUnionOf) {
			List<OWLClassExpression> disjuncts = ((OWLObjectUnionOf) right)
					.getOperandsAsList();
			if (disjuncts.size() != 2)
				return false;
			for (int i = 0; i < 2; i++) {
				if (!isSimpleConcept(disjuncts.get(i))) {
					return false;
				}
			}
			return true;
		} else if (right instanceof OWLObjectHasSelf)
			return true;
		else
			return false;
	}

	protected void addInclusion(
			OWLObjectPropertyExpression subObjectPropertyExpression,
			OWLObjectPropertyExpression superObjectPropertyExpression) {
		m_axioms.m_simpleObjectPropertyInclusions
				.add(new OWLObjectPropertyExpression[] {
						subObjectPropertyExpression.getSimplified(),
						superObjectPropertyExpression.getSimplified() });
	}

	protected void addInclusion(
			OWLObjectPropertyExpression[] subObjectPropertyExpressions,
			OWLObjectPropertyExpression superObjectPropertyExpression) {
		for (int index = subObjectPropertyExpressions.length - 1; index >= 0; --index)
			subObjectPropertyExpressions[index] = subObjectPropertyExpressions[index]
					.getSimplified();
		m_axioms.m_complexObjectPropertyInclusions
				.add(new OWLAxioms.ComplexObjectPropertyInclusion(
						subObjectPropertyExpressions,
						superObjectPropertyExpression.getSimplified()));
	}

	protected void addFact(OWLIndividualAxiom axiom) {
		m_axioms.m_facts.add(axiom);
	}

	class AxiomVisitor implements OWLAxiomVisitor {
		protected final List<OWLClassExpression[]> m_classExpressionInclusions;

		public AxiomVisitor() {
			m_classExpressionInclusions = new ArrayList<OWLClassExpression[]>();
		}

		// Semantics-less axioms

		public void visit(OWLImportsDeclaration axiom) {
		}

		public void visit(OWLDeclarationAxiom axiom) {
		}

		public void visit(OWLAnnotationAssertionAxiom axiom) {
		}

		public void visit(OWLSubAnnotationPropertyOfAxiom axiom) {
		}

		public void visit(OWLAnnotationPropertyDomainAxiom axiom) {
		}

		public void visit(OWLAnnotationPropertyRangeAxiom axiom) {
		}

		// TBOX
		@Override
		public void visit(OWLSubClassOfAxiom axiom) {
			m_classExpressionInclusions.add(new OWLClassExpression[] {
					axiom.getSubClass().getNNF(),
					axiom.getSuperClass().getNNF() });

		}

		public void visit(OWLEquivalentClassesAxiom axiom) {
			if (axiom.getClassExpressions().size() > 1) {
				Iterator<OWLClassExpression> iterator = axiom
						.getClassExpressions().iterator();
				OWLClassExpression first = iterator.next();
				OWLClassExpression last = first;
				while (iterator.hasNext()) {
					OWLClassExpression next = iterator.next();
					m_classExpressionInclusions.add(new OWLClassExpression[] {
							last.getNNF(), next.getNNF() });
					last = next;
				}
				m_classExpressionInclusions.add(new OWLClassExpression[] {
						last.getNNF(), first.getNNF() });
			}
		}

		public void visit(OWLDisjointClassesAxiom axiom) {
			if (axiom.getClassExpressions().size() <= 1) {
				throw new IllegalArgumentException(
						"Error: Parsed "
								+ axiom.toString()
								+ ". A DisjointClasses axiom in OWL 2 DL must have at least two classes as parameters. ");
			}
			OWLClassExpression[] descriptions = new OWLClassExpression[axiom
					.getClassExpressions().size()];
			axiom.getClassExpressions().toArray(descriptions);
			OWLClass botClass = m_factory.getOWLNothing();
			for (int i = 0; i < descriptions.length; i++)
				for (int j = i + 1; j < descriptions.length; j++)
					m_classExpressionInclusions.add(new OWLClassExpression[] {
							descriptions[i].getNNF(), descriptions[j].getNNF(),
							botClass });
		}

		// RBOX

		public void visit(OWLSubObjectPropertyOfAxiom axiom) {
			if (!axiom.getSubProperty().isOWLBottomObjectProperty()
					&& !axiom.getSuperProperty().isOWLTopObjectProperty())
				m_axioms.m_simpleObjectPropertyInclusions
						.add(new OWLObjectPropertyExpression[] {
								axiom.getSubProperty(),
								axiom.getSuperProperty() });
		}

		public void visit(OWLSubPropertyChainOfAxiom axiom) {
			List<OWLObjectPropertyExpression> subPropertyChain = axiom
					.getPropertyChain();
			OWLObjectPropertyExpression superObjectPropertyExpression = axiom
					.getSuperProperty();

			if (subPropertyChain.size() == 1)
				addInclusion(subPropertyChain.get(0),
						superObjectPropertyExpression);
			else if (subPropertyChain.size() == 2) {
				OWLObjectPropertyExpression[] subObjectProperties = new OWLObjectPropertyExpression[subPropertyChain
						.size()];
				subPropertyChain.toArray(subObjectProperties);
				addInclusion(subObjectProperties, superObjectPropertyExpression);
			} else { // Normalization of Role Chain
				OWLObjectPropertyExpression[] subObjectProperties = new OWLObjectPropertyExpression[2];
				subObjectProperties[0] = subPropertyChain.get(0);
				subObjectProperties[1] = subPropertyChain.get(1);
				IRI ontologyIRI = IRI.create("fresh_role_name");
				OWLObjectProperty newProperty = m_factory
						.getOWLObjectProperty(IRI.create(ontologyIRI + ""
								+ fresh_role_name_index++));
				addInclusion(subObjectProperties, newProperty);
				for (int i = 2; i < subPropertyChain.size() - 1; i++) {
					subObjectProperties[0] = newProperty;
					subObjectProperties[1] = subPropertyChain.get(i);
					newProperty = m_factory
							.getOWLObjectProperty(IRI.create(ontologyIRI + ""
									+ fresh_role_name_index++));
					addInclusion(subObjectProperties, newProperty);
				}
				subObjectProperties[0] = newProperty;
				subObjectProperties[1] = subPropertyChain.get(subPropertyChain
						.size() - 1);
				addInclusion(subObjectProperties, superObjectPropertyExpression);
			}

		}

		public void visit(OWLEquivalentObjectPropertiesAxiom axiom) {
			Set<OWLObjectPropertyExpression> objectPropertyExpressions = axiom
					.getProperties();
			if (objectPropertyExpressions.size() > 1) {
				Iterator<OWLObjectPropertyExpression> iterator = objectPropertyExpressions
						.iterator();
				OWLObjectPropertyExpression first = iterator.next();
				OWLObjectPropertyExpression last = first;
				while (iterator.hasNext()) {
					OWLObjectPropertyExpression next = iterator.next();
					addInclusion(last, next);
					last = next;
				}
				addInclusion(last, first);
			}
		}

		public void visit(OWLInverseObjectPropertiesAxiom axiom) {
			OWLObjectPropertyExpression first = axiom.getFirstProperty();
			OWLObjectPropertyExpression second = axiom.getSecondProperty();
			m_axioms.m_inverseObjectPropertyInclusions
					.add(new OWLObjectPropertyExpression[] { first, second });
		}

		public void visit(OWLReflexiveObjectPropertyAxiom axiom) {
			m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(axiom
					.getProperty().getNamedProperty());
			m_axioms.m_reflexiveObjectProperties.add(axiom.getProperty());
		}

		public void visit(OWLIrreflexiveObjectPropertyAxiom axiom) {
			m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(axiom
					.getProperty().getNamedProperty());
			m_axioms.m_irreflexiveObjectProperties.add(axiom.getProperty());
		}

		public void visit(OWLSymmetricObjectPropertyAxiom axiom) {
			OWLObjectPropertyExpression objectProperty = axiom.getProperty();
			m_axioms.m_inverseObjectPropertyInclusions
					.add(new OWLObjectPropertyExpression[] { objectProperty,
							objectProperty });
		}

		public void visit(OWLAsymmetricObjectPropertyAxiom axiom) {
			m_axioms.m_asymmetricObjectProperties.add(axiom.getProperty());
			m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(axiom
					.getProperty().getNamedProperty());
		}

		public void visit(OWLTransitiveObjectPropertyAxiom axiom) {
			OWLObjectPropertyExpression[] subObjectProperties = new OWLObjectPropertyExpression[] {
					axiom.getProperty(), axiom.getProperty() };
			addInclusion(subObjectProperties, axiom.getProperty());
		}

		public void visit(OWLDisjointObjectPropertiesAxiom axiom) {
			OWLObjectPropertyExpression[] objectPropertyExpressions = new OWLObjectPropertyExpression[axiom
					.getProperties().size()];
			axiom.getProperties().toArray(objectPropertyExpressions);
			for (int i = 0; i < objectPropertyExpressions.length; i++) {
				objectPropertyExpressions[i] = objectPropertyExpressions[i]
						.getSimplified();
				m_axioms.m_objectPropertiesOccurringInOWLAxioms
						.add(objectPropertyExpressions[i].getNamedProperty());
			}
			m_axioms.m_disjointObjectProperties.add(objectPropertyExpressions);
		}

		@Override
		public void visit(OWLFunctionalObjectPropertyAxiom axiom) {
			m_axioms.m_functionalObjectProperty.add(axiom.getProperty());
			// m_factory.getOWLTopObjectProperty();
		}

		// Assertions

		public void visit(OWLSameIndividualAxiom axiom) {
			if (axiom.containsAnonymousIndividuals())
				throw new IllegalArgumentException(
						"The axiom "
								+ axiom
								+ " contains anonymous individuals, which is not allowed in OWL 2. ");
			for (OWLIndividual e : axiom.getIndividuals()) {
				m_axioms.m_individuals.add(e);
			}
			addFact(axiom);
		}

		public void visit(OWLDifferentIndividualsAxiom axiom) {
			if (axiom.containsAnonymousIndividuals())
				throw new IllegalArgumentException(
						"The axiom "
								+ axiom
								+ " contains anonymous individuals, which is not allowed in OWL 2. ");
			for (OWLIndividual e : axiom.getIndividuals()) {
				m_axioms.m_individuals.add(e);
			}
			addFact(axiom);
		}

		public void visit(OWLClassAssertionAxiom axiom) {
			OWLClassExpression classExpression = axiom.getClassExpression();
			addFact(m_factory.getOWLClassAssertionAxiom(classExpression,
					axiom.getIndividual()));
			m_axioms.m_class_assertions.add(axiom);
			m_axioms.m_individuals.add(axiom.getIndividual());
			if (axiom instanceof OWLClass)
				m_axioms.m_classesOccurringInOWLAxioms.add((OWLClass) axiom);
		}

		public void visit(OWLObjectPropertyAssertionAxiom axiom) {
			addFact(m_factory.getOWLObjectPropertyAssertionAxiom(axiom
					.getProperty().getSimplified(), axiom.getSubject(), axiom
					.getObject()));
			m_axioms.m_property_assertions.add(axiom);
			m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(axiom
					.getProperty().getNamedProperty());
			m_axioms.m_individuals.add(axiom.getObject());
			m_axioms.m_individuals.add(axiom.getSubject());
		}

		public void visit(OWLNegativeObjectPropertyAssertionAxiom axiom) {
			if (axiom.containsAnonymousIndividuals())
				throw new IllegalArgumentException(
						"The axiom "
								+ axiom
								+ " contains anonymous individuals, which is not allowed in OWL 2 DL. ");
			addFact(m_factory.getOWLNegativeObjectPropertyAssertionAxiom(axiom
					.getProperty().getSimplified(), axiom.getSubject(), axiom
					.getObject()));
			m_axioms.m_objectPropertiesOccurringInOWLAxioms.add(axiom
					.getProperty().getNamedProperty());
			m_axioms.m_negative_property_assertions.add(axiom);
			m_axioms.m_individuals.add(axiom.getObject());
			m_axioms.m_individuals.add(axiom.getSubject());
		}

		@Override
		public void visit(OWLDataPropertyDomainAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLObjectPropertyDomainAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLNegativeDataPropertyAssertionAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLDisjointDataPropertiesAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLObjectPropertyRangeAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLDisjointUnionAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLDataPropertyRangeAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLFunctionalDataPropertyAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLEquivalentDataPropertiesAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLDataPropertyAssertionAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLSubDataPropertyOfAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLInverseFunctionalObjectPropertyAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLHasKeyAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(OWLDatatypeDefinitionAxiom axiom) {
			// TODO Auto-generated method stub

		}

		@Override
		public void visit(SWRLRule axiom) {
			// TODO Auto-generated method stub

		}

	}
}
