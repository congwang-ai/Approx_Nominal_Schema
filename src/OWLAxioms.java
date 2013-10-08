/* Copyright 2008, 2009, 2010 by the Oxford University Computing Laboratory

   This file is part of HermiT.

   HermiT is free software: you can redistribute it and/or modify
   it under the terms of the GNU Lesser General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   HermiT is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public License
   along with HermiT.  If not, see <http://www.gnu.org/licenses/>.
*/


import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLDataPropertyExpression;
import org.semanticweb.owlapi.model.OWLDataRange;
import org.semanticweb.owlapi.model.OWLHasKeyAxiom;
import org.semanticweb.owlapi.model.OWLIndividual;
import org.semanticweb.owlapi.model.OWLIndividualAxiom;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLNegativeObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.SWRLAtom;

public class OWLAxioms {
    public final Set<OWLClass> m_classes;
    public final Set<OWLClass> m_named_classes;
    public final Set<OWLObjectProperty> m_objectProperties;
    public final Set<OWLObjectProperty> m_objectPropertiesOccurringInOWLAxioms;
    public final Set<OWLClass> m_classesOccurringInOWLAxioms;
    public final Set<OWLObjectPropertyExpression> m_complexObjectPropertyExpressions;
    public final Set<OWLDataProperty> m_dataProperties;
    public final Set<OWLNamedIndividual> m_namedIndividuals;
    public final Collection<OWLClassExpression[]> m_conceptInclusions;
    public final ArrayList<OWLClassExpression[]> m_conceptInclusions_normalized;
    public final ArrayList<OWLClassExpression[]> m_conceptInclusions_approximated;
    public final HashSet<OWLClassExpression[]>  m_extraKnowledge;
    public final Collection<OWLDataRange[]> m_dataRangeInclusions;
    public final Collection<OWLObjectPropertyExpression[]> m_simpleObjectPropertyInclusions;
    public final Collection<OWLObjectPropertyExpression[]> m_inverseObjectPropertyInclusions;
    public final Collection<ComplexObjectPropertyInclusion> m_complexObjectPropertyInclusions;
    public final Collection<OWLObjectPropertyExpression[]> m_disjointObjectProperties;
    public final Set<OWLObjectPropertyExpression> m_reflexiveObjectProperties;
    public final Set<OWLObjectPropertyExpression> m_irreflexiveObjectProperties;
    public final Set<OWLObjectPropertyExpression> m_asymmetricObjectProperties;
    public final Collection<OWLDataPropertyExpression[]> m_dataPropertyInclusions;
    public final Collection<OWLDataPropertyExpression[]> m_disjointDataProperties;
    public final ArrayList<OWLIndividualAxiom> m_facts;
    public final ArrayList<String> m_datalog_rules;
    public final ArrayList<OWLClassAssertionAxiom> m_class_assertions;
    public final ArrayList<OWLObjectPropertyAssertionAxiom> m_property_assertions;
    public final ArrayList<OWLNegativeObjectPropertyAssertionAxiom> m_negative_property_assertions;
    public final Set<OWLIndividual> m_individuals;
    public final Set<String> negated_concepts;
    public OWLOntology m_ontology;
    public final Set<OWLObjectPropertyExpression> m_functionalObjectProperty;
    public final HashMap<OWLClass, OWLClass> c_to_n;
    public final HashMap<OWLObjectProperty, OWLObjectProperty> r_to_ir;
    public final HashMap<OWLClass, OWLClass> n_to_c;
    
    public OWLAxioms() {
    	m_ontology = null;
    	
        m_classes=new HashSet<OWLClass>();
        m_named_classes=new HashSet<OWLClass>();
        m_objectProperties=new HashSet<OWLObjectProperty>();
        m_objectPropertiesOccurringInOWLAxioms=new HashSet<OWLObjectProperty>();
        m_complexObjectPropertyExpressions=new HashSet<OWLObjectPropertyExpression>();
        m_dataProperties=new HashSet<OWLDataProperty>();
        m_namedIndividuals=new HashSet<OWLNamedIndividual>();
        m_conceptInclusions=new ArrayList<OWLClassExpression[]>();
        m_conceptInclusions_normalized=new ArrayList<OWLClassExpression[]>(); 
        m_conceptInclusions_approximated=new ArrayList<OWLClassExpression[]>(); 
        m_dataRangeInclusions=new ArrayList<OWLDataRange[]>();
        m_simpleObjectPropertyInclusions=new ArrayList<OWLObjectPropertyExpression[]>();
        m_inverseObjectPropertyInclusions=new ArrayList<OWLObjectPropertyExpression[]>();
        m_complexObjectPropertyInclusions=new ArrayList<ComplexObjectPropertyInclusion>();
        m_disjointObjectProperties=new ArrayList<OWLObjectPropertyExpression[]>();
        m_reflexiveObjectProperties=new HashSet<OWLObjectPropertyExpression>();
        m_irreflexiveObjectProperties=new HashSet<OWLObjectPropertyExpression>();
        m_asymmetricObjectProperties=new HashSet<OWLObjectPropertyExpression>();
        m_disjointDataProperties=new ArrayList<OWLDataPropertyExpression[]>();
        m_dataPropertyInclusions=new ArrayList<OWLDataPropertyExpression[]>();
        m_facts=new ArrayList<OWLIndividualAxiom>();
        m_datalog_rules=new ArrayList<String>();
        m_class_assertions=new ArrayList<OWLClassAssertionAxiom>();
        m_property_assertions=new ArrayList<OWLObjectPropertyAssertionAxiom>();
        m_individuals=new HashSet<OWLIndividual>();
        m_negative_property_assertions=new ArrayList<OWLNegativeObjectPropertyAssertionAxiom>();
        m_classesOccurringInOWLAxioms=new HashSet<OWLClass>(); 
        negated_concepts=new HashSet<String>();
        
        m_extraKnowledge = new HashSet<OWLClassExpression[]>();         
        c_to_n = new HashMap<OWLClass, OWLClass>();
        n_to_c = new HashMap<OWLClass, OWLClass>();
        r_to_ir = new HashMap<OWLObjectProperty, OWLObjectProperty>();
        m_functionalObjectProperty=new HashSet<OWLObjectPropertyExpression>();
        
    }

    public static class ComplexObjectPropertyInclusion {
        public final OWLObjectPropertyExpression[] m_subObjectProperties;
        public final OWLObjectPropertyExpression m_superObjectProperty;

        public ComplexObjectPropertyInclusion(OWLObjectPropertyExpression[] subObjectProperties,OWLObjectPropertyExpression superObjectPropery) {
            m_subObjectProperties=subObjectProperties;
            m_superObjectProperty=superObjectPropery;
        }
        public ComplexObjectPropertyInclusion(OWLObjectPropertyExpression transitiveObjectProperty) {
            m_subObjectProperties=new OWLObjectPropertyExpression[] { transitiveObjectProperty,transitiveObjectProperty };
            m_superObjectProperty=transitiveObjectProperty;
        }
    }

}
