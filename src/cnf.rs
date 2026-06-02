//! CNF/DNF conversion with Tseitin encoding

use crate::propositional::{Formula, Var};
use std::collections::BTreeMap;

/// A literal is either a variable or its negation
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Literal {
    Pos(Var),
    Neg(Var),
}

impl Literal {
    pub fn positive(name: &str) -> Self {
        Literal::Pos(Var(name.to_string()))
    }

    pub fn negative(name: &str) -> Self {
        Literal::Neg(Var(name.to_string()))
    }

    /// Negate this literal
    pub fn negate(&self) -> Literal {
        match self {
            Literal::Pos(v) => Literal::Neg(v.clone()),
            Literal::Neg(v) => Literal::Pos(v.clone()),
        }
    }

    pub fn var(&self) -> &Var {
        match self {
            Literal::Pos(v) | Literal::Neg(v) => v,
        }
    }
}

/// A clause is a disjunction of literals
pub type Clause = Vec<Literal>;

/// A CNF formula is a conjunction of clauses
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cnf {
    pub clauses: Vec<Clause>,
}

impl Cnf {
    pub fn new(clauses: Vec<Clause>) -> Self {
        Self { clauses }
    }

    pub fn empty() -> Self {
        Self { clauses: vec![] }
    }

    /// Add a clause
    pub fn add_clause(&mut self, clause: Clause) {
        self.clauses.push(clause);
    }

    /// Evaluate the CNF under an assignment
    pub fn eval(&self, assignment: &std::collections::BTreeMap<Var, bool>) -> bool {
        self.clauses.iter().all(|clause| {
            clause.iter().any(|lit| match lit {
                Literal::Pos(v) => *assignment.get(v).unwrap_or(&false),
                Literal::Neg(v) => !*assignment.get(v).unwrap_or(&false),
            })
        })
    }
}

/// A term (conjunction of literals) for DNF
pub type Term = Vec<Literal>;

/// A DNF formula is a disjunction of terms
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Dnf {
    pub terms: Vec<Term>,
}

impl Dnf {
    pub fn new(terms: Vec<Term>) -> Self {
        Self { terms }
    }

    /// Evaluate the DNF under an assignment
    pub fn eval(&self, assignment: &std::collections::BTreeMap<Var, bool>) -> bool {
        self.terms.iter().any(|term| {
            term.iter().all(|lit| match lit {
                Literal::Pos(v) => *assignment.get(v).unwrap_or(&false),
                Literal::Neg(v) => !*assignment.get(v).unwrap_or(&false),
            })
        })
    }
}

/// Convert a formula to NNF (Negation Normal Form) — push negations to atoms
fn to_nnf(f: &Formula) -> Formula {
    match f {
        Formula::Atom(v) => Formula::Atom(v.clone()),
        Formula::Not(inner) => push_neg(inner),
        Formula::And(a, b) => Formula::And(Box::new(to_nnf(a)), Box::new(to_nnf(b))),
        Formula::Or(a, b) => Formula::Or(Box::new(to_nnf(a)), Box::new(to_nnf(b))),
        Formula::Implies(a, b) => Formula::Or(
            Box::new(push_neg(a)),
            Box::new(to_nnf(b)),
        ),
        Formula::Iff(a, b) => {
            let a_nnf = to_nnf(a);
            let b_nnf = to_nnf(b);
            Formula::And(
                Box::new(Formula::Or(
                    Box::new(push_neg(&a_nnf.clone())),
                    Box::new(b_nnf.clone()),
                )),
                Box::new(Formula::Or(
                    Box::new(a_nnf),
                    Box::new(push_neg(&b_nnf)),
                )),
            )
        }
        Formula::Top => Formula::Top,
        Formula::Bot => Formula::Bot,
    }
}

/// Push a negation inward (used in NNF conversion)
fn push_neg(f: &Formula) -> Formula {
    match f {
        Formula::Atom(v) => Formula::Not(Box::new(Formula::Atom(v.clone()))),
        Formula::Not(inner) => to_nnf(inner), // double negation
        Formula::And(a, b) => Formula::Or(
            Box::new(push_neg(a)),
            Box::new(push_neg(b)),
        ), // De Morgan
        Formula::Or(a, b) => Formula::And(
            Box::new(push_neg(a)),
            Box::new(push_neg(b)),
        ), // De Morgan
        Formula::Implies(a, b) => Formula::And(
            Box::new(to_nnf(a)),
            Box::new(push_neg(b)),
        ),
        Formula::Iff(a, b) => {
            let a_nnf = to_nnf(a);
            let b_nnf = to_nnf(b);
            Formula::Or(
                Box::new(Formula::And(
                    Box::new(push_neg(&a_nnf.clone())),
                    Box::new(push_neg(&b_nnf.clone())),
                )),
                Box::new(Formula::And(
                    Box::new(a_nnf),
                    Box::new(b_nnf),
                )),
            )
        }
        Formula::Top => Formula::Bot,
        Formula::Bot => Formula::Top,
    }
}

/// Distribute OR over AND to get CNF from NNF
fn distribute_cnf(a: Formula, b: Formula) -> Formula {
    match (&a, &b) {
        (Formula::And(a1, a2), _) => Formula::And(
            Box::new(distribute_cnf(*a1.clone(), b.clone())),
            Box::new(distribute_cnf(*a2.clone(), b)),
        ),
        (_, Formula::And(b1, b2)) => Formula::And(
            Box::new(distribute_cnf(a.clone(), *b1.clone())),
            Box::new(distribute_cnf(a, *b2.clone())),
        ),
        _ => Formula::Or(Box::new(a), Box::new(b)),
    }
}

/// Convert a formula directly to CNF (naive approach — exponential worst case)
pub fn formula_to_cnf(f: &Formula) -> Cnf {
    let nnf = to_nnf(f);
    let cnf_form = to_cnf_form(&nnf);
    extract_clauses(&cnf_form)
}

fn to_cnf_form(f: &Formula) -> Formula {
    match f {
        Formula::And(a, b) => Formula::And(
            Box::new(to_cnf_form(a)),
            Box::new(to_cnf_form(b)),
        ),
        Formula::Or(a, b) => distribute_cnf(to_cnf_form(a), to_cnf_form(b)),
        other => other.clone(),
    }
}

fn extract_clauses(f: &Formula) -> Cnf {
    match f {
        Formula::And(a, b) => {
            let mut cnf = extract_clauses(a);
            cnf.clauses.extend(extract_clauses(b).clauses);
            cnf
        }
        _ => Cnf::new(vec![extract_clause(f)]),
    }
}

fn extract_clause(f: &Formula) -> Clause {
    match f {
        Formula::Or(a, b) => {
            let mut clause = extract_clause(a);
            clause.extend(extract_clause(b));
            clause
        }
        Formula::Not(inner) => {
            if let Formula::Atom(v) = inner.as_ref() {
                vec![Literal::Neg(v.clone())]
            } else {
                vec![] // shouldn't happen in NNF
            }
        }
        Formula::Atom(v) => vec![Literal::Pos(v.clone())],
        Formula::Top => vec![], // tautological
        Formula::Bot => vec![], // will make empty clause
        _ => vec![],
    }
}

/// Tseitin encoding: convert any formula to equisatisfiable CNF in linear time.
/// Introduces auxiliary variables for subformulas.
pub struct TseitinEncoder {
    counter: usize,
    clauses: Vec<Clause>,
}

impl TseitinEncoder {
    pub fn new() -> Self {
        Self {
            counter: 0,
            clauses: vec![],
        }
    }

    fn fresh_var(&mut self) -> Var {
        self.counter += 1;
        Var(format!("_ts{}", self.counter))
    }

    /// Encode a formula, returning the representative variable and CNF clauses
    pub fn encode(&mut self, f: &Formula) -> (Var, Cnf) {
        let (rep, cnf) = self.encode_inner(f);
        (rep, cnf)
    }

    fn encode_inner(&mut self, f: &Formula) -> (Var, Cnf) {
        match f {
            Formula::Atom(v) => (v.clone(), Cnf::empty()),
            Formula::Top => {
                let t = self.fresh_var();
                let cnf = Cnf::new(vec![vec![Literal::Pos(t.clone())]]);
                (t, cnf)
            }
            Formula::Bot => {
                let b = self.fresh_var();
                let cnf = Cnf::new(vec![vec![Literal::Neg(b.clone())]]);
                (b, cnf)
            }
            Formula::Not(inner) => {
                let (sub, sub_cnf) = self.encode_inner(inner);
                let rep = self.fresh_var();
                let mut clauses = sub_cnf.clauses;
                // rep ↔ ¬sub
                clauses.push(vec![Literal::Neg(rep.clone()), Literal::Neg(sub.clone())]);
                clauses.push(vec![Literal::Pos(rep.clone()), Literal::Pos(sub.clone())]);
                (rep, Cnf::new(clauses))
            }
            Formula::And(a, b) => {
                let (a_rep, a_cnf) = self.encode_inner(a);
                let (b_rep, b_cnf) = self.encode_inner(b);
                let rep = self.fresh_var();
                let mut clauses = a_cnf.clauses;
                clauses.extend(b_cnf.clauses);
                // rep ↔ (a_rep ∧ b_rep)
                // rep → a_rep, rep → b_rep
                clauses.push(vec![Literal::Neg(rep.clone()), Literal::Pos(a_rep.clone())]);
                clauses.push(vec![Literal::Neg(rep.clone()), Literal::Pos(b_rep.clone())]);
                // (¬a_rep ∨ ¬b_rep) → ¬rep  ≡  a_rep ∧ b_rep → rep
                // which is: ¬a_rep ∨ ¬b_rep ∨ rep
                clauses.push(vec![Literal::Neg(a_rep), Literal::Neg(b_rep), Literal::Pos(rep.clone())]);
                (rep, Cnf::new(clauses))
            }
            Formula::Or(a, b) => {
                let (a_rep, a_cnf) = self.encode_inner(a);
                let (b_rep, b_cnf) = self.encode_inner(b);
                let rep = self.fresh_var();
                let mut clauses = a_cnf.clauses;
                clauses.extend(b_cnf.clauses);
                // rep ↔ (a_rep ∨ b_rep)
                clauses.push(vec![Literal::Neg(rep.clone()), Literal::Pos(a_rep.clone()), Literal::Pos(b_rep.clone())]);
                clauses.push(vec![Literal::Pos(rep.clone()), Literal::Neg(a_rep.clone())]);
                clauses.push(vec![Literal::Pos(rep.clone()), Literal::Neg(b_rep.clone())]);
                (rep, Cnf::new(clauses))
            }
            Formula::Implies(a, b) => {
                // a → b ≡ ¬a ∨ b
                let impl_form = Formula::Or(
                    Box::new(Formula::Not(a.clone())),
                    Box::new(*b.clone()),
                );
                self.encode_inner(&impl_form)
            }
            Formula::Iff(a, b) => {
                // (a ↔ b) ≡ (a → b) ∧ (b → a)
                let and_form = Formula::And(
                    Box::new(Formula::Implies(a.clone(), b.clone())),
                    Box::new(Formula::Implies(b.clone(), a.clone())),
                );
                self.encode_inner(&and_form)
            }
        }
    }

    /// Full Tseitin encoding: returns CNF that is equisatisfiable with the original formula.
    pub fn tseitin_encode(f: &Formula) -> Cnf {
        let mut encoder = Self::new();
        let (rep, cnf) = encoder.encode(f);
        let mut clauses = cnf.clauses;
        // Assert the representative is true
        clauses.push(vec![Literal::Pos(rep)]);
        Cnf::new(clauses)
    }
}

/// Convert formula to DNF (disjunctive normal form)
pub fn formula_to_dnf(f: &Formula) -> Dnf {
    let cnf = formula_to_cnf(f);
    // Convert each CNF clause to DNF by cartesian product
    // This is the naive approach; for small formulas it works
    let mut terms: Vec<Term> = vec![vec![]];
    for clause in &cnf.clauses {
        let mut new_terms = Vec::new();
        for term in &terms {
            for lit in clause {
                let mut new_term = term.clone();
                new_term.push(lit.clone());
                new_terms.push(new_term);
            }
        }
        terms = new_terms;
    }
    Dnf::new(terms)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::propositional::*;

    #[test]
    fn test_simple_cnf() {
        // p ∧ q → CNF: {{p}, {q}}
        let f = and(atom("p"), atom("q"));
        let cnf = formula_to_cnf(&f);
        assert!(cnf.clauses.len() >= 2);
    }

    #[test]
    fn test_or_cnf() {
        // p ∨ q → CNF: {{p, q}}
        let f = or(atom("p"), atom("q"));
        let cnf = formula_to_cnf(&f);
        assert_eq!(cnf.clauses.len(), 1);
        assert_eq!(cnf.clauses[0].len(), 2);
    }

    #[test]
    fn test_negation_cnf() {
        // ¬p → CNF: {{¬p}}
        let f = not(atom("p"));
        let cnf = formula_to_cnf(&f);
        assert_eq!(cnf.clauses.len(), 1);
    }

    #[test]
    fn test_implication_cnf() {
        // p → q ≡ ¬p ∨ q → CNF: {{¬p, q}}
        let f = implies(atom("p"), atom("q"));
        let cnf = formula_to_cnf(&f);
        assert_eq!(cnf.clauses.len(), 1);
    }

    #[test]
    fn test_cnf_eval() {
        let cnf = Cnf::new(vec![
            vec![Literal::positive("p"), Literal::positive("q")],
            vec![Literal::negative("r")],
        ]);
        let mut a = BTreeMap::new();
        a.insert(Var("p".into()), true);
        a.insert(Var("q".into()), false);
        a.insert(Var("r".into()), true);
        assert!(!cnf.eval(&a)); // first clause fails (need p or q; p=T works)
        // Actually p=T so first clause is satisfied, r=T and ¬r fails
        // Wait: ¬r is Neg(r), and r=T, so ¬r is false. Second clause has only ¬r which is false.
        assert!(!cnf.eval(&a));
    }

    #[test]
    fn test_cnf_eval_satisfied() {
        let cnf = Cnf::new(vec![
            vec![Literal::positive("p"), Literal::positive("q")],
            vec![Literal::negative("r")],
        ]);
        let mut a = BTreeMap::new();
        a.insert(Var("p".into()), true);
        a.insert(Var("q".into()), false);
        a.insert(Var("r".into()), false);
        assert!(cnf.eval(&a));
    }

    #[test]
    fn test_tseitin_simple() {
        let f = and(atom("p"), atom("q"));
        let cnf = TseitinEncoder::tseitin_encode(&f);
        // Should have some clauses
        assert!(!cnf.clauses.is_empty());
    }

    #[test]
    fn test_tseitin_preserves_satisfiability() {
        let f = and(atom("p"), atom("q"));
        let cnf = TseitinEncoder::tseitin_encode(&f);
        // Should be satisfiable
        let mut a = BTreeMap::new();
        a.insert(Var("p".into()), true);
        a.insert(Var("q".into()), true);
        // Tseitin uses auxiliary vars; set them all true for satisfiability check
        for clause in &cnf.clauses {
            for lit in clause {
                if let Literal::Pos(v) = lit {
                    a.entry(v.clone()).or_insert(true);
                }
            }
        }
        assert!(cnf.eval(&a));
    }

    #[test]
    fn test_literal_negate() {
        let pos = Literal::positive("p");
        let neg = pos.negate();
        assert_eq!(neg, Literal::negative("p"));
        assert_eq!(neg.negate(), pos);
    }

    #[test]
    fn test_dnf_basic() {
        let f = or(atom("p"), atom("q"));
        let dnf = formula_to_dnf(&f);
        // p ∨ q → DNF: {p, q}
        assert!(!dnf.terms.is_empty());
    }

    #[test]
    fn test_de_morgan_cnf() {
        // ¬(p ∧ q) ≡ ¬p ∨ ¬q
        let f = not(and(atom("p"), atom("q")));
        let cnf = formula_to_cnf(&f);
        assert_eq!(cnf.clauses.len(), 1);
        assert_eq!(cnf.clauses[0].len(), 2);
    }
}
