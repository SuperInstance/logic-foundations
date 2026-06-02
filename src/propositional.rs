//! Propositional logic: syntax, truth tables, satisfiability

use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

/// A propositional variable, represented by a string name.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Var(pub String);

/// Propositional formula
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Formula {
    Atom(Var),
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Iff(Box<Formula>, Box<Formula>),
    Top,  // ⊤ always true
    Bot,  // ⊥ always false
}

impl Formula {
    /// Collect all variables in the formula.
    pub fn variables(&self) -> BTreeSet<Var> {
        match self {
            Formula::Atom(v) => {
                let mut s = BTreeSet::new();
                s.insert(v.clone());
                s
            }
            Formula::Not(f) => f.variables(),
            Formula::And(a, b) | Formula::Or(a, b) | Formula::Implies(a, b) | Formula::Iff(a, b) => {
                let mut s = a.variables();
                s.extend(b.variables());
                s
            }
            Formula::Top | Formula::Bot => BTreeSet::new(),
        }
    }

    /// Evaluate the formula under a given truth assignment.
    pub fn eval(&self, assignment: &BTreeMap<Var, bool>) -> bool {
        match self {
            Formula::Atom(v) => *assignment.get(v).unwrap_or(&false),
            Formula::Not(f) => !f.eval(assignment),
            Formula::And(a, b) => a.eval(assignment) && b.eval(assignment),
            Formula::Or(a, b) => a.eval(assignment) || b.eval(assignment),
            Formula::Implies(a, b) => !a.eval(assignment) || b.eval(assignment),
            Formula::Iff(a, b) => a.eval(assignment) == b.eval(assignment),
            Formula::Top => true,
            Formula::Bot => false,
        }
    }

    /// Generate the full truth table for this formula.
    /// Returns a vector of (assignment, result) pairs.
    pub fn truth_table(&self) -> Vec<(BTreeMap<Var, bool>, bool)> {
        let vars: Vec<Var> = self.variables().into_iter().collect();
        let n = vars.len();
        let mut table = Vec::new();
        for bits in 0..(1u32 << n) {
            let mut assignment = BTreeMap::new();
            for (i, v) in vars.iter().enumerate() {
                assignment.insert(v.clone(), (bits >> i) & 1 == 1);
            }
            let result = self.eval(&assignment);
            table.push((assignment, result));
        }
        table
    }

    /// Is the formula a tautology (true under all assignments)?
    pub fn is_tautology(&self) -> bool {
        self.truth_table().iter().all(|(_, r)| *r)
    }

    /// Is the formula satisfiable (true under some assignment)?
    pub fn is_satisfiable(&self) -> bool {
        self.truth_table().iter().any(|(_, r)| *r)
    }

    /// Is the formula a contradiction (false under all assignments)?
    pub fn is_contradiction(&self) -> bool {
        !self.is_satisfiable()
    }

    /// Check logical entailment: does this formula entail another?
    pub fn entails(&self, other: &Formula) -> bool {
        Formula::Implies(Box::new(self.clone()), Box::new(other.clone())).is_tautology()
    }

    /// Check logical equivalence of two formulas.
    pub fn equivalent(other: &Formula, other2: &Formula) -> bool {
        Formula::Iff(Box::new(other.clone()), Box::new(other2.clone())).is_tautology()
    }

    /// Negate the formula.
    pub fn negate(&self) -> Formula {
        Formula::Not(Box::new(self.clone()))
    }

    /// Substitute a variable with another formula.
    pub fn substitute(&self, var: &Var, replacement: &Formula) -> Formula {
        match self {
            Formula::Atom(v) if v == var => replacement.clone(),
            Formula::Atom(v) => Formula::Atom(v.clone()),
            Formula::Not(f) => Formula::Not(Box::new(f.substitute(var, replacement))),
            Formula::And(a, b) => Formula::And(
                Box::new(a.substitute(var, replacement)),
                Box::new(b.substitute(var, replacement)),
            ),
            Formula::Or(a, b) => Formula::Or(
                Box::new(a.substitute(var, replacement)),
                Box::new(b.substitute(var, replacement)),
            ),
            Formula::Implies(a, b) => Formula::Implies(
                Box::new(a.substitute(var, replacement)),
                Box::new(b.substitute(var, replacement)),
            ),
            Formula::Iff(a, b) => Formula::Iff(
                Box::new(a.substitute(var, replacement)),
                Box::new(b.substitute(var, replacement)),
            ),
            Formula::Top => Formula::Top,
            Formula::Bot => Formula::Bot,
        }
    }
}

/// Helper to build an atom
pub fn atom(name: &str) -> Formula {
    Formula::Atom(Var(name.to_string()))
}

/// Helper to build negation
pub fn not(f: Formula) -> Formula {
    Formula::Not(Box::new(f))
}

/// Helper to build conjunction
pub fn and(a: Formula, b: Formula) -> Formula {
    Formula::And(Box::new(a), Box::new(b))
}

/// Helper to build disjunction
pub fn or(a: Formula, b: Formula) -> Formula {
    Formula::Or(Box::new(a), Box::new(b))
}

/// Helper to build implication
pub fn implies(a: Formula, b: Formula) -> Formula {
    Formula::Implies(Box::new(a), Box::new(b))
}

/// Helper to build biconditional
pub fn iff(a: Formula, b: Formula) -> Formula {
    Formula::Iff(Box::new(a), Box::new(b))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_atom_eval() {
        let p = atom("p");
        let mut assignment = BTreeMap::new();
        assignment.insert(Var("p".into()), true);
        assert!(p.eval(&assignment));
    }

    #[test]
    fn test_not_eval() {
        let f = not(atom("p"));
        let mut a = BTreeMap::new();
        a.insert(Var("p".into()), true);
        assert!(!f.eval(&a));
        a.insert(Var("p".into()), false);
        assert!(f.eval(&a));
    }

    #[test]
    fn test_and_truth_table() {
        let f = and(atom("p"), atom("q"));
        let tt = f.truth_table();
        assert_eq!(tt.len(), 4);
        let true_count = tt.iter().filter(|(_, r)| *r).count();
        assert_eq!(true_count, 1); // only p=T, q=T
    }

    #[test]
    fn test_or_truth_table() {
        let f = or(atom("p"), atom("q"));
        let tt = f.truth_table();
        let true_count = tt.iter().filter(|(_, r)| *r).count();
        assert_eq!(true_count, 3);
    }

    #[test]
    fn test_implies_truth_table() {
        let f = implies(atom("p"), atom("q"));
        let tt = f.truth_table();
        let true_count = tt.iter().filter(|(_, r)| *r).count();
        assert_eq!(true_count, 3); // false only when p=T, q=F
    }

    #[test]
    fn test_iff_truth_table() {
        let f = iff(atom("p"), atom("q"));
        let tt = f.truth_table();
        let true_count = tt.iter().filter(|(_, r)| *r).count();
        assert_eq!(true_count, 2);
    }

    #[test]
    fn test_tautology() {
        // p ∨ ¬p is a tautology
        let f = or(atom("p"), not(atom("p")));
        assert!(f.is_tautology());
    }

    #[test]
    fn test_contradiction() {
        // p ∧ ¬p is a contradiction
        let f = and(atom("p"), not(atom("p")));
        assert!(f.is_contradiction());
    }

    #[test]
    fn test_satisfiable() {
        let f = and(atom("p"), not(atom("q")));
        assert!(f.is_satisfiable());
    }

    #[test]
    fn test_equivalence() {
        // ¬(p ∧ q) ≡ (¬p ∨ ¬q) — De Morgan
        let f1 = not(and(atom("p"), atom("q")));
        let f2 = or(not(atom("p")), not(atom("q")));
        assert!(Formula::equivalent(&f1, &f2));
    }

    #[test]
    fn test_entailment() {
        // p ∧ q entails p
        let f1 = and(atom("p"), atom("q"));
        let f2 = atom("p");
        assert!(f1.entails(&f2));
    }

    #[test]
    fn test_substitute() {
        let f = and(atom("p"), atom("q"));
        let subbed = f.substitute(&Var("p".into()), &atom("r"));
        assert_eq!(subbed, and(atom("r"), atom("q")));
    }

    #[test]
    fn test_top_bot() {
        assert!(Formula::Top.is_tautology());
        assert!(Formula::Bot.is_contradiction());
    }
}
