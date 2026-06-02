//! Predicate logic: quantifiers, substitution, unification

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt;

/// A term in predicate logic
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Term {
    Var(String),
    Const(String),
    Func(String, Vec<Term>),
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Term::Var(s) => write!(f, "{}", s),
            Term::Const(s) => write!(f, "{}", s),
            Term::Func(name, args) => {
                write!(f, "{}(", name)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            }
        }
    }
}

/// A predicate logic formula
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PredFormula {
    Atom(String, Vec<Term>),           // P(x, y)
    Not(Box<PredFormula>),
    And(Box<PredFormula>, Box<PredFormula>),
    Or(Box<PredFormula>, Box<PredFormula>),
    Implies(Box<PredFormula>, Box<PredFormula>),
    Iff(Box<PredFormula>, Box<PredFormula>),
    Forall(String, Box<PredFormula>),  // ∀x. φ
    Exists(String, Box<PredFormula>),  // ∃x. φ
    Top,
    Bot,
}

impl PredFormula {
    /// Substitute a term for a variable
    pub fn substitute(&self, var: &str, replacement: &Term) -> PredFormula {
        match self {
            PredFormula::Atom(pred, args) => {
                PredFormula::Atom(pred.clone(), args.iter().map(|t| t.substitute(var, replacement)).collect())
            }
            PredFormula::Not(f) => PredFormula::Not(Box::new(f.substitute(var, replacement))),
            PredFormula::And(a, b) => PredFormula::And(
                Box::new(a.substitute(var, replacement)),
                Box::new(b.substitute(var, replacement)),
            ),
            PredFormula::Or(a, b) => PredFormula::Or(
                Box::new(a.substitute(var, replacement)),
                Box::new(b.substitute(var, replacement)),
            ),
            PredFormula::Implies(a, b) => PredFormula::Implies(
                Box::new(a.substitute(var, replacement)),
                Box::new(b.substitute(var, replacement)),
            ),
            PredFormula::Iff(a, b) => PredFormula::Iff(
                Box::new(a.substitute(var, replacement)),
                Box::new(b.substitute(var, replacement)),
            ),
            PredFormula::Forall(x, f) => {
                if x == var { self.clone() } // bound variable, don't substitute
                else { PredFormula::Forall(x.clone(), Box::new(f.substitute(var, replacement))) }
            }
            PredFormula::Exists(x, f) => {
                if x == var { self.clone() }
                else { PredFormula::Exists(x.clone(), Box::new(f.substitute(var, replacement))) }
            }
            PredFormula::Top => PredFormula::Top,
            PredFormula::Bot => PredFormula::Bot,
        }
    }

    /// Collect free variables
    pub fn free_vars(&self) -> Vec<String> {
        let mut vars = Vec::new();
        self.collect_free_vars(&mut vars, &mut Vec::new());
        vars.sort();
        vars.dedup();
        vars
    }

    fn collect_free_vars(&self, vars: &mut Vec<String>, bound: &mut Vec<String>) {
        match self {
            PredFormula::Atom(_, args) => {
                for arg in args {
                    arg.collect_vars(vars, bound);
                }
            }
            PredFormula::Not(f) => f.collect_free_vars(vars, bound),
            PredFormula::And(a, b) | PredFormula::Or(a, b) | PredFormula::Implies(a, b) | PredFormula::Iff(a, b) => {
                a.collect_free_vars(vars, bound);
                b.collect_free_vars(vars, bound);
            }
            PredFormula::Forall(x, f) | PredFormula::Exists(x, f) => {
                bound.push(x.clone());
                f.collect_free_vars(vars, bound);
                bound.pop();
            }
            PredFormula::Top | PredFormula::Bot => {}
        }
    }

    /// Negate the formula (push negation inward for Prenex normal form)
    pub fn negate(&self) -> PredFormula {
        PredFormula::Not(Box::new(self.clone()))
    }

    /// Is this formula ground (no free variables)?
    pub fn is_ground(&self) -> bool {
        self.free_vars().is_empty()
    }
}

impl Term {
    fn substitute(&self, var: &str, replacement: &Term) -> Term {
        match self {
            Term::Var(s) if s == var => replacement.clone(),
            Term::Var(_) | Term::Const(_) => self.clone(),
            Term::Func(name, args) => {
                Term::Func(name.clone(), args.iter().map(|t| t.substitute(var, replacement)).collect())
            }
        }
    }

    fn collect_vars(&self, vars: &mut Vec<String>, bound: &[String]) {
        match self {
            Term::Var(s) => {
                if !bound.contains(s) && !vars.contains(s) {
                    vars.push(s.clone());
                }
            }
            Term::Const(_) => {}
            Term::Func(_, args) => {
                for arg in args {
                    arg.collect_vars(vars, bound);
                }
            }
        }
    }
}

/// A substitution mapping variables to terms
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Substitution {
    pub map: BTreeMap<String, Term>,
}

impl Substitution {
    pub fn empty() -> Self {
        Self { map: BTreeMap::new() }
    }

    pub fn single(var: &str, term: Term) -> Self {
        let mut map = BTreeMap::new();
        map.insert(var.to_string(), term);
        Self { map }
    }

    /// Apply substitution to a term
    pub fn apply_to_term(&self, term: &Term) -> Term {
        match term {
            Term::Var(s) => self.map.get(s).cloned().unwrap_or_else(|| term.clone()),
            Term::Const(_) => term.clone(),
            Term::Func(name, args) => {
                Term::Func(name.clone(), args.iter().map(|t| self.apply_to_term(t)).collect())
            }
        }
    }

    /// Apply substitution to a formula
    pub fn apply_to_formula(&self, formula: &PredFormula) -> PredFormula {
        match formula {
            PredFormula::Atom(pred, args) => {
                PredFormula::Atom(pred.clone(), args.iter().map(|t| self.apply_to_term(t)).collect())
            }
            PredFormula::Not(f) => PredFormula::Not(Box::new(self.apply_to_formula(f))),
            PredFormula::And(a, b) => PredFormula::And(
                Box::new(self.apply_to_formula(a)),
                Box::new(self.apply_to_formula(b)),
            ),
            PredFormula::Or(a, b) => PredFormula::Or(
                Box::new(self.apply_to_formula(a)),
                Box::new(self.apply_to_formula(b)),
            ),
            PredFormula::Implies(a, b) => PredFormula::Implies(
                Box::new(self.apply_to_formula(a)),
                Box::new(self.apply_to_formula(b)),
            ),
            PredFormula::Iff(a, b) => PredFormula::Iff(
                Box::new(self.apply_to_formula(a)),
                Box::new(self.apply_to_formula(b)),
            ),
            PredFormula::Forall(x, f) => {
                let inner = if self.map.contains_key(x) {
                    // Don't substitute bound variable
                    let mut sub = self.clone();
                    sub.map.remove(x);
                    sub.apply_to_formula(f)
                } else {
                    self.apply_to_formula(f)
                };
                PredFormula::Forall(x.clone(), Box::new(inner))
            }
            PredFormula::Exists(x, f) => {
                let inner = if self.map.contains_key(x) {
                    let mut sub = self.clone();
                    sub.map.remove(x);
                    sub.apply_to_formula(f)
                } else {
                    self.apply_to_formula(f)
                };
                PredFormula::Exists(x.clone(), Box::new(inner))
            }
            PredFormula::Top => PredFormula::Top,
            PredFormula::Bot => PredFormula::Bot,
        }
    }

    /// Compose two substitutions: self ∘ other
    pub fn compose(&self, other: &Substitution) -> Substitution {
        let mut result = BTreeMap::new();
        for (v, t) in &other.map {
            result.insert(v.clone(), self.apply_to_term(t));
        }
        for (v, t) in &self.map {
            if !result.contains_key(v) {
                result.insert(v.clone(), t.clone());
            }
        }
        Substitution { map: result }
    }
}

/// Unification result
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnificationResult {
    Success(Substitution),
    Failure(String),
}

/// Unify two terms
pub fn unify(t1: &Term, t2: &Term) -> UnificationResult {
    unify_with_subst(t1, t2, &Substitution::empty())
}

fn unify_with_subst(t1: &Term, t2: &Term, subst: &Substitution) -> UnificationResult {
    let t1 = subst.apply_to_term(t1);
    let t2 = subst.apply_to_term(t2);

    if t1 == t2 {
        return UnificationResult::Success(subst.clone());
    }

    match (&t1, &t2) {
        (Term::Var(x), _) => UnificationResult::Success(apply_binding(x.clone(), t2, subst)),
        (_, Term::Var(y)) => UnificationResult::Success(apply_binding(y.clone(), t1, subst)),
        (Term::Func(f1, args1), Term::Func(f2, args2)) => {
            if f1 != f2 || args1.len() != args2.len() {
                return UnificationResult::Failure(format!("Cannot unify {} with {}", t1, t2));
            }
            let mut current_subst = subst.clone();
            for (a1, a2) in args1.iter().zip(args2.iter()) {
                match unify_with_subst(a1, a2, &current_subst) {
                    UnificationResult::Success(s) => current_subst = s,
                    UnificationResult::Failure(msg) => return UnificationResult::Failure(msg),
                }
            }
            UnificationResult::Success(current_subst)
        }
        _ => UnificationResult::Failure(format!("Cannot unify {} with {}", t1, t2)),
    }
}

fn apply_binding(var: String, term: Term, subst: &Substitution) -> Substitution {
    let mut new_map = subst.map.clone();
    new_map.insert(var, term);
    // Apply the new binding to all existing bindings
    let new_subst = Substitution { map: new_map };
    let mut result = BTreeMap::new();
    for (v, t) in &new_subst.map {
        result.insert(v.clone(), new_subst.apply_to_term(t));
    }
    Substitution { map: result }
}

/// Unify two lists of terms
pub fn unify_list(terms1: &[Term], terms2: &[Term]) -> UnificationResult {
    if terms1.len() != terms2.len() {
        return UnificationResult::Failure("Argument count mismatch".to_string());
    }
    let mut subst = Substitution::empty();
    for (t1, t2) in terms1.iter().zip(terms2.iter()) {
        match unify_with_subst(t1, t2, &subst) {
            UnificationResult::Success(s) => subst = s,
            UnificationResult::Failure(msg) => return UnificationResult::Failure(msg),
        }
    }
    UnificationResult::Success(subst)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_substitute_term() {
        let f = PredFormula::Atom("P".to_string(), vec![Term::Var("x".to_string())]);
        let result = f.substitute("x", &Term::Const("a".to_string()));
        assert_eq!(result, PredFormula::Atom("P".to_string(), vec![Term::Const("a".to_string())]));
    }

    #[test]
    fn test_substitute_bound_var() {
        // ∀x.P(x) — substituting x should be a no-op
        let f = PredFormula::Forall("x".to_string(), Box::new(
            PredFormula::Atom("P".to_string(), vec![Term::Var("x".to_string())])
        ));
        let result = f.substitute("x", &Term::Const("a".to_string()));
        assert_eq!(result, f); // unchanged
    }

    #[test]
    fn test_free_vars() {
        let f = PredFormula::Forall("x".to_string(), Box::new(
            PredFormula::Atom("P".to_string(), vec![
                Term::Var("x".to_string()),
                Term::Var("y".to_string()),
            ])
        ));
        let fv = f.free_vars();
        assert_eq!(fv, vec!["y".to_string()]);
    }

    #[test]
    fn test_free_vars_no_quantifier() {
        let f = PredFormula::Atom("P".to_string(), vec![
            Term::Var("x".to_string()),
            Term::Var("y".to_string()),
        ]);
        let fv = f.free_vars();
        assert_eq!(fv, vec!["x".to_string(), "y".to_string()]);
    }

    #[test]
    fn test_unify_same_var() {
        let t = Term::Var("x".to_string());
        let result = unify(&t, &t);
        assert!(matches!(result, UnificationResult::Success(_)));
    }

    #[test]
    fn test_unify_var_with_const() {
        let result = unify(&Term::Var("x".to_string()), &Term::Const("a".to_string()));
        match result {
            UnificationResult::Success(subst) => {
                assert_eq!(subst.map["x"], Term::Const("a".to_string()));
            }
            _ => panic!("Expected success"),
        }
    }

    #[test]
    fn test_unify_same_const() {
        let result = unify(&Term::Const("a".to_string()), &Term::Const("a".to_string()));
        assert!(matches!(result, UnificationResult::Success(_)));
    }

    #[test]
    fn test_unify_different_const() {
        let result = unify(&Term::Const("a".to_string()), &Term::Const("b".to_string()));
        assert!(matches!(result, UnificationResult::Failure(_)));
    }

    #[test]
    fn test_unify_functions() {
        // f(x) with f(a)
        let t1 = Term::Func("f".to_string(), vec![Term::Var("x".to_string())]);
        let t2 = Term::Func("f".to_string(), vec![Term::Const("a".to_string())]);
        let result = unify(&t1, &t2);
        match result {
            UnificationResult::Success(subst) => {
                assert_eq!(subst.map["x"], Term::Const("a".to_string()));
            }
            _ => panic!("Expected success"),
        }
    }

    #[test]
    fn test_unify_different_functions() {
        let t1 = Term::Func("f".to_string(), vec![Term::Var("x".to_string())]);
        let t2 = Term::Func("g".to_string(), vec![Term::Var("x".to_string())]);
        let result = unify(&t1, &t2);
        assert!(matches!(result, UnificationResult::Failure(_)));
    }

    #[test]
    fn test_unify_list() {
        let t1 = vec![Term::Var("x".to_string()), Term::Var("y".to_string())];
        let t2 = vec![Term::Const("a".to_string()), Term::Const("b".to_string())];
        let result = unify_list(&t1, &t2);
        match result {
            UnificationResult::Success(subst) => {
                assert_eq!(subst.map["x"], Term::Const("a".to_string()));
                assert_eq!(subst.map["y"], Term::Const("b".to_string()));
            }
            _ => panic!("Expected success"),
        }
    }

    #[test]
    fn test_substitution_compose() {
        let s1 = Substitution::single("y", Term::Const("b".to_string()));
        let s2 = Substitution::single("x", Term::Var("y".to_string()));
        let composed = s1.compose(&s2);
        assert_eq!(composed.map["x"], Term::Const("b".to_string()));
    }

    #[test]
    fn test_is_ground() {
        let ground = PredFormula::Atom("P".to_string(), vec![Term::Const("a".to_string())]);
        assert!(ground.is_ground());
        let not_ground = PredFormula::Atom("P".to_string(), vec![Term::Var("x".to_string())]);
        assert!(!not_ground.is_ground());
    }
}
