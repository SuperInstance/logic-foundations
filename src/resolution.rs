//! Resolution refutation: clausal form, resolution rule

use crate::cnf::{Clause, Literal};
use crate::predicate::{Term, PredFormula};
use std::collections::BTreeMap;

/// A literal for resolution (uses Terms instead of just Vars)
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ResLiteral {
    Pos(String, Vec<Term>),
    Neg(String, Vec<Term>),
}

impl ResLiteral {
    pub fn negate(&self) -> ResLiteral {
        match self {
            ResLiteral::Pos(p, args) => ResLiteral::Neg(p.clone(), args.clone()),
            ResLiteral::Neg(p, args) => ResLiteral::Pos(p.clone(), args.clone()),
        }
    }

    pub fn predicate(&self) -> &str {
        match self {
            ResLiteral::Pos(p, _) | ResLiteral::Neg(p, _) => p,
        }
    }

    pub fn apply_substitution(&self, subst: &crate::predicate::Substitution) -> ResLiteral {
        match self {
            ResLiteral::Pos(p, args) => ResLiteral::Pos(p.clone(), args.iter().map(|t| subst.apply_to_term(t)).collect()),
            ResLiteral::Neg(p, args) => ResLiteral::Neg(p.clone(), args.iter().map(|t| subst.apply_to_term(t)).collect()),
        }
    }
}

/// A clause for resolution
pub type ResClause = Vec<ResLiteral>;

/// Result of a resolution step
#[derive(Debug, Clone)]
pub struct ResolutionStep {
    pub clause1: ResClause,
    pub clause2: ResClause,
    pub resolved_literal: ResLiteral,
    pub resolvent: ResClause,
    pub substitution: crate::predicate::Substitution,
}

/// Resolution prover
pub struct ResolutionProver {
    pub steps: Vec<ResolutionStep>,
}

impl ResolutionProver {
    pub fn new() -> Self {
        Self { steps: vec![] }
    }

    /// Attempt to prove a formula by resolution refutation.
    /// Input: set of clauses (assumed to be in CNF clausal form).
    /// Returns true if the empty clause can be derived (refutation successful).
    pub fn prove(&mut self, clauses: &[ResClause]) -> bool {
        let mut clause_set: Vec<ResClause> = clauses.to_vec();
        let mut new_clauses: Vec<ResClause> = Vec::new();

        // Simple resolution loop
        let mut changed = true;
        let mut iterations = 0;
        let max_iterations = 1000;

        while changed && iterations < max_iterations {
            changed = false;
            iterations += 1;

            let len = clause_set.len();
            for i in 0..len {
                for j in (i + 1)..len {
                    if let Some(resolvents) = self.resolve(&clause_set[i], &clause_set[j]) {
                        for resolvent in resolvents {
                            // Check for empty clause
                            if resolvent.resolvent.is_empty() {
                                self.steps.push(resolvent.clone());
                                return true;
                            }

                            // Check if this clause is new
                            if !clause_set.iter().any(|c| c == &resolvent.resolvent) &&
                               !new_clauses.iter().any(|c| c == &resolvent.resolvent) {
                                self.steps.push(resolvent.clone());
                                new_clauses.push(resolvent.resolvent);
                                changed = true;
                            }
                        }
                    }
                }
            }

            clause_set.extend(new_clauses.drain(..));
        }

        false
    }

    /// Try to resolve two clauses
    fn resolve(&mut self, c1: &ResClause, c2: &ResClause) -> Option<Vec<ResolutionStep>> {
        let mut results = Vec::new();

        for l1 in c1 {
            for l2 in c2 {
                // Try to resolve l1 with the complement of l2
                if l1.predicate() == l2.predicate() {
                    let (args1, args2, is_complement) = match (l1, l2) {
                        (ResLiteral::Pos(_, a1), ResLiteral::Neg(_, a2)) => (a1, a2, true),
                        (ResLiteral::Neg(_, a1), ResLiteral::Pos(_, a2)) => (a1, a2, true),
                        _ => (&vec![], &vec![], false),
                    };

                    if is_complement {
                        if let crate::predicate::UnificationResult::Success(subst) =
                            crate::predicate::unify_list(args1, args2) {
                            // Build resolvent
                            let mut resolvent = ResClause::new();
                            for lit in c1 {
                                if lit != l1 {
                                    resolvent.push(lit.apply_substitution(&subst));
                                }
                            }
                            for lit in c2 {
                                if lit != l2 {
                                    resolvent.push(lit.apply_substitution(&subst));
                                }
                            }
                            resolvent.sort();
                            resolvent.dedup();

                            results.push(ResolutionStep {
                                clause1: c1.clone(),
                                clause2: c2.clone(),
                                resolved_literal: l1.apply_substitution(&subst),
                                resolvent: resolvent.clone(),
                                substitution: subst,
                            });
                        }
                    }
                }
            }
        }

        if results.is_empty() { None } else { Some(results) }
    }
}

/// Convert propositional clauses to resolution clauses
pub fn prop_to_res_clauses(clauses: &[Clause]) -> Vec<ResClause> {
    clauses.iter().map(|clause| {
        clause.iter().map(|lit| match lit {
            Literal::Pos(v) => ResLiteral::Pos(v.0.clone(), vec![]),
            Literal::Neg(v) => ResLiteral::Neg(v.0.clone(), vec![]),
        }).collect()
    }).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cnf::Literal;

    #[test]
    fn test_simple_refutation() {
        // P, ¬P ∨ Q, ¬Q → derive empty clause
        let clauses: Vec<ResClause> = vec![
            vec![ResLiteral::Pos("P".to_string(), vec![])],
            vec![ResLiteral::Neg("P".to_string(), vec![]), ResLiteral::Pos("Q".to_string(), vec![])],
            vec![ResLiteral::Neg("Q".to_string(), vec![])],
        ];
        let mut prover = ResolutionProver::new();
        assert!(prover.prove(&clauses));
        assert!(!prover.steps.is_empty());
    }

    #[test]
    fn test_no_refutation() {
        // P, Q — no contradiction possible
        let clauses: Vec<ResClause> = vec![
            vec![ResLiteral::Pos("P".to_string(), vec![])],
            vec![ResLiteral::Pos("Q".to_string(), vec![])],
        ];
        let mut prover = ResolutionProver::new();
        assert!(!prover.prove(&clauses));
    }

    #[test]
    fn test_propositional_resolution() {
        // (P ∨ Q) ∧ (¬P ∨ Q) ∧ (P ∨ ¬Q) ∧ (¬P ∨ ¬Q) — contradiction
        let clauses: Vec<ResClause> = vec![
            vec![ResLiteral::Pos("P".to_string(), vec![]), ResLiteral::Pos("Q".to_string(), vec![])],
            vec![ResLiteral::Neg("P".to_string(), vec![]), ResLiteral::Pos("Q".to_string(), vec![])],
            vec![ResLiteral::Pos("P".to_string(), vec![]), ResLiteral::Neg("Q".to_string(), vec![])],
            vec![ResLiteral::Neg("P".to_string(), vec![]), ResLiteral::Neg("Q".to_string(), vec![])],
        ];
        let mut prover = ResolutionProver::new();
        assert!(prover.prove(&clauses));
    }

    #[test]
    fn test_predicate_resolution() {
        // P(a), ¬P(x) ∨ Q(x), ¬Q(a) → contradiction
        let clauses: Vec<ResClause> = vec![
            vec![ResLiteral::Pos("P".to_string(), vec![Term::Const("a".to_string())])],
            vec![ResLiteral::Neg("P".to_string(), vec![Term::Var("x".to_string())]),
                 ResLiteral::Pos("Q".to_string(), vec![Term::Var("x".to_string())])],
            vec![ResLiteral::Neg("Q".to_string(), vec![Term::Const("a".to_string())])],
        ];
        let mut prover = ResolutionProver::new();
        assert!(prover.prove(&clauses));
    }

    #[test]
    fn test_res_literal_negate() {
        let pos = ResLiteral::Pos("P".to_string(), vec![Term::Var("x".to_string())]);
        let neg = pos.negate();
        assert_eq!(neg, ResLiteral::Neg("P".to_string(), vec![Term::Var("x".to_string())]));
    }

    #[test]
    fn test_prop_to_res_conversion() {
        let clauses = vec![
            vec![Literal::positive("p"), Literal::negative("q")],
        ];
        let res = prop_to_res_clauses(&clauses);
        assert_eq!(res.len(), 1);
        assert_eq!(res[0].len(), 2);
    }
}
