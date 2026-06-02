//! DPLL SAT solver with unit propagation and backtracking

use crate::cnf::{Cnf, Clause, Literal};
use crate::propositional::Var;
use std::collections::BTreeMap;

/// Result of SAT solving
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SatResult {
    Satisfiable(BTreeMap<Var, bool>),
    Unsatisfiable,
}

/// DPLL SAT solver
pub struct DpllSolver {
    /// Whether to use pure literal elimination
    pub use_pure_literal: bool,
}

impl DpllSolver {
    pub fn new() -> Self {
        Self { use_pure_literal: true }
    }

    /// Solve the SAT problem for a CNF formula
    pub fn solve(&self, cnf: &Cnf) -> SatResult {
        let mut assignment = BTreeMap::new();
        let mut clauses = cnf.clauses.clone();
        if self.dpll(&mut clauses, &mut assignment) {
            SatResult::Satisfiable(assignment)
        } else {
            SatResult::Unsatisfiable
        }
    }

    /// Solve SAT for a propositional formula (converts to CNF internally)
    pub fn solve_formula(&self, cnf: &Cnf) -> SatResult {
        self.solve(cnf)
    }

    fn dpll(&self, clauses: &mut Vec<Clause>, assignment: &mut BTreeMap<Var, bool>) -> bool {
        // Unit propagation
        loop {
            let simplified = self.simplify(clauses, assignment);
            if !simplified {
                return false; // conflict
            }
            if let Some(unit) = self.find_unit_clause(clauses) {
                assignment.insert(unit.0.clone(), unit.1);
                continue;
            }
            break;
        }

        // Check if all clauses are satisfied
        if clauses.is_empty() {
            return true;
        }

        // Check for empty clause
        if clauses.iter().any(|c| c.is_empty()) {
            return false;
        }

        // Pure literal elimination
        if self.use_pure_literal {
            if let Some((var, val)) = self.find_pure_literal(clauses) {
                assignment.insert(var, val);
                let simplified = self.simplify(clauses, assignment);
                return simplified && self.dpll(clauses, assignment);
            }
        }

        // Choose a variable to branch on
        if let Some(var) = self.choose_variable(clauses) {
            let mut clauses_copy = clauses.clone();
            let mut assignment_copy = assignment.clone();

            // Try true
            assignment.insert(var.clone(), true);
            let mut clauses_true = clauses.clone();
            if self.simplify(&mut clauses_true, assignment) && self.dpll(&mut clauses_true, assignment) {
                *clauses = clauses_true;
                return true;
            }

            // Try false
            *assignment = assignment_copy;
            assignment.insert(var.clone(), false);
            let mut clauses_false = clauses_copy.clone();
            if self.simplify(&mut clauses_false, assignment) && self.dpll(&mut clauses_false, assignment) {
                *clauses = clauses_false;
                return true;
            }

            false
        } else {
            clauses.is_empty()
        }
    }

    /// Simplify clauses given current assignment. Returns false on conflict.
    fn simplify(&self, clauses: &mut Vec<Clause>, assignment: &BTreeMap<Var, bool>) -> bool {
        // Remove satisfied clauses and false literals
        let mut i = 0;
        while i < clauses.len() {
            let mut satisfied = false;
            let mut j = 0;
            while j < clauses[i].len() {
                let lit_val = match &clauses[i][j] {
                    Literal::Pos(v) => assignment.get(v).copied(),
                    Literal::Neg(v) => assignment.get(v).map(|b| !b),
                };
                match lit_val {
                    Some(true) => { satisfied = true; break; }
                    Some(false) => { clauses[i].remove(j); }
                    None => { j += 1; }
                }
            }
            if satisfied {
                clauses.remove(i);
            } else if clauses[i].is_empty() {
                return false; // empty clause = conflict
            } else {
                i += 1;
            }
        }
        true
    }

    /// Find a unit clause (clause with exactly one literal)
    fn find_unit_clause(&self, clauses: &[Clause]) -> Option<(Var, bool)> {
        for clause in clauses {
            if clause.len() == 1 {
                return match &clause[0] {
                    Literal::Pos(v) => Some((v.clone(), true)),
                    Literal::Neg(v) => Some((v.clone(), false)),
                };
            }
        }
        None
    }

    /// Find a pure literal (appears with only one polarity)
    fn find_pure_literal(&self, clauses: &[Clause]) -> Option<(Var, bool)> {
        let mut positive: BTreeMap<Var, bool> = BTreeMap::new();
        let mut negative: BTreeMap<Var, bool> = BTreeMap::new();

        for clause in clauses {
            for lit in clause {
                match lit {
                    Literal::Pos(v) => { positive.insert(v.clone(), true); }
                    Literal::Neg(v) => { negative.insert(v.clone(), true); }
                }
            }
        }

        for (v, _) in &positive {
            if !negative.contains_key(v) {
                return Some((v.clone(), true));
            }
        }
        for (v, _) in &negative {
            if !positive.contains_key(v) {
                return Some((v.clone(), false));
            }
        }
        None
    }

    /// Choose next variable to branch on (first unassigned variable found)
    fn choose_variable(&self, clauses: &[Clause]) -> Option<Var> {
        for clause in clauses {
            for lit in clause {
                return Some(lit.var().clone());
            }
        }
        None
    }
}

/// Convenience function: solve a CNF formula
pub fn solve_sat(cnf: &Cnf) -> SatResult {
    DpllSolver::new().solve(cnf)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cnf::Literal;

    #[test]
    fn test_simple_satisfiable() {
        // {{p}}
        let cnf = Cnf::new(vec![vec![Literal::positive("p")]]);
        let result = solve_sat(&cnf);
        assert!(matches!(result, SatResult::Satisfiable(_)));
    }

    #[test]
    fn test_simple_unsatisfiable() {
        // {{p}, {¬p}}
        let cnf = Cnf::new(vec![
            vec![Literal::positive("p")],
            vec![Literal::negative("p")],
        ]);
        let result = solve_sat(&cnf);
        assert_eq!(result, SatResult::Unsatisfiable);
    }

    #[test]
    fn test_two_var_satisfiable() {
        // {{p, q}, {¬p, q}, {p, ¬q}}
        let cnf = Cnf::new(vec![
            vec![Literal::positive("p"), Literal::positive("q")],
            vec![Literal::negative("p"), Literal::positive("q")],
            vec![Literal::positive("p"), Literal::negative("q")],
        ]);
        let result = solve_sat(&cnf);
        assert!(matches!(result, SatResult::Satisfiable(_)));
    }

    #[test]
    fn test_empty_cnf_satisfiable() {
        // Empty CNF = trivially satisfiable
        let cnf = Cnf::new(vec![]);
        let result = solve_sat(&cnf);
        assert!(matches!(result, SatResult::Satisfiable(_)));
    }

    #[test]
    fn test_empty_clause_unsatisfiable() {
        // {{}} = unsatisfiable
        let cnf = Cnf::new(vec![vec![]]);
        let result = solve_sat(&cnf);
        assert_eq!(result, SatResult::Unsatisfiable);
    }

    #[test]
    fn test_unit_propagation() {
        // {{p}, {¬p, q}} → unit propagate p=true → {q} → q=true
        let cnf = Cnf::new(vec![
            vec![Literal::positive("p")],
            vec![Literal::negative("p"), Literal::positive("q")],
        ]);
        let result = solve_sat(&cnf);
        if let SatResult::Satisfiable(assignment) = result {
            assert_eq!(assignment[&Var("p".into())], true);
            assert_eq!(assignment[&Var("q".into())], true);
        } else {
            panic!("Expected satisfiable");
        }
    }

    #[test]
    fn test_pure_literal() {
        // {{p, q}, {¬p, q}} → q is pure positive, set q=true
        let cnf = Cnf::new(vec![
            vec![Literal::positive("p"), Literal::positive("q")],
            vec![Literal::negative("p"), Literal::positive("q")],
        ]);
        let result = solve_sat(&cnf);
        assert!(matches!(result, SatResult::Satisfiable(_)));
    }

    #[test]
    fn test_three_sat() {
        // Classic 3-SAT: (p ∨ q ∨ r) ∧ (¬p ∨ q ∨ r) ∧ (p ∨ ¬q ∨ r)
        let cnf = Cnf::new(vec![
            vec![Literal::positive("p"), Literal::positive("q"), Literal::positive("r")],
            vec![Literal::negative("p"), Literal::positive("q"), Literal::positive("r")],
            vec![Literal::positive("p"), Literal::negative("q"), Literal::positive("r")],
        ]);
        let result = solve_sat(&cnf);
        assert!(matches!(result, SatResult::Satisfiable(_)));
    }

    #[test]
    fn test_backtracking() {
        // A formula that requires backtracking:
        // (p ∨ q) ∧ (p ∨ ¬q) ∧ (¬p ∨ q) ∧ (¬p ∨ ¬q) ... actually this might be satisfiable
        // Let's use: (p ∨ q) ∧ (¬p ∨ q) ∧ (p ∨ ¬q) ∧ (¬p ∨ ¬q)
        // This forces q=true (from 1,2) and q=false (from 3,4)... no it's not
        // Actually: all combos checked, no solution exists when p,q are both constrained
        // Let's verify: p=F,q=F: fails clause 1. p=F,q=T: fails clause 3. p=T,q=F: fails clause 2. p=T,q=T: fails clause 4.
        // UNSAT!
        let cnf = Cnf::new(vec![
            vec![Literal::positive("p"), Literal::positive("q")],
            vec![Literal::negative("p"), Literal::positive("q")],
            vec![Literal::positive("p"), Literal::negative("q")],
            vec![Literal::negative("p"), Literal::negative("q")],
        ]);
        let result = solve_sat(&cnf);
        assert_eq!(result, SatResult::Unsatisfiable);
    }

    #[test]
    fn test_large_satisfiable() {
        // Many variables, but satisfiable
        let mut clauses = vec![];
        for i in 0..10 {
            clauses.push(vec![
                Literal::positive(&format!("x{}", i)),
                Literal::positive(&format!("x{}", (i + 1) % 10)),
            ]);
        }
        let cnf = Cnf::new(clauses);
        let result = solve_sat(&cnf);
        assert!(matches!(result, SatResult::Satisfiable(_)));
    }

    #[test]
    fn test_result_assignment_valid() {
        let cnf = Cnf::new(vec![
            vec![Literal::positive("a"), Literal::negative("b")],
            vec![Literal::negative("a"), Literal::positive("c")],
            vec![Literal::positive("b"), Literal::positive("c")],
        ]);
        let result = solve_sat(&cnf);
        if let SatResult::Satisfiable(assignment) = result {
            assert!(cnf.eval(&assignment));
        } else {
            panic!("Expected satisfiable");
        }
    }
}
