//! Natural deduction: proof terms, introduction/elimination rules

use serde::{Deserialize, Serialize};
use std::fmt;

/// Proof term representing a natural deduction proof
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProofTerm {
    /// A variable/assumption reference
    Var(String),
    /// Abstraction (assumption introduction): λx:A. t
    Abs(String, Box<Formula>, Box<ProofTerm>),
    /// Application (modus ponens / elimination)
    App(Box<ProofTerm>, Box<ProofTerm>),
    /// Pair (conjunction introduction)
    Pair(Box<ProofTerm>, Box<ProofTerm>),
    /// First projection (conjunction elimination)
    Fst(Box<ProofTerm>),
    /// Second projection (conjunction elimination)
    Snd(Box<ProofTerm>),
    /// Inl (disjunction introduction left)
    Inl(Box<ProofTerm>, Box<Formula>),
    /// Inr (disjunction introduction right)
    Inr(Box<ProofTerm>, Box<Formula>),
    /// Case analysis (disjunction elimination)
    Case(Box<ProofTerm>, String, Box<ProofTerm>, String, Box<ProofTerm>),
    /// Abort (false elimination)
    Abort(Box<ProofTerm>, Box<Formula>),
    /// Trivial (true introduction)
    Trivial,
}

/// Formula for natural deduction (simplified)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Formula {
    Atom(String),
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Top,
    Bot,
}

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Formula::Atom(s) => write!(f, "{}", s),
            Formula::Not(g) => write!(f, "¬{}", g),
            Formula::And(a, b) => write!(f, "({} ∧ {})", a, b),
            Formula::Or(a, b) => write!(f, "({} ∨ {})", a, b),
            Formula::Implies(a, b) => write!(f, "({} → {})", a, b),
            Formula::Top => write!(f, "⊤"),
            Formula::Bot => write!(f, "⊥"),
        }
    }
}

/// Natural deduction proof context
pub struct ProofContext {
    /// Assumptions: variable name → formula
    assumptions: Vec<(String, Formula)>,
}

impl ProofContext {
    pub fn new() -> Self {
        Self { assumptions: vec![] }
    }

    /// Add an assumption
    pub fn assume(&mut self, name: &str, formula: Formula) -> ProofTerm {
        self.assumptions.push((name.to_string(), formula.clone()));
        ProofTerm::Var(name.to_string())
    }

    /// → Introduction (Implication Introduction)
    /// Given a proof of B from assumption x:A, produce a proof of A → B
    pub fn implies_intro(&self, var: &str, formula_a: Formula, proof_b: ProofTerm) -> ProofTerm {
        ProofTerm::Abs(var.to_string(), Box::new(formula_a), Box::new(proof_b))
    }

    /// → Elimination (Modus Ponens)
    pub fn implies_elim(&self, proof_impl: ProofTerm, proof_a: ProofTerm) -> ProofTerm {
        ProofTerm::App(Box::new(proof_impl), Box::new(proof_a))
    }

    /// ∧ Introduction
    pub fn and_intro(&self, proof_a: ProofTerm, proof_b: ProofTerm) -> ProofTerm {
        ProofTerm::Pair(Box::new(proof_a), Box::new(proof_b))
    }

    /// ∧ Elimination (first)
    pub fn and_elim_left(&self, proof: ProofTerm) -> ProofTerm {
        ProofTerm::Fst(Box::new(proof))
    }

    /// ∧ Elimination (second)
    pub fn and_elim_right(&self, proof: ProofTerm) -> ProofTerm {
        ProofTerm::Snd(Box::new(proof))
    }

    /// ∨ Introduction (left)
    pub fn or_intro_left(&self, proof: ProofTerm, right_formula: Formula) -> ProofTerm {
        ProofTerm::Inl(Box::new(proof), Box::new(right_formula))
    }

    /// ∨ Introduction (right)
    pub fn or_intro_right(&self, proof: ProofTerm, left_formula: Formula) -> ProofTerm {
        ProofTerm::Inr(Box::new(proof), Box::new(left_formula))
    }

    /// ∨ Elimination (case analysis)
    pub fn or_elim(
        &self,
        proof: ProofTerm,
        var1: &str,
        proof_c1: ProofTerm,
        var2: &str,
        proof_c2: ProofTerm,
    ) -> ProofTerm {
        ProofTerm::Case(
            Box::new(proof),
            var1.to_string(),
            Box::new(proof_c1),
            var2.to_string(),
            Box::new(proof_c2),
        )
    }

    /// ⊥ Elimination (ex falso quodlibet)
    pub fn false_elim(&self, proof_false: ProofTerm, target: Formula) -> ProofTerm {
        ProofTerm::Abort(Box::new(proof_false), Box::new(target))
    }

    /// ⊤ Introduction
    pub fn true_intro(&self) -> ProofTerm {
        ProofTerm::Trivial
    }

    /// ¬ Introduction: assume A, derive ⊥, conclude ¬A
    pub fn not_intro(&self, var: &str, formula_a: Formula, proof_false: ProofTerm) -> ProofTerm {
        ProofTerm::Abs(var.to_string(), Box::new(formula_a), Box::new(proof_false))
    }

    /// Find the formula associated with a variable name
    pub fn lookup(&self, name: &str) -> Option<&Formula> {
        self.assumptions.iter().find(|(n, _)| n == name).map(|(_, f)| f)
    }
}

/// Type-check a proof term against a formula in a given context
pub fn type_check(ctx: &ProofContext, term: &ProofTerm) -> Result<Formula, String> {
    match term {
        ProofTerm::Var(name) => {
            ctx.lookup(name).cloned().ok_or_else(|| format!("Unbound variable: {}", name))
        }
        ProofTerm::Abs(var, ty, body) => {
            let mut inner_ctx = ProofContext::new();
            inner_ctx.assumptions = ctx.assumptions.clone();
            inner_ctx.assumptions.push((var.clone(), (**ty).clone()));
            let body_ty = type_check(&inner_ctx, body)?;
            Ok(Formula::Implies(Box::new((**ty).clone()), Box::new(body_ty)))
        }
        ProofTerm::App(func, arg) => {
            let func_ty = type_check(ctx, func)?;
            let arg_ty = type_check(ctx, arg)?;
            match func_ty {
                Formula::Implies(a, b) => {
                    if *a == arg_ty { Ok(*b) }
                    else { Err(format!("Argument type mismatch: expected {:?}, got {:?}", *a, arg_ty)) }
                }
                _ => Err(format!("Expected function type, got {:?}", func_ty)),
            }
        }
        ProofTerm::Pair(a, b) => {
            let ta = type_check(ctx, a)?;
            let tb = type_check(ctx, b)?;
            Ok(Formula::And(Box::new(ta), Box::new(tb)))
        }
        ProofTerm::Fst(p) => {
            let t = type_check(ctx, p)?;
            match t {
                Formula::And(a, _) => Ok(*a),
                _ => Err(format!("Expected conjunction, got {:?}", t)),
            }
        }
        ProofTerm::Snd(p) => {
            let t = type_check(ctx, p)?;
            match t {
                Formula::And(_, b) => Ok(*b),
                _ => Err(format!("Expected conjunction, got {:?}", t)),
            }
        }
        ProofTerm::Inl(proof, right) => {
            let t = type_check(ctx, proof)?;
            Ok(Formula::Or(Box::new(t), Box::new((**right).clone())))
        }
        ProofTerm::Inr(proof, left) => {
            let t = type_check(ctx, proof)?;
            Ok(Formula::Or(Box::new((**left).clone()), Box::new(t)))
        }
        ProofTerm::Case(scrut, v1, c1, v2, c2) => {
            let scrut_ty = type_check(ctx, scrut)?;
            let (a, b) = match scrut_ty {
                Formula::Or(a, b) => (a, b),
                _ => return Err(format!("Expected disjunction, got {:?}", scrut_ty)),
            };

            let mut ctx1 = ProofContext::new();
            ctx1.assumptions = ctx.assumptions.clone();
            ctx1.assumptions.push((v1.clone(), *a));
            let c1_ty = type_check(&ctx1, c1)?;

            let mut ctx2 = ProofContext::new();
            ctx2.assumptions = ctx.assumptions.clone();
            ctx2.assumptions.push((v2.clone(), *b));
            let c2_ty = type_check(&ctx2, c2)?;

            if c1_ty == c2_ty { Ok(c1_ty) }
            else { Err(format!("Case branches have different types: {:?} vs {:?}", c1_ty, c2_ty)) }
        }
        ProofTerm::Abort(proof, target) => {
            let t = type_check(ctx, proof)?;
            match t {
                Formula::Bot => Ok((**target).clone()),
                _ => Err(format!("Expected ⊥, got {:?}", t)),
            }
        }
        ProofTerm::Trivial => Ok(Formula::Top),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn atom(s: &str) -> Formula {
        Formula::Atom(s.to_string())
    }

    #[test]
    fn test_modus_ponens() {
        let mut ctx = ProofContext::new();
        // Prove: (A → A) applied to proof of A gives A
        // identity: λx:A. x : A → A
        let identity = ctx.implies_intro("x", atom("A"), ProofTerm::Var("x".to_string()));
        // Assume we have A
        let proof_a = ctx.assume("proof_a", atom("A"));
        let result = ctx.implies_elim(identity, proof_a);
        let mut check_ctx = ProofContext::new();
        check_ctx.assume("proof_a", atom("A"));
        let ty = type_check(&check_ctx, &result).unwrap();
        assert_eq!(ty, atom("A"));
    }

    #[test]
    fn test_and_intro_elim() {
        let mut ctx = ProofContext::new();
        let proof_a = ctx.assume("a", atom("A"));
        let proof_b = ctx.assume("b", atom("B"));
        let pair = ctx.and_intro(proof_a, proof_b);
        let left = ctx.and_elim_left(pair.clone());
        let right = ctx.and_elim_right(pair);

        let mut check_ctx = ProofContext::new();
        check_ctx.assume("a", atom("A"));
        check_ctx.assume("b", atom("B"));
        assert_eq!(type_check(&check_ctx, &left).unwrap(), atom("A"));
        assert_eq!(type_check(&check_ctx, &right).unwrap(), atom("B"));
    }

    #[test]
    fn test_identity_function() {
        // λx:A. x : A → A
        let proof = ProofTerm::Abs("x".to_string(), Box::new(atom("A")), Box::new(ProofTerm::Var("x".to_string())));
        let ty = type_check(&ProofContext::new(), &proof).unwrap();
        assert_eq!(ty, Formula::Implies(Box::new(atom("A")), Box::new(atom("A"))));
    }

    #[test]
    fn test_true_intro() {
        let proof = ProofTerm::Trivial;
        let ty = type_check(&ProofContext::new(), &proof).unwrap();
        assert_eq!(ty, Formula::Top);
    }

    #[test]
    fn test_or_intro() {
        let mut ctx = ProofContext::new();
        let proof_a = ctx.assume("a", atom("A"));
        let or_proof = ctx.or_intro_left(proof_a, atom("B"));
        let mut check_ctx = ProofContext::new();
        check_ctx.assume("a", atom("A"));
        let ty = type_check(&check_ctx, &or_proof).unwrap();
        assert_eq!(ty, Formula::Or(Box::new(atom("A")), Box::new(atom("B"))));
    }

    #[test]
    fn test_type_check_unbound_var() {
        let result = type_check(&ProofContext::new(), &ProofTerm::Var("x".to_string()));
        assert!(result.is_err());
    }

    #[test]
    fn test_type_check_app_not_function() {
        let mut ctx = ProofContext::new();
        let proof_a = ctx.assume("a", atom("A"));
        let result = type_check(&ctx, &ProofTerm::App(Box::new(proof_a), Box::new(ProofTerm::Trivial)));
        assert!(result.is_err());
    }

    #[test]
    fn test_complex_proof() {
        // Prove: A → B → A (const combinator)
        // λx:A. λy:B. x
        let proof = ProofTerm::Abs(
            "x".to_string(),
            Box::new(atom("A")),
            Box::new(ProofTerm::Abs(
                "y".to_string(),
                Box::new(atom("B")),
                Box::new(ProofTerm::Var("x".to_string())),
            )),
        );
        let ty = type_check(&ProofContext::new(), &proof).unwrap();
        assert_eq!(ty, Formula::Implies(
            Box::new(atom("A")),
            Box::new(Formula::Implies(Box::new(atom("B")), Box::new(atom("A")))),
        ));
    }

    #[test]
    fn test_false_elim() {
        let mut ctx = ProofContext::new();
        let proof_bot = ctx.assume("f", Formula::Bot);
        let result = ctx.false_elim(proof_bot, atom("C"));
        let mut check = ProofContext::new();
        check.assume("f", Formula::Bot);
        let ty = type_check(&check, &result).unwrap();
        assert_eq!(ty, atom("C"));
    }
}
