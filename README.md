# logic-foundations

Logic foundations in Rust. From propositions to proofs.

A Rust library for mathematical logic: propositional logic, predicate logic, automated reasoning (DPLL, resolution), natural deduction proofs, and Gödel numbering.

## What This Does

`logic-foundations` provides the core machinery of formal logic as composable Rust types and algorithms:

- **Propositional logic** — syntax trees, truth tables, tautology/satisfiability checking, entailment, equivalence.
- **Connectives** — truth-table definitions for all standard binary connectives (AND, OR, IMPLIES, IFF, NAND, NOR, XOR) with commutativity and duality.
- **CNF / DNF conversion** — negation normal form (NNF), distribution-based CNF, and **Tseitin encoding** for linear-size equisatisfiable CNF.
- **DPLL SAT solver** — unit propagation, pure literal elimination, backtracking search.
- **Resolution** — clausal resolution with unification for both propositional and predicate literals.
- **Predicate logic** — terms, quantifiers (∀, ∃), substitution (capture-avoiding), unification, and Robinson's unification algorithm.
- **Natural deduction** — proof terms as a typed λ-calculus (Curry-Howard correspondence) with full type-checking.
- **Gödel numbering** — encode propositional and predicate formulas as natural numbers via prime factorization.

## Key Idea

The crate treats logic as **data structures you can compute with**. Formulas are `enum` trees. Proofs are typed λ-terms. SAT solving returns satisfying assignments. Resolution produces explicit proof steps. This makes it possible to embed logical reasoning inside larger systems.

## Install

```toml
[dependencies]
logic-foundations = "0.1"
```

## Quick Start

### Propositional Logic

```rust
use logic_foundations::{atom, and, or, not, implies, Formula};

let p = atom("p");
let q = atom("q");

// Is (p ∧ q → p) a tautology?
let f = implies(and(p.clone(), q.clone()), p.clone());
assert!(f.is_tautology());

// De Morgan: ¬(p ∧ q) ≡ (¬p ∨ ¬q)
let f1 = not(and(atom("p"), atom("q")));
let f2 = or(not(atom("p")), not(atom("q")));
assert!(Formula::equivalent(&f1, &f2));
```

### SAT Solving (DPLL)

```rust
use logic_foundations::{Cnf, Literal, solve_sat, SatResult};

let cnf = Cnf::new(vec![
    vec![Literal::positive("p"), Literal::positive("q")],
    vec![Literal::negative("p"), Literal::positive("q")],
]);

match solve_sat(&cnf) {
    SatResult::Satisfiable(assignment) => { /* use assignment */ }
    SatResult::Unsatisfiable => { /* no solution */ }
}
```

### Predicate Logic & Unification

```rust
use logic_foundations::{Term, PredFormula, unify, Substitution};

let t1 = Term::Func("f".into(), vec![Term::Var("x".into())]);
let t2 = Term::Func("f".into(), vec![Term::Const("a".into())]);

if let UnificationResult::Success(subst) = unify(&t1, &t2) {
    assert_eq!(subst.map["x"], Term::Const("a".into()));
}
```

## API Reference

### `propositional` — Formula, Var, builders

| Item | Description |
|---|---|
| `Formula` | Enum: Atom, Not, And, Or, Implies, Iff, Top, Bot |
| `atom`, `not`, `and`, `or`, `implies`, `iff` | Builder functions |
| `Formula::truth_table()` | Exhaustive (assignment → result) pairs |
| `Formula::is_tautology()` | True under all assignments |
| `Formula::is_satisfiable()` | True under some assignment |
| `Formula::entails(other)` | `self → other` is a tautology |
| `Formula::equivalent(a, b)` | `a ↔ b` is a tautology |
| `Formula::substitute(var, replacement)` | Variable substitution |

### `connectives` — UnaryConnective, BinaryConnective

Truth-table evaluation for AND, OR, IMPLIES, IFF, NAND, NOR, XOR. Includes `is_commutative()`, `dual()`, and `TruthTableBuilder`.

### `cnf` — CNF, DNF, Tseitin Encoding

| Item | Description |
|---|---|
| `Literal` | Positive or negative variable |
| `Cnf` | Conjunction of clauses (disjunctions of literals) |
| `Dnf` | Disjunction of terms |
| `formula_to_cnf(f)` | Naïve NNF + distribution |
| `TseitinEncoder::tseitin_encode(f)` | Linear equisatisfiable CNF |
| `formula_to_dnf(f)` | Disjunctive normal form |

### `dpll` — DpllSolver

| Item | Description |
|---|---|
| `DpllSolver::new()` | Create solver (with pure literal elimination) |
| `solve(&Cnf)` | Returns `SatResult::Satisfiable(assignment)` or `Unsatisfiable` |
| `solve_sat(cnf)` | Convenience function |

### `predicate` — Term, PredFormula, Substitution

| Item | Description |
|---|---|
| `Term` | Var, Const, Func(name, args) |
| `PredFormula` | Atom, Not, And, Or, Implies, Iff, Forall, Exists, Top, Bot |
| `PredFormula::free_vars()` | Collect free variables |
| `PredFormula::substitute(var, term)` | Capture-avoiding substitution |
| `Substitution` | Variable → term mapping, with `compose()` |
| `unify(t1, t2)` | Robinson unification → `UnificationResult` |
| `unify_list(ts1, ts2)` | Unify parallel term lists |

### `resolution` — ResolutionProver

| Item | Description |
|---|---|
| `ResolutionProver::prove(&[ResClause])` | Refutation by resolution → `bool` |
| `prop_to_res_clauses(&[Clause])` | Convert propositional CNF clauses |

### `natural_deduction` — ProofTerm, ProofContext

| Item | Description |
|---|---|
| `ProofTerm` | Var, Abs, App, Pair, Fst, Snd, Inl, Inr, Case, Abort, Trivial |
| `ProofContext` | Manages assumptions; provides intro/elim rule builders |
| `type_check(ctx, term)` | Returns `Result<Formula, String>` |

### `godel` — Gödel Numbering

| Item | Description |
|---|---|
| `GodelEncoding` | Symbol table with standard codes (¬=1, ∨=2, →=3, ∀=4, ∧=5, ↔=6, ∃=7) |
| `encode_formula(enc, f)` | Propositional formula → Gödel number |
| `encode_pred_formula(enc, f)` | Predicate formula → Gödel number |
| `encode_sequence(&[u64])` | Sequence → prime-factorization Gödel number |
| `decode_sequence(godel_num, len)` | Inverse |
| `beta(b, c, i)` | Gödel's β function |

## How It Works

1. **Formulas as trees.** Both propositional and predicate formulas are recursive `enum` types, enabling pattern-matching traversals for evaluation, substitution, and transformation.

2. **CNF via NNF + distribution.** `formula_to_cnf` first converts to Negation Normal Form (pushing ¬ inward using De Morgan's laws), then distributes ∨ over ∧. This is exponential in the worst case.

3. **Tseitin encoding** avoids the exponential blowup by introducing auxiliary variables for each subformula, producing an *equisatisfiable* (not equivalent) CNF in linear size.

4. **DPLL** operates on the CNF clause list: unit propagation forces single-literal clauses, pure literal elimination assigns variables that appear in only one polarity, and backtracking search branches on remaining variables.

5. **Resolution** finds complementary literals (one positive, one negative) with matching predicates, unifies their arguments, and produces the resolvent. Refutation succeeds when the empty clause is derived.

6. **Natural deduction** uses the Curry-Howard correspondence: proofs are typed λ-terms (abstraction = →-intro, application = →-elim, pairs = ∧-intro, projections = ∧-elim, etc.). `type_check` is the proof checker.

7. **Gödel numbering** encodes formulas as natural numbers using prime factorization: the sequence [a₁, ..., aₙ] maps to 2^a₁ · 3^a₂ · ... · pₙ^aₙ. Each subformula gets its own Gödel number recursively.

## License

MIT OR Apache-2.0
