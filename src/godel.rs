//! Gödel numbering: encode formulas as natural numbers

use crate::propositional::{Formula, Var};
use crate::predicate::{Term, PredFormula};
use std::collections::BTreeMap;

/// Gödel numbering configuration
pub struct GodelEncoding {
    /// Symbol table: symbol → code
    symbol_codes: BTreeMap<String, u64>,
    next_code: u64,
}

impl GodelEncoding {
    pub fn new() -> Self {
        let mut enc = Self {
            symbol_codes: BTreeMap::new(),
            next_code: 1,
        };
        // Assign standard Gödel codes
        enc.assign_standard_codes();
        enc
    }

    fn assign_standard_codes(&mut self) {
        // Standard encoding:
        // 1: ¬, 2: ∨, 3: →, 4: ∀, 5: ∧, 6: ↔, 7: ∃
        // 7+k: variable v_k
        // Variables get codes starting from 8
        self.symbol_codes.insert("¬".to_string(), 1);
        self.symbol_codes.insert("∨".to_string(), 2);
        self.symbol_codes.insert("→".to_string(), 3);
        self.symbol_codes.insert("∀".to_string(), 4);
        self.symbol_codes.insert("∧".to_string(), 5);
        self.symbol_codes.insert("↔".to_string(), 6);
        self.symbol_codes.insert("∃".to_string(), 7);
        self.next_code = 8;
    }

    /// Get or assign a code for a symbol
    pub fn code_for(&mut self, symbol: &str) -> u64 {
        if let Some(&code) = self.symbol_codes.get(symbol) {
            code
        } else {
            let code = self.next_code;
            self.next_code += 1;
            self.symbol_codes.insert(symbol.to_string(), code);
            code
        }
    }

    /// Get the symbol for a code
    pub fn symbol_for_code(&self, code: u64) -> Option<&str> {
        self.symbol_codes.iter().find(|(_, &c)| c == code).map(|(s, _)| s.as_str())
    }
}

/// Encode a sequence of numbers using prime factorization (Gödel's β function approach)
/// The Gödel number of a sequence [a1, a2, ..., an] is:
/// 2^a1 * 3^a2 * 5^a3 * ... * p_n^a_n
pub fn encode_sequence(nums: &[u64]) -> u64 {
    let primes = first_n_primes(nums.len());
    let mut result: u64 = 1;
    for (i, &num) in nums.iter().enumerate() {
        result = result.saturating_mul(primes[i].saturating_pow(num as u32));
    }
    // For sequences with large numbers, we cap at u64 max
    // In practice, use BigInt for real Gödel numbering
    result
}

/// Decode a Gödel number back to a sequence of given length
pub fn decode_sequence(godel_num: u64, len: usize) -> Vec<u64> {
    let primes = first_n_primes(len);
    let mut remaining = godel_num;
    let mut result = Vec::new();

    for p in &primes {
        let mut count: u64 = 0;
        while remaining % p == 0 && remaining > 0 {
            count += 1;
            remaining /= p;
        }
        result.push(count);
    }

    result
}

/// Generate the first n prime numbers
pub fn first_n_primes(n: usize) -> Vec<u64> {
    if n == 0 { return vec![]; }
    let mut primes = vec![2u64];
    let mut candidate = 3u64;
    while primes.len() < n {
        if primes.iter().all(|&p| candidate % p != 0) {
            primes.push(candidate);
        }
        candidate += 1;
    }
    primes
}

/// Encode a propositional formula as a Gödel number
pub fn encode_formula(enc: &mut GodelEncoding, f: &Formula) -> u64 {
    match f {
        Formula::Atom(Var(name)) => {
            let code = enc.code_for(name);
            encode_sequence(&[code])
        }
        Formula::Not(inner) => {
            let not_code = enc.code_for("¬");
            let inner_code = encode_formula(enc, inner);
            encode_sequence(&[not_code, inner_code])
        }
        Formula::And(a, b) => {
            let and_code = enc.code_for("∧");
            let a_code = encode_formula(enc, a);
            let b_code = encode_formula(enc, b);
            encode_sequence(&[and_code, a_code, b_code])
        }
        Formula::Or(a, b) => {
            let or_code = enc.code_for("∨");
            let a_code = encode_formula(enc, a);
            let b_code = encode_formula(enc, b);
            encode_sequence(&[or_code, a_code, b_code])
        }
        Formula::Implies(a, b) => {
            let imp_code = enc.code_for("→");
            let a_code = encode_formula(enc, a);
            let b_code = encode_formula(enc, b);
            encode_sequence(&[imp_code, a_code, b_code])
        }
        Formula::Iff(a, b) => {
            let iff_code = enc.code_for("↔");
            let a_code = encode_formula(enc, a);
            let b_code = encode_formula(enc, b);
            encode_sequence(&[iff_code, a_code, b_code])
        }
        Formula::Top => {
            let code = enc.code_for("⊤");
            encode_sequence(&[code])
        }
        Formula::Bot => {
            let code = enc.code_for("⊥");
            encode_sequence(&[code])
        }
    }
}

/// Encode a predicate logic term as a Gödel number
pub fn encode_term(enc: &mut GodelEncoding, t: &Term) -> u64 {
    match t {
        Term::Var(name) => {
            let code = enc.code_for(name);
            encode_sequence(&[0, code])
        }
        Term::Const(name) => {
            let code = enc.code_for(name);
            encode_sequence(&[1, code])
        }
        Term::Func(name, args) => {
            let code = enc.code_for(name);
            let mut nums = vec![2, code, args.len() as u64];
            for arg in args {
                nums.push(encode_term(enc, arg));
            }
            encode_sequence(&nums)
        }
    }
}

/// Encode a predicate formula
pub fn encode_pred_formula(enc: &mut GodelEncoding, f: &PredFormula) -> u64 {
    match f {
        PredFormula::Atom(pred, args) => {
            let code = enc.code_for(pred);
            let mut nums = vec![0, code, args.len() as u64];
            for arg in args {
                nums.push(encode_term(enc, arg));
            }
            encode_sequence(&nums)
        }
        PredFormula::Not(inner) => {
            let not_code = enc.code_for("¬");
            encode_sequence(&[not_code, encode_pred_formula(enc, inner)])
        }
        PredFormula::And(a, b) => {
            let and_code = enc.code_for("∧");
            encode_sequence(&[and_code, encode_pred_formula(enc, a), encode_pred_formula(enc, b)])
        }
        PredFormula::Or(a, b) => {
            let or_code = enc.code_for("∨");
            encode_sequence(&[or_code, encode_pred_formula(enc, a), encode_pred_formula(enc, b)])
        }
        PredFormula::Implies(a, b) => {
            let imp_code = enc.code_for("→");
            encode_sequence(&[imp_code, encode_pred_formula(enc, a), encode_pred_formula(enc, b)])
        }
        PredFormula::Iff(a, b) => {
            let iff_code = enc.code_for("↔");
            encode_sequence(&[iff_code, encode_pred_formula(enc, a), encode_pred_formula(enc, b)])
        }
        PredFormula::Forall(var, body) => {
            let forall_code = enc.code_for("∀");
            let var_code = enc.code_for(var);
            encode_sequence(&[forall_code, var_code, encode_pred_formula(enc, body)])
        }
        PredFormula::Exists(var, body) => {
            let exists_code = enc.code_for("∃");
            let var_code = enc.code_for(var);
            encode_sequence(&[exists_code, var_code, encode_pred_formula(enc, body)])
        }
        PredFormula::Top => {
            let code = enc.code_for("⊤");
            encode_sequence(&[code])
        }
        PredFormula::Bot => {
            let code = enc.code_for("⊥");
            encode_sequence(&[code])
        }
    }
}

/// Compute Gödel's β function: β(b, c, i) = c % (1 + (i+1) * b)
pub fn beta(b: u64, c: u64, i: u64) -> u64 {
    let divisor = 1 + (i + 1) * b;
    c % divisor
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::propositional::*;

    #[test]
    fn test_first_primes() {
        let primes = first_n_primes(5);
        assert_eq!(primes, vec![2, 3, 5, 7, 11]);
    }

    #[test]
    fn test_encode_decode_sequence_simple() {
        let nums = vec![1, 2, 3];
        let encoded = encode_sequence(&nums);
        let decoded = decode_sequence(encoded, 3);
        assert_eq!(decoded, nums);
    }

    #[test]
    fn test_encode_decode_zeros() {
        let nums = vec![0, 0, 0];
        let encoded = encode_sequence(&nums);
        assert_eq!(encoded, 1); // all exponents are 0, product of primes^0 = 1
        let decoded = decode_sequence(encoded, 3);
        assert_eq!(decoded, nums);
    }

    #[test]
    fn test_encode_atom() {
        let mut enc = GodelEncoding::new();
        let f = atom("p");
        let godel_num = encode_formula(&mut enc, &f);
        assert!(godel_num > 0);
    }

    #[test]
    fn test_encode_different_atoms_different_numbers() {
        let mut enc = GodelEncoding::new();
        let f1 = atom("p");
        let f2 = atom("q");
        let g1 = encode_formula(&mut enc, &f1);
        let g2 = encode_formula(&mut enc, &f2);
        assert_ne!(g1, g2);
    }

    #[test]
    fn test_encode_same_formula_same_number() {
        let mut enc = GodelEncoding::new();
        let f1 = and(atom("p"), atom("q"));
        let f2 = and(atom("p"), atom("q"));
        let g1 = encode_formula(&mut enc, &f1);
        let g2 = encode_formula(&mut enc, &f2);
        assert_eq!(g1, g2);
    }

    #[test]
    fn test_encode_negation() {
        let mut enc = GodelEncoding::new();
        let f = not(atom("p"));
        let godel_num = encode_formula(&mut enc, &f);
        assert!(godel_num > 0);
    }

    #[test]
    fn test_encode_implication() {
        let mut enc = GodelEncoding::new();
        let f = implies(atom("p"), atom("q"));
        let godel_num = encode_formula(&mut enc, &f);
        assert!(godel_num > 0);
    }

    #[test]
    fn test_encode_predicate_term() {
        let mut enc = GodelEncoding::new();
        let t = Term::Var("x".to_string());
        let g = encode_term(&mut enc, &t);
        assert!(g > 0);
    }

    #[test]
    fn test_encode_predicate_formula() {
        let mut enc = GodelEncoding::new();
        let f = PredFormula::Forall("x".to_string(), Box::new(
            PredFormula::Atom("P".to_string(), vec![Term::Var("x".to_string())])
        ));
        let g = encode_pred_formula(&mut enc, &f);
        assert!(g > 0);
    }

    #[test]
    fn test_beta_function() {
        // β(b, c, i) should be deterministic
        let result = beta(3, 17, 0);
        assert_eq!(result, 17 % (1 + 1 * 3)); // 17 % 4 = 1
        assert_eq!(result, 1);
    }

    #[test]
    fn test_encode_sequence_roundtrip() {
        for seq in &[vec![1], vec![2, 3], vec![5, 0, 1], vec![0, 0, 0, 1]] {
            let encoded = encode_sequence(seq);
            let decoded = decode_sequence(encoded, seq.len());
            assert_eq!(&decoded, seq, "Failed for {:?}", seq);
        }
    }

    #[test]
    fn test_godel_symbol_codes() {
        let enc = GodelEncoding::new();
        assert_eq!(enc.symbol_codes["¬"], 1);
        assert_eq!(enc.symbol_codes["∨"], 2);
        assert_eq!(enc.symbol_codes["→"], 3);
        assert_eq!(enc.symbol_codes["∀"], 4);
        assert_eq!(enc.symbol_codes["∧"], 5);
    }
}
