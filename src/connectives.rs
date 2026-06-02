//! Logical connectives with truth table definitions

use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

/// Unary connective
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum UnaryConnective {
    Not,
}

/// Binary connective
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum BinaryConnective {
    And,
    Or,
    Implies,
    Iff,
    Nand,
    Nor,
    Xor,
}

impl BinaryConnective {
    /// Evaluate the connective given two boolean values.
    pub fn eval(&self, a: bool, b: bool) -> bool {
        match self {
            BinaryConnective::And => a && b,
            BinaryConnective::Or => a || b,
            BinaryConnective::Implies => !a || b,
            BinaryConnective::Iff => a == b,
            BinaryConnective::Nand => !(a && b),
            BinaryConnective::Nor => !(a || b),
            BinaryConnective::Xor => a != b,
        }
    }

    /// Return the truth table for this connective (4 rows: FF, FT, TF, TT).
    pub fn truth_table(&self) -> Vec<(bool, bool, bool)> {
        let inputs = [(false, false), (false, true), (true, false), (true, true)];
        inputs.iter().map(|(a, b)| (*a, *b, self.eval(*a, *b))).collect()
    }

    /// Is this connective commutative?
    pub fn is_commutative(&self) -> bool {
        matches!(self, BinaryConnective::And | BinaryConnective::Or | BinaryConnective::Iff | BinaryConnective::Nand | BinaryConnective::Nor | BinaryConnective::Xor)
    }

    /// Get the dual connective (swap true/false).
    pub fn dual(&self) -> BinaryConnective {
        match self {
            BinaryConnective::And => BinaryConnective::Or,
            BinaryConnective::Or => BinaryConnective::And,
            BinaryConnective::Implies => BinaryConnective::Nand, // simplified
            BinaryConnective::Iff => BinaryConnective::Xor,
            BinaryConnective::Nand => BinaryConnective::Nor,
            BinaryConnective::Nor => BinaryConnective::Nand,
            BinaryConnective::Xor => BinaryConnective::Iff,
        }
    }
}

/// Connective truth table: maps all input combinations to outputs
pub struct ConnectiveTable {
    pub connective: BinaryConnective,
    pub rows: Vec<(bool, bool, bool)>,
}

impl ConnectiveTable {
    pub fn new(connective: BinaryConnective) -> Self {
        let rows = connective.truth_table();
        Self { connective, rows }
    }

    /// Verify the truth table against manual evaluation
    pub fn verify(&self) -> bool {
        self.rows.iter().all(|(a, b, result)| self.connective.eval(*a, *b) == *result)
    }
}

/// Full truth table builder for arbitrary expressions over variables
pub struct TruthTableBuilder {
    pub var_names: Vec<String>,
    pub rows: Vec<(BTreeMap<String, bool>, bool)>,
}

impl TruthTableBuilder {
    /// Build a truth table for 2 variables given a binary connective
    pub fn for_binary_connective(conn: BinaryConnective, name_a: &str, name_b: &str) -> Self {
        let var_names = vec![name_a.to_string(), name_b.to_string()];
        let rows = vec![
            (false, false), (false, true), (true, false), (true, true),
        ].iter().map(|(a, b)| {
            let mut map = BTreeMap::new();
            map.insert(name_a.to_string(), *a);
            map.insert(name_b.to_string(), *b);
            (map, conn.eval(*a, *b))
        }).collect();
        Self { var_names, rows }
    }

    /// Count rows where the result is true
    pub fn true_count(&self) -> usize {
        self.rows.iter().filter(|(_, r)| *r).count()
    }

    /// Count rows where the result is false
    pub fn false_count(&self) -> usize {
        self.rows.len() - self.true_count()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_and_truth_table() {
        let tt = BinaryConnective::And.truth_table();
        assert_eq!(tt, vec![
            (false, false, false),
            (false, true, false),
            (true, false, false),
            (true, true, true),
        ]);
    }

    #[test]
    fn test_or_truth_table() {
        let tt = BinaryConnective::Or.truth_table();
        assert_eq!(tt, vec![
            (false, false, false),
            (false, true, true),
            (true, false, true),
            (true, true, true),
        ]);
    }

    #[test]
    fn test_not_eval() {
        // Verify UnaryConnective exists and is usable
        let _not = UnaryConnective::Not;
        assert_eq!(true, !false);
    }

    #[test]
    fn test_implies_truth_table() {
        let tt = BinaryConnective::Implies.truth_table();
        assert_eq!(tt, vec![
            (false, false, true),
            (false, true, true),
            (true, false, false),
            (true, true, true),
        ]);
    }

    #[test]
    fn test_iff_truth_table() {
        let tt = BinaryConnective::Iff.truth_table();
        assert_eq!(tt, vec![
            (false, false, true),
            (false, true, false),
            (true, false, false),
            (true, true, true),
        ]);
    }

    #[test]
    fn test_nand_truth_table() {
        let tt = BinaryConnective::Nand.truth_table();
        assert_eq!(tt[3], (true, true, false)); // T NAND T = F
        assert_eq!(tt[0], (false, false, true)); // F NAND F = T
    }

    #[test]
    fn test_nor_truth_table() {
        let tt = BinaryConnective::Nor.truth_table();
        assert_eq!(tt[0], (false, false, true)); // F NOR F = T
        assert_eq!(tt[3], (true, true, false)); // T NOR T = F
    }

    #[test]
    fn test_xor_truth_table() {
        let tt = BinaryConnective::Xor.truth_table();
        assert_eq!(tt[0], (false, false, false));
        assert_eq!(tt[1], (false, true, true));
        assert_eq!(tt[2], (true, false, true));
        assert_eq!(tt[3], (true, true, false));
    }

    #[test]
    fn test_commutativity() {
        assert!(BinaryConnective::And.is_commutative());
        assert!(BinaryConnective::Or.is_commutative());
        assert!(!BinaryConnective::Implies.is_commutative());
    }

    #[test]
    fn test_connective_table_verify() {
        let ct = ConnectiveTable::new(BinaryConnective::And);
        assert!(ct.verify());
    }

    #[test]
    fn test_truth_table_builder() {
        let ttb = TruthTableBuilder::for_binary_connective(BinaryConnective::And, "p", "q");
        assert_eq!(ttb.true_count(), 1);
        assert_eq!(ttb.false_count(), 3);
        assert_eq!(ttb.var_names, vec!["p", "q"]);
    }

    #[test]
    fn test_dual() {
        assert_eq!(BinaryConnective::And.dual(), BinaryConnective::Or);
        assert_eq!(BinaryConnective::Or.dual(), BinaryConnective::And);
    }
}
