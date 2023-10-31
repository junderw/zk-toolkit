use crate::zk::w_trusted_setup::pinocchio::gates::bool_circuit::{BoolCircuit, Processor};

pub struct HalfAdder();

#[derive(Debug)]
pub struct AdderResult {
    pub sum: bool,
    pub carry: bool,
}

impl HalfAdder {
    // (augend, addend) -> (sum, carry)
    pub fn add(augend: bool, addend: bool) -> AdderResult {
        let sum = BoolCircuit::Xor(
            Box::new(BoolCircuit::Leaf(augend)),
            Box::new(BoolCircuit::Leaf(addend)),
        );
        let carry = BoolCircuit::And(
            Box::new(BoolCircuit::Leaf(augend)),
            Box::new(BoolCircuit::Leaf(addend)),
        );

        let sum = Processor::eval(&sum);
        let carry = Processor::eval(&carry);

        AdderResult { sum, carry }
    }
}

pub struct FullAdder();

impl FullAdder {
    pub fn add(augend: bool, addend: bool, carry: bool) -> AdderResult {
        let res1 = HalfAdder::add(augend, addend);
        let res2 = HalfAdder::add(res1.sum, carry);
        let carry = BoolCircuit::Or(
            Box::new(BoolCircuit::Leaf(res1.carry)),
            Box::new(BoolCircuit::Leaf(res2.carry)),
        );
        let carry = Processor::eval(&carry);
        AdderResult {
            sum: res2.sum,
            carry,
        }
    }
}

#[cfg(test)]
mod half_adder_tests {
    use super::*;

    #[test]
    fn add_0_0() {
        let res = HalfAdder::add(false, false);
        assert!(!res.sum);
        assert!(!res.carry);
    }

    #[test]
    fn add_1_0_or_0_1() {
        let res = HalfAdder::add(true, false);
        assert!(res.sum);
        assert!(!res.carry);

        let res = HalfAdder::add(false, true);
        assert!(res.sum);
        assert!(!res.carry);
    }

    #[test]
    fn add_1_1() {
        let res = HalfAdder::add(true, true);
        assert!(!res.sum);
        assert!(res.carry);
    }
}

#[cfg(test)]
mod full_adder_tests {
    use super::*;

    #[test]
    fn single_inst_add_0_0_0() {
        let res = FullAdder::add(false, false, false);
        assert!(!res.sum);
        assert!(!res.carry);
    }

    #[test]
    fn single_inst_add_1_0_0_or_0_1_0_or_0_0_1() {
        let res = FullAdder::add(true, false, false);
        assert!(res.sum);
        assert!(!res.carry);

        let res = FullAdder::add(false, true, false);
        assert!(res.sum);
        assert!(!res.carry);

        let res = FullAdder::add(false, false, true);
        assert!(res.sum);
        assert!(!res.carry);
    }

    #[test]
    fn single_inst_add_1_1_0_or_1_0_1_or_0_1_1() {
        let res = FullAdder::add(true, true, false);
        assert!(!res.sum);
        assert!(res.carry);

        let res = FullAdder::add(true, false, true);
        assert!(!res.sum);
        assert!(res.carry);

        let res = FullAdder::add(false, true, true);
        assert!(!res.sum);
        assert!(res.carry);
    }

    #[test]
    fn single_inst_add_1_1_1() {
        let res = FullAdder::add(true, true, true);
        assert!(res.sum);
        assert!(res.carry);
    }
}
