use crate::building_block::field::prime_field::PrimeField;
use crate::zk::w_trusted_setup::pinocchio::{
  term::Term,
  equation_parser::{Equation, MathExpr},
};

pub struct Gate {
  pub a: Term,
  pub b: Term,
  pub c: Term,
}

impl std::fmt::Debug for Gate {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
      write!(f, "{:?} * {:?} = {:?}", self.a, self.b, self.c)
  }
}

impl Gate {
  // traverse the Equation tree generating statement at each Add/Mul node
  fn traverse_lhs(
    f: &PrimeField, expr: &MathExpr, gates: &mut Vec<Gate>
  ) -> Term {
    match expr {
      MathExpr::Num(n) => Term::Num(n.clone()),
      MathExpr::Var(s) => Term::Var(s.clone()),

      MathExpr::Add(signal_id, left, right) => {
        let a = Gate::traverse_lhs(f, left, gates);
        let b = Gate::traverse_lhs(f, right, gates);
        let c = Term::TmpVar(*signal_id);
        // a + b = c
        // -> (a + b) * 1 = c
        let sum = Term::Sum(Box::new(a), Box::new(b));
        gates.push(Gate { a: sum, b: Term::One, c: c.clone() });
        c
      },
      MathExpr::Mul(signal_id, left, right) => {
        let a = Gate::traverse_lhs(f, left, gates);
        let b = Gate::traverse_lhs(f, right, gates);
        let c = Term::TmpVar(*signal_id);
        gates.push(Gate { a, b, c: c.clone() });
        c
      },
      MathExpr::Sub(signal_id, left, right) => {
        let a = Gate::traverse_lhs(f, left, gates);
        let b = Gate::traverse_lhs(f, right, gates);
        let c = Term::TmpVar(*signal_id);
        // a - b = c
        // -> b + c = a
        // -> (b + c) * 1 = a
        let sum = Term::Sum(Box::new(b), Box::new(c.clone()));
        gates.push(Gate { a: sum, b: Term::One, c: a.clone() });
        c
      },
      MathExpr::Div(signal_id, left, right) => {
        let a = Gate::traverse_lhs(f, left, gates);
        let b = Gate::traverse_lhs(f, right, gates);
        let c = Term::TmpVar(*signal_id);
        // a / b = c
        // -> b * c = a
        gates.push(Gate { a: b, b: c.clone(), c: a.clone() });
        // send c to next as the original division does
        c
      },
      MathExpr::Equation(_lhs, _rhs) => {
        panic!("should not be visited");
      }
    }
  }

  pub fn build(f: &PrimeField, eq: &Equation) -> Vec<Gate> {
    let mut gates: Vec<Gate> = vec![];
    let root = Gate::traverse_lhs(f, &eq.lhs, &mut gates);
    let out_gate = Gate { a: root, b: Term::One, c: Term::Out };
    gates.push(out_gate);
    gates
  }
}


#[cfg(test)]
mod tests {
  use super::*;
  use crate::zk::w_trusted_setup::pinocchio::equation_parser::EquationParser;

  #[test]
  fn test_build_add() {
    let f = &PrimeField::new(&3911u16);
    let input = "x + 4 == 9";
    let eq = EquationParser::parse(f, input).unwrap();
    let gates = &Gate::build(f, &eq);
    println!("{:?}", gates);
    assert_eq!(gates.len(), 2);

    // t1 = (x + 4) * 1
    assert_eq!(gates[0].a, Term::Sum(Box::new(Term::Var("x".to_string())), Box::new(Term::Num(f.elem(&4u8)))));
    assert_eq!(gates[0].b, Term::One);
    assert_eq!(gates[0].c, Term::TmpVar(1));

    // out = t1 * 1
    assert_eq!(gates[1].a, Term::TmpVar(1));
    assert_eq!(gates[1].b, Term::One);
    assert_eq!(gates[1].c, Term::Out);
  }

  #[test]
  fn test_build_sub() {
    let f = &PrimeField::new(&3911u16);
    let input = "x - 4 == 9";
    let eq = EquationParser::parse(f, input).unwrap();
    let gates = &Gate::build(f, &eq);
    assert_eq!(gates.len(), 2);

    // t1 = (x + 4) * 1
    assert_eq!(gates[0].a, Term::Sum(Box::new(Term::Num(f.elem(&4u8))), Box::new(Term::TmpVar(1))));
    assert_eq!(gates[0].b, Term::One);
    assert_eq!(gates[0].c, Term::Var("x".to_string()));

    // out = t1 * 1
    assert_eq!(gates[1].a, Term::TmpVar(1));
    assert_eq!(gates[1].b, Term::One);
    assert_eq!(gates[1].c, Term::Out);
  }

  #[test]
  fn test_build_mul() {
    let f = &PrimeField::new(&3911u16);
    let input = "x * 4 == 9";
    let eq = EquationParser::parse(f, input).unwrap();
    let gates = &Gate::build(f, &eq);
    assert_eq!(gates.len(), 2);

    // x = (4 + t1) * 1
    assert_eq!(gates[0].a, Term::Var("x".to_string()));
    assert_eq!(gates[0].b, Term::Num(f.elem(&4u8)));
    assert_eq!(gates[0].c, Term::TmpVar(1));

    // out = t1 * 1
    assert_eq!(gates[1].a, Term::TmpVar(1));
    assert_eq!(gates[1].c, Term::Out);
  }

  #[test]
  fn test_build_div() {
    let f = &PrimeField::new(&3911u16);
    let input = "x / 4 == 2";
    let eq = EquationParser::parse(f, input).unwrap();
    let gates = &Gate::build(f, &eq);
    assert_eq!(gates.len(), 2);

    // x = 4 * t1
    assert_eq!(gates[0].a, Term::Num(f.elem(&4u8)));
    assert_eq!(gates[0].b, Term::TmpVar(1));
    assert_eq!(gates[0].c, Term::Var("x".to_string()));

    // out = t1 * 1
    assert_eq!(gates[1].a, Term::TmpVar(1));
    assert_eq!(gates[1].c, Term::Out);
  }

  #[test]
  fn test_build_combined1() {
    let f = &PrimeField::new(&3911u16);
    let input = "(3 * x + 4) / 2 == 11";
    let eq = EquationParser::parse(f, input).unwrap();
    let gates = &Gate::build(f, &eq);
    assert_eq!(gates.len(), 4);

    // t1 = 3 * x
    assert_eq!(gates[0].a, Term::Num(f.elem(&3u8)));
    assert_eq!(gates[0].b, Term::Var("x".to_string()));
    assert_eq!(gates[0].c, Term::TmpVar(1));

    // t2 = (t1 + 4) * 1
    assert_eq!(gates[1].a, Term::Sum(
      Box::new(Term::TmpVar(1)),
      Box::new(Term::Num(f.elem(&4u8)))
    ));
    assert_eq!(gates[1].b, Term::One);
    assert_eq!(gates[1].c, Term::TmpVar(2));

    // t2 = 2 * t3
    assert_eq!(gates[2].a, Term::Num(f.elem(&2u8)));
    assert_eq!(gates[2].b, Term::TmpVar(3));
    assert_eq!(gates[2].c, Term::TmpVar(2));

    // out = t3 * 1
    assert_eq!(gates[3].a, Term::TmpVar(3));
    assert_eq!(gates[3].b, Term::One);
    assert_eq!(gates[3].c, Term::Out);
  }

  #[test]
  fn test_build_combined2() {
    let f = &PrimeField::new(&3911u16);
    let input = "(x * x * x) + x + 5 == 35";
    println!("Equation: {}", input);

    let eq = EquationParser::parse(f, input).unwrap();
    let gates = &Gate::build(f, &eq);
    println!("Gates: {:?}", gates);
    assert_eq!(gates.len(), 5);

    // t1 = x * x
    assert_eq!(gates[0].a, Term::Var("x".to_string()));
    assert_eq!(gates[0].b, Term::Var("x".to_string()));
    assert_eq!(gates[0].c, Term::TmpVar(1));

    // t2 = x * t1
    assert_eq!(gates[1].a, Term::Var("x".to_string()));
    assert_eq!(gates[1].b, Term::TmpVar(1));
    assert_eq!(gates[1].c, Term::TmpVar(2));

    // t3 = (x + 5) * 1
    assert_eq!(gates[2].a, Term::Sum(
      Box::new(Term::Var("x".to_string())),
      Box::new(Term::Num(f.elem(&5u8)))
    ));
    assert_eq!(gates[2].b, Term::One);
    assert_eq!(gates[2].c, Term::TmpVar(3));

    // t4 = (t2 + t3) * 1
    assert_eq!(gates[3].a, Term::Sum(
      Box::new(Term::TmpVar(2)),
      Box::new(Term::TmpVar(3))
    ));
    assert_eq!(gates[3].b, Term::One);
    assert_eq!(gates[3].c, Term::TmpVar(4));

    // out = t4 * 1
    assert_eq!(gates[4].a, Term::TmpVar(4));
    assert_eq!(gates[4].b, Term::One);
    assert_eq!(gates[4].c, Term::Out);
  }

  #[test]
  fn blog_post_1_example_1() {
    let f = &PrimeField::new(&37u8);
    let expr = "(x * x * x) + x + 5 == 35";
    let eq = EquationParser::parse(f, expr).unwrap();
    let gates = &Gate::build(f, &eq);
    println!("{:?}", gates);
  }
}
