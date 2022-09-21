use nom::{
  IResult,
  branch::alt,
  character::{
    complete::{ char, one_of, multispace0, alpha1 },
  },
  combinator::{ opt, recognize },
  multi::{ many0, many1 },
  sequence::{ tuple, delimited, terminated },
};
use crate::building_block::field::{Field, FieldElem};
use num_bigint::{BigInt, BigUint, Sign};

type SignalId = u128;

#[derive(Debug, PartialEq, Clone)]
pub enum MathExpr {
  Num(SignalId, FieldElem),
  Var(SignalId, String),
  Mul(SignalId, Box<MathExpr>, Box<MathExpr>),
  Div(SignalId, Box<MathExpr>, Box<MathExpr>),
  Add(SignalId, Box<MathExpr>, Box<MathExpr>),
  Sub(SignalId, Box<MathExpr>, Box<MathExpr>),
}

pub struct MathExprParser(Field, u128);

impl MathExprParser {
    pub fn new(f: Field, s: u128) -> Self {
        Self(f, s)
    }

    #[inline]
    fn incr_int(&self) {
        let int = (&self.1) as *const u128 as *mut u128;
        // Safety: Should use std::sync::Mutex, but performance!
        // This is super unsafe
        unsafe {
            *int += 1;
        }
        /*
        // If self.1 was a Mutex<u128>
        let lock = self.1.lock().unwrap();
        *lock += 1;
        */
    }

    fn num_str_to_field_elem(&self) -> impl Fn(&str) -> FieldElem + '_ {
        |s| {
            let field = &self.0;
            if s.starts_with("-") {
                let mut n = BigInt::parse_bytes(s.as_bytes(), 10).unwrap();
                if n.sign() == Sign::Minus {
                    let order = BigInt::from_biguint(Sign::Plus, (*field.order).clone());
                    n = -n;
                    n = n % &order;
                    n = &order - n;
                    let n = n.to_biguint().unwrap();
                    field.elem(&n)
                } else {
                    let n = n.to_biguint().unwrap();
                    field.elem(&n)
                }
            } else {
                // if positive
                let n = BigUint::parse_bytes(s.as_bytes(), 10).unwrap();
                field.elem(&n)
            }
        }
    }

    fn variable(&self) -> impl Fn(&str) -> IResult<&str, MathExpr> + '_ {
        |input| {
            let (input, s) = delimited(
                multispace0,
                recognize(terminated(alpha1, many0(one_of("0123456789")))),
                multispace0,
            )(input)?;
            self.incr_int();
            Ok((input, MathExpr::Var(self.1, s.to_string())))
        }
    }

    fn decimal(&self) -> impl Fn(&str) -> IResult<&str, MathExpr> + '_ {
        |input| {
            let (input, s) = delimited(
                multispace0,
                recognize(tuple((opt(char('-')), many1(one_of("0123456789"))))),
                multispace0,
            )(input)?;

            let n = self.num_str_to_field_elem()(s);
            self.incr_int();
            Ok((input, MathExpr::Num(self.1, n)))
        }
    }

    // <term2> ::= <variable> | <number> | '(' <expr> ')'
    fn term2(&self) -> impl Fn(&str) -> IResult<&str, MathExpr> + '_ {
        |input| {
            let (input, node) = alt((
                self.variable(),
                self.decimal(),
                delimited(
                    delimited(multispace0, char('('), multispace0),
                    self.expr(),
                    delimited(multispace0, char(')'), multispace0),
                ),
            ))(input)?;

            Ok((input, node))
        }
    }

    // <term1> ::= <term2> [ ('*'|'/') <term2> ]*
    fn term1(&self) -> impl Fn(&str) -> IResult<&str, MathExpr> + '_ {
        |input| {
            let rhs = tuple((alt((char('*'), char('/'))), self.term2()));
            let (input, (lhs, rhs)) = tuple((self.term2(), many0(rhs)))(input)?;

            if rhs.len() == 0 {
                Ok((input, lhs))
            } else {
                // translate rhs vector to Mul<Mul<..,Mul>>>..
                let rhs_head = &rhs[0];
                let rhs = rhs
                    .iter()
                    .skip(1)
                    .fold(rhs_head.1.clone(), |acc, x| match x {
                        ('*', node) => {
                            self.incr_int();
                            MathExpr::Mul(self.1, Box::new(acc), Box::new(node.clone()))
                        }
                        ('/', node) => {
                            self.incr_int();
                            MathExpr::Div(self.1, Box::new(acc), Box::new(node.clone()))
                        }
                        (op, _) => panic!("unexpected operator encountered in term1 {}", op),
                    });

                self.incr_int();
                let node = if rhs_head.0 == '*' {
                    MathExpr::Mul(self.1, Box::new(lhs), Box::new(rhs))
                } else {
                    MathExpr::Div(self.1, Box::new(lhs), Box::new(rhs))
                };
                Ok((input, node))
            }
        }
    }

    // <expr> ::= <term1> [ ('+'|'-') <term1> ]*
    pub fn expr(&self) -> impl Fn(&str) -> IResult<&str, MathExpr> + '_ {
        |input| {
            let rhs = tuple((alt((char('+'), char('-'))), self.term1()));
            let (input, (lhs, rhs)) = tuple((self.term1(), many0(rhs)))(input)?;

            if rhs.len() == 0 {
                Ok((input, lhs))
            } else {
                // translate rhs vector to Add<Add<..,Add>>>..
                let rhs_head = &rhs[0];
                let rhs = rhs
                    .iter()
                    .skip(1)
                    .fold(rhs_head.1.clone(), |acc, x| match x {
                        ('+', node) => {
                            self.incr_int();
                            MathExpr::Add(self.1, Box::new(acc), Box::new(node.clone()))
                        }
                        ('-', node) => {
                            self.incr_int();
                            MathExpr::Sub(self.1, Box::new(acc), Box::new(node.clone()))
                        }
                        (op, _) => panic!("unexpected operator encountered in expr: {}", op),
                    });

                self.incr_int();
                let node = if rhs_head.0 == '+' {
                    MathExpr::Add(self.1, Box::new(lhs), Box::new(rhs))
                } else {
                    MathExpr::Sub(self.1, Box::new(lhs), Box::new(rhs))
                };
                Ok((input, node))
            }
        }
    }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_decimal() {
    let f = Field::new(&11u8);
    match MathExprParser::parse("123", f) {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Num(1, f.elem(&123u8)));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_decimal_with_spaces() {
    match MathExprParser::parse(" 123 ") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Num("123".to_string()));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_neg_decimal() {
    match MathExprParser::parse("-123") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Num("-123".to_string()));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_1_char_variable() {
    for s in vec!["x", "x1", "x0", "xy", "xy1"] {
      match MathExprParser::parse(s) {
        Ok((input, x)) => {
          assert_eq!(input, "");
          assert_eq!(x, MathExpr::Var(s.to_string()));
        },
        Err(_) => panic!(),
      }
    }
  }

  #[test]
  fn test_1_char_variable_with_spaces() {
    for s in vec!["x", "x1", "x0", "xy", "xy1"] {
      match MathExprParser::parse(&format!("  {}  ", s)) {
        Ok((input, x)) => {
          assert_eq!(input, "");
          assert_eq!(x, MathExpr::Var(s.to_string()));
        },
        Err(_) => panic!(),
      }
    }
  }

  #[test]
  fn test_simple_add_expr() {
    match MathExprParser::parse("123+456") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Add(
          Box::new(MathExpr::Num("123".to_string())),
          Box::new(MathExpr::Num("456".to_string())),
        ));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_simple_add_expr_with_1_var() {
    for s in vec!["x", "x1", "x0", "xy", "xy1"] {
      match MathExprParser::parse(&format!("{}+456", s)) {
        Ok((input, x)) => {
          assert_eq!(input, "");
          assert_eq!(x, MathExpr::Add(
            Box::new(MathExpr::Var(s.to_string())),
            Box::new(MathExpr::Num("456".to_string())),
          ));
        },
        Err(_) => panic!(),
      }
    }
  }

  #[test]
  fn test_simple_add_expr_with_2_vars() {
    for (a,b) in vec![("x", "y"), ("x1", "y1"), ("xxx1123", "yyy123443")] {
      match MathExprParser::parse(&format!("{}+{}", a, b)) {
        Ok((input, x)) => {
          assert_eq!(input, "");
          assert_eq!(x, MathExpr::Add(
            Box::new(MathExpr::Var(a.to_string())),
            Box::new(MathExpr::Var(b.to_string())),
          ));
        },
        Err(_) => panic!(),
      }
    }
  }

  #[test]
  fn test_simple_add_expr_incl_neg() {
    match MathExprParser::parse("123+-456") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Add(
          Box::new(MathExpr::Num("123".to_string())),
          Box::new(MathExpr::Num("-456".to_string())),
        ));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_simple_sub_expr() {
    match MathExprParser::parse("123-456") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Sub(
          Box::new(MathExpr::Num("123".to_string())),
          Box::new(MathExpr::Num("456".to_string())),
        ));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_simple_sub_expr_1_var() {
    for s in vec!["x", "x1", "x0", "xy", "xy1"] {
      match MathExprParser::parse(&format!("123-{}", s)) {
        Ok((input, x)) => {
          assert_eq!(input, "");
          assert_eq!(x, MathExpr::Sub(
            Box::new(MathExpr::Num("123".to_string())),
            Box::new(MathExpr::Var(s.to_string())),
          ));
        },
        Err(_) => panic!(),
      }
    }
  }

  #[test]
  fn test_simple_sub_expr_incl_neg1() {
    match MathExprParser::parse("-123-456") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Sub(
          Box::new(MathExpr::Num("-123".to_string())),
          Box::new(MathExpr::Num("456".to_string())),
        ));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_simple_sub_expr_incl_neg1_1_var() {
    for s in vec!["x", "x1", "x0", "xy", "xy1"] {
      match MathExprParser::parse(&format!("-123-{}", s)) {
        Ok((input, x)) => {
          assert_eq!(input, "");
          assert_eq!(x, MathExpr::Sub(
            Box::new(MathExpr::Num("-123".to_string())),
            Box::new(MathExpr::Var(s.to_string())),
          ));
        },
        Err(_) => panic!(),
      }
    }
  }
  #[test]
  fn test_simple_sub_expr_incl_neg2() {
    match MathExprParser::parse("123--456") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Sub(
          Box::new(MathExpr::Num("123".to_string())),
          Box::new(MathExpr::Num("-456".to_string())),
        ));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_simple_sub_expr_incl_neg2_with_spaces() {
    match MathExprParser::parse("123 - -456") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Sub(
          Box::new(MathExpr::Num("123".to_string())),
          Box::new(MathExpr::Num("-456".to_string())),
        ));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_simple_sub_expr_incl_neg2_with_spaces_1_var() {
    match MathExprParser::parse("x - -456") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Sub(
          Box::new(MathExpr::Var("x".to_string())),
          Box::new(MathExpr::Num("-456".to_string())),
        ));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_simple_mul_expr() {
    match MathExprParser::parse("123*456") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Mul(
          Box::new(MathExpr::Num("123".to_string())),
          Box::new(MathExpr::Num("456".to_string())),
        ));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_simple_mul_expr_incl_neg1() {
    match MathExprParser::parse("123*-456") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Mul(
          Box::new(MathExpr::Num("123".to_string())),
          Box::new(MathExpr::Num("-456".to_string())),
        ));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_simple_mul_expr_incl_neg2() {
    match MathExprParser::parse("-123*456") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Mul(
          Box::new(MathExpr::Num("-123".to_string())),
          Box::new(MathExpr::Num("456".to_string())),
        ));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_simple_mul_expr_incl_neg() {
    match MathExprParser::parse("123*-456") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Mul(
          Box::new(MathExpr::Num("123".to_string())),
          Box::new(MathExpr::Num("-456".to_string())),
        ));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_simple_div_expr() {
    match MathExprParser::parse("123/456") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Div(
          Box::new(MathExpr::Num("123".to_string())),
          Box::new(MathExpr::Num("456".to_string())),
        ));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_add_and_mul_expr() {
    match MathExprParser::parse("123+456*789") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Add(
          Box::new(MathExpr::Num("123".to_string())),
          Box::new(MathExpr::Mul(
            Box::new(MathExpr::Num("456".to_string())),
            Box::new(MathExpr::Num("789".to_string()))
          )),
        ));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_add_mul_div_expr() {
    match MathExprParser::parse("111/222+333*444") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Add(
          Box::new(MathExpr::Div(
            Box::new(MathExpr::Num("111".to_string())),
            Box::new(MathExpr::Num("222".to_string()))
          )),
          Box::new(MathExpr::Mul(
            Box::new(MathExpr::Num("333".to_string())),
            Box::new(MathExpr::Num("444".to_string()))
          )),
        ));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_paren_add_and_mul_expr() {
    match MathExprParser::parse("(123+456)*789") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Mul(
          Box::new(MathExpr::Add(
            Box::new(MathExpr::Num("123".to_string())),
            Box::new(MathExpr::Num("456".to_string()))
          )),
          Box::new(MathExpr::Num("789".to_string())),
        ));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_paren_add_and_mul_expr_with_spaces() {
    match MathExprParser::parse(" (123 + 456) * 789") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Mul(
          Box::new(MathExpr::Add(
            Box::new(MathExpr::Num("123".to_string())),
            Box::new(MathExpr::Num("456".to_string()))
          )),
          Box::new(MathExpr::Num("789".to_string())),
        ));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_paren_add_mul_sub_expr() {
    match MathExprParser::parse("(111+222)*(333-444)") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Mul(
          Box::new(MathExpr::Add(
            Box::new(MathExpr::Num("111".to_string())),
            Box::new(MathExpr::Num("222".to_string()))
          )),
          Box::new(MathExpr::Sub(
            Box::new(MathExpr::Num("333".to_string())),
            Box::new(MathExpr::Num("444".to_string()))
          )),
        ));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_multiple_paren() {
    match MathExprParser::parse("((111+222))") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Add(
          Box::new(MathExpr::Num("111".to_string())),
          Box::new(MathExpr::Num("222".to_string())),
        ));
      },
      Err(_) => panic!(),
    }
  }

  #[test]
  fn test_multiple_paren_with_spaces() {
    match MathExprParser::parse(" ( (111+222) ) ") {
      Ok((input, x)) => {
        assert_eq!(input, "");
        assert_eq!(x, MathExpr::Add(
          Box::new(MathExpr::Num("111".to_string())),
          Box::new(MathExpr::Num("222".to_string())),
        ));
      },
      Err(_) => panic!(),
    }
  }
}
