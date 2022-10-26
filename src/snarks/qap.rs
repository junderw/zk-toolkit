use crate::building_block::field::{Field, FieldElem};
use crate::snarks::{
  r1cs::R1CS,
  polynomial::Polynomial,
};

pub struct QAP {
  pub f: Field,
  pub a_polys: Vec<Polynomial>,
  pub b_polys: Vec<Polynomial>,
  pub c_polys: Vec<Polynomial>,
}

impl QAP {
  // build a polynomial that returns target_val at x == index
  // and zero for x != index.
  // e.g. (x - 2) * (x - 3) * 3 / ((1 - 2) * (1 - 3))
  fn build_polynomial_for_target_values(
    f: &Field,
    target_vals: Vec<FieldElem>,
  ) -> Polynomial {
    let mut target_val_polys = vec![];
    let num_target_vals = target_vals.len();

    for (target_x, target_val) in target_vals.iter().enumerate() {
      let target_x = target_x + 1;  // make target_x one-based

      let mut numerator_polys = vec![
        Polynomial::new(f, vec![target_val.clone()]),
      ];
      let mut denominator = f.elem(&1u8);

      for i in 1..=num_target_vals {
        if i == target_x {
          continue;
        }

        // (x - i) to make the polynomal zero at x = i
        let numerator_poly = Polynomial::new(f, vec![
          -f.elem(&i),
          f.elem(&1u8),
        ]);
        println!("numerator_poly: {:?}", numerator_poly);
        numerator_polys.push(numerator_poly);

        // (target_idx - i) to cancel out the corresponding
        // numerator_poly at x = target_idx
        denominator = denominator * (f.elem(&target_x) - f.elem(&i));
      }

      // merge numerator and denominator
      let denominator_poly = Polynomial::new(f, vec![denominator.inv()]);
      let mut polys = numerator_polys;
      polys.push(denominator_poly);

      // aggregate polynomials
      let mut acc_poly = Polynomial::new(f, vec![f.elem(&1u8)]);
      for poly in polys {
        acc_poly = acc_poly.mul(&poly);
      }
      target_val_polys.push(acc_poly);
    }
    // aggregate polynomials for all target values
    let mut res = target_val_polys[0].clone();
    for x in &target_val_polys[1..] {
      res = res.add(x);
    }
    println!("poly={:?}", &res);
    res
  }

  pub fn build(f: &Field, r1cs: R1CS) -> QAP {
    let mut a_polys = vec![];
    let mut b_polys = vec![];
    let mut c_polys = vec![];

    /*
                 4 Polynomials
                     a1 a2
    a1 [0 3 0 0] ->  |0 0|
    a2 [0 0 0 2]     |3 0| <- need polynomial that returns
    +------^         |0 0|    3 at x=1 and 0 at x=2
    r1cs selector *  |0 2| <- here polynomial that retuns
    witness         x=1 x=2   0 at x=1 and 2 at x=2
    */
    println!("# of witnesses={}", r1cs.witness.size);

    for witness_idx in 0..r1cs.witness.size {
      println!("witness_idx={}", witness_idx);
      println!("# of constraints={}", r1cs.constraints.len());
      for i in 0..r1cs.constraints.len() {
        println!("a[{}] * w ={}", i, (&r1cs.constraints[i].a * &r1cs.witness).pretty_print());
      }
      for i in 0..r1cs.constraints.len() {
        println!("b[{}] * w ={}", i, (&r1cs.constraints[i].b * &r1cs.witness).pretty_print());
      }
      for i in 0..r1cs.constraints.len() {
        println!("c[{}] * w ={}", i, (&r1cs.constraints[i].c * &r1cs.witness).pretty_print());
      }

      let a_target_vals = r1cs.constraints.iter().map(|constraint| {
        (&constraint.a * &r1cs.witness)[&witness_idx].clone()
      }).collect::<Vec<FieldElem>>();
      let b_target_vals = r1cs.constraints.iter().map(|constraint| {
        (&constraint.b * &r1cs.witness)[&witness_idx].clone()
      }).collect::<Vec<FieldElem>>();
      let c_target_vals = r1cs.constraints.iter().map(|constraint| {
        (&constraint.c * &r1cs.witness)[&witness_idx].clone()
      }).collect::<Vec<FieldElem>>();
      use num_bigint::BigUint;
      println!("a_target_vals={:?}", a_target_vals.iter().map(|x| x.n.clone()).collect::<Vec<BigUint>>());
      println!("b_target_vals={:?}", b_target_vals.iter().map(|x| x.n.clone()).collect::<Vec<BigUint>>());
      println!("c_target_vals={:?}", c_target_vals.iter().map(|x| x.n.clone()).collect::<Vec<BigUint>>());

      a_polys.push(QAP::build_polynomial_for_target_values(f, a_target_vals));
      b_polys.push(QAP::build_polynomial_for_target_values(f, b_target_vals));
      c_polys.push(QAP::build_polynomial_for_target_values(f, c_target_vals));
    }

    QAP { f: f.clone(), a_polys, b_polys, c_polys }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::snarks::{
    sparse_vec::SparseVec,
    constraint::Constraint,
  };

  #[test]
  fn test1() {
    let f = &Field::new(&3911u16);

    //     x  out t1 y   t2
    //  0  1   2  3   4   5
    // [1, 3, 35, 9, 27, 30]
    let witness = SparseVec::of_vec(f, vec![
      f.elem(&1u8),
      f.elem(&3u8),
      f.elem(&35u8),
      f.elem(&9u8),
      f.elem(&27u8),
      f.elem(&30u8),
    ]);

    // A
    //  0  1  2  3  4  5
    // [0, 1, 0, 0, 0, 0]
    // [0, 0, 0, 1, 0, 0]
    // [0, 1, 0, 0, 1, 0]
    // [5, 0, 0, 0, 0, 1]
    let mut a1 = SparseVec::new(f, witness.size);
    a1.set(&1, f.elem(&1u8));

    let mut a2 = SparseVec::new(f, witness.size);
    a2.set(&3, f.elem(&1u8));

    let mut a3 = SparseVec::new(f, witness.size);
    a3.set(&1, f.elem(&1u8));
    a3.set(&4, f.elem(&1u8));

    let mut a4 = SparseVec::new(f, witness.size);
    a4.set(&0, f.elem(&5u8));
    a4.set(&5, f.elem(&1u8));

    // B
    //  0  1  2  3  4  5
    // [0, 1, 0, 0, 0, 0]
    // [0, 1, 0, 0, 0, 0]
    // [1, 0, 0, 0, 0, 0]
    // [1, 0, 0, 0, 0, 0]
    let mut b1 = SparseVec::new(f, witness.size);
    b1.set(&1, f.elem(&1u8));

    let mut b2 = SparseVec::new(f, witness.size);
    b2.set(&1, f.elem(&1u8));

    let mut b3 = SparseVec::new(f, witness.size);
    b3.set(&0, f.elem(&1u8));

    let mut b4 = SparseVec::new(f, witness.size);
    b4.set(&0, f.elem(&1u8));

    // C
    //  0  1  2  3  4  5
    // [0, 0, 0, 1, 0, 0]
    // [0, 0, 0, 0, 1, 0]
    // [0, 0, 0, 0, 0, 1]
    // [0, 0, 1, 0, 0, 0]
    let mut c1 = SparseVec::new(f, witness.size);
    c1.set(&3, f.elem(&1u8));

    let mut c2 = SparseVec::new(f, witness.size);
    c2.set(&4, f.elem(&1u8));

    let mut c3 = SparseVec::new(f, witness.size);
    c3.set(&5, f.elem(&1u8));

    let mut c4 = SparseVec::new(f, witness.size);
    c4.set(&2, f.elem(&1u8));

    let constraints = vec![
      Constraint::new(a1, b1, c1),
      Constraint::new(a2, b2, c2),
      Constraint::new(a3, b3, c3),
      Constraint::new(a4, b4, c4),
    ];
    let r1cs = R1CS { constraints, witness };

    let qap = QAP::build(f, r1cs);
    let a_poly = &qap.a_polys[3];
    let v = a_poly.eval_at(&2u8);
    println!("a_poly={:?}", v.n);

    for (poly_idx, poly) in qap.a_polys.iter().enumerate() {
      for i in 1u8..=4 {
        println!("a[{}] at x={}: {:?} = {:?}", poly_idx, i, poly, poly.eval_at(&i).n);
      }
    }
    println!("");
    for (poly_idx, poly) in qap.b_polys.iter().enumerate() {
      for i in 1u8..=4 {
        println!("b[{}] at x={}: {:?} = {:?}", poly_idx, i, poly, poly.eval_at(&i).n);
      }
    }
    println!("");
    for (poly_idx, poly) in qap.c_polys.iter().enumerate() {
      for i in 1u8..=4 {
        println!("c[{}] at x={}: {:?} = {:?}", poly_idx, i, poly, poly.eval_at(&i).n);
      }
    }
  }
}