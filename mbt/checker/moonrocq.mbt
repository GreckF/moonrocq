// Extracted from Rocq by rocq2mbt (MoonBit extraction).

pub fn negb(b : Bool) -> Bool {
  match b {
    true => false
    false => true
  }
}

pub(all) enum Nat {
  O
  S(Nat)
}

pub fn[A, B] option_map(f : (A) -> B, o : Option[A]) -> Option[B] {
  match o {
    Some(a) => Some(f(a))
    None => None
  }
}

pub fn[A, B] fst(p : (A, B)) -> A {
  match p {
    (x, _) => x
  }
}

pub fn[A, B] snd(p : (A, B)) -> B {
  match p {
    (_, y) => y
  }
}

pub(all) enum List[A] {
  Nil
  Cons(A, List[A])
}

pub fn[A] length(l : List[A]) -> Nat {
  match l {
    List::Nil => Nat::O
    List::Cons(_, l_) => Nat::S(length(l_))
  }
}

pub fn[A] app(l : List[A], m : List[A]) -> List[A] {
  match l {
    List::Nil => m
    List::Cons(a, l1) => List::Cons(a, app(l1, m))
  }
}

pub fn compOpp(r : @rocqrt.Comparison) -> @rocqrt.Comparison {
  match r {
    @rocqrt.Comparison::Eq => @rocqrt.Comparison::Eq
    @rocqrt.Comparison::Lt => @rocqrt.Comparison::Gt
    @rocqrt.Comparison::Gt => @rocqrt.Comparison::Lt
  }
}

// Sig : singleton inductive, expanded at use sites

pub(all) enum SigT[A, B] {
  ExistT(A, B)
}

pub(all) enum Sumor[A] {
  Inleft(A)
  Inright
}

pub fn add(n : Nat, m : Nat) -> Nat {
  match n {
    Nat::O => m
    Nat::S(p) => Nat::S(add(p, m))
  }
}

pub fn mul(n : Nat, m : Nat) -> Nat {
  match n {
    Nat::O => Nat::O
    Nat::S(p) => add(m, mul(p, m))
  }
}

pub type Array0[A] = Array[A]

pub type List_List[T0] = @list.List[T0]

pub fn bool_dec(b1 : Bool, b2 : Bool) -> Bool {
  match b1 {
    true => match b2 {
      true => true
      false => false
    }
    false => match b2 {
      true => false
      false => true
    }
  }
}

pub fn eqb(b1 : Bool, b2 : Bool) -> Bool {
  match b1 {
    true => b2
    false => match b2 {
      true => false
      false => true
    }
  }
}

pub fn eqb0(n : Nat, m : Nat) -> Bool {
  match n {
    Nat::O => match m {
      Nat::O => true
      Nat::S(_) => false
    }
    Nat::S(n_) => match m {
      Nat::O => false
      Nat::S(m_) => eqb0(n_, m_)
    }
  }
}

pub fn leb(n : Nat, m : Nat) -> Bool {
  match n {
    Nat::O => true
    Nat::S(n_) => match m {
      Nat::O => false
      Nat::S(m_) => leb(n_, m_)
    }
  }
}

pub fn ltb(n : Nat, m : Nat) -> Bool {
  leb(Nat::S(n), m)
}

pub fn eq_dec(n : Nat, m : Nat) -> Bool {
  match n {
    Nat::O => match m {
      Nat::O => true
      Nat::S(_) => false
    }
    Nat::S(n0) => match m {
      Nat::O => false
      Nat::S(n1) => eq_dec(n0, n1)
    }
  }
}

pub fn[A, B] map(f : (A) -> B, l : List[A]) -> List[B] {
  match l {
    List::Nil => List::Nil
    List::Cons(a, l0) => List::Cons(f(a), map(f, l0))
  }
}

pub fn seq(start : Nat, len : Nat) -> List[Nat] {
  match len {
    Nat::O => List::Nil
    Nat::S(len0) => List::Cons(start, seq(Nat::S(start), len0))
  }
}

pub fn[A] repeat(x : A, n : Nat) -> List[A] {
  match n {
    Nat::O => List::Nil
    Nat::S(k) => List::Cons(x, repeat(x, k))
  }
}

pub fn[A] nth(n : Nat, l : List[A], default : A) -> A {
  match n {
    Nat::O => match l {
      List::Nil => default
      List::Cons(x, _) => x
    }
    Nat::S(m) => match l {
      List::Nil => default
      List::Cons(_, l_) => nth(m, l_, default)
    }
  }
}

pub fn[A] firstn(n : Nat, l : List[A]) -> List[A] {
  match n {
    Nat::O => List::Nil
    Nat::S(n0) => match l {
      List::Nil => List::Nil
      List::Cons(a, l0) => List::Cons(a, firstn(n0, l0))
    }
  }
}

pub fn[A] skipn(n : Nat, l : List[A]) -> List[A] {
  match n {
    Nat::O => l
    Nat::S(n0) => match l {
      List::Nil => List::Nil
      List::Cons(_, l0) => skipn(n0, l0)
    }
  }
}

pub fn[A] hd_error(l : List[A]) -> Option[A] {
  match l {
    List::Nil => None
    List::Cons(x, _) => Some(x)
  }
}

pub fn[A] tl(l : List[A]) -> List[A] {
  match l {
    List::Nil => List::Nil
    List::Cons(_, l_) => l_
  }
}

pub fn[A] in_dec(h : (A) -> (A) -> Bool, a : A, l : List[A]) -> Bool {
  match l {
    List::Nil => false
    List::Cons(a0, l0) => {
      let s = h(a0)(a)
      match s {
        true => true
        false => in_dec(h, a, l0)
      }
    }
  }
}

pub fn[A] nth_error(l : List[A], n : Nat) -> Option[A] {
  match n {
    Nat::O => match l {
      List::Nil => None
      List::Cons(x, _) => Some(x)
    }
    Nat::S(n0) => match l {
      List::Nil => None
      List::Cons(_, l_) => nth_error(l_, n0)
    }
  }
}

pub fn[A] concat(l : List[List[A]]) -> List[A] {
  match l {
    List::Nil => List::Nil
    List::Cons(x, l0) => app(x, concat(l0))
  }
}

pub fn[A] list_eq_dec(eq_dec1 : (A) -> (A) -> Bool, l : List[A], l_ : List[A]) -> Bool {
  match l {
    List::Nil => match l_ {
      List::Nil => true
      List::Cons(_, _) => false
    }
    List::Cons(a, l0) => match l_ {
      List::Nil => false
      List::Cons(a0, l1) => match eq_dec1(a)(a0) {
        true => list_eq_dec(eq_dec1, l0, l1)
        false => false
      }
    }
  }
}

pub fn[A, B] flat_map(f : (A) -> List[B], l : List[A]) -> List[B] {
  match l {
    List::Nil => List::Nil
    List::Cons(x, l0) => app(f(x), flat_map(f, l0))
  }
}

pub fn[A, B] fold_left(f : (A) -> (B) -> A, l : List[B], a0 : A) -> A {
  match l {
    List::Nil => a0
    List::Cons(b, l0) => fold_left(f, l0, f(a0)(b))
  }
}

pub fn[A, B] fold_right(f : (B) -> (A) -> A, a0 : A, l : List[B]) -> A {
  match l {
    List::Nil => a0
    List::Cons(b, l0) => f(b)(fold_right(f, a0, l0))
  }
}

pub fn[A] existsb(f : (A) -> Bool, l : List[A]) -> Bool {
  match l {
    List::Nil => false
    List::Cons(a, l0) => match f(a) {
      true => true
      false => existsb(f, l0)
    }
  }
}

pub fn[A] forallb(f : (A) -> Bool, l : List[A]) -> Bool {
  match l {
    List::Nil => true
    List::Cons(a, l0) => match f(a) {
      true => forallb(f, l0)
      false => false
    }
  }
}

pub fn[A] filter(f : (A) -> Bool, l : List[A]) -> List[A] {
  match l {
    List::Nil => List::Nil
    List::Cons(x, l0) => match f(x) {
      true => List::Cons(x, filter(f, l0))
      false => filter(f, l0)
    }
  }
}

pub fn[A] find(f : (A) -> Bool, l : List[A]) -> Option[A] {
  match l {
    List::Nil => None
    List::Cons(x, tl0) => match f(x) {
      true => Some(x)
      false => find(f, tl0)
    }
  }
}

pub fn[A, B] combine(l : List[A], l_ : List[B]) -> List[(A, B)] {
  match l {
    List::Nil => List::Nil
    List::Cons(x, tl0) => match l_ {
      List::Nil => List::Nil
      List::Cons(y, tl_) => List::Cons((x, y), combine(tl0, tl_))
    }
  }
}

pub fn[A] nodup(decA : (A) -> (A) -> Bool, l : List[A]) -> List[A] {
  match l {
    List::Nil => List::Nil
    List::Cons(x, xs) => match in_dec(decA, x, xs) {
      true => nodup(decA, xs)
      false => List::Cons(x, nodup(decA, xs))
    }
  }
}

pub fn list_sum(l : List[Nat]) -> Nat {
  fold_right(fn(x1) { fn(x2) { add(x1, x2) } }, Nat::O, l)
}

pub(all) enum Result0[A, B] {
  Ok(A)
  Err(B)
}

pub fn[A, B, C] bind(m : Result0[A, C], k : (A) -> Result0[B, C]) -> Result0[B, C] {
  match m {
    Result0::Ok(a) => k(a)
    Result0::Err(e) => Result0::Err(e)
  }
}

pub fn[A, B, C] map_err(f : (B) -> C, m : Result0[A, B]) -> Result0[A, C] {
  match m {
    Result0::Ok(a) => Result0::Ok(a)
    Result0::Err(e) => Result0::Err(f(e))
  }
}

pub fn[A, B, C] mapM(f : (A) -> Result0[B, C], xs : List[A]) -> Result0[List[B], C] {
  match xs {
    List::Nil => Result0::Ok(List::Nil)
    List::Cons(x, xs_) => bind(f(x), fn(y) { bind(mapM(f, xs_), fn(ys) { Result0::Ok(List::Cons(y, ys)) }) })
  }
}

pub(all) enum Positive {
  XI(Positive)
  XO(Positive)
  XH
}

pub(all) enum N {
  N0
  Npos(Positive)
}

pub(all) enum Z {
  Z0
  Zpos(Positive)
  Zneg(Positive)
}

pub fn succ(x : Positive) -> Positive {
  match x {
    Positive::XI(p) => Positive::XO(succ(p))
    Positive::XO(p) => Positive::XI(p)
    Positive::XH => Positive::XO(Positive::XH)
  }
}

pub fn add0(x : Positive, y : Positive) -> Positive {
  match x {
    Positive::XI(p) => match y {
      Positive::XI(q) => Positive::XO(add_carry(p, q))
      Positive::XO(q) => Positive::XI(add0(p, q))
      Positive::XH => Positive::XO(succ(p))
    }
    Positive::XO(p) => match y {
      Positive::XI(q) => Positive::XI(add0(p, q))
      Positive::XO(q) => Positive::XO(add0(p, q))
      Positive::XH => Positive::XI(p)
    }
    Positive::XH => match y {
      Positive::XI(q) => Positive::XO(succ(q))
      Positive::XO(q) => Positive::XI(q)
      Positive::XH => Positive::XO(Positive::XH)
    }
  }
}

pub fn add_carry(x : Positive, y : Positive) -> Positive {
  match x {
    Positive::XI(p) => match y {
      Positive::XI(q) => Positive::XI(add_carry(p, q))
      Positive::XO(q) => Positive::XO(add_carry(p, q))
      Positive::XH => Positive::XI(succ(p))
    }
    Positive::XO(p) => match y {
      Positive::XI(q) => Positive::XO(add_carry(p, q))
      Positive::XO(q) => Positive::XI(add0(p, q))
      Positive::XH => Positive::XO(succ(p))
    }
    Positive::XH => match y {
      Positive::XI(q) => Positive::XI(succ(q))
      Positive::XO(q) => Positive::XO(succ(q))
      Positive::XH => Positive::XI(Positive::XH)
    }
  }
}

pub fn pred_double(x : Positive) -> Positive {
  match x {
    Positive::XI(p) => Positive::XI(Positive::XO(p))
    Positive::XO(p) => Positive::XI(pred_double(p))
    Positive::XH => Positive::XH
  }
}

pub fn mul0(x : Positive, y : Positive) -> Positive {
  match x {
    Positive::XI(p) => add0(y, Positive::XO(mul0(p, y)))
    Positive::XO(p) => Positive::XO(mul0(p, y))
    Positive::XH => y
  }
}

pub fn[A] iter(f : (A) -> A, x : A, n : Positive) -> A {
  match n {
    Positive::XI(n_) => f(iter(f, iter(f, x, n_), n_))
    Positive::XO(n_) => iter(f, iter(f, x, n_), n_)
    Positive::XH => f(x)
  }
}

pub fn compare_cont(r : @rocqrt.Comparison, x : Positive, y : Positive) -> @rocqrt.Comparison {
  match x {
    Positive::XI(p) => match y {
      Positive::XI(q) => compare_cont(r, p, q)
      Positive::XO(q) => compare_cont(@rocqrt.Comparison::Gt, p, q)
      Positive::XH => @rocqrt.Comparison::Gt
    }
    Positive::XO(p) => match y {
      Positive::XI(q) => compare_cont(@rocqrt.Comparison::Lt, p, q)
      Positive::XO(q) => compare_cont(r, p, q)
      Positive::XH => @rocqrt.Comparison::Gt
    }
    Positive::XH => match y {
      Positive::XH => r
      _ => @rocqrt.Comparison::Lt
    }
  }
}

pub let compare : (Positive) -> (Positive) -> @rocqrt.Comparison = fn(x1) { fn(x2) { compare_cont(@rocqrt.Comparison::Eq, x1, x2) } }

pub fn eqb1(p : Positive, q : Positive) -> Bool {
  match p {
    Positive::XI(p0) => match q {
      Positive::XI(q0) => eqb1(p0, q0)
      _ => false
    }
    Positive::XO(p0) => match q {
      Positive::XO(q0) => eqb1(p0, q0)
      _ => false
    }
    Positive::XH => match q {
      Positive::XH => true
      _ => false
    }
  }
}

pub fn double(x : Z) -> Z {
  match x {
    Z::Z0 => Z::Z0
    Z::Zpos(p) => Z::Zpos(Positive::XO(p))
    Z::Zneg(p) => Z::Zneg(Positive::XO(p))
  }
}

pub fn succ_double(x : Z) -> Z {
  match x {
    Z::Z0 => Z::Zpos(Positive::XH)
    Z::Zpos(p) => Z::Zpos(Positive::XI(p))
    Z::Zneg(p) => Z::Zneg(pred_double(p))
  }
}

pub fn pred_double0(x : Z) -> Z {
  match x {
    Z::Z0 => Z::Zneg(Positive::XH)
    Z::Zpos(p) => Z::Zpos(pred_double(p))
    Z::Zneg(p) => Z::Zneg(Positive::XI(p))
  }
}

pub fn pos_sub(x : Positive, y : Positive) -> Z {
  match x {
    Positive::XI(p) => match y {
      Positive::XI(q) => double(pos_sub(p, q))
      Positive::XO(q) => succ_double(pos_sub(p, q))
      Positive::XH => Z::Zpos(Positive::XO(p))
    }
    Positive::XO(p) => match y {
      Positive::XI(q) => pred_double0(pos_sub(p, q))
      Positive::XO(q) => double(pos_sub(p, q))
      Positive::XH => Z::Zpos(pred_double(p))
    }
    Positive::XH => match y {
      Positive::XI(q) => Z::Zneg(Positive::XO(q))
      Positive::XO(q) => Z::Zneg(pred_double(q))
      Positive::XH => Z::Z0
    }
  }
}

pub fn add1(x : Z, y : Z) -> Z {
  match x {
    Z::Z0 => y
    Z::Zpos(x_) => match y {
      Z::Z0 => x
      Z::Zpos(y_) => Z::Zpos(add0(x_, y_))
      Z::Zneg(y_) => pos_sub(x_, y_)
    }
    Z::Zneg(x_) => match y {
      Z::Z0 => x
      Z::Zpos(y_) => pos_sub(y_, x_)
      Z::Zneg(y_) => Z::Zneg(add0(x_, y_))
    }
  }
}

pub fn opp(x : Z) -> Z {
  match x {
    Z::Z0 => Z::Z0
    Z::Zpos(x0) => Z::Zneg(x0)
    Z::Zneg(x0) => Z::Zpos(x0)
  }
}

pub fn sub(m : Z, n : Z) -> Z {
  add1(m, opp(n))
}

pub fn mul1(x : Z, y : Z) -> Z {
  match x {
    Z::Z0 => Z::Z0
    Z::Zpos(x_) => match y {
      Z::Z0 => Z::Z0
      Z::Zpos(y_) => Z::Zpos(mul0(x_, y_))
      Z::Zneg(y_) => Z::Zneg(mul0(x_, y_))
    }
    Z::Zneg(x_) => match y {
      Z::Z0 => Z::Z0
      Z::Zpos(y_) => Z::Zneg(mul0(x_, y_))
      Z::Zneg(y_) => Z::Zpos(mul0(x_, y_))
    }
  }
}

pub fn pow_pos(z : Z) -> (Positive) -> Z {
  {
    let a1 = fn(x1) { mul1(z, x1) }
    fn(x1) { iter(a1, Z::Zpos(Positive::XH), x1) }
  }
}

pub fn pow(x : Z, y : Z) -> Z {
  match y {
    Z::Z0 => Z::Zpos(Positive::XH)
    Z::Zpos(p) => (pow_pos(x))(p)
    Z::Zneg(_) => Z::Z0
  }
}

pub fn compare0(x : Z, y : Z) -> @rocqrt.Comparison {
  match x {
    Z::Z0 => match y {
      Z::Z0 => @rocqrt.Comparison::Eq
      Z::Zpos(_) => @rocqrt.Comparison::Lt
      Z::Zneg(_) => @rocqrt.Comparison::Gt
    }
    Z::Zpos(x_) => match y {
      Z::Zpos(y_) => compare(x_)(y_)
      _ => @rocqrt.Comparison::Gt
    }
    Z::Zneg(x_) => match y {
      Z::Zneg(y_) => compOpp(compare(x_)(y_))
      _ => @rocqrt.Comparison::Lt
    }
  }
}

pub fn leb0(x : Z, y : Z) -> Bool {
  match compare0(x, y) {
    @rocqrt.Comparison::Gt => false
    _ => true
  }
}

pub fn ltb0(x : Z, y : Z) -> Bool {
  match compare0(x, y) {
    @rocqrt.Comparison::Lt => true
    _ => false
  }
}

pub fn eqb2(x : Z, y : Z) -> Bool {
  match x {
    Z::Z0 => match y {
      Z::Z0 => true
      _ => false
    }
    Z::Zpos(p) => match y {
      Z::Zpos(q) => eqb1(p, q)
      _ => false
    }
    Z::Zneg(p) => match y {
      Z::Zneg(q) => eqb1(p, q)
      _ => false
    }
  }
}

pub fn pos_div_eucl(a : Positive, b : Z) -> (Z, Z) {
  match a {
    Positive::XI(a_) => match pos_div_eucl(a_, b) {
      (q, r) => {
        let r_ = add1(mul1(Z::Zpos(Positive::XO(Positive::XH)), r), Z::Zpos(Positive::XH))
        match ltb0(r_, b) {
          true => (mul1(Z::Zpos(Positive::XO(Positive::XH)), q), r_)
          false => (add1(mul1(Z::Zpos(Positive::XO(Positive::XH)), q), Z::Zpos(Positive::XH)), sub(r_, b))
        }
      }
    }
    Positive::XO(a_) => match pos_div_eucl(a_, b) {
      (q, r) => {
        let r_ = mul1(Z::Zpos(Positive::XO(Positive::XH)), r)
        match ltb0(r_, b) {
          true => (mul1(Z::Zpos(Positive::XO(Positive::XH)), q), r_)
          false => (add1(mul1(Z::Zpos(Positive::XO(Positive::XH)), q), Z::Zpos(Positive::XH)), sub(r_, b))
        }
      }
    }
    Positive::XH => match leb0(Z::Zpos(Positive::XO(Positive::XH)), b) {
      true => (Z::Z0, Z::Zpos(Positive::XH))
      false => (Z::Zpos(Positive::XH), Z::Z0)
    }
  }
}

pub fn div_eucl(a : Z, b : Z) -> (Z, Z) {
  match a {
    Z::Z0 => (Z::Z0, Z::Z0)
    Z::Zpos(a_) => match b {
      Z::Z0 => (Z::Z0, a)
      Z::Zpos(_) => pos_div_eucl(a_, b)
      Z::Zneg(b_) => match pos_div_eucl(a_, Z::Zpos(b_)) {
        (q, r) => match r {
          Z::Z0 => (opp(q), Z::Z0)
          _ => (opp(add1(q, Z::Zpos(Positive::XH))), add1(b, r))
        }
      }
    }
    Z::Zneg(a_) => match b {
      Z::Z0 => (Z::Z0, a)
      Z::Zpos(_) => match pos_div_eucl(a_, b) {
        (q, r) => match r {
          Z::Z0 => (opp(q), Z::Z0)
          _ => (opp(add1(q, Z::Zpos(Positive::XH))), sub(b, r))
        }
      }
      Z::Zneg(b_) => match pos_div_eucl(a_, Z::Zpos(b_)) {
        (q, r) => (q, opp(r))
      }
    }
  }
}

pub fn modulo(a : Z, b : Z) -> Z {
  match div_eucl(a, b) {
    (_, r) => r
  }
}

pub fn geb(x : Z, y : Z) -> Bool {
  match compare0(x, y) {
    @rocqrt.Comparison::Lt => false
    _ => true
  }
}

pub(all) enum Ascii {
  Ascii0(Bool, Bool, Bool, Bool, Bool, Bool, Bool, Bool)
}

pub fn ascii_dec(a : Ascii, b : Ascii) -> Bool {
  match a {
    Ascii::Ascii0(b0, b1, b2, b3, b4, b5, b6, b7) => match b {
      Ascii::Ascii0(b8, b9, b10, b11, b12, b13, b14, b15) => match bool_dec(b0, b8) {
        true => match bool_dec(b1, b9) {
          true => match bool_dec(b2, b10) {
            true => match bool_dec(b3, b11) {
              true => match bool_dec(b4, b12) {
                true => match bool_dec(b5, b13) {
                  true => match bool_dec(b6, b14) {
                    true => bool_dec(b7, b15)
                    false => false
                  }
                  false => false
                }
                false => false
              }
              false => false
            }
            false => false
          }
          false => false
        }
        false => false
      }
    }
  }
}

pub fn eqb3(a : Ascii, b : Ascii) -> Bool {
  match a {
    Ascii::Ascii0(a0, a1, a2, a3, a4, a5, a6, a7) => match b {
      Ascii::Ascii0(b0, b1, b2, b3, b4, b5, b6, b7) => match (match (match (match (match (match (match eqb(a0, b0) {
        true => eqb(a1, b1)
        false => false
      }) {
        true => eqb(a2, b2)
        false => false
      }) {
        true => eqb(a3, b3)
        false => false
      }) {
        true => eqb(a4, b4)
        false => false
      }) {
        true => eqb(a5, b5)
        false => false
      }) {
        true => eqb(a6, b6)
        false => false
      }) {
        true => eqb(a7, b7)
        false => false
      }
    }
  }
}

pub(all) enum String0 {
  EmptyString
  String1(Ascii, String0)
}

pub fn string_dec(s : String0, x : String0) -> Bool {
  match s {
    String0::EmptyString => match x {
      String0::EmptyString => true
      String0::String1(_, _) => false
    }
    String0::String1(a, s0) => match x {
      String0::EmptyString => false
      String0::String1(a0, s1) => match ascii_dec(a, a0) {
        true => string_dec(s0, s1)
        false => false
      }
    }
  }
}

pub fn eqb4(s1 : String0, s2 : String0) -> Bool {
  match s1 {
    String0::EmptyString => match s2 {
      String0::EmptyString => true
      String0::String1(_, _) => false
    }
    String0::String1(c1, s1_) => match s2 {
      String0::EmptyString => false
      String0::String1(c2, s2_) => match eqb3(c1, c2) {
        true => eqb4(s1_, s2_)
        false => false
      }
    }
  }
}

pub fn append(s1 : String0, s2 : String0) -> String0 {
  match s1 {
    String0::EmptyString => s2
    String0::String1(c, s1_) => String0::String1(c, append(s1_, s2))
  }
}

pub type EqDec[A] = (A) -> (A) -> Bool
// singleton inductive, whose constructor was Build_EqDec

pub fn[A] eq_dec0(h : EqDec[A], x : A, y : A) -> Bool {
  let b = h(x)(y)
  match b {
    true => true
    false => false
  }
}

pub fn[A] eqb_of_dec(dec : (A) -> (A) -> Bool, x : A, y : A) -> Bool {
  match dec(x)(y) {
    true => true
    false => false
  }
}

pub fn[A] eqDec_of_dec() -> ((A) -> (A) -> Bool) -> EqDec[A] {
  fn(x1) { fn(x2) { fn(x3) { eqb_of_dec(x1, x2, x3) } } }
}

pub let eqDec_nat : EqDec[Nat] = fn(x1) { fn(x2) { eqb0(x1, x2) } }

pub let eqDec_string : EqDec[String0] = fn(x1) { fn(x2) { eqb4(x1, x2) } }

pub fn[A, B] prod_eqb(h : EqDec[A], h0 : EqDec[B], p : (A, B), q : (A, B)) -> Bool {
  match h(fst(p))(fst(q)) {
    true => h0(snd(p))(snd(q))
    false => false
  }
}

pub fn[A, B] eqDec_prod() -> (EqDec[A]) -> (EqDec[B]) -> EqDec[(A, B)] {
  fn(x1) { fn(x2) { fn(x3) { fn(x4) { prod_eqb(x1, x2, x3, x4) } } } }
}

pub fn[A] list_eqb(h : EqDec[A], xs : List[A], ys : List[A]) -> Bool {
  match xs {
    List::Nil => match ys {
      List::Nil => true
      List::Cons(_, _) => false
    }
    List::Cons(x, xs_) => match ys {
      List::Nil => false
      List::Cons(y, ys_) => match h(x)(y) {
        true => list_eqb(h, xs_, ys_)
        false => false
      }
    }
  }
}

pub fn[A] eqDec_list() -> (EqDec[A]) -> EqDec[List[A]] {
  fn(x1) { fn(x2) { fn(x3) { list_eqb(x1, x2, x3) } } }
}

pub type Ident = String0

pub let eqDec_ident : EqDec[Ident] = eqDec_string

pub(all) enum Int_kind {
  I16
  I32
  I64
  U16
  U32
  U64
  IByte
  IBigInt
}

pub(all) enum Base_ty {
  BUnit
  BBool
  BInt(Int_kind)
  BChar
  BDouble
  BFloat
  BString
  BNever
}

pub fn int_kind_eq_dec(x : Int_kind, y : Int_kind) -> Bool {
  match x {
    Int_kind::I16 => match y {
      Int_kind::I16 => true
      _ => false
    }
    Int_kind::I32 => match y {
      Int_kind::I32 => true
      _ => false
    }
    Int_kind::I64 => match y {
      Int_kind::I64 => true
      _ => false
    }
    Int_kind::U16 => match y {
      Int_kind::U16 => true
      _ => false
    }
    Int_kind::U32 => match y {
      Int_kind::U32 => true
      _ => false
    }
    Int_kind::U64 => match y {
      Int_kind::U64 => true
      _ => false
    }
    Int_kind::IByte => match y {
      Int_kind::IByte => true
      _ => false
    }
    Int_kind::IBigInt => match y {
      Int_kind::IBigInt => true
      _ => false
    }
  }
}

pub fn base_ty_eq_dec(x : Base_ty, y : Base_ty) -> Bool {
  match x {
    Base_ty::BUnit => match y {
      Base_ty::BUnit => true
      _ => false
    }
    Base_ty::BBool => match y {
      Base_ty::BBool => true
      _ => false
    }
    Base_ty::BInt(k) => match y {
      Base_ty::BInt(k0) => int_kind_eq_dec(k, k0)
      _ => false
    }
    Base_ty::BChar => match y {
      Base_ty::BChar => true
      _ => false
    }
    Base_ty::BDouble => match y {
      Base_ty::BDouble => true
      _ => false
    }
    Base_ty::BFloat => match y {
      Base_ty::BFloat => true
      _ => false
    }
    Base_ty::BString => match y {
      Base_ty::BString => true
      _ => false
    }
    Base_ty::BNever => match y {
      Base_ty::BNever => true
      _ => false
    }
  }
}

pub(all) enum Array_kind {
  AFixed
  AGrow
}

pub fn array_kind_eq_dec(x : Array_kind, y : Array_kind) -> Bool {
  match x {
    Array_kind::AFixed => match y {
      Array_kind::AFixed => true
      Array_kind::AGrow => false
    }
    Array_kind::AGrow => match y {
      Array_kind::AFixed => false
      Array_kind::AGrow => true
    }
  }
}

pub let eqDec_array_kind : EqDec[Array_kind] = eqDec_of_dec()(fn(x1) { fn(x2) { array_kind_eq_dec(x1, x2) } })

pub let eqDec_base_ty : EqDec[Base_ty] = eqDec_of_dec()(fn(x1) { fn(x2) { base_ty_eq_dec(x1, x2) } })

pub(all) enum Ty {
  TBase(Base_ty)
  TVar(Nat)
  TTuple(List[Ty])
  TArrow(List[Ty], Ty, Ty)
  TData(Ident, List[Ty])
  TRef(Ty)
  TArray(Array_kind, Ty)
  TError
}

pub fn[A] forall2b(f : (A) -> (A) -> Bool, xs : List[A], ys : List[A]) -> Bool {
  match xs {
    List::Nil => match ys {
      List::Nil => true
      List::Cons(_, _) => false
    }
    List::Cons(x, xs_) => match ys {
      List::Nil => false
      List::Cons(y, ys_) => match f(x)(y) {
        true => forall2b(f, xs_, ys_)
        false => false
      }
    }
  }
}

pub fn ty_eqb(a : Ty, b : Ty) -> Bool {
  match a {
    Ty::TBase(x) => match b {
      Ty::TBase(y) => eqDec_base_ty(x)(y)
      _ => false
    }
    Ty::TVar(i) => match b {
      Ty::TVar(j) => eqb0(i, j)
      _ => false
    }
    Ty::TTuple(xs) => match b {
      Ty::TTuple(ys) => forall2b(fn(x1) { fn(x2) { ty_eqb(x1, x2) } }, xs, ys)
      _ => false
    }
    Ty::TArrow(ps, r, _UU03b5_) => match b {
      Ty::TArrow(qs, s, _UU03b7_) => match (match forall2b(fn(x1) { fn(x2) { ty_eqb(x1, x2) } }, ps, qs) {
        true => ty_eqb(r, s)
        false => false
      }) {
        true => ty_eqb(_UU03b5_, _UU03b7_)
        false => false
      }
      _ => false
    }
    Ty::TData(t, ts) => match b {
      Ty::TData(u, us) => match eqDec_ident(t)(u) {
        true => forall2b(fn(x1) { fn(x2) { ty_eqb(x1, x2) } }, ts, us)
        false => false
      }
      _ => false
    }
    Ty::TRef(t) => match b {
      Ty::TRef(u) => ty_eqb(t, u)
      _ => false
    }
    Ty::TArray(k, t) => match b {
      Ty::TArray(k_, u) => match eqDec_array_kind(k)(k_) {
        true => ty_eqb(t, u)
        false => false
      }
      _ => false
    }
    Ty::TError => match b {
      Ty::TError => true
      _ => false
    }
  }
}

pub let eqDec_ty : EqDec[Ty] = fn(x1) { fn(x2) { ty_eqb(x1, x2) } }

pub let ty_eq_dec : (Ty) -> (Ty) -> Bool = fn(x1) { fn(x2) { eq_dec0(eqDec_ty, x1, x2) } }

pub(all) enum Lit {
  LUnit
  LBool(Bool)
  LInt(Int_kind, Z)
  LChar(Z)
  LDouble(Z)
  LFloat(Z)
  LString(List[Z])
}

pub fn lit_ty(l : Lit) -> Base_ty {
  match l {
    Lit::LUnit => Base_ty::BUnit
    Lit::LBool(_) => Base_ty::BBool
    Lit::LInt(k, _) => Base_ty::BInt(k)
    Lit::LChar(_) => Base_ty::BChar
    Lit::LDouble(_) => Base_ty::BDouble
    Lit::LFloat(_) => Base_ty::BFloat
    Lit::LString(_) => Base_ty::BString
  }
}

pub(all) enum Arith_op {
  AAdd
  ASub
  AMul
  ADiv
  AMod
}

pub(all) enum Cmp_op {
  CEq
  CNe
  CLt
  CLe
  CGt
  CGe
}

pub(all) enum Prim_op {
  PIntArith(Arith_op, Int_kind)
  PIntNeg(Int_kind)
  PIntCmp(Cmp_op, Int_kind)
  PCharCmp(Cmp_op)
  PBoolNot
  PBoolEq
  PStrConcat
  PStrEq
}

pub(all) enum Mem_op {
  MRef(Ty)
  MGet(Ty)
  MSet(Ty)
  MArray(Array_kind, Ty, Nat)
  MMake(Array_kind, Ty)
  MIndex(Array_kind, Ty)
  MSetIndex(Array_kind, Ty)
  MLength(Array_kind, Ty)
  MPush(Ty)
}

pub fn mem_sig(op : Mem_op) -> (List[Ty], Ty) {
  match op {
    Mem_op::MRef(t) => (List::Cons(t, List::Nil), Ty::TRef(t))
    Mem_op::MGet(t) => (List::Cons(Ty::TRef(t), List::Nil), t)
    Mem_op::MSet(t) => (List::Cons(Ty::TRef(t), List::Cons(t, List::Nil)), Ty::TBase(Base_ty::BUnit))
    Mem_op::MArray(k, t, n) => (repeat(t, n), Ty::TArray(k, t))
    Mem_op::MMake(k, t) => (List::Cons(Ty::TBase(Base_ty::BInt(Int_kind::I32)), List::Cons(t, List::Nil)), Ty::TArray(k, t))
    Mem_op::MIndex(k, t) => (List::Cons(Ty::TArray(k, t), List::Cons(Ty::TBase(Base_ty::BInt(Int_kind::I32)), List::Nil)), t)
    Mem_op::MSetIndex(k, t) => (List::Cons(Ty::TArray(k, t), List::Cons(Ty::TBase(Base_ty::BInt(Int_kind::I32)), List::Cons(t, List::Nil))), Ty::TBase(Base_ty::BUnit))
    Mem_op::MLength(k, t) => (List::Cons(Ty::TArray(k, t), List::Nil), Ty::TBase(Base_ty::BInt(Int_kind::I32)))
    Mem_op::MPush(t) => (List::Cons(Ty::TArray(Array_kind::AGrow, t), List::Cons(t, List::Nil)), Ty::TBase(Base_ty::BUnit))
  }
}

pub(all) enum Lty {
  LCell(Ty)
  LArr(Array_kind, Ty)
}

pub fn lty_ty(s : Lty) -> Ty {
  match s {
    Lty::LCell(t) => Ty::TRef(t)
    Lty::LArr(k, t) => Ty::TArray(k, t)
  }
}

pub type Styping = List[Lty]

pub(all) enum Ctl {
  CBreak
  CCont
}

pub type Lblctx = List[(List[Ty], Ty)]

pub fn ctl_ty(c : Ctl, lbl : (List[Ty], Ty)) -> Ty {
  match c {
    Ctl::CBreak => snd(lbl)
    Ctl::CCont => Ty::TTuple(fst(lbl))
  }
}

pub(all) enum Cctx {
  Mk_cctx(Lblctx, Ty)
}

pub fn push_lbl(lbl : (List[Ty], Ty), _UU039b_ : Cctx) -> Cctx {
  Cctx::Mk_cctx(List::Cons(lbl, match _UU039b_ {
    Cctx::Mk_cctx(cc_lbls, _) => cc_lbls
  }), match _UU039b_ {
    Cctx::Mk_cctx(_, cc_exn) => cc_exn
  })
}

pub fn with_exn(_UU03b5_ : Ty, _UU039b_ : Cctx) -> Cctx {
  Cctx::Mk_cctx(match _UU039b_ {
    Cctx::Mk_cctx(cc_lbls, _) => cc_lbls
  }, _UU03b5_)
}

pub let cc0 : Cctx = Cctx::Mk_cctx(List::Nil, Ty::TBase(Base_ty::BNever))

pub(all) enum Pat {
  PWild
  PVar
  PLit(Lit)
  PTuple(List[Pat])
  PConstr(Ident, List[Pat])
  PRef(Pat)
  PUp(Ident, Pat)
}

pub(all) enum Expr {
  EVar(Nat)
  EGlobal(Ident, List[Ty])
  ELit(Lit)
  ELam(List[Ty], Ty, Ty, Expr)
  EApp(Expr, List[Expr])
  ELet(Expr, Expr)
  EIf(Expr, Expr, Expr)
  ETuple(List[Expr])
  EProj(Expr, Nat)
  EPrim(Prim_op, List[Expr])
  EConstr(Ident, Ident, List[Ty], Expr)
  EMatch(Expr, Ty, List[(Pat, Expr)])
  ELoc(Nat)
  EMem(Mem_op, List[Expr])
  ELoop(Expr, List[Ty], Ty, Expr)
  EJump(Ctl, Nat, Expr, Ty)
  EAbort(Ty)
  EUp(Ident, Expr)
  ERaise(Expr, Ty)
  ETry(Expr, Ty, Expr, Expr)
  EDefer(Bool, Expr, Expr)
}

pub(all) enum Fdef {
  Mk_fdef(Ident, Nat, List[Ty], Ty, Ty, Expr)
}

pub(all) enum Cdef {
  Mk_cdef(Ident, List[Ty])
}

pub(all) enum Tdef {
  Mk_tdef(Ident, Nat, List[Cdef], Bool)
}

pub(all) enum Genv {
  Mk_genv(List[Tdef], List[Fdef])
}

pub fn lookup_fn(ge : Genv, f : Ident) -> Option[Fdef] {
  find(fn(fd) {
    eqDec_ident(match fd {
      Fdef::Mk_fdef(fd_name, _, _, _, _, _) => fd_name
    })(f)
  }, match ge {
    Genv::Mk_genv(_, ge_funs) => ge_funs
  })
}

pub fn lookup_ty(ge : Genv, t : Ident) -> Option[Tdef] {
  find(fn(td) {
    eqDec_ident(match td {
      Tdef::Mk_tdef(td_name, _, _, _) => td_name
    })(t)
  }, match ge {
    Genv::Mk_genv(ge_types, _) => ge_types
  })
}

pub fn lookup_ctor(td : Tdef, c : Ident) -> Option[Cdef] {
  find(fn(cd) {
    eqDec_ident(match cd {
      Cdef::Mk_cdef(cd_name, _) => cd_name
    })(c)
  }, match td {
    Tdef::Mk_tdef(_, _, td_ctors, _) => td_ctors
  })
}

pub fn prim_sig(op : Prim_op) -> (List[Ty], Ty) {
  match op {
    Prim_op::PIntArith(_, k) => (List::Cons(Ty::TBase(Base_ty::BInt(k)), List::Cons(Ty::TBase(Base_ty::BInt(k)), List::Nil)), Ty::TBase(Base_ty::BInt(k)))
    Prim_op::PIntNeg(k) => (List::Cons(Ty::TBase(Base_ty::BInt(k)), List::Nil), Ty::TBase(Base_ty::BInt(k)))
    Prim_op::PIntCmp(_, k) => (List::Cons(Ty::TBase(Base_ty::BInt(k)), List::Cons(Ty::TBase(Base_ty::BInt(k)), List::Nil)), Ty::TBase(Base_ty::BBool))
    Prim_op::PCharCmp(_) => (List::Cons(Ty::TBase(Base_ty::BChar), List::Cons(Ty::TBase(Base_ty::BChar), List::Nil)), Ty::TBase(Base_ty::BBool))
    Prim_op::PBoolNot => (List::Cons(Ty::TBase(Base_ty::BBool), List::Nil), Ty::TBase(Base_ty::BBool))
    Prim_op::PBoolEq => (List::Cons(Ty::TBase(Base_ty::BBool), List::Cons(Ty::TBase(Base_ty::BBool), List::Nil)), Ty::TBase(Base_ty::BBool))
    Prim_op::PStrConcat => (List::Cons(Ty::TBase(Base_ty::BString), List::Cons(Ty::TBase(Base_ty::BString), List::Nil)), Ty::TBase(Base_ty::BString))
    Prim_op::PStrEq => (List::Cons(Ty::TBase(Base_ty::BString), List::Cons(Ty::TBase(Base_ty::BString), List::Nil)), Ty::TBase(Base_ty::BBool))
  }
}

pub fn wrap_unsigned(n : Z, z : Z) -> Z {
  modulo(z, pow(Z::Zpos(Positive::XO(Positive::XH)), n))
}

pub fn wrap_signed(n : Z, z : Z) -> Z {
  let r = modulo(z, pow(Z::Zpos(Positive::XO(Positive::XH)), n))
  match geb(r, pow(Z::Zpos(Positive::XO(Positive::XH)), sub(n, Z::Zpos(Positive::XH)))) {
    true => sub(r, pow(Z::Zpos(Positive::XO(Positive::XH)), n))
    false => r
  }
}

pub fn wrap(k : Int_kind, z : Z) -> Z {
  match k {
    Int_kind::I16 => wrap_signed(Z::Zpos(Positive::XO(Positive::XO(Positive::XO(Positive::XO(Positive::XH))))), z)
    Int_kind::I32 => wrap_signed(Z::Zpos(Positive::XO(Positive::XO(Positive::XO(Positive::XO(Positive::XO(Positive::XH)))))), z)
    Int_kind::I64 => wrap_signed(Z::Zpos(Positive::XO(Positive::XO(Positive::XO(Positive::XO(Positive::XO(Positive::XO(Positive::XH))))))), z)
    Int_kind::U16 => wrap_unsigned(Z::Zpos(Positive::XO(Positive::XO(Positive::XO(Positive::XO(Positive::XH))))), z)
    Int_kind::U32 => wrap_unsigned(Z::Zpos(Positive::XO(Positive::XO(Positive::XO(Positive::XO(Positive::XO(Positive::XH)))))), z)
    Int_kind::U64 => wrap_unsigned(Z::Zpos(Positive::XO(Positive::XO(Positive::XO(Positive::XO(Positive::XO(Positive::XO(Positive::XH))))))), z)
    Int_kind::IByte => wrap_unsigned(Z::Zpos(Positive::XO(Positive::XO(Positive::XO(Positive::XH)))), z)
    Int_kind::IBigInt => z
  }
}

pub fn tsubst(_UU03c3_ : (Nat) -> Ty, t : Ty) -> Ty {
  match t {
    Ty::TVar(i) => _UU03c3_(i)
    Ty::TTuple(ts) => Ty::TTuple(map(fn(x1) { tsubst(_UU03c3_, x1) }, ts))
    Ty::TArrow(ps, r, _UU03b5_) => Ty::TArrow(map(fn(x1) { tsubst(_UU03c3_, x1) }, ps), tsubst(_UU03c3_, r), tsubst(_UU03c3_, _UU03b5_))
    Ty::TData(t0, ts) => Ty::TData(t0, map(fn(x1) { tsubst(_UU03c3_, x1) }, ts))
    Ty::TRef(t0) => Ty::TRef(tsubst(_UU03c3_, t0))
    Ty::TArray(k, t0) => Ty::TArray(k, tsubst(_UU03c3_, t0))
    x => x
  }
}

pub fn inst(ts : List[Ty], i : Nat) -> Ty {
  nth(i, ts, Ty::TBase(Base_ty::BUnit))
}

pub type Ctx = List[Ty]

pub fn err_wfb(ge : Genv, n : Nat, t : Ty) -> Bool {
  match t {
    Ty::TBase(b) => match b {
      Base_ty::BNever => true
      _ => false
    }
    Ty::TVar(i) => ltb(i, n)
    Ty::TData(t0, ts) => match ts {
      List::Nil => match lookup_ty(ge, t0) {
        Some(td) => match td {
          Tdef::Mk_tdef(_, _, _, td_err) => td_err
        }
        None => false
      }
      List::Cons(_, _) => false
    }
    Ty::TError => true
    _ => false
  }
}

pub fn ty_wfb(ge : Genv, n : Nat, t : Ty) -> Bool {
  match t {
    Ty::TVar(i) => ltb(i, n)
    Ty::TTuple(ts) => forallb(fn(x1) { ty_wfb(ge, n, x1) }, ts)
    Ty::TArrow(ps, r, _UU03b5_) => match (match forallb(fn(x1) { ty_wfb(ge, n, x1) }, ps) {
      true => ty_wfb(ge, n, r)
      false => false
    }) {
      true => err_wfb(ge, n, _UU03b5_)
      false => false
    }
    Ty::TData(t0, ts) => match lookup_ty(ge, t0) {
      Some(td) => match eqb0(length(ts), match td {
        Tdef::Mk_tdef(_, td_tparams, _, _) => td_tparams
      }) {
        true => forallb(fn(x1) { ty_wfb(ge, n, x1) }, ts)
        false => false
      }
      None => false
    }
    Ty::TRef(t0) => ty_wfb(ge, n, t0)
    Ty::TArray(_, t0) => ty_wfb(ge, n, t0)
    _ => true
  }
}

pub fn[A] memb(h : EqDec[A], x : A, l : List[A]) -> Bool {
  existsb(h(x), l)
}

pub fn[A] nodupb(h : EqDec[A], l : List[A]) -> Bool {
  match l {
    List::Nil => true
    List::Cons(x, l_) => match negb(memb(h, x, l_)) {
      true => nodupb(h, l_)
      false => false
    }
  }
}

pub fn[A] noDup_dec(h : EqDec[A], l : List[A]) -> Bool {
  let b = nodupb(h, l)
  match b {
    true => true
    false => false
  }
}

pub(all) enum Type_error {
  E_UnboundVar(Nat)
  E_UnknownGlobal(Ident)
  E_TypeArgArity(Ident, Nat, Nat)
  E_Mismatch(Ty, Ty)
  E_NotFunction(Ty)
  E_ArgArity(Nat, Nat)
  E_NotTuple(Ty)
  E_TupleIndex(Nat, Ty)
  E_DuplicateGlobal
  E_InGlobal(Ident, Type_error)
  E_UnknownType(Ident)
  E_UnknownCtor(Ident, Ident)
  E_NotData(Ty)
  E_PatArity(Nat, Nat)
  E_DuplicateType
  E_DuplicateCtor
  E_IllFormed(Ty)
  E_InType(Ident, Type_error)
  E_NotRef(Ty)
  E_UnboundLoc(Nat)
  E_UnknownLabel(Nat)
  E_Effect(Ty, Ty)
  E_NotError(Ident)
}

pub fn[A, B] of_option(o : Option[A], err : B) -> Result0[A, B] {
  match o {
    Some(a) => Result0::Ok(a)
    None => Result0::Err(err)
  }
}

pub fn expect_ty(expected : Ty, got : Ty) -> Result0[Unit, Type_error] {
  match ty_eq_dec(expected)(got) {
    true => Result0::Ok(())
    false => Result0::Err(Type_error::E_Mismatch(expected, got))
  }
}

pub fn expect_nat(expected : Nat, got : Nat, err : Type_error) -> Result0[Unit, Type_error] {
  match eq_dec(got, expected) {
    true => Result0::Ok(())
    false => Result0::Err(err)
  }
}

pub fn as_arrow(t : Ty) -> Result0[SigT[List[Ty], SigT[Ty, Ty]], Type_error] {
  match t {
    Ty::TArrow(ps, r, _UU03b5_) => Result0::Ok(SigT::ExistT(ps, SigT::ExistT(r, _UU03b5_)))
    _ => Result0::Err(Type_error::E_NotFunction(t))
  }
}

pub fn expect_eff(_UU03b5_ : Ty, _UU03c1_ : Ty) -> Result0[Unit, Type_error] {
  match ty_eq_dec(_UU03b5_)(Ty::TBase(Base_ty::BNever)) {
    true => Result0::Ok(())
    false => match ty_eq_dec(_UU03b5_)(_UU03c1_) {
      true => Result0::Ok(())
      false => Result0::Err(Type_error::E_Effect(_UU03b5_, _UU03c1_))
    }
  }
}

pub fn check_bool(b : Bool, err : Type_error) -> Result0[Unit, Type_error] {
  match b {
    true => Result0::Ok(())
    false => Result0::Err(err)
  }
}

pub fn as_tuple(t : Ty) -> Result0[List[Ty], Type_error] {
  match t {
    Ty::TTuple(ts) => Result0::Ok(ts)
    _ => Result0::Err(Type_error::E_NotTuple(t))
  }
}

pub fn as_ref(t : Ty) -> Result0[Ty, Type_error] {
  match t {
    Ty::TRef(u) => Result0::Ok(u)
    _ => Result0::Err(Type_error::E_NotRef(t))
  }
}

pub fn as_data(t : Ty) -> Result0[SigT[Ident, List[Ty]], Type_error] {
  match t {
    Ty::TData(t0, ts) => Result0::Ok(SigT::ExistT(t0, ts))
    _ => Result0::Err(Type_error::E_NotData(t))
  }
}

pub fn infer_list(ge : Genv, _UU03a3_ : Styping, _UU039b_ : Cctx, _UU0393_ : Ctx, inf : (Expr) -> Result0[Ty, Type_error], es : List[Expr]) -> Result0[List[Ty], Type_error] {
  match es {
    List::Nil => Result0::Ok(List::Nil)
    List::Cons(e, es_) => bind(inf(e), fn(x) {
      bind(infer_list(ge, _UU03a3_, _UU039b_, _UU0393_, inf, es_), fn(x0) { Result0::Ok(List::Cons(x, x0)) })
    })
  }
}

pub fn check_list(ge : Genv, _UU03a3_ : Styping, _UU039b_ : Cctx, _UU0393_ : Ctx, inf : (Expr) -> Result0[Ty, Type_error], es : List[Expr], _UU03c4_s : List[Ty]) -> Result0[Unit, Type_error] {
  match es {
    List::Nil => match _UU03c4_s {
      List::Nil => Result0::Ok(())
      List::Cons(_, _) => Result0::Err(Type_error::E_ArgArity(length(_UU03c4_s), length(es)))
    }
    List::Cons(e, es_) => match _UU03c4_s {
      List::Nil => Result0::Err(Type_error::E_ArgArity(length(_UU03c4_s), length(es)))
      List::Cons(_UU03c4_, _UU03c4_s_) => bind(inf(e), fn(x) {
        bind(expect_ty(_UU03c4_, x), fn(_) {
          bind(check_list(ge, _UU03a3_, _UU039b_, _UU0393_, inf, es_, _UU03c4_s_), fn(_) { Result0::Ok(()) })
        })
      })
    }
  }
}

pub fn check_pats(ge : Genv, cp : (Pat) -> (Ty) -> Result0[Ctx, Type_error], ps : List[Pat], _UU03c4_s : List[Ty]) -> Result0[Ctx, Type_error] {
  match ps {
    List::Nil => match _UU03c4_s {
      List::Nil => Result0::Ok(List::Nil)
      List::Cons(_, _) => Result0::Err(Type_error::E_PatArity(length(_UU03c4_s), length(ps)))
    }
    List::Cons(p, ps_) => match _UU03c4_s {
      List::Nil => Result0::Err(Type_error::E_PatArity(length(_UU03c4_s), length(ps)))
      List::Cons(_UU03c4_, _UU03c4_s_) => bind(cp(p)(_UU03c4_), fn(x) {
        bind(check_pats(ge, cp, ps_, _UU03c4_s_), fn(x0) { Result0::Ok(app(x, x0)) })
      })
    }
  }
}

pub fn check_pat(ge : Genv, p : Pat, _UU03c4_ : Ty) -> Result0[Ctx, Type_error] {
  match p {
    Pat::PWild => Result0::Ok(List::Nil)
    Pat::PVar => Result0::Ok(List::Cons(_UU03c4_, List::Nil))
    Pat::PLit(l) => bind(expect_ty(_UU03c4_, Ty::TBase(lit_ty(l))), fn(_) { Result0::Ok(List::Nil) })
    Pat::PTuple(ps) => bind(as_tuple(_UU03c4_), fn(x) {
      bind(expect_nat(length(x), length(ps), Type_error::E_PatArity(length(x), length(ps))), fn(_) {
        bind(check_pats(ge, fn(x1) { fn(x2) { check_pat(ge, x1, x2) } }, ps, x), fn(x0) { Result0::Ok(x0) })
      })
    })
    Pat::PConstr(c, ps) => bind(as_data(_UU03c4_), fn(x) {
      match x {
        SigT::ExistT(t, s) => bind(of_option(lookup_ty(ge, t), Type_error::E_UnknownType(t)), fn(x0) {
          bind(of_option(lookup_ctor(x0, c), Type_error::E_UnknownCtor(t, c)), fn(x1) {
            bind(expect_nat(length(match x1 {
              Cdef::Mk_cdef(_, cd_fields) => cd_fields
            }), length(ps), Type_error::E_PatArity(length(match x1 {
              Cdef::Mk_cdef(_, cd_fields) => cd_fields
            }), length(ps))), fn(_) {
              bind(check_pats(ge, fn(x3) { fn(x2) { check_pat(ge, x3, x2) } }, ps, map({ let a1 = fn(x2) { inst(s, x2) }; fn(x2) { tsubst(a1, x2) } }, match x1 {
                Cdef::Mk_cdef(_, cd_fields) => cd_fields
              })), fn(x2) { Result0::Ok(x2) })
            })
          })
        })
      }
    })
    Pat::PRef(p0) => bind(as_ref(_UU03c4_), fn(x) { bind(check_pat(ge, p0, x), fn(x0) { Result0::Ok(x0) }) })
    Pat::PUp(t, p0) => bind(expect_ty(Ty::TError, _UU03c4_), fn(_) {
      bind(check_pat(ge, p0, Ty::TData(t, List::Nil)), fn(x) { Result0::Ok(x) })
    })
  }
}

pub fn check_branches(ge : Genv, _UU03a3_ : Styping, _UU039b_ : Cctx, inf : (Ctx) -> (Expr) -> Result0[Ty, Type_error], _UU0393_ : Ctx, _UU03c4_s : Ty, _UU03c4_ : Ty, bs : List[(Pat, Expr)]) -> Result0[Unit, Type_error] {
  match bs {
    List::Nil => Result0::Ok(())
    List::Cons(p0, bs_) => match p0 {
      (p, b) => bind(check_pat(ge, p, _UU03c4_s), fn(x) {
        bind(inf(app(x, _UU0393_))(b), fn(x0) {
          bind(expect_ty(_UU03c4_, x0), fn(_) {
            bind(check_branches(ge, _UU03a3_, _UU039b_, inf, _UU0393_, _UU03c4_s, _UU03c4_, bs_), fn(_) { Result0::Ok(()) })
          })
        })
      })
    }
  }
}

pub fn infer(ge : Genv, _UU03a3_ : Styping, _UU039b_ : Cctx, _UU0393_ : Ctx, e : Expr) -> Result0[Ty, Type_error] {
  match e {
    Expr::EVar(x) => bind(of_option(nth_error(_UU0393_, x), Type_error::E_UnboundVar(x)), fn(x0) { Result0::Ok(x0) })
    Expr::EGlobal(f, ts) => bind(of_option(lookup_fn(ge, f), Type_error::E_UnknownGlobal(f)), fn(x) {
      bind(expect_nat(match x {
        Fdef::Mk_fdef(_, fd_tparams, _, _, _, _) => fd_tparams
      }, length(ts), Type_error::E_TypeArgArity(f, match x {
        Fdef::Mk_fdef(_, fd_tparams, _, _, _, _) => fd_tparams
      }, length(ts))), fn(_) {
        Result0::Ok(Ty::TArrow(map({ let a1 = fn(x1) { inst(ts, x1) }; fn(x1) { tsubst(a1, x1) } }, match x {
          Fdef::Mk_fdef(_, _, fd_params, _, _, _) => fd_params
        }), tsubst(fn(x1) { inst(ts, x1) }, match x {
          Fdef::Mk_fdef(_, _, _, fd_ret, _, _) => fd_ret
        }), tsubst(fn(x1) { inst(ts, x1) }, match x {
          Fdef::Mk_fdef(_, _, _, _, fd_eff, _) => fd_eff
        })))
      })
    })
    Expr::ELit(l) => Result0::Ok(Ty::TBase(lit_ty(l)))
    Expr::ELam(ps, r, _UU03b5_, b) => bind(infer(ge, _UU03a3_, Cctx::Mk_cctx(List::Nil, _UU03b5_), app(ps, _UU0393_), b), fn(x) {
      bind(expect_ty(r, x), fn(_) { Result0::Ok(Ty::TArrow(ps, r, _UU03b5_)) })
    })
    Expr::EApp(f, args) => bind(infer(ge, _UU03a3_, _UU039b_, _UU0393_, f), fn(x) {
      bind(as_arrow(x), fn(x0) {
        match x0 {
          SigT::ExistT(ps, s) => match s {
            SigT::ExistT(r, s0) => bind(expect_nat(length(ps), length(args), Type_error::E_ArgArity(length(ps), length(args))), fn(_) {
              bind(check_list(ge, _UU03a3_, _UU039b_, _UU0393_, fn(x1) { infer(ge, _UU03a3_, _UU039b_, _UU0393_, x1) }, args, ps), fn(_) {
                bind(expect_eff(s0, match _UU039b_ {
                  Cctx::Mk_cctx(_, cc_exn) => cc_exn
                }), fn(_) { Result0::Ok(r) })
              })
            })
          }
        }
      })
    })
    Expr::ELet(e1, e2) => bind(infer(ge, _UU03a3_, _UU039b_, _UU0393_, e1), fn(x) {
      bind(infer(ge, _UU03a3_, _UU039b_, List::Cons(x, _UU0393_), e2), fn(x0) { Result0::Ok(x0) })
    })
    Expr::EIf(c, t, e0) => bind(infer(ge, _UU03a3_, _UU039b_, _UU0393_, c), fn(x) {
      bind(expect_ty(Ty::TBase(Base_ty::BBool), x), fn(_) {
        bind(infer(ge, _UU03a3_, _UU039b_, _UU0393_, t), fn(x0) {
          bind(infer(ge, _UU03a3_, _UU039b_, _UU0393_, e0), fn(x1) { bind(expect_ty(x0, x1), fn(_) { Result0::Ok(x0) }) })
        })
      })
    })
    Expr::ETuple(es) => bind(infer_list(ge, _UU03a3_, _UU039b_, _UU0393_, fn(x1) { infer(ge, _UU03a3_, _UU039b_, _UU0393_, x1) }, es), fn(x) { Result0::Ok(Ty::TTuple(x)) })
    Expr::EProj(e0, i) => bind(infer(ge, _UU03a3_, _UU039b_, _UU0393_, e0), fn(x) {
      bind(as_tuple(x), fn(x0) {
        bind(of_option(nth_error(x0, i), Type_error::E_TupleIndex(i, x)), fn(x1) { Result0::Ok(x1) })
      })
    })
    Expr::EPrim(op, args) => bind(expect_nat(length(fst(prim_sig(op))), length(args), Type_error::E_ArgArity(length(fst(prim_sig(op))), length(args))), fn(_) {
      bind(check_list(ge, _UU03a3_, _UU039b_, _UU0393_, fn(x1) { infer(ge, _UU03a3_, _UU039b_, _UU0393_, x1) }, args, fst(prim_sig(op))), fn(_) { Result0::Ok(snd(prim_sig(op))) })
    })
    Expr::EConstr(t, c, ts, e0) => bind(of_option(lookup_ty(ge, t), Type_error::E_UnknownType(t)), fn(x) {
      bind(expect_nat(match x {
        Tdef::Mk_tdef(_, td_tparams, _, _) => td_tparams
      }, length(ts), Type_error::E_TypeArgArity(t, match x {
        Tdef::Mk_tdef(_, td_tparams, _, _) => td_tparams
      }, length(ts))), fn(_) {
        bind(of_option(lookup_ctor(x, c), Type_error::E_UnknownCtor(t, c)), fn(x0) {
          bind(infer(ge, _UU03a3_, _UU039b_, _UU0393_, e0), fn(x1) {
            bind(expect_ty(Ty::TTuple(map({ let a1 = fn(x2) { inst(ts, x2) }; fn(x2) { tsubst(a1, x2) } }, match x0 {
              Cdef::Mk_cdef(_, cd_fields) => cd_fields
            })), x1), fn(_) { Result0::Ok(Ty::TData(t, ts)) })
          })
        })
      })
    })
    Expr::EMatch(e0, _UU03c4_, bs) => bind(infer(ge, _UU03a3_, _UU039b_, _UU0393_, e0), fn(x) {
      bind(check_branches(ge, _UU03a3_, _UU039b_, fn(_UU0393__) { fn(e_) { infer(ge, _UU03a3_, _UU039b_, _UU0393__, e_) } }, _UU0393_, x, _UU03c4_, bs), fn(_) { Result0::Ok(_UU03c4_) })
    })
    Expr::ELoc(l) => bind(of_option(nth_error(_UU03a3_, l), Type_error::E_UnboundLoc(l)), fn(x) { Result0::Ok(lty_ty(x)) })
    Expr::EMem(op, args) => bind(expect_nat(length(fst(mem_sig(op))), length(args), Type_error::E_ArgArity(length(fst(mem_sig(op))), length(args))), fn(_) {
      bind(check_list(ge, _UU03a3_, _UU039b_, _UU0393_, fn(x1) { infer(ge, _UU03a3_, _UU039b_, _UU0393_, x1) }, args, fst(mem_sig(op))), fn(_) { Result0::Ok(snd(mem_sig(op))) })
    })
    Expr::ELoop(e0, ps, _UU03c4_, b) => bind(infer(ge, _UU03a3_, _UU039b_, _UU0393_, e0), fn(x) {
      bind(expect_ty(Ty::TTuple(ps), x), fn(_) {
        bind(infer(ge, _UU03a3_, push_lbl((ps, _UU03c4_), _UU039b_), app(ps, _UU0393_), b), fn(x0) { bind(expect_ty(_UU03c4_, x0), fn(_) { Result0::Ok(_UU03c4_) }) })
      })
    })
    Expr::EJump(c, k, e0, _UU03c4_) => bind(of_option(nth_error(match _UU039b_ {
      Cctx::Mk_cctx(cc_lbls, _) => cc_lbls
    }, k), Type_error::E_UnknownLabel(k)), fn(x) {
      bind(infer(ge, _UU03a3_, _UU039b_, _UU0393_, e0), fn(x0) { bind(expect_ty(ctl_ty(c, x), x0), fn(_) { Result0::Ok(_UU03c4_) }) })
    })
    Expr::EAbort(_UU03c4_) => Result0::Ok(_UU03c4_)
    Expr::EUp(t, e0) => bind(of_option(lookup_ty(ge, t), Type_error::E_UnknownType(t)), fn(x) {
      bind(check_bool(match x {
        Tdef::Mk_tdef(_, _, _, td_err) => td_err
      }, Type_error::E_NotError(t)), fn(_) {
        bind(infer(ge, _UU03a3_, _UU039b_, _UU0393_, e0), fn(x0) {
          bind(expect_ty(Ty::TData(t, List::Nil), x0), fn(_) { Result0::Ok(Ty::TError) })
        })
      })
    })
    Expr::ERaise(e0, _UU03c4_) => bind(infer(ge, _UU03a3_, _UU039b_, _UU0393_, e0), fn(x) {
      bind(expect_eff(x, match _UU039b_ {
        Cctx::Mk_cctx(_, cc_exn) => cc_exn
      }), fn(_) { Result0::Ok(_UU03c4_) })
    })
    Expr::ETry(e0, _UU03c4_e, h, k) => bind(infer(ge, _UU03a3_, with_exn(_UU03c4_e, _UU039b_), _UU0393_, e0), fn(x) {
      bind(infer(ge, _UU03a3_, _UU039b_, List::Cons(_UU03c4_e, _UU0393_), h), fn(x0) {
        bind(infer(ge, _UU03a3_, _UU039b_, List::Cons(x, _UU0393_), k), fn(x1) { bind(expect_ty(x0, x1), fn(_) { Result0::Ok(x0) }) })
      })
    })
    Expr::EDefer(_, c, e0) => bind(infer(ge, _UU03a3_, Cctx::Mk_cctx(List::Nil, match _UU039b_ {
      Cctx::Mk_cctx(_, cc_exn) => cc_exn
    }), _UU0393_, c), fn(_) {
      bind(infer(ge, _UU03a3_, _UU039b_, _UU0393_, e0), fn(x) { Result0::Ok(x) })
    })
  }
}

pub fn check_fdef(ge : Genv, fd : Fdef) -> Result0[Unit, Type_error] {
  map_err(fn(x) {
    Type_error::E_InGlobal(match fd {
      Fdef::Mk_fdef(fd_name, _, _, _, _, _) => fd_name
    }, x)
  }, bind(infer(ge, List::Nil, Cctx::Mk_cctx(List::Nil, match fd {
    Fdef::Mk_fdef(_, _, _, _, fd_eff, _) => fd_eff
  }), match fd {
    Fdef::Mk_fdef(_, _, fd_params, _, _, _) => fd_params
  }, match fd {
    Fdef::Mk_fdef(_, _, _, _, _, fd_body) => fd_body
  }), fn(x) {
    bind(expect_ty(match fd {
      Fdef::Mk_fdef(_, _, _, fd_ret, _, _) => fd_ret
    }, x), fn(_) { Result0::Ok(()) })
  }))
}

pub fn check_fdefs(ge : Genv, fds : List[Fdef]) -> Result0[Unit, Type_error] {
  match fds {
    List::Nil => Result0::Ok(())
    List::Cons(fd, fds_) => bind(check_fdef(ge, fd), fn(_) { bind(check_fdefs(ge, fds_), fn(_) { Result0::Ok(()) }) })
  }
}

pub fn[A] check_all(f : (A) -> Result0[Unit, Type_error], l : List[A]) -> Result0[Unit, Type_error] {
  match l {
    List::Nil => Result0::Ok(())
    List::Cons(a, l_) => bind(f(a), fn(_) { bind(check_all(f, l_), fn(_) { Result0::Ok(()) }) })
  }
}

pub fn check_nodup(l : List[Ident], err : Type_error) -> Result0[Unit, Type_error] {
  match noDup_dec(eqDec_ident, l) {
    true => Result0::Ok(())
    false => Result0::Err(err)
  }
}

pub fn check_wf(ge : Genv, n : Nat, t : Ty) -> Result0[Unit, Type_error] {
  check_bool(ty_wfb(ge, n, t), Type_error::E_IllFormed(t))
}

pub fn check_tdef(ge : Genv, td : Tdef) -> Result0[Unit, Type_error] {
  map_err(fn(x) {
    Type_error::E_InType(match td {
      Tdef::Mk_tdef(td_name, _, _, _) => td_name
    }, x)
  }, bind(check_nodup(map(fn(c) {
    match c {
      Cdef::Mk_cdef(cd_name, _) => cd_name
    }
  }, match td {
    Tdef::Mk_tdef(_, _, td_ctors, _) => td_ctors
  }), Type_error::E_DuplicateCtor), fn(_) {
    bind(check_all(fn(cd) {
      check_all({
        let a2 = match td {
          Tdef::Mk_tdef(_, td_tparams, _, _) => td_tparams
        }
        fn(x1) { check_wf(ge, a2, x1) }
      }, match cd {
        Cdef::Mk_cdef(_, cd_fields) => cd_fields
      })
    }, match td {
      Tdef::Mk_tdef(_, _, td_ctors, _) => td_ctors
    }), fn(_) { Result0::Ok(()) })
  }))
}

pub fn check_fsig(ge : Genv, fd : Fdef) -> Result0[Unit, Type_error] {
  map_err(fn(x) {
    Type_error::E_InGlobal(match fd {
      Fdef::Mk_fdef(fd_name, _, _, _, _, _) => fd_name
    }, x)
  }, bind(check_all({
    let a2 = match fd {
      Fdef::Mk_fdef(_, fd_tparams, _, _, _, _) => fd_tparams
    }
    fn(x1) { check_wf(ge, a2, x1) }
  }, match fd {
    Fdef::Mk_fdef(_, _, fd_params, _, _, _) => fd_params
  }), fn(_) {
    bind(check_wf(ge, match fd {
      Fdef::Mk_fdef(_, fd_tparams, _, _, _, _) => fd_tparams
    }, match fd {
      Fdef::Mk_fdef(_, _, _, fd_ret, _, _) => fd_ret
    }), fn(_) {
      bind(check_bool(err_wfb(ge, match fd {
        Fdef::Mk_fdef(_, fd_tparams, _, _, _, _) => fd_tparams
      }, match fd {
        Fdef::Mk_fdef(_, _, _, _, fd_eff, _) => fd_eff
      }), Type_error::E_IllFormed(match fd {
        Fdef::Mk_fdef(_, _, _, _, fd_eff, _) => fd_eff
      })), fn(_) { Result0::Ok(()) })
    })
  }))
}

pub fn check_genv(ge : Genv) -> Result0[Unit, Type_error] {
  bind(check_nodup(map(fn(t) {
    match t {
      Tdef::Mk_tdef(td_name, _, _, _) => td_name
    }
  }, match ge {
    Genv::Mk_genv(ge_types, _) => ge_types
  }), Type_error::E_DuplicateType), fn(_) {
    bind(check_all(fn(x1) { check_tdef(ge, x1) }, match ge {
      Genv::Mk_genv(ge_types, _) => ge_types
    }), fn(_) {
      bind(check_nodup(map(fn(f) {
        match f {
          Fdef::Mk_fdef(fd_name, _, _, _, _, _) => fd_name
        }
      }, match ge {
        Genv::Mk_genv(_, ge_funs) => ge_funs
      }), Type_error::E_DuplicateGlobal), fn(_) {
        bind(check_all(fn(x1) { check_fsig(ge, x1) }, match ge {
          Genv::Mk_genv(_, ge_funs) => ge_funs
        }), fn(_) {
          bind(check_fdefs(ge, match ge {
            Genv::Mk_genv(_, ge_funs) => ge_funs
          }), fn(_) { Result0::Ok(()) })
        })
      })
    })
  })
}

pub fn check_program(ge : Genv, e : Expr) -> Result0[Ty, Type_error] {
  bind(check_genv(ge), fn(_) {
    bind(infer(ge, List::Nil, cc0, List::Nil, e), fn(x) { Result0::Ok(x) })
  })
}

pub(all) enum Pos {
  Mk_pos(N, N)
}

pub(all) enum Sty {
  SName(Pos, Ident, List[Sty])
  STuple(Pos, List[Sty])
  SArrow(Pos, List[Sty], Sty, Option[Sty])
  SObj(Pos, Ident)
}

pub(all) enum Slit {
  SLUnit
  SLBool(Bool)
  SLInt(Option[Int_kind], Z)
  SLChar(Z)
  SLDouble(Z)
  SLFloat(Z)
  SLString(List[Z])
}

pub(all) enum Spat {
  SPWild(Pos)
  SPVar(Pos, Ident)
  SPLit(Pos, Slit)
  SPTuple(Pos, List[Spat])
  SPConstr(Pos, Option[Ident], Ident, List[Spat], Bool)
  SPRecord(Pos, List[(Ident, Spat)], Bool)
  SPAnnot(Pos, Spat, Sty)
}

pub(all) enum Sexpr {
  SVar(Pos, Ident)
  SLit(Pos, Slit)
  SApp(Pos, Sexpr, List[Sexpr])
  SInfix(Pos, Ident, Sexpr, Sexpr)
  SUnary(Pos, Ident, Sexpr)
  SLet(Pos, Option[Ident], Option[Sty], Sexpr, Sexpr)
  SIf(Pos, Sexpr, Sexpr, Option[Sexpr])
  STup(Pos, List[Sexpr])
  SProj(Pos, Sexpr, Nat)
  SLam(Pos, List[(Ident, Option[Sty])], Option[Sty], Option[Option[Sty]], Sexpr)
  SAnnot(Pos, Sexpr, Sty)
  SConstr(Pos, Option[Ident], Ident)
  SRecord(Pos, Option[Ident], List[(Ident, Sexpr)])
  SField(Pos, Sexpr, Ident)
  SMatch(Pos, Sexpr, List[(Spat, Sexpr)])
  SLetMut(Pos, Ident, Option[Sty], Sexpr, Sexpr)
  SAssign(Pos, Ident, Option[Ident], Sexpr)
  SArray(Pos, List[Sexpr])
  SIndex(Pos, Sexpr, Sexpr)
  SIndexSet(Pos, Sexpr, Sexpr, Option[Ident], Sexpr)
  SFieldSet(Pos, Sexpr, Ident, Option[Ident], Sexpr)
  SMethod(Pos, Sexpr, Ident, List[Sexpr])
  SQual(Pos, Ident, Ident)
  SWhile(Pos, Option[Ident], Sexpr, Sexpr, Option[Sexpr])
  SFor(Pos, Option[Ident], List[(Ident, Sexpr)], Option[Sexpr], List[(Ident, Sexpr)], Sexpr, Option[Sexpr])
  SBlock(Pos, Ident, Sexpr)
  SBreak(Pos, Option[Ident], Option[Sexpr])
  SContinue(Pos, Option[Ident], List[Sexpr])
  SReturn(Pos, Option[Sexpr])
  SForIn(Pos, Option[Ident], List[Spat], Sexpr, List[(Ident, Sexpr)], List[(Ident, Sexpr)], Sexpr, Option[Sexpr])
  SRaise(Pos, Sexpr)
  STry(Pos, Sexpr, List[(Spat, Sexpr)], Option[List[(Spat, Sexpr)]])
  STryBang(Pos, Sexpr)
  SDefer(Pos, Bool, Sexpr, Sexpr)
  SAs(Pos, Sexpr, Ident)
}

pub(all) enum Sfun {
  Mk_sfun(Pos, Option[Ident], Ident, List[Ident], List[(Ident, Ident)], List[(Ident, Sty)], Option[Sty], Option[Sty], Sexpr)
}

pub(all) enum Sdecl {
  SDEnum(List[(Ident, List[Sty])])
  SDStruct(List[((Ident, Bool), Sty)])
  SDTupleStruct(List[Sty])
  SDError(List[(Ident, List[Sty])])
}

pub(all) enum Stype {
  Mk_stype(Pos, Ident, List[Ident], Sdecl)
}

pub(all) enum Smeth {
  Mk_smeth(Ident, List[Sty], Sty, Option[Sty], Bool)
}

pub(all) enum Strait {
  Mk_strait(Pos, Ident, List[Ident], List[Smeth])
}

pub(all) enum Simethod {
  Mk_simethod(Ident, List[(Ident, Option[Sty])], Option[Sty], Option[Sty], Sexpr)
}

pub(all) enum Simpl {
  Mk_simpl(Pos, List[Ident], List[(Ident, Ident)], Ident, Option[Sty], Option[Simethod])
}

pub(all) enum Sprog {
  Mk_sprog(List[Stype], List[Strait], List[Simpl], List[Sfun], Option[Sexpr])
}

pub fn sexpr_pos(e : Sexpr) -> Pos {
  match e {
    Sexpr::SVar(p, _) => p
    Sexpr::SLit(p, _) => p
    Sexpr::SApp(p, _, _) => p
    Sexpr::SInfix(p, _, _, _) => p
    Sexpr::SUnary(p, _, _) => p
    Sexpr::SLet(p, _, _, _, _) => p
    Sexpr::SIf(p, _, _, _) => p
    Sexpr::STup(p, _) => p
    Sexpr::SProj(p, _, _) => p
    Sexpr::SLam(p, _, _, _, _) => p
    Sexpr::SAnnot(p, _, _) => p
    Sexpr::SConstr(p, _, _) => p
    Sexpr::SRecord(p, _, _) => p
    Sexpr::SField(p, _, _) => p
    Sexpr::SMatch(p, _, _) => p
    Sexpr::SLetMut(p, _, _, _, _) => p
    Sexpr::SAssign(p, _, _, _) => p
    Sexpr::SArray(p, _) => p
    Sexpr::SIndex(p, _, _) => p
    Sexpr::SIndexSet(p, _, _, _, _) => p
    Sexpr::SFieldSet(p, _, _, _, _) => p
    Sexpr::SMethod(p, _, _, _) => p
    Sexpr::SQual(p, _, _) => p
    Sexpr::SWhile(p, _, _, _, _) => p
    Sexpr::SFor(p, _, _, _, _, _, _) => p
    Sexpr::SBlock(p, _, _) => p
    Sexpr::SBreak(p, _, _) => p
    Sexpr::SContinue(p, _, _) => p
    Sexpr::SReturn(p, _) => p
    Sexpr::SForIn(p, _, _, _, _, _, _, _) => p
    Sexpr::SRaise(p, _) => p
    Sexpr::STry(p, _, _, _) => p
    Sexpr::STryBang(p, _) => p
    Sexpr::SDefer(p, _, _, _) => p
    Sexpr::SAs(p, _, _) => p
  }
}

pub(all) enum Head {
  HBase(Base_ty)
  HTuple(Nat)
  HData(Ident)
  HRef
  HArray(Array_kind)
  HError
}

pub fn head_eq_dec(x : Head, y : Head) -> Bool {
  match x {
    Head::HBase(b) => match y {
      Head::HBase(b0) => eq_dec0(eqDec_base_ty, b, b0)
      _ => false
    }
    Head::HTuple(n) => match y {
      Head::HTuple(n0) => eq_dec0(eqDec_nat, n, n0)
      _ => false
    }
    Head::HData(t) => match y {
      Head::HData(t0) => eq_dec0(eqDec_ident, t, t0)
      _ => false
    }
    Head::HRef => match y {
      Head::HRef => true
      _ => false
    }
    Head::HArray(k) => match y {
      Head::HArray(k0) => eq_dec0(eqDec_array_kind, k, k0)
      _ => false
    }
    Head::HError => match y {
      Head::HError => true
      _ => false
    }
  }
}

pub let eqDec_head : EqDec[Head] = eqDec_of_dec()(fn(x1) { fn(x2) { head_eq_dec(x1, x2) } })

pub fn head_args(_UU03c4_ : Ty) -> Option[(Head, List[Ty])] {
  match _UU03c4_ {
    Ty::TBase(b) => Some((Head::HBase(b), List::Nil))
    Ty::TTuple(ts) => Some((Head::HTuple(length(ts)), ts))
    Ty::TData(t, ts) => Some((Head::HData(t), ts))
    Ty::TRef(t) => Some((Head::HRef, List::Cons(t, List::Nil)))
    Ty::TArray(k, t) => Some((Head::HArray(k), List::Cons(t, List::Nil)))
    Ty::TError => Some((Head::HError, List::Nil))
    _ => None
  }
}

pub fn head_args_sig(_UU03c4_ : Ty) -> Option[(Head, List[Ty])] {
  match head_args(_UU03c4_) {
    Some(p) => Some(p)
    None => None
  }
}

pub(all) enum Idef {
  Mk_idef(Ident, Head, Nat, List[(Ident, Nat)], Ident)
}

pub type Assumption = ((Ident, Ty), Expr)

pub fn find_assume(tr : Ident, _UU03c4_ : Ty, l : List[Assumption]) -> Option[Expr] {
  match l {
    List::Nil => None
    List::Cons(a, l_) => match a {
      (p, d_) => match eq_dec0(eqDec_prod()(eqDec_ident)(eqDec_ty), p, (tr, _UU03c4_)) {
        true => Some(d_)
        false => find_assume(tr, _UU03c4_, l_)
      }
    }
  }
}

pub fn find_assumption(_UU0398_ : List[Assumption], tr : Ident, _UU03c4_ : Ty) -> Option[Expr] {
  find_assume(tr, _UU03c4_, _UU0398_)
}

pub fn[A] opt_sig(o : Option[A]) -> Option[A] {
  match o {
    Some(a) => Some(a)
    None => None
  }
}

pub fn resolve_ctx(i : List[Idef], _UU0398_ : List[Assumption], rs : (Ident) -> (Ty) -> Option[Expr], args : List[Ty], ctx : List[(Ident, Nat)]) -> Option[List[Expr]] {
  match ctx {
    List::Nil => Some(List::Nil)
    List::Cons(p, ctx_) => match p {
      (tr_, i0) => match opt_sig(nth_error(args, i0)) {
        Some(s) => match resolve_ctx(i, _UU0398_, rs, args, ctx_) {
          Some(s0) => match rs(tr_)(s) {
            Some(s1) => Some(List::Cons(s1, s0))
            None => None
          }
          None => None
        }
        None => None
      }
    }
  }
}

pub fn resolve_insts(i : List[Idef], _UU0398_ : List[Assumption], tr : Ident, _UU03c4_ : Ty, h : Head, args : List[Ty], rc : (List[(Ident, Nat)]) -> Option[List[Expr]], j : List[Idef]) -> Option[Expr] {
  match j {
    List::Nil => None
    List::Cons(id, j_) => {
      let rest = resolve_insts(i, _UU0398_, tr, _UU03c4_, h, args, rc, j_)
      match eq_dec0(eqDec_ident, match id {
        Idef::Mk_idef(in_trait, _, _, _, _) => in_trait
      }, tr) {
        true => match eq_dec0(eqDec_head, match id {
          Idef::Mk_idef(_, in_head, _, _, _) => in_head
        }, h) {
          true => match eq_dec(length(args), match id {
            Idef::Mk_idef(_, _, in_arity, _, _) => in_arity
          }) {
            true => match rc(match id {
              Idef::Mk_idef(_, _, _, in_ctx, _) => in_ctx
            }) {
              Some(s) => Some(Expr::EApp(Expr::EGlobal(match id {
                Idef::Mk_idef(_, _, _, _, in_fun) => in_fun
              }, args), s))
              None => rest
            }
            false => rest
          }
          false => rest
        }
        false => rest
      }
    }
  }
}

pub fn resolve_dict(i : List[Idef], _UU0398_ : List[Assumption], n : Nat, tr : Ident, _UU03c4_ : Ty) -> Option[Expr] {
  match find_assumption(_UU0398_, tr, _UU03c4_) {
    Some(s) => Some(s)
    None => match n {
      Nat::O => None
      Nat::S(n_) => match head_args_sig(_UU03c4_) {
        Some(s) => match s {
          (h, args) => resolve_insts(i, _UU0398_, tr, _UU03c4_, h, args, {
            let a3 = fn(x1) { fn(x2) { resolve_dict(i, _UU0398_, n_, x1, x2) } }
            fn(x1) { resolve_ctx(i, _UU0398_, a3, args, x1) }
          }, i)
        }
        None => None
      }
    }
  }
}

pub fn ty_size(t : Ty) -> Nat {
  match t {
    Ty::TTuple(ts) => Nat::S(list_sum(map(fn(x1) { ty_size(x1) }, ts)))
    Ty::TArrow(ps, r, _UU03b5_) => Nat::S(add(add(list_sum(map(fn(x1) { ty_size(x1) }, ps)), ty_size(r)), ty_size(_UU03b5_)))
    Ty::TData(_, ts) => Nat::S(list_sum(map(fn(x1) { ty_size(x1) }, ts)))
    Ty::TRef(t0) => Nat::S(ty_size(t0))
    Ty::TArray(_, t0) => Nat::S(ty_size(t0))
    _ => Nat::S(Nat::O)
  }
}

pub fn entails_dec(i : List[Idef], _UU0398_ : List[Assumption], tr : Ident, _UU03c4_ : Ty) -> Sumor[Expr] {
  let o = resolve_dict(i, _UU0398_, ty_size(_UU03c4_), tr, _UU03c4_)
  match o {
    Some(s) => Sumor::Inleft(s)
    None => Sumor::Inright
  }
}

pub fn coherent_dec(i : List[Idef]) -> Bool {
  noDup_dec(eqDec_prod()(eqDec_ident)(eqDec_head), map(fn(id) {
    (match id {
      Idef::Mk_idef(in_trait, _, _, _, _) => in_trait
    }, match id {
      Idef::Mk_idef(_, in_head, _, _, _) => in_head
    })
  }, i))
}

pub(all) enum Elab_error {
  EE_Unbound(Pos, Ident)
  EE_UnknownType(Pos, Ident)
  EE_TypeArgs(Pos, Ident, Nat, Nat)
  EE_CannotInfer(Pos, Ident)
  EE_LambdaParam(Pos, Ident)
  EE_IntRange(Pos, Int_kind, Z)
  EE_NoOperator(Pos, Ident, Ty)
  EE_Annot(Pos, Ty, Ty)
  EE_Type(Pos, Type_error)
  EE_UnknownCtor(Pos, Ident)
  EE_AmbiguousCtor(Pos, Ident)
  EE_CtorArity(Pos, Ident, Nat, Nat)
  EE_NotRecord(Pos, Ty)
  EE_UnknownField(Pos, Ident)
  EE_MissingField(Pos, Ident)
  EE_PatType(Pos, Ty)
  EE_EmptyMatch(Pos)
  EE_NotMutable(Pos, Ident)
  EE_NoTarget(Pos)
  EE_BadContinue(Pos, Nat, Nat)
  EE_NoMethod(Pos, Ident, Ty)
  EE_NotError(Pos, Ty)
  EE_NoInstance(Pos, Ident, Ty)
  EE_AmbiguousMethod(Pos, Ident)
  EE_MissingMethod(Pos, Ident, Ident)
  EE_Overlap(Pos)
  EE_NotObjectSafe(Pos, Ident)
  EE_Unsupported(Pos, Ident)
}

pub fn[A] assoc(x : Ident, l : List[(Ident, A)]) -> Option[A] {
  match l {
    List::Nil => None
    List::Cons(p, l_) => match p {
      (y, a) => match eqDec_ident(x)(y) {
        true => Some(a)
        false => assoc(x, l_)
      }
    }
  }
}

pub fn index_of(x : Ident, l : List[Ident]) -> Option[Nat] {
  match l {
    List::Nil => None
    List::Cons(y, l_) => match eqDec_ident(x)(y) {
      true => Some(Nat::O)
      false => option_map(fn(x0) { Nat::S(x0) }, index_of(x, l_))
    }
  }
}

pub fn[A] set_nth(i : Nat, x : A, l : List[A]) -> List[A] {
  match l {
    List::Nil => List::Nil
    List::Cons(y, l_) => match i {
      Nat::O => List::Cons(x, l_)
      Nat::S(i_) => List::Cons(y, set_nth(i_, x, l_))
    }
  }
}

pub fn[A] all_some(l : List[Option[A]]) -> Option[List[A]] {
  match l {
    List::Nil => Some(List::Nil)
    List::Cons(o, l_) => match o {
      Some(a) => option_map(fn(x) { List::Cons(a, x) }, all_some(l_))
      None => None
    }
  }
}

pub fn[A] of_opt(o : Option[A], e : Elab_error) -> Result0[A, Elab_error] {
  match o {
    Some(a) => Result0::Ok(a)
    None => Result0::Err(e)
  }
}

pub fn array_kind_of(n : Ident) -> Option[Array_kind] {
  match eqDec_ident(n)(String0::String1(Ascii::Ascii0(true, false, false, false, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, true, true, true, false), String0::EmptyString)))))) {
    true => Some(Array_kind::AGrow)
    false => match eqDec_ident(n)(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, true, true, true, false), String0::EmptyString))))))))))) {
      true => Some(Array_kind::AFixed)
      false => None
    }
  }
}

pub let builtin_types : List[(Ident, Ty)] = List::Cons((String0::String1(Ascii::Ascii0(true, false, true, false, true, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))), Ty::TBase(Base_ty::BUnit)), List::Cons((String0::String1(Ascii::Ascii0(false, true, false, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))), Ty::TBase(Base_ty::BBool)), List::Cons((String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))), Ty::TBase(Base_ty::BInt(Int_kind::I32))), List::Cons((String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, true, true, false, false), String0::String1(Ascii::Ascii0(false, true, true, false, true, true, false, false), String0::EmptyString))))), Ty::TBase(Base_ty::BInt(Int_kind::I16))), List::Cons((String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, true, true, false, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, false, false), String0::EmptyString))))), Ty::TBase(Base_ty::BInt(Int_kind::I64))), List::Cons((String0::String1(Ascii::Ascii0(true, false, true, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))), Ty::TBase(Base_ty::BInt(Int_kind::U32))), List::Cons((String0::String1(Ascii::Ascii0(true, false, true, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, true, true, false, false), String0::String1(Ascii::Ascii0(false, true, true, false, true, true, false, false), String0::EmptyString)))))), Ty::TBase(Base_ty::BInt(Int_kind::U16))), List::Cons((String0::String1(Ascii::Ascii0(true, false, true, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, true, true, false, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, false, false), String0::EmptyString)))))), Ty::TBase(Base_ty::BInt(Int_kind::U64))), List::Cons((String0::String1(Ascii::Ascii0(false, true, false, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString)))), Ty::TBase(Base_ty::BInt(Int_kind::IByte))), List::Cons((String0::String1(Ascii::Ascii0(false, true, false, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))), Ty::TBase(Base_ty::BInt(Int_kind::IBigInt))), List::Cons((String0::String1(Ascii::Ascii0(true, true, false, false, false, false, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::EmptyString)))), Ty::TBase(Base_ty::BChar)), List::Cons((String0::String1(Ascii::Ascii0(false, false, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString)))))), Ty::TBase(Base_ty::BDouble)), List::Cons((String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))))), Ty::TBase(Base_ty::BFloat)), List::Cons((String0::String1(Ascii::Ascii0(true, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, false, true, true, false), String0::EmptyString)))))), Ty::TBase(Base_ty::BString)), List::Cons((String0::String1(Ascii::Ascii0(true, false, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::EmptyString))))), Ty::TError), List::Nil)))))))))))))))

pub let ref_tdef : Tdef = Tdef::Mk_tdef(String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString))), Nat::S(Nat::O), List::Cons(Cdef::Mk_cdef(String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString))), List::Cons(Ty::TRef(Ty::TVar(Nat::O)), List::Nil)), List::Nil), false)

pub let option_tdef : Tdef = Tdef::Mk_tdef(String0::String1(Ascii::Ascii0(true, true, true, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::EmptyString)))))), Nat::S(Nat::O), List::Cons(Cdef::Mk_cdef(String0::String1(Ascii::Ascii0(false, true, true, true, false, false, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString)))), List::Nil), List::Cons(Cdef::Mk_cdef(String0::String1(Ascii::Ascii0(true, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString)))), List::Cons(Ty::TVar(Nat::O), List::Nil)), List::Nil)), false)

pub let result_tdef : Tdef = Tdef::Mk_tdef(String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))), Nat::S(Nat::S(Nat::O)), List::Cons(Cdef::Mk_cdef(String0::String1(Ascii::Ascii0(true, true, true, true, false, false, true, false), String0::String1(Ascii::Ascii0(true, true, false, true, false, true, true, false), String0::EmptyString)), List::Cons(Ty::TVar(Nat::O), List::Nil)), List::Cons(Cdef::Mk_cdef(String0::String1(Ascii::Ascii0(true, false, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::EmptyString))), List::Cons(Ty::TVar(Nat::S(Nat::O)), List::Nil)), List::Nil)), false)

pub let failure_tdef : Tdef = Tdef::Mk_tdef(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), Nat::O, List::Cons(Cdef::Mk_cdef(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Cons(Ty::TBase(Base_ty::BString), List::Nil)), List::Nil), true)

pub fn elab_ty(tys : List[(Ident, Nat)], tps : List[Ident], t : Sty) -> Result0[Ty, Elab_error] {
  match t {
    Sty::SName(p, n, args) => match index_of(n, tps) {
      Some(i) => match args {
        List::Nil => Result0::Ok(Ty::TVar(i))
        List::Cons(_, _) => Result0::Err(Elab_error::EE_TypeArgs(p, n, Nat::O, length(args)))
      }
      None => match assoc(n, builtin_types) {
        Some(_UU03c4_) => match args {
          List::Nil => Result0::Ok(_UU03c4_)
          List::Cons(_, _) => Result0::Err(Elab_error::EE_TypeArgs(p, n, Nat::O, length(args)))
        }
        None => match assoc(n, tys) {
          Some(k) => match eqb0(k, length(args)) {
            true => bind(mapM(fn(x1) { elab_ty(tys, tps, x1) }, args), fn(_UU03c4_s) { Result0::Ok(Ty::TData(n, _UU03c4_s)) })
            false => Result0::Err(Elab_error::EE_TypeArgs(p, n, k, length(args)))
          }
          None => match array_kind_of(n) {
            Some(k) => match args {
              List::Nil => Result0::Err(Elab_error::EE_TypeArgs(p, n, Nat::S(Nat::O), length(args)))
              List::Cons(a, l) => match l {
                List::Nil => bind(elab_ty(tys, tps, a), fn(_UU03c4_) { Result0::Ok(Ty::TArray(k, _UU03c4_)) })
                List::Cons(_, _) => Result0::Err(Elab_error::EE_TypeArgs(p, n, Nat::S(Nat::O), length(args)))
              }
            }
            None => Result0::Err(Elab_error::EE_UnknownType(p, n))
          }
        }
      }
    }
    Sty::STuple(_, ts) => bind(mapM(fn(x1) { elab_ty(tys, tps, x1) }, ts), fn(_UU03c4_s) { Result0::Ok(Ty::TTuple(_UU03c4_s)) })
    Sty::SArrow(_, ps, r, eff) => bind(mapM(fn(x1) { elab_ty(tys, tps, x1) }, ps), fn(_UU03c4_s) {
      bind(elab_ty(tys, tps, r), fn(_UU03c4_) {
        bind(match eff {
          Some(t0) => elab_ty(tys, tps, t0)
          None => Result0::Ok(Ty::TBase(Base_ty::BNever))
        }, fn(_UU03b5_) { Result0::Ok(Ty::TArrow(_UU03c4_s, _UU03c4_, _UU03b5_)) })
      })
    })
    Sty::SObj(_, tr) => Result0::Ok(Ty::TData(append(String0::String1(Ascii::Ascii0(false, true, true, false, false, true, false, false), String0::EmptyString), tr), List::Nil))
  }
}

pub fn tmatch(p : Ty, t : Ty, s : List[Option[Ty]]) -> List[Option[Ty]] {
  let go = {
    letrec go = fn(ps) {
      fn(ts) {
        fn(s0) {
          match ps {
            List::Nil => s0
            List::Cons(p0, ps_) => match ts {
              List::Nil => s0
              List::Cons(t0, ts_) => go(ps_)(ts_)(tmatch(p0, t0, s0))
            }
          }
        }
      }
    }
    go
  }
  match p {
    Ty::TVar(i) => match nth_error(s, i) {
      Some(o) => match o {
        Some(_) => s
        None => set_nth(i, Some(t), s)
      }
      None => s
    }
    Ty::TTuple(ps) => match t {
      Ty::TTuple(ts) => go(ps)(ts)(s)
      _ => s
    }
    Ty::TArrow(ps, r, _UU03b5_) => match t {
      Ty::TArrow(ts, u, _UU03b7_) => tmatch(_UU03b5_, _UU03b7_, tmatch(r, u, go(ps)(ts)(s)))
      _ => s
    }
    Ty::TData(t0, ps) => match t {
      Ty::TData(u, ts) => match eqDec_ident(t0)(u) {
        true => go(ps)(ts)(s)
        false => s
      }
      _ => s
    }
    Ty::TRef(p0) => match t {
      Ty::TRef(t0) => tmatch(p0, t0, s)
      _ => s
    }
    Ty::TArray(k, p0) => match t {
      Ty::TArray(k_, t0) => match eqDec_array_kind(k)(k_) {
        true => tmatch(p0, t0, s)
        false => s
      }
      _ => s
    }
    _ => s
  }
}

pub fn resolve(s : List[Option[Ty]], p : Ty) -> Option[Ty] {
  let go = {
    letrec go = fn(ps) {
      match ps {
        List::Nil => Some(List::Nil)
        List::Cons(p0, ps_) => match resolve(s, p0) {
          Some(t) => match go(ps_) {
            Some(ts) => Some(List::Cons(t, ts))
            None => None
          }
          None => None
        }
      }
    }
    go
  }
  match p {
    Ty::TVar(i) => match nth_error(s, i) {
      Some(o) => o
      None => None
    }
    Ty::TTuple(ps) => option_map(fn(x) { Ty::TTuple(x) }, go(ps))
    Ty::TArrow(ps, r, _UU03b5_) => match go(ps) {
      Some(ts) => match resolve(s, r) {
        Some(t) => match resolve(s, _UU03b5_) {
          Some(_UU03b7_) => Some(Ty::TArrow(ts, t, _UU03b7_))
          None => None
        }
        None => None
      }
      None => None
    }
    Ty::TData(t, ps) => option_map(fn(x) { Ty::TData(t, x) }, go(ps))
    Ty::TRef(p0) => option_map(fn(x) { Ty::TRef(x) }, resolve(s, p0))
    Ty::TArray(k, p0) => option_map(fn(x) { Ty::TArray(k, x) }, resolve(s, p0))
    x => Some(x)
  }
}

pub fn int_in_range(k : Int_kind, z : Z) -> Bool {
  eqb2(wrap(k, z), z)
}

pub fn elab_lit(p : Pos, exp : Option[Ty], l : Slit) -> Result0[Lit, Elab_error] {
  let int = fn(k) {
    fn(z) {
      match int_in_range(k, z) {
        true => Result0::Ok(Lit::LInt(k, z))
        false => Result0::Err(Elab_error::EE_IntRange(p, k, z))
      }
    }
  }
  match l {
    Slit::SLUnit => Result0::Ok(Lit::LUnit)
    Slit::SLBool(b) => Result0::Ok(Lit::LBool(b))
    Slit::SLInt(k0, z) => match k0 {
      Some(k) => int(k)(z)
      None => match exp {
        Some(t) => match t {
          Ty::TBase(b) => match b {
            Base_ty::BInt(k) => int(k)(z)
            _ => int(Int_kind::I32)(z)
          }
          _ => int(Int_kind::I32)(z)
        }
        None => int(Int_kind::I32)(z)
      }
    }
    Slit::SLChar(c) => Result0::Ok(Lit::LChar(c))
    Slit::SLDouble(b) => Result0::Ok(Lit::LDouble(b))
    Slit::SLFloat(b) => Result0::Ok(Lit::LFloat(b))
    Slit::SLString(s) => Result0::Ok(Lit::LString(s))
  }
}

pub let arith_ops : List[(Ident, Arith_op)] = List::Cons((String0::String1(Ascii::Ascii0(true, true, false, true, false, true, false, false), String0::EmptyString), Arith_op::AAdd), List::Cons((String0::String1(Ascii::Ascii0(true, false, true, true, false, true, false, false), String0::EmptyString), Arith_op::ASub), List::Cons((String0::String1(Ascii::Ascii0(false, true, false, true, false, true, false, false), String0::EmptyString), Arith_op::AMul), List::Cons((String0::String1(Ascii::Ascii0(true, true, true, true, false, true, false, false), String0::EmptyString), Arith_op::ADiv), List::Cons((String0::String1(Ascii::Ascii0(true, false, true, false, false, true, false, false), String0::EmptyString), Arith_op::AMod), List::Nil)))))

pub let cmp_ops : List[(Ident, Cmp_op)] = List::Cons((String0::String1(Ascii::Ascii0(true, false, true, true, true, true, false, false), String0::String1(Ascii::Ascii0(true, false, true, true, true, true, false, false), String0::EmptyString)), Cmp_op::CEq), List::Cons((String0::String1(Ascii::Ascii0(true, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, false, true, true, true, true, false, false), String0::EmptyString)), Cmp_op::CNe), List::Cons((String0::String1(Ascii::Ascii0(false, false, true, true, true, true, false, false), String0::EmptyString), Cmp_op::CLt), List::Cons((String0::String1(Ascii::Ascii0(false, false, true, true, true, true, false, false), String0::String1(Ascii::Ascii0(true, false, true, true, true, true, false, false), String0::EmptyString)), Cmp_op::CLe), List::Cons((String0::String1(Ascii::Ascii0(false, true, true, true, true, true, false, false), String0::EmptyString), Cmp_op::CGt), List::Cons((String0::String1(Ascii::Ascii0(false, true, true, true, true, true, false, false), String0::String1(Ascii::Ascii0(true, false, true, true, true, true, false, false), String0::EmptyString)), Cmp_op::CGe), List::Nil))))))

pub let e_true : Expr = Expr::ELit(Lit::LBool(true))

pub let e_false : Expr = Expr::ELit(Lit::LBool(false))

pub fn elab_binop(p : Pos, op : Ident, ta : Ty, a : Expr, b : Expr) -> Result0[Expr, Elab_error] {
  match assoc(op, arith_ops) {
    Some(o) => match o {
      Arith_op::AAdd => match assoc(op, cmp_ops) {
        Some(c) => match c {
          Cmp_op::CEq => match ta {
            Ty::TBase(b0) => match b0 {
              Base_ty::BBool => Result0::Ok(Expr::EPrim(Prim_op::PBoolEq, List::Cons(a, List::Cons(b, List::Nil))))
              Base_ty::BInt(k) => Result0::Ok(Expr::EPrim(Prim_op::PIntArith(o, k), List::Cons(a, List::Cons(b, List::Nil))))
              Base_ty::BChar => Result0::Ok(Expr::EPrim(Prim_op::PCharCmp(c), List::Cons(a, List::Cons(b, List::Nil))))
              Base_ty::BString => Result0::Ok(Expr::EPrim(Prim_op::PStrConcat, List::Cons(a, List::Cons(b, List::Nil))))
              _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
            }
            _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
          }
          Cmp_op::CNe => match ta {
            Ty::TBase(b0) => match b0 {
              Base_ty::BBool => Result0::Ok(Expr::EPrim(Prim_op::PBoolNot, List::Cons(Expr::EPrim(Prim_op::PBoolEq, List::Cons(a, List::Cons(b, List::Nil))), List::Nil)))
              Base_ty::BInt(k) => Result0::Ok(Expr::EPrim(Prim_op::PIntArith(o, k), List::Cons(a, List::Cons(b, List::Nil))))
              Base_ty::BChar => Result0::Ok(Expr::EPrim(Prim_op::PCharCmp(c), List::Cons(a, List::Cons(b, List::Nil))))
              Base_ty::BString => Result0::Ok(Expr::EPrim(Prim_op::PStrConcat, List::Cons(a, List::Cons(b, List::Nil))))
              _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
            }
            _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
          }
          _ => match ta {
            Ty::TBase(b0) => match b0 {
              Base_ty::BInt(k) => Result0::Ok(Expr::EPrim(Prim_op::PIntArith(o, k), List::Cons(a, List::Cons(b, List::Nil))))
              Base_ty::BChar => Result0::Ok(Expr::EPrim(Prim_op::PCharCmp(c), List::Cons(a, List::Cons(b, List::Nil))))
              Base_ty::BString => Result0::Ok(Expr::EPrim(Prim_op::PStrConcat, List::Cons(a, List::Cons(b, List::Nil))))
              _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
            }
            _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
          }
        }
        None => match ta {
          Ty::TBase(b0) => match b0 {
            Base_ty::BInt(k) => Result0::Ok(Expr::EPrim(Prim_op::PIntArith(o, k), List::Cons(a, List::Cons(b, List::Nil))))
            Base_ty::BString => Result0::Ok(Expr::EPrim(Prim_op::PStrConcat, List::Cons(a, List::Cons(b, List::Nil))))
            _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
          }
          _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
        }
      }
      _ => match assoc(op, cmp_ops) {
        Some(c) => match c {
          Cmp_op::CEq => match ta {
            Ty::TBase(b0) => match b0 {
              Base_ty::BBool => Result0::Ok(Expr::EPrim(Prim_op::PBoolEq, List::Cons(a, List::Cons(b, List::Nil))))
              Base_ty::BInt(k) => Result0::Ok(Expr::EPrim(Prim_op::PIntArith(o, k), List::Cons(a, List::Cons(b, List::Nil))))
              Base_ty::BChar => Result0::Ok(Expr::EPrim(Prim_op::PCharCmp(c), List::Cons(a, List::Cons(b, List::Nil))))
              Base_ty::BString => Result0::Ok(Expr::EPrim(Prim_op::PStrEq, List::Cons(a, List::Cons(b, List::Nil))))
              _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
            }
            _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
          }
          Cmp_op::CNe => match ta {
            Ty::TBase(b0) => match b0 {
              Base_ty::BBool => Result0::Ok(Expr::EPrim(Prim_op::PBoolNot, List::Cons(Expr::EPrim(Prim_op::PBoolEq, List::Cons(a, List::Cons(b, List::Nil))), List::Nil)))
              Base_ty::BInt(k) => Result0::Ok(Expr::EPrim(Prim_op::PIntArith(o, k), List::Cons(a, List::Cons(b, List::Nil))))
              Base_ty::BChar => Result0::Ok(Expr::EPrim(Prim_op::PCharCmp(c), List::Cons(a, List::Cons(b, List::Nil))))
              Base_ty::BString => Result0::Ok(Expr::EPrim(Prim_op::PBoolNot, List::Cons(Expr::EPrim(Prim_op::PStrEq, List::Cons(a, List::Cons(b, List::Nil))), List::Nil)))
              _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
            }
            _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
          }
          _ => match ta {
            Ty::TBase(b0) => match b0 {
              Base_ty::BInt(k) => Result0::Ok(Expr::EPrim(Prim_op::PIntArith(o, k), List::Cons(a, List::Cons(b, List::Nil))))
              Base_ty::BChar => Result0::Ok(Expr::EPrim(Prim_op::PCharCmp(c), List::Cons(a, List::Cons(b, List::Nil))))
              _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
            }
            _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
          }
        }
        None => match ta {
          Ty::TBase(b0) => match b0 {
            Base_ty::BInt(k) => Result0::Ok(Expr::EPrim(Prim_op::PIntArith(o, k), List::Cons(a, List::Cons(b, List::Nil))))
            _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
          }
          _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
        }
      }
    }
    None => match assoc(op, cmp_ops) {
      Some(c) => match c {
        Cmp_op::CEq => match ta {
          Ty::TBase(b0) => match b0 {
            Base_ty::BBool => Result0::Ok(Expr::EPrim(Prim_op::PBoolEq, List::Cons(a, List::Cons(b, List::Nil))))
            Base_ty::BInt(k) => Result0::Ok(Expr::EPrim(Prim_op::PIntCmp(c, k), List::Cons(a, List::Cons(b, List::Nil))))
            Base_ty::BChar => Result0::Ok(Expr::EPrim(Prim_op::PCharCmp(c), List::Cons(a, List::Cons(b, List::Nil))))
            Base_ty::BString => Result0::Ok(Expr::EPrim(Prim_op::PStrEq, List::Cons(a, List::Cons(b, List::Nil))))
            _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
          }
          _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
        }
        Cmp_op::CNe => match ta {
          Ty::TBase(b0) => match b0 {
            Base_ty::BBool => Result0::Ok(Expr::EPrim(Prim_op::PBoolNot, List::Cons(Expr::EPrim(Prim_op::PBoolEq, List::Cons(a, List::Cons(b, List::Nil))), List::Nil)))
            Base_ty::BInt(k) => Result0::Ok(Expr::EPrim(Prim_op::PIntCmp(c, k), List::Cons(a, List::Cons(b, List::Nil))))
            Base_ty::BChar => Result0::Ok(Expr::EPrim(Prim_op::PCharCmp(c), List::Cons(a, List::Cons(b, List::Nil))))
            Base_ty::BString => Result0::Ok(Expr::EPrim(Prim_op::PBoolNot, List::Cons(Expr::EPrim(Prim_op::PStrEq, List::Cons(a, List::Cons(b, List::Nil))), List::Nil)))
            _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
          }
          _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
        }
        _ => match ta {
          Ty::TBase(b0) => match b0 {
            Base_ty::BInt(k) => Result0::Ok(Expr::EPrim(Prim_op::PIntCmp(c, k), List::Cons(a, List::Cons(b, List::Nil))))
            Base_ty::BChar => Result0::Ok(Expr::EPrim(Prim_op::PCharCmp(c), List::Cons(a, List::Cons(b, List::Nil))))
            _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
          }
          _ => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
        }
      }
      None => Result0::Err(Elab_error::EE_NoOperator(p, op, ta))
    }
  }
}

pub fn flexible(e : Sexpr) -> Bool {
  match e {
    Sexpr::SLit(_, l) => match l {
      Slit::SLInt(k, _) => match k {
        Some(_) => false
        None => true
      }
      _ => false
    }
    _ => false
  }
}

pub(all) enum Lab_kind {
  LKFun
  LKBlock
  LKWhile
  LKForBody
  LKForInBody
  LKHead
}

pub(all) enum Lab {
  Mk_lab(Option[Ident], Lab_kind, List[Ty], Ty)
}

pub fn core_labels(l : List[Lab]) -> List[(List[Ty], Ty)] {
  map(fn(l0) {
    (match l0 {
      Lab::Mk_lab(_, _, lb_ps, _) => lb_ps
    }, match l0 {
      Lab::Mk_lab(_, _, _, lb_res) => lb_res
    })
  }, l)
}

pub fn named(x : Ident, l : Lab) -> Bool {
  match (match l {
    Lab::Mk_lab(lb_name, _, _, _) => lb_name
  }) {
    Some(y) => eqDec_ident(x)(y)
    None => false
  }
}

pub fn next_res(l : List[Lab]) -> Ty {
  match l {
    List::Nil => Ty::TBase(Base_ty::BUnit)
    List::Cons(l0, _) => match l0 {
      Lab::Mk_lab(_, _, _, lb_res) => lb_res
    }
  }
}

pub fn next_ps(l : List[Lab]) -> List[Ty] {
  match l {
    List::Nil => List::Nil
    List::Cons(l0, _) => match l0 {
      Lab::Mk_lab(_, _, lb_ps, _) => lb_ps
    }
  }
}

pub fn next_state(l : List[Lab]) -> List[Ty] {
  match l {
    List::Nil => List::Nil
    List::Cons(l0, _) => match (match l0 {
      Lab::Mk_lab(_, _, _, lb_res) => lb_res
    }) {
      Ty::TTuple(_UU03c4_s) => _UU03c4_s
      _ => List::Nil
    }
  }
}

pub fn break_target(x : Option[Ident], l : List[Lab], k : Nat) -> Option[(Nat, Ty)] {
  match l {
    List::Nil => None
    List::Cons(l0, l_) => match (match l0 {
      Lab::Mk_lab(_, lb_kind, _, _) => lb_kind
    }) {
      Lab_kind::LKFun => None
      Lab_kind::LKBlock => match x {
        Some(y) => match named(y, l0) {
          true => Some((k, match l0 {
            Lab::Mk_lab(_, _, _, lb_res) => lb_res
          }))
          false => break_target(x, l_, Nat::S(k))
        }
        None => None
      }
      Lab_kind::LKWhile => match x {
        Some(y) => match named(y, l0) {
          true => Some((k, match l0 {
            Lab::Mk_lab(_, _, _, lb_res) => lb_res
          }))
          false => break_target(x, l_, Nat::S(k))
        }
        None => Some((k, match l0 {
          Lab::Mk_lab(_, _, _, lb_res) => lb_res
        }))
      }
      Lab_kind::LKForBody => match x {
        Some(y) => match named(y, l0) {
          true => Some((Nat::S(k), next_res(l_)))
          false => break_target(x, l_, Nat::S(k))
        }
        None => Some((Nat::S(k), next_res(l_)))
      }
      Lab_kind::LKForInBody => match x {
        Some(y) => match named(y, l0) {
          true => Some((Nat::S(Nat::S(k)), next_res(tl(l_))))
          false => break_target(x, l_, Nat::S(k))
        }
        None => Some((Nat::S(Nat::S(k)), next_res(tl(l_))))
      }
      Lab_kind::LKHead => break_target(x, l_, Nat::S(k))
    }
  }
}

pub(all) enum Cont_target {
  CTWhile(Nat)
  CTFor(Nat, List[Ty])
  CTForIn(Nat, List[Ty])
}

pub fn cont_target_of(x : Option[Ident], l : List[Lab], k : Nat) -> Option[Cont_target] {
  match l {
    List::Nil => None
    List::Cons(l0, l_) => match (match l0 {
      Lab::Mk_lab(_, lb_kind, _, _) => lb_kind
    }) {
      Lab_kind::LKFun => None
      Lab_kind::LKBlock => match x {
        Some(y) => match named(y, l0) {
          true => None
          false => cont_target_of(x, l_, Nat::S(k))
        }
        None => None
      }
      Lab_kind::LKWhile => match x {
        Some(y) => match named(y, l0) {
          true => Some(Cont_target::CTWhile(k))
          false => cont_target_of(x, l_, Nat::S(k))
        }
        None => Some(Cont_target::CTWhile(k))
      }
      Lab_kind::LKForBody => match x {
        Some(y) => match named(y, l0) {
          true => Some(Cont_target::CTFor(k, next_ps(l_)))
          false => cont_target_of(x, l_, Nat::S(k))
        }
        None => Some(Cont_target::CTFor(k, next_ps(l_)))
      }
      Lab_kind::LKForInBody => match x {
        Some(y) => match named(y, l0) {
          true => Some(Cont_target::CTForIn(k, next_state(l_)))
          false => cont_target_of(x, l_, Nat::S(k))
        }
        None => Some(Cont_target::CTForIn(k, next_state(l_)))
      }
      Lab_kind::LKHead => cont_target_of(x, l_, Nat::S(k))
    }
  }
}

pub fn return_target(l : List[Lab], k : Nat) -> Option[(Nat, Ty)] {
  match l {
    List::Nil => None
    List::Cons(l0, l_) => match (match l0 {
      Lab::Mk_lab(_, lb_kind, _, _) => lb_kind
    }) {
      Lab_kind::LKFun => Some((k, match l0 {
        Lab::Mk_lab(_, _, _, lb_res) => lb_res
      }))
      _ => return_target(l_, Nat::S(k))
    }
  }
}

pub(all) enum Range_kind {
  RUpExcl
  RUpIncl
  RDownExcl
  RDownIncl
}

pub fn range_op(op : Ident) -> Option[Range_kind] {
  match eqDec_ident(op)(String0::String1(Ascii::Ascii0(false, true, true, true, false, true, false, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, false, false), String0::String1(Ascii::Ascii0(false, false, true, true, true, true, false, false), String0::EmptyString)))) {
    true => Some(Range_kind::RUpExcl)
    false => match eqDec_ident(op)(String0::String1(Ascii::Ascii0(false, true, true, true, false, true, false, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, false, false), String0::String1(Ascii::Ascii0(false, false, true, true, true, true, false, false), String0::String1(Ascii::Ascii0(true, false, true, true, true, true, false, false), String0::EmptyString))))) {
      true => Some(Range_kind::RUpIncl)
      false => match eqDec_ident(op)(String0::String1(Ascii::Ascii0(false, true, true, true, true, true, false, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, false, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, false, false), String0::EmptyString)))) {
        true => Some(Range_kind::RDownExcl)
        false => match eqDec_ident(op)(String0::String1(Ascii::Ascii0(false, true, true, true, true, true, false, false), String0::String1(Ascii::Ascii0(true, false, true, true, true, true, false, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, false, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, false, false), String0::EmptyString))))) {
          true => Some(Range_kind::RDownIncl)
          false => None
        }
      }
    }
  }
}

pub(all) enum Iter_src {
  IRange(Range_kind, Int_kind)
  IArray(Array_kind, Ty)
}

pub fn int1(kk : Int_kind) -> Expr {
  Expr::ELit(Lit::LInt(kk, Z::Zpos(Positive::XH)))
}

pub fn iarith(o : Arith_op, kk : Int_kind, a : Expr, b : Expr) -> Expr {
  Expr::EPrim(Prim_op::PIntArith(o, kk), List::Cons(a, List::Cons(b, List::Nil)))
}

pub fn icmp(c : Cmp_op, kk : Int_kind, a : Expr, b : Expr) -> Expr {
  Expr::EPrim(Prim_op::PIntCmp(c, kk), List::Cons(a, List::Cons(b, List::Nil)))
}

pub(all) enum Cenv {
  Mk_cenv(List[Lab], Ty)
}

pub fn push_lab(l : Lab, l0 : Cenv) -> Cenv {
  Cenv::Mk_cenv(List::Cons(l, match l0 {
    Cenv::Mk_cenv(ce_labs, _) => ce_labs
  }), match l0 {
    Cenv::Mk_cenv(_, ce_exn) => ce_exn
  })
}

pub fn set_exn(_UU03b5_ : Ty, l : Cenv) -> Cenv {
  Cenv::Mk_cenv(match l {
    Cenv::Mk_cenv(ce_labs, _) => ce_labs
  }, _UU03b5_)
}

pub(all) enum Catch_info {
  CINone
  CIOne(Ident)
  CIMany
}

pub fn eblock(_UU03c4_ : Ty, b : Expr) -> Expr {
  Expr::ELoop(Expr::ETuple(List::Nil), List::Nil, _UU03c4_, b)
}

pub fn diverges(e : Sexpr) -> Bool {
  match e {
    Sexpr::SApp(_, f, _) => match f {
      Sexpr::SVar(_, g) => match (match eqDec_ident(g)(String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::EmptyString)))))) {
        true => true
        false => eqDec_ident(g)(String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))))))
      }) {
        true => true
        false => eqDec_ident(g)(String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))
      }
      _ => false
    }
    Sexpr::SLet(_, _, _, _, body) => diverges(body)
    Sexpr::SLetMut(_, _, _, _, body) => diverges(body)
    Sexpr::SBreak(_, _, _) => true
    Sexpr::SContinue(_, _, _) => true
    Sexpr::SReturn(_, _) => true
    Sexpr::SRaise(_, _) => true
    _ => false
  }
}

pub type Lctx = List[(Option[Ident], Ty)]

pub fn lookup_local(x : Ident, _UU0393_ : Lctx) -> Option[Nat] {
  match _UU0393_ {
    List::Nil => None
    List::Cons(p, _UU0393__) => match p {
      (o, _) => match o {
        Some(y) => match eqDec_ident(x)(y) {
          true => Some(Nat::O)
          false => option_map(fn(x0) { Nat::S(x0) }, lookup_local(x, _UU0393__))
        }
        None => option_map(fn(x0) { Nat::S(x0) }, lookup_local(x, _UU0393__))
      }
    }
  }
}

pub(all) enum Msig {
  Mk_msig(Ident, List[Ty], Ty, Ty)
}

pub(all) enum Trinfo {
  Mk_trinfo(Ident, List[Ident], List[Msig], List[Ident])
}

pub(all) enum Xenv {
  Mk_xenv(List[Trinfo], List[Idef], List[(Ident, List[(Ident, Nat)])], List[(Ident, Ident)], List[Ident], List[((Ident, Ty), Ident)])
}

pub fn find_trait(trs0 : List[Trinfo], tr : Ident) -> Option[Trinfo] {
  find(fn(ti) {
    eqDec_ident(match ti {
      Trinfo::Mk_trinfo(ti_name, _, _, _) => ti_name
    })(tr)
  }, trs0)
}

pub fn dict_fields(ti : Trinfo) -> List[Ty] {
  app(map(fn(sn) { Ty::TData(sn, List::Cons(Ty::TVar(Nat::O), List::Nil)) }, match ti {
    Trinfo::Mk_trinfo(_, ti_supers, _, _) => ti_supers
  }), map(fn(m) {
    Ty::TArrow(match m {
      Msig::Mk_msig(_, ms_params, _, _) => ms_params
    }, match m {
      Msig::Mk_msig(_, _, ms_ret, _) => ms_ret
    }, match m {
      Msig::Mk_msig(_, _, _, ms_eff) => ms_eff
    })
  }, match ti {
    Trinfo::Mk_trinfo(_, _, ti_methods, _) => ti_methods
  }))
}

pub fn dict_tdef(ti : Trinfo) -> Tdef {
  Tdef::Mk_tdef(match ti {
    Trinfo::Mk_trinfo(ti_name, _, _, _) => ti_name
  }, Nat::S(Nat::O), List::Cons(Cdef::Mk_cdef(match ti {
    Trinfo::Mk_trinfo(ti_name, _, _, _) => ti_name
  }, dict_fields(ti)), List::Nil), false)
}

pub fn method_of(ti : Trinfo, m : Ident) -> Option[(Nat, Msig)] {
  {
    letrec go = fn(ms) {
      fn(i) {
        match ms {
          List::Nil => None
          List::Cons(s, ms_) => match eqDec_ident(match s {
            Msig::Mk_msig(ms_name, _, _, _) => ms_name
          })(m) {
            true => Some((i, s))
            false => go(ms_)(Nat::S(i))
          }
        }
      }
    }
    go(match ti {
      Trinfo::Mk_trinfo(_, _, ti_methods, _) => ti_methods
    })(length(match ti {
      Trinfo::Mk_trinfo(_, ti_supers, _, _) => ti_supers
    }))
  }
}

pub fn field_of(t : Ident, n : Nat, i : Nat, d : Expr, _UU03c4_ : Ty) -> Expr {
  Expr::EMatch(d, _UU03c4_, List::Cons((Pat::PConstr(t, map(fn(j) {
    match eqb0(j, i) {
      true => Pat::PVar
      false => Pat::PWild
    }
  }, seq(Nat::O, n))), Expr::EVar(Nat::O)), List::Nil))
}

pub fn trait_closure(trs0 : List[Trinfo], fuel : Nat, tr : Ident) -> List[Ident] {
  match fuel {
    Nat::O => List::Cons(tr, List::Nil)
    Nat::S(f) => List::Cons(tr, match find_trait(trs0, tr) {
      Some(ti) => concat(map(fn(x1) { trait_closure(trs0, f, x1) }, match ti {
        Trinfo::Mk_trinfo(_, ti_supers, _, _) => ti_supers
      }))
      None => List::Nil
    })
  }
}

pub fn closure(trs0 : List[Trinfo], tr : Ident) -> List[Ident] {
  nodup(fn(x1) { fn(x2) { eq_dec0(eqDec_ident, x1, x2) } }, trait_closure(trs0, length(trs0), tr))
}

pub fn occurs0(t : Ty) -> Bool {
  match t {
    Ty::TVar(i) => eqb0(i, Nat::O)
    Ty::TTuple(ts) => existsb(fn(x1) { occurs0(x1) }, ts)
    Ty::TArrow(ps, r, _UU03b5_) => match (match existsb(fn(x1) { occurs0(x1) }, ps) {
      true => true
      false => occurs0(r)
    }) {
      true => true
      false => occurs0(_UU03b5_)
    }
    Ty::TData(_, ts) => existsb(fn(x1) { occurs0(x1) }, ts)
    Ty::TRef(t0) => occurs0(t0)
    Ty::TArray(_, t0) => occurs0(t0)
    _ => false
  }
}

pub fn obj_safe_m(m : Msig) -> Bool {
  match (match m {
    Msig::Mk_msig(_, ms_params, _, _) => ms_params
  }) {
    List::Nil => false
    List::Cons(t, ps) => match t {
      Ty::TVar(i) => match i {
        Nat::O => negb(match (match existsb(fn(x1) { occurs0(x1) }, ps) {
          true => true
          false => occurs0(match m {
            Msig::Mk_msig(_, _, ms_ret, _) => ms_ret
          })
        }) {
          true => true
          false => occurs0(match m {
            Msig::Mk_msig(_, _, _, ms_eff) => ms_eff
          })
        })
        Nat::S(_) => false
      }
      _ => false
    }
  }
}

pub fn obj_safe(trs0 : List[Trinfo], tr : Ident) -> Bool {
  forallb(fn(sn) {
    match find_trait(trs0, sn) {
      Some(ti) => forallb(fn(x1) { obj_safe_m(x1) }, match ti {
        Trinfo::Mk_trinfo(_, _, ti_methods, _) => ti_methods
      })
      None => false
    }
  }, closure(trs0, tr))
}

pub fn obj_name(tr : Ident) -> Ident {
  append(String0::String1(Ascii::Ascii0(false, true, true, false, false, true, false, false), String0::EmptyString), tr)
}

pub fn obj_fields(trs0 : List[Trinfo], tr : Ident) -> List[(Ident, Msig)] {
  concat(map(fn(sn) {
    match find_trait(trs0, sn) {
      Some(ti) => map(fn(m) { (sn, m) }, match ti {
        Trinfo::Mk_trinfo(_, _, ti_methods, _) => ti_methods
      })
      None => List::Nil
    }
  }, closure(trs0, tr)))
}

pub fn obj_field_ty(m : Msig) -> Ty {
  Ty::TArrow(tl(match m {
    Msig::Mk_msig(_, ms_params, _, _) => ms_params
  }), match m {
    Msig::Mk_msig(_, _, ms_ret, _) => ms_ret
  }, match m {
    Msig::Mk_msig(_, _, _, ms_eff) => ms_eff
  })
}

pub fn obj_tdef(trs0 : List[Trinfo], tr : Ident) -> Tdef {
  Tdef::Mk_tdef(obj_name(tr), Nat::O, List::Cons(Cdef::Mk_cdef(obj_name(tr), map(fn(sm) { obj_field_ty(snd(sm)) }, obj_fields(trs0, tr))), List::Nil), false)
}

pub fn head_name(t : Ty) -> Option[Ident] {
  match t {
    Ty::TBase(b) => option_map(fn(x1) { fst(x1) }, find(fn(nt) { eqDec_ty(snd(nt))(Ty::TBase(b)) }, builtin_types))
    Ty::TData(t0, _) => Some(t0)
    Ty::TArray(k, _) => match k {
      Array_kind::AFixed => Some(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, true, true, true, false), String0::EmptyString)))))))))))
      Array_kind::AGrow => Some(String0::String1(Ascii::Ascii0(true, false, false, false, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, true, true, true, false), String0::EmptyString))))))
    }
    Ty::TError => Some(String0::String1(Ascii::Ascii0(true, false, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::EmptyString))))))
    _ => None
  }
}

pub fn dict_var(tr : Ident, x : Ident) -> Ident {
  append(String0::String1(Ascii::Ascii0(false, false, true, false, false, true, false, false), String0::EmptyString), append(tr, append(String0::String1(Ascii::Ascii0(false, false, true, false, false, true, false, false), String0::EmptyString), x)))
}

pub fn super_lets(trs0 : List[Trinfo], fuel : Nat, have : List[(Ident, Ident)], queue : List[((Ident, Ident), Nat)]) -> List[((((Ident, Ident), Nat), Ident), Nat)] {
  match fuel {
    Nat::O => List::Nil
    Nat::S(f) => match queue {
      List::Nil => List::Nil
      List::Cons(p, q) => match p {
        (p0, i) => match p0 {
          (t, x) => {
            let sups = match find_trait(trs0, t) {
              Some(ti) => match ti {
                Trinfo::Mk_trinfo(_, ti_supers, _, _) => ti_supers
              }
              None => List::Nil
            }
            let add2 = {
              letrec add2 = fn(ss) {
                fn(j) {
                  fn(have0) {
                    match ss {
                      List::Nil => (List::Nil, have0)
                      List::Cons(s, ss_) => match existsb(fn(p1) {
                        match eqDec_ident(fst(p1))(s) {
                          true => eqDec_ident(snd(p1))(x)
                          false => false
                        }
                      }, have0) {
                        true => add2(ss_)(Nat::S(j))(have0)
                        false => match add2(ss_)(Nat::S(j))(List::Cons((s, x), have0)) {
                          (r, h) => (List::Cons(((((s, x), i), t), j), r), h)
                        }
                      }
                    }
                  }
                }
              }
              add2
            }
            match add2(sups)(Nat::O)(have) {
              (new, have_) => app(new, super_lets(trs0, f, have_, app(q, map(fn(l) {
                match l {
                  (y, _) => match y {
                    (y1, _) => y1
                  }
                }
              }, new))))
            }
          }
        }
      }
    }
  }
}

pub(all) enum Senv {
  Mk_senv(List[(Ident, Nat)], Genv, List[(Ident, List[Ident])], List[Ident], Xenv)
}

pub fn ety(e : Senv, t : Sty) -> Result0[Ty, Elab_error] {
  elab_ty(match e {
    Senv::Mk_senv(se_tys, _, _, _, _) => se_tys
  }, match e {
    Senv::Mk_senv(_, _, _, se_tps, _) => se_tps
  }, t)
}

pub fn sbounds(e : Senv, g : Ident) -> List[(Ident, Nat)] {
  match assoc(g, match (match e {
    Senv::Mk_senv(_, _, _, _, se_x) => se_x
  }) {
    Xenv::Mk_xenv(_, _, x_bounds, _, _, _) => x_bounds
  }) {
    Some(b) => b
    None => List::Nil
  }
}

pub fn ctx_of(_UU0393_ : Lctx) -> Ctx {
  map(fn(x1) { snd(x1) }, _UU0393_)
}

pub fn fun_env(r : Ty, _UU03b5_ : Ty) -> Cenv {
  Cenv::Mk_cenv(List::Cons(Lab::Mk_lab(None, Lab_kind::LKFun, List::Nil, r), List::Nil), _UU03b5_)
}

pub fn lam_ctx(ps : List[(Ident, Option[Sty])], _UU03c4_s : List[Ty]) -> Lctx {
  combine(map(fn(xa) { Some(fst(xa)) }, ps), _UU03c4_s)
}

pub fn fn_inst(fd : Fdef, ts : List[Ty]) -> Ty {
  Ty::TArrow(map({ let a1 = fn(x1) { inst(ts, x1) }; fn(x1) { tsubst(a1, x1) } }, match fd {
    Fdef::Mk_fdef(_, _, fd_params, _, _, _) => fd_params
  }), tsubst(fn(x1) { inst(ts, x1) }, match fd {
    Fdef::Mk_fdef(_, _, _, fd_ret, _, _) => fd_ret
  }), tsubst(fn(x1) { inst(ts, x1) }, match fd {
    Fdef::Mk_fdef(_, _, _, _, fd_eff, _) => fd_eff
  }))
}

pub fn lit_of(l : Slit) -> Option[Lit] {
  match l {
    Slit::SLUnit => Some(Lit::LUnit)
    Slit::SLBool(b) => Some(Lit::LBool(b))
    Slit::SLInt(ko, z) => {
      let k = match ko {
        Some(k) => k
        None => Int_kind::I32
      }
      match int_in_range(k, z) {
        true => Some(Lit::LInt(k, z))
        false => None
      }
    }
    Slit::SLChar(c) => Some(Lit::LChar(c))
    Slit::SLDouble(b) => Some(Lit::LDouble(b))
    Slit::SLFloat(b) => Some(Lit::LFloat(b))
    Slit::SLString(s) => Some(Lit::LString(s))
  }
}

pub fn binop_res(op : Ident, _UU03c4_ : Ty) -> Ty {
  match assoc(op, arith_ops) {
    Some(a) => match a {
      Arith_op::AAdd => match _UU03c4_ {
        Ty::TBase(b) => match b {
          Base_ty::BInt(_) => _UU03c4_
          Base_ty::BString => _UU03c4_
          _ => Ty::TBase(Base_ty::BBool)
        }
        _ => Ty::TBase(Base_ty::BBool)
      }
      _ => match _UU03c4_ {
        Ty::TBase(b) => match b {
          Base_ty::BInt(_) => _UU03c4_
          _ => Ty::TBase(Base_ty::BBool)
        }
        _ => Ty::TBase(Base_ty::BBool)
      }
    }
    None => Ty::TBase(Base_ty::BBool)
  }
}

pub fn promote_call(t : Ident, _UU03b5_ : Ty, r : Ty, f : Expr, es : List[Expr]) -> Expr {
  Expr::ELet(Expr::ETuple(List::Cons(f, es)), Expr::ETry(Expr::EApp(Expr::EProj(Expr::EVar(Nat::O), Nat::O), map(fn(i) { Expr::EProj(Expr::EVar(Nat::O), i) }, seq(Nat::S(Nat::O), length(es)))), _UU03b5_, Expr::ERaise(Expr::EUp(t, Expr::EVar(Nat::O)), r), Expr::EVar(Nat::O)))
}

pub fn wrap_call(l : Cenv, _UU03b5_ : Ty, r : Ty, f : Expr, es : List[Expr]) -> Expr {
  match _UU03b5_ {
    Ty::TData(t, ts) => match ts {
      List::Nil => match (match l {
        Cenv::Mk_cenv(_, ce_exn) => ce_exn
      }) {
        Ty::TError => promote_call(t, _UU03b5_, r, f, es)
        _ => Expr::EApp(f, es)
      }
      List::Cons(_, _) => Expr::EApp(f, es)
    }
    _ => Expr::EApp(f, es)
  }
}

pub fn ctor_in(c : Ident, td : Tdef) -> Bool {
  match lookup_ctor(td, c) {
    Some(_) => true
    None => false
  }
}

pub fn is_rec(e : Senv, t : Ident) -> Bool {
  match assoc(t, match e {
    Senv::Mk_senv(_, _, se_sinfo, _, _) => se_sinfo
  }) {
    Some(_) => true
    None => false
  }
}

pub fn proj_pats(i : Nat, q : Pat, k : Nat, n : Nat) -> List[Pat] {
  map(fn(j) {
    match eqb0(j, i) {
      true => q
      false => Pat::PWild
    }
  }, seq(k, n))
}

pub fn field_proj(e : Senv, t : Ident, ts : List[Ty], i : Nat, e0 : Expr) -> Option[(Expr, Ty)] {
  match lookup_ty(match e {
    Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
  }, t) {
    Some(td) => match (match td {
      Tdef::Mk_tdef(_, _, td_ctors, _) => td_ctors
    }) {
      List::Nil => None
      List::Cons(cd, l) => match l {
        List::Nil => {
          let fs = map({ let a1 = fn(x1) { inst(ts, x1) }; fn(x1) { tsubst(a1, x1) } }, match cd {
            Cdef::Mk_cdef(_, cd_fields) => cd_fields
          })
          match nth_error(fs, i) {
            Some(_UU03c4_) => match _UU03c4_ {
              Ty::TRef(t0) => {
                let q = Pat::PRef(Pat::PVar)
                Some((Expr::EMatch(e0, t0, List::Cons((Pat::PConstr(match cd {
                  Cdef::Mk_cdef(cd_name, _) => cd_name
                }, proj_pats(i, q, Nat::O, length(fs))), Expr::EVar(Nat::O)), List::Nil)), t0))
              }
              _ => {
                let q = Pat::PVar
                Some((Expr::EMatch(e0, _UU03c4_, List::Cons((Pat::PConstr(match cd {
                  Cdef::Mk_cdef(cd_name, _) => cd_name
                }, proj_pats(i, q, Nat::O, length(fs))), Expr::EVar(Nat::O)), List::Nil)), _UU03c4_))
              }
            }
            None => None
          }
        }
        List::Cons(_, _) => None
      }
    }
    None => None
  }
}

pub fn trs(e : Senv) -> List[Trinfo] {
  match (match e {
    Senv::Mk_senv(_, _, _, _, se_x) => se_x
  }) {
    Xenv::Mk_xenv(x_traits, _, _, _, _, _) => x_traits
  }
}

pub fn asm_of(e : Senv, _UU0393_ : Lctx) -> List[Assumption] {
  flat_map(fn(a) {
    match a {
      (y, x) => match y {
        (tr, _UU03c4_) => match lookup_local(x, _UU0393_) {
          Some(i) => match nth_error(ctx_of(_UU0393_), i) {
            Some(t) => match eq_dec0(eqDec_ty, t, Ty::TData(tr, List::Cons(_UU03c4_, List::Nil))) {
              true => List::Cons(((tr, _UU03c4_), Expr::EVar(i)), List::Nil)
              false => List::Nil
            }
            None => List::Nil
          }
          None => List::Nil
        }
      }
    }
  }, match (match e {
    Senv::Mk_senv(_, _, _, _, se_x) => se_x
  }) {
    Xenv::Mk_xenv(_, _, _, _, _, x_asm) => x_asm
  })
}

pub fn has_dict(e : Senv, _UU0393_ : Lctx, tr : Ident, _UU03c4_ : Ty) -> Bool {
  match entails_dec(match (match e {
    Senv::Mk_senv(_, _, _, _, se_x) => se_x
  }) {
    Xenv::Mk_xenv(_, x_insts, _, _, _, _) => x_insts
  }, asm_of(e, _UU0393_), tr, _UU03c4_) {
    Sumor::Inleft(_) => true
    Sumor::Inright => false
  }
}

pub fn nbounds(e : Senv, g : Ident) -> Nat {
  length(sbounds(e, g))
}

pub fn meth_name(t : Ident, m : Ident) -> Ident {
  append(t, append(String0::String1(Ascii::Ascii0(false, true, false, true, true, true, false, false), String0::String1(Ascii::Ascii0(false, true, false, true, true, true, false, false), String0::EmptyString)), m))
}

pub fn has_meth(e : Senv, t : Ident, m : Ident) -> Bool {
  existsb(fn(tm) {
    match eqb4(fst(tm), t) {
      true => eqb4(snd(tm), m)
      false => false
    }
  }, match (match e {
    Senv::Mk_senv(_, _, _, _, se_x) => se_x
  }) {
    Xenv::Mk_xenv(_, _, _, x_meths, _, _) => x_meths
  })
}

pub fn meth_fn(e : Senv, _UU03c4_ : Ty, m : Ident) -> Bool {
  match head_name(_UU03c4_) {
    Some(h) => has_meth(e, h, m)
    None => false
  }
}

pub fn qual_builtin(t : Ident, m : Ident, n : Nat) -> Bool {
  match array_kind_of(t) {
    Some(_) => match n {
      Nat::O => eqb4(m, String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, true, true, true, false), String0::EmptyString))))
      Nat::S(n0) => match n0 {
        Nat::O => false
        Nat::S(n1) => match n1 {
          Nat::O => eqb4(m, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString)))))
          Nat::S(_) => false
        }
      }
    }
    None => match n {
      Nat::O => false
      Nat::S(n0) => match n0 {
        Nat::O => match eqb4(t, String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString)))) {
          true => eqb4(m, String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, true, true, true, false), String0::EmptyString))))
          false => false
        }
        Nat::S(_) => false
      }
    }
  }
}

pub fn arr_builtin(_UU03c4_ : Ty, m : Ident, n : Nat) -> Bool {
  match _UU03c4_ {
    Ty::TArray(k, _) => match k {
      Array_kind::AFixed => match n {
        Nat::O => eqb4(m, String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::EmptyString)))))))
        Nat::S(_) => false
      }
      Array_kind::AGrow => match n {
        Nat::O => eqb4(m, String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::EmptyString)))))))
        Nat::S(n0) => match n0 {
          Nat::O => eqb4(m, String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::EmptyString)))))
          Nat::S(_) => false
        }
      }
    }
    _ => false
  }
}

pub fn declares(e : Senv, m : Ident, tr : Ident) -> Bool {
  match find_trait(trs(e), tr) {
    Some(ti) => match method_of(ti, m) {
      Some(_) => true
      None => false
    }
    None => false
  }
}

pub fn asm_traits(e : Senv, _UU03c4_ : Ty) -> List[Ident] {
  map(fn(a) { fst(fst(a)) }, filter(fn(a) {
    match eq_dec0(eqDec_ty, snd(fst(a)), _UU03c4_) {
      true => true
      false => false
    }
  }, match (match e {
    Senv::Mk_senv(_, _, _, _, se_x) => se_x
  }) {
    Xenv::Mk_xenv(_, _, _, _, _, x_asm) => x_asm
  }))
}

pub fn dot_traits(_UU03c4_ : Ty) -> Bool {
  match _UU03c4_ {
    Ty::TVar(_) => true
    Ty::TData(t, _) => negb(existsb(fn(x1) { eqb4(t, x1) }, List::Cons(String0::String1(Ascii::Ascii0(true, true, true, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::EmptyString)))))), List::Cons(String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString))), List::Cons(String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))), List::Cons(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil))))))
    _ => false
  }
}

pub fn dot_trait(e : Senv, _UU0393_ : Lctx, m : Ident, _UU03c4_ : Ty) -> List[Ident] {
  filter(fn(tr) {
    match declares(e, m, tr) {
      true => has_dict(e, _UU0393_, tr, _UU03c4_)
      false => false
    }
  }, map(fn(t) {
    match t {
      Trinfo::Mk_trinfo(ti_name, _, _, _) => ti_name
    }
  }, trs(e)))
}

pub fn obj_of(e : Senv, _UU03c4_ : Ty) -> Option[Ident] {
  match _UU03c4_ {
    Ty::TData(on, ts) => match ts {
      List::Nil => find(fn(tr) { eqb4(obj_name(tr), on) }, match (match e {
        Senv::Mk_senv(_, _, _, _, se_x) => se_x
      }) {
        Xenv::Mk_xenv(_, _, _, _, x_objs, _) => x_objs
      })
      List::Cons(_, _) => None
    }
    _ => None
  }
}

pub fn obj_index(fs : List[(Ident, Msig)], m : Ident) -> Option[Nat] {
  match fs {
    List::Nil => None
    List::Cons(p, fs_) => match p {
      (_, sg) => match eqb4(match sg {
        Msig::Mk_msig(ms_name, _, _, _) => ms_name
      }, m) {
        true => Some(Nat::O)
        false => option_map(fn(x) { Nat::S(x) }, obj_index(fs_, m))
      }
    }
  }
}

pub fn assemble(op : Bool, given : List[((Nat, Pat), Lctx)], j : Nat, fs : List[Ty]) -> Option[(List[Pat], Lctx)] {
  match fs {
    List::Nil => Some((List::Nil, List::Nil))
    List::Cons(_, fs_) => match find(fn(x) { eqb0(fst(fst(x)), j) }, given) {
      Some(p) => match p {
        (p0, _UU0394_) => match p0 {
          (_, q) => {
            let p1 = (q, _UU0394_)
            match p1 {
              (q0, _UU0394_0) => match assemble(op, given, Nat::S(j), fs_) {
                Some(p2) => match p2 {
                  (qs, _UU0394_s) => Some((List::Cons(q0, qs), app(_UU0394_0, _UU0394_s)))
                }
                None => None
              }
            }
          }
        }
      }
      None => match op {
        true => {
          let p = (Pat::PWild, List::Nil)
          match p {
            (q, _UU0394_) => match assemble(op, given, Nat::S(j), fs_) {
              Some(p0) => match p0 {
                (qs, _UU0394_s) => Some((List::Cons(q, qs), app(_UU0394_, _UU0394_s)))
              }
              None => None
            }
          }
        }
        false => None
      }
    }
  }
}

pub fn same_fields(declared : List[Ident], written : List[Ident]) -> Bool {
  match eqb0(length(declared), length(written)) {
    true => forallb(fn(f) {
      match index_of(f, declared) {
        Some(_) => true
        None => false
      }
    }, written)
    false => false
  }
}

pub fn pos_of(j : Nat, ixs : List[Nat]) -> Option[Nat] {
  match ixs {
    List::Nil => None
    List::Cons(i, ixs_) => match eqb0(i, j) {
      true => Some(Nat::O)
      false => option_map(fn(x) { Nat::S(x) }, pos_of(j, ixs_))
    }
  }
}

pub fn rec_vars(ixs : List[Nat], n : Nat) -> Option[List[Expr]] {
  match eqb0(length(ixs), n) {
    true => all_some(map(fn(j) {
      option_map(fn(k) { Expr::EProj(Expr::EVar(Nat::O), k) }, pos_of(j, ixs))
    }, seq(Nat::O, n)))
    false => None
  }
}

pub fn field_cell(e : Senv, t : Ident, ts : List[Ty], i : Nat) -> Option[((Ident, Nat), Ty)] {
  match lookup_ty(match e {
    Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
  }, t) {
    Some(td) => match (match td {
      Tdef::Mk_tdef(_, _, td_ctors, _) => td_ctors
    }) {
      List::Nil => None
      List::Cons(cd, l) => match l {
        List::Nil => {
          let fs = map({ let a1 = fn(x1) { inst(ts, x1) }; fn(x1) { tsubst(a1, x1) } }, match cd {
            Cdef::Mk_cdef(_, cd_fields) => cd_fields
          })
          match nth_error(fs, i) {
            Some(t0) => match t0 {
              Ty::TRef(t1) => Some(((match cd {
                Cdef::Mk_cdef(cd_name, _) => cd_name
              }, length(fs)), t1))
              _ => None
            }
            None => None
          }
        }
        List::Cons(_, _) => None
      }
    }
    None => None
  }
}

pub fn names_ctx(xs : List[Ident], _UU03c4_s : List[Ty]) -> Lctx {
  combine(map(fn(x) { Some(x) }, xs), _UU03c4_s)
}

pub fn hd_env(ps : List[Ty], _UU03c4_ : Ty, l : Cenv) -> Cenv {
  push_lab(Lab::Mk_lab(None, Lab_kind::LKHead, ps, _UU03c4_), l)
}

pub fn while_loop(_UU03c4_ : Ty, c : Expr, b : Expr, nb : Expr) -> Expr {
  Expr::ELoop(Expr::ETuple(List::Nil), List::Nil, _UU03c4_, Expr::EIf(c, Expr::ELet(b, Expr::EJump(Ctl::CCont, Nat::O, Expr::ETuple(List::Nil), _UU03c4_)), nb))
}

pub fn upd_next(off : Nat, names : List[Ident], us : List[(Ident, Expr)]) -> List[Expr] {
  map(fn(i) {
    match find(fn(yu) {
      match index_of(fst(yu), names) {
        Some(j) => eqb0(j, i)
        None => false
      }
    }, us) {
      Some(p) => match p {
        (_, u) => u
      }
      None => Expr::EVar(add(off, i))
    }
  }, seq(Nat::O, length(names)))
}

pub fn for_next(names : List[Ident], us : List[(Ident, Expr)]) -> List[Expr] {
  upd_next(Nat::S(Nat::O), names, us)
}

pub fn for_loop(es : List[Expr], _UU03c4_s : List[Ty], _UU03c4_ : Ty, c : Option[Expr], b : Expr, names : List[Ident], us : List[(Ident, Expr)], nb : Expr) -> Expr {
  let step = Expr::ELet(eblock(Ty::TBase(Base_ty::BUnit), b), Expr::EJump(Ctl::CCont, Nat::O, Expr::ETuple(for_next(names, us)), _UU03c4_))
  Expr::ELoop(Expr::ETuple(es), _UU03c4_s, _UU03c4_, match c {
    Some(c0) => Expr::EIf(c0, step, nb)
    None => step
  })
}

pub fn fi_t1(it : Iter_src) -> Ty {
  match it {
    Iter_src::IRange(_, kk) => Ty::TBase(Base_ty::BInt(kk))
    Iter_src::IArray(k, t) => Ty::TArray(k, t)
  }
}

pub fn fi_t2(it : Iter_src) -> Ty {
  match it {
    Iter_src::IRange(_, kk) => Ty::TBase(Base_ty::BInt(kk))
    Iter_src::IArray(_, _) => Ty::TBase(Base_ty::BInt(Int_kind::I32))
  }
}

pub fn fi_ivs(it : Iter_src) -> List[Ty] {
  match it {
    Iter_src::IRange(rk, kk) => match rk {
      Range_kind::RUpExcl => List::Cons(Ty::TBase(Base_ty::BInt(kk)), List::Nil)
      Range_kind::RDownExcl => List::Cons(Ty::TBase(Base_ty::BInt(kk)), List::Nil)
      _ => List::Cons(Ty::TBase(Base_ty::BInt(kk)), List::Cons(Ty::TBase(Base_ty::BBool), List::Nil))
    }
    Iter_src::IArray(_, _) => List::Cons(Ty::TBase(Base_ty::BInt(Int_kind::I32)), List::Nil)
  }
}

pub fn fi_init(it : Iter_src) -> List[Expr] {
  match it {
    Iter_src::IRange(rk, _) => match rk {
      Range_kind::RUpExcl => List::Cons(Expr::EVar(Nat::S(Nat::O)), List::Nil)
      Range_kind::RDownExcl => List::Cons(Expr::EVar(Nat::S(Nat::O)), List::Nil)
      _ => List::Cons(Expr::EVar(Nat::S(Nat::O)), List::Cons(e_false, List::Nil))
    }
    Iter_src::IArray(_, _) => List::Cons(Expr::ELit(Lit::LInt(Int_kind::I32, Z::Z0)), List::Nil)
  }
}

pub fn fi_n(it : Iter_src, _UU03c4_s : List[Ty]) -> Nat {
  add(length(fi_ivs(it)), length(_UU03c4_s))
}

pub fn fi_cond(it : Iter_src, n : Nat) -> Expr {
  let v = Expr::EVar(Nat::O)
  let bound = Expr::EVar(n)
  match it {
    Iter_src::IRange(rk, kk) => match rk {
      Range_kind::RUpExcl => icmp(Cmp_op::CLt, kk, v, bound)
      Range_kind::RUpIncl => Expr::EIf(Expr::EVar(Nat::S(Nat::O)), e_false, icmp(Cmp_op::CLe, kk, v, bound))
      Range_kind::RDownExcl => icmp(Cmp_op::CGt, kk, v, bound)
      Range_kind::RDownIncl => Expr::EIf(Expr::EVar(Nat::S(Nat::O)), e_false, icmp(Cmp_op::CGe, kk, v, bound))
    }
    Iter_src::IArray(_, _) => icmp(Cmp_op::CLt, Int_kind::I32, v, bound)
  }
}

pub fn fi_elem(it : Iter_src, n : Nat) -> Expr {
  match it {
    Iter_src::IRange(rk, kk) => match rk {
      Range_kind::RDownExcl => iarith(Arith_op::ASub, kk, Expr::EVar(Nat::O), int1(kk))
      _ => Expr::EVar(Nat::O)
    }
    Iter_src::IArray(k, t) => Expr::EMem(Mem_op::MIndex(k, t), List::Cons(Expr::EVar(Nat::S(n)), List::Cons(Expr::EVar(Nat::O), List::Nil)))
  }
}

pub fn fi_elem_ty(it : Iter_src) -> Ty {
  match it {
    Iter_src::IRange(_, kk) => Ty::TBase(Base_ty::BInt(kk))
    Iter_src::IArray(_, t) => t
  }
}

pub fn fi_next(it : Iter_src, d : Nat, n : Nat) -> List[Expr] {
  let vv = Expr::EVar(add(Nat::S(Nat::O), d))
  let bb = Expr::EVar(add(add(Nat::S(Nat::O), d), n))
  match it {
    Iter_src::IRange(rk, kk) => match rk {
      Range_kind::RUpExcl => List::Cons(iarith(Arith_op::AAdd, kk, vv, int1(kk)), List::Nil)
      Range_kind::RUpIncl => List::Cons(Expr::EIf(icmp(Cmp_op::CEq, kk, vv, bb), vv, iarith(Arith_op::AAdd, kk, vv, int1(kk))), List::Cons(icmp(Cmp_op::CEq, kk, vv, bb), List::Nil))
      Range_kind::RDownExcl => List::Cons(iarith(Arith_op::ASub, kk, vv, int1(kk)), List::Nil)
      Range_kind::RDownIncl => List::Cons(Expr::EIf(icmp(Cmp_op::CEq, kk, vv, bb), vv, iarith(Arith_op::ASub, kk, vv, int1(kk))), List::Cons(icmp(Cmp_op::CEq, kk, vv, bb), List::Nil))
    }
    Iter_src::IArray(_, _) => List::Cons(iarith(Arith_op::AAdd, Int_kind::I32, vv, int1(Int_kind::I32)), List::Nil)
  }
}

pub fn fo_ctx(it : Iter_src, _UU0393_ : Lctx) -> Lctx {
  List::Cons((None, fi_t2(it)), List::Cons((None, fi_t1(it)), _UU0393_))
}

pub fn fl_ctx(it : Iter_src, names : List[Ident], _UU03c4_s : List[Ty], _UU0393_ : Lctx) -> Lctx {
  app(map(fn(t) { (None, t) }, fi_ivs(it)), app(names_ctx(names, _UU03c4_s), fo_ctx(it, _UU0393_)))
}

pub fn fi_loop_env(it : Iter_src, _UU03c4_s : List[Ty], _UU03c4_ : Ty, l : Cenv) -> Cenv {
  hd_env(app(fi_ivs(it), _UU03c4_s), _UU03c4_, l)
}

pub fn fi_state_env(it : Iter_src, _UU03c4_s : List[Ty], _UU03c4_ : Ty, l : Cenv) -> Cenv {
  push_lab(Lab::Mk_lab(None, Lab_kind::LKHead, List::Nil, Ty::TTuple(_UU03c4_s)), fi_loop_env(it, _UU03c4_s, _UU03c4_, l))
}

pub fn fi_body_env(x : Option[Ident], it : Iter_src, _UU03c4_s : List[Ty], _UU03c4_ : Ty, l : Cenv) -> Cenv {
  push_lab(Lab::Mk_lab(x, Lab_kind::LKForInBody, List::Nil, Ty::TBase(Base_ty::BUnit)), fi_state_env(it, _UU03c4_s, _UU03c4_, l))
}

pub fn forin_loop(it : Iter_src, e1 : Expr, e2 : Expr, es : List[Expr], _UU03c4_s : List[Ty], _UU03c4_ : Ty, q : Pat, scrut : Expr, d : Nat, b : Expr, names : List[Ident], us : List[(Ident, Expr)], nb : Expr) -> Expr {
  let n = fi_n(it, _UU03c4_s)
  let state = upd_next(add(add(Nat::S(Nat::O), d), length(fi_ivs(it))), names, us)
  let blk = eblock(Ty::TTuple(_UU03c4_s), Expr::ELet(eblock(Ty::TBase(Base_ty::BUnit), b), Expr::ETuple(state)))
  let next = app(fi_next(it, d, n), map(fn(j) { Expr::EProj(Expr::EVar(Nat::O), j) }, seq(Nat::O, length(names))))
  let step = Expr::ELet(blk, Expr::EJump(Ctl::CCont, Nat::O, Expr::ETuple(next), _UU03c4_))
  Expr::ELet(e1, Expr::ELet(e2, Expr::ELoop(Expr::ETuple(app(fi_init(it), es)), app(fi_ivs(it), _UU03c4_s), _UU03c4_, Expr::EIf(fi_cond(it, n), Expr::EMatch(scrut, _UU03c4_, List::Cons((q, step), List::Nil)), nb))))
}

pub fn catch_owner(e : Senv, sp : Spat) -> Option[Ident] {
  match sp {
    Spat::SPConstr(_, t0, c, _, _) => match t0 {
      Some(t) => Some(t)
      None => match filter(fn(td) {
        match (match td {
          Tdef::Mk_tdef(_, _, _, td_err) => td_err
        }) {
          true => ctor_in(c, td)
          false => false
        }
      }, match (match e {
        Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
      }) {
        Genv::Mk_genv(ge_types, _) => ge_types
      }) {
        List::Nil => None
        List::Cons(td, l) => match l {
          List::Nil => Some(match td {
            Tdef::Mk_tdef(td_name, _, _, _) => td_name
          })
          List::Cons(_, _) => None
        }
      }
    }
    _ => None
  }
}

pub fn catch_step(e : Senv, acc : Catch_info, c : (Spat, Sexpr)) -> Catch_info {
  match catch_owner(e, fst(c)) {
    Some(t) => match acc {
      Catch_info::CINone => Catch_info::CIOne(t)
      Catch_info::CIOne(t_) => match eqb4(t, t_) {
        true => acc
        false => Catch_info::CIMany
      }
      Catch_info::CIMany => Catch_info::CIMany
    }
    None => acc
  }
}

pub fn catch_of(e : Senv, cases : List[(Spat, Sexpr)]) -> Catch_info {
  fold_left(fn(x1) { fn(x2) { catch_step(e, x1, x2) } }, cases, Catch_info::CINone)
}

pub fn fail_val(a : Expr) -> Expr {
  Expr::EConstr(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil, Expr::ETuple(List::Cons(a, List::Nil)))
}

pub(all) enum Mode {
  Syn
  Chk(Ty)
}

pub fn hint(m : Mode) -> Option[Ty] {
  match m {
    Mode::Syn => None
    Mode::Chk(_UU03c4_) => Some(_UU03c4_)
  }
}

pub fn bcheck(b : Bool, err : Elab_error) -> Result0[Unit, Elab_error] {
  match b {
    true => Result0::Ok(())
    false => Result0::Err(err)
  }
}

pub fn postpone(s : Sexpr) -> Bool {
  match s {
    Sexpr::SLam(_, ps, _, _, _) => existsb(fn(xa) {
      match snd(xa) {
        Some(_) => false
        None => true
      }
    }, ps)
    _ => false
  }
}

pub fn int_lit_dec(a : Sexpr) -> Sumor[SigT[Pos, SigT[Option[Int_kind], Z]]] {
  match a {
    Sexpr::SLit(q, l) => match l {
      Slit::SLInt(k, z) => Sumor::Inleft(SigT::ExistT(q, SigT::ExistT(k, z)))
      _ => Sumor::Inright
    }
    _ => Sumor::Inright
  }
}

pub type Sout = SigT[Ty, Expr]

pub type Cout = Expr

pub type Out = SigT[Ty, Expr]

pub fn cO(_ : Senv, _ : Cenv, _ : Lctx, _ : Sexpr, _UU03c4_ : Ty, x : Cout) -> Out {
  SigT::ExistT(_UU03c4_, x)
}

pub fn oc(_ : Senv, _ : Cenv, _ : Lctx, _ : Sexpr, _ : Ty, x : Out) -> Cout {
  match x {
    SigT::ExistT(_, s0) => s0
  }
}

pub fn okc(e : Senv, l : Cenv, _UU0393_ : Lctx, s : Sexpr, _UU03c4_ : Ty, x : Cout) -> Result0[Out, Elab_error] {
  Result0::Ok(cO(e, l, _UU0393_, s, _UU03c4_, x))
}

pub fn cres(e : Senv, l : Cenv, _UU0393_ : Lctx, s : Sexpr, _UU03c4_ : Ty, r : Result0[Out, Elab_error]) -> Result0[Cout, Elab_error] {
  match r {
    Result0::Ok(x) => Result0::Ok(oc(e, l, _UU0393_, s, _UU03c4_, x))
    Result0::Err(err) => Result0::Err(err)
  }
}

pub fn ety_dec(e : Senv, t : Sty) -> Result0[Ty, Elab_error] {
  match ety(e, t) {
    Result0::Ok(_UU03c4_) => Result0::Ok(_UU03c4_)
    Result0::Err(err) => Result0::Err(err)
  }
}

pub fn err_dec(e : Senv, p : Pos, t : Ident) -> Result0[Unit, Elab_error] {
  bind(of_option(lookup_ty(match e {
    Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
  }, t), Elab_error::EE_NotError(p, Ty::TData(t, List::Nil))), fn(x) {
    bind(bcheck(match x {
      Tdef::Mk_tdef(_, _, _, td_err) => td_err
    }, Elab_error::EE_NotError(p, Ty::TData(t, List::Nil))), fn(_) { Result0::Ok(()) })
  })
}

pub fn eff_dec(p : Pos, _UU03b5_ : Ty, _UU03c1_ : Ty) -> Result0[Unit, Elab_error] {
  match ty_eq_dec(_UU03b5_)(Ty::TBase(Base_ty::BNever)) {
    true => Result0::Ok(())
    false => match ty_eq_dec(_UU03b5_)(_UU03c1_) {
      true => Result0::Ok(())
      false => Result0::Err(Elab_error::EE_Type(p, Type_error::E_Effect(_UU03b5_, _UU03c1_)))
    }
  }
}

pub fn allowed_dec(e : Senv, p : Pos, _UU03b5_ : Ty, _UU03c1_ : Ty) -> Result0[Unit, Elab_error] {
  match _UU03b5_ {
    Ty::TData(t, ts) => match ts {
      List::Nil => {
        let _UU03b5_0 = Ty::TData(t, List::Nil)
        match _UU03c1_ {
          Ty::TError => err_dec(e, p, t)
          x => eff_dec(p, _UU03b5_0, x)
        }
      }
      List::Cons(t0, l) => eff_dec(p, Ty::TData(t, List::Cons(t0, l)), _UU03c1_)
    }
    x => eff_dec(p, x, _UU03c1_)
  }
}

pub fn field_proj_dec(e : Senv, p : Pos, t : Ident, ts : List[Ty], i : Nat, e0 : Expr) -> Result0[(Expr, Ty), Elab_error] {
  match field_proj(e, t, ts, i, e0) {
    Some(r) => Result0::Ok(r)
    None => Result0::Err(Elab_error::EE_Type(p, Type_error::E_TupleIndex(i, Ty::TData(t, ts))))
  }
}

pub fn dict_dec(e : Senv, p : Pos, _UU0393_ : Lctx, tr : Ident, _UU03c4_ : Ty) -> Result0[Expr, Elab_error] {
  match entails_dec(match (match e {
    Senv::Mk_senv(_, _, _, _, se_x) => se_x
  }) {
    Xenv::Mk_xenv(_, x_insts, _, _, _, _) => x_insts
  }, asm_of(e, _UU0393_), tr, _UU03c4_) {
    Sumor::Inleft(s) => Result0::Ok(s)
    Sumor::Inright => Result0::Err(Elab_error::EE_NoInstance(p, tr, _UU03c4_))
  }
}

pub fn dicts_dec(e : Senv, p : Pos, _UU0393_ : Lctx, _UU03c4_s : List[Ty]) -> Result0[List[Expr], Elab_error] {
  match _UU03c4_s {
    List::Nil => Result0::Ok(List::Nil)
    List::Cons(t, _UU03c4_s_) => bind(match t {
      Ty::TData(tr, ts) => match ts {
        List::Nil => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::EmptyString))))))))))))))))))))))
        List::Cons(_UU03c4_, l) => match l {
          List::Nil => bind(dict_dec(e, p, _UU0393_, tr, _UU03c4_), fn(x) { Result0::Ok(x) })
          List::Cons(_, _) => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::EmptyString))))))))))))))))))))))
        }
      }
      _ => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::EmptyString))))))))))))))))))))))
    }, fn(x) {
      bind(dicts_dec(e, p, _UU0393_, _UU03c4_s_), fn(x0) { Result0::Ok(List::Cons(x, x0)) })
    })
  }
}

pub fn obj_meth_dec(e : Senv, p : Pos, _UU0393_o : Lctx, _UU03c4_ : Ty, sm : (Ident, Msig), fty : Ty) -> Result0[Expr, Elab_error] {
  bind(of_option(find_trait(trs(e), fst(sm)), Elab_error::EE_NotObjectSafe(p, fst(sm))), fn(x) {
    bind(of_option(method_of(x, match snd(sm) {
      Msig::Mk_msig(ms_name, _, _, _) => ms_name
    }), Elab_error::EE_NoMethod(p, match snd(sm) {
      Msig::Mk_msig(ms_name, _, _, _) => ms_name
    }, _UU03c4_)), fn(x0) {
      match x0 {
        (i, _) => match fty {
          Ty::TArrow(ps, r, _UU03b5_) => bind(dict_dec(e, p, app(map(fn(t) { (None, t) }, ps), _UU0393_o), fst(sm), _UU03c4_), fn(x1) {
            bind(field_proj_dec(e, p, fst(sm), List::Cons(_UU03c4_, List::Nil), i, x1), fn(x2) {
              match x2 {
                (mv, t) => match ty_eq_dec(t)(Ty::TArrow(List::Cons(_UU03c4_, ps), r, _UU03b5_)) {
                  true => Result0::Ok(Expr::ELam(ps, r, _UU03b5_, Expr::EApp(mv, List::Cons(Expr::EVar(length(ps)), map(fn(x3) { Expr::EVar(x3) }, seq(Nat::O, length(ps)))))))
                  false => Result0::Err(Elab_error::EE_Annot(p, Ty::TArrow(List::Cons(_UU03c4_, ps), r, _UU03b5_), t))
                }
              }
            })
          })
          _ => Result0::Err(Elab_error::EE_NotObjectSafe(p, fst(sm)))
        }
      }
    })
  })
}

pub fn obj_meths_dec(e : Senv, p : Pos, _UU0393_o : Lctx, _UU03c4_ : Ty, sms : List[(Ident, Msig)], ftys : List[Ty]) -> Result0[List[Expr], Elab_error] {
  match sms {
    List::Nil => match ftys {
      List::Nil => Result0::Ok(List::Nil)
      List::Cons(_, _) => Result0::Err(Elab_error::EE_NotObjectSafe(p, String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))))))))
    }
    List::Cons(sm, sms_) => match ftys {
      List::Nil => Result0::Err(Elab_error::EE_NotObjectSafe(p, String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))))))))
      List::Cons(t, ts_) => bind(obj_meth_dec(e, p, _UU0393_o, _UU03c4_, sm, t), fn(x) {
        bind(obj_meths_dec(e, p, _UU0393_o, _UU03c4_, sms_, ts_), fn(x0) { Result0::Ok(List::Cons(x, x0)) })
      })
    }
  }
}

pub fn obj_coerce(e : Senv, p : Pos, _UU0393_ : Lctx, e0 : Expr, _UU03c4_ : Ty, _ : Ty, tr : Ident) -> Result0[Expr, Elab_error] {
  bind(of_option(lookup_ty(match e {
    Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
  }, obj_name(tr)), Elab_error::EE_UnknownType(p, obj_name(tr))), fn(x) {
    match eq_dec(match x {
      Tdef::Mk_tdef(_, td_tparams, _, _) => td_tparams
    }, Nat::O) {
      true => bind(of_option(lookup_ctor(x, obj_name(tr)), Elab_error::EE_UnknownCtor(p, obj_name(tr))), fn(x0) {
        bind(obj_meths_dec(e, p, List::Cons((None, _UU03c4_), _UU0393_), _UU03c4_, obj_fields(trs(e), tr), map({ let a1 = fn(x1) { inst(List::Nil, x1) }; fn(x1) { tsubst(a1, x1) } }, match x0 {
          Cdef::Mk_cdef(_, cd_fields) => cd_fields
        })), fn(x1) {
          Result0::Ok(Expr::ELet(e0, Expr::EConstr(obj_name(tr), obj_name(tr), List::Nil, Expr::ETuple(x1))))
        })
      })
      false => Result0::Err(Elab_error::EE_UnknownType(p, obj_name(tr)))
    }
  })
}

pub fn coerce(e : Senv, p : Pos, _UU0393_ : Lctx, e0 : Expr, _UU03c4__ : Ty, _UU03c4_ : Ty) -> Result0[Expr, Elab_error] {
  match ty_eq_dec(_UU03c4__)(_UU03c4_) {
    true => Result0::Ok(e0)
    false => match obj_of(e, _UU03c4_) {
      Some(tr) => obj_coerce(e, p, _UU0393_, e0, _UU03c4__, _UU03c4_, tr)
      None => match _UU03c4__ {
        Ty::TData(t, ts) => match ts {
          List::Nil => match _UU03c4_ {
            Ty::TError => bind(err_dec(e, p, t), fn(_) { Result0::Ok(Expr::EUp(t, e0)) })
            _ => Result0::Err(Elab_error::EE_Annot(p, _UU03c4_, _UU03c4__))
          }
          List::Cons(_, _) => Result0::Err(Elab_error::EE_Annot(p, _UU03c4_, _UU03c4__))
        }
        _ => Result0::Err(Elab_error::EE_Annot(p, _UU03c4_, _UU03c4__))
      }
    }
  }
}

pub fn fin(e : Senv, p : Pos, l : Cenv, _UU0393_ : Lctx, s : Sexpr, m : Mode, r : Result0[Sout, Elab_error]) -> Result0[Out, Elab_error] {
  match m {
    Mode::Syn => r
    Mode::Chk(_UU03c4_) => bind(r, fn(x) {
      match x {
        SigT::ExistT(_UU03c4__, s0) => bind(coerce(e, p, _UU0393_, s0, _UU03c4__, _UU03c4_), fn(x0) { okc(e, l, _UU0393_, s, _UU03c4_, x0) })
      }
    })
  }
}

pub fn binop_dec(p : Pos, op : Ident, _UU03c4_ : Ty, a : Expr, b : Expr) -> Result0[Expr, Elab_error] {
  match elab_binop(p, op, _UU03c4_, a, b) {
    Result0::Ok(e) => Result0::Ok(e)
    Result0::Err(err) => Result0::Err(err)
  }
}

pub fn targs(p : Pos, g : Ident, n : Nat, st : List[Option[Ty]]) -> Result0[List[Ty], Elab_error] {
  match all_some(st) {
    Some(ts) => match eq_dec(length(ts), n) {
      true => Result0::Ok(ts)
      false => Result0::Err(Elab_error::EE_CannotInfer(p, g))
    }
    None => Result0::Err(Elab_error::EE_CannotInfer(p, g))
  }
}

pub fn fn_targs(p : Pos, g : Ident, fd : Fdef, st : List[Option[Ty]]) -> Result0[List[Ty], Elab_error] {
  targs(p, g, match fd {
    Fdef::Mk_fdef(_, fd_tparams, _, _, _, _) => fd_tparams
  }, st)
}

pub fn no_bounds(e : Senv, p : Pos, g : Ident) -> Result0[Unit, Elab_error] {
  match sbounds(e, g) {
    List::Nil => Result0::Ok(())
    List::Cons(_, _) => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::EmptyString))))))))))))))))))))))))))))))
  }
}

pub fn params_ann_dec(e : Senv, p : Pos, ps : List[(Ident, Option[Sty])], exps : List[Option[Ty]]) -> Result0[List[Ty], Elab_error] {
  match ps {
    List::Nil => Result0::Ok(List::Nil)
    List::Cons(p0, ps_) => match p0 {
      (x, a) => bind(match a {
        Some(t) => bind(ety_dec(e, t), fn(x0) { Result0::Ok(x0) })
        None => match hd_error(exps) {
          Some(o) => match o {
            Some(_UU03c4_) => Result0::Ok(_UU03c4_)
            None => Result0::Err(Elab_error::EE_LambdaParam(p, x))
          }
          None => Result0::Err(Elab_error::EE_LambdaParam(p, x))
        }
      }, fn(x0) {
        bind(params_ann_dec(e, p, ps_, tl(exps)), fn(x1) { Result0::Ok(List::Cons(x0, x1)) })
      })
    }
  }
}

pub fn params_syn_dec(e : Senv, p : Pos, ps : List[(Ident, Option[Sty])]) -> Result0[List[Ty], Elab_error] {
  match ps {
    List::Nil => Result0::Ok(List::Nil)
    List::Cons(p0, ps_) => match p0 {
      (x, a) => bind(match a {
        Some(t) => bind(ety_dec(e, t), fn(x0) { Result0::Ok(x0) })
        None => Result0::Err(Elab_error::EE_LambdaParam(p, x))
      }, fn(x0) {
        bind(params_syn_dec(e, p, ps_), fn(x1) { Result0::Ok(List::Cons(x0, x1)) })
      })
    }
  }
}

pub fn params_fit(e : Senv, p : Pos, ps : List[(Ident, Option[Sty])], _UU03c4_s : List[Ty]) -> Result0[Unit, Elab_error] {
  match ps {
    List::Nil => match _UU03c4_s {
      List::Nil => Result0::Ok(())
      List::Cons(_, _) => Result0::Err(Elab_error::EE_Type(p, Type_error::E_ArgArity(length(_UU03c4_s), length(ps))))
    }
    List::Cons(p0, ps_) => match p0 {
      (_, a) => match _UU03c4_s {
        List::Nil => Result0::Err(Elab_error::EE_Type(p, Type_error::E_ArgArity(length(_UU03c4_s), length(ps))))
        List::Cons(_UU03c4_, _UU03c4_s_) => bind(match a {
          Some(t) => bind(ety_dec(e, t), fn(x) {
            match ty_eq_dec(x)(_UU03c4_) {
              true => Result0::Ok(())
              false => Result0::Err(Elab_error::EE_Annot(p, _UU03c4_, x))
            }
          })
          None => Result0::Ok(())
        }, fn(_) { bind(params_fit(e, p, ps_, _UU03c4_s_), fn(_) { Result0::Ok(()) }) })
      }
    }
  }
}

pub fn ann_fit(e : Senv, p : Pos, a : Option[Sty], _UU03c4_ : Ty) -> Result0[Unit, Elab_error] {
  match a {
    Some(t) => bind(ety_dec(e, t), fn(x) {
      match ty_eq_dec(x)(_UU03c4_) {
        true => Result0::Ok(())
        false => Result0::Err(Elab_error::EE_Annot(p, _UU03c4_, x))
      }
    })
    None => Result0::Ok(())
  }
}

pub fn eff_fit(e : Senv, p : Pos, a : Option[Option[Sty]], _UU03b5_ : Ty) -> Result0[Unit, Elab_error] {
  match a {
    Some(o) => match o {
      Some(t) => ann_fit(e, p, Some(t), _UU03b5_)
      None => match ty_eq_dec(_UU03b5_)(Ty::TBase(Base_ty::BNever)) {
        true => Result0::Ok(())
        false => Result0::Err(Elab_error::EE_Annot(p, Ty::TBase(Base_ty::BNever), _UU03b5_))
      }
    }
    None => Result0::Ok(())
  }
}

pub fn eff_pick(e : Senv, a : Option[Option[Sty]], exp : Option[Ty]) -> Result0[Ty, Elab_error] {
  match a {
    Some(o) => match o {
      Some(t) => bind(ety_dec(e, t), fn(x) { Result0::Ok(x) })
      None => Result0::Ok(Ty::TBase(Base_ty::BNever))
    }
    None => Result0::Ok(match exp {
      Some(_UU03b5_) => _UU03b5_
      None => Ty::TBase(Base_ty::BNever)
    })
  }
}

pub fn eff_syn_dec(e : Senv, a : Option[Option[Sty]]) -> Result0[Ty, Elab_error] {
  match a {
    Some(o) => match o {
      Some(t) => bind(ety_dec(e, t), fn(x) { Result0::Ok(x) })
      None => Result0::Ok(Ty::TBase(Base_ty::BNever))
    }
    None => Result0::Ok(Ty::TBase(Base_ty::BNever))
  }
}

pub fn chk_list(e : Senv, p : Pos, l : Cenv, _UU0393_ : Lctx, f : (Sexpr) -> (Ty) -> Result0[Cout, Elab_error], ss : List[Sexpr], _UU03c4_s : List[Ty]) -> Result0[List[Expr], Elab_error] {
  match ss {
    List::Nil => match _UU03c4_s {
      List::Nil => Result0::Ok(List::Nil)
      List::Cons(_, _) => Result0::Err(Elab_error::EE_Type(p, Type_error::E_ArgArity(length(_UU03c4_s), length(ss))))
    }
    List::Cons(s, ss_) => match _UU03c4_s {
      List::Nil => Result0::Err(Elab_error::EE_Type(p, Type_error::E_ArgArity(length(_UU03c4_s), length(ss))))
      List::Cons(_UU03c4_, _UU03c4_s_) => bind(f(s)(_UU03c4_), fn(x) {
        bind(chk_list(e, p, l, _UU0393_, f, ss_, _UU03c4_s_), fn(x0) { Result0::Ok(List::Cons(x, x0)) })
      })
    }
  }
}

pub fn syn_list(e : Senv, l : Cenv, _UU0393_ : Lctx, f : (Sexpr) -> Result0[Sout, Elab_error], ss : List[Sexpr]) -> Result0[SigT[List[Ty], List[Expr]], Elab_error] {
  match ss {
    List::Nil => Result0::Ok(SigT::ExistT(List::Nil, List::Nil))
    List::Cons(s, ss_) => bind(f(s), fn(x) {
      match x {
        SigT::ExistT(_UU03c4_, s0) => bind(syn_list(e, l, _UU0393_, f, ss_), fn(x0) {
          match x0 {
            SigT::ExistT(_UU03c4_s, s1) => Result0::Ok(SigT::ExistT(List::Cons(_UU03c4_, _UU03c4_s), List::Cons(s0, s1)))
          }
        })
      }
    })
  }
}

pub(all) enum Ahd {
  AH_Chk(Ty, Expr)
  AH_Syn(Ty, Expr)
  AH_Post
}

pub type Ares = List[SigT[Sexpr, Ahd]]

pub fn[A] is_none(o : Option[A]) -> Bool {
  match o {
    Some(_) => false
    None => true
  }
}

pub fn split_hd(ps : List[Ty]) -> (Option[Ty], List[Ty]) {
  match ps {
    List::Nil => (None, List::Nil)
    List::Cons(t, ts) => (Some(t), ts)
  }
}

pub fn pass1(e : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], l : Cenv, _UU0393_ : Lctx, args : List[Sexpr], ps : List[Ty], st : List[Option[Ty]]) -> Result0[(Ares, List[Option[Ty]]), Elab_error] {
  match args {
    List::Nil => Result0::Ok((List::Nil, st))
    List::Cons(s, args_) => match split_hd(ps) {
      (pt, ps_) => {
        let ex = match pt {
          Some(t) => resolve(st, t)
          None => None
        }
        bind(match (match postpone(s) {
          true => is_none(ex)
          false => false
        }) {
          true => Result0::Ok((Ahd::AH_Post, st))
          false => match ex {
            Some(t) => bind(cres(e, l, _UU0393_, s, t, rec(s)(l)(_UU0393_)(Mode::Chk(t))), fn(x) { Result0::Ok((Ahd::AH_Chk(t, x), st)) })
            None => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
              match x {
                SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), match pt {
                  Some(q) => tmatch(q, t, st)
                  None => st
                }))
              }
            })
          }
        }, fn(x) {
          match x {
            (h, st1) => bind(pass1(e, rec, l, _UU0393_, args_, ps_, st1), fn(x0) {
              match x0 {
                (a, st2) => Result0::Ok((List::Cons(SigT::ExistT(s, h), a), st2))
              }
            })
          }
        })
      }
    }
  }
}

pub fn ahd_cast(_ : Senv, _ : Cenv, _ : Lctx, _ : Sexpr, _ : Sexpr, h : Ahd) -> Ahd {
  h
}

pub fn late_lam(e : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], l : Cenv, _UU0393_ : Lctx, pt : Option[Ty], st : List[Option[Ty]], s : Sexpr) -> Result0[(Ahd, List[Option[Ty]]), Elab_error] {
  let learn = fn(t) {
    match pt {
      Some(q) => tmatch(q, t, st)
      None => st
    }
  }
  match (match pt {
    Some(q) => resolve(st, q)
    None => None
  }) {
    Some(t) => bind(cres(e, l, _UU0393_, s, t, rec(s)(l)(_UU0393_)(Mode::Chk(t))), fn(x) { Result0::Ok((Ahd::AH_Chk(t, x), st)) })
    None => match s {
      Sexpr::SVar(_, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SLit(_, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SApp(_, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SInfix(_, _, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SUnary(_, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SLet(_, _, _, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SIf(_, _, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::STup(_, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SProj(_, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SLam(q, lps, ret, a, body) => match pt {
        Some(t) => match t {
          Ty::TBase(_) => {
            let p = (repeat(None, length(lps)), None)
            let _UU03b5_exp = None
            match p {
              (pexps, rexp) => bind(params_ann_dec(e, q, lps, pexps), fn(x) {
                bind(eff_pick(e, a, _UU03b5_exp), fn(x0) {
                  let _UU0393__ = app(lam_ctx(lps, x), _UU0393_)
                  bind(match ret {
                    Some(s0) => {
                      let r0 = Some(s0)
                      bind(match r0 {
                        Some(t0) => bind(ety_dec(e, t0), fn(x1) { Result0::Ok(x1) })
                        None => match rexp {
                          Some(r) => Result0::Ok(r)
                          None => Result0::Err(Elab_error::EE_LambdaParam(q, String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))))))))
                        }
                      }, fn(x1) {
                        bind(cres(e, fun_env(x1, x0), _UU0393__, body, x1, rec(body)(fun_env(x1, x0))(_UU0393__)(Mode::Chk(x1))), fn(x2) {
                          Result0::Ok((Ahd::AH_Chk(Ty::TArrow(x, x1, x0), Expr::ELam(x, x1, x0, eblock(x1, x2))), learn(Ty::TArrow(x, x1, x0))))
                        })
                      })
                    }
                    None => {
                      let r0 = None
                      match rexp {
                        Some(_) => bind(match r0 {
                          Some(t0) => bind(ety_dec(e, t0), fn(x1) { Result0::Ok(x1) })
                          None => match rexp {
                            Some(r) => Result0::Ok(r)
                            None => Result0::Err(Elab_error::EE_LambdaParam(q, String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))))))))
                          }
                        }, fn(x1) {
                          bind(cres(e, fun_env(x1, x0), _UU0393__, body, x1, rec(body)(fun_env(x1, x0))(_UU0393__)(Mode::Chk(x1))), fn(x2) {
                            Result0::Ok((Ahd::AH_Chk(Ty::TArrow(x, x1, x0), Expr::ELam(x, x1, x0, eblock(x1, x2))), learn(Ty::TArrow(x, x1, x0))))
                          })
                        })
                        None => bind(rec(body)(Cenv::Mk_cenv(List::Nil, x0))(_UU0393__)(Mode::Syn), fn(x1) {
                          match x1 {
                            SigT::ExistT(r, s0) => Result0::Ok((Ahd::AH_Chk(Ty::TArrow(x, r, x0), Expr::ELam(x, r, x0, s0)), learn(Ty::TArrow(x, r, x0))))
                          }
                        })
                      }
                    }
                  }, fn(x1) {
                    match x1 {
                      (h, st_) => Result0::Ok((ahd_cast(e, l, _UU0393_, Sexpr::SLam(q, lps, ret, a, body), s, h), st_))
                    }
                  })
                })
              })
            }
          }
          Ty::TVar(_) => {
            let p = (repeat(None, length(lps)), None)
            let _UU03b5_exp = None
            match p {
              (pexps, rexp) => bind(params_ann_dec(e, q, lps, pexps), fn(x) {
                bind(eff_pick(e, a, _UU03b5_exp), fn(x0) {
                  let _UU0393__ = app(lam_ctx(lps, x), _UU0393_)
                  bind(match ret {
                    Some(s0) => {
                      let r0 = Some(s0)
                      bind(match r0 {
                        Some(t0) => bind(ety_dec(e, t0), fn(x1) { Result0::Ok(x1) })
                        None => match rexp {
                          Some(r) => Result0::Ok(r)
                          None => Result0::Err(Elab_error::EE_LambdaParam(q, String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))))))))
                        }
                      }, fn(x1) {
                        bind(cres(e, fun_env(x1, x0), _UU0393__, body, x1, rec(body)(fun_env(x1, x0))(_UU0393__)(Mode::Chk(x1))), fn(x2) {
                          Result0::Ok((Ahd::AH_Chk(Ty::TArrow(x, x1, x0), Expr::ELam(x, x1, x0, eblock(x1, x2))), learn(Ty::TArrow(x, x1, x0))))
                        })
                      })
                    }
                    None => {
                      let r0 = None
                      match rexp {
                        Some(_) => bind(match r0 {
                          Some(t0) => bind(ety_dec(e, t0), fn(x1) { Result0::Ok(x1) })
                          None => match rexp {
                            Some(r) => Result0::Ok(r)
                            None => Result0::Err(Elab_error::EE_LambdaParam(q, String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))))))))
                          }
                        }, fn(x1) {
                          bind(cres(e, fun_env(x1, x0), _UU0393__, body, x1, rec(body)(fun_env(x1, x0))(_UU0393__)(Mode::Chk(x1))), fn(x2) {
                            Result0::Ok((Ahd::AH_Chk(Ty::TArrow(x, x1, x0), Expr::ELam(x, x1, x0, eblock(x1, x2))), learn(Ty::TArrow(x, x1, x0))))
                          })
                        })
                        None => bind(rec(body)(Cenv::Mk_cenv(List::Nil, x0))(_UU0393__)(Mode::Syn), fn(x1) {
                          match x1 {
                            SigT::ExistT(r, s0) => Result0::Ok((Ahd::AH_Chk(Ty::TArrow(x, r, x0), Expr::ELam(x, r, x0, s0)), learn(Ty::TArrow(x, r, x0))))
                          }
                        })
                      }
                    }
                  }, fn(x1) {
                    match x1 {
                      (h, st_) => Result0::Ok((ahd_cast(e, l, _UU0393_, Sexpr::SLam(q, lps, ret, a, body), s, h), st_))
                    }
                  })
                })
              })
            }
          }
          Ty::TTuple(_) => {
            let p = (repeat(None, length(lps)), None)
            let _UU03b5_exp = None
            match p {
              (pexps, rexp) => bind(params_ann_dec(e, q, lps, pexps), fn(x) {
                bind(eff_pick(e, a, _UU03b5_exp), fn(x0) {
                  let _UU0393__ = app(lam_ctx(lps, x), _UU0393_)
                  bind(match ret {
                    Some(s0) => {
                      let r0 = Some(s0)
                      bind(match r0 {
                        Some(t0) => bind(ety_dec(e, t0), fn(x1) { Result0::Ok(x1) })
                        None => match rexp {
                          Some(r) => Result0::Ok(r)
                          None => Result0::Err(Elab_error::EE_LambdaParam(q, String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))))))))
                        }
                      }, fn(x1) {
                        bind(cres(e, fun_env(x1, x0), _UU0393__, body, x1, rec(body)(fun_env(x1, x0))(_UU0393__)(Mode::Chk(x1))), fn(x2) {
                          Result0::Ok((Ahd::AH_Chk(Ty::TArrow(x, x1, x0), Expr::ELam(x, x1, x0, eblock(x1, x2))), learn(Ty::TArrow(x, x1, x0))))
                        })
                      })
                    }
                    None => {
                      let r0 = None
                      match rexp {
                        Some(_) => bind(match r0 {
                          Some(t0) => bind(ety_dec(e, t0), fn(x1) { Result0::Ok(x1) })
                          None => match rexp {
                            Some(r) => Result0::Ok(r)
                            None => Result0::Err(Elab_error::EE_LambdaParam(q, String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))))))))
                          }
                        }, fn(x1) {
                          bind(cres(e, fun_env(x1, x0), _UU0393__, body, x1, rec(body)(fun_env(x1, x0))(_UU0393__)(Mode::Chk(x1))), fn(x2) {
                            Result0::Ok((Ahd::AH_Chk(Ty::TArrow(x, x1, x0), Expr::ELam(x, x1, x0, eblock(x1, x2))), learn(Ty::TArrow(x, x1, x0))))
                          })
                        })
                        None => bind(rec(body)(Cenv::Mk_cenv(List::Nil, x0))(_UU0393__)(Mode::Syn), fn(x1) {
                          match x1 {
                            SigT::ExistT(r, s0) => Result0::Ok((Ahd::AH_Chk(Ty::TArrow(x, r, x0), Expr::ELam(x, r, x0, s0)), learn(Ty::TArrow(x, r, x0))))
                          }
                        })
                      }
                    }
                  }, fn(x1) {
                    match x1 {
                      (h, st_) => Result0::Ok((ahd_cast(e, l, _UU0393_, Sexpr::SLam(q, lps, ret, a, body), s, h), st_))
                    }
                  })
                })
              })
            }
          }
          Ty::TArrow(pps, pr, p_UU03b5_) => {
            let p = (match eqb0(length(pps), length(lps)) {
              true => map(fn(x1) { resolve(st, x1) }, pps)
              false => repeat(None, length(lps))
            }, resolve(st, pr))
            let _UU03b5_exp = resolve(st, p_UU03b5_)
            match p {
              (pexps, rexp) => bind(params_ann_dec(e, q, lps, pexps), fn(x) {
                bind(eff_pick(e, a, _UU03b5_exp), fn(x0) {
                  let _UU0393__ = app(lam_ctx(lps, x), _UU0393_)
                  bind(match ret {
                    Some(s0) => {
                      let r0 = Some(s0)
                      bind(match r0 {
                        Some(t0) => bind(ety_dec(e, t0), fn(x1) { Result0::Ok(x1) })
                        None => match rexp {
                          Some(r) => Result0::Ok(r)
                          None => Result0::Err(Elab_error::EE_LambdaParam(q, String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))))))))
                        }
                      }, fn(x1) {
                        bind(cres(e, fun_env(x1, x0), _UU0393__, body, x1, rec(body)(fun_env(x1, x0))(_UU0393__)(Mode::Chk(x1))), fn(x2) {
                          Result0::Ok((Ahd::AH_Chk(Ty::TArrow(x, x1, x0), Expr::ELam(x, x1, x0, eblock(x1, x2))), learn(Ty::TArrow(x, x1, x0))))
                        })
                      })
                    }
                    None => {
                      let r0 = None
                      match rexp {
                        Some(_) => bind(match r0 {
                          Some(t0) => bind(ety_dec(e, t0), fn(x1) { Result0::Ok(x1) })
                          None => match rexp {
                            Some(r) => Result0::Ok(r)
                            None => Result0::Err(Elab_error::EE_LambdaParam(q, String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))))))))
                          }
                        }, fn(x1) {
                          bind(cres(e, fun_env(x1, x0), _UU0393__, body, x1, rec(body)(fun_env(x1, x0))(_UU0393__)(Mode::Chk(x1))), fn(x2) {
                            Result0::Ok((Ahd::AH_Chk(Ty::TArrow(x, x1, x0), Expr::ELam(x, x1, x0, eblock(x1, x2))), learn(Ty::TArrow(x, x1, x0))))
                          })
                        })
                        None => bind(rec(body)(Cenv::Mk_cenv(List::Nil, x0))(_UU0393__)(Mode::Syn), fn(x1) {
                          match x1 {
                            SigT::ExistT(r, s0) => Result0::Ok((Ahd::AH_Chk(Ty::TArrow(x, r, x0), Expr::ELam(x, r, x0, s0)), learn(Ty::TArrow(x, r, x0))))
                          }
                        })
                      }
                    }
                  }, fn(x1) {
                    match x1 {
                      (h, st_) => Result0::Ok((ahd_cast(e, l, _UU0393_, Sexpr::SLam(q, lps, ret, a, body), s, h), st_))
                    }
                  })
                })
              })
            }
          }
          _ => {
            let p = (repeat(None, length(lps)), None)
            let _UU03b5_exp = None
            match p {
              (pexps, rexp) => bind(params_ann_dec(e, q, lps, pexps), fn(x) {
                bind(eff_pick(e, a, _UU03b5_exp), fn(x0) {
                  let _UU0393__ = app(lam_ctx(lps, x), _UU0393_)
                  bind(match ret {
                    Some(s0) => {
                      let r0 = Some(s0)
                      bind(match r0 {
                        Some(t0) => bind(ety_dec(e, t0), fn(x1) { Result0::Ok(x1) })
                        None => match rexp {
                          Some(r) => Result0::Ok(r)
                          None => Result0::Err(Elab_error::EE_LambdaParam(q, String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))))))))
                        }
                      }, fn(x1) {
                        bind(cres(e, fun_env(x1, x0), _UU0393__, body, x1, rec(body)(fun_env(x1, x0))(_UU0393__)(Mode::Chk(x1))), fn(x2) {
                          Result0::Ok((Ahd::AH_Chk(Ty::TArrow(x, x1, x0), Expr::ELam(x, x1, x0, eblock(x1, x2))), learn(Ty::TArrow(x, x1, x0))))
                        })
                      })
                    }
                    None => {
                      let r0 = None
                      match rexp {
                        Some(_) => bind(match r0 {
                          Some(t0) => bind(ety_dec(e, t0), fn(x1) { Result0::Ok(x1) })
                          None => match rexp {
                            Some(r) => Result0::Ok(r)
                            None => Result0::Err(Elab_error::EE_LambdaParam(q, String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))))))))
                          }
                        }, fn(x1) {
                          bind(cres(e, fun_env(x1, x0), _UU0393__, body, x1, rec(body)(fun_env(x1, x0))(_UU0393__)(Mode::Chk(x1))), fn(x2) {
                            Result0::Ok((Ahd::AH_Chk(Ty::TArrow(x, x1, x0), Expr::ELam(x, x1, x0, eblock(x1, x2))), learn(Ty::TArrow(x, x1, x0))))
                          })
                        })
                        None => bind(rec(body)(Cenv::Mk_cenv(List::Nil, x0))(_UU0393__)(Mode::Syn), fn(x1) {
                          match x1 {
                            SigT::ExistT(r, s0) => Result0::Ok((Ahd::AH_Chk(Ty::TArrow(x, r, x0), Expr::ELam(x, r, x0, s0)), learn(Ty::TArrow(x, r, x0))))
                          }
                        })
                      }
                    }
                  }, fn(x1) {
                    match x1 {
                      (h, st_) => Result0::Ok((ahd_cast(e, l, _UU0393_, Sexpr::SLam(q, lps, ret, a, body), s, h), st_))
                    }
                  })
                })
              })
            }
          }
        }
        None => {
          let p = (repeat(None, length(lps)), None)
          let _UU03b5_exp = None
          match p {
            (pexps, rexp) => bind(params_ann_dec(e, q, lps, pexps), fn(x) {
              bind(eff_pick(e, a, _UU03b5_exp), fn(x0) {
                let _UU0393__ = app(lam_ctx(lps, x), _UU0393_)
                bind(match ret {
                  Some(s0) => {
                    let r0 = Some(s0)
                    bind(match r0 {
                      Some(t) => bind(ety_dec(e, t), fn(x1) { Result0::Ok(x1) })
                      None => match rexp {
                        Some(r) => Result0::Ok(r)
                        None => Result0::Err(Elab_error::EE_LambdaParam(q, String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))))))))
                      }
                    }, fn(x1) {
                      bind(cres(e, fun_env(x1, x0), _UU0393__, body, x1, rec(body)(fun_env(x1, x0))(_UU0393__)(Mode::Chk(x1))), fn(x2) {
                        Result0::Ok((Ahd::AH_Chk(Ty::TArrow(x, x1, x0), Expr::ELam(x, x1, x0, eblock(x1, x2))), learn(Ty::TArrow(x, x1, x0))))
                      })
                    })
                  }
                  None => {
                    let r0 = None
                    match rexp {
                      Some(_) => bind(match r0 {
                        Some(t) => bind(ety_dec(e, t), fn(x1) { Result0::Ok(x1) })
                        None => match rexp {
                          Some(r) => Result0::Ok(r)
                          None => Result0::Err(Elab_error::EE_LambdaParam(q, String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))))))))
                        }
                      }, fn(x1) {
                        bind(cres(e, fun_env(x1, x0), _UU0393__, body, x1, rec(body)(fun_env(x1, x0))(_UU0393__)(Mode::Chk(x1))), fn(x2) {
                          Result0::Ok((Ahd::AH_Chk(Ty::TArrow(x, x1, x0), Expr::ELam(x, x1, x0, eblock(x1, x2))), learn(Ty::TArrow(x, x1, x0))))
                        })
                      })
                      None => bind(rec(body)(Cenv::Mk_cenv(List::Nil, x0))(_UU0393__)(Mode::Syn), fn(x1) {
                        match x1 {
                          SigT::ExistT(r, s0) => Result0::Ok((Ahd::AH_Chk(Ty::TArrow(x, r, x0), Expr::ELam(x, r, x0, s0)), learn(Ty::TArrow(x, r, x0))))
                        }
                      })
                    }
                  }
                }, fn(x1) {
                  match x1 {
                    (h, st_) => Result0::Ok((ahd_cast(e, l, _UU0393_, Sexpr::SLam(q, lps, ret, a, body), s, h), st_))
                  }
                })
              })
            })
          }
        }
      }
      Sexpr::SAnnot(_, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SConstr(_, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SRecord(_, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SField(_, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SMatch(_, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SLetMut(_, _, _, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SAssign(_, _, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SArray(_, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SIndex(_, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SIndexSet(_, _, _, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SFieldSet(_, _, _, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SMethod(_, _, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SQual(_, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SWhile(_, _, _, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SFor(_, _, _, _, _, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SBlock(_, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SBreak(_, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SContinue(_, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SReturn(_, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SForIn(_, _, _, _, _, _, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SRaise(_, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::STry(_, _, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::STryBang(_, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SDefer(_, _, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
      Sexpr::SAs(_, _, _) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(t, s0) => Result0::Ok((Ahd::AH_Syn(t, s0), learn(t)))
        }
      })
    }
  }
}

pub fn pass2(e : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], l : Cenv, _UU0393_ : Lctx, args : List[Sexpr], rs : List[SigT[Sexpr, Ahd]], x : List[Ty], x0 : List[Option[Ty]]) -> Result0[(Ares, List[Option[Ty]]), Elab_error] {
  match args {
    List::Nil => Result0::Ok((List::Nil, x0))
    List::Cons(s, args_) => match rs {
      List::Nil => abort("absurd case")
      List::Cons(x1, rs_) => match split_hd(x) {
        (pt, ps_) => match x1 {
          SigT::ExistT(s0, h) => match h {
            Ahd::AH_Chk(_, _) => bind(pass2(e, rec, l, _UU0393_, args_, rs_, ps_, x0), fn(x2) {
              match x2 {
                (a, st2) => Result0::Ok((List::Cons(SigT::ExistT(s0, h), a), st2))
              }
            })
            Ahd::AH_Syn(_, _) => bind(pass2(e, rec, l, _UU0393_, args_, rs_, ps_, x0), fn(x2) {
              match x2 {
                (a, st2) => Result0::Ok((List::Cons(SigT::ExistT(s0, h), a), st2))
              }
            })
            Ahd::AH_Post => bind(late_lam(e, rec, l, _UU0393_, pt, x0, s), fn(x2) {
              match x2 {
                (h0, st1) => bind(pass2(e, rec, l, _UU0393_, args_, rs_, ps_, st1), fn(x3) {
                  match x3 {
                    (a, st2) => Result0::Ok((List::Cons(SigT::ExistT(s, h0), a), st2))
                  }
                })
              }
            })
          }
        }
      }
    }
  }
}

pub fn finish(e : Senv, p : Pos, l : Cenv, _UU0393_ : Lctx, args : List[Sexpr], rs : List[SigT[Sexpr, Ahd]], _UU03c4_s : List[Ty]) -> Result0[List[Expr], Elab_error] {
  match args {
    List::Nil => match _UU03c4_s {
      List::Nil => Result0::Ok(List::Nil)
      List::Cons(_, _) => Result0::Err(Elab_error::EE_Type(p, Type_error::E_ArgArity(length(_UU03c4_s), Nat::O)))
    }
    List::Cons(_, args_) => match rs {
      List::Nil => abort("absurd case")
      List::Cons(x, rs_) => match _UU03c4_s {
        List::Nil => Result0::Err(Elab_error::EE_Type(p, Type_error::E_ArgArity(Nat::O, length(args))))
        List::Cons(_UU03c4_, _UU03c4_s_) => bind(match x {
          SigT::ExistT(_, y) => match y {
            Ahd::AH_Chk(t, e0) => match ty_eq_dec(t)(_UU03c4_) {
              true => Result0::Ok(e0)
              false => Result0::Err(Elab_error::EE_Annot(p, _UU03c4_, t))
            }
            Ahd::AH_Syn(t, e0) => bind(coerce(e, p, _UU0393_, e0, t, _UU03c4_), fn(x0) { Result0::Ok(x0) })
            Ahd::AH_Post => Result0::Err(Elab_error::EE_CannotInfer(p, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))))))))))
          }
        }, fn(x0) {
          bind(finish(e, p, l, _UU0393_, args_, rs_, _UU03c4_s_), fn(x1) { Result0::Ok(List::Cons(x0, x1)) })
        })
      }
    }
  }
}

pub fn gargs(e : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], p : Pos, q : Pos, l : Cenv, _UU0393_ : Lctx, args : List[Sexpr], ps : List[Ty], n : Nat, st0 : List[Option[Ty]], g : Ident) -> Result0[SigT[List[Ty], List[Expr]], Elab_error] {
  bind(bcheck(eqb0(length(args), length(ps)), Elab_error::EE_Type(q, Type_error::E_ArgArity(length(ps), length(args)))), fn(_) {
    bind(pass1(e, rec, l, _UU0393_, args, ps, st0), fn(x) {
      match x {
        (a, st1) => bind(pass2(e, rec, l, _UU0393_, args, a, ps, st1), fn(x0) {
          match x0 {
            (a0, st2) => bind(targs(q, g, n, st2), fn(x1) {
              bind(finish(e, p, l, _UU0393_, args, a0, map({ let a1 = fn(x2) { inst(x1, x2) }; fn(x2) { tsubst(a1, x2) } }, ps)), fn(x2) { Result0::Ok(SigT::ExistT(x1, x2)) })
            })
          }
        })
      }
    })
  })
}

pub fn lit_err(p : Pos, l : Slit) -> Elab_error {
  match l {
    Slit::SLInt(ko, z) => Elab_error::EE_IntRange(p, match ko {
      Some(k) => k
      None => Int_kind::I32
    }, z)
    _ => Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))))))
  }
}

pub fn lit_syn(_ : Senv, p : Pos, _ : Cenv, _ : Lctx, l : Slit) -> Result0[Sout, Elab_error] {
  match lit_of(l) {
    Some(l_) => Result0::Ok(SigT::ExistT(Ty::TBase(lit_ty(l_)), Expr::ELit(l_)))
    None => Result0::Err(lit_err(p, l))
  }
}

pub fn lit_m(e : Senv, p : Pos, l : Cenv, _UU0393_ : Lctx, l0 : Slit, m : Mode) -> Result0[Out, Elab_error] {
  match m {
    Mode::Syn => lit_syn(e, p, l, _UU0393_, l0)
    Mode::Chk(_UU03c4_) => match l0 {
      Slit::SLInt(k0, z) => match k0 {
        Some(i) => {
          let l1 = Slit::SLInt(Some(i), z)
          fin(e, p, l, _UU0393_, Sexpr::SLit(p, l1), Mode::Chk(_UU03c4_), lit_syn(e, p, l, _UU0393_, l1))
        }
        None => {
          let l1 = Slit::SLInt(None, z)
          match _UU03c4_ {
            Ty::TBase(b) => match b {
              Base_ty::BInt(k) => bind(bcheck(int_in_range(k, z), Elab_error::EE_IntRange(p, k, z)), fn(_) {
                okc(e, l, _UU0393_, Sexpr::SLit(p, Slit::SLInt(None, z)), Ty::TBase(Base_ty::BInt(k)), Expr::ELit(Lit::LInt(k, z)))
              })
              x => fin(e, p, l, _UU0393_, Sexpr::SLit(p, l1), Mode::Chk(Ty::TBase(x)), lit_syn(e, p, l, _UU0393_, l1))
            }
            x => fin(e, p, l, _UU0393_, Sexpr::SLit(p, l1), Mode::Chk(x), lit_syn(e, p, l, _UU0393_, l1))
          }
        }
      }
      x => fin(e, p, l, _UU0393_, Sexpr::SLit(p, x), Mode::Chk(_UU03c4_), lit_syn(e, p, l, _UU0393_, x))
    }
  }
}

pub fn var_syn(e : Senv, p : Pos, _ : Cenv, _UU0393_ : Lctx, x : Ident, h : Option[Ty]) -> Result0[Sout, Elab_error] {
  match lookup_local(x, _UU0393_) {
    Some(i) => bind(of_option(nth_error(ctx_of(_UU0393_), i), Elab_error::EE_Unbound(p, x)), fn(x0) {
      match x0 {
        Ty::TRef(u) => Result0::Ok(SigT::ExistT(u, Expr::EMem(Mem_op::MGet(u), List::Cons(Expr::EVar(i), List::Nil))))
        x1 => Result0::Ok(SigT::ExistT(x1, Expr::EVar(i)))
      }
    })
    None => bind(of_option(lookup_fn(match e {
      Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
    }, x), Elab_error::EE_Unbound(p, x)), fn(x0) {
      bind(no_bounds(e, p, x), fn(_) {
        let n = match x0 {
          Fdef::Mk_fdef(_, fd_tparams, _, _, _, _) => fd_tparams
        }
        bind(fn_targs(p, x, x0, match h {
          Some(t) => tmatch(Ty::TArrow(match x0 {
            Fdef::Mk_fdef(_, _, fd_params, _, _, _) => fd_params
          }, match x0 {
            Fdef::Mk_fdef(_, _, _, fd_ret, _, _) => fd_ret
          }, match x0 {
            Fdef::Mk_fdef(_, _, _, _, fd_eff, _) => fd_eff
          }), t, repeat(None, n))
          None => repeat(None, n)
        }), fn(x1) { Result0::Ok(SigT::ExistT(fn_inst(x0, x1), Expr::EGlobal(x, x1))) })
      })
    })
  }
}

pub fn tq_dec(_ : Pos, tq : Option[Ident], t : Ident, err : Elab_error) -> Result0[Unit, Elab_error] {
  match tq {
    Some(t_) => match eq_dec0(eqDec_ident, t_, t) {
      true => Result0::Ok(())
      false => Result0::Err(err)
    }
    None => Result0::Ok(())
  }
}

pub fn ctor_pick_dec(e : Senv, p : Pos, tq : Option[Ident], c : Ident) -> Result0[Ident, Elab_error] {
  match tq {
    Some(t) => Result0::Ok(t)
    None => match map(fn(t) {
      match t {
        Tdef::Mk_tdef(td_name, _, _, _) => td_name
      }
    }, filter(fn(td) {
      match negb(is_rec(e, match td {
        Tdef::Mk_tdef(td_name, _, _, _) => td_name
      })) {
        true => ctor_in(c, td)
        false => false
      }
    }, match (match e {
      Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
    }) {
      Genv::Mk_genv(ge_types, _) => ge_types
    })) {
      List::Nil => Result0::Err(Elab_error::EE_UnknownCtor(p, c))
      List::Cons(t, l) => match l {
        List::Nil => Result0::Ok(t)
        List::Cons(_, _) => Result0::Err(Elab_error::EE_AmbiguousCtor(p, c))
      }
    }
  }
}

pub fn err_owner_dec(e : Senv, p : Pos, tq : Option[Ident], c : Ident) -> Result0[Ident, Elab_error] {
  match tq {
    Some(t) => Result0::Ok(t)
    None => match map(fn(t) {
      match t {
        Tdef::Mk_tdef(td_name, _, _, _) => td_name
      }
    }, filter(fn(td) {
      match (match td {
        Tdef::Mk_tdef(_, _, _, td_err) => td_err
      }) {
        true => ctor_in(c, td)
        false => false
      }
    }, match (match e {
      Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
    }) {
      Genv::Mk_genv(ge_types, _) => ge_types
    })) {
      List::Nil => Result0::Err(Elab_error::EE_UnknownCtor(p, c))
      List::Cons(t, l) => match l {
        List::Nil => Result0::Ok(t)
        List::Cons(_, _) => Result0::Err(Elab_error::EE_AmbiguousCtor(p, c))
      }
    }
  }
}

pub fn single_ctor(p : Pos, td : Tdef, t : Ty) -> Result0[Cdef, Elab_error] {
  match (match td {
    Tdef::Mk_tdef(_, _, td_ctors, _) => td_ctors
  }) {
    List::Nil => Result0::Err(Elab_error::EE_NotRecord(p, t))
    List::Cons(cd, l) => match l {
      List::Nil => Result0::Ok(cd)
      List::Cons(_, _) => Result0::Err(Elab_error::EE_NotRecord(p, t))
    }
  }
}

pub fn fpat(_ : Senv, rec : (Spat) -> (Ty) -> Result0[SigT[Pat, Lctx], Elab_error], sp : Spat, _UU03c4_ : Ty) -> Result0[SigT[Pat, Lctx], Elab_error] {
  match _UU03c4_ {
    Ty::TBase(b) => {
      let t = Ty::TBase(b)
      bind(rec(sp)(t), fn(x) {
        match x {
          SigT::ExistT(q, s) => Result0::Ok(SigT::ExistT(q, s))
        }
      })
    }
    Ty::TVar(i) => {
      let t = Ty::TVar(i)
      bind(rec(sp)(t), fn(x) {
        match x {
          SigT::ExistT(q, s) => Result0::Ok(SigT::ExistT(q, s))
        }
      })
    }
    Ty::TTuple(ts) => {
      let t = Ty::TTuple(ts)
      bind(rec(sp)(t), fn(x) {
        match x {
          SigT::ExistT(q, s) => Result0::Ok(SigT::ExistT(q, s))
        }
      })
    }
    Ty::TArrow(ps, r, _UU03b5_) => {
      let t = Ty::TArrow(ps, r, _UU03b5_)
      bind(rec(sp)(t), fn(x) {
        match x {
          SigT::ExistT(q, s) => Result0::Ok(SigT::ExistT(q, s))
        }
      })
    }
    Ty::TData(t, ts) => {
      let t0 = Ty::TData(t, ts)
      bind(rec(sp)(t0), fn(x) {
        match x {
          SigT::ExistT(q, s) => Result0::Ok(SigT::ExistT(q, s))
        }
      })
    }
    Ty::TRef(u) => bind(rec(sp)(u), fn(x) {
      match x {
        SigT::ExistT(q, s) => Result0::Ok(SigT::ExistT(Pat::PRef(q), s))
      }
    })
    Ty::TArray(k, t0) => {
      let t = Ty::TArray(k, t0)
      bind(rec(sp)(t), fn(x) {
        match x {
          SigT::ExistT(q, s) => Result0::Ok(SigT::ExistT(q, s))
        }
      })
    }
    Ty::TError => {
      let t = Ty::TError
      bind(rec(sp)(t), fn(x) {
        match x {
          SigT::ExistT(q, s) => Result0::Ok(SigT::ExistT(q, s))
        }
      })
    }
  }
}

pub fn fpats_prefix(e : Senv, rec : (Spat) -> (Ty) -> Result0[SigT[Pat, Lctx], Elab_error], err : Elab_error, sps : List[Spat], fs : List[Ty]) -> Result0[SigT[List[Pat], SigT[Lctx, SigT[List[Ty], List[Ty]]]], Elab_error] {
  match sps {
    List::Nil => Result0::Ok(SigT::ExistT(List::Nil, SigT::ExistT(List::Nil, SigT::ExistT(List::Nil, fs))))
    List::Cons(sp, sps_) => match fs {
      List::Nil => Result0::Err(err)
      List::Cons(_UU03c4_, fs_) => bind(fpat(e, rec, sp, _UU03c4_), fn(x) {
        match x {
          SigT::ExistT(q, s) => bind(fpats_prefix(e, rec, err, sps_, fs_), fn(x0) {
            match x0 {
              SigT::ExistT(qs, s0) => match s0 {
                SigT::ExistT(_UU0394_2, s1) => match s1 {
                  SigT::ExistT(fs1, s2) => Result0::Ok(SigT::ExistT(List::Cons(q, qs), SigT::ExistT(app(s, _UU0394_2), SigT::ExistT(List::Cons(_UU03c4_, fs1), s2))))
                }
              }
            }
          })
        }
      })
    }
  }
}

pub fn named_pats(e : Senv, rec : (Spat) -> (Ty) -> Result0[SigT[Pat, Lctx], Elab_error], p : Pos, names : List[Ident], fs : List[Ty], fps : List[(Ident, Spat)]) -> Result0[List[((Nat, Pat), Lctx)], Elab_error] {
  match fps {
    List::Nil => Result0::Ok(List::Nil)
    List::Cons(p0, fps_) => match p0 {
      (f, sp) => bind(of_option(index_of(f, names), Elab_error::EE_UnknownField(p, f)), fn(x) {
        bind(of_option(nth_error(fs, x), Elab_error::EE_UnknownField(p, f)), fn(x0) {
          bind(fpat(e, rec, sp, x0), fn(x1) {
            match x1 {
              SigT::ExistT(q, s) => bind(named_pats(e, rec, p, names, fs, fps_), fn(x2) { Result0::Ok(List::Cons(((x, q), s), x2)) })
            }
          })
        })
      })
    }
  }
}

pub fn open_ok(p : Pos, _UU03c4_ : Ty, op : Bool, fs2 : List[Ty]) -> Result0[Unit, Elab_error] {
  match op {
    true => Result0::Ok(())
    false => match fs2 {
      List::Nil => Result0::Ok(())
      List::Cons(_, _) => Result0::Err(Elab_error::EE_PatType(p, _UU03c4_))
    }
  }
}

pub fn missing_field(names : List[Ident], given : List[((Nat, Pat), Lctx)]) -> Ident {
  match find(fn(f) {
    match index_of(f, names) {
      Some(j) => negb(existsb(fn(x) { eqb0(fst(fst(x)), j) }, given))
      None => false
    }
  }, names) {
    Some(f) => f
    None => String0::EmptyString
  }
}

pub fn epat(e : Senv, sp : Spat, _UU03c4_ : Ty) -> Result0[SigT[Pat, Lctx], Elab_error] {
  match sp {
    Spat::SPWild(_) => Result0::Ok(SigT::ExistT(Pat::PWild, List::Nil))
    Spat::SPVar(_, x) => Result0::Ok(SigT::ExistT(Pat::PVar, List::Cons((Some(x), _UU03c4_), List::Nil)))
    Spat::SPLit(p, l) => match elab_lit(p, Some(_UU03c4_), l) {
      Result0::Ok(l_) => match ty_eq_dec(Ty::TBase(lit_ty(l_)))(_UU03c4_) {
        true => Result0::Ok(SigT::ExistT(Pat::PLit(l_), List::Nil))
        false => Result0::Err(Elab_error::EE_PatType(p, _UU03c4_))
      }
      Result0::Err(err) => Result0::Err(err)
    }
    Spat::SPTuple(p, sps) => match _UU03c4_ {
      Ty::TTuple(_UU03c4_s) => bind(fpats_prefix(e, fn(x1) { fn(x2) { epat(e, x1, x2) } }, Elab_error::EE_PatType(p, Ty::TTuple(_UU03c4_s)), sps, _UU03c4_s), fn(x) {
        match x {
          SigT::ExistT(qs, s) => match s {
            SigT::ExistT(_UU0394_, s0) => match s0 {
              SigT::ExistT(_, s1) => match s1 {
                List::Nil => Result0::Ok(SigT::ExistT(Pat::PTuple(qs), _UU0394_))
                List::Cons(_, _) => Result0::Err(Elab_error::EE_PatType(p, Ty::TTuple(_UU03c4_s)))
              }
            }
          }
        }
      })
      _ => Result0::Err(Elab_error::EE_PatType(p, _UU03c4_))
    }
    Spat::SPConstr(p, tq, c, sps, op) => match _UU03c4_ {
      Ty::TData(t, ts) => bind(tq_dec(p, tq, t, Elab_error::EE_PatType(p, Ty::TData(t, ts))), fn(_) {
        bind(of_option(lookup_ty(match e {
          Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
        }, t), Elab_error::EE_UnknownType(p, t)), fn(x) {
          bind(of_option(lookup_ctor(x, c), Elab_error::EE_UnknownCtor(p, c)), fn(x0) {
            bind(fpats_prefix(e, fn(x1) { fn(x2) { epat(e, x1, x2) } }, Elab_error::EE_PatType(p, Ty::TData(t, ts)), sps, map({ let a1 = fn(x1) { inst(ts, x1) }; fn(x1) { tsubst(a1, x1) } }, match x0 {
              Cdef::Mk_cdef(_, cd_fields) => cd_fields
            })), fn(x1) {
              match x1 {
                SigT::ExistT(qs, s) => match s {
                  SigT::ExistT(_UU0394_, s0) => match s0 {
                    SigT::ExistT(_, s1) => bind(open_ok(p, Ty::TData(t, ts), op, s1), fn(_) {
                      Result0::Ok(SigT::ExistT(Pat::PConstr(c, app(qs, map(fn(_) { Pat::PWild }, s1))), _UU0394_))
                    })
                  }
                }
              }
            })
          })
        })
      })
      Ty::TError => bind(err_owner_dec(e, p, tq, c), fn(x) {
        bind(of_option(lookup_ty(match e {
          Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
        }, x), Elab_error::EE_UnknownType(p, x)), fn(x0) {
          bind(of_option(lookup_ctor(x0, c), Elab_error::EE_UnknownCtor(p, c)), fn(x1) {
            bind(fpats_prefix(e, fn(x3) { fn(x2) { epat(e, x3, x2) } }, Elab_error::EE_PatType(p, Ty::TError), sps, map({ let a1 = fn(x2) { inst(List::Nil, x2) }; fn(x2) { tsubst(a1, x2) } }, match x1 {
              Cdef::Mk_cdef(_, cd_fields) => cd_fields
            })), fn(x2) {
              match x2 {
                SigT::ExistT(qs, s) => match s {
                  SigT::ExistT(_UU0394_, s0) => match s0 {
                    SigT::ExistT(_, s1) => bind(open_ok(p, Ty::TError, op, s1), fn(_) {
                      Result0::Ok(SigT::ExistT(Pat::PUp(x, Pat::PConstr(c, app(qs, map(fn(_) { Pat::PWild }, s1)))), _UU0394_))
                    })
                  }
                }
              }
            })
          })
        })
      })
      _ => Result0::Err(Elab_error::EE_PatType(p, _UU03c4_))
    }
    Spat::SPRecord(p, fps, op) => match _UU03c4_ {
      Ty::TData(t, ts) => bind(of_option(assoc(t, match e {
        Senv::Mk_senv(_, _, se_sinfo, _, _) => se_sinfo
      }), Elab_error::EE_NotRecord(p, Ty::TData(t, ts))), fn(x) {
        bind(of_option(lookup_ty(match e {
          Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
        }, t), Elab_error::EE_UnknownType(p, t)), fn(x0) {
          bind(single_ctor(p, x0, Ty::TData(t, ts)), fn(x1) {
            bind(named_pats(e, fn(x3) { fn(x2) { epat(e, x3, x2) } }, p, x, map({ let a1 = fn(x2) { inst(ts, x2) }; fn(x2) { tsubst(a1, x2) } }, match x1 {
              Cdef::Mk_cdef(_, cd_fields) => cd_fields
            }), fps), fn(x2) {
              match assemble(op, x2, Nat::O, map({ let a1 = fn(x3) { inst(ts, x3) }; fn(x3) { tsubst(a1, x3) } }, match x1 {
                Cdef::Mk_cdef(_, cd_fields) => cd_fields
              })) {
                Some(p0) => match p0 {
                  (qs, _UU0394_) => Result0::Ok(SigT::ExistT(Pat::PConstr(match x1 {
                    Cdef::Mk_cdef(cd_name, _) => cd_name
                  }, qs), _UU0394_))
                }
                None => Result0::Err(Elab_error::EE_MissingField(p, missing_field(x, x2)))
              }
            })
          })
        })
      })
      _ => Result0::Err(Elab_error::EE_NotRecord(p, _UU03c4_))
    }
    Spat::SPAnnot(p, sp0, t) => bind(ety_dec(e, t), fn(x) {
      match ty_eq_dec(x)(_UU03c4_) {
        true => bind(epat(e, sp0, _UU03c4_), fn(x0) {
          match x0 {
            SigT::ExistT(q, s) => Result0::Ok(SigT::ExistT(q, s))
          }
        })
        false => Result0::Err(Elab_error::EE_Annot(p, x, _UU03c4_))
      }
    })
  }
}

pub fn arm_live(c : (Spat, Sexpr)) -> Bool {
  negb(diverges(snd(c)))
}

pub fn live_arm(e : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], l : Cenv, _UU0393_ : Lctx, _UU03c4_s : Ty, cs : List[(Spat, Sexpr)]) -> Result0[Sumor[Ty], Elab_error] {
  match cs {
    List::Nil => Result0::Ok(Sumor::Inright)
    List::Cons(p, cs_) => match p {
      (sp, b) => match arm_live((sp, b)) {
        true => bind(epat(e, sp, _UU03c4_s), fn(x) {
          match x {
            SigT::ExistT(_, s) => bind(rec(b)(l)(app(s, _UU0393_))(Mode::Syn), fn(x0) {
              match x0 {
                SigT::ExistT(_UU03c4_, _) => Result0::Ok(Sumor::Inleft(_UU03c4_))
              }
            })
          }
        })
        false => bind(live_arm(e, rec, l, _UU0393_, _UU03c4_s, cs_), fn(r) {
          match r {
            Sumor::Inleft(s) => Result0::Ok(Sumor::Inleft(s))
            Sumor::Inright => Result0::Ok(Sumor::Inright)
          }
        })
      }
    }
  }
}

pub fn pick_syn(e : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], p : Pos, l : Cenv, _UU0393_ : Lctx, _UU03c4_s : Ty, cs : List[(Spat, Sexpr)]) -> Result0[Ty, Elab_error] {
  bind(live_arm(e, rec, l, _UU0393_, _UU03c4_s, cs), fn(r) {
    match r {
      Sumor::Inleft(s) => Result0::Ok(s)
      Sumor::Inright => match cs {
        List::Nil => Result0::Err(Elab_error::EE_EmptyMatch(p))
        List::Cons(p0, _) => match p0 {
          (sp, b) => bind(epat(e, sp, _UU03c4_s), fn(x) {
            match x {
              SigT::ExistT(_, s) => bind(rec(b)(l)(app(s, _UU0393_))(Mode::Syn), fn(x0) {
                match x0 {
                  SigT::ExistT(_UU03c4_, _) => Result0::Ok(_UU03c4_)
                }
              })
            }
          })
        }
      }
    }
  })
}

pub fn arms_list(e : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], l : Cenv, _UU0393_ : Lctx, _UU03c4_s : Ty, _UU03c4_ : Ty, cs : List[(Spat, Sexpr)]) -> Result0[List[(Pat, Expr)], Elab_error] {
  match cs {
    List::Nil => Result0::Ok(List::Nil)
    List::Cons(p, cs_) => match p {
      (sp, b) => bind(epat(e, sp, _UU03c4_s), fn(x) {
        match x {
          SigT::ExistT(q, s) => bind(cres(e, l, app(s, _UU0393_), b, _UU03c4_, rec(b)(l)(app(s, _UU0393_))(Mode::Chk(_UU03c4_))), fn(x0) {
            bind(arms_list(e, rec, l, _UU0393_, _UU03c4_s, _UU03c4_, cs_), fn(x1) { Result0::Ok(List::Cons((q, x0), x1)) })
          })
        }
      })
    }
  }
}

pub fn nil_fields(p : Pos, c : Ident, cd : Cdef) -> Result0[Unit, Elab_error] {
  match (match cd {
    Cdef::Mk_cdef(_, cd_fields) => cd_fields
  }) {
    List::Nil => Result0::Ok(())
    List::Cons(t, l0) => Result0::Err(Elab_error::EE_CtorArity(p, c, length(List::Cons(t, l0)), Nat::O))
  }
}

pub fn rec_pick_dec(e : Senv, p : Pos, tq : Option[Ident], written : List[Ident]) -> Result0[Ident, Elab_error] {
  match tq {
    Some(t) => Result0::Ok(t)
    None => match map(fn(x1) { fst(x1) }, filter(fn(tf) { same_fields(snd(tf), written) }, match e {
      Senv::Mk_senv(_, _, se_sinfo, _, _) => se_sinfo
    })) {
      List::Nil => Result0::Err(Elab_error::EE_NotRecord(p, Ty::TBase(Base_ty::BUnit)))
      List::Cons(t, l) => match l {
        List::Nil => Result0::Ok(t)
        List::Cons(_, _) => Result0::Err(Elab_error::EE_NotRecord(p, Ty::TBase(Base_ty::BUnit)))
      }
    }
  }
}

pub fn rfields_dec(e : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], p : Pos, l : Cenv, _UU0393_ : Lctx, names : List[Ident], fs : List[Ty], fes : List[(Ident, Sexpr)]) -> Result0[SigT[List[Expr], List[Nat]], Elab_error] {
  match fes {
    List::Nil => Result0::Ok(SigT::ExistT(List::Nil, List::Nil))
    List::Cons(p0, fes_) => match p0 {
      (f, fe) => bind(of_option(index_of(f, names), Elab_error::EE_UnknownField(p, f)), fn(x) {
        bind(of_option(nth_error(fs, x), Elab_error::EE_UnknownField(p, f)), fn(x0) {
          match x0 {
            Ty::TBase(b) => {
              let t = Ty::TBase(b)
              bind(cres(e, l, _UU0393_, fe, t, rec(fe)(l)(_UU0393_)(Mode::Chk(t))), fn(x1) {
                bind(rfields_dec(e, rec, p, l, _UU0393_, names, fs, fes_), fn(x2) {
                  match x2 {
                    SigT::ExistT(es, s) => Result0::Ok(SigT::ExistT(List::Cons(x1, es), List::Cons(x, s)))
                  }
                })
              })
            }
            Ty::TVar(i0) => {
              let t = Ty::TVar(i0)
              bind(cres(e, l, _UU0393_, fe, t, rec(fe)(l)(_UU0393_)(Mode::Chk(t))), fn(x1) {
                bind(rfields_dec(e, rec, p, l, _UU0393_, names, fs, fes_), fn(x2) {
                  match x2 {
                    SigT::ExistT(es, s) => Result0::Ok(SigT::ExistT(List::Cons(x1, es), List::Cons(x, s)))
                  }
                })
              })
            }
            Ty::TTuple(ts) => {
              let t = Ty::TTuple(ts)
              bind(cres(e, l, _UU0393_, fe, t, rec(fe)(l)(_UU0393_)(Mode::Chk(t))), fn(x1) {
                bind(rfields_dec(e, rec, p, l, _UU0393_, names, fs, fes_), fn(x2) {
                  match x2 {
                    SigT::ExistT(es, s) => Result0::Ok(SigT::ExistT(List::Cons(x1, es), List::Cons(x, s)))
                  }
                })
              })
            }
            Ty::TArrow(ps, r, _UU03b5_) => {
              let t = Ty::TArrow(ps, r, _UU03b5_)
              bind(cres(e, l, _UU0393_, fe, t, rec(fe)(l)(_UU0393_)(Mode::Chk(t))), fn(x1) {
                bind(rfields_dec(e, rec, p, l, _UU0393_, names, fs, fes_), fn(x2) {
                  match x2 {
                    SigT::ExistT(es, s) => Result0::Ok(SigT::ExistT(List::Cons(x1, es), List::Cons(x, s)))
                  }
                })
              })
            }
            Ty::TData(t, ts) => {
              let t0 = Ty::TData(t, ts)
              bind(cres(e, l, _UU0393_, fe, t0, rec(fe)(l)(_UU0393_)(Mode::Chk(t0))), fn(x1) {
                bind(rfields_dec(e, rec, p, l, _UU0393_, names, fs, fes_), fn(x2) {
                  match x2 {
                    SigT::ExistT(es, s) => Result0::Ok(SigT::ExistT(List::Cons(x1, es), List::Cons(x, s)))
                  }
                })
              })
            }
            Ty::TRef(u) => bind(cres(e, l, _UU0393_, fe, u, rec(fe)(l)(_UU0393_)(Mode::Chk(u))), fn(x1) {
              bind(rfields_dec(e, rec, p, l, _UU0393_, names, fs, fes_), fn(x2) {
                match x2 {
                  SigT::ExistT(es, s) => Result0::Ok(SigT::ExistT(List::Cons(Expr::EMem(Mem_op::MRef(u), List::Cons(x1, List::Nil)), es), List::Cons(x, s)))
                }
              })
            })
            Ty::TArray(k, t0) => {
              let t = Ty::TArray(k, t0)
              bind(cres(e, l, _UU0393_, fe, t, rec(fe)(l)(_UU0393_)(Mode::Chk(t))), fn(x1) {
                bind(rfields_dec(e, rec, p, l, _UU0393_, names, fs, fes_), fn(x2) {
                  match x2 {
                    SigT::ExistT(es, s) => Result0::Ok(SigT::ExistT(List::Cons(x1, es), List::Cons(x, s)))
                  }
                })
              })
            }
            Ty::TError => {
              let t = Ty::TError
              bind(cres(e, l, _UU0393_, fe, t, rec(fe)(l)(_UU0393_)(Mode::Chk(t))), fn(x1) {
                bind(rfields_dec(e, rec, p, l, _UU0393_, names, fs, fes_), fn(x2) {
                  match x2 {
                    SigT::ExistT(es, s) => Result0::Ok(SigT::ExistT(List::Cons(x1, es), List::Cons(x, s)))
                  }
                })
              })
            }
          }
        })
      })
    }
  }
}

pub fn rec_vars_dec(p : Pos, names : List[Ident], ixs : List[Nat]) -> Result0[List[Expr], Elab_error] {
  match rec_vars(ixs, length(names)) {
    Some(vs) => Result0::Ok(vs)
    None => match find(fn(f) {
      match index_of(f, names) {
        Some(j) => negb(existsb(fn(x1) { eqb0(j, x1) }, ixs))
        None => false
      }
    }, names) {
      Some(f) => Result0::Err(Elab_error::EE_MissingField(p, f))
      None => Result0::Err(Elab_error::EE_UnknownField(p, String0::EmptyString))
    }
  }
}

pub fn len_dec(p : Pos, t : Ident, a : Nat, b : Nat) -> Result0[Unit, Elab_error] {
  match eq_dec(a, b) {
    true => Result0::Ok(())
    false => Result0::Err(Elab_error::EE_NotRecord(p, Ty::TData(t, List::Nil)))
  }
}

pub fn content(t : Ty) -> Ty {
  match t {
    Ty::TRef(u) => u
    _ => t
  }
}

pub fn rpass(e : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], l : Cenv, _UU0393_ : Lctx, names : List[Ident], fs0 : List[Ty], fes : List[(Ident, Sexpr)], st : List[Option[Ty]]) -> Result0[List[Option[Ty]], Elab_error] {
  match fes {
    List::Nil => Result0::Ok(st)
    List::Cons(p, fes_) => match p {
      (f, fe) => {
        let pt = match index_of(f, names) {
          Some(i) => content(nth(i, fs0, Ty::TBase(Base_ty::BUnit)))
          None => Ty::TBase(Base_ty::BUnit)
        }
        bind(match resolve(st, pt) {
          Some(_) => Result0::Ok(st)
          None => bind(rec(fe)(l)(_UU0393_)(Mode::Syn), fn(x) {
            match x {
              SigT::ExistT(t, _) => Result0::Ok(tmatch(pt, t, st))
            }
          })
        }, fn(st_) { rpass(e, rec, l, _UU0393_, names, fs0, fes_, st_) })
      }
    }
  }
}

pub fn upd_rhs_dec(p : Pos, op : Option[Ident], _UU03c4_ : Ty, cur : Expr, v : Expr) -> Result0[Expr, Elab_error] {
  match op {
    Some(o) => match ty_eq_dec(binop_res(o, _UU03c4_))(_UU03c4_) {
      true => bind(binop_dec(p, o, _UU03c4_, cur, v), fn(x) { Result0::Ok(x) })
      false => Result0::Err(Elab_error::EE_NoOperator(p, o, _UU03c4_))
    }
    None => Result0::Ok(v)
  }
}

pub fn field_cell_dec(e : Senv, p : Pos, f : Ident, t : Ident, ts : List[Ty], i : Nat) -> Result0[((Ident, Nat), Ty), Elab_error] {
  match field_cell(e, t, ts, i) {
    Some(r) => Result0::Ok(r)
    None => Result0::Err(Elab_error::EE_NotMutable(p, f))
  }
}

pub fn ref_ok_dec(e : Senv, p : Pos) -> Result0[Unit, Elab_error] {
  bind(of_option(lookup_ty(match e {
    Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
  }, String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString)))), Elab_error::EE_UnknownType(p, String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString))))), fn(x) {
    match eq_dec(match x {
      Tdef::Mk_tdef(_, td_tparams, _, _) => td_tparams
    }, Nat::S(Nat::O)) {
      true => bind(of_option(lookup_ctor(x, String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString)))), Elab_error::EE_UnknownCtor(p, String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString))))), fn(x0) {
        match list_eq_dec(ty_eq_dec, match x0 {
          Cdef::Mk_cdef(_, cd_fields) => cd_fields
        }, List::Cons(Ty::TRef(Ty::TVar(Nat::O)), List::Nil)) {
          true => Result0::Ok(())
          false => Result0::Err(Elab_error::EE_UnknownType(p, String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString)))))
        }
      })
      false => Result0::Err(Elab_error::EE_UnknownType(p, String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString)))))
    }
  })
}

pub fn sinits_dec(e : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], l : Cenv, _UU0393_ : Lctx, inits : List[(Ident, Sexpr)]) -> Result0[SigT[List[Ty], List[Expr]], Elab_error] {
  match inits {
    List::Nil => Result0::Ok(SigT::ExistT(List::Nil, List::Nil))
    List::Cons(p, inits_) => match p {
      (_, s) => bind(rec(s)(l)(_UU0393_)(Mode::Syn), fn(x0) {
        match x0 {
          SigT::ExistT(_UU03c4_, s0) => bind(sinits_dec(e, rec, l, _UU0393_, inits_), fn(x1) {
            match x1 {
              SigT::ExistT(_UU03c4_s, s1) => Result0::Ok(SigT::ExistT(List::Cons(_UU03c4_, _UU03c4_s), List::Cons(s0, s1)))
            }
          })
        }
      })
    }
  }
}

pub fn supds_dec(e : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], p : Pos, l : Cenv, _UU0393_ : Lctx, names : List[Ident], _UU03c4_s : List[Ty], upds : List[(Ident, Sexpr)]) -> Result0[List[(Ident, Expr)], Elab_error] {
  match upds {
    List::Nil => Result0::Ok(List::Nil)
    List::Cons(p0, upds_) => match p0 {
      (y, s) => bind(of_option(index_of(y, names), Elab_error::EE_Unbound(p, y)), fn(x) {
        bind(of_option(nth_error(_UU03c4_s, x), Elab_error::EE_Unbound(p, y)), fn(x0) {
          bind(cres(e, l, _UU0393_, s, x0, rec(s)(l)(_UU0393_)(Mode::Chk(x0))), fn(x1) {
            bind(supds_dec(e, rec, p, l, _UU0393_, names, _UU03c4_s, upds_), fn(x2) { Result0::Ok(List::Cons((y, x1), x2)) })
          })
        })
      })
    }
  }
}

pub fn ochk_dec(e : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], l : Cenv, _UU0393_ : Lctx, _UU03c4_ : Ty, os : Option[Sexpr]) -> Result0[Option[Expr], Elab_error] {
  match os {
    Some(s) => bind(cres(e, l, _UU0393_, s, _UU03c4_, rec(s)(l)(_UU0393_)(Mode::Chk(_UU03c4_))), fn(x) { Result0::Ok(Some(x)) })
    None => Result0::Ok(None)
  }
}

pub fn label_at(p : Pos, l : Cenv, k : Nat) -> Result0[(List[Ty], Ty), Elab_error] {
  of_option(nth_error(core_labels(match l {
    Cenv::Mk_cenv(ce_labs, _) => ce_labs
  }), k), Elab_error::EE_NoTarget(p))
}

pub fn array_src(_ : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], p : Pos, l : Cenv, _UU0393_ : Lctx, src : Sexpr) -> Result0[SigT[Expr, SigT[Expr, Iter_src]], Elab_error] {
  bind(rec(src)(l)(_UU0393_)(Mode::Syn), fn(x) {
    match x {
      SigT::ExistT(_UU03c4_, s) => match _UU03c4_ {
        Ty::TArray(k, t) => Result0::Ok(SigT::ExistT(s, SigT::ExistT(Expr::EMem(Mem_op::MLength(k, t), List::Cons(Expr::EVar(Nat::O), List::Nil)), Iter_src::IArray(k, t))))
        _ => Result0::Err(Elab_error::EE_NoMethod(p, String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::EmptyString)))), _UU03c4_))
      }
    }
  })
}

pub fn fsrc_dec(e : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], p : Pos, l : Cenv, _UU0393_ : Lctx, src : Sexpr) -> Result0[SigT[Expr, SigT[Expr, Iter_src]], Elab_error] {
  match src {
    Sexpr::SInfix(q, op, lo, hi) => match range_op(op) {
      Some(rk) => bind(rec(lo)(l)(_UU0393_)(Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(_UU03c4_, s) => match _UU03c4_ {
            Ty::TBase(b) => match b {
              Base_ty::BInt(kk) => bind(cres(e, l, List::Cons((None, Ty::TBase(Base_ty::BInt(kk))), _UU0393_), hi, Ty::TBase(Base_ty::BInt(kk)), rec(hi)(l)(List::Cons((None, Ty::TBase(Base_ty::BInt(kk))), _UU0393_))(Mode::Chk(Ty::TBase(Base_ty::BInt(kk))))), fn(x0) {
                Result0::Ok(SigT::ExistT(s, SigT::ExistT(x0, Iter_src::IRange(rk, kk))))
              })
              _ => Result0::Err(Elab_error::EE_NoOperator(q, op, _UU03c4_))
            }
            _ => Result0::Err(Elab_error::EE_NoOperator(q, op, _UU03c4_))
          }
        }
      })
      None => array_src(e, rec, p, l, _UU0393_, src)
    }
    _ => array_src(e, rec, p, l, _UU0393_, src)
  }
}

pub fn fi_pat_dec(e : Senv, p : Pos, it : Iter_src, _UU03c4_s : List[Ty], pats : List[Spat]) -> Result0[SigT[Pat, SigT[Lctx, SigT[Expr, Ty]]], Elab_error] {
  match pats {
    List::Nil => Result0::Err(Elab_error::EE_PatType(p, fi_elem_ty(it)))
    List::Cons(sp1, l) => match l {
      List::Nil => bind(epat(e, sp1, fi_elem_ty(it)), fn(x) {
        match x {
          SigT::ExistT(q, s) => Result0::Ok(SigT::ExistT(q, SigT::ExistT(s, SigT::ExistT(fi_elem(it, fi_n(it, _UU03c4_s)), fi_elem_ty(it)))))
        }
      })
      List::Cons(sp2, l0) => match l0 {
        List::Nil => match it {
          Iter_src::IRange(_, _) => Result0::Err(Elab_error::EE_PatType(p, fi_elem_ty(it)))
          Iter_src::IArray(_, t) => bind(epat(e, sp1, Ty::TBase(Base_ty::BInt(Int_kind::I32))), fn(x) {
            match x {
              SigT::ExistT(q1, s) => bind(epat(e, sp2, t), fn(x0) {
                match x0 {
                  SigT::ExistT(q2, s0) => Result0::Ok(SigT::ExistT(Pat::PTuple(List::Cons(q1, List::Cons(q2, List::Nil))), SigT::ExistT(app(s, s0), SigT::ExistT(Expr::ETuple(List::Cons(Expr::EVar(Nat::O), List::Cons(fi_elem(it, fi_n(it, _UU03c4_s)), List::Nil))), Ty::TTuple(List::Cons(Ty::TBase(Base_ty::BInt(Int_kind::I32)), List::Cons(t, List::Nil)))))))
                }
              })
            }
          })
        }
        List::Cons(_, _) => Result0::Err(Elab_error::EE_PatType(p, fi_elem_ty(it)))
      }
    }
  }
}

pub fn try_cands(e : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], p : Pos, l : Cenv, _UU0393_ : Lctx, body : Sexpr, bm : Mode, ts : List[Ident]) -> List[SigT[Ident, (Unit, Out)]] {
  match ts {
    List::Nil => List::Nil
    List::Cons(t, ts_) => match err_dec(e, p, t) {
      Result0::Ok(_) => match rec(body)(set_exn(Ty::TData(t, List::Nil), l))(_UU0393_)(bm) {
        Result0::Ok(o) => List::Cons(SigT::ExistT(t, ((), o)), try_cands(e, rec, p, l, _UU0393_, body, bm, ts_))
        Result0::Err(_) => try_cands(e, rec, p, l, _UU0393_, body, bm, ts_)
      }
      Result0::Err(_) => try_cands(e, rec, p, l, _UU0393_, body, bm, ts_)
    }
  }
}

pub fn try_pick(e : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], p : Pos, l : Cenv, _UU0393_ : Lctx, cases : List[(Spat, Sexpr)], body : Sexpr, bm : Mode) -> Result0[SigT[Ty, (Unit, Out)], Elab_error] {
  match catch_of(e, cases) {
    Catch_info::CINone => match try_cands(e, rec, p, l, _UU0393_, body, bm, map(fn(t) {
      match t {
        Tdef::Mk_tdef(td_name, _, _, _) => td_name
      }
    }, filter(fn(t) {
      match t {
        Tdef::Mk_tdef(_, _, _, td_err) => td_err
      }
    }, match (match e {
      Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
    }) {
      Genv::Mk_genv(ge_types, _) => ge_types
    }))) {
      List::Nil => bind(rec(body)(set_exn(Ty::TError, l))(_UU0393_)(bm), fn(o) { Result0::Ok(SigT::ExistT(Ty::TError, ((), o))) })
      List::Cons(s, l0) => match s {
        SigT::ExistT(t, p0) => match p0 {
          (_, o) => match l0 {
            List::Nil => Result0::Ok(SigT::ExistT(Ty::TData(t, List::Nil), ((), o)))
            List::Cons(_, _) => bind(rec(body)(set_exn(Ty::TError, l))(_UU0393_)(bm), fn(o0) { Result0::Ok(SigT::ExistT(Ty::TError, ((), o0))) })
          }
        }
      }
    }
    Catch_info::CIOne(t) => bind(rec(body)(set_exn(Ty::TData(t, List::Nil), l))(_UU0393_)(bm), fn(o) { Result0::Ok(SigT::ExistT(Ty::TData(t, List::Nil), ((), o))) })
    Catch_info::CIMany => bind(rec(body)(set_exn(Ty::TError, l))(_UU0393_)(bm), fn(o) { Result0::Ok(SigT::ExistT(Ty::TError, ((), o))) })
  }
}

pub fn failure_ok_dec(e : Senv, p : Pos) -> Result0[Unit, Elab_error] {
  bind(of_option(lookup_ty(match e {
    Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
  }, String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString)))))))), Elab_error::EE_UnknownType(p, String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))))), fn(x) {
    match eq_dec(match x {
      Tdef::Mk_tdef(_, td_tparams, _, _) => td_tparams
    }, Nat::O) {
      true => bind(of_option(lookup_ctor(x, String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString)))))))), Elab_error::EE_UnknownCtor(p, String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))))), fn(x0) {
        match list_eq_dec(ty_eq_dec, match x0 {
          Cdef::Mk_cdef(_, cd_fields) => cd_fields
        }, List::Cons(Ty::TBase(Base_ty::BString), List::Nil)) {
          true => Result0::Ok(())
          false => Result0::Err(Elab_error::EE_UnknownType(p, String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString)))))))))
        }
      })
      false => Result0::Err(Elab_error::EE_UnknownType(p, String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString)))))))))
    }
  })
}

pub fn qual_trait_dec(e : Senv, q : Pos, t : Ident, mn : Ident) -> Result0[SigT[Ident, Option[Ty]], Elab_error] {
  match find_trait(trs(e), t) {
    Some(_) => Result0::Ok(SigT::ExistT(t, None))
    None => match index_of(t, match e {
      Senv::Mk_senv(_, _, _, se_tps, _) => se_tps
    }) {
      Some(i) => match hd_error(filter(fn(x1) { declares(e, mn, x1) }, asm_traits(e, Ty::TVar(i)))) {
        Some(tr) => Result0::Ok(SigT::ExistT(tr, Some(Ty::TVar(i))))
        None => Result0::Err(Elab_error::EE_NoMethod(q, mn, Ty::TVar(i)))
      }
      None => match filter(fn(x1) { declares(e, mn, x1) }, map(fn(t0) {
        match t0 {
          Trinfo::Mk_trinfo(ti_name, _, _, _) => ti_name
        }
      }, trs(e))) {
        List::Nil => Result0::Err(Elab_error::EE_NoMethod(q, mn, Ty::TBase(Base_ty::BUnit)))
        List::Cons(tr, l) => match l {
          List::Nil => Result0::Ok(SigT::ExistT(tr, None))
          List::Cons(_, _) => Result0::Err(Elab_error::EE_AmbiguousMethod(q, mn))
        }
      }
    }
  }
}

pub type Pre_t = SigT[Ty, Expr]

pub fn tself(_ : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], q : Pos, l : Cenv, _UU0393_ : Lctx, os : Option[Ty], sg : Msig, args : List[Sexpr], hm : Option[Ty]) -> Result0[SigT[Ty, Option[Pre_t]], Elab_error] {
  match os {
    Some(t) => Result0::Ok(SigT::ExistT(t, None))
    None => match (match sg {
      Msig::Mk_msig(_, ms_params, _, _) => ms_params
    }) {
      List::Nil => match (match sg {
        Msig::Mk_msig(_, _, ms_ret, _) => ms_ret
      }) {
        Ty::TVar(i) => match i {
          Nat::O => match hm {
            Some(t) => Result0::Ok(SigT::ExistT(t, None))
            None => Result0::Err(Elab_error::EE_CannotInfer(q, match sg {
              Msig::Mk_msig(ms_name, _, _, _) => ms_name
            }))
          }
          Nat::S(_) => Result0::Err(Elab_error::EE_CannotInfer(q, match sg {
            Msig::Mk_msig(ms_name, _, _, _) => ms_name
          }))
        }
        _ => Result0::Err(Elab_error::EE_CannotInfer(q, match sg {
          Msig::Mk_msig(ms_name, _, _, _) => ms_name
        }))
      }
      List::Cons(t, _) => match t {
        Ty::TVar(i) => match i {
          Nat::O => match args {
            List::Nil => match (match sg {
              Msig::Mk_msig(_, _, ms_ret, _) => ms_ret
            }) {
              Ty::TVar(i0) => match i0 {
                Nat::O => match hm {
                  Some(t0) => Result0::Ok(SigT::ExistT(t0, None))
                  None => Result0::Err(Elab_error::EE_CannotInfer(q, match sg {
                    Msig::Mk_msig(ms_name, _, _, _) => ms_name
                  }))
                }
                Nat::S(_) => Result0::Err(Elab_error::EE_CannotInfer(q, match sg {
                  Msig::Mk_msig(ms_name, _, _, _) => ms_name
                }))
              }
              _ => Result0::Err(Elab_error::EE_CannotInfer(q, match sg {
                Msig::Mk_msig(ms_name, _, _, _) => ms_name
              }))
            }
            List::Cons(a0, _) => bind(rec(a0)(l)(_UU0393_)(Mode::Syn), fn(x) {
              match x {
                SigT::ExistT(t0, s) => Result0::Ok(SigT::ExistT(t0, Some(SigT::ExistT(t0, s))))
              }
            })
          }
          Nat::S(_) => match (match sg {
            Msig::Mk_msig(_, _, ms_ret, _) => ms_ret
          }) {
            Ty::TVar(i0) => match i0 {
              Nat::O => match hm {
                Some(t0) => Result0::Ok(SigT::ExistT(t0, None))
                None => Result0::Err(Elab_error::EE_CannotInfer(q, match sg {
                  Msig::Mk_msig(ms_name, _, _, _) => ms_name
                }))
              }
              Nat::S(_) => Result0::Err(Elab_error::EE_CannotInfer(q, match sg {
                Msig::Mk_msig(ms_name, _, _, _) => ms_name
              }))
            }
            _ => Result0::Err(Elab_error::EE_CannotInfer(q, match sg {
              Msig::Mk_msig(ms_name, _, _, _) => ms_name
            }))
          }
        }
        _ => match (match sg {
          Msig::Mk_msig(_, _, ms_ret, _) => ms_ret
        }) {
          Ty::TVar(i) => match i {
            Nat::O => match hm {
              Some(t0) => Result0::Ok(SigT::ExistT(t0, None))
              None => Result0::Err(Elab_error::EE_CannotInfer(q, match sg {
                Msig::Mk_msig(ms_name, _, _, _) => ms_name
              }))
            }
            Nat::S(_) => Result0::Err(Elab_error::EE_CannotInfer(q, match sg {
              Msig::Mk_msig(ms_name, _, _, _) => ms_name
            }))
          }
          _ => Result0::Err(Elab_error::EE_CannotInfer(q, match sg {
            Msig::Mk_msig(ms_name, _, _, _) => ms_name
          }))
        }
      }
    }
  }
}

pub fn pre_args(e : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], p : Pos, l : Cenv, _UU0393_ : Lctx, args : List[Sexpr], pre : Option[Pre_t], ps : List[Ty]) -> Result0[List[Expr], Elab_error] {
  match args {
    List::Nil => chk_list(e, p, l, _UU0393_, fn(s_) {
      fn(_UU03c4__) {
        cres(e, l, _UU0393_, s_, _UU03c4__, rec(s_)(l)(_UU0393_)(Mode::Chk(_UU03c4__)))
      }
    }, List::Nil, ps)
    List::Cons(a0, rest) => match pre {
      Some(p0) => match p0 {
        SigT::ExistT(t, s) => match ps {
          List::Nil => Result0::Err(Elab_error::EE_Type(p, Type_error::E_ArgArity(Nat::O, length(List::Cons(a0, rest)))))
          List::Cons(p1, ps_) => match ty_eq_dec(t)(p1) {
            true => bind(chk_list(e, p, l, _UU0393_, fn(s_) {
              fn(_UU03c4__) {
                cres(e, l, _UU0393_, s_, _UU03c4__, rec(s_)(l)(_UU0393_)(Mode::Chk(_UU03c4__)))
              }
            }, rest, ps_), fn(x) { Result0::Ok(List::Cons(s, x)) })
            false => Result0::Err(Elab_error::EE_Annot(p, p1, t))
          }
        }
      }
      None => chk_list(e, p, l, _UU0393_, fn(s_) {
        fn(_UU03c4__) {
          cres(e, l, _UU0393_, s_, _UU03c4__, rec(s_)(l)(_UU0393_)(Mode::Chk(_UU03c4__)))
        }
      }, List::Cons(a0, rest), ps)
    }
  }
}

pub fn tcall(e : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], p : Pos, q : Pos, l : Cenv, _UU0393_ : Lctx, _ : Sexpr, t : Ident, mn : Ident, args : List[Sexpr], hm : Option[Ty]) -> Result0[Sout, Elab_error] {
  bind(qual_trait_dec(e, q, t, mn), fn(x) {
    match x {
      SigT::ExistT(tr, s) => bind(of_option(find_trait(trs(e), tr), Elab_error::EE_NoMethod(q, mn, Ty::TBase(Base_ty::BUnit))), fn(x0) {
        bind(of_option(method_of(x0, mn), Elab_error::EE_NoMethod(q, mn, Ty::TBase(Base_ty::BUnit))), fn(x1) {
          match x1 {
            (i, sg) => bind(tself(e, rec, q, l, _UU0393_, s, sg, args, hm), fn(x2) {
              match x2 {
                SigT::ExistT(_UU03c4_s, s0) => bind(dict_dec(e, q, _UU0393_, tr, _UU03c4_s), fn(x3) {
                  bind(field_proj_dec(e, q, tr, List::Cons(_UU03c4_s, List::Nil), i, x3), fn(x4) {
                    match x4 {
                      (mv, t0) => match t0 {
                        Ty::TArrow(ps, r, _UU03b5_) => bind(pre_args(e, rec, p, l, _UU0393_, args, s0, ps), fn(x5) {
                          bind(allowed_dec(e, p, _UU03b5_, match l {
                            Cenv::Mk_cenv(_, ce_exn) => ce_exn
                          }), fn(_) { Result0::Ok(SigT::ExistT(r, wrap_call(l, _UU03b5_, r, mv, x5))) })
                        })
                        _ => Result0::Err(Elab_error::EE_Type(q, Type_error::E_NotFunction(t0)))
                      }
                    }
                  })
                })
              }
            })
          }
        })
      })
    }
  })
}

pub fn qcall(e : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], p : Pos, q : Pos, l : Cenv, _UU0393_ : Lctx, f : Sexpr, t : Ident, mn : Ident, args : List[Sexpr], hm : Option[Ty]) -> Result0[Sout, Elab_error] {
  match has_meth(e, t, mn) {
    true => bind(of_option(lookup_fn(match e {
      Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
    }, meth_name(t, mn)), Elab_error::EE_Unbound(q, meth_name(t, mn))), fn(x) {
      let n = nbounds(e, meth_name(t, mn))
      let st0 = match hm {
        Some(t0) => tmatch(match x {
          Fdef::Mk_fdef(_, _, _, fd_ret, _, _) => fd_ret
        }, t0, repeat(None, match x {
          Fdef::Mk_fdef(_, fd_tparams, _, _, _, _) => fd_tparams
        }))
        None => repeat(None, match x {
          Fdef::Mk_fdef(_, fd_tparams, _, _, _, _) => fd_tparams
        })
      }
      bind(gargs(e, rec, p, q, l, _UU0393_, args, skipn(n, match x {
        Fdef::Mk_fdef(_, _, fd_params, _, _, _) => fd_params
      }), match x {
        Fdef::Mk_fdef(_, fd_tparams, _, _, _, _) => fd_tparams
      }, st0, meth_name(t, mn)), fn(x0) {
        match x0 {
          SigT::ExistT(ts, s) => bind(dicts_dec(e, q, _UU0393_, map({ let a1 = fn(x1) { inst(ts, x1) }; fn(x1) { tsubst(a1, x1) } }, firstn(n, match x {
            Fdef::Mk_fdef(_, _, fd_params, _, _, _) => fd_params
          }))), fn(x1) {
            bind(allowed_dec(e, p, tsubst(fn(x2) { inst(ts, x2) }, match x {
              Fdef::Mk_fdef(_, _, _, _, fd_eff, _) => fd_eff
            }), match l {
              Cenv::Mk_cenv(_, ce_exn) => ce_exn
            }), fn(_) {
              Result0::Ok(SigT::ExistT(tsubst(fn(x2) { inst(ts, x2) }, match x {
                Fdef::Mk_fdef(_, _, _, fd_ret, _, _) => fd_ret
              }), wrap_call(l, tsubst(fn(x2) { inst(ts, x2) }, match x {
                Fdef::Mk_fdef(_, _, _, _, fd_eff, _) => fd_eff
              }), tsubst(fn(x2) { inst(ts, x2) }, match x {
                Fdef::Mk_fdef(_, _, _, fd_ret, _, _) => fd_ret
              }), Expr::EGlobal(meth_name(t, mn), ts), app(x1, s))))
            })
          })
        }
      })
    })
    false => tcall(e, rec, p, q, l, _UU0393_, f, t, mn, args, hm)
  }
}

pub fn dcall(e : Senv, rec : (Sexpr) -> (Cenv) -> (Lctx) -> (Mode) -> Result0[Out, Elab_error], p : Pos, l : Cenv, _UU0393_ : Lctx, _ : Sexpr, mn : Ident, args : List[Sexpr], _UU03c4_r : Ty, r_ : Expr, hm : Option[Ty]) -> Result0[Sout, Elab_error] {
  match meth_fn(e, _UU03c4_r, mn) {
    true => bind(of_option(head_name(_UU03c4_r), Elab_error::EE_NoMethod(p, mn, _UU03c4_r)), fn(x) {
      bind(bcheck(has_meth(e, x, mn), Elab_error::EE_NoMethod(p, mn, _UU03c4_r)), fn(_) {
        bind(of_option(lookup_fn(match e {
          Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
        }, meth_name(x, mn)), Elab_error::EE_Unbound(p, meth_name(x, mn))), fn(x0) {
          let n = nbounds(e, meth_name(x, mn))
          match skipn(n, match x0 {
            Fdef::Mk_fdef(_, _, fd_params, _, _, _) => fd_params
          }) {
            List::Nil => Result0::Err(Elab_error::EE_Type(p, Type_error::E_ArgArity(Nat::O, length(args))))
            List::Cons(p0, ps) => {
              let st0 = match hm {
                Some(t) => tmatch(match x0 {
                  Fdef::Mk_fdef(_, _, _, fd_ret, _, _) => fd_ret
                }, t, repeat(None, match x0 {
                  Fdef::Mk_fdef(_, fd_tparams, _, _, _, _) => fd_tparams
                }))
                None => repeat(None, match x0 {
                  Fdef::Mk_fdef(_, fd_tparams, _, _, _, _) => fd_tparams
                })
              }
              bind(gargs(e, rec, p, p, l, _UU0393_, args, ps, match x0 {
                Fdef::Mk_fdef(_, fd_tparams, _, _, _, _) => fd_tparams
              }, tmatch(p0, _UU03c4_r, st0), meth_name(x, mn)), fn(x1) {
                match x1 {
                  SigT::ExistT(ts, s0) => match ty_eq_dec(tsubst(fn(x2) { inst(ts, x2) }, p0))(_UU03c4_r) {
                    true => bind(dicts_dec(e, p, _UU0393_, map({ let a1 = fn(x2) { inst(ts, x2) }; fn(x2) { tsubst(a1, x2) } }, firstn(n, match x0 {
                      Fdef::Mk_fdef(_, _, fd_params, _, _, _) => fd_params
                    }))), fn(x2) {
                      bind(allowed_dec(e, p, tsubst(fn(x3) { inst(ts, x3) }, match x0 {
                        Fdef::Mk_fdef(_, _, _, _, fd_eff, _) => fd_eff
                      }), match l {
                        Cenv::Mk_cenv(_, ce_exn) => ce_exn
                      }), fn(_) {
                        Result0::Ok(SigT::ExistT(tsubst(fn(x3) { inst(ts, x3) }, match x0 {
                          Fdef::Mk_fdef(_, _, _, fd_ret, _, _) => fd_ret
                        }), wrap_call(l, tsubst(fn(x3) { inst(ts, x3) }, match x0 {
                          Fdef::Mk_fdef(_, _, _, _, fd_eff, _) => fd_eff
                        }), tsubst(fn(x3) { inst(ts, x3) }, match x0 {
                          Fdef::Mk_fdef(_, _, _, fd_ret, _, _) => fd_ret
                        }), Expr::EGlobal(meth_name(x, mn), ts), app(x2, List::Cons(r_, s0)))))
                      })
                    })
                    false => Result0::Err(Elab_error::EE_Annot(p, tsubst(fn(x2) { inst(ts, x2) }, p0), _UU03c4_r))
                  }
                }
              })
            }
          }
        })
      })
    })
    false => match obj_of(e, _UU03c4_r) {
      Some(tr) => bind(of_option(obj_index(obj_fields(trs(e), tr), mn), Elab_error::EE_NoMethod(p, mn, _UU03c4_r)), fn(x) {
        bind(field_proj_dec(e, p, obj_name(tr), List::Nil, x, r_), fn(x0) {
          match x0 {
            (fv, t) => match t {
              Ty::TArrow(ps, r, _UU03b5_) => bind(chk_list(e, p, l, _UU0393_, fn(s_) {
                fn(_UU03c4__) {
                  cres(e, l, _UU0393_, s_, _UU03c4__, rec(s_)(l)(_UU0393_)(Mode::Chk(_UU03c4__)))
                }
              }, args, ps), fn(x1) {
                bind(allowed_dec(e, p, _UU03b5_, match l {
                  Cenv::Mk_cenv(_, ce_exn) => ce_exn
                }), fn(_) { Result0::Ok(SigT::ExistT(r, wrap_call(l, _UU03b5_, r, fv, x1))) })
              })
              _ => Result0::Err(Elab_error::EE_Type(p, Type_error::E_NotFunction(t)))
            }
          }
        })
      })
      None => bind(bcheck(dot_traits(_UU03c4_r), Elab_error::EE_NoMethod(p, mn, _UU03c4_r)), fn(_) {
        match dot_trait(e, _UU0393_, mn, _UU03c4_r) {
          List::Nil => Result0::Err(Elab_error::EE_NoMethod(p, mn, _UU03c4_r))
          List::Cons(tr, l0) => match l0 {
            List::Nil => bind(of_option(find_trait(trs(e), tr), Elab_error::EE_NoMethod(p, mn, _UU03c4_r)), fn(x) {
              bind(of_option(method_of(x, mn), Elab_error::EE_NoMethod(p, mn, _UU03c4_r)), fn(x0) {
                match x0 {
                  (i, _) => bind(dict_dec(e, p, _UU0393_, tr, _UU03c4_r), fn(x1) {
                    bind(field_proj_dec(e, p, tr, List::Cons(_UU03c4_r, List::Nil), i, x1), fn(x2) {
                      match x2 {
                        (mv, t) => match t {
                          Ty::TArrow(ps0, r, _UU03b5_) => match ps0 {
                            List::Nil => Result0::Err(Elab_error::EE_Type(p, Type_error::E_NotFunction(t)))
                            List::Cons(p0, ps) => match ty_eq_dec(p0)(_UU03c4_r) {
                              true => bind(chk_list(e, p, l, _UU0393_, fn(s_) {
                                fn(_UU03c4__) {
                                  cres(e, l, _UU0393_, s_, _UU03c4__, rec(s_)(l)(_UU0393_)(Mode::Chk(_UU03c4__)))
                                }
                              }, args, ps), fn(x3) {
                                bind(allowed_dec(e, p, _UU03b5_, match l {
                                  Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                }), fn(_) {
                                  Result0::Ok(SigT::ExistT(r, wrap_call(l, _UU03b5_, r, mv, List::Cons(r_, x3))))
                                })
                              })
                              false => Result0::Err(Elab_error::EE_Annot(p, _UU03c4_r, p0))
                            }
                          }
                          _ => Result0::Err(Elab_error::EE_Type(p, Type_error::E_NotFunction(t)))
                        }
                      }
                    })
                  })
                }
              })
            })
            List::Cons(_, _) => Result0::Err(Elab_error::EE_AmbiguousMethod(p, mn))
          }
        }
      })
    }
  }
}

pub(all) enum Head0 {
  HName(Pos, Ident)
  HExpr
  HCtor(Pos, Option[Ident], Ident)
  HQual(Pos, Ident, Ident)
  HOther
}

pub fn head_of(_UU0393_ : Lctx, f : Sexpr) -> Head0 {
  match f {
    Sexpr::SVar(q, g) => match lookup_local(g, _UU0393_) {
      Some(_) => Head0::HExpr
      None => Head0::HName(q, g)
    }
    Sexpr::SConstr(q, tq, c) => Head0::HCtor(q, tq, c)
    Sexpr::SQual(q, t, m) => Head0::HQual(q, t, m)
    _ => Head0::HExpr
  }
}

pub fn elab(e : Senv, s : Sexpr, l : Cenv, _UU0393_ : Lctx, m : Mode) -> Result0[Out, Elab_error] {
  match s {
    Sexpr::SVar(p, x) => fin(e, p, l, _UU0393_, Sexpr::SVar(p, x), m, var_syn(e, p, l, _UU0393_, x, hint(m)))
    Sexpr::SLit(p, l0) => lit_m(e, p, l, _UU0393_, l0, m)
    Sexpr::SApp(p, f, args) => match head_of(_UU0393_, f) {
      Head0::HName(q, g) => match lookup_fn(match e {
        Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
      }, g) {
        Some(fd) => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, args), m, {
          let n = nbounds(e, g)
          let st0 = match hint(m) {
            Some(t) => tmatch(match fd {
              Fdef::Mk_fdef(_, _, _, fd_ret, _, _) => fd_ret
            }, t, repeat(None, match fd {
              Fdef::Mk_fdef(_, fd_tparams, _, _, _, _) => fd_tparams
            }))
            None => repeat(None, match fd {
              Fdef::Mk_fdef(_, fd_tparams, _, _, _, _) => fd_tparams
            })
          }
          bind(gargs(e, fn(x1) { fn(x2) { fn(x3) { fn(x4) { elab(e, x1, x2, x3, x4) } } } }, p, q, l, _UU0393_, args, skipn(n, match fd {
            Fdef::Mk_fdef(_, _, fd_params, _, _, _) => fd_params
          }), match fd {
            Fdef::Mk_fdef(_, fd_tparams, _, _, _, _) => fd_tparams
          }, st0, g), fn(x) {
            match x {
              SigT::ExistT(ts, s0) => bind(dicts_dec(e, q, _UU0393_, map({ let a1 = fn(x1) { inst(ts, x1) }; fn(x1) { tsubst(a1, x1) } }, firstn(n, match fd {
                Fdef::Mk_fdef(_, _, fd_params, _, _, _) => fd_params
              }))), fn(x0) {
                bind(allowed_dec(e, p, tsubst(fn(x1) { inst(ts, x1) }, match fd {
                  Fdef::Mk_fdef(_, _, _, _, fd_eff, _) => fd_eff
                }), match l {
                  Cenv::Mk_cenv(_, ce_exn) => ce_exn
                }), fn(_) {
                  Result0::Ok(SigT::ExistT(tsubst(fn(x1) { inst(ts, x1) }, match fd {
                    Fdef::Mk_fdef(_, _, _, fd_ret, _, _) => fd_ret
                  }), wrap_call(l, tsubst(fn(x1) { inst(ts, x1) }, match fd {
                    Fdef::Mk_fdef(_, _, _, _, fd_eff, _) => fd_eff
                  }), tsubst(fn(x1) { inst(ts, x1) }, match fd {
                    Fdef::Mk_fdef(_, _, _, fd_ret, _, _) => fd_ret
                  }), Expr::EGlobal(g, ts), app(x0, s0))))
                })
              })
            }
          })
        })
        None => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))) {
          true => match args {
            List::Nil => {
              let a0 = List::Nil
              match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))) {
                true => match a0 {
                  List::Nil => match string_dec(g, String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::EmptyString)))))) {
                    true => match a0 {
                      List::Nil => match m {
                        Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::EAbort(Ty::TBase(Base_ty::BUnit))))
                        Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Nil), _UU03c4_, Expr::EAbort(_UU03c4_))
                      }
                      List::Cons(s0, l0) => {
                        let a2 = List::Cons(s0, l0)
                        match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))) {
                          true => match a2 {
                            List::Nil => {
                              let a3 = List::Nil
                              match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                true => match a3 {
                                  List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                  List::Cons(a, l1) => match l1 {
                                    List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                      bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                        bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                          Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                        }), fn(x0) {
                                          match m {
                                            Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                            Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                          }
                                        })
                                      })
                                    })
                                    List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                  }
                                }
                                false => Result0::Err(Elab_error::EE_Unbound(q, g))
                              }
                            }
                            List::Cons(a, l1) => match l1 {
                              List::Nil => bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                match m {
                                  Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(x, Expr::EAbort(Ty::TBase(Base_ty::BUnit)))))
                                  Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ELet(x, Expr::EAbort(_UU03c4_)))
                                }
                              })
                              List::Cons(s1, l2) => {
                                let a3 = List::Cons(a, List::Cons(s1, l2))
                                match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                  true => match a3 {
                                    List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                    List::Cons(a1, l3) => match l3 {
                                      List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                        bind(cres(e, l, _UU0393_, a1, Ty::TBase(Base_ty::BString), elab(e, a1, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                          bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                            Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                          }), fn(x0) {
                                            match m {
                                              Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                              Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a1, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                            }
                                          })
                                        })
                                      })
                                      List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                    }
                                  }
                                  false => Result0::Err(Elab_error::EE_Unbound(q, g))
                                }
                              }
                            }
                          }
                          false => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                            true => match a2 {
                              List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                              List::Cons(a, l1) => match l1 {
                                List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                  bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                    bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                      Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                    }), fn(x0) {
                                      match m {
                                        Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                        Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                      }
                                    })
                                  })
                                })
                                List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                              }
                            }
                            false => Result0::Err(Elab_error::EE_Unbound(q, g))
                          }
                        }
                      }
                    }
                    false => match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))) {
                      true => match a0 {
                        List::Nil => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                          true => match a0 {
                            List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                            List::Cons(a, l0) => match l0 {
                              List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                  bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                    Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                  }), fn(x0) {
                                    match m {
                                      Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                      Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                    }
                                  })
                                })
                              })
                              List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                            }
                          }
                          false => Result0::Err(Elab_error::EE_Unbound(q, g))
                        }
                        List::Cons(a, l0) => match l0 {
                          List::Nil => bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                            match m {
                              Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(x, Expr::EAbort(Ty::TBase(Base_ty::BUnit)))))
                              Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ELet(x, Expr::EAbort(_UU03c4_)))
                            }
                          })
                          List::Cons(s0, l1) => {
                            let a3 = List::Cons(a, List::Cons(s0, l1))
                            match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                              true => match a3 {
                                List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                List::Cons(a1, l2) => match l2 {
                                  List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                    bind(cres(e, l, _UU0393_, a1, Ty::TBase(Base_ty::BString), elab(e, a1, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                      bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                        Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                      }), fn(x0) {
                                        match m {
                                          Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                          Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a1, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                        }
                                      })
                                    })
                                  })
                                  List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                }
                              }
                              false => Result0::Err(Elab_error::EE_Unbound(q, g))
                            }
                          }
                        }
                      }
                      false => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                        true => match a0 {
                          List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                          List::Cons(a, l0) => match l0 {
                            List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                              bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                  Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                }), fn(x0) {
                                  match m {
                                    Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                    Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                  }
                                })
                              })
                            })
                            List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                          }
                        }
                        false => Result0::Err(Elab_error::EE_Unbound(q, g))
                      }
                    }
                  }
                  List::Cons(a, l0) => match l0 {
                    List::Nil => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), m, bind(elab(e, a, l, _UU0393_, Mode::Syn), fn(x) {
                      match x {
                        SigT::ExistT(_, s0) => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(s0, Expr::ELit(Lit::LUnit))))
                      }
                    }))
                    List::Cons(s0, l1) => {
                      let a1 = List::Cons(a, List::Cons(s0, l1))
                      match string_dec(g, String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::EmptyString)))))) {
                        true => match a1 {
                          List::Nil => match m {
                            Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::EAbort(Ty::TBase(Base_ty::BUnit))))
                            Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Nil), _UU03c4_, Expr::EAbort(_UU03c4_))
                          }
                          List::Cons(s1, l2) => {
                            let a2 = List::Cons(s1, l2)
                            match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))) {
                              true => match a2 {
                                List::Nil => {
                                  let a3 = List::Nil
                                  match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                    true => match a3 {
                                      List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                      List::Cons(a4, l3) => match l3 {
                                        List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                          bind(cres(e, l, _UU0393_, a4, Ty::TBase(Base_ty::BString), elab(e, a4, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                            bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                              Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                            }), fn(x0) {
                                              match m {
                                                Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                                Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a4, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                              }
                                            })
                                          })
                                        })
                                        List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                      }
                                    }
                                    false => Result0::Err(Elab_error::EE_Unbound(q, g))
                                  }
                                }
                                List::Cons(a3, l3) => match l3 {
                                  List::Nil => bind(cres(e, l, _UU0393_, a3, Ty::TBase(Base_ty::BString), elab(e, a3, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                    match m {
                                      Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(x, Expr::EAbort(Ty::TBase(Base_ty::BUnit)))))
                                      Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a3, List::Nil)), _UU03c4_, Expr::ELet(x, Expr::EAbort(_UU03c4_)))
                                    }
                                  })
                                  List::Cons(s2, l4) => {
                                    let a4 = List::Cons(a3, List::Cons(s2, l4))
                                    match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                      true => match a4 {
                                        List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                        List::Cons(a5, l5) => match l5 {
                                          List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                            bind(cres(e, l, _UU0393_, a5, Ty::TBase(Base_ty::BString), elab(e, a5, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                              bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                                Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                              }), fn(x0) {
                                                match m {
                                                  Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                                  Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a5, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                                }
                                              })
                                            })
                                          })
                                          List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                        }
                                      }
                                      false => Result0::Err(Elab_error::EE_Unbound(q, g))
                                    }
                                  }
                                }
                              }
                              false => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                true => match a2 {
                                  List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                  List::Cons(a3, l3) => match l3 {
                                    List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                      bind(cres(e, l, _UU0393_, a3, Ty::TBase(Base_ty::BString), elab(e, a3, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                        bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                          Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                        }), fn(x0) {
                                          match m {
                                            Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                            Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a3, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                          }
                                        })
                                      })
                                    })
                                    List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                  }
                                }
                                false => Result0::Err(Elab_error::EE_Unbound(q, g))
                              }
                            }
                          }
                        }
                        false => match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))) {
                          true => match a1 {
                            List::Nil => {
                              let a3 = List::Nil
                              match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                true => match a3 {
                                  List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                  List::Cons(a2, l2) => match l2 {
                                    List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                      bind(cres(e, l, _UU0393_, a2, Ty::TBase(Base_ty::BString), elab(e, a2, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                        bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                          Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                        }), fn(x0) {
                                          match m {
                                            Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                            Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a2, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                          }
                                        })
                                      })
                                    })
                                    List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                  }
                                }
                                false => Result0::Err(Elab_error::EE_Unbound(q, g))
                              }
                            }
                            List::Cons(a2, l2) => match l2 {
                              List::Nil => bind(cres(e, l, _UU0393_, a2, Ty::TBase(Base_ty::BString), elab(e, a2, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                match m {
                                  Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(x, Expr::EAbort(Ty::TBase(Base_ty::BUnit)))))
                                  Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a2, List::Nil)), _UU03c4_, Expr::ELet(x, Expr::EAbort(_UU03c4_)))
                                }
                              })
                              List::Cons(s1, l3) => {
                                let a3 = List::Cons(a2, List::Cons(s1, l3))
                                match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                  true => match a3 {
                                    List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                    List::Cons(a4, l4) => match l4 {
                                      List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                        bind(cres(e, l, _UU0393_, a4, Ty::TBase(Base_ty::BString), elab(e, a4, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                          bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                            Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                          }), fn(x0) {
                                            match m {
                                              Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                              Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a4, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                            }
                                          })
                                        })
                                      })
                                      List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                    }
                                  }
                                  false => Result0::Err(Elab_error::EE_Unbound(q, g))
                                }
                              }
                            }
                          }
                          false => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                            true => match a1 {
                              List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                              List::Cons(a2, l2) => match l2 {
                                List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                  bind(cres(e, l, _UU0393_, a2, Ty::TBase(Base_ty::BString), elab(e, a2, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                    bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                      Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                    }), fn(x0) {
                                      match m {
                                        Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                        Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a2, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                      }
                                    })
                                  })
                                })
                                List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                              }
                            }
                            false => Result0::Err(Elab_error::EE_Unbound(q, g))
                          }
                        }
                      }
                    }
                  }
                }
                false => match string_dec(g, String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::EmptyString)))))) {
                  true => match a0 {
                    List::Nil => match m {
                      Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::EAbort(Ty::TBase(Base_ty::BUnit))))
                      Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Nil), _UU03c4_, Expr::EAbort(_UU03c4_))
                    }
                    List::Cons(s0, l0) => {
                      let a2 = List::Cons(s0, l0)
                      match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))) {
                        true => match a2 {
                          List::Nil => {
                            let a3 = List::Nil
                            match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                              true => match a3 {
                                List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                List::Cons(a, l1) => match l1 {
                                  List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                    bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                      bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                        Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                      }), fn(x0) {
                                        match m {
                                          Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                          Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                        }
                                      })
                                    })
                                  })
                                  List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                }
                              }
                              false => Result0::Err(Elab_error::EE_Unbound(q, g))
                            }
                          }
                          List::Cons(a, l1) => match l1 {
                            List::Nil => bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                              match m {
                                Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(x, Expr::EAbort(Ty::TBase(Base_ty::BUnit)))))
                                Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ELet(x, Expr::EAbort(_UU03c4_)))
                              }
                            })
                            List::Cons(s1, l2) => {
                              let a3 = List::Cons(a, List::Cons(s1, l2))
                              match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                true => match a3 {
                                  List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                  List::Cons(a1, l3) => match l3 {
                                    List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                      bind(cres(e, l, _UU0393_, a1, Ty::TBase(Base_ty::BString), elab(e, a1, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                        bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                          Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                        }), fn(x0) {
                                          match m {
                                            Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                            Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a1, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                          }
                                        })
                                      })
                                    })
                                    List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                  }
                                }
                                false => Result0::Err(Elab_error::EE_Unbound(q, g))
                              }
                            }
                          }
                        }
                        false => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                          true => match a2 {
                            List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                            List::Cons(a, l1) => match l1 {
                              List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                  bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                    Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                  }), fn(x0) {
                                    match m {
                                      Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                      Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                    }
                                  })
                                })
                              })
                              List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                            }
                          }
                          false => Result0::Err(Elab_error::EE_Unbound(q, g))
                        }
                      }
                    }
                  }
                  false => match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))) {
                    true => match a0 {
                      List::Nil => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                        true => match a0 {
                          List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                          List::Cons(a, l0) => match l0 {
                            List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                              bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                  Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                }), fn(x0) {
                                  match m {
                                    Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                    Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                  }
                                })
                              })
                            })
                            List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                          }
                        }
                        false => Result0::Err(Elab_error::EE_Unbound(q, g))
                      }
                      List::Cons(a, l0) => match l0 {
                        List::Nil => bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                          match m {
                            Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(x, Expr::EAbort(Ty::TBase(Base_ty::BUnit)))))
                            Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ELet(x, Expr::EAbort(_UU03c4_)))
                          }
                        })
                        List::Cons(s0, l1) => {
                          let a3 = List::Cons(a, List::Cons(s0, l1))
                          match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                            true => match a3 {
                              List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                              List::Cons(a1, l2) => match l2 {
                                List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                  bind(cres(e, l, _UU0393_, a1, Ty::TBase(Base_ty::BString), elab(e, a1, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                    bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                      Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                    }), fn(x0) {
                                      match m {
                                        Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                        Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a1, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                      }
                                    })
                                  })
                                })
                                List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                              }
                            }
                            false => Result0::Err(Elab_error::EE_Unbound(q, g))
                          }
                        }
                      }
                    }
                    false => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                      true => match a0 {
                        List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                        List::Cons(a, l0) => match l0 {
                          List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                            bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                              bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                Cenv::Mk_cenv(_, ce_exn) => ce_exn
                              }), fn(x0) {
                                match m {
                                  Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                  Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                }
                              })
                            })
                          })
                          List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                        }
                      }
                      false => Result0::Err(Elab_error::EE_Unbound(q, g))
                    }
                  }
                }
              }
            }
            List::Cons(a, l0) => match l0 {
              List::Nil => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), m, bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BBool), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BBool)))), fn(x) {
                Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BBool), Expr::EPrim(Prim_op::PBoolNot, List::Cons(x, List::Nil))))
              }))
              List::Cons(s0, l1) => {
                let a0 = List::Cons(a, List::Cons(s0, l1))
                match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))) {
                  true => match a0 {
                    List::Nil => {
                      let a1 = List::Nil
                      match string_dec(g, String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::EmptyString)))))) {
                        true => match a1 {
                          List::Nil => match m {
                            Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::EAbort(Ty::TBase(Base_ty::BUnit))))
                            Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Nil), _UU03c4_, Expr::EAbort(_UU03c4_))
                          }
                          List::Cons(s1, l2) => {
                            let a2 = List::Cons(s1, l2)
                            match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))) {
                              true => match a2 {
                                List::Nil => {
                                  let a3 = List::Nil
                                  match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                    true => match a3 {
                                      List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                      List::Cons(a4, l3) => match l3 {
                                        List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                          bind(cres(e, l, _UU0393_, a4, Ty::TBase(Base_ty::BString), elab(e, a4, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                            bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                              Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                            }), fn(x0) {
                                              match m {
                                                Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                                Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a4, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                              }
                                            })
                                          })
                                        })
                                        List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                      }
                                    }
                                    false => Result0::Err(Elab_error::EE_Unbound(q, g))
                                  }
                                }
                                List::Cons(a3, l3) => match l3 {
                                  List::Nil => bind(cres(e, l, _UU0393_, a3, Ty::TBase(Base_ty::BString), elab(e, a3, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                    match m {
                                      Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(x, Expr::EAbort(Ty::TBase(Base_ty::BUnit)))))
                                      Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a3, List::Nil)), _UU03c4_, Expr::ELet(x, Expr::EAbort(_UU03c4_)))
                                    }
                                  })
                                  List::Cons(s2, l4) => {
                                    let a4 = List::Cons(a3, List::Cons(s2, l4))
                                    match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                      true => match a4 {
                                        List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                        List::Cons(a5, l5) => match l5 {
                                          List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                            bind(cres(e, l, _UU0393_, a5, Ty::TBase(Base_ty::BString), elab(e, a5, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                              bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                                Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                              }), fn(x0) {
                                                match m {
                                                  Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                                  Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a5, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                                }
                                              })
                                            })
                                          })
                                          List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                        }
                                      }
                                      false => Result0::Err(Elab_error::EE_Unbound(q, g))
                                    }
                                  }
                                }
                              }
                              false => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                true => match a2 {
                                  List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                  List::Cons(a3, l3) => match l3 {
                                    List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                      bind(cres(e, l, _UU0393_, a3, Ty::TBase(Base_ty::BString), elab(e, a3, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                        bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                          Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                        }), fn(x0) {
                                          match m {
                                            Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                            Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a3, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                          }
                                        })
                                      })
                                    })
                                    List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                  }
                                }
                                false => Result0::Err(Elab_error::EE_Unbound(q, g))
                              }
                            }
                          }
                        }
                        false => match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))) {
                          true => match a1 {
                            List::Nil => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                              true => match a1 {
                                List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                List::Cons(a2, l2) => match l2 {
                                  List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                    bind(cres(e, l, _UU0393_, a2, Ty::TBase(Base_ty::BString), elab(e, a2, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                      bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                        Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                      }), fn(x0) {
                                        match m {
                                          Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                          Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a2, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                        }
                                      })
                                    })
                                  })
                                  List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                }
                              }
                              false => Result0::Err(Elab_error::EE_Unbound(q, g))
                            }
                            List::Cons(a2, l2) => match l2 {
                              List::Nil => bind(cres(e, l, _UU0393_, a2, Ty::TBase(Base_ty::BString), elab(e, a2, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                match m {
                                  Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(x, Expr::EAbort(Ty::TBase(Base_ty::BUnit)))))
                                  Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a2, List::Nil)), _UU03c4_, Expr::ELet(x, Expr::EAbort(_UU03c4_)))
                                }
                              })
                              List::Cons(s1, l3) => {
                                let a3 = List::Cons(a2, List::Cons(s1, l3))
                                match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                  true => match a3 {
                                    List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                    List::Cons(a4, l4) => match l4 {
                                      List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                        bind(cres(e, l, _UU0393_, a4, Ty::TBase(Base_ty::BString), elab(e, a4, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                          bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                            Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                          }), fn(x0) {
                                            match m {
                                              Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                              Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a4, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                            }
                                          })
                                        })
                                      })
                                      List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                    }
                                  }
                                  false => Result0::Err(Elab_error::EE_Unbound(q, g))
                                }
                              }
                            }
                          }
                          false => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                            true => match a1 {
                              List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                              List::Cons(a2, l2) => match l2 {
                                List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                  bind(cres(e, l, _UU0393_, a2, Ty::TBase(Base_ty::BString), elab(e, a2, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                    bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                      Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                    }), fn(x0) {
                                      match m {
                                        Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                        Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a2, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                      }
                                    })
                                  })
                                })
                                List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                              }
                            }
                            false => Result0::Err(Elab_error::EE_Unbound(q, g))
                          }
                        }
                      }
                    }
                    List::Cons(a1, l2) => match l2 {
                      List::Nil => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a1, List::Nil)), m, bind(elab(e, a1, l, _UU0393_, Mode::Syn), fn(x) {
                        match x {
                          SigT::ExistT(_, s1) => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(s1, Expr::ELit(Lit::LUnit))))
                        }
                      }))
                      List::Cons(s1, l3) => {
                        let a2 = List::Cons(a1, List::Cons(s1, l3))
                        match string_dec(g, String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::EmptyString)))))) {
                          true => match a2 {
                            List::Nil => match m {
                              Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::EAbort(Ty::TBase(Base_ty::BUnit))))
                              Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Nil), _UU03c4_, Expr::EAbort(_UU03c4_))
                            }
                            List::Cons(s2, l4) => {
                              let a3 = List::Cons(s2, l4)
                              match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))) {
                                true => match a3 {
                                  List::Nil => {
                                    let a4 = List::Nil
                                    match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                      true => match a4 {
                                        List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                        List::Cons(a5, l5) => match l5 {
                                          List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                            bind(cres(e, l, _UU0393_, a5, Ty::TBase(Base_ty::BString), elab(e, a5, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                              bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                                Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                              }), fn(x0) {
                                                match m {
                                                  Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                                  Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a5, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                                }
                                              })
                                            })
                                          })
                                          List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                        }
                                      }
                                      false => Result0::Err(Elab_error::EE_Unbound(q, g))
                                    }
                                  }
                                  List::Cons(a4, l5) => match l5 {
                                    List::Nil => bind(cres(e, l, _UU0393_, a4, Ty::TBase(Base_ty::BString), elab(e, a4, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                      match m {
                                        Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(x, Expr::EAbort(Ty::TBase(Base_ty::BUnit)))))
                                        Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a4, List::Nil)), _UU03c4_, Expr::ELet(x, Expr::EAbort(_UU03c4_)))
                                      }
                                    })
                                    List::Cons(s3, l6) => {
                                      let a5 = List::Cons(a4, List::Cons(s3, l6))
                                      match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                        true => match a5 {
                                          List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                          List::Cons(a6, l7) => match l7 {
                                            List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                              bind(cres(e, l, _UU0393_, a6, Ty::TBase(Base_ty::BString), elab(e, a6, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                                bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                                  Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                                }), fn(x0) {
                                                  match m {
                                                    Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                                    Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a6, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                                  }
                                                })
                                              })
                                            })
                                            List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                          }
                                        }
                                        false => Result0::Err(Elab_error::EE_Unbound(q, g))
                                      }
                                    }
                                  }
                                }
                                false => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                  true => match a3 {
                                    List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                    List::Cons(a4, l5) => match l5 {
                                      List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                        bind(cres(e, l, _UU0393_, a4, Ty::TBase(Base_ty::BString), elab(e, a4, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                          bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                            Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                          }), fn(x0) {
                                            match m {
                                              Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                              Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a4, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                            }
                                          })
                                        })
                                      })
                                      List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                    }
                                  }
                                  false => Result0::Err(Elab_error::EE_Unbound(q, g))
                                }
                              }
                            }
                          }
                          false => match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))) {
                            true => match a2 {
                              List::Nil => {
                                let a3 = List::Nil
                                match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                  true => match a3 {
                                    List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                    List::Cons(a4, l4) => match l4 {
                                      List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                        bind(cres(e, l, _UU0393_, a4, Ty::TBase(Base_ty::BString), elab(e, a4, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                          bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                            Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                          }), fn(x0) {
                                            match m {
                                              Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                              Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a4, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                            }
                                          })
                                        })
                                      })
                                      List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                    }
                                  }
                                  false => Result0::Err(Elab_error::EE_Unbound(q, g))
                                }
                              }
                              List::Cons(a3, l4) => match l4 {
                                List::Nil => bind(cres(e, l, _UU0393_, a3, Ty::TBase(Base_ty::BString), elab(e, a3, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                  match m {
                                    Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(x, Expr::EAbort(Ty::TBase(Base_ty::BUnit)))))
                                    Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a3, List::Nil)), _UU03c4_, Expr::ELet(x, Expr::EAbort(_UU03c4_)))
                                  }
                                })
                                List::Cons(s2, l5) => {
                                  let a4 = List::Cons(a3, List::Cons(s2, l5))
                                  match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                    true => match a4 {
                                      List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                      List::Cons(a5, l6) => match l6 {
                                        List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                          bind(cres(e, l, _UU0393_, a5, Ty::TBase(Base_ty::BString), elab(e, a5, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                            bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                              Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                            }), fn(x0) {
                                              match m {
                                                Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                                Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a5, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                              }
                                            })
                                          })
                                        })
                                        List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                      }
                                    }
                                    false => Result0::Err(Elab_error::EE_Unbound(q, g))
                                  }
                                }
                              }
                            }
                            false => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                              true => match a2 {
                                List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                List::Cons(a3, l4) => match l4 {
                                  List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                    bind(cres(e, l, _UU0393_, a3, Ty::TBase(Base_ty::BString), elab(e, a3, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                      bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                        Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                      }), fn(x0) {
                                        match m {
                                          Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                          Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a3, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                        }
                                      })
                                    })
                                  })
                                  List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                }
                              }
                              false => Result0::Err(Elab_error::EE_Unbound(q, g))
                            }
                          }
                        }
                      }
                    }
                  }
                  false => match string_dec(g, String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::EmptyString)))))) {
                    true => match a0 {
                      List::Nil => match m {
                        Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::EAbort(Ty::TBase(Base_ty::BUnit))))
                        Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Nil), _UU03c4_, Expr::EAbort(_UU03c4_))
                      }
                      List::Cons(s1, l2) => {
                        let a2 = List::Cons(s1, l2)
                        match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))) {
                          true => match a2 {
                            List::Nil => {
                              let a3 = List::Nil
                              match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                true => match a3 {
                                  List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                  List::Cons(a1, l3) => match l3 {
                                    List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                      bind(cres(e, l, _UU0393_, a1, Ty::TBase(Base_ty::BString), elab(e, a1, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                        bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                          Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                        }), fn(x0) {
                                          match m {
                                            Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                            Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a1, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                          }
                                        })
                                      })
                                    })
                                    List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                  }
                                }
                                false => Result0::Err(Elab_error::EE_Unbound(q, g))
                              }
                            }
                            List::Cons(a1, l3) => match l3 {
                              List::Nil => bind(cres(e, l, _UU0393_, a1, Ty::TBase(Base_ty::BString), elab(e, a1, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                match m {
                                  Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(x, Expr::EAbort(Ty::TBase(Base_ty::BUnit)))))
                                  Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a1, List::Nil)), _UU03c4_, Expr::ELet(x, Expr::EAbort(_UU03c4_)))
                                }
                              })
                              List::Cons(s2, l4) => {
                                let a3 = List::Cons(a1, List::Cons(s2, l4))
                                match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                  true => match a3 {
                                    List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                    List::Cons(a4, l5) => match l5 {
                                      List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                        bind(cres(e, l, _UU0393_, a4, Ty::TBase(Base_ty::BString), elab(e, a4, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                          bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                            Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                          }), fn(x0) {
                                            match m {
                                              Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                              Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a4, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                            }
                                          })
                                        })
                                      })
                                      List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                    }
                                  }
                                  false => Result0::Err(Elab_error::EE_Unbound(q, g))
                                }
                              }
                            }
                          }
                          false => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                            true => match a2 {
                              List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                              List::Cons(a1, l3) => match l3 {
                                List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                  bind(cres(e, l, _UU0393_, a1, Ty::TBase(Base_ty::BString), elab(e, a1, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                    bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                      Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                    }), fn(x0) {
                                      match m {
                                        Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                        Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a1, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                      }
                                    })
                                  })
                                })
                                List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                              }
                            }
                            false => Result0::Err(Elab_error::EE_Unbound(q, g))
                          }
                        }
                      }
                    }
                    false => match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))) {
                      true => match a0 {
                        List::Nil => {
                          let a3 = List::Nil
                          match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                            true => match a3 {
                              List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                              List::Cons(a1, l2) => match l2 {
                                List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                  bind(cres(e, l, _UU0393_, a1, Ty::TBase(Base_ty::BString), elab(e, a1, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                    bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                      Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                    }), fn(x0) {
                                      match m {
                                        Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                        Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a1, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                      }
                                    })
                                  })
                                })
                                List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                              }
                            }
                            false => Result0::Err(Elab_error::EE_Unbound(q, g))
                          }
                        }
                        List::Cons(a1, l2) => match l2 {
                          List::Nil => bind(cres(e, l, _UU0393_, a1, Ty::TBase(Base_ty::BString), elab(e, a1, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                            match m {
                              Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(x, Expr::EAbort(Ty::TBase(Base_ty::BUnit)))))
                              Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a1, List::Nil)), _UU03c4_, Expr::ELet(x, Expr::EAbort(_UU03c4_)))
                            }
                          })
                          List::Cons(s1, l3) => {
                            let a3 = List::Cons(a1, List::Cons(s1, l3))
                            match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                              true => match a3 {
                                List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                List::Cons(a2, l4) => match l4 {
                                  List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                    bind(cres(e, l, _UU0393_, a2, Ty::TBase(Base_ty::BString), elab(e, a2, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                      bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                        Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                      }), fn(x0) {
                                        match m {
                                          Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                          Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a2, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                        }
                                      })
                                    })
                                  })
                                  List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                }
                              }
                              false => Result0::Err(Elab_error::EE_Unbound(q, g))
                            }
                          }
                        }
                      }
                      false => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                        true => match a0 {
                          List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                          List::Cons(a1, l2) => match l2 {
                            List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                              bind(cres(e, l, _UU0393_, a1, Ty::TBase(Base_ty::BString), elab(e, a1, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                  Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                }), fn(x0) {
                                  match m {
                                    Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                    Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a1, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                  }
                                })
                              })
                            })
                            List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                          }
                        }
                        false => Result0::Err(Elab_error::EE_Unbound(q, g))
                      }
                    }
                  }
                }
              }
            }
          }
          false => match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))) {
            true => match args {
              List::Nil => {
                let a1 = List::Nil
                match string_dec(g, String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::EmptyString)))))) {
                  true => match a1 {
                    List::Nil => match m {
                      Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::EAbort(Ty::TBase(Base_ty::BUnit))))
                      Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Nil), _UU03c4_, Expr::EAbort(_UU03c4_))
                    }
                    List::Cons(s0, l0) => {
                      let a2 = List::Cons(s0, l0)
                      match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))) {
                        true => match a2 {
                          List::Nil => {
                            let a3 = List::Nil
                            match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                              true => match a3 {
                                List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                List::Cons(a, l1) => match l1 {
                                  List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                    bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                      bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                        Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                      }), fn(x0) {
                                        match m {
                                          Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                          Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                        }
                                      })
                                    })
                                  })
                                  List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                }
                              }
                              false => Result0::Err(Elab_error::EE_Unbound(q, g))
                            }
                          }
                          List::Cons(a, l1) => match l1 {
                            List::Nil => bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                              match m {
                                Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(x, Expr::EAbort(Ty::TBase(Base_ty::BUnit)))))
                                Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ELet(x, Expr::EAbort(_UU03c4_)))
                              }
                            })
                            List::Cons(s1, l2) => {
                              let a3 = List::Cons(a, List::Cons(s1, l2))
                              match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                true => match a3 {
                                  List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                  List::Cons(a0, l3) => match l3 {
                                    List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                      bind(cres(e, l, _UU0393_, a0, Ty::TBase(Base_ty::BString), elab(e, a0, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                        bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                          Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                        }), fn(x0) {
                                          match m {
                                            Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                            Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a0, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                          }
                                        })
                                      })
                                    })
                                    List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                  }
                                }
                                false => Result0::Err(Elab_error::EE_Unbound(q, g))
                              }
                            }
                          }
                        }
                        false => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                          true => match a2 {
                            List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                            List::Cons(a, l1) => match l1 {
                              List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                  bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                    Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                  }), fn(x0) {
                                    match m {
                                      Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                      Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                    }
                                  })
                                })
                              })
                              List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                            }
                          }
                          false => Result0::Err(Elab_error::EE_Unbound(q, g))
                        }
                      }
                    }
                  }
                  false => match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))) {
                    true => match a1 {
                      List::Nil => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                        true => match a1 {
                          List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                          List::Cons(a, l0) => match l0 {
                            List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                              bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                  Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                }), fn(x0) {
                                  match m {
                                    Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                    Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                  }
                                })
                              })
                            })
                            List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                          }
                        }
                        false => Result0::Err(Elab_error::EE_Unbound(q, g))
                      }
                      List::Cons(a, l0) => match l0 {
                        List::Nil => bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                          match m {
                            Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(x, Expr::EAbort(Ty::TBase(Base_ty::BUnit)))))
                            Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ELet(x, Expr::EAbort(_UU03c4_)))
                          }
                        })
                        List::Cons(s0, l1) => {
                          let a3 = List::Cons(a, List::Cons(s0, l1))
                          match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                            true => match a3 {
                              List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                              List::Cons(a0, l2) => match l2 {
                                List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                  bind(cres(e, l, _UU0393_, a0, Ty::TBase(Base_ty::BString), elab(e, a0, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                    bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                      Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                    }), fn(x0) {
                                      match m {
                                        Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                        Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a0, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                      }
                                    })
                                  })
                                })
                                List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                              }
                            }
                            false => Result0::Err(Elab_error::EE_Unbound(q, g))
                          }
                        }
                      }
                    }
                    false => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                      true => match a1 {
                        List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                        List::Cons(a, l0) => match l0 {
                          List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                            bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                              bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                Cenv::Mk_cenv(_, ce_exn) => ce_exn
                              }), fn(x0) {
                                match m {
                                  Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                  Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                }
                              })
                            })
                          })
                          List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                        }
                      }
                      false => Result0::Err(Elab_error::EE_Unbound(q, g))
                    }
                  }
                }
              }
              List::Cons(a, l0) => match l0 {
                List::Nil => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), m, bind(elab(e, a, l, _UU0393_, Mode::Syn), fn(x) {
                  match x {
                    SigT::ExistT(_, s0) => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(s0, Expr::ELit(Lit::LUnit))))
                  }
                }))
                List::Cons(s0, l1) => {
                  let a1 = List::Cons(a, List::Cons(s0, l1))
                  match string_dec(g, String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::EmptyString)))))) {
                    true => match a1 {
                      List::Nil => match m {
                        Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::EAbort(Ty::TBase(Base_ty::BUnit))))
                        Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Nil), _UU03c4_, Expr::EAbort(_UU03c4_))
                      }
                      List::Cons(s1, l2) => {
                        let a2 = List::Cons(s1, l2)
                        match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))) {
                          true => match a2 {
                            List::Nil => {
                              let a3 = List::Nil
                              match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                true => match a3 {
                                  List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                  List::Cons(a0, l3) => match l3 {
                                    List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                      bind(cres(e, l, _UU0393_, a0, Ty::TBase(Base_ty::BString), elab(e, a0, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                        bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                          Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                        }), fn(x0) {
                                          match m {
                                            Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                            Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a0, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                          }
                                        })
                                      })
                                    })
                                    List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                  }
                                }
                                false => Result0::Err(Elab_error::EE_Unbound(q, g))
                              }
                            }
                            List::Cons(a0, l3) => match l3 {
                              List::Nil => bind(cres(e, l, _UU0393_, a0, Ty::TBase(Base_ty::BString), elab(e, a0, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                match m {
                                  Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(x, Expr::EAbort(Ty::TBase(Base_ty::BUnit)))))
                                  Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a0, List::Nil)), _UU03c4_, Expr::ELet(x, Expr::EAbort(_UU03c4_)))
                                }
                              })
                              List::Cons(s2, l4) => {
                                let a3 = List::Cons(a0, List::Cons(s2, l4))
                                match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                                  true => match a3 {
                                    List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                    List::Cons(a4, l5) => match l5 {
                                      List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                        bind(cres(e, l, _UU0393_, a4, Ty::TBase(Base_ty::BString), elab(e, a4, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                          bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                            Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                          }), fn(x0) {
                                            match m {
                                              Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                              Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a4, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                            }
                                          })
                                        })
                                      })
                                      List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                    }
                                  }
                                  false => Result0::Err(Elab_error::EE_Unbound(q, g))
                                }
                              }
                            }
                          }
                          false => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                            true => match a2 {
                              List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                              List::Cons(a0, l3) => match l3 {
                                List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                  bind(cres(e, l, _UU0393_, a0, Ty::TBase(Base_ty::BString), elab(e, a0, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                    bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                      Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                    }), fn(x0) {
                                      match m {
                                        Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                        Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a0, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                      }
                                    })
                                  })
                                })
                                List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                              }
                            }
                            false => Result0::Err(Elab_error::EE_Unbound(q, g))
                          }
                        }
                      }
                    }
                    false => match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))) {
                      true => match a1 {
                        List::Nil => {
                          let a3 = List::Nil
                          match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                            true => match a3 {
                              List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                              List::Cons(a0, l2) => match l2 {
                                List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                  bind(cres(e, l, _UU0393_, a0, Ty::TBase(Base_ty::BString), elab(e, a0, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                    bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                      Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                    }), fn(x0) {
                                      match m {
                                        Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                        Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a0, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                      }
                                    })
                                  })
                                })
                                List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                              }
                            }
                            false => Result0::Err(Elab_error::EE_Unbound(q, g))
                          }
                        }
                        List::Cons(a0, l2) => match l2 {
                          List::Nil => bind(cres(e, l, _UU0393_, a0, Ty::TBase(Base_ty::BString), elab(e, a0, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                            match m {
                              Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(x, Expr::EAbort(Ty::TBase(Base_ty::BUnit)))))
                              Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a0, List::Nil)), _UU03c4_, Expr::ELet(x, Expr::EAbort(_UU03c4_)))
                            }
                          })
                          List::Cons(s1, l3) => {
                            let a3 = List::Cons(a0, List::Cons(s1, l3))
                            match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                              true => match a3 {
                                List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                                List::Cons(a2, l4) => match l4 {
                                  List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                    bind(cres(e, l, _UU0393_, a2, Ty::TBase(Base_ty::BString), elab(e, a2, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                      bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                        Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                      }), fn(x0) {
                                        match m {
                                          Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                          Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a2, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                        }
                                      })
                                    })
                                  })
                                  List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                                }
                              }
                              false => Result0::Err(Elab_error::EE_Unbound(q, g))
                            }
                          }
                        }
                      }
                      false => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                        true => match a1 {
                          List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                          List::Cons(a0, l2) => match l2 {
                            List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                              bind(cres(e, l, _UU0393_, a0, Ty::TBase(Base_ty::BString), elab(e, a0, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                  Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                }), fn(x0) {
                                  match m {
                                    Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                    Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a0, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                  }
                                })
                              })
                            })
                            List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                          }
                        }
                        false => Result0::Err(Elab_error::EE_Unbound(q, g))
                      }
                    }
                  }
                }
              }
            }
            false => match string_dec(g, String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::EmptyString)))))) {
              true => match args {
                List::Nil => match m {
                  Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::EAbort(Ty::TBase(Base_ty::BUnit))))
                  Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Nil), _UU03c4_, Expr::EAbort(_UU03c4_))
                }
                List::Cons(s0, l0) => {
                  let a2 = List::Cons(s0, l0)
                  match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))) {
                    true => match a2 {
                      List::Nil => {
                        let a3 = List::Nil
                        match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                          true => match a3 {
                            List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                            List::Cons(a, l1) => match l1 {
                              List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                  bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                    Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                  }), fn(x0) {
                                    match m {
                                      Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                      Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                    }
                                  })
                                })
                              })
                              List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                            }
                          }
                          false => Result0::Err(Elab_error::EE_Unbound(q, g))
                        }
                      }
                      List::Cons(a, l1) => match l1 {
                        List::Nil => bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                          match m {
                            Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(x, Expr::EAbort(Ty::TBase(Base_ty::BUnit)))))
                            Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ELet(x, Expr::EAbort(_UU03c4_)))
                          }
                        })
                        List::Cons(s1, l2) => {
                          let a3 = List::Cons(a, List::Cons(s1, l2))
                          match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                            true => match a3 {
                              List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                              List::Cons(a0, l3) => match l3 {
                                List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                                  bind(cres(e, l, _UU0393_, a0, Ty::TBase(Base_ty::BString), elab(e, a0, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                    bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                      Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                    }), fn(x0) {
                                      match m {
                                        Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                        Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a0, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                      }
                                    })
                                  })
                                })
                                List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                              }
                            }
                            false => Result0::Err(Elab_error::EE_Unbound(q, g))
                          }
                        }
                      }
                    }
                    false => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                      true => match a2 {
                        List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                        List::Cons(a, l1) => match l1 {
                          List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                            bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                              bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                Cenv::Mk_cenv(_, ce_exn) => ce_exn
                              }), fn(x0) {
                                match m {
                                  Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                  Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                }
                              })
                            })
                          })
                          List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                        }
                      }
                      false => Result0::Err(Elab_error::EE_Unbound(q, g))
                    }
                  }
                }
              }
              false => match string_dec(g, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))) {
                true => match args {
                  List::Nil => {
                    let a3 = List::Nil
                    match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                      true => match a3 {
                        List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                        List::Cons(a, l0) => match l0 {
                          List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                            bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                              bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                Cenv::Mk_cenv(_, ce_exn) => ce_exn
                              }), fn(x0) {
                                match m {
                                  Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                  Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                }
                              })
                            })
                          })
                          List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                        }
                      }
                      false => Result0::Err(Elab_error::EE_Unbound(q, g))
                    }
                  }
                  List::Cons(a, l0) => match l0 {
                    List::Nil => bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                      match m {
                        Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(x, Expr::EAbort(Ty::TBase(Base_ty::BUnit)))))
                        Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ELet(x, Expr::EAbort(_UU03c4_)))
                      }
                    })
                    List::Cons(s0, l1) => {
                      let a3 = List::Cons(a, List::Cons(s0, l1))
                      match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                        true => match a3 {
                          List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                          List::Cons(a0, l2) => match l2 {
                            List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                              bind(cres(e, l, _UU0393_, a0, Ty::TBase(Base_ty::BString), elab(e, a0, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                                bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                                  Cenv::Mk_cenv(_, ce_exn) => ce_exn
                                }), fn(x0) {
                                  match m {
                                    Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                                    Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a0, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                                  }
                                })
                              })
                            })
                            List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                          }
                        }
                        false => Result0::Err(Elab_error::EE_Unbound(q, g))
                      }
                    }
                  }
                }
                false => match string_dec(g, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))))) {
                  true => match args {
                    List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                    List::Cons(a, l0) => match l0 {
                      List::Nil => bind(failure_ok_dec(e, q), fn(_) {
                        bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BString), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BString)))), fn(x) {
                          bind(coerce(e, q, _UU0393_, fail_val(x), Ty::TData(String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), List::Nil), match l {
                            Cenv::Mk_cenv(_, ce_exn) => ce_exn
                          }), fn(x0) {
                            match m {
                              Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x0, Ty::TBase(Base_ty::BUnit))))
                              Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(a, List::Nil)), _UU03c4_, Expr::ERaise(x0, _UU03c4_))
                            }
                          })
                        })
                      })
                      List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                    }
                  }
                  false => Result0::Err(Elab_error::EE_Unbound(q, g))
                }
              }
            }
          }
        }
      }
      Head0::HExpr => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, args), m, bind(elab(e, f, l, _UU0393_, Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(_UU03c4_f, s0) => match _UU03c4_f {
            Ty::TArrow(ps, r, _UU03b5_) => bind(chk_list(e, p, l, _UU0393_, fn(s_) {
              fn(_UU03c4__) {
                cres(e, l, _UU0393_, s_, _UU03c4__, elab(e, s_, l, _UU0393_, Mode::Chk(_UU03c4__)))
              }
            }, args, ps), fn(x0) {
              bind(allowed_dec(e, p, _UU03b5_, match l {
                Cenv::Mk_cenv(_, ce_exn) => ce_exn
              }), fn(_) { Result0::Ok(SigT::ExistT(r, wrap_call(l, _UU03b5_, r, s0, x0))) })
            })
            _ => Result0::Err(Elab_error::EE_Type(p, Type_error::E_NotFunction(_UU03c4_f)))
          }
        }
      }))
      Head0::HCtor(q, tq, c) => {
        let syn_c = bind(ctor_pick_dec(e, q, tq, c), fn(x) {
          bind(of_option(lookup_ty(match e {
            Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
          }, x), Elab_error::EE_UnknownType(q, x)), fn(x0) {
            bind(of_option(lookup_ctor(x0, c), Elab_error::EE_UnknownCtor(q, c)), fn(x1) {
              let ps = match x1 {
                Cdef::Mk_cdef(_, cd_fields) => cd_fields
              }
              bind(bcheck(eqb0(length(args), length(ps)), Elab_error::EE_CtorArity(q, c, length(ps), length(args))), fn(_) {
                bind(pass1(e, fn(x5) { fn(x2) { fn(x3) { fn(x4) { elab(e, x5, x2, x3, x4) } } } }, l, _UU0393_, args, ps, repeat(None, match x0 {
                  Tdef::Mk_tdef(_, td_tparams, _, _) => td_tparams
                })), fn(x2) {
                  match x2 {
                    (a, st1) => bind(pass2(e, fn(x6) { fn(x5) { fn(x3) { fn(x4) { elab(e, x6, x5, x3, x4) } } } }, l, _UU0393_, args, a, ps, st1), fn(x3) {
                      match x3 {
                        (a0, st2) => bind(targs(q, c, match x0 {
                          Tdef::Mk_tdef(_, td_tparams, _, _) => td_tparams
                        }, st2), fn(x4) {
                          bind(finish(e, p, l, _UU0393_, args, a0, map({ let a1 = fn(x5) { inst(x4, x5) }; fn(x5) { tsubst(a1, x5) } }, ps)), fn(x5) {
                            Result0::Ok(SigT::ExistT(Ty::TData(x, x4), Expr::EConstr(x, c, x4, Expr::ETuple(x5))))
                          })
                        })
                      }
                    })
                  }
                })
              })
            })
          })
        })
        match m {
          Mode::Syn => syn_c
          Mode::Chk(_UU03c4_) => match _UU03c4_ {
            Ty::TData(t, ts) => match lookup_ty(match e {
              Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
            }, t) {
              Some(td) => match lookup_ctor(td, c) {
                Some(cd) => bind(tq_dec(q, tq, t, Elab_error::EE_UnknownCtor(q, c)), fn(_) {
                  bind(match eq_dec(length(ts), match td {
                    Tdef::Mk_tdef(_, td_tparams, _, _) => td_tparams
                  }) {
                    true => Result0::Ok(())
                    false => Result0::Err(Elab_error::EE_TypeArgs(q, t, match td {
                      Tdef::Mk_tdef(_, td_tparams, _, _) => td_tparams
                    }, length(ts)))
                  }, fn(_) {
                    bind(bcheck(eqb0(length(args), length(match cd {
                      Cdef::Mk_cdef(_, cd_fields) => cd_fields
                    })), Elab_error::EE_CtorArity(q, c, length(match cd {
                      Cdef::Mk_cdef(_, cd_fields) => cd_fields
                    }), length(args))), fn(_) {
                      bind(chk_list(e, p, l, _UU0393_, fn(s_) {
                        fn(_UU03c4__) {
                          cres(e, l, _UU0393_, s_, _UU03c4__, elab(e, s_, l, _UU0393_, Mode::Chk(_UU03c4__)))
                        }
                      }, args, map({ let a1 = fn(x1) { inst(ts, x1) }; fn(x1) { tsubst(a1, x1) } }, match cd {
                        Cdef::Mk_cdef(_, cd_fields) => cd_fields
                      })), fn(x) {
                        okc(e, l, _UU0393_, Sexpr::SApp(p, f, args), Ty::TData(t, ts), Expr::EConstr(t, c, ts, Expr::ETuple(x)))
                      })
                    })
                  })
                })
                None => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, args), Mode::Chk(Ty::TData(t, ts)), syn_c)
              }
              None => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, args), Mode::Chk(Ty::TData(t, ts)), syn_c)
            }
            x => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, args), Mode::Chk(x), syn_c)
          }
        }
      }
      Head0::HQual(q, t, mn) => match qual_builtin(t, mn, length(args)) {
        true => match string_dec(t, String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString)))) {
          true => match string_dec(mn, String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, true, true, true, false), String0::EmptyString)))) {
            true => match args {
              List::Nil => {
                let a0 = List::Nil
                match array_kind_of(t) {
                  Some(k) => match string_dec(mn, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))) {
                    true => match string_dec(mn, String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, true, true, true, false), String0::EmptyString)))) {
                      true => match a0 {
                        List::Nil => match m {
                          Mode::Syn => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                          Mode::Chk(_UU03c4_) => match _UU03c4_ {
                            Ty::TArray(k_, t0) => match array_kind_eq_dec(k, k_) {
                              true => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Nil), Ty::TArray(k_, t0), Expr::EMem(Mem_op::MArray(k, t0, Nat::O), List::Nil))
                              false => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                            }
                            _ => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                          }
                        }
                        List::Cons(n, l0) => match l0 {
                          List::Nil => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                          List::Cons(v, l1) => match l1 {
                            List::Nil => bind(cres(e, l, _UU0393_, n, Ty::TBase(Base_ty::BInt(Int_kind::I32)), elab(e, n, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BInt(Int_kind::I32))))), fn(x) {
                              let syn_m = bind(elab(e, v, l, _UU0393_, Mode::Syn), fn(x0) {
                                match x0 {
                                  SigT::ExistT(t0, s0) => Result0::Ok(SigT::ExistT(Ty::TArray(k, t0), Expr::EMem(Mem_op::MMake(k, t0), List::Cons(x, List::Cons(s0, List::Nil)))))
                                }
                              })
                              match m {
                                Mode::Syn => syn_m
                                Mode::Chk(_UU03c4_) => match _UU03c4_ {
                                  Ty::TArray(k_, t0) => match array_kind_eq_dec(k, k_) {
                                    true => bind(cres(e, l, _UU0393_, v, t0, elab(e, v, l, _UU0393_, Mode::Chk(t0))), fn(x0) {
                                      okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v, List::Nil))), Ty::TArray(k_, t0), Expr::EMem(Mem_op::MMake(k, t0), List::Cons(x, List::Cons(x0, List::Nil))))
                                    })
                                    false => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v, List::Nil))), Mode::Chk(Ty::TArray(k_, t0)), syn_m)
                                  }
                                  x0 => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v, List::Nil))), Mode::Chk(x0), syn_m)
                                }
                              }
                            })
                            List::Cons(_, _) => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                          }
                        }
                      }
                      false => match a0 {
                        List::Nil => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                        List::Cons(n, l0) => match l0 {
                          List::Nil => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                          List::Cons(v, l1) => match l1 {
                            List::Nil => bind(cres(e, l, _UU0393_, n, Ty::TBase(Base_ty::BInt(Int_kind::I32)), elab(e, n, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BInt(Int_kind::I32))))), fn(x) {
                              let syn_m = bind(elab(e, v, l, _UU0393_, Mode::Syn), fn(x0) {
                                match x0 {
                                  SigT::ExistT(t0, s0) => Result0::Ok(SigT::ExistT(Ty::TArray(k, t0), Expr::EMem(Mem_op::MMake(k, t0), List::Cons(x, List::Cons(s0, List::Nil)))))
                                }
                              })
                              match m {
                                Mode::Syn => syn_m
                                Mode::Chk(_UU03c4_) => match _UU03c4_ {
                                  Ty::TArray(k_, t0) => match array_kind_eq_dec(k, k_) {
                                    true => bind(cres(e, l, _UU0393_, v, t0, elab(e, v, l, _UU0393_, Mode::Chk(t0))), fn(x0) {
                                      okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v, List::Nil))), Ty::TArray(k_, t0), Expr::EMem(Mem_op::MMake(k, t0), List::Cons(x, List::Cons(x0, List::Nil))))
                                    })
                                    false => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v, List::Nil))), Mode::Chk(Ty::TArray(k_, t0)), syn_m)
                                  }
                                  x0 => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v, List::Nil))), Mode::Chk(x0), syn_m)
                                }
                              }
                            })
                            List::Cons(_, _) => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                          }
                        }
                      }
                    }
                    false => match string_dec(mn, String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, true, true, true, false), String0::EmptyString)))) {
                      true => match a0 {
                        List::Nil => match m {
                          Mode::Syn => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                          Mode::Chk(_UU03c4_) => match _UU03c4_ {
                            Ty::TArray(k_, t0) => match array_kind_eq_dec(k, k_) {
                              true => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Nil), Ty::TArray(k_, t0), Expr::EMem(Mem_op::MArray(k, t0, Nat::O), List::Nil))
                              false => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                            }
                            _ => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                          }
                        }
                        List::Cons(_, _) => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                      }
                      false => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                    }
                  }
                  None => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                }
              }
              List::Cons(v, l0) => match l0 {
                List::Nil => bind(ref_ok_dec(e, q), fn(_) {
                  match m {
                    Mode::Syn => bind(elab(e, v, l, _UU0393_, Mode::Syn), fn(x) {
                      match x {
                        SigT::ExistT(t0, s0) => Result0::Ok(SigT::ExistT(Ty::TData(String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString))), List::Cons(t0, List::Nil)), Expr::EConstr(String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString))), String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString))), List::Cons(t0, List::Nil), Expr::ETuple(List::Cons(Expr::EMem(Mem_op::MRef(t0), List::Cons(s0, List::Nil)), List::Nil)))))
                      }
                    })
                    Mode::Chk(_UU03c4_) => {
                      let syn_r = bind(elab(e, v, l, _UU0393_, Mode::Syn), fn(x) {
                        match x {
                          SigT::ExistT(t0, s0) => Result0::Ok(SigT::ExistT(Ty::TData(String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString))), List::Cons(t0, List::Nil)), Expr::EConstr(String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString))), String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString))), List::Cons(t0, List::Nil), Expr::ETuple(List::Cons(Expr::EMem(Mem_op::MRef(t0), List::Cons(s0, List::Nil)), List::Nil)))))
                        }
                      })
                      match _UU03c4_ {
                        Ty::TData(r, ts) => match ts {
                          List::Nil => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(v, List::Nil)), Mode::Chk(Ty::TData(r, List::Nil)), syn_r)
                          List::Cons(t0, l1) => match l1 {
                            List::Nil => match string_dec(r, String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString)))) {
                              true => bind(cres(e, l, _UU0393_, v, t0, elab(e, v, l, _UU0393_, Mode::Chk(t0))), fn(x) {
                                okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(v, List::Nil)), Ty::TData(r, List::Cons(t0, List::Nil)), Expr::EConstr(String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString))), String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString))), List::Cons(t0, List::Nil), Expr::ETuple(List::Cons(Expr::EMem(Mem_op::MRef(t0), List::Cons(x, List::Nil)), List::Nil))))
                              })
                              false => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(v, List::Nil)), Mode::Chk(Ty::TData(r, List::Cons(t0, List::Nil))), syn_r)
                            }
                            List::Cons(t1, l2) => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(v, List::Nil)), Mode::Chk(Ty::TData(r, List::Cons(t0, List::Cons(t1, l2)))), syn_r)
                          }
                        }
                        x => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(v, List::Nil)), Mode::Chk(x), syn_r)
                      }
                    }
                  }
                })
                List::Cons(s0, l1) => {
                  let a0 = List::Cons(v, List::Cons(s0, l1))
                  match array_kind_of(t) {
                    Some(k) => match string_dec(mn, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))) {
                      true => match string_dec(mn, String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, true, true, true, false), String0::EmptyString)))) {
                        true => match a0 {
                          List::Nil => match m {
                            Mode::Syn => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                            Mode::Chk(_UU03c4_) => match _UU03c4_ {
                              Ty::TArray(k_, t0) => match array_kind_eq_dec(k, k_) {
                                true => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Nil), Ty::TArray(k_, t0), Expr::EMem(Mem_op::MArray(k, t0, Nat::O), List::Nil))
                                false => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                              }
                              _ => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                            }
                          }
                          List::Cons(n, l2) => match l2 {
                            List::Nil => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                            List::Cons(v0, l3) => match l3 {
                              List::Nil => bind(cres(e, l, _UU0393_, n, Ty::TBase(Base_ty::BInt(Int_kind::I32)), elab(e, n, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BInt(Int_kind::I32))))), fn(x) {
                                let syn_m = bind(elab(e, v0, l, _UU0393_, Mode::Syn), fn(x0) {
                                  match x0 {
                                    SigT::ExistT(t0, s1) => Result0::Ok(SigT::ExistT(Ty::TArray(k, t0), Expr::EMem(Mem_op::MMake(k, t0), List::Cons(x, List::Cons(s1, List::Nil)))))
                                  }
                                })
                                match m {
                                  Mode::Syn => syn_m
                                  Mode::Chk(_UU03c4_) => match _UU03c4_ {
                                    Ty::TArray(k_, t0) => match array_kind_eq_dec(k, k_) {
                                      true => bind(cres(e, l, _UU0393_, v0, t0, elab(e, v0, l, _UU0393_, Mode::Chk(t0))), fn(x0) {
                                        okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v0, List::Nil))), Ty::TArray(k_, t0), Expr::EMem(Mem_op::MMake(k, t0), List::Cons(x, List::Cons(x0, List::Nil))))
                                      })
                                      false => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v0, List::Nil))), Mode::Chk(Ty::TArray(k_, t0)), syn_m)
                                    }
                                    x0 => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v0, List::Nil))), Mode::Chk(x0), syn_m)
                                  }
                                }
                              })
                              List::Cons(_, _) => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                            }
                          }
                        }
                        false => match a0 {
                          List::Nil => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                          List::Cons(n, l2) => match l2 {
                            List::Nil => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                            List::Cons(v0, l3) => match l3 {
                              List::Nil => bind(cres(e, l, _UU0393_, n, Ty::TBase(Base_ty::BInt(Int_kind::I32)), elab(e, n, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BInt(Int_kind::I32))))), fn(x) {
                                let syn_m = bind(elab(e, v0, l, _UU0393_, Mode::Syn), fn(x0) {
                                  match x0 {
                                    SigT::ExistT(t0, s1) => Result0::Ok(SigT::ExistT(Ty::TArray(k, t0), Expr::EMem(Mem_op::MMake(k, t0), List::Cons(x, List::Cons(s1, List::Nil)))))
                                  }
                                })
                                match m {
                                  Mode::Syn => syn_m
                                  Mode::Chk(_UU03c4_) => match _UU03c4_ {
                                    Ty::TArray(k_, t0) => match array_kind_eq_dec(k, k_) {
                                      true => bind(cres(e, l, _UU0393_, v0, t0, elab(e, v0, l, _UU0393_, Mode::Chk(t0))), fn(x0) {
                                        okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v0, List::Nil))), Ty::TArray(k_, t0), Expr::EMem(Mem_op::MMake(k, t0), List::Cons(x, List::Cons(x0, List::Nil))))
                                      })
                                      false => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v0, List::Nil))), Mode::Chk(Ty::TArray(k_, t0)), syn_m)
                                    }
                                    x0 => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v0, List::Nil))), Mode::Chk(x0), syn_m)
                                  }
                                }
                              })
                              List::Cons(_, _) => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                            }
                          }
                        }
                      }
                      false => match string_dec(mn, String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, true, true, true, false), String0::EmptyString)))) {
                        true => match a0 {
                          List::Nil => match m {
                            Mode::Syn => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                            Mode::Chk(_UU03c4_) => match _UU03c4_ {
                              Ty::TArray(k_, t0) => match array_kind_eq_dec(k, k_) {
                                true => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Nil), Ty::TArray(k_, t0), Expr::EMem(Mem_op::MArray(k, t0, Nat::O), List::Nil))
                                false => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                              }
                              _ => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                            }
                          }
                          List::Cons(_, _) => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                        }
                        false => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                      }
                    }
                    None => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                  }
                }
              }
            }
            false => match array_kind_of(t) {
              Some(k) => match string_dec(mn, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))) {
                true => match string_dec(mn, String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, true, true, true, false), String0::EmptyString)))) {
                  true => match args {
                    List::Nil => match m {
                      Mode::Syn => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                      Mode::Chk(_UU03c4_) => match _UU03c4_ {
                        Ty::TArray(k_, t0) => match array_kind_eq_dec(k, k_) {
                          true => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Nil), Ty::TArray(k_, t0), Expr::EMem(Mem_op::MArray(k, t0, Nat::O), List::Nil))
                          false => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                        }
                        _ => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                      }
                    }
                    List::Cons(n, l0) => match l0 {
                      List::Nil => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                      List::Cons(v, l1) => match l1 {
                        List::Nil => bind(cres(e, l, _UU0393_, n, Ty::TBase(Base_ty::BInt(Int_kind::I32)), elab(e, n, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BInt(Int_kind::I32))))), fn(x) {
                          let syn_m = bind(elab(e, v, l, _UU0393_, Mode::Syn), fn(x0) {
                            match x0 {
                              SigT::ExistT(t0, s0) => Result0::Ok(SigT::ExistT(Ty::TArray(k, t0), Expr::EMem(Mem_op::MMake(k, t0), List::Cons(x, List::Cons(s0, List::Nil)))))
                            }
                          })
                          match m {
                            Mode::Syn => syn_m
                            Mode::Chk(_UU03c4_) => match _UU03c4_ {
                              Ty::TArray(k_, t0) => match array_kind_eq_dec(k, k_) {
                                true => bind(cres(e, l, _UU0393_, v, t0, elab(e, v, l, _UU0393_, Mode::Chk(t0))), fn(x0) {
                                  okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v, List::Nil))), Ty::TArray(k_, t0), Expr::EMem(Mem_op::MMake(k, t0), List::Cons(x, List::Cons(x0, List::Nil))))
                                })
                                false => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v, List::Nil))), Mode::Chk(Ty::TArray(k_, t0)), syn_m)
                              }
                              x0 => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v, List::Nil))), Mode::Chk(x0), syn_m)
                            }
                          }
                        })
                        List::Cons(_, _) => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                      }
                    }
                  }
                  false => match args {
                    List::Nil => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                    List::Cons(n, l0) => match l0 {
                      List::Nil => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                      List::Cons(v, l1) => match l1 {
                        List::Nil => bind(cres(e, l, _UU0393_, n, Ty::TBase(Base_ty::BInt(Int_kind::I32)), elab(e, n, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BInt(Int_kind::I32))))), fn(x) {
                          let syn_m = bind(elab(e, v, l, _UU0393_, Mode::Syn), fn(x0) {
                            match x0 {
                              SigT::ExistT(t0, s0) => Result0::Ok(SigT::ExistT(Ty::TArray(k, t0), Expr::EMem(Mem_op::MMake(k, t0), List::Cons(x, List::Cons(s0, List::Nil)))))
                            }
                          })
                          match m {
                            Mode::Syn => syn_m
                            Mode::Chk(_UU03c4_) => match _UU03c4_ {
                              Ty::TArray(k_, t0) => match array_kind_eq_dec(k, k_) {
                                true => bind(cres(e, l, _UU0393_, v, t0, elab(e, v, l, _UU0393_, Mode::Chk(t0))), fn(x0) {
                                  okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v, List::Nil))), Ty::TArray(k_, t0), Expr::EMem(Mem_op::MMake(k, t0), List::Cons(x, List::Cons(x0, List::Nil))))
                                })
                                false => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v, List::Nil))), Mode::Chk(Ty::TArray(k_, t0)), syn_m)
                              }
                              x0 => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v, List::Nil))), Mode::Chk(x0), syn_m)
                            }
                          }
                        })
                        List::Cons(_, _) => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                      }
                    }
                  }
                }
                false => match string_dec(mn, String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, true, true, true, false), String0::EmptyString)))) {
                  true => match args {
                    List::Nil => match m {
                      Mode::Syn => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                      Mode::Chk(_UU03c4_) => match _UU03c4_ {
                        Ty::TArray(k_, t0) => match array_kind_eq_dec(k, k_) {
                          true => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Nil), Ty::TArray(k_, t0), Expr::EMem(Mem_op::MArray(k, t0, Nat::O), List::Nil))
                          false => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                        }
                        _ => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                      }
                    }
                    List::Cons(_, _) => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                  }
                  false => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                }
              }
              None => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
            }
          }
          false => match array_kind_of(t) {
            Some(k) => match string_dec(mn, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))) {
              true => match string_dec(mn, String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, true, true, true, false), String0::EmptyString)))) {
                true => match args {
                  List::Nil => match m {
                    Mode::Syn => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                    Mode::Chk(_UU03c4_) => match _UU03c4_ {
                      Ty::TArray(k_, t0) => match array_kind_eq_dec(k, k_) {
                        true => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Nil), Ty::TArray(k_, t0), Expr::EMem(Mem_op::MArray(k, t0, Nat::O), List::Nil))
                        false => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                      }
                      _ => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                    }
                  }
                  List::Cons(n, l0) => match l0 {
                    List::Nil => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                    List::Cons(v, l1) => match l1 {
                      List::Nil => bind(cres(e, l, _UU0393_, n, Ty::TBase(Base_ty::BInt(Int_kind::I32)), elab(e, n, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BInt(Int_kind::I32))))), fn(x) {
                        let syn_m = bind(elab(e, v, l, _UU0393_, Mode::Syn), fn(x0) {
                          match x0 {
                            SigT::ExistT(t0, s0) => Result0::Ok(SigT::ExistT(Ty::TArray(k, t0), Expr::EMem(Mem_op::MMake(k, t0), List::Cons(x, List::Cons(s0, List::Nil)))))
                          }
                        })
                        match m {
                          Mode::Syn => syn_m
                          Mode::Chk(_UU03c4_) => match _UU03c4_ {
                            Ty::TArray(k_, t0) => match array_kind_eq_dec(k, k_) {
                              true => bind(cres(e, l, _UU0393_, v, t0, elab(e, v, l, _UU0393_, Mode::Chk(t0))), fn(x0) {
                                okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v, List::Nil))), Ty::TArray(k_, t0), Expr::EMem(Mem_op::MMake(k, t0), List::Cons(x, List::Cons(x0, List::Nil))))
                              })
                              false => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v, List::Nil))), Mode::Chk(Ty::TArray(k_, t0)), syn_m)
                            }
                            x0 => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v, List::Nil))), Mode::Chk(x0), syn_m)
                          }
                        }
                      })
                      List::Cons(_, _) => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                    }
                  }
                }
                false => match args {
                  List::Nil => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                  List::Cons(n, l0) => match l0 {
                    List::Nil => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                    List::Cons(v, l1) => match l1 {
                      List::Nil => bind(cres(e, l, _UU0393_, n, Ty::TBase(Base_ty::BInt(Int_kind::I32)), elab(e, n, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BInt(Int_kind::I32))))), fn(x) {
                        let syn_m = bind(elab(e, v, l, _UU0393_, Mode::Syn), fn(x0) {
                          match x0 {
                            SigT::ExistT(t0, s0) => Result0::Ok(SigT::ExistT(Ty::TArray(k, t0), Expr::EMem(Mem_op::MMake(k, t0), List::Cons(x, List::Cons(s0, List::Nil)))))
                          }
                        })
                        match m {
                          Mode::Syn => syn_m
                          Mode::Chk(_UU03c4_) => match _UU03c4_ {
                            Ty::TArray(k_, t0) => match array_kind_eq_dec(k, k_) {
                              true => bind(cres(e, l, _UU0393_, v, t0, elab(e, v, l, _UU0393_, Mode::Chk(t0))), fn(x0) {
                                okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v, List::Nil))), Ty::TArray(k_, t0), Expr::EMem(Mem_op::MMake(k, t0), List::Cons(x, List::Cons(x0, List::Nil))))
                              })
                              false => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v, List::Nil))), Mode::Chk(Ty::TArray(k_, t0)), syn_m)
                            }
                            x0 => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, List::Cons(n, List::Cons(v, List::Nil))), Mode::Chk(x0), syn_m)
                          }
                        }
                      })
                      List::Cons(_, _) => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                    }
                  }
                }
              }
              false => match string_dec(mn, String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, true, true, true, false), String0::EmptyString)))) {
                true => match args {
                  List::Nil => match m {
                    Mode::Syn => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                    Mode::Chk(_UU03c4_) => match _UU03c4_ {
                      Ty::TArray(k_, t0) => match array_kind_eq_dec(k, k_) {
                        true => okc(e, l, _UU0393_, Sexpr::SApp(p, f, List::Nil), Ty::TArray(k_, t0), Expr::EMem(Mem_op::MArray(k, t0, Nat::O), List::Nil))
                        false => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                      }
                      _ => Result0::Err(Elab_error::EE_CannotInfer(q, mn))
                    }
                  }
                  List::Cons(_, _) => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                }
                false => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
              }
            }
            None => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
          }
        }
        false => fin(e, p, l, _UU0393_, Sexpr::SApp(p, f, args), m, qcall(e, fn(x1) { fn(x2) { fn(x3) { fn(x4) { elab(e, x1, x2, x3, x4) } } } }, p, q, l, _UU0393_, f, t, mn, args, hint(m)))
      }
      Head0::HOther => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
    }
    Sexpr::SInfix(p, op, a, b) => match string_dec(op, String0::String1(Ascii::Ascii0(false, true, true, false, false, true, false, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, false, false), String0::EmptyString))) {
      true => fin(e, p, l, _UU0393_, Sexpr::SInfix(p, op, a, b), m, bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BBool), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BBool)))), fn(x) {
        bind(cres(e, l, _UU0393_, b, Ty::TBase(Base_ty::BBool), elab(e, b, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BBool)))), fn(x0) {
          Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BBool), Expr::EIf(x, x0, e_false)))
        })
      }))
      false => match string_dec(op, String0::String1(Ascii::Ascii0(false, false, true, true, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, true, true, true, false), String0::EmptyString))) {
        true => fin(e, p, l, _UU0393_, Sexpr::SInfix(p, op, a, b), m, bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BBool), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BBool)))), fn(x) {
          bind(cres(e, l, _UU0393_, b, Ty::TBase(Base_ty::BBool), elab(e, b, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BBool)))), fn(x0) {
            Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BBool), Expr::EIf(x, e_true, x0)))
          })
        }))
        false => {
          let bin_syn = match (match flexible(a) {
            true => negb(flexible(b))
            false => false
          }) {
            true => bind(elab(e, b, l, _UU0393_, Mode::Syn), fn(x) {
              match x {
                SigT::ExistT(_UU03c4_, s0) => bind(cres(e, l, _UU0393_, a, _UU03c4_, elab(e, a, l, _UU0393_, Mode::Chk(_UU03c4_))), fn(x0) {
                  bind(binop_dec(p, op, _UU03c4_, x0, s0), fn(x1) { Result0::Ok(SigT::ExistT(binop_res(op, _UU03c4_), x1)) })
                })
              }
            })
            false => bind(elab(e, a, l, _UU0393_, Mode::Syn), fn(x) {
              match x {
                SigT::ExistT(_UU03c4_, s0) => bind(cres(e, l, _UU0393_, b, _UU03c4_, elab(e, b, l, _UU0393_, Mode::Chk(_UU03c4_))), fn(x0) {
                  bind(binop_dec(p, op, _UU03c4_, s0, x0), fn(x1) { Result0::Ok(SigT::ExistT(binop_res(op, _UU03c4_), x1)) })
                })
              }
            })
          }
          match m {
            Mode::Syn => bin_syn
            Mode::Chk(_UU03c4_) => match assoc(op, arith_ops) {
              Some(_) => match ty_eq_dec(binop_res(op, _UU03c4_))(_UU03c4_) {
                true => bind(cres(e, l, _UU0393_, a, _UU03c4_, elab(e, a, l, _UU0393_, Mode::Chk(_UU03c4_))), fn(x) {
                  bind(cres(e, l, _UU0393_, b, _UU03c4_, elab(e, b, l, _UU0393_, Mode::Chk(_UU03c4_))), fn(x0) {
                    bind(binop_dec(p, op, _UU03c4_, x, x0), fn(x1) { okc(e, l, _UU0393_, Sexpr::SInfix(p, op, a, b), _UU03c4_, x1) })
                  })
                })
                false => fin(e, p, l, _UU0393_, Sexpr::SInfix(p, op, a, b), Mode::Chk(_UU03c4_), bin_syn)
              }
              None => fin(e, p, l, _UU0393_, Sexpr::SInfix(p, op, a, b), Mode::Chk(_UU03c4_), bin_syn)
            }
          }
        }
      }
    }
    Sexpr::SUnary(p, op, a) => match string_dec(op, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, false, false), String0::EmptyString)) {
      true => match int_lit_dec(a) {
        Sumor::Inleft(s0) => match s0 {
          SigT::ExistT(q, s1) => match s1 {
            SigT::ExistT(k, s2) => match m {
              Mode::Syn => bind(lit_syn(e, q, l, _UU0393_, Slit::SLInt(k, opp(s2))), fn(x) {
                match x {
                  SigT::ExistT(_UU03c4_, s3) => Result0::Ok(SigT::ExistT(_UU03c4_, s3))
                }
              })
              Mode::Chk(_UU03c4_) => bind(cres(e, l, _UU0393_, Sexpr::SLit(q, Slit::SLInt(k, opp(s2))), _UU03c4_, lit_m(e, q, l, _UU0393_, Slit::SLInt(k, opp(s2)), Mode::Chk(_UU03c4_))), fn(x) { okc(e, l, _UU0393_, Sexpr::SUnary(p, op, a), _UU03c4_, x) })
            }
          }
        }
        Sumor::Inright => fin(e, p, l, _UU0393_, Sexpr::SUnary(p, op, a), m, bind(elab(e, a, l, _UU0393_, Mode::Syn), fn(x) {
          match x {
            SigT::ExistT(_UU03c4_, s0) => match _UU03c4_ {
              Ty::TBase(b) => match b {
                Base_ty::BInt(k) => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BInt(k)), Expr::EPrim(Prim_op::PIntNeg(k), List::Cons(s0, List::Nil))))
                _ => Result0::Err(Elab_error::EE_NoOperator(p, op, _UU03c4_))
              }
              _ => Result0::Err(Elab_error::EE_NoOperator(p, op, _UU03c4_))
            }
          }
        }))
      }
      false => match string_dec(op, String0::String1(Ascii::Ascii0(true, false, false, false, false, true, false, false), String0::EmptyString)) {
        true => fin(e, p, l, _UU0393_, Sexpr::SUnary(p, op, a), m, bind(cres(e, l, _UU0393_, a, Ty::TBase(Base_ty::BBool), elab(e, a, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BBool)))), fn(x) {
          Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BBool), Expr::EPrim(Prim_op::PBoolNot, List::Cons(x, List::Nil))))
        }))
        false => Result0::Err(Elab_error::EE_NoOperator(p, op, Ty::TBase(Base_ty::BUnit)))
      }
    }
    Sexpr::SLet(p, x, ann, s1, s2) => bind(match ann {
      Some(t) => bind(ety_dec(e, t), fn(x0) {
        bind(cres(e, l, _UU0393_, s1, x0, elab(e, s1, l, _UU0393_, Mode::Chk(x0))), fn(x1) { Result0::Ok(SigT::ExistT(x0, x1)) })
      })
      None => bind(elab(e, s1, l, _UU0393_, Mode::Syn), fn(x0) {
        match x0 {
          SigT::ExistT(_UU03c4_, s0) => Result0::Ok(SigT::ExistT(_UU03c4_, s0))
        }
      })
    }, fn(x0) {
      match x0 {
        SigT::ExistT(_UU03c4_1, s0) => match m {
          Mode::Syn => bind(elab(e, s2, l, List::Cons((x, _UU03c4_1), _UU0393_), Mode::Syn), fn(x1) {
            match x1 {
              SigT::ExistT(_UU03c4_, s3) => Result0::Ok(SigT::ExistT(_UU03c4_, Expr::ELet(s0, s3)))
            }
          })
          Mode::Chk(_UU03c4_) => bind(cres(e, l, List::Cons((x, _UU03c4_1), _UU0393_), s2, _UU03c4_, elab(e, s2, l, List::Cons((x, _UU03c4_1), _UU0393_), Mode::Chk(_UU03c4_))), fn(x1) {
            okc(e, l, _UU0393_, Sexpr::SLet(p, x, ann, s1, s2), _UU03c4_, Expr::ELet(s0, x1))
          })
        }
      }
    })
    Sexpr::SIf(p, c, t, oe) => bind(cres(e, l, _UU0393_, c, Ty::TBase(Base_ty::BBool), elab(e, c, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BBool)))), fn(x) {
      match oe {
        Some(f) => match m {
          Mode::Syn => match (match diverges(t) {
            true => negb(diverges(f))
            false => false
          }) {
            true => bind(elab(e, f, l, _UU0393_, Mode::Syn), fn(x0) {
              match x0 {
                SigT::ExistT(_UU03c4_, s0) => bind(cres(e, l, _UU0393_, t, _UU03c4_, elab(e, t, l, _UU0393_, Mode::Chk(_UU03c4_))), fn(x1) { Result0::Ok(SigT::ExistT(_UU03c4_, Expr::EIf(x, x1, s0))) })
              }
            })
            false => bind(elab(e, t, l, _UU0393_, Mode::Syn), fn(x0) {
              match x0 {
                SigT::ExistT(_UU03c4_, s0) => bind(cres(e, l, _UU0393_, f, _UU03c4_, elab(e, f, l, _UU0393_, Mode::Chk(_UU03c4_))), fn(x1) { Result0::Ok(SigT::ExistT(_UU03c4_, Expr::EIf(x, s0, x1))) })
              }
            })
          }
          Mode::Chk(_UU03c4_) => bind(cres(e, l, _UU0393_, t, _UU03c4_, elab(e, t, l, _UU0393_, Mode::Chk(_UU03c4_))), fn(x0) {
            bind(cres(e, l, _UU0393_, f, _UU03c4_, elab(e, f, l, _UU0393_, Mode::Chk(_UU03c4_))), fn(x1) {
              okc(e, l, _UU0393_, Sexpr::SIf(p, c, t, Some(f)), _UU03c4_, Expr::EIf(x, x0, x1))
            })
          })
        }
        None => fin(e, p, l, _UU0393_, Sexpr::SIf(p, c, t, None), m, bind(cres(e, l, _UU0393_, t, Ty::TBase(Base_ty::BUnit), elab(e, t, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BUnit)))), fn(x0) {
          Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::EIf(x, x0, Expr::ELit(Lit::LUnit))))
        }))
      }
    })
    Sexpr::STup(p, ss) => {
      let syn_t = bind(syn_list(e, l, _UU0393_, fn(s_) { elab(e, s_, l, _UU0393_, Mode::Syn) }, ss), fn(x) {
        match x {
          SigT::ExistT(_UU03c4_s, s0) => Result0::Ok(SigT::ExistT(Ty::TTuple(_UU03c4_s), Expr::ETuple(s0)))
        }
      })
      match m {
        Mode::Syn => syn_t
        Mode::Chk(_UU03c4_) => match _UU03c4_ {
          Ty::TTuple(ts) => match eqb0(length(ts), length(ss)) {
            true => bind(chk_list(e, p, l, _UU0393_, fn(s_) {
              fn(_UU03c4__) {
                cres(e, l, _UU0393_, s_, _UU03c4__, elab(e, s_, l, _UU0393_, Mode::Chk(_UU03c4__)))
              }
            }, ss, ts), fn(x) {
              okc(e, l, _UU0393_, Sexpr::STup(p, ss), Ty::TTuple(ts), Expr::ETuple(x))
            })
            false => fin(e, p, l, _UU0393_, Sexpr::STup(p, ss), Mode::Chk(Ty::TTuple(ts)), syn_t)
          }
          x => fin(e, p, l, _UU0393_, Sexpr::STup(p, ss), Mode::Chk(x), syn_t)
        }
      }
    }
    Sexpr::SProj(p, s0, i) => fin(e, p, l, _UU0393_, Sexpr::SProj(p, s0, i), m, bind(elab(e, s0, l, _UU0393_, Mode::Syn), fn(x) {
      match x {
        SigT::ExistT(_UU03c4_0, s1) => match _UU03c4_0 {
          Ty::TTuple(_UU03c4_s) => bind(of_option(nth_error(_UU03c4_s, i), Elab_error::EE_Type(p, Type_error::E_TupleIndex(i, Ty::TTuple(_UU03c4_s)))), fn(x0) { Result0::Ok(SigT::ExistT(x0, Expr::EProj(s1, i))) })
          Ty::TData(t, ts) => bind(field_proj_dec(e, p, t, ts, i, s1), fn(x0) {
            match x0 {
              (e_, _UU03c4_) => Result0::Ok(SigT::ExistT(_UU03c4_, e_))
            }
          })
          _ => Result0::Err(Elab_error::EE_Type(p, Type_error::E_NotTuple(_UU03c4_0)))
        }
      }
    }))
    Sexpr::SLam(p, ps, ret, a, body) => {
      let syn_l = bind(params_syn_dec(e, p, ps), fn(x) {
        bind(eff_syn_dec(e, a), fn(x0) {
          match ret {
            Some(t) => bind(ety_dec(e, t), fn(x1) {
              bind(cres(e, fun_env(x1, x0), app(lam_ctx(ps, x), _UU0393_), body, x1, elab(e, body, fun_env(x1, x0), app(lam_ctx(ps, x), _UU0393_), Mode::Chk(x1))), fn(x2) {
                Result0::Ok(SigT::ExistT(Ty::TArrow(x, x1, x0), Expr::ELam(x, x1, x0, eblock(x1, x2))))
              })
            })
            None => bind(elab(e, body, Cenv::Mk_cenv(List::Nil, x0), app(lam_ctx(ps, x), _UU0393_), Mode::Syn), fn(x1) {
              match x1 {
                SigT::ExistT(r, s0) => Result0::Ok(SigT::ExistT(Ty::TArrow(x, r, x0), Expr::ELam(x, r, x0, s0)))
              }
            })
          }
        })
      })
      match m {
        Mode::Syn => syn_l
        Mode::Chk(_UU03c4_) => match _UU03c4_ {
          Ty::TArrow(_UU03c4_s, r, _UU03b5_) => match eqb0(length(_UU03c4_s), length(ps)) {
            true => bind(params_fit(e, p, ps, _UU03c4_s), fn(_) {
              bind(ann_fit(e, p, ret, r), fn(_) {
                bind(eff_fit(e, p, a, _UU03b5_), fn(_) {
                  bind(cres(e, fun_env(r, _UU03b5_), app(lam_ctx(ps, _UU03c4_s), _UU0393_), body, r, elab(e, body, fun_env(r, _UU03b5_), app(lam_ctx(ps, _UU03c4_s), _UU0393_), Mode::Chk(r))), fn(x) {
                    okc(e, l, _UU0393_, Sexpr::SLam(p, ps, ret, a, body), Ty::TArrow(_UU03c4_s, r, _UU03b5_), Expr::ELam(_UU03c4_s, r, _UU03b5_, eblock(r, x)))
                  })
                })
              })
            })
            false => fin(e, p, l, _UU0393_, Sexpr::SLam(p, ps, ret, a, body), Mode::Chk(Ty::TArrow(_UU03c4_s, r, _UU03b5_)), syn_l)
          }
          x => fin(e, p, l, _UU0393_, Sexpr::SLam(p, ps, ret, a, body), Mode::Chk(x), syn_l)
        }
      }
    }
    Sexpr::SAnnot(p, s0, t) => fin(e, p, l, _UU0393_, Sexpr::SAnnot(p, s0, t), m, bind(ety_dec(e, t), fn(x) {
      bind(cres(e, l, _UU0393_, s0, x, elab(e, s0, l, _UU0393_, Mode::Chk(x))), fn(x0) { Result0::Ok(SigT::ExistT(x, x0)) })
    }))
    Sexpr::SConstr(p, tq, c) => {
      let syn_c = bind(ctor_pick_dec(e, p, tq, c), fn(x) {
        bind(of_option(lookup_ty(match e {
          Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
        }, x), Elab_error::EE_UnknownType(p, x)), fn(x0) {
          bind(of_option(lookup_ctor(x0, c), Elab_error::EE_UnknownCtor(p, c)), fn(x1) {
            bind(nil_fields(p, c, x1), fn(_) {
              bind(targs(p, c, match x0 {
                Tdef::Mk_tdef(_, td_tparams, _, _) => td_tparams
              }, repeat(None, match x0 {
                Tdef::Mk_tdef(_, td_tparams, _, _) => td_tparams
              })), fn(x2) {
                Result0::Ok(SigT::ExistT(Ty::TData(x, x2), Expr::EConstr(x, c, x2, Expr::ETuple(List::Nil))))
              })
            })
          })
        })
      })
      match m {
        Mode::Syn => syn_c
        Mode::Chk(_UU03c4_) => match _UU03c4_ {
          Ty::TData(t, ts) => match lookup_ty(match e {
            Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
          }, t) {
            Some(td) => match lookup_ctor(td, c) {
              Some(cd) => bind(tq_dec(p, tq, t, Elab_error::EE_UnknownCtor(p, c)), fn(_) {
                bind(match eq_dec(length(ts), match td {
                  Tdef::Mk_tdef(_, td_tparams, _, _) => td_tparams
                }) {
                  true => Result0::Ok(())
                  false => Result0::Err(Elab_error::EE_TypeArgs(p, t, match td {
                    Tdef::Mk_tdef(_, td_tparams, _, _) => td_tparams
                  }, length(ts)))
                }, fn(_) {
                  bind(nil_fields(p, c, cd), fn(_) {
                    okc(e, l, _UU0393_, Sexpr::SConstr(p, tq, c), Ty::TData(t, ts), Expr::EConstr(t, c, ts, Expr::ETuple(List::Nil)))
                  })
                })
              })
              None => fin(e, p, l, _UU0393_, Sexpr::SConstr(p, tq, c), Mode::Chk(Ty::TData(t, ts)), syn_c)
            }
            None => fin(e, p, l, _UU0393_, Sexpr::SConstr(p, tq, c), Mode::Chk(Ty::TData(t, ts)), syn_c)
          }
          x => fin(e, p, l, _UU0393_, Sexpr::SConstr(p, tq, c), Mode::Chk(x), syn_c)
        }
      }
    }
    Sexpr::SRecord(p, tq, fes) => {
      let syn_r = bind(rec_pick_dec(e, p, tq, map(fn(x1) { fst(x1) }, fes)), fn(x) {
        bind(of_option(assoc(x, match e {
          Senv::Mk_senv(_, _, se_sinfo, _, _) => se_sinfo
        }), Elab_error::EE_NotRecord(p, Ty::TData(x, List::Nil))), fn(x0) {
          bind(of_option(lookup_ty(match e {
            Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
          }, x), Elab_error::EE_UnknownType(p, x)), fn(x1) {
            bind(single_ctor(p, x1, Ty::TData(x, List::Nil)), fn(x2) {
              bind(len_dec(p, x, length(match x2 {
                Cdef::Mk_cdef(_, cd_fields) => cd_fields
              }), length(x0)), fn(_) {
                bind(match (match x1 {
                  Tdef::Mk_tdef(_, td_tparams, _, _) => td_tparams
                }) {
                  Nat::O => Result0::Ok(List::Nil)
                  Nat::S(_) => bind(rpass(e, fn(x6) { fn(x5) { fn(x3) { fn(x4) { elab(e, x6, x5, x3, x4) } } } }, l, _UU0393_, x0, match x2 {
                    Cdef::Mk_cdef(_, cd_fields) => cd_fields
                  }, fes, repeat(None, match x1 {
                    Tdef::Mk_tdef(_, td_tparams, _, _) => td_tparams
                  })), fn(st) {
                    targs(p, x, match x1 {
                      Tdef::Mk_tdef(_, td_tparams, _, _) => td_tparams
                    }, st)
                  })
                }, fn(x3) {
                  bind(rfields_dec(e, fn(x7) { fn(x6) { fn(x5) { fn(x4) { elab(e, x7, x6, x5, x4) } } } }, p, l, _UU0393_, x0, map({ let a1 = fn(x4) { inst(x3, x4) }; fn(x4) { tsubst(a1, x4) } }, match x2 {
                    Cdef::Mk_cdef(_, cd_fields) => cd_fields
                  }), fes), fn(x4) {
                    match x4 {
                      SigT::ExistT(es, s0) => bind(rec_vars_dec(p, x0, s0), fn(x5) {
                        Result0::Ok(SigT::ExistT(Ty::TData(x, x3), Expr::ELet(Expr::ETuple(es), Expr::EConstr(x, match x2 {
                          Cdef::Mk_cdef(cd_name, _) => cd_name
                        }, x3, Expr::ETuple(x5)))))
                      })
                    }
                  })
                })
              })
            })
          })
        })
      })
      match m {
        Mode::Syn => syn_r
        Mode::Chk(_UU03c4_) => match _UU03c4_ {
          Ty::TData(t, ts) => match assoc(t, match e {
            Senv::Mk_senv(_, _, se_sinfo, _, _) => se_sinfo
          }) {
            Some(names) => bind(tq_dec(p, tq, t, Elab_error::EE_NotRecord(p, Ty::TData(t, ts))), fn(_) {
              bind(of_option(lookup_ty(match e {
                Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
              }, t), Elab_error::EE_UnknownType(p, t)), fn(x) {
                bind(single_ctor(p, x, Ty::TData(t, ts)), fn(x0) {
                  bind(len_dec(p, t, length(ts), match x {
                    Tdef::Mk_tdef(_, td_tparams, _, _) => td_tparams
                  }), fn(_) {
                    bind(len_dec(p, t, length(match x0 {
                      Cdef::Mk_cdef(_, cd_fields) => cd_fields
                    }), length(names)), fn(_) {
                      bind(rfields_dec(e, fn(x1) { fn(x2) { fn(x3) { fn(x4) { elab(e, x1, x2, x3, x4) } } } }, p, l, _UU0393_, names, map({ let a1 = fn(x1) { inst(ts, x1) }; fn(x1) { tsubst(a1, x1) } }, match x0 {
                        Cdef::Mk_cdef(_, cd_fields) => cd_fields
                      }), fes), fn(x1) {
                        match x1 {
                          SigT::ExistT(es, s0) => bind(rec_vars_dec(p, names, s0), fn(x2) {
                            okc(e, l, _UU0393_, Sexpr::SRecord(p, tq, fes), Ty::TData(t, ts), Expr::ELet(Expr::ETuple(es), Expr::EConstr(t, match x0 {
                              Cdef::Mk_cdef(cd_name, _) => cd_name
                            }, ts, Expr::ETuple(x2))))
                          })
                        }
                      })
                    })
                  })
                })
              })
            })
            None => fin(e, p, l, _UU0393_, Sexpr::SRecord(p, tq, fes), Mode::Chk(Ty::TData(t, ts)), syn_r)
          }
          x => fin(e, p, l, _UU0393_, Sexpr::SRecord(p, tq, fes), Mode::Chk(x), syn_r)
        }
      }
    }
    Sexpr::SField(p, s0, f) => fin(e, p, l, _UU0393_, Sexpr::SField(p, s0, f), m, bind(elab(e, s0, l, _UU0393_, Mode::Syn), fn(x) {
      match x {
        SigT::ExistT(_UU03c4_0, s1) => match _UU03c4_0 {
          Ty::TData(t, ts) => bind(of_option(assoc(t, match e {
            Senv::Mk_senv(_, _, se_sinfo, _, _) => se_sinfo
          }), Elab_error::EE_NotRecord(p, Ty::TData(t, ts))), fn(x0) {
            bind(of_option(index_of(f, x0), Elab_error::EE_UnknownField(p, f)), fn(x1) {
              bind(field_proj_dec(e, p, t, ts, x1, s1), fn(x2) {
                match x2 {
                  (e_, _UU03c4_) => Result0::Ok(SigT::ExistT(_UU03c4_, e_))
                }
              })
            })
          })
          _ => Result0::Err(Elab_error::EE_NotRecord(p, _UU03c4_0))
        }
      }
    }))
    Sexpr::SMatch(p, s0, cases) => bind(elab(e, s0, l, _UU0393_, Mode::Syn), fn(x) {
      match x {
        SigT::ExistT(_UU03c4_s, s1) => match m {
          Mode::Syn => bind(pick_syn(e, fn(x1) { fn(x2) { fn(x3) { fn(x4) { elab(e, x1, x2, x3, x4) } } } }, p, l, _UU0393_, _UU03c4_s, cases), fn(x0) {
            bind(arms_list(e, fn(x1) { fn(x2) { fn(x3) { fn(x4) { elab(e, x1, x2, x3, x4) } } } }, l, _UU0393_, _UU03c4_s, x0, cases), fn(x1) { Result0::Ok(SigT::ExistT(x0, Expr::EMatch(s1, x0, x1))) })
          })
          Mode::Chk(_UU03c4_) => bind(arms_list(e, fn(x1) { fn(x2) { fn(x3) { fn(x4) { elab(e, x1, x2, x3, x4) } } } }, l, _UU0393_, _UU03c4_s, _UU03c4_, cases), fn(x0) {
            okc(e, l, _UU0393_, Sexpr::SMatch(p, s0, cases), _UU03c4_, Expr::EMatch(s1, _UU03c4_, x0))
          })
        }
      }
    })
    Sexpr::SLetMut(p, x, ann, s1, s2) => bind(match ann {
      Some(t) => bind(ety_dec(e, t), fn(x0) {
        bind(cres(e, l, _UU0393_, s1, x0, elab(e, s1, l, _UU0393_, Mode::Chk(x0))), fn(x1) { Result0::Ok(SigT::ExistT(x0, x1)) })
      })
      None => bind(elab(e, s1, l, _UU0393_, Mode::Syn), fn(x0) {
        match x0 {
          SigT::ExistT(_UU03c4_, s0) => Result0::Ok(SigT::ExistT(_UU03c4_, s0))
        }
      })
    }, fn(x0) {
      match x0 {
        SigT::ExistT(_UU03c4_1, s0) => match m {
          Mode::Syn => bind(elab(e, s2, l, List::Cons((Some(x), Ty::TRef(_UU03c4_1)), _UU0393_), Mode::Syn), fn(x1) {
            match x1 {
              SigT::ExistT(_UU03c4_, s3) => Result0::Ok(SigT::ExistT(_UU03c4_, Expr::ELet(Expr::EMem(Mem_op::MRef(_UU03c4_1), List::Cons(s0, List::Nil)), s3)))
            }
          })
          Mode::Chk(_UU03c4_) => bind(cres(e, l, List::Cons((Some(x), Ty::TRef(_UU03c4_1)), _UU0393_), s2, _UU03c4_, elab(e, s2, l, List::Cons((Some(x), Ty::TRef(_UU03c4_1)), _UU0393_), Mode::Chk(_UU03c4_))), fn(x1) {
            okc(e, l, _UU0393_, Sexpr::SLetMut(p, x, ann, s1, s2), _UU03c4_, Expr::ELet(Expr::EMem(Mem_op::MRef(_UU03c4_1), List::Cons(s0, List::Nil)), x1))
          })
        }
      }
    })
    Sexpr::SAssign(p, x, op, s0) => fin(e, p, l, _UU0393_, Sexpr::SAssign(p, x, op, s0), m, bind(of_option(lookup_local(x, _UU0393_), Elab_error::EE_NotMutable(p, x)), fn(x0) {
      bind(of_option(nth_error(ctx_of(_UU0393_), x0), Elab_error::EE_NotMutable(p, x)), fn(x1) {
        match x1 {
          Ty::TRef(_UU03c4_) => bind(cres(e, l, _UU0393_, s0, _UU03c4_, elab(e, s0, l, _UU0393_, Mode::Chk(_UU03c4_))), fn(x2) {
            bind(upd_rhs_dec(p, op, _UU03c4_, Expr::EMem(Mem_op::MGet(_UU03c4_), List::Cons(Expr::EVar(x0), List::Nil)), x2), fn(x3) {
              Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::EMem(Mem_op::MSet(_UU03c4_), List::Cons(Expr::EVar(x0), List::Cons(x3, List::Nil)))))
            })
          })
          _ => Result0::Err(Elab_error::EE_NotMutable(p, x))
        }
      })
    }))
    Sexpr::SArray(p, ss) => {
      let syn_a = match ss {
        List::Nil => Result0::Err(Elab_error::EE_CannotInfer(p, String0::String1(Ascii::Ascii0(true, true, false, true, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, true, true, false, true, false), String0::EmptyString))))
        List::Cons(s0, ss_) => bind(elab(e, s0, l, _UU0393_, Mode::Syn), fn(x) {
          match x {
            SigT::ExistT(t, s1) => bind(chk_list(e, p, l, _UU0393_, fn(s_) {
              fn(_UU03c4__) {
                cres(e, l, _UU0393_, s_, _UU03c4__, elab(e, s_, l, _UU0393_, Mode::Chk(_UU03c4__)))
              }
            }, ss_, repeat(t, length(ss_))), fn(x0) {
              Result0::Ok(SigT::ExistT(Ty::TArray(Array_kind::AGrow, t), Expr::EMem(Mem_op::MArray(Array_kind::AGrow, t, Nat::S(length(ss_))), List::Cons(s1, x0))))
            })
          }
        })
      }
      match m {
        Mode::Syn => syn_a
        Mode::Chk(_UU03c4_) => match _UU03c4_ {
          Ty::TArray(k, t) => bind(chk_list(e, p, l, _UU0393_, fn(s_) {
            fn(_UU03c4__) {
              cres(e, l, _UU0393_, s_, _UU03c4__, elab(e, s_, l, _UU0393_, Mode::Chk(_UU03c4__)))
            }
          }, ss, repeat(t, length(ss))), fn(x) {
            okc(e, l, _UU0393_, Sexpr::SArray(p, ss), Ty::TArray(k, t), Expr::EMem(Mem_op::MArray(k, t, length(ss)), x))
          })
          x => fin(e, p, l, _UU0393_, Sexpr::SArray(p, ss), Mode::Chk(x), syn_a)
        }
      }
    }
    Sexpr::SIndex(p, a, i) => fin(e, p, l, _UU0393_, Sexpr::SIndex(p, a, i), m, bind(elab(e, a, l, _UU0393_, Mode::Syn), fn(x) {
      match x {
        SigT::ExistT(_UU03c4_a, s0) => match _UU03c4_a {
          Ty::TArray(k, t) => bind(cres(e, l, _UU0393_, i, Ty::TBase(Base_ty::BInt(Int_kind::I32)), elab(e, i, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BInt(Int_kind::I32))))), fn(x0) {
            Result0::Ok(SigT::ExistT(t, Expr::EMem(Mem_op::MIndex(k, t), List::Cons(s0, List::Cons(x0, List::Nil)))))
          })
          _ => Result0::Err(Elab_error::EE_NoMethod(p, String0::String1(Ascii::Ascii0(true, true, false, true, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, true, true, false, true, false), String0::EmptyString)), _UU03c4_a))
        }
      }
    }))
    Sexpr::SIndexSet(p, a, i, op, v) => fin(e, p, l, _UU0393_, Sexpr::SIndexSet(p, a, i, op, v), m, bind(elab(e, a, l, _UU0393_, Mode::Syn), fn(x) {
      match x {
        SigT::ExistT(_UU03c4_a, s0) => match _UU03c4_a {
          Ty::TArray(k, t) => match op {
            Some(o) => bind(cres(e, l, List::Cons((None, Ty::TArray(k, t)), _UU0393_), i, Ty::TBase(Base_ty::BInt(Int_kind::I32)), elab(e, i, l, List::Cons((None, Ty::TArray(k, t)), _UU0393_), Mode::Chk(Ty::TBase(Base_ty::BInt(Int_kind::I32))))), fn(x0) {
              bind(cres(e, l, List::Cons((None, Ty::TBase(Base_ty::BInt(Int_kind::I32))), List::Cons((None, Ty::TArray(k, t)), _UU0393_)), v, t, elab(e, v, l, List::Cons((None, Ty::TBase(Base_ty::BInt(Int_kind::I32))), List::Cons((None, Ty::TArray(k, t)), _UU0393_)), Mode::Chk(t))), fn(x1) {
                match ty_eq_dec(binop_res(o, t))(t) {
                  true => bind(binop_dec(p, o, t, Expr::EMem(Mem_op::MIndex(k, t), List::Cons(Expr::EVar(Nat::S(Nat::O)), List::Cons(Expr::EVar(Nat::O), List::Nil))), x1), fn(x2) {
                    Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ELet(s0, Expr::ELet(x0, Expr::EMem(Mem_op::MSetIndex(k, t), List::Cons(Expr::EVar(Nat::S(Nat::O)), List::Cons(Expr::EVar(Nat::O), List::Cons(x2, List::Nil))))))))
                  })
                  false => Result0::Err(Elab_error::EE_NoOperator(p, o, t))
                }
              })
            })
            None => bind(cres(e, l, _UU0393_, i, Ty::TBase(Base_ty::BInt(Int_kind::I32)), elab(e, i, l, _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BInt(Int_kind::I32))))), fn(x0) {
              bind(cres(e, l, _UU0393_, v, t, elab(e, v, l, _UU0393_, Mode::Chk(t))), fn(x1) {
                Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::EMem(Mem_op::MSetIndex(k, t), List::Cons(s0, List::Cons(x0, List::Cons(x1, List::Nil))))))
              })
            })
          }
          _ => Result0::Err(Elab_error::EE_NoMethod(p, String0::String1(Ascii::Ascii0(true, true, false, true, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, true, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, true, true, true, false, false), String0::EmptyString))), _UU03c4_a))
        }
      }
    }))
    Sexpr::SFieldSet(p, s0, f, op, v) => fin(e, p, l, _UU0393_, Sexpr::SFieldSet(p, s0, f, op, v), m, bind(elab(e, s0, l, _UU0393_, Mode::Syn), fn(x) {
      match x {
        SigT::ExistT(_UU03c4_0, s1) => match _UU03c4_0 {
          Ty::TData(t, ts) => bind(of_option(assoc(t, match e {
            Senv::Mk_senv(_, _, se_sinfo, _, _) => se_sinfo
          }), Elab_error::EE_NotRecord(p, Ty::TData(t, ts))), fn(x0) {
            bind(of_option(index_of(f, x0), Elab_error::EE_UnknownField(p, f)), fn(x1) {
              bind(field_cell_dec(e, p, f, t, ts, x1), fn(x2) {
                match x2 {
                  (p0, t0) => match p0 {
                    (c, n) => bind(cres(e, l, List::Cons((None, Ty::TRef(t0)), _UU0393_), v, t0, elab(e, v, l, List::Cons((None, Ty::TRef(t0)), _UU0393_), Mode::Chk(t0))), fn(x3) {
                      bind(upd_rhs_dec(p, op, t0, Expr::EMem(Mem_op::MGet(t0), List::Cons(Expr::EVar(Nat::O), List::Nil)), x3), fn(x4) {
                        Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::EMatch(s1, Ty::TBase(Base_ty::BUnit), List::Cons((Pat::PConstr(c, proj_pats(x1, Pat::PVar, Nat::O, n)), Expr::EMem(Mem_op::MSet(t0), List::Cons(Expr::EVar(Nat::O), List::Cons(x4, List::Nil)))), List::Nil))))
                      })
                    })
                  }
                }
              })
            })
          })
          _ => Result0::Err(Elab_error::EE_NotRecord(p, _UU03c4_0))
        }
      }
    }))
    Sexpr::SMethod(p, s0, mn, args) => fin(e, p, l, _UU0393_, Sexpr::SMethod(p, s0, mn, args), m, bind(elab(e, s0, l, _UU0393_, Mode::Syn), fn(x) {
      match x {
        SigT::ExistT(_UU03c4_0, s1) => match arr_builtin(_UU03c4_0, mn, length(args)) {
          true => match string_dec(mn, String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::EmptyString))))))) {
            true => match string_dec(mn, String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::EmptyString))))) {
              true => match args {
                List::Nil => match _UU03c4_0 {
                  Ty::TArray(k, t) => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BInt(Int_kind::I32)), Expr::EMem(Mem_op::MLength(k, t), List::Cons(s1, List::Nil))))
                  _ => Result0::Err(Elab_error::EE_NoMethod(p, mn, _UU03c4_0))
                }
                List::Cons(a, l0) => match l0 {
                  List::Nil => match _UU03c4_0 {
                    Ty::TArray(k, t) => match k {
                      Array_kind::AFixed => Result0::Err(Elab_error::EE_NoMethod(p, mn, _UU03c4_0))
                      Array_kind::AGrow => bind(cres(e, l, _UU0393_, a, t, elab(e, a, l, _UU0393_, Mode::Chk(t))), fn(x0) {
                        Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::EMem(Mem_op::MPush(t), List::Cons(s1, List::Cons(x0, List::Nil)))))
                      })
                    }
                    _ => Result0::Err(Elab_error::EE_NoMethod(p, mn, _UU03c4_0))
                  }
                  List::Cons(_, _) => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                }
              }
              false => match args {
                List::Nil => match _UU03c4_0 {
                  Ty::TArray(k, t) => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BInt(Int_kind::I32)), Expr::EMem(Mem_op::MLength(k, t), List::Cons(s1, List::Nil))))
                  _ => Result0::Err(Elab_error::EE_NoMethod(p, mn, _UU03c4_0))
                }
                List::Cons(_, _) => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
              }
            }
            false => match string_dec(mn, String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::EmptyString))))) {
              true => match args {
                List::Nil => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                List::Cons(a, l0) => match l0 {
                  List::Nil => match _UU03c4_0 {
                    Ty::TArray(k, t) => match k {
                      Array_kind::AFixed => Result0::Err(Elab_error::EE_NoMethod(p, mn, _UU03c4_0))
                      Array_kind::AGrow => bind(cres(e, l, _UU0393_, a, t, elab(e, a, l, _UU0393_, Mode::Chk(t))), fn(x0) {
                        Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::EMem(Mem_op::MPush(t), List::Cons(s1, List::Cons(x0, List::Nil)))))
                      })
                    }
                    _ => Result0::Err(Elab_error::EE_NoMethod(p, mn, _UU03c4_0))
                  }
                  List::Cons(_, _) => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
                }
              }
              false => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))))))))))))
            }
          }
          false => dcall(e, fn(x1) { fn(x2) { fn(x3) { fn(x4) { elab(e, x1, x2, x3, x4) } } } }, p, l, _UU0393_, s0, mn, args, _UU03c4_0, s1, hint(m))
        }
      }
    }))
    Sexpr::SQual(_, _, _) => Result0::Err(Elab_error::EE_Unsupported(sexpr_pos(s), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, false, false, true, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::EmptyString)))))))))))))))))))))))))))))))))))))
    Sexpr::SWhile(p, x, c, body, onb) => match onb {
      Some(nb) => match m {
        Mode::Syn => bind(elab(e, nb, hd_env(List::Nil, Ty::TBase(Base_ty::BUnit), l), _UU0393_, Mode::Syn), fn(x0) {
          match x0 {
            SigT::ExistT(_UU03c4_, _) => bind(cres(e, hd_env(List::Nil, _UU03c4_, l), _UU0393_, c, Ty::TBase(Base_ty::BBool), elab(e, c, hd_env(List::Nil, _UU03c4_, l), _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BBool)))), fn(x1) {
              bind(cres(e, push_lab(Lab::Mk_lab(x, Lab_kind::LKWhile, List::Nil, _UU03c4_), l), _UU0393_, body, Ty::TBase(Base_ty::BUnit), elab(e, body, push_lab(Lab::Mk_lab(x, Lab_kind::LKWhile, List::Nil, _UU03c4_), l), _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BUnit)))), fn(x2) {
                bind(cres(e, hd_env(List::Nil, _UU03c4_, l), _UU0393_, nb, _UU03c4_, elab(e, nb, hd_env(List::Nil, _UU03c4_, l), _UU0393_, Mode::Chk(_UU03c4_))), fn(x3) {
                  Result0::Ok(SigT::ExistT(_UU03c4_, while_loop(_UU03c4_, x1, x2, x3)))
                })
              })
            })
          }
        })
        Mode::Chk(_UU03c4_) => bind(cres(e, hd_env(List::Nil, _UU03c4_, l), _UU0393_, c, Ty::TBase(Base_ty::BBool), elab(e, c, hd_env(List::Nil, _UU03c4_, l), _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BBool)))), fn(x0) {
          bind(cres(e, push_lab(Lab::Mk_lab(x, Lab_kind::LKWhile, List::Nil, _UU03c4_), l), _UU0393_, body, Ty::TBase(Base_ty::BUnit), elab(e, body, push_lab(Lab::Mk_lab(x, Lab_kind::LKWhile, List::Nil, _UU03c4_), l), _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BUnit)))), fn(x1) {
            bind(cres(e, hd_env(List::Nil, _UU03c4_, l), _UU0393_, nb, _UU03c4_, elab(e, nb, hd_env(List::Nil, _UU03c4_, l), _UU0393_, Mode::Chk(_UU03c4_))), fn(x2) {
              okc(e, l, _UU0393_, Sexpr::SWhile(p, x, c, body, Some(nb)), _UU03c4_, while_loop(_UU03c4_, x0, x1, x2))
            })
          })
        })
      }
      None => fin(e, p, l, _UU0393_, Sexpr::SWhile(p, x, c, body, None), m, bind(cres(e, hd_env(List::Nil, Ty::TBase(Base_ty::BUnit), l), _UU0393_, c, Ty::TBase(Base_ty::BBool), elab(e, c, hd_env(List::Nil, Ty::TBase(Base_ty::BUnit), l), _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BBool)))), fn(x0) {
        bind(cres(e, push_lab(Lab::Mk_lab(x, Lab_kind::LKWhile, List::Nil, Ty::TBase(Base_ty::BUnit)), l), _UU0393_, body, Ty::TBase(Base_ty::BUnit), elab(e, body, push_lab(Lab::Mk_lab(x, Lab_kind::LKWhile, List::Nil, Ty::TBase(Base_ty::BUnit)), l), _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BUnit)))), fn(x1) {
          Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), while_loop(Ty::TBase(Base_ty::BUnit), x0, x1, Expr::ELit(Lit::LUnit))))
        })
      }))
    }
    Sexpr::SFor(p, x, inits, oc0, upds, body, onb) => bind(sinits_dec(e, fn(x1) { fn(x2) { fn(x3) { fn(x4) { elab(e, x1, x2, x3, x4) } } } }, l, _UU0393_, inits), fn(x0) {
      match x0 {
        SigT::ExistT(_UU03c4_s, s0) => {
          let _UU0393__ = app(names_ctx(map(fn(x1) { fst(x1) }, inits), _UU03c4_s), _UU0393_)
          let names = map(fn(x1) { fst(x1) }, inits)
          let parts = fn(_UU03c4_) {
            bind(ochk_dec(e, fn(x1) { fn(x2) { fn(x3) { fn(x4) { elab(e, x1, x2, x3, x4) } } } }, hd_env(_UU03c4_s, _UU03c4_, l), _UU0393__, Ty::TBase(Base_ty::BBool), oc0), fn(x1) {
              bind(cres(e, push_lab(Lab::Mk_lab(x, Lab_kind::LKForBody, List::Nil, Ty::TBase(Base_ty::BUnit)), hd_env(_UU03c4_s, _UU03c4_, l)), _UU0393__, body, Ty::TBase(Base_ty::BUnit), elab(e, body, push_lab(Lab::Mk_lab(x, Lab_kind::LKForBody, List::Nil, Ty::TBase(Base_ty::BUnit)), hd_env(_UU03c4_s, _UU03c4_, l)), _UU0393__, Mode::Chk(Ty::TBase(Base_ty::BUnit)))), fn(x2) {
                bind(supds_dec(e, fn(x6) { fn(x5) { fn(x3) { fn(x4) { elab(e, x6, x5, x3, x4) } } } }, p, hd_env(_UU03c4_s, _UU03c4_, l), List::Cons((None, Ty::TBase(Base_ty::BUnit)), _UU0393__), names, _UU03c4_s, upds), fn(x3) { Result0::Ok(((x1, x2), x3)) })
              })
            })
          }
          match onb {
            Some(nb) => match m {
              Mode::Syn => bind(elab(e, nb, hd_env(_UU03c4_s, Ty::TBase(Base_ty::BUnit), l), _UU0393__, Mode::Syn), fn(x1) {
                match x1 {
                  SigT::ExistT(_UU03c4_, _) => bind(parts(_UU03c4_), fn(x2) {
                    match x2 {
                      (p0, us) => match p0 {
                        (c_, b_) => bind(cres(e, hd_env(_UU03c4_s, _UU03c4_, l), _UU0393__, nb, _UU03c4_, elab(e, nb, hd_env(_UU03c4_s, _UU03c4_, l), _UU0393__, Mode::Chk(_UU03c4_))), fn(x3) {
                          Result0::Ok(SigT::ExistT(_UU03c4_, for_loop(s0, _UU03c4_s, _UU03c4_, c_, b_, map(fn(x4) { fst(x4) }, inits), us, x3)))
                        })
                      }
                    }
                  })
                }
              })
              Mode::Chk(_UU03c4_) => bind(parts(_UU03c4_), fn(x1) {
                match x1 {
                  (p0, us) => match p0 {
                    (c_, b_) => bind(cres(e, hd_env(_UU03c4_s, _UU03c4_, l), _UU0393__, nb, _UU03c4_, elab(e, nb, hd_env(_UU03c4_s, _UU03c4_, l), _UU0393__, Mode::Chk(_UU03c4_))), fn(x2) {
                      okc(e, l, _UU0393_, Sexpr::SFor(p, x, inits, oc0, upds, body, Some(nb)), _UU03c4_, for_loop(s0, _UU03c4_s, _UU03c4_, c_, b_, map(fn(x3) { fst(x3) }, inits), us, x2))
                    })
                  }
                }
              })
            }
            None => {
              let syn_f = bind(parts(Ty::TBase(Base_ty::BUnit)), fn(x1) {
                match x1 {
                  (p0, us) => match p0 {
                    (c_, b_) => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), for_loop(s0, _UU03c4_s, Ty::TBase(Base_ty::BUnit), c_, b_, map(fn(x2) { fst(x2) }, inits), us, Expr::ELit(Lit::LUnit))))
                  }
                }
              })
              match m {
                Mode::Syn => syn_f
                Mode::Chk(_UU03c4_) => match oc0 {
                  Some(c0) => bind(cres(e, l, _UU0393_, Sexpr::SFor(p, x, inits, oc0, upds, body, None), _UU03c4_, fin(e, p, l, _UU0393_, Sexpr::SFor(p, x, inits, oc0, upds, body, None), Mode::Chk(_UU03c4_), syn_f)), fn(x1) {
                    okc(e, l, _UU0393_, Sexpr::SFor(p, x, inits, Some(c0), upds, body, None), _UU03c4_, x1)
                  })
                  None => bind(cres(e, push_lab(Lab::Mk_lab(x, Lab_kind::LKForBody, List::Nil, Ty::TBase(Base_ty::BUnit)), hd_env(_UU03c4_s, _UU03c4_, l)), _UU0393__, body, Ty::TBase(Base_ty::BUnit), elab(e, body, push_lab(Lab::Mk_lab(x, Lab_kind::LKForBody, List::Nil, Ty::TBase(Base_ty::BUnit)), hd_env(_UU03c4_s, _UU03c4_, l)), _UU0393__, Mode::Chk(Ty::TBase(Base_ty::BUnit)))), fn(x1) {
                    bind(supds_dec(e, fn(x5) { fn(x2) { fn(x3) { fn(x4) { elab(e, x5, x2, x3, x4) } } } }, p, hd_env(_UU03c4_s, _UU03c4_, l), List::Cons((None, Ty::TBase(Base_ty::BUnit)), _UU0393__), names, _UU03c4_s, upds), fn(x2) {
                      okc(e, l, _UU0393_, Sexpr::SFor(p, x, inits, None, upds, body, None), _UU03c4_, for_loop(s0, _UU03c4_s, _UU03c4_, None, x1, map(fn(x3) { fst(x3) }, inits), x2, Expr::ELit(Lit::LUnit)))
                    })
                  })
                }
              }
            }
          }
        }
      }
    })
    Sexpr::SBlock(p, x, body) => match m {
      Mode::Syn => bind(cres(e, push_lab(Lab::Mk_lab(Some(x), Lab_kind::LKBlock, List::Nil, Ty::TBase(Base_ty::BUnit)), l), _UU0393_, body, Ty::TBase(Base_ty::BUnit), elab(e, body, push_lab(Lab::Mk_lab(Some(x), Lab_kind::LKBlock, List::Nil, Ty::TBase(Base_ty::BUnit)), l), _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BUnit)))), fn(x0) {
        Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), eblock(Ty::TBase(Base_ty::BUnit), x0)))
      })
      Mode::Chk(_UU03c4_) => bind(cres(e, push_lab(Lab::Mk_lab(Some(x), Lab_kind::LKBlock, List::Nil, _UU03c4_), l), _UU0393_, body, _UU03c4_, elab(e, body, push_lab(Lab::Mk_lab(Some(x), Lab_kind::LKBlock, List::Nil, _UU03c4_), l), _UU0393_, Mode::Chk(_UU03c4_))), fn(x0) {
        okc(e, l, _UU0393_, Sexpr::SBlock(p, x, body), _UU03c4_, eblock(_UU03c4_, x0))
      })
    }
    Sexpr::SBreak(p, x, oa) => {
      let jmp = fn(_UU03c4_) {
        bind(of_option(break_target(x, match l {
          Cenv::Mk_cenv(ce_labs, _) => ce_labs
        }, Nat::O), Elab_error::EE_NoTarget(p)), fn(x0) {
          match x0 {
            (k, _UU03c4_t) => bind(label_at(p, l, k), fn(x1) {
              match x1 {
                (_, r) => match ty_eq_dec(r)(_UU03c4_t) {
                  true => match oa {
                    Some(a) => bind(cres(e, l, _UU0393_, a, _UU03c4_t, elab(e, a, l, _UU0393_, Mode::Chk(_UU03c4_t))), fn(x2) { Result0::Ok(Expr::EJump(Ctl::CBreak, k, x2, _UU03c4_)) })
                    None => match ty_eq_dec(_UU03c4_t)(Ty::TBase(Base_ty::BUnit)) {
                      true => Result0::Ok(Expr::EJump(Ctl::CBreak, k, Expr::ELit(Lit::LUnit), _UU03c4_))
                      false => Result0::Err(Elab_error::EE_Annot(p, _UU03c4_t, Ty::TBase(Base_ty::BUnit)))
                    }
                  }
                  false => Result0::Err(Elab_error::EE_NoTarget(p))
                }
              }
            })
          }
        })
      }
      match m {
        Mode::Syn => bind(jmp(Ty::TBase(Base_ty::BUnit)), fn(x0) { Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), x0)) })
        Mode::Chk(_UU03c4_) => bind(jmp(_UU03c4_), fn(r) { okc(e, l, _UU0393_, Sexpr::SBreak(p, x, oa), _UU03c4_, r) })
      }
    }
    Sexpr::SContinue(p, x, args) => {
      let jmp = fn(_UU03c4_) {
        bind(of_option(cont_target_of(x, match l {
          Cenv::Mk_cenv(ce_labs, _) => ce_labs
        }, Nat::O), Elab_error::EE_NoTarget(p)), fn(x0) {
          match x0 {
            Cont_target::CTWhile(k) => match args {
              List::Nil => bind(label_at(p, l, k), fn(x1) {
                match x1 {
                  (ps, _) => match list_eq_dec(ty_eq_dec, ps, List::Nil) {
                    true => Result0::Ok(Expr::EJump(Ctl::CCont, k, Expr::ETuple(List::Nil), _UU03c4_))
                    false => Result0::Err(Elab_error::EE_NoTarget(p))
                  }
                }
              })
              List::Cons(_, _) => Result0::Err(Elab_error::EE_BadContinue(p, Nat::O, length(args)))
            }
            Cont_target::CTFor(k, ps) => match args {
              List::Nil => bind(label_at(p, l, k), fn(x1) {
                match x1 {
                  (_, r) => match ty_eq_dec(r)(Ty::TBase(Base_ty::BUnit)) {
                    true => Result0::Ok(Expr::EJump(Ctl::CBreak, k, Expr::ELit(Lit::LUnit), _UU03c4_))
                    false => Result0::Err(Elab_error::EE_NoTarget(p))
                  }
                }
              })
              List::Cons(a, a_) => bind(bcheck(eqb0(length(ps), length(List::Cons(a, a_))), Elab_error::EE_BadContinue(p, length(ps), length(List::Cons(a, a_)))), fn(_) {
                bind(label_at(p, l, Nat::S(k)), fn(x1) {
                  match x1 {
                    (ps_, _) => match list_eq_dec(ty_eq_dec, ps_, ps) {
                      true => bind(chk_list(e, p, l, _UU0393_, fn(s_) {
                        fn(_UU03c4__) {
                          cres(e, l, _UU0393_, s_, _UU03c4__, elab(e, s_, l, _UU0393_, Mode::Chk(_UU03c4__)))
                        }
                      }, List::Cons(a, a_), ps), fn(x2) {
                        Result0::Ok(Expr::EJump(Ctl::CCont, Nat::S(k), Expr::ETuple(x2), _UU03c4_))
                      })
                      false => Result0::Err(Elab_error::EE_NoTarget(p))
                    }
                  }
                })
              })
            }
            Cont_target::CTForIn(k, ss) => match args {
              List::Nil => bind(label_at(p, l, k), fn(x1) {
                match x1 {
                  (_, r) => match ty_eq_dec(r)(Ty::TBase(Base_ty::BUnit)) {
                    true => Result0::Ok(Expr::EJump(Ctl::CBreak, k, Expr::ELit(Lit::LUnit), _UU03c4_))
                    false => Result0::Err(Elab_error::EE_NoTarget(p))
                  }
                }
              })
              List::Cons(a, a_) => bind(bcheck(eqb0(length(ss), length(List::Cons(a, a_))), Elab_error::EE_BadContinue(p, length(ss), length(List::Cons(a, a_)))), fn(_) {
                bind(label_at(p, l, Nat::S(k)), fn(x1) {
                  match x1 {
                    (_, r) => match ty_eq_dec(r)(Ty::TTuple(ss)) {
                      true => bind(chk_list(e, p, l, _UU0393_, fn(s_) {
                        fn(_UU03c4__) {
                          cres(e, l, _UU0393_, s_, _UU03c4__, elab(e, s_, l, _UU0393_, Mode::Chk(_UU03c4__)))
                        }
                      }, List::Cons(a, a_), ss), fn(x2) {
                        Result0::Ok(Expr::EJump(Ctl::CBreak, Nat::S(k), Expr::ETuple(x2), _UU03c4_))
                      })
                      false => Result0::Err(Elab_error::EE_NoTarget(p))
                    }
                  }
                })
              })
            }
          }
        })
      }
      match m {
        Mode::Syn => bind(jmp(Ty::TBase(Base_ty::BUnit)), fn(x0) { Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), x0)) })
        Mode::Chk(_UU03c4_) => bind(jmp(_UU03c4_), fn(r) { okc(e, l, _UU0393_, Sexpr::SContinue(p, x, args), _UU03c4_, r) })
      }
    }
    Sexpr::SReturn(p, oa) => {
      let jmp = fn(_UU03c4_) {
        bind(of_option(return_target(match l {
          Cenv::Mk_cenv(ce_labs, _) => ce_labs
        }, Nat::O), Elab_error::EE_NoTarget(p)), fn(x) {
          match x {
            (k, r) => bind(label_at(p, l, k), fn(x0) {
              match x0 {
                (_, r_) => match ty_eq_dec(r_)(r) {
                  true => match oa {
                    Some(a) => bind(cres(e, l, _UU0393_, a, r, elab(e, a, l, _UU0393_, Mode::Chk(r))), fn(x1) { Result0::Ok(Expr::EJump(Ctl::CBreak, k, x1, _UU03c4_)) })
                    None => match ty_eq_dec(r)(Ty::TBase(Base_ty::BUnit)) {
                      true => Result0::Ok(Expr::EJump(Ctl::CBreak, k, Expr::ELit(Lit::LUnit), _UU03c4_))
                      false => Result0::Err(Elab_error::EE_Annot(p, r, Ty::TBase(Base_ty::BUnit)))
                    }
                  }
                  false => Result0::Err(Elab_error::EE_NoTarget(p))
                }
              }
            })
          }
        })
      }
      match m {
        Mode::Syn => bind(jmp(Ty::TBase(Base_ty::BUnit)), fn(x) { Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), x)) })
        Mode::Chk(_UU03c4_) => bind(jmp(_UU03c4_), fn(r) { okc(e, l, _UU0393_, Sexpr::SReturn(p, oa), _UU03c4_, r) })
      }
    }
    Sexpr::SForIn(p, x, pats, src, inits, upds, body, onb) => bind(fsrc_dec(e, fn(x1) { fn(x2) { fn(x3) { fn(x4) { elab(e, x1, x2, x3, x4) } } } }, p, l, _UU0393_, src), fn(x0) {
      match x0 {
        SigT::ExistT(e1, s0) => match s0 {
          SigT::ExistT(e2, s1) => bind(sinits_dec(e, fn(x1) { fn(x2) { fn(x3) { fn(x4) { elab(e, x1, x2, x3, x4) } } } }, l, fo_ctx(s1, _UU0393_), inits), fn(x1) {
            match x1 {
              SigT::ExistT(_UU03c4_s, s2) => {
                let names = map(fn(x2) { fst(x2) }, inits)
                let _UU0393_l = fl_ctx(s1, names, _UU03c4_s, _UU0393_)
                bind(fi_pat_dec(e, p, s1, _UU03c4_s, pats), fn(x2) {
                  match x2 {
                    SigT::ExistT(q, s3) => match s3 {
                      SigT::ExistT(_UU0394_, s4) => match s4 {
                        SigT::ExistT(scrut, _) => {
                          let parts = fn(_UU03c4_) {
                            bind(cres(e, fi_body_env(x, s1, _UU03c4_s, _UU03c4_, l), app(_UU0394_, _UU0393_l), body, Ty::TBase(Base_ty::BUnit), elab(e, body, fi_body_env(x, s1, _UU03c4_s, _UU03c4_, l), app(_UU0394_, _UU0393_l), Mode::Chk(Ty::TBase(Base_ty::BUnit)))), fn(x3) {
                              bind(supds_dec(e, fn(x7) { fn(x6) { fn(x5) { fn(x4) { elab(e, x7, x6, x5, x4) } } } }, p, fi_state_env(s1, _UU03c4_s, _UU03c4_, l), List::Cons((None, Ty::TBase(Base_ty::BUnit)), app(_UU0394_, _UU0393_l)), names, _UU03c4_s, upds), fn(x4) { Result0::Ok((x3, x4)) })
                            })
                          }
                          match onb {
                            Some(nb) => match m {
                              Mode::Syn => bind(elab(e, nb, fi_loop_env(s1, _UU03c4_s, Ty::TBase(Base_ty::BUnit), l), _UU0393_l, Mode::Syn), fn(x3) {
                                match x3 {
                                  SigT::ExistT(_UU03c4_, _) => bind(parts(_UU03c4_), fn(x4) {
                                    match x4 {
                                      (b_, us) => bind(cres(e, fi_loop_env(s1, _UU03c4_s, _UU03c4_, l), _UU0393_l, nb, _UU03c4_, elab(e, nb, fi_loop_env(s1, _UU03c4_s, _UU03c4_, l), _UU0393_l, Mode::Chk(_UU03c4_))), fn(x5) {
                                        Result0::Ok(SigT::ExistT(_UU03c4_, forin_loop(s1, e1, e2, s2, _UU03c4_s, _UU03c4_, q, scrut, length(_UU0394_), b_, map(fn(x6) { fst(x6) }, inits), us, x5)))
                                      })
                                    }
                                  })
                                }
                              })
                              Mode::Chk(_UU03c4_) => bind(parts(_UU03c4_), fn(x3) {
                                match x3 {
                                  (b_, us) => bind(cres(e, fi_loop_env(s1, _UU03c4_s, _UU03c4_, l), _UU0393_l, nb, _UU03c4_, elab(e, nb, fi_loop_env(s1, _UU03c4_s, _UU03c4_, l), _UU0393_l, Mode::Chk(_UU03c4_))), fn(x4) {
                                    okc(e, l, _UU0393_, Sexpr::SForIn(p, x, pats, src, inits, upds, body, Some(nb)), _UU03c4_, forin_loop(s1, e1, e2, s2, _UU03c4_s, _UU03c4_, q, scrut, length(_UU0394_), b_, map(fn(x5) { fst(x5) }, inits), us, x4))
                                  })
                                }
                              })
                            }
                            None => fin(e, p, l, _UU0393_, Sexpr::SForIn(p, x, pats, src, inits, upds, body, None), m, bind(parts(Ty::TBase(Base_ty::BUnit)), fn(x3) {
                              match x3 {
                                (b_, us) => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), forin_loop(s1, e1, e2, s2, _UU03c4_s, Ty::TBase(Base_ty::BUnit), q, scrut, length(_UU0394_), b_, map(fn(x4) { fst(x4) }, inits), us, Expr::ELit(Lit::LUnit))))
                              }
                            }))
                          }
                        }
                      }
                    }
                  }
                })
              }
            }
          })
        }
      }
    })
    Sexpr::SRaise(p, s0) => bind(cres(e, l, _UU0393_, s0, match l {
      Cenv::Mk_cenv(_, ce_exn) => ce_exn
    }, elab(e, s0, l, _UU0393_, Mode::Chk(match l {
      Cenv::Mk_cenv(_, ce_exn) => ce_exn
    }))), fn(x) {
      match m {
        Mode::Syn => Result0::Ok(SigT::ExistT(Ty::TBase(Base_ty::BUnit), Expr::ERaise(x, Ty::TBase(Base_ty::BUnit))))
        Mode::Chk(_UU03c4_) => okc(e, l, _UU0393_, Sexpr::SRaise(p, s0), _UU03c4_, Expr::ERaise(x, _UU03c4_))
      }
    })
    Sexpr::STry(p, body, cases, onr) => match onr {
      Some(ncs) => bind(try_pick(e, fn(x1) { fn(x2) { fn(x3) { fn(x4) { elab(e, x1, x2, x3, x4) } } } }, p, l, _UU0393_, cases, body, Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(_UU03c4_e, p0) => match p0 {
            (_, o) => match o {
              SigT::ExistT(_UU03c4_0, s0) => match m {
                Mode::Syn => bind(pick_syn(e, fn(x1) { fn(x2) { fn(x3) { fn(x4) { elab(e, x1, x2, x3, x4) } } } }, p, l, List::Cons((None, _UU03c4_e), _UU0393_), _UU03c4_e, cases), fn(x0) {
                  bind(arms_list(e, fn(x1) { fn(x2) { fn(x3) { fn(x4) { elab(e, x1, x2, x3, x4) } } } }, l, List::Cons((None, _UU03c4_e), _UU0393_), _UU03c4_e, x0, cases), fn(x1) {
                    bind(arms_list(e, fn(x5) { fn(x2) { fn(x3) { fn(x4) { elab(e, x5, x2, x3, x4) } } } }, l, List::Cons((None, _UU03c4_0), _UU0393_), _UU03c4_0, x0, ncs), fn(x2) {
                      Result0::Ok(SigT::ExistT(x0, Expr::ETry(s0, _UU03c4_e, Expr::EMatch(Expr::EVar(Nat::O), x0, x1), Expr::EMatch(Expr::EVar(Nat::O), x0, x2))))
                    })
                  })
                })
                Mode::Chk(_UU03c4_) => bind(arms_list(e, fn(x1) { fn(x2) { fn(x3) { fn(x4) { elab(e, x1, x2, x3, x4) } } } }, l, List::Cons((None, _UU03c4_e), _UU0393_), _UU03c4_e, _UU03c4_, cases), fn(x0) {
                  bind(arms_list(e, fn(x1) { fn(x2) { fn(x3) { fn(x4) { elab(e, x1, x2, x3, x4) } } } }, l, List::Cons((None, _UU03c4_0), _UU0393_), _UU03c4_0, _UU03c4_, ncs), fn(x1) {
                    okc(e, l, _UU0393_, Sexpr::STry(p, body, cases, Some(ncs)), _UU03c4_, Expr::ETry(s0, _UU03c4_e, Expr::EMatch(Expr::EVar(Nat::O), _UU03c4_, x0), Expr::EMatch(Expr::EVar(Nat::O), _UU03c4_, x1)))
                  })
                })
              }
            }
          }
        }
      })
      None => match m {
        Mode::Syn => bind(try_pick(e, fn(x1) { fn(x2) { fn(x3) { fn(x4) { elab(e, x1, x2, x3, x4) } } } }, p, l, _UU0393_, cases, body, Mode::Syn), fn(x) {
          match x {
            SigT::ExistT(_UU03c4_e, p0) => match p0 {
              (_, o) => match o {
                SigT::ExistT(_UU03c4_, s0) => bind(arms_list(e, fn(x1) { fn(x2) { fn(x3) { fn(x4) { elab(e, x1, x2, x3, x4) } } } }, l, List::Cons((None, _UU03c4_e), _UU0393_), _UU03c4_e, _UU03c4_, cases), fn(x0) {
                  Result0::Ok(SigT::ExistT(_UU03c4_, Expr::ETry(s0, _UU03c4_e, Expr::EMatch(Expr::EVar(Nat::O), _UU03c4_, x0), Expr::EVar(Nat::O))))
                })
              }
            }
          }
        })
        Mode::Chk(_UU03c4_) => bind(try_pick(e, fn(x1) { fn(x2) { fn(x3) { fn(x4) { elab(e, x1, x2, x3, x4) } } } }, p, l, _UU0393_, cases, body, Mode::Chk(_UU03c4_)), fn(x) {
          match x {
            SigT::ExistT(_UU03c4_e, p0) => match p0 {
              (_, o) => match o {
                SigT::ExistT(_, s0) => bind(arms_list(e, fn(x1) { fn(x2) { fn(x3) { fn(x4) { elab(e, x1, x2, x3, x4) } } } }, l, List::Cons((None, _UU03c4_e), _UU0393_), _UU03c4_e, _UU03c4_, cases), fn(x0) {
                  okc(e, l, _UU0393_, Sexpr::STry(p, body, cases, None), _UU03c4_, Expr::ETry(s0, _UU03c4_e, Expr::EMatch(Expr::EVar(Nat::O), _UU03c4_, x0), Expr::EVar(Nat::O)))
                })
              }
            }
          }
        })
      }
    }
    Sexpr::STryBang(p, body) => match m {
      Mode::Syn => bind(elab(e, body, set_exn(Ty::TError, l), _UU0393_, Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(_UU03c4_, s0) => Result0::Ok(SigT::ExistT(_UU03c4_, Expr::ETry(s0, Ty::TError, Expr::EAbort(_UU03c4_), Expr::EVar(Nat::O))))
        }
      })
      Mode::Chk(_UU03c4_) => bind(cres(e, set_exn(Ty::TError, l), _UU0393_, body, _UU03c4_, elab(e, body, set_exn(Ty::TError, l), _UU0393_, Mode::Chk(_UU03c4_))), fn(x) {
        okc(e, l, _UU0393_, Sexpr::STryBang(p, body), _UU03c4_, Expr::ETry(x, Ty::TError, Expr::EAbort(_UU03c4_), Expr::EVar(Nat::O)))
      })
    }
    Sexpr::SDefer(p, d, c, body) => bind(cres(e, Cenv::Mk_cenv(List::Nil, match l {
      Cenv::Mk_cenv(_, ce_exn) => ce_exn
    }), _UU0393_, c, Ty::TBase(Base_ty::BUnit), elab(e, c, Cenv::Mk_cenv(List::Nil, match l {
      Cenv::Mk_cenv(_, ce_exn) => ce_exn
    }), _UU0393_, Mode::Chk(Ty::TBase(Base_ty::BUnit)))), fn(x) {
      match m {
        Mode::Syn => bind(elab(e, body, l, _UU0393_, Mode::Syn), fn(x0) {
          match x0 {
            SigT::ExistT(_UU03c4_, s0) => Result0::Ok(SigT::ExistT(_UU03c4_, Expr::EDefer(d, x, s0)))
          }
        })
        Mode::Chk(_UU03c4_) => bind(cres(e, l, _UU0393_, body, _UU03c4_, elab(e, body, l, _UU0393_, Mode::Chk(_UU03c4_))), fn(x0) {
          okc(e, l, _UU0393_, Sexpr::SDefer(p, d, c, body), _UU03c4_, Expr::EDefer(d, x, x0))
        })
      }
    })
    Sexpr::SAs(p, s0, tr) => fin(e, p, l, _UU0393_, Sexpr::SAs(p, s0, tr), m, bind(bcheck(existsb(fn(x1) { eqb4(tr, x1) }, match (match e {
      Senv::Mk_senv(_, _, _, _, se_x) => se_x
    }) {
      Xenv::Mk_xenv(_, _, _, _, x_objs, _) => x_objs
    }), Elab_error::EE_NotObjectSafe(p, tr)), fn(_) {
      bind(elab(e, s0, l, _UU0393_, Mode::Syn), fn(x) {
        match x {
          SigT::ExistT(_UU03c4_, s1) => bind(coerce(e, p, _UU0393_, s1, _UU03c4_, Ty::TData(obj_name(tr), List::Nil)), fn(x0) { Result0::Ok(SigT::ExistT(Ty::TData(obj_name(tr), List::Nil), x0)) })
        }
      })
    }))
  }
}

pub fn elab_tdef(tys : List[(Ident, Nat)], st : Stype) -> Result0[Tdef, Elab_error] {
  let tps = match st {
    Stype::Mk_stype(_, _, st_tparams, _) => st_tparams
  }
  let n = length(tps)
  match (match st {
    Stype::Mk_stype(_, _, _, st_body) => st_body
  }) {
    Sdecl::SDEnum(cs) => bind(mapM(fn(c) {
      bind(mapM(fn(x1) { elab_ty(tys, tps, x1) }, snd(c)), fn(_UU03c4_s) { Result0::Ok(Cdef::Mk_cdef(fst(c), _UU03c4_s)) })
    }, cs), fn(cds) {
      Result0::Ok(Tdef::Mk_tdef(match st {
        Stype::Mk_stype(_, st_name, _, _) => st_name
      }, n, cds, false))
    })
    Sdecl::SDStruct(fs) => bind(mapM(fn(f) {
      bind(elab_ty(tys, tps, snd(f)), fn(_UU03c4_) {
        Result0::Ok(match snd(fst(f)) {
          true => Ty::TRef(_UU03c4_)
          false => _UU03c4_
        })
      })
    }, fs), fn(_UU03c4_s) {
      Result0::Ok(Tdef::Mk_tdef(match st {
        Stype::Mk_stype(_, st_name, _, _) => st_name
      }, n, List::Cons(Cdef::Mk_cdef(match st {
        Stype::Mk_stype(_, st_name, _, _) => st_name
      }, _UU03c4_s), List::Nil), false))
    })
    Sdecl::SDTupleStruct(ts) => bind(mapM(fn(x1) { elab_ty(tys, tps, x1) }, ts), fn(_UU03c4_s) {
      Result0::Ok(Tdef::Mk_tdef(match st {
        Stype::Mk_stype(_, st_name, _, _) => st_name
      }, n, List::Cons(Cdef::Mk_cdef(match st {
        Stype::Mk_stype(_, st_name, _, _) => st_name
      }, _UU03c4_s), List::Nil), false))
    })
    Sdecl::SDError(cs) => bind(mapM(fn(c) {
      bind(mapM(fn(x1) { elab_ty(tys, tps, x1) }, snd(c)), fn(_UU03c4_s) { Result0::Ok(Cdef::Mk_cdef(fst(c), _UU03c4_s)) })
    }, cs), fn(cds) {
      Result0::Ok(Tdef::Mk_tdef(match st {
        Stype::Mk_stype(_, st_name, _, _) => st_name
      }, n, cds, true))
    })
  }
}

pub fn sty_mentions(x : Ident, t : Sty) -> Bool {
  let go = {
    letrec go = fn(ts) {
      match ts {
        List::Nil => false
        List::Cons(t0, ts_) => match sty_mentions(x, t0) {
          true => true
          false => go(ts_)
        }
      }
    }
    go
  }
  match t {
    Sty::SName(_, n, args) => match eqDec_ident(n)(x) {
      true => true
      false => go(args)
    }
    Sty::STuple(_, ts) => go(ts)
    Sty::SArrow(_, ps, r, eff) => match (match go(ps) {
      true => true
      false => sty_mentions(x, r)
    }) {
      true => true
      false => match eff {
        Some(t0) => sty_mentions(x, t0)
        None => false
      }
    }
    Sty::SObj(_, _) => false
  }
}

pub fn sig_tparams(f : Sfun) -> List[Ident] {
  let poly = match existsb(fn(xt) {
    sty_mentions(String0::String1(Ascii::Ascii0(true, true, true, true, true, true, false, false), String0::EmptyString), snd(xt))
  }, match f {
    Sfun::Mk_sfun(_, _, _, _, _, sf_params, _, _, _) => sf_params
  }) {
    true => true
    false => match (match f {
      Sfun::Mk_sfun(_, _, _, _, _, _, _, sf_eff, _) => sf_eff
    }) {
      Some(t) => sty_mentions(String0::String1(Ascii::Ascii0(true, true, true, true, true, true, false, false), String0::EmptyString), t)
      None => false
    }
  }
  match poly {
    true => app(match f {
      Sfun::Mk_sfun(_, _, _, sf_tparams, _, _, _, _, _) => sf_tparams
    }, List::Cons(String0::String1(Ascii::Ascii0(true, true, true, true, true, true, false, false), String0::EmptyString), List::Nil))
    false => match f {
      Sfun::Mk_sfun(_, _, _, sf_tparams, _, _, _, _, _) => sf_tparams
    }
  }
}

pub fn fun_name(f : Sfun) -> Ident {
  match (match f {
    Sfun::Mk_sfun(_, sf_self, _, _, _, _, _, _, _) => sf_self
  }) {
    Some(t) => append(t, append(String0::String1(Ascii::Ascii0(false, true, false, true, true, true, false, false), String0::String1(Ascii::Ascii0(false, true, false, true, true, true, false, false), String0::EmptyString)), match f {
      Sfun::Mk_sfun(_, _, sf_name, _, _, _, _, _, _) => sf_name
    }))
    None => match f {
      Sfun::Mk_sfun(_, _, sf_name, _, _, _, _, _, _) => sf_name
    }
  }
}

pub fn bound_ctx(p : Pos, tps : List[Ident], bs : List[(Ident, Ident)]) -> Result0[List[(Ident, Nat)], Elab_error] {
  mapM(fn(b) {
    bind(of_opt(index_of(fst(b), tps), Elab_error::EE_UnknownType(p, fst(b))), fn(i) { Result0::Ok((snd(b), i)) })
  }, bs)
}

pub fn dict_ty(c : (Ident, Nat)) -> Ty {
  Ty::TData(fst(c), List::Cons(Ty::TVar(snd(c)), List::Nil))
}

pub fn elab_sig(tys : List[(Ident, Nat)], f : Sfun) -> Result0[Fdef, Elab_error] {
  let tps = sig_tparams(f)
  bind(bound_ctx(match f {
    Sfun::Mk_sfun(sf_pos, _, _, _, _, _, _, _, _) => sf_pos
  }, tps, match f {
    Sfun::Mk_sfun(_, _, _, _, sf_bounds, _, _, _, _) => sf_bounds
  }), fn(ctx) {
    bind(mapM(fn(xt) { elab_ty(tys, tps, snd(xt)) }, match f {
      Sfun::Mk_sfun(_, _, _, _, _, sf_params, _, _, _) => sf_params
    }), fn(_UU03c4_s) {
      bind(match (match f {
        Sfun::Mk_sfun(_, _, _, _, _, _, sf_ret, _, _) => sf_ret
      }) {
        Some(t) => elab_ty(tys, tps, t)
        None => Result0::Ok(Ty::TBase(Base_ty::BUnit))
      }, fn(_UU03c4_) {
        bind(match (match f {
          Sfun::Mk_sfun(_, _, _, _, _, _, _, sf_eff, _) => sf_eff
        }) {
          Some(t) => elab_ty(tys, tps, t)
          None => Result0::Ok(Ty::TBase(Base_ty::BNever))
        }, fn(_UU03b5_) {
          Result0::Ok(Fdef::Mk_fdef(fun_name(f), length(tps), app(map(fn(x1) { dict_ty(x1) }, ctx), _UU03c4_s), _UU03c4_, _UU03b5_, Expr::ELit(Lit::LUnit)))
        })
      })
    })
  })
}

pub fn dict_ctx(tps : List[Ident], ctx : List[(Ident, Nat)]) -> Lctx {
  map(fn(c) {
    (Some(dict_var(fst(c), nth(snd(c), tps, String0::EmptyString))), dict_ty(c))
  }, ctx)
}

pub fn body_lets(e : Senv, tps : List[Ident], ctx : List[(Ident, Nat)]) -> List[((((Ident, Ident), Nat), Ident), Nat)] {
  super_lets(trs(e), mul(length(trs(e)), Nat::S(length(ctx))), List::Nil, map(fn(c) { ((fst(c), nth(snd(c), tps, String0::EmptyString)), snd(c)) }, ctx))
}

pub fn body_asm(e : Senv, tps : List[Ident], ctx : List[(Ident, Nat)]) -> List[((Ident, Ty), Ident)] {
  app(map(fn(c) {
    ((fst(c), Ty::TVar(snd(c))), dict_var(fst(c), nth(snd(c), tps, String0::EmptyString)))
  }, ctx), map(fn(l) {
    match l {
      (y, _) => match y {
        (y1, _) => match y1 {
          (y3, i) => match y3 {
            (sn, x) => ((sn, Ty::TVar(i)), dict_var(sn, x))
          }
        }
      }
    }
  }, body_lets(e, tps, ctx)))
}

pub fn with_asm(e : Senv, tps : List[Ident], asm0 : List[((Ident, Ty), Ident)]) -> Senv {
  let x = match e {
    Senv::Mk_senv(_, _, _, _, se_x) => se_x
  }
  Senv::Mk_senv(match e {
    Senv::Mk_senv(se_tys, _, _, _, _) => se_tys
  }, match e {
    Senv::Mk_senv(_, se_hdr, _, _, _) => se_hdr
  }, match e {
    Senv::Mk_senv(_, _, se_sinfo, _, _) => se_sinfo
  }, tps, Xenv::Mk_xenv(match x {
    Xenv::Mk_xenv(x_traits, _, _, _, _, _) => x_traits
  }, match x {
    Xenv::Mk_xenv(_, x_insts, _, _, _, _) => x_insts
  }, match x {
    Xenv::Mk_xenv(_, _, x_bounds, _, _, _) => x_bounds
  }, match x {
    Xenv::Mk_xenv(_, _, _, x_meths, _, _) => x_meths
  }, match x {
    Xenv::Mk_xenv(_, _, _, _, x_objs, _) => x_objs
  }, asm0))
}

pub fn sup_lets_dec(e : Senv, ls : List[((((Ident, Ident), Nat), Ident), Nat)], _UU0393_ : Lctx) -> Result0[SigT[List[Expr], Lctx], Elab_error] {
  match ls {
    List::Nil => Result0::Ok(SigT::ExistT(List::Nil, _UU0393_))
    List::Cons(p, ls_) => match p {
      (p0, j) => match p0 {
        (p1, t) => match p1 {
          (p2, i) => match p2 {
            (sn, x) => {
              let p3 = Pos::Mk_pos(N::N0, N::N0)
              bind(of_option(lookup_local(dict_var(t, x), _UU0393_), Elab_error::EE_Unbound(p3, dict_var(t, x))), fn(x0) {
                bind(of_option(nth_error(ctx_of(_UU0393_), x0), Elab_error::EE_Unbound(p3, dict_var(t, x))), fn(x1) {
                  match ty_eq_dec(x1)(Ty::TData(t, List::Cons(Ty::TVar(i), List::Nil))) {
                    true => bind(field_proj_dec(e, p3, t, List::Cons(Ty::TVar(i), List::Nil), j, Expr::EVar(x0)), fn(x2) {
                      match x2 {
                        (e0, u) => match ty_eq_dec(u)(Ty::TData(sn, List::Cons(Ty::TVar(i), List::Nil))) {
                          true => bind(sup_lets_dec(e, ls_, List::Cons((Some(dict_var(sn, x)), Ty::TData(sn, List::Cons(Ty::TVar(i), List::Nil))), _UU0393_)), fn(x3) {
                            match x3 {
                              SigT::ExistT(es, s) => Result0::Ok(SigT::ExistT(List::Cons(e0, es), s))
                            }
                          })
                          false => Result0::Err(Elab_error::EE_NoInstance(p3, sn, Ty::TVar(i)))
                        }
                      }
                    })
                    false => Result0::Err(Elab_error::EE_NoInstance(p3, t, Ty::TVar(i)))
                  }
                })
              })
            }
          }
        }
      }
    }
  }
}

pub fn body_dec(e : Senv, tps : List[Ident], ctx : List[(Ident, Nat)], _UU0393_p : Lctx, r : Ty, _UU03b5_ : Ty, body : Sexpr) -> Result0[Expr, Elab_error] {
  bind(sup_lets_dec(e, body_lets(e, tps, ctx), app(dict_ctx(tps, ctx), _UU0393_p)), fn(x) {
    match x {
      SigT::ExistT(es, s) => bind(cres(with_asm(e, tps, body_asm(e, tps, ctx)), fun_env(r, _UU03b5_), s, body, r, elab(with_asm(e, tps, body_asm(e, tps, ctx)), body, fun_env(r, _UU03b5_), s, Mode::Chk(r))), fn(x0) {
        Result0::Ok(fold_right(fn(x1) { fn(x2) { Expr::ELet(x1, x2) } }, eblock(r, x0), es))
      })
    }
  })
}

pub fn elab_body(e : Senv, tps : List[Ident], ctx : List[(Ident, Nat)], _UU0393_p : Lctx, r : Ty, _UU03b5_ : Ty, body : Sexpr) -> Result0[Expr, Elab_error] {
  bind(body_dec(e, tps, ctx, _UU0393_p, r, _UU03b5_, body), fn(x) { Result0::Ok(x) })
}

pub fn elab_fun(e : Senv, f : Sfun, sig : Fdef) -> Result0[Fdef, Elab_error] {
  let tps = sig_tparams(f)
  bind(bound_ctx(match f {
    Sfun::Mk_sfun(sf_pos, _, _, _, _, _, _, _, _) => sf_pos
  }, tps, match f {
    Sfun::Mk_sfun(_, _, _, _, sf_bounds, _, _, _, _) => sf_bounds
  }), fn(ctx) {
    let _UU0393_p = combine(map(fn(xt) { Some(fst(xt)) }, match f {
      Sfun::Mk_sfun(_, _, _, _, _, sf_params, _, _, _) => sf_params
    }), skipn(length(ctx), match sig {
      Fdef::Mk_fdef(_, _, fd_params, _, _, _) => fd_params
    }))
    bind(elab_body(e, tps, ctx, _UU0393_p, match sig {
      Fdef::Mk_fdef(_, _, _, fd_ret, _, _) => fd_ret
    }, match sig {
      Fdef::Mk_fdef(_, _, _, _, fd_eff, _) => fd_eff
    }, match f {
      Sfun::Mk_sfun(_, _, _, _, _, _, _, _, sf_body) => sf_body
    }), fn(b) {
      Result0::Ok(Fdef::Mk_fdef(match sig {
        Fdef::Mk_fdef(fd_name, _, _, _, _, _) => fd_name
      }, match sig {
        Fdef::Mk_fdef(_, fd_tparams, _, _, _, _) => fd_tparams
      }, match sig {
        Fdef::Mk_fdef(_, _, fd_params, _, _, _) => fd_params
      }, match sig {
        Fdef::Mk_fdef(_, _, _, fd_ret, _, _) => fd_ret
      }, match sig {
        Fdef::Mk_fdef(_, _, _, _, fd_eff, _) => fd_eff
      }, b))
    })
  })
}

pub fn elab_funs(e : Senv, fs : List[Sfun], sigs : List[Fdef]) -> Result0[List[Fdef], Elab_error] {
  match fs {
    List::Nil => Result0::Ok(List::Nil)
    List::Cons(f, fs_) => match sigs {
      List::Nil => Result0::Ok(List::Nil)
      List::Cons(sig, sigs_) => bind(elab_fun(e, f, sig), fn(fd) {
        bind(elab_funs(e, fs_, sigs_), fn(fds) { Result0::Ok(List::Cons(fd, fds)) })
      })
    }
  }
}

pub fn elab_trait(tys : List[(Ident, Nat)], t : Strait) -> Result0[Trinfo, Elab_error] {
  bind(mapM(fn(m) {
    bind(mapM(fn(x1) {
      elab_ty(tys, List::Cons(String0::String1(Ascii::Ascii0(true, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString)))), List::Nil), x1)
    }, match m {
      Smeth::Mk_smeth(_, sm_params, _, _, _) => sm_params
    }), fn(ps) {
      bind(elab_ty(tys, List::Cons(String0::String1(Ascii::Ascii0(true, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString)))), List::Nil), match m {
        Smeth::Mk_smeth(_, _, sm_ret, _, _) => sm_ret
      }), fn(r) {
        bind(match (match m {
          Smeth::Mk_smeth(_, _, _, sm_eff, _) => sm_eff
        }) {
          Some(t0) => elab_ty(tys, List::Cons(String0::String1(Ascii::Ascii0(true, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString)))), List::Nil), t0)
          None => Result0::Ok(Ty::TBase(Base_ty::BNever))
        }, fn(_UU03b5_) {
          Result0::Ok(Msig::Mk_msig(match m {
            Smeth::Mk_smeth(sm_name, _, _, _, _) => sm_name
          }, ps, r, _UU03b5_))
        })
      })
    })
  }, match t {
    Strait::Mk_strait(_, _, _, str_methods) => str_methods
  }), fn(ms) {
    Result0::Ok(Trinfo::Mk_trinfo(match t {
      Strait::Mk_strait(_, str_name, _, _) => str_name
    }, match t {
      Strait::Mk_strait(_, _, str_supers, _) => str_supers
    }, ms, map(fn(s) {
      match s {
        Smeth::Mk_smeth(sm_name, _, _, _, _) => sm_name
      }
    }, filter(fn(s) {
      match s {
        Smeth::Mk_smeth(_, _, _, _, sm_default) => sm_default
      }
    }, match t {
      Strait::Mk_strait(_, _, _, str_methods) => str_methods
    }))))
  })
}

pub(all) enum Igroup {
  Mk_igroup(Pos, Ident, Ty, List[Ident], List[(Ident, Ident)], List[Simethod])
}

pub fn add_impl(gs : List[Igroup], p : Pos, tr : Ident, _UU03c4_ : Ty, tps : List[Ident], bs : List[(Ident, Ident)], m : Option[Simethod]) -> List[Igroup] {
  match gs {
    List::Nil => List::Cons(Igroup::Mk_igroup(p, tr, _UU03c4_, tps, bs, match m {
      Some(m0) => List::Cons(m0, List::Nil)
      None => List::Nil
    }), List::Nil)
    List::Cons(g, gs_) => match (match eqDec_ident(match g {
      Igroup::Mk_igroup(_, ig_trait, _, _, _, _) => ig_trait
    })(tr) {
      true => eqDec_ty(match g {
        Igroup::Mk_igroup(_, _, ig_head, _, _, _) => ig_head
      })(_UU03c4_)
      false => false
    }) {
      true => List::Cons(Igroup::Mk_igroup(match g {
        Igroup::Mk_igroup(ig_pos, _, _, _, _, _) => ig_pos
      }, tr, _UU03c4_, match g {
        Igroup::Mk_igroup(_, _, _, ig_tparams, _, _) => ig_tparams
      }, match g {
        Igroup::Mk_igroup(_, _, _, _, ig_bounds, _) => ig_bounds
      }, app(match g {
        Igroup::Mk_igroup(_, _, _, _, _, ig_methods) => ig_methods
      }, match m {
        Some(m0) => List::Cons(m0, List::Nil)
        None => List::Nil
      })), gs_)
      false => List::Cons(g, add_impl(gs_, p, tr, _UU03c4_, tps, bs, m))
    }
  }
}

pub fn inst_name(tr : Ident, h : Ident) -> Ident {
  append(String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, false, false), String0::EmptyString))))), append(tr, append(String0::String1(Ascii::Ascii0(false, false, true, false, false, true, false, false), String0::EmptyString), h)))
}

pub fn impl_name(tr : Ident, h : Ident, m : Ident) -> Ident {
  append(String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, false, false), String0::EmptyString))))), append(tr, append(String0::String1(Ascii::Ascii0(false, false, true, false, false, true, false, false), String0::EmptyString), append(h, append(String0::String1(Ascii::Ascii0(false, false, true, false, false, true, false, false), String0::EmptyString), m)))))
}

pub fn default_name(tr : Ident, m : Ident) -> Ident {
  append(String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, false, false), String0::EmptyString)))))))), append(tr, append(String0::String1(Ascii::Ascii0(false, false, true, false, false, true, false, false), String0::EmptyString), m)))
}

pub(all) enum Iinfo {
  Mk_iinfo(Igroup, Trinfo, Ident, List[(Ident, Nat)], Idef)
}

pub fn check_group(trs0 : List[Trinfo], g : Igroup) -> Result0[Iinfo, Elab_error] {
  let p = match g {
    Igroup::Mk_igroup(ig_pos, _, _, _, _, _) => ig_pos
  }
  let n = length(match g {
    Igroup::Mk_igroup(_, _, _, ig_tparams, _, _) => ig_tparams
  })
  bind(of_opt(find_trait(trs0, match g {
    Igroup::Mk_igroup(_, ig_trait, _, _, _, _) => ig_trait
  }), Elab_error::EE_UnknownType(p, match g {
    Igroup::Mk_igroup(_, ig_trait, _, _, _, _) => ig_trait
  })), fn(ti) {
    bind(of_opt(head_args(match g {
      Igroup::Mk_igroup(_, _, ig_head, _, _, _) => ig_head
    }), Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString)))))))))))))))))))), fn(x) {
      match x {
        (h, args) => bind(match eqDec_list()(eqDec_ty)(args)(map(fn(x0) { Ty::TVar(x0) }, seq(Nat::O, n))) {
          true => Result0::Ok(())
          false => Result0::Err(Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, false, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, false, false), String0::EmptyString))))))))))))))))))))))))))))))))))))))
        }, fn(_) {
          bind(of_opt(head_name(match g {
            Igroup::Mk_igroup(_, _, ig_head, _, _, _) => ig_head
          }), Elab_error::EE_Unsupported(p, String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, false, true, false, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString)))))))))))))))))))), fn(h0) {
            bind(bound_ctx(p, match g {
              Igroup::Mk_igroup(_, _, _, ig_tparams, _, _) => ig_tparams
            }, match g {
              Igroup::Mk_igroup(_, _, _, _, ig_bounds, _) => ig_bounds
            }), fn(ctx) {
              bind(mapM(fn(s) {
                match (match existsb(fn(im) {
                  eqDec_ident(match im {
                    Simethod::Mk_simethod(sim_name, _, _, _, _) => sim_name
                  })(match s {
                    Msig::Mk_msig(ms_name, _, _, _) => ms_name
                  })
                }, match g {
                  Igroup::Mk_igroup(_, _, _, _, _, ig_methods) => ig_methods
                }) {
                  true => true
                  false => existsb(eqDec_ident(match s {
                    Msig::Mk_msig(ms_name, _, _, _) => ms_name
                  }), match ti {
                    Trinfo::Mk_trinfo(_, _, _, ti_defaults) => ti_defaults
                  })
                }) {
                  true => Result0::Ok(())
                  false => Result0::Err(Elab_error::EE_MissingMethod(p, match g {
                    Igroup::Mk_igroup(_, ig_trait, _, _, _, _) => ig_trait
                  }, match s {
                    Msig::Mk_msig(ms_name, _, _, _) => ms_name
                  }))
                }
              }, match ti {
                Trinfo::Mk_trinfo(_, _, ti_methods, _) => ti_methods
              }), fn(_) {
                bind(match noDup_dec(eqDec_ident, map(fn(s) {
                  match s {
                    Simethod::Mk_simethod(sim_name, _, _, _, _) => sim_name
                  }
                }, match g {
                  Igroup::Mk_igroup(_, _, _, _, _, ig_methods) => ig_methods
                })) {
                  true => Result0::Ok(())
                  false => Result0::Err(Elab_error::EE_Overlap(p))
                }, fn(_) {
                  bind(mapM(fn(im) {
                    match method_of(ti, match im {
                      Simethod::Mk_simethod(sim_name, _, _, _, _) => sim_name
                    }) {
                      Some(_) => Result0::Ok(())
                      None => Result0::Err(Elab_error::EE_NoMethod(p, match im {
                        Simethod::Mk_simethod(sim_name, _, _, _, _) => sim_name
                      }, match g {
                        Igroup::Mk_igroup(_, _, ig_head, _, _, _) => ig_head
                      }))
                    }
                  }, match g {
                    Igroup::Mk_igroup(_, _, _, _, _, ig_methods) => ig_methods
                  }), fn(_) {
                    Result0::Ok(Iinfo::Mk_iinfo(g, ti, h0, ctx, Idef::Mk_idef(match g {
                      Igroup::Mk_igroup(_, ig_trait, _, _, _, _) => ig_trait
                    }, h, n, ctx, inst_name(match g {
                      Igroup::Mk_igroup(_, ig_trait, _, _, _, _) => ig_trait
                    }, h0))))
                  })
                })
              })
            })
          })
        })
      }
    })
  })
}

pub fn group_sigs(ii : Iinfo) -> List[Fdef] {
  let g = match ii {
    Iinfo::Mk_iinfo(ii_group, _, _, _, _) => ii_group
  }
  let _UU03c3_ = {
    let a1 = {
      let a1 = List::Cons(match g {
        Igroup::Mk_igroup(_, _, ig_head, _, _, _) => ig_head
      }, List::Nil)
      fn(x1) { inst(a1, x1) }
    }
    fn(x1) { tsubst(a1, x1) }
  }
  let n = length(match g {
    Igroup::Mk_igroup(_, _, _, ig_tparams, _, _) => ig_tparams
  })
  let dicts = map(fn(x1) { dict_ty(x1) }, match ii {
    Iinfo::Mk_iinfo(_, _, _, ii_ctx, _) => ii_ctx
  })
  List::Cons(Fdef::Mk_fdef(inst_name(match g {
    Igroup::Mk_igroup(_, ig_trait, _, _, _, _) => ig_trait
  }, match ii {
    Iinfo::Mk_iinfo(_, _, ii_name, _, _) => ii_name
  }), n, dicts, Ty::TData(match g {
    Igroup::Mk_igroup(_, ig_trait, _, _, _, _) => ig_trait
  }, List::Cons(match g {
    Igroup::Mk_igroup(_, _, ig_head, _, _, _) => ig_head
  }, List::Nil)), Ty::TBase(Base_ty::BNever), Expr::ELit(Lit::LUnit)), flat_map(fn(im) {
    match method_of(match ii {
      Iinfo::Mk_iinfo(_, ii_ti, _, _, _) => ii_ti
    }, match im {
      Simethod::Mk_simethod(sim_name, _, _, _, _) => sim_name
    }) {
      Some(p) => match p {
        (_, s) => List::Cons(Fdef::Mk_fdef(impl_name(match g {
          Igroup::Mk_igroup(_, ig_trait, _, _, _, _) => ig_trait
        }, match ii {
          Iinfo::Mk_iinfo(_, _, ii_name, _, _) => ii_name
        }, match im {
          Simethod::Mk_simethod(sim_name, _, _, _, _) => sim_name
        }), n, app(dicts, map(_UU03c3_, match s {
          Msig::Mk_msig(_, ms_params, _, _) => ms_params
        })), _UU03c3_(match s {
          Msig::Mk_msig(_, _, ms_ret, _) => ms_ret
        }), _UU03c3_(match s {
          Msig::Mk_msig(_, _, _, ms_eff) => ms_eff
        }), Expr::ELit(Lit::LUnit)), List::Nil)
      }
      None => List::Nil
    }
  }, match g {
    Igroup::Mk_igroup(_, _, _, _, _, ig_methods) => ig_methods
  }))
}

pub fn inst_body(insts : List[Idef], _ : List[Trinfo], _ : List[(Ident, Ident)], ii : Iinfo) -> Result0[Expr, Elab_error] {
  let g = match ii {
    Iinfo::Mk_iinfo(ii_group, _, _, _, _) => ii_group
  }
  let ti = match ii {
    Iinfo::Mk_iinfo(_, ii_ti, _, _, _) => ii_ti
  }
  let p = match g {
    Igroup::Mk_igroup(ig_pos, _, _, _, _, _) => ig_pos
  }
  let n = length(match g {
    Igroup::Mk_igroup(_, _, _, ig_tparams, _, _) => ig_tparams
  })
  let nc = length(match ii {
    Iinfo::Mk_iinfo(_, _, _, ii_ctx, _) => ii_ctx
  })
  let tvars = map(fn(x) { Ty::TVar(x) }, seq(Nat::O, n))
  let _UU03c4_h = match g {
    Igroup::Mk_igroup(_, _, ig_head, _, _, _) => ig_head
  }
  let _UU03c3_ = {
    let a1 = fn(x1) { inst(List::Cons(_UU03c4_h, List::Nil), x1) }
    fn(x1) { tsubst(a1, x1) }
  }
  let _UU0398_ = map(fn(jc) { ((fst(snd(jc)), Ty::TVar(snd(snd(jc)))), Expr::EVar(fst(jc))) }, combine(seq(Nat::O, nc), match ii {
    Iinfo::Mk_iinfo(_, _, _, ii_ctx, _) => ii_ctx
  }))
  bind(mapM(fn(s) {
    match entails_dec(insts, _UU0398_, s, _UU03c4_h) {
      Sumor::Inleft(s0) => Result0::Ok(s0)
      Sumor::Inright => Result0::Err(Elab_error::EE_NoInstance(p, s, _UU03c4_h))
    }
  }, match ti {
    Trinfo::Mk_trinfo(_, ti_supers, _, _) => ti_supers
  }), fn(sups) {
    bind(mapM(fn(s) {
      let ps = map(_UU03c3_, match s {
        Msig::Mk_msig(_, ms_params, _, _) => ms_params
      })
      let k = length(ps)
      let lvars = map(fn(x) { Expr::EVar(x) }, seq(Nat::O, k))
      let dvars = map(fn(j) { Expr::EVar(add(k, j)) }, seq(Nat::O, nc))
      match existsb(fn(im) {
        eqDec_ident(match im {
          Simethod::Mk_simethod(sim_name, _, _, _, _) => sim_name
        })(match s {
          Msig::Mk_msig(ms_name, _, _, _) => ms_name
        })
      }, match g {
        Igroup::Mk_igroup(_, _, _, _, _, ig_methods) => ig_methods
      }) {
        true => Result0::Ok(Expr::ELam(ps, _UU03c3_(match s {
          Msig::Mk_msig(_, _, ms_ret, _) => ms_ret
        }), _UU03c3_(match s {
          Msig::Mk_msig(_, _, _, ms_eff) => ms_eff
        }), Expr::EApp(Expr::EGlobal(impl_name(match g {
          Igroup::Mk_igroup(_, ig_trait, _, _, _, _) => ig_trait
        }, match ii {
          Iinfo::Mk_iinfo(_, _, ii_name, _, _) => ii_name
        }, match s {
          Msig::Mk_msig(ms_name, _, _, _) => ms_name
        }), tvars), app(dvars, lvars))))
        false => {
          let self0 = Expr::EApp(Expr::EGlobal(inst_name(match g {
            Igroup::Mk_igroup(_, ig_trait, _, _, _, _) => ig_trait
          }, match ii {
            Iinfo::Mk_iinfo(_, _, ii_name, _, _) => ii_name
          }), tvars), dvars)
          Result0::Ok(Expr::ELam(ps, _UU03c3_(match s {
            Msig::Mk_msig(_, _, ms_ret, _) => ms_ret
          }), _UU03c3_(match s {
            Msig::Mk_msig(_, _, _, ms_eff) => ms_eff
          }), Expr::EApp(Expr::EGlobal(default_name(match g {
            Igroup::Mk_igroup(_, ig_trait, _, _, _, _) => ig_trait
          }, match s {
            Msig::Mk_msig(ms_name, _, _, _) => ms_name
          }), List::Cons(_UU03c4_h, List::Nil)), List::Cons(self0, lvars))))
        }
      }
    }, match ti {
      Trinfo::Mk_trinfo(_, _, ti_methods, _) => ti_methods
    }), fn(ms) {
      Result0::Ok(Expr::EConstr(match g {
        Igroup::Mk_igroup(_, ig_trait, _, _, _, _) => ig_trait
      }, match g {
        Igroup::Mk_igroup(_, ig_trait, _, _, _, _) => ig_trait
      }, List::Cons(_UU03c4_h, List::Nil), Expr::ETuple(app(sups, ms))))
    })
  })
}

pub fn obj_insts(trs0 : List[Trinfo], tr : Ident) -> List[(Idef, Fdef)] {
  let on = obj_name(tr)
  map(fn(sn) {
    (Idef::Mk_idef(sn, Head::HData(on), Nat::O, List::Nil, inst_name(sn, on)), Fdef::Mk_fdef(inst_name(sn, on), Nat::O, List::Nil, Ty::TData(sn, List::Cons(Ty::TData(on, List::Nil), List::Nil)), Ty::TBase(Base_ty::BNever), Expr::ELit(Lit::LUnit)))
  }, closure(trs0, tr))
}

pub fn obj_inst_body(insts : List[Idef], trs0 : List[Trinfo], tr : Ident, sn : Ident) -> Result0[Expr, Elab_error] {
  let on = obj_name(tr)
  let _UU03c4_o = Ty::TData(on, List::Nil)
  let fs = obj_fields(trs0, tr)
  bind(of_opt(find_trait(trs0, sn), Elab_error::EE_UnknownType(Pos::Mk_pos(N::N0, N::N0), sn)), fn(ti) {
    bind(mapM(fn(s_) {
      match entails_dec(insts, List::Nil, s_, _UU03c4_o) {
        Sumor::Inleft(s) => Result0::Ok(s)
        Sumor::Inright => Result0::Err(Elab_error::EE_NoInstance(Pos::Mk_pos(N::N0, N::N0), s_, _UU03c4_o))
      }
    }, match ti {
      Trinfo::Mk_trinfo(_, ti_supers, _, _) => ti_supers
    }), fn(sups) {
      bind(mapM(fn(s) {
        bind(of_opt(index_of(match s {
          Msig::Mk_msig(ms_name, _, _, _) => ms_name
        }, map(fn(sm) {
          match snd(sm) {
            Msig::Mk_msig(ms_name, _, _, _) => ms_name
          }
        }, fs)), Elab_error::EE_NotObjectSafe(Pos::Mk_pos(N::N0, N::N0), tr)), fn(j) {
          let ps = tl(match s {
            Msig::Mk_msig(_, ms_params, _, _) => ms_params
          })
          let k = length(ps)
          Result0::Ok(Expr::ELam(List::Cons(_UU03c4_o, ps), match s {
            Msig::Mk_msig(_, _, ms_ret, _) => ms_ret
          }, match s {
            Msig::Mk_msig(_, _, _, ms_eff) => ms_eff
          }, Expr::EApp(field_of(on, length(fs), j, Expr::EVar(Nat::O), obj_field_ty(s)), map(fn(x) { Expr::EVar(x) }, seq(Nat::S(Nat::O), k)))))
        })
      }, match ti {
        Trinfo::Mk_trinfo(_, _, ti_methods, _) => ti_methods
      }), fn(ms) {
        Result0::Ok(Expr::EConstr(sn, sn, List::Cons(_UU03c4_o, List::Nil), Expr::ETuple(app(sups, ms))))
      })
    })
  })
}

pub fn elab_prog(sp : Sprog) -> Result0[(Genv, Expr), Elab_error] {
  let trnames = map(fn(s) {
    match s {
      Strait::Mk_strait(_, str_name, _, _) => str_name
    }
  }, match sp {
    Sprog::Mk_sprog(_, sp_traits, _, _, _) => sp_traits
  })
  let tys = app(List::Cons((String0::String1(Ascii::Ascii0(true, true, true, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::EmptyString)))))), Nat::S(Nat::O)), List::Cons((String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString))), Nat::S(Nat::O)), List::Cons((String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))), Nat::S(Nat::S(Nat::O))), List::Cons((String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))), Nat::O), List::Nil)))), app(map(fn(st) {
    (match st {
      Stype::Mk_stype(_, st_name, _, _) => st_name
    }, length(match st {
      Stype::Mk_stype(_, _, st_tparams, _) => st_tparams
    }))
  }, match sp {
    Sprog::Mk_sprog(sp_types, _, _, _, _) => sp_types
  }), app(map(fn(n) { (n, Nat::S(Nat::O)) }, trnames), map(fn(n) { (obj_name(n), Nat::O) }, trnames))))
  let sinfo = List::Cons((String0::String1(Ascii::Ascii0(false, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString))), List::Cons(String0::String1(Ascii::Ascii0(false, true, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString))), List::Nil)), flat_map(fn(st) {
    match (match st {
      Stype::Mk_stype(_, _, _, st_body) => st_body
    }) {
      Sdecl::SDEnum(_) => List::Nil
      Sdecl::SDStruct(fs) => List::Cons((match st {
        Stype::Mk_stype(_, st_name, _, _) => st_name
      }, map(fn(f) { fst(fst(f)) }, fs)), List::Nil)
      _ => List::Nil
    }
  }, match sp {
    Sprog::Mk_sprog(sp_types, _, _, _, _) => sp_types
  }))
  bind(mapM(fn(x1) { elab_trait(tys, x1) }, match sp {
    Sprog::Mk_sprog(_, sp_traits, _, _, _) => sp_traits
  }), fn(trs0) {
    let objs = filter(fn(x1) { obj_safe(trs0, x1) }, trnames)
    bind(mapM(fn(x1) { elab_tdef(tys, x1) }, match sp {
      Sprog::Mk_sprog(sp_types, _, _, _, _) => sp_types
    }), fn(tds) {
      let types = app(List::Cons(option_tdef, List::Cons(ref_tdef, List::Cons(result_tdef, List::Cons(failure_tdef, List::Nil)))), app(tds, app(map(fn(x1) { dict_tdef(x1) }, trs0), map(fn(x1) { obj_tdef(trs0, x1) }, objs))))
      bind(fold_left(fn(acc) {
        fn(i) {
          bind(acc, fn(gs) {
            match (match i {
              Simpl::Mk_simpl(_, _, _, _, si_self, _) => si_self
            }) {
              Some(t) => bind(elab_ty(tys, match i {
                Simpl::Mk_simpl(_, si_tparams, _, _, _, _) => si_tparams
              }, t), fn(_UU03c4_) {
                Result0::Ok(add_impl(gs, match i {
                  Simpl::Mk_simpl(si_pos, _, _, _, _, _) => si_pos
                }, match i {
                  Simpl::Mk_simpl(_, _, _, si_trait, _, _) => si_trait
                }, _UU03c4_, match i {
                  Simpl::Mk_simpl(_, si_tparams, _, _, _, _) => si_tparams
                }, match i {
                  Simpl::Mk_simpl(_, _, si_bounds, _, _, _) => si_bounds
                }, match i {
                  Simpl::Mk_simpl(_, _, _, _, _, si_method) => si_method
                }))
              })
              None => Result0::Ok(gs)
            }
          })
        }
      }, match sp {
        Sprog::Mk_sprog(_, _, sp_impls, _, _) => sp_impls
      }, Result0::Ok(List::Nil)), fn(groups) {
        bind(mapM(fn(x1) { check_group(trs0, x1) }, groups), fn(iis) {
          let defaults = flat_map(fn(i) {
            match (match i {
              Simpl::Mk_simpl(_, _, _, _, si_self, _) => si_self
            }) {
              Some(_) => List::Nil
              None => match (match i {
                Simpl::Mk_simpl(_, _, _, _, _, si_method) => si_method
              }) {
                Some(m) => List::Cons((match i {
                  Simpl::Mk_simpl(_, _, _, si_trait, _, _) => si_trait
                }, m), List::Nil)
                None => List::Nil
              }
            }
          }, match sp {
            Sprog::Mk_sprog(_, _, sp_impls, _, _) => sp_impls
          })
          bind(mapM(fn(tm) {
            match tm {
              (tr, im) => bind(of_opt(find_trait(trs0, tr), Elab_error::EE_UnknownType(Pos::Mk_pos(N::N0, N::N0), tr)), fn(ti) {
                bind(of_opt(method_of(ti, match im {
                  Simethod::Mk_simethod(sim_name, _, _, _, _) => sim_name
                }), Elab_error::EE_NoMethod(Pos::Mk_pos(N::N0, N::N0), match im {
                  Simethod::Mk_simethod(sim_name, _, _, _, _) => sim_name
                }, Ty::TBase(Base_ty::BUnit))), fn(x) {
                  match x {
                    (_, s) => Result0::Ok(Fdef::Mk_fdef(default_name(tr, match im {
                      Simethod::Mk_simethod(sim_name, _, _, _, _) => sim_name
                    }), Nat::S(Nat::O), List::Cons(Ty::TData(tr, List::Cons(Ty::TVar(Nat::O), List::Nil)), match s {
                      Msig::Mk_msig(_, ms_params, _, _) => ms_params
                    }), match s {
                      Msig::Mk_msig(_, _, ms_ret, _) => ms_ret
                    }, match s {
                      Msig::Mk_msig(_, _, _, ms_eff) => ms_eff
                    }, Expr::ELit(Lit::LUnit)))
                  }
                })
              })
            }
          }, defaults), fn(dsigs) {
            let oinsts = flat_map(fn(x1) { obj_insts(trs0, x1) }, objs)
            let insts = app(map(fn(i) {
              match i {
                Iinfo::Mk_iinfo(_, _, _, _, ii_idef) => ii_idef
              }
            }, iis), map(fn(x1) { fst(x1) }, oinsts))
            bind(match coherent_dec(insts) {
              true => Result0::Ok(())
              false => Result0::Err(Elab_error::EE_Overlap(Pos::Mk_pos(N::N0, N::N0)))
            }, fn(_) {
              bind(mapM(fn(x1) { elab_sig(tys, x1) }, match sp {
                Sprog::Mk_sprog(_, _, _, sp_funs, _) => sp_funs
              }), fn(sigs) {
                let gsigs = flat_map(fn(x1) { group_sigs(x1) }, iis)
                let hdr = Genv::Mk_genv(types, app(sigs, app(gsigs, app(dsigs, map(fn(x1) { snd(x1) }, oinsts)))))
                let bounds = app(flat_map(fn(f) {
                  match bound_ctx(match f {
                    Sfun::Mk_sfun(sf_pos, _, _, _, _, _, _, _, _) => sf_pos
                  }, sig_tparams(f), match f {
                    Sfun::Mk_sfun(_, _, _, _, sf_bounds, _, _, _, _) => sf_bounds
                  }) {
                    Result0::Ok(ctx) => List::Cons((fun_name(f), ctx), List::Nil)
                    Result0::Err(_) => List::Nil
                  }
                }, match sp {
                  Sprog::Mk_sprog(_, _, _, sp_funs, _) => sp_funs
                }), app(flat_map(fn(ii) {
                  map(fn(im) {
                    (impl_name(match (match ii {
                      Iinfo::Mk_iinfo(ii_group, _, _, _, _) => ii_group
                    }) {
                      Igroup::Mk_igroup(_, ig_trait, _, _, _, _) => ig_trait
                    }, match ii {
                      Iinfo::Mk_iinfo(_, _, ii_name, _, _) => ii_name
                    }, match im {
                      Simethod::Mk_simethod(sim_name, _, _, _, _) => sim_name
                    }), match ii {
                      Iinfo::Mk_iinfo(_, _, _, ii_ctx, _) => ii_ctx
                    })
                  }, match (match ii {
                    Iinfo::Mk_iinfo(ii_group, _, _, _, _) => ii_group
                  }) {
                    Igroup::Mk_igroup(_, _, _, _, _, ig_methods) => ig_methods
                  })
                }, iis), flat_map(fn(ii) {
                  List::Cons((inst_name(match (match ii {
                    Iinfo::Mk_iinfo(ii_group, _, _, _, _) => ii_group
                  }) {
                    Igroup::Mk_igroup(_, ig_trait, _, _, _, _) => ig_trait
                  }, match ii {
                    Iinfo::Mk_iinfo(_, _, ii_name, _, _) => ii_name
                  }), match ii {
                    Iinfo::Mk_iinfo(_, _, _, ii_ctx, _) => ii_ctx
                  }), List::Nil)
                }, iis)))
                let meths = flat_map(fn(f) {
                  match (match f {
                    Sfun::Mk_sfun(_, sf_self, _, _, _, _, _, _, _) => sf_self
                  }) {
                    Some(t) => List::Cons((t, match f {
                      Sfun::Mk_sfun(_, _, sf_name, _, _, _, _, _, _) => sf_name
                    }), List::Nil)
                    None => List::Nil
                  }
                }, match sp {
                  Sprog::Mk_sprog(_, _, _, sp_funs, _) => sp_funs
                })
                let gx = Xenv::Mk_xenv(trs0, insts, bounds, meths, objs, List::Nil)
                let e = Senv::Mk_senv(tys, hdr, sinfo, List::Nil, gx)
                bind(elab_funs(e, match sp {
                  Sprog::Mk_sprog(_, _, _, sp_funs, _) => sp_funs
                }, sigs), fn(funs) {
                  bind(mapM(fn(ii) {
                    let g = match ii {
                      Iinfo::Mk_iinfo(ii_group, _, _, _, _) => ii_group
                    }
                    let _UU03c3_ = {
                      let a1 = {
                        let a1 = List::Cons(match g {
                          Igroup::Mk_igroup(_, _, ig_head, _, _, _) => ig_head
                        }, List::Nil)
                        fn(x1) { inst(a1, x1) }
                      }
                      fn(x1) { tsubst(a1, x1) }
                    }
                    mapM(fn(im) {
                      bind(of_opt(method_of(match ii {
                        Iinfo::Mk_iinfo(_, ii_ti, _, _, _) => ii_ti
                      }, match im {
                        Simethod::Mk_simethod(sim_name, _, _, _, _) => sim_name
                      }), Elab_error::EE_NoMethod(match g {
                        Igroup::Mk_igroup(ig_pos, _, _, _, _, _) => ig_pos
                      }, match im {
                        Simethod::Mk_simethod(sim_name, _, _, _, _) => sim_name
                      }, Ty::TBase(Base_ty::BUnit))), fn(x) {
                        match x {
                          (_, s) => {
                            let ps = map(_UU03c3_, match s {
                              Msig::Mk_msig(_, ms_params, _, _) => ms_params
                            })
                            bind(match eqb0(length(match im {
                              Simethod::Mk_simethod(_, sim_params, _, _, _) => sim_params
                            }), length(ps)) {
                              true => Result0::Ok(())
                              false => Result0::Err(Elab_error::EE_Type(match g {
                                Igroup::Mk_igroup(ig_pos, _, _, _, _, _) => ig_pos
                              }, Type_error::E_ArgArity(length(ps), length(match im {
                                Simethod::Mk_simethod(_, sim_params, _, _, _) => sim_params
                              }))))
                            }, fn(_) {
                              let _UU0393_p = combine(map(fn(x0) { Some(fst(x0)) }, match im {
                                Simethod::Mk_simethod(_, sim_params, _, _, _) => sim_params
                              }), ps)
                              bind(elab_body(e, match g {
                                Igroup::Mk_igroup(_, _, _, ig_tparams, _, _) => ig_tparams
                              }, match ii {
                                Iinfo::Mk_iinfo(_, _, _, ii_ctx, _) => ii_ctx
                              }, _UU0393_p, _UU03c3_(match s {
                                Msig::Mk_msig(_, _, ms_ret, _) => ms_ret
                              }), _UU03c3_(match s {
                                Msig::Mk_msig(_, _, _, ms_eff) => ms_eff
                              }), match im {
                                Simethod::Mk_simethod(_, _, _, _, sim_body) => sim_body
                              }), fn(b) {
                                Result0::Ok(Fdef::Mk_fdef(impl_name(match g {
                                  Igroup::Mk_igroup(_, ig_trait, _, _, _, _) => ig_trait
                                }, match ii {
                                  Iinfo::Mk_iinfo(_, _, ii_name, _, _) => ii_name
                                }, match im {
                                  Simethod::Mk_simethod(sim_name, _, _, _, _) => sim_name
                                }), length(match g {
                                  Igroup::Mk_igroup(_, _, _, ig_tparams, _, _) => ig_tparams
                                }), app(map(fn(x1) { dict_ty(x1) }, match ii {
                                  Iinfo::Mk_iinfo(_, _, _, ii_ctx, _) => ii_ctx
                                }), ps), _UU03c3_(match s {
                                  Msig::Mk_msig(_, _, ms_ret, _) => ms_ret
                                }), _UU03c3_(match s {
                                  Msig::Mk_msig(_, _, _, ms_eff) => ms_eff
                                }), b))
                              })
                            })
                          }
                        }
                      })
                    }, match g {
                      Igroup::Mk_igroup(_, _, _, _, _, ig_methods) => ig_methods
                    })
                  }, iis), fn(imfs) {
                    bind(mapM(fn(ii) {
                      let g = match ii {
                        Iinfo::Mk_iinfo(ii_group, _, _, _, _) => ii_group
                      }
                      bind(inst_body(insts, trs0, List::Nil, ii), fn(b) {
                        Result0::Ok(Fdef::Mk_fdef(inst_name(match g {
                          Igroup::Mk_igroup(_, ig_trait, _, _, _, _) => ig_trait
                        }, match ii {
                          Iinfo::Mk_iinfo(_, _, ii_name, _, _) => ii_name
                        }), length(match g {
                          Igroup::Mk_igroup(_, _, _, ig_tparams, _, _) => ig_tparams
                        }), map(fn(x1) { dict_ty(x1) }, match ii {
                          Iinfo::Mk_iinfo(_, _, _, ii_ctx, _) => ii_ctx
                        }), Ty::TData(match g {
                          Igroup::Mk_igroup(_, ig_trait, _, _, _, _) => ig_trait
                        }, List::Cons(match g {
                          Igroup::Mk_igroup(_, _, ig_head, _, _, _) => ig_head
                        }, List::Nil)), Ty::TBase(Base_ty::BNever), b))
                      })
                    }, iis), fn(ifs) {
                      bind(mapM(fn(tm) {
                        match tm {
                          (tr, im) => bind(of_opt(find_trait(trs0, tr), Elab_error::EE_UnknownType(Pos::Mk_pos(N::N0, N::N0), tr)), fn(ti) {
                            bind(of_opt(method_of(ti, match im {
                              Simethod::Mk_simethod(sim_name, _, _, _, _) => sim_name
                            }), Elab_error::EE_NoMethod(Pos::Mk_pos(N::N0, N::N0), match im {
                              Simethod::Mk_simethod(sim_name, _, _, _, _) => sim_name
                            }, Ty::TBase(Base_ty::BUnit))), fn(x) {
                              match x {
                                (_, s) => {
                                  let _UU0393_p = combine(map(fn(x0) { Some(fst(x0)) }, match im {
                                    Simethod::Mk_simethod(_, sim_params, _, _, _) => sim_params
                                  }), match s {
                                    Msig::Mk_msig(_, ms_params, _, _) => ms_params
                                  })
                                  bind(elab_body(e, List::Cons(String0::String1(Ascii::Ascii0(true, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, true, false), String0::EmptyString)))), List::Nil), List::Cons((tr, Nat::O), List::Nil), _UU0393_p, match s {
                                    Msig::Mk_msig(_, _, ms_ret, _) => ms_ret
                                  }, match s {
                                    Msig::Mk_msig(_, _, _, ms_eff) => ms_eff
                                  }, match im {
                                    Simethod::Mk_simethod(_, _, _, _, sim_body) => sim_body
                                  }), fn(b) {
                                    Result0::Ok(Fdef::Mk_fdef(default_name(tr, match im {
                                      Simethod::Mk_simethod(sim_name, _, _, _, _) => sim_name
                                    }), Nat::S(Nat::O), List::Cons(Ty::TData(tr, List::Cons(Ty::TVar(Nat::O), List::Nil)), match s {
                                      Msig::Mk_msig(_, ms_params, _, _) => ms_params
                                    }), match s {
                                      Msig::Mk_msig(_, _, ms_ret, _) => ms_ret
                                    }, match s {
                                      Msig::Mk_msig(_, _, _, ms_eff) => ms_eff
                                    }, b))
                                  })
                                }
                              }
                            })
                          })
                        }
                      }, defaults), fn(dfs) {
                        bind(mapM(fn(tr) {
                          mapM(fn(sn) {
                            bind(obj_inst_body(insts, trs0, tr, sn), fn(b) {
                              Result0::Ok(Fdef::Mk_fdef(inst_name(sn, obj_name(tr)), Nat::O, List::Nil, Ty::TData(sn, List::Cons(Ty::TData(obj_name(tr), List::Nil), List::Nil)), Ty::TBase(Base_ty::BNever), b))
                            })
                          }, closure(trs0, tr))
                        }, objs), fn(ofs) {
                          bind(match (match sp {
                            Sprog::Mk_sprog(_, _, _, _, sp_main) => sp_main
                          }) {
                            Some(e0) => elab_body(e, List::Nil, List::Nil, List::Nil, Ty::TBase(Base_ty::BUnit), Ty::TBase(Base_ty::BNever), Sexpr::SAnnot(sexpr_pos(e0), e0, Sty::SName(sexpr_pos(e0), String0::String1(Ascii::Ascii0(true, false, true, false, true, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))), List::Nil)))
                            None => Result0::Ok(Expr::ELit(Lit::LUnit))
                          }, fn(main0) {
                            Result0::Ok((Genv::Mk_genv(types, app(funs, app(concat(imfs), app(ifs, app(dfs, concat(ofs)))))), main0))
                          })
                        })
                      })
                    })
                  })
                })
              })
            })
          })
        })
      })
    })
  })
}

pub(all) enum Lower_error {
  LowerUnsupported(String, Pos)
}

pub(all) enum Outcome {
  O_Parse(Array0[@basic.Report])
  O_Unsupported(Lower_error)
  O_Elab(Elab_error)
  O_Type(Type_error)
  O_Ok(Genv, Expr, Ty)
}

pub fn check_core(ge : Genv, main0 : Expr) -> Outcome {
  match check_program(ge, main0) {
    Result0::Ok(s) => Outcome::O_Ok(ge, main0, s)
    Result0::Err(e) => Outcome::O_Type(e)
  }
}

pub fn check_sprog(sp : Sprog) -> Outcome {
  match elab_prog(sp) {
    Result0::Ok(p) => match p {
      (ge, main0) => check_core(ge, main0)
    }
    Result0::Err(e) => Outcome::O_Elab(e)
  }
}

pub fn check_source(src : String) -> Outcome {
  match @parser.parse_string(src) {
    (impls, reports) => match (reports.length() == @rocqrt.u63_to_int(0UL)) {
      true => match lower_impls(impls) {
        Result0::Ok(sp) => check_sprog(sp)
        Result0::Err(e) => Outcome::O_Unsupported(e)
      }
      false => Outcome::O_Parse(reports)
    }
  }
}
