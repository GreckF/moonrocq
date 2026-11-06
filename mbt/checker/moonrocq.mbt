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

pub fn sub(n : Nat, m : Nat) -> Nat {
  match n {
    Nat::O => n
    Nat::S(k) => match m {
      Nat::O => n
      Nat::S(l) => sub(k, l)
    }
  }
}

pub type Array0[A] = Array[A]

pub type List_List[T0] = @list.List[T0]

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

pub fn[A, B] flat_map(f : (A) -> List[B], l : List[A]) -> List[B] {
  match l {
    List::Nil => List::Nil
    List::Cons(x, l0) => app(f(x), flat_map(f, l0))
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
    List::Cons(x, tl) => match f(x) {
      true => Some(x)
      false => find(f, tl)
    }
  }
}

pub fn[A, B] combine(l : List[A], l_ : List[B]) -> List[(A, B)] {
  match l {
    List::Nil => List::Nil
    List::Cons(x, tl) => match l_ {
      List::Nil => List::Nil
      List::Cons(y, tl_) => List::Cons((x, y), combine(tl, tl_))
    }
  }
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

pub fn[A, B, C] map_result(f : (A) -> B, m : Result0[A, C]) -> Result0[B, C] {
  match m {
    Result0::Ok(a) => Result0::Ok(f(a))
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

pub fn add(x : Positive, y : Positive) -> Positive {
  match x {
    Positive::XI(p) => match y {
      Positive::XI(q) => Positive::XO(add_carry(p, q))
      Positive::XO(q) => Positive::XI(add(p, q))
      Positive::XH => Positive::XO(succ(p))
    }
    Positive::XO(p) => match y {
      Positive::XI(q) => Positive::XI(add(p, q))
      Positive::XO(q) => Positive::XO(add(p, q))
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
      Positive::XO(q) => Positive::XI(add(p, q))
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

pub fn mul(x : Positive, y : Positive) -> Positive {
  match x {
    Positive::XI(p) => add(y, Positive::XO(mul(p, y)))
    Positive::XO(p) => Positive::XO(mul(p, y))
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

pub fn add0(x : Z, y : Z) -> Z {
  match x {
    Z::Z0 => y
    Z::Zpos(x_) => match y {
      Z::Z0 => x
      Z::Zpos(y_) => Z::Zpos(add(x_, y_))
      Z::Zneg(y_) => pos_sub(x_, y_)
    }
    Z::Zneg(x_) => match y {
      Z::Z0 => x
      Z::Zpos(y_) => pos_sub(y_, x_)
      Z::Zneg(y_) => Z::Zneg(add(x_, y_))
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

pub fn sub0(m : Z, n : Z) -> Z {
  add0(m, opp(n))
}

pub fn mul0(x : Z, y : Z) -> Z {
  match x {
    Z::Z0 => Z::Z0
    Z::Zpos(x_) => match y {
      Z::Z0 => Z::Z0
      Z::Zpos(y_) => Z::Zpos(mul(x_, y_))
      Z::Zneg(y_) => Z::Zneg(mul(x_, y_))
    }
    Z::Zneg(x_) => match y {
      Z::Z0 => Z::Z0
      Z::Zpos(y_) => Z::Zneg(mul(x_, y_))
      Z::Zneg(y_) => Z::Zpos(mul(x_, y_))
    }
  }
}

pub fn pow_pos(z : Z) -> (Positive) -> Z {
  {
    let a1 = fn(x1) { mul0(z, x1) }
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
        let r_ = add0(mul0(Z::Zpos(Positive::XO(Positive::XH)), r), Z::Zpos(Positive::XH))
        match ltb0(r_, b) {
          true => (mul0(Z::Zpos(Positive::XO(Positive::XH)), q), r_)
          false => (add0(mul0(Z::Zpos(Positive::XO(Positive::XH)), q), Z::Zpos(Positive::XH)), sub0(r_, b))
        }
      }
    }
    Positive::XO(a_) => match pos_div_eucl(a_, b) {
      (q, r) => {
        let r_ = mul0(Z::Zpos(Positive::XO(Positive::XH)), r)
        match ltb0(r_, b) {
          true => (mul0(Z::Zpos(Positive::XO(Positive::XH)), q), r_)
          false => (add0(mul0(Z::Zpos(Positive::XO(Positive::XH)), q), Z::Zpos(Positive::XH)), sub0(r_, b))
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
          _ => (opp(add0(q, Z::Zpos(Positive::XH))), add0(b, r))
        }
      }
    }
    Z::Zneg(a_) => match b {
      Z::Z0 => (Z::Z0, a)
      Z::Zpos(_) => match pos_div_eucl(a_, b) {
        (q, r) => match r {
          Z::Z0 => (opp(q), Z::Z0)
          _ => (opp(add0(q, Z::Zpos(Positive::XH))), sub0(b, r))
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

pub let eqDec_string : EqDec[String0] = fn(x1) { fn(x2) { eqb4(x1, x2) } }

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
  }
}

pub let eqDec_base_ty : EqDec[Base_ty] = eqDec_of_dec()(fn(x1) { fn(x2) { base_ty_eq_dec(x1, x2) } })

pub(all) enum Ty {
  TBase(Base_ty)
  TVar(Nat)
  TTuple(List[Ty])
  TArrow(List[Ty], Ty)
  TData(Ident, List[Ty])
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
    Ty::TArrow(ps, r) => match b {
      Ty::TArrow(qs, s) => match forall2b(fn(x1) { fn(x2) { ty_eqb(x1, x2) } }, ps, qs) {
        true => ty_eqb(r, s)
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

pub(all) enum Pat {
  PWild
  PVar
  PLit(Lit)
  PTuple(List[Pat])
  PConstr(Ident, List[Pat])
}

pub(all) enum Expr {
  EVar(Nat)
  EGlobal(Ident, List[Ty])
  ELit(Lit)
  ELam(List[Ty], Ty, Expr)
  EApp(Expr, List[Expr])
  ELet(Expr, Expr)
  EIf(Expr, Expr, Expr)
  ETuple(List[Expr])
  EProj(Expr, Nat)
  EPrim(Prim_op, List[Expr])
  EConstr(Ident, Ident, List[Ty], Expr)
  EMatch(Expr, Ty, List[(Pat, Expr)])
}

pub(all) enum Fdef {
  Mk_fdef(Ident, Nat, List[Ty], Ty, Expr)
}

pub(all) enum Cdef {
  Mk_cdef(Ident, List[Ty])
}

pub(all) enum Tdef {
  Mk_tdef(Ident, Nat, List[Cdef])
}

pub(all) enum Genv {
  Mk_genv(List[Tdef], List[Fdef])
}

pub fn lookup_fn(ge : Genv, f : Ident) -> Option[Fdef] {
  find(fn(fd) {
    eqDec_ident(match fd {
      Fdef::Mk_fdef(fd_name, _, _, _, _) => fd_name
    })(f)
  }, match ge {
    Genv::Mk_genv(_, ge_funs) => ge_funs
  })
}

pub fn lookup_ty(ge : Genv, t : Ident) -> Option[Tdef] {
  find(fn(td) {
    eqDec_ident(match td {
      Tdef::Mk_tdef(td_name, _, _) => td_name
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
    Tdef::Mk_tdef(_, _, td_ctors) => td_ctors
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
  match geb(r, pow(Z::Zpos(Positive::XO(Positive::XH)), sub0(n, Z::Zpos(Positive::XH)))) {
    true => sub0(r, pow(Z::Zpos(Positive::XO(Positive::XH)), n))
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
    Ty::TBase(b) => Ty::TBase(b)
    Ty::TVar(i) => _UU03c3_(i)
    Ty::TTuple(ts) => Ty::TTuple(map(fn(x1) { tsubst(_UU03c3_, x1) }, ts))
    Ty::TArrow(ps, r) => Ty::TArrow(map(fn(x1) { tsubst(_UU03c3_, x1) }, ps), tsubst(_UU03c3_, r))
    Ty::TData(t0, ts) => Ty::TData(t0, map(fn(x1) { tsubst(_UU03c3_, x1) }, ts))
  }
}

pub fn inst(ts : List[Ty], i : Nat) -> Ty {
  nth(i, ts, Ty::TBase(Base_ty::BUnit))
}

pub type Ctx = List[Ty]

pub fn ty_wfb(ge : Genv, n : Nat, t : Ty) -> Bool {
  match t {
    Ty::TBase(_) => true
    Ty::TVar(i) => ltb(i, n)
    Ty::TTuple(ts) => forallb(fn(x1) { ty_wfb(ge, n, x1) }, ts)
    Ty::TArrow(ps, r) => match forallb(fn(x1) { ty_wfb(ge, n, x1) }, ps) {
      true => ty_wfb(ge, n, r)
      false => false
    }
    Ty::TData(t0, ts) => match lookup_ty(ge, t0) {
      Some(td) => match eqb0(length(ts), match td {
        Tdef::Mk_tdef(_, td_tparams, _) => td_tparams
      }) {
        true => forallb(fn(x1) { ty_wfb(ge, n, x1) }, ts)
        false => false
      }
      None => false
    }
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

pub fn as_arrow(t : Ty) -> Result0[SigT[List[Ty], Ty], Type_error] {
  match t {
    Ty::TArrow(ps, r) => Result0::Ok(SigT::ExistT(ps, r))
    _ => Result0::Err(Type_error::E_NotFunction(t))
  }
}

pub fn as_tuple(t : Ty) -> Result0[List[Ty], Type_error] {
  match t {
    Ty::TTuple(ts) => Result0::Ok(ts)
    _ => Result0::Err(Type_error::E_NotTuple(t))
  }
}

pub fn as_data(t : Ty) -> Result0[SigT[Ident, List[Ty]], Type_error] {
  match t {
    Ty::TData(t0, ts) => Result0::Ok(SigT::ExistT(t0, ts))
    _ => Result0::Err(Type_error::E_NotData(t))
  }
}

pub fn infer_list(ge : Genv, _UU0393_ : Ctx, inf : (Expr) -> Result0[Ty, Type_error], es : List[Expr]) -> Result0[List[Ty], Type_error] {
  match es {
    List::Nil => Result0::Ok(List::Nil)
    List::Cons(e, es_) => bind(inf(e), fn(x) {
      bind(infer_list(ge, _UU0393_, inf, es_), fn(x0) { Result0::Ok(List::Cons(x, x0)) })
    })
  }
}

pub fn check_list(ge : Genv, _UU0393_ : Ctx, inf : (Expr) -> Result0[Ty, Type_error], es : List[Expr], _UU03c4_s : List[Ty]) -> Result0[Unit, Type_error] {
  match es {
    List::Nil => match _UU03c4_s {
      List::Nil => Result0::Ok(())
      List::Cons(_, _) => Result0::Err(Type_error::E_ArgArity(length(_UU03c4_s), length(es)))
    }
    List::Cons(e, es_) => match _UU03c4_s {
      List::Nil => Result0::Err(Type_error::E_ArgArity(length(_UU03c4_s), length(es)))
      List::Cons(_UU03c4_, _UU03c4_s_) => bind(inf(e), fn(x) {
        bind(expect_ty(_UU03c4_, x), fn(_) {
          bind(check_list(ge, _UU0393_, inf, es_, _UU03c4_s_), fn(_) { Result0::Ok(()) })
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
  }
}

pub fn check_branches(ge : Genv, inf : (Ctx) -> (Expr) -> Result0[Ty, Type_error], _UU0393_ : Ctx, _UU03c4_s : Ty, _UU03c4_ : Ty, bs : List[(Pat, Expr)]) -> Result0[Unit, Type_error] {
  match bs {
    List::Nil => Result0::Ok(())
    List::Cons(p0, bs_) => match p0 {
      (p, b) => bind(check_pat(ge, p, _UU03c4_s), fn(x) {
        bind(inf(app(x, _UU0393_))(b), fn(x0) {
          bind(expect_ty(_UU03c4_, x0), fn(_) {
            bind(check_branches(ge, inf, _UU0393_, _UU03c4_s, _UU03c4_, bs_), fn(_) { Result0::Ok(()) })
          })
        })
      })
    }
  }
}

pub fn infer(ge : Genv, _UU0393_ : Ctx, e : Expr) -> Result0[Ty, Type_error] {
  match e {
    Expr::EVar(x) => bind(of_option(nth_error(_UU0393_, x), Type_error::E_UnboundVar(x)), fn(x0) { Result0::Ok(x0) })
    Expr::EGlobal(f, ts) => bind(of_option(lookup_fn(ge, f), Type_error::E_UnknownGlobal(f)), fn(x) {
      bind(expect_nat(match x {
        Fdef::Mk_fdef(_, fd_tparams, _, _, _) => fd_tparams
      }, length(ts), Type_error::E_TypeArgArity(f, match x {
        Fdef::Mk_fdef(_, fd_tparams, _, _, _) => fd_tparams
      }, length(ts))), fn(_) {
        Result0::Ok(Ty::TArrow(map({ let a1 = fn(x1) { inst(ts, x1) }; fn(x1) { tsubst(a1, x1) } }, match x {
          Fdef::Mk_fdef(_, _, fd_params, _, _) => fd_params
        }), tsubst(fn(x1) { inst(ts, x1) }, match x {
          Fdef::Mk_fdef(_, _, _, fd_ret, _) => fd_ret
        })))
      })
    })
    Expr::ELit(l) => Result0::Ok(Ty::TBase(lit_ty(l)))
    Expr::ELam(ps, r, b) => bind(infer(ge, app(ps, _UU0393_), b), fn(x) { bind(expect_ty(r, x), fn(_) { Result0::Ok(Ty::TArrow(ps, r)) }) })
    Expr::EApp(f, args) => bind(infer(ge, _UU0393_, f), fn(x) {
      bind(as_arrow(x), fn(x0) {
        match x0 {
          SigT::ExistT(ps, s) => bind(expect_nat(length(ps), length(args), Type_error::E_ArgArity(length(ps), length(args))), fn(_) {
            bind(check_list(ge, _UU0393_, fn(x1) { infer(ge, _UU0393_, x1) }, args, ps), fn(_) { Result0::Ok(s) })
          })
        }
      })
    })
    Expr::ELet(e1, e2) => bind(infer(ge, _UU0393_, e1), fn(x) {
      bind(infer(ge, List::Cons(x, _UU0393_), e2), fn(x0) { Result0::Ok(x0) })
    })
    Expr::EIf(c, t, e0) => bind(infer(ge, _UU0393_, c), fn(x) {
      bind(expect_ty(Ty::TBase(Base_ty::BBool), x), fn(_) {
        bind(infer(ge, _UU0393_, t), fn(x0) {
          bind(infer(ge, _UU0393_, e0), fn(x1) { bind(expect_ty(x0, x1), fn(_) { Result0::Ok(x0) }) })
        })
      })
    })
    Expr::ETuple(es) => bind(infer_list(ge, _UU0393_, fn(x1) { infer(ge, _UU0393_, x1) }, es), fn(x) { Result0::Ok(Ty::TTuple(x)) })
    Expr::EProj(e0, i) => bind(infer(ge, _UU0393_, e0), fn(x) {
      bind(as_tuple(x), fn(x0) {
        bind(of_option(nth_error(x0, i), Type_error::E_TupleIndex(i, x)), fn(x1) { Result0::Ok(x1) })
      })
    })
    Expr::EPrim(op, args) => bind(expect_nat(length(fst(prim_sig(op))), length(args), Type_error::E_ArgArity(length(fst(prim_sig(op))), length(args))), fn(_) {
      bind(check_list(ge, _UU0393_, fn(x1) { infer(ge, _UU0393_, x1) }, args, fst(prim_sig(op))), fn(_) { Result0::Ok(snd(prim_sig(op))) })
    })
    Expr::EConstr(t, c, ts, e0) => bind(of_option(lookup_ty(ge, t), Type_error::E_UnknownType(t)), fn(x) {
      bind(expect_nat(match x {
        Tdef::Mk_tdef(_, td_tparams, _) => td_tparams
      }, length(ts), Type_error::E_TypeArgArity(t, match x {
        Tdef::Mk_tdef(_, td_tparams, _) => td_tparams
      }, length(ts))), fn(_) {
        bind(of_option(lookup_ctor(x, c), Type_error::E_UnknownCtor(t, c)), fn(x0) {
          bind(infer(ge, _UU0393_, e0), fn(x1) {
            bind(expect_ty(Ty::TTuple(map({ let a1 = fn(x2) { inst(ts, x2) }; fn(x2) { tsubst(a1, x2) } }, match x0 {
              Cdef::Mk_cdef(_, cd_fields) => cd_fields
            })), x1), fn(_) { Result0::Ok(Ty::TData(t, ts)) })
          })
        })
      })
    })
    Expr::EMatch(e0, _UU03c4_, bs) => bind(infer(ge, _UU0393_, e0), fn(x) {
      bind(check_branches(ge, fn(x1) { fn(x2) { infer(ge, x1, x2) } }, _UU0393_, x, _UU03c4_, bs), fn(_) { Result0::Ok(_UU03c4_) })
    })
  }
}

pub fn check_fdef(ge : Genv, fd : Fdef) -> Result0[Unit, Type_error] {
  map_err(fn(x) {
    Type_error::E_InGlobal(match fd {
      Fdef::Mk_fdef(fd_name, _, _, _, _) => fd_name
    }, x)
  }, bind(infer(ge, match fd {
    Fdef::Mk_fdef(_, _, fd_params, _, _) => fd_params
  }, match fd {
    Fdef::Mk_fdef(_, _, _, _, fd_body) => fd_body
  }), fn(x) {
    bind(expect_ty(match fd {
      Fdef::Mk_fdef(_, _, _, fd_ret, _) => fd_ret
    }, x), fn(_) { Result0::Ok(()) })
  }))
}

pub fn check_fdefs(ge : Genv, fds : List[Fdef]) -> Result0[Unit, Type_error] {
  match fds {
    List::Nil => Result0::Ok(())
    List::Cons(fd, fds_) => bind(check_fdef(ge, fd), fn(_) { bind(check_fdefs(ge, fds_), fn(_) { Result0::Ok(()) }) })
  }
}

pub fn check_bool(b : Bool, err : Type_error) -> Result0[Unit, Type_error] {
  match b {
    true => Result0::Ok(())
    false => Result0::Err(err)
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
      Tdef::Mk_tdef(td_name, _, _) => td_name
    }, x)
  }, bind(check_nodup(map(fn(c) {
    match c {
      Cdef::Mk_cdef(cd_name, _) => cd_name
    }
  }, match td {
    Tdef::Mk_tdef(_, _, td_ctors) => td_ctors
  }), Type_error::E_DuplicateCtor), fn(_) {
    bind(check_all(fn(cd) {
      check_all({
        let a2 = match td {
          Tdef::Mk_tdef(_, td_tparams, _) => td_tparams
        }
        fn(x1) { check_wf(ge, a2, x1) }
      }, match cd {
        Cdef::Mk_cdef(_, cd_fields) => cd_fields
      })
    }, match td {
      Tdef::Mk_tdef(_, _, td_ctors) => td_ctors
    }), fn(_) { Result0::Ok(()) })
  }))
}

pub fn check_fsig(ge : Genv, fd : Fdef) -> Result0[Unit, Type_error] {
  map_err(fn(x) {
    Type_error::E_InGlobal(match fd {
      Fdef::Mk_fdef(fd_name, _, _, _, _) => fd_name
    }, x)
  }, bind(check_all({
    let a2 = match fd {
      Fdef::Mk_fdef(_, fd_tparams, _, _, _) => fd_tparams
    }
    fn(x1) { check_wf(ge, a2, x1) }
  }, match fd {
    Fdef::Mk_fdef(_, _, fd_params, _, _) => fd_params
  }), fn(_) {
    bind(check_wf(ge, match fd {
      Fdef::Mk_fdef(_, fd_tparams, _, _, _) => fd_tparams
    }, match fd {
      Fdef::Mk_fdef(_, _, _, fd_ret, _) => fd_ret
    }), fn(_) { Result0::Ok(()) })
  }))
}

pub fn check_genv(ge : Genv) -> Result0[Unit, Type_error] {
  bind(check_nodup(map(fn(t) {
    match t {
      Tdef::Mk_tdef(td_name, _, _) => td_name
    }
  }, match ge {
    Genv::Mk_genv(ge_types, _) => ge_types
  }), Type_error::E_DuplicateType), fn(_) {
    bind(check_all(fn(x1) { check_tdef(ge, x1) }, match ge {
      Genv::Mk_genv(ge_types, _) => ge_types
    }), fn(_) {
      bind(check_nodup(map(fn(f) {
        match f {
          Fdef::Mk_fdef(fd_name, _, _, _, _) => fd_name
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
  bind(check_genv(ge), fn(_) { bind(infer(ge, List::Nil, e), fn(x) { Result0::Ok(x) }) })
}

pub(all) enum Pos {
  Mk_pos(N, N)
}

pub(all) enum Sty {
  SName(Pos, Ident, List[Sty])
  STuple(Pos, List[Sty])
  SArrow(Pos, List[Sty], Sty)
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
  SLam(Pos, List[(Ident, Option[Sty])], Option[Sty], Sexpr)
  SAnnot(Pos, Sexpr, Sty)
  SConstr(Pos, Option[Ident], Ident)
  SRecord(Pos, Option[Ident], List[(Ident, Sexpr)])
  SField(Pos, Sexpr, Ident)
  SMatch(Pos, Sexpr, List[(Spat, Sexpr)])
}

pub(all) enum Sfun {
  Mk_sfun(Pos, Ident, List[Ident], List[(Ident, Sty)], Option[Sty], Sexpr)
}

pub(all) enum Sdecl {
  SDEnum(List[(Ident, List[Sty])])
  SDStruct(List[(Ident, Sty)])
  SDTupleStruct(List[Sty])
}

pub(all) enum Stype {
  Mk_stype(Pos, Ident, List[Ident], Sdecl)
}

pub(all) enum Sprog {
  Mk_sprog(List[Stype], List[Sfun], Option[Sexpr])
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
    Sexpr::SLam(p, _, _, _) => p
    Sexpr::SAnnot(p, _, _) => p
    Sexpr::SConstr(p, _, _) => p
    Sexpr::SRecord(p, _, _) => p
    Sexpr::SField(p, _, _) => p
    Sexpr::SMatch(p, _, _) => p
  }
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

pub fn tvars(n : Nat) -> List[Ty] {
  map(fn(x) { Ty::TVar(x) }, seq(Nat::O, n))
}

pub let builtin_types : List[(Ident, Ty)] = List::Cons((String0::String1(Ascii::Ascii0(true, false, true, false, true, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))), Ty::TBase(Base_ty::BUnit)), List::Cons((String0::String1(Ascii::Ascii0(false, true, false, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))), Ty::TBase(Base_ty::BBool)), List::Cons((String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))), Ty::TBase(Base_ty::BInt(Int_kind::I32))), List::Cons((String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, true, true, false, false), String0::String1(Ascii::Ascii0(false, true, true, false, true, true, false, false), String0::EmptyString))))), Ty::TBase(Base_ty::BInt(Int_kind::I16))), List::Cons((String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, true, true, false, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, false, false), String0::EmptyString))))), Ty::TBase(Base_ty::BInt(Int_kind::I64))), List::Cons((String0::String1(Ascii::Ascii0(true, false, true, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))), Ty::TBase(Base_ty::BInt(Int_kind::U32))), List::Cons((String0::String1(Ascii::Ascii0(true, false, true, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, true, true, false, false), String0::String1(Ascii::Ascii0(false, true, true, false, true, true, false, false), String0::EmptyString)))))), Ty::TBase(Base_ty::BInt(Int_kind::U16))), List::Cons((String0::String1(Ascii::Ascii0(true, false, true, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, true, true, false, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, false, false), String0::EmptyString)))))), Ty::TBase(Base_ty::BInt(Int_kind::U64))), List::Cons((String0::String1(Ascii::Ascii0(false, true, false, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString)))), Ty::TBase(Base_ty::BInt(Int_kind::IByte))), List::Cons((String0::String1(Ascii::Ascii0(false, true, false, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))), Ty::TBase(Base_ty::BInt(Int_kind::IBigInt))), List::Cons((String0::String1(Ascii::Ascii0(true, true, false, false, false, false, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::EmptyString)))), Ty::TBase(Base_ty::BChar)), List::Cons((String0::String1(Ascii::Ascii0(false, false, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString)))))), Ty::TBase(Base_ty::BDouble)), List::Cons((String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))))), Ty::TBase(Base_ty::BFloat)), List::Cons((String0::String1(Ascii::Ascii0(true, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, false, true, true, false), String0::EmptyString)))))), Ty::TBase(Base_ty::BString)), List::Nil))))))))))))))

pub let option_tdef : Tdef = Tdef::Mk_tdef(String0::String1(Ascii::Ascii0(true, true, true, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::EmptyString)))))), Nat::S(Nat::O), List::Cons(Cdef::Mk_cdef(String0::String1(Ascii::Ascii0(false, true, true, true, false, false, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString)))), List::Nil), List::Cons(Cdef::Mk_cdef(String0::String1(Ascii::Ascii0(true, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString)))), List::Cons(Ty::TVar(Nat::O), List::Nil)), List::Nil)))

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
          None => Result0::Err(Elab_error::EE_UnknownType(p, n))
        }
      }
    }
    Sty::STuple(_, ts) => bind(mapM(fn(x1) { elab_ty(tys, tps, x1) }, ts), fn(_UU03c4_s) { Result0::Ok(Ty::TTuple(_UU03c4_s)) })
    Sty::SArrow(_, ps, r) => bind(mapM(fn(x1) { elab_ty(tys, tps, x1) }, ps), fn(_UU03c4_s) {
      bind(elab_ty(tys, tps, r), fn(_UU03c4_) { Result0::Ok(Ty::TArrow(_UU03c4_s, _UU03c4_)) })
    })
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
    Ty::TBase(_) => s
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
    Ty::TArrow(ps, r) => match t {
      Ty::TArrow(ts, u) => tmatch(r, u, go(ps)(ts)(s))
      _ => s
    }
    Ty::TData(t0, ps) => match t {
      Ty::TData(u, ts) => match eqDec_ident(t0)(u) {
        true => go(ps)(ts)(s)
        false => s
      }
      _ => s
    }
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
    Ty::TBase(b) => Some(Ty::TBase(b))
    Ty::TVar(i) => match nth_error(s, i) {
      Some(o) => o
      None => None
    }
    Ty::TTuple(ps) => option_map(fn(x) { Ty::TTuple(x) }, go(ps))
    Ty::TArrow(ps, r) => match go(ps) {
      Some(ts) => match resolve(s, r) {
        Some(t) => Some(Ty::TArrow(ts, t))
        None => None
      }
      None => None
    }
    Ty::TData(t, ps) => option_map(fn(x) { Ty::TData(t, x) }, go(ps))
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

pub fn type_of(hdr : Genv, p : Pos, _UU0393_ : Lctx, e : Expr) -> Result0[Ty, Elab_error] {
  match infer(hdr, map(fn(x1) { snd(x1) }, _UU0393_), e) {
    Result0::Ok(s) => Result0::Ok(s)
    Result0::Err(err) => Result0::Err(Elab_error::EE_Type(p, err))
  }
}

pub fn arrow_params(t : Ty, n : Nat) -> List[Option[Ty]] {
  match t {
    Ty::TArrow(ps, _) => match eqb0(length(ps), n) {
      true => map(fn(x) { Some(x) }, ps)
      false => repeat(None, n)
    }
    _ => repeat(None, n)
  }
}

pub fn elab_global(p : Pos, f : Ident, fd : Fdef, exp : Option[Ty]) -> Result0[Expr, Elab_error] {
  match (match fd {
    Fdef::Mk_fdef(_, fd_tparams, _, _, _) => fd_tparams
  }) {
    Nat::O => Result0::Ok(Expr::EGlobal(f, List::Nil))
    Nat::S(n0) => {
      let n = Nat::S(n0)
      let s = match exp {
        Some(t) => tmatch(Ty::TArrow(match fd {
          Fdef::Mk_fdef(_, _, fd_params, _, _) => fd_params
        }, match fd {
          Fdef::Mk_fdef(_, _, _, fd_ret, _) => fd_ret
        }), t, repeat(None, n))
        None => repeat(None, n)
      }
      match all_some(s) {
        Some(ts) => Result0::Ok(Expr::EGlobal(f, ts))
        None => Result0::Err(Elab_error::EE_CannotInfer(p, f))
      }
    }
  }
}

pub fn is_record(sinfo : List[(Ident, List[Ident])], t : Ident) -> Bool {
  match assoc(t, sinfo) {
    Some(_) => true
    None => false
  }
}

pub fn has_ctor(c : Ident, td : Tdef) -> Bool {
  match lookup_ctor(td, c) {
    Some(_) => true
    None => false
  }
}

pub fn resolve_ctor(hdr : Genv, sinfo : List[(Ident, List[Ident])], p : Pos, tq : Option[Ident], c : Ident, exp : Option[Ty]) -> Result0[(Tdef, Cdef), Elab_error] {
  let in_type = fn(td) {
    match lookup_ctor(td, c) {
      Some(cd) => Result0::Ok((td, cd))
      None => Result0::Err(Elab_error::EE_UnknownCtor(p, c))
    }
  }
  match tq {
    Some(t) => bind(of_opt(lookup_ty(hdr, t), Elab_error::EE_UnknownType(p, t)), in_type)
    None => {
      let from_exp = match exp {
        Some(t) => match t {
          Ty::TBase(_) => None
          Ty::TVar(_) => None
          Ty::TTuple(_) => None
          Ty::TArrow(_, _) => None
          Ty::TData(t0, _) => match lookup_ty(hdr, t0) {
            Some(td) => match has_ctor(c, td) {
              true => Some(td)
              false => None
            }
            None => None
          }
        }
        None => None
      }
      match from_exp {
        Some(td) => in_type(td)
        None => match filter(fn(td) {
          match negb(is_record(sinfo, match td {
            Tdef::Mk_tdef(td_name, _, _) => td_name
          })) {
            true => has_ctor(c, td)
            false => false
          }
        }, match hdr {
          Genv::Mk_genv(ge_types, _) => ge_types
        }) {
          List::Nil => Result0::Err(Elab_error::EE_UnknownCtor(p, c))
          List::Cons(td, l) => match l {
            List::Nil => in_type(td)
            List::Cons(_, _) => Result0::Err(Elab_error::EE_AmbiguousCtor(p, c))
          }
        }
      }
    }
  }
}

pub fn resolve_record(sinfo : List[(Ident, List[Ident])], p : Pos, tq : Option[Ident], names : List[Ident], exp : Option[Ty]) -> Result0[Ident, Elab_error] {
  let same = fn(fs) {
    match eqb0(length(fs), length(names)) {
      true => forallb(fn(f) {
        match index_of(f, fs) {
          Some(_) => true
          None => false
        }
      }, names)
      false => false
    }
  }
  match tq {
    Some(t) => Result0::Ok(t)
    None => match exp {
      Some(t) => match t {
        Ty::TData(t0, _) => match is_record(sinfo, t0) {
          true => Result0::Ok(t0)
          false => Result0::Err(Elab_error::EE_NotRecord(p, Ty::TData(t0, List::Nil)))
        }
        _ => match filter(fn(tf) { same(snd(tf)) }, sinfo) {
          List::Nil => Result0::Err(Elab_error::EE_NotRecord(p, Ty::TBase(Base_ty::BUnit)))
          List::Cons(p0, l) => match p0 {
            (t0, _) => match l {
              List::Nil => Result0::Ok(t0)
              List::Cons(_, _) => Result0::Err(Elab_error::EE_NotRecord(p, Ty::TBase(Base_ty::BUnit)))
            }
          }
        }
      }
      None => match filter(fn(tf) { same(snd(tf)) }, sinfo) {
        List::Nil => Result0::Err(Elab_error::EE_NotRecord(p, Ty::TBase(Base_ty::BUnit)))
        List::Cons(p0, l) => match p0 {
          (t, _) => match l {
            List::Nil => Result0::Ok(t)
            List::Cons(_, _) => Result0::Err(Elab_error::EE_NotRecord(p, Ty::TBase(Base_ty::BUnit)))
          }
        }
      }
    }
  }
}

pub fn proj_field(hdr : Genv, p : Pos, t : Ident, ts : List[Ty], i : Nat, e : Expr) -> Result0[Expr, Elab_error] {
  bind(of_opt(lookup_ty(hdr, t), Elab_error::EE_UnknownType(p, t)), fn(td) {
    match (match td {
      Tdef::Mk_tdef(_, _, td_ctors) => td_ctors
    }) {
      List::Nil => Result0::Err(Elab_error::EE_NotRecord(p, Ty::TData(t, ts)))
      List::Cons(cd, l) => match l {
        List::Nil => {
          let fs = map({ let a1 = fn(x1) { inst(ts, x1) }; fn(x1) { tsubst(a1, x1) } }, match cd {
            Cdef::Mk_cdef(_, cd_fields) => cd_fields
          })
          bind(of_opt(nth_error(fs, i), Elab_error::EE_Type(p, Type_error::E_TupleIndex(i, Ty::TData(t, ts)))), fn(_UU03c4_) {
            let ps = map(fn(j) {
              match eqb0(j, i) {
                true => Pat::PVar
                false => Pat::PWild
              }
            }, seq(Nat::O, length(fs)))
            Result0::Ok(Expr::EMatch(e, _UU03c4_, List::Cons((Pat::PConstr(match cd {
              Cdef::Mk_cdef(cd_name, _) => cd_name
            }, ps), Expr::EVar(Nat::O)), List::Nil)))
          })
        }
        List::Cons(_, _) => Result0::Err(Elab_error::EE_NotRecord(p, Ty::TData(t, ts)))
      }
    }
  })
}

pub fn elab_pat(tys : List[(Ident, Nat)], hdr : Genv, sinfo : List[(Ident, List[Ident])], tps : List[Ident], _UU03c4_ : Ty, sp : Spat) -> Result0[(Pat, Lctx), Elab_error] {
  let go = {
    letrec go = fn(p) {
      fn(open) {
        fn(sps) {
          fn(_UU03c4_s) {
            match sps {
              List::Nil => match _UU03c4_s {
                List::Nil => Result0::Ok((List::Nil, List::Nil))
                List::Cons(_, _) => match open {
                  true => Result0::Ok((map(fn(_) { Pat::PWild }, _UU03c4_s), List::Nil))
                  false => Result0::Err(Elab_error::EE_PatType(p, _UU03c4_))
                }
              }
              List::Cons(sp0, sps_) => match _UU03c4_s {
                List::Nil => Result0::Err(Elab_error::EE_PatType(p, _UU03c4_))
                List::Cons(_UU03c4_0, _UU03c4_s_) => bind(elab_pat(tys, hdr, sinfo, tps, _UU03c4_0, sp0), fn(x) {
                  match x {
                    (q, _UU0394_1) => bind(go(p)(open)(sps_)(_UU03c4_s_), fn(x0) {
                      match x0 {
                        (qs, _UU0394_2) => Result0::Ok((List::Cons(q, qs), app(_UU0394_1, _UU0394_2)))
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
    go
  }
  let named = {
    letrec named = fn(p) {
      fn(names) {
        fn(fs) {
          fn(fps) {
            match fps {
              List::Nil => Result0::Ok(List::Nil)
              List::Cons(p0, fps_) => match p0 {
                (f, sp0) => bind(of_opt(index_of(f, names), Elab_error::EE_UnknownField(p, f)), fn(i) {
                  bind(of_opt(nth_error(fs, i), Elab_error::EE_UnknownField(p, f)), fn(_UU03c4_i) {
                    bind(elab_pat(tys, hdr, sinfo, tps, _UU03c4_i, sp0), fn(x) {
                      match x {
                        (q, _UU0394_) => bind(named(p)(names)(fs)(fps_), fn(rest) { Result0::Ok(List::Cons(((i, q), _UU0394_), rest)) })
                      }
                    })
                  })
                })
              }
            }
          }
        }
      }
    }
    named
  }
  match sp {
    Spat::SPWild(_) => Result0::Ok((Pat::PWild, List::Nil))
    Spat::SPVar(_, x) => Result0::Ok((Pat::PVar, List::Cons((Some(x), _UU03c4_), List::Nil)))
    Spat::SPLit(p, l) => bind(elab_lit(p, Some(_UU03c4_), l), fn(l_) { Result0::Ok((Pat::PLit(l_), List::Nil)) })
    Spat::SPTuple(p, sps) => match _UU03c4_ {
      Ty::TTuple(_UU03c4_s) => bind(go(p)(false)(sps)(_UU03c4_s), fn(x) {
        match x {
          (qs, _UU0394_) => Result0::Ok((Pat::PTuple(qs), _UU0394_))
        }
      })
      _ => Result0::Err(Elab_error::EE_PatType(p, _UU03c4_))
    }
    Spat::SPConstr(p, tq, c, sps, open) => match _UU03c4_ {
      Ty::TData(t, ts) => bind(of_opt(lookup_ty(hdr, t), Elab_error::EE_UnknownType(p, t)), fn(td) {
        bind(match tq {
          Some(t_) => match eqDec_ident(t)(t_) {
            true => Result0::Ok(())
            false => Result0::Err(Elab_error::EE_PatType(p, _UU03c4_))
          }
          None => Result0::Ok(())
        }, fn(_) {
          bind(of_opt(lookup_ctor(td, c), Elab_error::EE_UnknownCtor(p, c)), fn(cd) {
            bind(go(p)(open)(sps)(map({ let a1 = fn(x1) { inst(ts, x1) }; fn(x1) { tsubst(a1, x1) } }, match cd {
              Cdef::Mk_cdef(_, cd_fields) => cd_fields
            })), fn(x) {
              match x {
                (qs, _UU0394_) => Result0::Ok((Pat::PConstr(c, qs), _UU0394_))
              }
            })
          })
        })
      })
      _ => Result0::Err(Elab_error::EE_PatType(p, _UU03c4_))
    }
    Spat::SPRecord(p, fps, open) => match _UU03c4_ {
      Ty::TData(t, ts) => bind(of_opt(assoc(t, sinfo), Elab_error::EE_NotRecord(p, _UU03c4_)), fn(names) {
        bind(of_opt(lookup_ty(hdr, t), Elab_error::EE_UnknownType(p, t)), fn(td) {
          match (match td {
            Tdef::Mk_tdef(_, _, td_ctors) => td_ctors
          }) {
            List::Nil => Result0::Err(Elab_error::EE_NotRecord(p, _UU03c4_))
            List::Cons(cd, l) => match l {
              List::Nil => {
                let fs = map({ let a1 = fn(x1) { inst(ts, x1) }; fn(x1) { tsubst(a1, x1) } }, match cd {
                  Cdef::Mk_cdef(_, cd_fields) => cd_fields
                })
                bind(named(p)(names)(fs)(fps), fn(given) {
                  let pick = fn(j) {
                    match find(fn(x) { eqb0(fst(fst(x)), j) }, given) {
                      Some(p0) => match p0 {
                        (p1, _UU0394_) => match p1 {
                          (_, q) => Result0::Ok((q, _UU0394_))
                        }
                      }
                      None => match open {
                        true => Result0::Ok((Pat::PWild, List::Nil))
                        false => Result0::Err(Elab_error::EE_MissingField(p, nth(j, names, String0::EmptyString)))
                      }
                    }
                  }
                  bind(mapM(pick, seq(Nat::O, length(fs))), fn(q_UU0394_s) {
                    Result0::Ok((Pat::PConstr(match cd {
                      Cdef::Mk_cdef(cd_name, _) => cd_name
                    }, map(fn(x1) { fst(x1) }, q_UU0394_s)), concat(map(fn(x1) { snd(x1) }, q_UU0394_s))))
                  })
                })
              }
              List::Cons(_, _) => Result0::Err(Elab_error::EE_NotRecord(p, _UU03c4_))
            }
          }
        })
      })
      _ => Result0::Err(Elab_error::EE_NotRecord(p, _UU03c4_))
    }
    Spat::SPAnnot(p, q, t) => bind(elab_ty(tys, tps, t), fn(_UU03c4__) {
      match eqDec_ty(_UU03c4__)(_UU03c4_) {
        true => elab_pat(tys, hdr, sinfo, tps, _UU03c4_, q)
        false => Result0::Err(Elab_error::EE_Annot(p, _UU03c4__, _UU03c4_))
      }
    })
  }
}

pub fn param_tys(tys : List[(Ident, Nat)], tps : List[Ident], p : Pos, ps : List[(Ident, Option[Sty])], exps : List[Option[Ty]]) -> Result0[List[Ty], Elab_error] {
  match ps {
    List::Nil => Result0::Ok(List::Nil)
    List::Cons(p0, ps_) => match p0 {
      (x, ann) => match exps {
        List::Nil => {
          let ex = None
          let exps_ = List::Nil
          bind(match ann {
            Some(t) => elab_ty(tys, tps, t)
            None => match ex {
              Some(_UU03c4_) => Result0::Ok(_UU03c4_)
              None => Result0::Err(Elab_error::EE_LambdaParam(p, x))
            }
          }, fn(_UU03c4_) {
            bind(param_tys(tys, tps, p, ps_, exps_), fn(_UU03c4_s) { Result0::Ok(List::Cons(_UU03c4_, _UU03c4_s)) })
          })
        }
        List::Cons(y, ys) => bind(match ann {
          Some(t) => elab_ty(tys, tps, t)
          None => match y {
            Some(_UU03c4_) => Result0::Ok(_UU03c4_)
            None => Result0::Err(Elab_error::EE_LambdaParam(p, x))
          }
        }, fn(_UU03c4_) {
          bind(param_tys(tys, tps, p, ps_, ys), fn(_UU03c4_s) { Result0::Ok(List::Cons(_UU03c4_, _UU03c4_s)) })
        })
      }
    }
  }
}

pub fn elab_lam(tys : List[(Ident, Nat)], hdr : Genv, tps : List[Ident], _UU0393_ : Lctx, p : Pos, ps : List[(Ident, Option[Sty])], ret : Option[Sty], pexps : List[Option[Ty]], rexp : Option[Ty], elab_body : (Lctx) -> (Option[Ty]) -> Result0[Expr, Elab_error]) -> Result0[Expr, Elab_error] {
  bind(param_tys(tys, tps, p, ps, pexps), fn(_UU03c4_s) {
    let _UU0393__ = app(combine(map(fn(x) { Some(fst(x)) }, ps), _UU03c4_s), _UU0393_)
    bind(match ret {
      Some(t) => map_result(fn(x) { Some(x) }, elab_ty(tys, tps, t))
      None => Result0::Ok(rexp)
    }, fn(_UU03c4_r) {
      bind(elab_body(_UU0393__)(_UU03c4_r), fn(body_) {
        bind(match _UU03c4_r {
          Some(r) => Result0::Ok(r)
          None => type_of(hdr, p, _UU0393__, body_)
        }, fn(r) { Result0::Ok(Expr::ELam(_UU03c4_s, r, body_)) })
      })
    })
  })
}

pub fn needs_context(e : Sexpr) -> Bool {
  match e {
    Sexpr::SLam(_, ps, _, _) => existsb(fn(xa) {
      match snd(xa) {
        Some(_) => false
        None => true
      }
    }, ps)
    _ => false
  }
}

pub fn data_inst(t : Ident, n : Nat, exp : Option[Ty]) -> List[Option[Ty]] {
  match exp {
    Some(t0) => tmatch(Ty::TData(t, tvars(n)), t0, repeat(None, n))
    None => repeat(None, n)
  }
}

pub fn elab(tys : List[(Ident, Nat)], hdr : Genv, sinfo : List[(Ident, List[Ident])], tps : List[Ident], _UU0393_ : Lctx, exp : Option[Ty], e : Sexpr) -> Result0[Expr, Elab_error] {
  let elab_args = {
    letrec elab_args = fn(es) {
      fn(exps) {
        match es {
          List::Nil => Result0::Ok(List::Nil)
          List::Cons(e0, es_) => match exps {
            List::Nil => {
              let x = None
              let exps_ = List::Nil
              bind(elab(tys, hdr, sinfo, tps, _UU0393_, x, e0), fn(e_) {
                bind(elab_args(es_)(exps_), fn(es2) { Result0::Ok(List::Cons(e_, es2)) })
              })
            }
            List::Cons(x, xs) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, x, e0), fn(e_) {
              bind(elab_args(es_)(xs), fn(es2) { Result0::Ok(List::Cons(e_, es2)) })
            })
          }
        }
      }
    }
    elab_args
  }
  let gargs1 = {
    letrec gargs1 = fn(p) {
      fn(es) {
        fn(ps) {
          fn(s) {
            match es {
              List::Nil => Result0::Ok((List::Nil, s))
              List::Cons(e0, es_) => match ps {
                List::Nil => {
                  let pt = None
                  let ps_ = List::Nil
                  let ex = match pt {
                    Some(t) => resolve(s, t)
                    None => None
                  }
                  match needs_context(e0) {
                    true => match ex {
                      Some(_) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, ex, e0), fn(e_) {
                        bind(match pt {
                          Some(t) => bind(type_of(hdr, p, _UU0393_, e_), fn(_UU03c4_) { Result0::Ok(tmatch(t, _UU03c4_, s)) })
                          None => Result0::Ok(s)
                        }, fn(s_) {
                          bind(gargs1(p)(es_)(ps_)(s_), fn(x) {
                            match x {
                              (r, s2) => Result0::Ok((List::Cons(Some(e_), r), s2))
                            }
                          })
                        })
                      })
                      None => bind(gargs1(p)(es_)(ps_)(s), fn(x) {
                        match x {
                          (r, s2) => Result0::Ok((List::Cons(None, r), s2))
                        }
                      })
                    }
                    false => bind(elab(tys, hdr, sinfo, tps, _UU0393_, ex, e0), fn(e_) {
                      bind(match pt {
                        Some(t) => bind(type_of(hdr, p, _UU0393_, e_), fn(_UU03c4_) { Result0::Ok(tmatch(t, _UU03c4_, s)) })
                        None => Result0::Ok(s)
                      }, fn(s_) {
                        bind(gargs1(p)(es_)(ps_)(s_), fn(x) {
                          match x {
                            (r, s2) => Result0::Ok((List::Cons(Some(e_), r), s2))
                          }
                        })
                      })
                    })
                  }
                }
                List::Cons(t, ts) => {
                  let pt = Some(t)
                  let ex = match pt {
                    Some(t0) => resolve(s, t0)
                    None => None
                  }
                  match needs_context(e0) {
                    true => match ex {
                      Some(_) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, ex, e0), fn(e_) {
                        bind(match pt {
                          Some(t0) => bind(type_of(hdr, p, _UU0393_, e_), fn(_UU03c4_) { Result0::Ok(tmatch(t0, _UU03c4_, s)) })
                          None => Result0::Ok(s)
                        }, fn(s_) {
                          bind(gargs1(p)(es_)(ts)(s_), fn(x) {
                            match x {
                              (r, s2) => Result0::Ok((List::Cons(Some(e_), r), s2))
                            }
                          })
                        })
                      })
                      None => bind(gargs1(p)(es_)(ts)(s), fn(x) {
                        match x {
                          (r, s2) => Result0::Ok((List::Cons(None, r), s2))
                        }
                      })
                    }
                    false => bind(elab(tys, hdr, sinfo, tps, _UU0393_, ex, e0), fn(e_) {
                      bind(match pt {
                        Some(t0) => bind(type_of(hdr, p, _UU0393_, e_), fn(_UU03c4_) { Result0::Ok(tmatch(t0, _UU03c4_, s)) })
                        None => Result0::Ok(s)
                      }, fn(s_) {
                        bind(gargs1(p)(es_)(ts)(s_), fn(x) {
                          match x {
                            (r, s2) => Result0::Ok((List::Cons(Some(e_), r), s2))
                          }
                        })
                      })
                    })
                  }
                }
              }
            }
          }
        }
      }
    }
    gargs1
  }
  let gargs2 = {
    letrec gargs2 = fn(p) {
      fn(es) {
        fn(pre) {
          fn(ps) {
            fn(s) {
              match es {
                List::Nil => Result0::Ok((List::Nil, s))
                List::Cons(e0, es_) => match pre {
                  List::Nil => {
                    let d = None
                    let pre_ = List::Nil
                    match ps {
                      List::Nil => {
                        let pt = None
                        let ps_ = List::Nil
                        bind(match d {
                          Some(e_) => Result0::Ok(e_)
                          None => match e0 {
                            Sexpr::SLam(q, lps, ret, body) => match pt {
                              Some(t) => match t {
                                Ty::TArrow(pps, pr) => {
                                  let pexps = match eqb0(length(pps), length(lps)) {
                                    true => map(fn(x1) { resolve(s, x1) }, pps)
                                    false => repeat(None, length(lps))
                                  }
                                  elab_lam(tys, hdr, tps, _UU0393_, q, lps, ret, pexps, resolve(s, pr), fn(_UU0393__) { fn(t0) { elab(tys, hdr, sinfo, tps, _UU0393__, t0, body) } })
                                }
                                _ => elab(tys, hdr, sinfo, tps, _UU0393_, match pt {
                                  Some(t0) => resolve(s, t0)
                                  None => None
                                }, e0)
                              }
                              None => elab(tys, hdr, sinfo, tps, _UU0393_, match pt {
                                Some(t) => resolve(s, t)
                                None => None
                              }, e0)
                            }
                            _ => elab(tys, hdr, sinfo, tps, _UU0393_, match pt {
                              Some(t) => resolve(s, t)
                              None => None
                            }, e0)
                          }
                        }, fn(e_) {
                          bind(match d {
                            Some(_) => Result0::Ok(s)
                            None => match pt {
                              Some(t) => bind(type_of(hdr, p, _UU0393_, e_), fn(_UU03c4_) { Result0::Ok(tmatch(t, _UU03c4_, s)) })
                              None => Result0::Ok(s)
                            }
                          }, fn(s_) {
                            bind(gargs2(p)(es_)(pre_)(ps_)(s_), fn(x) {
                              match x {
                                (r, s2) => Result0::Ok((List::Cons(e_, r), s2))
                              }
                            })
                          })
                        })
                      }
                      List::Cons(t, ts) => {
                        let pt = Some(t)
                        bind(match d {
                          Some(e_) => Result0::Ok(e_)
                          None => match e0 {
                            Sexpr::SLam(q, lps, ret, body) => match pt {
                              Some(t0) => match t0 {
                                Ty::TArrow(pps, pr) => {
                                  let pexps = match eqb0(length(pps), length(lps)) {
                                    true => map(fn(x1) { resolve(s, x1) }, pps)
                                    false => repeat(None, length(lps))
                                  }
                                  elab_lam(tys, hdr, tps, _UU0393_, q, lps, ret, pexps, resolve(s, pr), fn(_UU0393__) { fn(t1) { elab(tys, hdr, sinfo, tps, _UU0393__, t1, body) } })
                                }
                                _ => elab(tys, hdr, sinfo, tps, _UU0393_, match pt {
                                  Some(t1) => resolve(s, t1)
                                  None => None
                                }, e0)
                              }
                              None => elab(tys, hdr, sinfo, tps, _UU0393_, match pt {
                                Some(t0) => resolve(s, t0)
                                None => None
                              }, e0)
                            }
                            _ => elab(tys, hdr, sinfo, tps, _UU0393_, match pt {
                              Some(t0) => resolve(s, t0)
                              None => None
                            }, e0)
                          }
                        }, fn(e_) {
                          bind(match d {
                            Some(_) => Result0::Ok(s)
                            None => match pt {
                              Some(t0) => bind(type_of(hdr, p, _UU0393_, e_), fn(_UU03c4_) { Result0::Ok(tmatch(t0, _UU03c4_, s)) })
                              None => Result0::Ok(s)
                            }
                          }, fn(s_) {
                            bind(gargs2(p)(es_)(pre_)(ts)(s_), fn(x) {
                              match x {
                                (r, s2) => Result0::Ok((List::Cons(e_, r), s2))
                              }
                            })
                          })
                        })
                      }
                    }
                  }
                  List::Cons(d, ds) => match ps {
                    List::Nil => {
                      let pt = None
                      let ps_ = List::Nil
                      bind(match d {
                        Some(e_) => Result0::Ok(e_)
                        None => match e0 {
                          Sexpr::SLam(q, lps, ret, body) => match pt {
                            Some(t) => match t {
                              Ty::TArrow(pps, pr) => {
                                let pexps = match eqb0(length(pps), length(lps)) {
                                  true => map(fn(x1) { resolve(s, x1) }, pps)
                                  false => repeat(None, length(lps))
                                }
                                elab_lam(tys, hdr, tps, _UU0393_, q, lps, ret, pexps, resolve(s, pr), fn(_UU0393__) { fn(t0) { elab(tys, hdr, sinfo, tps, _UU0393__, t0, body) } })
                              }
                              _ => elab(tys, hdr, sinfo, tps, _UU0393_, match pt {
                                Some(t0) => resolve(s, t0)
                                None => None
                              }, e0)
                            }
                            None => elab(tys, hdr, sinfo, tps, _UU0393_, match pt {
                              Some(t) => resolve(s, t)
                              None => None
                            }, e0)
                          }
                          _ => elab(tys, hdr, sinfo, tps, _UU0393_, match pt {
                            Some(t) => resolve(s, t)
                            None => None
                          }, e0)
                        }
                      }, fn(e_) {
                        bind(match d {
                          Some(_) => Result0::Ok(s)
                          None => match pt {
                            Some(t) => bind(type_of(hdr, p, _UU0393_, e_), fn(_UU03c4_) { Result0::Ok(tmatch(t, _UU03c4_, s)) })
                            None => Result0::Ok(s)
                          }
                        }, fn(s_) {
                          bind(gargs2(p)(es_)(ds)(ps_)(s_), fn(x) {
                            match x {
                              (r, s2) => Result0::Ok((List::Cons(e_, r), s2))
                            }
                          })
                        })
                      })
                    }
                    List::Cons(t, ts) => {
                      let pt = Some(t)
                      bind(match d {
                        Some(e_) => Result0::Ok(e_)
                        None => match e0 {
                          Sexpr::SLam(q, lps, ret, body) => match pt {
                            Some(t0) => match t0 {
                              Ty::TArrow(pps, pr) => {
                                let pexps = match eqb0(length(pps), length(lps)) {
                                  true => map(fn(x1) { resolve(s, x1) }, pps)
                                  false => repeat(None, length(lps))
                                }
                                elab_lam(tys, hdr, tps, _UU0393_, q, lps, ret, pexps, resolve(s, pr), fn(_UU0393__) { fn(t1) { elab(tys, hdr, sinfo, tps, _UU0393__, t1, body) } })
                              }
                              _ => elab(tys, hdr, sinfo, tps, _UU0393_, match pt {
                                Some(t1) => resolve(s, t1)
                                None => None
                              }, e0)
                            }
                            None => elab(tys, hdr, sinfo, tps, _UU0393_, match pt {
                              Some(t0) => resolve(s, t0)
                              None => None
                            }, e0)
                          }
                          _ => elab(tys, hdr, sinfo, tps, _UU0393_, match pt {
                            Some(t0) => resolve(s, t0)
                            None => None
                          }, e0)
                        }
                      }, fn(e_) {
                        bind(match d {
                          Some(_) => Result0::Ok(s)
                          None => match pt {
                            Some(t0) => bind(type_of(hdr, p, _UU0393_, e_), fn(_UU03c4_) { Result0::Ok(tmatch(t0, _UU03c4_, s)) })
                            None => Result0::Ok(s)
                          }
                        }, fn(s_) {
                          bind(gargs2(p)(es_)(ds)(ts)(s_), fn(x) {
                            match x {
                              (r, s2) => Result0::Ok((List::Cons(e_, r), s2))
                            }
                          })
                        })
                      })
                    }
                  }
                }
              }
            }
          }
        }
      }
    }
    gargs2
  }
  let ctor_app = fn(p) {
    fn(q) {
      fn(td) {
        fn(cd) {
          fn(args) {
            let n = match td {
              Tdef::Mk_tdef(_, td_tparams, _) => td_tparams
            }
            let fs = match cd {
              Cdef::Mk_cdef(_, cd_fields) => cd_fields
            }
            match negb(eqb0(length(fs), length(args))) {
              true => Result0::Err(Elab_error::EE_CtorArity(q, match cd {
                Cdef::Mk_cdef(cd_name, _) => cd_name
              }, length(fs), length(args)))
              false => bind(gargs1(p)(args)(fs)(data_inst(match td {
                Tdef::Mk_tdef(td_name, _, _) => td_name
              }, n, exp)), fn(x) {
                match x {
                  (pre, s1) => bind(gargs2(p)(args)(pre)(fs)(s1), fn(x0) {
                    match x0 {
                      (args_, s) => match all_some(s) {
                        Some(ts) => Result0::Ok(Expr::EConstr(match td {
                          Tdef::Mk_tdef(td_name, _, _) => td_name
                        }, match cd {
                          Cdef::Mk_cdef(cd_name, _) => cd_name
                        }, ts, Expr::ETuple(args_)))
                        None => Result0::Err(Elab_error::EE_CannotInfer(q, match cd {
                          Cdef::Mk_cdef(cd_name, _) => cd_name
                        }))
                      }
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
  let rfields = {
    letrec rfields = fn(p) {
      fn(_UU0393_0) {
        fn(names) {
          fn(fs) {
            fn(fes) {
              fn(s) {
                match fes {
                  List::Nil => Result0::Ok(((List::Nil, _UU0393_0), s))
                  List::Cons(p0, fes_) => match p0 {
                    (f, fe) => bind(of_opt(index_of(f, names), Elab_error::EE_UnknownField(p, f)), fn(i) {
                      bind(of_opt(nth_error(fs, i), Elab_error::EE_UnknownField(p, f)), fn(_UU03c4_f) {
                        bind(elab(tys, hdr, sinfo, tps, _UU0393_0, resolve(s, _UU03c4_f), fe), fn(e_) {
                          bind(type_of(hdr, p, _UU0393_0, e_), fn(_UU03c4_) {
                            bind(rfields(p)(List::Cons((None, _UU03c4_), _UU0393_0))(names)(fs)(fes_)(tmatch(_UU03c4_f, _UU03c4_, s)), fn(x) {
                              match x {
                                (p1, s1) => match p1 {
                                  (rest, _UU0393_1) => Result0::Ok(((List::Cons((e_, i), rest), _UU0393_1), s1))
                                }
                              }
                            })
                          })
                        })
                      })
                    })
                  }
                }
              }
            }
          }
        }
      }
    }
    rfields
  }
  match e {
    Sexpr::SVar(p, x) => match lookup_local(x, _UU0393_) {
      Some(i) => Result0::Ok(Expr::EVar(i))
      None => match lookup_fn(hdr, x) {
        Some(fd) => elab_global(p, x, fd, exp)
        None => Result0::Err(Elab_error::EE_Unbound(p, x))
      }
    }
    Sexpr::SLit(p, l) => bind(elab_lit(p, exp, l), fn(l_) { Result0::Ok(Expr::ELit(l_)) })
    Sexpr::SApp(p, f, args) => match f {
      Sexpr::SVar(q, g) => match lookup_local(g, _UU0393_) {
        Some(_) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, None, f), fn(f_) {
          bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
            bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
          })
        })
        None => match lookup_fn(hdr, g) {
          Some(fd) => match (match fd {
            Fdef::Mk_fdef(_, fd_tparams, _, _, _) => fd_tparams
          }) {
            Nat::O => bind(elab_args(args)(map(fn(x) { Some(x) }, match fd {
              Fdef::Mk_fdef(_, _, fd_params, _, _) => fd_params
            })), fn(args_) { Result0::Ok(Expr::EApp(Expr::EGlobal(g, List::Nil), args_)) })
            Nat::S(n0) => {
              let n = Nat::S(n0)
              let s0 = match exp {
                Some(t) => tmatch(match fd {
                  Fdef::Mk_fdef(_, _, _, fd_ret, _) => fd_ret
                }, t, repeat(None, n))
                None => repeat(None, n)
              }
              bind(gargs1(p)(args)(match fd {
                Fdef::Mk_fdef(_, _, fd_params, _, _) => fd_params
              })(s0), fn(x) {
                match x {
                  (pre, s1) => bind(gargs2(p)(args)(pre)(match fd {
                    Fdef::Mk_fdef(_, _, fd_params, _, _) => fd_params
                  })(s1), fn(x0) {
                    match x0 {
                      (args_, s) => match all_some(s) {
                        Some(ts) => Result0::Ok(Expr::EApp(Expr::EGlobal(g, ts), args_))
                        None => Result0::Err(Elab_error::EE_CannotInfer(q, g))
                      }
                    }
                  })
                }
              })
            }
          }
          None => match eqDec_ident(g)(String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))) {
            true => bind(elab_args(args)(List::Cons(Some(Ty::TBase(Base_ty::BBool)), List::Nil)), fn(args_) { Result0::Ok(Expr::EPrim(Prim_op::PBoolNot, args_)) })
            false => match eqDec_ident(g)(String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString))))))) {
              true => match args {
                List::Nil => Result0::Err(Elab_error::EE_Unbound(q, g))
                List::Cons(a, l) => match l {
                  List::Nil => bind(elab(tys, hdr, sinfo, tps, _UU0393_, None, a), fn(a_) { Result0::Ok(Expr::ELet(a_, Expr::ELit(Lit::LUnit))) })
                  List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                }
              }
              false => Result0::Err(Elab_error::EE_Unbound(q, g))
            }
          }
        }
      }
      Sexpr::SLit(_, _) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::SApp(_, _, _) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::SInfix(_, _, _, _) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::SUnary(_, _, _) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::SLet(_, _, _, _, _) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::SIf(_, _, _, _) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::STup(_, _) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::SProj(_, _, _) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::SLam(_, _, _, _) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::SAnnot(_, _, _) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::SConstr(q, tq, c) => bind(resolve_ctor(hdr, sinfo, q, tq, c, exp), fn(x) {
        match x {
          (td, cd) => ctor_app(p)(q)(td)(cd)(args)
        }
      })
      Sexpr::SRecord(_, _, _) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::SField(_, _, _) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::SMatch(_, _, _) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
    }
    Sexpr::SInfix(p, op, a, b) => match eqDec_ident(op)(String0::String1(Ascii::Ascii0(false, true, true, false, false, true, false, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, false, false), String0::EmptyString))) {
      true => bind(elab(tys, hdr, sinfo, tps, _UU0393_, Some(Ty::TBase(Base_ty::BBool)), a), fn(a_) {
        bind(elab(tys, hdr, sinfo, tps, _UU0393_, Some(Ty::TBase(Base_ty::BBool)), b), fn(b_) { Result0::Ok(Expr::EIf(a_, b_, e_false)) })
      })
      false => match eqDec_ident(op)(String0::String1(Ascii::Ascii0(false, false, true, true, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, true, true, true, false), String0::EmptyString))) {
        true => bind(elab(tys, hdr, sinfo, tps, _UU0393_, Some(Ty::TBase(Base_ty::BBool)), a), fn(a_) {
          bind(elab(tys, hdr, sinfo, tps, _UU0393_, Some(Ty::TBase(Base_ty::BBool)), b), fn(b_) { Result0::Ok(Expr::EIf(a_, e_true, b_)) })
        })
        false => {
          let exp_ = match assoc(op, arith_ops) {
            Some(_) => exp
            None => None
          }
          match (match flexible(a) {
            true => negb(flexible(b))
            false => false
          }) {
            true => bind(elab(tys, hdr, sinfo, tps, _UU0393_, exp_, b), fn(b_) {
              bind(type_of(hdr, p, _UU0393_, b_), fn(_UU03c4_) {
                bind(elab(tys, hdr, sinfo, tps, _UU0393_, Some(_UU03c4_), a), fn(a_) { elab_binop(p, op, _UU03c4_, a_, b_) })
              })
            })
            false => bind(elab(tys, hdr, sinfo, tps, _UU0393_, exp_, a), fn(a_) {
              bind(type_of(hdr, p, _UU0393_, a_), fn(_UU03c4_) {
                bind(elab(tys, hdr, sinfo, tps, _UU0393_, Some(_UU03c4_), b), fn(b_) { elab_binop(p, op, _UU03c4_, a_, b_) })
              })
            })
          }
        }
      }
    }
    Sexpr::SUnary(p, op, a) => match eqDec_ident(op)(String0::String1(Ascii::Ascii0(true, false, true, true, false, true, false, false), String0::EmptyString)) {
      true => match a {
        Sexpr::SLit(q, l) => match l {
          Slit::SLInt(k, z) => bind(elab_lit(q, exp, Slit::SLInt(k, opp(z))), fn(l_) { Result0::Ok(Expr::ELit(l_)) })
          _ => bind(elab(tys, hdr, sinfo, tps, _UU0393_, exp, a), fn(a_) {
            bind(type_of(hdr, p, _UU0393_, a_), fn(_UU03c4_) {
              match _UU03c4_ {
                Ty::TBase(b) => match b {
                  Base_ty::BInt(k) => Result0::Ok(Expr::EPrim(Prim_op::PIntNeg(k), List::Cons(a_, List::Nil)))
                  _ => Result0::Err(Elab_error::EE_NoOperator(p, op, _UU03c4_))
                }
                _ => Result0::Err(Elab_error::EE_NoOperator(p, op, _UU03c4_))
              }
            })
          })
        }
        _ => bind(elab(tys, hdr, sinfo, tps, _UU0393_, exp, a), fn(a_) {
          bind(type_of(hdr, p, _UU0393_, a_), fn(_UU03c4_) {
            match _UU03c4_ {
              Ty::TBase(b) => match b {
                Base_ty::BInt(k) => Result0::Ok(Expr::EPrim(Prim_op::PIntNeg(k), List::Cons(a_, List::Nil)))
                _ => Result0::Err(Elab_error::EE_NoOperator(p, op, _UU03c4_))
              }
              _ => Result0::Err(Elab_error::EE_NoOperator(p, op, _UU03c4_))
            }
          })
        })
      }
      false => match eqDec_ident(op)(String0::String1(Ascii::Ascii0(true, false, false, false, false, true, false, false), String0::EmptyString)) {
        true => bind(elab(tys, hdr, sinfo, tps, _UU0393_, Some(Ty::TBase(Base_ty::BBool)), a), fn(a_) {
          Result0::Ok(Expr::EPrim(Prim_op::PBoolNot, List::Cons(a_, List::Nil)))
        })
        false => Result0::Err(Elab_error::EE_NoOperator(p, op, Ty::TBase(Base_ty::BUnit)))
      }
    }
    Sexpr::SLet(p, x, ann, e1, body) => bind(match ann {
      Some(t) => map_result(fn(x0) { Some(x0) }, elab_ty(tys, tps, t))
      None => Result0::Ok(None)
    }, fn(_UU03c4_ann) {
      bind(elab(tys, hdr, sinfo, tps, _UU0393_, _UU03c4_ann, e1), fn(e1_) {
        bind(type_of(hdr, p, _UU0393_, e1_), fn(_UU03c4_1) {
          bind(match _UU03c4_ann {
            Some(t) => match eqDec_ty(t)(_UU03c4_1) {
              true => Result0::Ok(())
              false => Result0::Err(Elab_error::EE_Annot(p, t, _UU03c4_1))
            }
            None => Result0::Ok(())
          }, fn(_) {
            bind(elab(tys, hdr, sinfo, tps, List::Cons((x, _UU03c4_1), _UU0393_), exp, body), fn(body_) { Result0::Ok(Expr::ELet(e1_, body_)) })
          })
        })
      })
    })
    Sexpr::SIf(p, c, t, oe) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, Some(Ty::TBase(Base_ty::BBool)), c), fn(c_) {
      match oe {
        Some(e0) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, exp, t), fn(t_) {
          bind(match exp {
            Some(_UU03c4_) => Result0::Ok(Some(_UU03c4_))
            None => map_result(fn(x) { Some(x) }, type_of(hdr, p, _UU0393_, t_))
          }, fn(exp_) {
            bind(elab(tys, hdr, sinfo, tps, _UU0393_, exp_, e0), fn(e0_) { Result0::Ok(Expr::EIf(c_, t_, e0_)) })
          })
        })
        None => bind(elab(tys, hdr, sinfo, tps, _UU0393_, Some(Ty::TBase(Base_ty::BUnit)), t), fn(t_) { Result0::Ok(Expr::EIf(c_, t_, Expr::ELit(Lit::LUnit))) })
      }
    })
    Sexpr::STup(_, es) => {
      let exps = match exp {
        Some(t) => match t {
          Ty::TBase(_) => repeat(None, length(es))
          Ty::TVar(_) => repeat(None, length(es))
          Ty::TTuple(ts) => match eqb0(length(ts), length(es)) {
            true => map(fn(x) { Some(x) }, ts)
            false => repeat(None, length(es))
          }
          _ => repeat(None, length(es))
        }
        None => repeat(None, length(es))
      }
      bind(elab_args(es)(exps), fn(es_) { Result0::Ok(Expr::ETuple(es_)) })
    }
    Sexpr::SProj(p, e0, i) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, None, e0), fn(e0_) {
      bind(type_of(hdr, p, _UU0393_, e0_), fn(_UU03c4_) {
        match _UU03c4_ {
          Ty::TData(t, ts) => proj_field(hdr, p, t, ts, i, e0_)
          _ => Result0::Ok(Expr::EProj(e0_, i))
        }
      })
    })
    Sexpr::SLam(p, ps, ret, body) => {
      let pexps = match exp {
        Some(t) => arrow_params(t, length(ps))
        None => repeat(None, length(ps))
      }
      let rexp = match exp {
        Some(t) => match t {
          Ty::TBase(_) => None
          Ty::TVar(_) => None
          Ty::TTuple(_) => None
          Ty::TArrow(_, r) => Some(r)
          Ty::TData(_, _) => None
        }
        None => None
      }
      elab_lam(tys, hdr, tps, _UU0393_, p, ps, ret, pexps, rexp, fn(_UU0393__) { fn(t) { elab(tys, hdr, sinfo, tps, _UU0393__, t, body) } })
    }
    Sexpr::SAnnot(p, e0, t) => bind(elab_ty(tys, tps, t), fn(_UU03c4_) {
      bind(elab(tys, hdr, sinfo, tps, _UU0393_, Some(_UU03c4_), e0), fn(e0_) {
        bind(type_of(hdr, p, _UU0393_, e0_), fn(_UU03c4_0) {
          match eqDec_ty(_UU03c4_)(_UU03c4_0) {
            true => Result0::Ok(e0_)
            false => Result0::Err(Elab_error::EE_Annot(p, _UU03c4_, _UU03c4_0))
          }
        })
      })
    })
    Sexpr::SConstr(p, tq, c) => bind(resolve_ctor(hdr, sinfo, p, tq, c, exp), fn(x) {
      match x {
        (td, cd) => ctor_app(p)(p)(td)(cd)(List::Nil)
      }
    })
    Sexpr::SRecord(p, tq, fes) => bind(resolve_record(sinfo, p, tq, map(fn(x1) { fst(x1) }, fes), exp), fn(t) {
      bind(of_opt(assoc(t, sinfo), Elab_error::EE_NotRecord(p, Ty::TData(t, List::Nil))), fn(names) {
        bind(of_opt(lookup_ty(hdr, t), Elab_error::EE_UnknownType(p, t)), fn(td) {
          match (match td {
            Tdef::Mk_tdef(_, _, td_ctors) => td_ctors
          }) {
            List::Nil => Result0::Err(Elab_error::EE_NotRecord(p, Ty::TData(t, List::Nil)))
            List::Cons(cd, l) => match l {
              List::Nil => {
                let n = match td {
                  Tdef::Mk_tdef(_, td_tparams, _) => td_tparams
                }
                bind(rfields(p)(_UU0393_)(names)(match cd {
                  Cdef::Mk_cdef(_, cd_fields) => cd_fields
                })(fes)(data_inst(t, n, exp)), fn(x) {
                  match x {
                    (p0, s) => match p0 {
                      (bound, _) => bind(of_opt(all_some(s), Elab_error::EE_CannotInfer(p, t)), fn(ts) {
                        let m = length(bound)
                        let var_of = fn(j) {
                          match find(fn(x0) { eqb0(snd(fst(x0)), j) }, combine(bound, seq(Nat::O, m))) {
                            Some(p1) => match p1 {
                              (_, k) => Result0::Ok(Expr::EVar(sub(sub(m, Nat::S(Nat::O)), k)))
                            }
                            None => Result0::Err(Elab_error::EE_MissingField(p, nth(j, names, String0::EmptyString)))
                          }
                        }
                        bind(mapM(var_of, seq(Nat::O, length(names))), fn(vs) {
                          bind(match eqb0(m, length(names)) {
                            true => Result0::Ok(())
                            false => Result0::Err(Elab_error::EE_UnknownField(p, String0::EmptyString))
                          }, fn(_) {
                            Result0::Ok(fold_right(fn(b) { fn(acc) { Expr::ELet(fst(b), acc) } }, Expr::EConstr(t, match cd {
                              Cdef::Mk_cdef(cd_name, _) => cd_name
                            }, ts, Expr::ETuple(vs)), bound))
                          })
                        })
                      })
                    }
                  }
                })
              }
              List::Cons(_, _) => Result0::Err(Elab_error::EE_NotRecord(p, Ty::TData(t, List::Nil)))
            }
          }
        })
      })
    })
    Sexpr::SField(p, e0, f) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, None, e0), fn(e0_) {
      bind(type_of(hdr, p, _UU0393_, e0_), fn(_UU03c4_) {
        match _UU03c4_ {
          Ty::TData(t, ts) => bind(of_opt(assoc(t, sinfo), Elab_error::EE_NotRecord(p, _UU03c4_)), fn(names) {
            bind(of_opt(index_of(f, names), Elab_error::EE_UnknownField(p, f)), fn(i) { proj_field(hdr, p, t, ts, i, e0_) })
          })
          _ => Result0::Err(Elab_error::EE_NotRecord(p, _UU03c4_))
        }
      })
    })
    Sexpr::SMatch(p, e0, cases) => bind(elab(tys, hdr, sinfo, tps, _UU0393_, None, e0), fn(e0_) {
      bind(type_of(hdr, p, _UU0393_, e0_), fn(_UU03c4_s) {
        let arms = {
          letrec arms = fn(cs) {
            fn(exp0) {
              match cs {
                List::Nil => Result0::Ok((List::Nil, exp0))
                List::Cons(p0, cs_) => match p0 {
                  (sp, b) => bind(elab_pat(tys, hdr, sinfo, tps, _UU03c4_s, sp), fn(x) {
                    match x {
                      (q, _UU0394_) => {
                        let _UU0393__ = app(_UU0394_, _UU0393_)
                        bind(elab(tys, hdr, sinfo, tps, _UU0393__, exp0, b), fn(b_) {
                          bind(match exp0 {
                            Some(t) => Result0::Ok(t)
                            None => type_of(hdr, p, _UU0393__, b_)
                          }, fn(_UU03c4_b) {
                            bind(arms(cs_)(Some(_UU03c4_b)), fn(x0) {
                              match x0 {
                                (rest, r) => Result0::Ok((List::Cons((q, b_), rest), r))
                              }
                            })
                          })
                        })
                      }
                    }
                  })
                }
              }
            }
          }
          arms
        }
        bind(arms(cases)(exp), fn(x) {
          match x {
            (bs, r) => bind(of_opt(r, Elab_error::EE_EmptyMatch(p)), fn(_UU03c4_) { Result0::Ok(Expr::EMatch(e0_, _UU03c4_, bs)) })
          }
        })
      })
    })
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
      }, n, cds))
    })
    Sdecl::SDStruct(fs) => bind(mapM(fn(f) { elab_ty(tys, tps, snd(f)) }, fs), fn(_UU03c4_s) {
      Result0::Ok(Tdef::Mk_tdef(match st {
        Stype::Mk_stype(_, st_name, _, _) => st_name
      }, n, List::Cons(Cdef::Mk_cdef(match st {
        Stype::Mk_stype(_, st_name, _, _) => st_name
      }, _UU03c4_s), List::Nil)))
    })
    Sdecl::SDTupleStruct(ts) => bind(mapM(fn(x1) { elab_ty(tys, tps, x1) }, ts), fn(_UU03c4_s) {
      Result0::Ok(Tdef::Mk_tdef(match st {
        Stype::Mk_stype(_, st_name, _, _) => st_name
      }, n, List::Cons(Cdef::Mk_cdef(match st {
        Stype::Mk_stype(_, st_name, _, _) => st_name
      }, _UU03c4_s), List::Nil)))
    })
  }
}

pub fn elab_sig(tys : List[(Ident, Nat)], f : Sfun) -> Result0[Fdef, Elab_error] {
  bind(mapM(fn(xt) {
    elab_ty(tys, match f {
      Sfun::Mk_sfun(_, _, sf_tparams, _, _, _) => sf_tparams
    }, snd(xt))
  }, match f {
    Sfun::Mk_sfun(_, _, _, sf_params, _, _) => sf_params
  }), fn(_UU03c4_s) {
    bind(match (match f {
      Sfun::Mk_sfun(_, _, _, _, sf_ret, _) => sf_ret
    }) {
      Some(t) => elab_ty(tys, match f {
        Sfun::Mk_sfun(_, _, sf_tparams, _, _, _) => sf_tparams
      }, t)
      None => Result0::Ok(Ty::TBase(Base_ty::BUnit))
    }, fn(_UU03c4_) {
      Result0::Ok(Fdef::Mk_fdef(match f {
        Sfun::Mk_sfun(_, sf_name, _, _, _, _) => sf_name
      }, length(match f {
        Sfun::Mk_sfun(_, _, sf_tparams, _, _, _) => sf_tparams
      }), _UU03c4_s, _UU03c4_, Expr::ELit(Lit::LUnit)))
    })
  })
}

pub fn elab_fun(tys : List[(Ident, Nat)], hdr : Genv, sinfo : List[(Ident, List[Ident])], f : Sfun, sig : Fdef) -> Result0[Fdef, Elab_error] {
  let _UU0393_ = combine(map(fn(xt) { Some(fst(xt)) }, match f {
    Sfun::Mk_sfun(_, _, _, sf_params, _, _) => sf_params
  }), match sig {
    Fdef::Mk_fdef(_, _, fd_params, _, _) => fd_params
  })
  bind(elab(tys, hdr, sinfo, match f {
    Sfun::Mk_sfun(_, _, sf_tparams, _, _, _) => sf_tparams
  }, _UU0393_, Some(match sig {
    Fdef::Mk_fdef(_, _, _, fd_ret, _) => fd_ret
  }), match f {
    Sfun::Mk_sfun(_, _, _, _, _, sf_body) => sf_body
  }), fn(b) {
    Result0::Ok(Fdef::Mk_fdef(match sig {
      Fdef::Mk_fdef(fd_name, _, _, _, _) => fd_name
    }, match sig {
      Fdef::Mk_fdef(_, fd_tparams, _, _, _) => fd_tparams
    }, match sig {
      Fdef::Mk_fdef(_, _, fd_params, _, _) => fd_params
    }, match sig {
      Fdef::Mk_fdef(_, _, _, fd_ret, _) => fd_ret
    }, b))
  })
}

pub fn elab_funs(tys : List[(Ident, Nat)], hdr : Genv, sinfo : List[(Ident, List[Ident])], fs : List[Sfun], sigs : List[Fdef]) -> Result0[List[Fdef], Elab_error] {
  match fs {
    List::Nil => Result0::Ok(List::Nil)
    List::Cons(f, fs_) => match sigs {
      List::Nil => Result0::Ok(List::Nil)
      List::Cons(sig, sigs_) => bind(elab_fun(tys, hdr, sinfo, f, sig), fn(fd) {
        bind(elab_funs(tys, hdr, sinfo, fs_, sigs_), fn(fds) { Result0::Ok(List::Cons(fd, fds)) })
      })
    }
  }
}

pub fn elab_prog(sp : Sprog) -> Result0[(Genv, Expr), Elab_error] {
  let tys = List::Cons((String0::String1(Ascii::Ascii0(true, true, true, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, false, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::EmptyString)))))), Nat::S(Nat::O)), map(fn(st) {
    (match st {
      Stype::Mk_stype(_, st_name, _, _) => st_name
    }, length(match st {
      Stype::Mk_stype(_, _, st_tparams, _) => st_tparams
    }))
  }, match sp {
    Sprog::Mk_sprog(sp_types, _, _) => sp_types
  }))
  let sinfo = flat_map(fn(st) {
    match (match st {
      Stype::Mk_stype(_, _, _, st_body) => st_body
    }) {
      Sdecl::SDEnum(_) => List::Nil
      Sdecl::SDStruct(fs) => List::Cons((match st {
        Stype::Mk_stype(_, st_name, _, _) => st_name
      }, map(fn(x1) { fst(x1) }, fs)), List::Nil)
      Sdecl::SDTupleStruct(_) => List::Nil
    }
  }, match sp {
    Sprog::Mk_sprog(sp_types, _, _) => sp_types
  })
  bind(mapM(fn(x1) { elab_tdef(tys, x1) }, match sp {
    Sprog::Mk_sprog(sp_types, _, _) => sp_types
  }), fn(tds) {
    let types = List::Cons(option_tdef, tds)
    bind(mapM(fn(x1) { elab_sig(tys, x1) }, match sp {
      Sprog::Mk_sprog(_, sp_funs, _) => sp_funs
    }), fn(sigs) {
      let hdr = Genv::Mk_genv(types, sigs)
      bind(elab_funs(tys, hdr, sinfo, match sp {
        Sprog::Mk_sprog(_, sp_funs, _) => sp_funs
      }, sigs), fn(funs) {
        bind(match (match sp {
          Sprog::Mk_sprog(_, _, sp_main) => sp_main
        }) {
          Some(e) => elab(tys, hdr, sinfo, List::Nil, List::Nil, Some(Ty::TBase(Base_ty::BUnit)), Sexpr::SAnnot(sexpr_pos(e), e, Sty::SName(sexpr_pos(e), String0::String1(Ascii::Ascii0(true, false, true, false, true, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))), List::Nil)))
          None => Result0::Ok(Expr::ELit(Lit::LUnit))
        }, fn(main0) { Result0::Ok((Genv::Mk_genv(types, funs), main0)) })
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
