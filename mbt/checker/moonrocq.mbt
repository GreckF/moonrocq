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

pub fn[A] existsb(f : (A) -> Bool, l : List[A]) -> Bool {
  match l {
    List::Nil => false
    List::Cons(a, l0) => match f(a) {
      true => true
      false => existsb(f, l0)
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

pub fn sub(m : Z, n : Z) -> Z {
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

pub fn leb(x : Z, y : Z) -> Bool {
  match compare0(x, y) {
    @rocqrt.Comparison::Gt => false
    _ => true
  }
}

pub fn ltb(x : Z, y : Z) -> Bool {
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
        match ltb(r_, b) {
          true => (mul0(Z::Zpos(Positive::XO(Positive::XH)), q), r_)
          false => (add0(mul0(Z::Zpos(Positive::XO(Positive::XH)), q), Z::Zpos(Positive::XH)), sub(r_, b))
        }
      }
    }
    Positive::XO(a_) => match pos_div_eucl(a_, b) {
      (q, r) => {
        let r_ = mul0(Z::Zpos(Positive::XO(Positive::XH)), r)
        match ltb(r_, b) {
          true => (mul0(Z::Zpos(Positive::XO(Positive::XH)), q), r_)
          false => (add0(mul0(Z::Zpos(Positive::XO(Positive::XH)), q), Z::Zpos(Positive::XH)), sub(r_, b))
        }
      }
    }
    Positive::XH => match leb(Z::Zpos(Positive::XO(Positive::XH)), b) {
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
          _ => (opp(add0(q, Z::Zpos(Positive::XH))), sub(b, r))
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
}

pub(all) enum Fdef {
  Mk_fdef(Ident, Nat, List[Ty], Ty, Expr)
}

pub type Genv = List[Fdef]

pub fn lookup_fn(ge : Genv, f : Ident) -> Option[Fdef] {
  find(fn(fd) {
    eqDec_ident(match fd {
      Fdef::Mk_fdef(fd_name, _, _, _, _) => fd_name
    })(f)
  }, ge)
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
    Ty::TBase(b) => Ty::TBase(b)
    Ty::TVar(i) => _UU03c3_(i)
    Ty::TTuple(ts) => Ty::TTuple(map(fn(x1) { tsubst(_UU03c3_, x1) }, ts))
    Ty::TArrow(ps, r) => Ty::TArrow(map(fn(x1) { tsubst(_UU03c3_, x1) }, ps), tsubst(_UU03c3_, r))
  }
}

pub fn inst(ts : List[Ty], i : Nat) -> Ty {
  nth(i, ts, Ty::TBase(Base_ty::BUnit))
}

pub type Ctx = List[Ty]

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

pub fn check_names(ge : Genv) -> Result0[Unit, Type_error] {
  match noDup_dec(eqDec_ident, map(fn(f) {
    match f {
      Fdef::Mk_fdef(fd_name, _, _, _, _) => fd_name
    }
  }, ge)) {
    true => Result0::Ok(())
    false => Result0::Err(Type_error::E_DuplicateGlobal)
  }
}

pub fn check_genv(ge : Genv) -> Result0[Unit, Type_error] {
  bind(check_names(ge), fn(_) { bind(check_fdefs(ge, ge), fn(_) { Result0::Ok(()) }) })
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
}

pub(all) enum Sfun {
  Mk_sfun(Pos, Ident, List[Ident], List[(Ident, Sty)], Option[Sty], Sexpr)
}

pub(all) enum Sprog {
  Mk_sprog(List[Sfun], Option[Sexpr])
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
  }
}

pub(all) enum Elab_error {
  EE_Unbound(Pos, Ident)
  EE_UnknownType(Pos, Ident)
  EE_TypeArgs(Pos, Ident)
  EE_CannotInfer(Pos, Ident)
  EE_LambdaParam(Pos, Ident)
  EE_IntRange(Pos, Int_kind, Z)
  EE_NoOperator(Pos, Ident, Ty)
  EE_Annot(Pos, Ty, Ty)
  EE_Type(Pos, Type_error)
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

pub let builtin_types : List[(Ident, Ty)] = List::Cons((String0::String1(Ascii::Ascii0(true, false, true, false, true, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))), Ty::TBase(Base_ty::BUnit)), List::Cons((String0::String1(Ascii::Ascii0(false, true, false, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::EmptyString)))), Ty::TBase(Base_ty::BBool)), List::Cons((String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))), Ty::TBase(Base_ty::BInt(Int_kind::I32))), List::Cons((String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, true, true, false, false), String0::String1(Ascii::Ascii0(false, true, true, false, true, true, false, false), String0::EmptyString))))), Ty::TBase(Base_ty::BInt(Int_kind::I16))), List::Cons((String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, true, true, false, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, false, false), String0::EmptyString))))), Ty::TBase(Base_ty::BInt(Int_kind::I64))), List::Cons((String0::String1(Ascii::Ascii0(true, false, true, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))), Ty::TBase(Base_ty::BInt(Int_kind::U32))), List::Cons((String0::String1(Ascii::Ascii0(true, false, true, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, true, true, false, false), String0::String1(Ascii::Ascii0(false, true, true, false, true, true, false, false), String0::EmptyString)))))), Ty::TBase(Base_ty::BInt(Int_kind::U16))), List::Cons((String0::String1(Ascii::Ascii0(true, false, true, false, true, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, false, true, true, false, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, false, false), String0::EmptyString)))))), Ty::TBase(Base_ty::BInt(Int_kind::U64))), List::Cons((String0::String1(Ascii::Ascii0(false, true, false, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString)))), Ty::TBase(Base_ty::BInt(Int_kind::IByte))), List::Cons((String0::String1(Ascii::Ascii0(false, true, false, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))))), Ty::TBase(Base_ty::BInt(Int_kind::IBigInt))), List::Cons((String0::String1(Ascii::Ascii0(true, true, false, false, false, false, true, false), String0::String1(Ascii::Ascii0(false, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::EmptyString)))), Ty::TBase(Base_ty::BChar)), List::Cons((String0::String1(Ascii::Ascii0(false, false, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, true, false, false, true, true, false), String0::EmptyString)))))), Ty::TBase(Base_ty::BDouble)), List::Cons((String0::String1(Ascii::Ascii0(false, true, true, false, false, false, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, false, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString))))), Ty::TBase(Base_ty::BFloat)), List::Cons((String0::String1(Ascii::Ascii0(true, true, false, false, true, false, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::String1(Ascii::Ascii0(false, true, false, false, true, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, true, true, false, false, true, true, false), String0::EmptyString)))))), Ty::TBase(Base_ty::BString)), List::Nil))))))))))))))

pub fn elab_ty(tps : List[Ident], t : Sty) -> Result0[Ty, Elab_error] {
  match t {
    Sty::SName(p, n, args) => match args {
      List::Nil => match index_of(n, tps) {
        Some(i) => Result0::Ok(Ty::TVar(i))
        None => match assoc(n, builtin_types) {
          Some(_UU03c4_) => Result0::Ok(_UU03c4_)
          None => Result0::Err(Elab_error::EE_UnknownType(p, n))
        }
      }
      List::Cons(_, _) => Result0::Err(Elab_error::EE_TypeArgs(p, n))
    }
    Sty::STuple(_, ts) => bind(mapM(fn(x1) { elab_ty(tps, x1) }, ts), fn(_UU03c4_s) { Result0::Ok(Ty::TTuple(_UU03c4_s)) })
    Sty::SArrow(_, ps, r) => bind(mapM(fn(x1) { elab_ty(tps, x1) }, ps), fn(_UU03c4_s) {
      bind(elab_ty(tps, r), fn(_UU03c4_) { Result0::Ok(Ty::TArrow(_UU03c4_s, _UU03c4_)) })
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
  }
}

pub fn int_in_range(k : Int_kind, z : Z) -> Bool {
  eqb2(wrap(k, z), z)
}

pub fn elab_lit(p : Pos, exp : Option[Ty], l : Slit) -> Result0[Expr, Elab_error] {
  let int = fn(k) {
    fn(z) {
      match int_in_range(k, z) {
        true => Result0::Ok(Expr::ELit(Lit::LInt(k, z)))
        false => Result0::Err(Elab_error::EE_IntRange(p, k, z))
      }
    }
  }
  match l {
    Slit::SLUnit => Result0::Ok(Expr::ELit(Lit::LUnit))
    Slit::SLBool(b) => Result0::Ok(Expr::ELit(Lit::LBool(b)))
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
    Slit::SLChar(c) => Result0::Ok(Expr::ELit(Lit::LChar(c)))
    Slit::SLDouble(b) => Result0::Ok(Expr::ELit(Lit::LDouble(b)))
    Slit::SLFloat(b) => Result0::Ok(Expr::ELit(Lit::LFloat(b)))
    Slit::SLString(s) => Result0::Ok(Expr::ELit(Lit::LString(s)))
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

pub fn param_tys(tps : List[Ident], p : Pos, ps : List[(Ident, Option[Sty])], exps : List[Option[Ty]]) -> Result0[List[Ty], Elab_error] {
  match ps {
    List::Nil => Result0::Ok(List::Nil)
    List::Cons(p0, ps_) => match p0 {
      (x, ann) => match exps {
        List::Nil => {
          let ex = None
          let exps_ = List::Nil
          bind(match ann {
            Some(t) => elab_ty(tps, t)
            None => match ex {
              Some(_UU03c4_) => Result0::Ok(_UU03c4_)
              None => Result0::Err(Elab_error::EE_LambdaParam(p, x))
            }
          }, fn(_UU03c4_) {
            bind(param_tys(tps, p, ps_, exps_), fn(_UU03c4_s) { Result0::Ok(List::Cons(_UU03c4_, _UU03c4_s)) })
          })
        }
        List::Cons(y, ys) => bind(match ann {
          Some(t) => elab_ty(tps, t)
          None => match y {
            Some(_UU03c4_) => Result0::Ok(_UU03c4_)
            None => Result0::Err(Elab_error::EE_LambdaParam(p, x))
          }
        }, fn(_UU03c4_) {
          bind(param_tys(tps, p, ps_, ys), fn(_UU03c4_s) { Result0::Ok(List::Cons(_UU03c4_, _UU03c4_s)) })
        })
      }
    }
  }
}

pub fn elab_lam(hdr : Genv, tps : List[Ident], _UU0393_ : Lctx, p : Pos, ps : List[(Ident, Option[Sty])], ret : Option[Sty], pexps : List[Option[Ty]], rexp : Option[Ty], elab_body : (Lctx) -> (Option[Ty]) -> Result0[Expr, Elab_error]) -> Result0[Expr, Elab_error] {
  bind(param_tys(tps, p, ps, pexps), fn(_UU03c4_s) {
    let _UU0393__ = app(combine(map(fn(x) { Some(fst(x)) }, ps), _UU03c4_s), _UU0393_)
    bind(match ret {
      Some(t) => map_result(fn(x) { Some(x) }, elab_ty(tps, t))
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

pub fn elab(hdr : Genv, tps : List[Ident], _UU0393_ : Lctx, exp : Option[Ty], e : Sexpr) -> Result0[Expr, Elab_error] {
  let elab_args = {
    letrec elab_args = fn(es) {
      fn(exps) {
        match es {
          List::Nil => Result0::Ok(List::Nil)
          List::Cons(e0, es_) => match exps {
            List::Nil => {
              let x = None
              let exps_ = List::Nil
              bind(elab(hdr, tps, _UU0393_, x, e0), fn(e_) {
                bind(elab_args(es_)(exps_), fn(es2) { Result0::Ok(List::Cons(e_, es2)) })
              })
            }
            List::Cons(x, xs) => bind(elab(hdr, tps, _UU0393_, x, e0), fn(e_) {
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
                      Some(_) => bind(elab(hdr, tps, _UU0393_, ex, e0), fn(e_) {
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
                    false => bind(elab(hdr, tps, _UU0393_, ex, e0), fn(e_) {
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
                      Some(_) => bind(elab(hdr, tps, _UU0393_, ex, e0), fn(e_) {
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
                    false => bind(elab(hdr, tps, _UU0393_, ex, e0), fn(e_) {
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
                                  elab_lam(hdr, tps, _UU0393_, q, lps, ret, pexps, resolve(s, pr), fn(_UU0393__) { fn(t0) { elab(hdr, tps, _UU0393__, t0, body) } })
                                }
                                _ => elab(hdr, tps, _UU0393_, match pt {
                                  Some(t0) => resolve(s, t0)
                                  None => None
                                }, e0)
                              }
                              None => elab(hdr, tps, _UU0393_, match pt {
                                Some(t) => resolve(s, t)
                                None => None
                              }, e0)
                            }
                            _ => elab(hdr, tps, _UU0393_, match pt {
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
                                  elab_lam(hdr, tps, _UU0393_, q, lps, ret, pexps, resolve(s, pr), fn(_UU0393__) { fn(t1) { elab(hdr, tps, _UU0393__, t1, body) } })
                                }
                                _ => elab(hdr, tps, _UU0393_, match pt {
                                  Some(t1) => resolve(s, t1)
                                  None => None
                                }, e0)
                              }
                              None => elab(hdr, tps, _UU0393_, match pt {
                                Some(t0) => resolve(s, t0)
                                None => None
                              }, e0)
                            }
                            _ => elab(hdr, tps, _UU0393_, match pt {
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
                                elab_lam(hdr, tps, _UU0393_, q, lps, ret, pexps, resolve(s, pr), fn(_UU0393__) { fn(t0) { elab(hdr, tps, _UU0393__, t0, body) } })
                              }
                              _ => elab(hdr, tps, _UU0393_, match pt {
                                Some(t0) => resolve(s, t0)
                                None => None
                              }, e0)
                            }
                            None => elab(hdr, tps, _UU0393_, match pt {
                              Some(t) => resolve(s, t)
                              None => None
                            }, e0)
                          }
                          _ => elab(hdr, tps, _UU0393_, match pt {
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
                                elab_lam(hdr, tps, _UU0393_, q, lps, ret, pexps, resolve(s, pr), fn(_UU0393__) { fn(t1) { elab(hdr, tps, _UU0393__, t1, body) } })
                              }
                              _ => elab(hdr, tps, _UU0393_, match pt {
                                Some(t1) => resolve(s, t1)
                                None => None
                              }, e0)
                            }
                            None => elab(hdr, tps, _UU0393_, match pt {
                              Some(t0) => resolve(s, t0)
                              None => None
                            }, e0)
                          }
                          _ => elab(hdr, tps, _UU0393_, match pt {
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
  match e {
    Sexpr::SVar(p, x) => match lookup_local(x, _UU0393_) {
      Some(i) => Result0::Ok(Expr::EVar(i))
      None => match lookup_fn(hdr, x) {
        Some(fd) => elab_global(p, x, fd, exp)
        None => Result0::Err(Elab_error::EE_Unbound(p, x))
      }
    }
    Sexpr::SLit(p, l) => elab_lit(p, exp, l)
    Sexpr::SApp(p, f, args) => match f {
      Sexpr::SVar(q, g) => match lookup_local(g, _UU0393_) {
        Some(_) => bind(elab(hdr, tps, _UU0393_, None, f), fn(f_) {
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
                  List::Nil => bind(elab(hdr, tps, _UU0393_, None, a), fn(a_) { Result0::Ok(Expr::ELet(a_, Expr::ELit(Lit::LUnit))) })
                  List::Cons(_, _) => Result0::Err(Elab_error::EE_Unbound(q, g))
                }
              }
              false => Result0::Err(Elab_error::EE_Unbound(q, g))
            }
          }
        }
      }
      Sexpr::SLit(_, _) => bind(elab(hdr, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::SApp(_, _, _) => bind(elab(hdr, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::SInfix(_, _, _, _) => bind(elab(hdr, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::SUnary(_, _, _) => bind(elab(hdr, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::SLet(_, _, _, _, _) => bind(elab(hdr, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::SIf(_, _, _, _) => bind(elab(hdr, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::STup(_, _) => bind(elab(hdr, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::SProj(_, _, _) => bind(elab(hdr, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::SLam(_, _, _, _) => bind(elab(hdr, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
      Sexpr::SAnnot(_, _, _) => bind(elab(hdr, tps, _UU0393_, None, f), fn(f_) {
        bind(type_of(hdr, p, _UU0393_, f_), fn(_UU03c4_f) {
          bind(elab_args(args)(arrow_params(_UU03c4_f, length(args))), fn(args_) { Result0::Ok(Expr::EApp(f_, args_)) })
        })
      })
    }
    Sexpr::SInfix(p, op, a, b) => match eqDec_ident(op)(String0::String1(Ascii::Ascii0(false, true, true, false, false, true, false, false), String0::String1(Ascii::Ascii0(false, true, true, false, false, true, false, false), String0::EmptyString))) {
      true => bind(elab(hdr, tps, _UU0393_, Some(Ty::TBase(Base_ty::BBool)), a), fn(a_) {
        bind(elab(hdr, tps, _UU0393_, Some(Ty::TBase(Base_ty::BBool)), b), fn(b_) { Result0::Ok(Expr::EIf(a_, b_, e_false)) })
      })
      false => match eqDec_ident(op)(String0::String1(Ascii::Ascii0(false, false, true, true, true, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, true, true, true, true, false), String0::EmptyString))) {
        true => bind(elab(hdr, tps, _UU0393_, Some(Ty::TBase(Base_ty::BBool)), a), fn(a_) {
          bind(elab(hdr, tps, _UU0393_, Some(Ty::TBase(Base_ty::BBool)), b), fn(b_) { Result0::Ok(Expr::EIf(a_, e_true, b_)) })
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
            true => bind(elab(hdr, tps, _UU0393_, exp_, b), fn(b_) {
              bind(type_of(hdr, p, _UU0393_, b_), fn(_UU03c4_) {
                bind(elab(hdr, tps, _UU0393_, Some(_UU03c4_), a), fn(a_) { elab_binop(p, op, _UU03c4_, a_, b_) })
              })
            })
            false => bind(elab(hdr, tps, _UU0393_, exp_, a), fn(a_) {
              bind(type_of(hdr, p, _UU0393_, a_), fn(_UU03c4_) {
                bind(elab(hdr, tps, _UU0393_, Some(_UU03c4_), b), fn(b_) { elab_binop(p, op, _UU03c4_, a_, b_) })
              })
            })
          }
        }
      }
    }
    Sexpr::SUnary(p, op, a) => match eqDec_ident(op)(String0::String1(Ascii::Ascii0(true, false, true, true, false, true, false, false), String0::EmptyString)) {
      true => match a {
        Sexpr::SLit(q, l) => match l {
          Slit::SLInt(k, z) => elab_lit(q, exp, Slit::SLInt(k, opp(z)))
          _ => bind(elab(hdr, tps, _UU0393_, exp, a), fn(a_) {
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
        _ => bind(elab(hdr, tps, _UU0393_, exp, a), fn(a_) {
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
        true => bind(elab(hdr, tps, _UU0393_, Some(Ty::TBase(Base_ty::BBool)), a), fn(a_) {
          Result0::Ok(Expr::EPrim(Prim_op::PBoolNot, List::Cons(a_, List::Nil)))
        })
        false => Result0::Err(Elab_error::EE_NoOperator(p, op, Ty::TBase(Base_ty::BUnit)))
      }
    }
    Sexpr::SLet(p, x, ann, e1, body) => bind(match ann {
      Some(t) => map_result(fn(x0) { Some(x0) }, elab_ty(tps, t))
      None => Result0::Ok(None)
    }, fn(_UU03c4_ann) {
      bind(elab(hdr, tps, _UU0393_, _UU03c4_ann, e1), fn(e1_) {
        bind(type_of(hdr, p, _UU0393_, e1_), fn(_UU03c4_1) {
          bind(match _UU03c4_ann {
            Some(t) => match eqDec_ty(t)(_UU03c4_1) {
              true => Result0::Ok(())
              false => Result0::Err(Elab_error::EE_Annot(p, t, _UU03c4_1))
            }
            None => Result0::Ok(())
          }, fn(_) {
            bind(elab(hdr, tps, List::Cons((x, _UU03c4_1), _UU0393_), exp, body), fn(body_) { Result0::Ok(Expr::ELet(e1_, body_)) })
          })
        })
      })
    })
    Sexpr::SIf(p, c, t, oe) => bind(elab(hdr, tps, _UU0393_, Some(Ty::TBase(Base_ty::BBool)), c), fn(c_) {
      match oe {
        Some(e0) => bind(elab(hdr, tps, _UU0393_, exp, t), fn(t_) {
          bind(match exp {
            Some(_UU03c4_) => Result0::Ok(Some(_UU03c4_))
            None => map_result(fn(x) { Some(x) }, type_of(hdr, p, _UU0393_, t_))
          }, fn(exp_) {
            bind(elab(hdr, tps, _UU0393_, exp_, e0), fn(e0_) { Result0::Ok(Expr::EIf(c_, t_, e0_)) })
          })
        })
        None => bind(elab(hdr, tps, _UU0393_, Some(Ty::TBase(Base_ty::BUnit)), t), fn(t_) { Result0::Ok(Expr::EIf(c_, t_, Expr::ELit(Lit::LUnit))) })
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
          Ty::TArrow(_, _) => repeat(None, length(es))
        }
        None => repeat(None, length(es))
      }
      bind(elab_args(es)(exps), fn(es_) { Result0::Ok(Expr::ETuple(es_)) })
    }
    Sexpr::SProj(_, e0, i) => bind(elab(hdr, tps, _UU0393_, None, e0), fn(e0_) { Result0::Ok(Expr::EProj(e0_, i)) })
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
        }
        None => None
      }
      elab_lam(hdr, tps, _UU0393_, p, ps, ret, pexps, rexp, fn(_UU0393__) { fn(t) { elab(hdr, tps, _UU0393__, t, body) } })
    }
    Sexpr::SAnnot(p, e0, t) => bind(elab_ty(tps, t), fn(_UU03c4_) {
      bind(elab(hdr, tps, _UU0393_, Some(_UU03c4_), e0), fn(e0_) {
        bind(type_of(hdr, p, _UU0393_, e0_), fn(_UU03c4_0) {
          match eqDec_ty(_UU03c4_)(_UU03c4_0) {
            true => Result0::Ok(e0_)
            false => Result0::Err(Elab_error::EE_Annot(p, _UU03c4_, _UU03c4_0))
          }
        })
      })
    })
  }
}

pub fn elab_sig(f : Sfun) -> Result0[Fdef, Elab_error] {
  bind(mapM(fn(xt) {
    elab_ty(match f {
      Sfun::Mk_sfun(_, _, sf_tparams, _, _, _) => sf_tparams
    }, snd(xt))
  }, match f {
    Sfun::Mk_sfun(_, _, _, sf_params, _, _) => sf_params
  }), fn(_UU03c4_s) {
    bind(match (match f {
      Sfun::Mk_sfun(_, _, _, _, sf_ret, _) => sf_ret
    }) {
      Some(t) => elab_ty(match f {
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

pub fn elab_fun(hdr : Genv, f : Sfun, sig : Fdef) -> Result0[Fdef, Elab_error] {
  let _UU0393_ = combine(map(fn(xt) { Some(fst(xt)) }, match f {
    Sfun::Mk_sfun(_, _, _, sf_params, _, _) => sf_params
  }), match sig {
    Fdef::Mk_fdef(_, _, fd_params, _, _) => fd_params
  })
  bind(elab(hdr, match f {
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

pub fn elab_funs(hdr : Genv, fs : List[Sfun], sigs : List[Fdef]) -> Result0[Genv, Elab_error] {
  match fs {
    List::Nil => Result0::Ok(List::Nil)
    List::Cons(f, fs_) => match sigs {
      List::Nil => Result0::Ok(List::Nil)
      List::Cons(sig, sigs_) => bind(elab_fun(hdr, f, sig), fn(fd) {
        bind(elab_funs(hdr, fs_, sigs_), fn(ge) { Result0::Ok(List::Cons(fd, ge)) })
      })
    }
  }
}

pub fn elab_prog(sp : Sprog) -> Result0[(Genv, Expr), Elab_error] {
  bind(mapM(fn(x1) { elab_sig(x1) }, match sp {
    Sprog::Mk_sprog(sp_funs, _) => sp_funs
  }), fn(hdr) {
    bind(elab_funs(hdr, match sp {
      Sprog::Mk_sprog(sp_funs, _) => sp_funs
    }, hdr), fn(ge) {
      bind(match (match sp {
        Sprog::Mk_sprog(_, sp_main) => sp_main
      }) {
        Some(e) => elab(hdr, List::Nil, List::Nil, Some(Ty::TBase(Base_ty::BUnit)), Sexpr::SAnnot(sexpr_pos(e), e, Sty::SName(sexpr_pos(e), String0::String1(Ascii::Ascii0(true, false, true, false, true, false, true, false), String0::String1(Ascii::Ascii0(false, true, true, true, false, true, true, false), String0::String1(Ascii::Ascii0(true, false, false, true, false, true, true, false), String0::String1(Ascii::Ascii0(false, false, true, false, true, true, true, false), String0::EmptyString)))), List::Nil)))
        None => Result0::Ok(Expr::ELit(Lit::LUnit))
      }, fn(main0) { Result0::Ok((ge, main0)) })
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
