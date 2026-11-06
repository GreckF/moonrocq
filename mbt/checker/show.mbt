// Human-readable rendering of the extracted verdicts (untrusted glue).

///|
fn nat_to_int(n : Nat) -> Int {
  let mut k = 0
  let mut m = n
  while m is S(p) {
    k = k + 1
    m = p
  }
  k
}

///|
fn positive_to_bigint(p : Positive) -> BigInt {
  match p {
    XH => 1N
    XO(q) => positive_to_bigint(q) * 2N
    XI(q) => positive_to_bigint(q) * 2N + 1N
  }
}

///|
fn z_to_bigint(z : Z) -> BigInt {
  match z {
    Z0 => 0N
    Zpos(p) => positive_to_bigint(p)
    Zneg(p) => -positive_to_bigint(p)
  }
}

///|
fn n_to_int(n : N) -> Int {
  match n {
    N0 => 0
    Npos(p) => positive_to_bigint(p).to_int()
  }
}

///|
fn[A] list_to_array(l : List[A]) -> Array[A] {
  let out = []
  let mut c = l
  while c is Cons(x, r) {
    out.push(x)
    c = r
  }
  out
}

///|
fn byte_of_ascii(a : Ascii) -> Int {
  let Ascii0(b0, b1, b2, b3, b4, b5, b6, b7) = a
  let bits = [b0, b1, b2, b3, b4, b5, b6, b7]
  let mut v = 0
  for i = 7; i >= 0; i = i - 1 {
    v = v * 2 + (if bits[i] { 1 } else { 0 })
  }
  v
}

///|
/// Inverse of `ident_of_string` (UTF-8 decoding).
pub fn string_of_ident(s : String0) -> String {
  let bytes = []
  let mut c = s
  while c is String1(a, r) {
    bytes.push(byte_of_ascii(a))
    c = r
  }
  let buf = StringBuilder()
  let mut i = 0
  while i < bytes.length() {
    let b = bytes[i]
    let (cp, len) = if b < 0x80 {
      (b, 1)
    } else if b < 0xE0 && i + 1 < bytes.length() {
      (((b & 0x1F) << 6) | (bytes[i + 1] & 0x3F), 2)
    } else if b < 0xF0 && i + 2 < bytes.length() {
      (((b & 0x0F) << 12) | ((bytes[i + 1] & 0x3F) << 6) | (bytes[i + 2] & 0x3F), 3)
    } else if i + 3 < bytes.length() {
      (
        ((b & 0x07) << 18) |
        ((bytes[i + 1] & 0x3F) << 12) |
        ((bytes[i + 2] & 0x3F) << 6) |
        (bytes[i + 3] & 0x3F),
        4,
      )
    } else {
      (0xFFFD, 1)
    }
    buf.write_char(Int::unsafe_to_char(cp))
    i = i + len
  }
  buf.to_string()
}

///|
pub fn show_pos(p : Pos) -> String {
  let Mk_pos(l, c) = p
  "\{n_to_int(l)}:\{n_to_int(c)}"
}

///|
fn show_int_kind(k : Int_kind) -> String {
  match k {
    I16 => "Int16"
    I32 => "Int"
    I64 => "Int64"
    U16 => "UInt16"
    U32 => "UInt"
    U64 => "UInt64"
    IByte => "Byte"
    IBigInt => "BigInt"
  }
}

///|
/// Type variables are shown by position, `T0`, `T1`, ...  (Core has no names).
pub fn show_ty(t : Ty) -> String {
  match t {
    TBase(b) =>
      match b {
        BUnit => "Unit"
        BBool => "Bool"
        BInt(k) => show_int_kind(k)
        BChar => "Char"
        BDouble => "Double"
        BFloat => "Float"
        BString => "String"
      }
    TVar(i) => "T\{nat_to_int(i)}"
    TTuple(ts) => "(" + show_tys(ts) + ")"
    TArrow(ps, r) => "(" + show_tys(ps) + ") -> " + show_ty(r)
    TData(n, ts) =>
      if ts is Nil {
        string_of_ident(n)
      } else {
        string_of_ident(n) + "[" + show_tys(ts) + "]"
      }
  }
}

///|
fn show_tys(ts : List[Ty]) -> String {
  list_to_array(ts).map(show_ty).join(", ")
}

///|
pub fn show_type_error(e : Type_error) -> String {
  match e {
    E_UnboundVar(x) => "unbound variable #\{nat_to_int(x)}"
    E_UnknownGlobal(f) => "unknown function `\{string_of_ident(f)}`"
    E_TypeArgArity(f, n, m) =>
      "`\{string_of_ident(f)}` expects \{nat_to_int(n)} type argument(s), got \{nat_to_int(m)}"
    E_Mismatch(a, b) => "type mismatch: expected \{show_ty(a)}, found \{show_ty(b)}"
    E_NotFunction(t) => "not a function: \{show_ty(t)}"
    E_ArgArity(n, m) => "expected \{nat_to_int(n)} argument(s), got \{nat_to_int(m)}"
    E_NotTuple(t) => "not a tuple: \{show_ty(t)}"
    E_TupleIndex(i, t) => "tuple \{show_ty(t)} has no field \{nat_to_int(i)}"
    E_DuplicateGlobal => "duplicate top-level definition"
    E_InGlobal(f, e) => "in `\{string_of_ident(f)}`: " + show_type_error(e)
    E_UnknownType(t) => "unknown type `\{string_of_ident(t)}`"
    E_UnknownCtor(t, c) =>
      "type `\{string_of_ident(t)}` has no constructor `\{string_of_ident(c)}`"
    E_NotData(t) => "not a data type: \{show_ty(t)}"
    E_PatArity(n, m) => "pattern expects \{nat_to_int(n)} field(s), got \{nat_to_int(m)}"
    E_DuplicateType => "duplicate type definition"
    E_DuplicateCtor => "duplicate constructor"
    E_IllFormed(t) => "ill-formed type \{show_ty(t)}"
    E_InType(t, e) => "in type `\{string_of_ident(t)}`: " + show_type_error(e)
  }
}

///|
pub fn show_elab_error(e : Elab_error) -> String {
  match e {
    EE_Unbound(p, x) => "\{show_pos(p)}: unbound identifier `\{string_of_ident(x)}`"
    EE_UnknownType(p, n) => "\{show_pos(p)}: unknown type `\{string_of_ident(n)}`"
    EE_TypeArgs(p, n, k, m) =>
      "\{show_pos(p)}: type `\{string_of_ident(n)}` expects \{nat_to_int(k)} type argument(s), got \{nat_to_int(m)}"
    EE_CannotInfer(p, f) =>
      "\{show_pos(p)}: cannot infer the type arguments of `\{string_of_ident(f)}`"
    EE_LambdaParam(p, x) =>
      "\{show_pos(p)}: cannot infer the type of parameter `\{string_of_ident(x)}`; add an annotation"
    EE_IntRange(p, k, z) =>
      "\{show_pos(p)}: literal \{z_to_bigint(z)} is out of range for \{show_int_kind(k)}"
    EE_NoOperator(p, op, t) =>
      "\{show_pos(p)}: operator `\{string_of_ident(op)}` is not defined on \{show_ty(t)}"
    EE_Annot(p, a, b) =>
      "\{show_pos(p)}: type mismatch: expected \{show_ty(a)}, found \{show_ty(b)}"
    EE_Type(p, e) => "\{show_pos(p)}: " + show_type_error(e)
    EE_UnknownCtor(p, c) => "\{show_pos(p)}: unknown constructor `\{string_of_ident(c)}`"
    EE_AmbiguousCtor(p, c) =>
      "\{show_pos(p)}: constructor `\{string_of_ident(c)}` is ambiguous; write `T::\{string_of_ident(c)}`"
    EE_CtorArity(p, c, n, m) =>
      "\{show_pos(p)}: constructor `\{string_of_ident(c)}` expects \{nat_to_int(n)} argument(s), got \{nat_to_int(m)}"
    EE_NotRecord(p, t) => "\{show_pos(p)}: not a struct with named fields: \{show_ty(t)}"
    EE_UnknownField(p, f) => "\{show_pos(p)}: unknown field `\{string_of_ident(f)}`"
    EE_MissingField(p, f) => "\{show_pos(p)}: missing field `\{string_of_ident(f)}`"
    EE_PatType(p, t) => "\{show_pos(p)}: pattern does not match type \{show_ty(t)}"
    EE_EmptyMatch(p) => "\{show_pos(p)}: cannot infer the type of an empty match"
  }
}

///|
fn show_fdef(fd : Fdef) -> String {
  let Mk_fdef(name, n, ps, r, _) = fd
  let k = nat_to_int(n)
  let tps = if k == 0 {
    ""
  } else {
    "[" + Array::makei(k, i => "T\{i}").join(", ") + "]"
  }
  "fn\{tps} \{string_of_ident(name)}(\{show_tys(ps)}) -> \{show_ty(r)}"
}

///|
fn show_tdef(td : Tdef) -> String {
  let Mk_tdef(name, n, cds) = td
  let k = nat_to_int(n)
  let tps = if k == 0 {
    ""
  } else {
    "[" + Array::makei(k, i => "T\{i}").join(", ") + "]"
  }
  let ctors = list_to_array(cds).map(cd => {
    let Mk_cdef(c, fs) = cd
    if fs is Nil {
      string_of_ident(c)
    } else {
      string_of_ident(c) + "(" + show_tys(fs) + ")"
    }
  })
  "type \{string_of_ident(name)}\{tps} = " + ctors.join(" | ")
}

///|
/// Outcome of `check_source`, as (accepted?, message lines).
pub fn render_outcome(o : Outcome) -> (Bool, Array[String]) {
  match o {
    O_Parse(reports) =>
      (false, reports.map(r => show_pos(pos_of_loc(r.loc)) + ": parse error: " + r.msg))
    O_Unsupported(LowerUnsupported(what, p)) =>
      (false, ["\{show_pos(p)}: unsupported: \{what}"])
    O_Elab(e) => (false, [show_elab_error(e)])
    O_Type(e) => (false, ["type error: " + show_type_error(e)])
    O_Ok(Mk_genv(tds, fds), _, t) => {
      let lines = []
      for td in list_to_array(tds) {
        let Mk_tdef(name, _, _) = td
        if string_of_ident(name) != "Option" {
          lines.push(show_tdef(td))
        }
      }
      lines.append(list_to_array(fds).map(show_fdef))
      lines.push("main : " + show_ty(t))
      (true, lines)
    }
  }
}
