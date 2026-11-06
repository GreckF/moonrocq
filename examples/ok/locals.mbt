// Local inference: expected types flow into literals, lambdas and branches.
fn[A, B] apply(f : (A) -> B, x : A) -> B {
  f(x)
}

fn[T] twice(f : (T) -> T) -> (T) -> T {
  fn(x) { f(f(x)) }
}

fn clamp(lo : Int64, x : Int64, hi : Int64) -> Int64 {
  if x < lo { lo } else if x > hi { hi } else { x }
}

fn main {
  let a : Int64 = 10
  let b = clamp(0, a * 3, 20)
  let c = apply(fn(n) { n - 1L }, b)
  let d = twice((s : String) => s + s)("ab")
  let e : UInt = 4000000000
  let big : BigInt = 123456789012345678901234567890
  let ch = 'λ'
  let t = (c, d, e, big, ch == 'λ')
  ignore(t.4 || false)
}
