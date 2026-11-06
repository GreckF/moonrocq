fn[T] id(x : T) -> T {
  x
}

fn fact(n : Int) -> Int {
  if n <= 1 {
    1
  } else {
    n * fact(n - 1)
  }
}

fn[A, B] swap(p : (A, B)) -> (B, A) {
  (p.1, p.0)
}

fn[A, B, C] compose(f : (B) -> C, g : (A) -> B) -> (A) -> C {
  fn(x) { f(g(x)) }
}

fn is_even(n : Int) -> Bool {
  if n == 0 { true } else { is_odd(n - 1) }
}

fn is_odd(n : Int) -> Bool {
  if n == 0 { false } else { is_even(n - 1) }
}

fn greet(name : String) -> String {
  "Hello, " + name + "!"
}

fn main {
  let n = fact(id(5))
  let big : Int64 = 1 + 9223372036854775806
  let p = swap((n, "five"))
  let inc = compose(fn(x) { x + 1 }, (y : Int) => y * 2)
  let _ = inc(p.1)
  ignore(big)
  ignore(greet(p.0))
  ignore(is_even(10) && !is_odd(3))
}
