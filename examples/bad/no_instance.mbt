trait A {
  f(Self) -> Int
}

fn[T : A] use_a(x : T) -> Int {
  x.f()
}

fn main {
  ignore(use_a("no"))
}
