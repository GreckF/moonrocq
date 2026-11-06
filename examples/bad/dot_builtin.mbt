trait A {
  f(Self) -> Int
}

impl A for Int with f(self) {
  self + 1
}

fn main {
  ignore((1).f())
}
