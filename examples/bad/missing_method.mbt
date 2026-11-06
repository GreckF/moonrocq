trait A {
  f(Self) -> Int
  g(Self) -> Int
}

impl A for Int with f(self) {
  self
}
