trait S {
  s(Self) -> Int
}

impl S for Int with s(_self) {
  1
}

impl S for Int with s(_self) {
  2
}
