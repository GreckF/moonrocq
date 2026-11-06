trait C {
  cmp(Self, Self) -> Bool
}

impl C for Int with cmp(self, o) {
  self == o
}

fn main {
  let c = 1 as &C
  ignore(c)
}
