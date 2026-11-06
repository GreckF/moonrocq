struct Counter {
  mut count : Int
}

fn main {
  let c : Counter = { count: 0 }
  ignore(c)
}
