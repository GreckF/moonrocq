enum Shape {
  Circle(Int)
  Rect(Int, Int)
}

fn main {
  let s = Rect(1)
  ignore(s)
}
