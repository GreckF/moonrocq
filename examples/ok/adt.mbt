// Milestone M2: data types and pattern matching.
enum Shape {
  Circle(Int)
  Rect(Int, Int)
  Empty
}

fn area(s : Shape) -> Int {
  match s {
    Circle(r) => 3 * r * r
    Rect(w, h) => w * h
    Empty => 0
  }
}

enum MyList[T] {
  Nil
  Cons(T, MyList[T])
}

fn[T] length(l : MyList[T]) -> Int {
  match l {
    Nil => 0
    Cons(_, rest) => 1 + length(rest)
  }
}

fn[A, B] map_list(f : (A) -> B, l : MyList[A]) -> MyList[B] {
  match l {
    Nil => Nil
    Cons(x, rest) => Cons(f(x), map_list(f, rest))
  }
}

struct Point {
  x : Int
  y : Int
}

struct Wrapper(Int, String)

fn abs(n : Int) -> Int {
  if n < 0 { -n } else { n }
}

fn norm1(p : Point) -> Int {
  let { x, y } = p
  abs(x) + abs(y)
}

fn first_or(o : Int?, d : Int) -> Int {
  match o {
    Some(v) => v
    None => d
  }
}

fn describe(n : Int, flag : Bool) -> String {
  match (n, flag) {
    (0, _) => "none"
    (_, true) => "some"
    _ => "?"
  }
}

fn main {
  let shapes = Cons(Circle(2), Cons(Rect(3, 4), Cons(Empty, Nil)))
  let areas = map_list(area, shapes)
  let n = length(areas)
  let p : Point = { x: 3, y: -4 }
  let q = Point::{ y: p.x, x: p.y }
  let w = Wrapper(norm1(q), "w")
  let (a, b) = (w.0, w.1)
  ignore(first_or(Some(n + a), 0))
  ignore(b + describe(n, true))
}
