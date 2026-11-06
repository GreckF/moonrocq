// Milestone M5: traits, impls (default methods, supertraits, constrained
// impls), bounds, methods, trait objects.
trait Area {
  area(Self) -> Int
  name(Self) -> String = _
}

impl Area with name(_self) {
  "shape"
}

struct Sq {
  s : Int
}

struct Rect {
  w : Int
  h : Int
}

impl Area for Sq with area(self) {
  self.s * self.s
}

impl Area for Sq with name(_self) {
  "sq"
}

impl Area for Rect with area(self) {
  self.w * self.h
}

trait Size {
  size(Self) -> Int
}

impl Size for Int with size(_self) {
  1
}

impl[T : Size] Size for Array[T] with size(self) {
  let mut n = 0
  for x in self {
    n = n + Size::size(x)
  }
  n
}

trait Named : Area {
  label(Self) -> String
}

impl Named for Sq with label(self) {
  self.name() + "!"
}

fn[T : Area] total(xs : Array[T]) -> Int {
  let mut n = 0
  for x in xs {
    n = n + x.area()
  }
  n
}

fn[T : Named] describe(x : T) -> String {
  x.label() + Area::name(x)
}

struct P {
  x : Int
}

fn P::make(x : Int) -> P {
  { x, }
}

fn P::get(self : P) -> Int {
  self.x
}

trait Zero {
  zero() -> Self
}

impl Zero for Int with zero() {
  0
}

fn[T : Zero] mk() -> T {
  T::zero()
}

suberror Neg

trait Check {
  check(Self) -> Int raise Neg
}

impl Check for Int with check(self) {
  if self < 0 {
    raise Neg
  }
  self
}

fn[T : Area] twice(x : T) -> Int {
  x.area() * 2
}

fn main {
  let shapes : Array[&Area] = [Sq::{ s: 2 } as &Area, Rect::{ w: 1, h: 3 }]
  let mut sum = 0
  for s in shapes {
    sum = sum + s.area()
  }
  let a : &Area = Sq::{ s: 9 }
  let p = P::make(3)
  let z : Int = Zero::zero()
  let m : Int = mk()
  let k = Check::check(3) catch { _ => -1 }
  ignore(
    (
      sum,
      Area::area(a),
      total([Sq::{ s: 1 }, Sq::{ s: 2 }]),
      Size::size([[1, 2], [3]]),
      describe(Sq::{ s: 1 }),
      p.get(),
      m + z,
      k,
      twice(a),
      Rect::{ w: 2, h: 2 }.name(),
    ),
  )
}
