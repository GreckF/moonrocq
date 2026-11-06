// The temporary elaborator needs the expected type of a labelled block
// (or of an infinite `for` loop) whose `break` carries a value.
fn main {
  let x = l~: {
    if true {
      break l~ 5
    }
    6
  }
  ignore(x)
}
