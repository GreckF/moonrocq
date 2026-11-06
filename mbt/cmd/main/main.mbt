// moonrocq: certified type checker for a fragment of MoonBit.
//
//   moonrocq FILE.mbt...
//
// Exit status 0 iff every file is accepted.

///|
fn main {
  let args = @env.args()
  if args.length() < 2 {
    println("usage: moonrocq FILE.mbt...")
    @sys.exit(2)
  }
  let mut ok = true
  for i in 1..<args.length() {
    let path = args[i]
    let src = @fs.read_file_to_string(path) catch {
      e => {
        println("\{path}: cannot read: \{e}")
        ok = false
        continue
      }
    }
    let (accepted, lines) = @checker.render_outcome(@checker.check_source(src))
    if accepted {
      println("\{path}: OK")
      for l in lines {
        println("  " + l)
      }
    } else {
      ok = false
      for l in lines {
        println("\{path}:" + l)
      }
    }
  }
  if !ok {
    @sys.exit(1)
  }
}
