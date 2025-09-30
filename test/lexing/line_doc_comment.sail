default Order dec

$include <prelude.sail>

/// Line documentation comment
///
/// Another paragraph
val main : unit -> unit

union foo = {
  ///
  /// A second line comment
  ///
  /// With multiple lines
  Ctor : unit
}

struct bar = {
  /// Comment
  baz : unit
}

bitfield quux : bits(32) = {
  /// Another doc comment
  $[attr]
  /// Second doc comment!
  some_field : 31 .. 16
}

function main() = {
  print_endline("Doc comment test")
}
