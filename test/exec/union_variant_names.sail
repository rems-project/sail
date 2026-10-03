default Order dec

$include <prelude.sail>
$include <string.sail>

// Ensure that unions with variants that match the union name work.
// In the past the generated C code was not compatible with C++ due
// to different rules around anonymous unions.

union n0 = {
    n0 : int,
}

union n1 = {
    n2 : int,
    n1 : int,
}

// newtype is syntactic sugar for a single entry union.
newtype n3 = n3 : int

enum n4 = { n4 }

function main() -> unit = {
  // Prevent dead-code elimination of the types.
  // This is not very robust but it works for now.
  let v0 = n0(1);
  let v1 = n1(2);
  let v3 = n3(3);
  let v4 = n4;
  let x : int = match v1 {
    n2(d) => d + 10,
    n1(d) => d + 20,
  };
  print_endline(dec_str(x));
}
