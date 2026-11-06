default Order dec

$include <prelude.sail>

$option --unroll-loops

$[enum_vector E_members]
scattered enum E

enum clause E = A

enum clause E = B

end E

val main : unit -> unit

function main() = {
  let xs : vector(2, E) = E_members;
  foreach (i from 0 to 1) {
    match xs[i] {
      A => print_endline("A"),
      B => print_endline("B"),
    }
  }
}
