/* This example is more testing the typechecker flow typing rather
than the ocaml backend, but it does test that recursive functions work
correctly */

val get_size : unit -> {|32, 64|}

function get_size () = 32

val only64 = { ocaml: "(fun _ -> ())" } : bits(64) -> unit

val zeros : forall 'n. atom('n) -> vector('n, dec, bit)

function zeros n =
  if (n == 1 + 0) then 0b0 else 0b0 @ zeros('n - 1)

val main : unit -> unit

function main () = {
  let 'len = get_size ();
  let xs = zeros(len);
  if (len == 32) then {
    ()
  } else {
    only64(xs)
  };
  print_bits("xs = ", xs);
  print_bits("zeros(64) = ", zeros(64))
}