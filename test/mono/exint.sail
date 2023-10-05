default Order dec
$include <prelude.sail>

val cast ex_int : int -> {'n, true. int('n)}
function ex_int 'n = n


/* Decode -> int -> existential test */

val needssize : forall 'n, 'n >= 0. int('n) -> unit

function needssize(n) = {
  let x : bits('n) = replicate_bits(0b0,n) in
  ()
}

val test : bits(2) -> unit

function test(x) = {
  n : int = undefined;
  match x {
    0b00 => n = 1,
    0b01 => n = 2,
    0b10 => n = 4,
    0b11 => n = 8
  };
  let 'n2 = ex_int(n) in {
    assert(constraint('n2 >= 0));
    needssize(n2)
  }
}

val run : unit -> unit

function run () = {
  test(0b00);
  test(0b01);
  test(0b10);
  test(0b11);
}
