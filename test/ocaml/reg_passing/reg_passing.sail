
register R1 : int
register R2 : int
register R3 : int

val cast "reg_deref" : forall ('a : Type). register('a) -> 'a effect {rreg}
val output = {
    ocaml: "(fun (str, n) -> print_endline (str ^ string_of_big_int n))"
  } : (string, int) -> unit

val f : register(int) -> unit effect {rreg, wreg}

function f R = {
  R1 = R;
}

val g : unit -> unit effect {rreg, wreg}

function g () = {
  f(R1);
  f(R2);
}

val main : unit -> unit effect {rreg, wreg}

function main () = {
  R1 = 4;
  R2 = 5;
  g ();
  R3 = 10;
  f(R3);
  R2 = 20;
  output("R1 = ", R1);
  output("R2 = ", R2);
  output("R3 = ", R3)
}