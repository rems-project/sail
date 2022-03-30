
register R1 : int
register R2 : int
register R3 : int

val __deref = monadic "reg_deref" : forall ('a : Type). register('a) -> 'a effect {rreg}

val output = {
    ocaml: "(fun (str, n) -> print_endline (str ^ Big_int.to_string n))",
    interpreter: "print_int"
  } : (string, int) -> unit

val f : register(int) -> unit effect {rreg, wreg}

function f R = {
  R1 = *R;
}

val g : unit -> unit effect {rreg, wreg}

function g () = {
  f(ref R1);
  f(ref R2);
}

val main : unit -> unit effect {rreg, wreg}

function main () = {
  R1 = 4;
  R2 = 5;
  g ();
  R3 = 10;
  f(ref R3);
  R2 = 20;
  output("R1 = ", R1);
  output("R2 = ", R2);
  output("R3 = ", R3)
}