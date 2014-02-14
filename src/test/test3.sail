(* a register containing nat numbers *)
register nat dummy_reg
(* a function to read from memory; wmem serves no purpose currently,
   memory-writing functions are figured out syntactically. *)
val  nat -> nat effect { wmem , rmem }  MEM
val  nat -> nat effect { wmem , rmem }  MEM_GPU
val ( nat * nat ) -> nat effect { wmem , rmem }  MEM_SIZE

val  nat -> (bit[8]) effect { wmem , rmem }  MEM_WORD

function unit ignore(x) = ()

(* extern functions *)
val extern ( nat * nat ) -> nat effect pure add = "add"
val extern ( nat * nat ) -> nat effect pure (deinfix + ) = "add_infix"   (* infix plus *)

function nat (deinfix * ) ( (nat) x, (nat) y ) = 42

function nat main _ = {
  (* left-hand side function call = memory write *)
  MEM(0) := 0;
  (* memory read, thanks to effect { rmem} above *)
  ignore(MEM(0));
  (* register write, idem *)
  dummy_reg := 1;
  (* register read, thanks to register declaration *)
  ignore(dummy_reg);


  MEM_WORD(0) := 0b10101010;
  (MEM_WORD(0))[3..4] := 0b10;
  (* XXX this one is broken - I don't what it should do,
  or even if we should accept it, but the current result
  is to eat up one bit, ending up with a 7-bit word. *)
  (MEM_WORD(0))[4..3] := 0b10;
  ignore(MEM_WORD(0));

  (* infix call *)
  ignore(7 * 9);

  (* Some more checks *)
  MEM(1) := 2;
  ignore(MEM(1));
  MEM_GPU(0) := 3;
  ignore(MEM_GPU(0));
  MEM_SIZE(0,1) := 4;
  ignore(MEM_SIZE(0,1));

  (* extern calls *)
  ignore(3 + 39);
  add(5, 37);
}
