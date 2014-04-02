(* a register containing nat numbers *)
register [|0:256|] dummy_reg
(* and one containing a byte *)
register (bit[8]) dummy_reg2
(* a function to read from memory; wmem serves no purpose currently,
   memory-writing functions are figured out syntactically. *)
val extern nat -> nat effect { wmem , rmem }  MEM
val extern nat -> nat effect { wmem , rmem }  MEM_GPU
val extern forall Nat 'n . ( nat, [|'n|] ) -> (bit['n * 8]) effect { wmem , rmem }  MEM_SIZE
val extern nat -> (bit[8]) effect { wmem , rmem }  MEM_WORD

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
  MEM_SIZE(0,1) := 0b11110000;
  ignore(MEM_SIZE(0,1));
  MEM_SIZE(0,2) := 0b1111000010100000;
  ignore(MEM_SIZE(0,2));

  (* extern calls *)
  dummy_reg := 3 + 39;
  dummy_reg := (deinfix +)(5, 37);
  (* casts and external calls *)
  dummy_reg := 0b01 + 0b01;
  dummy_reg2 := dummy_reg;               (* cast from [|256|] to bit[8] *)
  dummy_reg2 := dummy_reg2 + dummy_reg2; (* cast to nat for add call *)
  dummy_reg2;                            (* cast again and return 4 *)
}
