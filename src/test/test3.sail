(* a register containing nat numbers *)
register [|0:256|] dummy_reg
(* and one containing a byte *)
register (bit[8]) dummy_reg2
(* a function to read from memory; wmem serves no purpose currently,
   memory-writing functions are figured out syntactically. *)
val extern (nat,nat) -> unit effect { wmem }  MEMw
val extern nat -> nat effect { rmem } MEMr
val extern (nat,nat) -> unit effect { wmem }  MEM_GPUw
val extern nat -> nat effect { rmem} MEM_GPUr
val extern forall Nat 'n . ( nat, [|'n|], bit['n*8]) -> unit effect { wmem }  MEM_SIZEw
val extern forall Nat 'n . ( nat, [|'n|]) -> bit['n*8] effect { rmem } MEM_SIZEr
val extern (nat,bit[8]) -> unit effect { wmem }  MEM_WORDw
val extern nat -> bit[8] effect { rmem } MEM_WORDr

function nat (deinfix * ) ( (nat) x, (nat) y ) = 42

function nat main _ = {
  (* left-hand side function call = memory write *)
  MEMw(0) := 0;
  ignore(MEMr(0));
  (* register write, idem *)
  dummy_reg := 1;
  (* register read, thanks to register declaration *)
  ignore(dummy_reg);


  MEM_WORDw(0) := 0b10101010;
  (MEM_WORDw(0))[3..4] := 0b10;
  (* XXX this one is broken - I don't what it should do,
  or even if we should accept it, but the current result
  is to eat up one bit, ending up with a 7-bit word. *)
  (*(MEM_WORD(0))[4..3] := 0b10;*) (*We reject this as 4 > 3 not <= *)
  ignore(MEM_WORDr(0));

  (* infix call *)
  ignore(7 * 9);

  (* Some more checks *)
  MEMw(1) := 2;
  ignore(MEMr(1));
  MEM_GPUw(0) := 3;
  ignore(MEM_GPUr(0));
  MEM_SIZEw(0,1) := 0b11110000;
  ignore(MEM_SIZEr(0,1));
  MEM_SIZEw(0,2) := 0b1111000010100000;
  ignore(MEM_SIZEr(0,2));

  (* extern calls *)
  dummy_reg := 3 + 39;
  dummy_reg := (deinfix +)(5, 37);
  (* casts and external calls *)
  dummy_reg := 0b01 + 0b01;
  dummy_reg2 := 0b00000001;
  dummy_reg2 := dummy_reg2 + dummy_reg2; (* cast to nat for add call *)
  dummy_reg2;                            (* cast again and return 4 *)
}
