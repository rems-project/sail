(* a register containing nat numbers *)
register nat reg
(* a function to read from memory; wmem serves no purpose currently,
   memory-writing functions are figured out syntactically. *)
val ( nat -> nat effect { wmem , rmem } ) MEM

function nat main _ = {
  (* memory read, thanks to effect { rmem} above *)
  MEM(0);
  (* left-hand side function call = memory write *)
  MEM(0) := 1;
  (* register read, thanks to register declaration *)
  reg;
  (* register write, idem *)
  reg := 1;
}
