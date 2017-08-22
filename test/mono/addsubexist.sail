(* Adapted from hand-written ARM model *)

default Order dec
typedef boolean = bit
typedef reg_size   = bit[5]
typedef reg_index = [|31|]

val reg_size -> reg_index effect pure UInt_reg
val unit -> unit effect pure (* probably not pure *) ReservedValue
function forall Nat 'N. bit['N] NOT((bit['N]) x) = ~(x)
val forall Nat 'M, Nat 'N. bit['M] -> bit['N] effect pure ZeroExtend
val forall Nat 'N. (bit['N], bit['N], bit) -> (bit['N],bit[4]) effect pure AddWithCarry
val forall Nat 'N, 'N IN {8,16,32,64}. (*broken? implicit<'N>*)unit -> bit['N] effect {rreg} rSP
val forall Nat 'N, 'N IN {8,16,32,64}. ((*ditto implicit<'N>,*)reg_index) -> bit['N] effect {rreg}rX
val (unit, bit[4]) -> unit effect {wreg} wPSTATE_NZCV
val forall Nat 'N, 'N IN {32,64}. (unit, bit['N]) -> unit effect {rreg,wreg} wSP
val forall Nat 'N, 'N IN {32,64}. (reg_index,bit['N]) -> unit effect {wreg} wX

typedef ast = const union
{
  (exist 'R, 'R in {32,64}. (reg_index,reg_index,[:'R:],boolean,boolean,bit['R])) AddSubImmediate;
}

val ast -> unit effect {rreg,wreg(*,rmem,barr,eamem,wmv,escape*)} execute
scattered function unit execute

val bit[32] -> option<(ast)> effect pure decodeAddSubtractImmediate

(* ADD/ADDS (immediate) *)
(* SUB/SUBS (immediate) *)
function option<(ast)> effect pure decodeAddSubtractImmediate ([sf]:[op]:[S]:0b10001:(bit[2]) shift:(bit[12]) imm12:(reg_size) Rn:(reg_size) Rd) =
{
  (reg_index) d := UInt_reg(Rd);
  (reg_index) n := UInt_reg(Rn);
  let (exist 'R, 'R in {32,64}. [:'R:]) 'datasize = if sf then 64 else 32 in {
  (boolean) sub_op := op;
  (boolean) setflags := S;
  (bit['datasize]) imm := 0; (* ARM: uninitialized *)

  switch shift {
    case 0b00 -> imm := ZeroExtend(imm12)
    case 0b01 -> imm := ZeroExtend(imm12 : (0b0 ^^ 12))
    case [bitone,_] -> ReservedValue()
  };

  Some(AddSubImmediate( (d,n,datasize,sub_op,setflags,imm) ));
}}

function clause execute (AddSubImmediate('datasize)) = {
switch datasize {
case (d,n,datasize,sub_op,setflags,imm) ->
{
  (bit['datasize]) operand1 := if n == 31 then rSP() else rX(n);
  (bit['datasize]) operand2 := imm;
  (bit) carry_in := bitzero; (* ARM: uninitialized *)

  if sub_op then {
    operand2 := NOT(operand2);
    carry_in := bitone;
  }
  else
    carry_in := bitzero;

  let (result,nzcv) = (AddWithCarry(operand1, operand2, carry_in)) in {

    if setflags then
      wPSTATE_NZCV() := nzcv;

    if (d == 31 & ~(setflags)) then
      wSP() := result
    else
      wX(d) := result;
  }
}}}
end execute
