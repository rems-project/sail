import Out.Sail.Sail
import Out.Sail.BitVec

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

def decode (merge_var : (BitVec 32)) : Bool :=
  match_bv merge_var with
  | [11,111,0,00,opc:2,1,Rm:5,option_v:3,S,10,Rn:5,Rt:5] =>
    if (Eq Rm Rn)
    then true
    else false
  | [sf,10,01010,shift:2,N,Rm:5,imm6:6,Rn:5,Rd:5] =>
    if (Eq Rn Rd)
    then true
    else false
  | [1101010100,0,00,011,0011,CRm:4,1,01,11111] => true
  | [1,011010,0,imm19:19,Rt:5] => false
  | _ => true

def initialize_registers (_ : Unit) : Unit :=
  ()

