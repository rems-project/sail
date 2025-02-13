import Out.Sail.Sail
import Out.Sail.BitVec

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

def decode (v__0 : (BitVec 32)) : Bool :=
  if (Bool.and (Eq (Sail.BitVec.extractLsb v__0 31 24) (0xF8 : (BitVec 8)))
       (Bool.and (Eq (Sail.BitVec.extractLsb v__0 21 21) (0b1 : (BitVec 1)))
         (Eq (Sail.BitVec.extractLsb v__0 11 10) (0b10 : (BitVec 2)))))
  then let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
       let Rm : (BitVec 5) := (Sail.BitVec.extractLsb v__0 20 16)
       if (Eq Rm Rn)
       then true
       else false
  else if (Eq (Sail.BitVec.extractLsb v__0 30 24) (0b1001010 : (BitVec 7)))
       then let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
            let Rd : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
            if (Eq Rn Rd)
            then true
            else false
       else if (Bool.and (Eq (Sail.BitVec.extractLsb v__0 31 12) (0xD5033 : (BitVec 20)))
                 (Eq (Sail.BitVec.extractLsb v__0 7 0) (0xBF : (BitVec 8))))
            then true
            else if (Eq (Sail.BitVec.extractLsb v__0 31 24) (0xB4 : (BitVec 8)))
                 then false
                 else true

def initialize_registers (_ : Unit) : Unit :=
  ()

