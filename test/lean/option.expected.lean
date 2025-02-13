import Out.Sail.Sail
import Out.Sail.BitVec

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

def match_option (x : (Option (BitVec 1))) : (BitVec 1) :=
  match x with
  | some x => x
  | none => 0#1

def option_match (x : (Option Unit)) (y : (BitVec 1)) : (Option (BitVec 1)) :=
  match x with
  | some () => (some y)
  | none => none

def initialize_registers (_ : Unit) : Unit :=
  ()

