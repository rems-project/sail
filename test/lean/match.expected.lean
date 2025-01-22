import Out.Sail.Sail

open Sail

inductive E where | A | B | C
  deriving Inhabited
open E

def undefined_E : SailM E := do
  sorry

def match_enum (x : E) : (BitVec 1) :=
  match x with
  | A => 1#1
  | B => 1#1
  | C => 0#1


def match_option (x : (Option (BitVec 1))) : (BitVec 1) :=
  match x with
  | Some x => x
  | None () => 0#1


/-- Type quantifiers: y : Int, x : Int -/
def match_pair_pat (x : Int) (y : Int) : Int :=
  match (x, y) with
  | (a, b) => (HAdd.hAdd a b)


/-- Type quantifiers: arg1 : Int, arg0 : Int -/
def match_pair (arg0 : Int) (arg1 : Int) : Int :=
  let x := (arg0, arg1)
  match x with
  | (a, b) => (HAdd.hAdd a b)


def initialize_registers : Unit :=
  ()

