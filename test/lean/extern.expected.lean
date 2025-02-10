import Out.Sail.Sail

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

def extern_add (lit : Unit) : Int :=
  (Int.add 5 4)

def extern_sub (lit : Unit) : Int :=
  (Int.sub 5 (-4))

def extern_tdiv (lit : Unit) : Int :=
  (Int.tdiv 5 4)

def extern_tmod (lit : Unit) : Int :=
  (Int.tmod 5 4)

def extern_tmod_positive (lit : Unit) : Int :=
  (Int.tmod 5 4)

def extern_negate (lit : Unit) : Int :=
  (Int.neg (-5))

def extern_mult (lit : Unit) : Int :=
  (Int.mul 5 (-4))

def extern_and (lit : Unit) : Bool :=
  (Bool.and true false)

def extern_and_no_flow (lit : Unit) : Bool :=
  (Bool.and true false)

def extern_or (lit : Unit) : Bool :=
  (Bool.or true false)

def extern_eq_bool (lit : Unit) : Bool :=
  (Eq true false)

def extern_eq_bit (lit : Unit) : Bool :=
  (Eq 0#1 1#1)

def initialize_registers (lit : Unit) : Unit :=
  ()

