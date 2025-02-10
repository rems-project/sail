import Out.Sail.Sail

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

def extern_add (lit : Unit) : Int :=
  (HAdd.hAdd 5 4)

def extern_sub (lit : Unit) : Int :=
  (HSub.hSub 5 (-4))

def extern_sub_nat (lit : Unit) : Nat :=
  (HSub.hSub 5 4)

def extern_negate (lit : Unit) : Int :=
  (Neg.neg 5)

def extern_mult (lit : Unit) : Int :=
  (HMul.hMul 5 4)

def extern_tdiv (lit : Unit) : Int :=
  (Int.tdiv 5 4)

def extern_tmod (lit : Unit) : Int :=
  (Int.tmod 5 4)

def extern_tmod_positive (lit : Unit) : Int :=
  (Int.tmod 5 4)

def extern_max (lit : Unit) : Int :=
  (Max.max 5 4)

def extern_min (lit : Unit) : Int :=
  (Min.min 5 4)

def extern_abs_int_plain (lit : Unit) : Int :=
  let x : Int := (-5)
  (Sail.Int.intAbs x)

def extern_eq_unit (lit : Unit) : Bool :=
  (Eq () ())

def extern_eq_bit (lit : Unit) : Bool :=
  (Eq 0#1 1#1)

def extern_not (lit : Unit) : Bool :=
  (Bool.not true)

def extern_and (lit : Unit) : Bool :=
  (Bool.and true false)

def extern_and_no_flow (lit : Unit) : Bool :=
  (Bool.and true false)

def extern_or (lit : Unit) : Bool :=
  (Bool.or true false)

def extern_eq_bool (lit : Unit) : Bool :=
  (Eq true false)

def extern_eq_int (lit : Unit) : Bool :=
  (Eq 5 4)

def extern_lteq_int (lit : Unit) : Bool :=
  (LE.le 5 4)

def extern_gteq_int (lit : Unit) : Bool :=
  (GE.ge 5 4)

def extern_lt_int (lit : Unit) : Bool :=
  (LT.lt 5 4)

def extern_gt_int (lit : Unit) : Bool :=
  (GT.gt 5 4)

def extern_eq_anything (lit : Unit) : Bool :=
  (BEq.beq true true)

def initialize_registers (lit : Unit) : Unit :=
  ()

