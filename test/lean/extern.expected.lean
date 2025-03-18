import Out.Sail.Sail
import Out.Sail.BitVec

open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

abbrev bits k_n := (BitVec k_n)

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq

abbrev Register := PEmpty
abbrev RegisterType : Register -> Type := PEmpty.elim

abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception


XXXXXXXXX

import Out.Mapping

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

open option

namespace Functions

def extern_add (_ : Unit) : Int :=
  (5 +i 4)

def extern_sub (_ : Unit) : Int :=
  (5 -i (-4))

def extern_sub_nat (_ : Unit) : Nat :=
  (5 -i 4)

def extern_negate (_ : Unit) : Int :=
  (Neg.neg 5)

def extern_mult (_ : Unit) : Int :=
  (5 *i 4)

def extern__shl8 (_ : Unit) : Int :=
  (Int.shiftl 8 2)

def extern__shl32 (_ : Unit) : Int :=
  (Int.shiftl 32 1)

def extern__shl1 (_ : Unit) : Int :=
  (Int.shiftl 1 2)

def extern__shl_int (_ : Unit) : Int :=
  (Int.shiftl 4 2)

def extern__shr32 (_ : Unit) : Int :=
  (Int.shiftl 30 1)

def extern__shr_int (_ : Unit) : Int :=
  (Int.shiftr 8 2)

def extern_tdiv (_ : Unit) : Int :=
  (Int.tdiv 5 4)

def extern_tmod (_ : Unit) : Int :=
  (Int.tmod 5 4)

def extern_tmod_positive (_ : Unit) : Int :=
  (Int.tmod 5 4)

def extern_max (_ : Unit) : Int :=
  (Max.max 5 4)

def extern_min (_ : Unit) : Int :=
  (Min.min 5 4)

def extern_abs_int_plain (_ : Unit) : Int :=
  let x : Int := (-5)
  (Sail.Int.intAbs x)

def extern_eq_unit (_ : Unit) : Bool :=
  (BEq.beq () ())

def extern_eq_bit (_ : Unit) : Bool :=
  (BEq.beq 0#1 1#1)

def extern_not (_ : Unit) : Bool :=
  (Bool.not true)

def extern_and (_ : Unit) : Bool :=
  (Bool.and true false)

def extern_and_no_flow (_ : Unit) : Bool :=
  (Bool.and true false)

def extern_or (_ : Unit) : Bool :=
  (Bool.or true false)

def extern_eq_bool (_ : Unit) : Bool :=
  (BEq.beq true false)

def extern_eq_int (_ : Unit) : Bool :=
  (BEq.beq 5 4)

def extern_lteq_int (_ : Unit) : Bool :=
  (5 ≤b 4)

def extern_gteq_int (_ : Unit) : Bool :=
  (5 ≥b 4)

def extern_lt_int (_ : Unit) : Bool :=
  (5 <b 4)

def extern_gt_int (_ : Unit) : Bool :=
  (5 >b 4)

def extern_eq_anything (_ : Unit) : Bool :=
  (BEq.beq true true)

def extern_vector_update (_ : Unit) : (Vector Int 5) :=
  (vectorUpdate #v[23, 23, 23, 23, 23] 2 42)

def extern_string_take (_ : Unit) : String :=
  (String.take "Hello, world" 5)

def extern_string_drop (_ : Unit) : String :=
  (String.drop "Hello, world" 5)

def extern_string_length (_ : Unit) : Int :=
  (String.length "Hello, world")

def extern_string_append (_ : Unit) : String :=
  (String.append "Hello, " "world")

def extern_string_startswith (_ : Unit) : Bool :=
  (String.startsWith "Hello, world" "Hello")

def extern_eq_string (_ : Unit) : Bool :=
  (BEq.beq "Hello" "world")

def extern_concat_str (_ : Unit) : String :=
  (HAppend.hAppend "Hello, " "world")

def extern_n_leading_spaces (_ : Unit) : Nat :=
  (String.leadingSpaces "   Belated Hello world!")

def extern_hex_str (_ : Unit) : String :=
  (Int.toHex 123)

def extern_hex_str_upper (_ : Unit) : String :=
  (Int.toHexUpper 123)

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

end Functions
