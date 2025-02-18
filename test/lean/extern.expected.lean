import Out.Sail.Sail
import Out.Sail.BitVec

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false

open Sail

abbrev bits k_n := (BitVec k_n)

/-- Type quantifiers: k_a : Type -/

inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)

open option

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource Unit

namespace Functions

/-- Type quantifiers: k_ex1162# : Bool, k_ex1161# : Bool -/
def neq_bool (x : Bool) (y : Bool) : Bool :=
  (Bool.not (BEq.beq x y))

/-- Type quantifiers: x : Int -/
def __id (x : Int) : Int :=
  x

/-- Type quantifiers: len : Nat, k_v : Nat, len ≥ 0 ∧ k_v ≥ 0 -/
def sail_mask (len : Nat) (v : (BitVec k_v)) : (BitVec len) :=
  if (LE.le len (Sail.BitVec.length v))
  then (Sail.BitVec.truncate v len)
  else (Sail.BitVec.zeroExtend v len)

/-- Type quantifiers: n : Nat, n ≥ 0 -/
def sail_ones (n : Nat) : (BitVec n) :=
  (Complement.complement (BitVec.zero n))

/-- Type quantifiers: l : Int, i : Int, n : Nat, n ≥ 0 -/
def slice_mask {n : _} (i : Int) (l : Int) : (BitVec n) :=
  if (GE.ge l n)
  then (HShiftLeft.hShiftLeft (sail_ones n) i)
  else let one : (BitVec n) := (sail_mask n (0b1 : (BitVec 1)))
       (HShiftLeft.hShiftLeft (HSub.hSub (HShiftLeft.hShiftLeft one l) one) i)

/-- Type quantifiers: n : Int, m : Int -/
def _shl_int_general (m : Int) (n : Int) : Int :=
  if (GE.ge n 0)
  then (Int.shiftl m n)
  else (Int.shiftr m (Neg.neg n))

/-- Type quantifiers: n : Int, m : Int -/
def _shr_int_general (m : Int) (n : Int) : Int :=
  if (GE.ge n 0)
  then (Int.shiftr m n)
  else (Int.shiftl m (Neg.neg n))

/-- Type quantifiers: m : Int, n : Int -/
def fdiv_int (n : Int) (m : Int) : Int :=
  if (Bool.and (LT.lt n 0) (GT.gt m 0))
  then (HSub.hSub (Int.tdiv (HAdd.hAdd n 1) m) 1)
  else if (Bool.and (GT.gt n 0) (LT.lt m 0))
       then (HSub.hSub (Int.tdiv (HSub.hSub n 1) m) 1)
       else (Int.tdiv n m)

/-- Type quantifiers: m : Int, n : Int -/
def fmod_int (n : Int) (m : Int) : Int :=
  (HSub.hSub n (HMul.hMul m (fdiv_int n m)))

/-- Type quantifiers: k_a : Type -/
def is_none (opt : (Option k_a)) : Bool :=
  match opt with
  | .some _ => false
  | none => true

/-- Type quantifiers: k_a : Type -/
def is_some (opt : (Option k_a)) : Bool :=
  match opt with
  | .some _ => true
  | none => false

/-- Type quantifiers: k_n : Int -/
def concat_str_bits (str : String) (x : (BitVec k_n)) : String :=
  (HAppend.hAppend str (BitVec.toFormatted x))

/-- Type quantifiers: x : Int -/
def concat_str_dec (str : String) (x : Int) : String :=
  (HAppend.hAppend str (Int.repr x))

def spc_forwards (_ : Unit) : String :=
  " "

def spc_forwards_matches (_ : Unit) : Bool :=
  true

def spc_backwards (x_0 : String) : Unit :=
  ()

def spc_backwards_matches (s : String) : Bool :=
  let len := (String.length s)
  (Bool.and (BEq.beq (String.leadingSpaces s) len) (GT.gt len 0))

def opt_spc_forwards (_ : Unit) : String :=
  ""

def opt_spc_forwards_matches (_ : Unit) : Bool :=
  true

def opt_spc_backwards (x_0 : String) : Unit :=
  ()

def opt_spc_backwards_matches (s : String) : Bool :=
  (BEq.beq (String.leadingSpaces s) (String.length s))

def def_spc_forwards (_ : Unit) : String :=
  " "

def def_spc_forwards_matches (_ : Unit) : Bool :=
  true

def def_spc_backwards (x_0 : String) : Unit :=
  ()

def def_spc_backwards_matches (s : String) : Bool :=
  (BEq.beq (String.leadingSpaces s) (String.length s))

def sep_forwards (arg_ : Unit) : String :=
  match arg_ with
  | () =>
    (String.append (opt_spc_forwards ())
      (String.append "," (String.append (def_spc_forwards ()) "")))

def sep_backwards (arg_ : String) : SailM Unit := do
  match arg_ with
  | _ => throw Error.Exit

def sep_forwards_matches (arg_ : Unit) : Bool :=
  match arg_ with
  | () => true

def sep_backwards_matches (arg_ : String) : SailM Bool := do
  match arg_ with
  | _ => throw Error.Exit

def extern_add (_ : Unit) : Int :=
  (HAdd.hAdd 5 4)

def extern_sub (_ : Unit) : Int :=
  (HSub.hSub 5 (-4))

def extern_sub_nat (_ : Unit) : Nat :=
  (HSub.hSub 5 4)

def extern_negate (_ : Unit) : Int :=
  (Neg.neg 5)

def extern_mult (_ : Unit) : Int :=
  (HMul.hMul 5 4)

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
  (LE.le 5 4)

def extern_gteq_int (_ : Unit) : Bool :=
  (GE.ge 5 4)

def extern_lt_int (_ : Unit) : Bool :=
  (LT.lt 5 4)

def extern_gt_int (_ : Unit) : Bool :=
  (GT.gt 5 4)

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

def initialize_registers (_ : Unit) : Unit :=
  ()

end Functions

open Functions

