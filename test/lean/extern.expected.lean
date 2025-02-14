import Out.Sail.Sail
import Out.Sail.BitVec

open Sail

abbrev bits k_n := (BitVec k_n)

/-- Type quantifiers: k_a : Type -/

inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)

open option

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource Unit

def spc_forwards (_ : Unit) : String :=
  " "

def spc_forwards_matches (_ : Unit) : Bool :=
  true

def spc_backwards (x : String) : Unit :=
  ()

def spc_backwards_matches (s : String) : Bool :=
  let len := (String.length s)
  (Bool.and (Eq (String.leadingSpaces s) len) (GT.gt len 0))

def opt_spc_forwards (_ : Unit) : String :=
  ""

def opt_spc_forwards_matches (_ : Unit) : Bool :=
  true

def opt_spc_backwards (x : String) : Unit :=
  ()

def opt_spc_backwards_matches (s : String) : Bool :=
  (Eq (String.leadingSpaces s) (String.length s))

def def_spc_forwards (_ : Unit) : String :=
  " "

def def_spc_forwards_matches (_ : Unit) : Bool :=
  true

def def_spc_backwards (x : String) : Unit :=
  ()

def def_spc_backwards_matches (s : String) : Bool :=
  (Eq (String.leadingSpaces s) (String.length s))

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
  (Eq () ())

def extern_eq_bit (_ : Unit) : Bool :=
  (Eq 0#1 1#1)

def extern_not (_ : Unit) : Bool :=
  (Bool.not true)

def extern_and (_ : Unit) : Bool :=
  (Bool.and true false)

def extern_and_no_flow (_ : Unit) : Bool :=
  (Bool.and true false)

def extern_or (_ : Unit) : Bool :=
  (Bool.or true false)

def extern_eq_bool (_ : Unit) : Bool :=
  (Eq true false)

def extern_eq_int (_ : Unit) : Bool :=
  (Eq 5 4)

def extern_lteq_int (_ : Unit) : Bool :=
  (LE.le 5 4)

def extern_gteq_int (_ : Unit) : Bool :=
  (GE.ge 5 4)

def extern_lt_int (_ : Unit) : Bool :=
  (LT.lt 5 4)

def extern_gt_int (_ : Unit) : Bool :=
  (GT.gt 5 4)

def extern_eq_anything (_ : Unit) : Bool :=
  (Eq true true)

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
  (Eq "Hello" "world")

def extern_concat_str (_ : Unit) : String :=
  (HAppend.hAppend "Hello, " "world")

def extern_n_leading_spaces (_ : Unit) : Nat :=
  (String.leadingSpaces "   Belated Hello world!")

def initialize_registers (_ : Unit) : Unit :=
  ()

