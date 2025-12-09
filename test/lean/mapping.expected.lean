import Out.Sail.Sail
import Out.Sail.BitVec

open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV1

abbrev bit := (BitVec 1)

abbrev bits k_n := (BitVec k_n)

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq, Repr
  open option

inductive word_width where | BYTE | HALF | WORD | DOUBLE
  deriving BEq, Inhabited, Repr
  open word_width

abbrev Register := PEmpty
abbrev RegisterType : Register -> Type := PEmpty.elim

abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception
abbrev SailME := PreSailME RegisterType trivialChoiceSource exception


XXXXXXXXX

import Out.Sail.Sail
import Out.Sail.BitVec
import Out.Sail.IntRange
import Out.Defs
import Out.Specialization
import Out.FakeReal

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV1

namespace Out.Functions

open word_width
open option

/-- Type quantifiers: k_ex1029_ : Bool, k_ex1028_ : Bool -/
def neq_bool (x : Bool) (y : Bool) : Bool :=
  (! (x == y))

/-- Type quantifiers: x : Int -/
def __id (x : Int) : Int :=
  x

/-- Type quantifiers: n : Int, m : Int -/
def _shl_int_general (m : Int) (n : Int) : Int :=
  if ((n ≥b 0) : Bool)
  then (Int.shiftl m n)
  else (Int.shiftr m (Neg.neg n))

/-- Type quantifiers: n : Int, m : Int -/
def _shr_int_general (m : Int) (n : Int) : Int :=
  if ((n ≥b 0) : Bool)
  then (Int.shiftr m n)
  else (Int.shiftl m (Neg.neg n))

/-- Type quantifiers: m : Int, n : Int -/
def fdiv_int (n : Int) (m : Int) : Int :=
  if (((n <b 0) && (m >b 0)) : Bool)
  then ((Int.tdiv (n +i 1) m) -i 1)
  else
    (if (((n >b 0) && (m <b 0)) : Bool)
    then ((Int.tdiv (n -i 1) m) -i 1)
    else (Int.tdiv n m))

/-- Type quantifiers: m : Int, n : Int -/
def fmod_int (n : Int) (m : Int) : Int :=
  (n -i (m *i (fdiv_int n m)))

/-- Type quantifiers: len : Nat, k_v : Nat, len ≥ 0 ∧ k_v ≥ 0 -/
def sail_mask (len : Nat) (v : (BitVec k_v)) : (BitVec len) :=
  if ((len ≤b (Sail.BitVec.length v)) : Bool)
  then (Sail.BitVec.truncate v len)
  else (Sail.BitVec.zeroExtend v len)

/-- Type quantifiers: n : Nat, n ≥ 0 -/
def sail_ones (n : Nat) : (BitVec n) :=
  (Complement.complement (BitVec.zero n))

/-- Type quantifiers: l : Int, i : Int, n : Nat, n ≥ 0 -/
def slice_mask {n : _} (i : Int) (l : Int) : (BitVec n) :=
  if ((l ≥b n) : Bool)
  then ((sail_ones n) <<< i)
  else
    (let one : (BitVec n) := (sail_mask n (1#1 : (BitVec 1)))
    (((one <<< l) - one) <<< i))

/-- Type quantifiers: n : Nat, n > 0 -/
def to_bytes_le {n : _} (b : (BitVec (8 * n))) : (Vector (BitVec 8) n) := Id.run do
  let res := (vectorInit (BitVec.zero 8))
  let loop_i_lower := 0
  let loop_i_upper := (n -i 1)
  let mut loop_vars := res
  for i in [loop_i_lower:loop_i_upper:1]i do
    let res := loop_vars
    loop_vars := (vectorUpdate res i (Sail.BitVec.extractLsb b ((8 *i i) +i 7) (8 *i i)))
  (pure loop_vars)

/-- Type quantifiers: n : Nat, n > 0 -/
def from_bytes_le {n : _} (v : (Vector (BitVec 8) n)) : (BitVec (8 * n)) := Id.run do
  let res := (BitVec.zero (8 *i n))
  let loop_i_lower := 0
  let loop_i_upper := (n -i 1)
  let mut loop_vars := res
  for i in [loop_i_lower:loop_i_upper:1]i do
    let res := loop_vars
    loop_vars := (Sail.BitVec.updateSubrange res ((8 *i i) +i 7) (8 *i i) (GetElem?.getElem! v i))
  (pure loop_vars)

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

def undefined_word_width (_ : Unit) : SailM word_width := do
  (internal_pick [BYTE, HALF, WORD, DOUBLE])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def word_width_of_num (arg_ : Nat) : word_width :=
  match arg_ with
  | 0 => BYTE
  | 1 => HALF
  | 2 => WORD
  | _ => DOUBLE

def num_of_word_width (arg_ : word_width) : Int :=
  match arg_ with
  | BYTE => 0
  | HALF => 1
  | WORD => 2
  | DOUBLE => 3

def size_bits_forwards (arg_ : word_width) : (BitVec 2) :=
  match arg_ with
  | BYTE => 0b00#2
  | HALF => 0b01#2
  | WORD => 0b10#2
  | DOUBLE => 0b11#2

def size_bits_backwards (arg_ : (BitVec 2)) : word_width :=
  match arg_ with
  | 0b00 => BYTE
  | 0b01 => HALF
  | 0b10 => WORD
  | _ => DOUBLE

def size_bits_forwards_matches (arg_ : word_width) : Bool :=
  match arg_ with
  | BYTE => true
  | HALF => true
  | WORD => true
  | DOUBLE => true
  | _ => false

def size_bits_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b00 => true
  | 0b01 => true
  | 0b10 => true
  | 0b11 => true
  | _ => false

def size_bits2_forwards (arg_ : word_width) : (BitVec 2) :=
  match arg_ with
  | BYTE => 0b00#2
  | HALF => 0b01#2
  | WORD => 0b10#2
  | DOUBLE => 0b11#2

def size_bits2_backwards (arg_ : (BitVec 2)) : word_width :=
  match arg_ with
  | 0b00 => BYTE
  | 0b01 => HALF
  | 0b10 => WORD
  | _ => DOUBLE

def size_bits2_forwards_matches (arg_ : word_width) : Bool :=
  match arg_ with
  | BYTE => true
  | HALF => true
  | WORD => true
  | DOUBLE => true
  | _ => false

def size_bits2_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b00 => true
  | 0b01 => true
  | 0b10 => true
  | 0b11 => true
  | _ => false

def size_bits3_forwards (arg_ : word_width) : (BitVec 2) :=
  match arg_ with
  | BYTE => 0b00#2
  | HALF => 0b01#2
  | WORD => 0b10#2
  | DOUBLE => 0b11#2

def size_bits3_backwards (arg_ : (BitVec 2)) : word_width :=
  match arg_ with
  | 0b00 => BYTE
  | 0b01 => HALF
  | 0b10 => WORD
  | _ => DOUBLE

def size_bits3_forwards_matches (arg_ : word_width) : Bool :=
  match arg_ with
  | BYTE => true
  | HALF => true
  | WORD => true
  | DOUBLE => true
  | _ => false

def size_bits3_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  match arg_ with
  | 0b00 => true
  | 0b01 => true
  | 0b10 => true
  | 0b11 => true
  | _ => false

def ta_flag_forwards (arg_ : String) : SailM (BitVec 1) := do
  match arg_ with
  | "ta" => (pure 1#1)
  | "tu" => (pure 0#1)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def ta_flag_backwards (arg_ : (BitVec 1)) : String :=
  match arg_ with
  | 1 => "ta"
  | _ => "tu"

def ta_flag_forwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | "ta" => true
  | "tu" => true
  | _ => false

def ta_flag_backwards_matches (arg_ : (BitVec 1)) : Bool :=
  match arg_ with
  | 1 => true
  | 0 => true
  | _ => false

/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def hex_bits_forwards (bv : (BitVec k_n)) : (Nat × String) :=
  ((Sail.BitVec.length bv), (Int.toHex (BitVec.toNatInt bv)))

/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def hex_bits_forwards_matches (bv : (BitVec k_n)) : Bool :=
  true

/-- Type quantifiers: tuple_0.1 : Nat, tuple_0.1 > 0 -/
def hex_bits_backwards (tuple_0 : (Nat × String)) : (BitVec tuple_0.1) :=
  let (n, str) := tuple_0
  (parse_hex_bits n str)

/-- Type quantifiers: tuple_0.1 : Nat, tuple_0.1 > 0 -/
def hex_bits_backwards_matches (tuple_0 : (Nat × String)) : Bool :=
  let (n, str) := tuple_0
  (valid_hex_bits n str)

def hex_bits_2_forwards (arg_ : (BitVec 2)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (2, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_2_backwards (arg_ : String) : (BitVec 2) :=
  match arg_ with
  | s => (hex_bits_backwards (2, s))

def hex_bits_2_forwards_matches (arg_ : (BitVec 2)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (2, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_2_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def vtype_assembly_forwards (arg_ : String) : SailM ((BitVec 1) × (BitVec 1)) := do
  throw Error.Exit

def vtype_assembly_backwards (arg_ : ((BitVec 1) × (BitVec 1))) : SailM String := do
  match arg_ with
  | (ta, sew) =>
    (do
      if (((BitVec.access sew 0) == 1#1) : Bool)
      then (pure (String.append (ta_flag_backwards sew) (String.append (ta_flag_backwards ta) "")))
      else (hex_bits_2_forwards ((ta : (BitVec 1)) ++ (sew : (BitVec 1)))))

def vtype_assembly_forwards_matches (arg_ : String) : SailM Bool := do
  throw Error.Exit

def vtype_assembly_backwards_matches (arg_ : ((BitVec 1) × (BitVec 1))) : Bool :=
  match arg_ with
  | (ta, sew) =>
    (if (((BitVec.access sew 0) == 1#1) : Bool)
    then true
    else true)

def vtype_assembly2_forwards (arg_ : String) : SailM ((BitVec 1) × (BitVec 1)) := do
  let head_exp_ := arg_
  match (let mapping0_ := head_exp_
  if ((hex_bits_2_backwards_matches mapping0_) : Bool)
  then
    (match_bv (hex_bits_2_backwards mapping0_) with
    | [ta:1,sew:1] => (some (ta, sew))
    | _ => none)
  else none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def vtype_assembly2_backwards (arg_ : ((BitVec 1) × (BitVec 1))) : SailM String := do
  match arg_ with
  | (ta, sew) => (hex_bits_2_forwards ((ta : (BitVec 1)) ++ (sew : (BitVec 1))))

def vtype_assembly2_forwards_matches (arg_ : String) : SailM Bool := do
  let head_exp_ := arg_
  match (let mapping0_ := head_exp_
  if ((hex_bits_2_backwards_matches mapping0_) : Bool)
  then
    (match_bv (hex_bits_2_backwards mapping0_) with
    | [ta:1,sew:1] => (some true)
    | _ => none)
  else none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def vtype_assembly2_backwards_matches (arg_ : ((BitVec 1) × (BitVec 1))) : Bool :=
  match arg_ with
  | (ta, sew) => true
  | _ => false

def vtype_assembly3_forwards (arg_ : String) : SailM ((BitVec 1) × (BitVec 1)) := do
  match arg_ with
  | _ => throw Error.Exit

def vtype_assembly3_backwards (arg_ : ((BitVec 1) × (BitVec 1))) : String :=
  match arg_ with
  | (ta, sew) => (String.append (ta_flag_backwards sew) (String.append (ta_flag_backwards ta) ""))

def vtype_assembly3_forwards_matches (arg_ : String) : SailM Bool := do
  match arg_ with
  | _ => throw Error.Exit
  | _ => (pure false)

def vtype_assembly3_backwards_matches (arg_ : ((BitVec 1) × (BitVec 1))) : Bool :=
  match arg_ with
  | (ta, sew) => true
  | _ => false

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

end Out.Functions
