import Out.Sail.Sail
import Out.Sail.BitVec

open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

abbrev bits k_n := (BitVec k_n)

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq, Repr

abbrev Register := PEmpty
abbrev RegisterType : Register -> Type := PEmpty.elim

abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception


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

namespace Out.Functions

open option

/-- Type quantifiers: k_ex1883# : Bool, k_ex1882# : Bool -/
def neq_bool (x : Bool) (y : Bool) : Bool :=
  (! (x == y))

/-- Type quantifiers: x : Int -/
def __id (x : Int) : Int :=
  x

/-- Type quantifiers: n : Int, m : Int -/
def _shl_int_general (m : Int) (n : Int) : Int :=
  if (n ≥b 0)
  then (Int.shiftl m n)
  else (Int.shiftr m (Neg.neg n))

/-- Type quantifiers: n : Int, m : Int -/
def _shr_int_general (m : Int) (n : Int) : Int :=
  if (n ≥b 0)
  then (Int.shiftr m n)
  else (Int.shiftl m (Neg.neg n))

/-- Type quantifiers: m : Int, n : Int -/
def fdiv_int (n : Int) (m : Int) : Int :=
  if ((n <b 0) && (m >b 0))
  then ((Int.tdiv (n +i 1) m) -i 1)
  else
    (if ((n >b 0) && (m <b 0))
    then ((Int.tdiv (n -i 1) m) -i 1)
    else (Int.tdiv n m))

/-- Type quantifiers: m : Int, n : Int -/
def fmod_int (n : Int) (m : Int) : Int :=
  (n -i (m *i (fdiv_int n m)))

/-- Type quantifiers: len : Nat, k_v : Nat, len ≥ 0 ∧ k_v ≥ 0 -/
def sail_mask (len : Nat) (v : (BitVec k_v)) : (BitVec len) :=
  if (len ≤b (Sail.BitVec.length v))
  then (Sail.BitVec.truncate v len)
  else (Sail.BitVec.zeroExtend v len)

/-- Type quantifiers: n : Nat, n ≥ 0 -/
def sail_ones (n : Nat) : (BitVec n) :=
  (Complement.complement (BitVec.zero n))

/-- Type quantifiers: l : Int, i : Int, n : Nat, n ≥ 0 -/
def slice_mask {n : _} (i : Int) (l : Int) : (BitVec n) :=
  if (l ≥b n)
  then ((sail_ones n) <<< i)
  else
    (let one : (BitVec n) := (sail_mask n (0b1 : (BitVec 1)))
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

/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def hex_bits_forwards (bv : (BitVec k_n)) : (Nat × String) :=
  ((Sail.BitVec.length bv), (Int.toHex (BitVec.toNat bv)))

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

def hex_bits_1_forwards (arg_ : (BitVec 1)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (1, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_1_backwards (arg_ : String) : (BitVec 1) :=
  match arg_ with
  | s => (hex_bits_backwards (1, s))

def hex_bits_1_forwards_matches (arg_ : (BitVec 1)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (1, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_1_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

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

def hex_bits_2_forwards_matches (arg_ : (BitVec 2)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (2, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_2_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_3_forwards (arg_ : (BitVec 3)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (3, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_3_backwards (arg_ : String) : (BitVec 3) :=
  match arg_ with
  | s => (hex_bits_backwards (3, s))

def hex_bits_3_forwards_matches (arg_ : (BitVec 3)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (3, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_3_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_4_forwards (arg_ : (BitVec 4)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (4, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_4_backwards (arg_ : String) : (BitVec 4) :=
  match arg_ with
  | s => (hex_bits_backwards (4, s))

def hex_bits_4_forwards_matches (arg_ : (BitVec 4)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (4, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_4_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_5_forwards (arg_ : (BitVec 5)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (5, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_5_backwards (arg_ : String) : (BitVec 5) :=
  match arg_ with
  | s => (hex_bits_backwards (5, s))

def hex_bits_5_forwards_matches (arg_ : (BitVec 5)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (5, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_5_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_6_forwards (arg_ : (BitVec 6)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (6, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_6_backwards (arg_ : String) : (BitVec 6) :=
  match arg_ with
  | s => (hex_bits_backwards (6, s))

def hex_bits_6_forwards_matches (arg_ : (BitVec 6)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (6, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_6_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_7_forwards (arg_ : (BitVec 7)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (7, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_7_backwards (arg_ : String) : (BitVec 7) :=
  match arg_ with
  | s => (hex_bits_backwards (7, s))

def hex_bits_7_forwards_matches (arg_ : (BitVec 7)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (7, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_7_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_8_forwards (arg_ : (BitVec 8)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (8, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_8_backwards (arg_ : String) : (BitVec 8) :=
  match arg_ with
  | s => (hex_bits_backwards (8, s))

def hex_bits_8_forwards_matches (arg_ : (BitVec 8)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (8, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_8_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_9_forwards (arg_ : (BitVec 9)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (9, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_9_backwards (arg_ : String) : (BitVec 9) :=
  match arg_ with
  | s => (hex_bits_backwards (9, s))

def hex_bits_9_forwards_matches (arg_ : (BitVec 9)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (9, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_9_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_10_forwards (arg_ : (BitVec 10)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (10, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_10_backwards (arg_ : String) : (BitVec 10) :=
  match arg_ with
  | s => (hex_bits_backwards (10, s))

def hex_bits_10_forwards_matches (arg_ : (BitVec 10)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (10, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_10_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_11_forwards (arg_ : (BitVec 11)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (11, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_11_backwards (arg_ : String) : (BitVec 11) :=
  match arg_ with
  | s => (hex_bits_backwards (11, s))

def hex_bits_11_forwards_matches (arg_ : (BitVec 11)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (11, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_11_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_12_forwards (arg_ : (BitVec 12)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (12, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_12_backwards (arg_ : String) : (BitVec 12) :=
  match arg_ with
  | s => (hex_bits_backwards (12, s))

def hex_bits_12_forwards_matches (arg_ : (BitVec 12)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (12, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_12_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_13_forwards (arg_ : (BitVec 13)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (13, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_13_backwards (arg_ : String) : (BitVec 13) :=
  match arg_ with
  | s => (hex_bits_backwards (13, s))

def hex_bits_13_forwards_matches (arg_ : (BitVec 13)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (13, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_13_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_14_forwards (arg_ : (BitVec 14)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (14, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_14_backwards (arg_ : String) : (BitVec 14) :=
  match arg_ with
  | s => (hex_bits_backwards (14, s))

def hex_bits_14_forwards_matches (arg_ : (BitVec 14)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (14, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_14_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_15_forwards (arg_ : (BitVec 15)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (15, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_15_backwards (arg_ : String) : (BitVec 15) :=
  match arg_ with
  | s => (hex_bits_backwards (15, s))

def hex_bits_15_forwards_matches (arg_ : (BitVec 15)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (15, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_15_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_16_forwards (arg_ : (BitVec 16)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (16, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_16_backwards (arg_ : String) : (BitVec 16) :=
  match arg_ with
  | s => (hex_bits_backwards (16, s))

def hex_bits_16_forwards_matches (arg_ : (BitVec 16)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (16, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_16_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_17_forwards (arg_ : (BitVec 17)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (17, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_17_backwards (arg_ : String) : (BitVec 17) :=
  match arg_ with
  | s => (hex_bits_backwards (17, s))

def hex_bits_17_forwards_matches (arg_ : (BitVec 17)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (17, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_17_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_18_forwards (arg_ : (BitVec 18)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (18, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_18_backwards (arg_ : String) : (BitVec 18) :=
  match arg_ with
  | s => (hex_bits_backwards (18, s))

def hex_bits_18_forwards_matches (arg_ : (BitVec 18)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (18, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_18_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_19_forwards (arg_ : (BitVec 19)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (19, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_19_backwards (arg_ : String) : (BitVec 19) :=
  match arg_ with
  | s => (hex_bits_backwards (19, s))

def hex_bits_19_forwards_matches (arg_ : (BitVec 19)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (19, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_19_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_20_forwards (arg_ : (BitVec 20)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (20, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_20_backwards (arg_ : String) : (BitVec 20) :=
  match arg_ with
  | s => (hex_bits_backwards (20, s))

def hex_bits_20_forwards_matches (arg_ : (BitVec 20)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (20, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_20_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_21_forwards (arg_ : (BitVec 21)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (21, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_21_backwards (arg_ : String) : (BitVec 21) :=
  match arg_ with
  | s => (hex_bits_backwards (21, s))

def hex_bits_21_forwards_matches (arg_ : (BitVec 21)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (21, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_21_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_22_forwards (arg_ : (BitVec 22)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (22, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_22_backwards (arg_ : String) : (BitVec 22) :=
  match arg_ with
  | s => (hex_bits_backwards (22, s))

def hex_bits_22_forwards_matches (arg_ : (BitVec 22)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (22, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_22_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_23_forwards (arg_ : (BitVec 23)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (23, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_23_backwards (arg_ : String) : (BitVec 23) :=
  match arg_ with
  | s => (hex_bits_backwards (23, s))

def hex_bits_23_forwards_matches (arg_ : (BitVec 23)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (23, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_23_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_24_forwards (arg_ : (BitVec 24)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (24, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_24_backwards (arg_ : String) : (BitVec 24) :=
  match arg_ with
  | s => (hex_bits_backwards (24, s))

def hex_bits_24_forwards_matches (arg_ : (BitVec 24)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (24, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_24_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_25_forwards (arg_ : (BitVec 25)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (25, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_25_backwards (arg_ : String) : (BitVec 25) :=
  match arg_ with
  | s => (hex_bits_backwards (25, s))

def hex_bits_25_forwards_matches (arg_ : (BitVec 25)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (25, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_25_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_26_forwards (arg_ : (BitVec 26)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (26, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_26_backwards (arg_ : String) : (BitVec 26) :=
  match arg_ with
  | s => (hex_bits_backwards (26, s))

def hex_bits_26_forwards_matches (arg_ : (BitVec 26)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (26, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_26_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_27_forwards (arg_ : (BitVec 27)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (27, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_27_backwards (arg_ : String) : (BitVec 27) :=
  match arg_ with
  | s => (hex_bits_backwards (27, s))

def hex_bits_27_forwards_matches (arg_ : (BitVec 27)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (27, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_27_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_28_forwards (arg_ : (BitVec 28)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (28, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_28_backwards (arg_ : String) : (BitVec 28) :=
  match arg_ with
  | s => (hex_bits_backwards (28, s))

def hex_bits_28_forwards_matches (arg_ : (BitVec 28)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (28, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_28_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_29_forwards (arg_ : (BitVec 29)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (29, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_29_backwards (arg_ : String) : (BitVec 29) :=
  match arg_ with
  | s => (hex_bits_backwards (29, s))

def hex_bits_29_forwards_matches (arg_ : (BitVec 29)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (29, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_29_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_30_forwards (arg_ : (BitVec 30)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (30, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_30_backwards (arg_ : String) : (BitVec 30) :=
  match arg_ with
  | s => (hex_bits_backwards (30, s))

def hex_bits_30_forwards_matches (arg_ : (BitVec 30)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (30, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_30_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_31_forwards (arg_ : (BitVec 31)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (31, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_31_backwards (arg_ : String) : (BitVec 31) :=
  match arg_ with
  | s => (hex_bits_backwards (31, s))

def hex_bits_31_forwards_matches (arg_ : (BitVec 31)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (31, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_31_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_32_forwards (arg_ : (BitVec 32)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (32, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_32_backwards (arg_ : String) : (BitVec 32) :=
  match arg_ with
  | s => (hex_bits_backwards (32, s))

def hex_bits_32_forwards_matches (arg_ : (BitVec 32)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (32, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_32_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_33_forwards (arg_ : (BitVec 33)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (33, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_33_backwards (arg_ : String) : (BitVec 33) :=
  match arg_ with
  | s => (hex_bits_backwards (33, s))

def hex_bits_33_forwards_matches (arg_ : (BitVec 33)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (33, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_33_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_34_forwards (arg_ : (BitVec 34)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (34, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_34_backwards (arg_ : String) : (BitVec 34) :=
  match arg_ with
  | s => (hex_bits_backwards (34, s))

def hex_bits_34_forwards_matches (arg_ : (BitVec 34)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (34, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_34_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_35_forwards (arg_ : (BitVec 35)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (35, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_35_backwards (arg_ : String) : (BitVec 35) :=
  match arg_ with
  | s => (hex_bits_backwards (35, s))

def hex_bits_35_forwards_matches (arg_ : (BitVec 35)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (35, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_35_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_36_forwards (arg_ : (BitVec 36)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (36, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_36_backwards (arg_ : String) : (BitVec 36) :=
  match arg_ with
  | s => (hex_bits_backwards (36, s))

def hex_bits_36_forwards_matches (arg_ : (BitVec 36)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (36, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_36_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_37_forwards (arg_ : (BitVec 37)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (37, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_37_backwards (arg_ : String) : (BitVec 37) :=
  match arg_ with
  | s => (hex_bits_backwards (37, s))

def hex_bits_37_forwards_matches (arg_ : (BitVec 37)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (37, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_37_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_38_forwards (arg_ : (BitVec 38)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (38, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_38_backwards (arg_ : String) : (BitVec 38) :=
  match arg_ with
  | s => (hex_bits_backwards (38, s))

def hex_bits_38_forwards_matches (arg_ : (BitVec 38)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (38, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_38_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_39_forwards (arg_ : (BitVec 39)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (39, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_39_backwards (arg_ : String) : (BitVec 39) :=
  match arg_ with
  | s => (hex_bits_backwards (39, s))

def hex_bits_39_forwards_matches (arg_ : (BitVec 39)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (39, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_39_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_40_forwards (arg_ : (BitVec 40)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (40, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_40_backwards (arg_ : String) : (BitVec 40) :=
  match arg_ with
  | s => (hex_bits_backwards (40, s))

def hex_bits_40_forwards_matches (arg_ : (BitVec 40)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (40, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_40_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_41_forwards (arg_ : (BitVec 41)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (41, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_41_backwards (arg_ : String) : (BitVec 41) :=
  match arg_ with
  | s => (hex_bits_backwards (41, s))

def hex_bits_41_forwards_matches (arg_ : (BitVec 41)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (41, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_41_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_42_forwards (arg_ : (BitVec 42)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (42, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_42_backwards (arg_ : String) : (BitVec 42) :=
  match arg_ with
  | s => (hex_bits_backwards (42, s))

def hex_bits_42_forwards_matches (arg_ : (BitVec 42)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (42, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_42_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_43_forwards (arg_ : (BitVec 43)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (43, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_43_backwards (arg_ : String) : (BitVec 43) :=
  match arg_ with
  | s => (hex_bits_backwards (43, s))

def hex_bits_43_forwards_matches (arg_ : (BitVec 43)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (43, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_43_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_44_forwards (arg_ : (BitVec 44)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (44, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_44_backwards (arg_ : String) : (BitVec 44) :=
  match arg_ with
  | s => (hex_bits_backwards (44, s))

def hex_bits_44_forwards_matches (arg_ : (BitVec 44)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (44, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_44_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_45_forwards (arg_ : (BitVec 45)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (45, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_45_backwards (arg_ : String) : (BitVec 45) :=
  match arg_ with
  | s => (hex_bits_backwards (45, s))

def hex_bits_45_forwards_matches (arg_ : (BitVec 45)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (45, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_45_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_46_forwards (arg_ : (BitVec 46)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (46, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_46_backwards (arg_ : String) : (BitVec 46) :=
  match arg_ with
  | s => (hex_bits_backwards (46, s))

def hex_bits_46_forwards_matches (arg_ : (BitVec 46)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (46, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_46_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_47_forwards (arg_ : (BitVec 47)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (47, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_47_backwards (arg_ : String) : (BitVec 47) :=
  match arg_ with
  | s => (hex_bits_backwards (47, s))

def hex_bits_47_forwards_matches (arg_ : (BitVec 47)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (47, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_47_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_48_forwards (arg_ : (BitVec 48)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (48, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_48_backwards (arg_ : String) : (BitVec 48) :=
  match arg_ with
  | s => (hex_bits_backwards (48, s))

def hex_bits_48_forwards_matches (arg_ : (BitVec 48)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (48, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_48_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_49_forwards (arg_ : (BitVec 49)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (49, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_49_backwards (arg_ : String) : (BitVec 49) :=
  match arg_ with
  | s => (hex_bits_backwards (49, s))

def hex_bits_49_forwards_matches (arg_ : (BitVec 49)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (49, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_49_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_50_forwards (arg_ : (BitVec 50)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (50, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_50_backwards (arg_ : String) : (BitVec 50) :=
  match arg_ with
  | s => (hex_bits_backwards (50, s))

def hex_bits_50_forwards_matches (arg_ : (BitVec 50)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (50, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_50_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_51_forwards (arg_ : (BitVec 51)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (51, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_51_backwards (arg_ : String) : (BitVec 51) :=
  match arg_ with
  | s => (hex_bits_backwards (51, s))

def hex_bits_51_forwards_matches (arg_ : (BitVec 51)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (51, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_51_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_52_forwards (arg_ : (BitVec 52)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (52, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_52_backwards (arg_ : String) : (BitVec 52) :=
  match arg_ with
  | s => (hex_bits_backwards (52, s))

def hex_bits_52_forwards_matches (arg_ : (BitVec 52)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (52, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_52_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_53_forwards (arg_ : (BitVec 53)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (53, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_53_backwards (arg_ : String) : (BitVec 53) :=
  match arg_ with
  | s => (hex_bits_backwards (53, s))

def hex_bits_53_forwards_matches (arg_ : (BitVec 53)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (53, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_53_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_54_forwards (arg_ : (BitVec 54)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (54, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_54_backwards (arg_ : String) : (BitVec 54) :=
  match arg_ with
  | s => (hex_bits_backwards (54, s))

def hex_bits_54_forwards_matches (arg_ : (BitVec 54)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (54, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_54_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_55_forwards (arg_ : (BitVec 55)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (55, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_55_backwards (arg_ : String) : (BitVec 55) :=
  match arg_ with
  | s => (hex_bits_backwards (55, s))

def hex_bits_55_forwards_matches (arg_ : (BitVec 55)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (55, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_55_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_56_forwards (arg_ : (BitVec 56)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (56, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_56_backwards (arg_ : String) : (BitVec 56) :=
  match arg_ with
  | s => (hex_bits_backwards (56, s))

def hex_bits_56_forwards_matches (arg_ : (BitVec 56)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (56, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_56_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_57_forwards (arg_ : (BitVec 57)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (57, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_57_backwards (arg_ : String) : (BitVec 57) :=
  match arg_ with
  | s => (hex_bits_backwards (57, s))

def hex_bits_57_forwards_matches (arg_ : (BitVec 57)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (57, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_57_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_58_forwards (arg_ : (BitVec 58)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (58, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_58_backwards (arg_ : String) : (BitVec 58) :=
  match arg_ with
  | s => (hex_bits_backwards (58, s))

def hex_bits_58_forwards_matches (arg_ : (BitVec 58)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (58, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_58_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_59_forwards (arg_ : (BitVec 59)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (59, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_59_backwards (arg_ : String) : (BitVec 59) :=
  match arg_ with
  | s => (hex_bits_backwards (59, s))

def hex_bits_59_forwards_matches (arg_ : (BitVec 59)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (59, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_59_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_60_forwards (arg_ : (BitVec 60)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (60, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_60_backwards (arg_ : String) : (BitVec 60) :=
  match arg_ with
  | s => (hex_bits_backwards (60, s))

def hex_bits_60_forwards_matches (arg_ : (BitVec 60)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (60, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_60_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_61_forwards (arg_ : (BitVec 61)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (61, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_61_backwards (arg_ : String) : (BitVec 61) :=
  match arg_ with
  | s => (hex_bits_backwards (61, s))

def hex_bits_61_forwards_matches (arg_ : (BitVec 61)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (61, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_61_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_62_forwards (arg_ : (BitVec 62)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (62, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_62_backwards (arg_ : String) : (BitVec 62) :=
  match arg_ with
  | s => (hex_bits_backwards (62, s))

def hex_bits_62_forwards_matches (arg_ : (BitVec 62)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (62, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_62_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_63_forwards (arg_ : (BitVec 63)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (63, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_63_backwards (arg_ : String) : (BitVec 63) :=
  match arg_ with
  | s => (hex_bits_backwards (63, s))

def hex_bits_63_forwards_matches (arg_ : (BitVec 63)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (63, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_63_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def hex_bits_64_forwards (arg_ : (BitVec 64)) : SailM String := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (64, s) => (some s)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def hex_bits_64_backwards (arg_ : String) : (BitVec 64) :=
  match arg_ with
  | s => (hex_bits_backwards (64, s))

def hex_bits_64_forwards_matches (arg_ : (BitVec 64)) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (64, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def hex_bits_64_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def csr_name_map_forwards (arg_ : (BitVec 12)) : SailM String := do
  match_bv arg_ with
  | 000101001101 => do (pure "stimecmp")
  | 000101011101 => do (pure "stimecmph")
  | 110000000011 => do (pure "hpmcounter3")
  | 110000000100 => do (pure "hpmcounter4")
  | 110000000101 => do (pure "hpmcounter5")
  | 110000000110 => do (pure "hpmcounter6")
  | 110000000111 => do (pure "hpmcounter7")
  | 110000001000 => do (pure "hpmcounter8")
  | 110000001001 => do (pure "hpmcounter9")
  | 110000001010 => do (pure "hpmcounter10")
  | 110000001011 => do (pure "hpmcounter11")
  | 110000001100 => do (pure "hpmcounter12")
  | 110000001101 => do (pure "hpmcounter13")
  | 110000001110 => do (pure "hpmcounter14")
  | 110000001111 => do (pure "hpmcounter15")
  | 110000010000 => do (pure "hpmcounter16")
  | 110000010001 => do (pure "hpmcounter17")
  | 110000010010 => do (pure "hpmcounter18")
  | 110000010011 => do (pure "hpmcounter19")
  | 110000010100 => do (pure "hpmcounter20")
  | 110000010101 => do (pure "hpmcounter21")
  | 110000010110 => do (pure "hpmcounter22")
  | 110000010111 => do (pure "hpmcounter23")
  | 110000011000 => do (pure "hpmcounter24")
  | 110000011001 => do (pure "hpmcounter25")
  | 110000011010 => do (pure "hpmcounter26")
  | 110000011011 => do (pure "hpmcounter27")
  | 110000011100 => do (pure "hpmcounter28")
  | 110000011101 => do (pure "hpmcounter29")
  | 110000011110 => do (pure "hpmcounter30")
  | 110000011111 => do (pure "hpmcounter31")
  | 110010000011 => do (pure "hpmcounter3h")
  | 110010000100 => do (pure "hpmcounter4h")
  | 110010000101 => do (pure "hpmcounter5h")
  | 110010000110 => do (pure "hpmcounter6h")
  | 110010000111 => do (pure "hpmcounter7h")
  | 110010001000 => do (pure "hpmcounter8h")
  | 110010001001 => do (pure "hpmcounter9h")
  | 110010001010 => do (pure "hpmcounter10h")
  | 110010001011 => do (pure "hpmcounter11h")
  | 110010001100 => do (pure "hpmcounter12h")
  | 110010001101 => do (pure "hpmcounter13h")
  | 110010001110 => do (pure "hpmcounter14h")
  | 110010001111 => do (pure "hpmcounter15h")
  | 110010010000 => do (pure "hpmcounter16h")
  | 110010010001 => do (pure "hpmcounter17h")
  | 110010010010 => do (pure "hpmcounter18h")
  | 110010010011 => do (pure "hpmcounter19h")
  | 110010010100 => do (pure "hpmcounter20h")
  | 110010010101 => do (pure "hpmcounter21h")
  | 110010010110 => do (pure "hpmcounter22h")
  | 110010010111 => do (pure "hpmcounter23h")
  | 110010011000 => do (pure "hpmcounter24h")
  | 110010011001 => do (pure "hpmcounter25h")
  | 110010011010 => do (pure "hpmcounter26h")
  | 110010011011 => do (pure "hpmcounter27h")
  | 110010011100 => do (pure "hpmcounter28h")
  | 110010011101 => do (pure "hpmcounter29h")
  | 110010011110 => do (pure "hpmcounter30h")
  | 110010011111 => do (pure "hpmcounter31h")
  | 001100100011 => do (pure "mhpmevent3")
  | 001100100100 => do (pure "mhpmevent4")
  | 001100100101 => do (pure "mhpmevent5")
  | 001100100110 => do (pure "mhpmevent6")
  | 001100100111 => do (pure "mhpmevent7")
  | 001100101000 => do (pure "mhpmevent8")
  | 001100101001 => do (pure "mhpmevent9")
  | 001100101010 => do (pure "mhpmevent10")
  | 001100101011 => do (pure "mhpmevent11")
  | 001100101100 => do (pure "mhpmevent12")
  | 001100101101 => do (pure "mhpmevent13")
  | 001100101110 => do (pure "mhpmevent14")
  | 001100101111 => do (pure "mhpmevent15")
  | 001100110000 => do (pure "mhpmevent16")
  | 001100110001 => do (pure "mhpmevent17")
  | 001100110010 => do (pure "mhpmevent18")
  | 001100110011 => do (pure "mhpmevent19")
  | 001100110100 => do (pure "mhpmevent20")
  | 001100110101 => do (pure "mhpmevent21")
  | 001100110110 => do (pure "mhpmevent22")
  | 001100110111 => do (pure "mhpmevent23")
  | 001100111000 => do (pure "mhpmevent24")
  | 001100111001 => do (pure "mhpmevent25")
  | 001100111010 => do (pure "mhpmevent26")
  | 001100111011 => do (pure "mhpmevent27")
  | 001100111100 => do (pure "mhpmevent28")
  | 001100111101 => do (pure "mhpmevent29")
  | 001100111110 => do (pure "mhpmevent30")
  | 001100111111 => do (pure "mhpmevent31")
  | 101100000011 => do (pure "mhpmcounter3")
  | 101100000100 => do (pure "mhpmcounter4")
  | 101100000101 => do (pure "mhpmcounter5")
  | 101100000110 => do (pure "mhpmcounter6")
  | 101100000111 => do (pure "mhpmcounter7")
  | 101100001000 => do (pure "mhpmcounter8")
  | 101100001001 => do (pure "mhpmcounter9")
  | 101100001010 => do (pure "mhpmcounter10")
  | 101100001011 => do (pure "mhpmcounter11")
  | 101100001100 => do (pure "mhpmcounter12")
  | 101100001101 => do (pure "mhpmcounter13")
  | 101100001110 => do (pure "mhpmcounter14")
  | 101100001111 => do (pure "mhpmcounter15")
  | 101100010000 => do (pure "mhpmcounter16")
  | 101100010001 => do (pure "mhpmcounter17")
  | 101100010010 => do (pure "mhpmcounter18")
  | 101100010011 => do (pure "mhpmcounter19")
  | 101100010100 => do (pure "mhpmcounter20")
  | 101100010101 => do (pure "mhpmcounter21")
  | 101100010110 => do (pure "mhpmcounter22")
  | 101100010111 => do (pure "mhpmcounter23")
  | 101100011000 => do (pure "mhpmcounter24")
  | 101100011001 => do (pure "mhpmcounter25")
  | 101100011010 => do (pure "mhpmcounter26")
  | 101100011011 => do (pure "mhpmcounter27")
  | 101100011100 => do (pure "mhpmcounter28")
  | 101100011101 => do (pure "mhpmcounter29")
  | 101100011110 => do (pure "mhpmcounter30")
  | 101100011111 => do (pure "mhpmcounter31")
  | 101110000011 => do (pure "mhpmcounter3h")
  | 101110000100 => do (pure "mhpmcounter4h")
  | 101110000101 => do (pure "mhpmcounter5h")
  | 101110000110 => do (pure "mhpmcounter6h")
  | 101110000111 => do (pure "mhpmcounter7h")
  | 101110001000 => do (pure "mhpmcounter8h")
  | 101110001001 => do (pure "mhpmcounter9h")
  | 101110001010 => do (pure "mhpmcounter10h")
  | 101110001011 => do (pure "mhpmcounter11h")
  | 101110001100 => do (pure "mhpmcounter12h")
  | 101110001101 => do (pure "mhpmcounter13h")
  | 101110001110 => do (pure "mhpmcounter14h")
  | 101110001111 => do (pure "mhpmcounter15h")
  | 101110010000 => do (pure "mhpmcounter16h")
  | 101110010001 => do (pure "mhpmcounter17h")
  | 101110010010 => do (pure "mhpmcounter18h")
  | 101110010011 => do (pure "mhpmcounter19h")
  | 101110010100 => do (pure "mhpmcounter20h")
  | 101110010101 => do (pure "mhpmcounter21h")
  | 101110010110 => do (pure "mhpmcounter22h")
  | 101110010111 => do (pure "mhpmcounter23h")
  | 101110011000 => do (pure "mhpmcounter24h")
  | 101110011001 => do (pure "mhpmcounter25h")
  | 101110011010 => do (pure "mhpmcounter26h")
  | 101110011011 => do (pure "mhpmcounter27h")
  | 101110011100 => do (pure "mhpmcounter28h")
  | 101110011101 => do (pure "mhpmcounter29h")
  | 101110011110 => do (pure "mhpmcounter30h")
  | 101110011111 => do (pure "mhpmcounter31h")
  | 101110000011 => do (pure "mhpmcounter3h")
  | 101110000100 => do (pure "mhpmcounter4h")
  | 101110000101 => do (pure "mhpmcounter5h")
  | 101110000110 => do (pure "mhpmcounter6h")
  | 101110000111 => do (pure "mhpmcounter7h")
  | 101110001000 => do (pure "mhpmcounter8h")
  | 101110001001 => do (pure "mhpmcounter9h")
  | 101110001010 => do (pure "mhpmcounter10h")
  | 101110001011 => do (pure "mhpmcounter11h")
  | 101110001100 => do (pure "mhpmcounter12h")
  | 101110001101 => do (pure "mhpmcounter13h")
  | 101110001110 => do (pure "mhpmcounter14h")
  | 101110001111 => do (pure "mhpmcounter15h")
  | 101110010000 => do (pure "mhpmcounter16h")
  | 101110010001 => do (pure "mhpmcounter17h")
  | 101110010010 => do (pure "mhpmcounter18h")
  | 101110010011 => do (pure "mhpmcounter19h")
  | 101110010100 => do (pure "mhpmcounter20h")
  | 101110010101 => do (pure "mhpmcounter21h")
  | 101110010110 => do (pure "mhpmcounter22h")
  | 101110010111 => do (pure "mhpmcounter23h")
  | 101110011000 => do (pure "mhpmcounter24h")
  | 101110011001 => do (pure "mhpmcounter25h")
  | 101110011010 => do (pure "mhpmcounter26h")
  | 101110011011 => do (pure "mhpmcounter27h")
  | 101110011100 => do (pure "mhpmcounter28h")
  | 101110011101 => do (pure "mhpmcounter29h")
  | 101110011110 => do (pure "mhpmcounter30h")
  | 101110011111 => do (pure "mhpmcounter31h")
  | 001110100000 => do (pure "pmpcfg0")
  | 001110100001 => do (pure "pmpcfg1")
  | 001110100010 => do (pure "pmpcfg2")
  | 001110100011 => do (pure "pmpcfg3")
  | 001110100100 => do (pure "pmpcfg4")
  | 001110100101 => do (pure "pmpcfg5")
  | 001110100110 => do (pure "pmpcfg6")
  | 001110100111 => do (pure "pmpcfg7")
  | 001110101000 => do (pure "pmpcfg8")
  | 001110101001 => do (pure "pmpcfg9")
  | 001110101010 => do (pure "pmpcfg10")
  | 001110101011 => do (pure "pmpcfg11")
  | 001110101100 => do (pure "pmpcfg12")
  | 001110101101 => do (pure "pmpcfg13")
  | 001110101110 => do (pure "pmpcfg14")
  | 001110101111 => do (pure "pmpcfg15")
  | 001110110000 => do (pure "pmpaddr0")
  | 001110110001 => do (pure "pmpaddr1")
  | 001110110010 => do (pure "pmpaddr2")
  | 001110110011 => do (pure "pmpaddr3")
  | 001110110100 => do (pure "pmpaddr4")
  | 001110110101 => do (pure "pmpaddr5")
  | 001110110110 => do (pure "pmpaddr6")
  | 001110110111 => do (pure "pmpaddr7")
  | 001110111000 => do (pure "pmpaddr8")
  | 001110111001 => do (pure "pmpaddr9")
  | 001110111010 => do (pure "pmpaddr10")
  | 001110111011 => do (pure "pmpaddr11")
  | 001110111100 => do (pure "pmpaddr12")
  | 001110111101 => do (pure "pmpaddr13")
  | 001110111110 => do (pure "pmpaddr14")
  | 001110111111 => do (pure "pmpaddr15")
  | 001111000000 => do (pure "pmpaddr16")
  | 001111000001 => do (pure "pmpaddr17")
  | 001111000010 => do (pure "pmpaddr18")
  | 001111000011 => do (pure "pmpaddr19")
  | 001111000100 => do (pure "pmpaddr20")
  | 001111000101 => do (pure "pmpaddr21")
  | 001111000110 => do (pure "pmpaddr22")
  | 001111000111 => do (pure "pmpaddr23")
  | 001111001000 => do (pure "pmpaddr24")
  | 001111001001 => do (pure "pmpaddr25")
  | 001111001010 => do (pure "pmpaddr26")
  | 001111001011 => do (pure "pmpaddr27")
  | 001111001100 => do (pure "pmpaddr28")
  | 001111001101 => do (pure "pmpaddr29")
  | 001111001110 => do (pure "pmpaddr30")
  | 001111001111 => do (pure "pmpaddr31")
  | 001111010000 => do (pure "pmpaddr32")
  | 001111010001 => do (pure "pmpaddr33")
  | 001111010010 => do (pure "pmpaddr34")
  | 001111010011 => do (pure "pmpaddr35")
  | 001111010100 => do (pure "pmpaddr36")
  | 001111010101 => do (pure "pmpaddr37")
  | 001111010110 => do (pure "pmpaddr38")
  | 001111010111 => do (pure "pmpaddr39")
  | 001111011000 => do (pure "pmpaddr40")
  | 001111011001 => do (pure "pmpaddr41")
  | 001111011010 => do (pure "pmpaddr42")
  | 001111011011 => do (pure "pmpaddr43")
  | 001111011100 => do (pure "pmpaddr44")
  | 001111011101 => do (pure "pmpaddr45")
  | 001111011110 => do (pure "pmpaddr46")
  | 001111011111 => do (pure "pmpaddr47")
  | 001111100000 => do (pure "pmpaddr48")
  | 001111100001 => do (pure "pmpaddr49")
  | 001111100010 => do (pure "pmpaddr50")
  | 001111100011 => do (pure "pmpaddr51")
  | 001111100100 => do (pure "pmpaddr52")
  | 001111100101 => do (pure "pmpaddr53")
  | 001111100110 => do (pure "pmpaddr54")
  | 001111100111 => do (pure "pmpaddr55")
  | 001111101000 => do (pure "pmpaddr56")
  | 001111101001 => do (pure "pmpaddr57")
  | 001111101010 => do (pure "pmpaddr58")
  | 001111101011 => do (pure "pmpaddr59")
  | 001111101100 => do (pure "pmpaddr60")
  | 001111101101 => do (pure "pmpaddr61")
  | 001111101110 => do (pure "pmpaddr62")
  | 001111101111 => do (pure "pmpaddr63")
  | 001100100001 => do (pure "mcyclecfg")
  | 011100100001 => do (pure "mcyclecfgh")
  | 001100100010 => do (pure "minstretcfg")
  | 011100100010 => do (pure "minstretcfgh")
  | 000000010101 => do (pure "seed")
  | 000000001000 => do (pure "vstart")
  | 000000001001 => do (pure "vxsat")
  | 000000001010 => do (pure "vxrm")
  | 000000001111 => do (pure "vcsr")
  | 000000000001 => do (pure "fflags")
  | 000000000010 => do (pure "frm")
  | 000000000011 => do (pure "fcsr")
  | 000100000101 => do (pure "stvec")
  | 000101000001 => do (pure "sepc")
  | 001100000101 => do (pure "mtvec")
  | 001101000001 => do (pure "mepc")
  | 110000000000 => do (pure "cycle")
  | 110000000001 => do (pure "time")
  | 110000000010 => do (pure "instret")
  | 110010000000 => do (pure "cycleh")
  | 001100001010 => do (pure "menvcfg")
  | 001100011010 => do (pure "menvcfgh")
  | 001101000011 => do (pure "mtval")
  | 001101000000 => do (pure "mscratch")
  | 000110000000 => do (pure "satp")
  | reg => do (hex_bits_12_forwards reg)

def csr_name_map_backwards (arg_ : String) : SailM (BitVec 12) := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | "stimecmp" => (some (0x14D : (BitVec 12)))
  | "stimecmph" => (some (0x15D : (BitVec 12)))
  | "hpmcounter3" => (some (0xC03 : (BitVec 12)))
  | "hpmcounter4" => (some (0xC04 : (BitVec 12)))
  | "hpmcounter5" => (some (0xC05 : (BitVec 12)))
  | "hpmcounter6" => (some (0xC06 : (BitVec 12)))
  | "hpmcounter7" => (some (0xC07 : (BitVec 12)))
  | "hpmcounter8" => (some (0xC08 : (BitVec 12)))
  | "hpmcounter9" => (some (0xC09 : (BitVec 12)))
  | "hpmcounter10" => (some (0xC0A : (BitVec 12)))
  | "hpmcounter11" => (some (0xC0B : (BitVec 12)))
  | "hpmcounter12" => (some (0xC0C : (BitVec 12)))
  | "hpmcounter13" => (some (0xC0D : (BitVec 12)))
  | "hpmcounter14" => (some (0xC0E : (BitVec 12)))
  | "hpmcounter15" => (some (0xC0F : (BitVec 12)))
  | "hpmcounter16" => (some (0xC10 : (BitVec 12)))
  | "hpmcounter17" => (some (0xC11 : (BitVec 12)))
  | "hpmcounter18" => (some (0xC12 : (BitVec 12)))
  | "hpmcounter19" => (some (0xC13 : (BitVec 12)))
  | "hpmcounter20" => (some (0xC14 : (BitVec 12)))
  | "hpmcounter21" => (some (0xC15 : (BitVec 12)))
  | "hpmcounter22" => (some (0xC16 : (BitVec 12)))
  | "hpmcounter23" => (some (0xC17 : (BitVec 12)))
  | "hpmcounter24" => (some (0xC18 : (BitVec 12)))
  | "hpmcounter25" => (some (0xC19 : (BitVec 12)))
  | "hpmcounter26" => (some (0xC1A : (BitVec 12)))
  | "hpmcounter27" => (some (0xC1B : (BitVec 12)))
  | "hpmcounter28" => (some (0xC1C : (BitVec 12)))
  | "hpmcounter29" => (some (0xC1D : (BitVec 12)))
  | "hpmcounter30" => (some (0xC1E : (BitVec 12)))
  | "hpmcounter31" => (some (0xC1F : (BitVec 12)))
  | "hpmcounter3h" => (some (0xC83 : (BitVec 12)))
  | "hpmcounter4h" => (some (0xC84 : (BitVec 12)))
  | "hpmcounter5h" => (some (0xC85 : (BitVec 12)))
  | "hpmcounter6h" => (some (0xC86 : (BitVec 12)))
  | "hpmcounter7h" => (some (0xC87 : (BitVec 12)))
  | "hpmcounter8h" => (some (0xC88 : (BitVec 12)))
  | "hpmcounter9h" => (some (0xC89 : (BitVec 12)))
  | "hpmcounter10h" => (some (0xC8A : (BitVec 12)))
  | "hpmcounter11h" => (some (0xC8B : (BitVec 12)))
  | "hpmcounter12h" => (some (0xC8C : (BitVec 12)))
  | "hpmcounter13h" => (some (0xC8D : (BitVec 12)))
  | "hpmcounter14h" => (some (0xC8E : (BitVec 12)))
  | "hpmcounter15h" => (some (0xC8F : (BitVec 12)))
  | "hpmcounter16h" => (some (0xC90 : (BitVec 12)))
  | "hpmcounter17h" => (some (0xC91 : (BitVec 12)))
  | "hpmcounter18h" => (some (0xC92 : (BitVec 12)))
  | "hpmcounter19h" => (some (0xC93 : (BitVec 12)))
  | "hpmcounter20h" => (some (0xC94 : (BitVec 12)))
  | "hpmcounter21h" => (some (0xC95 : (BitVec 12)))
  | "hpmcounter22h" => (some (0xC96 : (BitVec 12)))
  | "hpmcounter23h" => (some (0xC97 : (BitVec 12)))
  | "hpmcounter24h" => (some (0xC98 : (BitVec 12)))
  | "hpmcounter25h" => (some (0xC99 : (BitVec 12)))
  | "hpmcounter26h" => (some (0xC9A : (BitVec 12)))
  | "hpmcounter27h" => (some (0xC9B : (BitVec 12)))
  | "hpmcounter28h" => (some (0xC9C : (BitVec 12)))
  | "hpmcounter29h" => (some (0xC9D : (BitVec 12)))
  | "hpmcounter30h" => (some (0xC9E : (BitVec 12)))
  | "hpmcounter31h" => (some (0xC9F : (BitVec 12)))
  | "mhpmevent3" => (some (0x323 : (BitVec 12)))
  | "mhpmevent4" => (some (0x324 : (BitVec 12)))
  | "mhpmevent5" => (some (0x325 : (BitVec 12)))
  | "mhpmevent6" => (some (0x326 : (BitVec 12)))
  | "mhpmevent7" => (some (0x327 : (BitVec 12)))
  | "mhpmevent8" => (some (0x328 : (BitVec 12)))
  | "mhpmevent9" => (some (0x329 : (BitVec 12)))
  | "mhpmevent10" => (some (0x32A : (BitVec 12)))
  | "mhpmevent11" => (some (0x32B : (BitVec 12)))
  | "mhpmevent12" => (some (0x32C : (BitVec 12)))
  | "mhpmevent13" => (some (0x32D : (BitVec 12)))
  | "mhpmevent14" => (some (0x32E : (BitVec 12)))
  | "mhpmevent15" => (some (0x32F : (BitVec 12)))
  | "mhpmevent16" => (some (0x330 : (BitVec 12)))
  | "mhpmevent17" => (some (0x331 : (BitVec 12)))
  | "mhpmevent18" => (some (0x332 : (BitVec 12)))
  | "mhpmevent19" => (some (0x333 : (BitVec 12)))
  | "mhpmevent20" => (some (0x334 : (BitVec 12)))
  | "mhpmevent21" => (some (0x335 : (BitVec 12)))
  | "mhpmevent22" => (some (0x336 : (BitVec 12)))
  | "mhpmevent23" => (some (0x337 : (BitVec 12)))
  | "mhpmevent24" => (some (0x338 : (BitVec 12)))
  | "mhpmevent25" => (some (0x339 : (BitVec 12)))
  | "mhpmevent26" => (some (0x33A : (BitVec 12)))
  | "mhpmevent27" => (some (0x33B : (BitVec 12)))
  | "mhpmevent28" => (some (0x33C : (BitVec 12)))
  | "mhpmevent29" => (some (0x33D : (BitVec 12)))
  | "mhpmevent30" => (some (0x33E : (BitVec 12)))
  | "mhpmevent31" => (some (0x33F : (BitVec 12)))
  | "mhpmcounter3" => (some (0xB03 : (BitVec 12)))
  | "mhpmcounter4" => (some (0xB04 : (BitVec 12)))
  | "mhpmcounter5" => (some (0xB05 : (BitVec 12)))
  | "mhpmcounter6" => (some (0xB06 : (BitVec 12)))
  | "mhpmcounter7" => (some (0xB07 : (BitVec 12)))
  | "mhpmcounter8" => (some (0xB08 : (BitVec 12)))
  | "mhpmcounter9" => (some (0xB09 : (BitVec 12)))
  | "mhpmcounter10" => (some (0xB0A : (BitVec 12)))
  | "mhpmcounter11" => (some (0xB0B : (BitVec 12)))
  | "mhpmcounter12" => (some (0xB0C : (BitVec 12)))
  | "mhpmcounter13" => (some (0xB0D : (BitVec 12)))
  | "mhpmcounter14" => (some (0xB0E : (BitVec 12)))
  | "mhpmcounter15" => (some (0xB0F : (BitVec 12)))
  | "mhpmcounter16" => (some (0xB10 : (BitVec 12)))
  | "mhpmcounter17" => (some (0xB11 : (BitVec 12)))
  | "mhpmcounter18" => (some (0xB12 : (BitVec 12)))
  | "mhpmcounter19" => (some (0xB13 : (BitVec 12)))
  | "mhpmcounter20" => (some (0xB14 : (BitVec 12)))
  | "mhpmcounter21" => (some (0xB15 : (BitVec 12)))
  | "mhpmcounter22" => (some (0xB16 : (BitVec 12)))
  | "mhpmcounter23" => (some (0xB17 : (BitVec 12)))
  | "mhpmcounter24" => (some (0xB18 : (BitVec 12)))
  | "mhpmcounter25" => (some (0xB19 : (BitVec 12)))
  | "mhpmcounter26" => (some (0xB1A : (BitVec 12)))
  | "mhpmcounter27" => (some (0xB1B : (BitVec 12)))
  | "mhpmcounter28" => (some (0xB1C : (BitVec 12)))
  | "mhpmcounter29" => (some (0xB1D : (BitVec 12)))
  | "mhpmcounter30" => (some (0xB1E : (BitVec 12)))
  | "mhpmcounter31" => (some (0xB1F : (BitVec 12)))
  | "mhpmcounter3h" => (some (0xB83 : (BitVec 12)))
  | "mhpmcounter4h" => (some (0xB84 : (BitVec 12)))
  | "mhpmcounter5h" => (some (0xB85 : (BitVec 12)))
  | "mhpmcounter6h" => (some (0xB86 : (BitVec 12)))
  | "mhpmcounter7h" => (some (0xB87 : (BitVec 12)))
  | "mhpmcounter8h" => (some (0xB88 : (BitVec 12)))
  | "mhpmcounter9h" => (some (0xB89 : (BitVec 12)))
  | "mhpmcounter10h" => (some (0xB8A : (BitVec 12)))
  | "mhpmcounter11h" => (some (0xB8B : (BitVec 12)))
  | "mhpmcounter12h" => (some (0xB8C : (BitVec 12)))
  | "mhpmcounter13h" => (some (0xB8D : (BitVec 12)))
  | "mhpmcounter14h" => (some (0xB8E : (BitVec 12)))
  | "mhpmcounter15h" => (some (0xB8F : (BitVec 12)))
  | "mhpmcounter16h" => (some (0xB90 : (BitVec 12)))
  | "mhpmcounter17h" => (some (0xB91 : (BitVec 12)))
  | "mhpmcounter18h" => (some (0xB92 : (BitVec 12)))
  | "mhpmcounter19h" => (some (0xB93 : (BitVec 12)))
  | "mhpmcounter20h" => (some (0xB94 : (BitVec 12)))
  | "mhpmcounter21h" => (some (0xB95 : (BitVec 12)))
  | "mhpmcounter22h" => (some (0xB96 : (BitVec 12)))
  | "mhpmcounter23h" => (some (0xB97 : (BitVec 12)))
  | "mhpmcounter24h" => (some (0xB98 : (BitVec 12)))
  | "mhpmcounter25h" => (some (0xB99 : (BitVec 12)))
  | "mhpmcounter26h" => (some (0xB9A : (BitVec 12)))
  | "mhpmcounter27h" => (some (0xB9B : (BitVec 12)))
  | "mhpmcounter28h" => (some (0xB9C : (BitVec 12)))
  | "mhpmcounter29h" => (some (0xB9D : (BitVec 12)))
  | "mhpmcounter30h" => (some (0xB9E : (BitVec 12)))
  | "mhpmcounter31h" => (some (0xB9F : (BitVec 12)))
  | "mhpmcounter3h" => (some (0xB83 : (BitVec 12)))
  | "mhpmcounter4h" => (some (0xB84 : (BitVec 12)))
  | "mhpmcounter5h" => (some (0xB85 : (BitVec 12)))
  | "mhpmcounter6h" => (some (0xB86 : (BitVec 12)))
  | "mhpmcounter7h" => (some (0xB87 : (BitVec 12)))
  | "mhpmcounter8h" => (some (0xB88 : (BitVec 12)))
  | "mhpmcounter9h" => (some (0xB89 : (BitVec 12)))
  | "mhpmcounter10h" => (some (0xB8A : (BitVec 12)))
  | "mhpmcounter11h" => (some (0xB8B : (BitVec 12)))
  | "mhpmcounter12h" => (some (0xB8C : (BitVec 12)))
  | "mhpmcounter13h" => (some (0xB8D : (BitVec 12)))
  | "mhpmcounter14h" => (some (0xB8E : (BitVec 12)))
  | "mhpmcounter15h" => (some (0xB8F : (BitVec 12)))
  | "mhpmcounter16h" => (some (0xB90 : (BitVec 12)))
  | "mhpmcounter17h" => (some (0xB91 : (BitVec 12)))
  | "mhpmcounter18h" => (some (0xB92 : (BitVec 12)))
  | "mhpmcounter19h" => (some (0xB93 : (BitVec 12)))
  | "mhpmcounter20h" => (some (0xB94 : (BitVec 12)))
  | "mhpmcounter21h" => (some (0xB95 : (BitVec 12)))
  | "mhpmcounter22h" => (some (0xB96 : (BitVec 12)))
  | "mhpmcounter23h" => (some (0xB97 : (BitVec 12)))
  | "mhpmcounter24h" => (some (0xB98 : (BitVec 12)))
  | "mhpmcounter25h" => (some (0xB99 : (BitVec 12)))
  | "mhpmcounter26h" => (some (0xB9A : (BitVec 12)))
  | "mhpmcounter27h" => (some (0xB9B : (BitVec 12)))
  | "mhpmcounter28h" => (some (0xB9C : (BitVec 12)))
  | "mhpmcounter29h" => (some (0xB9D : (BitVec 12)))
  | "mhpmcounter30h" => (some (0xB9E : (BitVec 12)))
  | "mhpmcounter31h" => (some (0xB9F : (BitVec 12)))
  | "pmpcfg0" => (some (0x3A0 : (BitVec 12)))
  | "pmpcfg1" => (some (0x3A1 : (BitVec 12)))
  | "pmpcfg2" => (some (0x3A2 : (BitVec 12)))
  | "pmpcfg3" => (some (0x3A3 : (BitVec 12)))
  | "pmpcfg4" => (some (0x3A4 : (BitVec 12)))
  | "pmpcfg5" => (some (0x3A5 : (BitVec 12)))
  | "pmpcfg6" => (some (0x3A6 : (BitVec 12)))
  | "pmpcfg7" => (some (0x3A7 : (BitVec 12)))
  | "pmpcfg8" => (some (0x3A8 : (BitVec 12)))
  | "pmpcfg9" => (some (0x3A9 : (BitVec 12)))
  | "pmpcfg10" => (some (0x3AA : (BitVec 12)))
  | "pmpcfg11" => (some (0x3AB : (BitVec 12)))
  | "pmpcfg12" => (some (0x3AC : (BitVec 12)))
  | "pmpcfg13" => (some (0x3AD : (BitVec 12)))
  | "pmpcfg14" => (some (0x3AE : (BitVec 12)))
  | "pmpcfg15" => (some (0x3AF : (BitVec 12)))
  | "pmpaddr0" => (some (0x3B0 : (BitVec 12)))
  | "pmpaddr1" => (some (0x3B1 : (BitVec 12)))
  | "pmpaddr2" => (some (0x3B2 : (BitVec 12)))
  | "pmpaddr3" => (some (0x3B3 : (BitVec 12)))
  | "pmpaddr4" => (some (0x3B4 : (BitVec 12)))
  | "pmpaddr5" => (some (0x3B5 : (BitVec 12)))
  | "pmpaddr6" => (some (0x3B6 : (BitVec 12)))
  | "pmpaddr7" => (some (0x3B7 : (BitVec 12)))
  | "pmpaddr8" => (some (0x3B8 : (BitVec 12)))
  | "pmpaddr9" => (some (0x3B9 : (BitVec 12)))
  | "pmpaddr10" => (some (0x3BA : (BitVec 12)))
  | "pmpaddr11" => (some (0x3BB : (BitVec 12)))
  | "pmpaddr12" => (some (0x3BC : (BitVec 12)))
  | "pmpaddr13" => (some (0x3BD : (BitVec 12)))
  | "pmpaddr14" => (some (0x3BE : (BitVec 12)))
  | "pmpaddr15" => (some (0x3BF : (BitVec 12)))
  | "pmpaddr16" => (some (0x3C0 : (BitVec 12)))
  | "pmpaddr17" => (some (0x3C1 : (BitVec 12)))
  | "pmpaddr18" => (some (0x3C2 : (BitVec 12)))
  | "pmpaddr19" => (some (0x3C3 : (BitVec 12)))
  | "pmpaddr20" => (some (0x3C4 : (BitVec 12)))
  | "pmpaddr21" => (some (0x3C5 : (BitVec 12)))
  | "pmpaddr22" => (some (0x3C6 : (BitVec 12)))
  | "pmpaddr23" => (some (0x3C7 : (BitVec 12)))
  | "pmpaddr24" => (some (0x3C8 : (BitVec 12)))
  | "pmpaddr25" => (some (0x3C9 : (BitVec 12)))
  | "pmpaddr26" => (some (0x3CA : (BitVec 12)))
  | "pmpaddr27" => (some (0x3CB : (BitVec 12)))
  | "pmpaddr28" => (some (0x3CC : (BitVec 12)))
  | "pmpaddr29" => (some (0x3CD : (BitVec 12)))
  | "pmpaddr30" => (some (0x3CE : (BitVec 12)))
  | "pmpaddr31" => (some (0x3CF : (BitVec 12)))
  | "pmpaddr32" => (some (0x3D0 : (BitVec 12)))
  | "pmpaddr33" => (some (0x3D1 : (BitVec 12)))
  | "pmpaddr34" => (some (0x3D2 : (BitVec 12)))
  | "pmpaddr35" => (some (0x3D3 : (BitVec 12)))
  | "pmpaddr36" => (some (0x3D4 : (BitVec 12)))
  | "pmpaddr37" => (some (0x3D5 : (BitVec 12)))
  | "pmpaddr38" => (some (0x3D6 : (BitVec 12)))
  | "pmpaddr39" => (some (0x3D7 : (BitVec 12)))
  | "pmpaddr40" => (some (0x3D8 : (BitVec 12)))
  | "pmpaddr41" => (some (0x3D9 : (BitVec 12)))
  | "pmpaddr42" => (some (0x3DA : (BitVec 12)))
  | "pmpaddr43" => (some (0x3DB : (BitVec 12)))
  | "pmpaddr44" => (some (0x3DC : (BitVec 12)))
  | "pmpaddr45" => (some (0x3DD : (BitVec 12)))
  | "pmpaddr46" => (some (0x3DE : (BitVec 12)))
  | "pmpaddr47" => (some (0x3DF : (BitVec 12)))
  | "pmpaddr48" => (some (0x3E0 : (BitVec 12)))
  | "pmpaddr49" => (some (0x3E1 : (BitVec 12)))
  | "pmpaddr50" => (some (0x3E2 : (BitVec 12)))
  | "pmpaddr51" => (some (0x3E3 : (BitVec 12)))
  | "pmpaddr52" => (some (0x3E4 : (BitVec 12)))
  | "pmpaddr53" => (some (0x3E5 : (BitVec 12)))
  | "pmpaddr54" => (some (0x3E6 : (BitVec 12)))
  | "pmpaddr55" => (some (0x3E7 : (BitVec 12)))
  | "pmpaddr56" => (some (0x3E8 : (BitVec 12)))
  | "pmpaddr57" => (some (0x3E9 : (BitVec 12)))
  | "pmpaddr58" => (some (0x3EA : (BitVec 12)))
  | "pmpaddr59" => (some (0x3EB : (BitVec 12)))
  | "pmpaddr60" => (some (0x3EC : (BitVec 12)))
  | "pmpaddr61" => (some (0x3ED : (BitVec 12)))
  | "pmpaddr62" => (some (0x3EE : (BitVec 12)))
  | "pmpaddr63" => (some (0x3EF : (BitVec 12)))
  | "mcyclecfg" => (some (0x321 : (BitVec 12)))
  | "mcyclecfgh" => (some (0x721 : (BitVec 12)))
  | "minstretcfg" => (some (0x322 : (BitVec 12)))
  | "minstretcfgh" => (some (0x722 : (BitVec 12)))
  | "seed" => (some (0x015 : (BitVec 12)))
  | "vstart" => (some (0x008 : (BitVec 12)))
  | "vxsat" => (some (0x009 : (BitVec 12)))
  | "vxrm" => (some (0x00A : (BitVec 12)))
  | "vcsr" => (some (0x00F : (BitVec 12)))
  | "fflags" => (some (0x001 : (BitVec 12)))
  | "frm" => (some (0x002 : (BitVec 12)))
  | "fcsr" => (some (0x003 : (BitVec 12)))
  | "stvec" => (some (0x105 : (BitVec 12)))
  | "sepc" => (some (0x141 : (BitVec 12)))
  | "mtvec" => (some (0x305 : (BitVec 12)))
  | "mepc" => (some (0x341 : (BitVec 12)))
  | "cycle" => (some (0xC00 : (BitVec 12)))
  | "time" => (some (0xC01 : (BitVec 12)))
  | "instret" => (some (0xC02 : (BitVec 12)))
  | "cycleh" => (some (0xC80 : (BitVec 12)))
  | "menvcfg" => (some (0x30A : (BitVec 12)))
  | "menvcfgh" => (some (0x31A : (BitVec 12)))
  | "mtval" => (some (0x343 : (BitVec 12)))
  | "mscratch" => (some (0x340 : (BitVec 12)))
  | "satp" => (some (0x180 : (BitVec 12)))
  | mapping0_ =>
    (if (hex_bits_12_backwards_matches mapping0_)
    then
      (match (hex_bits_12_backwards mapping0_) with
      | reg => (some reg)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def csr_name_map_forwards_matches (arg_ : (BitVec 12)) : Bool :=
  match_bv arg_ with
  | 000101001101 => true
  | 000101011101 => true
  | 110000000011 => true
  | 110000000100 => true
  | 110000000101 => true
  | 110000000110 => true
  | 110000000111 => true
  | 110000001000 => true
  | 110000001001 => true
  | 110000001010 => true
  | 110000001011 => true
  | 110000001100 => true
  | 110000001101 => true
  | 110000001110 => true
  | 110000001111 => true
  | 110000010000 => true
  | 110000010001 => true
  | 110000010010 => true
  | 110000010011 => true
  | 110000010100 => true
  | 110000010101 => true
  | 110000010110 => true
  | 110000010111 => true
  | 110000011000 => true
  | 110000011001 => true
  | 110000011010 => true
  | 110000011011 => true
  | 110000011100 => true
  | 110000011101 => true
  | 110000011110 => true
  | 110000011111 => true
  | 110010000011 => true
  | 110010000100 => true
  | 110010000101 => true
  | 110010000110 => true
  | 110010000111 => true
  | 110010001000 => true
  | 110010001001 => true
  | 110010001010 => true
  | 110010001011 => true
  | 110010001100 => true
  | 110010001101 => true
  | 110010001110 => true
  | 110010001111 => true
  | 110010010000 => true
  | 110010010001 => true
  | 110010010010 => true
  | 110010010011 => true
  | 110010010100 => true
  | 110010010101 => true
  | 110010010110 => true
  | 110010010111 => true
  | 110010011000 => true
  | 110010011001 => true
  | 110010011010 => true
  | 110010011011 => true
  | 110010011100 => true
  | 110010011101 => true
  | 110010011110 => true
  | 110010011111 => true
  | 001100100011 => true
  | 001100100100 => true
  | 001100100101 => true
  | 001100100110 => true
  | 001100100111 => true
  | 001100101000 => true
  | 001100101001 => true
  | 001100101010 => true
  | 001100101011 => true
  | 001100101100 => true
  | 001100101101 => true
  | 001100101110 => true
  | 001100101111 => true
  | 001100110000 => true
  | 001100110001 => true
  | 001100110010 => true
  | 001100110011 => true
  | 001100110100 => true
  | 001100110101 => true
  | 001100110110 => true
  | 001100110111 => true
  | 001100111000 => true
  | 001100111001 => true
  | 001100111010 => true
  | 001100111011 => true
  | 001100111100 => true
  | 001100111101 => true
  | 001100111110 => true
  | 001100111111 => true
  | 101100000011 => true
  | 101100000100 => true
  | 101100000101 => true
  | 101100000110 => true
  | 101100000111 => true
  | 101100001000 => true
  | 101100001001 => true
  | 101100001010 => true
  | 101100001011 => true
  | 101100001100 => true
  | 101100001101 => true
  | 101100001110 => true
  | 101100001111 => true
  | 101100010000 => true
  | 101100010001 => true
  | 101100010010 => true
  | 101100010011 => true
  | 101100010100 => true
  | 101100010101 => true
  | 101100010110 => true
  | 101100010111 => true
  | 101100011000 => true
  | 101100011001 => true
  | 101100011010 => true
  | 101100011011 => true
  | 101100011100 => true
  | 101100011101 => true
  | 101100011110 => true
  | 101100011111 => true
  | 101110000011 => true
  | 101110000100 => true
  | 101110000101 => true
  | 101110000110 => true
  | 101110000111 => true
  | 101110001000 => true
  | 101110001001 => true
  | 101110001010 => true
  | 101110001011 => true
  | 101110001100 => true
  | 101110001101 => true
  | 101110001110 => true
  | 101110001111 => true
  | 101110010000 => true
  | 101110010001 => true
  | 101110010010 => true
  | 101110010011 => true
  | 101110010100 => true
  | 101110010101 => true
  | 101110010110 => true
  | 101110010111 => true
  | 101110011000 => true
  | 101110011001 => true
  | 101110011010 => true
  | 101110011011 => true
  | 101110011100 => true
  | 101110011101 => true
  | 101110011110 => true
  | 101110011111 => true
  | 101110000011 => true
  | 101110000100 => true
  | 101110000101 => true
  | 101110000110 => true
  | 101110000111 => true
  | 101110001000 => true
  | 101110001001 => true
  | 101110001010 => true
  | 101110001011 => true
  | 101110001100 => true
  | 101110001101 => true
  | 101110001110 => true
  | 101110001111 => true
  | 101110010000 => true
  | 101110010001 => true
  | 101110010010 => true
  | 101110010011 => true
  | 101110010100 => true
  | 101110010101 => true
  | 101110010110 => true
  | 101110010111 => true
  | 101110011000 => true
  | 101110011001 => true
  | 101110011010 => true
  | 101110011011 => true
  | 101110011100 => true
  | 101110011101 => true
  | 101110011110 => true
  | 101110011111 => true
  | 001110100000 => true
  | 001110100001 => true
  | 001110100010 => true
  | 001110100011 => true
  | 001110100100 => true
  | 001110100101 => true
  | 001110100110 => true
  | 001110100111 => true
  | 001110101000 => true
  | 001110101001 => true
  | 001110101010 => true
  | 001110101011 => true
  | 001110101100 => true
  | 001110101101 => true
  | 001110101110 => true
  | 001110101111 => true
  | 001110110000 => true
  | 001110110001 => true
  | 001110110010 => true
  | 001110110011 => true
  | 001110110100 => true
  | 001110110101 => true
  | 001110110110 => true
  | 001110110111 => true
  | 001110111000 => true
  | 001110111001 => true
  | 001110111010 => true
  | 001110111011 => true
  | 001110111100 => true
  | 001110111101 => true
  | 001110111110 => true
  | 001110111111 => true
  | 001111000000 => true
  | 001111000001 => true
  | 001111000010 => true
  | 001111000011 => true
  | 001111000100 => true
  | 001111000101 => true
  | 001111000110 => true
  | 001111000111 => true
  | 001111001000 => true
  | 001111001001 => true
  | 001111001010 => true
  | 001111001011 => true
  | 001111001100 => true
  | 001111001101 => true
  | 001111001110 => true
  | 001111001111 => true
  | 001111010000 => true
  | 001111010001 => true
  | 001111010010 => true
  | 001111010011 => true
  | 001111010100 => true
  | 001111010101 => true
  | 001111010110 => true
  | 001111010111 => true
  | 001111011000 => true
  | 001111011001 => true
  | 001111011010 => true
  | 001111011011 => true
  | 001111011100 => true
  | 001111011101 => true
  | 001111011110 => true
  | 001111011111 => true
  | 001111100000 => true
  | 001111100001 => true
  | 001111100010 => true
  | 001111100011 => true
  | 001111100100 => true
  | 001111100101 => true
  | 001111100110 => true
  | 001111100111 => true
  | 001111101000 => true
  | 001111101001 => true
  | 001111101010 => true
  | 001111101011 => true
  | 001111101100 => true
  | 001111101101 => true
  | 001111101110 => true
  | 001111101111 => true
  | 001100100001 => true
  | 011100100001 => true
  | 001100100010 => true
  | 011100100010 => true
  | 000000010101 => true
  | 000000001000 => true
  | 000000001001 => true
  | 000000001010 => true
  | 000000001111 => true
  | 000000000001 => true
  | 000000000010 => true
  | 000000000011 => true
  | 000100000101 => true
  | 000101000001 => true
  | 001100000101 => true
  | 001101000001 => true
  | 110000000000 => true
  | 110000000001 => true
  | 110000000010 => true
  | 110010000000 => true
  | 001100001010 => true
  | 001100011010 => true
  | 001101000011 => true
  | 001101000000 => true
  | 000110000000 => true
  | reg => true
  | _ => false

def csr_name_map_backwards_matches (arg_ : String) : Bool :=
  let head_exp_ := arg_
  match (match head_exp_ with
  | "stimecmp" => (some true)
  | "stimecmph" => (some true)
  | "hpmcounter3" => (some true)
  | "hpmcounter4" => (some true)
  | "hpmcounter5" => (some true)
  | "hpmcounter6" => (some true)
  | "hpmcounter7" => (some true)
  | "hpmcounter8" => (some true)
  | "hpmcounter9" => (some true)
  | "hpmcounter10" => (some true)
  | "hpmcounter11" => (some true)
  | "hpmcounter12" => (some true)
  | "hpmcounter13" => (some true)
  | "hpmcounter14" => (some true)
  | "hpmcounter15" => (some true)
  | "hpmcounter16" => (some true)
  | "hpmcounter17" => (some true)
  | "hpmcounter18" => (some true)
  | "hpmcounter19" => (some true)
  | "hpmcounter20" => (some true)
  | "hpmcounter21" => (some true)
  | "hpmcounter22" => (some true)
  | "hpmcounter23" => (some true)
  | "hpmcounter24" => (some true)
  | "hpmcounter25" => (some true)
  | "hpmcounter26" => (some true)
  | "hpmcounter27" => (some true)
  | "hpmcounter28" => (some true)
  | "hpmcounter29" => (some true)
  | "hpmcounter30" => (some true)
  | "hpmcounter31" => (some true)
  | "hpmcounter3h" => (some true)
  | "hpmcounter4h" => (some true)
  | "hpmcounter5h" => (some true)
  | "hpmcounter6h" => (some true)
  | "hpmcounter7h" => (some true)
  | "hpmcounter8h" => (some true)
  | "hpmcounter9h" => (some true)
  | "hpmcounter10h" => (some true)
  | "hpmcounter11h" => (some true)
  | "hpmcounter12h" => (some true)
  | "hpmcounter13h" => (some true)
  | "hpmcounter14h" => (some true)
  | "hpmcounter15h" => (some true)
  | "hpmcounter16h" => (some true)
  | "hpmcounter17h" => (some true)
  | "hpmcounter18h" => (some true)
  | "hpmcounter19h" => (some true)
  | "hpmcounter20h" => (some true)
  | "hpmcounter21h" => (some true)
  | "hpmcounter22h" => (some true)
  | "hpmcounter23h" => (some true)
  | "hpmcounter24h" => (some true)
  | "hpmcounter25h" => (some true)
  | "hpmcounter26h" => (some true)
  | "hpmcounter27h" => (some true)
  | "hpmcounter28h" => (some true)
  | "hpmcounter29h" => (some true)
  | "hpmcounter30h" => (some true)
  | "hpmcounter31h" => (some true)
  | "mhpmevent3" => (some true)
  | "mhpmevent4" => (some true)
  | "mhpmevent5" => (some true)
  | "mhpmevent6" => (some true)
  | "mhpmevent7" => (some true)
  | "mhpmevent8" => (some true)
  | "mhpmevent9" => (some true)
  | "mhpmevent10" => (some true)
  | "mhpmevent11" => (some true)
  | "mhpmevent12" => (some true)
  | "mhpmevent13" => (some true)
  | "mhpmevent14" => (some true)
  | "mhpmevent15" => (some true)
  | "mhpmevent16" => (some true)
  | "mhpmevent17" => (some true)
  | "mhpmevent18" => (some true)
  | "mhpmevent19" => (some true)
  | "mhpmevent20" => (some true)
  | "mhpmevent21" => (some true)
  | "mhpmevent22" => (some true)
  | "mhpmevent23" => (some true)
  | "mhpmevent24" => (some true)
  | "mhpmevent25" => (some true)
  | "mhpmevent26" => (some true)
  | "mhpmevent27" => (some true)
  | "mhpmevent28" => (some true)
  | "mhpmevent29" => (some true)
  | "mhpmevent30" => (some true)
  | "mhpmevent31" => (some true)
  | "mhpmcounter3" => (some true)
  | "mhpmcounter4" => (some true)
  | "mhpmcounter5" => (some true)
  | "mhpmcounter6" => (some true)
  | "mhpmcounter7" => (some true)
  | "mhpmcounter8" => (some true)
  | "mhpmcounter9" => (some true)
  | "mhpmcounter10" => (some true)
  | "mhpmcounter11" => (some true)
  | "mhpmcounter12" => (some true)
  | "mhpmcounter13" => (some true)
  | "mhpmcounter14" => (some true)
  | "mhpmcounter15" => (some true)
  | "mhpmcounter16" => (some true)
  | "mhpmcounter17" => (some true)
  | "mhpmcounter18" => (some true)
  | "mhpmcounter19" => (some true)
  | "mhpmcounter20" => (some true)
  | "mhpmcounter21" => (some true)
  | "mhpmcounter22" => (some true)
  | "mhpmcounter23" => (some true)
  | "mhpmcounter24" => (some true)
  | "mhpmcounter25" => (some true)
  | "mhpmcounter26" => (some true)
  | "mhpmcounter27" => (some true)
  | "mhpmcounter28" => (some true)
  | "mhpmcounter29" => (some true)
  | "mhpmcounter30" => (some true)
  | "mhpmcounter31" => (some true)
  | "mhpmcounter3h" => (some true)
  | "mhpmcounter4h" => (some true)
  | "mhpmcounter5h" => (some true)
  | "mhpmcounter6h" => (some true)
  | "mhpmcounter7h" => (some true)
  | "mhpmcounter8h" => (some true)
  | "mhpmcounter9h" => (some true)
  | "mhpmcounter10h" => (some true)
  | "mhpmcounter11h" => (some true)
  | "mhpmcounter12h" => (some true)
  | "mhpmcounter13h" => (some true)
  | "mhpmcounter14h" => (some true)
  | "mhpmcounter15h" => (some true)
  | "mhpmcounter16h" => (some true)
  | "mhpmcounter17h" => (some true)
  | "mhpmcounter18h" => (some true)
  | "mhpmcounter19h" => (some true)
  | "mhpmcounter20h" => (some true)
  | "mhpmcounter21h" => (some true)
  | "mhpmcounter22h" => (some true)
  | "mhpmcounter23h" => (some true)
  | "mhpmcounter24h" => (some true)
  | "mhpmcounter25h" => (some true)
  | "mhpmcounter26h" => (some true)
  | "mhpmcounter27h" => (some true)
  | "mhpmcounter28h" => (some true)
  | "mhpmcounter29h" => (some true)
  | "mhpmcounter30h" => (some true)
  | "mhpmcounter31h" => (some true)
  | "mhpmcounter3h" => (some true)
  | "mhpmcounter4h" => (some true)
  | "mhpmcounter5h" => (some true)
  | "mhpmcounter6h" => (some true)
  | "mhpmcounter7h" => (some true)
  | "mhpmcounter8h" => (some true)
  | "mhpmcounter9h" => (some true)
  | "mhpmcounter10h" => (some true)
  | "mhpmcounter11h" => (some true)
  | "mhpmcounter12h" => (some true)
  | "mhpmcounter13h" => (some true)
  | "mhpmcounter14h" => (some true)
  | "mhpmcounter15h" => (some true)
  | "mhpmcounter16h" => (some true)
  | "mhpmcounter17h" => (some true)
  | "mhpmcounter18h" => (some true)
  | "mhpmcounter19h" => (some true)
  | "mhpmcounter20h" => (some true)
  | "mhpmcounter21h" => (some true)
  | "mhpmcounter22h" => (some true)
  | "mhpmcounter23h" => (some true)
  | "mhpmcounter24h" => (some true)
  | "mhpmcounter25h" => (some true)
  | "mhpmcounter26h" => (some true)
  | "mhpmcounter27h" => (some true)
  | "mhpmcounter28h" => (some true)
  | "mhpmcounter29h" => (some true)
  | "mhpmcounter30h" => (some true)
  | "mhpmcounter31h" => (some true)
  | "pmpcfg0" => (some true)
  | "pmpcfg1" => (some true)
  | "pmpcfg2" => (some true)
  | "pmpcfg3" => (some true)
  | "pmpcfg4" => (some true)
  | "pmpcfg5" => (some true)
  | "pmpcfg6" => (some true)
  | "pmpcfg7" => (some true)
  | "pmpcfg8" => (some true)
  | "pmpcfg9" => (some true)
  | "pmpcfg10" => (some true)
  | "pmpcfg11" => (some true)
  | "pmpcfg12" => (some true)
  | "pmpcfg13" => (some true)
  | "pmpcfg14" => (some true)
  | "pmpcfg15" => (some true)
  | "pmpaddr0" => (some true)
  | "pmpaddr1" => (some true)
  | "pmpaddr2" => (some true)
  | "pmpaddr3" => (some true)
  | "pmpaddr4" => (some true)
  | "pmpaddr5" => (some true)
  | "pmpaddr6" => (some true)
  | "pmpaddr7" => (some true)
  | "pmpaddr8" => (some true)
  | "pmpaddr9" => (some true)
  | "pmpaddr10" => (some true)
  | "pmpaddr11" => (some true)
  | "pmpaddr12" => (some true)
  | "pmpaddr13" => (some true)
  | "pmpaddr14" => (some true)
  | "pmpaddr15" => (some true)
  | "pmpaddr16" => (some true)
  | "pmpaddr17" => (some true)
  | "pmpaddr18" => (some true)
  | "pmpaddr19" => (some true)
  | "pmpaddr20" => (some true)
  | "pmpaddr21" => (some true)
  | "pmpaddr22" => (some true)
  | "pmpaddr23" => (some true)
  | "pmpaddr24" => (some true)
  | "pmpaddr25" => (some true)
  | "pmpaddr26" => (some true)
  | "pmpaddr27" => (some true)
  | "pmpaddr28" => (some true)
  | "pmpaddr29" => (some true)
  | "pmpaddr30" => (some true)
  | "pmpaddr31" => (some true)
  | "pmpaddr32" => (some true)
  | "pmpaddr33" => (some true)
  | "pmpaddr34" => (some true)
  | "pmpaddr35" => (some true)
  | "pmpaddr36" => (some true)
  | "pmpaddr37" => (some true)
  | "pmpaddr38" => (some true)
  | "pmpaddr39" => (some true)
  | "pmpaddr40" => (some true)
  | "pmpaddr41" => (some true)
  | "pmpaddr42" => (some true)
  | "pmpaddr43" => (some true)
  | "pmpaddr44" => (some true)
  | "pmpaddr45" => (some true)
  | "pmpaddr46" => (some true)
  | "pmpaddr47" => (some true)
  | "pmpaddr48" => (some true)
  | "pmpaddr49" => (some true)
  | "pmpaddr50" => (some true)
  | "pmpaddr51" => (some true)
  | "pmpaddr52" => (some true)
  | "pmpaddr53" => (some true)
  | "pmpaddr54" => (some true)
  | "pmpaddr55" => (some true)
  | "pmpaddr56" => (some true)
  | "pmpaddr57" => (some true)
  | "pmpaddr58" => (some true)
  | "pmpaddr59" => (some true)
  | "pmpaddr60" => (some true)
  | "pmpaddr61" => (some true)
  | "pmpaddr62" => (some true)
  | "pmpaddr63" => (some true)
  | "mcyclecfg" => (some true)
  | "mcyclecfgh" => (some true)
  | "minstretcfg" => (some true)
  | "minstretcfgh" => (some true)
  | "seed" => (some true)
  | "vstart" => (some true)
  | "vxsat" => (some true)
  | "vxrm" => (some true)
  | "vcsr" => (some true)
  | "fflags" => (some true)
  | "frm" => (some true)
  | "fcsr" => (some true)
  | "stvec" => (some true)
  | "sepc" => (some true)
  | "mtvec" => (some true)
  | "mepc" => (some true)
  | "cycle" => (some true)
  | "time" => (some true)
  | "instret" => (some true)
  | "cycleh" => (some true)
  | "menvcfg" => (some true)
  | "menvcfgh" => (some true)
  | "mtval" => (some true)
  | "mscratch" => (some true)
  | "satp" => (some true)
  | mapping0_ =>
    (if (hex_bits_12_backwards_matches mapping0_)
    then
      (match (hex_bits_12_backwards mapping0_) with
      | reg => (some true)
      | _ => none)
    else none)) with
  | .some result => result
  | none =>
    (match head_exp_ with
    | _ => false)

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

end Out.Functions
