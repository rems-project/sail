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

open option

/-- Type quantifiers: k_ex2049_ : Bool, k_ex2048_ : Bool -/
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

/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def hex_bits_forwards (bv : (BitVec k_n)) : (Nat × String) :=
  ((Sail.BitVec.length bv), (Int.toHex (BitVec.toNatInt bv)))

/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def hex_bits_forwards_matches (x_0 : (BitVec k_n)) : Bool :=
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

def hex_bits_1_forwards_matches (arg_ : (BitVec 1)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (1, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_3_forwards_matches (arg_ : (BitVec 3)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (3, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_4_forwards_matches (arg_ : (BitVec 4)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (4, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_5_forwards_matches (arg_ : (BitVec 5)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (5, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_6_forwards_matches (arg_ : (BitVec 6)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (6, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_7_forwards_matches (arg_ : (BitVec 7)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (7, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_8_forwards_matches (arg_ : (BitVec 8)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (8, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_9_forwards_matches (arg_ : (BitVec 9)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (9, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_10_forwards_matches (arg_ : (BitVec 10)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (10, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_11_forwards_matches (arg_ : (BitVec 11)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (11, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_12_forwards_matches (arg_ : (BitVec 12)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (12, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_13_forwards_matches (arg_ : (BitVec 13)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (13, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_14_forwards_matches (arg_ : (BitVec 14)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (14, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_15_forwards_matches (arg_ : (BitVec 15)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (15, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_16_forwards_matches (arg_ : (BitVec 16)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (16, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_17_forwards_matches (arg_ : (BitVec 17)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (17, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_18_forwards_matches (arg_ : (BitVec 18)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (18, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_19_forwards_matches (arg_ : (BitVec 19)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (19, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_20_forwards_matches (arg_ : (BitVec 20)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (20, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_21_forwards_matches (arg_ : (BitVec 21)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (21, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_22_forwards_matches (arg_ : (BitVec 22)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (22, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_23_forwards_matches (arg_ : (BitVec 23)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (23, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_24_forwards_matches (arg_ : (BitVec 24)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (24, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_25_forwards_matches (arg_ : (BitVec 25)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (25, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_26_forwards_matches (arg_ : (BitVec 26)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (26, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_27_forwards_matches (arg_ : (BitVec 27)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (27, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_28_forwards_matches (arg_ : (BitVec 28)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (28, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_29_forwards_matches (arg_ : (BitVec 29)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (29, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_30_forwards_matches (arg_ : (BitVec 30)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (30, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_31_forwards_matches (arg_ : (BitVec 31)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (31, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_32_forwards_matches (arg_ : (BitVec 32)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (32, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_33_forwards_matches (arg_ : (BitVec 33)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (33, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_34_forwards_matches (arg_ : (BitVec 34)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (34, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_35_forwards_matches (arg_ : (BitVec 35)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (35, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_36_forwards_matches (arg_ : (BitVec 36)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (36, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_37_forwards_matches (arg_ : (BitVec 37)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (37, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_38_forwards_matches (arg_ : (BitVec 38)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (38, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_39_forwards_matches (arg_ : (BitVec 39)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (39, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_40_forwards_matches (arg_ : (BitVec 40)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (40, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_41_forwards_matches (arg_ : (BitVec 41)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (41, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_42_forwards_matches (arg_ : (BitVec 42)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (42, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_43_forwards_matches (arg_ : (BitVec 43)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (43, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_44_forwards_matches (arg_ : (BitVec 44)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (44, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_45_forwards_matches (arg_ : (BitVec 45)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (45, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_46_forwards_matches (arg_ : (BitVec 46)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (46, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_47_forwards_matches (arg_ : (BitVec 47)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (47, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_48_forwards_matches (arg_ : (BitVec 48)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (48, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_49_forwards_matches (arg_ : (BitVec 49)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (49, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_50_forwards_matches (arg_ : (BitVec 50)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (50, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_51_forwards_matches (arg_ : (BitVec 51)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (51, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_52_forwards_matches (arg_ : (BitVec 52)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (52, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_53_forwards_matches (arg_ : (BitVec 53)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (53, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_54_forwards_matches (arg_ : (BitVec 54)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (54, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_55_forwards_matches (arg_ : (BitVec 55)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (55, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_56_forwards_matches (arg_ : (BitVec 56)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (56, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_57_forwards_matches (arg_ : (BitVec 57)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (57, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_58_forwards_matches (arg_ : (BitVec 58)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (58, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_59_forwards_matches (arg_ : (BitVec 59)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (59, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_60_forwards_matches (arg_ : (BitVec 60)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (60, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_61_forwards_matches (arg_ : (BitVec 61)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (61, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_62_forwards_matches (arg_ : (BitVec 62)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (62, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_63_forwards_matches (arg_ : (BitVec 63)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (63, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

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

def hex_bits_64_forwards_matches (arg_ : (BitVec 64)) : SailM Bool := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | mapping0_ =>
    (match (hex_bits_forwards mapping0_) with
    | (64, s) => (some true)
    | _ => none)
  | _ => none) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def hex_bits_64_backwards_matches (arg_ : String) : Bool :=
  match arg_ with
  | s => true
  | _ => false

def csr_name_map_forwards (arg_ : (BitVec 12)) : SailM String := do
  match arg_ with
  | 0x14D => (pure "stimecmp")
  | 0x15D => (pure "stimecmph")
  | 0xC03 => (pure "hpmcounter3")
  | 0xC04 => (pure "hpmcounter4")
  | 0xC05 => (pure "hpmcounter5")
  | 0xC06 => (pure "hpmcounter6")
  | 0xC07 => (pure "hpmcounter7")
  | 0xC08 => (pure "hpmcounter8")
  | 0xC09 => (pure "hpmcounter9")
  | 0xC0A => (pure "hpmcounter10")
  | 0xC0B => (pure "hpmcounter11")
  | 0xC0C => (pure "hpmcounter12")
  | 0xC0D => (pure "hpmcounter13")
  | 0xC0E => (pure "hpmcounter14")
  | 0xC0F => (pure "hpmcounter15")
  | 0xC10 => (pure "hpmcounter16")
  | 0xC11 => (pure "hpmcounter17")
  | 0xC12 => (pure "hpmcounter18")
  | 0xC13 => (pure "hpmcounter19")
  | 0xC14 => (pure "hpmcounter20")
  | 0xC15 => (pure "hpmcounter21")
  | 0xC16 => (pure "hpmcounter22")
  | 0xC17 => (pure "hpmcounter23")
  | 0xC18 => (pure "hpmcounter24")
  | 0xC19 => (pure "hpmcounter25")
  | 0xC1A => (pure "hpmcounter26")
  | 0xC1B => (pure "hpmcounter27")
  | 0xC1C => (pure "hpmcounter28")
  | 0xC1D => (pure "hpmcounter29")
  | 0xC1E => (pure "hpmcounter30")
  | 0xC1F => (pure "hpmcounter31")
  | 0xC83 => (pure "hpmcounter3h")
  | 0xC84 => (pure "hpmcounter4h")
  | 0xC85 => (pure "hpmcounter5h")
  | 0xC86 => (pure "hpmcounter6h")
  | 0xC87 => (pure "hpmcounter7h")
  | 0xC88 => (pure "hpmcounter8h")
  | 0xC89 => (pure "hpmcounter9h")
  | 0xC8A => (pure "hpmcounter10h")
  | 0xC8B => (pure "hpmcounter11h")
  | 0xC8C => (pure "hpmcounter12h")
  | 0xC8D => (pure "hpmcounter13h")
  | 0xC8E => (pure "hpmcounter14h")
  | 0xC8F => (pure "hpmcounter15h")
  | 0xC90 => (pure "hpmcounter16h")
  | 0xC91 => (pure "hpmcounter17h")
  | 0xC92 => (pure "hpmcounter18h")
  | 0xC93 => (pure "hpmcounter19h")
  | 0xC94 => (pure "hpmcounter20h")
  | 0xC95 => (pure "hpmcounter21h")
  | 0xC96 => (pure "hpmcounter22h")
  | 0xC97 => (pure "hpmcounter23h")
  | 0xC98 => (pure "hpmcounter24h")
  | 0xC99 => (pure "hpmcounter25h")
  | 0xC9A => (pure "hpmcounter26h")
  | 0xC9B => (pure "hpmcounter27h")
  | 0xC9C => (pure "hpmcounter28h")
  | 0xC9D => (pure "hpmcounter29h")
  | 0xC9E => (pure "hpmcounter30h")
  | 0xC9F => (pure "hpmcounter31h")
  | 0x323 => (pure "mhpmevent3")
  | 0x324 => (pure "mhpmevent4")
  | 0x325 => (pure "mhpmevent5")
  | 0x326 => (pure "mhpmevent6")
  | 0x327 => (pure "mhpmevent7")
  | 0x328 => (pure "mhpmevent8")
  | 0x329 => (pure "mhpmevent9")
  | 0x32A => (pure "mhpmevent10")
  | 0x32B => (pure "mhpmevent11")
  | 0x32C => (pure "mhpmevent12")
  | 0x32D => (pure "mhpmevent13")
  | 0x32E => (pure "mhpmevent14")
  | 0x32F => (pure "mhpmevent15")
  | 0x330 => (pure "mhpmevent16")
  | 0x331 => (pure "mhpmevent17")
  | 0x332 => (pure "mhpmevent18")
  | 0x333 => (pure "mhpmevent19")
  | 0x334 => (pure "mhpmevent20")
  | 0x335 => (pure "mhpmevent21")
  | 0x336 => (pure "mhpmevent22")
  | 0x337 => (pure "mhpmevent23")
  | 0x338 => (pure "mhpmevent24")
  | 0x339 => (pure "mhpmevent25")
  | 0x33A => (pure "mhpmevent26")
  | 0x33B => (pure "mhpmevent27")
  | 0x33C => (pure "mhpmevent28")
  | 0x33D => (pure "mhpmevent29")
  | 0x33E => (pure "mhpmevent30")
  | 0x33F => (pure "mhpmevent31")
  | 0xB03 => (pure "mhpmcounter3")
  | 0xB04 => (pure "mhpmcounter4")
  | 0xB05 => (pure "mhpmcounter5")
  | 0xB06 => (pure "mhpmcounter6")
  | 0xB07 => (pure "mhpmcounter7")
  | 0xB08 => (pure "mhpmcounter8")
  | 0xB09 => (pure "mhpmcounter9")
  | 0xB0A => (pure "mhpmcounter10")
  | 0xB0B => (pure "mhpmcounter11")
  | 0xB0C => (pure "mhpmcounter12")
  | 0xB0D => (pure "mhpmcounter13")
  | 0xB0E => (pure "mhpmcounter14")
  | 0xB0F => (pure "mhpmcounter15")
  | 0xB10 => (pure "mhpmcounter16")
  | 0xB11 => (pure "mhpmcounter17")
  | 0xB12 => (pure "mhpmcounter18")
  | 0xB13 => (pure "mhpmcounter19")
  | 0xB14 => (pure "mhpmcounter20")
  | 0xB15 => (pure "mhpmcounter21")
  | 0xB16 => (pure "mhpmcounter22")
  | 0xB17 => (pure "mhpmcounter23")
  | 0xB18 => (pure "mhpmcounter24")
  | 0xB19 => (pure "mhpmcounter25")
  | 0xB1A => (pure "mhpmcounter26")
  | 0xB1B => (pure "mhpmcounter27")
  | 0xB1C => (pure "mhpmcounter28")
  | 0xB1D => (pure "mhpmcounter29")
  | 0xB1E => (pure "mhpmcounter30")
  | 0xB1F => (pure "mhpmcounter31")
  | 0xB83 => (pure "mhpmcounter3h")
  | 0xB84 => (pure "mhpmcounter4h")
  | 0xB85 => (pure "mhpmcounter5h")
  | 0xB86 => (pure "mhpmcounter6h")
  | 0xB87 => (pure "mhpmcounter7h")
  | 0xB88 => (pure "mhpmcounter8h")
  | 0xB89 => (pure "mhpmcounter9h")
  | 0xB8A => (pure "mhpmcounter10h")
  | 0xB8B => (pure "mhpmcounter11h")
  | 0xB8C => (pure "mhpmcounter12h")
  | 0xB8D => (pure "mhpmcounter13h")
  | 0xB8E => (pure "mhpmcounter14h")
  | 0xB8F => (pure "mhpmcounter15h")
  | 0xB90 => (pure "mhpmcounter16h")
  | 0xB91 => (pure "mhpmcounter17h")
  | 0xB92 => (pure "mhpmcounter18h")
  | 0xB93 => (pure "mhpmcounter19h")
  | 0xB94 => (pure "mhpmcounter20h")
  | 0xB95 => (pure "mhpmcounter21h")
  | 0xB96 => (pure "mhpmcounter22h")
  | 0xB97 => (pure "mhpmcounter23h")
  | 0xB98 => (pure "mhpmcounter24h")
  | 0xB99 => (pure "mhpmcounter25h")
  | 0xB9A => (pure "mhpmcounter26h")
  | 0xB9B => (pure "mhpmcounter27h")
  | 0xB9C => (pure "mhpmcounter28h")
  | 0xB9D => (pure "mhpmcounter29h")
  | 0xB9E => (pure "mhpmcounter30h")
  | 0xB9F => (pure "mhpmcounter31h")
  | 0xB83 => (pure "mhpmcounter3h")
  | 0xB84 => (pure "mhpmcounter4h")
  | 0xB85 => (pure "mhpmcounter5h")
  | 0xB86 => (pure "mhpmcounter6h")
  | 0xB87 => (pure "mhpmcounter7h")
  | 0xB88 => (pure "mhpmcounter8h")
  | 0xB89 => (pure "mhpmcounter9h")
  | 0xB8A => (pure "mhpmcounter10h")
  | 0xB8B => (pure "mhpmcounter11h")
  | 0xB8C => (pure "mhpmcounter12h")
  | 0xB8D => (pure "mhpmcounter13h")
  | 0xB8E => (pure "mhpmcounter14h")
  | 0xB8F => (pure "mhpmcounter15h")
  | 0xB90 => (pure "mhpmcounter16h")
  | 0xB91 => (pure "mhpmcounter17h")
  | 0xB92 => (pure "mhpmcounter18h")
  | 0xB93 => (pure "mhpmcounter19h")
  | 0xB94 => (pure "mhpmcounter20h")
  | 0xB95 => (pure "mhpmcounter21h")
  | 0xB96 => (pure "mhpmcounter22h")
  | 0xB97 => (pure "mhpmcounter23h")
  | 0xB98 => (pure "mhpmcounter24h")
  | 0xB99 => (pure "mhpmcounter25h")
  | 0xB9A => (pure "mhpmcounter26h")
  | 0xB9B => (pure "mhpmcounter27h")
  | 0xB9C => (pure "mhpmcounter28h")
  | 0xB9D => (pure "mhpmcounter29h")
  | 0xB9E => (pure "mhpmcounter30h")
  | 0xB9F => (pure "mhpmcounter31h")
  | 0x3A0 => (pure "pmpcfg0")
  | 0x3A1 => (pure "pmpcfg1")
  | 0x3A2 => (pure "pmpcfg2")
  | 0x3A3 => (pure "pmpcfg3")
  | 0x3A4 => (pure "pmpcfg4")
  | 0x3A5 => (pure "pmpcfg5")
  | 0x3A6 => (pure "pmpcfg6")
  | 0x3A7 => (pure "pmpcfg7")
  | 0x3A8 => (pure "pmpcfg8")
  | 0x3A9 => (pure "pmpcfg9")
  | 0x3AA => (pure "pmpcfg10")
  | 0x3AB => (pure "pmpcfg11")
  | 0x3AC => (pure "pmpcfg12")
  | 0x3AD => (pure "pmpcfg13")
  | 0x3AE => (pure "pmpcfg14")
  | 0x3AF => (pure "pmpcfg15")
  | 0x3B0 => (pure "pmpaddr0")
  | 0x3B1 => (pure "pmpaddr1")
  | 0x3B2 => (pure "pmpaddr2")
  | 0x3B3 => (pure "pmpaddr3")
  | 0x3B4 => (pure "pmpaddr4")
  | 0x3B5 => (pure "pmpaddr5")
  | 0x3B6 => (pure "pmpaddr6")
  | 0x3B7 => (pure "pmpaddr7")
  | 0x3B8 => (pure "pmpaddr8")
  | 0x3B9 => (pure "pmpaddr9")
  | 0x3BA => (pure "pmpaddr10")
  | 0x3BB => (pure "pmpaddr11")
  | 0x3BC => (pure "pmpaddr12")
  | 0x3BD => (pure "pmpaddr13")
  | 0x3BE => (pure "pmpaddr14")
  | 0x3BF => (pure "pmpaddr15")
  | 0x3C0 => (pure "pmpaddr16")
  | 0x3C1 => (pure "pmpaddr17")
  | 0x3C2 => (pure "pmpaddr18")
  | 0x3C3 => (pure "pmpaddr19")
  | 0x3C4 => (pure "pmpaddr20")
  | 0x3C5 => (pure "pmpaddr21")
  | 0x3C6 => (pure "pmpaddr22")
  | 0x3C7 => (pure "pmpaddr23")
  | 0x3C8 => (pure "pmpaddr24")
  | 0x3C9 => (pure "pmpaddr25")
  | 0x3CA => (pure "pmpaddr26")
  | 0x3CB => (pure "pmpaddr27")
  | 0x3CC => (pure "pmpaddr28")
  | 0x3CD => (pure "pmpaddr29")
  | 0x3CE => (pure "pmpaddr30")
  | 0x3CF => (pure "pmpaddr31")
  | 0x3D0 => (pure "pmpaddr32")
  | 0x3D1 => (pure "pmpaddr33")
  | 0x3D2 => (pure "pmpaddr34")
  | 0x3D3 => (pure "pmpaddr35")
  | 0x3D4 => (pure "pmpaddr36")
  | 0x3D5 => (pure "pmpaddr37")
  | 0x3D6 => (pure "pmpaddr38")
  | 0x3D7 => (pure "pmpaddr39")
  | 0x3D8 => (pure "pmpaddr40")
  | 0x3D9 => (pure "pmpaddr41")
  | 0x3DA => (pure "pmpaddr42")
  | 0x3DB => (pure "pmpaddr43")
  | 0x3DC => (pure "pmpaddr44")
  | 0x3DD => (pure "pmpaddr45")
  | 0x3DE => (pure "pmpaddr46")
  | 0x3DF => (pure "pmpaddr47")
  | 0x3E0 => (pure "pmpaddr48")
  | 0x3E1 => (pure "pmpaddr49")
  | 0x3E2 => (pure "pmpaddr50")
  | 0x3E3 => (pure "pmpaddr51")
  | 0x3E4 => (pure "pmpaddr52")
  | 0x3E5 => (pure "pmpaddr53")
  | 0x3E6 => (pure "pmpaddr54")
  | 0x3E7 => (pure "pmpaddr55")
  | 0x3E8 => (pure "pmpaddr56")
  | 0x3E9 => (pure "pmpaddr57")
  | 0x3EA => (pure "pmpaddr58")
  | 0x3EB => (pure "pmpaddr59")
  | 0x3EC => (pure "pmpaddr60")
  | 0x3ED => (pure "pmpaddr61")
  | 0x3EE => (pure "pmpaddr62")
  | 0x3EF => (pure "pmpaddr63")
  | 0x321 => (pure "mcyclecfg")
  | 0x721 => (pure "mcyclecfgh")
  | 0x322 => (pure "minstretcfg")
  | 0x722 => (pure "minstretcfgh")
  | 0x015 => (pure "seed")
  | 0x008 => (pure "vstart")
  | 0x009 => (pure "vxsat")
  | 0x00A => (pure "vxrm")
  | 0x00F => (pure "vcsr")
  | 0x001 => (pure "fflags")
  | 0x002 => (pure "frm")
  | 0x003 => (pure "fcsr")
  | 0x105 => (pure "stvec")
  | 0x141 => (pure "sepc")
  | 0x305 => (pure "mtvec")
  | 0x341 => (pure "mepc")
  | 0xC00 => (pure "cycle")
  | 0xC01 => (pure "time")
  | 0xC02 => (pure "instret")
  | 0xC80 => (pure "cycleh")
  | 0x30A => (pure "menvcfg")
  | 0x31A => (pure "menvcfgh")
  | 0x343 => (pure "mtval")
  | 0x340 => (pure "mscratch")
  | 0x180 => (pure "satp")
  | reg => (hex_bits_12_forwards reg)

def csr_name_map_backwards (arg_ : String) : SailM (BitVec 12) := do
  let head_exp_ := arg_
  match (match head_exp_ with
  | "stimecmp" => (some 0x14D#12)
  | "stimecmph" => (some 0x15D#12)
  | "hpmcounter3" => (some 0xC03#12)
  | "hpmcounter4" => (some 0xC04#12)
  | "hpmcounter5" => (some 0xC05#12)
  | "hpmcounter6" => (some 0xC06#12)
  | "hpmcounter7" => (some 0xC07#12)
  | "hpmcounter8" => (some 0xC08#12)
  | "hpmcounter9" => (some 0xC09#12)
  | "hpmcounter10" => (some 0xC0A#12)
  | "hpmcounter11" => (some 0xC0B#12)
  | "hpmcounter12" => (some 0xC0C#12)
  | "hpmcounter13" => (some 0xC0D#12)
  | "hpmcounter14" => (some 0xC0E#12)
  | "hpmcounter15" => (some 0xC0F#12)
  | "hpmcounter16" => (some 0xC10#12)
  | "hpmcounter17" => (some 0xC11#12)
  | "hpmcounter18" => (some 0xC12#12)
  | "hpmcounter19" => (some 0xC13#12)
  | "hpmcounter20" => (some 0xC14#12)
  | "hpmcounter21" => (some 0xC15#12)
  | "hpmcounter22" => (some 0xC16#12)
  | "hpmcounter23" => (some 0xC17#12)
  | "hpmcounter24" => (some 0xC18#12)
  | "hpmcounter25" => (some 0xC19#12)
  | "hpmcounter26" => (some 0xC1A#12)
  | "hpmcounter27" => (some 0xC1B#12)
  | "hpmcounter28" => (some 0xC1C#12)
  | "hpmcounter29" => (some 0xC1D#12)
  | "hpmcounter30" => (some 0xC1E#12)
  | "hpmcounter31" => (some 0xC1F#12)
  | "hpmcounter3h" => (some 0xC83#12)
  | "hpmcounter4h" => (some 0xC84#12)
  | "hpmcounter5h" => (some 0xC85#12)
  | "hpmcounter6h" => (some 0xC86#12)
  | "hpmcounter7h" => (some 0xC87#12)
  | "hpmcounter8h" => (some 0xC88#12)
  | "hpmcounter9h" => (some 0xC89#12)
  | "hpmcounter10h" => (some 0xC8A#12)
  | "hpmcounter11h" => (some 0xC8B#12)
  | "hpmcounter12h" => (some 0xC8C#12)
  | "hpmcounter13h" => (some 0xC8D#12)
  | "hpmcounter14h" => (some 0xC8E#12)
  | "hpmcounter15h" => (some 0xC8F#12)
  | "hpmcounter16h" => (some 0xC90#12)
  | "hpmcounter17h" => (some 0xC91#12)
  | "hpmcounter18h" => (some 0xC92#12)
  | "hpmcounter19h" => (some 0xC93#12)
  | "hpmcounter20h" => (some 0xC94#12)
  | "hpmcounter21h" => (some 0xC95#12)
  | "hpmcounter22h" => (some 0xC96#12)
  | "hpmcounter23h" => (some 0xC97#12)
  | "hpmcounter24h" => (some 0xC98#12)
  | "hpmcounter25h" => (some 0xC99#12)
  | "hpmcounter26h" => (some 0xC9A#12)
  | "hpmcounter27h" => (some 0xC9B#12)
  | "hpmcounter28h" => (some 0xC9C#12)
  | "hpmcounter29h" => (some 0xC9D#12)
  | "hpmcounter30h" => (some 0xC9E#12)
  | "hpmcounter31h" => (some 0xC9F#12)
  | "mhpmevent3" => (some 0x323#12)
  | "mhpmevent4" => (some 0x324#12)
  | "mhpmevent5" => (some 0x325#12)
  | "mhpmevent6" => (some 0x326#12)
  | "mhpmevent7" => (some 0x327#12)
  | "mhpmevent8" => (some 0x328#12)
  | "mhpmevent9" => (some 0x329#12)
  | "mhpmevent10" => (some 0x32A#12)
  | "mhpmevent11" => (some 0x32B#12)
  | "mhpmevent12" => (some 0x32C#12)
  | "mhpmevent13" => (some 0x32D#12)
  | "mhpmevent14" => (some 0x32E#12)
  | "mhpmevent15" => (some 0x32F#12)
  | "mhpmevent16" => (some 0x330#12)
  | "mhpmevent17" => (some 0x331#12)
  | "mhpmevent18" => (some 0x332#12)
  | "mhpmevent19" => (some 0x333#12)
  | "mhpmevent20" => (some 0x334#12)
  | "mhpmevent21" => (some 0x335#12)
  | "mhpmevent22" => (some 0x336#12)
  | "mhpmevent23" => (some 0x337#12)
  | "mhpmevent24" => (some 0x338#12)
  | "mhpmevent25" => (some 0x339#12)
  | "mhpmevent26" => (some 0x33A#12)
  | "mhpmevent27" => (some 0x33B#12)
  | "mhpmevent28" => (some 0x33C#12)
  | "mhpmevent29" => (some 0x33D#12)
  | "mhpmevent30" => (some 0x33E#12)
  | "mhpmevent31" => (some 0x33F#12)
  | "mhpmcounter3" => (some 0xB03#12)
  | "mhpmcounter4" => (some 0xB04#12)
  | "mhpmcounter5" => (some 0xB05#12)
  | "mhpmcounter6" => (some 0xB06#12)
  | "mhpmcounter7" => (some 0xB07#12)
  | "mhpmcounter8" => (some 0xB08#12)
  | "mhpmcounter9" => (some 0xB09#12)
  | "mhpmcounter10" => (some 0xB0A#12)
  | "mhpmcounter11" => (some 0xB0B#12)
  | "mhpmcounter12" => (some 0xB0C#12)
  | "mhpmcounter13" => (some 0xB0D#12)
  | "mhpmcounter14" => (some 0xB0E#12)
  | "mhpmcounter15" => (some 0xB0F#12)
  | "mhpmcounter16" => (some 0xB10#12)
  | "mhpmcounter17" => (some 0xB11#12)
  | "mhpmcounter18" => (some 0xB12#12)
  | "mhpmcounter19" => (some 0xB13#12)
  | "mhpmcounter20" => (some 0xB14#12)
  | "mhpmcounter21" => (some 0xB15#12)
  | "mhpmcounter22" => (some 0xB16#12)
  | "mhpmcounter23" => (some 0xB17#12)
  | "mhpmcounter24" => (some 0xB18#12)
  | "mhpmcounter25" => (some 0xB19#12)
  | "mhpmcounter26" => (some 0xB1A#12)
  | "mhpmcounter27" => (some 0xB1B#12)
  | "mhpmcounter28" => (some 0xB1C#12)
  | "mhpmcounter29" => (some 0xB1D#12)
  | "mhpmcounter30" => (some 0xB1E#12)
  | "mhpmcounter31" => (some 0xB1F#12)
  | "mhpmcounter3h" => (some 0xB83#12)
  | "mhpmcounter4h" => (some 0xB84#12)
  | "mhpmcounter5h" => (some 0xB85#12)
  | "mhpmcounter6h" => (some 0xB86#12)
  | "mhpmcounter7h" => (some 0xB87#12)
  | "mhpmcounter8h" => (some 0xB88#12)
  | "mhpmcounter9h" => (some 0xB89#12)
  | "mhpmcounter10h" => (some 0xB8A#12)
  | "mhpmcounter11h" => (some 0xB8B#12)
  | "mhpmcounter12h" => (some 0xB8C#12)
  | "mhpmcounter13h" => (some 0xB8D#12)
  | "mhpmcounter14h" => (some 0xB8E#12)
  | "mhpmcounter15h" => (some 0xB8F#12)
  | "mhpmcounter16h" => (some 0xB90#12)
  | "mhpmcounter17h" => (some 0xB91#12)
  | "mhpmcounter18h" => (some 0xB92#12)
  | "mhpmcounter19h" => (some 0xB93#12)
  | "mhpmcounter20h" => (some 0xB94#12)
  | "mhpmcounter21h" => (some 0xB95#12)
  | "mhpmcounter22h" => (some 0xB96#12)
  | "mhpmcounter23h" => (some 0xB97#12)
  | "mhpmcounter24h" => (some 0xB98#12)
  | "mhpmcounter25h" => (some 0xB99#12)
  | "mhpmcounter26h" => (some 0xB9A#12)
  | "mhpmcounter27h" => (some 0xB9B#12)
  | "mhpmcounter28h" => (some 0xB9C#12)
  | "mhpmcounter29h" => (some 0xB9D#12)
  | "mhpmcounter30h" => (some 0xB9E#12)
  | "mhpmcounter31h" => (some 0xB9F#12)
  | "pmpcfg0" => (some 0x3A0#12)
  | "pmpcfg1" => (some 0x3A1#12)
  | "pmpcfg2" => (some 0x3A2#12)
  | "pmpcfg3" => (some 0x3A3#12)
  | "pmpcfg4" => (some 0x3A4#12)
  | "pmpcfg5" => (some 0x3A5#12)
  | "pmpcfg6" => (some 0x3A6#12)
  | "pmpcfg7" => (some 0x3A7#12)
  | "pmpcfg8" => (some 0x3A8#12)
  | "pmpcfg9" => (some 0x3A9#12)
  | "pmpcfg10" => (some 0x3AA#12)
  | "pmpcfg11" => (some 0x3AB#12)
  | "pmpcfg12" => (some 0x3AC#12)
  | "pmpcfg13" => (some 0x3AD#12)
  | "pmpcfg14" => (some 0x3AE#12)
  | "pmpcfg15" => (some 0x3AF#12)
  | "pmpaddr0" => (some 0x3B0#12)
  | "pmpaddr1" => (some 0x3B1#12)
  | "pmpaddr2" => (some 0x3B2#12)
  | "pmpaddr3" => (some 0x3B3#12)
  | "pmpaddr4" => (some 0x3B4#12)
  | "pmpaddr5" => (some 0x3B5#12)
  | "pmpaddr6" => (some 0x3B6#12)
  | "pmpaddr7" => (some 0x3B7#12)
  | "pmpaddr8" => (some 0x3B8#12)
  | "pmpaddr9" => (some 0x3B9#12)
  | "pmpaddr10" => (some 0x3BA#12)
  | "pmpaddr11" => (some 0x3BB#12)
  | "pmpaddr12" => (some 0x3BC#12)
  | "pmpaddr13" => (some 0x3BD#12)
  | "pmpaddr14" => (some 0x3BE#12)
  | "pmpaddr15" => (some 0x3BF#12)
  | "pmpaddr16" => (some 0x3C0#12)
  | "pmpaddr17" => (some 0x3C1#12)
  | "pmpaddr18" => (some 0x3C2#12)
  | "pmpaddr19" => (some 0x3C3#12)
  | "pmpaddr20" => (some 0x3C4#12)
  | "pmpaddr21" => (some 0x3C5#12)
  | "pmpaddr22" => (some 0x3C6#12)
  | "pmpaddr23" => (some 0x3C7#12)
  | "pmpaddr24" => (some 0x3C8#12)
  | "pmpaddr25" => (some 0x3C9#12)
  | "pmpaddr26" => (some 0x3CA#12)
  | "pmpaddr27" => (some 0x3CB#12)
  | "pmpaddr28" => (some 0x3CC#12)
  | "pmpaddr29" => (some 0x3CD#12)
  | "pmpaddr30" => (some 0x3CE#12)
  | "pmpaddr31" => (some 0x3CF#12)
  | "pmpaddr32" => (some 0x3D0#12)
  | "pmpaddr33" => (some 0x3D1#12)
  | "pmpaddr34" => (some 0x3D2#12)
  | "pmpaddr35" => (some 0x3D3#12)
  | "pmpaddr36" => (some 0x3D4#12)
  | "pmpaddr37" => (some 0x3D5#12)
  | "pmpaddr38" => (some 0x3D6#12)
  | "pmpaddr39" => (some 0x3D7#12)
  | "pmpaddr40" => (some 0x3D8#12)
  | "pmpaddr41" => (some 0x3D9#12)
  | "pmpaddr42" => (some 0x3DA#12)
  | "pmpaddr43" => (some 0x3DB#12)
  | "pmpaddr44" => (some 0x3DC#12)
  | "pmpaddr45" => (some 0x3DD#12)
  | "pmpaddr46" => (some 0x3DE#12)
  | "pmpaddr47" => (some 0x3DF#12)
  | "pmpaddr48" => (some 0x3E0#12)
  | "pmpaddr49" => (some 0x3E1#12)
  | "pmpaddr50" => (some 0x3E2#12)
  | "pmpaddr51" => (some 0x3E3#12)
  | "pmpaddr52" => (some 0x3E4#12)
  | "pmpaddr53" => (some 0x3E5#12)
  | "pmpaddr54" => (some 0x3E6#12)
  | "pmpaddr55" => (some 0x3E7#12)
  | "pmpaddr56" => (some 0x3E8#12)
  | "pmpaddr57" => (some 0x3E9#12)
  | "pmpaddr58" => (some 0x3EA#12)
  | "pmpaddr59" => (some 0x3EB#12)
  | "pmpaddr60" => (some 0x3EC#12)
  | "pmpaddr61" => (some 0x3ED#12)
  | "pmpaddr62" => (some 0x3EE#12)
  | "pmpaddr63" => (some 0x3EF#12)
  | "mcyclecfg" => (some 0x321#12)
  | "mcyclecfgh" => (some 0x721#12)
  | "minstretcfg" => (some 0x322#12)
  | "minstretcfgh" => (some 0x722#12)
  | "seed" => (some 0x015#12)
  | "vstart" => (some 0x008#12)
  | "vxsat" => (some 0x009#12)
  | "vxrm" => (some 0x00A#12)
  | "vcsr" => (some 0x00F#12)
  | "fflags" => (some 0x001#12)
  | "frm" => (some 0x002#12)
  | "fcsr" => (some 0x003#12)
  | "stvec" => (some 0x105#12)
  | "sepc" => (some 0x141#12)
  | "mtvec" => (some 0x305#12)
  | "mepc" => (some 0x341#12)
  | "cycle" => (some 0xC00#12)
  | "time" => (some 0xC01#12)
  | "instret" => (some 0xC02#12)
  | "cycleh" => (some 0xC80#12)
  | "menvcfg" => (some 0x30A#12)
  | "menvcfgh" => (some 0x31A#12)
  | "mtval" => (some 0x343#12)
  | "mscratch" => (some 0x340#12)
  | "satp" => (some 0x180#12)
  | mapping0_ =>
    (if ((hex_bits_12_backwards_matches mapping0_) : Bool)
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
  match arg_ with
  | 0x14D => true
  | 0x15D => true
  | 0xC03 => true
  | 0xC04 => true
  | 0xC05 => true
  | 0xC06 => true
  | 0xC07 => true
  | 0xC08 => true
  | 0xC09 => true
  | 0xC0A => true
  | 0xC0B => true
  | 0xC0C => true
  | 0xC0D => true
  | 0xC0E => true
  | 0xC0F => true
  | 0xC10 => true
  | 0xC11 => true
  | 0xC12 => true
  | 0xC13 => true
  | 0xC14 => true
  | 0xC15 => true
  | 0xC16 => true
  | 0xC17 => true
  | 0xC18 => true
  | 0xC19 => true
  | 0xC1A => true
  | 0xC1B => true
  | 0xC1C => true
  | 0xC1D => true
  | 0xC1E => true
  | 0xC1F => true
  | 0xC83 => true
  | 0xC84 => true
  | 0xC85 => true
  | 0xC86 => true
  | 0xC87 => true
  | 0xC88 => true
  | 0xC89 => true
  | 0xC8A => true
  | 0xC8B => true
  | 0xC8C => true
  | 0xC8D => true
  | 0xC8E => true
  | 0xC8F => true
  | 0xC90 => true
  | 0xC91 => true
  | 0xC92 => true
  | 0xC93 => true
  | 0xC94 => true
  | 0xC95 => true
  | 0xC96 => true
  | 0xC97 => true
  | 0xC98 => true
  | 0xC99 => true
  | 0xC9A => true
  | 0xC9B => true
  | 0xC9C => true
  | 0xC9D => true
  | 0xC9E => true
  | 0xC9F => true
  | 0x323 => true
  | 0x324 => true
  | 0x325 => true
  | 0x326 => true
  | 0x327 => true
  | 0x328 => true
  | 0x329 => true
  | 0x32A => true
  | 0x32B => true
  | 0x32C => true
  | 0x32D => true
  | 0x32E => true
  | 0x32F => true
  | 0x330 => true
  | 0x331 => true
  | 0x332 => true
  | 0x333 => true
  | 0x334 => true
  | 0x335 => true
  | 0x336 => true
  | 0x337 => true
  | 0x338 => true
  | 0x339 => true
  | 0x33A => true
  | 0x33B => true
  | 0x33C => true
  | 0x33D => true
  | 0x33E => true
  | 0x33F => true
  | 0xB03 => true
  | 0xB04 => true
  | 0xB05 => true
  | 0xB06 => true
  | 0xB07 => true
  | 0xB08 => true
  | 0xB09 => true
  | 0xB0A => true
  | 0xB0B => true
  | 0xB0C => true
  | 0xB0D => true
  | 0xB0E => true
  | 0xB0F => true
  | 0xB10 => true
  | 0xB11 => true
  | 0xB12 => true
  | 0xB13 => true
  | 0xB14 => true
  | 0xB15 => true
  | 0xB16 => true
  | 0xB17 => true
  | 0xB18 => true
  | 0xB19 => true
  | 0xB1A => true
  | 0xB1B => true
  | 0xB1C => true
  | 0xB1D => true
  | 0xB1E => true
  | 0xB1F => true
  | 0xB83 => true
  | 0xB84 => true
  | 0xB85 => true
  | 0xB86 => true
  | 0xB87 => true
  | 0xB88 => true
  | 0xB89 => true
  | 0xB8A => true
  | 0xB8B => true
  | 0xB8C => true
  | 0xB8D => true
  | 0xB8E => true
  | 0xB8F => true
  | 0xB90 => true
  | 0xB91 => true
  | 0xB92 => true
  | 0xB93 => true
  | 0xB94 => true
  | 0xB95 => true
  | 0xB96 => true
  | 0xB97 => true
  | 0xB98 => true
  | 0xB99 => true
  | 0xB9A => true
  | 0xB9B => true
  | 0xB9C => true
  | 0xB9D => true
  | 0xB9E => true
  | 0xB9F => true
  | 0xB83 => true
  | 0xB84 => true
  | 0xB85 => true
  | 0xB86 => true
  | 0xB87 => true
  | 0xB88 => true
  | 0xB89 => true
  | 0xB8A => true
  | 0xB8B => true
  | 0xB8C => true
  | 0xB8D => true
  | 0xB8E => true
  | 0xB8F => true
  | 0xB90 => true
  | 0xB91 => true
  | 0xB92 => true
  | 0xB93 => true
  | 0xB94 => true
  | 0xB95 => true
  | 0xB96 => true
  | 0xB97 => true
  | 0xB98 => true
  | 0xB99 => true
  | 0xB9A => true
  | 0xB9B => true
  | 0xB9C => true
  | 0xB9D => true
  | 0xB9E => true
  | 0xB9F => true
  | 0x3A0 => true
  | 0x3A1 => true
  | 0x3A2 => true
  | 0x3A3 => true
  | 0x3A4 => true
  | 0x3A5 => true
  | 0x3A6 => true
  | 0x3A7 => true
  | 0x3A8 => true
  | 0x3A9 => true
  | 0x3AA => true
  | 0x3AB => true
  | 0x3AC => true
  | 0x3AD => true
  | 0x3AE => true
  | 0x3AF => true
  | 0x3B0 => true
  | 0x3B1 => true
  | 0x3B2 => true
  | 0x3B3 => true
  | 0x3B4 => true
  | 0x3B5 => true
  | 0x3B6 => true
  | 0x3B7 => true
  | 0x3B8 => true
  | 0x3B9 => true
  | 0x3BA => true
  | 0x3BB => true
  | 0x3BC => true
  | 0x3BD => true
  | 0x3BE => true
  | 0x3BF => true
  | 0x3C0 => true
  | 0x3C1 => true
  | 0x3C2 => true
  | 0x3C3 => true
  | 0x3C4 => true
  | 0x3C5 => true
  | 0x3C6 => true
  | 0x3C7 => true
  | 0x3C8 => true
  | 0x3C9 => true
  | 0x3CA => true
  | 0x3CB => true
  | 0x3CC => true
  | 0x3CD => true
  | 0x3CE => true
  | 0x3CF => true
  | 0x3D0 => true
  | 0x3D1 => true
  | 0x3D2 => true
  | 0x3D3 => true
  | 0x3D4 => true
  | 0x3D5 => true
  | 0x3D6 => true
  | 0x3D7 => true
  | 0x3D8 => true
  | 0x3D9 => true
  | 0x3DA => true
  | 0x3DB => true
  | 0x3DC => true
  | 0x3DD => true
  | 0x3DE => true
  | 0x3DF => true
  | 0x3E0 => true
  | 0x3E1 => true
  | 0x3E2 => true
  | 0x3E3 => true
  | 0x3E4 => true
  | 0x3E5 => true
  | 0x3E6 => true
  | 0x3E7 => true
  | 0x3E8 => true
  | 0x3E9 => true
  | 0x3EA => true
  | 0x3EB => true
  | 0x3EC => true
  | 0x3ED => true
  | 0x3EE => true
  | 0x3EF => true
  | 0x321 => true
  | 0x721 => true
  | 0x322 => true
  | 0x722 => true
  | 0x015 => true
  | 0x008 => true
  | 0x009 => true
  | 0x00A => true
  | 0x00F => true
  | 0x001 => true
  | 0x002 => true
  | 0x003 => true
  | 0x105 => true
  | 0x141 => true
  | 0x305 => true
  | 0x341 => true
  | 0xC00 => true
  | 0xC01 => true
  | 0xC02 => true
  | 0xC80 => true
  | 0x30A => true
  | 0x31A => true
  | 0x343 => true
  | 0x340 => true
  | 0x180 => true
  | reg => true
  | _ => false

def csr_name_map_backwards_matches (arg_ : String) : SailM Bool := do
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
    (if ((hex_bits_12_backwards_matches mapping0_) : Bool)
    then
      (match (hex_bits_12_backwards mapping0_) with
      | reg => (some true)
      | _ => none)
    else none)) with
  | .some result => (pure result)
  | none =>
    (match head_exp_ with
    | _ => (pure false))

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

end Out.Functions
