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

inductive Register : Type where
  | r
  deriving DecidableEq, Hashable, Repr
open Register

abbrev RegisterType : Register → Type
  | .r => Nat

instance : Inhabited (RegisterRef RegisterType Nat) where
  default := .Reg r
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
open Register

/-- Type quantifiers: k_ex2776_ : Bool, k_ex2775_ : Bool -/
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

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreach_loop (m : Nat) (n : Nat) : Nat := Id.run do
  let res : Nat := 0
  let loop_i_lower := m
  let loop_i_upper := n
  let mut loop_vars := res
  for i in [loop_i_lower:loop_i_upper:1]i do
    let res := loop_vars
    loop_vars := (res +i 1)
  (pure loop_vars)

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreach_loopmon (m : Nat) (n : Nat) : SailM Nat := do
  let loop_i_lower := n
  let loop_i_upper := m
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do writeReg r ((← readReg r) +i 1)
  (pure loop_vars)
  readReg r

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreach_loopboth (m : Nat) (n : Nat) : SailM Nat := do
  let res : Nat := 0
  let res ← (( do
    let loop_i_lower := n
    let loop_i_upper := m
    let mut loop_vars := res
    for i in [loop_i_lower:loop_i_upper:1]i do
      let res := loop_vars
      loop_vars ← do
        let res : Nat := (res +i 1)
        writeReg r ((← readReg r) +i res)
        (pure res)
    (pure loop_vars) ) : SailM Nat )
  (pure (res +i 1))

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreach_loopmultiplevar (m : Nat) (n : Nat) : Nat := Id.run do
  let res : Nat := 0
  let mult : Nat := 1
  let (mult, res) ← (( do
    let loop_i_lower := m
    let loop_i_upper := n
    let mut loop_vars := (mult, res)
    for i in [loop_i_lower:loop_i_upper:1]i do
      let (mult, res) := loop_vars
      loop_vars :=
        let res : Nat := (res +i 1)
        let mult : Nat := (res *i mult)
        (mult, res)
    (pure loop_vars) ) : Id (Nat × Nat) )
  (pure mult)

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreach_loopuseindex (m : Nat) (n : Nat) : Nat := Id.run do
  let res : Nat := 0
  let loop_i_lower := m
  let loop_i_upper := n
  let mut loop_vars := res
  for i in [loop_i_lower:loop_i_upper:1]i do
    let res := loop_vars
    loop_vars := (res +i i)
  (pure loop_vars)

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def while_loop (m : Nat) (n : Nat) : Nat := Id.run do
  let res : Nat := 0
  let mut loop_vars := res
  while (λ res => (res <b n)) loop_vars do
    let res := loop_vars
    loop_vars := ((res +i 1) : Nat)
  (pure loop_vars)

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def while_loopmon (m : Nat) (n : Nat) : SailM Nat := do
  let mut loop_vars := ()
  while (← (λ _ => do (pure ((← readReg r) <b n))) loop_vars) do
    let () := loop_vars
    loop_vars ← do writeReg r ((← readReg r) +i 1)
  (pure loop_vars)
  readReg r

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def while_loopboth (m : Nat) (n : Nat) : SailM Nat := do
  let res : Nat := 0
  let res ← (( do
    let mut loop_vars := res
    while (λ res => (res <b n)) loop_vars do
      let res := loop_vars
      loop_vars ← do
        let res : Nat := (res +i 1)
        writeReg r ((← readReg r) +i res)
        (pure res)
    (pure loop_vars) ) : SailM Nat )
  (pure (res +i 1))

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def while_loopmultiplevar (m : Nat) (n : Nat) : Nat := Id.run do
  let res : Nat := 0
  let mult : Nat := 1
  let (mult, res) ← (( do
    let mut loop_vars := (mult, res)
    while (λ (mult, res) => (res <b n)) loop_vars do
      let (mult, res) := loop_vars
      loop_vars :=
        (let res : Nat := (res +i 1)
        let mult : Nat := (res *i mult)
        (mult, res) : (Nat × Nat))
    (pure loop_vars) ) : Id (Nat × Nat) )
  (pure mult)

def while_print (_ : Unit) : Unit := Id.run do
  let i : Int := 0
  let i ← (( do
    let mut loop_vars := i
    while (λ i => (i <b 10)) loop_vars do
      let i := loop_vars
      loop_vars := ((i +i 1) : Int)
    (pure loop_vars) ) : Id Int )
  (pure (print_int "i = " i))

def while_print_fuel (_ : Unit) : SailM Unit := do
  let i : Int := 0
  let i ← (( do
    let loop_vars ← whileFuelM (fuel :=100) (fun i => (pure (i <b 100))) i
      fun i => do
        assert true "loop dummy assert"
        (pure (i +i 1))
    (pure loop_vars) ) : SailM Int )
  (pure (print_int "i = " i))

/-- Type quantifiers: n : Int -/
def until_print_fuel (n : Int) : SailM Unit := do
  let i : Int := 0
  let i ← (( do
    let loop_vars ← untilFuelM (fuel :=n) (fun i => (pure (i <b 100))) i
      fun i => do
        assert true "loop dummy assert"
        (pure (i +i 1))
    (pure loop_vars) ) : SailM Int )
  (pure (print_int "i = " i))

def while_print_long (_ : Unit) : Unit := Id.run do
  let this_is_a_very_long_variable_name_to_stress_the_formatting : Int := 0
  let this_is_a_very_long_variable_name_to_stress_the_formatting ← (( do
    let mut loop_vars := this_is_a_very_long_variable_name_to_stress_the_formatting
    while (λ this_is_a_very_long_variable_name_to_stress_the_formatting =>
      ((this_is_a_very_long_variable_name_to_stress_the_formatting +i this_is_a_very_long_variable_name_to_stress_the_formatting) <b 10))
      loop_vars
      do
      let this_is_a_very_long_variable_name_to_stress_the_formatting := loop_vars
      loop_vars := ((this_is_a_very_long_variable_name_to_stress_the_formatting +i 1) : Int)
    (pure loop_vars) ) : Id Int )
  (pure (print_int "i = " this_is_a_very_long_variable_name_to_stress_the_formatting))

def nothing (_ : Unit) : Unit :=
  ()

/-- Type quantifiers: m : Int, n : Int -/
def foreachpure (n : Int) (m : Int) : Unit := Id.run do
  let x : Int := n
  let x ← (( do
    let loop_rr_lower := 0
    let loop_rr_upper := (m -i 1)
    let mut loop_vars := x
    for rr in [loop_rr_lower:loop_rr_upper:1]i do
      let x := loop_vars
      loop_vars :=
        let _ : Unit :=
          let vec := n
          Id.run for i in [0:(m -i 1):1]i do (nothing ())
        (x +i 1)
    (pure loop_vars) ) : Id Int )
  (pure ())

/-- Type quantifiers: m : Int, n : Nat, 0 ≤ n -/
def foreachnotsopure (n : Nat) (m : Int) : SailM Unit := do
  let x : Nat := n
  let x ← (( do
    let loop_rr_lower := 0
    let loop_rr_upper := (m -i 1)
    let mut loop_vars := x
    for rr in [loop_rr_lower:loop_rr_upper:1]i do
      let x := loop_vars
      loop_vars ← do
        let vec := n
        for i in [0:(m -i 1):1]i do writeReg r x
        (pure (x +i 1))
    (pure loop_vars) ) : SailM Nat )
  (pure ())

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg r (← (undefined_nat ()))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  (initialize_registers ())

end Out.Functions
