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

inductive E where | A | B | C
  deriving BEq, Inhabited, Repr
  open E

inductive Register : Type where
  | r
  | r_C
  | r_B
  | r_A
  deriving DecidableEq, Hashable, Repr
open Register

abbrev RegisterType : Register → Type
  | .r => Nat
  | .r_C => E
  | .r_B => E
  | .r_A => E

instance : Inhabited (RegisterRef RegisterType E) where
  default := .Reg r_A
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
open E

/-- Type quantifiers: k_ex2693_ : Bool, k_ex2692_ : Bool -/
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

def undefined_E (_ : Unit) : SailM E := do
  (internal_pick [A, B, C])

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def foreach_earlyreturneffect (n : Nat) : SailM Bool := SailME.run do
  let loop_i_lower := 0
  let loop_i_upper := n
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((i >b 5) : Bool)
      then SailME.throw (false : Bool)
      else writeReg r ((← readReg r) +i 1)
  (pure loop_vars)
  (pure ((← readReg r) >b n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def foreach_earlyreturnpure (n : Nat) : Bool := ExceptM.run do
  let res : Nat := 0
  let res ← (( do
    let loop_i_lower := 0
    let loop_i_upper := n
    let mut loop_vars := res
    for i in [loop_i_lower:loop_i_upper:1]i do
      let res := loop_vars
      loop_vars ← do
        if ((i >b 5) : Bool)
        then throw (false : Bool)
        else (pure (res +i i))
    (pure loop_vars) ) : ExceptM Bool Nat )
  (pure (res >b n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def foreach_inner_earlyreturneffect (n : Nat) : SailM Bool := SailME.run do
  let loop_i_lower := 0
  let loop_i_upper := n
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_j_lower := 0
      let loop_j_upper := i
      let mut loop_vars_1 := ()
      for j in [loop_j_lower:loop_j_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do
          if ((i >b 5) : Bool)
          then SailME.throw (false : Bool)
          else writeReg r ((← readReg r) +i 1)
      (pure loop_vars_1)
  (pure loop_vars)
  (pure ((← readReg r) >b n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def foreach_inner_earlyreturnpure (n : Nat) : Bool := ExceptM.run do
  let res : Nat := 0
  let res ← (( do
    let loop_i_lower := 0
    let loop_i_upper := n
    let mut loop_vars := res
    for i in [loop_i_lower:loop_i_upper:1]i do
      let res := loop_vars
      loop_vars ← do
        let loop_j_lower := 0
        let loop_j_upper := i
        let mut loop_vars_1 := res
        for j in [loop_j_lower:loop_j_upper:1]i do
          let res := loop_vars_1
          loop_vars_1 ← do
            if ((i >b 5) : Bool)
            then throw (false : Bool)
            else (pure (res +i 1))
        (pure loop_vars_1)
    (pure loop_vars) ) : ExceptM Bool Nat )
  (pure (res >b n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def foreach_inner_earlyreturneffect_catch (n : Nat) : SailM Bool := SailME.run do
  let loop_i_lower := 0
  let loop_i_upper := n
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_j_lower := 0
      let loop_j_upper := i
      let mut loop_vars_1 := ()
      for j in [loop_j_lower:loop_j_upper:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do
          if ((i >b 5) : Bool)
          then SailME.throw (false : Bool)
          else writeReg r ((← readReg r) +i 1)
      (pure loop_vars_1)
      writeReg r ((← readReg r) *i 2)
  (pure loop_vars)
  (pure ((← readReg r) >b n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def foreach_inner_earlyreturnpure_catch (n : Nat) : Bool := ExceptM.run do
  let res : Nat := 0
  let res ← (( do
    let loop_i_lower := 0
    let loop_i_upper := n
    let mut loop_vars := res
    for i in [loop_i_lower:loop_i_upper:1]i do
      let res := loop_vars
      loop_vars ← do
        let res ← (( do
          let loop_j_lower := 0
          let loop_j_upper := i
          let mut loop_vars_1 := res
          for j in [loop_j_lower:loop_j_upper:1]i do
            let res := loop_vars_1
            loop_vars_1 ← do
              if ((i >b 5) : Bool)
              then throw (false : Bool)
              else (pure (res +i 1))
          (pure loop_vars_1) ) : ExceptM Bool Nat )
        (pure (res *i 2))
    (pure loop_vars) ) : ExceptM Bool Nat )
  (pure (res >b n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def while_earlyreturneffect (n : Nat) : SailM Bool := SailME.run do
  let mut loop_vars := ()
  while (← (λ _ => do (pure ((← readReg r) <b n))) loop_vars) do
    let () := loop_vars
    loop_vars ← do
      if (((← readReg r) >b 5) : Bool)
      then SailME.throw (false : Bool)
      else writeReg r ((← readReg r) +i 1)
  (pure loop_vars)
  (pure ((← readReg r) >b n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def while_earlyreturnpure (n : Nat) : Bool := ExceptM.run do
  let res : Nat := 0
  let res ← (( do
    let mut loop_vars := res
    while (λ res => (res <b n)) loop_vars do
      let res := loop_vars
      loop_vars ← do
        if ((res >b 5) : Bool)
        then throw (false : Bool)
        else (pure (res +i 1))
    (pure loop_vars) ) : ExceptM Bool Nat )
  (pure (res >b n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def while_inner_earlyreturneffect (n : Nat) : SailM Bool := SailME.run do
  let mut loop_vars := ()
  while (← (λ _ => do (pure ((← readReg r) <b n))) loop_vars) do
    let () := loop_vars
    loop_vars ← do
      let mut loop_vars_1 := ()
      while (← (λ _ => do (pure ((← readReg r) <b n))) loop_vars_1) do
        let () := loop_vars_1
        loop_vars_1 ← do
          if ((n >b 5) : Bool)
          then SailME.throw (false : Bool)
          else writeReg r ((← readReg r) +i 1)
      (pure loop_vars_1)
  (pure loop_vars)
  (pure ((← readReg r) >b n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def while_inner_earlyreturnpure (n : Nat) : Bool := ExceptM.run do
  let res : Nat := 0
  let res ← (( do
    let mut loop_vars := res
    while (λ res => (res <b n)) loop_vars do
      let res := loop_vars
      loop_vars ← do
        let mut loop_vars_1 := res
        while (λ res => (res <b n)) loop_vars_1 do
          let res := loop_vars_1
          loop_vars_1 ← do
            if ((n >b 5) : Bool)
            then throw (false : Bool)
            else (pure (res +i 1))
        (pure loop_vars_1)
    (pure loop_vars) ) : ExceptM Bool Nat )
  (pure (res >b n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def while_inner_earlyreturneffect_catch (n : Nat) : SailM Bool := SailME.run do
  let mut loop_vars := ()
  while (← (λ _ => do (pure ((← readReg r) <b n))) loop_vars) do
    let () := loop_vars
    loop_vars ← do
      let mut loop_vars_1 := ()
      while (← (λ _ => do (pure ((← readReg r) <b n))) loop_vars_1) do
        let () := loop_vars_1
        loop_vars_1 ← do
          if ((n >b 5) : Bool)
          then SailME.throw (false : Bool)
          else writeReg r ((← readReg r) +i 1)
      (pure loop_vars_1)
      writeReg r ((← readReg r) *i 2)
  (pure loop_vars)
  (pure ((← readReg r) >b n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def while_inner_earlyreturnpure_catch (n : Nat) : Bool := ExceptM.run do
  let res : Nat := 0
  let res ← (( do
    let mut loop_vars := res
    while (λ res => (res <b n)) loop_vars do
      let res := loop_vars
      loop_vars ← do
        let res ← (( do
          let mut loop_vars_1 := res
          while (λ res => (res <b n)) loop_vars_1 do
            let res := loop_vars_1
            loop_vars_1 ← do
              if ((n >b 5) : Bool)
              then throw (false : Bool)
              else (pure (res +i 1))
          (pure loop_vars_1) ) : ExceptM Bool Nat )
        (pure (res *i 2))
    (pure loop_vars) ) : ExceptM Bool Nat )
  (pure (res >b n))

def match_early_return (x : E) : SailM E := SailME.run do
  match x with
  | A =>
    SailME.throw (← do
        readReg r_A)
  | B => writeReg r_B A
  | C => writeReg r_C A
  readReg r_B

def match_early_return_inloop (x : E) : SailM E := SailME.run do
  let loop_i_lower := 0
  let loop_i_upper := 10
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      match x with
      | A =>
        SailME.throw (← do
            readReg r_A)
      | B => writeReg r_B A
      | C => writeReg r_C A
  (pure loop_vars)
  readReg r_B

def match_early_return_inloop_2 (x : E) : SailM E := SailME.run do
  let loop_i_lower := 0
  let loop_i_upper := 10
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let y ← (( do
        match x with
        | A =>
          SailME.throw (← do
              readReg r_A)
        | B => readReg r_B
        | C => readReg r_C ) : SailME E E )
      (pure ())
  (pure loop_vars)
  readReg r_B

def match_early_return_loop (x : E) : SailM E := SailME.run do
  match x with
  | A =>
    (do
      let loop_i_lower := 0
      let loop_i_upper := 10
      let mut loop_vars := ()
      for i in [loop_i_lower:loop_i_upper:1]i do
        let () := loop_vars
        loop_vars ← do
          SailME.throw (← do
              readReg r_A)
      (pure loop_vars))
  | B => writeReg r_B A
  | C => writeReg r_C A
  readReg r_B

/-- Type quantifiers: k_ex3009_ : Bool -/
def ite_early_return (x : Bool) : SailM E := SailME.run do
  writeReg r_A (← readReg r_C)
  let y ← (( do
    if (x : Bool)
    then
      SailME.throw (← do
          readReg r_A)
    else readReg r_B ) : SailME E E )
  readReg r_B

/-- Type quantifiers: k_ex3011_ : Bool -/
def ite_early_return_inloop (x : Bool) : SailM E := SailME.run do
  let loop_i_lower := 0
  let loop_i_upper := 10
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      writeReg r_A (← readReg r_C)
      let y ← (( do
        if (x : Bool)
        then
          SailME.throw (← do
              readReg r_A)
        else readReg r_B ) : SailME E E )
      (pure ())
  (pure loop_vars)
  readReg r_B

/-- Type quantifiers: k_ex3015_ : Bool -/
def ite_early_return_loop (x : Bool) : SailM E := SailME.run do
  if (x : Bool)
  then
    (do
      let loop_i_lower := 0
      let loop_i_upper := 10
      let mut loop_vars := ()
      for i in [loop_i_lower:loop_i_upper:1]i do
        let () := loop_vars
        loop_vars ← do
          SailME.throw (← do
              readReg r_A)
      (pure loop_vars))
  else writeReg r_B A
  readReg r_B

def unit_type (x : E) : SailM Unit := do
  writeReg r_A x

/-- Type quantifiers: k_ex3019_ : Bool -/
def ite_early_return_seq (x : Bool) : SailM E := SailME.run do
  writeReg r_A (← readReg r_C)
  let y ← (( do
    if (x : Bool)
    then
      SailME.throw (← do
          (unit_type A)
          readReg r_A)
    else readReg r_B ) : SailME E E )
  readReg r_B

/-- Type quantifiers: k_ex3021_ : Bool -/
def ite_early_return_exit (x : Bool) : SailM E := SailME.run do
  writeReg r_A (← readReg r_C)
  let y ← (( do
    if (x : Bool)
    then
      SailME.throw (← do
          readReg r_A)
    else readReg r_B ) : SailME E E )
  if (x : Bool)
  then throw Error.Exit
  else (pure ())
  readReg r_B

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg r_A (← (undefined_E ()))
  writeReg r_B (← (undefined_E ()))
  writeReg r_C (← (undefined_E ()))
  writeReg r (← (undefined_nat ()))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  (initialize_registers ())

end Out.Functions
