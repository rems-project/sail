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

inductive E where | A | B | C
  deriving Inhabited, BEq

inductive Register : Type where
  | r
  | r_C
  | r_B
  | r_A
  deriving DecidableEq, Hashable
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


XXXXXXXXX

import Out.String

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

open option
open Register
open E

namespace Functions

def undefined_E (_ : Unit) : SailM E := do
  (internal_pick [A, B, C])

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def foreach_earlyreturneffect (n : Nat) : SailM Bool := SailME.run do
  let loop_i_lower := 0
  let loop_i_upper := n
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper + 1:1]i do
    let () := loop_vars
    loop_vars ← do
      if (i >b 5)
      then throw (false : Bool)
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
    for i in [loop_i_lower:loop_i_upper + 1:1]i do
      let res := loop_vars
      loop_vars ← do
        if (i >b 5)
        then throw (false : Bool)
        else (pure (res +i i))
    (pure loop_vars) ) : ExceptM _ Nat )
  (pure (res >b n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def foreach_inner_earlyreturneffect (n : Nat) : SailM Bool := SailME.run do
  let loop_i_lower := 0
  let loop_i_upper := n
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper + 1:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_j_lower := 0
      let loop_j_upper := i
      let mut loop_vars_1 := ()
      for j in [loop_j_lower:loop_j_upper + 1:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do
          if (i >b 5)
          then throw (false : Bool)
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
    for i in [loop_i_lower:loop_i_upper + 1:1]i do
      let res := loop_vars
      loop_vars ← do
        let loop_j_lower := 0
        let loop_j_upper := i
        let mut loop_vars_1 := res
        for j in [loop_j_lower:loop_j_upper + 1:1]i do
          let res := loop_vars_1
          loop_vars_1 ← do
            if (i >b 5)
            then throw (false : Bool)
            else (pure (res +i 1))
        (pure loop_vars_1)
    (pure loop_vars) ) : ExceptM _ Nat )
  (pure (res >b n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def foreach_inner_earlyreturneffect_catch (n : Nat) : SailM Bool := SailME.run do
  let loop_i_lower := 0
  let loop_i_upper := n
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper + 1:1]i do
    let () := loop_vars
    loop_vars ← do
      let loop_j_lower := 0
      let loop_j_upper := i
      let mut loop_vars_1 := ()
      for j in [loop_j_lower:loop_j_upper + 1:1]i do
        let () := loop_vars_1
        loop_vars_1 ← do
          if (i >b 5)
          then throw (false : Bool)
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
    for i in [loop_i_lower:loop_i_upper + 1:1]i do
      let res := loop_vars
      loop_vars ← do
        let res ← (( do
          let loop_j_lower := 0
          let loop_j_upper := i
          let mut loop_vars_1 := res
          for j in [loop_j_lower:loop_j_upper + 1:1]i do
            let res := loop_vars_1
            loop_vars_1 ← do
              if (i >b 5)
              then throw (false : Bool)
              else (pure (res +i 1))
          (pure loop_vars_1) ) : ExceptM _ Nat )
        (pure (res *i 2))
    (pure loop_vars) ) : ExceptM _ Nat )
  (pure (res >b n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def while_earlyreturneffect (n : Nat) : SailM Bool := SailME.run do
  let mut loop_vars := ()
  while (← (λ _ => do (pure ((← readReg r) <b n))) loop_vars) do
    let () := loop_vars
    loop_vars ← do
      if ((← readReg r) >b 5)
      then throw (false : Bool)
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
        if (res >b 5)
        then throw (false : Bool)
        else (pure (res +i 1))
    (pure loop_vars) ) : ExceptM _ Nat )
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
          if (n >b 5)
          then throw (false : Bool)
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
            if (n >b 5)
            then throw (false : Bool)
            else (pure (res +i 1))
        (pure loop_vars_1)
    (pure loop_vars) ) : ExceptM _ Nat )
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
          if (n >b 5)
          then throw (false : Bool)
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
              if (n >b 5)
              then throw (false : Bool)
              else (pure (res +i 1))
          (pure loop_vars_1) ) : ExceptM _ Nat )
        (pure (res *i 2))
    (pure loop_vars) ) : ExceptM _ Nat )
  (pure (res >b n))

def match_early_return (x : E) : SailM E := SailME.run do
  match x with
  | A =>
    throw (← do
        readReg r_A)
  | B => writeReg r_B A
  | C => writeReg r_C A
  readReg r_B

def match_early_return_inloop (x : E) : SailM E := SailME.run do
  let loop_i_lower := 0
  let loop_i_upper := 10
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper + 1:1]i do
    let () := loop_vars
    loop_vars ← do
      match x with
      | A =>
        throw (← do
            readReg r_A)
      | B => writeReg r_B A
      | C => writeReg r_C A
  (pure loop_vars)
  readReg r_B

def match_early_return_inloop_2 (x : E) : SailM E := SailME.run do
  let loop_i_lower := 0
  let loop_i_upper := 10
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper + 1:1]i do
    let () := loop_vars
    loop_vars ← do
      let y ← (( do
        match x with
        | A =>
          throw (← do
              readReg r_A)
        | B => readReg r_B
        | C => readReg r_C ) : SailME _ E )
      (pure ())
  (pure loop_vars)
  readReg r_B

def match_early_return_loop (x : E) : SailM E := SailME.run do
  match x with
  | A =>
    let loop_i_lower := 0
    let loop_i_upper := 10
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper + 1:1]i do
      let () := loop_vars
      loop_vars ← do
        throw (← do
            readReg r_A)
    (pure loop_vars)
  | B => writeReg r_B A
  | C => writeReg r_C A
  readReg r_B

/-- Type quantifiers: k_ex2655# : Bool -/
def ite_early_return (x : Bool) : SailM E := SailME.run do
  writeReg r_A (← readReg r_C)
  let y ← (( do
    if x
    then
      throw (← do
          readReg r_A)
    else readReg r_B ) : SailME _ E )
  readReg r_B

/-- Type quantifiers: k_ex2657# : Bool -/
def ite_early_return_inloop (x : Bool) : SailM E := SailME.run do
  let loop_i_lower := 0
  let loop_i_upper := 10
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper + 1:1]i do
    let () := loop_vars
    loop_vars ← do
      writeReg r_A (← readReg r_C)
      let y ← (( do
        if x
        then
          throw (← do
              readReg r_A)
        else readReg r_B ) : SailME _ E )
      (pure ())
  (pure loop_vars)
  readReg r_B

/-- Type quantifiers: k_ex2661# : Bool -/
def ite_early_return_loop (x : Bool) : SailM E := SailME.run do
  if x
  then
    let loop_i_lower := 0
    let loop_i_upper := 10
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper + 1:1]i do
      let () := loop_vars
      loop_vars ← do
        throw (← do
            readReg r_A)
    (pure loop_vars)
  else writeReg r_B A
  readReg r_B

def unit_type (x : E) : SailM Unit := do
  writeReg r_A x

/-- Type quantifiers: k_ex2665# : Bool -/
def ite_early_return_seq (x : Bool) : SailM E := SailME.run do
  writeReg r_A (← readReg r_C)
  let y ← (( do
    if x
    then
      throw (← do
          (unit_type A)
          readReg r_A)
    else readReg r_B ) : SailME _ E )
  readReg r_B

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg r_A (← (undefined_E ()))
  writeReg r_B (← (undefined_E ()))
  writeReg r_C (← (undefined_E ()))
  writeReg r (← (undefined_nat ()))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  (initialize_registers ())

end Functions
