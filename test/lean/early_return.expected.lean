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
  deriving BEq



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

import Out.Sail.Sail
import Out.Sail.BitVec
import Out.Defs

import Out.Specialization

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail


open option
open Register
open E

namespace Functions

/-- Type quantifiers: k_ex2343# : Bool, k_ex2342# : Bool -/
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
  then ((sail_ones n) <<< i)
  else let one : (BitVec n) := (sail_mask n (0b1 : (BitVec 1)))
       (((one <<< l) - one) <<< i)

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
  then ((Int.tdiv (n + 1) m) -i 1)
  else if (Bool.and (GT.gt n 0) (LT.lt m 0))
       then ((Int.tdiv (n -i 1) m) -i 1)
       else (Int.tdiv n m)

/-- Type quantifiers: m : Int, n : Int -/
def fmod_int (n : Int) (m : Int) : Int :=
  (n -i (m * (fdiv_int n m)))

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
def foreach_earlyreturneffect (n : Nat) : SailM Bool := do
  let loop_i_lower := 0
  let loop_i_upper := n
  catchEarlyReturn
  (foreach_ME loop_i_lower loop_i_upper 1 ()
    (λ i _ => do
      if (GT.gt i 5)
      then return (early_return
             (false : Bool))
      else (pure (cont (← writeReg r ((← readReg r) + 1))))))
  (pure (GT.gt (← readReg r) n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def foreach_earlyreturnpure (n : Nat) : Bool := Id.run do
  let res : Nat := 0
  let res : Nat ← do
    let loop_i_lower := 0
    let loop_i_upper := n
    catchEarlyReturnPure
    (foreach_E loop_i_lower loop_i_upper 1 res
      (λ i res => Id.run do
        if (GT.gt i 5)
        then return (early_return
               (false : Bool))
        else (cont (res + i))))
  (pure (GT.gt res n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def foreach_inner_earlyreturneffect (n : Nat) : SailM Bool := do
  let loop_i_lower := 0
  let loop_i_upper := n
  catchEarlyReturn
  (foreach_ME loop_i_lower loop_i_upper 1 ()
    (λ i _ => do
      let loop_j_lower := 0
      let loop_j_upper := i
      foreach_ME loop_j_lower loop_j_upper 1 ()
        (λ j _ => do
          if (GT.gt i 5)
          then return (early_return
                 (false : Bool))
          else (pure (cont (← writeReg r ((← readReg r) + 1)))))))
  (pure (GT.gt (← readReg r) n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def foreach_inner_earlyreturnpure (n : Nat) : Bool := Id.run do
  let res : Nat := 0
  let res : Nat ← do
    let loop_i_lower := 0
    let loop_i_upper := n
    catchEarlyReturnPure
    (foreach_E loop_i_lower loop_i_upper 1 res
      (λ i res => Id.run do
        let loop_j_lower := 0
        let loop_j_upper := i
        foreach_E loop_j_lower loop_j_upper 1 res
          (λ j res => Id.run do
            if (GT.gt i 5)
            then return (early_return
                   (false : Bool))
            else (cont (res + 1)))))
  (pure (GT.gt res n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def foreach_inner_earlyreturneffect_catch (n : Nat) : SailM Bool := do
  let loop_i_lower := 0
  let loop_i_upper := n
  catchEarlyReturn
  (foreach_ME loop_i_lower loop_i_upper 1 ()
    (λ i _ => do
      let loop_j_lower := 0
      let loop_j_upper := i
      catchEarlyReturnInner
      (foreach_ME loop_j_lower loop_j_upper 1 ()
        (λ j _ => do
          if (GT.gt i 5)
          then return (early_return
                 (false : Bool))
          else (pure (cont (← writeReg r ((← readReg r) + 1))))))
      (pure (cont (← do
            writeReg r ((← readReg r) * 2))))))
  (pure (GT.gt (← readReg r) n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def foreach_inner_earlyreturnpure_catch (n : Nat) : Bool := Id.run do
  let res : Nat := 0
  let res : Nat ← do
    let loop_i_lower := 0
    let loop_i_upper := n
    catchEarlyReturnPure
    (foreach_E loop_i_lower loop_i_upper 1 res
      (λ i res => Id.run do
        let res : Nat ← do
          let loop_j_lower := 0
          let loop_j_upper := i
          catchEarlyReturnPureInner
          (foreach_E loop_j_lower loop_j_upper 1 res
            (λ j res => Id.run do
              if (GT.gt i 5)
              then return (early_return
                     (false : Bool))
              else (cont (res + 1))))
        (cont (res * 2))))
  (pure (GT.gt res n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def while_earlyreturneffect (n : Nat) : SailM Bool := do
  catchEarlyReturn
  (while_ME (λ _ => do (pure (LT.lt (← readReg r) n))) ()
    (λ _ => do
      if (GT.gt (← readReg r) 5)
      then return (early_return
             (false : Bool))
      else (pure (cont (← writeReg r ((← readReg r) + 1))))))
  (pure (GT.gt (← readReg r) n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def while_earlyreturnpure (n : Nat) : Bool := Id.run do
  let res : Nat := 0
  let res : Nat ← do
    catchEarlyReturnPure
    (while_E (λ res => (LT.lt res n)) res
      (λ res => Id.run do
        if (GT.gt res 5)
        then return (early_return
               (false : Bool))
        else (cont (res + 1))))
  (pure (GT.gt res n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def while_inner_earlyreturneffect (n : Nat) : SailM Bool := do
  catchEarlyReturn
  (while_ME (λ _ => do (pure (LT.lt (← readReg r) n))) ()
    (λ _ => do
      while_ME (λ _ => do (pure (LT.lt (← readReg r) n))) ()
        (λ _ => do
          if (GT.gt n 5)
          then return (early_return
                 (false : Bool))
          else (pure (cont (← writeReg r ((← readReg r) + 1)))))))
  (pure (GT.gt (← readReg r) n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def while_inner_earlyreturnpure (n : Nat) : Bool := Id.run do
  let res : Nat := 0
  let res : Nat ← do
    catchEarlyReturnPure
    (while_E (λ res => (LT.lt res n)) res
      (λ res => Id.run do
        while_E (λ res => (LT.lt res n)) res
          (λ res => Id.run do
            if (GT.gt n 5)
            then return (early_return
                   (false : Bool))
            else (cont (res + 1)))))
  (pure (GT.gt res n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def while_inner_earlyreturneffect_catch (n : Nat) : SailM Bool := do
  catchEarlyReturn
  (while_ME (λ _ => do (pure (LT.lt (← readReg r) n))) ()
    (λ _ => do
      catchEarlyReturnInner
      (while_ME (λ _ => do (pure (LT.lt (← readReg r) n))) ()
        (λ _ => do
          if (GT.gt n 5)
          then return (early_return
                 (false : Bool))
          else (pure (cont (← writeReg r ((← readReg r) + 1))))))
      (pure (cont (← do
            writeReg r ((← readReg r) * 2))))))
  (pure (GT.gt (← readReg r) n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def while_inner_earlyreturnpure_catch (n : Nat) : Bool := Id.run do
  let res : Nat := 0
  let res : Nat ← do
    catchEarlyReturnPure
    (while_E (λ res => (LT.lt res n)) res
      (λ res => Id.run do
        let res : Nat ← do
          catchEarlyReturnPureInner
          (while_E (λ res => (LT.lt res n)) res
            (λ res => Id.run do
              if (GT.gt n 5)
              then return (early_return
                     (false : Bool))
              else (cont (res + 1))))
        (cont (res * 2))))
  (pure (GT.gt res n))

def match_early_return (x : E) : SailM E := do
  match x with
  | A =>
    return (← do
        readReg r_A)
  | B => writeReg r_B A
  | C => writeReg r_C A
  readReg r_B

def match_early_return_inloop (x : E) : SailM E := do
  let loop_i_lower := 0
  let loop_i_upper := 10
  catchEarlyReturn
  (foreach_ME loop_i_lower loop_i_upper 1 ()
    (λ i _ => do
      match x with
      | A =>
        return (early_return
          (← do
            readReg r_A))
      | B => (pure (cont (← writeReg r_B A)))
      | C => (pure (cont (← writeReg r_C A)))))
  readReg r_B

def match_early_return_inloop_2 (x : E) : SailM E := do
  let loop_i_lower := 0
  let loop_i_upper := 10
  catchEarlyReturn
  (foreach_ME loop_i_lower loop_i_upper 1 ()
    (λ i _ => do
      let y : E ← do
        match x with
        | A =>
          return (early_return
            (← do
              readReg r_A))
        | B => readReg r_B
        | C => readReg r_C
      (pure (cont ()))))
  readReg r_B

def match_early_return_loop (x : E) : SailM E := do
  match x with
  | A =>
    let loop_i_lower := 0
    let loop_i_upper := 10
    catchEarlyReturn
    (foreach_ME loop_i_lower loop_i_upper 1 ()
      (λ i _ => do
        return (early_return
          (← do
            readReg r_A))))
  | B => writeReg r_B A
  | C => writeReg r_C A
  readReg r_B

/-- Type quantifiers: k_ex2655# : Bool -/
def ite_early_return (x : Bool) : SailM E := do
  writeReg r_A (← readReg r_C)
  let y : E ← do
    if x
    then return (← do
             readReg r_A)
    else readReg r_B
  readReg r_B

/-- Type quantifiers: k_ex2657# : Bool -/
def ite_early_return_inloop (x : Bool) : SailM E := do
  let loop_i_lower := 0
  let loop_i_upper := 10
  catchEarlyReturn
  (foreach_ME loop_i_lower loop_i_upper 1 ()
    (λ i _ => do
      writeReg r_A (← readReg r_C)
      let y : E ← do
        if x
        then return (early_return
               (← do
                 readReg r_A))
        else readReg r_B
      (pure (cont ()))))
  readReg r_B

/-- Type quantifiers: k_ex2661# : Bool -/
def ite_early_return_loop (x : Bool) : SailM E := do
  if x
  then let loop_i_lower := 0
       let loop_i_upper := 10
       catchEarlyReturn
       (foreach_ME loop_i_lower loop_i_upper 1 ()
         (λ i _ => do
           return (early_return
             (← do
               readReg r_A))))
  else writeReg r_B A
  readReg r_B

def unit_type (x : E) : SailM Unit := do
  writeReg r_A x

/-- Type quantifiers: k_ex2665# : Bool -/
def ite_early_return_seq (x : Bool) : SailM E := do
  writeReg r_A (← readReg r_C)
  let y : E ← do
    if x
    then return (← do
             (unit_type A)
             readReg r_A)
    else readReg r_B
  readReg r_B

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg r_A (← (undefined_E ()))
  writeReg r_B (← (undefined_E ()))
  writeReg r_C (← (undefined_E ()))
  writeReg r (← (undefined_nat ()))

end Functions
open Functions

