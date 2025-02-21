import Out.Sail.Sail
import Out.Sail.BitVec

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

open option

inductive Register : Type where
  | r
  deriving DecidableEq, Hashable
open Register

abbrev RegisterType : Register → Type
  | .r => Nat

open RegisterRef
instance : Inhabited (RegisterRef RegisterType Nat) where
  default := .Reg r
abbrev SailM := PreSailM RegisterType trivialChoiceSource Unit

namespace Functions

/-- Type quantifiers: k_ex2319# : Bool, k_ex2318# : Bool -/
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
  then ((Int.tdiv (n + 1) m) - 1)
  else if (Bool.and (GT.gt n 0) (LT.lt m 0))
       then ((Int.tdiv (n - 1) m) - 1)
       else (Int.tdiv n m)

/-- Type quantifiers: m : Int, n : Int -/
def fmod_int (n : Int) (m : Int) : Int :=
  (n - (m * (fdiv_int n m)))

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
def foreach_loop (m : Nat) (n : Nat) : Nat :=
  let res : Nat := 0
  let loop_i_lower := m
  let loop_i_upper := n
  foreach_ loop_i_lower loop_i_upper 1 res (λ i res => (res + 1))

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreach_loopmon (m : Nat) (n : Nat) : SailM Nat := do
  let loop_i_lower := n
  let loop_i_upper := m
  foreach_M loop_i_lower loop_i_upper 1 () (λ i _ => do writeReg r ((← readReg r) + 1))
  readReg r

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreach_loopboth (m : Nat) (n : Nat) : SailM Nat := do
  let res : Nat := 0
  let res : Nat ← do
    let loop_i_lower := n
    let loop_i_upper := m
    foreach_M loop_i_lower loop_i_upper 1 res
      (λ i res => do
        let res : Int := (res + 1)
        writeReg r ((← readReg r) + res)
        (pure res))
  (pure (res + 1))

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreach_loopmultiplevar (m : Nat) (n : Nat) : Nat :=
  let res : Nat := 0
  let mult : Nat := 1
  let (mult, res) :=
    let loop_i_lower := m
    let loop_i_upper := n
    foreach_ loop_i_lower loop_i_upper 1 (mult, res)
      (λ i (mult, res) =>
        let res : Int := (res + 1)
        let mult : Int := (res * mult)
        (mult, res))
  mult

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreach_loopuseindex (m : Nat) (n : Nat) : Nat :=
  let res : Nat := 0
  let loop_i_lower := m
  let loop_i_upper := n
  foreach_ loop_i_lower loop_i_upper 1 res (λ i res => (res + i))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def foreach_earlyreturneffect (n : Nat) : SailM Bool := do
  let loop_i_lower := 0
  let loop_i_upper := n
  catchEarlyReturn
  (foreach_ME loop_i_lower loop_i_upper 1 ()
    (λ i _ => do
      if (GT.gt i 5)
      then (pure (early_return (false : Bool)))
      else (pure (cont ((← writeReg r ((← readReg r) + 1)))))))
  (pure (GT.gt (← readReg r) n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def foreach_earlyreturnpure (n : Nat) : Bool := Id.run do
  let res : Nat := 0
  let res : Nat ← do
    let loop_i_lower := 0
    let loop_i_upper := n
    catchEarlyReturnPure
    (foreach_E loop_i_lower loop_i_upper 1 res
      (λ i res =>
        if (GT.gt i 5)
        then (early_return (false : Bool))
        else (cont ((res + i)))))
  (pure (GT.gt res n))

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def while_loop (m : Nat) (n : Nat) : Nat :=
  let res : Nat := 0
  while_ (λ res => (LT.lt res n)) res (λ res => ((HAdd.hAdd res 1) : Nat))

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def while_loopmon (m : Nat) (n : Nat) : SailM Nat := do
  while_M (λ _ => do (pure (LT.lt (← readReg r) n))) ()
    (λ _ => do writeReg r (HAdd.hAdd (← readReg r) 1))
  readReg r

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def while_loopboth (m : Nat) (n : Nat) : SailM Nat := do
  let res : Nat := 0
  let res : Nat ← do
    while_M (λ res => do (pure (LT.lt res n))) res
      (λ res => do
        let res : Nat := (HAdd.hAdd res 1)
        writeReg r (HAdd.hAdd (← readReg r) res)
        (pure res))
  (pure (HAdd.hAdd res 1))

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def while_loopmultiplevar (m : Nat) (n : Nat) : Nat :=
  let res : Nat := 0
  let mult : Nat := 1
  let (mult, res) :=
    while_ (λ (mult, res) => (LT.lt res n)) (mult, res)
      (λ (mult, res) =>
        (let res : Nat := (HAdd.hAdd res 1)
        let mult : Nat := (HMul.hMul res mult)
        (mult, res) : (Nat × Nat)))
  mult

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def while_earlyreturneffect (n : Nat) : SailM Bool := do
  catchEarlyReturn
  (while_ME (λ _ => do (pure (LT.lt (← readReg r) n))) ()
    (λ _ => do
      if (GT.gt (← readReg r) 5)
      then (pure (early_return (false : Bool)))
      else (pure (cont ((← writeReg r (HAdd.hAdd (← readReg r) 1)))))))
  (pure (GT.gt (← readReg r) n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def while_earlyreturnpure (n : Nat) : Bool := Id.run do
  let res : Nat := 0
  let res : Nat ← do
    catchEarlyReturnPure
    (while_E (λ res => (LT.lt res n)) res
      (λ res =>
        if (GT.gt res 5)
        then (early_return (false : Bool))
        else (cont ((HAdd.hAdd res 1)))))
  (pure (GT.gt res n))

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg r (← (undefined_nat ()))

end Functions

open Functions

