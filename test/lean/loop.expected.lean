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
  deriving BEq

open option

inductive Register : Type where
  | r
  deriving DecidableEq, Hashable
open Register

abbrev RegisterType : Register → Type
  | .r => Int

open RegisterRef
instance : Inhabited (RegisterRef RegisterType Int) where
  default := .Reg r
abbrev SailM := PreSailM RegisterType trivialChoiceSource Unit

namespace Functions

/-- Type quantifiers: k_ex1485# : Bool, k_ex1484# : Bool -/
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

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreachloop (m : Nat) (n : Nat) : Int :=
  let res : Int := 0
  let loop_i_lower := m
  let loop_i_upper := n
  foreach_ loop_i_lower loop_i_upper 1 res (λ i res => (HAdd.hAdd res 1))

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreachloopmon (m : Nat) (n : Nat) : SailM Int := do
  let loop_i_lower := n
  let loop_i_upper := m
  foreach_M loop_i_lower loop_i_upper 1 () (λ i _ => do writeReg r (HAdd.hAdd (← readReg r) 1))
  readReg r

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreachloopboth (m : Nat) (n : Nat) : SailM Int := do
  let res : Int := 0
  let res : Int ← do
    let loop_i_lower := n
    let loop_i_upper := m
    foreach_M loop_i_lower loop_i_upper 1 res
      (λ i res => do
        let res : Int := (HAdd.hAdd res 1)
        writeReg r (HAdd.hAdd (← readReg r) res)
        (pure res))
  (pure (HAdd.hAdd res 1))

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreachloopmultiplevar (m : Nat) (n : Nat) : Int :=
  let res : Int := 0
  let mult : Int := 1
  let (mult, res) :=
    let loop_i_lower := m
    let loop_i_upper := n
    foreach_ loop_i_lower loop_i_upper 1 (mult, res)
      (λ i (mult, res) =>
        let res : Int := (HAdd.hAdd res 1)
        let mult : Int := (HMul.hMul res mult)
        (mult, res))
  mult

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreachloopuseindex (m : Nat) (n : Nat) : Nat :=
  let res : Nat := 0
  let loop_i_lower := m
  let loop_i_upper := n
  foreach_ loop_i_lower loop_i_upper 1 res (λ i res => (HAdd.hAdd res i))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def earlyreturneffect (n : Nat) : SailM Bool := do
  let loop_i_lower := 0
  let loop_i_upper := n
  catchEarlyReturn
  (foreach_ME loop_i_lower loop_i_upper 1 ()
    (λ i _ => do
      if (GT.gt i 5)
      then (pure (early_return (false : Bool)))
      else (pure (cont ((← writeReg r (HAdd.hAdd (← readReg r) 1)))))))
  (pure (GT.gt (← readReg r) n))

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def earlyreturnpure (n : Nat) : Bool := Id.run do
  let res : Nat := 0
  let res : Nat ← do
    let loop_i_lower := 0
    let loop_i_upper := n
    catchEarlyReturnPure
    (foreach_E loop_i_lower loop_i_upper 1 res
      (λ i res =>
        if (GT.gt i 5)
        then (early_return (false : Bool))
        else (cont ((HAdd.hAdd res i)))))
  (pure (GT.gt res n))

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg r (← (undefined_int ()))

end Functions

open Functions

