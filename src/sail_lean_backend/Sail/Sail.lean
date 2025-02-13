import Std.Data.DHashMap
namespace Sail

section Regs

variable {Register : Type} {RegisterType : Register → Type} [DecidableEq Register] [Hashable Register]

inductive Primitive where
  | bool
  | bit
  | int
  | nat
  | string
  | fin (n : Nat)
  | bitvector (n : Nat)

abbrev Primitive.reflect : Primitive → Type
  | bool => Bool
  | bit => BitVec 1
  | int => Int
  | nat => Nat
  | string => String
  | fin n => Fin (n + 1)
  | bitvector n => BitVec n

structure ChoiceSource where
  (α : Type)
  (nextState : Primitive → α → α)
  (choose : ∀ p : Primitive, α → p.reflect)

def trivialChoiceSource : ChoiceSource where
  α := Unit
  nextState _ _ := ()
  choose p _ :=
    match p with
    | .bool => false
    | .bit => 0
    | .int => 0
    | .nat => 0
    | .string => ""
    | .fin _ => 0
    | .bitvector _ => 0

/- The Units are placeholders for a future implementation of the state monad some Sail functions use. -/
inductive Error where
  | Exit
  | Unreachable
  | Assertion (s : String)
open Error

def Error.print : Error → String
| Exit => "Exit"
| Unreachable => "Unreachable"
| Assertion s => s!"Assertion failed: {s}"

structure SequentialState (RegisterType : Register → Type) (c : ChoiceSource) where
  regs : Std.DHashMap Register RegisterType
  choiceState : c.α
  mem : Unit
  tags : Unit
  sail_output : Array String -- TODO: be able to use the IO monad to run

inductive RegisterRef (RegisterType : Register → Type) : Type → Type where
  | Reg (r : Register) : RegisterRef _ (RegisterType r)

abbrev PreSailM (RegisterType : Register → Type) (c : ChoiceSource) :=
  EStateM Error (SequentialState RegisterType c)

def choose (p : Primitive) : PreSailM RegisterType c p.reflect :=
  modifyGet
    (fun σ => (c.choose _ σ.choiceState, { σ with choiceState := c.nextState p σ.choiceState }))

def undefined_bit (_ : Unit) : PreSailM RegisterType c (BitVec 1) :=
  choose .bit

def undefined_bool (_ : Unit) : PreSailM RegisterType c Bool :=
  choose .bool

def undefined_int (_ : Unit) : PreSailM RegisterType c Int :=
  choose .int

def undefined_nat (_ : Unit) : PreSailM RegisterType c Nat :=
  choose .nat

def undefined_string (_ : Unit) : PreSailM RegisterType c String :=
  choose .string

def undefined_bitvector (n : Nat) : PreSailM RegisterType c (BitVec n) :=
  choose <| .bitvector n

def undefined_vector (n : Nat) (a : α) : PreSailM RegisterType c (Vector α n) :=
  pure <| .mkVector n a

def internal_pick {α : Type} : List α → PreSailM RegisterType c α
  | [] => .error .Unreachable
  | (a :: as) => do
    let idx ← choose <| .fin (as.length)
    pure <| (a :: as).get idx

def writeReg (r : Register) (v : RegisterType r) : PreSailM RegisterType c PUnit :=
  modify fun s => { s with regs := s.regs.insert r v }

def readReg (r : Register) : PreSailM RegisterType c (RegisterType r) := do
  let .some s := (← get).regs.get? r
    | throw Unreachable
  pure s

def readRegRef (reg_ref : @RegisterRef Register RegisterType α) : PreSailM RegisterType c α := do
  match reg_ref with | .Reg r => readReg r

def writeRegRef (reg_ref : @RegisterRef Register RegisterType α) (a : α) :
  PreSailM RegisterType c Unit := do
  match reg_ref with | .Reg r => writeReg r a

def reg_deref (reg_ref : @RegisterRef Register RegisterType α) : PreSailM RegisterType c α :=
  readRegRef reg_ref

def vectorAccess [Inhabited α] (v : Vector α m) (n : Nat) := v[n]!

def vectorUpdate (v : Vector α m) (n : Nat) (a : α) := v.set! n a

def assert (p : Bool) (s : String) : PreSailM RegisterType c Unit :=
  if p then pure () else throw (Assertion s)

/- def print_effect (s : String) : IO Unit := IO.print s -/

def print_effect (str : String) : PreSailM RegisterType c Unit :=
  modify fun s ↦ { s with sail_output := s.sail_output.push str }

def print_endline_effect (str : String) : PreSailM RegisterType c Unit :=
  print_effect s!"{str}\n"

def main_of_sail_main (initialState : SequentialState RegisterType c) (main : Unit → PreSailM RegisterType c Unit) : IO Unit := do
  let res := main () |>.run initialState
  match res with
  | .ok _ s => do
    for m in s.sail_output do
      IO.print m
  | .error e _ => do
    IO.println s!"Error while running the sail program!: {e.print}"

end Regs

namespace BitVec

def length {w : Nat} (_ : BitVec w) : Nat := w

def signExtend {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' :=
  x.signExtend w'

def zeroExtend {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' :=
  x.zeroExtend w'

def truncate {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' :=
  x.truncate w'

def truncateLsb {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' :=
  x.extractLsb' (w - w') w'

def extractLsb {w : Nat} (x : BitVec w) (hi lo : Nat) : BitVec (hi - lo + 1) :=
  x.extractLsb hi lo

def updateSubrange' {w : Nat} (x : BitVec w) (start len : Nat) (y : BitVec len) : BitVec w :=
  let mask := ~~~(((BitVec.allOnes len).zeroExtend w) <<< start)
  let y' := mask ||| ((y.zeroExtend w) <<< start)
  x &&& y'

def updateSubrange {w : Nat} (x : BitVec w) (hi lo : Nat) (y : BitVec (hi - lo + 1)) : BitVec w :=
  updateSubrange' x lo _ y

def replicateBits {w : Nat} (x : BitVec w) (i : Nat) := BitVec.replicate i x

def access {w : Nat} (x : BitVec w) (i : Nat) : BitVec 1 :=
  BitVec.ofBool x[i]!

def addInt {w : Nat} (x : BitVec w) (i : Int) : BitVec w :=
  x + BitVec.ofInt w i

end BitVec

namespace Nat

-- NB: below is taken from Mathlib.Logic.Function.Iterate
/-- Iterate a function. -/
def iterate {α : Sort u} (op : α → α) : Nat → α → α
  | 0, a => a
  | Nat.succ k, a => iterate op k (op a)

end Nat

namespace Int

def intAbs (x : Int) : Int := Int.ofNat (Int.natAbs x)

def shiftl (a : Int) (n : Int) : Int :=
  match n with
  | Int.ofNat n => Sail.Nat.iterate (fun x => x * 2) n a
  | Int.negSucc n => Sail.Nat.iterate (fun x => x / 2) (n+1) a

def shiftr (a : Int) (n : Int) : Int :=
  match n with
  | Int.ofNat n => Sail.Nat.iterate (fun x => x / 2) n a
  | Int.negSucc n => Sail.Nat.iterate (fun x => x * 2) (n+1) a

end Int
end Sail
