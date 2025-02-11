import Std.Data.DHashMap
import Std.Data.HashMap
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

class Arch where
  va_size : Nat
  pa : Type
  arch_ak : Type
  translation : Type
  abort : Type
  barrier : Type
  cache_op : Type
  tlb_op : Type
  fault : Type
  sys_reg_id : Type

/- The Units are placeholders for a future implementation of the state monad some Sail functions use. -/
inductive Error where
  | Exit
  | Unreachable
  | UninitializedMemory
  | Assertion (s : String)
open Error

structure SequentialState (RegisterType : Register → Type) (c : ChoiceSource) where
  regs : Std.DHashMap Register RegisterType
  choiceState : c.α
  mem : Std.HashMap Nat (BitVec 8)
  tags : Unit

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

section concurrency_interface

inductive Access_variety where
| AV_plain
| AV_exclusive
| AV_atomic_rmw
export Access_variety (AV_plain AV_exclusive AV_atomic_rmw)

inductive Access_strength where
| AS_normal
| AS_rel_or_acq
| AS_acq_rcpc
export Access_strength(AS_normal AS_rel_or_acq AS_acq_rcpc)

structure Explicit_access_kind where
  variety : Access_variety
  strength : Access_strength

inductive Access_kind (arch : Type) where
  | AK_explicit (_ : Explicit_access_kind)
  | AK_ifetch (_ : Unit)
  | AK_ttw (_ : Unit)
  | AK_arch (_ : arch)
export Access_kind(AK_explicit AK_ifetch AK_ttw AK_arch)

inductive Result (α : Type) (β : Type) where
  | Ok (_ : α)
  | Err (_ : β)
export Result(Ok Err)

structure Mem_read_request
  (n : Nat) (vasize : Nat) (pa : Type) (ts : Type) (arch_ak : Type) where
  access_kind : Access_kind arch_ak
  va : (Option (BitVec vasize))
  pa : pa
  translation : ts
  size : Int
  tag : Bool

structure Mem_write_request
  (n : Nat) (vasize : Nat) (pa : Type) (ts : Type) (arch_ak : Type) where
  access_kind : Access_kind arch_ak
  va : (Option (BitVec vasize))
  pa : pa
  translation : ts
  size : Int
  value : (Option (BitVec (8 * n)))
  tag : (Option Bool)

def write_byte (addr : Nat) (value : BitVec 8) : PreSailM RegisterType c PUnit := do
  modify fun s => { s with mem := s.mem.insert addr value }
  pure ()

def write_bytes (addr : Nat) (value : BitVec (8 * n)) : PreSailM RegisterType c Bool := do
  let list := List.ofFn (λ i : Fin n => (addr + i, value.extractLsb' (8 * i) 8))
  List.forM list (λ (a, v) => write_byte a v)
  pure true

def sail_mem_write [Arch] (req : Mem_write_request n vasize (BitVec pa_size) ts arch) : PreSailM RegisterType c (Result (Option Bool) Arch.abort) := do
  let addr := req.pa.toNat
  let b ← match req.value with
    | some v => write_bytes addr v
    | none => pure true
  pure (Ok (some b))

def read_byte (addr : Nat) : PreSailM RegisterType c (BitVec 8) := do
  let .some s := (← get).mem.get? addr
    | throw UninitializedMemory
  pure s

def read_bytes (size : Nat) (addr : Nat) : PreSailM RegisterType c ((BitVec (8 * size)) × (Option Bool)) :=
  match size with
  | 0 => pure (default, some true)
  | n + 1 => do
      let b ← read_byte addr
      let (bytes, bool) ← read_bytes n (addr+1)
      have h : 8 + 8 * n = 8 * (n + 1) := by omega
      return (h ▸ b.append bytes, bool)

def sail_mem_read [Arch] (req : Mem_read_request n vasize (BitVec pa_size) ts arch) : PreSailM RegisterType c (Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort) := do
  let addr := req.pa.toNat
  let value ← read_bytes n addr
  pure (Ok value)

def sail_barrier (_ : α) : PreSailM RegisterType c Unit := pure ()

end concurrency_interface

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

namespace Int

def intAbs (x : Int) : Int := Int.ofNat (Int.natAbs x)

end Int
end Sail
