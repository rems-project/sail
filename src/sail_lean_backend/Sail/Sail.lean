import THE_MODULE_NAME.Sail.Attr

import Std.Data.ExtDHashMap
import Std.Data.ExtHashMap

namespace Sail

namespace BitVec

abbrev length {w : Nat} (_ : BitVec w) : Nat := w

@[simp_sail]
def toNatInt {w : Nat} (x : BitVec w) : Int :=
  Int.ofNat x.toNat

@[simp_sail]
def signExtend {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' :=
  x.signExtend w'

@[simp_sail]
def zeroExtend {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' :=
  x.zeroExtend w'

@[simp_sail]
def truncate {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' :=
  x.truncate w'

@[simp_sail]
def truncateLsb {w : Nat} (x : BitVec w) (w' : Nat) : BitVec w' :=
  x.extractLsb' (w - w') w'

@[simp_sail]
def extractLsb {w : Nat} (x : BitVec w) (hi lo : Nat) : BitVec (hi - lo + 1) :=
  x.extractLsb hi lo

@[simp_sail]
def updateSubrange' {w : Nat} (x : BitVec w) (start len : Nat) (y : BitVec len) : BitVec w :=
  let mask := ~~~(((BitVec.allOnes len).zeroExtend w) <<< start)
  let y' := ((y.zeroExtend w) <<< start)
  (mask &&& x) ||| y'

@[simp_sail]
def slice {w : Nat} (x : BitVec w) (start len : Nat) : BitVec len :=
  x.extractLsb' start len

@[simp_sail]
def sliceBE {w : Nat} (x : BitVec w) (start len : Nat) : BitVec len :=
  x.extractLsb' (w - start - len) len

@[simp_sail]
def subrangeBE {w : Nat} (x : BitVec w) (lo hi : Nat) : BitVec (hi - lo + 1) :=
  x.extractLsb' (w - hi - 1) _

@[simp_sail]
def updateSubrange {w : Nat} (x : BitVec w) (hi lo : Nat) (y : BitVec (hi - lo + 1)) : BitVec w :=
  updateSubrange' x lo _ y

@[simp_sail]
def updateSubrangeBE {w : Nat} (x : BitVec w) (lo hi : Nat) (y : BitVec (hi - lo + 1)) : BitVec w :=
  updateSubrange' x (w - hi - 1) _ y

@[simp_sail]
def replicateBits {w : Nat} (x : BitVec w) (i : Nat) := BitVec.replicate i x

@[simp_sail]
def access {w : Nat} (x : BitVec w) (i : Nat) : BitVec 1 :=
  BitVec.ofBool x[i]!

@[simp_sail]
def accessBE {w : Nat} (x : BitVec w) (i : Nat) : BitVec 1 :=
  BitVec.ofBool x[w - i - 1]!

@[simp_sail]
def addInt {w : Nat} (x : BitVec w) (i : Int) : BitVec w :=
  x + BitVec.ofInt w i

@[simp_sail]
def subInt (x : BitVec w) (i : Int) : BitVec w :=
  x - BitVec.ofInt w i

@[simp_sail]
def countLeadingZeros (x : BitVec w) : Nat := x.clz.toNat

@[simp_sail]
def countTrailingZeros (x : BitVec w) : Nat :=
  countLeadingZeros (x.reverse)

@[simp_sail]
def append' (x : BitVec n) (y : BitVec m) {mn}
    (hmn : mn = n + m := by (conv => rhs; simp); try rfl) : BitVec mn :=
  (x.append y).cast hmn.symm

@[simp_sail]
def update (x : BitVec m) (n : Nat) (b : BitVec 1) := updateSubrange' x n _ b

@[simp_sail]
def updateBE (x : BitVec m) (n : Nat) (b : BitVec 1) := updateSubrange' x (m - n - 1) _ b

def toBin {w : Nat} (x : BitVec w) : String :=
  String.ofList (List.map (fun c => if c then '1' else '0') (List.ofFn (BitVec.getMsb x)))

def toFormatted {w : Nat} (x : BitVec w) : String :=
  if (length x % 4) == 0 then
    s!"0x{String.toUpper (BitVec.toHex x)}"
  else
    s!"0b{BitVec.toBin x}"

@[simp_sail]
def join1 (xs : List (BitVec 1)) : BitVec xs.length :=
  (BitVec.ofBoolListBE (xs.map fun x => x[0])).cast (by simp)

instance (priority := low) : Coe (BitVec (1 * n)) (BitVec n) where
  coe x := x.cast (by simp)

end BitVec

def charToHex (c : Char) : BitVec 4 :=
  match c.toLower with
  | '0' => 0 | '1' => 1 | '2' => 2 | '3' => 3 | '4' => 4
  | '5' => 5 | '6' => 6 | '7' => 7 | '8' => 8 | '9' => 9
  | 'a' => 10 | 'b' => 11 | 'c' => 12 | 'd' => 13
  | 'e' => 14 | 'f' => 15 | _ => 0

def round4 (n : Nat) := ((n - 1) / 4) * 4 + 4

def parse_hex_bits_digits (n : Nat) (str : String) : BitVec n :=
  let len := str.length
  if h : n < 4 || len = 0 then BitVec.zero n else
    let bv := parse_hex_bits_digits (n-4) (str.take (len-1))
    let c := String.Pos.Raw.get! str ⟨len-1⟩ |> charToHex
    BitVec.append bv c |>.cast (by simp_all)
decreasing_by simp_all <;> omega

def parse_dec_bits (n : Nat) (str : String) : BitVec n :=
  go str.length str
where
  -- TODO: when there are lemmas about `String.take`, replace with WF induction
  go (fuel : Nat) (str : String) :=
    if fuel = 0 then 0 else
      let lsd := String.Pos.Raw.get! str ⟨str.length - 1⟩
      let rest := str.take (str.length - 1)
      (charToHex lsd).setWidth n + 10#n * go (fuel-1) rest

def parse_hex_bits (n : Nat) (str : String) : BitVec n :=
  let bv := parse_hex_bits_digits (round4 n) (str.drop 2)
  bv.setWidth n

def valid_hex_bits (n : Nat) (str : String) : Bool :=
  if str.length < 2 then false else
  let str := str.drop 2
  str.all fun x => x.toLower ∈
    ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f'] &&
  2 ^ n > (parse_hex_bits_digits (round4 n) str).toNat

def valid_dec_bits (_ : Nat) (str : String) : Bool :=
  str.all fun x => x.toLower ∈
    ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']

@[simp_sail]
def shift_bits_left (bv : BitVec n) (sh : BitVec m) : BitVec n :=
  bv <<< sh

@[simp_sail]
def shift_bits_right (bv : BitVec n) (sh : BitVec m) : BitVec n :=
  bv >>> sh

@[simp_sail]
def shiftl (bv : BitVec n) (m : Nat) : BitVec n :=
  bv <<< m

@[simp_sail]
def shiftr (bv : BitVec n) (m : Nat) : BitVec n :=
  bv >>> m

@[simp_sail]
def pow2 := (2 ^ ·)

namespace Nat

-- NB: below is taken from Mathlib.Logic.Function.Iterate
/-- Iterate a function. -/
def iterate {α : Sort u} (op : α → α) : Nat → α → α
  | 0, a => a
  | Nat.succ k, a => iterate op k (op a)

def toHex (n : Nat) : String :=
  have nbv : BitVec (Nat.log2 n + 1) := BitVec.ofNat _ n
  "0x" ++ nbv.toHex

def toHexUpper (n : Nat) : String :=
  have nbv : BitVec (Nat.log2 n + 1) := BitVec.ofNat _ n
  "0x" ++ nbv.toHex.toUpper

end Nat

namespace Int

def intAbs (x : Int) : Int := Int.ofNat (Int.natAbs x)

@[simp_sail]
def shiftl (a : Int) (n : Int) : Int :=
  match n with
  | Int.ofNat n => Sail.Nat.iterate (fun x => x * 2) n a
  | Int.negSucc n => Sail.Nat.iterate (fun x => x / 2) (n+1) a

@[simp_sail]
def shiftr (a : Int) (n : Int) : Int :=
  match n with
  | Int.ofNat n => Sail.Nat.iterate (fun x => x / 2) n a
  | Int.negSucc n => Sail.Nat.iterate (fun x => x * 2) (n+1) a


def toHex (i : Int) : String :=
  match i with
  | Int.ofNat n => Nat.toHex n
  | Int.negSucc n => "-" ++ Nat.toHex (n+1)

def toHexUpper (i : Int) : String :=
  match i with
  | Int.ofNat n => Nat.toHexUpper n
  | Int.negSucc n => "-" ++ Nat.toHexUpper (n+1)

end Int

@[simp_sail]
def get_slice_int (len : Nat) (n : Int) (lo : Nat) : BitVec len :=
  BitVec.extractLsb' lo len (BitVec.ofInt (lo + len + 1) n)

@[simp_sail]
def set_slice_int (len : Nat) (n : Int) (lo : Nat) (x : BitVec len) : Int :=
  BitVec.toInt (BitVec.updateSubrange' (BitVec.ofInt len n) lo len x)

@[simp_sail]
def set_slice {n : Nat} (m : Nat) (bv : BitVec n) (start : Nat) (bv' : BitVec m) : BitVec n :=
  BitVec.updateSubrange' bv start m bv'

def String.leadingSpaces (s : String) : Nat :=
  s.length - (s.dropWhile (· = ' ')).length

abbrev Vector.length (_v : Vector α n) : Nat := n

@[simp_sail]
def vectorInit {n : Nat} (a : α) : Vector α n := Vector.replicate n a

@[simp_sail]
def vectorUpdate (v : Vector α m) (n : Nat) (a : α) := v.set! n a

@[simp_sail]
instance : HShiftLeft (BitVec w) Int (BitVec w) where
  hShiftLeft b i :=
    match i with
    | .ofNat n => BitVec.shiftLeft b n
    | .negSucc n => BitVec.ushiftRight b (n + 1)

@[simp_sail]
instance : HShiftRight (BitVec w) Int (BitVec w) where
  hShiftRight b i := b <<< (- i)

section PreSailTypes

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

class ConcurrencyInterfaceV1.Arch where
  va_size : Nat
  pa : Type
  arch_ak : Type
  translation : Type
  trans_start : Type
  trans_end : Type
  abort : Type
  barrier : Type
  cache_op : Type
  tlb_op : Type
  fault : Type
  sys_reg_id : Type

class ConcurrencyInterfaceV2.Arch where
  addr_size : Nat
  addr_space : Type
  CHERI : Bool
  cap_size_log : Nat

  mem_acc : Type
  mem_acc_is_explicit : mem_acc -> Bool
  mem_acc_is_ifetch : mem_acc -> Bool
  mem_acc_is_ttw : mem_acc -> Bool
  mem_acc_is_relaxed : mem_acc -> Bool
  mem_acc_is_rel_acq_rcpc : mem_acc -> Bool
  mem_acc_is_rel_acq_rcsc : mem_acc -> Bool
  mem_acc_is_standalone : mem_acc -> Bool
  mem_acc_is_exclusive : mem_acc -> Bool
  mem_acc_is_atomic_rmw : mem_acc -> Bool

  trans_start : Type
  trans_end : Type
  abort : Type
  barrier : Type
  cache_op : Type
  tlbi : Type
  exn : Type
  sys_reg_id : Type


/- The Units are placeholders for a future implementation of the state monad some Sail functions use. -/
inductive Error (ue: Type) where
  | Exit
  | Unreachable
  | OutOfMemoryRange (n : Nat)
  | Assertion (s : String)
  | User (e : ue)
open Error

def Error.print : Error UE → String
  | Exit => "Exit"
  | Unreachable => "Unreachable"
  | OutOfMemoryRange n => s!"{n} Out of Memory Range"
  | Assertion s => s!"Assertion failed: {s}"
  | User _ => "Uncaught user exception"

inductive Result (α : Type) (β : Type) where
  | Ok (_ : α)
  | Err (_ : β)
  deriving Repr
export Result(Ok Err)

namespace ConcurrencyInterfaceV1

inductive Access_variety where
  | AV_plain
  | AV_exclusive
  | AV_atomic_rmw
  deriving Inhabited, DecidableEq, Repr

export Access_variety (AV_plain AV_exclusive AV_atomic_rmw)

inductive Access_strength where
  | AS_normal
  | AS_rel_or_acq
  | AS_acq_rcpc
  deriving Inhabited, DecidableEq, Repr

export Access_strength(AS_normal AS_rel_or_acq AS_acq_rcpc)

structure Explicit_access_kind where
  variety : Access_variety
  strength : Access_strength
deriving Repr

inductive Access_kind (arch : Type) where
  | AK_explicit (_ : Explicit_access_kind)
  | AK_ifetch (_ : Unit)
  | AK_ttw (_ : Unit)
  | AK_arch (_ : arch)
  deriving Inhabited, Repr

export Access_kind(AK_explicit AK_ifetch AK_ttw AK_arch)


structure Mem_read_request
  (n : Nat) (vasize : Nat) (pa : Type) (ts : Type) (arch_ak : Type) where
  access_kind : Access_kind arch_ak
  va : (Option (BitVec vasize))
  pa : pa
  translation : ts
  size : Int
  tag : Bool
  deriving Inhabited, Repr

structure Mem_write_request
  (n : Nat) (vasize : Nat) (pa : Type) (ts : Type) (arch_ak : Type) where
  access_kind : Access_kind arch_ak
  va : (Option (BitVec vasize))
  pa : pa
  translation : ts
  size : Int
  value : (Option (BitVec (8 * n)))
  tag : (Option Bool)
  deriving Inhabited, Repr

end ConcurrencyInterfaceV1

namespace ConcurrencyInterfaceV2

attribute [reducible] Arch.exn Arch.cache_op Arch.barrier Arch.trans_start Arch.trans_end Arch.tlbi

structure Mem_request (n : Nat) (nt : Nat) (addr_size : Nat) (addr_space : Type) (mem_acc : Type) where
  access_kind : mem_acc
  address : BitVec addr_size
  address_space : addr_space
  size : Nat
  num_tag : Nat

end ConcurrencyInterfaceV2

end PreSailTypes

def print_int : String → Int → Unit := fun _ _ => ()

def prerr_int : String → Int → Unit := fun _ _ => ()

def prerr_bits: String → BitVec n → Unit := fun _ _ => ()

def print_endline : String → Unit := fun _  => ()

def prerr_endline : String → Unit := fun _ => ()

def print : String → Unit := fun _ => ()

def prerr : String → Unit := fun _ => ()

end Sail

namespace PreSail

open Sail

section Regs

variable {Register : Type} {RegisterType : Register → Type} [DecidableEq Register] [Hashable Register]

structure SequentialState (RegisterType : Register → Type) (c : ChoiceSource) where
  regs : Std.ExtDHashMap Register RegisterType
  choiceState : c.α
  mem : Std.ExtHashMap Nat (BitVec 8)
  tags : Unit
  cycleCount : Nat -- Part of the concurrency interface. See `{get_}cycle_count`
  sailOutput : Array String -- TODO: be able to use the IO monad to run

inductive RegisterRef (RegisterType : Register → Type) : Type → Type where
  | Reg (r : Register) : RegisterRef _ (RegisterType r)
export RegisterRef (Reg)

abbrev PreSailM (RegisterType : Register → Type) (c : ChoiceSource) (ue: Type) :=
  EStateM (Error ue) (SequentialState RegisterType c)

@[simp_sail]
def sailTryCatch (e : PreSailM RegisterType c ue α) (h : ue → PreSailM RegisterType c ue α) :
    PreSailM RegisterType c ue α :=
  EStateM.tryCatch e fun e =>
    match e with
    | .User u => h u
    | _ => EStateM.throw e

@[simp_sail]
def sailThrow (e : ue) : PreSailM RegisterType c ue α := EStateM.throw (.User e)

def choose (p : Primitive) : PreSailM RegisterType c ue p.reflect :=
  modifyGet
    (fun σ => (c.choose _ σ.choiceState, { σ with choiceState := c.nextState p σ.choiceState }))

def undefined_unit (_ : Unit) : PreSailM RegisterType c ue Unit := pure ()

def undefined_bit (_ : Unit) : PreSailM RegisterType c ue (BitVec 1) :=
  choose .bit

def undefined_bool (_ : Unit) : PreSailM RegisterType c ue Bool :=
  choose .bool

def undefined_int (_ : Unit) : PreSailM RegisterType c ue Int :=
  choose .int

def undefined_range (low high : Int) : PreSailM RegisterType c ue Int := do
  pure (low + (← choose .int) % (high - low))

def undefined_nat (_ : Unit) : PreSailM RegisterType c ue Nat :=
  choose .nat

def undefined_string (_ : Unit) : PreSailM RegisterType c ue String :=
  choose .string

def undefined_bitvector (n : Nat) : PreSailM RegisterType c ue (BitVec n) :=
  choose <| .bitvector n

def undefined_vector (n : Nat) (a : α) : PreSailM RegisterType c ue (Vector α n) :=
  pure <| .replicate n a

def internal_pick {α : Type} : List α → PreSailM RegisterType c ue α
  | [] => .error .Unreachable
  | (a :: as) => do
    let idx ← choose <| .fin (as.length)
    pure <| (a :: as).get idx

@[simp_sail]
def writeReg (r : Register) (v : RegisterType r) : PreSailM RegisterType c ue PUnit :=
  modify fun s => { s with regs := s.regs.insert r v }

@[simp_sail]
def readReg (r : Register) : PreSailM RegisterType c ue (RegisterType r) := do
  let .some s := (← get).regs.get? r
    | throw .Unreachable
  pure s

@[simp_sail]
def readRegRef (reg_ref : @RegisterRef Register RegisterType α) : PreSailM RegisterType c ue α := do
  match reg_ref with | .Reg r => readReg r

@[simp_sail]
def writeRegRef (reg_ref : @RegisterRef Register RegisterType α) (a : α) :
  PreSailM RegisterType c ue Unit := do
  match reg_ref with | .Reg r => writeReg r a

@[simp_sail]
def reg_deref (reg_ref : @RegisterRef Register RegisterType α) : PreSailM RegisterType c ue α :=
  readRegRef reg_ref

@[simp_sail]
def assert (p : Bool) (s : String) : PreSailM RegisterType c ue Unit :=
  if p then pure () else throw (.Assertion s)

section ConcurrencyInterface

@[simp_sail]
def writeByte (addr : Nat) (value : BitVec 8) : PreSailM RegisterType c ue PUnit := do
  modify fun s => { s with mem := s.mem.insert addr value }

@[simp_sail]
def writeBytes (addr : Nat) (value : BitVec (8 * n)) : PreSailM RegisterType c ue Bool := do
  let list := List.ofFn (λ i : Fin n => (addr + i.val, value.extractLsb' (8 * i.val) 8))
  List.forM list (λ (a, v) => writeByte a v)
  pure true

@[simp_sail]
def writeByteVec (addr : Nat) (value : Vector (BitVec 8) n) : PreSailM RegisterType c ue Bool := do
  let list := List.ofFn (λ i : Fin n => (addr + i.val, value[i]))
  List.forM list (λ (a, v) => writeByte a v)
  pure true

@[simp_sail]
def write_ram (addr_size data_size : Nat) (_hex_ram addr : BitVec addr_size) (value : BitVec (8 * data_size)) :
    PreSailM RegisterType c ue Unit := do
  let _ ← writeBytes addr.toNat value
  pure ()

@[simp_sail]
def readByte (addr : Nat) : PreSailM RegisterType c ue (BitVec 8) := do
  let .some s := (← get).mem.get? addr
    | throw (.OutOfMemoryRange addr)
  pure s

@[simp_sail]
def readBytes (size : Nat) (addr : Nat) : PreSailM RegisterType c ue ((BitVec (8 * size)) × Option Bool) :=
  match size with
  | 0 => pure (default, none)
  | 1 => do
    let b ← readByte addr
    have h : 8 * 1 = 8 := rfl
    return (h ▸ b, none)
  | n + 1 => do
    let b ← readByte addr
    let (bytes, bool) ← readBytes n (addr+1)
    have h : 8 * n + 8 = 8 * (n + 1) := by omega
    return (h ▸ bytes.append b, bool)

@[simp_sail]
def readBytesVec (size : Nat) (addr : Nat) :
    PreSailM RegisterType c ue ((Vector (BitVec 8) size) × Vector Bool nt) :=
  match size with
  | 0 => pure (default, default)
  | 1 => do
    let b ← readByte addr
    return (#v[b], default)
  | n + 1 => do
    let b ← readByte (addr + n)
    let (bytes, bool) ← readBytesVec n addr
    return (bytes.push b, bool)

namespace ConcurrencyInterfaceV1

open Sail.ConcurrencyInterfaceV1

@[simp_sail]
def sail_mem_write [Arch] (req : Mem_write_request n vasize (BitVec pa_size) ts arch) : PreSailM RegisterType c ue (Result (Option Bool) Arch.abort) := do
  let addr := req.pa.toNat
  let b ← match req.value with
    | some v => writeBytes addr v
    | none => pure true
  pure (Ok (some b))

@[simp_sail]
def sail_mem_read [Arch] (req : Mem_read_request n vasize (BitVec pa_size) ts arch) : PreSailM RegisterType c ue (Result ((BitVec (8 * n)) × (Option Bool)) Arch.abort) := do
  let addr := req.pa.toNat
  let value ← readBytes n addr
  pure (Ok value)


@[simp_sail]
def sail_barrier (_ : α) : PreSailM RegisterType c ue Unit := pure ()
@[simp_sail]
def sail_cache_op [Arch] (_ : Arch.cache_op) : PreSailM RegisterType c ue Unit := pure ()
@[simp_sail]
def sail_tlbi [Arch] (_ : Arch.tlb_op) : PreSailM RegisterType c ue Unit := pure ()
@[simp_sail]
def sail_translation_start [Arch] (_ : Arch.trans_start) : PreSailM RegisterType c ue Unit := pure ()
@[simp_sail]
def sail_translation_end [Arch] (_ : Arch.trans_end) : PreSailM RegisterType c ue Unit := pure ()
@[simp_sail]
def sail_take_exception [Arch] (_ : Arch.fault) : PreSailM RegisterType c ue Unit := pure ()
@[simp_sail]
def sail_return_exception [Arch] (_ : Arch.pa) : PreSailM RegisterType c ue Unit := pure ()

end ConcurrencyInterfaceV1

namespace ConcurrencyInterfaceV2

open Sail.ConcurrencyInterfaceV2

@[simp_sail]
def sail_mem_read [Arch] (req : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc) :
    PreSailM RegisterType c ue (Result ((Vector (BitVec 8) n) × (Vector Bool nt)) Arch.abort) := do
  let addr := req.address.toNat
  let value ← readBytesVec n addr
  pure (Ok value)

def sail_mem_write [Arch] (req : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc) (valueBytes : Vector (BitVec 8) n) (_tags : Vector Bool nt) :
    PreSailM RegisterType c ue (Result (Option Bool) Arch.abort) := do
  let addr := req.address.toNat
  let b ← writeByteVec addr valueBytes
  pure (Ok (some b))

@[simp_sail]
def sail_sys_reg_read [Arch] (_id : Arch.sys_reg_id) (r : @RegisterRef Register RegisterType α) : PreSailM RegisterType c ue α :=
  readRegRef r

@[simp_sail]
def sail_sys_reg_write [Arch] (_id : Arch.sys_reg_id) (r : @RegisterRef Register RegisterType α) (v : α) :
    PreSailM RegisterType c ue Unit :=
  writeRegRef r v

def sail_mem_address_announce [Arch] (_ann : Mem_request n nt Arch.addr_size Arch.addr_space Arch.mem_acc) : PreSailM RegisterType c ue Unit :=
  pure ()

@[simp_sail]
def sail_translation_start [Arch] (_ : Arch.trans_start) : PreSailM RegisterType c ue Unit := pure ()

@[simp_sail]
def sail_translation_end [Arch] (_ : Arch.trans_end) : PreSailM RegisterType c ue Unit := pure ()

@[simp_sail]
def sail_barrier [Arch] (_ : Arch.barrier) : PreSailM RegisterType c ue Unit := pure ()

@[simp_sail]
def sail_take_exception [Arch] (_ : Arch.exn) : PreSailM RegisterType c ue Unit := pure ()

@[simp_sail]
def sail_return_exception (_ : Unit) : PreSailM RegisterType c ue Unit := pure ()

@[simp_sail]
def sail_cache_op [Arch] (_ : Arch.cache_op) : PreSailM RegisterType c ue Unit := pure ()

@[simp_sail]
def sail_tlbi [Arch] (_ : Arch.tlbi) : PreSailM RegisterType c ue Unit := pure ()

end ConcurrencyInterfaceV2

@[simp_sail]
def read_ram (addr_size data_size : Nat) (_hex_ram addr : BitVec addr_size) : PreSailM RegisterType c ue (BitVec (8 * data_size)) := do
  let ⟨bytes, _⟩ ← readBytes data_size addr.toNat
  pure bytes

@[simp_sail]
def cycle_count (_ : Unit) : PreSailM RegisterType c ue Unit :=
  modify fun s => { s with cycleCount := s.cycleCount + 1 }

@[simp_sail]
def get_cycle_count (_ : Unit) : PreSailM RegisterType c ue Nat := do
  pure (← get).cycleCount

end ConcurrencyInterface

def print_effect (str : String) : PreSailM RegisterType c ue Unit :=
  modify fun s ↦ { s with sailOutput := s.sailOutput.push str }

def print_int_effect (str : String) (n : Int) : PreSailM RegisterType c ue Unit :=
  print_effect s!"{str}{n}\n"

def print_bits_effect {w : Nat} (str : String) (x : BitVec w) : PreSailM RegisterType c ue Unit :=
  print_effect s!"{str}{BitVec.toFormatted x}\n"

def print_endline_effect (str : String) : PreSailM RegisterType c ue Unit :=
  print_effect s!"{str}\n"

@[simp_sail]
def sailTryCatchE (e : ExceptT β (PreSailM RegisterType c ue) α) (h : ue → ExceptT β (PreSailM RegisterType c ue) α) : ExceptT β (PreSailM RegisterType c ue) α :=
  EStateM.tryCatch e fun e =>
    match e with
    | .User u => h u
    | _ => EStateM.throw e

end Regs

section SailME

variable {Register : Type} {RT : Register → Type} [DecidableEq Register] [Hashable Register]

variable (RT) in
abbrev PreSailME c ue α := ExceptT (Error ue ⊕ α) (PreSailM RT c ue)

instance: MonadExceptOf (Error ue) (PreSailME RT c ue α) where
  throw e := MonadExcept.throw (.inl e)
  tryCatch x h := MonadExcept.tryCatch x (fun e => match e with | .inl e => h e | .inr _ => MonadExcept.throw e)

def PreSailME.run (m : PreSailME RT c ue α α) : PreSailM RT c ue α := do
  match (← ExceptT.run m) with
    | .error (.inr e) => pure e
    | .error (.inl e) => throw e
    | .ok e => pure e

def _root_.ExceptT.map_error [Monad m] (e : ExceptT ε m α) (f : ε → ε') : ExceptT ε' m α :=
  ExceptT.mk <| do
    match ← e.run with
    | .ok x => pure $ .ok x
    | .error e => pure $ .error (f e)

instance [∀ x, CoeT α x α'] :
    CoeT (PreSailME RT c ue α β) e (PreSailME RT c ue α' β) where
  coe := e.map_error (fun x => match x with | .inl e => .inl e | .inr e => .inr e)

def PreSailME.throw (e : α) : PreSailME RT c ue α β :=
    MonadExceptOf.throw (Sum.inr (α := Error ue) e)

instance : Inhabited (PreSail.SequentialState RT trivialChoiceSource) where
  default := ⟨default, (), default, default, default, default⟩

end SailME

end PreSail

abbrev ExceptM α := ExceptT α Id

def ExceptM.run (m : ExceptM α α) : α :=
  match (ExceptT.run m) with
    | .error e => e
    | .ok e => e

namespace Sail

open PreSail

variable {Register : Type} {RegisterType : Register → Type} [DecidableEq Register] [Hashable Register]

def main_of_sail_main (initialState : SequentialState RegisterType c) (main : Unit → PreSailM RegisterType c ue Unit) : IO UInt32 := do
  let res := main () |>.run initialState
  match res with
  | .ok _ s => do
    for m in s.sailOutput do
      IO.print m
    return 0
  | .error e s => do
    for m in s.sailOutput do
      IO.print m
    IO.eprintln s!"Error while running the sail program!: {e.print}"
    return 1

end Sail

def whileFuelM {α} [Monad m] (fuel : Nat) (cond : α → m Bool) (init : α) (f : α → m α)  :=
  let rec go x n := do
    match n with
    | 0 => pure x
    | n+1 =>
      if ←cond x then go (←f x) n else pure x
  go init fuel

def untilFuelM {α} [Monad m] (fuel : Nat) (cond : α → m Bool) (init : α) (f : α → m α)  :=
  let rec go x n := do
    match n with
    | 0 => pure x
    | n+1 =>
      let x ← f x
      if ←cond x then pure x else go x n
  go init fuel


instance : CoeT Int x Nat where
  coe := x.toNat

instance : CoeT (BitVec n) x (BitVec m) where
  coe := x.setWidth m

instance: CoeT (Vector (BitVec n₁) m) x (Vector (BitVec n₂) m) where
  coe := x.map fun (bv : BitVec n₁) => bv.setWidth n₂

instance {α α' β : Type u} (x : α × β) [CoeT α x.1 α'] : CoeT (α × β) x (α' × β) where
  coe := (x.1, x.2)

instance {α α' β : Type u} (x : β × α) [CoeT α x.2 α'] : CoeT (β × α) x (β × α') where
  coe := (x.1, x.2)

instance {α α' β β' : Type u} (x : α × β) [CoeT α x.1 α'] [CoeT β x.2 β'] : CoeT (α × β) x (α' × β') where
  coe := (x.1, x.2)

instance {α α' : Type u} [∀ x, CoeT α x α'] (xs : List α) : CoeT (List α) xs (List α') where
  coe := List.map (α := α) (β := α') (fun x => x) xs

instance (priority := low) : HAdd (BitVec n) (BitVec m) (BitVec n) where
  hAdd x y := x + y

instance (priority := low) : HSub (BitVec n) (BitVec m) (BitVec n) where
  hSub x y := x - y

instance (priority := low) : HAnd (BitVec n) (BitVec m) (BitVec n) where
  hAnd x y := x &&& y

instance (priority := low) : HOr (BitVec n) (BitVec m) (BitVec n) where
  hOr x y := x ||| y

instance (priority := low) : HXor (BitVec n) (BitVec m) (BitVec n) where
  hXor x y := x ^^^ y

instance [GetElem? coll Nat elem valid] : GetElem? coll Int elem (λ c i ↦ valid c i.toNat) where
  getElem c i h := c[i.toNat]'h
  getElem? c i := c[i.toNat]?

instance : HPow Int Int Int where
  hPow x n := x ^ n.toNat

infixl:65 " +i "   => fun (x y : Int) => x + y
infixl:65 " -i "   => fun (x y : Int) => x - y
infixl:65 " ^i "   => fun (x y : Int) => x ^ y
infixl:65 " *i "   => fun (x y : Int) => x * y

notation:50 x "≤b" y => decide (x ≤ y)
notation:50 x "<b" y => decide (x < y)
notation:50 x "≥b" y => decide (x ≥ y)
notation:50 x ">b" y => decide (x > y)

-- for termination measures, since they're almost always `Int`s but not always
abbrev Nat.toNat (x : Nat) := x

set_option grind.warning false
macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  first
  | grind
  | decide)

-- This lemma replaces `bif` by `if` in functions when Lean is trying to prove
-- termination.
@[wf_preprocess]
theorem cond_eq_ite (b : Bool) (x y : α) : cond b x y = ite b x y := by cases b <;> rfl
