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

abbrev xlen : Int := 64

abbrev xlen_bytes : Int := 8

abbrev xlenbits := (BitVec 64)

abbrev regbits := (BitVec 5)

inductive iop where | RISCV_ADDI | RISCV_SLTI | RISCV_SLTIU | RISCV_XORI | RISCV_ORI | RISCV_ANDI
  deriving BEq, Inhabited, Repr
  open iop

inductive ast where
  | ITYPE (_ : ((BitVec 12) × regbits × regbits × iop))
  | LOAD (_ : ((BitVec 12) × regbits × regbits))
  deriving Inhabited, BEq, Repr
  open ast

inductive Register : Type where
  | Xs
  | nextPC
  | PC
  deriving DecidableEq, Hashable, Repr
open Register

abbrev RegisterType : Register → Type
  | .Xs => (Vector (BitVec 64) 32)
  | .nextPC => (BitVec 64)
  | .PC => (BitVec 64)

instance : Inhabited (RegisterRef RegisterType (BitVec 64)) where
  default := .Reg PC
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 32)) where
  default := .Reg Xs
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
open iop
open ast
open Register

/-- Type quantifiers: k_ex994_ : Bool, k_ex993_ : Bool -/
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

/-- Type quantifiers: k_n : Int, m : Int, m ≥ k_n -/
def EXTS {m : _} (v : (BitVec k_n)) : (BitVec m) :=
  (Sail.BitVec.signExtend v m)

/-- Type quantifiers: k_n : Int, m : Int, m ≥ k_n -/
def EXTZ {m : _} (v : (BitVec k_n)) : (BitVec m) :=
  (Sail.BitVec.zeroExtend v m)

/-- Type quantifiers: n : Nat, n ≥ 0 -/
def zeros (n : Nat) : (BitVec n) :=
  (BitVec.replicateBits 0#1 n)

def rX (r : (BitVec 5)) : SailM (BitVec 64) := do
  match r with
  | 0b00000 => (pure (EXTZ (m := 64) 0x0#4))
  | _ => (pure (GetElem?.getElem! (← readReg Xs) (BitVec.toNatInt r)))

def wX (r : (BitVec 5)) (v : (BitVec 64)) : SailM Unit := do
  if ((r != 0b00000#5) : Bool)
  then writeReg Xs (vectorUpdate (← readReg Xs) (BitVec.toNatInt r) v)
  else (pure ())

/-- Type quantifiers: width : Nat, width ≥ 0 -/
def read_mem (addr : (BitVec 64)) (width : Nat) : SailM (BitVec (8 * width)) := do
  (read_ram 64 width (EXTZ (m := 64) 0x0#4) addr)

def undefined_iop (_ : Unit) : SailM iop := do
  (internal_pick [RISCV_ADDI, RISCV_SLTI, RISCV_SLTIU, RISCV_XORI, RISCV_ORI, RISCV_ANDI])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def iop_of_num (arg_ : Nat) : iop :=
  match arg_ with
  | 0 => RISCV_ADDI
  | 1 => RISCV_SLTI
  | 2 => RISCV_SLTIU
  | 3 => RISCV_XORI
  | 4 => RISCV_ORI
  | _ => RISCV_ANDI

def num_of_iop (arg_ : iop) : Int :=
  match arg_ with
  | RISCV_ADDI => 0
  | RISCV_SLTI => 1
  | RISCV_SLTIU => 2
  | RISCV_XORI => 3
  | RISCV_ORI => 4
  | RISCV_ANDI => 5

def execute_LOAD (imm : (BitVec 12)) (rs1 : (BitVec 5)) (rd : (BitVec 5)) : SailM Unit := do
  let addr ← (( do (pure ((← (rX rs1)) + (EXTS (m := 64) imm))) ) : SailM xlenbits )
  let result ← (( do (read_mem addr 8) ) : SailM xlenbits )
  (wX rd result)

def execute_ITYPE (imm : (BitVec 12)) (rs1 : (BitVec 5)) (rd : (BitVec 5)) (id_3 : iop) : SailM Unit := do
  let rs1_val ← do (rX rs1)
  let imm_ext : xlenbits := (EXTS (m := 64) imm)
  let result := (rs1_val + imm_ext)
  (wX rd result)

def execute (merge_var : ast) : SailM Unit := do
  match merge_var with
  | .ITYPE (imm, rs1, rd, arg3) => (execute_ITYPE imm rs1 rd arg3)
  | .LOAD (imm, rs1, rd) => (execute_LOAD imm rs1 rd)
  | _ =>
    (do
      assert false "Pattern match failure at riscv_duopod.sail:138.0-142.1"
      throw Error.Exit)

def decode (merge_var : (BitVec 32)) : (Option ast) :=
  match_bv merge_var with
  | [imm:12,rs1:5,000,rd:5,0010011] => (some (ITYPE (imm, rs1, rd, RISCV_ADDI)))
  | [imm:12,rs1:5,011,rd:5,0000011] => (some (LOAD (imm, rs1, rd)))
  | _ => none

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg PC (← (undefined_bitvector 64))
  writeReg nextPC (← (undefined_bitvector 64))
  writeReg Xs (← (undefined_vector 32 (← (undefined_bitvector 64))))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  (initialize_registers ())

end Out.Functions
