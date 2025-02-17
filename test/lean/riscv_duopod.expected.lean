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

open option

abbrev xlen : Int := 64

abbrev xlen_bytes : Int := 8

abbrev xlenbits := (BitVec 64)

abbrev regbits := (BitVec 5)

inductive iop where | RISCV_ADDI | RISCV_SLTI | RISCV_SLTIU | RISCV_XORI | RISCV_ORI | RISCV_ANDI
  deriving Inhabited, DecidableEq

open iop


inductive ast where
  | ITYPE (_ : ((BitVec 12) × regbits × regbits × iop))
  | LOAD (_ : ((BitVec 12) × regbits × regbits))

open ast

inductive Register : Type where
  | Xs
  | nextPC
  | PC
  deriving DecidableEq, Hashable
open Register

abbrev RegisterType : Register → Type
  | .Xs => (Vector (BitVec 64) 32)
  | .nextPC => (BitVec 64)
  | .PC => (BitVec 64)

open RegisterRef
instance : Inhabited (RegisterRef RegisterType (BitVec 64)) where
  default := .Reg PC
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 32)) where
  default := .Reg Xs
abbrev SailM := PreSailM RegisterType trivialChoiceSource Unit

namespace Functions

/-- Type quantifiers: k_ex1030# : Bool, k_ex1029# : Bool -/
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
  (HAppend.hAppend str (BitVec.string_of_bits x))

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
  (BitVec.replicateBits (0b0 : (BitVec 1)) n)

def rX (r : (BitVec 5)) : SailM (BitVec 64) := do
  let b__0 := r
  if (BEq.beq b__0 (0b00000 : (BitVec 5)))
  then (pure (EXTZ (0x0 : (BitVec 4))))
  else (pure (vectorAccess (← readReg Xs) (BitVec.toNat r)))

def wX (r : (BitVec 5)) (v : (BitVec 64)) : SailM Unit := do
  if (bne r (0b00000 : (BitVec 5)))
  then writeReg Xs (vectorUpdate (← readReg Xs) (BitVec.toNat r) v)
  else (pure ())

/-- Type quantifiers: width : Nat, width ≥ 0 -/
def read_mem (addr : (BitVec 64)) (width : Nat) : SailM (BitVec (8 * width)) := do
  (read_ram 64 width (EXTZ (0x0 : (BitVec 4))) addr)

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
  let addr : xlenbits ← do (pure (HAdd.hAdd (← (rX rs1)) (EXTS imm)))
  let result : xlenbits ← do (read_mem addr 8)
  (wX rd result)

def execute_ITYPE (arg0 : (BitVec 12)) (arg1 : (BitVec 5)) (arg2 : (BitVec 5)) (arg3 : iop) : SailM Unit := do
  let merge_var := (arg0, arg1, arg2, arg3)
  match merge_var with
  | (imm, rs1, rd, RISCV_ADDI) =>
    let rs1_val ← do (rX rs1)
    let imm_ext : xlenbits := (EXTS imm)
    let result := (HAdd.hAdd rs1_val imm_ext)
    (wX rd result)
  | _ => throw Error.Exit

def execute (merge_var : ast) : SailM Unit := do
  match merge_var with
  | .ITYPE (imm, rs1, rd, arg3) => (execute_ITYPE imm rs1 rd arg3)
  | .LOAD (imm, rs1, rd) => (execute_LOAD imm rs1 rd)

def decode (v__0 : (BitVec 32)) : (Option ast) :=
  if (Bool.and (BEq.beq (Sail.BitVec.extractLsb v__0 14 12) (0b000 : (BitVec 3)))
       (BEq.beq (Sail.BitVec.extractLsb v__0 6 0) (0b0010011 : (BitVec 7))))
  then let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__0 31 20)
       let rs1 : regbits := (Sail.BitVec.extractLsb v__0 19 15)
       let rd : regbits := (Sail.BitVec.extractLsb v__0 11 7)
       let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__0 31 20)
       (some (ITYPE (imm, rs1, rd, RISCV_ADDI)))
  else if (Bool.and (BEq.beq (Sail.BitVec.extractLsb v__0 14 12) (0b011 : (BitVec 3)))
            (BEq.beq (Sail.BitVec.extractLsb v__0 6 0) (0b0000011 : (BitVec 7))))
       then let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__0 31 20)
            let rs1 : regbits := (Sail.BitVec.extractLsb v__0 19 15)
            let rd : regbits := (Sail.BitVec.extractLsb v__0 11 7)
            let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__0 31 20)
            (some (LOAD (imm, rs1, rd)))
       else none

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg PC (← (undefined_bitvector 64))
  writeReg nextPC (← (undefined_bitvector 64))
  writeReg Xs (← (undefined_vector 32 (← (undefined_bitvector 64))))

end Functions

open Functions

