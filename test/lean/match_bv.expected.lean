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

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource Unit

namespace Functions

/-- Type quantifiers: k_ex1669# : Bool, k_ex1668# : Bool -/
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

def decode (v__0 : (BitVec 32)) : Bool :=
  if (Bool.and (BEq.beq (Sail.BitVec.extractLsb v__0 31 24) (0xF8 : (BitVec 8)))
       (Bool.and (BEq.beq (Sail.BitVec.extractLsb v__0 21 21) (0b1 : (BitVec 1)))
         (BEq.beq (Sail.BitVec.extractLsb v__0 11 10) (0b10 : (BitVec 2)))))
  then let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
       let Rm : (BitVec 5) := (Sail.BitVec.extractLsb v__0 20 16)
       if (BEq.beq Rm Rn)
       then true
       else false
  else if (BEq.beq (Sail.BitVec.extractLsb v__0 30 24) (0b1001010 : (BitVec 7)))
       then let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
            let Rd : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
            if (BEq.beq Rn Rd)
            then true
            else false
       else if (Bool.and (BEq.beq (Sail.BitVec.extractLsb v__0 31 12) (0xD5033 : (BitVec 20)))
                 (BEq.beq (Sail.BitVec.extractLsb v__0 7 0) (0xBF : (BitVec 8))))
            then true
            else if (BEq.beq (Sail.BitVec.extractLsb v__0 31 24) (0xB4 : (BitVec 8)))
                 then false
                 else true

def xlen := 32

def write_CSR (v__26 : (BitVec 12)) : SailM Bool := do
  if (Bool.and (BEq.beq (Sail.BitVec.extractLsb v__26 11 5) (0b1011000 : (BitVec 7)))
       (let index : (BitVec 5) := (Sail.BitVec.extractLsb v__26 4 0)
       (GE.ge (BitVec.toNat index) 3) : Bool))
  then (pure true)
  else if (Bool.and (BEq.beq (Sail.BitVec.extractLsb v__26 11 5) (0b1011100 : (BitVec 7)))
            (let index : (BitVec 5) := (Sail.BitVec.extractLsb v__26 4 0)
            (Bool.and (BEq.beq xlen 32) ((GE.ge (BitVec.toNat index) 3) : Bool))))
       then (pure true)
       else assert false "Pattern match failure at match_bv.sail:36.0-38.1"
            throw Error.Exit

def write_CSR2 (v__30 : (BitVec 12)) : SailM Bool := do
  if (Bool.and (BEq.beq (Sail.BitVec.extractLsb v__30 11 5) (0b1011100 : (BitVec 7)))
       (let index : (BitVec 5) := (Sail.BitVec.extractLsb v__30 4 0)
       (Bool.and (BEq.beq xlen 32) ((GE.ge (BitVec.toNat index) 3) : Bool))))
  then (pure true)
  else assert false "Pattern match failure at match_bv.sail:41.0-43.1"
       throw Error.Exit

def initialize_registers (_ : Unit) : Unit :=
  ()

end Functions

open Functions

