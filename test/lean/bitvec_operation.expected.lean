import Out.Sail.Sail

def bitvector_eq (x : BitVec 16) (y : BitVec 16) : Bool :=
  (Eq x y)

def bitvector_neq (x : BitVec 16) (y : BitVec 16) : Bool :=
  (Ne x y)

def bitvector_len (x : BitVec 16) : Nat :=
  (Sail.BitVec.length x)

def bitvector_sign_extend (x : BitVec 16) : BitVec 32 :=
  (Sail.BitVec.signExtend x 32)

def bitvector_zero_extend (x : BitVec 16) : BitVec 32 :=
  (Sail.BitVec.zeroExtend x 32)

def bitvector_truncate (x : BitVec 32) : BitVec 16 :=
  (Sail.BitVec.truncate x 16)

def bitvector_truncateLSB (x : BitVec 32) : BitVec 16 :=
  (Sail.BitVec.truncateLsb x 16)

def bitvector_append (x : BitVec 16) (y : BitVec 16) : BitVec 32 :=
  (BitVec.append x y)

def bitvector_add (x : BitVec 16) (y : BitVec 16) : BitVec 16 :=
  (HAdd.hAdd x y)

def bitvector_sub (x : BitVec 16) (y : BitVec 16) : BitVec 16 :=
  (HSub.hSub x y)

def bitvector_not (x : BitVec 16) : BitVec 16 :=
  (Complement.complement x)

def bitvector_and (x : BitVec 16) (y : BitVec 16) : BitVec 16 :=
  (HAnd.hAnd x y)

def bitvector_or (x : BitVec 16) (y : BitVec 16) : BitVec 16 :=
  (HOr.hOr x y)

def bitvector_xor (x : BitVec 16) (y : BitVec 16) : BitVec 16 :=
  (HXor.hXor x y)

def bitvector_unsigned (x : BitVec 16) : Nat :=
  (BitVec.toNat x)

def bitvector_signed (x : BitVec 16) : Int :=
  (BitVec.toInt x)

def initialize_registers : Unit :=
  ()

