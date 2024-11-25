def bitvector_eq (x : BitVec 16) (y : BitVec 16) : Bool :=
  (Eq x y)

def bitvector_neq (x : BitVec 16) (y : BitVec 16) : Bool :=
  (Ne x y)

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

def initialize_registers : Unit :=
  ()

