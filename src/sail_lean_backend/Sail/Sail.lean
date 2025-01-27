namespace Sail
namespace BitVec

def length {w: Nat} (_: BitVec w): Nat := w

def signExtend {w: Nat} (x: BitVec w) (w': Nat) : BitVec w' :=
  x.signExtend w'

def zeroExtend {w: Nat} (x: BitVec w) (w': Nat) : BitVec w' :=
  x.zeroExtend w'

def truncate {w: Nat} (x: BitVec w) (w': Nat) : BitVec w' :=
  x.truncate w'

def truncateLSB {w: Nat} (x: BitVec w) (w': Nat) : BitVec w' :=
  x.extractLsb' 0 w'

end BitVec

namespace Int

def intAbs (x : Int) : Int := Int.ofNat (Int.natAbs x)

end Int
end Sail
