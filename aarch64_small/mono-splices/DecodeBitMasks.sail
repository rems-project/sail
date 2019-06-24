val DecodeBitMasks2 : forall 'M 'S 'd, 'M >= 'd + 1 & 'S >= 0 & 'd >= 0. (int, int('S), nat, int('d), int('M)) -> (bits('M), bits('M)) effect {escape}

function DecodeBitMasks2(esize as 'E, S, R, d, M) = {
  assert(constraint('E in {2,4,8,16,32,64} & 'M >= 'E & 'E >= 'd + 1));
  assert(esize >= S+1); /* CP: adding this assertion to make typecheck */
  welem : bits('E) = ZeroExtend(Ones(S + 1));
  telem : bits('E) = ZeroExtend(Ones(d + 1));
  wmask = Replicate(M,ROR(welem, R));
  tmask = Replicate(M,telem);
  (wmask, tmask);
}

function DecodeBitMasks(M : int('M), immN : bit, imms : bits(6), immr : bits(6), immediate : boolean) = {
  /* let M = (length((bit['M]) 0)) in { */
  /* ARM: (bit['M]) tmask := 0; (* ARM: uninitialized *) */
  /* ARM: (bit['M]) wmask := 0; (* ARM: uninitialized *) */
  levels : bits(6) = Zeros(); /* ARM: uninitialized */

  /* Compute log2 of element size */
  /* 2^len must be in range [2, 'M] */
  let len : range(0,6) = match HighestSetBit([immN]@(~(imms))) {
    None() => { assert (false, "DecodeBitMasks: HighestSetBit returned None"); 0; },
    Some(c) => c
  };
  if len < 1 then {ReservedValue(); exit()} else {
  assert(M >= lsl(1, len));

  /* Determine S, R and S - R parameters */
  levels = ZeroExtend(Ones(len));

  /* For logical immediates an all-ones value of S is reserved */
  /* since it would generate a useless all-ones result (many times) */
  if immediate & ((imms & levels) == levels) then
    ReservedValue();

  let S = UInt (imms & levels);
  let R = UInt (immr & levels);
  let diff : bits(6) = to_bits(S - R); /* 6-bit subtract with borrow */

  let esize as int('E) = lsl(1, len);
  let d /* : bits(6) */ = UInt (diff[(len - 1)..0]);
  DecodeBitMasks2(esize, S, R, d, M);
}}
