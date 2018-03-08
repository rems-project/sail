/*========================================================================*/
/*                                                                        */
/*  Copyright (c) 2015-2017 Robert M. Norton                              */
/*  Copyright (c) 2015-2017 Kathyrn Gray                                  */
/*  All rights reserved.                                                  */
/*                                                                        */
/*  This software was developed by the University of Cambridge Computer   */
/*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  */
/*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   */
/*                                                                        */
/*  Redistribution and use in source and binary forms, with or without    */
/*  modification, are permitted provided that the following conditions    */
/*  are met:                                                              */
/*  1. Redistributions of source code must retain the above copyright     */
/*     notice, this list of conditions and the following disclaimer.      */
/*  2. Redistributions in binary form must reproduce the above copyright  */
/*     notice, this list of conditions and the following disclaimer in    */
/*     the documentation and/or other materials provided with the         */
/*     distribution.                                                      */
/*                                                                        */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    */
/*  SUCH DAMAGE.                                                          */
/*========================================================================*/

/* 128 bit cap + tag */
type CapReg = bits(129)

/*
val cast_bool_bit : cast extern bool -> bit effect pure
val cast_boolvec_bitvec : cast extern forall 'n, 'm. vector<'n,'m,dec,bool> -> vector<'n,'m,dec,bit> effect pure
val cast_range_bitvec : cast forall 'm. [|0:2**'m - 1|] -> vector<'m - 1,'m,dec,bit> effect pure
function vector<'m - 1,'m,dec,bit> cast_range_bitvec (v) = to_vec (v)
val not : extern bool -> bool effect pure
*/

struct CapStruct = {
  tag                    : bool    ,
  uperms                 : bits(4) ,
  access_system_regs     : bool    ,
  perm_reserved9         : bool    ,
  permit_ccall           : bool    ,
  permit_seal            : bool    ,
  permit_store_local_cap : bool    ,
  permit_store_cap       : bool    ,
  permit_load_cap        : bool    ,
  permit_store           : bool    ,
  permit_load            : bool    ,
  permit_execute         : bool    ,
  global                 : bool    ,
  reserved               : bits(2) ,
  E                      : bits(6) ,
  sealed                 : bool    ,
  B                      : bits(20),
  T                      : bits(20),
  otype                  : bits(24),
  address                : bits(64)
}

let null_cap : CapStruct = struct {
  tag                    = false,
  uperms                 = zeros(),
  access_system_regs     = false,
  perm_reserved9         = false,
  permit_ccall           = false,
  permit_seal            = false,
  permit_store_local_cap = false,
  permit_store_cap       = false,
  permit_load_cap        = false,
  permit_store           = false,
  permit_load            = false,
  permit_execute         = false,
  global                 = false,
  reserved               = zeros(),
  E                      = 0b110000, /* 48, encoded as 0 in memory due to xor */
  sealed                 = false,
  B                      = zeros(),
  T                      = 0x10000,
  otype                  = zeros(),
  address                = zeros()
}

let default_cap : CapStruct = struct {
  tag                    = true,
  uperms                 = ones(),
  access_system_regs     = true,
  perm_reserved9         = true,
  permit_ccall           = true,
  permit_seal            = true,
  permit_store_local_cap = true,
  permit_store_cap       = true,
  permit_load_cap        = true,
  permit_store           = true,
  permit_load            = true,
  permit_execute         = true,
  global                 = true,
  reserved               = zeros(),
  E                      = 0b110000, /* 48, encoded as 0 in memory due to xor */
  sealed                 = false,
  B                      = zeros(),
  T                      = 0x10000,
  otype                  = zeros(),
  address                = zeros()
}

let 'cap_size = 16

function capRegToCapStruct(c) : CapReg -> CapStruct =
  let s : bool  = c[104] in
  let Bc : bits(20) = if s then c[103..96] @ 0x000 else c[103..84] in
  let Tc : bits(20) = if s then c[83..76] @ 0x000 else c[83..64] in
  let otype : bits(24) = if s then c[95..84] @ c[75..64] else zeros() in
  struct {
    tag                    = c[128],
    uperms                 = c[127..124],
    access_system_regs     = c[123],
    perm_reserved9         = c[122],
    permit_ccall           = c[121],
    permit_seal            = c[120],
    permit_store_local_cap = c[119],
    permit_store_cap       = c[118],
    permit_load_cap        = c[117],
    permit_store           = c[116],
    permit_load            = c[115],
    permit_execute         = c[114],
    global                 = c[113],
    reserved               = c[112..111],
    E                      = c[110..105] ^ 0b110000,
    sealed                 = s,
    B                      = Bc,
    T                      = Tc,
    otype                  = otype,
    address                = c[63..0]
  }

function getCapHardPerms(cap) : CapStruct -> bits(11) =
   (cap.access_system_regs
  @ cap.perm_reserved9
  @ cap.permit_ccall
  @ cap.permit_seal
  @ cap.permit_store_local_cap
  @ cap.permit_store_cap
  @ cap.permit_load_cap
  @ cap.permit_store
  @ cap.permit_load
  @ cap.permit_execute
  @ cap.global)

function capStructToMemBits128(cap) : CapStruct -> bits(128) =
    let b : bits(20) = if cap.sealed then (cap.B)[19..12] @ (cap.otype)[23..12] else cap.B in
    let t : bits(20) = if cap.sealed then (cap.T)[19..12] @ (cap.otype)[11..0]  else cap.T in
    ( cap.uperms
    @ getCapHardPerms(cap)
    @ cap.reserved
    @ cap.E ^ 0b110000
    @ cap.sealed
    @ b
    @ t
    @ cap.address
    )

function capStructToCapReg(cap) : CapStruct -> CapReg =
    (cap.tag @ capStructToMemBits128(cap))

/* Reverse of above used when reading from memory */
function memBitsToCapBits128(tag, b) : (bool, bits(128)) -> CapReg=
  (tag @ b)

/* When saving/restoring capabilities xor them with bits of null_cap --
   this ensures that canonical null_cap is always all-zeros in memory
   even though it may have bits set logically (e.g. length or exponent */

let null_cap_bits : bits(128) = capStructToMemBits128(null_cap)

function capStructToMemBits(cap) : CapStruct -> bits(128) =
  capStructToMemBits128(cap) ^ null_cap_bits

function memBitsToCapBits(tag, b) : (bool, bits(128)) -> bits(129) =
  memBitsToCapBits128(tag, b ^ null_cap_bits)

function getCapPerms(cap) : CapStruct -> bits(31) = 
    let perms : bits(15) = EXTS(getCapHardPerms(cap)) in /* NB access_system copied into 14-11 */
    (0x000 /* uperms 30-19 */
  @ cap.uperms
  @ perms)

function setCapPerms(cap, perms) : (CapStruct, bits(31)) -> CapStruct =
    { cap with
      uperms                 = perms[18..15],
      /* 14..11 reserved -- ignore */
      access_system_regs     = perms[10],
      perm_reserved9         = perms[9],
      permit_ccall           = perms[8],
      permit_seal            = perms[7],
      permit_store_local_cap = perms[6],
      permit_store_cap       = perms[5],
      permit_load_cap        = perms[4],
      permit_store           = perms[3],
      permit_load            = perms[2],
      permit_execute         = perms[1],
      global                 = perms[0]
      }

function sealCap(cap, otype) : (CapStruct, bits(24)) -> (bool, CapStruct) =
    if (((cap.T)[11..0] == zeros()) & ((cap.B)[11..0] == zeros())) then
        (true, {cap with sealed=true, otype=otype})
    else
        (false, cap /* XXX should be undefined? */ )

function a_top_correction(a_mid, R, bound) : (bits(20), bits(20), bits(20)) -> bits(65) =
    match (a_mid <_u R, bound <_u R) {
      (false, false)  => zeros(),
      (false, true)   => EXTZ(0b1),
      (true, false)   => ones(),
      (true, true)    => zeros()
    }

function getCapBase(c) : CapStruct -> uint64 =
    let E = min(unsigned(c.E), 48) in
    let Bc : bits(20) = c.B in
    let a : bits(65) = EXTZ(c.address) in
    let R : bits(20) = Bc - 0x01000 in /* wraps */
    let a_mid : bits(20) = mask(a >> E) in
    let correction = a_top_correction(a_mid, R, Bc) in
    let a_top = a >> E+20 in
    let base : bits(64) = mask(((a_top + correction) @ Bc) << E) in
    unsigned(base)

function getCapTop (c) : CapStruct -> CapLen = 
    let E = min(unsigned(c.E), 48) in
    let Bc : bits(20) = c.B in
    let T : bits(20) = c.T in
    let a : bits(65) = EXTZ(c.address)  in
    let R : bits(20) = Bc - 0x01000 in /* wraps */
    let a_mid : bits(20) = mask(a >> E) in
    let correction = a_top_correction(a_mid, R, T) in
    let a_top = a >> E+20 in
    let top1 : bits(65) = mask((a_top + correction) @ T) in
    unsigned(top1 << E)

function getCapOffset(c) : CapStruct -> uint64 = 
    let base = getCapBase(c) in
    (unsigned(c.address) - base) % pow2(64)

function getCapLength(c) : CapStruct -> CapLen =
         let 'top = getCapTop(c) in
         let 'base = getCapBase(c) in {
             assert (top >= base);
             top - base
         }

function getCapCursor(cap) : CapStruct -> uint64 = unsigned(cap.address)

function fastRepCheck(c, i) : (CapStruct, bits(64)) -> bool=
    let 'E = unsigned(c.E) in
    if (E >= 44) then
        true /* in this case representable region is whole address space */
    else
        let E'       = min(E, 43) in
        let i_top    = signed(i[63..E+20]) in
        let i_mid : bits(20) = i[E+19..E] in
        let a_mid : bits(20) = (c.address)[E+19..E] in
        let R : bits(20)     = (c.B) - 0x01000 in
        let diff : bits(20)  = R - a_mid in
        let diff1 : bits(20) = diff - 1 in
        /* i_top determines 1. whether the increment is inRange
           i.e. less than the size of the representable region
           (2**(E+20)) and 2. whether it is positive or negative. To
           satisfy 1. all top bits must be the same so we are
           interested in the cases i_top is 0 or -1 */
        if (i_top == 0) then
          i_mid <_u diff1
        else if (i_top == -1) then
          (i_mid >=_u diff) & (R != a_mid)
        else
          false

function setCapOffset(c, offset) : (CapStruct, bits(64)) -> (bool, CapStruct) =
    let base : bits(64)       = to_bits(64, getCapBase(c)) in
    let newAddress : bits(64) = base + offset in
    let newCap     = { c with address = newAddress } in
    let representable = fastRepCheck(c, (newAddress - c.address)) in
    (representable, newCap)

function incCapOffset(c, delta) : (CapStruct, bits(64)) -> (bool, CapStruct) =
    let newAddress : bits(64) = c.address + delta in
    let newCap     = { c with address = newAddress } in
    let representable = fastRepCheck(c, delta) in
    (representable, newCap)

/** FUNCTION:integer HighestSetBit(bits(N) x) */

val HighestSetBit : forall 'N , 'N >= 2. bits('N) -> {'n, 0 <= 'n < 'N . option(atom('n))}
function HighestSetBit x = {
  foreach (i from ('N - 1) to 0 by 1 in dec)
    if [x[i]] == 0b1 then return Some(i) else ();
  return None() : option(atom(0))
}

/* hw rounds up E to multiple of 4 */
function roundUp(e) : range(0, 45) -> range(0, 48) =
    let 'r = e % 4 in
    if (r == 0)
    then e
    else (e - r + 4)

function computeE (rlength) : bits(65) -> range(0, 48) =
    let 'msb = HighestSetBit((rlength + (rlength >> 6)) >> 19) in
    match msb {
      None()   => 0,
      /* above will always return <= 45 because 19 bits of zero are shifted in from right */
      Some('b) => {assert(0 <= b & b <= 45); roundUp (min(b,45)) }
      }

function setCapBounds(cap, base, top) : (CapStruct, bits(64), bits(65)) -> (bool, CapStruct) =
    /* {cap with base=base; length=(bits(64)) length; offset=0} */
    let 'e = computeE(top - (0b0 @ base)) in
    let Bc : bits(20) = mask(base >> e) in
    let T : bits(20) = mask(top >> e) in
    let e_mask : bits(65) = EXTZ(replicate_bits(0b1, e)) in
    let e_bits = top & e_mask in
    let T2 : bits(20) = T + (if unsigned(e_bits) == 0 then 0x00000 else 0x00001) in
    let newCap  = {cap with E=to_bits(6, e), B=Bc, T=T2} in
    let newBase = getCapBase(newCap) in
    let newTop  = getCapTop(newCap) in
    let exact   = (unsigned(base) == newBase) & (unsigned(top) == newTop) in
    (exact, newCap)

function int_to_cap (offset) : bits(64) -> CapStruct = 
    {null_cap with address = offset}
