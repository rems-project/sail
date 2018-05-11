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

/* 256 bit cap + tag */
type CapReg = bits(257)

struct CapStruct = {
  tag                     : bool    ,
  padding                 : bits(8) ,
  otype                   : bits(24),
  uperms                  : bits(16),
  perm_reserved11_14      : bits(4) ,
  access_system_regs      : bool    ,
  permit_unseal           : bool    ,
  permit_ccall            : bool    ,
  permit_seal             : bool    ,
  permit_store_local_cap  : bool    ,
  permit_store_cap        : bool    ,
  permit_load_cap         : bool    ,
  permit_store            : bool    ,
  permit_load             : bool    ,
  permit_execute          : bool    ,
  global                  : bool    ,
  sealed                  : bool    ,
  address                 : bits(64),
  base                    : bits(64),
  length                  : bits(64),
}

let null_cap : CapStruct = struct {
  tag = false,
  padding = zeros(),
  otype = zeros(),
  uperms = zeros(),
  perm_reserved11_14 = zeros(),
  access_system_regs = false,
  permit_unseal = false,
  permit_ccall = false,
  permit_seal = false,
  permit_store_local_cap = false,
  permit_store_cap = false,
  permit_load_cap = false,
  permit_store = false,
  permit_load = false,
  permit_execute = false,
  global = false,
  sealed = false,
  address = zeros(),
  base = zeros(),
  length = 0xffffffffffffffff
}

let default_cap : CapStruct = struct {
  tag = true,
  padding = zeros(),
  otype = zeros(),
  uperms = ones(),
  perm_reserved11_14 = ones(),
  access_system_regs = true,
  permit_unseal = true,
  permit_ccall = true,
  permit_seal = true,
  permit_store_local_cap = true,
  permit_store_cap = true,
  permit_load_cap = true,
  permit_store = true,
  permit_load = true,
  permit_execute = true,
  global = true,
  sealed = false,
  address = zeros(),
  base = zeros(),
  length = 0xffffffffffffffff
}

let 'cap_size = 32

function capRegToCapStruct(capReg) : CapReg -> CapStruct =
  struct {
    tag                        = capReg[256],
    padding                    = capReg[255..248],
    otype                      = capReg[247..224],
    uperms                     = capReg[223..208],
    perm_reserved11_14         = capReg[207..204],
    access_system_regs         = capReg[203],
    permit_unseal              = capReg[202],
    permit_ccall               = capReg[201],
    permit_seal                = capReg[200],
    permit_store_local_cap     = capReg[199],
    permit_store_cap           = capReg[198],
    permit_load_cap            = capReg[197],
    permit_store               = capReg[196],
    permit_load                = capReg[195],
    permit_execute             = capReg[194],
    global                     = capReg[193],
    sealed                     = capReg[192],
    address                    = capReg[191..128],
    base                       = capReg[127..64],
    length                     = capReg[63..0]
  }

function getCapPerms(cap) : CapStruct -> bits(31) = 
  (
    cap.uperms
      @ cap.perm_reserved11_14
      @ cap.access_system_regs
      @ cap.permit_unseal
      @ cap.permit_ccall
      @ cap.permit_seal
      @ cap.permit_store_local_cap
      @ cap.permit_store_cap
      @ cap.permit_load_cap
      @ cap.permit_store
      @ cap.permit_load
      @ cap.permit_execute
      @ cap.global
  )


/* Function to convert capabilities to in-memory format. */
function capStructToMemBits256(cap) : CapStruct -> bits(256) =
  (
        cap.padding
      @ cap.otype
      @ getCapPerms(cap)
      @ cap.sealed
      @ cap.address
      @ cap.base
      @ cap.length
  )


/* When saving/restoring capabilities xor them with bits of null_cap --
   this ensures that canonical null_cap is always all-zeros in memory
   even though it may have bits set logically (e.g. length or exponent) */

let null_cap_bits : bits(256) = capStructToMemBits256(null_cap)

function capStructToMemBits(cap) : CapStruct -> bits(256)=
  capStructToMemBits256(cap) ^ null_cap_bits

function memBitsToCapBits(tag, b) : (bool, bits(256)) -> bits(257)  =
  tag @ (b ^ null_cap_bits)

function capStructToCapReg(cap) : CapStruct -> CapReg = cap.tag @ capStructToMemBits256(cap)

function setCapPerms(cap, perms) : (CapStruct, bits(31)) -> CapStruct =
    { cap with
      uperms                 = perms[30..15],
      perm_reserved11_14     = perms[14..11],
      access_system_regs     = perms[10],
      permit_unseal          = perms[9],
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
    (true, {cap with sealed=true, otype=otype})

function getCapBase(c)   : CapStruct -> uint64 = unsigned(c.base)
function getCapTop(c)    : CapStruct -> CapLen = unsigned(c.base) + unsigned(c.length) /* XXX bug here? -- should be mod 2^64 */
function getCapOffset(c) : CapStruct -> uint64 = (unsigned(c.address) - unsigned(c.base)) % (pow2(64))
function getCapLength(c) : CapStruct -> CapLen = unsigned(c.length)

function getCapCursor(c) : CapStruct -> uint64 = unsigned(c.address)

/*!
Set the offset capability of the a capability to given value and return the result, along with a boolean indicating true if the operation preserved the existing bounds of the capability.  When using compressed capabilities, setting the offset far outside the capability bounds can cause the result to become unrepresentable (XXX mention guarantees). Additionally in some implementations a fast representablity check may be used that could cause the operation to return failure even though the capability would be representable (XXX provide details). 
 */
val setCapOffset : (CapStruct, bits(64)) -> (bool, CapStruct)
function setCapOffset(c, offset) =
    (true, {c with address=c.base + offset})

/*!
\function{incCapOffset} is the same as \function{setCapOffset} except that the 64-bit value is added to the current capability offset modulo $2^{64}$ (i.e. signed twos-complement arithemtic).
 */
val incCapOffset : (CapStruct, bits(64)) -> (bool, CapStruct)
function incCapOffset(c, delta) =
    let newAddr : bits(64) = c.address + delta in
    (true, {c with address = newAddr})

/*!
Returns a capability derived from the given capability by setting the base and top to values provided.  The offset of the resulting capability is zero.  In case the requested bounds are not exactly representable the returned boolean is false and the returned capability has bounds at least including the region bounded by base and top but rounded to representable values.
 */
val setCapBounds : (CapStruct, bits(64), bits(65)) -> (bool, CapStruct)
function setCapBounds(cap, base, top) =
    let length : bits(65) = top - (0b0 @ base) in
    (true, {cap with base = base, length = length[63..0], address = base})

function int_to_cap (address) : bits(64) -> CapStruct = 
    {null_cap with address = address}
