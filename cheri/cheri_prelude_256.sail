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

/*
val cast_bool_bit : bool -> bit effect pure
val cast_boolvec_bitvec :  'n, 'm. vector<'n,'m,dec,bool> -> vector<'n,'m,dec,bit> effect pure
val cast_range_bitvec : forall 'm. [|0:2**'m - 1|] -> vector<'m - 1,'m,dec,bit> effect pure
function vector<'m - 1,'m,dec,bit> cast_range_bitvec (v) = to_vec (v)
val not : extern bool -> bool effect pure */

struct CapStruct = {
  tag                     : bool    ,
  padding                 : bits(8) ,
  otype                   : bits(24),
  uperms                  : bits(16),
  perm_reserved11_14      : bits(4) ,
  access_system_regs      : bool    ,
  perm_reserved9          : bool    ,
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
  offset                  : bits(64),
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
  perm_reserved9 = false,
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
  offset = zeros(),
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
  perm_reserved9 = true,
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
  offset = zeros(),
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
    perm_reserved9             = capReg[202],
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
    offset                     = capReg[191..128],
    base                       = capReg[127..64],
    length                     = capReg[63..0]
  }

function getCapPerms(cap) : CapStruct -> bits(31) = 
  (
    cap.uperms
      @ cap.perm_reserved11_14
      @ cap.access_system_regs
      @ cap.perm_reserved9
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


/* Function used to convert capabilities to in-memory format 
   - this is the same as register format except for the offset,
     field which is stored as an absolute cursor on CHERI
     due to uarch optimisation */
function capStructToMemBits256(cap) : CapStruct -> bits(256) =
  (
        cap.padding
      @ cap.otype
      @ getCapPerms(cap)
      @ cap.sealed
        /* NB in memory format stores cursor, not offset */
      @ (cap.base + cap.offset) 
      @ cap.base
      @ cap.length
  )


/* Reverse of above used when reading from memory */
function memBitsToCapBits256(tag, b) : (bool, bits(256)) -> bits(257)=
  (tag
   @ b[255..192]
   @ (b[191..128] - b[127..64])
   @ b[127..0]
  )

/* When saving/restoring capabilities xor them with bits of null_cap --
   this ensures that canonical null_cap is always all-zeros in memory
   even though it may have bits set logically (e.g. length or exponent) */

function capStructToMemBits(cap) : CapStruct -> bits(256)=
  let null_cap_bits : bits(256) = capStructToMemBits256(null_cap) in
  capStructToMemBits256(cap) ^ null_cap_bits

function memBitsToCapBits(tag, b) : (bool, bits(256)) -> bits(257)  =
  let null_cap_bits : bits(256) = capStructToMemBits256(null_cap) in
  memBitsToCapBits256(tag, b ^ null_cap_bits)

function capStructToCapReg(cap) : CapStruct -> CapReg =
      cap.tag
      @ cap.padding
      @ cap.otype
      @ getCapPerms(cap)
      @ cap.sealed
      @ cap.offset
      @ cap.base
      @ cap.length

function setCapPerms(cap, perms) : (CapStruct, bits(31)) -> CapStruct =
    { cap with
      uperms                 = perms[30..15],
      perm_reserved11_14     = perms[14..11],
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
    (true, {cap with sealed=true, otype=otype})

function getCapBase(c)   : CapStruct -> uint64 = unsigned(c.base)
function getCapTop(c)    : CapStruct -> CapLen = unsigned(c.base) + unsigned(c.length)
function getCapOffset(c) : CapStruct -> uint64 = unsigned(c.offset)
function getCapLength(c) : CapStruct -> CapLen = unsigned(c.length)

function getCapCursor(cap) : CapStruct -> uint64 = 
  (unsigned(cap.base) + unsigned(cap.offset)) % (pow2(64))

function setCapOffset(c, offset) : (CapStruct, bits(64)) -> (bool, CapStruct) = 
    (true, {c with offset=offset})

function incCapOffset(c, delta) : (CapStruct, bits(64)) -> (bool, CapStruct) =
    let newOffset : bits(64) = c.offset + delta in
    (true, {c with offset = newOffset})

function setCapBounds(cap, base, top) : (CapStruct, bits(64), bits(65)) -> (bool, CapStruct) =
    let length : bits(65) = top - (0b0 @ base) in
    (true, {cap with base = base, length = length[63..0], offset = zeros()})

function int_to_cap (offset) : bits(64) -> CapStruct = 
    {null_cap with offset = offset}
