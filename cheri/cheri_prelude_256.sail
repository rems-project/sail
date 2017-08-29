(*========================================================================*)
(*                                                                        *)
(*  Copyright (c) 2015-2017 Robert M. Norton                              *)
(*  Copyright (c) 2015-2017 Kathyrn Gray                                  *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(*========================================================================*)

(* 256 bit cap + tag *)
typedef CapReg = bit[257]

val cast bool -> bit effect pure cast_bool_bit
val cast forall 'n, 'm. vector<'n,'m,dec,bool> -> vector<'n,'m,dec,bit> effect pure cast_boolvec_bitvec
val cast forall 'm. [|0:2**'m - 1|] -> vector<'m - 1,'m,dec,bit> effect pure cast_range_bitvec
function vector<'m - 1,'m,dec,bit> cast_range_bitvec (v) = to_vec (v)
val extern bool -> bool effect pure not

typedef uint64 = range<0, (2** 64) - 1>

typedef CapStruct = const struct {
  bool    tag;
  bit[8]  padding;
  bit[24] otype;
  bit[16] uperms;
  bit[4]  perm_reserved11_14;
  bool    access_system_regs;
  bool    perm_reserved9;
  bool    permit_ccall;
  bool    permit_seal;
  bool    permit_store_local_cap;
  bool    permit_store_cap;
  bool    permit_load_cap;
  bool    permit_store;
  bool    permit_load;
  bool    permit_execute;
  bool    global;
  bool    sealed;
  bit[64] offset;
  bit[64] base;
  bit[64] length;
}

let (CapStruct) null_cap = {
  tag = false;
  padding = 0;
  otype = 0;
  uperms = 0;
  perm_reserved11_14 = 0;
  access_system_regs = false;
  perm_reserved9 = false;
  permit_ccall = false;
  permit_seal = false;
  permit_store_local_cap = false;
  permit_store_cap = false;
  permit_load_cap = false;
  permit_store = false;
  permit_load = false;
  permit_execute = false;
  global = false;
  sealed = false;
  offset = 0;
  base = 0;
  length = 0;
}

def Nat cap_size_t  = 32 (* cap size in bytes *)
let ([:cap_size_t:]) cap_size = 32

function CapStruct capRegToCapStruct((CapReg) capReg) =
  {
    tag                        = capReg[256];
    padding                    = capReg[255..248];
    otype                      = capReg[247..224];
    uperms                     = capReg[223..208];
    perm_reserved11_14         = capReg[207..204];
    access_system_regs         = capReg[203];
    perm_reserved9             = capReg[202];
    permit_ccall               = capReg[201];
    permit_seal                = capReg[200];
    permit_store_local_cap     = capReg[199];
    permit_store_cap           = capReg[198];
    permit_load_cap            = capReg[197];
    permit_store               = capReg[196];
    permit_load                = capReg[195];
    permit_execute             = capReg[194];
    global                     = capReg[193];
    sealed                     = capReg[192];
    offset                     = capReg[191..128];
    base                       = capReg[127..64];
    length                     = capReg[63..0];
  }

function (bit[31]) getCapPerms((CapStruct) cap) = 
  (
    cap.uperms
      : cap.perm_reserved11_14
      : [cap.access_system_regs]
      : [cap.perm_reserved9]
      : [cap.permit_ccall]
      : [cap.permit_seal]
      : [cap.permit_store_local_cap]
      : [cap.permit_store_cap]
      : [cap.permit_load_cap]
      : [cap.permit_store]
      : [cap.permit_load]
      : [cap.permit_execute]
      : [cap.global]
  )


(* Function used to convert capabilities to in-memory format 
   - this is the same as register format except for the offset,
     field which is stored as an absolute cursor on CHERI
     due to uarch optimisation *)
function (bit[256]) capStructToMemBits((CapStruct) cap) =
  (
        cap.padding
      : cap.otype
      : getCapPerms(cap)
      : [cap.sealed]
        (* NB in memory format stores cursor, not offset *)
      : (cap.base + cap.offset) 
      : cap.base
      : cap.length
  )


(* Reverse of above used when reading from memory *)
function (bit[257]) memBitsToCapBits((bool) tag, (bit[256]) b) =
  ([tag]
   : b[255..192]
   : ((bit[64])(b[191..128] - b[127..64]))
   : b[127..0]
  )

function (CapReg) capStructToCapReg((CapStruct) cap) =
    (
      [cap.tag]
      : cap.padding
      : cap.otype
      : getCapPerms(cap)
      : [cap.sealed]
      : cap.offset
      : cap.base
      : cap.length
    )

function CapStruct setCapPerms((CapStruct) cap, (bit[31]) perms) =
    { cap with
      uperms                 = perms[30..15];
      perm_reserved11_14     = perms[14..11];
      access_system_regs     = perms[10];
      perm_reserved9         = perms[9];
      permit_ccall           = perms[8];
      permit_seal            = perms[7];
      permit_store_local_cap = perms[6];
      permit_store_cap       = perms[5];
      permit_load_cap        = perms[4];
      permit_store           = perms[3];
      permit_load            = perms[2];
      permit_execute         = perms[1];
      global                 = perms[0];
      }

function (bool, CapStruct) sealCap((CapStruct) cap, (bit[24]) otype) =
    (true, {cap with sealed=true; otype=otype})

function bit[64] getCapBase((CapStruct) c)        = c.base
function [|0:2**65 - 2|] getCapTop((CapStruct) c) = unsigned(c.base) + unsigned(c.length)
function bit[64] getCapOffset((CapStruct) c)      = c.offset
function CapLen  getCapLength((CapStruct) c)      = unsigned(c.length)

function uint64 getCapCursor((CapStruct) cap) = 
  (unsigned(cap.base) + unsigned(cap.offset)) mod (pow2(64))

function (bool, CapStruct) setCapOffset((CapStruct) c, (bit[64]) offset) = 
    (true, {c with offset=offset})

function (bool, CapStruct) incCapOffset((CapStruct) c, (bit[64]) delta) =
    let (bit[64]) newOffset = c.offset + delta in
    (true, {c with offset = newOffset})

function (bool, CapStruct) setCapBounds((CapStruct) cap, (bit[64]) base, (bit[65]) top) =
    let (bit[65]) length = top - (0b0 : base) in
    (true, {cap with base = base; length = length[63..0]; offset = 0})

function CapStruct int_to_cap ((bit[64]) offset) = 
    {null_cap with offset = offset}
