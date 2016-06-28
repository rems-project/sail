(*========================================================================*)
(*                                                                        *)
(*  Copyright (c) 2015-2016 Robert M. Norton                              *)
(*  Copyright (c) 2015-2016 Kathyrn Gray                                  *)
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

(* 265-bit capability is really 257 bits including tag *)
typedef CapReg = register bits [256:0] {
  256:      tag;
  (* 255..248: reserved1; padding *)
  247..224: otype;
  223..208: sw_perms;
  207:      access_KR2C;
  206:      access_KR1C;
  205:      access_KCC;
  204:      access_KDC;
  203:      access_EPCC;
  202:      perm_reserved9; (* perm bit 9 *)
  201:      perm_reserved8; (* perm bit 8 *)
  200:      permit_seal;
  199:      permit_store_local_cap;
  198:      permit_store_cap;
  197:      permit_load_cap;
  196:      permit_store;
  195:      permit_load;
  194:      permit_execute;
  193:      global;
  192:      sealed;
  191..128: offset;
  127..64:  base;
  63 .. 0:  length;
}

register CapReg PCC
register CapReg nextPCC
register CapReg delayedPCC
register CapReg C00 (* aka default data capability, DDC *)
register CapReg C01
register CapReg C02
register CapReg C03
register CapReg C04
register CapReg C05
register CapReg C06
register CapReg C07
register CapReg C08
register CapReg C09
register CapReg C10
register CapReg C11
register CapReg C12
register CapReg C13
register CapReg C14
register CapReg C15
register CapReg C16
register CapReg C17
register CapReg C18
register CapReg C19
register CapReg C20
register CapReg C21
register CapReg C22
register CapReg C23
register CapReg C24 (* aka return code capability, RCC *)
register CapReg C25
register CapReg C26 (* aka invoked data capability, IDC *)
register CapReg C27 (* aka kernel reserved capability 1, KR1C *)
register CapReg C28 (* aka kernel reserved capability 2, KR2C *)
register CapReg C29 (* aka kernel code capability, KCC *)
register CapReg C30 (* aka kernel data capability, KDC *)
register CapReg C31 (* aka exception program counter capability, EPCC *)

let (vector <0, 32, inc, (CapReg)>) CapRegs =
  [ C00, C01, C02, C03, C04, C05, C06, C07, C08, C09, C10,
  C11, C12, C13, C14, C15, C16, C17, C18, C19, C20,
  C21, C22, C23, C24, C25, C26, C27, C28, C29, C30, C31
  ]

typedef CapStruct = const struct {
  bool    tag;
  bit[8]  padding;
  bit[24] otype;
  bit[16] sw_perms;
  bool    access_KR2C;
  bool    access_KR1C;
  bool    access_KCC;
  bool    access_KDC;
  bool    access_EPCC;
  bool    perm_reserved9;
  bool    perm_reserved8;
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
  sw_perms = 0;
  access_KR2C = false;
  access_KR1C = false;
  access_KCC = false;
  access_KDC = false;
  access_EPCC = false;
  perm_reserved9 = false;
  perm_reserved8 = false;
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
let (nat) max_otype = 0xffffff
def Nat cap_size_t  = 32 (* cap size in bytes *)
let ([:cap_size_t:]) cap_size = 32
let have_cp2 = true

function CapStruct capRegToCapStruct((CapReg) capReg) =
  {
    tag                        = capReg.tag;
    padding                    = capReg[255..248];
    otype                      = capReg.otype;
    sw_perms                   = capReg.sw_perms;
    access_KR2C                = capReg.access_KR2C;
    access_KR1C                = capReg.access_KR1C;
    access_KCC                 = capReg.access_KCC;
    access_KDC                 = capReg.access_KDC;
    access_EPCC                = capReg.access_EPCC;
    perm_reserved9             = capReg.perm_reserved9;
    perm_reserved8             = capReg.perm_reserved8;
    permit_seal                = capReg.permit_seal;
    permit_store_local_cap     = capReg.permit_store_local_cap;
    permit_store_cap           = capReg.permit_store_cap;
    permit_load_cap            = capReg.permit_load_cap;
    permit_store               = capReg.permit_store;
    permit_load                = capReg.permit_load;
    permit_execute             = capReg.permit_execute;
    global                     = capReg.global;
    sealed                     = capReg.sealed;
    offset                     = capReg.offset;
    base                       = capReg.base;
    length                     = capReg.length;
  }


function (CapStruct) readCapReg((regno) n) =
  capRegToCapStruct(CapRegs[n])

function (bit[31]) capPermsToVec((CapStruct) cap) = 
  (
    cap.sw_perms
      : [cap.access_KR2C]
      : [cap.access_KR1C]
      : [cap.access_KCC]
      : [cap.access_KDC]
      : [cap.access_EPCC]
      : [cap.perm_reserved9]
      : [cap.perm_reserved8]
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
      : capPermsToVec(cap)
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

function (bit[257]) capStructToBit257((CapStruct) cap) =
    (
      [cap.tag]
      : cap.padding
      : cap.otype
      : capPermsToVec(cap)
      : [cap.sealed]
      : cap.offset
      : cap.base
      : cap.length
    )

function nat getCapCursor((CapStruct) cap) = 
  (((nat)(cap.base)) + ((nat)(cap.offset))) mod (2 ** 64)

function unit writeCapReg((regno) n, (CapStruct) cap) =
    {
      (CapRegs[n]) := capStructToBit257(cap)
    }

typedef CapEx = enumerate {
  CapEx_None; 
  CapEx_LengthViolation;
  CapEx_TagViolation;
  CapEx_SealViolation;
  CapEx_TypeViolation;
  CapEx_CallTrap;
  CapEx_ReturnTrap;
  CapEx_TSSUnderFlow;
  CapEx_UserDefViolation;
  CapEx_TLBNoStoreCap;
  CapEx_InexactBounds;
  CapEx_GlobalViolation;
  CapEx_PermitExecuteViolation;
  CapEx_PermitLoadViolation;
  CapEx_PermitStoreViolation;
  CapEx_PermitLoadCapViolation;
  CapEx_PermitStoreCapViolation;
  CapEx_PermitStoreLocalCapViolation;
  CapEx_PermitSealViolation;
  CapEx_AccessEPCCViolation;
  CapEx_AccessKDCViolation;
  CapEx_AccessKCCViolation;
  CapEx_AccessKR1CViolation;
  CapEx_AccessKR2CViolation;
}

typedef CGetXOp = enumerate {
  CGetPerm;
  CGetType;
  CGetBase;
  CGetOffset;
  CGetLen;
  CGetTag;
  CGetUnsealed;
}

typedef CPtrCmpOp = enumerate {
  CEQ;
  CNE;
  CLT;
  CLE;
  CLTU;
  CLEU;
  CEXEQ;
}

typedef ClearRegSet = enumerate {
GPLo;
GPHi;
CLo;
CHi;
}

function (bit[8]) CapExCode((CapEx) ex) =
  switch(ex) {
    case CapEx_None                         -> 0x00
    case CapEx_LengthViolation              -> 0x01
    case CapEx_TagViolation                 -> 0x02
    case CapEx_SealViolation                -> 0x03
    case CapEx_TypeViolation                -> 0x04
    case CapEx_CallTrap                     -> 0x05
    case CapEx_ReturnTrap                   -> 0x06
    case CapEx_TSSUnderFlow                 -> 0x07
    case CapEx_UserDefViolation             -> 0x08
    case CapEx_TLBNoStoreCap                -> 0x09
    case CapEx_InexactBounds                -> 0x0a
    case CapEx_GlobalViolation              -> 0x10
    case CapEx_PermitExecuteViolation       -> 0x11
    case CapEx_PermitLoadViolation          -> 0x12
    case CapEx_PermitStoreViolation         -> 0x13
    case CapEx_PermitLoadCapViolation       -> 0x14
    case CapEx_PermitStoreCapViolation      -> 0x15
    case CapEx_PermitStoreLocalCapViolation -> 0x16
    case CapEx_PermitSealViolation          -> 0x17
    case CapEx_AccessEPCCViolation          -> 0x18
    case CapEx_AccessKDCViolation           -> 0x18
    case CapEx_AccessKCCViolation           -> 0x18
    case CapEx_AccessKR1CViolation          -> 0x18
    case CapEx_AccessKR2CViolation          -> 0x18
  }

typedef CapCauseReg = register bits [15:0] {
  15..8: ExcCode;
  7..0:  RegNum;
}

register CapCauseReg CapCause

function unit SignalException ((Exception) ex) = 
  {
    C31        := PCC;
    C31.offset := PC;
    nextPCC    := C29; (* KCC *)
    delayedPCC := C29; (* always write delayedPCC together whether PCC so 
                          that non-capability branches don't override PCC *)
    SignalExceptionMIPS(ex, C29.base);
  }

function unit ERETHook() =
  {
    nextPCC    := C31;
    delayedPCC := C31; (* always write delayedPCC together whether PCC so 
                          that non-capability branches don't override PCC *)
  }

function unit raise_c2_exception8((CapEx) capEx, (bit[8]) regnum) =
  {
    (CapCause.ExcCode) := CapExCode(capEx);
    (CapCause.RegNum)  := regnum;
    let mipsEx = 
      if ((capEx == CapEx_CallTrap) | (capEx == CapEx_ReturnTrap)) 
      then C2Trap else C2E in
    SignalException(mipsEx);
  }

function unit raise_c2_exception((CapEx) capEx, (regno) regnum) =
  raise_c2_exception8(capEx, 0b000 : regnum)

function unit raise_c2_exception_v((regno) regnum) =
  switch(regnum) {
   case 0b11011 -> raise_c2_exception(CapEx_AccessKR1CViolation, regnum)
   case 0b11100 -> raise_c2_exception(CapEx_AccessKR2CViolation, regnum)
   case 0b11101 -> raise_c2_exception(CapEx_AccessKCCViolation, regnum)
   case 0b11110 -> raise_c2_exception(CapEx_AccessKDCViolation, regnum)
   case 0b11111 -> raise_c2_exception(CapEx_AccessEPCCViolation, regnum)
   case _       -> assert(false, Some("should only call for cap reg violation"))
  }

function unit raise_c2_exception_noreg((CapEx) capEx) =
  raise_c2_exception8(capEx, 0xff)

function bool register_inaccessible((regno) r) = 
  ~(switch(r) {
    case 0b11011 -> (PCC.access_KR1C)
    case 0b11100 -> (PCC.access_KR2C)
    case 0b11101 -> (PCC.access_KCC)
    case 0b11110 -> (PCC.access_KDC)
    case 0b11111 -> (PCC.access_EPCC)
    case _       -> bitone
  })

val extern (bit[64] , bit[8]) -> unit effect { wmem } TAGw
val extern (bit[64]) -> (bit[8]) effect { rmem } TAGr

function (bool, bit[cap_size_t * 8]) MEMr_tagged ((bit[64]) addr) =
{
  (* assumes addr is cap. aligned *)
  let tag = (TAGr (addr)) in
  let mem = (MEMr (addr, cap_size)) in
  (tag[0], mem)
}

function (bool, bit[cap_size_t * 8]) MEMr_tagged_reserve ((bit[64]) addr) =
{
  (* assumes addr is cap. aligned *)
  let tag = (TAGr (addr)) in
  let mem = (MEMr_reserve (addr, cap_size)) in
  (tag[0], mem)
}

function unit MEMw_tagged((bit[64]) addr, (bool) tag, (bit[cap_size_t * 8]) data) =
{
  (* assumes addr is cap. aligned *)
  MEMw(addr, cap_size, data);
  TAGw(addr, (0b0000000 : [tag]));
}

function bool MEMw_tagged_conditional((bit[64]) addr, (bool) tag, (bit[cap_size_t * 8]) data) =
{
  (* assumes addr is cap. aligned *)
  success := MEMw_conditional(addr, cap_size, data);
  if (success) then
    TAGw(addr, (0b0000000 : [tag]));
  success;
}

function unit effect {wmem} MEMw_wrapper(addr, size, data) =
  {
    (* On cheri non-capability writes must clear the corresponding tag*)
    TAGw((addr[63..5] : 0b00000), 0x00);
    MEMw(addr,size,data)
  }

function bool effect {wmem} MEMw_conditional_wrapper(addr, size, data) =
  {
    (* On cheri non-capability writes must clear the corresponding tag*)
    success := MEMw_conditional(addr,size,data);
    if (success) then
      TAGw((addr[63..5] : 0b00000), 0x00);
    success;
  }

function bit[64] addrWrapper((bit[64]) addr, (MemAccessType) accessType, (WordType) width) =
  {
    capno := 0b00000;
    cap := readCapReg(capno);
    if (~(cap.tag)) then
      exit (raise_c2_exception(CapEx_TagViolation, capno))
    else if (cap.sealed) then
      exit (raise_c2_exception(CapEx_SealViolation, capno));
    switch (accessType) {
      case Instruction -> if (~(cap.permit_execute)) then exit (raise_c2_exception(CapEx_PermitExecuteViolation, capno))
      case LoadData    -> if (~(cap.permit_load)) then exit (raise_c2_exception(CapEx_PermitLoadViolation, capno))
      case StoreData   -> if (~(cap.permit_store)) then exit (raise_c2_exception(CapEx_PermitStoreViolation, capno))
    };
    cursor := getCapCursor(cap);
    vAddr  := cursor + unsigned(addr);
    vAddr64:= (bit[64]) vAddr;
    size   := wordWidthBytes(width);
    if ((vAddr + size) > ((nat) (cap.base) + ((nat) (cap.length)))) then
      exit (raise_c2_exception(CapEx_LengthViolation, capno))
    else if (vAddr < ((nat) (cap.base))) then
      exit (raise_c2_exception(CapEx_LengthViolation, capno));
    vAddr64;
  }

function (bit[64]) TranslateAddress ((bit[64]) vAddr, (MemAccessType) accessType) = {
  incrementCP0Count();
  let (bit[64])  base = PCC.base in
  let (bit[64])  length = PCC.length in
  let (bit[64])  absPC = (base + vAddr) in
  if (absPC[1..0] != 0b00) then (* bad PC alignment *)
    exit (SignalExceptionBadAddr(AdEL, absPC))
  else if ((unsigned(vAddr) + 4) > unsigned(length)) then
    exit (raise_c2_exception_noreg(CapEx_LengthViolation))
  else
    TLBTranslate(absPC, accessType)
}

function unit checkCP2usable () =
      {
        if (~((CP0Status.CU)[2])) then
          {
            (CP0Cause.CE) := 0b10;
            exit (SignalException(CpU));
          }
      }

