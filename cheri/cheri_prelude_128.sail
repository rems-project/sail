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
typedef CapReg = bit[129]

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

let (vector <0, 32, inc, (register<CapReg>)>) CapRegs =
  [ C00, C01, C02, C03, C04, C05, C06, C07, C08, C09, C10,
  C11, C12, C13, C14, C15, C16, C17, C18, C19, C20,
  C21, C22, C23, C24, C25, C26, C27, C28, C29, C30, C31
  ]

let num_uperms = 4


typedef CapStruct = const struct {
  bool    tag;
  bit[4]  uperms;
  bool    access_system_regs;
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
  bit[2]  reserved;
  bit[6]  E;
  bool    sealed;
  bit[20] B;
  bit[20] T;
  bit[24] otype;
  bit[64] address;
}

let (CapStruct) null_cap = {
  tag                    = false;
  uperms                 = 0;
  access_system_regs     = false;
  perm_reserved9         = false;
  perm_reserved8         = false;
  permit_seal            = false;
  permit_store_local_cap = false;
  permit_store_cap       = false;
  permit_load_cap        = false;
  permit_store           = false;
  permit_load            = false;
  permit_execute         = false;
  global                 = false;
  reserved               = 0;
  E                      = 48; (* encoded as 0 in memory due to xor *)
  sealed                 = false;
  B                      = 0;
  T                      = 0;
  otype                  = 0;
  address                = 0;
}

let (nat) max_otype = 0xffffff
def Nat cap_size_t  = 16 (* cap size in bytes *)
let ([:cap_size_t:]) cap_size = 16
let have_cp2 = true

function CapStruct capRegToCapStruct((CapReg) c) =
  let (bool)    s = c[104] in
  let (bit[20]) B = if s then c[103..96] : 0x000 else c[103..84] in
  let (bit[20]) T = if s then c[83..76] : 0x000 else c[83..64] in
  let (bit[24]) otype = if s then c[95..84] : c[75..64] else 0 in
  {
    tag                    = c[128];
    uperms                 = c[127..124];
    access_system_regs     = c[123];
    perm_reserved9         = c[122];
    perm_reserved8         = c[121];
    permit_seal            = c[120];
    permit_store_local_cap = c[119];
    permit_store_cap       = c[118];
    permit_load_cap        = c[117];
    permit_store           = c[116];
    permit_load            = c[115];
    permit_execute         = c[114];
    global                 = c[113];
    reserved               = c[112..111];
    E                      = c[110..105];
    sealed                 = s;
    B                      = B;
    T                      = T;
    otype                  = otype;
    address                = c[63..0];
  }


function (CapStruct) readCapReg((regno) n) =
  capRegToCapStruct(CapRegs[n])

function (bit[11]) getCapHardPerms((CapStruct) cap) =
   ([cap.access_system_regs]
  : [cap.perm_reserved9]
  : [cap.perm_reserved8]
  : [cap.permit_seal]
  : [cap.permit_store_local_cap]
  : [cap.permit_store_cap]
  : [cap.permit_load_cap]
  : [cap.permit_store]
  : [cap.permit_load]
  : [cap.permit_execute]
  : [cap.global])

function (bit[31]) getCapPerms((CapStruct) cap) = 
    let (bit[15]) perms = EXTS(getCapHardPerms(cap)) in (* NB access_system copied into 14-11 *)
    (0x000 (* uperms 30-19 *)
  : cap.uperms
  : perms)

function CapStruct setCapPerms((CapStruct) cap, (bit[31]) perms) =
    { cap with
      uperms                 = perms[18..15];
(*      perm_reserved11_14     = (cap.perm_reserved11_14 & (perms[14..11]));*)
      access_system_regs     = perms[10];
      perm_reserved9         = perms[9];
      perm_reserved8         = perms[8];
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
    if (((cap.T)[11..0] == 0) & ((cap.B)[11..0] == 0)) then
        (true, {cap with sealed=true; otype=otype})
    else
        (false, undefined)

function (bit[128]) capStructToMemBits((CapStruct) cap) =
    let (bit[20]) b = if cap.sealed then (cap.B)[23..12] : (cap.otype)[23..12] else cap.B in
    let (bit[20]) t = if cap.sealed then (cap.T)[23..12] : (cap.otype)[11..0]  else cap.T in
    ( cap.uperms
    : getCapHardPerms(cap)
    : cap.reserved
    : cap.E
    : [cap.sealed]
    : b
    : t
    : cap.address
    )

function (CapReg) capStructToCapReg((CapStruct) cap) =
    ([cap.tag] : capStructToMemBits(cap))

(* Reverse of above used when reading from memory *)
function (CapReg) memBitsToCapBits((bool) tag, (bit[128]) b) =
  ([tag]
   : b
  )

function unit writeCapReg((regno) n, (CapStruct) cap) =
    {
      CapRegs[n] := capStructToCapReg(cap)
    }


function int a_top_correction((bit[20]) a_mid, (bit[20]) R, (bit[20]) bound) =
    switch (a_mid < R, bound < R) {
      case (False, False) -> 0
      case (False, True)  -> 1
      case (True, False)  -> -1
      case (True, True)   -> 0
    }

function bit[64] getCapBase((CapStruct) c)  = 
    let ([|63|])  E = unsigned(c.E) in
    let (bool)    s = c.sealed in
    let (bit[20]) B = c.B in
    let (bit[64]) a = c.address in
    let (bit[20]) R = B - 0x00100 in (* wraps *)
    let (bit[20]) a_mid = a[(E + 19)..E] in
    let (int) correction = a_top_correction(a_mid, R, B) in
    let a_top = a[63..(E+20)] in
    let (bit[64]) base = EXTZ((a_top + correction) : B) in
    base << E

function bit[65] getCapTop((CapStruct) c)  = 
    let ([|63|])  E = unsigned(c.E) in
    let (bool)    s = c.sealed in
    let (bit[20]) B = c.B in
    let (bit[20]) T = c.T in
    let (bit[64]) a = c.address  in
    let (bit[20]) R = B - 0x00100 in (* wraps *)
    let (bit[20]) a_mid = a[(E + 19)..E] in
    let (int) correction = a_top_correction(a_mid, R, T) in
    let a_top = a[63..(E+20)] in
    let (bit[65]) top1 = EXTZ((a_top + correction) : T) in
    top1 << E

function bit[64] getCapOffset((CapStruct) c) = 
    let base = getCapBase(c) in
    c.address - base

function bit[65] getCapLength((CapStruct) c)  = getCapTop(c) - (0b0 : getCapBase(c))

function nat getCapCursor((CapStruct) cap) = unsigned(cap.address)

function (bool, CapStruct) setCapOffset((CapStruct) c, (bit[64]) offset) =
    let oldBase    = getCapBase(c) in
    let oldTop     = getCapTop(c) in
    let (bit[64]) newAddress = oldBase + offset in
    let newCap     = { c with address = newAddress } in
    let newBase    = getCapBase(newCap) in
    let newTop     = getCapTop(newCap) in
    let representable = (oldBase == newBase) & (oldTop == newTop) in
    (representable, newCap)

function (bool, CapStruct) incCapOffset((CapStruct) c, (bit[64]) delta) =
    let oldBase    = getCapBase(c) in
    let oldTop     = getCapTop(c) in
    let (bit[64]) newAddress = c.address + delta in
    let newCap     = { c with address = newAddress } in
    let newBase    = getCapBase(newCap) in
    let newTop     = getCapTop(newCap) in
    let representable = (oldBase == newBase) & (oldTop == newTop) in
    (representable, newCap)

(** FUNCTION:integer HighestSetBit(bits(N) x) *)

function forall Nat 'N. option<[|0:('N + -1)|]> HighestSetBit((bit['N]) x) = {
  let N = (length(x)) in {
  ([|('N + -1)|]) result := 0;
  (bool) break := false;
  foreach (i from (N - 1) downto 0)
    if ~(break) & x[i] == 1 then {
      result := i;
      break := true;
    };

  if break then Some(result) else None;
}}

function (bit[6]) computeE ((bit[65]) rlength) =
    let msb = HighestSetBit((rlength + (rlength >> 6)) >> 19) in
    switch (msb) {
      case (Some(b)) -> (bit[6]) b (* hw rounds up to multiple of 4 *)
      case None    -> 0
    }    

function (bool, CapStruct) setCapBounds((CapStruct) cap, (bit[64]) base, (bit[65]) top) =
    (* {cap with base=base; length=(bit[64]) length; offset=0} *)
    let (bit[6])  e = computeE(top - (0b0 : base)) in
    let (bit[20]) B = base[(19+e)..e] in
    let (bit[20]) T = top[(19+e)..e] in
    let (bit[20]) T2 = T + if (top[(e - 1)..0] == 0) then 0 else 1 in
    let newCap  = {cap with E=e; B=B; T=T2} in
    let newBase = getCapBase(newCap) in
    let newTop  = getCapTop(newCap) in
    let exact   = (base == newBase) & (top == newTop) in
    (exact, newCap)

function CapStruct int_to_cap ((bit[64]) offset) = 
    {null_cap with address = offset}

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
  CapEx_AccessSystemRegsViolation;
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
    case CapEx_AccessSystemRegsViolation    -> 0x18
  }

typedef CapCauseReg = register bits [15:0] {
  15..8: ExcCode;
  7..0:  RegNum;
}

register CapCauseReg CapCause

function forall Type 'o . 'o SignalException ((Exception) ex) = 
  {
    let pcc = capRegToCapStruct(PCC) in
    let (success, epcc) = setCapOffset(pcc, PC) in
    C31        := capStructToCapReg(epcc);
    (* XXX what if not success? *)
    nextPCC    := C29; (* KCC *)
    delayedPCC := C29; (* always write delayedPCC together whether PCC so 
                          that non-capability branches don't override PCC *)
    SignalExceptionMIPS(ex, getCapBase(capRegToCapStruct(C29)));
  }

function unit ERETHook() =
  {
    nextPCC    := C31;
    delayedPCC := C31; (* always write delayedPCC together whether PCC so 
                          that non-capability branches don't override PCC *)
  }

function forall Type 'o . 'o raise_c2_exception8((CapEx) capEx, (bit[8]) regnum) =
  {
    (CapCause.ExcCode) := CapExCode(capEx);
    (CapCause.RegNum)  := regnum;
    let mipsEx = 
      if ((capEx == CapEx_CallTrap) | (capEx == CapEx_ReturnTrap)) 
      then C2Trap else C2E in
    SignalException(mipsEx);
  }

function forall Type 'o . 'o raise_c2_exception((CapEx) capEx, (regno) regnum) =
  raise_c2_exception8(capEx, 0b000 : regnum)

function forall Type 'o . 'o raise_c2_exception_noreg((CapEx) capEx) =
  raise_c2_exception8(capEx, 0xff)

function bool pcc_access_system_regs () = 
      let pcc = capRegToCapStruct(PCC) in
      (pcc.access_system_regs)

function bool register_inaccessible((regno) r) = 
  let is_sys_reg = switch(r) {
    case 0b11011 -> true
    case 0b11100 -> true
    case 0b11101 -> true
    case 0b11110 -> true
    case 0b11111 -> true
    case _       -> false
  } in
  if is_sys_reg then
    not (pcc_access_system_regs ())
  else
    false

val extern forall Nat 'n. ( bit[64] , [|'n|] ) -> (bit[8 * ('n + 1)]) effect { rmem } MEMr_tag
val extern forall Nat 'n. ( bit[64] , [|'n|] ) -> (bit[8 * ('n + 1)]) effect { rmem } MEMr_tag_reserve

val extern (bit[64] , bit[8]) -> unit effect { wmem } TAGw
val extern forall Nat 'n. ( bit[64] , [|'n|]) -> unit effect { eamem } MEMea_tag
val extern forall Nat 'n. ( bit[64] , [|'n|]) -> unit effect { eamem } MEMea_tag_conditional
val extern forall Nat 'n. ( bit[64] , [|'n|] , bit[8 * ('n + 1)]) -> unit effect { wmv } MEMval_tag
val extern forall Nat 'n. ( bit[64] , [|'n|] , bit[8 * ('n + 1)]) -> bool effect { wmv } MEMval_tag_conditional


function (bool, bit[cap_size_t * 8]) MEMr_tagged ((bit[64]) addr) =
{
  (* assumes addr is cap. aligned *)
  let ((bit[8]) tag : mem) = (MEMr_tag (addr, cap_size)) in
  (tag[0], mem)
}

function (bool, bit[cap_size_t * 8]) MEMr_tagged_reserve ((bit[64]) addr) =
{
  (* assumes addr is cap. aligned *)
  let ((bit[8]) tag : mem) = (MEMr_tag_reserve (addr, cap_size)) in
  (tag[0], mem)
}

function unit MEMw_tagged((bit[64]) addr, (bool) tag, (bit[cap_size_t * 8]) data) =
{
  (* assumes addr is cap. aligned *)
  MEMea_tag(addr, cap_size);
  MEMval_tag(addr, cap_size, 0b0000000 : [tag] :  data);
}

function bool MEMw_tagged_conditional((bit[64]) addr, (bool) tag, (bit[cap_size_t * 8]) data) =
{
  (* assumes addr is cap. aligned *)
  MEMea_tag_conditional(addr, cap_size);
  MEMval_tag_conditional(addr, cap_size, 0b0000000 : [tag] :  data);
}

function unit effect {wmem} MEMw_wrapper(addr, size, data) =
  if (addr == 0x000000007f000000) then
  {
    UART_WDATA   := data[31..24];
    UART_WRITTEN := 1;
  }
  else
  {
    (* On cheri non-capability writes must clear the corresponding tag
       XXX this is vestigal and only works on sequential modle -- tag clearing
       should probably be done in memory model. *)
    TAGw((addr[63..4] : 0b0000), 0x00);
    MEMea(addr,size);
    MEMval(addr, size, data);
  }

function bool effect {wmem} MEMw_conditional_wrapper(addr, size, data) =
  {
    (* On cheri non-capability writes must clear the corresponding tag*)
    MEMea_conditional(addr, size);
    success := MEMval_conditional(addr,size,data);
    if (success) then
      (* XXX as above TAGw is vestigal and must die *)
      TAGw((addr[63..4] : 0b0000), 0x00);
    success;
  }

function bit[64] addrWrapper((bit[64]) addr, (MemAccessType) accessType, (WordType) width) =
  {
    capno := 0b00000;
    cap := readCapReg(capno);
    if (~(cap.tag)) then
      (raise_c2_exception(CapEx_TagViolation, capno))
    else if (cap.sealed) then
        (raise_c2_exception(CapEx_SealViolation, capno));
    switch (accessType) {
      case Instruction -> if (~(cap.permit_execute)) then (raise_c2_exception(CapEx_PermitExecuteViolation, capno))
      case LoadData    -> if (~(cap.permit_load)) then (raise_c2_exception(CapEx_PermitLoadViolation, capno))
      case StoreData   -> if (~(cap.permit_store)) then (raise_c2_exception(CapEx_PermitStoreViolation, capno))
    };
    cursor := getCapCursor(cap);
    vAddr  := cursor + unsigned(addr);
    size   := wordWidthBytes(width);
    base   := unsigned(getCapBase(cap));
    top    := unsigned(getCapTop(cap));
    if ((vAddr + size) > top) then
      (raise_c2_exception(CapEx_LengthViolation, capno))
    else if (vAddr < (base)) then
      (raise_c2_exception(CapEx_LengthViolation, capno))
    else
      (bit[64]) vAddr; (* XXX vAddr not truncated because top <= 2^64 and size > 0 *)
  }

function (bit[64]) TranslateAddress ((bit[64]) vAddr, (MemAccessType) accessType) = {
  incrementCP0Count();
  let pcc = capRegToCapStruct(PCC) in
  let base  = unsigned(getCapBase(pcc)) in
  let top   = unsigned(getCapTop(pcc)) in
  let absPC = (unsigned(vAddr)) in
  if ((absPC mod 4)  != 0) then (* bad PC alignment *)
    (SignalExceptionBadAddr(AdEL, (bit[64]) absPC)) (* XXX absPC may be truncated *)
  else if ((absPC + 4) > top) then
    (raise_c2_exception_noreg(CapEx_LengthViolation))
  else
    TLBTranslate((bit[64]) absPC, accessType) (* XXX assert absPC never gets truncated due to above check and top <= 2^64 for valid caps *)
}

function unit checkCP2usable () =
      {
        if (~((CP0Status.CU)[2])) then
          {
            (CP0Cause.CE) := 0b10;
            (SignalException(CpU));
          }
      }

