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

let (nat) max_otype = 0xffffff
let have_cp2 = true

function (CapStruct) readCapReg((regno) n) =
  capRegToCapStruct(CapRegs[n])

function unit writeCapReg((regno) n, (CapStruct) cap) =
  CapRegs[n] := capStructToCapReg(cap)

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
    if (~ (CP0Status.EXL)) then {
      let pc  = (bit[64]) PC in (* Cast forces read of register. *)
      let pcc = capRegToCapStruct(PCC) in
      let (success, epcc) = setCapOffset(pcc, pc) in
      if (success) then
        C31 := capStructToCapReg(epcc)
      else
        C31 := capStructToCapReg(int_to_cap(getCapBase(pcc) + pc));
    };

    nextPCC    := C29; (* KCC *)
    delayedPCC := C29; (* always write delayedPCC together with nextPCC so 
                          that non-capability branches don't override PCC *)
    let base = (bit[64]) (getCapBase(capRegToCapStruct(C29))) in
    SignalExceptionMIPS(ex, base);
  }

function unit ERETHook() =
  {
    nextPCC    := C31;
    delayedPCC := C31; (* always write delayedPCC together with nextPCC so 
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
  (tag[0], reverse_endianness(mem))
}

function (bool, bit[cap_size_t * 8]) MEMr_tagged_reserve ((bit[64]) addr) =
{
  (* assumes addr is cap. aligned *)
  let ((bit[8]) tag : mem) = (MEMr_tag_reserve (addr, cap_size)) in
  (tag[0], reverse_endianness(mem))
}

function unit MEMw_tagged((bit[64]) addr, (bool) tag, (bit[cap_size_t * 8]) data) =
{
  (* assumes addr is cap. aligned *)
  MEMea_tag(addr, cap_size);
  MEMval_tag(addr, cap_size, 0b0000000 : [tag] :  reverse_endianness(data));
}

function bool MEMw_tagged_conditional((bit[64]) addr, (bool) tag, (bit[cap_size_t * 8]) data) =
{
  (* assumes addr is cap. aligned *)
  MEMea_tag_conditional(addr, cap_size);
  MEMval_tag_conditional(addr, cap_size, 0b0000000 : [tag] :  reverse_endianness(data));
}

function (bit[64]) align((bit[64]) addr, (nat) alignment) =
    let remainder = unsigned(addr) mod alignment in
    addr - remainder

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
    TAGw(align(addr, cap_size), 0x00);
    MEMea(addr,size);
    MEMval(addr, size, reverse_endianness(data));
  }

function bool effect {wmem} MEMw_conditional_wrapper(addr, size, data) =
  {
    (* On cheri non-capability writes must clear the corresponding tag*)
    MEMea_conditional(addr, size);
    success := MEMval_conditional(addr,size,reverse_endianness(data));
    if (success) then
      (* XXX as above TAGw is vestigal and must die *)
      TAGw(align(addr, cap_size), 0x00);
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
    base   := getCapBase(cap);
    top    := getCapTop(cap);
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
  let base  = getCapBase(pcc) in
  let top   = getCapTop(pcc) in
  let absPC = base + unsigned(vAddr) in
  if ((absPC mod 4)  != 0) then (* bad PC alignment *)
    (SignalExceptionBadAddr(AdEL, (bit[64]) absPC)) (* XXX absPC may be truncated *)
  else if ((absPC + 4) > top) then
    (raise_c2_exception_noreg(CapEx_LengthViolation))
  else
    TLBTranslate((bit[64]) absPC, accessType) (* XXX assert absPC never gets truncated due to above check and top <= 2^64 for valid caps *)
}

function unit checkCP2usable () =
  if not ((CP0Status.CU)[2]) then
    {
      (CP0Cause.CE) := 0b10;
      (SignalException(CpU));
    }
