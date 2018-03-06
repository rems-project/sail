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


scattered union ast

val execute : ast -> unit effect {barr, eamem, escape, rmem, rmemt, rreg, undef, wmv, wmvt, wreg}
scattered function execute

val decode : bits(32) -> option(ast) effect pure
scattered function decode

register PCC        : CapReg
register nextPCC    : CapReg
register delayedPCC : CapReg
register inCCallDelay : bits(1)
register C00 : CapReg /* aka default data capability, DDC */
register C01 : CapReg
register C02 : CapReg
register C03 : CapReg
register C04 : CapReg
register C05 : CapReg
register C06 : CapReg
register C07 : CapReg
register C08 : CapReg
register C09 : CapReg
register C10 : CapReg
register C11 : CapReg
register C12 : CapReg
register C13 : CapReg
register C14 : CapReg
register C15 : CapReg
register C16 : CapReg
register C17 : CapReg
register C18 : CapReg
register C19 : CapReg
register C20 : CapReg
register C21 : CapReg
register C22 : CapReg
register C23 : CapReg
register C24 : CapReg /* aka return code capability, RCC */
register C25 : CapReg
register C26 : CapReg /* aka invoked data capability, IDC */
register C27 : CapReg /* aka kernel reserved capability 1, KR1C */
register C28 : CapReg /* aka kernel reserved capability 2, KR2C */
register C29 : CapReg /* aka kernel code capability, KCC */
register C30 : CapReg /* aka kernel data capability, KDC */
register C31 : CapReg /* aka exception program counter capability, EPCC */

let IDC : regno = 0b11010 /* 26 */

let CapRegs : vector(32, dec, register(CapReg)) =
  [
    ref C31,
    ref C30,
    ref C29,
    ref C28,
    ref C27,
    ref C26,
    ref C25,
    ref C24,
    ref C23,
    ref C22,
    ref C21,
    ref C20,
    ref C19,
    ref C18,
    ref C17,
    ref C16,
    ref C15,
    ref C14,
    ref C13,
    ref C12,
    ref C11,
    ref C10,
    ref C09,
    ref C08,
    ref C07,
    ref C06,
    ref C05,
    ref C04,
    ref C03,
    ref C02,
    ref C01,
    ref C00
  ]

let max_otype = MAX(24) /*0xffffff*/
let have_cp2 = true

function readCapReg(n) : regno -> CapStruct =
  let 'i = unsigned(n) in
  capRegToCapStruct(reg_deref(CapRegs[i]))

function writeCapReg(n, cap) : (regno, CapStruct) -> unit =
  let 'i = unsigned(n) in
  (*CapRegs[i]) = capStructToCapReg(cap) 

enum CapEx = {
  CapEx_None, 
  CapEx_LengthViolation,
  CapEx_TagViolation,
  CapEx_SealViolation,
  CapEx_TypeViolation,
  CapEx_CallTrap,
  CapEx_ReturnTrap,
  CapEx_TSSUnderFlow,
  CapEx_UserDefViolation,
  CapEx_TLBNoStoreCap,
  CapEx_InexactBounds,
  CapEx_GlobalViolation,
  CapEx_PermitExecuteViolation,
  CapEx_PermitLoadViolation,
  CapEx_PermitStoreViolation,
  CapEx_PermitLoadCapViolation,
  CapEx_PermitStoreCapViolation,
  CapEx_PermitStoreLocalCapViolation,
  CapEx_PermitSealViolation,
  CapEx_AccessSystemRegsViolation,
  CapEx_PermitCCallViolation,
  CapEx_AccessCCallIDCViolation
}

function CapExCode(ex) : CapEx -> bits(8)=
  match ex {
    CapEx_None                          => 0x00,
    CapEx_LengthViolation               => 0x01,
    CapEx_TagViolation                  => 0x02,
    CapEx_SealViolation                 => 0x03,
    CapEx_TypeViolation                 => 0x04,
    CapEx_CallTrap                      => 0x05,
    CapEx_ReturnTrap                    => 0x06,
    CapEx_TSSUnderFlow                  => 0x07,
    CapEx_UserDefViolation              => 0x08,
    CapEx_TLBNoStoreCap                 => 0x09,
    CapEx_InexactBounds                 => 0x0a,
    CapEx_GlobalViolation               => 0x10,
    CapEx_PermitExecuteViolation        => 0x11,
    CapEx_PermitLoadViolation           => 0x12,
    CapEx_PermitStoreViolation          => 0x13,
    CapEx_PermitLoadCapViolation        => 0x14,
    CapEx_PermitStoreCapViolation       => 0x15,
    CapEx_PermitStoreLocalCapViolation  => 0x16,
    CapEx_PermitSealViolation           => 0x17,
    CapEx_AccessSystemRegsViolation     => 0x18,
    CapEx_PermitCCallViolation          => 0x19,
    CapEx_AccessCCallIDCViolation       => 0x1a
  }

bitfield CapCauseReg : bits(16) = {
  ExcCode : 15..8,
  RegNum : 7..0,
}

register CapCause : CapCauseReg

function SignalException (ex) = 
  {
    if (not (CP0Status.EXL())) then {
      let pc  = PC in 
      let pcc = capRegToCapStruct(PCC) in
      let (success, epcc) = setCapOffset(pcc, pc) in
      if (success) then
        C31 = capStructToCapReg(epcc)
      else
        C31 = capStructToCapReg(int_to_cap(to_bits(64, getCapBase(pcc)) + unsigned(pc)));
    };

    nextPCC    = C29; /* KCC */
    delayedPCC = C29; /* always write delayedPCC together with nextPCC so 
                          that non-capability branches don't override PCC */
    let base = getCapBase(capRegToCapStruct(C29)) in
    SignalExceptionMIPS(ex, to_bits(64, base));
  }

function ERETHook() : unit -> unit =
  {
    nextPCC    = C31;
    delayedPCC = C31; /* always write delayedPCC together with nextPCC so 
                          that non-capability branches don't override PCC */
  }

val raise_c2_exception8 : forall ('o : Type) . (CapEx, bits(8)) -> 'o effect {escape, rreg, wreg}
function raise_c2_exception8(capEx, regnum) =
  {
    CapCause->ExcCode() = CapExCode(capEx);
    CapCause->RegNum()  = regnum;
    let mipsEx = 
      if ((capEx == CapEx_CallTrap) | (capEx == CapEx_ReturnTrap)) 
      then C2Trap else C2E in
    SignalException(mipsEx);
  }

val raise_c2_exception : forall ('o : Type) . (CapEx, regno) -> 'o effect {escape, rreg, wreg}
function raise_c2_exception(capEx, regnum) =
  let reg8 = 0b000 @ regnum in
  if ((capEx == CapEx_AccessSystemRegsViolation) & (regnum == IDC)) then
     raise_c2_exception8(CapEx_AccessCCallIDCViolation, reg8)
  else
     raise_c2_exception8(capEx, reg8)

val raise_c2_exception_noreg : forall ('o : Type) . (CapEx) -> 'o effect {escape, rreg, wreg}
function raise_c2_exception_noreg(capEx) =
  raise_c2_exception8(capEx, 0xff)

val pcc_access_system_regs : unit -> bool effect {rreg}
function pcc_access_system_regs () = 
      let pcc = capRegToCapStruct(PCC) in
      (pcc.access_system_regs)

val register_inaccessible : regno -> bool effect {rreg}
function register_inaccessible(r) =
  if (r == IDC) & inCCallDelay then true else
  let is_sys_reg : bool = match r {
    0b11011  => true,
    0b11100  => true,
    0b11101  => true,
    0b11110  => true,
    0b11111  => true,
    _        => false
  } in
  if is_sys_reg then
    not (pcc_access_system_regs ())
  else
    false

val MEMr_tag = "read_tag"  : bits(64) -> bool effect { rmemt }
val MEMw_tag = "write_tag" : (bits(64) , bool) -> unit effect { wmvt }

val MEMr_tagged : bits(64) -> (bool, bits('cap_size * 8)) effect { escape, rmem, rmemt }
function MEMr_tagged (addr) =
{
  /* assumes addr is cap. aligned */
  assert(unsigned(addr) % cap_size == 0);
  let tag  = MEMr_tag(addr) in
  let data = MEMr(addr, cap_size) in
  (tag, reverse_endianness(data))
}

val MEMr_tagged_reserve : bits(64) -> (bool, bits('cap_size * 8)) effect { escape, rmem, rmemt }
function MEMr_tagged_reserve (addr) =
{
  /* assumes addr is cap. aligned */
  assert(unsigned(addr) % cap_size == 0);
  let tag = MEMr_tag(addr) in
  let data = MEMr_reserve(addr, cap_size) in
  (tag, reverse_endianness(data))
}

val MEMw_tagged : (bits(64), bool, bits('cap_size * 8)) -> unit effect { escape, eamem, wmv, wmvt }
function MEMw_tagged(addr, tag, data) =
{
  /* assumes addr is cap. aligned */
  assert(unsigned(addr) % cap_size == 0);
  MEMea(addr, cap_size);
  MEMval(addr, cap_size, reverse_endianness(data));
  MEMw_tag(addr, tag);
}

val MEMw_tagged_conditional : (bits(64), bool, bits('cap_size * 8)) -> bool effect { escape, eamem, wmv, wmvt }
function MEMw_tagged_conditional(addr, tag, data) =
{
  /* assumes addr is cap. aligned */
  assert(unsigned(addr) % cap_size == 0);
  MEMea_conditional(addr, cap_size);
  success = MEMval_conditional(addr, cap_size, reverse_endianness(data));
  if success then
     MEMw_tag(addr, tag);
  success;
}

let cap_addr_mask = to_bits(64, pow2(64) - cap_size)

val MEMw_wrapper : forall 'n, 'n >= 1. (bits(64), atom('n), bits(8 * 'n)) -> unit effect {escape, wmv, wmvt, wreg, eamem}
function MEMw_wrapper(addr, size, data) =
  let ledata = reverse_endianness(data) in
  if (addr == 0x000000007f000000) then
  {
    UART_WDATA   = ledata[7..0];
    UART_WRITTEN = 0b1;
  }
  else
  {
    /* require that writes don't cross capability boundaries (should be true due to mips alignment requirements) */  
    assert((addr & cap_addr_mask) == ((addr + to_bits(64, size - 1)) & cap_addr_mask));
    MEMea(addr, size);
    MEMval(addr, size, ledata);
    /* On cheri non-capability writes must clear the corresponding tag*/
    MEMw_tag(addr & cap_addr_mask, false);
  }

val MEMw_conditional_wrapper : forall 'n, 'n >= 1. (bits(64), atom('n), bits(8 * 'n)) -> bool effect {escape, wmv, wmvt, eamem}
function MEMw_conditional_wrapper(addr, size, data) =
  {
    /* require that writes don't cross capability boundaries (should be true due to mips alignment requirements) */
    assert((addr & cap_addr_mask) == ((addr + to_bits(64, size - 1)) & cap_addr_mask));
    MEMea_conditional(addr, size);
    success = MEMval_conditional(addr,size,reverse_endianness(data));
    if success then
       /* On cheri non-capability writes must clear the corresponding tag */
       MEMw_tag(addr & cap_addr_mask, false);
    success;
  }

val addrWrapper : (bits(64), MemAccessType, WordType) -> bits(64) effect {rreg, wreg, escape}
function addrWrapper(addr, accessType, width) =
  {
    capno = 0b00000;
    cap = readCapReg(capno);
    if (not (cap.tag)) then
      (raise_c2_exception(CapEx_TagViolation, capno))
    else if (cap.sealed) then
        (raise_c2_exception(CapEx_SealViolation, capno));
    match accessType {
      Instruction  => if (~(cap.permit_execute)) then (raise_c2_exception(CapEx_PermitExecuteViolation, capno)),
      LoadData     => if (~(cap.permit_load)) then (raise_c2_exception(CapEx_PermitLoadViolation, capno)),
      StoreData    => if (~(cap.permit_store)) then (raise_c2_exception(CapEx_PermitStoreViolation, capno))
    };
    cursor = getCapCursor(cap);
    vAddr  = cursor + unsigned(addr);
    size   = wordWidthBytes(width);
    base   = getCapBase(cap);
    top    = getCapTop(cap);
    if ((vAddr + size) > top) then
      (raise_c2_exception(CapEx_LengthViolation, capno))
    else if (vAddr < base) then
      (raise_c2_exception(CapEx_LengthViolation, capno))
    else
      to_bits(64, vAddr); /* XXX vAddr not truncated because top <= 2^64 and size > 0 */
  }

val TranslatePC : bits(64) -> bits(64) effect {rreg, wreg, undef, escape}
function TranslatePC (vAddr) = {
  incrementCP0Count();
  let pcc = capRegToCapStruct(PCC);
  let base  = getCapBase(pcc);
  let top   = getCapTop(pcc);
  let absPC = base + unsigned(vAddr);
  if ((absPC % 4)  != 0) then /* bad PC alignment */
    (SignalExceptionBadAddr(AdEL, to_bits(64, absPC))) /* XXX absPC may be truncated */
  else if not (pcc.tag) then
    (raise_c2_exception_noreg(CapEx_TagViolation))
  else if ((absPC + 4) > top) then
    (raise_c2_exception_noreg(CapEx_LengthViolation))
  else
    TLBTranslate(to_bits(64, absPC), Instruction) /* XXX assert absPC never gets truncated due to above check and top <= 2^64 for valid caps */
}
val checkCP2usable : unit -> unit effect {rreg, wreg, escape}
function checkCP2usable ()  =
  if not ((CP0Status.CU())[2]) then
    {
      (CP0Cause->CE()) = 0b10;
      (SignalException(CpU));
    }

function init_cp2_state () = {
  let defaultBits = capStructToCapReg(default_cap);
  PCC = defaultBits;
  nextPCC = defaultBits;
  delayedPCC = defaultBits;
  foreach(i from 0 to 31) {
    let idx = to_bits(5, i) in
    writeCapReg(idx, default_cap);
  }
}

function cp2_next_pc () = {
  PCC = nextPCC;
  if inBranchDelay then {
    nextPCC = delayedPCC;
  } else {
    inCCallDelay = 0b0;
  };
}

val capToString : CapStruct -> string effect {escape}
function capToString cap = {
         skip_escape(); /* because cheri128 getCapX functions contain asserts but cheri256 ones do not */
         concat_str(" t:",
         concat_str(if cap.tag then "1" else "0",
         concat_str(" s:",
         concat_str(if cap.sealed then "1" else "0",
         concat_str(" perms:",
         concat_str(BitStr(0b0 @ getCapPerms(cap)),
         concat_str(" type:",
         concat_str(BitStr(cap.otype),
         concat_str(" offset:",
         concat_str(BitStr(to_bits(64, getCapOffset(cap))),
         concat_str(" base:",
         concat_str(BitStr(to_bits(64, getCapBase(cap))),
         concat_str(" length:", BitStr(to_bits(64, min(getCapLength(cap), MAX(64)))))))))))))))))
         }

function dump_cp2_state () = {
  print(concat_str("DEBUG CAP PCC", capToString(capRegToCapStruct(PCC))));
  foreach(i from 0 to 31) {
    print(concat_str("DEBUG CAP REG ", concat_str(string_of_int(i), capToString(readCapReg(to_bits(5, i))))))
  }
}
