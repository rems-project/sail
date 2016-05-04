(* Operations that extract parts of a capability into GPR *)

union ast member (CGetXOp, regno, regno) CGetX
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : 0b00000000 : 0b000) = Some(CGetX(CGetPerm, rd, cb))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : 0b00000000 : 0b001) = Some(CGetX(CGetType, rd, cb))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : 0b00000000 : 0b010) = Some(CGetX(CGetBase, rd, cb))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : 0b00000000 : 0b011) = Some(CGetX(CGetLen, rd, cb))
(* NB CGetCause Handled separately *)
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : 0b00000000 : 0b101) = Some(CGetX(CGetTag, rd, cb))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : 0b00000000 : 0b110) = Some(CGetX(CGetUnsealed, rd, cb))
function clause decode (0b010010 : 0b01101 : (regno) rd : (regno) cb : 0b00000000 : 0b010) = Some(CGetX(CGetOffset, rd, cb)) (* NB encoding does not follow pattern *)

function clause execute (CGetX(op, rd, cb)) =
  {
    checkCP2usable();
    if (register_inaccessible(cb)) then
      exit (raise_c2_exception_v(cb))
    else
      {
        cbval    := CapRegs[cb];
        wGPR(rd) := switch(op) {
          case CGetPerm     -> EXTZ(cbval[223..193])  (* XXX only correct for 256-bit *)
          case CGetType     -> EXTZ(cbval.otype)
          case CGetBase     -> cbval.base
          case CGetOffset   -> cbval.offset
          case CGetLen      -> cbval.length
          case CGetTag      -> EXTZ([cbval.tag])
          case CGetUnsealed -> EXTZ([cbval.sealed])
        }
      }
  }


union ast member regno CGetPCC
function clause decode (0b010010 : 0b00000 : (regno) cd : 0b00000 : 0b11111 : 0b111111) = Some(CGetPCC(cd))
function clause execute (CGetPCC(cd)) =
    {
      checkCP2usable();
      if (register_inaccessible(cd)) then
        exit (raise_c2_exception_v(cd))
      else
        let pcc = (capRegToCapStruct(PCC)) in
        writeCapReg(cd, {pcc with offset = PC})
    }

union ast member (regno, regno) CGetPCCSetOffset
function clause decode (0b010010 : 0b00000 : (regno) cd : (regno) rs : 0b00111 : 0b111111) = Some(CGetPCCSetOffset(cd, rs))
function clause execute (CGetPCCSetOffset(cd, rs)) =
    {
      checkCP2usable();
      if (register_inaccessible(cd)) then
        exit (raise_c2_exception_v(cd))
      else
        let pcc = (capRegToCapStruct(PCC)) in
        let rs_val = rGPR(rs) in
        writeCapReg(cd, {pcc with offset = rs_val})
    }

(* Get and Set CP2 cause register *)

union ast member regno CGetCause
function clause decode (0b010010 : 0b00000 : (regno) rd : 0b00000 : 0b00000000 : 0b100) = Some(CGetCause(rd))
function clause execute (CGetCause(rd)) = 
    {
      checkCP2usable();
      if (~(PCC.access_EPCC)) then
        exit (raise_c2_exception_noreg(CapEx_AccessEPCCViolation))
      else
        wGPR(rd) := EXTZ(CapCause)
    }

union ast member (regno) CSetCause
function clause decode (0b010010 : 0b00100 : 0b00000 : 0b00000 : (regno) rt : 0b000 : 0b100) = Some(CSetCause(rt))
function clause execute (CSetCause((regno) rt)) = 
    {
      checkCP2usable();
      if (~(PCC.access_EPCC)) then
        exit (raise_c2_exception_noreg(CapEx_AccessEPCCViolation))
      else
        {
          (bit[64]) rt_val := rGPR(rt);
          CapCause.ExcCode := rt_val[15..8];
          CapCause.RegNum  := rt_val[7..0];
        }
    }

union ast member regregreg CAndPerm
function clause decode (0b010010 : 0b00100 : (regno) cd : (regno) cb : (regno) rt : 0b000 : 0b000) = Some(CAndPerm(cd, cb, rt))
function clause execute(CAndPerm(cd, cb, rt)) = 
{
  checkCP2usable();
  cb_val := readCapReg(cb);
  rt_val := rGPR(rt);
  if (register_inaccessible(cd)) then
    exit (raise_c2_exception_v(cd))
  else if (register_inaccessible(cb)) then
    exit (raise_c2_exception_v(cb))
  else if (~(cb_val.tag)) then
    exit (raise_c2_exception(CapEx_TagViolation, cb))
  else if (cb_val.sealed) then
    exit (raise_c2_exception(CapEx_SealViolation, cb))
  else
    {
      writeCapReg(cd, {cb_val with 
        sw_perms                   = (cb_val.sw_perms                   & (rt_val[30..15]));
        access_KR2C                = (cb_val.access_KR2C                & (rt_val[14]));
        access_KR1C                = (cb_val.access_KR1C                & (rt_val[13]));
        access_KCC                 = (cb_val.access_KCC                 & (rt_val[12]));
        access_KDC                 = (cb_val.access_KDC                 & (rt_val[11]));
        access_EPCC                = (cb_val.access_EPCC                & (rt_val[10]));
        perm_reserved9             = (cb_val.perm_reserved9             & (rt_val[9]));
        perm_reserved8             = (cb_val.perm_reserved8             & (rt_val[8]));
        permit_seal                = (cb_val.permit_seal                & (rt_val[7]));
        permit_store_ephemeral_cap = (cb_val.permit_store_ephemeral_cap & (rt_val[6]));
        permit_store_cap           = (cb_val.permit_store_cap           & (rt_val[5]));
        permit_load_cap            = (cb_val.permit_load_cap            & (rt_val[4]));
        permit_store               = (cb_val.permit_store               & (rt_val[3]));
        permit_load                = (cb_val.permit_load                & (rt_val[2]));
        permit_execute             = (cb_val.permit_execute             & (rt_val[1]));
        non_ephemeral              = (cb_val.non_ephemeral              & (rt_val[0]));
      })
    }
}

union ast member regregreg CToPtr
function clause decode (0b010010 : 0b01100 : (regno) rd : (regno) cb : (regno) ct : 0b000 : 0b000) = Some(CToPtr(rd, cb, ct))
function clause execute(CToPtr(rd, cb, ct)) = 
{
  checkCP2usable();
  ct_val := readCapReg(ct);
  cb_val := readCapReg(cb);
  if (register_inaccessible(cb)) then
    exit (raise_c2_exception_v(cb))
  else if (register_inaccessible(ct)) then
    exit (raise_c2_exception_v(ct))
  else if (~(ct_val.tag)) then
    exit (raise_c2_exception(CapEx_TagViolation, ct))
  else 
    {
      wGPR(rd) := if (~(cb_val.tag)) then
          ((bit[64]) 0)
        else
          (bit[64])(((nat)(cb_val.base)) + ((nat) (cb_val.offset)) - ((nat)(ct_val.base)))
    }
}

union ast member (regno, regno, regno, CPtrCmpOp) CPtrCmp
function clause decode (0b010010 : 0b01110 : (regno) rd : (regno) cb : (regno) ct : 0b000 : 0b000) = Some(CPtrCmp(rd, cb, ct, CEQ))
function clause decode (0b010010 : 0b01110 : (regno) rd : (regno) cb : (regno) ct : 0b000 : 0b001) = Some(CPtrCmp(rd, cb, ct, CNE))
function clause decode (0b010010 : 0b01110 : (regno) rd : (regno) cb : (regno) ct : 0b000 : 0b010) = Some(CPtrCmp(rd, cb, ct, CLT))
function clause decode (0b010010 : 0b01110 : (regno) rd : (regno) cb : (regno) ct : 0b000 : 0b011) = Some(CPtrCmp(rd, cb, ct, CLE))
function clause decode (0b010010 : 0b01110 : (regno) rd : (regno) cb : (regno) ct : 0b000 : 0b100) = Some(CPtrCmp(rd, cb, ct, CLTU))
function clause decode (0b010010 : 0b01110 : (regno) rd : (regno) cb : (regno) ct : 0b000 : 0b101) = Some(CPtrCmp(rd, cb, ct, CLEU))
function clause decode (0b010010 : 0b01110 : (regno) rd : (regno) cb : (regno) ct : 0b000 : 0b110) = Some(CPtrCmp(rd, cb, ct, CEXEQ))

function clause execute(CPtrCmp(rd, cb, ct, op)) = 
{
  checkCP2usable();
  if (register_inaccessible(cb)) then
    exit (raise_c2_exception_v(cb))
  else if (register_inaccessible(ct)) then
    exit (raise_c2_exception_v(ct))
  else 
    {
      cb_val := readCapReg(cb);
      ct_val := readCapReg(ct);
      equal  := false;
      ltu    := false;
      lts    := false;
      if (cb_val.tag != ct_val.tag) then
        {
          if (~(cb_val.tag)) then
            {
              ltu := true;
              lts := true;
            }
        }
      else
        {
          cursor1 := getCapCursor(cb_val);
          cursor2 := getCapCursor(ct_val);
          equal   := (cursor1 == cursor2);
          ltu     := (cursor1 < cursor2);
          lts     := (((bit[64])cursor1) <_s ((bit[64])cursor2));
        };
      wGPR(rd) := EXTZ(switch (op) {
        case CEQ   -> [equal]
        case CNE   -> [~(equal)]
        case CLT   -> [lts]
        case CLE   -> [lts | equal]
        case CLTU  -> [ltu]
        case CLEU  -> [lts | equal]
        case CEXEQ -> [cb_val == ct_val]
      })
    }
}

union ast member regregreg CIncOffset
function clause decode (0b010010 : 0b01101 : (regno) cd : (regno) cb : (regno) rt : 0b000 : 0b000) = Some(CIncOffset(cd, cb, rt))
function clause execute (CIncOffset(cd, cb, rt)) =
    {
      checkCP2usable();
      cb_val := readCapReg(cb);
      rt_val := rGPR(rt);
      if (register_inaccessible(cd)) then
        exit (raise_c2_exception_v(cd))
      else if (register_inaccessible(cb)) then
        exit (raise_c2_exception_v(cb))
      else if ((cb_val.tag) & (cb_val.sealed) & (rt_val != 0x0000000000000000)) then
        exit (raise_c2_exception(CapEx_SealViolation, cb))
      else
        writeCapReg(cd, {cb_val with offset=cb_val.offset+rt_val})
    }

union ast member regregreg CSetOffset
function clause decode (0b010010 : 0b01101 : (regno) cd : (regno) cb : (regno) rt : 0b000 : 0b001) = Some(CSetOffset(cd, cb, rt))
function clause execute (CSetOffset(cd, cb, rt)) =
    {
      checkCP2usable();
      cb_val := readCapReg(cb);
      rt_val := rGPR(rt);
      if (register_inaccessible(cd)) then
        exit (raise_c2_exception_v(cd))
      else if (register_inaccessible(cb)) then
        exit (raise_c2_exception_v(cb))
      else if ((cb_val.tag) & (cb_val.sealed)) then
        exit (raise_c2_exception(CapEx_SealViolation, cb))
      else
        writeCapReg(cd, {cb_val with offset=rt_val})
    }

union ast member regregreg CSetBounds
function clause decode (0b010010 : 0b00001 : (regno) cd : (regno) cb : (regno) rt : 0b000000) = Some(CSetBounds(cd, cb, rt))
function clause execute (CSetBounds(cd, cb, rt)) =
    {
      checkCP2usable();
      cb_val := readCapReg(cb);
      (nat) rt_val := rGPR(rt);
      (nat) cursor := getCapCursor(cb_val);
      if (register_inaccessible(cd)) then
        exit (raise_c2_exception_v(cd))
      else if (register_inaccessible(cb)) then
        exit (raise_c2_exception_v(cb))
      else if (~(cb_val.tag)) then
        exit (raise_c2_exception(CapEx_TagViolation, cb))
      else if (cb_val.sealed) then
        exit (raise_c2_exception(CapEx_SealViolation, cb))
      else if (cursor < ((nat)(cb_val.base))) then
        exit (raise_c2_exception(CapEx_LengthViolation, cb))
      else if ((cursor + rt_val) > ((nat)(cb_val.base) + (nat)(cb_val.length))) then
        exit (raise_c2_exception(CapEx_LengthViolation, cb))
      else
        writeCapReg(cd, {cb_val with base=(bit[64])cursor; length=(bit[64])rt_val; offset=0})
    }

union ast member (regno, regno) CClearTag
function clause decode (0b010010 : 0b00100 : (regno) cd : (regno) cb : 0b00000 : 0b000: 0b101) = Some(CClearTag(cd, cb))
function clause execute (CClearTag(cd, cb)) =
    {
      checkCP2usable();
      if (register_inaccessible(cd)) then
        exit (raise_c2_exception_v(cd))
      else if (register_inaccessible(cb)) then
        exit (raise_c2_exception_v(cb))
      else
        {
          cb_val := readCapReg(cb);
          writeCapReg(cd, {cb_val with tag = false});
        }
    }

union ast member (ClearRegSet, bit[16]) ClearRegs
function clause decode (0b010010 : 0b01111 : 0b00000 : (bit[16]) imm) = Some(ClearRegs(GPLo, imm)) (* ClearLo *)
function clause decode (0b010010 : 0b01111 : 0b00001 : (bit[16]) imm) = Some(ClearRegs(GPHi, imm)) (* ClearHi *)
function clause decode (0b010010 : 0b01111 : 0b00010 : (bit[16]) imm) = Some(ClearRegs(CLo, imm))  (* CClearLo *)
function clause decode (0b010010 : 0b01111 : 0b00011 : (bit[16]) imm) = Some(ClearRegs(CHi, imm))  (* CClearHi *)
function clause execute (ClearRegs(regset, mask)) =
{
  checkCP2usable();
  if (regset == CHi) then
    ()(* XXX check exception *);
  foreach (i from 0 to 15)
    if (mask[i]) then
      switch (regset) {
        case GPLo -> wGPR((bit[5])i) := 0
        case GPHi -> wGPR((bit[5])(i+16)) := 0
        case CLo  -> writeCapReg((bit[5]) i) := null_cap
        case CHi  -> writeCapReg((bit[5]) (i+16)) := null_cap
      }
}

union ast member regregreg CFromPtr
function clause decode (0b010010 : 0b00100 : (regno) cd : (regno) cb : (regno) rt : 0b000: 0b111) = Some(CFromPtr(cd, cb, rt))
function clause execute (CFromPtr(cd, cb, rt)) =
    {
      checkCP2usable();
      cb_val := readCapReg(cb);
      rt_val := rGPR(rt);
      if (register_inaccessible(cd)) then
        exit (raise_c2_exception_v(cd))
      else if (register_inaccessible(cb)) then
        exit (raise_c2_exception_v(cb))
      else if (rt == 0) then
        writeCapReg(cd, null_cap)
      else if (~(cb_val.tag)) then
        exit (raise_c2_exception(CapEx_TagViolation, cb))
      else if (cb_val.sealed) then
        exit (raise_c2_exception(CapEx_SealViolation, cb))
      else
        writeCapReg(cd, {cb_val with offset = rt_val});
    }

union ast member (regno, regno) CCheckPerm
function clause decode (0b010010 : 0b01011 : (regno) cs : 0b00000 : (regno) rt : 0b000: 0b000) = Some(CCheckPerm(cs, rt))
function clause execute (CCheckPerm(cs, rt)) =
    {
      checkCP2usable();
      cs_val := readCapReg(cs);
      cs_perms := capPermsToVec(cs_val);
      rt_perms := (rGPR(rt))[30..0];
      if (register_inaccessible(cs)) then
        exit (raise_c2_exception_v(cs))
      else if (~(cs_val.tag)) then
        exit (raise_c2_exception(CapEx_TagViolation, cs))
      else if ((cs_perms & rt_perms) != rt_perms) then
        exit (raise_c2_exception(CapEx_UserDefViolation, cs))
    }

union ast member (regno, regno) CCheckType
function clause decode (0b010010 : 0b01011 : (regno) cs : (regno) cb : 0b00000 : 0b000: 0b001) = Some(CCheckType(cs, cb))
function clause execute (CCheckType(cs, cb)) =
{
  checkCP2usable();
  cs_val := readCapReg(cs);
  cb_val := readCapReg(cb);
  if (register_inaccessible(cs)) then
    exit (raise_c2_exception_v(cs))
  else if (register_inaccessible(cb)) then
    exit (raise_c2_exception_v(cb))
  else if (~(cs_val.tag)) then
    exit (raise_c2_exception(CapEx_TagViolation, cs))
  else if (~(cb_val.tag)) then
    exit (raise_c2_exception(CapEx_TagViolation, cb))
  else if (~(cs_val.sealed)) then
    exit (raise_c2_exception(CapEx_SealViolation, cs))
  else if (~(cb_val.sealed)) then
    exit (raise_c2_exception(CapEx_SealViolation, cb))
  else if ((cs_val.otype) != (cb_val.otype)) then
    exit (raise_c2_exception(CapEx_TypeViolation, cs))
}

union ast member regregreg CSeal
function clause decode (0b010010 : 0b00010 : (regno) cd : (regno) cs : (regno) ct : 0b000: 0b000) = Some(CSeal(cd, cs, ct))
function clause execute (CSeal(cd, cs, ct)) =
{
  checkCP2usable();
  cs_val := readCapReg(cs);
  ct_val := readCapReg(ct);
  (nat) ct_cursor := ((nat)(ct_val.base) + (nat)(ct_val.offset));
  if (register_inaccessible(cd)) then
    exit (raise_c2_exception_v(cd))
  else if (register_inaccessible(cs)) then
    exit (raise_c2_exception_v(cs))
  else if (register_inaccessible(ct)) then
    exit (raise_c2_exception_v(ct))
  else if (~(cs_val.tag)) then
    exit (raise_c2_exception(CapEx_TagViolation, cs))
  else if (~(ct_val.tag)) then
    exit (raise_c2_exception(CapEx_TagViolation, ct))
  else if (cs_val.sealed) then
    exit (raise_c2_exception(CapEx_SealViolation, cs))
  else if (ct_val.sealed) then
    exit (raise_c2_exception(CapEx_SealViolation, ct))
  else if (~(ct_val.permit_seal)) then
    exit (raise_c2_exception(CapEx_PermitSealViolation, ct))
  else if ((nat)(ct_val.offset) >= (nat)(ct_val.length)) then
    exit (raise_c2_exception(CapEx_LengthViolation, ct))
  else if (ct_cursor > max_otype) then
    exit (raise_c2_exception(CapEx_LengthViolation, ct))
  else
    writeCapReg(cd, {cs_val with sealed=true; otype=((bit[24])ct_cursor)})
}

union ast member regregreg CUnseal
function clause decode (0b010010 : 0b00011 : (regno) cd : (regno) cs : (regno) ct : 0b000: 0b000) = Some(CUnseal(cd, cs, ct))
function clause execute (CUnseal(cd, cs, ct)) =
{
  checkCP2usable();
  cs_val := readCapReg(cs);
  ct_val := readCapReg(ct);
  (nat) ct_cursor := ((nat)(ct_val.base) + (nat)(ct_val.offset));
  if (register_inaccessible(cd)) then
    exit (raise_c2_exception_v(cd))
  else if (register_inaccessible(cs)) then
    exit (raise_c2_exception_v(cs))
  else if (register_inaccessible(ct)) then
    exit (raise_c2_exception_v(ct))
  else if (~(cs_val.tag)) then
    exit (raise_c2_exception(CapEx_TagViolation, cs))
  else if (~(ct_val.tag)) then
    exit (raise_c2_exception(CapEx_TagViolation, ct))
  else if (~(cs_val.sealed)) then
    exit (raise_c2_exception(CapEx_SealViolation, cs))
  else if (ct_val.sealed) then
    exit (raise_c2_exception(CapEx_SealViolation, ct))
  else if (ct_cursor != ((nat)(cs_val.otype))) then
    exit (raise_c2_exception(CapEx_TypeViolation, ct))
  else if (~(ct_val.permit_seal)) then
    exit (raise_c2_exception(CapEx_PermitSealViolation, ct))
  else if (unsigned(ct_val.offset) >= unsigned(ct_val.length)) then
    exit (raise_c2_exception(CapEx_LengthViolation, ct))
  else
    writeCapReg(cd, {cs_val with 
      sealed=false; 
      otype=0;
      non_ephemeral=(cs_val.non_ephemeral & ct_val.non_ephemeral)
    })
}

union ast member (regno, regno) CCall
function clause decode (0b010010 : 0b00101 : (regno) cs : (regno) cb : (bit[11]) selector) = Some(CCall(cs, cb))
function clause execute (CCall(cs, cb)) =
{
  checkCP2usable();
  (* Partial implementation of CCall with checks in hardware, but raising a trap to perform trusted stack manipulation *)
  cs_val := readCapReg(cs);
  cb_val := readCapReg(cb);
  if (register_inaccessible(cs)) then
    exit (raise_c2_exception_v(cs))
  else if (register_inaccessible(cb)) then
    exit (raise_c2_exception_v(cb))
  else if (~(cs_val.tag)) then
    exit (raise_c2_exception(CapEx_TagViolation, cs))
  else if (~(cb_val.tag)) then
    exit (raise_c2_exception(CapEx_TagViolation, cb))
  else if (~(cs_val.sealed)) then
    exit (raise_c2_exception(CapEx_SealViolation, cs))
  else if (~(cb_val.sealed)) then
    exit (raise_c2_exception(CapEx_SealViolation, cb))
  else if ((cs_val.otype) != (cb_val.otype)) then
    exit (raise_c2_exception(CapEx_TypeViolation, cs))
  else if (~(cs_val.permit_execute)) then
    exit (raise_c2_exception(CapEx_PermitExecuteViolation, cs))
  else if (cb_val.permit_execute) then
    exit (raise_c2_exception(CapEx_PermitExecuteViolation, cb))
  else if (cs_val.offset >= cs_val.length) then
    exit (raise_c2_exception(CapEx_LengthViolation, cs))
  else
    exit (raise_c2_exception(CapEx_CallTrap, cs));
}

union ast member unit CReturn
function clause decode (0b010010 : 0b00110 : 0b000000000000000000000) = Some(CReturn)
function clause execute (CReturn) =
    {
      checkCP2usable();
      exit (raise_c2_exception_noreg(CapEx_ReturnTrap))
    }

union ast member (regno, bit[16], bool) CBX
function clause decode (0b010010 : 0b01001 : (regno) cb : (bit[16]) imm) = Some(CBX(cb, imm, true)) (* CBTU *)
function clause decode (0b010010 : 0b01010 : (regno) cb : (bit[16]) imm) = Some(CBX(cb, imm, false)) (* CBTS *)

function clause execute (CBX(cb, imm, invert)) =
{
  checkCP2usable();
  if (register_inaccessible(cb)) then
    exit (raise_c2_exception_v(cb))
  else if (((CapRegs[cb]).tag) ^ invert) then
    {
      let (bit[64]) offset = (EXTS(imm : 0b00) + 4) in
      delayedPC     := PC + offset;
      branchPending := 1;
    }
}

union ast member (regno, regno, bool) CJALR
function clause decode (0b010010 : 0b00111 : (regno) cd : (regno) cb : 0b00000 : 0b000000) = Some(CJALR(cd, cb, true)) (* CJALR *)
function clause decode (0b010010 : 0b01000 : 0b00000    : (regno) cb : 0b00000 : 0b000000) = Some(CJALR(0b00000, cb, false)) (* CJR *)
function clause execute(CJALR(cd, cb, link)) = 
{
  checkCP2usable();
  cb_val := readCapReg(cb);
  if (link & register_inaccessible(cd)) then
    exit (raise_c2_exception_v(cd))
  else if (register_inaccessible(cb)) then
    exit (raise_c2_exception_v(cb))
  else if (~(cb_val.tag)) then
    exit (raise_c2_exception(CapEx_TagViolation, cb))
  else if (cb_val.sealed) then
    exit (raise_c2_exception(CapEx_SealViolation, cb))
  else if (~(cb_val.permit_execute)) then
    exit (raise_c2_exception(CapEx_PermitExecuteViolation, cb))
  else if (~(cb_val.non_ephemeral)) then
    exit (raise_c2_exception(CapEx_GlobalViolation, cb))
  else if (((nat)(cb_val.offset)) + 4 > ((nat) (cb_val.length))) then
    exit (raise_c2_exception(CapEx_LengthViolation, cb))
  else if (((cb_val.base+cb_val.offset)[1..0]) != 0b00) then
    exit (SignalException(AdEL))
  else
    {
      if (link) then
        writeCapReg(cd, {capRegToCapStruct(PCC) with offset=(PC+8)});
      delayedPC := cb_val.offset;
      delayedPCC := capStructToBit257(cb_val);
      branchPending := 1;
    }
}

union ast member (regno, regno, regno, bit[8], bool, WordType, bool) CLoad
function clause decode (0b110010 : (regno) rd : (regno) cb: (regno) rt : (bit[8]) offset : 0b0 : 0b00) = Some(CLoad(rd, cb, rt, offset, false, B, false)) (* CLBU *)
function clause decode (0b110010 : (regno) rd : (regno) cb: (regno) rt : (bit[8]) offset : 0b1 : 0b00) = Some(CLoad(rd, cb, rt, offset, true,  B, false)) (* CLB *)
function clause decode (0b110010 : (regno) rd : (regno) cb: (regno) rt : (bit[8]) offset : 0b0 : 0b01) = Some(CLoad(rd, cb, rt, offset, false, H, false)) (* CLHU *)
function clause decode (0b110010 : (regno) rd : (regno) cb: (regno) rt : (bit[8]) offset : 0b1 : 0b01) = Some(CLoad(rd, cb, rt, offset, true,  H, false)) (* CLH *)
function clause decode (0b110010 : (regno) rd : (regno) cb: (regno) rt : (bit[8]) offset : 0b0 : 0b10) = Some(CLoad(rd, cb, rt, offset, false, W, false)) (* CLWU *)
function clause decode (0b110010 : (regno) rd : (regno) cb: (regno) rt : (bit[8]) offset : 0b1 : 0b10) = Some(CLoad(rd, cb, rt, offset, true,  W, false)) (* CLW *)
function clause decode (0b110010 : (regno) rd : (regno) cb: (regno) rt : (bit[8]) offset : 0b0 : 0b11) = Some(CLoad(rd, cb, rt, offset, false, D, false)) (* CLD *)

function clause decode (0b010010 : 0b10000 : (regno) rd : (regno) cb : 0b00000001 : 0b0 : 0b00) = Some(CLoad(rd, cb, 0b00000, 0b00000000, false, B, true)) (* CLLBU *)
function clause decode (0b010010 : 0b10000 : (regno) rd : (regno) cb : 0b00000001 : 0b1 : 0b00) = Some(CLoad(rd, cb, 0b00000, 0b00000000, true,  B, true)) (* CLLB  *)
function clause decode (0b010010 : 0b10000 : (regno) rd : (regno) cb : 0b00000001 : 0b0 : 0b01) = Some(CLoad(rd, cb, 0b00000, 0b00000000, false, H, true)) (* CLLHU *)
function clause decode (0b010010 : 0b10000 : (regno) rd : (regno) cb : 0b00000001 : 0b1 : 0b01) = Some(CLoad(rd, cb, 0b00000, 0b00000000, true,  H, true)) (* CLLH  *)
function clause decode (0b010010 : 0b10000 : (regno) rd : (regno) cb : 0b00000001 : 0b0 : 0b10) = Some(CLoad(rd, cb, 0b00000, 0b00000000, false, W, true)) (* CLLWU *)
function clause decode (0b010010 : 0b10000 : (regno) rd : (regno) cb : 0b00000001 : 0b1 : 0b10) = Some(CLoad(rd, cb, 0b00000, 0b00000000, true,  W, true)) (* CLLW  *)
function clause decode (0b010010 : 0b10000 : (regno) rd : (regno) cb : 0b00000001 : 0b0 : 0b11) = Some(CLoad(rd, cb, 0b00000, 0b00000000, false, D, true)) (* CLLD  *)

function clause execute (CLoad(rd, cb, rt, offset, signext, width, linked)) =
  {
    checkCP2usable();
    cb_val := readCapReg(cb);
    if (register_inaccessible(cb)) then
      exit (raise_c2_exception_v(cb))
    else if (~(cb_val.tag)) then
      exit (raise_c2_exception(CapEx_TagViolation, cb))
    else if (cb_val.sealed) then
      exit (raise_c2_exception(CapEx_SealViolation, cb))
    else if (~(cb_val.permit_load)) then
      exit (raise_c2_exception(CapEx_PermitLoadViolation, cb))
    else
      {
        size   := wordWidthBytes(width);
        cursor := getCapCursor(cb_val);
        vAddr  := cursor + unsigned(rGPR(rt)) + (size*signed(offset));
        vAddr64:= (bit[64]) vAddr;
        if ((vAddr + size) > ((nat) (cb_val.base) + ((nat) (cb_val.length)))) then
          exit (raise_c2_exception(CapEx_LengthViolation, cb))
        else if (vAddr < ((nat) (cb_val.base))) then
          exit (raise_c2_exception(CapEx_LengthViolation, cb))
        else if ~(isAddressAligned(vAddr64, width)) then
          exit (SignalExceptionBadAddr(AdEL, vAddr64))
        else
          {
            pAddr      := (TranslateOrExit(vAddr64, LoadData));
            widthBytes := wordWidthBytes(width);
            memResult  := if (linked) then
                {
                  CP0LLBit  := 0b1;
                  CP0LLAddr := pAddr;
                  MEMr_reserve(pAddr, widthBytes);
                }
              else
                MEMr(pAddr, widthBytes);
            if (signext) then
              wGPR(rd) := EXTS(memResult)
            else
              wGPR(rd) := EXTZ(memResult)
          }
      }
  }

union ast member (regno, regno, regno, regno, bit[8], WordType, bool) CStore
function clause decode (0b111010 : (regno) rs : (regno) cb: (regno) rt : (bit[8]) offset : 0b0 : 0b00) = Some(CStore(rs, cb, rt, 0b00000, offset, B, false)) (* CSB *)
function clause decode (0b111010 : (regno) rs : (regno) cb: (regno) rt : (bit[8]) offset : 0b0 : 0b01) = Some(CStore(rs, cb, rt, 0b00000, offset, H, false)) (* CSH *)
function clause decode (0b111010 : (regno) rs : (regno) cb: (regno) rt : (bit[8]) offset : 0b0 : 0b10) = Some(CStore(rs, cb, rt, 0b00000, offset, W, false)) (* CSW *)
function clause decode (0b111010 : (regno) rs : (regno) cb: (regno) rt : (bit[8]) offset : 0b0 : 0b11) = Some(CStore(rs, cb, rt, 0b00000, offset, D, false)) (* CSD *)

function clause decode (0b010010 : 0b10000 : (regno) rs : (regno) cb : (regno) rd : 0b0000 : 0b00) = Some(CStore(rs, cb, 0b00000, rd, 0b00000000, B, true)) (* CSCB *)
function clause decode (0b010010 : 0b10000 : (regno) rs : (regno) cb : (regno) rd : 0b0000 : 0b01) = Some(CStore(rs, cb, 0b00000, rd, 0b00000000, H, true)) (* CSCH *)
function clause decode (0b010010 : 0b10000 : (regno) rs : (regno) cb : (regno) rd : 0b0000 : 0b10) = Some(CStore(rs, cb, 0b00000, rd, 0b00000000, W, true)) (* CSCW *)
function clause decode (0b010010 : 0b10000 : (regno) rs : (regno) cb : (regno) rd : 0b0000 : 0b11) = Some(CStore(rs, cb, 0b00000, rd, 0b00000000, D, true)) (* CSCD *)

function clause execute (CStore(rs, cb, rt, rd, offset, width, conditional)) =
  {
    checkCP2usable();
    cb_val := readCapReg(cb);
    if (register_inaccessible(cb)) then
      exit (raise_c2_exception_v(cb))
    else if (~(cb_val.tag)) then
      exit (raise_c2_exception(CapEx_TagViolation, cb))
    else if (cb_val.sealed) then
      exit (raise_c2_exception(CapEx_SealViolation, cb))
    else if (~(cb_val.permit_store)) then
      exit (raise_c2_exception(CapEx_PermitStoreViolation, cb))
    else
      {
        size   := wordWidthBytes(width);
        cursor := getCapCursor(cb_val);
        vAddr  := cursor + unsigned(rGPR(rt)) + (size * signed(offset));
        vAddr64:= (bit[64]) vAddr;
        if ((vAddr + size) > ((nat) (cb_val.base) + ((nat) (cb_val.length)))) then
          exit (raise_c2_exception(CapEx_LengthViolation, cb))
        else if (vAddr < ((nat) (cb_val.base))) then
          exit (raise_c2_exception(CapEx_LengthViolation, cb))
        else if ~(isAddressAligned(vAddr64, width)) then
          exit (SignalExceptionBadAddr(AdES, vAddr64))
        else
          {
            pAddr  := (TranslateOrExit(vAddr64, StoreData));
            rs_val := rGPR(rs);
            if (conditional) then
              {
                success := if (CP0LLBit[0]) then
                    switch(width)
                      {
                        case B -> MEMw_conditional_wrapper(pAddr, 1, rs_val[7..0])
                        case H -> MEMw_conditional_wrapper(pAddr, 2, rs_val[15..0])
                        case W -> MEMw_conditional_wrapper(pAddr, 4, rs_val[31..0])
                        case D -> MEMw_conditional_wrapper(pAddr, 8, rs_val)
                      }
                  else
                    false;
                wGPR(rd) := EXTZ([success]);
              }
              else
            switch(width)
              {
                case B -> MEMw_wrapper(pAddr, 1) := rs_val[7..0]
                case H -> MEMw_wrapper(pAddr, 2) := rs_val[15..0]
                case W -> MEMw_wrapper(pAddr, 4) := rs_val[31..0]
                case D -> MEMw_wrapper(pAddr, 8) := rs_val
              }
          }
      }
  }

union ast member (regno, regno, regno, regno, bit[11], bool) CSC
function clause decode (0b111110 : (regno) cs : (regno) cb: (regno) rt : (bit[11]) offset) = Some(CSC(cs, cb, rt, 0b00000, offset, false))
function clause decode (0b010010 : 0b10000 : (regno) cs : (regno) cb: (regno) rd : 0b00 : 0b0111) = Some(CSC(cs, cb, 0b00000, rd, 0b00000000000, true))
function clause execute (CSC(cs, cb, rt, rd, offset, conditional)) =
  {
    checkCP2usable();
    cs_val := readCapReg(cs);
    cb_val := readCapReg(cb);
    if (register_inaccessible(cs)) then
      exit (raise_c2_exception_v(cs))
    else if (register_inaccessible(cb)) then
      exit (raise_c2_exception_v(cb))
    else if (~(cb_val.tag)) then
      exit (raise_c2_exception(CapEx_TagViolation, cb))
    else if (cb_val.sealed) then
      exit (raise_c2_exception(CapEx_SealViolation, cb))
    else if (~(cb_val.permit_store_cap)) then
      exit (raise_c2_exception(CapEx_PermitStoreCapViolation, cb))
    else if ((~(cb_val.permit_store_ephemeral_cap)) & (cs_val.tag) & ~(cs_val.non_ephemeral)) then
      exit (raise_c2_exception(CapEx_PermitStoreLocalCapViolation, cb))
    else
      {
        cursor := getCapCursor(cb_val);
        vAddr  := cursor + unsigned(rGPR(rt)) + (16 * signed(offset));
        vAddr64:= (bit[64]) vAddr;
        if ((vAddr + cap_size) > ((nat) (cb_val.base) + ((nat) (cb_val.length)))) then
          exit (raise_c2_exception(CapEx_LengthViolation, cb))
        else if (vAddr < ((nat) (cb_val.base))) then
          exit (raise_c2_exception(CapEx_LengthViolation, cb))
        else if (vAddr64[4..0] != 0b00000) then
          exit (SignalExceptionBadAddr(AdES, vAddr64))
        else
          {
            pAddr  := (TranslateOrExit(vAddr64, if cs_val.tag then StoreData else StoreData)); (* XXX use StoreCap here. *)
            if (conditional) then
              {
                success := if (CP0LLBit[0]) then
                    MEMw_tagged_conditional(pAddr, cs_val.tag, (capStructToBit257(cs_val))[255..0])
                  else
                    false;
                wGPR(rd) := EXTZ([success]);
              }
            else
              MEMw_tagged(pAddr, cs_val.tag, (capStructToBit257(cs_val))[255..0]);
          }
      }
  }

union ast member (regno, regno, regno, bit[11], bool) CLC
function clause decode (0b110110 : (regno) cd : (regno) cb: (regno) rt : (bit[11]) offset) = Some(CLC(cd, cb, rt, offset, false))
function clause decode (0b010010 : 0b10000 : (regno) cd : (regno) cb: 0b0000000 : 0b1111) = Some(CLC(cd, cb, 0b00000, 0b00000000000, true))
function clause execute (CLC(cd, cb, rt, offset, linked)) =  
  {
    checkCP2usable();
    cb_val := readCapReg(cb);
    if (register_inaccessible(cd)) then
      exit (raise_c2_exception_v(cd))
    else if (register_inaccessible(cb)) then
      exit (raise_c2_exception_v(cb))
    else if (~(cb_val.tag)) then
      exit (raise_c2_exception(CapEx_TagViolation, cb))
    else if (cb_val.sealed) then
      exit (raise_c2_exception(CapEx_SealViolation, cb))
    else if (~(cb_val.permit_load_cap)) then
      exit (raise_c2_exception(CapEx_PermitLoadCapViolation, cb))
    else
      {
        cursor := getCapCursor(cb_val);
        vAddr  := cursor + unsigned(rGPR(rt)) + (16*signed(offset));
        vAddr64:= (bit[64]) vAddr;
        if ((vAddr + cap_size) > ((nat) (cb_val.base) + ((nat) (cb_val.length)))) then
          exit (raise_c2_exception(CapEx_LengthViolation, cb))
        else if (vAddr < ((nat) (cb_val.base))) then
          exit (raise_c2_exception(CapEx_LengthViolation, cb))
        else if (vAddr64[4..0] != 0b00000) then
          exit (SignalExceptionBadAddr(AdEL, vAddr64))
        else
          {
            pAddr  := (TranslateOrExit(vAddr64, LoadData)); (* XXX use LoadCap here. *)
            let (tag, mem) = (if (linked) 
              then
                {
                  CP0LLBit  := 0b1;
                  CP0LLAddr := pAddr;
                  MEMr_tagged_reserve(pAddr);
                }
              else 
                (MEMr_tagged(pAddr)))
            in
            (CapRegs[cd]) := ([tag] : mem);
          }
      }
  }
