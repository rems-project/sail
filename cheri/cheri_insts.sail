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
    if (register_inaccessible(cb)) then
      exit (raise_c2_exception_v(cb))
    else
      {
        cbval    := CapRegs[cb];
        wGPR(rd) := switch(op) {
          case CGetPerm     -> EXTZ(cbval[223..193])
          case CGetType     -> EXTZ(cbval.otype)
          case CGetBase     -> cbval.base
          case CGetOffset   -> cbval.cursor
          case CGetLen      -> cbval.length (* XXX only correct for 256-bit *)
          case CGetTag      -> EXTZ([cbval.tag])
          case CGetUnsealed -> EXTZ([cbval.sealed])
        }
      }
  }


union ast member regno CGetPCC
function clause decode (0b010010 : 0b00000 : 0b00000 : (regno) cd : 0b00000 : 0b000 : 0b111) = Some(CGetPCC(cd))
function clause execute (CGetPCC(cd)) =
    {
      if (register_inaccessible(cd)) then
        exit (raise_c2_exception_v(cd))
      else
        {
          (CapRegs[cd]).cursor      := 0;
          (*destReg          := PCC;*)
          (*destReg.cursor):= PC; XXX help *)
        } 
    }
(* Get and Set CP2 cause register *)

union ast member regno CGetCause
function clause decode (0b010010 : 0b00000 : (regno) rd : 0b00000 : 0b00000000 : 0b100) = Some(CGetCause(rd))
function clause execute (CGetCause(rd)) = 
    {
      if (~(PCC.access_EPCC)) then
        exit (raise_c2_exception_noreg(CapEx_AccessEPCCViolation))
      else
        wGPR(rd) := EXTZ(CapCause)
    }

union ast member (regno) CSetCause
function clause decode (0b010010 : 0b00100 : 0b00000 : 0b00000 : (regno) rt : 0b000 : 0b100) = Some(CSetCause(rt))
function clause execute (CSetCause((regno) rt)) = 
    {
      if (~(PCC.access_EPCC)) then
        exit (raise_c2_exception_noreg(CapEx_AccessEPCCViolation))
      else
        {
          (bit[64]) rt_val := rGPR(rt);
          CapCause.ExcCode := rt_val[15..8];
          CapCause.RegNum  := rt_val[7..0];
        }
    }

union ast member (regno, regno, regno) CAndPerm
function clause decode (0b010010 : 0b00100 : (regno) cd : (regno) cb : (regno) rt : 0b000 : 0b000) = Some(CAndPerm(cd, cb, rt))
function clause execute(CAndPerm(cd, cb, rt)) = 
{
  cb_reg := CapRegs[cb];
  if (register_inaccessible(cd)) then
    exit (raise_c2_exception_v(cd))
  else if (register_inaccessible(cb)) then
    exit (raise_c2_exception_v(cb))
  else if (~(cb_reg.tag)) then
    exit (raise_c2_exception(CapEx_TagViolation, cb))
  else if (~(cb_reg.sealed)) then
    exit (raise_c2_exception(CapEx_SealViolation, cb))
  else
    {
      (CapRegs[cd]) := cb_reg;
      (*cd_reg :=*)
    }
}

