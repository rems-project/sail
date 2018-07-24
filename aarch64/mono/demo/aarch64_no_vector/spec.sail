enum boolean = {FALSE, TRUE}

enum signal = {LOW, HIGH}

enum __RetCode = {
  __RC_OK,
  __RC_UNDEFINED,
  __RC_UNPREDICTABLE,
  __RC_SEE,
  __RC_IMPLEMENTATION_DEFINED,
  __RC_SUBARCHITECTURE_DEFINED,
  __RC_EXCEPTION_TAKEN,
  __RC_ASSERT_FAILED,
  __RC_UNMATCHED_CASE
}

type CPACRType = bits(32)

type CNTKCTLType = bits(32)

type ESRType = bits(32)

type FPCRType = bits(32)

type MAIRType = bits(64)

type SCRType = bits(32)

type SCTLRType = bits(32)

enum FPConvOp = {
  FPConvOp_CVT_FtoI,
  FPConvOp_CVT_ItoF,
  FPConvOp_MOV_FtoI,
  FPConvOp_MOV_ItoF,
  FPConvOp_CVT_FtoI_JS
}

enum Exception = {
  Exception_Uncategorized,
  Exception_WFxTrap,
  Exception_CP15RTTrap,
  Exception_CP15RRTTrap,
  Exception_CP14RTTrap,
  Exception_CP14DTTrap,
  Exception_AdvSIMDFPAccessTrap,
  Exception_FPIDTrap,
  Exception_PACTrap,
  Exception_CP14RRTTrap,
  Exception_IllegalState,
  Exception_SupervisorCall,
  Exception_HypervisorCall,
  Exception_MonitorCall,
  Exception_SystemRegisterTrap,
  Exception_ERetTrap,
  Exception_InstructionAbort,
  Exception_PCAlignment,
  Exception_DataAbort,
  Exception_SPAlignment,
  Exception_FPTrappedException,
  Exception_SError,
  Exception_Breakpoint,
  Exception_SoftwareStep,
  Exception_Watchpoint,
  Exception_SoftwareBreakpoint,
  Exception_VectorCatch,
  Exception_IRQ,
  Exception_FIQ
}

enum ArchVersion = {ARMv8p0, ARMv8p1, ARMv8p2, ARMv8p3}

enum Unpredictable = {
  Unpredictable_WBOVERLAPLD,
  Unpredictable_WBOVERLAPST,
  Unpredictable_LDPOVERLAP,
  Unpredictable_BASEOVERLAP,
  Unpredictable_DATAOVERLAP,
  Unpredictable_DEVPAGE2,
  Unpredictable_INSTRDEVICE,
  Unpredictable_RESCPACR,
  Unpredictable_RESMAIR,
  Unpredictable_RESTEXCB,
  Unpredictable_RESPRRR,
  Unpredictable_RESDACR,
  Unpredictable_RESVTCRS,
  Unpredictable_RESTnSZ,
  Unpredictable_OORTnSZ,
  Unpredictable_LARGEIPA,
  Unpredictable_ESRCONDPASS,
  Unpredictable_ILZEROIT,
  Unpredictable_ILZEROT,
  Unpredictable_BPVECTORCATCHPRI,
  Unpredictable_VCMATCHHALF,
  Unpredictable_VCMATCHDAPA,
  Unpredictable_WPMASKANDBAS,
  Unpredictable_WPBASCONTIGUOUS,
  Unpredictable_RESWPMASK,
  Unpredictable_WPMASKEDBITS,
  Unpredictable_RESBPWPCTRL,
  Unpredictable_BPNOTIMPL,
  Unpredictable_RESBPTYPE,
  Unpredictable_BPNOTCTXCMP,
  Unpredictable_BPMATCHHALF,
  Unpredictable_BPMISMATCHHALF,
  Unpredictable_RESTARTALIGNPC,
  Unpredictable_RESTARTZEROUPPERPC,
  Unpredictable_ZEROUPPER,
  Unpredictable_ERETZEROUPPERPC,
  Unpredictable_A32FORCEALIGNPC,
  Unpredictable_SMD,
  Unpredictable_AFUPDATE,
  Unpredictable_IESBinDebug,
  Unpredictable_ZEROPMSEVFR,
  Unpredictable_NOOPTYPES,
  Unpredictable_ZEROMINLATENCY,
  Unpredictable_CLEARERRITEZERO,
  Unpredictable_TBD
}

enum Constraint = {
  Constraint_NONE,
  Constraint_UNKNOWN,
  Constraint_UNDEF,
  Constraint_UNDEFEL0,
  Constraint_NOP,
  Constraint_TRUE,
  Constraint_FALSE,
  Constraint_DISABLED,
  Constraint_UNCOND,
  Constraint_COND,
  Constraint_ADDITIONAL_DECODE,
  Constraint_WBSUPPRESS,
  Constraint_FAULT,
  Constraint_FORCE,
  Constraint_FORCENOSLCHECK
}

enum InstrSet = {InstrSet_A64, InstrSet_A32, InstrSet_T32}

struct ProcState = {
  N : bits(1),
  Z : bits(1),
  C : bits(1),
  V : bits(1),
  D : bits(1),
  A : bits(1),
  I : bits(1),
  F : bits(1),
  PAN : bits(1),
  UAO : bits(1),
  SS : bits(1),
  IL : bits(1),
  EL : bits(2),
  nRW : bits(1),
  SP : bits(1),
  Q : bits(1),
  GE : bits(4),
  IT : bits(8),
  J : bits(1),
  T : bits(1),
  E : bits(1),
  M : bits(5)
}

enum BranchType = {
  BranchType_CALL,
  BranchType_ERET,
  BranchType_DBGEXIT,
  BranchType_RET,
  BranchType_JMP,
  BranchType_EXCEPTION,
  BranchType_UNKNOWN
}

struct ExceptionRecord = {
  typ : Exception,
  syndrome : bits(25),
  vaddress : bits(64),
  ipavalid : bool,
  ipaddress : bits(52)
}

enum Fault = {
  Fault_None,
  Fault_AccessFlag,
  Fault_Alignment,
  Fault_Background,
  Fault_Domain,
  Fault_Permission,
  Fault_Translation,
  Fault_AddressSize,
  Fault_SyncExternal,
  Fault_SyncExternalOnWalk,
  Fault_SyncParity,
  Fault_SyncParityOnWalk,
  Fault_AsyncParity,
  Fault_AsyncExternal,
  Fault_Debug,
  Fault_TLBConflict,
  Fault_Lockdown,
  Fault_Exclusive,
  Fault_ICacheMaint
}

enum AccType = {
  AccType_NORMAL,
  AccType_VEC,
  AccType_STREAM,
  AccType_VECSTREAM,
  AccType_ATOMIC,
  AccType_ATOMICRW,
  AccType_ORDERED,
  AccType_ORDEREDRW,
  AccType_LIMITEDORDERED,
  AccType_UNPRIV,
  AccType_IFETCH,
  AccType_PTW,
  AccType_DC,
  AccType_IC,
  AccType_DCZVA,
  AccType_AT
}

struct FaultRecord = {
  typ : Fault,
  acctype : AccType,
  ipaddress : bits(52),
  s2fs1walk : bool,
  write : bool,
  level : int,
  extflag : bits(1),
  secondstage : bool,
  domain : bits(4),
  errortype : bits(2),
  debugmoe : bits(4)
}

enum MBReqDomain = {
  MBReqDomain_Nonshareable,
  MBReqDomain_InnerShareable,
  MBReqDomain_OuterShareable,
  MBReqDomain_FullSystem
}

enum MBReqTypes = {MBReqTypes_Reads, MBReqTypes_Writes, MBReqTypes_All}

enum MemType = {MemType_Normal, MemType_Device}

enum DeviceType = {
  DeviceType_GRE,
  DeviceType_nGRE,
  DeviceType_nGnRE,
  DeviceType_nGnRnE
}

struct MemAttrHints = {attrs : bits(2), hints : bits(2), transient : bool}

struct MemoryAttributes = {
  typ : MemType,
  device : DeviceType,
  inner : MemAttrHints,
  outer : MemAttrHints,
  shareable : bool,
  outershareable : bool
}

struct FullAddress = {physicaladdress : bits(52), NS : bits(1)}

struct AddressDescriptor = {
  fault : FaultRecord,
  memattrs : MemoryAttributes,
  paddress : FullAddress,
  vaddress : bits(64)
}

struct DescriptorUpdate = {AF : bool, AP : bool, descaddr : AddressDescriptor}

enum MemAtomicOp = {
  MemAtomicOp_ADD,
  MemAtomicOp_BIC,
  MemAtomicOp_EOR,
  MemAtomicOp_ORR,
  MemAtomicOp_SMAX,
  MemAtomicOp_SMIN,
  MemAtomicOp_UMAX,
  MemAtomicOp_UMIN,
  MemAtomicOp_SWP
}

enum FPType = {
  FPType_Nonzero,
  FPType_Zero,
  FPType_Infinity,
  FPType_QNaN,
  FPType_SNaN
}

enum FPExc = {
  FPExc_InvalidOp,
  FPExc_DivideByZero,
  FPExc_Overflow,
  FPExc_Underflow,
  FPExc_Inexact,
  FPExc_InputDenorm
}

enum FPRounding = {
  FPRounding_TIEEVEN,
  FPRounding_POSINF,
  FPRounding_NEGINF,
  FPRounding_ZERO,
  FPRounding_TIEAWAY,
  FPRounding_ODD
}

enum SysRegAccess = {
  SysRegAccess_OK,
  SysRegAccess_UNDEFINED,
  SysRegAccess_TrapToEL1,
  SysRegAccess_TrapToEL2,
  SysRegAccess_TrapToEL3
}

enum SRType = {SRType_LSL, SRType_LSR, SRType_ASR, SRType_ROR, SRType_RRX}

enum ShiftType = {ShiftType_LSL, ShiftType_LSR, ShiftType_ASR, ShiftType_ROR}

enum PrefetchHint = {Prefetch_READ, Prefetch_WRITE, Prefetch_EXEC}

enum InterruptID = {
  InterruptID_PMUIRQ,
  InterruptID_COMMIRQ,
  InterruptID_CTIIRQ,
  InterruptID_COMMRX,
  InterruptID_COMMTX
}

enum CrossTriggerOut = {
  CrossTriggerOut_DebugRequest,
  CrossTriggerOut_RestartRequest,
  CrossTriggerOut_IRQ,
  CrossTriggerOut_RSVD3,
  CrossTriggerOut_TraceExtIn0,
  CrossTriggerOut_TraceExtIn1,
  CrossTriggerOut_TraceExtIn2,
  CrossTriggerOut_TraceExtIn3
}

enum CrossTriggerIn = {
  CrossTriggerIn_CrossHalt,
  CrossTriggerIn_PMUOverflow,
  CrossTriggerIn_RSVD2,
  CrossTriggerIn_RSVD3,
  CrossTriggerIn_TraceExtOut0,
  CrossTriggerIn_TraceExtOut1,
  CrossTriggerIn_TraceExtOut2,
  CrossTriggerIn_TraceExtOut3
}

enum MemBarrierOp = {MemBarrierOp_DSB, MemBarrierOp_DMB, MemBarrierOp_ISB}

struct AccessDescriptor = {
  acctype : AccType,
  page_table_walk : bool,
  secondstage : bool,
  s2fs1walk : bool,
  level : int
}

struct Permissions = {ap : bits(3), xn : bits(1), xxn : bits(1), pxn : bits(1)}

struct TLBRecord = {
  perms : Permissions,
  nG : bits(1),
  domain : bits(4),
  contiguous : bool,
  level : int,
  blocksize : int,
  descupdate : DescriptorUpdate,
  CnP : bits(1),
  addrdesc : AddressDescriptor
}

enum ImmediateOp = {
  ImmediateOp_MOVI,
  ImmediateOp_MVNI,
  ImmediateOp_ORR,
  ImmediateOp_BIC
}

enum MoveWideOp = {MoveWideOp_N, MoveWideOp_Z, MoveWideOp_K}

enum SystemAccessType = {
  SystemAccessType_RT,
  SystemAccessType_RRT,
  SystemAccessType_DT
}

enum VBitOp = {VBitOp_VBIF, VBitOp_VBIT, VBitOp_VBSL, VBitOp_VEOR}

enum TimeStamp = {TimeStamp_None, TimeStamp_Virtual, TimeStamp_Physical}

enum PrivilegeLevel = {PL3, PL2, PL1, PL0}

struct AArch32_SErrorSyndrome = {AET : bits(2), ExT : bits(1)}

enum SystemOp = {Sys_AT, Sys_DC, Sys_IC, Sys_TLBI, Sys_SYS}

struct PCSample = {
  valid_name : bool,
  pc : bits(64),
  el : bits(2),
  rw : bits(1),
  ns : bits(1),
  contextidr : bits(32),
  contextidr_el2 : bits(32),
  vmid : bits(16)
}

enum ReduceOp = {
  ReduceOp_FMINNUM,
  ReduceOp_FMAXNUM,
  ReduceOp_FMIN,
  ReduceOp_FMAX,
  ReduceOp_FADD,
  ReduceOp_ADD
}

enum LogicalOp = {LogicalOp_AND, LogicalOp_EOR, LogicalOp_ORR}

enum ExtendType = {
  ExtendType_SXTB,
  ExtendType_SXTH,
  ExtendType_SXTW,
  ExtendType_SXTX,
  ExtendType_UXTB,
  ExtendType_UXTH,
  ExtendType_UXTW,
  ExtendType_UXTX
}

enum SystemHintOp = {
  SystemHintOp_NOP,
  SystemHintOp_YIELD,
  SystemHintOp_WFE,
  SystemHintOp_WFI,
  SystemHintOp_SEV,
  SystemHintOp_SEVL,
  SystemHintOp_ESB,
  SystemHintOp_PSB
}

enum MemOp = {MemOp_LOAD, MemOp_STORE, MemOp_PREFETCH}

enum OpType = {
  OpType_Load,
  OpType_Store,
  OpType_LoadAtomic,
  OpType_Branch,
  OpType_Other
}

enum FPUnaryOp = {FPUnaryOp_ABS, FPUnaryOp_MOV, FPUnaryOp_NEG, FPUnaryOp_SQRT}

enum CompareOp = {
  CompareOp_GT,
  CompareOp_GE,
  CompareOp_EQ,
  CompareOp_LE,
  CompareOp_LT
}

enum PSTATEField = {
  PSTATEField_DAIFSet,
  PSTATEField_DAIFClr,
  PSTATEField_PAN,
  PSTATEField_UAO,
  PSTATEField_SP
}

enum FPMaxMinOp = {
  FPMaxMinOp_MAX,
  FPMaxMinOp_MIN,
  FPMaxMinOp_MAXNUM,
  FPMaxMinOp_MINNUM
}

enum CountOp = {CountOp_CLZ, CountOp_CLS, CountOp_CNT}

enum VFPNegMul = {VFPNegMul_VNMLA, VFPNegMul_VNMLS, VFPNegMul_VNMUL}

enum VBitOps = {VBitOps_VBIF, VBitOps_VBIT, VBitOps_VBSL}

enum VCGEtype = {VCGEtype_signed, VCGEtype_unsigned, VCGEtype_fp}

enum VCGTtype = {VCGTtype_signed, VCGTtype_unsigned, VCGTtype_fp}

enum __InstrEnc = {__A64, __A32, __T16, __T32}

val AArch64_CheckAndUpdateDescriptor_SecondStage : (DescriptorUpdate, FaultRecord, bits(64), AccType, bool, bool, bool) -> FaultRecord effect {escape, rreg, rmem, wmem, undef}

val AArch64_TranslationTableWalk_SecondStage : (bits(52), bits(64), AccType, bool, bool, int) -> TLBRecord effect {escape, rreg, rmem, undef}

val AArch64_SecondStageTranslate : (AddressDescriptor, bits(64), AccType, bool, bool, bool, int, bool) -> AddressDescriptor effect {rreg, escape, rmem, undef, wmem}

val AArch64_CheckAndUpdateDescriptor : (DescriptorUpdate, FaultRecord, bool, bits(64), AccType, bool, bool, bool) -> FaultRecord effect {escape, rreg, rmem, wmem, undef}

register __unconditional : bool

register __currentCond : bits(4)

val __UNKNOWN_real : unit -> real

function __UNKNOWN_real () = return(0.0)

val __UNKNOWN_integer : unit -> int

function __UNKNOWN_integer () = return(0)

register __ThisInstrEnc : __InstrEnc

register __ThisInstr : bits(32)

register __Sleeping : bool

register __PendingPhysicalSError : bool

register __PendingInterrupt : bool

register __Memory : bits(52)

register __ExclusiveLocal : bool

register __BranchTaken : bool

register _V : vector(32, dec, bits(128))

register _R : vector(31, dec, bits(64))

register _PC : bits(64)

val aget_PC : unit -> bits(64) effect {rreg}

function aget_PC () = return(_PC)

register VTTBR_EL2 : bits(64)

register VTCR_EL2 : bits(32)

register VSESR_EL2 : bits(32)

register VDFSR : bits(32)

register VBAR_EL3 : bits(64)

register VBAR_EL2 : bits(64)

register VBAR_EL1 : bits(64)

register VBAR : bits(32)

val UndefinedFault : unit -> unit effect {escape}

function UndefinedFault () = assert(false, "Undefined fault")

val ThisInstrAddr : forall ('N : Int), 'N >= 0. unit -> bits('N) effect {rreg}

function ThisInstrAddr () = return(slice(_PC, 0, 'N))

val ThisInstr : unit -> bits(32) effect {rreg}

function ThisInstr () = return(__ThisInstr)

register TTBR1_EL2 : bits(64)

register TTBR1_EL1 : bits(64)

register TTBR0_EL3 : bits(64)

register TTBR0_EL2 : bits(64)

register TTBR0_EL1 : bits(64)

register TTBCR : bits(32)

register TCR_EL3 : bits(32)

register TCR_EL2 : bits(64)

register TCR_EL1 : bits(64)

val __UNKNOWN_SystemHintOp : unit -> SystemHintOp

function __UNKNOWN_SystemHintOp () = return(SystemHintOp_NOP)

val SynchronizeContext : unit -> unit

function SynchronizeContext () = ()

register SP_mon : bits(32)

register SP_EL3 : bits(64)

register SP_EL2 : bits(64)

register SP_EL1 : bits(64)

register SP_EL0 : bits(64)

register SPSR_und : bits(32)

register SPSR_svc : bits(32)

register SPSR_mon : bits(32)

register SPSR_irq : bits(32)

register SPSR_hyp : bits(32)

register SPSR_fiq : bits(32)

register SPSR_abt : bits(32)

register SPSR_EL3 : bits(32)

register SPSR_EL2 : bits(32)

register SPSR_EL1 : bits(32)

register SPIDEN : signal

val SErrorPending : unit -> bool effect {rreg}

function SErrorPending () = return(__PendingPhysicalSError)

register SDER : bits(32)

register SDCR : bits(32)

register SCTLR_EL3 : bits(32)

register SCTLR_EL2 : bits(32)

register SCTLR_EL1 : bits(32)

register SCTLR : bits(32)

register SCR_EL3 : bits(32)

register SCR : bits(32)

val ResetExternalDebugRegisters : bool -> unit

function ResetExternalDebugRegisters cold_reset = ()

register RVBAR_EL3 : bits(64)

register RVBAR_EL2 : bits(64)

register RVBAR_EL1 : bits(64)

register RC : vector(5, dec, bits(64))

val ProfilingSynchronizationBarrier : unit -> unit

function ProfilingSynchronizationBarrier () = ()

val ProcessorID : unit -> int

function ProcessorID () = return(0)

val __UNKNOWN_PrefetchHint : unit -> PrefetchHint

function __UNKNOWN_PrefetchHint () = return(Prefetch_READ)

val __UNKNOWN_PSTATEField : unit -> PSTATEField

function __UNKNOWN_PSTATEField () = return(PSTATEField_DAIFSet)

register PSTATE : ProcState

val PACCellShuffle : bits(64) -> bits(64) effect {undef}

function PACCellShuffle indata = {
  outdata : bits(64) = undefined;
  outdata : bits(64) = __SetSlice_bits(64, 4, outdata, 0, slice(indata, 52, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 4, slice(indata, 24, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 8, slice(indata, 44, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 12, slice(indata, 0, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 16, slice(indata, 28, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 20, slice(indata, 48, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 24, slice(indata, 4, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 28, slice(indata, 40, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 32, slice(indata, 32, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 36, slice(indata, 12, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 40, slice(indata, 56, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 44, slice(indata, 20, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 48, slice(indata, 8, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 52, slice(indata, 36, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 56, slice(indata, 16, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 60, slice(indata, 60, 4));
  return(outdata)
}

val PACCellInvShuffle : bits(64) -> bits(64) effect {undef}

function PACCellInvShuffle indata = {
  outdata : bits(64) = undefined;
  outdata : bits(64) = __SetSlice_bits(64, 4, outdata, 0, slice(indata, 12, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 4, slice(indata, 24, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 8, slice(indata, 48, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 12, slice(indata, 36, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 16, slice(indata, 56, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 20, slice(indata, 44, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 24, slice(indata, 4, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 28, slice(indata, 16, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 32, slice(indata, 32, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 36, slice(indata, 52, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 40, slice(indata, 28, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 44, slice(indata, 8, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 48, slice(indata, 20, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 52, slice(indata, 0, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 56, slice(indata, 40, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 60, slice(indata, 60, 4));
  return(outdata)
}

register OSLSR_EL1 : bits(32)

register OSDLR_EL1 : bits(32)

val __UNKNOWN_MoveWideOp : unit -> MoveWideOp

function __UNKNOWN_MoveWideOp () = return(MoveWideOp_N)

val __UNKNOWN_MemType : unit -> MemType

function __UNKNOWN_MemType () = return(MemType_Normal)

val __UNKNOWN_MemOp : unit -> MemOp

function __UNKNOWN_MemOp () = return(MemOp_LOAD)

let MemHint_RWA : vector(2, dec, bit) = 0b11

let MemHint_RA : vector(2, dec, bit) = 0b10

let MemHint_No : vector(2, dec, bit) = 0b00

val __UNKNOWN_MemBarrierOp : unit -> MemBarrierOp

function __UNKNOWN_MemBarrierOp () = return(MemBarrierOp_DSB)

let MemAttr_WT : vector(2, dec, bit) = 0b10

let MemAttr_WB : vector(2, dec, bit) = 0b11

let MemAttr_NC : vector(2, dec, bit) = 0b00

val __UNKNOWN_MemAtomicOp : unit -> MemAtomicOp

function __UNKNOWN_MemAtomicOp () = return(MemAtomicOp_ADD)

register MDSCR_EL1 : bits(32)

register MDCR_EL3 : bits(32)

register MDCR_EL2 : bits(32)

val __UNKNOWN_MBReqTypes : unit -> MBReqTypes

function __UNKNOWN_MBReqTypes () = return(MBReqTypes_Reads)

val __UNKNOWN_MBReqDomain : unit -> MBReqDomain

function __UNKNOWN_MBReqDomain () = return(MBReqDomain_Nonshareable)

register MAIR_EL3 : bits(64)

register MAIR_EL2 : bits(64)

register MAIR_EL1 : bits(64)

let M32_User : vector(5, dec, bit) = 0b10000

let M32_Undef : vector(5, dec, bit) = 0b11011

let M32_System : vector(5, dec, bit) = 0b11111

let M32_Svc : vector(5, dec, bit) = 0b10011

let M32_Monitor : vector(5, dec, bit) = 0b10110

let M32_IRQ : vector(5, dec, bit) = 0b10010

let M32_Hyp : vector(5, dec, bit) = 0b11010

let M32_FIQ : vector(5, dec, bit) = 0b10001

let M32_Abort : vector(5, dec, bit) = 0b10111

val __UNKNOWN_LogicalOp : unit -> LogicalOp

function __UNKNOWN_LogicalOp () = return(LogicalOp_AND)

register LR_mon : bits(32)

val IsExclusiveLocal : (FullAddress, int, int) -> bool effect {rreg}

function IsExclusiveLocal (paddress, 'processorid, 'size) = return(__ExclusiveLocal)

val InterruptPending : unit -> bool effect {rreg}

function InterruptPending () = return(__PendingInterrupt)

val asl_Int : forall ('N : Int), 'N >= 0. (bits('N), bool) -> int

function asl_Int (x, unsigned) = {
  result : int = if unsigned then UInt(x) else SInt(x);
  return(result)
}

val InstructionSynchronizationBarrier : unit -> unit

function InstructionSynchronizationBarrier () = ()

val __UNKNOWN_InstrSet : unit -> InstrSet

function __UNKNOWN_InstrSet () = return(InstrSet_A64)

register ID_AA64DFR0_EL1 : bits(64)

val Hint_Yield : unit -> unit

function Hint_Yield () = ()

val Hint_Prefetch : (bits(64), PrefetchHint, int, bool) -> unit

function Hint_Prefetch (address, hint, 'target, stream) = ()

val Hint_Branch : BranchType -> unit

function Hint_Branch hint = ()

val HaveFP16Ext : unit -> bool

function HaveFP16Ext () = return(true)

val HaveAnyAArch32 : unit -> bool

function HaveAnyAArch32 () = return(false)

register HVBAR : bits(32)

register HSR : bits(32)

register HSCTLR : bits(32)

register HPFAR_EL2 : bits(64)

register HPFAR : bits(32)

register HIFAR : bits(32)

register HDFAR : bits(32)

register HDCR : bits(32)

register HCR_EL2 : bits(64)

register HCR2 : bits(32)

register HCR : bits(32)

val __UNKNOWN_Fault : unit -> Fault

function __UNKNOWN_Fault () = return(Fault_None)

val __UNKNOWN_FPUnaryOp : unit -> FPUnaryOp

function __UNKNOWN_FPUnaryOp () = return(FPUnaryOp_ABS)

val __UNKNOWN_FPType : unit -> FPType

function __UNKNOWN_FPType () = return(FPType_Nonzero)

register FPSR : bits(32)

register FPSCR : bits(32)

val __UNKNOWN_FPRounding : unit -> FPRounding

function __UNKNOWN_FPRounding () = return(FPRounding_TIEEVEN)

val __UNKNOWN_FPMaxMinOp : unit -> FPMaxMinOp

function __UNKNOWN_FPMaxMinOp () = return(FPMaxMinOp_MAX)

register FPEXC : bits(32)

val FPDecodeRounding : bits(2) -> FPRounding

function FPDecodeRounding rmode = match rmode {
  0b00 => return(FPRounding_TIEEVEN),
  0b01 => return(FPRounding_POSINF),
  0b10 => return(FPRounding_NEGINF),
  0b11 => return(FPRounding_ZERO)
}

val FPRoundingMode : bits(32) -> FPRounding

function FPRoundingMode fpcr = return(FPDecodeRounding(slice(fpcr, 22, 2)))

val __UNKNOWN_FPConvOp : unit -> FPConvOp

function __UNKNOWN_FPConvOp () = return(FPConvOp_CVT_FtoI)

register FPCR : bits(32)

register FAR_EL3 : bits(64)

register FAR_EL2 : bits(64)

register FAR_EL1 : bits(64)

val __UNKNOWN_boolean : unit -> bool

function __UNKNOWN_boolean () = return(false)

val __ResetInterruptState : unit -> unit effect {wreg}

function __ResetInterruptState () = {
  __PendingPhysicalSError = false;
  __PendingInterrupt = false
}

val __ResetExecuteState : unit -> unit effect {wreg}

function __ResetExecuteState () = __Sleeping = false

val Unreachable : unit -> unit effect {escape}

function Unreachable () = assert(false, "FALSE")

val RBankSelect : (bits(5), int, int, int, int, int, int, int) -> int effect {escape, undef}

function RBankSelect (mode, 'usr, 'fiq, 'irq, 'svc, 'abt, 'und, 'hyp) = {
  result : int = undefined;
  match mode {
    ? if ? == M32_User => result = usr,
    ? if ? == M32_FIQ => result = fiq,
    ? if ? == M32_IRQ => result = irq,
    ? if ? == M32_Svc => result = svc,
    ? if ? == M32_Abort => result = abt,
    ? if ? == M32_Hyp => result = hyp,
    ? if ? == M32_Undef => result = und,
    ? if ? == M32_System => result = usr,
    _ => Unreachable()
  };
  return(result)
}

val TakeUnmaskedSErrorInterrupts : unit -> unit effect {escape}

function TakeUnmaskedSErrorInterrupts () = assert(false, "FALSE")

val TakeUnmaskedPhysicalSErrorInterrupts : bool -> unit effect {escape}

function TakeUnmaskedPhysicalSErrorInterrupts iesb_req = assert(false, "FALSE")

val StopInstructionPrefetchAndEnableITR : unit -> unit effect {escape}

function StopInstructionPrefetchAndEnableITR () = assert(false, "FALSE")

val SendEvent : unit -> unit effect {escape}

function SendEvent () = assert(false, "FALSE")

val MarkExclusiveLocal : (FullAddress, int, int) -> unit effect {wreg}

function MarkExclusiveLocal (paddress, 'processorid, 'size) = __ExclusiveLocal = false

val MarkExclusiveGlobal : (FullAddress, int, int) -> unit effect {escape}

function MarkExclusiveGlobal (paddress, 'processorid, 'size) = assert(false, "FALSE")

val IsExclusiveGlobal : (FullAddress, int, int) -> bool effect {escape}

function IsExclusiveGlobal (paddress, 'processorid, 'size) = {
  assert(false, "FALSE");
  return(false)
}

val ExclusiveMonitorsStatus : unit -> bits(1) effect {escape}

function ExclusiveMonitorsStatus () = {
  assert(false, "FALSE");
  return(0b0)
}

val __UNKNOWN_Exception : unit -> Exception

function __UNKNOWN_Exception () = return(Exception_Uncategorized)

register EventRegister : bits(1)

val SendEventLocal : unit -> unit effect {wreg}

function SendEventLocal () = {
  EventRegister = 0b1;
  ()
}

val ErrorSynchronizationBarrier : (MBReqDomain, MBReqTypes) -> unit

function ErrorSynchronizationBarrier (domain, types) = ()

val EnterLowPowerState : unit -> unit effect {wreg}

function EnterLowPowerState () = __Sleeping = true

val WaitForInterrupt : unit -> unit effect {wreg}

function WaitForInterrupt () = {
  EnterLowPowerState();
  ()
}

val EndOfInstruction : unit -> unit effect {escape}

function EndOfInstruction () = throw(Error_ExceptionTaken())

register ESR_EL3 : bits(32)

register ESR_EL2 : bits(32)

register ESR_EL1 : bits(32)

val TweakCellRot : bits(4) -> bits(4) effect {undef}

function TweakCellRot incell_name = {
  outcell : bits(4) = undefined;
  outcell : bits(4) = __SetSlice_bits(4, 1, outcell, 3, [incell_name[0]] ^ [incell_name[1]]);
  outcell = __SetSlice_bits(4, 1, outcell, 2, [incell_name[3]]);
  outcell = __SetSlice_bits(4, 1, outcell, 1, [incell_name[2]]);
  outcell = __SetSlice_bits(4, 1, outcell, 0, [incell_name[1]]);
  return(outcell)
}

val TweakShuffle : bits(64) -> bits(64) effect {undef}

function TweakShuffle indata = {
  outdata : bits(64) = undefined;
  outdata : bits(64) = __SetSlice_bits(64, 4, outdata, 0, slice(indata, 16, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 4, slice(indata, 20, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 8, TweakCellRot(slice(indata, 24, 4)));
  outdata = __SetSlice_bits(64, 4, outdata, 12, slice(indata, 28, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 16, TweakCellRot(slice(indata, 44, 4)));
  outdata = __SetSlice_bits(64, 4, outdata, 20, slice(indata, 8, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 24, slice(indata, 12, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 28, TweakCellRot(slice(indata, 32, 4)));
  outdata = __SetSlice_bits(64, 4, outdata, 32, slice(indata, 48, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 36, slice(indata, 52, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 40, slice(indata, 56, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 44, TweakCellRot(slice(indata, 60, 4)));
  outdata = __SetSlice_bits(64, 4, outdata, 48, TweakCellRot(slice(indata, 0, 4)));
  outdata = __SetSlice_bits(64, 4, outdata, 52, slice(indata, 4, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 56, TweakCellRot(slice(indata, 40, 4)));
  outdata = __SetSlice_bits(64, 4, outdata, 60, TweakCellRot(slice(indata, 36, 4)));
  return(outdata)
}

val TweakCellInvRot : bits(4) -> bits(4) effect {undef}

function TweakCellInvRot incell_name = {
  outcell : bits(4) = undefined;
  outcell : bits(4) = __SetSlice_bits(4, 1, outcell, 3, [incell_name[2]]);
  outcell = __SetSlice_bits(4, 1, outcell, 2, [incell_name[1]]);
  outcell = __SetSlice_bits(4, 1, outcell, 1, [incell_name[0]]);
  outcell = __SetSlice_bits(4, 1, outcell, 0, [incell_name[0]] ^ [incell_name[3]]);
  return(outcell)
}

val TweakInvShuffle : bits(64) -> bits(64) effect {undef}

function TweakInvShuffle indata = {
  outdata : bits(64) = undefined;
  outdata : bits(64) = __SetSlice_bits(64, 4, outdata, 0, TweakCellInvRot(slice(indata, 48, 4)));
  outdata = __SetSlice_bits(64, 4, outdata, 4, slice(indata, 52, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 8, slice(indata, 20, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 12, slice(indata, 24, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 16, slice(indata, 0, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 20, slice(indata, 4, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 24, TweakCellInvRot(slice(indata, 8, 4)));
  outdata = __SetSlice_bits(64, 4, outdata, 28, slice(indata, 12, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 32, TweakCellInvRot(slice(indata, 28, 4)));
  outdata = __SetSlice_bits(64, 4, outdata, 36, TweakCellInvRot(slice(indata, 60, 4)));
  outdata = __SetSlice_bits(64, 4, outdata, 40, TweakCellInvRot(slice(indata, 56, 4)));
  outdata = __SetSlice_bits(64, 4, outdata, 44, TweakCellInvRot(slice(indata, 16, 4)));
  outdata = __SetSlice_bits(64, 4, outdata, 48, slice(indata, 32, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 52, slice(indata, 36, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 56, slice(indata, 40, 4));
  outdata = __SetSlice_bits(64, 4, outdata, 60, TweakCellInvRot(slice(indata, 44, 4)));
  return(outdata)
}

register ELR_hyp : bits(32)

register ELR_EL3 : bits(64)

register ELR_EL2 : bits(64)

register ELR_EL1 : bits(64)

let EL3 : vector(2, dec, bit) = 0b11

let EL2 : vector(2, dec, bit) = 0b10

let EL1 : vector(2, dec, bit) = 0b01

let EL0 : vector(2, dec, bit) = 0b00

register EDSCR : bits(32)

val __UNKNOWN_DeviceType : unit -> DeviceType

function __UNKNOWN_DeviceType () = return(DeviceType_GRE)

val DecodeShift : bits(2) -> ShiftType

function DecodeShift op = match op {
  0b00 => return(ShiftType_LSL),
  0b01 => return(ShiftType_LSR),
  0b10 => return(ShiftType_ASR),
  0b11 => return(ShiftType_ROR)
}

val DecodeRegExtend : bits(3) -> ExtendType

function DecodeRegExtend op = match op {
  0b000 => return(ExtendType_UXTB),
  0b001 => return(ExtendType_UXTH),
  0b010 => return(ExtendType_UXTW),
  0b011 => return(ExtendType_UXTX),
  0b100 => return(ExtendType_SXTB),
  0b101 => return(ExtendType_SXTH),
  0b110 => return(ExtendType_SXTW),
  0b111 => return(ExtendType_SXTX)
}

let DebugHalt_Watchpoint : vector(6, dec, bit) = 0b101011

let DebugHalt_HaltInstruction : vector(6, dec, bit) = 0b101111

let DebugHalt_Breakpoint : vector(6, dec, bit) = 0b000111

let DebugException_VectorCatch : vector(4, dec, bit) = 0x5

val DataSynchronizationBarrier : (MBReqDomain, MBReqTypes) -> unit

function DataSynchronizationBarrier (domain, types) = ()

val DataMemoryBarrier : (MBReqDomain, MBReqTypes) -> unit

function DataMemoryBarrier (domain, types) = ()

val aarch64_system_barriers : (MBReqDomain, MemBarrierOp, MBReqTypes) -> unit

function aarch64_system_barriers (domain, op, types) = match op {
  MemBarrierOp_DSB => DataSynchronizationBarrier(domain, types),
  MemBarrierOp_DMB => DataMemoryBarrier(domain, types),
  MemBarrierOp_ISB => InstructionSynchronizationBarrier()
}

register DSPSR_EL0 : bits(32)

register DSPSR : bits(32)

register DLR_EL0 : bits(64)

register DLR : bits(32)

register DBGWVR_EL1 : vector(16, dec, bits(64))

register DBGWCR_EL1 : vector(16, dec, bits(32))

register DBGPRCR_EL1 : bits(32)

register DBGPRCR : bits(32)

register DBGOSLSR : bits(32)

register DBGOSDLR : bits(32)

register DBGEN : signal

register DBGBVR_EL1 : vector(16, dec, bits(64))

register DBGBCR_EL1 : vector(16, dec, bits(32))

val __UNKNOWN_Constraint : unit -> Constraint

function __UNKNOWN_Constraint () = return(Constraint_NONE)

val ConstrainUnpredictable : Unpredictable -> Constraint

function ConstrainUnpredictable which = match which {
  Unpredictable_WBOVERLAPLD => return(Constraint_WBSUPPRESS),
  Unpredictable_WBOVERLAPST => return(Constraint_NONE),
  Unpredictable_LDPOVERLAP => return(Constraint_UNDEF),
  Unpredictable_BASEOVERLAP => return(Constraint_NONE),
  Unpredictable_DATAOVERLAP => return(Constraint_NONE),
  Unpredictable_DEVPAGE2 => return(Constraint_FAULT),
  Unpredictable_INSTRDEVICE => return(Constraint_NONE),
  Unpredictable_RESCPACR => return(Constraint_UNKNOWN),
  Unpredictable_RESMAIR => return(Constraint_UNKNOWN),
  Unpredictable_RESTEXCB => return(Constraint_UNKNOWN),
  Unpredictable_RESDACR => return(Constraint_UNKNOWN),
  Unpredictable_RESPRRR => return(Constraint_UNKNOWN),
  Unpredictable_RESVTCRS => return(Constraint_UNKNOWN),
  Unpredictable_RESTnSZ => return(Constraint_FORCE),
  Unpredictable_OORTnSZ => return(Constraint_FORCE),
  Unpredictable_LARGEIPA => return(Constraint_FORCE),
  Unpredictable_ESRCONDPASS => return(Constraint_FALSE),
  Unpredictable_ILZEROIT => return(Constraint_FALSE),
  Unpredictable_ILZEROT => return(Constraint_FALSE),
  Unpredictable_BPVECTORCATCHPRI => return(Constraint_TRUE),
  Unpredictable_VCMATCHHALF => return(Constraint_FALSE),
  Unpredictable_VCMATCHDAPA => return(Constraint_FALSE),
  Unpredictable_WPMASKANDBAS => return(Constraint_FALSE),
  Unpredictable_WPBASCONTIGUOUS => return(Constraint_FALSE),
  Unpredictable_RESWPMASK => return(Constraint_DISABLED),
  Unpredictable_WPMASKEDBITS => return(Constraint_FALSE),
  Unpredictable_RESBPWPCTRL => return(Constraint_DISABLED),
  Unpredictable_BPNOTIMPL => return(Constraint_DISABLED),
  Unpredictable_RESBPTYPE => return(Constraint_DISABLED),
  Unpredictable_BPNOTCTXCMP => return(Constraint_DISABLED),
  Unpredictable_BPMATCHHALF => return(Constraint_FALSE),
  Unpredictable_BPMISMATCHHALF => return(Constraint_FALSE),
  Unpredictable_RESTARTALIGNPC => return(Constraint_FALSE),
  Unpredictable_RESTARTZEROUPPERPC => return(Constraint_TRUE),
  Unpredictable_ZEROUPPER => return(Constraint_TRUE),
  Unpredictable_ERETZEROUPPERPC => return(Constraint_TRUE),
  Unpredictable_A32FORCEALIGNPC => return(Constraint_FALSE),
  Unpredictable_SMD => return(Constraint_UNDEF),
  Unpredictable_AFUPDATE => return(Constraint_TRUE),
  Unpredictable_IESBinDebug => return(Constraint_TRUE),
  Unpredictable_CLEARERRITEZERO => return(Constraint_FALSE)
}

val ClearPendingPhysicalSError : unit -> unit effect {wreg}

function ClearPendingPhysicalSError () = {
  __PendingPhysicalSError = false;
  ()
}

val ClearExclusiveLocal : int -> unit effect {wreg}

function ClearExclusiveLocal 'processorid = {
  __ExclusiveLocal = false;
  ()
}

val aarch64_system_monitors : unit -> unit effect {wreg}

function aarch64_system_monitors () = ClearExclusiveLocal(ProcessorID())

val system_monitors_decode : (bits(1), bits(2), bits(3), bits(4), bits(4), bits(3), bits(5)) -> unit effect {wreg}

function system_monitors_decode (L, op0, op1, CRn, CRm, op2, Rt) = {
  __unconditional = true;
  aarch64_system_monitors()
}

val ClearExclusiveByAddress : (FullAddress, int, int) -> unit

function ClearExclusiveByAddress (paddress, 'processorid, 'size) = ()

val ClearEventRegister : unit -> unit effect {wreg}

function ClearEventRegister () = {
  EventRegister = 0b0;
  ()
}

val CTI_SignalEvent : CrossTriggerIn -> unit effect {escape}

function CTI_SignalEvent id = assert(false, "FALSE")

register CPTR_EL3 : bits(32)

register CPTR_EL2 : bits(32)

register CPACR_EL1 : bits(32)

register CONTEXTIDR_EL2 : bits(32)

register CONTEXTIDR_EL1 : bits(32)

val __UNKNOWN_BranchType : unit -> BranchType

function __UNKNOWN_BranchType () = return(BranchType_CALL)

val __UNKNOWN_AccType : unit -> AccType

function __UNKNOWN_AccType () = return(AccType_NORMAL)

val CreateAccessDescriptorPTW : (AccType, bool, bool, int) -> AccessDescriptor effect {undef}

function CreateAccessDescriptorPTW (acctype, secondstage, s2fs1walk, 'level) = {
  accdesc : AccessDescriptor = undefined;
  accdesc.acctype = acctype;
  accdesc.page_table_walk = true;
  accdesc.secondstage = s2fs1walk;
  accdesc.secondstage = secondstage;
  accdesc.level = level;
  return(accdesc)
}

val CreateAccessDescriptor : AccType -> AccessDescriptor effect {undef}

function CreateAccessDescriptor acctype = {
  accdesc : AccessDescriptor = undefined;
  accdesc.acctype = acctype;
  accdesc.page_table_walk = false;
  return(accdesc)
}

register APIBKeyLo_EL1 : bits(64)

register APIBKeyHi_EL1 : bits(64)

register APIAKeyLo_EL1 : bits(64)

register APIAKeyHi_EL1 : bits(64)

register APGAKeyLo_EL1 : bits(64)

register APGAKeyHi_EL1 : bits(64)

register APDBKeyLo_EL1 : bits(64)

register APDBKeyHi_EL1 : bits(64)

register APDAKeyLo_EL1 : bits(64)

register APDAKeyHi_EL1 : bits(64)

val aarch64_system_register_cpsr : (PSTATEField, bits(4)) -> unit effect {rreg, wreg}

function aarch64_system_register_cpsr (field, operand) = match field {
  PSTATEField_SP => PSTATE.SP = [operand[0]],
  PSTATEField_DAIFSet => {
    PSTATE.D = PSTATE.D | [operand[3]];
    PSTATE.A = PSTATE.A | [operand[2]];
    PSTATE.I = PSTATE.I | [operand[1]];
    PSTATE.F = PSTATE.F | [operand[0]]
  },
  PSTATEField_DAIFClr => {
    PSTATE.D = PSTATE.D & ~([operand[3]]);
    PSTATE.A = PSTATE.A & ~([operand[2]]);
    PSTATE.I = PSTATE.I & ~([operand[1]]);
    PSTATE.F = PSTATE.F & ~([operand[0]])
  },
  PSTATEField_PAN => PSTATE.PAN = [operand[0]],
  PSTATEField_UAO => PSTATE.UAO = [operand[0]]
}

val AArch64_SysRegWrite : (int, int, int, int, int, bits(64)) -> unit effect {escape}

function AArch64_SysRegWrite ('op0, 'op1, 'crn, 'crm, 'op2, val_name) = assert(false, "FALSE")

val AArch64_SysRegRead : (int, int, int, int, int) -> bits(64) effect {escape, undef}

function AArch64_SysRegRead _ = {
  assert(false, "Tried to read system register");
  undefined
}

val AArch64_SysInstr : (int, int, int, int, int, bits(64)) -> unit effect {escape}

function AArch64_SysInstr ('op0, 'op1, 'crn, 'crm, 'op2, val_name) = assert(false, "FALSE")

val AArch64_ResetControlRegisters : bool -> unit

function AArch64_ResetControlRegisters cold_reset = ()

val AArch64_ReportDeferredSError : bits(25) -> bits(64) effect {undef}

function AArch64_ReportDeferredSError syndrome = {
  target : bits(64) = undefined;
  target : bits(64) = __SetSlice_bits(64, 1, target, 31, 0b1);
  target = __SetSlice_bits(64, 1, target, 24, [syndrome[24]]);
  target = __SetSlice_bits(64, 24, target, 0, slice(syndrome, 0, 24));
  return(target)
}

val AArch64_MarkExclusiveVA : (bits(64), int, int) -> unit effect {escape}

function AArch64_MarkExclusiveVA (address, 'processorid, 'size) = assert(false, "FALSE")

val AArch64_IsExclusiveVA : (bits(64), int, int) -> bool effect {escape}

function AArch64_IsExclusiveVA (address, 'processorid, 'size) = {
  assert(false, "FALSE");
  return(false)
}

val AArch64_CreateFaultRecord : (Fault, bits(52), int, AccType, bool, bits(1), bits(2), bool, bool) -> FaultRecord effect {undef}

function AArch64_CreateFaultRecord (typ, ipaddress, 'level, acctype, write, extflag, errortype, secondstage, s2fs1walk) = {
  fault : FaultRecord = undefined;
  fault.typ = typ;
  fault.domain = undefined;
  fault.debugmoe = undefined;
  fault.errortype = errortype;
  fault.ipaddress = ipaddress;
  fault.level = level;
  fault.acctype = acctype;
  fault.write = write;
  fault.extflag = extflag;
  fault.secondstage = secondstage;
  fault.s2fs1walk = s2fs1walk;
  return(fault)
}

val AArch64_TranslationFault : (bits(52), int, AccType, bool, bool, bool) -> FaultRecord effect {undef}

function AArch64_TranslationFault (ipaddress, 'level, acctype, iswrite, secondstage, s2fs1walk) = {
  extflag : bits(1) = undefined;
  errortype : bits(2) = undefined;
  return(AArch64_CreateFaultRecord(Fault_Translation, ipaddress, level, acctype, iswrite, extflag, errortype, secondstage, s2fs1walk))
}

val AArch64_PermissionFault : (bits(52), int, AccType, bool, bool, bool) -> FaultRecord effect {undef}

function AArch64_PermissionFault (ipaddress, 'level, acctype, iswrite, secondstage, s2fs1walk) = {
  extflag : bits(1) = undefined;
  errortype : bits(2) = undefined;
  return(AArch64_CreateFaultRecord(Fault_Permission, ipaddress, level, acctype, iswrite, extflag, errortype, secondstage, s2fs1walk))
}

val AArch64_NoFault : unit -> FaultRecord effect {undef}

function AArch64_NoFault () = {
  ipaddress : bits(52) = undefined;
  level : int = undefined;
  acctype : AccType = AccType_NORMAL;
  iswrite : bool = undefined;
  extflag : bits(1) = undefined;
  errortype : bits(2) = undefined;
  secondstage : bool = false;
  s2fs1walk : bool = false;
  return(AArch64_CreateFaultRecord(Fault_None, ipaddress, level, acctype, iswrite, extflag, errortype, secondstage, s2fs1walk))
}

val AArch64_DebugFault : (AccType, bool) -> FaultRecord effect {undef}

function AArch64_DebugFault (acctype, iswrite) = {
  ipaddress : bits(52) = undefined;
  errortype : bits(2) = undefined;
  level : int = undefined;
  extflag : bits(1) = undefined;
  secondstage : bool = false;
  s2fs1walk : bool = false;
  return(AArch64_CreateFaultRecord(Fault_Debug, ipaddress, level, acctype, iswrite, extflag, errortype, secondstage, s2fs1walk))
}

val AArch64_CheckUnallocatedSystemAccess : (bits(2), bits(3), bits(4), bits(4), bits(3), bits(1)) -> bool effect {escape}

function AArch64_CheckUnallocatedSystemAccess (op0, op1, crn, crm, op2, read) = {
  assert(false, "FALSE");
  return(false)
}

val AArch64_CheckSystemRegisterTraps : (bits(2), bits(3), bits(4), bits(4), bits(3), bits(1)) -> (bool, bits(2)) effect {escape}

function AArch64_CheckSystemRegisterTraps (op0, op1, crn, crm, op2, read) = {
  assert(false, "FALSE");
  return((false, 0b00))
}

val AArch64_CheckAdvSIMDFPSystemRegisterTraps : (bits(2), bits(3), bits(4), bits(4), bits(3), bits(1)) -> (bool, bits(2)) effect {escape}

function AArch64_CheckAdvSIMDFPSystemRegisterTraps (op0, op1, crn, crm, op2, read) = {
  assert(false, "FALSE");
  return((false, 0b00))
}

val AArch64_AlignmentFault : (AccType, bool, bool) -> FaultRecord effect {undef}

function AArch64_AlignmentFault (acctype, iswrite, secondstage) = {
  ipaddress : bits(52) = undefined;
  level : int = undefined;
  extflag : bits(1) = undefined;
  errortype : bits(2) = undefined;
  s2fs1walk : bool = undefined;
  return(AArch64_CreateFaultRecord(Fault_Alignment, ipaddress, level, acctype, iswrite, extflag, errortype, secondstage, s2fs1walk))
}

val AArch64_AddressSizeFault : (bits(52), int, AccType, bool, bool, bool) -> FaultRecord effect {undef}

function AArch64_AddressSizeFault (ipaddress, 'level, acctype, iswrite, secondstage, s2fs1walk) = {
  extflag : bits(1) = undefined;
  errortype : bits(2) = undefined;
  return(AArch64_CreateFaultRecord(Fault_AddressSize, ipaddress, level, acctype, iswrite, extflag, errortype, secondstage, s2fs1walk))
}

val AArch64_AccessFlagFault : (bits(52), int, AccType, bool, bool, bool) -> FaultRecord effect {undef}

function AArch64_AccessFlagFault (ipaddress, 'level, acctype, iswrite, secondstage, s2fs1walk) = {
  extflag : bits(1) = undefined;
  errortype : bits(2) = undefined;
  return(AArch64_CreateFaultRecord(Fault_AccessFlag, ipaddress, level, acctype, iswrite, extflag, errortype, secondstage, s2fs1walk))
}

val AArch32_CurrentCond : unit -> bits(4) effect {rreg}

function AArch32_CurrentCond () = return(__currentCond)

val aget_SP : forall ('width : Int), 'width >= 0.
  unit -> bits('width) effect {escape, rreg}

function aget_SP () = {
  assert('width == 8 | 'width == 16 | 'width == 32 | 'width == 64, "((width == 8) || ((width == 16) || ((width == 32) || (width == 64))))");
  if PSTATE.SP == 0b0 then return(slice(SP_EL0, 0, 'width)) else match PSTATE.EL {
    ? if ? == EL0 => return(slice(SP_EL0, 0, 'width)),
    ? if ? == EL1 => return(slice(SP_EL1, 0, 'width)),
    ? if ? == EL2 => return(slice(SP_EL2, 0, 'width)),
    ? if ? == EL3 => return(slice(SP_EL3, 0, 'width))
  }
}

val __IMPDEF_integer : string -> int

function __IMPDEF_integer x = {
  if x == "Maximum Physical Address Size" then return(52) else if x == "Maximum Virtual Address Size" then return(56) else ();
  return(0)
}

val VAMax : unit -> int

function VAMax () = return(__IMPDEF_integer("Maximum Virtual Address Size"))

val PAMax : unit -> int

function PAMax () = return(__IMPDEF_integer("Maximum Physical Address Size"))

val __IMPDEF_boolean : string -> bool

function __IMPDEF_boolean x = {
  if x == "Condition valid for trapped T32" then return(true) else if x == "Has Dot Product extension" then return(true) else if x == "Has RAS extension" then return(true) else if x == "Has SHA512 and SHA3 Crypto instructions" then return(true) else if x == "Has SM3 and SM4 Crypto instructions" then return(true) else if x == "Has basic Crypto instructions" then return(true) else if x == "Have CRC extension" then return(true) else if x == "Report I-cache maintenance fault in IFSR" then return(true) else if x == "Reserved Control Space EL0 Trapped" then return(true) else if x == "Translation fault on misprogrammed contiguous bit" then return(true) else if x == "UNDEF unallocated CP15 access at NS EL0" then return(true) else if x == "UNDEF unallocated CP15 access at NS EL0" then return(true) else ();
  return(false)
}

val WaitForEvent : unit -> unit effect {rreg, wreg}

function WaitForEvent () = {
  if EventRegister == 0b0 then EnterLowPowerState() else ();
  ()
}

val ThisInstrLength : unit -> int effect {rreg}

function ThisInstrLength () = return(if __ThisInstrEnc == __T16 then 16 else 32)

val RoundTowardsZero : real -> int

function RoundTowardsZero x = return(if x == 0.0 then 0 else if x >= 0.0 then RoundDown(x) else RoundUp(x))

val Restarting : unit -> bool effect {rreg}

function Restarting () = return(slice(EDSCR, 0, 6) == 0b000001)

val PtrHasUpperAndLowerAddRanges : unit -> bool effect {rreg}

function PtrHasUpperAndLowerAddRanges () = return((PSTATE.EL == EL1 | PSTATE.EL == EL0) | PSTATE.EL == EL2 & [HCR_EL2[34]] == 0b1)

val MemAttrDefaults : MemoryAttributes -> MemoryAttributes effect {undef}

function MemAttrDefaults memattrs__arg = {
  memattrs = memattrs__arg;
  if memattrs.typ == MemType_Device then {
    memattrs.inner = undefined;
    memattrs.outer = undefined;
    memattrs.shareable = true;
    memattrs.outershareable = true
  } else {
    memattrs.device = undefined;
    if memattrs.inner.attrs == MemAttr_NC & memattrs.outer.attrs == MemAttr_NC then {
      memattrs.shareable = true;
      memattrs.outershareable = true
    } else ()
  };
  return(memattrs)
}

val IsEventRegisterSet : unit -> bool effect {rreg}

function IsEventRegisterSet () = return(EventRegister == 0b1)

val HaveEL : bits(2) -> bool

function HaveEL el = {
  if el == EL1 | el == EL0 then return(true) else ();
  return(true)
}

val HighestEL : unit -> bits(2)

function HighestEL () = if HaveEL(EL3) then return(EL3) else if HaveEL(EL2) then return(EL2) else return(EL1)

val Have16bitVMID : unit -> bool

function Have16bitVMID () = return(HaveEL(EL2))

val HasArchVersion : ArchVersion -> bool

function HasArchVersion version = return(version == ARMv8p0 | version == ARMv8p1 | version == ARMv8p2 | version == ARMv8p3)

val HaveVirtHostExt : unit -> bool

function HaveVirtHostExt () = return(HasArchVersion(ARMv8p1))

val HaveUAOExt : unit -> bool

function HaveUAOExt () = return(HasArchVersion(ARMv8p2))

val HaveTrapLoadStoreMultipleDeviceExt : unit -> bool

function HaveTrapLoadStoreMultipleDeviceExt () = return(HasArchVersion(ARMv8p2))

val HaveStatisticalProfiling : unit -> bool

function HaveStatisticalProfiling () = return(HasArchVersion(ARMv8p2))

val HaveRASExt : unit -> bool

function HaveRASExt () = return(HasArchVersion(ARMv8p2) | __IMPDEF_boolean("Has RAS extension"))

val HavePrivATExt : unit -> bool

function HavePrivATExt () = return(HasArchVersion(ARMv8p2))

val HavePANExt : unit -> bool

function HavePANExt () = return(HasArchVersion(ARMv8p1))

val HavePACExt : unit -> bool

function HavePACExt () = return(HasArchVersion(ARMv8p3))

val HaveNVExt : unit -> bool

function HaveNVExt () = return(HasArchVersion(ARMv8p3))

val HaveFJCVTZSExt : unit -> bool

function HaveFJCVTZSExt () = return(HasArchVersion(ARMv8p3))

val HaveExtendedExecuteNeverExt : unit -> bool

function HaveExtendedExecuteNeverExt () = return(HasArchVersion(ARMv8p2))

val HaveDirtyBitModifierExt : unit -> bool

function HaveDirtyBitModifierExt () = return(HasArchVersion(ARMv8p1))

val HaveCommonNotPrivateTransExt : unit -> bool

function HaveCommonNotPrivateTransExt () = return(HasArchVersion(ARMv8p2))

val HaveCRCExt : unit -> bool

function HaveCRCExt () = return(HasArchVersion(ARMv8p1) | __IMPDEF_boolean("Have CRC extension"))

val HaveAtomicExt : unit -> bool

function HaveAtomicExt () = return(HasArchVersion(ARMv8p1))

val HaveAccessFlagUpdateExt : unit -> bool

function HaveAccessFlagUpdateExt () = return(HasArchVersion(ARMv8p1))

val Have52BitVAExt : unit -> bool

function Have52BitVAExt () = return(HasArchVersion(ARMv8p2))

val Have52BitPAExt : unit -> bool

function Have52BitPAExt () = return(HasArchVersion(ARMv8p2))

val AArch64_HaveHPDExt : unit -> bool

function AArch64_HaveHPDExt () = return(HasArchVersion(ARMv8p1))

val ExternalInvasiveDebugEnabled : unit -> bool effect {rreg}

function ExternalInvasiveDebugEnabled () = return(DBGEN == HIGH)

val ConstrainUnpredictableInteger : (int, int, Unpredictable) -> (Constraint, int) effect {undef}

function ConstrainUnpredictableInteger ('low, 'high, which) = {
  c : Constraint = ConstrainUnpredictable(which);
  if c == Constraint_UNKNOWN then return((c, low)) else return((c, undefined))
}

val ConstrainUnpredictableBool : Unpredictable -> bool effect {escape}

function ConstrainUnpredictableBool which = {
  c : Constraint = ConstrainUnpredictable(which);
  assert(c == Constraint_TRUE | c == Constraint_FALSE, "((c == Constraint_TRUE) || (c == Constraint_FALSE))");
  return(c == Constraint_TRUE)
}

val CombineS1S2Device : (DeviceType, DeviceType) -> DeviceType effect {undef}

function CombineS1S2Device (s1device, s2device) = {
  result : DeviceType = undefined;
  if s2device == DeviceType_nGnRnE | s1device == DeviceType_nGnRnE then result = DeviceType_nGnRnE else if s2device == DeviceType_nGnRE | s1device == DeviceType_nGnRE then result = DeviceType_nGnRE else if s2device == DeviceType_nGRE | s1device == DeviceType_nGRE then result = DeviceType_nGRE else result = DeviceType_GRE;
  return(result)
}

val CombineS1S2AttrHints : (MemAttrHints, MemAttrHints) -> MemAttrHints effect {undef}

function CombineS1S2AttrHints (s1desc, s2desc) = {
  result : MemAttrHints = undefined;
  if s2desc.attrs == 0b01 | s1desc.attrs == 0b01 then result.attrs = undefined else if s2desc.attrs == MemAttr_NC | s1desc.attrs == MemAttr_NC then result.attrs = MemAttr_NC else if s2desc.attrs == MemAttr_WT | s1desc.attrs == MemAttr_WT then result.attrs = MemAttr_WT else result.attrs = MemAttr_WB;
  result.hints = s1desc.hints;
  result.transient = s1desc.transient;
  return(result)
}

val AArch64_InstructionDevice : (AddressDescriptor, bits(64), bits(52), int, AccType, bool, bool, bool) -> AddressDescriptor effect {escape, undef}

function AArch64_InstructionDevice (addrdesc__arg, vaddress, ipaddress, 'level, acctype, iswrite, secondstage, s2fs1walk) = {
  addrdesc = addrdesc__arg;
  c : Constraint = ConstrainUnpredictable(Unpredictable_INSTRDEVICE);
  assert(c == Constraint_NONE | c == Constraint_FAULT, "((c == Constraint_NONE) || (c == Constraint_FAULT))");
  if c == Constraint_FAULT then addrdesc.fault = AArch64_PermissionFault(ipaddress, level, acctype, iswrite, secondstage, s2fs1walk) else {
    __tmp_12 : MemoryAttributes = addrdesc.memattrs;
    __tmp_12.typ = MemType_Normal;
    addrdesc.memattrs = __tmp_12;
    __tmp_13 : MemAttrHints = addrdesc.memattrs.inner;
    __tmp_13.attrs = MemAttr_NC;
    __tmp_14 : MemoryAttributes = addrdesc.memattrs;
    __tmp_14.inner = __tmp_13;
    addrdesc.memattrs = __tmp_14;
    __tmp_15 : MemAttrHints = addrdesc.memattrs.inner;
    __tmp_15.hints = MemHint_No;
    __tmp_16 : MemoryAttributes = addrdesc.memattrs;
    __tmp_16.inner = __tmp_15;
    addrdesc.memattrs = __tmp_16;
    __tmp_17 : MemoryAttributes = addrdesc.memattrs;
    __tmp_17.outer = addrdesc.memattrs.inner;
    addrdesc.memattrs = __tmp_17;
    addrdesc.memattrs = MemAttrDefaults(addrdesc.memattrs)
  };
  return(addrdesc)
}

val aget_Vpart : forall ('width : Int), 'width >= 0.
  (int, int) -> bits('width) effect {escape, rreg}

function aget_Vpart ('n, 'part) = {
  assert(n >= 0 & n <= 31, "((n >= 0) && (n <= 31))");
  assert(part == 0 | part == 1, "((part == 0) || (part == 1))");
  if part == 0 then {
    assert('width == 8 | 'width == 16 | 'width == 32 | 'width == 64, "((width == 8) || ((width == 16) || ((width == 32) || (width == 64))))");
    return(slice(_V[n], 0, 'width))
  } else {
    assert('width == 64, "(width == 64)");
    return(slice(_V[n], 'width, 'width))
  }
}

val aget_V : forall ('width : Int), 'width >= 0.
  int -> bits('width) effect {escape, rreg}

function aget_V 'n = {
  assert(n >= 0 & n <= 31, "((n >= 0) && (n <= 31))");
  assert('width == 8 | 'width == 16 | 'width == 32 | 'width == 64 | 'width == 128, "((width == 8) || ((width == 16) || ((width == 32) || ((width == 64) || (width == 128)))))");
  return(slice(_V[n], 0, 'width))
}

val LookUpRIndex : (int, bits(5)) -> int effect {escape, undef}

function LookUpRIndex ('n, mode) = {
  assert(n >= 0 & n <= 14, "((n >= 0) && (n <= 14))");
  result : int = undefined;
  match n {
    8 => result = RBankSelect(mode, 8, 24, 8, 8, 8, 8, 8),
    9 => result = RBankSelect(mode, 9, 25, 9, 9, 9, 9, 9),
    10 => result = RBankSelect(mode, 10, 26, 10, 10, 10, 10, 10),
    11 => result = RBankSelect(mode, 11, 27, 11, 11, 11, 11, 11),
    12 => result = RBankSelect(mode, 12, 28, 12, 12, 12, 12, 12),
    13 => result = RBankSelect(mode, 13, 29, 17, 19, 21, 23, 15),
    14 => result = RBankSelect(mode, 14, 30, 16, 18, 20, 22, 14),
    _ => result = n
  };
  return(result)
}

val HighestSetBit : forall ('N : Int), 'N >= 0. bits('N) -> int

function HighestSetBit x = {
  foreach (i from ('N - 1) to 0 by 1 in dec)
    if [x[i]] == 0b1 then return(i) else ();
  return(negate(1))
}

val CountLeadingZeroBits : forall ('N : Int), 'N >= 2. bits('N) -> int

function CountLeadingZeroBits x = return(('N - 1) - HighestSetBit(x))

val CountLeadingSignBits : forall ('N : Int), 'N >= 3. bits('N) -> int

function CountLeadingSignBits x = return(CountLeadingZeroBits((x >> 1) ^ (x & slice_mask(0,'N))))

val BitReverse : forall ('N : Int), 'N >= 0 & 'N >= 0.
  bits('N) -> bits('N) effect {undef}

function BitReverse data = {
  result : bits('N) = undefined;
  foreach (i from 0 to ('N - 1) by 1 in inc)
    result = __SetSlice_bits('N, 1, result, ('N - i) - 1, [data[i]]);
  return(result)
}

val NextInstrAddr : forall ('N : Int), 'N >= 0. unit -> bits('N) effect {rreg}

function NextInstrAddr () = return(slice(_PC + ThisInstrLength() / 8, 0, 'N))

val AArch32_ExceptionClass : Exception -> (int, bits(1)) effect {escape, rreg, undef}

function AArch32_ExceptionClass typ = {
  il : bits(1) = if ThisInstrLength() == 32 then 0b1 else 0b0;
  ec : int = undefined;
  match typ {
    Exception_Uncategorized => {
      ec = 0;
      il = 0b1
    },
    Exception_WFxTrap => ec = 1,
    Exception_CP15RTTrap => ec = 3,
    Exception_CP15RRTTrap => ec = 4,
    Exception_CP14RTTrap => ec = 5,
    Exception_CP14DTTrap => ec = 6,
    Exception_AdvSIMDFPAccessTrap => ec = 7,
    Exception_FPIDTrap => ec = 8,
    Exception_CP14RRTTrap => ec = 12,
    Exception_IllegalState => {
      ec = 14;
      il = 0b1
    },
    Exception_SupervisorCall => ec = 17,
    Exception_HypervisorCall => ec = 18,
    Exception_MonitorCall => ec = 19,
    Exception_InstructionAbort => {
      ec = 32;
      il = 0b1
    },
    Exception_PCAlignment => {
      ec = 34;
      il = 0b1
    },
    Exception_DataAbort => ec = 36,
    Exception_FPTrappedException => ec = 40,
    _ => Unreachable()
  };
  if (ec == 32 | ec == 36) & PSTATE.EL == EL2 then ec = ec + 1 else ();
  return((ec, il))
}

val RotCell : (bits(4), int) -> bits(4) effect {undef}

function RotCell (incell_name, 'amount) = {
  tmp : bits(8) = undefined;
  outcell : bits(4) = undefined;
  tmp = __SetSlice_bits(8, 8, tmp, 0, slice(incell_name, 0, 4) @ slice(incell_name, 0, 4));
  outcell = slice(tmp, 4 - amount, 4);
  return(outcell)
}

val FPNeg : forall ('N : Int), 'N >= 0 & 'N >= 0.
  bits('N) -> bits('N) effect {escape}

function FPNeg op = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  return(~([op['N - 1]]) @ slice(op, 0, 'N - 1))
}

val FPAbs : forall ('N : Int), 'N >= 0 & 'N >= 0.
  bits('N) -> bits('N) effect {escape}

function FPAbs op = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  return(0b0 @ slice(op, 0, 'N - 1))
}

val EncodeLDFSC : (Fault, int) -> bits(6) effect {escape, undef}

function EncodeLDFSC (typ, 'level) = {
  result : bits(6) = undefined;
  match typ {
    Fault_AddressSize => {
      result = 0x0 @ __GetSlice_int(2, level, 0);
      assert(level == 0 | level == 1 | level == 2 | level == 3, "((level == 0) || ((level == 1) || ((level == 2) || (level == 3))))")
    },
    Fault_AccessFlag => {
      result = 0x2 @ __GetSlice_int(2, level, 0);
      assert(level == 1 | level == 2 | level == 3, "((level == 1) || ((level == 2) || (level == 3)))")
    },
    Fault_Permission => {
      result = 0x3 @ __GetSlice_int(2, level, 0);
      assert(level == 1 | level == 2 | level == 3, "((level == 1) || ((level == 2) || (level == 3)))")
    },
    Fault_Translation => {
      result = 0x1 @ __GetSlice_int(2, level, 0);
      assert(level == 0 | level == 1 | level == 2 | level == 3, "((level == 0) || ((level == 1) || ((level == 2) || (level == 3))))")
    },
    Fault_SyncExternal => result = 0b010000,
    Fault_SyncExternalOnWalk => {
      result = 0x5 @ __GetSlice_int(2, level, 0);
      assert(level == 0 | level == 1 | level == 2 | level == 3, "((level == 0) || ((level == 1) || ((level == 2) || (level == 3))))")
    },
    Fault_SyncParity => result = 0b011000,
    Fault_SyncParityOnWalk => {
      result = 0x7 @ __GetSlice_int(2, level, 0);
      assert(level == 0 | level == 1 | level == 2 | level == 3, "((level == 0) || ((level == 1) || ((level == 2) || (level == 3))))")
    },
    Fault_AsyncParity => result = 0b011001,
    Fault_AsyncExternal => result = 0b010001,
    Fault_Alignment => result = 0b100001,
    Fault_Debug => result = 0b100010,
    Fault_TLBConflict => result = 0b110000,
    Fault_Lockdown => result = 0b110100,
    Fault_Exclusive => result = 0b110101,
    _ => Unreachable()
  };
  return(result)
}

val BigEndianReverse = {lem: "BigEndianReverse"} : forall ('width : Int), 'width >= 0 & 'width >= 0.
  bits('width) -> bits('width) effect {escape}

function BigEndianReverse value_name = {
  assert('width == 8 | 'width == 16 | 'width == 32 | 'width == 64 | 'width == 128);
  result : bits('width) = replicate_bits(0b0,'width);
  foreach (i from 0 to ('width - 1) by 8)
    result[i+7 .. i] = (value_name['width-i - 1 .. 'width-i - 8] : bits(8));
  return result
}

val AArch32_ReportHypEntry : ExceptionRecord -> unit effect {escape, rreg, undef, wreg}

function AArch32_ReportHypEntry exception = {
  typ : Exception = exception.typ;
  il : bits(1) = undefined;
  ec : int = undefined;
  (ec, il) = AArch32_ExceptionClass(typ);
  iss : bits(25) = exception.syndrome;
  if (ec == 36 | ec == 37) & [iss[24]] == 0b0 then il = 0b1 else ();
  HSR = (__GetSlice_int(6, ec, 0) @ il) @ iss;
  if typ == Exception_InstructionAbort | typ == Exception_PCAlignment then {
    HIFAR = slice(exception.vaddress, 0, 32);
    HDFAR = undefined
  } else if typ == Exception_DataAbort then {
    HIFAR = undefined;
    HDFAR = slice(exception.vaddress, 0, 32)
  } else ();
  if exception.ipavalid then HPFAR = __SetSlice_bits(32, 28, HPFAR, 4, slice(exception.ipaddress, 12, 28)) else HPFAR = __SetSlice_bits(32, 28, HPFAR, 4, undefined);
  ()
}

val aset_Elem__0 : forall ('N : Int) ('size : Int), 'N >= 0 & 'size >= 0 & 'N >= 0.
  (bits('N), int, atom('size), bits('size)) -> bits('N) effect {escape}

val aset_Elem__1 : forall ('N : Int) ('size : Int), 'N >= 0 & 'size >= 0 & 'N >= 0.
  (bits('N), int, bits('size)) -> bits('N) effect {escape}

overload aset_Elem = {aset_Elem__0, aset_Elem__1}

function aset_Elem__0 (vector_name__arg, 'e, size, value_name) = {
  vector_name = vector_name__arg;
  assert(e >= 0 & (e + 1) * 'size <= 'N, "((e >= 0) && (((e + 1) * size) <= N))");
  vector_name = __SetSlice_bits('N, 'size, vector_name, e * 'size, value_name);
  return(vector_name)
}

function aset_Elem__1 (vector_name__arg, 'e, value_name) = {
  vector_name = vector_name__arg;
  vector_name = aset_Elem(vector_name, e, 'size, value_name);
  return(vector_name)
}

val aget_Elem__0 : forall ('N : Int) ('size : Int), 'N >= 0 & 'size >= 0.
  (bits('N), int, atom('size)) -> bits('size) effect {escape}

val aget_Elem__1 : forall ('N : Int) ('size : Int), 'N >= 0 & 'size >= 0.
  (bits('N), int) -> bits('size) effect {escape}

overload aget_Elem = {aget_Elem__0, aget_Elem__1}

function aget_Elem__0 (vector_name, 'e, size) = {
  assert(e >= 0 & (e + 1) * 'size <= 'N, "((e >= 0) && (((e + 1) * size) <= N))");
  return(slice(vector_name, e * 'size, 'size))
}

function aget_Elem__1 (vector_name, 'e) = return(aget_Elem(vector_name, e, 'size))

val UnsignedSatQ : forall ('N : Int), 'N >= 0.
  (int, atom('N)) -> (bits('N), bool) effect {undef}

function UnsignedSatQ ('i, N) = {
  saturated : bool = undefined;
  result : int = undefined;
  if i > 2 ^ 'N - 1 then {
    result = 2 ^ 'N - 1;
    saturated = true
  } else if i < 0 then {
    result = 0;
    saturated = true
  } else {
    result = i;
    saturated = false
  };
  return((__GetSlice_int('N, result, 0), saturated))
}

val SignedSatQ : forall ('N : Int), 'N >= 0.
  (int, atom('N)) -> (bits('N), bool) effect {undef}

function SignedSatQ ('i, N) = {
  saturated : bool = undefined;
  result : int = undefined;
  if i > 2 ^ ('N - 1) - 1 then {
    result = 2 ^ ('N - 1) - 1;
    saturated = true
  } else if i < negate(2 ^ ('N - 1)) then {
    result = negate(2 ^ ('N - 1));
    saturated = true
  } else {
    result = i;
    saturated = false
  };
  return((__GetSlice_int('N, result, 0), saturated))
}

val SatQ : forall ('N : Int), 'N >= 0.
  (int, atom('N), bool) -> (bits('N), bool) effect {undef}

function SatQ ('i, N, unsigned) = {
  sat : bool = undefined;
  result : bits('N) = undefined;
  (result, sat) = if unsigned then UnsignedSatQ(i, 'N) else SignedSatQ(i, 'N);
  return((result, sat))
}

val Replicate : forall ('M : Int) ('N : Int), 'M >= 0 & 'N >= 0.
  bits('M) -> bits('N) effect {escape}

function Replicate x = {
  assert('N % 'M == 0, "((N MOD M) == 0)");
  let 'O = 'N / 'M;
  assert(constraint('O * 'M = 'N));
  return(replicate_bits(x, 'N / 'M))
}

val Zeros__0 : forall ('N : Int), 'N >= 0. atom('N) -> bits('N)

val Zeros__1 : forall ('N : Int), 'N >= 0. unit -> bits('N)

overload Zeros = {Zeros__0, Zeros__1}

function Zeros__0 N = return(replicate_bits(0b0, 'N))

function Zeros__1 () = return(Zeros('N))

val __ResetMemoryState : unit -> unit effect {rreg, wreg}

function __ResetMemoryState () = {
  __InitRAM(52, 1, __Memory, Zeros(8));
  __ExclusiveLocal = false
}

val ZeroExtend__0 : forall ('M : Int) ('N : Int), 'M >= 0 & 'N >= 0.
  (bits('M), atom('N)) -> bits('N) effect {escape}

val ZeroExtend__1 : forall ('M : Int) ('N : Int), 'M >= 0 & 'N >= 0.
  bits('M) -> bits('N) effect {escape}

overload ZeroExtend = {ZeroExtend__0, ZeroExtend__1}

function ZeroExtend__0 (x, N) = {
  assert('N >= 'M);
  extzv(x)
}

function ZeroExtend__1 x = return(ZeroExtend(x, 'N))

val aset_Vpart : forall ('width : Int), 'width >= 0.
  (int, int, bits('width)) -> unit effect {escape, wreg, rreg}

function aset_Vpart (n, part, value_name) = {
  assert(n >= 0 & n <= 31, "((n >= 0) && (n <= 31))");
  assert(part == 0 | part == 1, "((part == 0) || (part == 1))");
  if part == 0 then {
    assert('width == 8 | 'width == 16 | 'width == 32 | 'width == 64, "((width == 8) || ((width == 16) || ((width == 32) || (width == 64))))");
    _V[n] = ZeroExtend(value_name) : bits(128)
  } else {
    assert('width == 64, "(width == 64)");
    __tmp_287 : bits(128) = _V[n];
    __tmp_287[127 .. 64] = value_name[63 .. 0];
    _V[n] = __tmp_287
  }
}

val aset_V : forall ('width : Int), 'width >= 0.
  (int, bits('width)) -> unit effect {escape, wreg}

function aset_V (n, value_name) = {
  assert(n >= 0 & n <= 31, "((n >= 0) && (n <= 31))");
  assert('width == 8 | 'width == 16 | 'width == 32 | 'width == 64 | 'width == 128, "((width == 8) || ((width == 16) || ((width == 32) || ((width == 64) || (width == 128)))))");
  _V[n] = ZeroExtend(value_name) : bits(128);
  ()
}

val AArch64_ResetSIMDFPRegisters : unit -> unit effect {escape, undef, wreg}

function AArch64_ResetSIMDFPRegisters () = {
  foreach (i from 0 to 31 by 1 in inc) aset_V(i, undefined : bits(64));
  ()
}

val aset_SP : forall ('width : Int), 'width >= 0.
  bits('width) -> unit effect {escape, rreg, wreg}

function aset_SP value_name = {
  assert('width == 32 | 'width == 64, "((width == 32) || (width == 64))");
  if PSTATE.SP == 0b0 then SP_EL0 = ZeroExtend(value_name) else match PSTATE.EL {
    ? if ? == EL0 => SP_EL0 = ZeroExtend(value_name),
    ? if ? == EL1 => SP_EL1 = ZeroExtend(value_name),
    ? if ? == EL2 => SP_EL2 = ZeroExtend(value_name),
    ? if ? == EL3 => SP_EL3 = ZeroExtend(value_name)
  };
  ()
}

val LSR_C : forall ('N : Int), 'N >= 0 & 'N >= 0 & 1 >= 0.
  (bits('N), int) -> (bits('N), bits(1)) effect {escape}

function LSR_C (x, 'shift) = {
  assert(shift > 0, "(shift > 0)");
  result : bits('N) = x >> shift;
  carry_out : bits(1) = if shift > 'N then 0b0 else [x[shift - 1]];
  return((result, carry_out))
}

val LSR : forall ('N : Int), 'N >= 0 & 'N >= 0.
  (bits('N), int) -> bits('N) effect {escape, undef}

function LSR (x, 'shift) = {
  assert(shift >= 0, "(shift >= 0)");
  __anon1 : bits(1) = undefined;
  result : bits('N) = undefined;
  if shift == 0 then result = x else (result, __anon1) = LSR_C(x, shift);
  return(result)
}

val Poly32Mod2 : forall ('N : Int), 'N >= 0 & 32 >= 0 & 32 >= 0.
  (bits('N), bits(32)) -> bits(32) effect {escape}

function Poly32Mod2 (data__arg, poly) = {
  data = data__arg;
  assert('N > 32, "(N > 32)");
  let poly' : bits('N) = extzv(poly) in
  foreach (i from ('N - 1) to 32 by 1 in dec)
    if [data[i]] == 0b1 then data = data | (poly' << i - 32) else ();
  return(slice(data, 0, 32))
}

val LSL_C : forall ('N : Int), 'N >= 0 & 'N >= 0 & 1 >= 0.
  (bits('N), int) -> (bits('N), bits(1)) effect {escape}

function LSL_C (x, 'shift) = {
  assert(shift > 0, "(shift > 0)");
  result : bits('N) = x << shift;
  carry_out : bits(1) = if shift > 'N then 0b0 else [x['N - shift]];
  return((result, carry_out))
}

val LSL : forall ('N : Int), 'N >= 0 & 'N >= 0.
  (bits('N), int) -> bits('N) effect {escape, undef}

function LSL (x, 'shift) = {
  assert(shift >= 0, "(shift >= 0)");
  __anon1 : bits(1) = undefined;
  result : bits('N) = undefined;
  if shift == 0 then result = x else (result, __anon1) = LSL_C(x, shift);
  return(result)
}

val AArch32_ITAdvance : unit -> unit effect {escape, rreg, undef, wreg}

function AArch32_ITAdvance () = {
  if slice(PSTATE.IT, 0, 3) == 0b000 then PSTATE.IT = 0x00 else {
    __tmp_276 : bits(8) = PSTATE.IT;
    __tmp_276 = __SetSlice_bits(8, 5, __tmp_276, 0, LSL(slice(PSTATE.IT, 0, 5), 1));
    PSTATE.IT = __tmp_276
  };
  ()
}

val LSInstructionSyndrome : unit -> bits(11) effect {escape}

function LSInstructionSyndrome () = {
  assert(false, "FALSE");
  return(Zeros(11))
}

val IsZero : forall ('N : Int), 'N >= 0. bits('N) -> bool

function IsZero x = return(x == Zeros('N))

val IsZeroBit : forall ('N : Int), 'N >= 0 & 1 >= 0. bits('N) -> bits(1)

function IsZeroBit x = return(if IsZero(x) then 0b1 else 0b0)

val AddWithCarry : forall ('N : Int), 'N >= 0 & 'N >= 0 & 1 >= 0 & 'N >= 0 & 4 >= 0.
  (bits('N), bits('N), bits(1)) -> (bits('N), bits(4))

function AddWithCarry (x, y, carry_in) = {
  unsigned_sum : int = (UInt(x) + UInt(y)) + UInt(carry_in);
  signed_sum : int = (SInt(x) + SInt(y)) + UInt(carry_in);
  result : bits('N) = __GetSlice_int('N, unsigned_sum, 0);
  n : bits(1) = [result['N - 1]];
  z : bits(1) = if IsZero(result) then 0b1 else 0b0;
  c : bits(1) = if UInt(result) == unsigned_sum then 0b0 else 0b1;
  v : bits(1) = if SInt(result) == signed_sum then 0b0 else 0b1;
  return((result, ((n @ z) @ c) @ v))
}

val GetPSRFromPSTATE : unit -> bits(32) effect {rreg, escape}

function GetPSRFromPSTATE () = {
  spsr : bits(32) = Zeros();
  spsr[31 .. 31] = PSTATE.N;
  spsr[30 .. 30] = PSTATE.Z;
  spsr[29 .. 29] = PSTATE.C;
  spsr[28 .. 28] = PSTATE.V;
  spsr[21 .. 21] = PSTATE.SS;
  spsr[20 .. 20] = PSTATE.IL;
  if PSTATE.nRW == 0b1 then {
    spsr[27 .. 27] = PSTATE.Q;
    spsr[26 .. 25] = PSTATE.IT[1 .. 0];
    spsr[19 .. 16] = PSTATE.GE;
    spsr[15 .. 10] = PSTATE.IT[7 .. 2];
    spsr[9 .. 9] = PSTATE.E;
    spsr[8 .. 8] = PSTATE.A;
    spsr[7 .. 7] = PSTATE.I;
    spsr[6 .. 6] = PSTATE.F;
    spsr[5 .. 5] = PSTATE.T;
    assert([PSTATE.M[4]] == PSTATE.nRW, "(((PSTATE).M)<4> == (PSTATE).nRW)");
    spsr[4 .. 0] = PSTATE.M
  } else {
    spsr[9 .. 9] = PSTATE.D;
    spsr[8 .. 8] = PSTATE.A;
    spsr[7 .. 7] = PSTATE.I;
    spsr[6 .. 6] = PSTATE.F;
    spsr[4 .. 4] = PSTATE.nRW;
    spsr[3 .. 2] = PSTATE.EL;
    spsr[0 .. 0] = PSTATE.SP
  };
  return(spsr)
}

val FPZero : forall ('N : Int), 1 >= 0 & 'N >= 0.
  bits(1) -> bits('N) effect {escape}

function FPZero sign = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  let 'E = (if 'N == 16 then 5 else if 'N == 32 then 8 else 11) : {|5, 8, 11|};
  F : atom('N - 'E - 1) = ('N - E) - 1;
  exp : bits('E) = Zeros(E);
  frac : bits('N - 1 - 'E) = Zeros(F);
  return(append(append(sign, exp), frac))
}

val ExceptionSyndrome : Exception -> ExceptionRecord effect {undef}

function ExceptionSyndrome typ = {
  r : ExceptionRecord = undefined;
  r.typ = typ;
  r.syndrome = Zeros();
  r.vaddress = Zeros();
  r.ipavalid = false;
  r.ipaddress = Zeros();
  return(r)
}

val ConstrainUnpredictableBits : forall ('width : Int), 'width >= 0.
  Unpredictable -> (Constraint, bits('width)) effect {undef}

function ConstrainUnpredictableBits which = {
  c : Constraint = ConstrainUnpredictable(which);
  if c == Constraint_UNKNOWN then return((c, Zeros('width))) else return((c, undefined))
}

val AArch64_SysInstrWithResult : (int, int, int, int, int) -> bits(64) effect {escape}

function AArch64_SysInstrWithResult ('op0, 'op1, 'crn, 'crm, 'op2) = {
  assert(false, "FALSE");
  return(Zeros(64))
}

val AArch64_PhysicalSErrorSyndrome : bool -> bits(25) effect {escape}

function AArch64_PhysicalSErrorSyndrome implicit_esb = {
  assert(false, "FALSE");
  return(Zeros(25))
}

val AArch32_PhysicalSErrorSyndrome : unit -> AArch32_SErrorSyndrome effect {escape, undef}

function AArch32_PhysicalSErrorSyndrome () = {
  assert(false, "FALSE");
  r : AArch32_SErrorSyndrome = undefined;
  r.AET = Zeros(2);
  r.ExT = Zeros(1);
  return(r)
}

val VFPExpandImm : forall ('N : Int), 8 >= 0 & 'N >= 0.
  bits(8) -> bits('N) effect {escape}

function VFPExpandImm imm8 = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  let 'E = (if 'N == 16 then 5 else if 'N == 32 then 8 else 11) : {|5, 8, 11|};
  F : atom('N - 'E - 1) = ('N - E) - 1;
  sign : bits(1) = [imm8[7]];
  exp : bits('E) = append(append(~([imm8[6]]), replicate_bits([imm8[6]], E - 3)), imm8[5 .. 4]);
  frac : bits('N - 1 - 'E) = append(imm8[3 .. 0], Zeros(F - 4));
  return(append(append(sign, exp), frac))
}

val SignExtend__0 : forall ('M : Int) ('N : Int), 'M >= 0 & 'N >= 0.
  (bits('M), atom('N)) -> bits('N) effect {escape}

val SignExtend__1 : forall ('M : Int) ('N : Int), 'M >= 0 & 'N >= 0.
  bits('M) -> bits('N) effect {escape}

overload SignExtend = {SignExtend__0, SignExtend__1}

function SignExtend__0 (x, N) = {
  assert('N >= 'M);
  return(extsv(x))
}

function SignExtend__1 x = return(SignExtend(x, 'N))

val Extend__0 : forall ('M : Int) ('N : Int), 'M >= 0 & 'N >= 0.
  (bits('M), atom('N), bool) -> bits('N) effect {escape}

val Extend__1 : forall ('M : Int) ('N : Int), 'M >= 0 & 'N >= 0.
  (bits('M), bool) -> bits('N) effect {escape}

overload Extend = {Extend__0, Extend__1}

function Extend__0 (x, N, unsigned) = return(if unsigned then ZeroExtend(x, 'N) else SignExtend(x, 'N))

function Extend__1 (x, unsigned) = return(Extend(x, 'N, unsigned))

val ASR_C : forall ('N : Int), 'N >= 0 & 'N >= 0 & 1 >= 0.
  (bits('N), int) -> (bits('N), bits(1)) effect {escape}

function ASR_C (x, 'shift) = {
  assert(shift > 0, "(shift > 0)");
  result : bits('N) = arith_shiftright(x, shift);
  carry_out : bits(1) = if shift > 'N then [x['N - 1]] else [x[shift - 1]];
  return((result, carry_out))
}

val ASR : forall ('N : Int), 'N >= 0 & 'N >= 0.
  (bits('N), int) -> bits('N) effect {escape, undef}

function ASR (x, 'shift) = {
  assert(shift >= 0, "(shift >= 0)");
  __anon1 : bits(1) = undefined;
  result : bits('N) = undefined;
  if shift == 0 then result = x else (result, __anon1) = ASR_C(x, shift);
  return(result)
}

val Ones__0 : forall ('N : Int), 'N >= 0. atom('N) -> bits('N)

val Ones__1 : forall ('N : Int), 'N >= 0. unit -> bits('N)

overload Ones = {Ones__0, Ones__1}

function Ones__0 N = return(replicate_bits(0b1, 'N))

function Ones__1 () = return(Ones('N))

val IsOnes : forall ('N : Int), 'N >= 0. bits('N) -> bool

function IsOnes x = return(x == Ones('N))

val FPMaxNormal : forall ('N : Int), 1 >= 0 & 'N >= 0.
  bits(1) -> bits('N) effect {escape}

function FPMaxNormal sign = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  let 'E = (if 'N == 16 then 5 else if 'N == 32 then 8 else 11) : {|5, 8, 11|};
  F : atom('N - 'E - 1) = ('N - E) - 1;
  exp : bits('E) = append(Ones(E - 1), 0b0);
  frac : bits('N - 1 - 'E) = Ones(F);
  return(append(append(sign, exp), frac))
}

val FPInfinity : forall ('N : Int), 1 >= 0 & 'N >= 0.
  bits(1) -> bits('N) effect {escape}

function FPInfinity sign = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  let 'E = (if 'N == 16 then 5 else if 'N == 32 then 8 else 11) : {|5, 8, 11|};
  F : atom('N - 'E - 1) = ('N - E) - 1;
  exp : bits('E) = Ones(E);
  frac : bits('N - 1 - 'E) = Zeros(F);
  return(append(append(sign, exp), frac))
}

val FPDefaultNaN : forall ('N : Int), 'N >= 0. unit -> bits('N) effect {escape}

function FPDefaultNaN () = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  let 'E = (if 'N == 16 then 5 else if 'N == 32 then 8 else 11) : {|5, 8, 11|};
  F : atom('N - 'E - 1) = ('N - E) - 1;
  sign : bits(1) = 0b0;
  exp : bits('E) = Ones(E);
  frac : bits('N - 1 - 'E) = append(0b1, Zeros(F - 1));
  return(append(append(sign, exp), frac))
}

val FPConvertNaN : forall ('N : Int) ('M : Int), 'N >= 0 & 'M >= 0.
  bits('N) -> bits('M) effect {escape, undef}

function FPConvertNaN op = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  assert('M == 16 | 'M == 32 | 'M == 64, "((M == 16) || ((M == 32) || (M == 64)))");
  result : bits('M) = undefined;
  frac : bits(51) = undefined;
  sign : bits(1) = [op['N - 1]];
  match 'N {
    64 => frac = slice(op, 0, 51),
    32 => frac = slice(op, 0, 22) @ Zeros(29),
    16 => frac = slice(op, 0, 9) @ Zeros(42)
  };
  match 'M {
    64 => result = (sign @ Ones('M - 52)) @ frac,
    32 => result = (sign @ Ones('M - 23)) @ slice(frac, 29, 22),
    16 => result = (sign @ Ones('M - 10)) @ slice(frac, 42, 9)
  };
  return(result)
}

val ExcVectorBase : unit -> bits(32) effect {rreg}

function ExcVectorBase () = if [SCTLR[13]] == 0b1 then return(Ones(16) @ Zeros(16)) else return(slice(VBAR, 5, 27) @ Zeros(5))

val PACSub : bits(64) -> bits(64) effect {undef}

function PACSub Tinput = {
  Toutput : bits(64) = undefined;
  foreach (i from 0 to 15 by 1 in inc)
    match slice(Tinput, 4 * i, 4) {
      0x0 => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0xB),
      0x1 => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0x6),
      0x2 => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0x8),
      0x3 => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0xF),
      0x4 => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0xC),
      0x5 => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0x0),
      0x6 => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0x9),
      0x7 => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0xE),
      0x8 => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0x3),
      0x9 => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0x7),
      0xA => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0x4),
      0xB => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0x5),
      0xC => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0xD),
      0xD => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0x2),
      0xE => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0x1),
      0xF => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0xA)
    };
  return(Toutput)
}

val PACMult : bits(64) -> bits(64) effect {undef}

function PACMult Sinput = {
  t0 : bits(4) = undefined;
  t1 : bits(4) = undefined;
  t2 : bits(4) = undefined;
  t3 : bits(4) = undefined;
  Soutput : bits(64) = undefined;
  foreach (i from 0 to 3 by 1 in inc) {
    t0 = __SetSlice_bits(4, 4, t0, 0, RotCell(slice(Sinput, 4 * (i + 8), 4), 1) ^ RotCell(slice(Sinput, 4 * (i + 4), 4), 2));
    t0 = __SetSlice_bits(4, 4, t0, 0, slice(t0, 0, 4) ^ RotCell(slice(Sinput, 4 * i, 4), 1));
    t1 = __SetSlice_bits(4, 4, t1, 0, RotCell(slice(Sinput, 4 * (i + 12), 4), 1) ^ RotCell(slice(Sinput, 4 * (i + 4), 4), 1));
    t1 = __SetSlice_bits(4, 4, t1, 0, slice(t1, 0, 4) ^ RotCell(slice(Sinput, 4 * i, 4), 2));
    t2 = __SetSlice_bits(4, 4, t2, 0, RotCell(slice(Sinput, 4 * (i + 12), 4), 2) ^ RotCell(slice(Sinput, 4 * (i + 8), 4), 1));
    t2 = __SetSlice_bits(4, 4, t2, 0, slice(t2, 0, 4) ^ RotCell(slice(Sinput, 4 * i, 4), 1));
    t3 = __SetSlice_bits(4, 4, t3, 0, RotCell(slice(Sinput, 4 * (i + 12), 4), 1) ^ RotCell(slice(Sinput, 4 * (i + 8), 4), 2));
    t3 = __SetSlice_bits(4, 4, t3, 0, slice(t3, 0, 4) ^ RotCell(slice(Sinput, 4 * (i + 4), 4), 1));
    Soutput = __SetSlice_bits(64, 4, Soutput, 4 * i, slice(t3, 0, 4));
    Soutput = __SetSlice_bits(64, 4, Soutput, 4 * (i + 4), slice(t2, 0, 4));
    Soutput = __SetSlice_bits(64, 4, Soutput, 4 * (i + 8), slice(t1, 0, 4));
    Soutput = __SetSlice_bits(64, 4, Soutput, 4 * (i + 12), slice(t0, 0, 4))
  };
  return(Soutput)
}

val PACInvSub : bits(64) -> bits(64) effect {undef}

function PACInvSub Tinput = {
  Toutput : bits(64) = undefined;
  foreach (i from 0 to 15 by 1 in inc)
    match slice(Tinput, 4 * i, 4) {
      0x0 => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0x5),
      0x1 => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0xE),
      0x2 => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0xD),
      0x3 => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0x8),
      0x4 => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0xA),
      0x5 => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0xB),
      0x6 => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0x1),
      0x7 => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0x9),
      0x8 => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0x2),
      0x9 => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0x6),
      0xA => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0xF),
      0xB => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0x0),
      0xC => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0x4),
      0xD => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0xC),
      0xE => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0x7),
      0xF => Toutput = __SetSlice_bits(64, 4, Toutput, 4 * i, 0x3)
    };
  return(Toutput)
}

val ComputePAC : (bits(64), bits(64), bits(64), bits(64)) -> bits(64) effect {escape, rreg, undef, wreg}

function ComputePAC (data, modifier, key0, key1) = {
  workingval : bits(64) = undefined;
  runningmod : bits(64) = undefined;
  roundkey : bits(64) = undefined;
  modk0 : bits(64) = undefined;
  Alpha : bits(64) = hex_slice("0xC0AC29B7C97C50DD", 64, 0);
  RC[0] = hex_slice("0x0", 64, 0);
  RC[1] = hex_slice("0x13198A2E03707344", 64, 0);
  RC[2] = hex_slice("0xA493822299F31D0", 64, 0);
  RC[3] = hex_slice("0x82EFA98EC4E6C89", 64, 0);
  RC[4] = hex_slice("0x452821E638D01377", 64, 0);
  modk0 = ([key0[0]] @ slice(key0, 2, 62)) @ ([key0[63]] ^ [key0[1]]);
  runningmod = modifier;
  workingval = data ^ key0;
  foreach (i from 0 to 4 by 1 in inc) {
    roundkey = key1 ^ runningmod;
    workingval = workingval ^ roundkey;
    workingval = workingval ^ RC[i];
    if i > 0 then {
      workingval = PACCellShuffle(workingval);
      workingval = PACMult(workingval)
    } else ();
    workingval = PACSub(workingval);
    runningmod = TweakShuffle(slice(runningmod, 0, 64))
  };
  roundkey = modk0 ^ runningmod;
  workingval = workingval ^ roundkey;
  workingval = PACCellShuffle(workingval);
  workingval = PACMult(workingval);
  workingval = PACSub(workingval);
  workingval = PACCellShuffle(workingval);
  workingval = PACMult(workingval);
  workingval = key1 ^ workingval;
  workingval = PACCellInvShuffle(workingval);
  workingval = PACInvSub(workingval);
  workingval = PACMult(workingval);
  workingval = PACCellInvShuffle(workingval);
  workingval = workingval ^ key0;
  workingval = workingval ^ runningmod;
  foreach (i from 0 to 4 by 1 in inc) {
    workingval = PACInvSub(workingval);
    if i < 4 then {
      workingval = PACMult(workingval);
      workingval = PACCellInvShuffle(workingval)
    } else ();
    runningmod = TweakInvShuffle(slice(runningmod, 0, 64));
    roundkey = key1 ^ runningmod;
    workingval = workingval ^ RC[4 - i];
    workingval = workingval ^ roundkey;
    workingval = workingval ^ Alpha
  };
  workingval = workingval ^ modk0;
  return(workingval)
}

val Align__0 : (int, int) -> int

val Align__1 : forall ('N : Int), 'N >= 0 & 'N >= 0. (bits('N), int) -> bits('N)

overload Align = {Align__0, Align__1}

function Align__0 ('x, 'y) = return(y * (x / y))

function Align__1 (x, 'y) = return(__GetSlice_int('N, Align(UInt(x), y), 0))

val aset__Mem : forall ('size : Int), 8 * 'size >= 0.
  (AddressDescriptor, atom('size), AccessDescriptor, bits(8 * 'size)) -> unit effect {escape, rreg, wmem}

function aset__Mem (desc, size, accdesc, value_name) = {
  assert('size == 1 | 'size == 2 | 'size == 4 | 'size == 8 | 'size == 16, "((size == 1) || ((size == 2) || ((size == 4) || ((size == 8) || (size == 16)))))");
  address : bits(52) = desc.paddress.physicaladdress;
  assert(address == Align(address, 'size), "(address == Align(address, size))");
  if address == hex_slice("0x13000000", 52, 0) then if UInt(value_name) == 4 then {
    print("Program exited by writing ^D to TUBE\n");
    exit(())
  } else putchar(UInt(slice(value_name, 0, 8))) else __WriteRAM(52, 'size, __Memory, address, value_name);
  ()
}

val aget__Mem : forall ('size : Int), 8 * 'size >= 0.
  (AddressDescriptor, atom('size), AccessDescriptor) -> bits(8 * 'size) effect {escape, rmem, rreg}

function aget__Mem (desc, size, accdesc) = {
  assert('size == 1 | 'size == 2 | 'size == 4 | 'size == 8 | 'size == 16, "((size == 1) || ((size == 2) || ((size == 4) || ((size == 8) || (size == 16)))))");
  address : bits(52) = desc.paddress.physicaladdress;
  assert(address == Align(address, 'size), "(address == Align(address, size))");
  return(__ReadRAM(52, 'size, __Memory, address))
}

val aset_X : forall ('width : Int), 'width >= 0.
  (int, bits('width)) -> unit effect {wreg, escape}

function aset_X (n, value_name) = {
  assert(n >= 0 & n <= 31, "((n >= 0) && (n <= 31))");
  assert('width == 32 | 'width == 64, "((width == 32) || (width == 64))");
  if n != 31 then _R[n] = ZeroExtend(value_name, 64)
  else ();
  ()
}

val aarch64_integer_arithmetic_address_pcrel : (int, bits(64), bool) -> unit effect {escape, rreg, wreg}

function aarch64_integer_arithmetic_address_pcrel ('d, imm, page) = {
  base : bits(64) = aget_PC();
  if page then base = __SetSlice_bits(64, 12, base, 0, Zeros(12)) else ();
  aset_X(d, base + imm)
}

val integer_arithmetic_address_pcrel_decode : (bits(1), bits(2), bits(19), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_arithmetic_address_pcrel_decode (op, immlo, immhi, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  page : bool = op == 0b1;
  imm : bits(64) = undefined;
  if page then imm = SignExtend((immhi @ immlo) @ Zeros(12), 64) else imm = SignExtend(immhi @ immlo, 64);
  aarch64_integer_arithmetic_address_pcrel(d, imm, page)
}

val AArch64_ResetGeneralRegisters : unit -> unit effect {escape, undef, wreg}

function AArch64_ResetGeneralRegisters () = {
  foreach (i from 0 to 30 by 1 in inc) aset_X(i, undefined : bits(64));
  ()
}

val aset_ELR__0 : (bits(2), bits(64)) -> unit effect {wreg, escape}

val aset_ELR__1 : bits(64) -> unit effect {wreg, rreg, escape}

overload aset_ELR = {aset_ELR__0, aset_ELR__1}

function aset_ELR__0 (el, value_name) = {
  r : bits(64) = value_name;
  match el {
    ? if ? == EL1 => ELR_EL1 = r,
    ? if ? == EL2 => ELR_EL2 = r,
    ? if ? == EL3 => ELR_EL3 = r,
    _ => Unreachable()
  };
  ()
}

function aset_ELR__1 value_name = {
  assert(PSTATE.EL != EL0);
  aset_ELR(PSTATE.EL, value_name);
  ()
}

val aget_X : forall ('width : Int), 'width >= 0.
  int -> bits('width) effect {escape, rreg}

function aget_X 'n = {
  assert(n >= 0 & n <= 31, "((n >= 0) && (n <= 31))");
  assert('width == 8 | 'width == 16 | 'width == 32 | 'width == 64, "((width == 8) || ((width == 16) || ((width == 32) || (width == 64))))");
  if n != 31 then return(slice(_R[n], 0, 'width)) else return(Zeros('width))
}

val aarch64_system_sysops : (bool, int, int, int, int, int, int) -> unit effect {escape, rreg, wreg}

function aarch64_system_sysops (has_result, 'sys_crm, 'sys_crn, 'sys_op0, 'sys_op1, 'sys_op2, 't) = if has_result then aset_X(t, AArch64_SysInstrWithResult(sys_op0, sys_op1, sys_crn, sys_crm, sys_op2)) else AArch64_SysInstr(sys_op0, sys_op1, sys_crn, sys_crm, sys_op2, aget_X(t))

val aarch64_system_register_system : (bool, int, int, int, int, int, int) -> unit effect {escape, rreg, undef, wreg}

function aarch64_system_register_system (read, 'sys_crm, 'sys_crn, 'sys_op0, 'sys_op1, 'sys_op2, 't) = if read then aset_X(t, AArch64_SysRegRead(sys_op0, sys_op1, sys_crn, sys_crm, sys_op2)) else AArch64_SysRegWrite(sys_op0, sys_op1, sys_crn, sys_crm, sys_op2, aget_X(t))

val aarch64_integer_insext_insert_movewide : (int, int, bits(16), MoveWideOp, int) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_insext_insert_movewide ('d, 'datasize, imm, opcode, 'pos) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  result : bits('datasize) = undefined;
  if opcode == MoveWideOp_K then result = aget_X(d) else result = Zeros();
  result = __SetSlice_bits(datasize, 16, result, pos, imm);
  if opcode == MoveWideOp_N then result = ~(result) else ();
  aset_X(d, result)
}

val aarch64_integer_insext_extract_immediate : (int, int, int, int, int) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_insext_extract_immediate ('d, 'datasize, 'lsb, 'm, 'n) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  result : bits('datasize) = undefined;
  operand1 : bits('datasize) = aget_X(n);
  operand2 : bits('datasize) = aget_X(m);
  concat : bits(2 * 'datasize) = operand1 @ operand2;
  result = slice(concat, lsb, datasize);
  aset_X(d, result)
}

val aarch64_integer_arithmetic_rev : (int, int, int, int) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_arithmetic_rev ('container_size, 'd, 'datasize, 'n) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  operand : bits('datasize) = aget_X(n);
  result : bits('datasize) = undefined;
  containers : int = datasize / container_size;
  elements_per_container : int = container_size / 8;
  index : int = 0;
  rev_index : int = undefined;
  foreach (c from 0 to (containers - 1) by 1 in inc) {
    rev_index = index + (elements_per_container - 1) * 8;
    foreach (e from 0 to (elements_per_container - 1) by 1 in inc) {
      result = __SetSlice_bits(datasize, 8, result, rev_index, slice(operand, index, 8));
      index = index + 8;
      rev_index = rev_index - 8
    }
  };
  aset_X(d, result)
}

val aarch64_integer_arithmetic_rbit : (int, int, int) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_arithmetic_rbit ('d, 'datasize, 'n) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  operand : bits('datasize) = aget_X(n);
  result : bits('datasize) = undefined;
  foreach (i from 0 to (datasize - 1) by 1 in inc)
    result = __SetSlice_bits(datasize, 1, result, (datasize - 1) - i, [operand[i]]);
  aset_X(d, result)
}

val integer_arithmetic_rbit_decode : (bits(1), bits(1), bits(5), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_arithmetic_rbit_decode (sf, S, opcode2, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  let 'datasize : {|64, 32|} = if sf == 0b1 then 64 else 32;
  aarch64_integer_arithmetic_rbit(d, datasize, n)
}

val aarch64_integer_arithmetic_mul_widening_64128hi : (int, int, int, int, bool) -> unit effect {escape, rreg, wreg}

function aarch64_integer_arithmetic_mul_widening_64128hi ('d, 'datasize, 'm, 'n, unsigned) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  operand1 : bits('datasize) = aget_X(n);
  operand2 : bits('datasize) = aget_X(m);
  result : int = asl_Int(operand1, unsigned) * asl_Int(operand2, unsigned);
  aset_X(d, __GetSlice_int(64, result, 64))
}

val integer_arithmetic_mul_widening_64128hi_decode : (bits(1), bits(2), bits(1), bits(5), bits(1), bits(5), bits(5), bits(5)) -> unit effect {escape, rreg, wreg}

function integer_arithmetic_mul_widening_64128hi_decode (sf, op54, U, Rm, o0, Ra, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  a : int = UInt(Ra);
  let 'destsize : {|64|} = 64;
  datasize : int = destsize;
  unsigned : bool = U == 0b1;
  aarch64_integer_arithmetic_mul_widening_64128hi(d, datasize, m, n, unsigned)
}

val aarch64_integer_arithmetic_mul_widening_3264 : (int, int, int, int, int, int, bool, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_arithmetic_mul_widening_3264 ('a, 'd, 'datasize, 'destsize, 'm, 'n, sub_op, unsigned) = {
  assert(constraint('destsize in {32, 64}), "destsize constraint");
  let 'dbytes = ex_int(datasize / 8);
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  operand1 : bits('datasize) = aget_X(n);
  operand2 : bits('datasize) = aget_X(m);
  operand3 : bits('destsize) = aget_X(a);
  result : int = undefined;
  if sub_op then result = asl_Int(operand3, unsigned) - asl_Int(operand1, unsigned) * asl_Int(operand2, unsigned) else result = asl_Int(operand3, unsigned) + asl_Int(operand1, unsigned) * asl_Int(operand2, unsigned);
  aset_X(d, __GetSlice_int(64, result, 0))
}

val integer_arithmetic_mul_widening_3264_decode : (bits(1), bits(2), bits(1), bits(5), bits(1), bits(5), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_arithmetic_mul_widening_3264_decode (sf, op54, U, Rm, o0, Ra, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  a : int = UInt(Ra);
  let 'destsize : {|64|} = 64;
  let 'datasize : {|32|} = 32;
  sub_op : bool = o0 == 0b1;
  unsigned : bool = U == 0b1;
  aarch64_integer_arithmetic_mul_widening_3264(a, d, datasize, destsize, m, n, sub_op, unsigned)
}

val aarch64_integer_arithmetic_mul_uniform_addsub : (int, int, int, int, int, int, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_arithmetic_mul_uniform_addsub ('a, 'd, 'datasize, 'destsize, 'm, 'n, sub_op) = {
  assert(constraint('destsize in {32, 64}), "destsize constraint");
  let 'dbytes = ex_int(datasize / 8);
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  operand1 : bits('datasize) = aget_X(n);
  operand2 : bits('datasize) = aget_X(m);
  operand3 : bits('destsize) = aget_X(a);
  result : int = undefined;
  if sub_op then result = UInt(operand3) - UInt(operand1) * UInt(operand2) else result = UInt(operand3) + UInt(operand1) * UInt(operand2);
  aset_X(d, __GetSlice_int(destsize, result, 0))
}

val integer_arithmetic_mul_uniform_addsub_decode : (bits(1), bits(2), bits(3), bits(5), bits(1), bits(5), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_arithmetic_mul_uniform_addsub_decode (sf, op54, op31, Rm, o0, Ra, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  a : int = UInt(Ra);
  let 'destsize : {|64, 32|} = if sf == 0b1 then 64 else 32;
  datasize : int = destsize;
  sub_op : bool = o0 == 0b1;
  aarch64_integer_arithmetic_mul_uniform_addsub(a, d, datasize, destsize, m, n, sub_op)
}

val aarch64_integer_arithmetic_div : (int, int, int, int, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_arithmetic_div ('d, 'datasize, 'm, 'n, unsigned) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  operand1 : bits('datasize) = aget_X(n);
  operand2 : bits('datasize) = aget_X(m);
  result : int = undefined;
  if IsZero(operand2) then result = 0 else result = RoundTowardsZero(Real(asl_Int(operand1, unsigned)) / Real(asl_Int(operand2, unsigned)));
  aset_X(d, __GetSlice_int(datasize, result, 0))
}

val integer_arithmetic_div_decode : (bits(1), bits(1), bits(1), bits(5), bits(5), bits(1), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_arithmetic_div_decode (sf, op, S, Rm, opcode2, o1, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  let 'datasize : {|64, 32|} = if sf == 0b1 then 64 else 32;
  unsigned : bool = o1 == 0b0;
  aarch64_integer_arithmetic_div(d, datasize, m, n, unsigned)
}

val aarch64_integer_arithmetic_cnt : (int, int, int, CountOp) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_arithmetic_cnt ('d, 'datasize, 'n, opcode) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  result : int = undefined;
  operand1 : bits('datasize) = aget_X(n);
  if opcode == CountOp_CLZ then result = CountLeadingZeroBits(operand1) else result = CountLeadingSignBits(operand1);
  aset_X(d, __GetSlice_int(datasize, result, 0))
}

val integer_arithmetic_cnt_decode : (bits(1), bits(1), bits(5), bits(1), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_arithmetic_cnt_decode (sf, S, opcode2, op, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  let 'datasize : {|64, 32|} = if sf == 0b1 then 64 else 32;
  opcode : CountOp = if op == 0b0 then CountOp_CLZ else CountOp_CLS;
  aarch64_integer_arithmetic_cnt(d, datasize, n, opcode)
}

val aarch64_integer_arithmetic_addsub_carry : (int, int, int, int, bool, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_arithmetic_addsub_carry ('d, 'datasize, 'm, 'n, setflags, sub_op) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  result : bits('datasize) = undefined;
  operand1 : bits('datasize) = aget_X(n);
  operand2 : bits('datasize) = aget_X(m);
  nzcv : bits(4) = undefined;
  if sub_op then operand2 = ~(operand2) else ();
  (result, nzcv) = AddWithCarry(operand1, operand2, PSTATE.C);
  if setflags then (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = nzcv else ();
  aset_X(d, result)
}

val integer_arithmetic_addsub_carry_decode : (bits(1), bits(1), bits(1), bits(5), bits(6), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_arithmetic_addsub_carry_decode (sf, op, S, Rm, opcode2, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  let 'datasize : {|64, 32|} = if sf == 0b1 then 64 else 32;
  sub_op : bool = op == 0b1;
  setflags : bool = S == 0b1;
  aarch64_integer_arithmetic_addsub_carry(d, datasize, m, n, setflags, sub_op)
}

val ExtendReg : forall ('N : Int), 'N >= 0.
  (int, ExtendType, int) -> bits('N) effect {escape, rreg, undef}

function ExtendReg (reg, typ, shift) = {
  assert(shift >= 0 & shift <= 4, "((shift >= 0) && (shift <= 4))");
  val_name : bits('N) = aget_X(reg);
  unsigned : bool = undefined;
  len : int = undefined;
  match typ {
    ExtendType_SXTB => {
      unsigned = false;
      len = 8
    },
    ExtendType_SXTH => {
      unsigned = false;
      len = 16
    },
    ExtendType_SXTW => {
      unsigned = false;
      len = 32
    },
    ExtendType_SXTX => {
      unsigned = false;
      len = 64
    },
    ExtendType_UXTB => {
      unsigned = true;
      len = 8
    },
    ExtendType_UXTH => {
      unsigned = true;
      len = 16
    },
    ExtendType_UXTW => {
      unsigned = true;
      len = 32
    },
    ExtendType_UXTX => {
      unsigned = true;
      len = 64
    }
  };
  len = min(len, 'N - shift);
  shift2 = coerce_int_nat(shift);
  let 'len2 : {'n, true. atom('n)} = ex_int(len);
  assert(constraint('len2 >= 2), "hack");
  return(Extend(append(val_name[len2 - 1 .. 0], Zeros(ex_nat(shift2))), 'N, unsigned))
}

val aget_ELR__0 : bits(2) -> bits(64) effect {escape, rreg, undef}

val aget_ELR__1 : unit -> bits(64) effect {escape, rreg, undef}

overload aget_ELR = {aget_ELR__0, aget_ELR__1}

function aget_ELR__0 el = {
  r : bits(64) = undefined;
  match el {
    ? if ? == EL1 => r = ELR_EL1,
    ? if ? == EL2 => r = ELR_EL2,
    ? if ? == EL3 => r = ELR_EL3,
    _ => Unreachable()
  };
  return(r)
}

function aget_ELR__1 () = {
  assert(PSTATE.EL != EL0);
  return(aget_ELR(PSTATE.EL))
}

val ROR_C : forall ('N : Int), 'N >= 0 & 'N >= 0 & 1 >= 0.
  (bits('N), int) -> (bits('N), bits(1)) effect {escape, undef}

function ROR_C (x, 'shift) = {
  assert(shift != 0, "(shift != 0)");
  m : int = shift % 'N;
  result : bits('N) = LSR(x, m) | LSL(x, 'N - m);
  carry_out : bits(1) = [result['N - 1]];
  return((result, carry_out))
}

val ROR : forall ('N : Int), 'N >= 0 & 'N >= 0.
  (bits('N), int) -> bits('N) effect {escape, undef}

function ROR (x, 'shift) = {
  assert(shift >= 0, "(shift >= 0)");
  __anon1 : bits(1) = undefined;
  result : bits('N) = undefined;
  if shift == 0 then result = x else (result, __anon1) = ROR_C(x, shift);
  return(result)
}

val aarch64_integer_bitfield : forall ('datasize : Int).
  (int, int, int, atom('datasize), bool, bool, int, bits('datasize), bits('datasize)) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_bitfield ('R, 'S, 'd, datasize, extend, inzero, 'n, tmask, wmask) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  dst : bits('datasize) = if inzero then Zeros() else aget_X(d);
  src : bits('datasize) = aget_X(n);
  bot : bits('datasize) = dst & ~(wmask) | ROR(src, R) & wmask;
  top : bits('datasize) = if extend then Replicate([src[S]]) else dst;
  aset_X(d, top & ~(tmask) | bot & tmask)
}

val ShiftReg : forall ('N : Int), 'N >= 0.
  (int, ShiftType, int) -> bits('N) effect {escape, rreg, undef}

function ShiftReg ('reg, typ, 'amount) = {
  result : bits('N) = aget_X(reg);
  match typ {
    ShiftType_LSL => result = LSL(result, amount),
    ShiftType_LSR => result = LSR(result, amount),
    ShiftType_ASR => result = ASR(result, amount),
    ShiftType_ROR => result = ROR(result, amount)
  };
  return(result)
}

val aarch64_integer_shift_variable : (int, int, int, int, ShiftType) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_shift_variable ('d, 'datasize, 'm, 'n, shift_type) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  result : bits('datasize) = undefined;
  operand2 : bits('datasize) = aget_X(m);
  result = ShiftReg(n, shift_type, UInt(operand2) % datasize);
  aset_X(d, result)
}

val integer_shift_variable_decode : (bits(1), bits(1), bits(1), bits(5), bits(4), bits(2), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_shift_variable_decode (sf, op, S, Rm, opcode2, op2, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  let 'datasize : {|64, 32|} = if sf == 0b1 then 64 else 32;
  shift_type : ShiftType = DecodeShift(op2);
  aarch64_integer_shift_variable(d, datasize, m, n, shift_type)
}

val aarch64_integer_logical_shiftedreg : (int, int, bool, int, int, LogicalOp, bool, int, ShiftType) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_logical_shiftedreg ('d, 'datasize, invert, 'm, 'n, op, setflags, 'shift_amount, shift_type) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  operand1 : bits('datasize) = aget_X(n);
  operand2 : bits('datasize) = ShiftReg(m, shift_type, shift_amount);
  if invert then operand2 = ~(operand2) else ();
  result : bits('datasize) = undefined;
  match op {
    LogicalOp_AND => result = operand1 & operand2,
    LogicalOp_ORR => result = operand1 | operand2,
    LogicalOp_EOR => result = operand1 ^ operand2
  };
  if setflags then (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = ([result[datasize - 1]] @ IsZeroBit(result)) @ 0b00 else ();
  aset_X(d, result)
}

val aarch64_integer_arithmetic_addsub_shiftedreg : (int, int, int, int, bool, int, ShiftType, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_arithmetic_addsub_shiftedreg ('d, 'datasize, 'm, 'n, setflags, 'shift_amount, shift_type, sub_op) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  result : bits('datasize) = undefined;
  operand1 : bits('datasize) = aget_X(n);
  operand2 : bits('datasize) = ShiftReg(m, shift_type, shift_amount);
  nzcv : bits(4) = undefined;
  carry_in : bits(1) = undefined;
  if sub_op then {
    operand2 = ~(operand2);
    carry_in = 0b1
  } else carry_in = 0b0;
  (result, nzcv) = AddWithCarry(operand1, operand2, carry_in);
  if setflags then (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = nzcv else ();
  aset_X(d, result)
}

val Prefetch : (bits(64), bits(5)) -> unit effect {undef}

function Prefetch (address, prfop) = {
  hint : PrefetchHint = undefined;
  target : int = undefined;
  stream : bool = undefined;
  match slice(prfop, 3, 2) {
    0b00 => hint = Prefetch_READ,
    0b01 => hint = Prefetch_EXEC,
    0b10 => hint = Prefetch_WRITE,
    0b11 => ()
  };
  target = UInt(slice(prfop, 1, 2));
  stream = [prfop[0]] != 0b0;
  Hint_Prefetch(address, hint, target, stream);
  ()
}

val IsSecondStage : FaultRecord -> bool effect {escape}

function IsSecondStage fault = {
  assert(fault.typ != Fault_None, "((fault).type != Fault_None)");
  return(fault.secondstage)
}

val IsFault : AddressDescriptor -> bool

function IsFault addrdesc = return(addrdesc.fault.typ != Fault_None)

val CombineS1S2Desc : (AddressDescriptor, AddressDescriptor) -> AddressDescriptor effect {undef}

function CombineS1S2Desc (s1desc, s2desc) = {
  result : AddressDescriptor = undefined;
  result.paddress = s2desc.paddress;
  if IsFault(s1desc) | IsFault(s2desc) then result = if IsFault(s1desc) then s1desc else s2desc else if s2desc.memattrs.typ == MemType_Device | s1desc.memattrs.typ == MemType_Device then {
    __tmp_61 : MemoryAttributes = result.memattrs;
    __tmp_61.typ = MemType_Device;
    result.memattrs = __tmp_61;
    if s1desc.memattrs.typ == MemType_Normal then {
      __tmp_62 : MemoryAttributes = result.memattrs;
      __tmp_62.device = s2desc.memattrs.device;
      result.memattrs = __tmp_62
    } else if s2desc.memattrs.typ == MemType_Normal then {
      __tmp_63 : MemoryAttributes = result.memattrs;
      __tmp_63.device = s1desc.memattrs.device;
      result.memattrs = __tmp_63
    } else {
      __tmp_64 : MemoryAttributes = result.memattrs;
      __tmp_64.device = CombineS1S2Device(s1desc.memattrs.device, s2desc.memattrs.device);
      result.memattrs = __tmp_64
    }
  } else {
    __tmp_65 : MemoryAttributes = result.memattrs;
    __tmp_65.typ = MemType_Normal;
    result.memattrs = __tmp_65;
    __tmp_66 : MemoryAttributes = result.memattrs;
    __tmp_66.device = undefined;
    result.memattrs = __tmp_66;
    __tmp_67 : MemoryAttributes = result.memattrs;
    __tmp_67.inner = CombineS1S2AttrHints(s1desc.memattrs.inner, s2desc.memattrs.inner);
    result.memattrs = __tmp_67;
    __tmp_68 : MemoryAttributes = result.memattrs;
    __tmp_68.outer = CombineS1S2AttrHints(s1desc.memattrs.outer, s2desc.memattrs.outer);
    result.memattrs = __tmp_68;
    __tmp_69 : MemoryAttributes = result.memattrs;
    __tmp_69.shareable = s1desc.memattrs.shareable | s2desc.memattrs.shareable;
    result.memattrs = __tmp_69;
    __tmp_70 : MemoryAttributes = result.memattrs;
    __tmp_70.outershareable = s1desc.memattrs.outershareable | s2desc.memattrs.outershareable;
    result.memattrs = __tmp_70
  };
  result.memattrs = MemAttrDefaults(result.memattrs);
  return(result)
}

val IsExternalSyncAbort__0 : Fault -> bool effect {escape}

val IsExternalSyncAbort__1 : FaultRecord -> bool effect {escape}

overload IsExternalSyncAbort = {IsExternalSyncAbort__0, IsExternalSyncAbort__1}

function IsExternalSyncAbort__0 typ = {
  assert(typ != Fault_None);
  return(typ == Fault_SyncExternal | typ == Fault_SyncParity | typ == Fault_SyncExternalOnWalk | typ == Fault_SyncParityOnWalk)
}

function IsExternalSyncAbort__1 fault = return(IsExternalSyncAbort(fault.typ))

val IsExternalAbort__0 : Fault -> bool effect {escape}

val IsExternalAbort__1 : FaultRecord -> bool effect {escape}

overload IsExternalAbort = {IsExternalAbort__0, IsExternalAbort__1}

function IsExternalAbort__0 typ = {
  assert(typ != Fault_None);
  return(typ == Fault_SyncExternal | typ == Fault_SyncParity | typ == Fault_SyncExternalOnWalk | typ == Fault_SyncParityOnWalk | typ == Fault_AsyncExternal | typ == Fault_AsyncParity)
}

function IsExternalAbort__1 fault = return(IsExternalAbort(fault.typ))

val IsDebugException : FaultRecord -> bool effect {escape}

function IsDebugException fault = {
  assert(fault.typ != Fault_None, "((fault).type != Fault_None)");
  return(fault.typ == Fault_Debug)
}

val IPAValid : FaultRecord -> bool effect {escape}

function IPAValid fault = {
  assert(fault.typ != Fault_None, "((fault).type != Fault_None)");
  if fault.s2fs1walk then return(fault.typ == Fault_AccessFlag | fault.typ == Fault_Permission | fault.typ == Fault_Translation | fault.typ == Fault_AddressSize) else if fault.secondstage then return(fault.typ == Fault_AccessFlag | fault.typ == Fault_Translation | fault.typ == Fault_AddressSize) else return(false)
}

val aarch64_integer_logical_immediate : forall ('datasize : Int).
  (int, atom('datasize), bits('datasize), int, LogicalOp, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_logical_immediate ('d, datasize, imm, 'n, op, setflags) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  result : bits('datasize) = undefined;
  operand1 : bits('datasize) = aget_X(n);
  operand2 : bits('datasize) = imm;
  match op {
    LogicalOp_AND => result = operand1 & operand2,
    LogicalOp_ORR => result = operand1 | operand2,
    LogicalOp_EOR => result = operand1 ^ operand2
  };
  if setflags then (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = ([result[datasize - 1]] @ IsZeroBit(result)) @ 0b00 else ();
  if d == 31 & ~(setflags) then aset_SP(result) else aset_X(d, result)
}

val aarch64_integer_arithmetic_addsub_immediate : forall ('datasize : Int).
  (int, atom('datasize), bits('datasize), int, bool, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_arithmetic_addsub_immediate ('d, datasize, imm, 'n, setflags, sub_op) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  result : bits('datasize) = undefined;
  operand1 : bits('datasize) = if n == 31 then aget_SP() else aget_X(n);
  operand2 : bits('datasize) = imm;
  nzcv : bits(4) = undefined;
  carry_in : bits(1) = undefined;
  if sub_op then {
    operand2 = ~(operand2);
    carry_in = 0b1
  } else carry_in = 0b0;
  (result, nzcv) = AddWithCarry(operand1, operand2, carry_in);
  if setflags then (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = nzcv else ();
  if d == 31 & ~(setflags) then aset_SP(result) else aset_X(d, result)
}

val aarch64_integer_arithmetic_addsub_extendedreg : (int, int, ExtendType, int, int, bool, int, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_arithmetic_addsub_extendedreg ('d, 'datasize, extend_type, 'm, 'n, setflags, 'shift, sub_op) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  result : bits('datasize) = undefined;
  operand1 : bits('datasize) = if n == 31 then aget_SP() else aget_X(n);
  operand2 : bits('datasize) = ExtendReg(m, extend_type, shift);
  nzcv : bits(4) = undefined;
  carry_in : bits(1) = undefined;
  if sub_op then {
    operand2 = ~(operand2);
    carry_in = 0b1
  } else carry_in = 0b0;
  (result, nzcv) = AddWithCarry(operand1, operand2, carry_in);
  if setflags then (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = nzcv else ();
  if d == 31 & ~(setflags) then aset_SP(result) else aset_X(d, result)
}

val RestoredITBits : bits(32) -> bits(8) effect {escape, rreg}

function RestoredITBits spsr = {
  it : bits(8) = spsr[15 .. 10] @ spsr[26 .. 25];
  if PSTATE.IL == 0b1 then
    if ConstrainUnpredictableBool(Unpredictable_ILZEROIT) then return(0x00) else return(it)
  else ();
  if ~(IsZero(it[7 .. 4])) & IsZero(it[3 .. 0]) then return(0x00) else ();
  itd : bits(1) = if PSTATE.EL == EL2 then [HSCTLR[7]] else [SCTLR[7]];
  if [spsr[5]] == 0b0 & ~(IsZero(it)) | itd == 0b1 & ~(IsZero(it[2 .. 0])) then return(0x00) else return(it)
}

val IsEL1TransRegimeRegs : unit -> bool effect {rreg}

function IsEL1TransRegimeRegs () = return((~(HaveEL(EL2)) | PSTATE.EL == EL1) | PSTATE.EL == EL0 & ([HCR_EL2[34]] == 0b0 | [HCR_EL2[27]] == 0b0))

val CalculateTBI : (bits(64), bool) -> bool effect {rreg}

function CalculateTBI (ptr, data) = {
  tbi : bool = false;
  if PtrHasUpperAndLowerAddRanges() then if IsEL1TransRegimeRegs() then if data then tbi = if [ptr[55]] == 0b1 then [TCR_EL1[38]] == 0b1 else [TCR_EL1[37]] == 0b1 else if [ptr[55]] == 0b1 then tbi = [TCR_EL1[38]] == 0b1 & [TCR_EL1[52]] == 0b0 else tbi = [TCR_EL1[37]] == 0b1 & [TCR_EL1[51]] == 0b0 else if data then tbi = if [ptr[55]] == 0b1 then [TCR_EL2[38]] == 0b1 else [TCR_EL2[37]] == 0b1 else if [ptr[55]] == 0b1 then tbi = [TCR_EL2[38]] == 0b1 & [TCR_EL2[52]] == 0b0 else tbi = [TCR_EL2[37]] == 0b1 & [TCR_EL2[51]] == 0b0 else if PSTATE.EL == EL2 then tbi = if data then [TCR_EL2[20]] == 0b1 else [TCR_EL2[20]] == 0b1 & [TCR_EL2[29]] == 0b0 else if PSTATE.EL == EL3 then tbi = if data then [TCR_EL3[20]] == 0b1 else [TCR_EL3[20]] == 0b1 & [TCR_EL3[29]] == 0b0 else ();
  return(tbi)
}

val CalculateBottomPACBit : (bits(64), bits(1)) -> int effect {escape, rreg, undef}

function CalculateBottomPACBit (ptr, top_bit) = {
  tsz_field : int = undefined;
  using64k : bool = undefined;
  if PtrHasUpperAndLowerAddRanges() then if IsEL1TransRegimeRegs() then {
    tsz_field = if top_bit == 0b1 then UInt(slice(TCR_EL1, 16, 6)) else UInt(slice(TCR_EL1, 0, 6));
    using64k = if top_bit == 0b1 then slice(TCR_EL1, 30, 2) == 0b11 else slice(TCR_EL1, 14, 2) == 0b11
  } else {
    assert(HaveEL(EL2), "HaveEL(EL2)");
    tsz_field = if top_bit == 0b1 then UInt(slice(TCR_EL2, 16, 6)) else UInt(slice(TCR_EL2, 0, 6));
    using64k = if top_bit == 0b1 then slice(TCR_EL2, 30, 2) == 0b11 else slice(TCR_EL2, 14, 2) == 0b11
  } else {
    tsz_field = if PSTATE.EL == EL2 then UInt(slice(TCR_EL2, 0, 6)) else UInt(slice(TCR_EL3, 0, 6));
    using64k = if PSTATE.EL == EL2 then slice(TCR_EL2, 14, 2) == 0b11 else slice(TCR_EL3, 14, 2) == 0b11
  };
  max_limit_tsz_field : int = 39;
  c : Constraint = undefined;
  if tsz_field > max_limit_tsz_field then {
    c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
    assert(c == Constraint_FORCE | c == Constraint_NONE, "((c == Constraint_FORCE) || (c == Constraint_NONE))");
    if c == Constraint_FORCE then tsz_field = max_limit_tsz_field else ()
  } else ();
  tszmin : int = if using64k & VAMax() == 52 then 12 else 16;
  if tsz_field < tszmin then {
    c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
    assert(c == Constraint_FORCE | c == Constraint_NONE, "((c == Constraint_FORCE) || (c == Constraint_NONE))");
    if c == Constraint_FORCE then tsz_field = tszmin else ()
  } else ();
  return(64 - tsz_field)
}

val Auth : (bits(64), bits(64), bits(128), bool, bits(1)) -> bits(64) effect {escape, wreg, rreg, undef}

function Auth (ptr, modifier, K, data, keynumber) = {
  PAC : bits(64) = undefined;
  result : bits(64) = undefined;
  original_ptr : bits(64) = undefined;
  error_code : bits(2) = undefined;
  extfield : bits(64) = undefined;
  tbi : bool = CalculateTBI(ptr, data);
  let 'bottom_PAC_bit = ex_int(CalculateBottomPACBit(ptr, [ptr[55]]));
  assert(constraint('bottom_PAC_bit >= 0));
  extfield = replicate_bits([ptr[55]], 64);
  if tbi then
    original_ptr = (ptr[63 .. 56] @ extfield[(negate(bottom_PAC_bit) + 56) - 1 .. 0]) @ ptr[bottom_PAC_bit - 1 .. 0]
  else
    original_ptr = extfield[(negate(bottom_PAC_bit) + 64) - 1 .. 0] @ ptr[bottom_PAC_bit - 1 .. 0];
  PAC = ComputePAC(original_ptr, modifier, K[127 .. 64], K[63 .. 0]);
  if tbi then
    if PAC[((negate(bottom_PAC_bit) + 55) - 1) + bottom_PAC_bit .. bottom_PAC_bit] == ptr[((negate(bottom_PAC_bit) + 55) - 1) + bottom_PAC_bit .. bottom_PAC_bit] then
      result = original_ptr
    else {
      error_code = keynumber @ ~(keynumber);
      result = (original_ptr[63 .. 55] @ error_code) @ original_ptr[52 .. 0]
    }
  else if PAC[((negate(bottom_PAC_bit) + 55) - 1) + bottom_PAC_bit .. bottom_PAC_bit] == ptr[((negate(bottom_PAC_bit) + 55) - 1) + bottom_PAC_bit .. bottom_PAC_bit] & PAC[63 .. 56] == ptr[63 .. 56] then
    result = original_ptr
  else {
    error_code = keynumber @ ~(keynumber);
    result = ([original_ptr[63]] @ error_code) @ original_ptr[60 .. 0]
  };
  return(result)
}

val HighestELUsingAArch32 : unit -> bool

function HighestELUsingAArch32 () = {
  if ~(HaveAnyAArch32()) then return(false) else ();
  return(false)
}

val aget_SCR_GEN : unit -> bits(32) effect {escape, rreg, undef}

function aget_SCR_GEN () = {
  assert(HaveEL(EL3), "HaveEL(EL3)");
  r : bits(32) = undefined;
  if HighestELUsingAArch32() then r = SCR else r = SCR_EL3;
  return(r)
}

val IsSecureBelowEL3 : unit -> bool effect {escape, rreg, undef}

function IsSecureBelowEL3 () = if HaveEL(EL3) then return([aget_SCR_GEN()[0]] == 0b0) else if HaveEL(EL2) then return(false) else return(false)

val UsingAArch32 : unit -> bool effect {escape, rreg}

function UsingAArch32 () = {
  aarch32 : bool = PSTATE.nRW == 0b1;
  if ~(HaveAnyAArch32()) then assert(~(aarch32), "!(aarch32)") else ();
  if HighestELUsingAArch32() then assert(aarch32, "aarch32") else ();
  return(aarch32)
}

val aset_SPSR : bits(32) -> unit effect {escape, rreg, wreg}

function aset_SPSR value_name = {
  if UsingAArch32() then match PSTATE.M {
    ? if ? == M32_FIQ => SPSR_fiq = value_name,
    ? if ? == M32_IRQ => SPSR_irq = value_name,
    ? if ? == M32_Svc => SPSR_svc = value_name,
    ? if ? == M32_Monitor => SPSR_mon = value_name,
    ? if ? == M32_Abort => SPSR_abt = value_name,
    ? if ? == M32_Hyp => SPSR_hyp = value_name,
    ? if ? == M32_Undef => SPSR_und = value_name,
    _ => Unreachable()
  } else match PSTATE.EL {
    ? if ? == EL1 => SPSR_EL1 = value_name,
    ? if ? == EL2 => SPSR_EL2 = value_name,
    ? if ? == EL3 => SPSR_EL3 = value_name,
    _ => Unreachable()
  };
  ()
}

val aget_SPSR : unit -> bits(32) effect {escape, rreg, undef}

function aget_SPSR () = {
  result : bits(32) = undefined;
  if UsingAArch32() then match PSTATE.M {
    ? if ? == M32_FIQ => result = SPSR_fiq,
    ? if ? == M32_IRQ => result = SPSR_irq,
    ? if ? == M32_Svc => result = SPSR_svc,
    ? if ? == M32_Monitor => result = SPSR_mon,
    ? if ? == M32_Abort => result = SPSR_abt,
    ? if ? == M32_Hyp => result = SPSR_hyp,
    ? if ? == M32_Undef => result = SPSR_und,
    _ => Unreachable()
  } else match PSTATE.EL {
    ? if ? == EL1 => result = SPSR_EL1,
    ? if ? == EL2 => result = SPSR_EL2,
    ? if ? == EL3 => result = SPSR_EL3,
    _ => Unreachable()
  };
  return(result)
}

val IsSecure : unit -> bool effect {escape, rreg, undef}

function IsSecure () = {
  if (HaveEL(EL3) & ~(UsingAArch32())) & PSTATE.EL == EL3 then return(true) else if (HaveEL(EL3) & UsingAArch32()) & PSTATE.M == M32_Monitor then return(true) else ();
  return(IsSecureBelowEL3())
}

val FPProcessException : (FPExc, bits(32)) -> unit effect {escape, rreg, undef, wreg}

function FPProcessException (exception, fpcr) = {
  cumul : int = undefined;
  match exception {
    FPExc_InvalidOp => cumul = 0,
    FPExc_DivideByZero => cumul = 1,
    FPExc_Overflow => cumul = 2,
    FPExc_Underflow => cumul = 3,
    FPExc_Inexact => cumul = 4,
    FPExc_InputDenorm => cumul = 7
  };
  enable : int = cumul + 8;
  if [fpcr[enable]] == 0b1 then throw(Error_Implementation_Defined("floating-point trap handling")) else if UsingAArch32() then FPSCR = __SetSlice_bits(32, 1, FPSCR, cumul, 0b1) else FPSR = __SetSlice_bits(32, 1, FPSR, cumul, 0b1);
  ()
}

val FPRoundBase : forall ('N : Int), 32 >= 0 & 'N >= 0.
  (real, bits(32), FPRounding) -> bits('N) effect {escape, wreg, rreg, undef}

function FPRoundBase (op, fpcr, rounding) = {
  assert('N == 16 | 'N == 32 | 'N == 64);
  assert(op != 0.0);
  assert(rounding != FPRounding_TIEAWAY);
  result : bits('N) = undefined;
  F_mut : int = undefined;
  E_mut : int = undefined;
  minimum_exp : int = undefined;
  if 'N == 16 then {
    minimum_exp = negate(14);
    E_mut = 5;
    F_mut = 10
  } else if 'N == 32 then {
    minimum_exp = negate(126);
    E_mut = 8;
    F_mut = 23
  } else {
    minimum_exp = negate(1022);
    E_mut = 11;
    F_mut = 52
  };
  let 'F = F_mut;
  let 'E = E_mut;
  assert(constraint('F in {10, 23, 52} & 'E in {5, 8, 11}));
  mantissa : real = undefined;
  sign : bits(1) = undefined;
  if op < 0.0 then {
    sign = 0b1;
    mantissa = negate(op)
  } else {
    sign = 0b0;
    mantissa = op
  };
  exponent : int = 0;
  while mantissa < 1.0 do {
    mantissa = mantissa * 2.0;
    exponent = exponent - 1
  };
  while mantissa >= 2.0 do {
    mantissa = mantissa / 2.0;
    exponent = exponent + 1
  };
  if ([fpcr[24]] == 0b1 & 'N != 16 | [fpcr[19]] == 0b1 & 'N == 16) & exponent < minimum_exp then {
    if UsingAArch32() then FPSCR = __SetSlice_bits(32, 1, FPSCR, 3, 0b1)
    else FPSR = __SetSlice_bits(32, 1, FPSR, 3, 0b1);
    return(FPZero(sign))
  } else ();
  biased_exp : int = max((exponent - minimum_exp) + 1, 0);
  if biased_exp == 0 then mantissa = mantissa / 2.0 ^ (minimum_exp - exponent)
  else ();
  int_mant : int = RoundDown(mantissa * 2.0 ^ F);
  error : real = mantissa * 2.0 ^ F - Real(int_mant);
  if biased_exp == 0 & (error != 0.0 | [fpcr[11]] == 0b1) then FPProcessException(FPExc_Underflow, fpcr) else ();
  overflow_to_inf : bool = undefined;
  round_up : bool = undefined;
  match rounding {
    FPRounding_TIEEVEN => {
      round_up = error > 0.5 | error == 0.5 & __GetSlice_int(1, int_mant, 0) == 0b1;
      overflow_to_inf = true
    },
    FPRounding_POSINF => {
      round_up = error != 0.0 & sign == 0b0;
      overflow_to_inf = sign == 0b0
    },
    FPRounding_NEGINF => {
      round_up = error != 0.0 & sign == 0b1;
      overflow_to_inf = sign == 0b1
    },
    FPRounding_ZERO => {
      round_up = false;
      overflow_to_inf = false
    },
    FPRounding_ODD => {
      round_up = false;
      overflow_to_inf = false
    }
  };
  if round_up then {
    int_mant = int_mant + 1;
    if int_mant == pow2(F) then biased_exp = 1
    else ();
    if int_mant == pow2(F + 1) then {
      biased_exp = biased_exp + 1;
      int_mant = int_mant / 2
    } else ()
  } else ();
  if error != 0.0 & rounding == FPRounding_ODD then
    int_mant = __SetSlice_int(1, int_mant, 0, 0b1)
  else ();
  if 'N != 16 | [fpcr[26]] == 0b0 then
    if biased_exp >= pow2(E) - 1 then {
      result = if overflow_to_inf then FPInfinity(sign) else FPMaxNormal(sign);
      FPProcessException(FPExc_Overflow, fpcr);
      error = 1.0
    } else
      result = (sign @ __GetSlice_int(('N - F) - 1, biased_exp, 0)) @ __GetSlice_int(F, int_mant, 0)
  else if biased_exp >= pow2(E) then {
    result = sign @ Ones('N - 1);
    FPProcessException(FPExc_InvalidOp, fpcr);
    error = 0.0
  } else
    result = (sign @ __GetSlice_int(('N - F) - 1, biased_exp, 0)) @ __GetSlice_int(F, int_mant, 0);
  if error != 0.0 then FPProcessException(FPExc_Inexact, fpcr) else ();
  return(result)
}

val FPRoundCV : forall ('N : Int), 32 >= 0 & 'N >= 0.
  (real, bits(32), FPRounding) -> bits('N) effect {escape, rreg, undef, wreg}

function FPRoundCV (op, fpcr__arg, rounding) = {
  fpcr = fpcr__arg;
  fpcr = __SetSlice_bits(32, 1, fpcr, 19, 0b0);
  return(FPRoundBase(op, fpcr, rounding))
}

val FPRound__0 : forall ('N : Int), 32 >= 0 & 'N >= 0.
  (real, bits(32), FPRounding) -> bits('N) effect {escape, rreg, undef, wreg}

val FPRound__1 : forall ('N : Int), 32 >= 0 & 'N >= 0.
  (real, bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

overload FPRound = {FPRound__0, FPRound__1}

function FPRound__0 (op, fpcr__arg, rounding) = {
  fpcr = fpcr__arg;
  fpcr = __SetSlice_bits(32, 1, fpcr, 26, 0b0);
  return(FPRoundBase(op, fpcr, rounding))
}

function FPRound__1 (op, fpcr) = return(FPRound(op, fpcr, FPRoundingMode(fpcr)))

val FixedToFP : forall ('M : Int) ('N : Int), 'M >= 0 & 32 >= 0 & 'N >= 0.
  (bits('M), int, bool, bits(32), FPRounding) -> bits('N) effect {escape, undef, wreg, rreg}

function FixedToFP (op, 'fbits, unsigned, fpcr, rounding) = {
  assert('N == 16 | 'N == 32 | 'N == 64);
  assert('M == 16 | 'M == 32 | 'M == 64);
  result : bits('N) = undefined;
  assert(fbits >= 0);
  assert(rounding != FPRounding_ODD);
  int_operand : int = asl_Int(op, unsigned);
  real_operand : real = Real(int_operand) / 2.0 ^ fbits;
  if real_operand == 0.0 then result = FPZero(0b0)
  else result = FPRound(real_operand, fpcr, rounding);
  return(result)
}

val FPProcessNaN : forall ('N : Int), 'N >= 0 & 32 >= 0 & 'N >= 0.
  (FPType, bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPProcessNaN (typ, op, fpcr) = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  assert(typ == FPType_QNaN | typ == FPType_SNaN, "((type == FPType_QNaN) || (type == FPType_SNaN))");
  topfrac : int = undefined;
  match 'N {
    16 => topfrac = 9,
    32 => topfrac = 22,
    64 => topfrac = 51
  };
  result : bits('N) = op;
  if typ == FPType_SNaN then {
    result = __SetSlice_bits('N, 1, result, topfrac, 0b1);
    FPProcessException(FPExc_InvalidOp, fpcr)
  } else ();
  if [fpcr[25]] == 0b1 then result = FPDefaultNaN() else ();
  return(result)
}

val FPProcessNaNs3 : forall ('N : Int), 'N >= 0 & 'N >= 0 & 'N >= 0 & 32 >= 0 & 'N >= 0.
  (FPType, FPType, FPType, bits('N), bits('N), bits('N), bits(32)) -> (bool, bits('N)) effect {escape, rreg, undef, wreg}

function FPProcessNaNs3 (type1, type2, type3, op1, op2, op3, fpcr) = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  result : bits('N) = undefined;
  done : bool = undefined;
  if type1 == FPType_SNaN then {
    done = true;
    result = FPProcessNaN(type1, op1, fpcr)
  } else if type2 == FPType_SNaN then {
    done = true;
    result = FPProcessNaN(type2, op2, fpcr)
  } else if type3 == FPType_SNaN then {
    done = true;
    result = FPProcessNaN(type3, op3, fpcr)
  } else if type1 == FPType_QNaN then {
    done = true;
    result = FPProcessNaN(type1, op1, fpcr)
  } else if type2 == FPType_QNaN then {
    done = true;
    result = FPProcessNaN(type2, op2, fpcr)
  } else if type3 == FPType_QNaN then {
    done = true;
    result = FPProcessNaN(type3, op3, fpcr)
  } else {
    done = false;
    result = Zeros()
  };
  return((done, result))
}

val FPProcessNaNs : forall ('N : Int), 'N >= 0 & 'N >= 0 & 32 >= 0 & 'N >= 0.
  (FPType, FPType, bits('N), bits('N), bits(32)) -> (bool, bits('N)) effect {escape, rreg, undef, wreg}

function FPProcessNaNs (type1, type2, op1, op2, fpcr) = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  result : bits('N) = undefined;
  done : bool = undefined;
  if type1 == FPType_SNaN then {
    done = true;
    result = FPProcessNaN(type1, op1, fpcr)
  } else if type2 == FPType_SNaN then {
    done = true;
    result = FPProcessNaN(type2, op2, fpcr)
  } else if type1 == FPType_QNaN then {
    done = true;
    result = FPProcessNaN(type1, op1, fpcr)
  } else if type2 == FPType_QNaN then {
    done = true;
    result = FPProcessNaN(type2, op2, fpcr)
  } else {
    done = false;
    result = Zeros()
  };
  return((done, result))
}

val CurrentInstrSet : unit -> InstrSet effect {escape, rreg, undef}

function CurrentInstrSet () = {
  result : InstrSet = undefined;
  if UsingAArch32() then result = if PSTATE.T == 0b0 then InstrSet_A32 else InstrSet_T32 else result = InstrSet_A64;
  return(result)
}

val AArch32_ExecutingLSMInstr : unit -> bool effect {escape, rreg, undef}

function AArch32_ExecutingLSMInstr () = {
  instr : bits(32) = ThisInstr();
  instr_set : InstrSet = CurrentInstrSet();
  assert(instr_set == InstrSet_A32 | instr_set == InstrSet_T32, "((instr_set == InstrSet_A32) || (instr_set == InstrSet_T32))");
  if instr_set == InstrSet_A32 then return(slice(instr, 28, 4) != 0xF & slice(instr, 25, 3) == 0b100) else if ThisInstrLength() == 16 then return(slice(instr, 12, 4) == 0xC) else return(slice(instr, 25, 7) == 0b1110100 & [instr[22]] == 0b0)
}

val AArch32_ExecutingCP10or11Instr : unit -> bool effect {escape, rreg, undef}

function AArch32_ExecutingCP10or11Instr () = {
  instr : bits(32) = ThisInstr();
  instr_set : InstrSet = CurrentInstrSet();
  assert(instr_set == InstrSet_A32 | instr_set == InstrSet_T32, "((instr_set == InstrSet_A32) || (instr_set == InstrSet_T32))");
  if instr_set == InstrSet_A32 then return((slice(instr, 24, 4) == 0xE | slice(instr, 25, 3) == 0b110) & (slice(instr, 8, 4) & 0xE) == 0xA) else return(((slice(instr, 28, 4) & 0xE) == 0xE & (slice(instr, 24, 4) == 0xE | slice(instr, 25, 3) == 0b110)) & (slice(instr, 8, 4) & 0xE) == 0xA)
}

val HaveAnyAArch64 : unit -> bool

function HaveAnyAArch64 () = return(~(HighestELUsingAArch32()))

val AArch32_ReportDeferredSError : (bits(2), bits(1)) -> bits(32) effect {escape, rreg, undef}

function AArch32_ReportDeferredSError (AET, ExT) = {
  target : bits(32) = undefined;
  target : bits(32) = __SetSlice_bits(32, 1, target, 31, 0b1);
  syndrome : bits(16) = Zeros(16);
  if PSTATE.EL == EL2 then {
    syndrome[11 .. 10] = AET;
    syndrome[9 .. 9] = ExT;
    syndrome[5 .. 0] = 0b010001
  } else {
    syndrome[15 .. 14] = AET;
    syndrome[12 .. 12] = ExT;
    syndrome[9 .. 9] = [TTBCR[31]];
    if [TTBCR[31]] == 0b1 then syndrome[5 .. 0] = 0b010001
    else (syndrome[10 .. 10], syndrome[3 .. 0]) = (0b1, 0b0110)
  };
  if HaveAnyAArch64() then target[24 .. 0] = ZeroExtend(syndrome, 25)
  else target[15 .. 0] = syndrome;
  return(target)
}

val HaveAArch32EL : bits(2) -> bool

function HaveAArch32EL el = {
  if ~(HaveEL(el)) then return(false) else if ~(HaveAnyAArch32()) then return(false) else if HighestELUsingAArch32() then return(true) else if el == HighestEL() then return(false) else if el == EL0 then return(true) else ();
  return(true)
}

val AArch64_ResetSpecialRegisters : unit -> unit effect {undef, wreg}

function AArch64_ResetSpecialRegisters () = {
  SP_EL0 = undefined;
  SP_EL1 = undefined;
  SPSR_EL1 = undefined;
  ELR_EL1 = undefined;
  if HaveEL(EL2) then {
    SP_EL2 = undefined;
    SPSR_EL2 = undefined;
    ELR_EL2 = undefined
  } else ();
  if HaveEL(EL3) then {
    SP_EL3 = undefined;
    SPSR_EL3 = undefined;
    ELR_EL3 = undefined
  } else ();
  if HaveAArch32EL(EL1) then {
    SPSR_fiq = undefined;
    SPSR_irq = undefined;
    SPSR_abt = undefined;
    SPSR_und = undefined
  } else ();
  DLR_EL0 = undefined;
  DSPSR_EL0 = undefined;
  ()
}

val Halted : unit -> bool effect {rreg}

function Halted () = return(~(slice(EDSCR, 0, 6) == 0b000001 | slice(EDSCR, 0, 6) == 0b000010))

val FPUnpackBase : forall ('N : Int), 'N >= 0 & 32 >= 0 & 1 >= 0.
  (bits('N), bits(32)) -> (FPType, bits(1), real) effect {escape, rreg, undef, wreg}

function FPUnpackBase (fpval, fpcr) = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  frac64 : bits(52) = undefined;
  exp64 : bits(11) = undefined;
  frac32 : bits(23) = undefined;
  exp32 : bits(8) = undefined;
  value_name : real = undefined;
  typ : FPType = undefined;
  frac16 : bits(10) = undefined;
  exp16 : bits(5) = undefined;
  sign : bits(1) = undefined;
  if 'N == 16 then {
    sign = [fpval[15]];
    exp16 = slice(fpval, 10, 5);
    frac16 = slice(fpval, 0, 10);
    if IsZero(exp16) then if IsZero(frac16) | [fpcr[19]] == 0b1 then {
      typ = FPType_Zero;
      value_name = 0.0
    } else {
      typ = FPType_Nonzero;
      value_name = 2.0 ^ negate(14) * (Real(UInt(frac16)) * 2.0 ^ negate(10))
    } else if IsOnes(exp16) & [fpcr[26]] == 0b0 then if IsZero(frac16) then {
      typ = FPType_Infinity;
      value_name = 2.0 ^ 1000000
    } else {
      typ = if [frac16[9]] == 0b1 then FPType_QNaN else FPType_SNaN;
      value_name = 0.0
    } else {
      typ = FPType_Nonzero;
      value_name = 2.0 ^ (UInt(exp16) - 15) * (1.0 + Real(UInt(frac16)) * 2.0 ^ negate(10))
    }
  } else if 'N == 32 then {
    sign = [fpval[31]];
    exp32 = slice(fpval, 23, 8);
    frac32 = slice(fpval, 0, 23);
    if IsZero(exp32) then if IsZero(frac32) | [fpcr[24]] == 0b1 then {
      typ = FPType_Zero;
      value_name = 0.0;
      if ~(IsZero(frac32)) then FPProcessException(FPExc_InputDenorm, fpcr) else ()
    } else {
      typ = FPType_Nonzero;
      value_name = 2.0 ^ negate(126) * (Real(UInt(frac32)) * 2.0 ^ negate(23))
    } else if IsOnes(exp32) then if IsZero(frac32) then {
      typ = FPType_Infinity;
      value_name = 2.0 ^ 1000000
    } else {
      typ = if [frac32[22]] == 0b1 then FPType_QNaN else FPType_SNaN;
      value_name = 0.0
    } else {
      typ = FPType_Nonzero;
      value_name = 2.0 ^ (UInt(exp32) - 127) * (1.0 + Real(UInt(frac32)) * 2.0 ^ negate(23))
    }
  } else {
    sign = [fpval[63]];
    exp64 = slice(fpval, 52, 11);
    frac64 = slice(fpval, 0, 52);
    if IsZero(exp64) then if IsZero(frac64) | [fpcr[24]] == 0b1 then {
      typ = FPType_Zero;
      value_name = 0.0;
      if ~(IsZero(frac64)) then FPProcessException(FPExc_InputDenorm, fpcr) else ()
    } else {
      typ = FPType_Nonzero;
      value_name = 2.0 ^ negate(1022) * (Real(UInt(frac64)) * 2.0 ^ negate(52))
    } else if IsOnes(exp64) then if IsZero(frac64) then {
      typ = FPType_Infinity;
      value_name = 2.0 ^ 1000000
    } else {
      typ = if [frac64[51]] == 0b1 then FPType_QNaN else FPType_SNaN;
      value_name = 0.0
    } else {
      typ = FPType_Nonzero;
      value_name = 2.0 ^ (UInt(exp64) - 1023) * (1.0 + Real(UInt(frac64)) * 2.0 ^ negate(52))
    }
  };
  if sign == 0b1 then value_name = negate(value_name) else ();
  return((typ, sign, value_name))
}

val FPUnpackCV : forall ('N : Int), 'N >= 0 & 32 >= 0 & 1 >= 0.
  (bits('N), bits(32)) -> (FPType, bits(1), real) effect {escape, rreg, undef, wreg}

function FPUnpackCV (fpval, fpcr__arg) = {
  fpcr = fpcr__arg;
  fpcr = __SetSlice_bits(32, 1, fpcr, 19, 0b0);
  value_name : real = undefined;
  sign : bits(1) = undefined;
  fp_type : FPType = undefined;
  (fp_type, sign, value_name) = FPUnpackBase(fpval, fpcr);
  return((fp_type, sign, value_name))
}

val FPConvert__0 : forall ('N : Int) ('M : Int), 'N >= 0 & 32 >= 0 & 'M >= 0.
  (bits('N), bits(32), FPRounding) -> bits('M) effect {escape, rreg, undef, wreg}

val FPConvert__1 : forall ('N : Int) ('M : Int), 'N >= 0 & 32 >= 0 & 'M >= 0.
  (bits('N), bits(32)) -> bits('M) effect {escape, rreg, undef, wreg}

overload FPConvert = {FPConvert__0, FPConvert__1}

function FPConvert__0 (op, fpcr, rounding) = {
  assert('M == 16 | 'M == 32 | 'M == 64);
  assert('N == 16 | 'N == 32 | 'N == 64);
  result : bits('M) = undefined;
  value_name : real = undefined;
  sign : bits(1) = undefined;
  typ : FPType = undefined;
  (typ, sign, value_name) = FPUnpackCV(op, fpcr);
  alt_hp : bool = 'M == 16 & [fpcr[26]] == 0b1;
  if typ == FPType_SNaN | typ == FPType_QNaN then {
    if alt_hp then result = FPZero(sign)
    else if [fpcr[25]] == 0b1 then result = FPDefaultNaN()
    else result = FPConvertNaN(op);
    if typ == FPType_SNaN | alt_hp then FPProcessException(FPExc_InvalidOp, fpcr) else ()
  } else if typ == FPType_Infinity then
    if alt_hp then {
      result = sign @ Ones('M - 1);
      FPProcessException(FPExc_InvalidOp, fpcr)
    } else result = FPInfinity(sign)
  else if typ == FPType_Zero then result = FPZero(sign)
  else result = FPRoundCV(value_name, fpcr, rounding);
  return(result)
}

function FPConvert__1 (op, fpcr) = return(FPConvert(op, fpcr, FPRoundingMode(fpcr)))

val FPUnpack : forall ('N : Int), 'N >= 0 & 32 >= 0 & 1 >= 0.
  (bits('N), bits(32)) -> (FPType, bits(1), real) effect {escape, rreg, undef, wreg}

function FPUnpack (fpval, fpcr__arg) = {
  fpcr = fpcr__arg;
  fpcr = __SetSlice_bits(32, 1, fpcr, 26, 0b0);
  value_name : real = undefined;
  sign : bits(1) = undefined;
  fp_type : FPType = undefined;
  (fp_type, sign, value_name) = FPUnpackBase(fpval, fpcr);
  return((fp_type, sign, value_name))
}

val FPToFixedJS : forall ('M : Int) ('N : Int), 'M >= 0 & 32 >= 0 & 'N >= 0.
  (bits('M), bits(32), bool) -> bits('N) effect {escape, rreg, undef, wreg}

function FPToFixedJS (op, fpcr, Is64) = {
  assert('M == 64 & 'N == 32, "((M == 64) && (N == 32))");
  value_name : real = undefined;
  sign : bits(1) = undefined;
  typ : FPType = undefined;
  (typ, sign, value_name) = FPUnpack(op, fpcr);
  Z : bits(1) = 0b1;
  if typ == FPType_SNaN | typ == FPType_QNaN then {
    FPProcessException(FPExc_InvalidOp, fpcr);
    Z = 0b0
  } else ();
  int_result : int = RoundDown(value_name);
  error : real = value_name - Real(int_result);
  round_it_up : bool = error != 0.0 & int_result < 0;
  if round_it_up then int_result = int_result + 1 else ();
  result : int = undefined;
  if int_result < 0 then result = int_result - 2 ^ 32 * RoundUp(Real(int_result) / Real(2 ^ 32)) else result = int_result - 2 ^ 32 * RoundDown(Real(int_result) / Real(2 ^ 32));
  if int_result < negate(2 ^ 31) | int_result > 2 ^ 31 - 1 then {
    FPProcessException(FPExc_InvalidOp, fpcr);
    Z = 0b0
  } else if error != 0.0 then {
    FPProcessException(FPExc_Inexact, fpcr);
    Z = 0b0
  } else ();
  if sign == 0b1 & value_name == 0.0 then Z = 0b0 else ();
  if typ == FPType_Infinity then result = 0 else ();
  if Is64 then (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = (0b0 @ Z) @ 0b00 else FPSCR = __SetSlice_bits(32, 4, FPSCR, 28, (0b0 @ Z) @ 0b00);
  return(__GetSlice_int(32, result, 0))
}

val FPToFixed : forall ('N : Int) ('M : Int), 'N >= 0 & 32 >= 0 & 'M >= 0.
  (bits('N), int, bool, bits(32), FPRounding) -> bits('M) effect {escape, rreg, undef, wreg}

function FPToFixed (op, 'fbits, unsigned, fpcr, rounding) = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  assert('M == 16 | 'M == 32 | 'M == 64, "((M == 16) || ((M == 32) || (M == 64)))");
  assert(fbits >= 0, "(fbits >= 0)");
  assert(rounding != FPRounding_ODD, "(rounding != FPRounding_ODD)");
  value_name : real = undefined;
  sign : bits(1) = undefined;
  typ : FPType = undefined;
  (typ, sign, value_name) = FPUnpack(op, fpcr);
  if typ == FPType_SNaN | typ == FPType_QNaN then FPProcessException(FPExc_InvalidOp, fpcr) else ();
  value_name = value_name * 2.0 ^ fbits;
  int_result : int = RoundDown(value_name);
  error : real = value_name - Real(int_result);
  round_up : bool = undefined;
  match rounding {
    FPRounding_TIEEVEN => round_up = error > 0.5 | error == 0.5 & __GetSlice_int(1, int_result, 0) == 0b1,
    FPRounding_POSINF => round_up = error != 0.0,
    FPRounding_NEGINF => round_up = false,
    FPRounding_ZERO => round_up = error != 0.0 & int_result < 0,
    FPRounding_TIEAWAY => round_up = error > 0.5 | error == 0.5 & int_result >= 0
  };
  if round_up then int_result = int_result + 1 else ();
  overflow : bool = undefined;
  result : bits('M) = undefined;
  (result, overflow) = SatQ(int_result, 'M, unsigned);
  if overflow then FPProcessException(FPExc_InvalidOp, fpcr) else if error != 0.0 then FPProcessException(FPExc_Inexact, fpcr) else ();
  return(result)
}

val FPSqrt : forall ('N : Int), 'N >= 0 & 32 >= 0 & 'N >= 0.
  (bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPSqrt (op, fpcr) = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  value_name : real = undefined;
  sign : bits(1) = undefined;
  typ : FPType = undefined;
  (typ, sign, value_name) = FPUnpack(op, fpcr);
  result : bits('N) = undefined;
  if typ == FPType_SNaN | typ == FPType_QNaN then result = FPProcessNaN(typ, op, fpcr) else if typ == FPType_Zero then result = FPZero(sign) else if typ == FPType_Infinity & sign == 0b0 then result = FPInfinity(sign) else if sign == 0b1 then {
    result = FPDefaultNaN();
    FPProcessException(FPExc_InvalidOp, fpcr)
  } else result = FPRound(Sqrt(value_name), fpcr);
  return(result)
}

val FPRoundInt : forall ('N : Int), 'N >= 0 & 32 >= 0 & 'N >= 0.
  (bits('N), bits(32), FPRounding, bool) -> bits('N) effect {escape, rreg, undef, wreg}

function FPRoundInt (op, fpcr, rounding, exact) = {
  assert(rounding != FPRounding_ODD, "(rounding != FPRounding_ODD)");
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  value_name : real = undefined;
  sign : bits(1) = undefined;
  typ : FPType = undefined;
  (typ, sign, value_name) = FPUnpack(op, fpcr);
  real_result : real = undefined;
  round_up : bool = undefined;
  error : real = undefined;
  int_result : int = undefined;
  result : bits('N) = undefined;
  if typ == FPType_SNaN | typ == FPType_QNaN then result = FPProcessNaN(typ, op, fpcr) else if typ == FPType_Infinity then result = FPInfinity(sign) else if typ == FPType_Zero then result = FPZero(sign) else {
    int_result = RoundDown(value_name);
    error = value_name - Real(int_result);
    match rounding {
      FPRounding_TIEEVEN => round_up = error > 0.5 | error == 0.5 & __GetSlice_int(1, int_result, 0) == 0b1,
      FPRounding_POSINF => round_up = error != 0.0,
      FPRounding_NEGINF => round_up = false,
      FPRounding_ZERO => round_up = error != 0.0 & int_result < 0,
      FPRounding_TIEAWAY => round_up = error > 0.5 | error == 0.5 & int_result >= 0
    };
    if round_up then int_result = int_result + 1 else ();
    real_result = Real(int_result);
    if real_result == 0.0 then result = FPZero(sign) else result = FPRound(real_result, fpcr, FPRounding_ZERO);
    if error != 0.0 & exact then FPProcessException(FPExc_Inexact, fpcr) else ()
  };
  return(result)
}

val FPCompare : forall ('N : Int), 'N >= 0 & 'N >= 0 & 32 >= 0 & 4 >= 0.
  (bits('N), bits('N), bool, bits(32)) -> bits(4) effect {escape, rreg, undef, wreg}

function FPCompare (op1, op2, signal_nans, fpcr) = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  value1_name : real = undefined;
  sign1 : bits(1) = undefined;
  type1 : FPType = undefined;
  (type1, sign1, value1_name) = FPUnpack(op1, fpcr);
  value2_name : real = undefined;
  sign2 : bits(1) = undefined;
  type2 : FPType = undefined;
  (type2, sign2, value2_name) = FPUnpack(op2, fpcr);
  result : bits(4) = undefined;
  if ((type1 == FPType_SNaN | type1 == FPType_QNaN) | type2 == FPType_SNaN) | type2 == FPType_QNaN then {
    result = 0x3;
    if (type1 == FPType_SNaN | type2 == FPType_SNaN) | signal_nans then FPProcessException(FPExc_InvalidOp, fpcr) else ()
  } else if value1_name == value2_name then result = 0x6 else if value1_name < value2_name then result = 0x8 else result = 0x2;
  return(result)
}

val FPSub : forall ('N : Int), 'N >= 0 & 'N >= 0 & 32 >= 0 & 'N >= 0.
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPSub (op1, op2, fpcr) = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  rounding : FPRounding = FPRoundingMode(fpcr);
  value1_name : real = undefined;
  sign1 : bits(1) = undefined;
  type1 : FPType = undefined;
  (type1, sign1, value1_name) = FPUnpack(op1, fpcr);
  value2_name : real = undefined;
  sign2 : bits(1) = undefined;
  type2 : FPType = undefined;
  (type2, sign2, value2_name) = FPUnpack(op2, fpcr);
  result : bits('N) = undefined;
  done : bool = undefined;
  (done, result) = FPProcessNaNs(type1, type2, op1, op2, fpcr);
  result_sign : bits(1) = undefined;
  result_value : real = undefined;
  zero2 : bool = undefined;
  zero1 : bool = undefined;
  inf2 : bool = undefined;
  inf1 : bool = undefined;
  if ~(done) then {
    inf1 = type1 == FPType_Infinity;
    inf2 = type2 == FPType_Infinity;
    zero1 = type1 == FPType_Zero;
    zero2 = type2 == FPType_Zero;
    if (inf1 & inf2) & sign1 == sign2 then {
      result = FPDefaultNaN();
      FPProcessException(FPExc_InvalidOp, fpcr)
    } else if inf1 & sign1 == 0b0 | inf2 & sign2 == 0b1 then result = FPInfinity(0b0) else if inf1 & sign1 == 0b1 | inf2 & sign2 == 0b0 then result = FPInfinity(0b1) else if (zero1 & zero2) & sign1 == ~(sign2) then result = FPZero(sign1) else {
      result_value = value1_name - value2_name;
      if result_value == 0.0 then {
        result_sign = if rounding == FPRounding_NEGINF then 0b1 else 0b0;
        result = FPZero(result_sign)
      } else result = FPRound(result_value, fpcr, rounding)
    }
  } else ();
  return(result)
}

val FPMulAdd : forall ('N : Int), 'N >= 0 & 'N >= 0 & 'N >= 0 & 32 >= 0 & 'N >= 0.
  (bits('N), bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPMulAdd (addend, op1, op2, fpcr) = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  rounding : FPRounding = FPRoundingMode(fpcr);
  valueA_name : real = undefined;
  signA : bits(1) = undefined;
  typeA : FPType = undefined;
  (typeA, signA, valueA_name) = FPUnpack(addend, fpcr);
  value1_name : real = undefined;
  sign1 : bits(1) = undefined;
  type1 : FPType = undefined;
  (type1, sign1, value1_name) = FPUnpack(op1, fpcr);
  value2_name : real = undefined;
  sign2 : bits(1) = undefined;
  type2 : FPType = undefined;
  (type2, sign2, value2_name) = FPUnpack(op2, fpcr);
  inf1 : bool = type1 == FPType_Infinity;
  zero1 : bool = type1 == FPType_Zero;
  inf2 : bool = type2 == FPType_Infinity;
  zero2 : bool = type2 == FPType_Zero;
  result : bits('N) = undefined;
  done : bool = undefined;
  (done, result) = FPProcessNaNs3(typeA, type1, type2, addend, op1, op2, fpcr);
  if typeA == FPType_QNaN & (inf1 & zero2 | zero1 & inf2) then {
    result = FPDefaultNaN();
    FPProcessException(FPExc_InvalidOp, fpcr)
  } else ();
  result_sign : bits(1) = undefined;
  result_value : real = undefined;
  zeroP : bool = undefined;
  infP : bool = undefined;
  signP : bits(1) = undefined;
  zeroA : bool = undefined;
  infA : bool = undefined;
  if ~(done) then {
    infA = typeA == FPType_Infinity;
    zeroA = typeA == FPType_Zero;
    signP = sign1 ^ sign2;
    infP = inf1 | inf2;
    zeroP = zero1 | zero2;
    if (inf1 & zero2 | zero1 & inf2) | (infA & infP) & signA != signP then {
      result = FPDefaultNaN();
      FPProcessException(FPExc_InvalidOp, fpcr)
    } else if infA & signA == 0b0 | infP & signP == 0b0 then result = FPInfinity(0b0) else if infA & signA == 0b1 | infP & signP == 0b1 then result = FPInfinity(0b1) else if (zeroA & zeroP) & signA == signP then result = FPZero(signA) else {
      result_value = valueA_name + value1_name * value2_name;
      if result_value == 0.0 then {
        result_sign = if rounding == FPRounding_NEGINF then 0b1 else 0b0;
        result = FPZero(result_sign)
      } else result = FPRound(result_value, fpcr)
    }
  } else ();
  return(result)
}

val FPMul : forall ('N : Int), 'N >= 0 & 'N >= 0 & 32 >= 0 & 'N >= 0.
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPMul (op1, op2, fpcr) = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  value1_name : real = undefined;
  sign1 : bits(1) = undefined;
  type1 : FPType = undefined;
  (type1, sign1, value1_name) = FPUnpack(op1, fpcr);
  value2_name : real = undefined;
  sign2 : bits(1) = undefined;
  type2 : FPType = undefined;
  (type2, sign2, value2_name) = FPUnpack(op2, fpcr);
  result : bits('N) = undefined;
  done : bool = undefined;
  (done, result) = FPProcessNaNs(type1, type2, op1, op2, fpcr);
  zero2 : bool = undefined;
  zero1 : bool = undefined;
  inf2 : bool = undefined;
  inf1 : bool = undefined;
  if ~(done) then {
    inf1 = type1 == FPType_Infinity;
    inf2 = type2 == FPType_Infinity;
    zero1 = type1 == FPType_Zero;
    zero2 = type2 == FPType_Zero;
    if inf1 & zero2 | zero1 & inf2 then {
      result = FPDefaultNaN();
      FPProcessException(FPExc_InvalidOp, fpcr)
    } else if inf1 | inf2 then result = FPInfinity(sign1 ^ sign2) else if zero1 | zero2 then result = FPZero(sign1 ^ sign2) else result = FPRound(value1_name * value2_name, fpcr)
  } else ();
  return(result)
}

val FPMin : forall ('N : Int), 'N >= 0 & 'N >= 0 & 32 >= 0 & 'N >= 0.
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPMin (op1, op2, fpcr) = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  value1_name : real = undefined;
  sign1 : bits(1) = undefined;
  type1 : FPType = undefined;
  (type1, sign1, value1_name) = FPUnpack(op1, fpcr);
  value2_name : real = undefined;
  sign2 : bits(1) = undefined;
  type2 : FPType = undefined;
  (type2, sign2, value2_name) = FPUnpack(op2, fpcr);
  result : bits('N) = undefined;
  done : bool = undefined;
  (done, result) = FPProcessNaNs(type1, type2, op1, op2, fpcr);
  value_name : real = undefined;
  sign : bits(1) = undefined;
  typ : FPType = undefined;
  if ~(done) then {
    if value1_name < value2_name then (typ, sign, value_name) = (type1, sign1, value1_name) else (typ, sign, value_name) = (type2, sign2, value2_name);
    if typ == FPType_Infinity then result = FPInfinity(sign) else if typ == FPType_Zero then {
      sign = sign1 | sign2;
      result = FPZero(sign)
    } else result = FPRound(value_name, fpcr)
  } else ();
  return(result)
}

val FPMinNum : forall ('N : Int), 'N >= 0 & 'N >= 0 & 32 >= 0 & 'N >= 0.
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPMinNum (op1__arg, op2__arg, fpcr) = {
  op1 = op1__arg;
  op2 = op2__arg;
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  __anon2 : real = undefined;
  __anon1 : bits(1) = undefined;
  type1 : FPType = undefined;
  (type1, __anon1, __anon2) = FPUnpack(op1, fpcr);
  __anon4 : real = undefined;
  __anon3 : bits(1) = undefined;
  type2 : FPType = undefined;
  (type2, __anon3, __anon4) = FPUnpack(op2, fpcr);
  if type1 == FPType_QNaN & type2 != FPType_QNaN then op1 = FPInfinity(0b0) else if type1 != FPType_QNaN & type2 == FPType_QNaN then op2 = FPInfinity(0b0) else ();
  return(FPMin(op1, op2, fpcr))
}

val FPMax : forall ('N : Int), 'N >= 0 & 'N >= 0 & 32 >= 0 & 'N >= 0.
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPMax (op1, op2, fpcr) = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  value1_name : real = undefined;
  sign1 : bits(1) = undefined;
  type1 : FPType = undefined;
  (type1, sign1, value1_name) = FPUnpack(op1, fpcr);
  value2_name : real = undefined;
  sign2 : bits(1) = undefined;
  type2 : FPType = undefined;
  (type2, sign2, value2_name) = FPUnpack(op2, fpcr);
  result : bits('N) = undefined;
  done : bool = undefined;
  (done, result) = FPProcessNaNs(type1, type2, op1, op2, fpcr);
  value_name : real = undefined;
  sign : bits(1) = undefined;
  typ : FPType = undefined;
  if ~(done) then {
    if value1_name > value2_name then (typ, sign, value_name) = (type1, sign1, value1_name) else (typ, sign, value_name) = (type2, sign2, value2_name);
    if typ == FPType_Infinity then result = FPInfinity(sign) else if typ == FPType_Zero then {
      sign = sign1 & sign2;
      result = FPZero(sign)
    } else result = FPRound(value_name, fpcr)
  } else ();
  return(result)
}

val FPMaxNum : forall ('N : Int), 'N >= 0 & 'N >= 0 & 32 >= 0 & 'N >= 0.
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPMaxNum (op1__arg, op2__arg, fpcr) = {
  op1 = op1__arg;
  op2 = op2__arg;
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  __anon2 : real = undefined;
  __anon1 : bits(1) = undefined;
  type1 : FPType = undefined;
  (type1, __anon1, __anon2) = FPUnpack(op1, fpcr);
  __anon4 : real = undefined;
  __anon3 : bits(1) = undefined;
  type2 : FPType = undefined;
  (type2, __anon3, __anon4) = FPUnpack(op2, fpcr);
  if type1 == FPType_QNaN & type2 != FPType_QNaN then op1 = FPInfinity(0b1) else if type1 != FPType_QNaN & type2 == FPType_QNaN then op2 = FPInfinity(0b1) else ();
  return(FPMax(op1, op2, fpcr))
}

val FPDiv : forall ('N : Int), 'N >= 0 & 'N >= 0 & 32 >= 0 & 'N >= 0.
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPDiv (op1, op2, fpcr) = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  value1_name : real = undefined;
  sign1 : bits(1) = undefined;
  type1 : FPType = undefined;
  (type1, sign1, value1_name) = FPUnpack(op1, fpcr);
  value2_name : real = undefined;
  sign2 : bits(1) = undefined;
  type2 : FPType = undefined;
  (type2, sign2, value2_name) = FPUnpack(op2, fpcr);
  result : bits('N) = undefined;
  done : bool = undefined;
  (done, result) = FPProcessNaNs(type1, type2, op1, op2, fpcr);
  zero2 : bool = undefined;
  zero1 : bool = undefined;
  inf2 : bool = undefined;
  inf1 : bool = undefined;
  if ~(done) then {
    inf1 = type1 == FPType_Infinity;
    inf2 = type2 == FPType_Infinity;
    zero1 = type1 == FPType_Zero;
    zero2 = type2 == FPType_Zero;
    if inf1 & inf2 | zero1 & zero2 then {
      result = FPDefaultNaN();
      FPProcessException(FPExc_InvalidOp, fpcr)
    } else if inf1 | zero2 then {
      result = FPInfinity(sign1 ^ sign2);
      if ~(inf1) then FPProcessException(FPExc_DivideByZero, fpcr) else ()
    } else if zero1 | inf2 then result = FPZero(sign1 ^ sign2) else result = FPRound(value1_name / value2_name, fpcr)
  } else ();
  return(result)
}

val FPAdd : forall ('N : Int), 'N >= 0 & 'N >= 0 & 32 >= 0 & 'N >= 0.
  (bits('N), bits('N), bits(32)) -> bits('N) effect {escape, rreg, undef, wreg}

function FPAdd (op1, op2, fpcr) = {
  assert('N == 16 | 'N == 32 | 'N == 64, "((N == 16) || ((N == 32) || (N == 64)))");
  rounding : FPRounding = FPRoundingMode(fpcr);
  value1_name : real = undefined;
  sign1 : bits(1) = undefined;
  type1 : FPType = undefined;
  (type1, sign1, value1_name) = FPUnpack(op1, fpcr);
  value2_name : real = undefined;
  sign2 : bits(1) = undefined;
  type2 : FPType = undefined;
  (type2, sign2, value2_name) = FPUnpack(op2, fpcr);
  result : bits('N) = undefined;
  done : bool = undefined;
  (done, result) = FPProcessNaNs(type1, type2, op1, op2, fpcr);
  result_sign : bits(1) = undefined;
  result_value : real = undefined;
  zero2 : bool = undefined;
  zero1 : bool = undefined;
  inf2 : bool = undefined;
  inf1 : bool = undefined;
  if ~(done) then {
    inf1 = type1 == FPType_Infinity;
    inf2 = type2 == FPType_Infinity;
    zero1 = type1 == FPType_Zero;
    zero2 = type2 == FPType_Zero;
    if (inf1 & inf2) & sign1 == ~(sign2) then {
      result = FPDefaultNaN();
      FPProcessException(FPExc_InvalidOp, fpcr)
    } else if inf1 & sign1 == 0b0 | inf2 & sign2 == 0b0 then result = FPInfinity(0b0) else if inf1 & sign1 == 0b1 | inf2 & sign2 == 0b1 then result = FPInfinity(0b1) else if (zero1 & zero2) & sign1 == sign2 then result = FPZero(sign1) else {
      result_value = value1_name + value2_name;
      if result_value == 0.0 then {
        result_sign = if rounding == FPRounding_NEGINF then 0b1 else 0b0;
        result = FPZero(result_sign)
      } else result = FPRound(result_value, fpcr, rounding)
    }
  } else ();
  return(result)
}

val ExternalSecureInvasiveDebugEnabled : unit -> bool effect {escape, rreg, undef}

function ExternalSecureInvasiveDebugEnabled () = {
  if ~(HaveEL(EL3)) & ~(IsSecure()) then return(false) else ();
  return(ExternalInvasiveDebugEnabled() & SPIDEN == HIGH)
}

val ExternalDebugInterruptsDisabled : bits(2) -> bool effect {escape, rreg, undef}

function ExternalDebugInterruptsDisabled target = {
  int_dis : bool = undefined;
  match target {
    ? if ? == EL3 => int_dis = slice(EDSCR, 22, 2) == 0b11 & ExternalSecureInvasiveDebugEnabled(),
    ? if ? == EL2 => int_dis = (slice(EDSCR, 22, 2) & 0b10) == 0b10 & ExternalInvasiveDebugEnabled(),
    ? if ? == EL1 => if IsSecure() then int_dis = (slice(EDSCR, 22, 2) & 0b10) == 0b10 & ExternalSecureInvasiveDebugEnabled() else int_dis = slice(EDSCR, 22, 2) != 0b00 & ExternalInvasiveDebugEnabled()
  };
  return(int_dis)
}

val ELStateUsingAArch32K : (bits(2), bool) -> (bool, bool) effect {rreg, undef}

function ELStateUsingAArch32K (el, secure) = {
  aarch32 : bool = undefined;
  known : bool = true;
  aarch32_at_el1 : bool = undefined;
  aarch32_below_el3 : bool = undefined;
  if ~(HaveAArch32EL(el)) then aarch32 = false else if HighestELUsingAArch32() then aarch32 = true else {
    aarch32_below_el3 = HaveEL(EL3) & [SCR_EL3[10]] == 0b0;
    aarch32_at_el1 = aarch32_below_el3 | ((HaveEL(EL2) & ~(secure)) & [HCR_EL2[31]] == 0b0) & ~(([HCR_EL2[34]] == 0b1 & [HCR_EL2[27]] == 0b1) & HaveVirtHostExt());
    if el == EL0 & ~(aarch32_at_el1) then if PSTATE.EL == EL0 then aarch32 = PSTATE.nRW == 0b1 else known = false else aarch32 = aarch32_below_el3 & el != EL3 | aarch32_at_el1 & (el == EL1 | el == EL0)
  };
  if ~(known) then aarch32 = undefined else ();
  return((known, aarch32))
}

val ELUsingAArch32K : bits(2) -> (bool, bool) effect {escape, rreg, undef}

function ELUsingAArch32K el = return(ELStateUsingAArch32K(el, IsSecureBelowEL3()))

val ELStateUsingAArch32 : (bits(2), bool) -> bool effect {escape, rreg, undef}

function ELStateUsingAArch32 (el, secure) = {
  aarch32 : bool = undefined;
  known : bool = undefined;
  (known, aarch32) = ELStateUsingAArch32K(el, secure);
  assert(known, "known");
  return(aarch32)
}

val ELUsingAArch32 : bits(2) -> bool effect {escape, rreg, undef}

function ELUsingAArch32 el = return(ELStateUsingAArch32(el, IsSecureBelowEL3()))

val UpdateEDSCRFields : unit -> unit effect {escape, rreg, undef, wreg}

function UpdateEDSCRFields () = {
  if ~(Halted()) then {
    EDSCR = __SetSlice_bits(32, 2, EDSCR, 8, 0b00);
    EDSCR = __SetSlice_bits(32, 1, EDSCR, 18, undefined);
    EDSCR = __SetSlice_bits(32, 4, EDSCR, 10, 0xF)
  } else {
    EDSCR = __SetSlice_bits(32, 2, EDSCR, 8, PSTATE.EL);
    EDSCR = __SetSlice_bits(32, 1, EDSCR, 18, if IsSecure() then 0b0 else 0b1);
    RW : bits(4) = undefined;
    RW : bits(4) = __SetSlice_bits(4, 1, RW, 1, if ELUsingAArch32(EL1) then 0b0 else 0b1);
    if PSTATE.EL != EL0 then RW = __SetSlice_bits(4, 1, RW, 0, [RW[1]]) else RW = __SetSlice_bits(4, 1, RW, 0, if UsingAArch32() then 0b0 else 0b1);
    if ~(HaveEL(EL2)) | HaveEL(EL3) & [aget_SCR_GEN()[0]] == 0b0 then RW = __SetSlice_bits(4, 1, RW, 2, [RW[1]]) else RW = __SetSlice_bits(4, 1, RW, 2, if ELUsingAArch32(EL2) then 0b0 else 0b1);
    if ~(HaveEL(EL3)) then RW = __SetSlice_bits(4, 1, RW, 3, [RW[2]]) else RW = __SetSlice_bits(4, 1, RW, 3, if ELUsingAArch32(EL3) then 0b0 else 0b1);
    if [RW[3]] == 0b0 then RW = __SetSlice_bits(4, 3, RW, 0, undefined) else if [RW[2]] == 0b0 then RW = __SetSlice_bits(4, 2, RW, 0, undefined) else if [RW[1]] == 0b0 then RW = __SetSlice_bits(4, 1, RW, 0, undefined) else ();
    EDSCR = __SetSlice_bits(32, 4, EDSCR, 10, RW)
  };
  ()
}

val Halt : bits(6) -> unit effect {wreg, undef, rreg, escape}

function Halt reason = {
  CTI_SignalEvent(CrossTriggerIn_CrossHalt);
  if UsingAArch32() then {
    DLR = ThisInstrAddr();
    DSPSR = GetPSRFromPSTATE();
    DSPSR[21 .. 21] = PSTATE.SS
  } else {
    DLR_EL0 = ThisInstrAddr();
    DSPSR_EL0 = GetPSRFromPSTATE();
    DSPSR_EL0[21 .. 21] = PSTATE.SS
  };
  EDSCR[24 .. 24] = 0b1;
  EDSCR[28 .. 28] = 0b0;
  if IsSecure() then EDSCR[16 .. 16] = 0b0
  else if HaveEL(EL3) then
    EDSCR[16 .. 16] = if ExternalSecureInvasiveDebugEnabled() then 0b0 else 0b1
  else assert([EDSCR[16]] == 0b1, "((EDSCR).SDD == '1')");
  EDSCR[20 .. 20] = 0b0;
  if UsingAArch32() then {
    (PSTATE.SS @ PSTATE.A @ PSTATE.I @ PSTATE.F) = undefined : bits(4);
    PSTATE.IT = 0x00;
    PSTATE.T = 0b1
  } else
    (PSTATE.SS @ PSTATE.D @ PSTATE.A @ PSTATE.I @ PSTATE.F) = undefined : bits(5);
  PSTATE.IL = 0b0;
  StopInstructionPrefetchAndEnableITR();
  EDSCR[5 .. 0] = reason;
  UpdateEDSCRFields();
  ()
}

val aarch64_system_exceptions_debug_halt : unit -> unit effect {escape, rreg, undef, wreg}

function aarch64_system_exceptions_debug_halt () = Halt(DebugHalt_HaltInstruction)

val S2CacheDisabled : AccType -> bool effect {escape, rreg, undef}

function S2CacheDisabled acctype = {
  disable : bits(1) = undefined;
  if ELUsingAArch32(EL2) then disable = if acctype == AccType_IFETCH then [HCR2[1]] else [HCR2[0]] else disable = if acctype == AccType_IFETCH then [HCR_EL2[33]] else [HCR_EL2[32]];
  return(disable == 0b1)
}

val S2ConvertAttrsHints : (bits(2), AccType) -> MemAttrHints effect {escape, rreg, undef}

function S2ConvertAttrsHints (attr, acctype) = {
  assert(~(IsZero(attr)), "!(IsZero(attr))");
  result : MemAttrHints = undefined;
  if S2CacheDisabled(acctype) then {
    result.attrs = MemAttr_NC;
    result.hints = MemHint_No
  } else match attr {
    0b01 => {
      result.attrs = MemAttr_NC;
      result.hints = MemHint_No
    },
    0b10 => {
      result.attrs = MemAttr_WT;
      result.hints = MemHint_RWA
    },
    0b11 => {
      result.attrs = MemAttr_WB;
      result.hints = MemHint_RWA
    }
  };
  result.transient = false;
  return(result)
}

val S2AttrDecode : (bits(2), bits(4), AccType) -> MemoryAttributes effect {escape, rreg, undef}

function S2AttrDecode (SH, attr, acctype) = {
  memattrs : MemoryAttributes = undefined;
  if slice(attr, 2, 2) == 0b00 then {
    memattrs.typ = MemType_Device;
    match slice(attr, 0, 2) {
      0b00 => memattrs.device = DeviceType_nGnRnE,
      0b01 => memattrs.device = DeviceType_nGnRE,
      0b10 => memattrs.device = DeviceType_nGRE,
      0b11 => memattrs.device = DeviceType_GRE
    }
  } else if slice(attr, 0, 2) != 0b00 then {
    memattrs.typ = MemType_Normal;
    memattrs.outer = S2ConvertAttrsHints(slice(attr, 2, 2), acctype);
    memattrs.inner = S2ConvertAttrsHints(slice(attr, 0, 2), acctype);
    memattrs.shareable = [SH[1]] == 0b1;
    memattrs.outershareable = SH == 0b10
  } else memattrs = undefined;
  return(MemAttrDefaults(memattrs))
}

val ELIsInHost : bits(2) -> bool effect {escape, rreg, undef}

function ELIsInHost el = return((((~(IsSecureBelowEL3()) & HaveVirtHostExt()) & ~(ELUsingAArch32(EL2))) & [HCR_EL2[34]] == 0b1) & (el == EL2 | el == EL0 & [HCR_EL2[27]] == 0b1))

val S1TranslationRegime__0 : bits(2) -> bits(2) effect {rreg, undef, escape}

val S1TranslationRegime__1 : unit -> bits(2) effect {rreg, undef, escape}

overload S1TranslationRegime = {S1TranslationRegime__0, S1TranslationRegime__1}

function S1TranslationRegime__0 el = if el != EL0 then return(el) else if (HaveEL(EL3) & ELUsingAArch32(EL3)) & [SCR[0]] == 0b0 then return(EL3) else if HaveVirtHostExt() & ELIsInHost(el) then return(EL2) else return(EL1)

function S1TranslationRegime__1 () = return(S1TranslationRegime(PSTATE.EL))

val aset_FAR__0 : (bits(2), bits(64)) -> unit effect {wreg, escape}

val aset_FAR__1 : bits(64) -> unit effect {wreg, undef, rreg, escape}

overload aset_FAR = {aset_FAR__0, aset_FAR__1}

function aset_FAR__0 (regime, value_name) = {
  r : bits(64) = value_name;
  match regime {
    ? if ? == EL1 => FAR_EL1 = r,
    ? if ? == EL2 => FAR_EL2 = r,
    ? if ? == EL3 => FAR_EL3 = r,
    _ => Unreachable()
  };
  ()
}

function aset_FAR__1 value_name = {
  aset_FAR(S1TranslationRegime(), value_name);
  ()
}

val aset_ESR__0 : (bits(2), bits(32)) -> unit effect {wreg, escape}

val aset_ESR__1 : bits(32) -> unit effect {wreg, rreg, undef, escape}

overload aset_ESR = {aset_ESR__0, aset_ESR__1}

function aset_ESR__0 (regime, value_name) = {
  r : bits(32) = value_name;
  match regime {
    ? if ? == EL1 => ESR_EL1 = r,
    ? if ? == EL2 => ESR_EL2 = r,
    ? if ? == EL3 => ESR_EL3 = r,
    _ => Unreachable()
  };
  ()
}

function aset_ESR__1 value_name = aset_ESR(S1TranslationRegime(), value_name)

val aget_VBAR__0 : bits(2) -> bits(64) effect {rreg, undef, escape}

val aget_VBAR__1 : unit -> bits(64) effect {rreg, undef, escape}

overload aget_VBAR = {aget_VBAR__0, aget_VBAR__1}

function aget_VBAR__0 regime = {
  r : bits(64) = undefined;
  match regime {
    ? if ? == EL1 => r = VBAR_EL1,
    ? if ? == EL2 => r = VBAR_EL2,
    ? if ? == EL3 => r = VBAR_EL3,
    _ => Unreachable()
  };
  return(r)
}

function aget_VBAR__1 () = return(aget_VBAR(S1TranslationRegime()))

val aget_SCTLR__0 : bits(2) -> bits(32) effect {rreg, undef, escape}

val aget_SCTLR__1 : unit -> bits(32) effect {rreg, undef, escape}

overload aget_SCTLR = {aget_SCTLR__0, aget_SCTLR__1}

function aget_SCTLR__0 regime = {
  r : bits(32) = undefined;
  match regime {
    ? if ? == EL1 => r = SCTLR_EL1,
    ? if ? == EL2 => r = SCTLR_EL2,
    ? if ? == EL3 => r = SCTLR_EL3,
    _ => Unreachable()
  };
  return(r)
}

function aget_SCTLR__1 () = return(aget_SCTLR(S1TranslationRegime()))

val BigEndian : unit -> bool effect {escape, rreg, undef}

function BigEndian () = {
  bigend : bool = undefined;
  if UsingAArch32() then bigend = PSTATE.E != 0b0 else if PSTATE.EL == EL0 then bigend = [aget_SCTLR()[24]] != 0b0 else bigend = [aget_SCTLR()[25]] != 0b0;
  return(bigend)
}

val aget_MAIR__0 : bits(2) -> bits(64) effect {rreg, undef, escape}

val aget_MAIR__1 : unit -> bits(64) effect {rreg, undef, escape}

overload aget_MAIR = {aget_MAIR__0, aget_MAIR__1}

function aget_MAIR__0 regime = {
  r : bits(64) = undefined;
  match regime {
    ? if ? == EL1 => r = MAIR_EL1,
    ? if ? == EL2 => r = MAIR_EL2,
    ? if ? == EL3 => r = MAIR_EL3,
    _ => Unreachable()
  };
  return(r)
}

function aget_MAIR__1 () = return(aget_MAIR(S1TranslationRegime()))

val S1CacheDisabled : AccType -> bool effect {escape, rreg, undef}

function S1CacheDisabled acctype = {
  enable : bits(1) = undefined;
  if ELUsingAArch32(S1TranslationRegime()) then if PSTATE.EL == EL2 then enable = if acctype == AccType_IFETCH then [HSCTLR[12]] else [HSCTLR[2]] else enable = if acctype == AccType_IFETCH then [SCTLR[12]] else [SCTLR[2]] else enable = if acctype == AccType_IFETCH then [aget_SCTLR()[12]] else [aget_SCTLR()[2]];
  return(enable == 0b0)
}

val ShortConvertAttrsHints : (bits(2), AccType, bool) -> MemAttrHints effect {escape, rreg, undef}

function ShortConvertAttrsHints (RGN, acctype, secondstage) = {
  result : MemAttrHints = undefined;
  if ~(secondstage) & S1CacheDisabled(acctype) | secondstage & S2CacheDisabled(acctype) then {
    result.attrs = MemAttr_NC;
    result.hints = MemHint_No
  } else match RGN {
    0b00 => {
      result.attrs = MemAttr_NC;
      result.hints = MemHint_No
    },
    0b01 => {
      result.attrs = MemAttr_WB;
      result.hints = MemHint_RWA
    },
    0b10 => {
      result.attrs = MemAttr_WT;
      result.hints = MemHint_RA
    },
    0b11 => {
      result.attrs = MemAttr_WB;
      result.hints = MemHint_RA
    }
  };
  result.transient = false;
  return(result)
}

val WalkAttrDecode : (bits(2), bits(2), bits(2), bool) -> MemoryAttributes effect {escape, rreg, undef}

function WalkAttrDecode (SH, ORGN, IRGN, secondstage) = {
  memattrs : MemoryAttributes = undefined;
  acctype : AccType = AccType_NORMAL;
  memattrs.typ = MemType_Normal;
  memattrs.inner = ShortConvertAttrsHints(IRGN, acctype, secondstage);
  memattrs.outer = ShortConvertAttrsHints(ORGN, acctype, secondstage);
  memattrs.shareable = [SH[1]] == 0b1;
  memattrs.outershareable = SH == 0b10;
  return(MemAttrDefaults(memattrs))
}

val LongConvertAttrsHints : (bits(4), AccType) -> MemAttrHints effect {escape, rreg, undef}

function LongConvertAttrsHints (attrfield, acctype) = {
  assert(~(IsZero(attrfield)), "!(IsZero(attrfield))");
  result : MemAttrHints = undefined;
  if S1CacheDisabled(acctype) then {
    result.attrs = MemAttr_NC;
    result.hints = MemHint_No
  } else if slice(attrfield, 2, 2) == 0b00 then {
    result.attrs = MemAttr_WT;
    result.hints = slice(attrfield, 0, 2);
    result.transient = true
  } else if slice(attrfield, 0, 4) == 0x4 then {
    result.attrs = MemAttr_NC;
    result.hints = MemHint_No;
    result.transient = false
  } else if slice(attrfield, 2, 2) == 0b01 then {
    result.attrs = slice(attrfield, 0, 2);
    result.hints = MemAttr_WB;
    result.transient = true
  } else {
    result.attrs = slice(attrfield, 2, 2);
    result.hints = slice(attrfield, 0, 2);
    result.transient = false
  };
  return(result)
}

val AArch64_S1AttrDecode : (bits(2), bits(3), AccType) -> MemoryAttributes effect {rreg, undef, escape}

function AArch64_S1AttrDecode (SH, attr, acctype) = let 'uattr = ex_nat(UInt(attr)) in {
  memattrs : MemoryAttributes = undefined;
  mair : bits(64) = aget_MAIR();
  index : atom(8 * 'uattr) = 8 * uattr;
  attrfield : bits(8) = mair[7 + index .. index];
  __anon1 : Constraint = undefined;
  if attrfield[7 .. 4] != 0x0 & attrfield[3 .. 0] == 0x0 | attrfield[7 .. 4] == 0x0 & (attrfield[3 .. 0] & 0x3) != 0x0 then
    (__anon1, attrfield) = ConstrainUnpredictableBits(Unpredictable_RESMAIR) : (Constraint, bits(8))
  else ();
  if attrfield[7 .. 4] == 0x0 then {
    memattrs.typ = MemType_Device;
    match attrfield[3 .. 0] {
      0x0 => memattrs.device = DeviceType_nGnRnE,
      0x4 => memattrs.device = DeviceType_nGnRE,
      0x8 => memattrs.device = DeviceType_nGRE,
      0xC => memattrs.device = DeviceType_GRE,
      _ => Unreachable()
    }
  } else if attrfield[3 .. 0] != 0x0 then {
    memattrs.typ = MemType_Normal;
    memattrs.outer = LongConvertAttrsHints(attrfield[7 .. 4], acctype);
    memattrs.inner = LongConvertAttrsHints(attrfield[3 .. 0], acctype);
    memattrs.shareable = [SH[1]] == 0b1;
    memattrs.outershareable = SH == 0b10
  } else Unreachable();
  return(MemAttrDefaults(memattrs))
}

val IsInHost : unit -> bool effect {escape, rreg, undef}

function IsInHost () = return(ELIsInHost(PSTATE.EL))

val aget_CPACR : unit -> bits(32) effect {escape, rreg, undef}

function aget_CPACR () = {
  if IsInHost() then return(CPTR_EL2) else ();
  return(CPACR_EL1)
}

val HasS2Translation : unit -> bool effect {escape, rreg, undef}

function HasS2Translation () = return(((HaveEL(EL2) & ~(IsSecure())) & ~(IsInHost())) & (PSTATE.EL == EL0 | PSTATE.EL == EL1))

val AArch64_SecondStageWalk : (AddressDescriptor, bits(64), AccType, bool, int, bool) -> AddressDescriptor effect {escape, rmem, rreg, undef, wmem}

function AArch64_SecondStageWalk (S1, vaddress, acctype, iswrite, 'size, hwupdatewalk) = {
  assert(HasS2Translation(), "HasS2Translation()");
  s2fs1walk : bool = true;
  wasaligned : bool = true;
  return(AArch64_SecondStageTranslate(S1, vaddress, acctype, iswrite, wasaligned, s2fs1walk, size, hwupdatewalk))
}

val DoubleLockStatus : unit -> bool effect {escape, rreg, undef}

function DoubleLockStatus () = if ELUsingAArch32(EL1) then return(([DBGOSDLR[0]] == 0b1 & [DBGPRCR[0]] == 0b0) & ~(Halted())) else return(([OSDLR_EL1[0]] == 0b1 & [DBGPRCR_EL1[0]] == 0b0) & ~(Halted()))

val HaltingAllowed : unit -> bool effect {escape, rreg, undef}

function HaltingAllowed () = if Halted() | DoubleLockStatus() then return(false) else if IsSecure() then return(ExternalSecureInvasiveDebugEnabled()) else return(ExternalInvasiveDebugEnabled())

val system_exceptions_debug_halt_decode : (bits(3), bits(16), bits(3), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function system_exceptions_debug_halt_decode (opc, imm16, op2, LL) = {
  __unconditional = true;
  if [EDSCR[14]] == 0b0 | ~(HaltingAllowed()) then UndefinedFault() else ();
  aarch64_system_exceptions_debug_halt()
}

val HaltOnBreakpointOrWatchpoint : unit -> bool effect {escape, rreg, undef}

function HaltOnBreakpointOrWatchpoint () = return((HaltingAllowed() & [EDSCR[14]] == 0b1) & [OSLSR_EL1[1]] == 0b0)

val DebugTargetFrom : bool -> bits(2) effect {escape, rreg, undef}

function DebugTargetFrom secure = {
  route_to_el2 : bool = undefined;
  if HaveEL(EL2) & ~(secure) then if ELUsingAArch32(EL2) then route_to_el2 = [HDCR[8]] == 0b1 | [HCR[27]] == 0b1 else route_to_el2 = [MDCR_EL2[8]] == 0b1 | [HCR_EL2[27]] == 0b1 else route_to_el2 = false;
  target : bits(2) = undefined;
  if route_to_el2 then target = EL2 else if (HaveEL(EL3) & HighestELUsingAArch32()) & secure then target = EL3 else target = EL1;
  return(target)
}

val DebugTarget : unit -> bits(2) effect {escape, rreg, undef}

function DebugTarget () = {
  secure : bool = IsSecure();
  return(DebugTargetFrom(secure))
}

val SSAdvance : unit -> unit effect {escape, rreg, undef, wreg}

function SSAdvance () = {
  target : bits(2) = DebugTarget();
  step_enabled : bool = ~(ELUsingAArch32(target)) & [MDSCR_EL1[0]] == 0b1;
  active_not_pending : bool = step_enabled & PSTATE.SS == 0b1;
  if active_not_pending then PSTATE.SS = 0b0 else ();
  ()
}

val ConditionHolds : bits(4) -> bool effect {rreg, undef}

function ConditionHolds cond = {
  result : bool = undefined;
  match slice(cond, 1, 3) {
    0b000 => result = PSTATE.Z == 0b1,
    0b001 => result = PSTATE.C == 0b1,
    0b010 => result = PSTATE.N == 0b1,
    0b011 => result = PSTATE.V == 0b1,
    0b100 => result = PSTATE.C == 0b1 & PSTATE.Z == 0b0,
    0b101 => result = PSTATE.N == PSTATE.V,
    0b110 => result = PSTATE.N == PSTATE.V & PSTATE.Z == 0b0,
    0b111 => result = true
  };
  if [cond[0]] == 0b1 & cond != 0xF then result = ~(result) else ();
  return(result)
}

val aarch64_integer_conditional_select : (bits(4), int, int, bool, bool, int, int) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_conditional_select (condition, 'd, 'datasize, else_inc, else_inv, 'm, 'n) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  result : bits('datasize) = undefined;
  operand1 : bits('datasize) = aget_X(n);
  operand2 : bits('datasize) = aget_X(m);
  if ConditionHolds(condition) then result = operand1 else {
    result = operand2;
    if else_inv then result = ~(result) else ();
    if else_inc then result = result + 1 else ()
  };
  aset_X(d, result)
}

val integer_conditional_select_decode : (bits(1), bits(1), bits(1), bits(5), bits(4), bits(1), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_conditional_select_decode (sf, op, S, Rm, cond, o2, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  let 'datasize : {|64, 32|} = if sf == 0b1 then 64 else 32;
  condition : bits(4) = cond;
  else_inv : bool = op == 0b1;
  else_inc : bool = o2 == 0b1;
  aarch64_integer_conditional_select(condition, d, datasize, else_inc, else_inv, m, n)
}

val aarch64_integer_conditional_compare_register : (bits(4), int, bits(4), int, int, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_conditional_compare_register (condition, 'datasize, flags__arg, 'm, 'n, sub_op) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  flags = flags__arg;
  operand1 : bits('datasize) = aget_X(n);
  operand2 : bits('datasize) = aget_X(m);
  carry_in : bits(1) = 0b0;
  __anon1 : bits('datasize) = undefined;
  if ConditionHolds(condition) then {
    if sub_op then {
      operand2 = ~(operand2);
      carry_in = 0b1
    } else ();
    (__anon1, flags) = AddWithCarry(operand1, operand2, carry_in)
  } else ();
  (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = flags
}

val integer_conditional_compare_register_decode : (bits(1), bits(1), bits(1), bits(5), bits(4), bits(1), bits(5), bits(1), bits(4)) -> unit effect {escape, rreg, undef, wreg}

function integer_conditional_compare_register_decode (sf, op, S, Rm, cond, o2, Rn, o3, nzcv) = {
  __unconditional = true;
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  let 'datasize : {|64, 32|} = if sf == 0b1 then 64 else 32;
  sub_op : bool = op == 0b1;
  condition : bits(4) = cond;
  flags : bits(4) = nzcv;
  aarch64_integer_conditional_compare_register(condition, datasize, flags, m, n, sub_op)
}

val aarch64_integer_conditional_compare_immediate : forall ('datasize : Int).
  (bits(4), atom('datasize), bits(4), bits('datasize), int, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_conditional_compare_immediate (condition, datasize, flags__arg, imm, 'n, sub_op) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  flags = flags__arg;
  operand1 : bits('datasize) = aget_X(n);
  operand2 : bits('datasize) = imm;
  carry_in : bits(1) = 0b0;
  __anon1 : bits('datasize) = undefined;
  if ConditionHolds(condition) then {
    if sub_op then {
      operand2 = ~(operand2);
      carry_in = 0b1
    } else ();
    (__anon1, flags) = AddWithCarry(operand1, operand2, carry_in)
  } else ();
  (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = flags
}

val integer_conditional_compare_immediate_decode : (bits(1), bits(1), bits(1), bits(5), bits(4), bits(1), bits(5), bits(1), bits(4)) -> unit effect {escape, wreg, undef, rreg}

function integer_conditional_compare_immediate_decode (sf, op, S, imm5, cond, o2, Rn, o3, nzcv) = {
  __unconditional = true;
  n : int = UInt(Rn);
  let 'datasize : {|64, 32|} = if sf == 0b1 then 64 else 32;
  sub_op : bool = op == 0b1;
  condition : bits(4) = cond;
  flags : bits(4) = nzcv;
  imm : bits('datasize) = ZeroExtend(imm5, datasize);
  aarch64_integer_conditional_compare_immediate(condition, datasize, flags, imm, n, sub_op)
}

val ConditionSyndrome : unit -> bits(5) effect {escape, rreg, undef}

function ConditionSyndrome () = {
  syndrome : bits(5) = undefined;
  cond : bits(4) = undefined;
  if UsingAArch32() then {
    cond = AArch32_CurrentCond();
    if PSTATE.T == 0b0 then {
      syndrome = __SetSlice_bits(5, 1, syndrome, 4, 0b1);
      if ConditionHolds(cond) & ConstrainUnpredictableBool(Unpredictable_ESRCONDPASS) then syndrome = __SetSlice_bits(5, 4, syndrome, 0, 0xE) else syndrome = __SetSlice_bits(5, 4, syndrome, 0, cond)
    } else if __IMPDEF_boolean("Condition valid for trapped T32") then {
      syndrome = __SetSlice_bits(5, 1, syndrome, 4, 0b1);
      syndrome = __SetSlice_bits(5, 4, syndrome, 0, cond)
    } else {
      syndrome = __SetSlice_bits(5, 1, syndrome, 4, 0b0);
      syndrome = __SetSlice_bits(5, 4, syndrome, 0, undefined)
    }
  } else {
    syndrome = __SetSlice_bits(5, 1, syndrome, 4, 0b1);
    syndrome = __SetSlice_bits(5, 4, syndrome, 0, 0xE)
  };
  return(syndrome)
}

val BranchToAddr : forall ('N : Int), 'N >= 0.
  (bits('N), BranchType) -> unit effect {escape, rreg, wreg}

function BranchToAddr (target, branch_type) = {
  __BranchTaken = true;
  Hint_Branch(branch_type);
  if 'N == 32 then {
    assert(UsingAArch32(), "UsingAArch32()");
    _PC = ZeroExtend(target)
  } else {
    assert('N == 64 & ~(UsingAArch32()), "((N == 64) && !(UsingAArch32()))");
    _PC = slice(target, 0, 64)
  };
  ()
}

val BadMode : bits(5) -> bool effect {undef}

function BadMode mode = {
  valid_name : bool = undefined;
  match mode {
    ? if ? == M32_Monitor => valid_name = HaveAArch32EL(EL3),
    ? if ? == M32_Hyp => valid_name = HaveAArch32EL(EL2),
    ? if ? == M32_FIQ => valid_name = HaveAArch32EL(EL1),
    ? if ? == M32_IRQ => valid_name = HaveAArch32EL(EL1),
    ? if ? == M32_Svc => valid_name = HaveAArch32EL(EL1),
    ? if ? == M32_Abort => valid_name = HaveAArch32EL(EL1),
    ? if ? == M32_Undef => valid_name = HaveAArch32EL(EL1),
    ? if ? == M32_System => valid_name = HaveAArch32EL(EL1),
    ? if ? == M32_User => valid_name = HaveAArch32EL(EL0),
    _ => valid_name = false
  };
  return(~(valid_name))
}

val aset_Rmode : (int, bits(5), bits(32)) -> unit effect {wreg, rreg, undef, escape}

function aset_Rmode (n, mode, value_name) = {
  assert(n >= 0 & n <= 14, "((n >= 0) && (n <= 14))");
  if ~(IsSecure()) then assert(mode != M32_Monitor, "(mode != M32_Monitor)") else ();
  assert(~(BadMode(mode)), "!(BadMode(mode))");
  if mode == M32_Monitor then
    if n == 13 then SP_mon = value_name
    else if n == 14 then LR_mon = value_name
    else {
      __tmp_1 : bits(64) = _R[n];
      __tmp_1[31 .. 0] = value_name;
      _R[n] = __tmp_1
    }
  else if ~(HighestELUsingAArch32()) & ConstrainUnpredictableBool(Unpredictable_ZEROUPPER) then
    _R[LookUpRIndex(n, mode)] = ZeroExtend(value_name, 64)
  else {
    __tmp_2 : bits(64) = _R[LookUpRIndex(n, mode)];
    __tmp_2[31 .. 0] = value_name;
    _R[LookUpRIndex(n, mode)] = __tmp_2
  };
  ()
}

val aset_R : (int, bits(32)) -> unit effect {escape, rreg, undef, wreg}

function aset_R ('n, value_name) = {
  aset_Rmode(n, PSTATE.M, value_name);
  ()
}

val set_LR : bits(32) -> unit effect {escape, rreg, undef, wreg}

function set_LR value_name = {
  aset_R(14, value_name);
  ()
}

val ELFromM32 : bits(5) -> (bool, bits(2)) effect {escape, rreg, undef}

function ELFromM32 mode = {
  el : bits(2) = undefined;
  valid_name : bool = ~(BadMode(mode));
  match mode {
    ? if ? == M32_Monitor => el = EL3,
    ? if ? == M32_Hyp => {
      el = EL2;
      valid_name = valid_name & (~(HaveEL(EL3)) | [aget_SCR_GEN()[0]] == 0b1)
    },
    ? if ? == M32_FIQ => el = if (HaveEL(EL3) & HighestELUsingAArch32()) & [SCR[0]] == 0b0 then EL3 else EL1,
    ? if ? == M32_IRQ => el = if (HaveEL(EL3) & HighestELUsingAArch32()) & [SCR[0]] == 0b0 then EL3 else EL1,
    ? if ? == M32_Svc => el = if (HaveEL(EL3) & HighestELUsingAArch32()) & [SCR[0]] == 0b0 then EL3 else EL1,
    ? if ? == M32_Abort => el = if (HaveEL(EL3) & HighestELUsingAArch32()) & [SCR[0]] == 0b0 then EL3 else EL1,
    ? if ? == M32_Undef => el = if (HaveEL(EL3) & HighestELUsingAArch32()) & [SCR[0]] == 0b0 then EL3 else EL1,
    ? if ? == M32_System => el = if (HaveEL(EL3) & HighestELUsingAArch32()) & [SCR[0]] == 0b0 then EL3 else EL1,
    ? if ? == M32_User => el = EL0,
    _ => valid_name = false
  };
  if ~(valid_name) then el = undefined else ();
  return((valid_name, el))
}

val ELFromSPSR : bits(32) -> (bool, bits(2)) effect {escape, rreg, undef}

function ELFromSPSR spsr = {
  valid_name : bool = undefined;
  el : bits(2) = undefined;
  if [spsr[4]] == 0b0 then {
    el = slice(spsr, 2, 2);
    if HighestELUsingAArch32() then valid_name = false else if ~(HaveEL(el)) then valid_name = false else if [spsr[1]] == 0b1 then valid_name = false else if el == EL0 & [spsr[0]] == 0b1 then valid_name = false else if (el == EL2 & HaveEL(EL3)) & [SCR_EL3[0]] == 0b0 then valid_name = false else valid_name = true
  } else if ~(HaveAnyAArch32()) then valid_name = false else (valid_name, el) = ELFromM32(slice(spsr, 0, 5));
  if ~(valid_name) then el = undefined else ();
  return((valid_name, el))
}

val IllegalExceptionReturn : bits(32) -> bool effect {escape, rreg, undef}

function IllegalExceptionReturn spsr = {
  target : bits(2) = undefined;
  valid_name : bool = undefined;
  (valid_name, target) = ELFromSPSR(spsr);
  if ~(valid_name) then return(true) else ();
  if UInt(target) > UInt(PSTATE.EL) then return(true) else ();
  spsr_mode_is_aarch32 : bool = [spsr[4]] == 0b1;
  target_el_is_aarch32 : bool = undefined;
  known : bool = undefined;
  (known, target_el_is_aarch32) = ELUsingAArch32K(target);
  assert(known | target == EL0 & ~(ELUsingAArch32(EL1)), "(known || ((target == EL0) && !(ELUsingAArch32(EL1))))");
  if known & spsr_mode_is_aarch32 != target_el_is_aarch32 then return(true) else ();
  if UsingAArch32() & ~(spsr_mode_is_aarch32) then return(true) else ();
  if ((HaveEL(EL2) & target == EL1) & ~(IsSecureBelowEL3())) & [HCR_EL2[27]] == 0b1 then return(true) else ();
  return(false)
}

val AArch32_WriteMode : bits(5) -> unit effect {escape, rreg, undef, wreg}

function AArch32_WriteMode mode = {
  el : bits(2) = undefined;
  valid_name : bool = undefined;
  (valid_name, el) = ELFromM32(mode);
  assert(valid_name, "valid");
  PSTATE.M = mode;
  PSTATE.EL = el;
  PSTATE.nRW = 0b1;
  PSTATE.SP = if mode == M32_User | mode == M32_System then 0b0 else 0b1;
  ()
}

val AddrTop : (bits(64), bool, bits(2)) -> int effect {escape, rreg, undef}

function AddrTop (address, IsInstr, el) = {
  assert(HaveEL(el), "HaveEL(el)");
  regime : bits(2) = S1TranslationRegime(el);
  tbid : bits(1) = undefined;
  tbi : bits(1) = undefined;
  if ELUsingAArch32(regime) then return(31) else match regime {
    ? if ? == EL1 => {
      tbi = if [address[55]] == 0b1 then [TCR_EL1[38]] else [TCR_EL1[37]];
      if HavePACExt() then tbid = if [address[55]] == 0b1 then [TCR_EL1[52]] else [TCR_EL1[51]] else ()
    },
    ? if ? == EL2 => if HaveVirtHostExt() & ELIsInHost(el) then {
      tbi = if [address[55]] == 0b1 then [TCR_EL2[38]] else [TCR_EL2[37]];
      if HavePACExt() then tbid = if [address[55]] == 0b1 then [TCR_EL2[52]] else [TCR_EL2[51]] else ()
    } else {
      tbi = [TCR_EL2[20]];
      if HavePACExt() then tbid = [TCR_EL2[29]] else ()
    },
    ? if ? == EL3 => {
      tbi = [TCR_EL3[20]];
      if HavePACExt() then tbid = [TCR_EL3[29]] else ()
    }
  };
  return(if tbi == 0b1 & ((~(HavePACExt()) | tbid == 0b0) | ~(IsInstr)) then 55 else 63)
}

val AddPAC : (bits(64), bits(64), bits(128), bool) -> bits(64) effect {escape, wreg, rreg, undef}

function AddPAC (ptr, modifier, K, data) = {
  PAC : bits(64) = undefined;
  result : bits(64) = undefined;
  ext_ptr : bits(64) = undefined;
  extfield : bits(64) = undefined;
  selbit : bits(1) = undefined;
  tbi : bool = CalculateTBI(ptr, data);
  let 'top_bit : {|55, 63|} = if tbi then 55 else 63;
  if PtrHasUpperAndLowerAddRanges() then
    if IsEL1TransRegimeRegs() then
      if data then
        selbit = if [TCR_EL1[38]] == 0b1 | [TCR_EL1[37]] == 0b1 then [ptr[55]] else [ptr[63]]
      else if [TCR_EL1[38]] == 0b1 & [TCR_EL1[52]] == 0b0 | [TCR_EL1[37]] == 0b1 & [TCR_EL1[51]] == 0b0 then
        selbit = [ptr[55]]
      else selbit = [ptr[63]]
    else if data then
      selbit = if HaveEL(EL2) & [TCR_EL2[38]] == 0b1 | HaveEL(EL2) & [TCR_EL2[37]] == 0b1 then [ptr[55]] else [ptr[63]]
    else
      selbit = if (HaveEL(EL2) & [TCR_EL2[38]] == 0b1) & [TCR_EL1[52]] == 0b0 | (HaveEL(EL2) & [TCR_EL2[37]] == 0b1) & [TCR_EL1[51]] == 0b0 then [ptr[55]] else [ptr[63]]
  else selbit = if tbi then [ptr[55]] else [ptr[63]];
  let 'bottom_PAC_bit : {'n, true. atom('n)} = ex_int(CalculateBottomPACBit(ptr, selbit));
  assert(constraint('bottom_PAC_bit <= 55));
  extfield = replicate_bits(selbit, 64);
  if tbi then
    ext_ptr = (ptr[63 .. 56] @ extfield[(negate(bottom_PAC_bit) + 56) - 1 .. 0]) @ ptr[bottom_PAC_bit - 1 .. 0]
  else
    ext_ptr = extfield[(negate(bottom_PAC_bit) + 64) - 1 .. 0] @ ptr[bottom_PAC_bit - 1 .. 0];
  PAC = ComputePAC(ext_ptr, modifier, K[127 .. 64], K[63 .. 0]);
  if ~(IsZero(ptr[(((top_bit - bottom_PAC_bit) + 1) - 1) + bottom_PAC_bit .. bottom_PAC_bit])) & ~(IsOnes(ptr[(((top_bit - bottom_PAC_bit) + 1) - 1) + bottom_PAC_bit .. bottom_PAC_bit])) then
    PAC[top_bit - 1 .. top_bit - 1] = ~([PAC[top_bit - 1]])
  else ();
  if tbi then
    result = ((ptr[63 .. 56] @ selbit) @ PAC[((negate(bottom_PAC_bit) + 55) - 1) + bottom_PAC_bit .. bottom_PAC_bit]) @ ptr[bottom_PAC_bit - 1 .. 0]
  else
    result = ((PAC[63 .. 56] @ selbit) @ PAC[((negate(bottom_PAC_bit) + 55) - 1) + bottom_PAC_bit .. bottom_PAC_bit]) @ ptr[bottom_PAC_bit - 1 .. 0];
  return(result)
}

val AArch64_vESBOperation : unit -> unit effect {escape, rreg, undef, wreg}

function AArch64_vESBOperation () = {
  assert((HaveEL(EL2) & ~(IsSecure())) & (PSTATE.EL == EL0 | PSTATE.EL == EL1), "((HaveEL(EL2) && !(IsSecure())) && (((PSTATE).EL == EL0) || ((PSTATE).EL == EL1)))");
  vSEI_enabled : bool = [HCR_EL2[27]] == 0b0 & [HCR_EL2[5]] == 0b1;
  vSEI_pending : bool = vSEI_enabled & [HCR_EL2[8]] == 0b1;
  vintdis : bool = Halted() | ExternalDebugInterruptsDisabled(EL1);
  vmasked : bool = vintdis | PSTATE.A == 0b1;
  VDISR_EL2 : bits(64) = undefined;
  VDISR : bits(32) = undefined;
  if vSEI_pending & vmasked then {
    if ELUsingAArch32(EL1) then VDISR = AArch32_ReportDeferredSError(slice(VDFSR, 14, 2), [VDFSR[12]]) else VDISR_EL2 = AArch64_ReportDeferredSError(slice(VSESR_EL2, 0, 25));
    HCR_EL2 = __SetSlice_bits(64, 1, HCR_EL2, 8, 0b0)
  } else ();
  ()
}

val AArch64_WatchpointByteMatch : (int, bits(64)) -> bool effect {rreg, undef, escape}

function AArch64_WatchpointByteMatch (n, vaddress) = let 'top : {'n, true. atom('n)} = AddrTop(vaddress, false, PSTATE.EL) in {
  bottom : int = if [DBGWVR_EL1[n][2]] == 0b1 then 2 else 3;
  byte_select_match : bool = [DBGWCR_EL1[n][12 .. 5][UInt(vaddress[bottom - 1 .. 0])]] != 0b0;
  mask : int = UInt(DBGWCR_EL1[n][28 .. 24]);
  MSB : bits(8) = undefined;
  LSB : bits(8) = undefined;
  if mask > 0 & ~(IsOnes(DBGWCR_EL1[n][12 .. 5])) then
    byte_select_match = ConstrainUnpredictableBool(Unpredictable_WPMASKANDBAS)
  else {
    LSB = DBGWCR_EL1[n][12 .. 5] & ~(DBGWCR_EL1[n][12 .. 5] - 1);
    MSB = DBGWCR_EL1[n][12 .. 5] + LSB;
    if ~(IsZero(MSB & MSB - 1)) then {
      byte_select_match = ConstrainUnpredictableBool(Unpredictable_WPBASCONTIGUOUS);
      bottom = 3
    } else ()
  };
  c : Constraint = undefined;
  if mask > 0 & mask <= 2 then {
    (c, mask) = ConstrainUnpredictableInteger(3, 31, Unpredictable_RESWPMASK);
    assert(c == Constraint_DISABLED | c == Constraint_NONE | c == Constraint_UNKNOWN, "((c == Constraint_DISABLED) || ((c == Constraint_NONE) || (c == Constraint_UNKNOWN)))");
    match c {
      Constraint_DISABLED => return(false),
      Constraint_NONE => mask = 0
    }
  } else ();
  WVR_match : bool = undefined;
  let 'mask2 : {'n, true. atom('n)} = ex_int(mask);
  let 'bottom2 : {'n, true. atom('n)} = ex_int(bottom);
  if mask > bottom then {
    assert(constraint('mask2 >= 'bottom2 + 1));
    WVR_match = vaddress[(((top - mask2) + 1) - 1) + mask2 .. mask2] == DBGWVR_EL1[n][(((top - mask2) + 1) - 1) + mask2 .. mask2];
    if WVR_match & ~(IsZero(DBGWVR_EL1[n][((mask2 - bottom2) - 1) + bottom2 .. bottom2])) then
      WVR_match = ConstrainUnpredictableBool(Unpredictable_WPMASKEDBITS)
    else ()
  } else
    WVR_match = vaddress[(((top - bottom2) + 1) - 1) + bottom2 .. bottom2] == DBGWVR_EL1[n][(((top - bottom2) + 1) - 1) + bottom2 .. bottom2];
  return(WVR_match & byte_select_match)
}

val IsZero_slice : forall 'n, 'n >= 0.
  (bits('n), int, int) -> bool effect {escape}

function IsZero_slice (xs, i, 'l) = {
  assert(constraint('l >= 0));
  IsZero(xs & slice_mask(i, l))
}

val IsOnes_slice : forall 'n, 'n >= 0.
  (bits('n), int, int) -> bool effect {escape}

function IsOnes_slice (xs, i, 'l) = {
  assert(constraint('l >= 0));
  let m : bits('n) = slice_mask(i,l) in
  (xs & m) == m
}

val ZeroExtend_slice_append : forall 'n 'm 'o, 'n >= 0 & 'm >= 0 & 'o >= 0.
  (bits('n), int, int, bits('m)) -> bits('o) effect {escape}

function ZeroExtend_slice_append (xs, i, 'l, ys) = {
  assert(constraint('l >= 0));
  let xs = xs & slice_mask(i,l) in
  let xs : bits('o) = extzv(xs >> i) << 'm in
  let ys : bits('o) = extzv(ys) in
  xs | ys
}

val AArch64_TranslationTableWalk : (bits(52), bits(64), AccType, bool, bool, bool, int) -> TLBRecord effect {escape, rreg, rmem, wmem, undef}

function AArch64_TranslationTableWalk (ipaddress, vaddress, acctype, iswrite, secondstage, s2fs1walk, 'size) = {
  if ~(secondstage) then assert(~(ELUsingAArch32(S1TranslationRegime()))) else assert(((HaveEL(EL2) & ~(IsSecure())) & ~(ELUsingAArch32(EL2))) & HasS2Translation());
  result : TLBRecord = undefined;
  descaddr : AddressDescriptor = undefined;
  baseregister : bits(64) = undefined;
  inputaddr : bits(64) = undefined;
  /* Initialise typ field of FaultRecord; otherwise, there might be an
   * read of the uninitialised value that can lead to an early return with a
   * fault (when checking the return value of the second stage translation in
   * the loop below, if second stage translation is disabled).  This looks like
   * a bug in the ASL specification. */
  __tmp_17 : FaultRecord = descaddr.fault;
  __tmp_17.typ = Fault_None;
  descaddr.fault = __tmp_17;
  __tmp_18 : MemoryAttributes = descaddr.memattrs;
  __tmp_18.typ = MemType_Normal;
  descaddr.memattrs = __tmp_18;
  startsizecheck : int = undefined;
  inputsizecheck : int = undefined;
  startlevel : int = undefined;
  level : int = undefined;
  stride : int = undefined;
  firstblocklevel : int = undefined;
  grainsize : int = undefined;
  hierattrsdisabled : bool = undefined;
  update_AP : bool = undefined;
  update_AF : bool = undefined;
  singlepriv : bool = undefined;
  lookupsecure : bool = undefined;
  reversedescriptors : bool = undefined;
  disabled : bool = undefined;
  basefound : bool = undefined;
  ps : bits(3) = undefined;
  inputsize_min : int = undefined;
  c : Constraint = undefined;
  inputsize_max : int = undefined;
  inputsize : int = undefined;
  midgrain : bool = undefined;
  largegrain : bool = undefined;
  top : int = undefined;
  if ~(secondstage) then {
    inputaddr = ZeroExtend(vaddress);
    top = AddrTop(inputaddr, acctype == AccType_IFETCH, PSTATE.EL);
    if PSTATE.EL == EL3 then {
      largegrain = slice(TCR_EL3, 14, 2) == 0b01;
      midgrain = slice(TCR_EL3, 14, 2) == 0b10;
      inputsize = 64 - UInt(slice(TCR_EL3, 0, 6));
      inputsize_max = if Have52BitVAExt() & largegrain then 52 else 48;
      if inputsize > inputsize_max then {
        c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
        assert(c == Constraint_FORCE | c == Constraint_FAULT);
        if c == Constraint_FORCE then inputsize = inputsize_max
        else ()
      } else ();
      inputsize_min = 64 - 39;
      if inputsize < inputsize_min then {
        c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
        assert(c == Constraint_FORCE | c == Constraint_FAULT);
        if c == Constraint_FORCE then inputsize = inputsize_min
        else ()
      } else ();
      ps = slice(TCR_EL3, 16, 3);
      basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsZero_slice(inputaddr, inputsize, (top - inputsize) + 1);
      disabled = false;
      baseregister = TTBR0_EL3;
      descaddr.memattrs = WalkAttrDecode(slice(TCR_EL3, 12, 2), slice(TCR_EL3, 10, 2), slice(TCR_EL3, 8, 2), secondstage);
      reversedescriptors = [SCTLR_EL3[25]] == 0b1;
      lookupsecure = true;
      singlepriv = true;
      update_AF = HaveAccessFlagUpdateExt() & [TCR_EL3[21]] == 0b1;
      update_AP = (HaveDirtyBitModifierExt() & update_AF) & [TCR_EL3[22]] == 0b1;
      hierattrsdisabled = AArch64_HaveHPDExt() & [TCR_EL3[24]] == 0b1
    } else if IsInHost() then {
      if [inputaddr[top]] == 0b0 then {
        largegrain = slice(TCR_EL2, 14, 2) == 0b01;
        midgrain = slice(TCR_EL2, 14, 2) == 0b10;
        inputsize = 64 - UInt(slice(TCR_EL2, 0, 6));
        inputsize_max = if Have52BitVAExt() & largegrain then 52 else 48;
        if inputsize > inputsize_max then {
          c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
          assert(c == Constraint_FORCE | c == Constraint_FAULT);
          if c == Constraint_FORCE then inputsize = inputsize_max
          else ()
        } else ();
        inputsize_min = 64 - 39;
        if inputsize < inputsize_min then {
          c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
          assert(c == Constraint_FORCE | c == Constraint_FAULT);
          if c == Constraint_FORCE then inputsize = inputsize_min
          else ()
        } else ();
        basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsZero_slice(inputaddr, inputsize, (top - inputsize) + 1);
        disabled = [TCR_EL2[7]] == 0b1;
        baseregister = TTBR0_EL2;
        descaddr.memattrs = WalkAttrDecode(slice(TCR_EL2, 12, 2), slice(TCR_EL2, 10, 2), slice(TCR_EL2, 8, 2), secondstage);
        hierattrsdisabled = AArch64_HaveHPDExt() & [TCR_EL2[41]] == 0b1
      } else {
        inputsize = 64 - UInt(slice(TCR_EL2, 16, 6));
        largegrain = slice(TCR_EL2, 30, 2) == 0b11;
        midgrain = slice(TCR_EL2, 30, 2) == 0b01;
        inputsize_max = if Have52BitVAExt() & largegrain then 52 else 48;
        if inputsize > inputsize_max then {
          c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
          assert(c == Constraint_FORCE | c == Constraint_FAULT);
          if c == Constraint_FORCE then inputsize = inputsize_max
          else ()
        } else ();
        inputsize_min = 64 - 39;
        if inputsize < inputsize_min then {
          c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
          assert(c == Constraint_FORCE | c == Constraint_FAULT);
          if c == Constraint_FORCE then inputsize = inputsize_min
          else ()
        } else ();
        basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsOnes_slice(inputaddr, inputsize, (top - inputsize) + 1);
        disabled = [TCR_EL2[23]] == 0b1;
        baseregister = TTBR1_EL2;
        descaddr.memattrs = WalkAttrDecode(slice(TCR_EL2, 28, 2), slice(TCR_EL2, 26, 2), slice(TCR_EL2, 24, 2), secondstage);
        hierattrsdisabled = AArch64_HaveHPDExt() & [TCR_EL2[42]] == 0b1
      };
      ps = slice(TCR_EL2, 32, 3);
      reversedescriptors = [SCTLR_EL2[25]] == 0b1;
      lookupsecure = false;
      singlepriv = false;
      update_AF = HaveAccessFlagUpdateExt() & [TCR_EL2[39]] == 0b1;
      update_AP = (HaveDirtyBitModifierExt() & update_AF) & [TCR_EL2[40]] == 0b1
    } else if PSTATE.EL == EL2 then {
      inputsize = 64 - UInt(slice(TCR_EL2, 0, 6));
      largegrain = slice(TCR_EL2, 14, 2) == 0b01;
      midgrain = slice(TCR_EL2, 14, 2) == 0b10;
      inputsize_max = if Have52BitVAExt() & largegrain then 52 else 48;
      if inputsize > inputsize_max then {
        c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
        assert(c == Constraint_FORCE | c == Constraint_FAULT);
        if c == Constraint_FORCE then inputsize = inputsize_max
        else ()
      } else ();
      inputsize_min = 64 - 39;
      if inputsize < inputsize_min then {
        c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
        assert(c == Constraint_FORCE | c == Constraint_FAULT);
        if c == Constraint_FORCE then inputsize = inputsize_min
        else ()
      } else ();
      ps = slice(TCR_EL2, 16, 3);
      basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsZero_slice(inputaddr, inputsize, (top - inputsize) + 1);
      disabled = false;
      baseregister = TTBR0_EL2;
      descaddr.memattrs = WalkAttrDecode(slice(TCR_EL2, 12, 2), slice(TCR_EL2, 10, 2), slice(TCR_EL2, 8, 2), secondstage);
      reversedescriptors = [SCTLR_EL2[25]] == 0b1;
      lookupsecure = false;
      singlepriv = true;
      update_AF = HaveAccessFlagUpdateExt() & [TCR_EL2[39]] == 0b1;
      update_AP = (HaveDirtyBitModifierExt() & update_AF) & [TCR_EL2[40]] == 0b1;
      hierattrsdisabled = AArch64_HaveHPDExt() & [TCR_EL2[24]] == 0b1
    } else {
      if [inputaddr[top]] == 0b0 then {
        inputsize = 64 - UInt(slice(TCR_EL1, 0, 6));
        largegrain = slice(TCR_EL1, 14, 2) == 0b01;
        midgrain = slice(TCR_EL1, 14, 2) == 0b10;
        inputsize_max = if Have52BitVAExt() & largegrain then 52 else 48;
        if inputsize > inputsize_max then {
          c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
          assert(c == Constraint_FORCE | c == Constraint_FAULT);
          if c == Constraint_FORCE then inputsize = inputsize_max
          else ()
        } else ();
        inputsize_min = 64 - 39;
        if inputsize < inputsize_min then {
          c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
          assert(c == Constraint_FORCE | c == Constraint_FAULT);
          if c == Constraint_FORCE then inputsize = inputsize_min
          else ()
        } else ();
        basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsZero_slice(inputaddr, inputsize, (top - inputsize) + 1);
        disabled = [TCR_EL1[7]] == 0b1;
        baseregister = TTBR0_EL1;
        descaddr.memattrs = WalkAttrDecode(slice(TCR_EL1, 12, 2), slice(TCR_EL1, 10, 2), slice(TCR_EL1, 8, 2), secondstage);
        hierattrsdisabled = AArch64_HaveHPDExt() & [TCR_EL1[41]] == 0b1
      } else {
        inputsize = 64 - UInt(slice(TCR_EL1, 16, 6));
        largegrain = slice(TCR_EL1, 30, 2) == 0b11;
        midgrain = slice(TCR_EL1, 30, 2) == 0b01;
        inputsize_max = if Have52BitVAExt() & largegrain then 52 else 48;
        if inputsize > inputsize_max then {
          c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
          assert(c == Constraint_FORCE | c == Constraint_FAULT);
          if c == Constraint_FORCE then inputsize = inputsize_max
          else ()
        } else ();
        inputsize_min = 64 - 39;
        if inputsize < inputsize_min then {
          c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
          assert(c == Constraint_FORCE | c == Constraint_FAULT);
          if c == Constraint_FORCE then inputsize = inputsize_min
          else ()
        } else ();
        basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsOnes_slice(inputaddr, inputsize, (top - inputsize) + 1);
        disabled = [TCR_EL1[23]] == 0b1;
        baseregister = TTBR1_EL1;
        descaddr.memattrs = WalkAttrDecode(slice(TCR_EL1, 28, 2), slice(TCR_EL1, 26, 2), slice(TCR_EL1, 24, 2), secondstage);
        hierattrsdisabled = AArch64_HaveHPDExt() & [TCR_EL1[42]] == 0b1
      };
      ps = slice(TCR_EL1, 32, 3);
      reversedescriptors = [SCTLR_EL1[25]] == 0b1;
      lookupsecure = IsSecure();
      singlepriv = false;
      update_AF = HaveAccessFlagUpdateExt() & [TCR_EL1[39]] == 0b1;
      update_AP = (HaveDirtyBitModifierExt() & update_AF) & [TCR_EL1[40]] == 0b1
    };
    if largegrain then {
      grainsize = 16;
      firstblocklevel = if Have52BitPAExt() then 1 else 2
    } else if midgrain then {
      grainsize = 14;
      firstblocklevel = 2
    } else {
      grainsize = 12;
      firstblocklevel = 1
    };
    stride = grainsize - 3;
    level = 4 - RoundUp(Real(inputsize - grainsize) / Real(stride))
  } else {
    inputaddr = ZeroExtend(ipaddress);
    inputsize = 64 - UInt(slice(VTCR_EL2, 0, 6));
    largegrain = slice(VTCR_EL2, 14, 2) == 0b01;
    midgrain = slice(VTCR_EL2, 14, 2) == 0b10;
    inputsize_max = if Have52BitVAExt() & largegrain then 52 else 48;
    if inputsize > inputsize_max then {
      c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
      assert(c == Constraint_FORCE | c == Constraint_FAULT);
      if c == Constraint_FORCE then inputsize = inputsize_max
      else ()
    } else ();
    inputsize_min = 64 - 39;
    if inputsize < inputsize_min then {
      c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
      assert(c == Constraint_FORCE | c == Constraint_FAULT);
      if c == Constraint_FORCE then inputsize = inputsize_min
      else ()
    } else ();
    ps = slice(VTCR_EL2, 16, 3);
    basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsZero_slice(inputaddr, inputsize, negate(inputsize) + 64);
    disabled = false;
    baseregister = VTTBR_EL2;
    descaddr.memattrs = WalkAttrDecode(slice(VTCR_EL2, 8, 2), slice(VTCR_EL2, 10, 2), slice(VTCR_EL2, 12, 2), secondstage);
    reversedescriptors = [SCTLR_EL2[25]] == 0b1;
    lookupsecure = false;
    singlepriv = true;
    update_AF = HaveAccessFlagUpdateExt() & [VTCR_EL2[21]] == 0b1;
    update_AP = (HaveDirtyBitModifierExt() & update_AF) & [VTCR_EL2[22]] == 0b1;
    startlevel = UInt(slice(VTCR_EL2, 6, 2));
    if largegrain then {
      grainsize = 16;
      level = 3 - startlevel;
      firstblocklevel = if Have52BitPAExt() then 1 else 2
    } else if midgrain then {
      grainsize = 14;
      level = 3 - startlevel;
      firstblocklevel = 2
    } else {
      grainsize = 12;
      level = 2 - startlevel;
      firstblocklevel = 1
    };
    stride = grainsize - 3;
    if largegrain then
      if level == 0 | level == 1 & PAMax() <= 42 then basefound = false
      else ()
    else if midgrain then
      if level == 0 | level == 1 & PAMax() <= 40 then basefound = false
      else ()
    else if level < 0 | level == 0 & PAMax() <= 42 then basefound = false
    else ();
    inputsizecheck = inputsize;
    if inputsize > PAMax() & (~(ELUsingAArch32(EL1)) | inputsize > 40) then match ConstrainUnpredictable(Unpredictable_LARGEIPA) {
      Constraint_FORCE => {
        inputsize = PAMax();
        inputsizecheck = PAMax()
      },
      Constraint_FORCENOSLCHECK => inputsize = PAMax(),
      Constraint_FAULT => basefound = false,
      _ => Unreachable()
    } else ();
    startsizecheck = inputsizecheck - ((3 - level) * stride + grainsize);
    if startsizecheck < 1 | startsizecheck > stride + 4 then basefound = false
    else ()
  };
  if ~(basefound) | disabled then {
    level = 0;
    __tmp_19 : AddressDescriptor = result.addrdesc;
    __tmp_19.fault = AArch64_TranslationFault(ipaddress, level, acctype, iswrite, secondstage, s2fs1walk);
    result.addrdesc = __tmp_19;
    return(result)
  } else ();
  outputsize : int = undefined;
  match ps {
    0b000 => outputsize = 32,
    0b001 => outputsize = 36,
    0b010 => outputsize = 40,
    0b011 => outputsize = 42,
    0b100 => outputsize = 44,
    0b101 => outputsize = 48,
    0b110 => outputsize = if Have52BitPAExt() & largegrain then 52 else 48,
    _ => outputsize = 48
  };
  if outputsize > PAMax() then outputsize = PAMax()
  else ();
  if outputsize < 48 & ~(IsZero_slice(baseregister, outputsize, negate(outputsize) + 48)) then {
    level = 0;
    __tmp_20 : AddressDescriptor = result.addrdesc;
    __tmp_20.fault = AArch64_AddressSizeFault(ipaddress, level, acctype, iswrite, secondstage, s2fs1walk);
    result.addrdesc = __tmp_20;
    return(result)
  } else ();
  let 'baselowerbound = ((3 + inputsize) - ((3 - level) * stride + grainsize)) : int;
  assert(constraint(0 <= 'baselowerbound & 'baselowerbound <= 48));
  baseaddress : bits(52) = undefined;
  if outputsize == 52 then let 'z = (if baselowerbound < 6 then 6 else baselowerbound) : int in {
    assert(constraint(0 <= 'z & 'z <= 48));
    baseaddress = (slice(baseregister, 2, 4) @ slice(baseregister, z, negate(z) + 48)) @ Zeros(z)
  } else
    baseaddress = ZeroExtend(slice(baseregister, baselowerbound, negate(baselowerbound) + 48) @ Zeros(baselowerbound));
  ns_table : bits(1) = if lookupsecure then 0b0 else 0b1;
  ap_table : bits(2) = 0b00;
  xn_table : bits(1) = 0b0;
  pxn_table : bits(1) = 0b0;
  addrselecttop : int = inputsize - 1;
  apply_nvnv1_effect : bool = ((HaveNVExt() & HaveEL(EL2)) & [HCR_EL2[42]] == 0b1) & [HCR_EL2[43]] == 0b1;
  blocktranslate : bool = undefined;
  desc : bits(64) = undefined;
  accdesc : AccessDescriptor = undefined;
  hwupdatewalk : bool = undefined;
  descaddr2 : AddressDescriptor = undefined;
  addrselectbottom : int = undefined;
  repeat {
    addrselectbottom = (3 - level) * stride + grainsize;
    index : bits(52) = ZeroExtend_slice_append(inputaddr, addrselectbottom, (addrselecttop - addrselectbottom) + 1, 0b000);
    __tmp_21 : FullAddress = descaddr.paddress;
    __tmp_21.physicaladdress = baseaddress | index;
    descaddr.paddress = __tmp_21;
    __tmp_22 : FullAddress = descaddr.paddress;
    __tmp_22.NS = ns_table;
    descaddr.paddress = __tmp_22;
    if secondstage | ~(HasS2Translation()) then descaddr2 = descaddr
    else {
      hwupdatewalk = false;
      descaddr2 = AArch64_SecondStageWalk(descaddr, vaddress, acctype, iswrite, 8, hwupdatewalk);
      if IsFault(descaddr2) then {
        __tmp_23 : AddressDescriptor = result.addrdesc;
        __tmp_23.fault = descaddr2.fault;
        result.addrdesc = __tmp_23;
        return(result)
      } else ()
    };
    descaddr2.vaddress = ZeroExtend(vaddress);
    accdesc = CreateAccessDescriptorPTW(acctype, secondstage, s2fs1walk, level);
    desc = aget__Mem(descaddr2, 8, accdesc);
    if reversedescriptors then desc = BigEndianReverse(desc)
    else ();
    if [desc[0]] == 0b0 | slice(desc, 0, 2) == 0b01 & level == 3 then {
      __tmp_24 : AddressDescriptor = result.addrdesc;
      __tmp_24.fault = AArch64_TranslationFault(ipaddress, level, acctype, iswrite, secondstage, s2fs1walk);
      result.addrdesc = __tmp_24;
      return(result)
    } else ();
    if slice(desc, 0, 2) == 0b01 | level == 3 then blocktranslate = true
    else {
      if (outputsize < 52 & largegrain) & ~(IsZero(slice(desc, 12, 4))) | outputsize < 48 & ~(IsZero_slice(desc, outputsize, negate(outputsize) + 48)) then {
        __tmp_25 : AddressDescriptor = result.addrdesc;
        __tmp_25.fault = AArch64_AddressSizeFault(ipaddress, level, acctype, iswrite, secondstage, s2fs1walk);
        result.addrdesc = __tmp_25;
        return(result)
      } else ();
      let 'gsz = grainsize;
      assert(constraint(0 <= 'gsz & 'gsz <= 48));
      if outputsize == 52 then
        baseaddress = (slice(desc, 12, 4) @ slice(desc, gsz, negate(gsz) + 48)) @ Zeros(gsz)
      else
        baseaddress = ZeroExtend(slice(desc, gsz, negate(gsz) + 48) @ Zeros(gsz));
      if ~(secondstage) then ns_table = ns_table | [desc[63]]
      else ();
      if ~(secondstage) & ~(hierattrsdisabled) then {
        ap_table = __SetSlice_bits(2, 1, ap_table, 1, [ap_table[1]] | [desc[62]]);
        if apply_nvnv1_effect then pxn_table = pxn_table | [desc[60]]
        else xn_table = xn_table | [desc[60]];
        if ~(singlepriv) then
          if ~(apply_nvnv1_effect) then {
            pxn_table = pxn_table | [desc[59]];
            ap_table = __SetSlice_bits(2, 1, ap_table, 0, [ap_table[0]] | [desc[61]])
          } else ()
        else ()
      } else ();
      level = level + 1;
      addrselecttop = addrselectbottom - 1;
      blocktranslate = false
    }
  } until blocktranslate;
  if level < firstblocklevel then {
    __tmp_26 : AddressDescriptor = result.addrdesc;
    __tmp_26.fault = AArch64_TranslationFault(ipaddress, level, acctype, iswrite, secondstage, s2fs1walk);
    result.addrdesc = __tmp_26;
    return(result)
  } else ();
  contiguousbitcheck : bool = undefined;
  if largegrain then contiguousbitcheck = level == 2 & inputsize < 34
  else if midgrain then contiguousbitcheck = level == 2 & inputsize < 30
  else contiguousbitcheck = level == 1 & inputsize < 34;
  if contiguousbitcheck & [desc[52]] == 0b1 then
    if undefined then {
      __tmp_27 : AddressDescriptor = result.addrdesc;
      __tmp_27.fault = AArch64_TranslationFault(ipaddress, level, acctype, iswrite, secondstage, s2fs1walk);
      result.addrdesc = __tmp_27;
      return(result)
    } else ()
  else ();
  if (outputsize < 52 & largegrain) & ~(IsZero(slice(desc, 12, 4))) | outputsize < 48 & ~(IsZero_slice(desc, outputsize, negate(outputsize) + 48)) then {
    __tmp_28 : AddressDescriptor = result.addrdesc;
    __tmp_28.fault = AArch64_AddressSizeFault(ipaddress, level, acctype, iswrite, secondstage, s2fs1walk);
    result.addrdesc = __tmp_28;
    return(result)
  } else ();
  outputaddress : bits(52) = undefined;
  let 'asb = addrselectbottom;
  assert(constraint(0 <= 'asb & 'asb <= 48));
  if outputsize == 52 then
    outputaddress = (slice(desc, 12, 4) @ slice(desc, asb, negate(asb) + 48)) @ slice(inputaddr, 0, asb)
  else
    outputaddress = ZeroExtend(slice(desc, asb, negate(asb) + 48) @ slice(inputaddr, 0, asb));
  __tmp_33 : DescriptorUpdate = result.descupdate;
  __tmp_33.AF = false;
  __tmp_33.AP = false;
  __tmp_33.descaddr = descaddr;
  result.descupdate = __tmp_33;
  if [desc[10]] == 0b0 then
    if ~(update_AF) then {
      __tmp_29 : AddressDescriptor = result.addrdesc;
      __tmp_29.fault = AArch64_AccessFlagFault(ipaddress, level, acctype, iswrite, secondstage, s2fs1walk);
      result.addrdesc = __tmp_29;
      return(result)
    } else {
      __tmp_30 : DescriptorUpdate = result.descupdate;
      __tmp_30.AF = true;
      result.descupdate = __tmp_30
    }
  else ();
  if update_AP & [desc[51]] == 0b1 then
    if ~(secondstage) & [desc[7]] == 0b1 then {
      desc = __SetSlice_bits(64, 1, desc, 7, 0b0);
      __tmp_31 : DescriptorUpdate = result.descupdate;
      __tmp_31.AP = true;
      result.descupdate = __tmp_31
    } else if secondstage & [desc[7]] == 0b0 then {
      desc = __SetSlice_bits(64, 1, desc, 7, 0b1);
      __tmp_32 : DescriptorUpdate = result.descupdate;
      __tmp_32.AP = true;
      result.descupdate = __tmp_32
    } else ()
  else ();
  xn : bits(1) = undefined;
  pxn : bits(1) = undefined;
  if apply_nvnv1_effect then {
    pxn = [desc[54]];
    xn = 0b0
  } else {
    xn = [desc[54]];
    pxn = [desc[53]]
  };
  contiguousbit : bits(1) = [desc[52]];
  nG : bits(1) = [desc[11]];
  sh : bits(2) = slice(desc, 8, 2);
  ap : bits(3) = undefined;
  if apply_nvnv1_effect then ap = [desc[7]] @ 0b01
  else ap = slice(desc, 6, 2) @ 0b1;
  memattr : bits(4) = slice(desc, 2, 4);
  result.domain = undefined;
  result.level = level;
  result.blocksize = 2 ^ ((3 - level) * stride + grainsize);
  if ~(secondstage) then {
    __tmp_34 : Permissions = result.perms;
    __tmp_34.xn = xn | xn_table;
    result.perms = __tmp_34;
    __tmp_35 : bits(3) = result.perms.ap;
    __tmp_35 = __SetSlice_bits(3, 1, __tmp_35, 2, [ap[2]] | [ap_table[1]]);
    __tmp_36 : Permissions = result.perms;
    __tmp_36.ap = __tmp_35;
    result.perms = __tmp_36;
    if ~(singlepriv) then {
      __tmp_37 : bits(3) = result.perms.ap;
      __tmp_37 = __SetSlice_bits(3, 1, __tmp_37, 1, [ap[1]] & ~([ap_table[0]]));
      __tmp_38 : Permissions = result.perms;
      __tmp_38.ap = __tmp_37;
      result.perms = __tmp_38;
      __tmp_39 : Permissions = result.perms;
      __tmp_39.pxn = pxn | pxn_table;
      result.perms = __tmp_39;
      if IsSecure() then result.nG = nG | ns_table
      else result.nG = nG
    } else {
      __tmp_40 : bits(3) = result.perms.ap;
      __tmp_40 = __SetSlice_bits(3, 1, __tmp_40, 1, 0b1);
      __tmp_41 : Permissions = result.perms;
      __tmp_41.ap = __tmp_40;
      result.perms = __tmp_41;
      __tmp_42 : Permissions = result.perms;
      __tmp_42.pxn = 0b0;
      result.perms = __tmp_42;
      result.nG = 0b0
    };
    __tmp_43 : bits(3) = result.perms.ap;
    __tmp_43 = __SetSlice_bits(3, 1, __tmp_43, 0, 0b1);
    __tmp_44 : Permissions = result.perms;
    __tmp_44.ap = __tmp_43;
    result.perms = __tmp_44;
    __tmp_45 : AddressDescriptor = result.addrdesc;
    __tmp_45.memattrs = AArch64_S1AttrDecode(sh, slice(memattr, 0, 3), acctype);
    result.addrdesc = __tmp_45;
    __tmp_46 : FullAddress = result.addrdesc.paddress;
    __tmp_46.NS = [memattr[3]] | ns_table;
    __tmp_47 : AddressDescriptor = result.addrdesc;
    __tmp_47.paddress = __tmp_46;
    result.addrdesc = __tmp_47
  } else {
    __tmp_48 : bits(3) = result.perms.ap;
    __tmp_48 = __SetSlice_bits(3, 2, __tmp_48, 1, slice(ap, 1, 2));
    __tmp_49 : Permissions = result.perms;
    __tmp_49.ap = __tmp_48;
    result.perms = __tmp_49;
    __tmp_50 : bits(3) = result.perms.ap;
    __tmp_50 = __SetSlice_bits(3, 1, __tmp_50, 0, 0b1);
    __tmp_51 : Permissions = result.perms;
    __tmp_51.ap = __tmp_50;
    result.perms = __tmp_51;
    __tmp_52 : Permissions = result.perms;
    __tmp_52.xn = xn;
    result.perms = __tmp_52;
    if HaveExtendedExecuteNeverExt() then {
      __tmp_53 : Permissions = result.perms;
      __tmp_53.xxn = [desc[53]];
      result.perms = __tmp_53
    } else ();
    __tmp_54 : Permissions = result.perms;
    __tmp_54.pxn = 0b0;
    result.perms = __tmp_54;
    result.nG = 0b0;
    __tmp_55 : AddressDescriptor = result.addrdesc;
    __tmp_55.memattrs = S2AttrDecode(sh, memattr, acctype);
    result.addrdesc = __tmp_55;
    __tmp_56 : FullAddress = result.addrdesc.paddress;
    __tmp_56.NS = 0b1;
    __tmp_57 : AddressDescriptor = result.addrdesc;
    __tmp_57.paddress = __tmp_56;
    result.addrdesc = __tmp_57
  };
  __tmp_58 : FullAddress = result.addrdesc.paddress;
  __tmp_58.physicaladdress = outputaddress;
  __tmp_59 : AddressDescriptor = result.addrdesc;
  __tmp_59.paddress = __tmp_58;
  result.addrdesc = __tmp_59;
  __tmp_60 : AddressDescriptor = result.addrdesc;
  __tmp_60.fault = AArch64_NoFault();
  result.addrdesc = __tmp_60;
  result.contiguous = contiguousbit == 0b1;
  if HaveCommonNotPrivateTransExt() then result.CnP = [baseregister[0]]
  else ();
  return(result)
}

val IsZero_slice2 : forall 'n, 'n >= 0.
  (bits('n), int, int) -> bool effect {escape}

function IsZero_slice2 (xs, i, 'l) = {
  assert(constraint('l >= 0));
  IsZero(xs & slice_mask(i, l))
}

val AArch64_TranslateAddressS1Off : (bits(64), AccType, bool) -> TLBRecord effect {rreg, undef, escape}

function AArch64_TranslateAddressS1Off (vaddress, acctype, iswrite) = {
  assert(~(ELUsingAArch32(S1TranslationRegime())));
  result : TLBRecord = undefined;
  Top : int = AddrTop(vaddress, false, PSTATE.EL);
  s2fs1walk : bool = undefined;
  secondstage : bool = undefined;
  ipaddress : bits(52) = undefined;
  level : int = undefined;
  if ~(IsZero_slice2(vaddress, PAMax(), (Top + 1) - PAMax())) then {
    level = 0;
    ipaddress = undefined;
    secondstage = false;
    s2fs1walk = false;
    __tmp_198 : AddressDescriptor = result.addrdesc;
    __tmp_198.fault = AArch64_AddressSizeFault(ipaddress, level, acctype, iswrite, secondstage, s2fs1walk);
    result.addrdesc = __tmp_198;
    return(result)
  } else ();
  default_cacheable : bool = HasS2Translation() & [HCR_EL2[12]] == 0b1;
  cacheable : bool = undefined;
  if default_cacheable then {
    __tmp_199 : MemoryAttributes = result.addrdesc.memattrs;
    __tmp_199.typ = MemType_Normal;
    __tmp_200 : AddressDescriptor = result.addrdesc;
    __tmp_200.memattrs = __tmp_199;
    result.addrdesc = __tmp_200;
    __tmp_201 : MemAttrHints = result.addrdesc.memattrs.inner;
    __tmp_201.attrs = MemAttr_WB;
    __tmp_202 : MemoryAttributes = result.addrdesc.memattrs;
    __tmp_202.inner = __tmp_201;
    __tmp_203 : AddressDescriptor = result.addrdesc;
    __tmp_203.memattrs = __tmp_202;
    result.addrdesc = __tmp_203;
    __tmp_204 : MemAttrHints = result.addrdesc.memattrs.inner;
    __tmp_204.hints = MemHint_RWA;
    __tmp_205 : MemoryAttributes = result.addrdesc.memattrs;
    __tmp_205.inner = __tmp_204;
    __tmp_206 : AddressDescriptor = result.addrdesc;
    __tmp_206.memattrs = __tmp_205;
    result.addrdesc = __tmp_206;
    __tmp_207 : MemoryAttributes = result.addrdesc.memattrs;
    __tmp_207.shareable = false;
    __tmp_208 : AddressDescriptor = result.addrdesc;
    __tmp_208.memattrs = __tmp_207;
    result.addrdesc = __tmp_208;
    __tmp_209 : MemoryAttributes = result.addrdesc.memattrs;
    __tmp_209.outershareable = false;
    __tmp_210 : AddressDescriptor = result.addrdesc;
    __tmp_210.memattrs = __tmp_209;
    result.addrdesc = __tmp_210
  } else if acctype != AccType_IFETCH then {
    __tmp_211 : MemoryAttributes = result.addrdesc.memattrs;
    __tmp_211.typ = MemType_Device;
    __tmp_212 : AddressDescriptor = result.addrdesc;
    __tmp_212.memattrs = __tmp_211;
    result.addrdesc = __tmp_212;
    __tmp_213 : MemoryAttributes = result.addrdesc.memattrs;
    __tmp_213.device = DeviceType_nGnRnE;
    __tmp_214 : AddressDescriptor = result.addrdesc;
    __tmp_214.memattrs = __tmp_213;
    result.addrdesc = __tmp_214;
    __tmp_215 : MemoryAttributes = result.addrdesc.memattrs;
    __tmp_215.inner = undefined;
    __tmp_216 : AddressDescriptor = result.addrdesc;
    __tmp_216.memattrs = __tmp_215;
    result.addrdesc = __tmp_216
  } else {
    cacheable = [aget_SCTLR()[12]] == 0b1;
    __tmp_217 : MemoryAttributes = result.addrdesc.memattrs;
    __tmp_217.typ = MemType_Normal;
    __tmp_218 : AddressDescriptor = result.addrdesc;
    __tmp_218.memattrs = __tmp_217;
    result.addrdesc = __tmp_218;
    if cacheable then {
      __tmp_219 : MemAttrHints = result.addrdesc.memattrs.inner;
      __tmp_219.attrs = MemAttr_WT;
      __tmp_220 : MemoryAttributes = result.addrdesc.memattrs;
      __tmp_220.inner = __tmp_219;
      __tmp_221 : AddressDescriptor = result.addrdesc;
      __tmp_221.memattrs = __tmp_220;
      result.addrdesc = __tmp_221;
      __tmp_222 : MemAttrHints = result.addrdesc.memattrs.inner;
      __tmp_222.hints = MemHint_RA;
      __tmp_223 : MemoryAttributes = result.addrdesc.memattrs;
      __tmp_223.inner = __tmp_222;
      __tmp_224 : AddressDescriptor = result.addrdesc;
      __tmp_224.memattrs = __tmp_223;
      result.addrdesc = __tmp_224
    } else {
      __tmp_225 : MemAttrHints = result.addrdesc.memattrs.inner;
      __tmp_225.attrs = MemAttr_NC;
      __tmp_226 : MemoryAttributes = result.addrdesc.memattrs;
      __tmp_226.inner = __tmp_225;
      __tmp_227 : AddressDescriptor = result.addrdesc;
      __tmp_227.memattrs = __tmp_226;
      result.addrdesc = __tmp_227;
      __tmp_228 : MemAttrHints = result.addrdesc.memattrs.inner;
      __tmp_228.hints = MemHint_No;
      __tmp_229 : MemoryAttributes = result.addrdesc.memattrs;
      __tmp_229.inner = __tmp_228;
      __tmp_230 : AddressDescriptor = result.addrdesc;
      __tmp_230.memattrs = __tmp_229;
      result.addrdesc = __tmp_230
    };
    __tmp_231 : MemoryAttributes = result.addrdesc.memattrs;
    __tmp_231.shareable = true;
    __tmp_232 : AddressDescriptor = result.addrdesc;
    __tmp_232.memattrs = __tmp_231;
    result.addrdesc = __tmp_232;
    __tmp_233 : MemoryAttributes = result.addrdesc.memattrs;
    __tmp_233.outershareable = true;
    __tmp_234 : AddressDescriptor = result.addrdesc;
    __tmp_234.memattrs = __tmp_233;
    result.addrdesc = __tmp_234
  };
  __tmp_235 : MemoryAttributes = result.addrdesc.memattrs;
  __tmp_235.outer = result.addrdesc.memattrs.inner;
  __tmp_236 : AddressDescriptor = result.addrdesc;
  __tmp_236.memattrs = __tmp_235;
  result.addrdesc = __tmp_236;
  __tmp_237 : AddressDescriptor = result.addrdesc;
  __tmp_237.memattrs = MemAttrDefaults(result.addrdesc.memattrs);
  result.addrdesc = __tmp_237;
  __tmp_238 : Permissions = result.perms;
  __tmp_238.ap = undefined;
  result.perms = __tmp_238;
  __tmp_239 : Permissions = result.perms;
  __tmp_239.xn = 0b0;
  result.perms = __tmp_239;
  __tmp_240 : Permissions = result.perms;
  __tmp_240.pxn = 0b0;
  result.perms = __tmp_240;
  result.nG = undefined;
  result.contiguous = undefined;
  result.domain = undefined;
  result.level = undefined;
  result.blocksize = undefined;
  __tmp_241 : FullAddress = result.addrdesc.paddress;
  __tmp_241.physicaladdress = slice(vaddress, 0, 52);
  __tmp_242 : AddressDescriptor = result.addrdesc;
  __tmp_242.paddress = __tmp_241;
  result.addrdesc = __tmp_242;
  __tmp_243 : FullAddress = result.addrdesc.paddress;
  __tmp_243.NS = if IsSecure() then 0b0 else 0b1;
  __tmp_244 : AddressDescriptor = result.addrdesc;
  __tmp_244.paddress = __tmp_243;
  result.addrdesc = __tmp_244;
  __tmp_245 : AddressDescriptor = result.addrdesc;
  __tmp_245.fault = AArch64_NoFault();
  result.addrdesc = __tmp_245;
  return(result)
}

val AArch64_MaybeZeroRegisterUppers : unit -> unit effect {escape, rreg, undef, wreg}

function AArch64_MaybeZeroRegisterUppers () = {
  assert(UsingAArch32(), "UsingAArch32()");
  include_R15_name : bool = undefined;
  last : int = undefined;
  first : int = undefined;
  if PSTATE.EL == EL0 & ~(ELUsingAArch32(EL1)) then {
    first = 0;
    last = 14;
    include_R15_name = false
  } else if (((PSTATE.EL == EL0 | PSTATE.EL == EL1) & HaveEL(EL2)) & ~(IsSecure())) & ~(ELUsingAArch32(EL2)) then {
    first = 0;
    last = 30;
    include_R15_name = false
  } else {
    first = 0;
    last = 30;
    include_R15_name = true
  };
  foreach (n from first to last by 1 in inc)
    if (n != 15 | include_R15_name) & ConstrainUnpredictableBool(Unpredictable_ZEROUPPER) then {
      __tmp_3 : bits(64) = _R[n];
      __tmp_3 = __SetSlice_bits(64, 32, __tmp_3, 32, Zeros());
      _R[n] = __tmp_3
    } else ();
  ()
}

val DCPSInstruction : bits(2) -> unit effect {escape, rreg, undef, wreg}

function DCPSInstruction target_el = {
  SynchronizeContext();
  handle_el : bits(2) = undefined;
  match target_el {
    ? if ? == EL1 => if PSTATE.EL == EL2 | PSTATE.EL == EL3 & ~(UsingAArch32()) then handle_el = PSTATE.EL else if (HaveEL(EL2) & ~(IsSecure())) & [HCR_EL2[27]] == 0b1 then UndefinedFault() else handle_el = EL1,
    ? if ? == EL2 => if ~(HaveEL(EL2)) then UndefinedFault() else if PSTATE.EL == EL3 & ~(UsingAArch32()) then handle_el = EL3 else if IsSecure() then UndefinedFault() else handle_el = EL2,
    ? if ? == EL3 => {
      if [EDSCR[16]] == 0b1 | ~(HaveEL(EL3)) then UndefinedFault() else ();
      handle_el = EL3
    },
    _ => Unreachable()
  };
  from_secure : bool = IsSecure();
  if ELUsingAArch32(handle_el) then {
    if PSTATE.M == M32_Monitor then SCR = __SetSlice_bits(32, 1, SCR, 0, 0b0) else ();
    assert(UsingAArch32(), "UsingAArch32()");
    match handle_el {
      ? if ? == EL1 => {
        AArch32_WriteMode(M32_Svc);
        if HavePANExt() & [SCTLR[23]] == 0b0 then PSTATE.PAN = 0b1 else ()
      },
      ? if ? == EL2 => AArch32_WriteMode(M32_Hyp),
      ? if ? == EL3 => {
        AArch32_WriteMode(M32_Monitor);
        if HavePANExt() then if ~(from_secure) then PSTATE.PAN = 0b0 else if [SCTLR[23]] == 0b0 then PSTATE.PAN = 0b1 else () else ()
      }
    };
    if handle_el == EL2 then {
      ELR_hyp = undefined;
      HSR = undefined
    } else set_LR(undefined);
    aset_SPSR(undefined);
    PSTATE.E = [aget_SCTLR()[25]];
    DLR = undefined;
    DSPSR = undefined
  } else {
    if UsingAArch32() then AArch64_MaybeZeroRegisterUppers() else ();
    PSTATE.nRW = 0b0;
    PSTATE.SP = 0b1;
    PSTATE.EL = handle_el;
    if HavePANExt() & (handle_el == EL1 & [SCTLR_EL1[23]] == 0b0 | ((handle_el == EL2 & [HCR_EL2[34]] == 0b1) & [HCR_EL2[27]] == 0b1) & [SCTLR_EL2[23]] == 0b0) then PSTATE.PAN = 0b1 else ();
    aset_ELR(undefined);
    aset_SPSR(undefined);
    aset_ESR(undefined);
    DLR_EL0 = undefined;
    DSPSR_EL0 = undefined;
    if HaveUAOExt() then PSTATE.UAO = 0b0 else ()
  };
  UpdateEDSCRFields();
  if (HaveRASExt() & [aget_SCTLR()[21]] == 0b1) & ConstrainUnpredictableBool(Unpredictable_IESBinDebug) then ErrorSynchronizationBarrier(MBReqDomain_FullSystem, MBReqTypes_All) else ();
  ()
}

val aarch64_system_exceptions_debug_exception : bits(2) -> unit effect {escape, rreg, undef, wreg}

function aarch64_system_exceptions_debug_exception target_level = DCPSInstruction(target_level)

val AArch64_GenerateDebugExceptionsFrom : (bits(2), bool, bits(1)) -> bool effect {escape, rreg, undef}

function AArch64_GenerateDebugExceptionsFrom (from, secure, mask) = {
  if ([OSLSR_EL1[1]] == 0b1 | DoubleLockStatus()) | Halted() then return(false) else ();
  route_to_el2 : bool = (HaveEL(EL2) & ~(secure)) & ([HCR_EL2[27]] == 0b1 | [MDCR_EL2[8]] == 0b1);
  target : bits(2) = if route_to_el2 then EL2 else EL1;
  enabled : bool = (~(HaveEL(EL3)) | ~(secure)) | [MDCR_EL3[16]] == 0b0;
  if from == target then enabled = (enabled & [MDSCR_EL1[13]] == 0b1) & mask == 0b0 else enabled = enabled & UInt(target) > UInt(from);
  return(enabled)
}

val AArch64_GenerateDebugExceptions : unit -> bool effect {escape, rreg, undef}

function AArch64_GenerateDebugExceptions () = return(AArch64_GenerateDebugExceptionsFrom(PSTATE.EL, IsSecure(), PSTATE.D))

val AArch64_FaultSyndrome : (bool, FaultRecord) -> bits(25) effect {escape, undef}

function AArch64_FaultSyndrome (d_side, fault) = {
  assert(fault.typ != Fault_None, "((fault).type != Fault_None)");
  iss : bits(25) = Zeros();
  if HaveRASExt() & IsExternalSyncAbort(fault) then iss = __SetSlice_bits(25, 2, iss, 11, fault.errortype) else ();
  if d_side then {
    if IsSecondStage(fault) & ~(fault.s2fs1walk) then iss = __SetSlice_bits(25, 11, iss, 14, LSInstructionSyndrome()) else ();
    if fault.acctype == AccType_DC | fault.acctype == AccType_IC | fault.acctype == AccType_AT then {
      iss = __SetSlice_bits(25, 1, iss, 8, 0b1);
      iss = __SetSlice_bits(25, 1, iss, 6, 0b1)
    } else iss = __SetSlice_bits(25, 1, iss, 6, if fault.write then 0b1 else 0b0)
  } else ();
  if IsExternalAbort(fault) then iss = __SetSlice_bits(25, 1, iss, 9, fault.extflag) else ();
  iss = __SetSlice_bits(25, 1, iss, 7, if fault.s2fs1walk then 0b1 else 0b0);
  iss = __SetSlice_bits(25, 6, iss, 0, EncodeLDFSC(fault.typ, fault.level));
  return(iss)
}

val AArch64_AbortSyndrome : (Exception, FaultRecord, bits(64)) -> ExceptionRecord effect {escape, undef}

function AArch64_AbortSyndrome (typ, fault, vaddress) = {
  exception : ExceptionRecord = ExceptionSyndrome(typ);
  d_side : bool = typ == Exception_DataAbort | typ == Exception_Watchpoint;
  exception.syndrome = AArch64_FaultSyndrome(d_side, fault);
  exception.vaddress = ZeroExtend(vaddress);
  if IPAValid(fault) then {
    exception.ipavalid = true;
    exception.ipaddress = fault.ipaddress
  } else exception.ipavalid = false;
  return(exception)
}

val AArch64_ExecutingATS1xPInstr : unit -> bool effect {rreg, undef}

function AArch64_ExecutingATS1xPInstr () = {
  if ~(HavePrivATExt()) then return(false) else ();
  instr : bits(32) = ThisInstr();
  op2 : bits(3) = undefined;
  CRm : bits(4) = undefined;
  CRn : bits(4) = undefined;
  op1 : bits(3) = undefined;
  if slice(instr, 22, 10) == 0b1101010100 then {
    op1 = slice(instr, 16, 3);
    CRn = slice(instr, 12, 4);
    CRm = slice(instr, 8, 4);
    op2 = slice(instr, 5, 3);
    return(((op1 == 0b000 & CRn == 0x7) & CRm == 0x9) & (op2 == 0b000 | op2 == 0b001))
  } else return(false)
}

val AArch64_ExceptionClass : (Exception, bits(2)) -> (int, bits(1)) effect {escape, rreg, undef}

function AArch64_ExceptionClass (typ, target_el) = {
  il : bits(1) = if ThisInstrLength() == 32 then 0b1 else 0b0;
  from_32 : bool = UsingAArch32();
  assert(from_32 | il == 0b1, "(from_32 || (il == '1'))");
  ec : int = undefined;
  match typ {
    Exception_Uncategorized => {
      ec = 0;
      il = 0b1
    },
    Exception_WFxTrap => ec = 1,
    Exception_CP15RTTrap => {
      ec = 3;
      assert(from_32, "from_32")
    },
    Exception_CP15RRTTrap => {
      ec = 4;
      assert(from_32, "from_32")
    },
    Exception_CP14RTTrap => {
      ec = 5;
      assert(from_32, "from_32")
    },
    Exception_CP14DTTrap => {
      ec = 6;
      assert(from_32, "from_32")
    },
    Exception_AdvSIMDFPAccessTrap => ec = 7,
    Exception_FPIDTrap => ec = 8,
    Exception_CP14RRTTrap => {
      ec = 12;
      assert(from_32, "from_32")
    },
    Exception_IllegalState => {
      ec = 14;
      il = 0b1
    },
    Exception_SupervisorCall => ec = 17,
    Exception_HypervisorCall => ec = 18,
    Exception_MonitorCall => ec = 19,
    Exception_SystemRegisterTrap => {
      ec = 24;
      assert(~(from_32), "!(from_32)")
    },
    Exception_InstructionAbort => {
      ec = 32;
      il = 0b1
    },
    Exception_PCAlignment => {
      ec = 34;
      il = 0b1
    },
    Exception_DataAbort => ec = 36,
    Exception_SPAlignment => {
      ec = 38;
      il = 0b1;
      assert(~(from_32), "!(from_32)")
    },
    Exception_FPTrappedException => ec = 40,
    Exception_SError => {
      ec = 47;
      il = 0b1
    },
    Exception_Breakpoint => {
      ec = 48;
      il = 0b1
    },
    Exception_SoftwareStep => {
      ec = 50;
      il = 0b1
    },
    Exception_Watchpoint => {
      ec = 52;
      il = 0b1
    },
    Exception_SoftwareBreakpoint => ec = 56,
    Exception_VectorCatch => {
      ec = 58;
      il = 0b1;
      assert(from_32, "from_32")
    },
    _ => Unreachable()
  };
  if (ec == 32 | ec == 36 | ec == 48 | ec == 50 | ec == 52) & target_el == PSTATE.EL then ec = ec + 1 else ();
  if (ec == 17 | ec == 18 | ec == 19 | ec == 40 | ec == 56) & ~(from_32) then ec = ec + 4 else ();
  return((ec, il))
}

val AArch64_ReportException : (ExceptionRecord, bits(2)) -> unit effect {escape, rreg, undef, wreg}

function AArch64_ReportException (exception, target_el) = {
  typ : Exception = exception.typ;
  il : bits(1) = undefined;
  ec : int = undefined;
  (ec, il) = AArch64_ExceptionClass(typ, target_el);
  iss : bits(25) = exception.syndrome;
  if (ec == 36 | ec == 37) & [iss[24]] == 0b0 then il = 0b1 else ();
  aset_ESR(target_el, (__GetSlice_int(6, ec, 0) @ il) @ iss);
  if typ == Exception_InstructionAbort | typ == Exception_PCAlignment | typ == Exception_DataAbort | typ == Exception_Watchpoint then aset_FAR(target_el, exception.vaddress) else aset_FAR(target_el, undefined);
  if target_el == EL2 then if exception.ipavalid then HPFAR_EL2 = __SetSlice_bits(64, 40, HPFAR_EL2, 4, slice(exception.ipaddress, 12, 40)) else HPFAR_EL2 = __SetSlice_bits(64, 40, HPFAR_EL2, 4, undefined) else ();
  ()
}

val AArch64_ESBOperation : unit -> unit effect {escape, wreg, undef, rreg}

function AArch64_ESBOperation () = {
  route_to_el3 : bool = HaveEL(EL3) & [SCR_EL3[3]] == 0b1;
  route_to_el2 : bool = (HaveEL(EL2) & ~(IsSecure())) & ([HCR_EL2[27]] == 0b1 | [HCR_EL2[5]] == 0b1);
  target : bits(2) = if route_to_el3 then EL3 else if route_to_el2 then EL2 else EL1;
  mask_active : bool = undefined;
  if target == EL1 then mask_active = PSTATE.EL == EL0 | PSTATE.EL == EL1
  else if (HaveVirtHostExt() & target == EL2) & ((HCR_EL2[34], HCR_EL2[27])) == ((bitone, bitone)) then
    mask_active = PSTATE.EL == EL0 | PSTATE.EL == EL2
  else mask_active = PSTATE.EL == target;
  mask_set : bool = PSTATE.A == 0b1;
  intdis : bool = Halted() | ExternalDebugInterruptsDisabled(target);
  masked : bool = (UInt(target) < UInt(PSTATE.EL) | intdis) | mask_active & mask_set;
  DISR_EL1 : bits(64) = undefined;
  syndrome64 : bits(25) = undefined;
  implicit_esb : bool = undefined;
  DISR : bits(32) = undefined;
  syndrome32 : AArch32_SErrorSyndrome = undefined;
  if SErrorPending() & masked then {
    if ELUsingAArch32(S1TranslationRegime()) then {
      syndrome32 = AArch32_PhysicalSErrorSyndrome();
      DISR = AArch32_ReportDeferredSError(syndrome32.AET, syndrome32.ExT)
    } else {
      implicit_esb = false;
      syndrome64 = AArch64_PhysicalSErrorSyndrome(implicit_esb);
      DISR_EL1 = AArch64_ReportDeferredSError(syndrome64)
    };
    ClearPendingPhysicalSError()
  } else ();
  ()
}

val AArch64_CheckS2Permission : (Permissions, bits(64), bits(52), int, AccType, bool, bool, bool) -> FaultRecord effect {escape, rreg, undef}

function AArch64_CheckS2Permission (perms, vaddress, ipaddress, 'level, acctype, iswrite, s2fs1walk, hwupdatewalk) = {
  assert(((HaveEL(EL2) & ~(IsSecure())) & ~(ELUsingAArch32(EL2))) & HasS2Translation(), "(((HaveEL(EL2) && !(IsSecure())) && !(ELUsingAArch32(EL2))) && HasS2Translation())");
  r : bool = [perms.ap[1]] == 0b1;
  w : bool = [perms.ap[2]] == 0b1;
  xn : bool = undefined;
  if HaveExtendedExecuteNeverExt() then match perms.xn @ perms.xxn {
    0b00 => xn = false,
    0b01 => xn = PSTATE.EL == EL1,
    0b10 => xn = true,
    0b11 => xn = PSTATE.EL == EL0
  } else xn = perms.xn == 0b1;
  failedread : bool = undefined;
  fail : bool = undefined;
  if acctype == AccType_IFETCH & ~(s2fs1walk) then {
    fail = xn;
    failedread = true
  } else if (acctype == AccType_ATOMICRW | acctype == AccType_ORDEREDRW) & ~(s2fs1walk) then {
    fail = ~(r) | ~(w);
    failedread = ~(r)
  } else if iswrite & ~(s2fs1walk) then {
    fail = ~(w);
    failedread = false
  } else if hwupdatewalk then {
    fail = ~(w);
    failedread = ~(iswrite)
  } else {
    fail = ~(r);
    failedread = ~(iswrite)
  };
  secondstage : bool = undefined;
  domain : bits(4) = undefined;
  if fail then {
    domain = undefined;
    secondstage = true;
    return(AArch64_PermissionFault(ipaddress, level, acctype, ~(failedread), secondstage, s2fs1walk))
  } else return(AArch64_NoFault())
}

function AArch64_CheckAndUpdateDescriptor_SecondStage (result, fault, vaddress, acctype, iswrite, s2fs1walk, hwupdatewalk__arg) = {
  hwupdatewalk = hwupdatewalk__arg;
  hw_update_AF : bool = undefined;
  if result.AF then
    if fault.typ == Fault_None then hw_update_AF = true
    else if ConstrainUnpredictable(Unpredictable_AFUPDATE) == Constraint_TRUE then
      hw_update_AF = true
    else hw_update_AF = false
  else ();
  hw_update_AP : bool = undefined;
  write_perm_req : bool = undefined;
  if result.AP & fault.typ == Fault_None then {
    write_perm_req = (iswrite | acctype == AccType_ATOMICRW | acctype == AccType_ORDEREDRW) & ~(s2fs1walk);
    hw_update_AP = write_perm_req & ~(acctype == AccType_AT | acctype == AccType_DC) | hwupdatewalk
  } else hw_update_AP = false;
  desc : bits(64) = undefined;
  accdesc : AccessDescriptor = undefined;
  descaddr2 : AddressDescriptor = undefined;
  if hw_update_AF | hw_update_AP then {
    descaddr2 = result.descaddr;
    accdesc = CreateAccessDescriptor(AccType_ATOMICRW);
    desc = aget__Mem(descaddr2, 8, accdesc);
    if hw_update_AF then desc = __SetSlice_bits(64, 1, desc, 10, 0b1)
    else ();
    if hw_update_AP then desc = __SetSlice_bits(64, 1, desc, 7, 0b1)
    else ();
    aset__Mem(descaddr2, 8, accdesc, desc)
  } else ();
  return(fault)
}

function AArch64_TranslationTableWalk_SecondStage (ipaddress, vaddress, acctype, iswrite, s2fs1walk, 'size) = {
  assert(((HaveEL(EL2) & ~(IsSecure())) & ~(ELUsingAArch32(EL2))) & HasS2Translation());
  result : TLBRecord = undefined;
  descaddr : AddressDescriptor = undefined;
  baseregister : bits(64) = undefined;
  inputaddr : bits(64) = undefined;
  __tmp_18 : MemoryAttributes = descaddr.memattrs;
  __tmp_18.typ = MemType_Normal;
  descaddr.memattrs = __tmp_18;
  startsizecheck : int = undefined;
  inputsizecheck : int = undefined;
  startlevel : int = undefined;
  level : int = undefined;
  stride : int = undefined;
  firstblocklevel : int = undefined;
  grainsize : int = undefined;
  hierattrsdisabled : bool = undefined;
  update_AP : bool = undefined;
  update_AF : bool = undefined;
  singlepriv : bool = undefined;
  lookupsecure : bool = undefined;
  reversedescriptors : bool = undefined;
  disabled : bool = undefined;
  basefound : bool = undefined;
  ps : bits(3) = undefined;
  inputsize_min : int = undefined;
  c : Constraint = undefined;
  inputsize_max : int = undefined;
  inputsize : int = undefined;
  midgrain : bool = undefined;
  largegrain : bool = undefined;
  top : int = undefined;
  inputaddr = ZeroExtend(ipaddress);
  inputsize = 64 - UInt(slice(VTCR_EL2, 0, 6));
  largegrain = slice(VTCR_EL2, 14, 2) == 0b01;
  midgrain = slice(VTCR_EL2, 14, 2) == 0b10;
  inputsize_max = if Have52BitVAExt() & largegrain then 52 else 48;
  if inputsize > inputsize_max then {
    c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
    assert(c == Constraint_FORCE | c == Constraint_FAULT);
    if c == Constraint_FORCE then inputsize = inputsize_max
    else ()
  } else ();
  inputsize_min = 64 - 39;
  if inputsize < inputsize_min then {
    c = ConstrainUnpredictable(Unpredictable_RESTnSZ);
    assert(c == Constraint_FORCE | c == Constraint_FAULT);
    if c == Constraint_FORCE then inputsize = inputsize_min
    else ()
  } else ();
  ps = slice(VTCR_EL2, 16, 3);
  basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsZero_slice(inputaddr, inputsize, negate(inputsize) + 64);
  disabled = false;
  baseregister = VTTBR_EL2;
  descaddr.memattrs = WalkAttrDecode(slice(VTCR_EL2, 8, 2), slice(VTCR_EL2, 10, 2), slice(VTCR_EL2, 12, 2), true);
  reversedescriptors = [SCTLR_EL2[25]] == 0b1;
  lookupsecure = false;
  singlepriv = true;
  update_AF = HaveAccessFlagUpdateExt() & [VTCR_EL2[21]] == 0b1;
  update_AP = (HaveDirtyBitModifierExt() & update_AF) & [VTCR_EL2[22]] == 0b1;
  startlevel = UInt(slice(VTCR_EL2, 6, 2));
  if largegrain then {
    grainsize = 16;
    level = 3 - startlevel;
    firstblocklevel = if Have52BitPAExt() then 1 else 2
  } else if midgrain then {
    grainsize = 14;
    level = 3 - startlevel;
    firstblocklevel = 2
  } else {
    grainsize = 12;
    level = 2 - startlevel;
    firstblocklevel = 1
  };
  stride = grainsize - 3;
  if largegrain then
    if level == 0 | level == 1 & PAMax() <= 42 then basefound = false
    else ()
  else if midgrain then
    if level == 0 | level == 1 & PAMax() <= 40 then basefound = false
    else ()
  else if level < 0 | level == 0 & PAMax() <= 42 then basefound = false
  else ();
  inputsizecheck = inputsize;
  if inputsize > PAMax() & (~(ELUsingAArch32(EL1)) | inputsize > 40) then match ConstrainUnpredictable(Unpredictable_LARGEIPA) {
    Constraint_FORCE => {
      inputsize = PAMax();
      inputsizecheck = PAMax()
    },
    Constraint_FORCENOSLCHECK => inputsize = PAMax(),
    Constraint_FAULT => basefound = false,
    _ => Unreachable()
  } else ();
  startsizecheck = inputsizecheck - ((3 - level) * stride + grainsize);
  if startsizecheck < 1 | startsizecheck > stride + 4 then basefound = false
  else ();
  if ~(basefound) | disabled then {
    level = 0;
    __tmp_19 : AddressDescriptor = result.addrdesc;
    __tmp_19.fault = AArch64_TranslationFault(ipaddress, level, acctype, iswrite, true, s2fs1walk);
    result.addrdesc = __tmp_19;
    return(result)
  } else ();
  outputsize : int = undefined;
  match ps {
    0b000 => outputsize = 32,
    0b001 => outputsize = 36,
    0b010 => outputsize = 40,
    0b011 => outputsize = 42,
    0b100 => outputsize = 44,
    0b101 => outputsize = 48,
    0b110 => outputsize = if Have52BitPAExt() & largegrain then 52 else 48,
    _ => outputsize = 48
  };
  if outputsize > PAMax() then outputsize = PAMax()
  else ();
  if outputsize < 48 & ~(IsZero_slice(baseregister, outputsize, negate(outputsize) + 48)) then {
    level = 0;
    __tmp_20 : AddressDescriptor = result.addrdesc;
    __tmp_20.fault = AArch64_AddressSizeFault(ipaddress, level, acctype, iswrite, true, s2fs1walk);
    result.addrdesc = __tmp_20;
    return(result)
  } else ();
  let 'baselowerbound = ((3 + inputsize) - ((3 - level) * stride + grainsize)) : int;
  assert(constraint(0 <= 'baselowerbound & 'baselowerbound <= 48));
  baseaddress : bits(52) = undefined;
  if outputsize == 52 then let 'z = (if baselowerbound < 6 then 6 else baselowerbound) : int in {
    assert(constraint(0 <= 'z & 'z <= 48));
    baseaddress = (slice(baseregister, 2, 4) @ slice(baseregister, z, negate(z) + 48)) @ Zeros(z)
  } else
    baseaddress = ZeroExtend(slice(baseregister, baselowerbound, negate(baselowerbound) + 48) @ Zeros(baselowerbound));
  ns_table : bits(1) = if lookupsecure then 0b0 else 0b1;
  ap_table : bits(2) = 0b00;
  xn_table : bits(1) = 0b0;
  pxn_table : bits(1) = 0b0;
  addrselecttop : int = inputsize - 1;
  apply_nvnv1_effect : bool = ((HaveNVExt() & HaveEL(EL2)) & [HCR_EL2[42]] == 0b1) & [HCR_EL2[43]] == 0b1;
  blocktranslate : bool = undefined;
  desc : bits(64) = undefined;
  accdesc : AccessDescriptor = undefined;
  hwupdatewalk : bool = undefined;
  descaddr2 : AddressDescriptor = undefined;
  addrselectbottom : int = undefined;
  repeat {
    addrselectbottom = (3 - level) * stride + grainsize;
    index : bits(52) = ZeroExtend_slice_append(inputaddr, addrselectbottom, (addrselecttop - addrselectbottom) + 1, 0b000);
    __tmp_21 : FullAddress = descaddr.paddress;
    __tmp_21.physicaladdress = baseaddress | index;
    descaddr.paddress = __tmp_21;
    __tmp_22 : FullAddress = descaddr.paddress;
    __tmp_22.NS = ns_table;
    descaddr.paddress = __tmp_22;
    descaddr2 = descaddr;
    descaddr2.vaddress = ZeroExtend(vaddress);
    accdesc = CreateAccessDescriptorPTW(acctype, true, s2fs1walk, level);
    desc = aget__Mem(descaddr2, 8, accdesc);
    if reversedescriptors then desc = BigEndianReverse(desc)
    else ();
    if [desc[0]] == 0b0 | slice(desc, 0, 2) == 0b01 & level == 3 then {
      __tmp_24 : AddressDescriptor = result.addrdesc;
      __tmp_24.fault = AArch64_TranslationFault(ipaddress, level, acctype, iswrite, true, s2fs1walk);
      result.addrdesc = __tmp_24;
      return(result)
    } else ();
    if slice(desc, 0, 2) == 0b01 | level == 3 then blocktranslate = true
    else {
      if (outputsize < 52 & largegrain) & ~(IsZero(slice(desc, 12, 4))) | outputsize < 48 & ~(IsZero_slice(desc, outputsize, negate(outputsize) + 48)) then {
        __tmp_25 : AddressDescriptor = result.addrdesc;
        __tmp_25.fault = AArch64_AddressSizeFault(ipaddress, level, acctype, iswrite, true, s2fs1walk);
        result.addrdesc = __tmp_25;
        return(result)
      } else ();
      let 'gsz = grainsize;
      assert(constraint(0 <= 'gsz & 'gsz <= 48));
      if outputsize == 52 then
        baseaddress = (slice(desc, 12, 4) @ slice(desc, gsz, negate(gsz) + 48)) @ Zeros(gsz)
      else
        baseaddress = ZeroExtend(slice(desc, gsz, negate(gsz) + 48) @ Zeros(gsz));
      level = level + 1;
      addrselecttop = addrselectbottom - 1;
      blocktranslate = false
    }
  } until blocktranslate;
  if level < firstblocklevel then {
    __tmp_26 : AddressDescriptor = result.addrdesc;
    __tmp_26.fault = AArch64_TranslationFault(ipaddress, level, acctype, iswrite, true, s2fs1walk);
    result.addrdesc = __tmp_26;
    return(result)
  } else ();
  contiguousbitcheck : bool = undefined;
  if largegrain then contiguousbitcheck = level == 2 & inputsize < 34
  else if midgrain then contiguousbitcheck = level == 2 & inputsize < 30
  else contiguousbitcheck = level == 1 & inputsize < 34;
  if contiguousbitcheck & [desc[52]] == 0b1 then
    if undefined then {
      __tmp_27 : AddressDescriptor = result.addrdesc;
      __tmp_27.fault = AArch64_TranslationFault(ipaddress, level, acctype, iswrite, true, s2fs1walk);
      result.addrdesc = __tmp_27;
      return(result)
    } else ()
  else ();
  if (outputsize < 52 & largegrain) & ~(IsZero(slice(desc, 12, 4))) | outputsize < 48 & ~(IsZero_slice(desc, outputsize, negate(outputsize) + 48)) then {
    __tmp_28 : AddressDescriptor = result.addrdesc;
    __tmp_28.fault = AArch64_AddressSizeFault(ipaddress, level, acctype, iswrite, true, s2fs1walk);
    result.addrdesc = __tmp_28;
    return(result)
  } else ();
  outputaddress : bits(52) = undefined;
  let 'asb = addrselectbottom;
  assert(constraint(0 <= 'asb & 'asb <= 48));
  if outputsize == 52 then
    outputaddress = (slice(desc, 12, 4) @ slice(desc, asb, negate(asb) + 48)) @ slice(inputaddr, 0, asb)
  else
    outputaddress = ZeroExtend(slice(desc, asb, negate(asb) + 48) @ slice(inputaddr, 0, asb));
  if [desc[10]] == 0b0 then
    if ~(update_AF) then {
      __tmp_29 : AddressDescriptor = result.addrdesc;
      __tmp_29.fault = AArch64_AccessFlagFault(ipaddress, level, acctype, iswrite, true, s2fs1walk);
      result.addrdesc = __tmp_29;
      return(result)
    } else {
      __tmp_30 : DescriptorUpdate = result.descupdate;
      __tmp_30.AF = true;
      result.descupdate = __tmp_30
    }
  else ();
  if update_AP & [desc[51]] == 0b1 then
    if [desc[7]] == 0b0 then {
      desc = __SetSlice_bits(64, 1, desc, 7, 0b1);
      __tmp_32 : DescriptorUpdate = result.descupdate;
      __tmp_32.AP = true;
      result.descupdate = __tmp_32
    } else ()
  else ();
  __tmp_33 : DescriptorUpdate = result.descupdate;
  __tmp_33.descaddr = descaddr;
  result.descupdate = __tmp_33;
  xn : bits(1) = undefined;
  pxn : bits(1) = undefined;
  if apply_nvnv1_effect then {
    pxn = [desc[54]];
    xn = 0b0
  } else {
    xn = [desc[54]];
    pxn = [desc[53]]
  };
  contiguousbit : bits(1) = [desc[52]];
  nG : bits(1) = [desc[11]];
  sh : bits(2) = slice(desc, 8, 2);
  ap : bits(3) = undefined;
  if apply_nvnv1_effect then ap = [desc[7]] @ 0b01
  else ap = slice(desc, 6, 2) @ 0b1;
  memattr : bits(4) = slice(desc, 2, 4);
  result.domain = undefined;
  result.level = level;
  result.blocksize = 2 ^ ((3 - level) * stride + grainsize);
  __tmp_48 : bits(3) = result.perms.ap;
  __tmp_48 = __SetSlice_bits(3, 2, __tmp_48, 1, slice(ap, 1, 2));
  __tmp_49 : Permissions = result.perms;
  __tmp_49.ap = __tmp_48;
  result.perms = __tmp_49;
  __tmp_50 : bits(3) = result.perms.ap;
  __tmp_50 = __SetSlice_bits(3, 1, __tmp_50, 0, 0b1);
  __tmp_51 : Permissions = result.perms;
  __tmp_51.ap = __tmp_50;
  result.perms = __tmp_51;
  __tmp_52 : Permissions = result.perms;
  __tmp_52.xn = xn;
  result.perms = __tmp_52;
  if HaveExtendedExecuteNeverExt() then {
    __tmp_53 : Permissions = result.perms;
    __tmp_53.xxn = [desc[53]];
    result.perms = __tmp_53
  } else ();
  __tmp_54 : Permissions = result.perms;
  __tmp_54.pxn = 0b0;
  result.perms = __tmp_54;
  result.nG = 0b0;
  __tmp_55 : AddressDescriptor = result.addrdesc;
  __tmp_55.memattrs = S2AttrDecode(sh, memattr, acctype);
  result.addrdesc = __tmp_55;
  __tmp_56 : FullAddress = result.addrdesc.paddress;
  __tmp_56.NS = 0b1;
  __tmp_57 : AddressDescriptor = result.addrdesc;
  __tmp_57.paddress = __tmp_56;
  result.addrdesc = __tmp_57;
  __tmp_58 : FullAddress = result.addrdesc.paddress;
  __tmp_58.physicaladdress = outputaddress;
  __tmp_59 : AddressDescriptor = result.addrdesc;
  __tmp_59.paddress = __tmp_58;
  result.addrdesc = __tmp_59;
  __tmp_60 : AddressDescriptor = result.addrdesc;
  __tmp_60.fault = AArch64_NoFault();
  result.addrdesc = __tmp_60;
  result.contiguous = contiguousbit == 0b1;
  if HaveCommonNotPrivateTransExt() then result.CnP = [baseregister[0]]
  else ();
  return(result)
}

function AArch64_SecondStageTranslate (S1, vaddress, acctype, iswrite, wasaligned, s2fs1walk, 'size, hwupdatewalk) = {
  assert(HasS2Translation(), "HasS2Translation()");
  s2_enabled : bool = [HCR_EL2[0]] == 0b1 | [HCR_EL2[12]] == 0b1;
  secondstage : bool = true;
  result : AddressDescriptor = undefined;
  S2 : TLBRecord = undefined;
  ipaddress : bits(52) = undefined;
  if s2_enabled then {
    ipaddress = slice(S1.paddress.physicaladdress, 0, 52);
    S2 = AArch64_TranslationTableWalk_SecondStage(ipaddress, vaddress, acctype, iswrite, s2fs1walk, size);
    if ((~(wasaligned) & acctype != AccType_IFETCH | acctype == AccType_DCZVA) & S2.addrdesc.memattrs.typ == MemType_Device) & ~(IsFault(S2.addrdesc)) then {
      __tmp_71 : AddressDescriptor = S2.addrdesc;
      __tmp_71.fault = AArch64_AlignmentFault(acctype, iswrite, secondstage);
      S2.addrdesc = __tmp_71
    } else ();
    if ~(IsFault(S2.addrdesc)) then {
      __tmp_72 : AddressDescriptor = S2.addrdesc;
      __tmp_72.fault = AArch64_CheckS2Permission(S2.perms, vaddress, ipaddress, S2.level, acctype, iswrite, s2fs1walk, hwupdatewalk);
      S2.addrdesc = __tmp_72
    } else ();
    if ((~(s2fs1walk) & ~(IsFault(S2.addrdesc))) & S2.addrdesc.memattrs.typ == MemType_Device) & acctype == AccType_IFETCH then
      S2.addrdesc = AArch64_InstructionDevice(S2.addrdesc, vaddress, ipaddress, S2.level, acctype, iswrite, secondstage, s2fs1walk)
    else ();
    if ((s2fs1walk & ~(IsFault(S2.addrdesc))) & [HCR_EL2[2]] == 0b1) & S2.addrdesc.memattrs.typ == MemType_Device then {
      __tmp_73 : AddressDescriptor = S2.addrdesc;
      __tmp_73.fault = AArch64_PermissionFault(ipaddress, S2.level, acctype, iswrite, secondstage, s2fs1walk);
      S2.addrdesc = __tmp_73
    } else ();
    __tmp_74 : AddressDescriptor = S2.addrdesc;
    __tmp_74.fault = AArch64_CheckAndUpdateDescriptor_SecondStage(S2.descupdate, S2.addrdesc.fault, vaddress, acctype, iswrite, s2fs1walk, hwupdatewalk);
    S2.addrdesc = __tmp_74;
    result = CombineS1S2Desc(S1, S2.addrdesc)
  } else result = S1;
  return(result)
}

function AArch64_CheckAndUpdateDescriptor (result, fault, secondstage, vaddress, acctype, iswrite, s2fs1walk, hwupdatewalk__arg) = {
  let reversedescriptors = (aget_SCTLR()[25] == bitone);
  hwupdatewalk = hwupdatewalk__arg;
  hw_update_AF : bool = undefined;
  if result.AF then if fault.typ == Fault_None then hw_update_AF = true else if ConstrainUnpredictable(Unpredictable_AFUPDATE) == Constraint_TRUE then hw_update_AF = true else hw_update_AF = false else hw_update_AF = false;
  hw_update_AP : bool = undefined;
  write_perm_req : bool = undefined;
  if result.AP & fault.typ == Fault_None then {
    write_perm_req = (iswrite | acctype == AccType_ATOMICRW | acctype == AccType_ORDEREDRW) & ~(s2fs1walk);
    hw_update_AP = write_perm_req & ~(acctype == AccType_AT | acctype == AccType_DC) | hwupdatewalk
  } else hw_update_AP = false;
  desc : bits(64) = undefined;
  accdesc : AccessDescriptor = undefined;
  descaddr2 : AddressDescriptor = undefined;
  if hw_update_AF | hw_update_AP then {
    if secondstage | ~(HasS2Translation()) then descaddr2 = result.descaddr else {
      hwupdatewalk = true;
      descaddr2 = AArch64_SecondStageWalk(result.descaddr, vaddress, acctype, iswrite, 8, hwupdatewalk);
      if IsFault(descaddr2) then return(descaddr2.fault) else ()
    };
    accdesc = CreateAccessDescriptor(AccType_ATOMICRW);
    desc = aget__Mem(descaddr2, 8, accdesc);
    if reversedescriptors then desc = BigEndianReverse(desc) else ();
    if hw_update_AF then desc = __SetSlice_bits(64, 1, desc, 10, 0b1) else ();
    if hw_update_AP then desc = __SetSlice_bits(64, 1, desc, 7, if secondstage then 0b1 else 0b0) else ();
    if reversedescriptors then desc = BigEndianReverse(desc) else ();
    aset__Mem(descaddr2, 8, accdesc, desc)
  } else ();
  return(fault)
}

val AArch64_BreakpointValueMatch : (int, bits(64), bool) -> bool

function AArch64_BreakpointValueMatch (n__arg, vaddress, linked_to) = false

val AArch64_StateMatch : (bits(2), bits(1), bits(2), bool, bits(4), bool, bool) -> bool effect {rreg, undef, escape}

function AArch64_StateMatch (SSC__arg, HMC__arg, PxC__arg, linked__arg, LBN, isbreakpnt, ispriv) = {
  HMC = HMC__arg;
  PxC = PxC__arg;
  SSC = SSC__arg;
  linked = linked__arg;
  c : Constraint = undefined;
  if (((((((HMC @ SSC) @ PxC) & 0b11100) == 0b01100 | (((HMC @ SSC) @ PxC) & 0b11101) == 0b10000 | (((HMC @ SSC) @ PxC) & 0b11101) == 0b10100 | ((HMC @ SSC) @ PxC) == 0b11010 | ((HMC @ SSC) @ PxC) == 0b11101 | (((HMC @ SSC) @ PxC) & 0b11110) == 0b11110) | (HMC == 0b0 & PxC == 0b00) & (~(isbreakpnt) | ~(HaveAArch32EL(EL1)))) | (SSC == 0b01 | SSC == 0b10) & ~(HaveEL(EL3))) | (((HMC @ SSC) != 0b000 & (HMC @ SSC) != 0b111) & ~(HaveEL(EL3))) & ~(HaveEL(EL2))) | ((HMC @ SSC) @ PxC) == 0b11100 & ~(HaveEL(EL2)) then {
    __tmp_5 : bits(5) = undefined;
    (c, __tmp_5) = ConstrainUnpredictableBits(Unpredictable_RESBPWPCTRL) : (Constraint, bits(5));
    __tmp_6 : bits(5) = __tmp_5;
    HMC = [__tmp_6[4]];
    __tmp_7 : bits(4) = slice(__tmp_6, 0, 4);
    SSC = slice(__tmp_7, 2, 2);
    PxC = slice(__tmp_7, 0, 2);
    assert(c == Constraint_DISABLED | c == Constraint_UNKNOWN, "((c == Constraint_DISABLED) || (c == Constraint_UNKNOWN))");
    if c == Constraint_DISABLED then return(false) else ()
  } else ();
  EL3_match : bool = (HaveEL(EL3) & HMC == 0b1) & [SSC[0]] == 0b0;
  EL2_match : bool = HaveEL(EL2) & HMC == 0b1;
  EL1_match : bool = [PxC[0]] == 0b1;
  EL0_match : bool = [PxC[1]] == 0b1;
  priv_match : bool = undefined;
  if ~(ispriv) & ~(isbreakpnt) then priv_match = EL0_match
  else match PSTATE.EL {
    ? if ? == EL3 => priv_match = EL3_match,
    ? if ? == EL2 => priv_match = EL2_match,
    ? if ? == EL1 => priv_match = EL1_match,
    ? if ? == EL0 => priv_match = EL0_match
  };
  security_state_match : bool = undefined;
  match SSC {
    0b00 => security_state_match = true,
    0b01 => security_state_match = ~(IsSecure()),
    0b10 => security_state_match = IsSecure(),
    0b11 => security_state_match = true
  };
  last_ctx_cmp : int = undefined;
  first_ctx_cmp : int = undefined;
  lbn : int = undefined;
  if linked then {
    lbn = UInt(LBN);
    first_ctx_cmp = UInt(slice(ID_AA64DFR0_EL1, 12, 4)) - UInt(slice(ID_AA64DFR0_EL1, 28, 4));
    last_ctx_cmp = UInt(slice(ID_AA64DFR0_EL1, 12, 4));
    if lbn < first_ctx_cmp | lbn > last_ctx_cmp then {
      (c, lbn) = ConstrainUnpredictableInteger(first_ctx_cmp, last_ctx_cmp, Unpredictable_BPNOTCTXCMP);
      assert(c == Constraint_DISABLED | c == Constraint_NONE | c == Constraint_UNKNOWN, "((c == Constraint_DISABLED) || ((c == Constraint_NONE) || (c == Constraint_UNKNOWN)))");
      match c {
        Constraint_DISABLED => return(false),
        Constraint_NONE => linked = false
      }
    } else ()
  } else ();
  linked_match : bool = undefined;
  linked_to : bool = undefined;
  vaddress : bits(64) = undefined;
  if linked then {
    vaddress = undefined;
    linked_to = true;
    linked_match = AArch64_BreakpointValueMatch(lbn, vaddress, linked_to)
  } else ();
  return((priv_match & security_state_match) & (~(linked) | linked_match))
}

val AArch64_WatchpointMatch : (int, bits(64), int, bool, bool) -> bool effect {escape, rreg, undef}

function AArch64_WatchpointMatch ('n, vaddress, 'size, ispriv, iswrite) = {
  assert(~(ELUsingAArch32(S1TranslationRegime())), "!(ELUsingAArch32(S1TranslationRegime()))");
  assert(n <= UInt(slice(ID_AA64DFR0_EL1, 20, 4)), "(n <= UInt((ID_AA64DFR0_EL1).WRPs))");
  enabled : bool = [DBGWCR_EL1[n][0]] == 0b1;
  linked : bool = [DBGWCR_EL1[n][20]] == 0b1;
  isbreakpnt : bool = false;
  state_match : bool = AArch64_StateMatch(slice(DBGWCR_EL1[n], 14, 2), [DBGWCR_EL1[n][13]], slice(DBGWCR_EL1[n], 1, 2), linked, slice(DBGWCR_EL1[n], 16, 4), isbreakpnt, ispriv);
  ls_match : bool = [slice(DBGWCR_EL1[n], 3, 2)[if iswrite then 1 else 0]] == 0b1;
  value_match_name : bool = false;
  foreach (byte from 0 to (size - 1) by 1 in inc)
    value_match_name = value_match_name | AArch64_WatchpointByteMatch(n, vaddress + byte);
  return(((value_match_name & state_match) & ls_match) & enabled)
}

val AArch64_BreakpointMatch : (int, bits(64), int) -> bool effect {escape, rreg, undef}

function AArch64_BreakpointMatch ('n, vaddress, 'size) = {
  assert(~(ELUsingAArch32(S1TranslationRegime())), "!(ELUsingAArch32(S1TranslationRegime()))");
  assert(n <= UInt(slice(ID_AA64DFR0_EL1, 12, 4)), "(n <= UInt((ID_AA64DFR0_EL1).BRPs))");
  enabled : bool = [DBGBCR_EL1[n][0]] == 0b1;
  ispriv : bool = PSTATE.EL != EL0;
  linked : bool = (slice(DBGBCR_EL1[n], 20, 4) & 0xB) == 0x1;
  isbreakpnt : bool = true;
  linked_to : bool = false;
  state_match : bool = AArch64_StateMatch(slice(DBGBCR_EL1[n], 14, 2), [DBGBCR_EL1[n][13]], slice(DBGBCR_EL1[n], 1, 2), linked, slice(DBGBCR_EL1[n], 16, 4), isbreakpnt, ispriv);
  value_match_name : bool = AArch64_BreakpointValueMatch(n, vaddress, linked_to);
  match_i : bool = undefined;
  if HaveAnyAArch32() & size == 4 then {
    match_i = AArch64_BreakpointValueMatch(n, vaddress + 2, linked_to);
    if ~(value_match_name) & match_i then value_match_name = ConstrainUnpredictableBool(Unpredictable_BPMATCHHALF) else ()
  } else ();
  if [vaddress[1]] == 0b1 & slice(DBGBCR_EL1[n], 5, 4) == 0xF then if value_match_name then value_match_name = ConstrainUnpredictableBool(Unpredictable_BPMATCHHALF) else () else ();
  val_match : bool = (value_match_name & state_match) & enabled;
  return(val_match)
}

val AArch64_CheckBreakpoint : (bits(64), int) -> FaultRecord effect {wreg, rreg, undef, escape}

function AArch64_CheckBreakpoint (vaddress, size) = {
  assert(~(ELUsingAArch32(S1TranslationRegime())), "!(ELUsingAArch32(S1TranslationRegime()))");
  assert(UsingAArch32() & (size == 2 | size == 4) | size == 4, "((UsingAArch32() && ((size == 2) || (size == 4))) || (size == 4))");
  val_match : bool = false;
  match_i : bool = undefined;
  foreach (i from 0 to UInt(slice(ID_AA64DFR0_EL1, 12, 4)) by 1 in inc) {
    match_i = AArch64_BreakpointMatch(i, vaddress, size);
    val_match = val_match | match_i
  };
  iswrite : bool = undefined;
  acctype : AccType = undefined;
  reason : bits(6) = undefined;
  if val_match & HaltOnBreakpointOrWatchpoint() then {
    reason = DebugHalt_Breakpoint;
    Halt(reason);
    undefined : FaultRecord
  } else if (val_match & [MDSCR_EL1[15]] == 0b1) & AArch64_GenerateDebugExceptions() then {
    acctype = AccType_IFETCH;
    iswrite = false;
    return(AArch64_DebugFault(acctype, iswrite))
  } else return(AArch64_NoFault())
}

val AArch64_BranchAddr : bits(64) -> bits(64) effect {rreg, undef, escape}

function AArch64_BranchAddr vaddress = {
  assert(~(UsingAArch32()), "!(UsingAArch32())");
  msbit : nat = coerce_int_nat(AddrTop(vaddress, true, PSTATE.EL));
  if msbit == 63 then return(vaddress) else if ((PSTATE.EL == EL0 | PSTATE.EL == EL1) | IsInHost()) & [vaddress[msbit]] == 0b1 then return(SignExtend(slice(vaddress, 0, msbit + 1))) else return(ZeroExtend(slice(vaddress, 0, msbit + 1)))
}

val BranchTo : forall ('N : Int), 'N >= 0.
  (bits('N), BranchType) -> unit effect {escape, rreg, undef, wreg}

function BranchTo (target, branch_type) = {
  __BranchTaken = true;
  Hint_Branch(branch_type);
  if 'N == 32 then {
    assert(UsingAArch32(), "UsingAArch32()");
    _PC = ZeroExtend(target)
  } else {
    assert('N == 64 & ~(UsingAArch32()), "((N == 64) && !(UsingAArch32()))");
    _PC = AArch64_BranchAddr(slice(target, 0, 64))
  };
  ()
}

val aarch64_branch_unconditional_immediate : (BranchType, bits(64)) -> unit effect {escape, rreg, undef, wreg}

function aarch64_branch_unconditional_immediate (branch_type, offset) = {
  if branch_type == BranchType_CALL then aset_X(30, aget_PC() + 4) else ();
  BranchTo(aget_PC() + offset, branch_type)
}

val branch_unconditional_immediate_decode : (bits(1), bits(26)) -> unit effect {escape, rreg, undef, wreg}

function branch_unconditional_immediate_decode (op, imm26) = {
  __unconditional = true;
  branch_type : BranchType = if op == 0b1 then BranchType_CALL else BranchType_JMP;
  offset : bits(64) = SignExtend(imm26 @ 0b00, 64);
  aarch64_branch_unconditional_immediate(branch_type, offset)
}

val aarch64_branch_conditional_test : (int, bits(1), int, bits(64), int) -> unit effect {escape, rreg, undef, wreg}

function aarch64_branch_conditional_test ('bit_pos, bit_val, 'datasize, offset, 't) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  operand : bits('datasize) = aget_X(t);
  if [operand[bit_pos]] == bit_val then BranchTo(aget_PC() + offset, BranchType_JMP) else ()
}

val branch_conditional_test_decode : (bits(1), bits(1), bits(5), bits(14), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function branch_conditional_test_decode (b5, op, b40, imm14, Rt) = {
  __unconditional = true;
  t : int = UInt(Rt);
  let 'datasize : {|64, 32|} = if b5 == 0b1 then 64 else 32;
  bit_pos : int = UInt(b5 @ b40);
  bit_val : bits(1) = op;
  offset : bits(64) = SignExtend(imm14 @ 0b00, 64);
  aarch64_branch_conditional_test(bit_pos, bit_val, datasize, offset, t)
}

val aarch64_branch_conditional_cond : (bits(4), bits(64)) -> unit effect {escape, rreg, undef, wreg}

function aarch64_branch_conditional_cond (condition, offset) = if ConditionHolds(condition) then BranchTo(aget_PC() + offset, BranchType_JMP) else ()

val branch_conditional_cond_decode : (bits(1), bits(19), bits(1), bits(4)) -> unit effect {escape, rreg, undef, wreg}

function branch_conditional_cond_decode (o1, imm19, o0, cond) = {
  __unconditional = true;
  offset : bits(64) = SignExtend(imm19 @ 0b00, 64);
  condition : bits(4) = cond;
  aarch64_branch_conditional_cond(condition, offset)
}

val aarch64_branch_conditional_compare : (int, bool, bits(64), int) -> unit effect {escape, rreg, undef, wreg}

function aarch64_branch_conditional_compare ('datasize, iszero, offset, 't) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  operand1 : bits('datasize) = aget_X(t);
  if IsZero(operand1) == iszero then BranchTo(aget_PC() + offset, BranchType_JMP) else ()
}

val branch_conditional_compare_decode : (bits(1), bits(1), bits(19), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function branch_conditional_compare_decode (sf, op, imm19, Rt) = {
  __unconditional = true;
  t : int = UInt(Rt);
  let 'datasize : {|64, 32|} = if sf == 0b1 then 64 else 32;
  iszero : bool = op == 0b0;
  offset : bits(64) = SignExtend(imm19 @ 0b00, 64);
  aarch64_branch_conditional_compare(datasize, iszero, offset, t)
}

val AArch64_TakeReset : bool -> unit effect {escape, rreg, undef, wreg}

function AArch64_TakeReset cold_reset = {
  assert(~(HighestELUsingAArch32()), "!(HighestELUsingAArch32())");
  PSTATE.nRW = 0b0;
  if HaveEL(EL3) then PSTATE.EL = EL3
  else if HaveEL(EL2) then PSTATE.EL = EL2
  else PSTATE.EL = EL1;
  AArch64_ResetControlRegisters(cold_reset);
  PSTATE.SP = 0b1;
  (PSTATE.D @ PSTATE.A @ PSTATE.I @ PSTATE.F) = 0xF;
  PSTATE.SS = 0b0;
  PSTATE.IL = 0b0;
  AArch64_ResetGeneralRegisters();
  AArch64_ResetSIMDFPRegisters();
  AArch64_ResetSpecialRegisters();
  ResetExternalDebugRegisters(cold_reset);
  rv : bits(64) = undefined;
  if HaveEL(EL3) then rv = RVBAR_EL3
  else if HaveEL(EL2) then rv = RVBAR_EL2
  else rv = RVBAR_EL1;
  assert(IsZero_slice(rv, PAMax(), 64 - PAMax()) & IsZero_slice(rv, 0, 2), "(IsZero((rv)<PAMax()+:((63 - PAMax()) + 1)>) && IsZero((rv)<0+:((1 - 0) + 1)>))");
  BranchTo(rv, BranchType_UNKNOWN)
}

val __TakeColdReset : unit -> unit effect {escape, rreg, undef, wreg}

function __TakeColdReset () = {
  PSTATE.nRW = 0b0;
  PSTATE.SS = 0b0;
  __ResetInterruptState();
  __ResetMemoryState();
  __ResetExecuteState();
  AArch64_TakeReset(true)
}

val AArch64_TakeException : (bits(2), ExceptionRecord, bits(64), int) -> unit effect {escape, rreg, undef, wreg}

function AArch64_TakeException (target_el, exception, preferred_exception_return, vect_offset__arg) = {
  vect_offset : int = vect_offset__arg;
  SynchronizeContext();
  assert((HaveEL(target_el) & ~(ELUsingAArch32(target_el))) & UInt(target_el) >= UInt(PSTATE.EL), "((HaveEL(target_el) && !(ELUsingAArch32(target_el))) && (UInt(target_el) >= UInt((PSTATE).EL)))");
  from_32 : bool = UsingAArch32();
  if from_32 then AArch64_MaybeZeroRegisterUppers() else ();
  if UInt(target_el) > UInt(PSTATE.EL) then {
    lower_32 : bool = undefined;
    if target_el == EL3 then
      if ~(IsSecure()) & HaveEL(EL2) then lower_32 = ELUsingAArch32(EL2)
      else lower_32 = ELUsingAArch32(EL1)
    else if (IsInHost() & PSTATE.EL == EL0) & target_el == EL2 then
      lower_32 = ELUsingAArch32(EL0)
    else lower_32 = ELUsingAArch32(target_el - 1);
    vect_offset = vect_offset + (if lower_32 then 1536 else 1024)
  } else if PSTATE.SP == 0b1 then vect_offset = vect_offset + 512
  else ();
  spsr : bits(32) = GetPSRFromPSTATE();
  if HaveUAOExt() then PSTATE.UAO = 0b0
  else ();
  if ~(exception.typ == Exception_IRQ | exception.typ == Exception_FIQ) then AArch64_ReportException(exception, target_el) else ();
  PSTATE.EL = target_el;
  PSTATE.nRW = 0b0;
  PSTATE.SP = 0b1;
  aset_SPSR(spsr);
  aset_ELR(preferred_exception_return);
  PSTATE.SS = 0b0;
  (PSTATE.D @ PSTATE.A @ PSTATE.I @ PSTATE.F) = 0xF;
  PSTATE.IL = 0b0;
  if from_32 then {
    PSTATE.IT = 0x00;
    PSTATE.T = 0b0
  } else ();
  if (HavePANExt() & (PSTATE.EL == EL1 | PSTATE.EL == EL2 & ELIsInHost(EL0))) & [aget_SCTLR()[23]] == 0b0 then
    PSTATE.PAN = 0b1
  else ();
  BranchTo(slice(aget_VBAR(), 11, 53) @ __GetSlice_int(11, vect_offset, 0), BranchType_EXCEPTION);
  iesb_req : bool = undefined;
  if HaveRASExt() & [aget_SCTLR()[21]] == 0b1 then {
    ErrorSynchronizationBarrier(MBReqDomain_FullSystem, MBReqTypes_All);
    iesb_req = true;
    TakeUnmaskedPhysicalSErrorInterrupts(iesb_req)
  } else ();
  EndOfInstruction()
}

val TrapPACUse : bits(2) -> unit effect {escape, rreg, undef, wreg}

function TrapPACUse target_el = {
  assert((HaveEL(target_el) & target_el != EL0) & UInt(target_el) >= UInt(PSTATE.EL), "((HaveEL(target_el) && (target_el != EL0)) && (UInt(target_el) >= UInt((PSTATE).EL)))");
  preferred_exception_return : bits(64) = ThisInstrAddr();
  exception : ExceptionRecord = undefined;
  vect_offset : int = 0;
  exception = ExceptionSyndrome(Exception_PACTrap);
  AArch64_TakeException(target_el, exception, preferred_exception_return, vect_offset)
}

val Strip : (bits(64), bool) -> bits(64) effect {wreg, rreg, escape, undef}

function Strip (A, data) = {
  TrapEL2 : bool = undefined;
  TrapEL3 : bool = undefined;
  original_ptr : bits(64) = undefined;
  extfield : bits(64) = undefined;
  tbi : bool = CalculateTBI(A, data);
  let 'bottom_PAC_bit = ex_int(CalculateBottomPACBit(A, [A[55]]));
  assert(constraint(0 <= 'bottom_PAC_bit & 'bottom_PAC_bit <= 56));
  extfield = replicate_bits([A[55]], 64);
  if tbi then
    original_ptr = (slice(A, 56, 8) @ slice(extfield, 0, negate(bottom_PAC_bit) + 56)) @ slice(A, 0, bottom_PAC_bit)
  else
    original_ptr = slice(extfield, 0, negate(bottom_PAC_bit) + 64) @ slice(A, 0, bottom_PAC_bit);
  match PSTATE.EL {
    ? if ? == EL0 => {
      IsEL1Regime : bool = (~(HaveEL(EL2)) | [HCR_EL2[27]] == 0b0) | [HCR_EL2[34]] == 0b0;
      TrapEL2 = ((HaveEL(EL2) & IsEL1Regime) & ~(IsSecure())) & [HCR_EL2[41]] == 0b0;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL1 => {
      TrapEL2 = (HaveEL(EL2) & ~(IsSecure())) & [HCR_EL2[41]] == 0b0;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL2 => {
      TrapEL2 = false;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL3 => {
      TrapEL2 = false;
      TrapEL3 = false
    }
  };
  if TrapEL2 then {
    TrapPACUse(EL2);
    undefined
  } else if TrapEL3 then {
    TrapPACUse(EL3);
    undefined
  } else return(original_ptr)
}

val aarch64_integer_pac_strip_dp_1src : (int, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_pac_strip_dp_1src ('d, data) = if HavePACExt() then aset_X(d, Strip(aget_X(d), data)) else ()

val integer_pac_strip_hint_decode : (bits(1), bits(2), bits(3), bits(4), bits(4), bits(3), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_pac_strip_hint_decode (L, op0, op1, CRn, CRm, op2, Rt) = {
  __unconditional = true;
  d : int = 30;
  data : bool = false;
  aarch64_integer_pac_strip_dp_1src(d, data)
}

val AuthIB : (bits(64), bits(64)) -> bits(64) effect {escape, wreg, rreg, undef}

function AuthIB (X, Y) = {
  TrapEL2 : bool = undefined;
  TrapEL3 : bool = undefined;
  Enable : bits(1) = undefined;
  APIBKey_EL1 : bits(128) = slice(APIBKeyHi_EL1, 0, 64) @ slice(APIBKeyLo_EL1, 0, 64);
  match PSTATE.EL {
    ? if ? == EL0 => {
      IsEL1Regime : bool = (~(HaveEL(EL2)) | [HCR_EL2[27]] == 0b0) | [HCR_EL2[34]] == 0b0;
      Enable = if IsEL1Regime then [SCTLR_EL1[30]] else [SCTLR_EL2[30]];
      TrapEL2 = ((HaveEL(EL2) & IsEL1Regime) & ~(IsSecure())) & [HCR_EL2[41]] == 0b0;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL1 => {
      Enable = [SCTLR_EL1[30]];
      TrapEL2 = (HaveEL(EL2) & ~(IsSecure())) & [HCR_EL2[41]] == 0b0;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL2 => {
      Enable = [SCTLR_EL2[30]];
      TrapEL2 = false;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL3 => {
      Enable = [SCTLR_EL3[30]];
      TrapEL2 = false;
      TrapEL3 = false
    }
  };
  if Enable == 0b0 then return(X) else if TrapEL2 then {
    TrapPACUse(EL2);
    undefined
  } else if TrapEL3 then {
    TrapPACUse(EL3);
    undefined
  } else return(Auth(X, Y, APIBKey_EL1, false, 0b1))
}

val aarch64_integer_pac_autib_dp_1src : (int, int, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_pac_autib_dp_1src ('d, 'n, source_is_sp) = if HavePACExt() then if source_is_sp then aset_X(d, AuthIB(aget_X(d), aget_SP())) else aset_X(d, AuthIB(aget_X(d), aget_X(n))) else ()

val integer_pac_autib_hint_decode : (bits(1), bits(2), bits(3), bits(4), bits(4), bits(3), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_pac_autib_hint_decode (L, op0, op1, CRn, CRm, op2, Rt) = {
  __unconditional = true;
  d : int = undefined;
  n : int = undefined;
  source_is_sp : bool = false;
  match CRm @ op2 {
    0b0011110 => {
      d = 30;
      n = 31
    },
    0b0011111 => {
      d = 30;
      source_is_sp = true
    },
    0b0001110 => {
      d = 17;
      n = 16
    },
    0b0001000 => throw(Error_See("PACIA")),
    0b0001010 => throw(Error_See("PACIB")),
    0b0001100 => throw(Error_See("AUTIA")),
    [bitzero] @ [bitzero] @ [bitone] @ [bitone] @ [bitzero] @ [bitzero] @ _ : bits(1) => throw(Error_See("PACIA")),
    [bitzero] @ [bitzero] @ [bitone] @ [bitone] @ [bitzero] @ [bitone] @ _ : bits(1) => throw(Error_See("PACIB")),
    [bitzero] @ [bitzero] @ [bitone] @ [bitone] @ [bitone] @ [bitzero] @ _ : bits(1) => throw(Error_See("AUTIA")),
    0b0000111 => throw(Error_See("XPACLRI"))
  };
  aarch64_integer_pac_autib_dp_1src(d, n, source_is_sp)
}

val AuthIA : (bits(64), bits(64)) -> bits(64) effect {escape, wreg, rreg, undef}

function AuthIA (X, Y) = {
  TrapEL2 : bool = undefined;
  TrapEL3 : bool = undefined;
  Enable : bits(1) = undefined;
  APIAKey_EL1 : bits(128) = slice(APIAKeyHi_EL1, 0, 64) @ slice(APIAKeyLo_EL1, 0, 64);
  match PSTATE.EL {
    ? if ? == EL0 => {
      IsEL1Regime : bool = (~(HaveEL(EL2)) | [HCR_EL2[27]] == 0b0) | [HCR_EL2[34]] == 0b0;
      Enable = if IsEL1Regime then [SCTLR_EL1[31]] else [SCTLR_EL2[31]];
      TrapEL2 = ((HaveEL(EL2) & IsEL1Regime) & ~(IsSecure())) & [HCR_EL2[41]] == 0b0;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL1 => {
      Enable = [SCTLR_EL1[31]];
      TrapEL2 = (HaveEL(EL2) & ~(IsSecure())) & [HCR_EL2[41]] == 0b0;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL2 => {
      Enable = [SCTLR_EL2[31]];
      TrapEL2 = false;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL3 => {
      Enable = [SCTLR_EL3[31]];
      TrapEL2 = false;
      TrapEL3 = false
    }
  };
  if Enable == 0b0 then return(X) else if TrapEL2 then {
    TrapPACUse(EL2);
    undefined
  } else if TrapEL3 then {
    TrapPACUse(EL3);
    undefined
  } else return(Auth(X, Y, APIAKey_EL1, false, 0b0))
}

val aarch64_integer_pac_autia_dp_1src : (int, int, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_pac_autia_dp_1src ('d, 'n, source_is_sp) = if HavePACExt() then if source_is_sp then aset_X(d, AuthIA(aget_X(d), aget_SP())) else aset_X(d, AuthIA(aget_X(d), aget_X(n))) else ()

val integer_pac_autia_hint_decode : (bits(1), bits(2), bits(3), bits(4), bits(4), bits(3), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_pac_autia_hint_decode (L, op0, op1, CRn, CRm, op2, Rt) = {
  __unconditional = true;
  d : int = undefined;
  n : int = undefined;
  source_is_sp : bool = false;
  match CRm @ op2 {
    0b0011100 => {
      d = 30;
      n = 31
    },
    0b0011101 => {
      d = 30;
      source_is_sp = true
    },
    0b0001100 => {
      d = 17;
      n = 16
    },
    0b0001000 => throw(Error_See("PACIA")),
    0b0001010 => throw(Error_See("PACIB")),
    0b0001110 => throw(Error_See("AUTIB")),
    [bitzero] @ [bitzero] @ [bitone] @ [bitone] @ [bitzero] @ [bitzero] @ _ : bits(1) => throw(Error_See("PACIA")),
    [bitzero] @ [bitzero] @ [bitone] @ [bitone] @ [bitzero] @ [bitone] @ _ : bits(1) => throw(Error_See("PACIB")),
    [bitzero] @ [bitzero] @ [bitone] @ [bitone] @ [bitone] @ [bitone] @ _ : bits(1) => throw(Error_See("AUTIB")),
    0b0000111 => throw(Error_See("XPACLRI")),
    _ => throw(Error_See("HINT"))
  };
  aarch64_integer_pac_autia_dp_1src(d, n, source_is_sp)
}

val aarch64_branch_unconditional_register : (BranchType, int, int, bool, bool, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_branch_unconditional_register (branch_type, 'm, 'n, pac, source_is_sp, use_key_a) = {
  target : bits(64) = aget_X(n);
  if pac then {
    modifier : bits(64) = if source_is_sp then aget_SP() else aget_X(m);
    if use_key_a then target = AuthIA(target, modifier) else target = AuthIB(target, modifier)
  } else ();
  if branch_type == BranchType_CALL then aset_X(30, aget_PC() + 4) else ();
  BranchTo(target, branch_type)
}

val AuthDB : (bits(64), bits(64)) -> bits(64) effect {undef, escape, wreg, rreg}

function AuthDB (X, Y) = {
  TrapEL2 : bool = undefined;
  TrapEL3 : bool = undefined;
  Enable : bits(1) = undefined;
  APDBKey_EL1 : bits(128) = slice(APDBKeyHi_EL1, 0, 64) @ slice(APDBKeyLo_EL1, 0, 64);
  match PSTATE.EL {
    ? if ? == EL0 => {
      IsEL1Regime : bool = (~(HaveEL(EL2)) | [HCR_EL2[27]] == 0b0) | [HCR_EL2[34]] == 0b0;
      Enable = if IsEL1Regime then [SCTLR_EL1[13]] else [SCTLR_EL2[13]];
      TrapEL2 = ((HaveEL(EL2) & IsEL1Regime) & ~(IsSecure())) & [HCR_EL2[41]] == 0b0;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL1 => {
      Enable = [SCTLR_EL1[13]];
      TrapEL2 = (HaveEL(EL2) & ~(IsSecure())) & [HCR_EL2[41]] == 0b0;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL2 => {
      Enable = [SCTLR_EL2[13]];
      TrapEL2 = false;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL3 => {
      Enable = [SCTLR_EL3[13]];
      TrapEL2 = false;
      TrapEL3 = false
    }
  };
  if Enable == 0b0 then return(X) else if TrapEL2 then {
    TrapPACUse(EL2);
    undefined
  } else if TrapEL3 then {
    TrapPACUse(EL3);
    undefined
  } else return(Auth(X, Y, APDBKey_EL1, true, 0b1))
}

val aarch64_integer_pac_autdb_dp_1src : (int, int, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_pac_autdb_dp_1src ('d, 'n, source_is_sp) = if source_is_sp then aset_X(d, AuthDB(aget_X(d), aget_SP())) else aset_X(d, AuthDB(aget_X(d), aget_X(n)))

val AuthDA : (bits(64), bits(64)) -> bits(64) effect {undef, escape, wreg, rreg}

function AuthDA (X, Y) = {
  TrapEL2 : bool = undefined;
  TrapEL3 : bool = undefined;
  Enable : bits(1) = undefined;
  APDAKey_EL1 : bits(128) = slice(APDAKeyHi_EL1, 0, 64) @ slice(APDAKeyLo_EL1, 0, 64);
  match PSTATE.EL {
    ? if ? == EL0 => {
      IsEL1Regime : bool = (~(HaveEL(EL2)) | [HCR_EL2[27]] == 0b0) | [HCR_EL2[34]] == 0b0;
      Enable = if IsEL1Regime then [SCTLR_EL1[27]] else [SCTLR_EL2[27]];
      TrapEL2 = ((HaveEL(EL2) & IsEL1Regime) & ~(IsSecure())) & [HCR_EL2[41]] == 0b0;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL1 => {
      Enable = [SCTLR_EL1[27]];
      TrapEL2 = (HaveEL(EL2) & ~(IsSecure())) & [HCR_EL2[41]] == 0b0;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL2 => {
      Enable = [SCTLR_EL2[27]];
      TrapEL2 = false;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL3 => {
      Enable = [SCTLR_EL3[27]];
      TrapEL2 = false;
      TrapEL3 = false
    }
  };
  if Enable == 0b0 then return(X) else if TrapEL2 then {
    TrapPACUse(EL2);
    undefined
  } else if TrapEL3 then {
    TrapPACUse(EL3);
    undefined
  } else return(Auth(X, Y, APDAKey_EL1, true, 0b0))
}

val aarch64_integer_pac_autda_dp_1src : (int, int, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_pac_autda_dp_1src ('d, 'n, source_is_sp) = if source_is_sp then aset_X(d, AuthDA(aget_X(d), aget_SP())) else aset_X(d, AuthDA(aget_X(d), aget_X(n)))

val AddPACIB : (bits(64), bits(64)) -> bits(64) effect {undef, escape, wreg, rreg}

function AddPACIB (X, Y) = {
  TrapEL2 : bool = undefined;
  TrapEL3 : bool = undefined;
  Enable : bits(1) = undefined;
  APIBKey_EL1 : bits(128) = slice(APIBKeyHi_EL1, 0, 64) @ slice(APIBKeyLo_EL1, 0, 64);
  match PSTATE.EL {
    ? if ? == EL0 => {
      IsEL1Regime : bool = (~(HaveEL(EL2)) | [HCR_EL2[27]] == 0b0) | [HCR_EL2[34]] == 0b0;
      Enable = if IsEL1Regime then [SCTLR_EL1[30]] else [SCTLR_EL2[30]];
      TrapEL2 = ((HaveEL(EL2) & IsEL1Regime) & ~(IsSecure())) & [HCR_EL2[41]] == 0b0;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL1 => {
      Enable = [SCTLR_EL1[30]];
      TrapEL2 = (HaveEL(EL2) & ~(IsSecure())) & [HCR_EL2[41]] == 0b0;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL2 => {
      Enable = [SCTLR_EL2[30]];
      TrapEL2 = false;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL3 => {
      Enable = [SCTLR_EL3[30]];
      TrapEL2 = false;
      TrapEL3 = false
    }
  };
  if Enable == 0b0 then return(X) else if TrapEL2 then {
    TrapPACUse(EL2);
    undefined
  } else if TrapEL3 then {
    TrapPACUse(EL3);
    undefined
  } else return(AddPAC(X, Y, APIBKey_EL1, false))
}

val aarch64_integer_pac_pacib_dp_1src : (int, int, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_pac_pacib_dp_1src ('d, 'n, source_is_sp) = if HavePACExt() then if source_is_sp then aset_X(d, AddPACIB(aget_X(d), aget_SP())) else aset_X(d, AddPACIB(aget_X(d), aget_X(n))) else ()

val integer_pac_pacib_hint_decode : (bits(1), bits(2), bits(3), bits(4), bits(4), bits(3), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_pac_pacib_hint_decode (L, op0, op1, CRn, CRm, op2, Rt) = {
  __unconditional = true;
  d : int = undefined;
  n : int = undefined;
  source_is_sp : bool = false;
  match CRm @ op2 {
    0b0011010 => {
      d = 30;
      n = 31
    },
    0b0011011 => {
      d = 30;
      source_is_sp = true
    },
    0b0001010 => {
      d = 17;
      n = 16
    },
    0b0001000 => throw(Error_See("PACIA")),
    0b0001100 => throw(Error_See("AUTIA")),
    0b0001110 => throw(Error_See("AUTIB")),
    [bitzero] @ [bitzero] @ [bitone] @ [bitone] @ [bitzero] @ [bitzero] @ _ : bits(1) => throw(Error_See("PACIA")),
    [bitzero] @ [bitzero] @ [bitone] @ [bitone] @ [bitone] @ [bitzero] @ _ : bits(1) => throw(Error_See("AUTIA")),
    [bitzero] @ [bitzero] @ [bitone] @ [bitone] @ [bitone] @ [bitone] @ _ : bits(1) => throw(Error_See("AUTIB")),
    0b0000111 => throw(Error_See("XPACLRI"))
  };
  aarch64_integer_pac_pacib_dp_1src(d, n, source_is_sp)
}

val AddPACIA : (bits(64), bits(64)) -> bits(64) effect {undef, escape, wreg, rreg}

function AddPACIA (X, Y) = {
  TrapEL2 : bool = undefined;
  TrapEL3 : bool = undefined;
  Enable : bits(1) = undefined;
  APIAKey_EL1 : bits(128) = slice(APIAKeyHi_EL1, 0, 64) @ slice(APIAKeyLo_EL1, 0, 64);
  match PSTATE.EL {
    ? if ? == EL0 => {
      IsEL1Regime : bool = (~(HaveEL(EL2)) | [HCR_EL2[27]] == 0b0) | [HCR_EL2[34]] == 0b0;
      Enable = if IsEL1Regime then [SCTLR_EL1[31]] else [SCTLR_EL2[31]];
      TrapEL2 = ((HaveEL(EL2) & IsEL1Regime) & ~(IsSecure())) & [HCR_EL2[41]] == 0b0;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL1 => {
      Enable = [SCTLR_EL1[31]];
      TrapEL2 = (HaveEL(EL2) & ~(IsSecure())) & [HCR_EL2[41]] == 0b0;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL2 => {
      Enable = [SCTLR_EL2[31]];
      TrapEL2 = false;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL3 => {
      Enable = [SCTLR_EL3[31]];
      TrapEL2 = false;
      TrapEL3 = false
    }
  };
  if Enable == 0b0 then return(X) else if TrapEL2 then {
    TrapPACUse(EL2);
    undefined
  } else if TrapEL3 then {
    TrapPACUse(EL3);
    undefined
  } else return(AddPAC(X, Y, APIAKey_EL1, false))
}

val aarch64_integer_pac_pacia_dp_1src : (int, int, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_pac_pacia_dp_1src ('d, 'n, source_is_sp) = if HavePACExt() then if source_is_sp then aset_X(d, AddPACIA(aget_X(d), aget_SP())) else aset_X(d, AddPACIA(aget_X(d), aget_X(n))) else ()

val integer_pac_pacia_hint_decode : (bits(1), bits(2), bits(3), bits(4), bits(4), bits(3), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_pac_pacia_hint_decode (L, op0, op1, CRn, CRm, op2, Rt) = {
  __unconditional = true;
  d : int = undefined;
  n : int = undefined;
  source_is_sp : bool = false;
  match CRm @ op2 {
    0b0011000 => {
      d = 30;
      n = 31
    },
    0b0011001 => {
      d = 30;
      source_is_sp = true
    },
    0b0001000 => {
      d = 17;
      n = 16
    },
    0b0001010 => throw(Error_See("PACIB")),
    0b0001100 => throw(Error_See("AUTIA")),
    0b0001110 => throw(Error_See("AUTIB")),
    [bitzero] @ [bitzero] @ [bitone] @ [bitone] @ [bitzero] @ [bitone] @ _ : bits(1) => throw(Error_See("PACIB")),
    [bitzero] @ [bitzero] @ [bitone] @ [bitone] @ [bitone] @ [bitzero] @ _ : bits(1) => throw(Error_See("AUTIA")),
    [bitzero] @ [bitzero] @ [bitone] @ [bitone] @ [bitone] @ [bitone] @ _ : bits(1) => throw(Error_See("AUTIB")),
    0b0000111 => throw(Error_See("XPACLRI"))
  };
  aarch64_integer_pac_pacia_dp_1src(d, n, source_is_sp)
}

val AddPACGA : (bits(64), bits(64)) -> bits(64) effect {undef, escape, wreg, rreg}

function AddPACGA (X, Y) = {
  TrapEL2 : bool = undefined;
  TrapEL3 : bool = undefined;
  APGAKey_EL1 : bits(128) = slice(APGAKeyHi_EL1, 0, 64) @ slice(APGAKeyLo_EL1, 0, 64);
  match PSTATE.EL {
    ? if ? == EL0 => {
      IsEL1Regime : bool = (~(HaveEL(EL2)) | [HCR_EL2[27]] == 0b0) | [HCR_EL2[34]] == 0b0;
      TrapEL2 = ((HaveEL(EL2) & IsEL1Regime) & ~(IsSecure())) & [HCR_EL2[41]] == 0b0;
      TrapEL3 = [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL1 => {
      TrapEL2 = (HaveEL(EL2) & ~(IsSecure())) & [HCR_EL2[41]] == 0b0;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL2 => {
      TrapEL2 = false;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL3 => {
      TrapEL2 = false;
      TrapEL3 = false
    }
  };
  if TrapEL2 then {
    TrapPACUse(EL2);
    undefined
  } else if TrapEL3 then {
    TrapPACUse(EL3);
    undefined
  } else return(slice(ComputePAC(X, Y, slice(APGAKey_EL1, 64, 64), slice(APGAKey_EL1, 0, 64)), 32, 32) @ Zeros(32))
}

val aarch64_integer_pac_pacga_dp_2src : (int, int, int, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_pac_pacga_dp_2src ('d, 'm, 'n, source_is_sp) = if source_is_sp then aset_X(d, AddPACGA(aget_X(n), aget_SP())) else aset_X(d, AddPACGA(aget_X(n), aget_X(m)))

val AddPACDB : (bits(64), bits(64)) -> bits(64) effect {undef, escape, wreg, rreg}

function AddPACDB (X, Y) = {
  TrapEL2 : bool = undefined;
  TrapEL3 : bool = undefined;
  Enable : bits(1) = undefined;
  APDBKey_EL1 : bits(128) = slice(APDBKeyHi_EL1, 0, 64) @ slice(APDBKeyLo_EL1, 0, 64);
  match PSTATE.EL {
    ? if ? == EL0 => {
      IsEL1Regime : bool = (~(HaveEL(EL2)) | [HCR_EL2[27]] == 0b0) | [HCR_EL2[34]] == 0b0;
      Enable = if IsEL1Regime then [SCTLR_EL1[13]] else [SCTLR_EL2[13]];
      TrapEL2 = ((HaveEL(EL2) & IsEL1Regime) & ~(IsSecure())) & [HCR_EL2[41]] == 0b0;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL1 => {
      Enable = [SCTLR_EL1[13]];
      TrapEL2 = (HaveEL(EL2) & ~(IsSecure())) & [HCR_EL2[41]] == 0b0;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL2 => {
      Enable = [SCTLR_EL2[13]];
      TrapEL2 = false;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL3 => {
      Enable = [SCTLR_EL3[13]];
      TrapEL2 = false;
      TrapEL3 = false
    }
  };
  if Enable == 0b0 then return(X) else if TrapEL2 then {
    TrapPACUse(EL2);
    undefined
  } else if TrapEL3 then {
    TrapPACUse(EL3);
    undefined
  } else return(AddPAC(X, Y, APDBKey_EL1, true))
}

val aarch64_integer_pac_pacdb_dp_1src : (int, int, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_pac_pacdb_dp_1src ('d, 'n, source_is_sp) = if source_is_sp then aset_X(d, AddPACDB(aget_X(d), aget_SP())) else aset_X(d, AddPACDB(aget_X(d), aget_X(n)))

val AddPACDA : (bits(64), bits(64)) -> bits(64) effect {undef, escape, wreg, rreg}

function AddPACDA (X, Y) = {
  TrapEL2 : bool = undefined;
  TrapEL3 : bool = undefined;
  Enable : bits(1) = undefined;
  APDAKey_EL1 : bits(128) = slice(APDAKeyHi_EL1, 0, 64) @ slice(APDAKeyLo_EL1, 0, 64);
  match PSTATE.EL {
    ? if ? == EL0 => {
      IsEL1Regime : bool = (~(HaveEL(EL2)) | [HCR_EL2[27]] == 0b0) | [HCR_EL2[34]] == 0b0;
      Enable = if IsEL1Regime then [SCTLR_EL1[27]] else [SCTLR_EL2[27]];
      TrapEL2 = ((HaveEL(EL2) & IsEL1Regime) & ~(IsSecure())) & [HCR_EL2[41]] == 0b0;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL1 => {
      Enable = [SCTLR_EL1[27]];
      TrapEL2 = (HaveEL(EL2) & ~(IsSecure())) & [HCR_EL2[41]] == 0b0;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL2 => {
      Enable = [SCTLR_EL2[27]];
      TrapEL2 = false;
      TrapEL3 = HaveEL(EL3) & [SCR_EL3[17]] == 0b0
    },
    ? if ? == EL3 => {
      Enable = [SCTLR_EL3[27]];
      TrapEL2 = false;
      TrapEL3 = false
    }
  };
  if Enable == 0b0 then return(X) else if TrapEL2 then {
    TrapPACUse(EL2);
    undefined
  } else if TrapEL3 then {
    TrapPACUse(EL3);
    undefined
  } else return(AddPAC(X, Y, APDAKey_EL1, true))
}

val aarch64_integer_pac_pacda_dp_1src : (int, int, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_integer_pac_pacda_dp_1src ('d, 'n, source_is_sp) = if source_is_sp then aset_X(d, AddPACDA(aget_X(d), aget_SP())) else aset_X(d, AddPACDA(aget_X(d), aget_X(n)))

val AArch64_WatchpointException : (bits(64), FaultRecord) -> unit effect {escape, rreg, undef, wreg}

function AArch64_WatchpointException (vaddress, fault) = {
  assert(PSTATE.EL != EL3, "((PSTATE).EL != EL3)");
  route_to_el2 : bool = ((HaveEL(EL2) & ~(IsSecure())) & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & ([HCR_EL2[27]] == 0b1 | [MDCR_EL2[8]] == 0b1);
  preferred_exception_return : bits(64) = ThisInstrAddr();
  vect_offset : int = 0;
  exception : ExceptionRecord = AArch64_AbortSyndrome(Exception_Watchpoint, fault, vaddress);
  if PSTATE.EL == EL2 | route_to_el2 then AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset) else AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
}

val AArch64_WFxTrap : (bits(2), bool) -> unit effect {escape, rreg, undef, wreg}

function AArch64_WFxTrap (target_el, is_wfe) = {
  assert(UInt(target_el) > UInt(PSTATE.EL), "(UInt(target_el) > UInt((PSTATE).EL))");
  preferred_exception_return : bits(64) = ThisInstrAddr();
  vect_offset : int = 0;
  exception : ExceptionRecord = ExceptionSyndrome(Exception_WFxTrap);
  __tmp_272 : bits(25) = exception.syndrome;
  __tmp_272 = __SetSlice_bits(25, 5, __tmp_272, 20, ConditionSyndrome());
  exception.syndrome = __tmp_272;
  __tmp_273 : bits(25) = exception.syndrome;
  __tmp_273 = __SetSlice_bits(25, 1, __tmp_273, 0, if is_wfe then 0b1 else 0b0);
  exception.syndrome = __tmp_273;
  if ((target_el == EL1 & HaveEL(EL2)) & ~(IsSecure())) & [HCR_EL2[27]] == 0b1 then AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset) else AArch64_TakeException(target_el, exception, preferred_exception_return, vect_offset)
}

val AArch64_CheckForWFxTrap : (bits(2), bool) -> unit effect {escape, rreg, undef, wreg}

function AArch64_CheckForWFxTrap (target_el, is_wfe) = {
  assert(HaveEL(target_el), "HaveEL(target_el)");
  trap : bool = undefined;
  match target_el {
    ? if ? == EL1 => trap = (if is_wfe then [aget_SCTLR()[18]] else [aget_SCTLR()[16]]) == 0b0,
    ? if ? == EL2 => trap = (if is_wfe then [HCR_EL2[14]] else [HCR_EL2[13]]) == 0b1,
    ? if ? == EL3 => trap = (if is_wfe then [SCR_EL3[13]] else [SCR_EL3[12]]) == 0b1
  };
  if trap then AArch64_WFxTrap(target_el, is_wfe) else ()
}

val aarch64_system_hints : SystemHintOp -> unit effect {escape, rreg, undef, wreg}

function aarch64_system_hints op = match op {
  SystemHintOp_YIELD => Hint_Yield(),
  SystemHintOp_WFE => if IsEventRegisterSet() then ClearEventRegister() else {
    if PSTATE.EL == EL0 then AArch64_CheckForWFxTrap(EL1, true) else ();
    if ((HaveEL(EL2) & ~(IsSecure())) & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & ~(IsInHost()) then AArch64_CheckForWFxTrap(EL2, true) else ();
    if HaveEL(EL3) & PSTATE.EL != EL3 then AArch64_CheckForWFxTrap(EL3, true) else ();
    WaitForEvent()
  },
  SystemHintOp_WFI => if ~(InterruptPending()) then {
    if PSTATE.EL == EL0 then AArch64_CheckForWFxTrap(EL1, false) else ();
    if ((HaveEL(EL2) & ~(IsSecure())) & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & ~(IsInHost()) then AArch64_CheckForWFxTrap(EL2, false) else ();
    if HaveEL(EL3) & PSTATE.EL != EL3 then AArch64_CheckForWFxTrap(EL3, false) else ();
    WaitForInterrupt()
  } else (),
  SystemHintOp_SEV => SendEvent(),
  SystemHintOp_SEVL => SendEventLocal(),
  SystemHintOp_ESB => {
    ErrorSynchronizationBarrier(MBReqDomain_FullSystem, MBReqTypes_All);
    AArch64_ESBOperation();
    if (HaveEL(EL2) & ~(IsSecure())) & (PSTATE.EL == EL0 | PSTATE.EL == EL1) then AArch64_vESBOperation() else ();
    TakeUnmaskedSErrorInterrupts()
  },
  SystemHintOp_PSB => ProfilingSynchronizationBarrier(),
  _ => ()
}

val system_hints_decode : (bits(1), bits(2), bits(3), bits(4), bits(4), bits(3), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function system_hints_decode (L, op0, op1, CRn, CRm, op2, Rt) = {
  __unconditional = true;
  op : SystemHintOp = undefined;
  match CRm @ op2 {
    0b0000000 => op = SystemHintOp_NOP,
    0b0000001 => op = SystemHintOp_YIELD,
    0b0000010 => op = SystemHintOp_WFE,
    0b0000011 => op = SystemHintOp_WFI,
    0b0000100 => op = SystemHintOp_SEV,
    0b0000101 => op = SystemHintOp_SEVL,
    0b0000111 => throw(Error_See("XPACLRI")),
    [bitzero] @ [bitzero] @ [bitzero] @ [bitone] @ _ : bits(1) @ _ : bits(1) @ _ : bits(1) => throw(Error_See("PACIA1716, PACIB1716, AUTIA1716, AUTIB1716")),
    0b0010000 => {
      if ~(HaveRASExt()) then EndOfInstruction() else ();
      op = SystemHintOp_ESB
    },
    0b0010001 => {
      if ~(HaveStatisticalProfiling()) then EndOfInstruction() else ();
      op = SystemHintOp_PSB
    },
    [bitzero] @ [bitzero] @ [bitone] @ [bitone] @ _ : bits(1) @ _ : bits(1) @ _ : bits(1) => throw(Error_See("PACIAZ, PACIASP, PACIBZ, PACIBSP, AUTIAZ, AUTIASP, AUTIBZ, AUTIBSP")),
    _ => EndOfInstruction()
  };
  aarch64_system_hints(op)
}

val AArch64_VectorCatchException : FaultRecord -> unit effect {escape, rreg, undef, wreg}

function AArch64_VectorCatchException fault = {
  assert(PSTATE.EL != EL2, "((PSTATE).EL != EL2)");
  assert((HaveEL(EL2) & ~(IsSecure())) & ([HCR_EL2[27]] == 0b1 | [MDCR_EL2[8]] == 0b1), "((HaveEL(EL2) && !(IsSecure())) && (((HCR_EL2).TGE == '1') || ((MDCR_EL2).TDE == '1')))");
  preferred_exception_return : bits(64) = ThisInstrAddr();
  vect_offset : int = 0;
  vaddress : bits(64) = undefined;
  exception : ExceptionRecord = AArch64_AbortSyndrome(Exception_VectorCatch, fault, vaddress);
  AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset)
}

val AArch64_UndefinedFault : unit -> unit effect {escape, rreg, undef, wreg}

function AArch64_UndefinedFault () = {
  route_to_el2 : bool = ((HaveEL(EL2) & ~(IsSecure())) & PSTATE.EL == EL0) & [HCR_EL2[27]] == 0b1;
  preferred_exception_return : bits(64) = ThisInstrAddr();
  vect_offset : int = 0;
  exception : ExceptionRecord = ExceptionSyndrome(Exception_Uncategorized);
  if UInt(PSTATE.EL) > UInt(EL1) then AArch64_TakeException(PSTATE.EL, exception, preferred_exception_return, vect_offset) else if route_to_el2 then AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset) else AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
}

val AArch64_SystemRegisterTrap : (bits(2), bits(2), bits(3), bits(3), bits(4), bits(5), bits(4), bits(1)) -> unit effect {escape, rreg, undef, wreg}

function AArch64_SystemRegisterTrap (target_el, op0, op2, op1, crn, rt, crm, dir) = {
  assert(UInt(target_el) >= UInt(PSTATE.EL), "(UInt(target_el) >= UInt((PSTATE).EL))");
  preferred_exception_return : bits(64) = ThisInstrAddr();
  vect_offset : int = 0;
  exception : ExceptionRecord = ExceptionSyndrome(Exception_SystemRegisterTrap);
  __tmp_280 : bits(25) = exception.syndrome;
  __tmp_280 = __SetSlice_bits(25, 2, __tmp_280, 20, op0);
  exception.syndrome = __tmp_280;
  __tmp_281 : bits(25) = exception.syndrome;
  __tmp_281 = __SetSlice_bits(25, 3, __tmp_281, 17, op2);
  exception.syndrome = __tmp_281;
  __tmp_282 : bits(25) = exception.syndrome;
  __tmp_282 = __SetSlice_bits(25, 3, __tmp_282, 14, op1);
  exception.syndrome = __tmp_282;
  __tmp_283 : bits(25) = exception.syndrome;
  __tmp_283 = __SetSlice_bits(25, 4, __tmp_283, 10, crn);
  exception.syndrome = __tmp_283;
  __tmp_284 : bits(25) = exception.syndrome;
  __tmp_284 = __SetSlice_bits(25, 5, __tmp_284, 5, rt);
  exception.syndrome = __tmp_284;
  __tmp_285 : bits(25) = exception.syndrome;
  __tmp_285 = __SetSlice_bits(25, 4, __tmp_285, 1, crm);
  exception.syndrome = __tmp_285;
  __tmp_286 : bits(25) = exception.syndrome;
  __tmp_286 = __SetSlice_bits(25, 1, __tmp_286, 0, dir);
  exception.syndrome = __tmp_286;
  if ((target_el == EL1 & HaveEL(EL2)) & ~(IsSecure())) & [HCR_EL2[27]] == 0b1 then AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset) else AArch64_TakeException(target_el, exception, preferred_exception_return, vect_offset)
}

val AArch64_SoftwareBreakpoint : bits(16) -> unit effect {escape, rreg, undef, wreg}

function AArch64_SoftwareBreakpoint immediate = {
  route_to_el2 : bool = ((HaveEL(EL2) & ~(IsSecure())) & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & ([HCR_EL2[27]] == 0b1 | [MDCR_EL2[8]] == 0b1);
  preferred_exception_return : bits(64) = ThisInstrAddr();
  vect_offset : int = 0;
  exception : ExceptionRecord = ExceptionSyndrome(Exception_SoftwareBreakpoint);
  __tmp_271 : bits(25) = exception.syndrome;
  __tmp_271 = __SetSlice_bits(25, 16, __tmp_271, 0, immediate);
  exception.syndrome = __tmp_271;
  if UInt(PSTATE.EL) > UInt(EL1) then AArch64_TakeException(PSTATE.EL, exception, preferred_exception_return, vect_offset) else if route_to_el2 then AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset) else AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
}

val aarch64_system_exceptions_debug_breakpoint : bits(16) -> unit effect {escape, rreg, undef, wreg}

function aarch64_system_exceptions_debug_breakpoint comment = AArch64_SoftwareBreakpoint(comment)

val system_exceptions_debug_breakpoint_decode : (bits(3), bits(16), bits(3), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function system_exceptions_debug_breakpoint_decode (opc, imm16, op2, LL) = {
  __unconditional = true;
  comment : bits(16) = imm16;
  aarch64_system_exceptions_debug_breakpoint(comment)
}

val AArch64_SPAlignmentFault : unit -> unit effect {escape, rreg, undef, wreg}

function AArch64_SPAlignmentFault () = {
  preferred_exception_return : bits(64) = ThisInstrAddr();
  vect_offset : int = 0;
  exception : ExceptionRecord = ExceptionSyndrome(Exception_SPAlignment);
  if UInt(PSTATE.EL) > UInt(EL1) then AArch64_TakeException(PSTATE.EL, exception, preferred_exception_return, vect_offset) else if (HaveEL(EL2) & ~(IsSecure())) & [HCR_EL2[27]] == 0b1 then AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset) else AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
}

val CheckSPAlignment : unit -> unit effect {escape, rreg, undef, wreg}

function CheckSPAlignment () = {
  sp : bits(64) = aget_SP();
  stack_align_check : bool = undefined;
  if PSTATE.EL == EL0 then stack_align_check = [aget_SCTLR()[4]] != 0b0 else stack_align_check = [aget_SCTLR()[3]] != 0b0;
  if stack_align_check & sp != Align(sp, 16) then AArch64_SPAlignmentFault() else ();
  ()
}

val AArch64_InstructionAbort : (bits(64), FaultRecord) -> unit effect {escape, rreg, undef, wreg}

function AArch64_InstructionAbort (vaddress, fault) = {
  route_to_el3 : bool = (HaveEL(EL3) & [SCR_EL3[3]] == 0b1) & IsExternalAbort(fault);
  route_to_el2 : bool = ((HaveEL(EL2) & ~(IsSecure())) & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & (([HCR_EL2[27]] == 0b1 | IsSecondStage(fault)) | (HaveRASExt() & [HCR_EL2[37]] == 0b1) & IsExternalAbort(fault));
  preferred_exception_return : bits(64) = ThisInstrAddr();
  vect_offset : int = 0;
  exception : ExceptionRecord = AArch64_AbortSyndrome(Exception_InstructionAbort, fault, vaddress);
  if PSTATE.EL == EL3 | route_to_el3 then AArch64_TakeException(EL3, exception, preferred_exception_return, vect_offset) else if PSTATE.EL == EL2 | route_to_el2 then AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset) else AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
}

val AArch64_DataAbort : (bits(64), FaultRecord) -> unit effect {escape, rreg, undef, wreg}

function AArch64_DataAbort (vaddress, fault) = {
  route_to_el3 : bool = (HaveEL(EL3) & [SCR_EL3[3]] == 0b1) & IsExternalAbort(fault);
  route_to_el2 : bool = ((HaveEL(EL2) & ~(IsSecure())) & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & (([HCR_EL2[27]] == 0b1 | IsSecondStage(fault)) | (HaveRASExt() & [HCR_EL2[37]] == 0b1) & IsExternalAbort(fault));
  preferred_exception_return : bits(64) = ThisInstrAddr();
  vect_offset : int = 0;
  exception : ExceptionRecord = AArch64_AbortSyndrome(Exception_DataAbort, fault, vaddress);
  if PSTATE.EL == EL3 | route_to_el3 then AArch64_TakeException(EL3, exception, preferred_exception_return, vect_offset) else if PSTATE.EL == EL2 | route_to_el2 then AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset) else AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
}

val AArch64_CheckForERetTrap : (bool, bool) -> unit effect {escape, rreg, undef, wreg}

function AArch64_CheckForERetTrap (eret_with_pac, pac_uses_key_a) = {
  route_to_el2 : bool = (((HaveNVExt() & HaveEL(EL2)) & ~(IsSecure())) & PSTATE.EL == EL1) & [HCR_EL2[42]] == 0b1;
  vect_offset : int = undefined;
  if route_to_el2 then {
    exception : ExceptionRecord = undefined;
    preferred_exception_return : bits(64) = ThisInstrAddr();
    vect_offset = 0;
    exception = ExceptionSyndrome(Exception_ERetTrap);
    __tmp_255 : bits(25) = exception.syndrome;
    __tmp_255 = __SetSlice_bits(25, 23, __tmp_255, 2, ZeroExtend(0b0, 23));
    exception.syndrome = __tmp_255;
    if ~(eret_with_pac) then {
      __tmp_256 : bits(25) = exception.syndrome;
      __tmp_256 = __SetSlice_bits(25, 1, __tmp_256, 1, 0b0);
      exception.syndrome = __tmp_256;
      __tmp_257 : bits(25) = exception.syndrome;
      __tmp_257 = __SetSlice_bits(25, 1, __tmp_257, 0, 0b0);
      exception.syndrome = __tmp_257
    } else {
      __tmp_258 : bits(25) = exception.syndrome;
      __tmp_258 = __SetSlice_bits(25, 1, __tmp_258, 1, 0b1);
      exception.syndrome = __tmp_258;
      if pac_uses_key_a then {
        __tmp_259 : bits(25) = exception.syndrome;
        __tmp_259 = __SetSlice_bits(25, 1, __tmp_259, 0, 0b0);
        exception.syndrome = __tmp_259
      } else {
        __tmp_260 : bits(25) = exception.syndrome;
        __tmp_260 = __SetSlice_bits(25, 1, __tmp_260, 0, 0b1);
        exception.syndrome = __tmp_260
      }
    };
    AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset)
  } else ()
}

val AArch64_CallSupervisor : bits(16) -> unit effect {escape, rreg, undef, wreg}

function AArch64_CallSupervisor immediate = {
  if UsingAArch32() then AArch32_ITAdvance() else ();
  SSAdvance();
  route_to_el2 : bool = ((HaveEL(EL2) & ~(IsSecure())) & PSTATE.EL == EL0) & [HCR_EL2[27]] == 0b1;
  preferred_exception_return : bits(64) = NextInstrAddr();
  vect_offset : int = 0;
  exception : ExceptionRecord = ExceptionSyndrome(Exception_SupervisorCall);
  __tmp_277 : bits(25) = exception.syndrome;
  __tmp_277 = __SetSlice_bits(25, 16, __tmp_277, 0, immediate);
  exception.syndrome = __tmp_277;
  if UInt(PSTATE.EL) > UInt(EL1) then AArch64_TakeException(PSTATE.EL, exception, preferred_exception_return, vect_offset) else if route_to_el2 then AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset) else AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
}

val aarch64_system_exceptions_runtime_svc : bits(16) -> unit effect {escape, rreg, undef, wreg}

function aarch64_system_exceptions_runtime_svc imm = AArch64_CallSupervisor(imm)

val system_exceptions_runtime_svc_decode : (bits(3), bits(16), bits(3), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function system_exceptions_runtime_svc_decode (opc, imm16, op2, LL) = {
  __unconditional = true;
  imm : bits(16) = imm16;
  aarch64_system_exceptions_runtime_svc(imm)
}

val AArch64_CallSecureMonitor : bits(16) -> unit effect {escape, rreg, undef, wreg}

function AArch64_CallSecureMonitor immediate = {
  assert(HaveEL(EL3) & ~(ELUsingAArch32(EL3)), "(HaveEL(EL3) && !(ELUsingAArch32(EL3)))");
  if UsingAArch32() then AArch32_ITAdvance() else ();
  SSAdvance();
  preferred_exception_return : bits(64) = NextInstrAddr();
  vect_offset : int = 0;
  exception : ExceptionRecord = ExceptionSyndrome(Exception_MonitorCall);
  __tmp_293 : bits(25) = exception.syndrome;
  __tmp_293 = __SetSlice_bits(25, 16, __tmp_293, 0, immediate);
  exception.syndrome = __tmp_293;
  AArch64_TakeException(EL3, exception, preferred_exception_return, vect_offset)
}

val AArch64_CallHypervisor : bits(16) -> unit effect {escape, rreg, undef, wreg}

function AArch64_CallHypervisor immediate = {
  assert(HaveEL(EL2), "HaveEL(EL2)");
  if UsingAArch32() then AArch32_ITAdvance() else ();
  SSAdvance();
  preferred_exception_return : bits(64) = NextInstrAddr();
  vect_offset : int = 0;
  exception : ExceptionRecord = ExceptionSyndrome(Exception_HypervisorCall);
  __tmp_289 : bits(25) = exception.syndrome;
  __tmp_289 = __SetSlice_bits(25, 16, __tmp_289, 0, immediate);
  exception.syndrome = __tmp_289;
  if PSTATE.EL == EL3 then AArch64_TakeException(EL3, exception, preferred_exception_return, vect_offset) else AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset)
}

val AArch64_BreakpointException : FaultRecord -> unit effect {escape, rreg, undef, wreg}

function AArch64_BreakpointException fault = {
  assert(PSTATE.EL != EL3, "((PSTATE).EL != EL3)");
  route_to_el2 : bool = ((HaveEL(EL2) & ~(IsSecure())) & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & ([HCR_EL2[27]] == 0b1 | [MDCR_EL2[8]] == 0b1);
  preferred_exception_return : bits(64) = ThisInstrAddr();
  vect_offset : int = 0;
  vaddress : bits(64) = undefined;
  exception : ExceptionRecord = AArch64_AbortSyndrome(Exception_Breakpoint, fault, vaddress);
  if PSTATE.EL == EL2 | route_to_el2 then AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset) else AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
}

val AArch64_Abort : (bits(64), FaultRecord) -> unit effect {escape, rreg, undef, wreg}

function AArch64_Abort (vaddress, fault) = if IsDebugException(fault) then if fault.acctype == AccType_IFETCH then if UsingAArch32() & fault.debugmoe == DebugException_VectorCatch then AArch64_VectorCatchException(fault) else AArch64_BreakpointException(fault) else AArch64_WatchpointException(vaddress, fault) else if fault.acctype == AccType_IFETCH then AArch64_InstructionAbort(vaddress, fault) else AArch64_DataAbort(vaddress, fault)

val AArch64_CheckAlignment : (bits(64), int, AccType, bool) -> bool effect {escape, rreg, undef, wreg}

function AArch64_CheckAlignment (address, 'alignment, acctype, iswrite) = {
  aligned : bool = address == Align(address, alignment);
  atomic : bool = acctype == AccType_ATOMIC | acctype == AccType_ATOMICRW;
  ordered : bool = acctype == AccType_ORDERED | acctype == AccType_ORDEREDRW | acctype == AccType_LIMITEDORDERED;
  vector_name : bool = acctype == AccType_VEC;
  check : bool = (atomic | ordered) | [aget_SCTLR()[1]] == 0b1;
  secondstage : bool = undefined;
  if check & ~(aligned) then {
    secondstage = false;
    AArch64_Abort(address, AArch64_AlignmentFault(acctype, iswrite, secondstage))
  } else ();
  return(aligned)
}

val AArch32_EnterMode : (bits(5), bits(32), int, int) -> unit effect {escape, rreg, undef, wreg}

function AArch32_EnterMode (target_mode, preferred_exception_return, 'lr_offset, 'vect_offset) = {
  SynchronizeContext();
  assert(ELUsingAArch32(EL1) & PSTATE.EL != EL2, "(ELUsingAArch32(EL1) && ((PSTATE).EL != EL2))");
  spsr : bits(32) = GetPSRFromPSTATE();
  if PSTATE.M == M32_Monitor then SCR = __SetSlice_bits(32, 1, SCR, 0, 0b0) else ();
  AArch32_WriteMode(target_mode);
  aset_SPSR(spsr);
  aset_R(14, preferred_exception_return + lr_offset);
  PSTATE.T = [SCTLR[30]];
  PSTATE.SS = 0b0;
  if target_mode == M32_FIQ then (PSTATE.A @ PSTATE.I @ PSTATE.F) = 0b111 else if target_mode == M32_Abort | target_mode == M32_IRQ then (PSTATE.A @ PSTATE.I) = 0b11 else PSTATE.I = 0b1;
  PSTATE.E = [SCTLR[25]];
  PSTATE.IL = 0b0;
  PSTATE.IT = 0x00;
  if HavePANExt() & [SCTLR[23]] == 0b0 then PSTATE.PAN = 0b1 else ();
  BranchTo(slice(ExcVectorBase(), 5, 27) @ __GetSlice_int(5, vect_offset, 0), BranchType_UNKNOWN);
  EndOfInstruction()
}

val AArch64_AdvSIMDFPAccessTrap : bits(2) -> unit effect {escape, rreg, undef, wreg}

function AArch64_AdvSIMDFPAccessTrap target_el = {
  preferred_exception_return : bits(64) = ThisInstrAddr();
  vect_offset : int = 0;
  route_to_el2 : bool = ((target_el == EL1 & HaveEL(EL2)) & ~(IsSecure())) & [HCR_EL2[27]] == 0b1;
  exception : ExceptionRecord = undefined;
  if route_to_el2 then {
    exception = ExceptionSyndrome(Exception_Uncategorized);
    AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset)
  } else {
    exception = ExceptionSyndrome(Exception_AdvSIMDFPAccessTrap);
    __tmp_261 : bits(25) = exception.syndrome;
    __tmp_261 = __SetSlice_bits(25, 5, __tmp_261, 20, ConditionSyndrome());
    exception.syndrome = __tmp_261;
    AArch64_TakeException(target_el, exception, preferred_exception_return, vect_offset)
  };
  ()
}

val AArch64_CheckFPAdvSIMDTrap : unit -> unit effect {escape, rreg, undef, wreg}

function AArch64_CheckFPAdvSIMDTrap () = {
  disabled : bool = undefined;
  if HaveEL(EL2) & ~(IsSecure()) then if HaveVirtHostExt() & [HCR_EL2[34]] == 0b1 then {
    match slice(CPTR_EL2, 20, 2) {
      _ : bits(1) @ [bitzero] => disabled = ~(PSTATE.EL == EL1 & [HCR_EL2[27]] == 0b1),
      0b01 => disabled = PSTATE.EL == EL0 & [HCR_EL2[27]] == 0b1,
      0b11 => disabled = false
    };
    if disabled then AArch64_AdvSIMDFPAccessTrap(EL2) else ()
  } else if [CPTR_EL2[10]] == 0b1 then AArch64_AdvSIMDFPAccessTrap(EL2) else () else ();
  if HaveEL(EL3) then if [CPTR_EL3[10]] == 0b1 then AArch64_AdvSIMDFPAccessTrap(EL3) else () else ();
  ()
}

val AArch64_CheckFPAdvSIMDEnabled : unit -> unit effect {escape, rreg, undef, wreg}

function AArch64_CheckFPAdvSIMDEnabled () = {
  disabled : bool = undefined;
  if PSTATE.EL == EL0 | PSTATE.EL == EL1 then {
    match slice(aget_CPACR(), 20, 2) {
      _ : bits(1) @ [bitzero] => disabled = true,
      0b01 => disabled = PSTATE.EL == EL0,
      0b11 => disabled = false
    };
    if disabled then AArch64_AdvSIMDFPAccessTrap(EL1) else ()
  } else ();
  AArch64_CheckFPAdvSIMDTrap()
}

val CheckFPAdvSIMDEnabled64 : unit -> unit effect {escape, rreg, undef, wreg}

function CheckFPAdvSIMDEnabled64 () = AArch64_CheckFPAdvSIMDEnabled()

val aarch64_float_move_fp_select : (bits(4), int, int, int, int) -> unit effect {escape, rreg, undef, wreg}

function aarch64_float_move_fp_select (condition, 'd, 'datasize, 'm, 'n) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  CheckFPAdvSIMDEnabled64();
  result : bits('datasize) = if ConditionHolds(condition) then aget_V(n) else aget_V(m);
  aset_V(d, result)
}

val aarch64_float_move_fp_imm : forall ('datasize : Int).
  (int, atom('datasize), bits('datasize)) -> unit effect {escape, rreg, undef, wreg}

function aarch64_float_move_fp_imm ('d, datasize, imm) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  CheckFPAdvSIMDEnabled64();
  aset_V(d, imm)
}

val aarch64_float_convert_int : forall ('fltsize : Int) ('intsize : Int), 'fltsize >= 0 & 'intsize >= 0.
  (int, atom('fltsize), atom('intsize), int, FPConvOp, int, FPRounding, bool) -> unit effect {undef, escape, wreg, rreg}

function aarch64_float_convert_int (d, fltsize, intsize, n, op, part, rounding, unsigned) = {
  CheckFPAdvSIMDEnabled64();
  fltval : bits('fltsize) = undefined;
  intval : bits('intsize) = undefined;
  match op {
    FPConvOp_CVT_FtoI => {
      fltval = aget_V(n);
      intval = FPToFixed(fltval, 0, unsigned, FPCR, rounding);
      aset_X(d, intval)
    },
    FPConvOp_CVT_ItoF => {
      intval = aget_X(n);
      fltval = FixedToFP(intval, 0, unsigned, FPCR, rounding);
      aset_V(d, fltval)
    },
    FPConvOp_MOV_FtoI => {
      fltval = aget_Vpart(n, part);
      intval = ZeroExtend(fltval, intsize);
      aset_X(d, intval)
    },
    FPConvOp_MOV_ItoF => {
      intval = aget_X(n);
      fltval = slice(intval, 0, fltsize);
      aset_Vpart(d, part, fltval)
    },
    FPConvOp_CVT_FtoI_JS => {
      fltval = aget_V(n);
      intval = FPToFixedJS(fltval, FPCR, true);
      aset_X(d, ZeroExtend(slice(intval, 0, 32), 64))
    }
  }
}

val aarch64_float_convert_fp : forall ('dstsize : Int) ('srcsize : Int), 'dstsize >= 0 & 'srcsize >= 0.
  (int, atom('dstsize), int, atom('srcsize)) -> unit effect {undef, escape, wreg, rreg}

function aarch64_float_convert_fp (d, dstsize, n, srcsize) = {
  CheckFPAdvSIMDEnabled64();
  result : bits('dstsize) = undefined;
  operand : bits('srcsize) = aget_V(n);
  result = FPConvert(operand, FPCR);
  aset_V(d, result)
}

val aarch64_float_convert_fix : forall ('fltsize : Int) ('intsize : Int), 'fltsize >= 0 & 'intsize >= 0.
  (int, atom('fltsize), int, atom('intsize), int, FPConvOp, FPRounding, bool) -> unit effect {undef, escape, wreg, rreg}

function aarch64_float_convert_fix (d, fltsize, fracbits, intsize, n, op, rounding, unsigned) = {
  CheckFPAdvSIMDEnabled64();
  fltval : bits('fltsize) = undefined;
  intval : bits('intsize) = undefined;
  match op {
    FPConvOp_CVT_FtoI => {
      fltval = aget_V(n);
      intval = FPToFixed(fltval, fracbits, unsigned, FPCR, rounding);
      aset_X(d, intval)
    },
    FPConvOp_CVT_ItoF => {
      intval = aget_X(n);
      fltval = FixedToFP(intval, fracbits, unsigned, FPCR, rounding);
      aset_V(d, fltval)
    }
  }
}

val aarch64_float_compare_uncond : (bool, int, int, int, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_float_compare_uncond (cmp_with_zero, 'datasize, 'm, 'n, signal_all_nans) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  CheckFPAdvSIMDEnabled64();
  operand1 : bits('datasize) = aget_V(n);
  operand2 : bits('datasize) = if cmp_with_zero then FPZero(0b0) else aget_V(m);
  (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = FPCompare(operand1, operand2, signal_all_nans, FPCR)
}

val aarch64_float_compare_cond : (bits(4), int, bits(4), int, int, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_float_compare_cond (condition, 'datasize, flags__arg, 'm, 'n, signal_all_nans) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  flags = flags__arg;
  CheckFPAdvSIMDEnabled64();
  operand1 : bits('datasize) = aget_V(n);
  operand2 : bits('datasize) = aget_V(m);
  if ConditionHolds(condition) then flags = FPCompare(operand1, operand2, signal_all_nans, FPCR) else ();
  (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = flags
}

val aarch64_float_arithmetic_unary : (int, int, FPUnaryOp, int) -> unit effect {escape, rreg, undef, wreg}

function aarch64_float_arithmetic_unary ('d, 'datasize, fpop, 'n) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  CheckFPAdvSIMDEnabled64();
  result : bits('datasize) = undefined;
  operand : bits('datasize) = aget_V(n);
  match fpop {
    FPUnaryOp_MOV => result = operand,
    FPUnaryOp_ABS => result = FPAbs(operand),
    FPUnaryOp_NEG => result = FPNeg(operand),
    FPUnaryOp_SQRT => result = FPSqrt(operand, FPCR)
  };
  aset_V(d, result)
}

val aarch64_float_arithmetic_round : (int, int, bool, int, FPRounding) -> unit effect {escape, rreg, undef, wreg}

function aarch64_float_arithmetic_round ('d, 'datasize, exact, 'n, rounding) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  CheckFPAdvSIMDEnabled64();
  result : bits('datasize) = undefined;
  operand : bits('datasize) = aget_V(n);
  result = FPRoundInt(operand, FPCR, rounding, exact);
  aset_V(d, result)
}

val aarch64_float_arithmetic_mul_product : (int, int, int, int, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_float_arithmetic_mul_product ('d, 'datasize, 'm, 'n, negated) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  CheckFPAdvSIMDEnabled64();
  result : bits('datasize) = undefined;
  operand1 : bits('datasize) = aget_V(n);
  operand2 : bits('datasize) = aget_V(m);
  result = FPMul(operand1, operand2, FPCR);
  if negated then result = FPNeg(result) else ();
  aset_V(d, result)
}

val aarch64_float_arithmetic_mul_addsub : (int, int, int, int, int, bool, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_float_arithmetic_mul_addsub ('a, 'd, 'datasize, 'm, 'n, op1_neg, opa_neg) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  CheckFPAdvSIMDEnabled64();
  result : bits('datasize) = undefined;
  operanda : bits('datasize) = aget_V(a);
  operand1 : bits('datasize) = aget_V(n);
  operand2 : bits('datasize) = aget_V(m);
  if opa_neg then operanda = FPNeg(operanda) else ();
  if op1_neg then operand1 = FPNeg(operand1) else ();
  result = FPMulAdd(operanda, operand1, operand2, FPCR);
  aset_V(d, result)
}

val aarch64_float_arithmetic_maxmin : (int, int, int, int, FPMaxMinOp) -> unit effect {escape, rreg, undef, wreg}

function aarch64_float_arithmetic_maxmin ('d, 'datasize, 'm, 'n, operation) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  CheckFPAdvSIMDEnabled64();
  result : bits('datasize) = undefined;
  operand1 : bits('datasize) = aget_V(n);
  operand2 : bits('datasize) = aget_V(m);
  match operation {
    FPMaxMinOp_MAX => result = FPMax(operand1, operand2, FPCR),
    FPMaxMinOp_MIN => result = FPMin(operand1, operand2, FPCR),
    FPMaxMinOp_MAXNUM => result = FPMaxNum(operand1, operand2, FPCR),
    FPMaxMinOp_MINNUM => result = FPMinNum(operand1, operand2, FPCR)
  };
  aset_V(d, result)
}

val aarch64_float_arithmetic_div : (int, int, int, int) -> unit effect {escape, rreg, undef, wreg}

function aarch64_float_arithmetic_div ('d, 'datasize, 'm, 'n) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  CheckFPAdvSIMDEnabled64();
  result : bits('datasize) = undefined;
  operand1 : bits('datasize) = aget_V(n);
  operand2 : bits('datasize) = aget_V(m);
  result = FPDiv(operand1, operand2, FPCR);
  aset_V(d, result)
}

val aarch64_float_arithmetic_addsub : (int, int, int, int, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_float_arithmetic_addsub ('d, 'datasize, 'm, 'n, sub_op) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  CheckFPAdvSIMDEnabled64();
  result : bits('datasize) = undefined;
  operand1 : bits('datasize) = aget_V(n);
  operand2 : bits('datasize) = aget_V(m);
  if sub_op then result = FPSub(operand1, operand2, FPCR) else result = FPAdd(operand1, operand2, FPCR);
  aset_V(d, result)
}

val AArch64_AccessIsPrivileged : AccType -> bool effect {escape, rreg, undef}

function AArch64_AccessIsPrivileged acctype = {
  ispriv : bool = undefined;
  if PSTATE.EL == EL0 then ispriv = false else if PSTATE.EL == EL3 then ispriv = true else if PSTATE.EL == EL2 & (~(IsInHost()) | [HCR_EL2[27]] == 0b0) then ispriv = true else if HaveUAOExt() & PSTATE.UAO == 0b1 then ispriv = true else ispriv = acctype != AccType_UNPRIV;
  return(ispriv)
}

val AArch64_CheckWatchpoint : (bits(64), AccType, bool, int) -> FaultRecord effect {wreg, rreg, undef, escape}

function AArch64_CheckWatchpoint (vaddress, acctype, iswrite, size) = {
  assert(~(ELUsingAArch32(S1TranslationRegime())), "!(ELUsingAArch32(S1TranslationRegime()))");
  val_match : bool = false;
  ispriv : bool = AArch64_AccessIsPrivileged(acctype);
  foreach (i from 0 to UInt(slice(ID_AA64DFR0_EL1, 20, 4)) by 1 in inc)
    val_match = val_match | AArch64_WatchpointMatch(i, vaddress, size, ispriv, iswrite);
  reason : bits(6) = undefined;
  if val_match & HaltOnBreakpointOrWatchpoint() then {
    reason = DebugHalt_Watchpoint;
    Halt(reason);
    undefined
  } else if (val_match & [MDSCR_EL1[15]] == 0b1) & AArch64_GenerateDebugExceptions() then return(AArch64_DebugFault(acctype, iswrite)) else return(AArch64_NoFault())
}

val AArch64_CheckDebug : (bits(64), AccType, bool, int) -> FaultRecord effect {escape, rreg, undef, wreg}

function AArch64_CheckDebug (vaddress, acctype, iswrite, 'size) = {
  fault : FaultRecord = AArch64_NoFault();
  d_side : bool = acctype != AccType_IFETCH;
  generate_exception : bool = AArch64_GenerateDebugExceptions() & [MDSCR_EL1[15]] == 0b1;
  halt : bool = HaltOnBreakpointOrWatchpoint();
  if generate_exception | halt then if d_side then fault = AArch64_CheckWatchpoint(vaddress, acctype, iswrite, size) else fault = AArch64_CheckBreakpoint(vaddress, size) else ();
  return(fault)
}

val AArch64_CheckPermission : (Permissions, bits(64), int, bits(1), AccType, bool) -> FaultRecord effect {rreg, undef, escape}

function AArch64_CheckPermission (perms, vaddress, level, NS, acctype, iswrite) = {
  assert(~(ELUsingAArch32(S1TranslationRegime())), "!(ELUsingAArch32(S1TranslationRegime()))");
  wxn : bool = [aget_SCTLR()[19]] == 0b1;
  xn : bool = undefined;
  w : bool = undefined;
  r : bool = undefined;
  priv_xn : bool = undefined;
  user_xn : bool = undefined;
  pan : bits(1) = undefined;
  ispriv : bool = undefined;
  user_w : bool = undefined;
  user_r : bool = undefined;
  priv_w : bool = undefined;
  priv_r : bool = undefined;
  if (PSTATE.EL == EL0 | PSTATE.EL == EL1) | IsInHost() then {
    priv_r = true;
    priv_w = [perms.ap[2]] == 0b0;
    user_r = [perms.ap[1]] == 0b1;
    user_w = slice(perms.ap, 1, 2) == 0b01;
    ispriv = AArch64_AccessIsPrivileged(acctype);
    pan = if HavePANExt() then PSTATE.PAN else 0b0;
    if ((((HaveNVExt() & HaveEL(EL2)) & [HCR_EL2[42]] == 0b1) & [HCR_EL2[43]] == 0b1) & ~(IsSecure())) & PSTATE.EL == EL1 then
      pan = 0b0
    else ();
    if ((pan == 0b1 & user_r) & ispriv) & ~(acctype == AccType_DC | acctype == AccType_AT | acctype == AccType_IFETCH) | acctype == AccType_AT & AArch64_ExecutingATS1xPInstr() then {
      priv_r = false;
      priv_w = false
    } else ();
    user_xn = perms.xn == 0b1 | user_w & wxn;
    priv_xn = (perms.pxn == 0b1 | priv_w & wxn) | user_w;
    if ispriv then (r, w, xn) = (priv_r, priv_w, priv_xn)
    else (r, w, xn) = (user_r, user_w, user_xn)
  } else {
    r = true;
    w = [perms.ap[2]] == 0b0;
    xn = perms.xn == 0b1 | w & wxn
  };
  if ((HaveEL(EL3) & IsSecure()) & NS == 0b1) & [SCR_EL3[9]] == 0b1 then
    xn = true
  else ();
  failedread : bool = undefined;
  fail : bool = undefined;
  if acctype == AccType_IFETCH then {
    fail = xn;
    failedread = true
  } else if acctype == AccType_ATOMICRW | acctype == AccType_ORDEREDRW then {
    fail = ~(r) | ~(w);
    failedread = ~(r)
  } else if iswrite then {
    fail = ~(w);
    failedread = false
  } else {
    fail = ~(r);
    failedread = true
  };
  ipaddress : bits(52) = undefined;
  s2fs1walk : bool = undefined;
  secondstage : bool = undefined;
  if fail then {
    secondstage = false;
    s2fs1walk = false;
    ipaddress = undefined;
    return(AArch64_PermissionFault(ipaddress, level, acctype, ~(failedread), secondstage, s2fs1walk))
  } else return(AArch64_NoFault())
}

val AArch64_FirstStageTranslate : (bits(64), AccType, bool, bool, int) -> AddressDescriptor effect {escape, rmem, rreg, undef, wmem}

function AArch64_FirstStageTranslate (vaddress, acctype, iswrite, wasaligned, 'size) = {
  s1_enabled : bool = undefined;
  if HasS2Translation() then s1_enabled = ([HCR_EL2[27]] == 0b0 & [HCR_EL2[12]] == 0b0) & [SCTLR_EL1[0]] == 0b1 else s1_enabled = [aget_SCTLR()[0]] == 0b1;
  ipaddress : bits(52) = undefined;
  secondstage : bool = false;
  s2fs1walk : bool = false;
  nTLSMD : bits(1) = undefined;
  permissioncheck : bool = undefined;
  S1 : TLBRecord = undefined;
  if s1_enabled then {
    S1 = AArch64_TranslationTableWalk(ipaddress, vaddress, acctype, iswrite, secondstage, s2fs1walk, size);
    permissioncheck = true
  } else {
    S1 = AArch64_TranslateAddressS1Off(vaddress, acctype, iswrite);
    permissioncheck = false;
    if (UsingAArch32() & HaveTrapLoadStoreMultipleDeviceExt()) & AArch32_ExecutingLSMInstr() then if S1.addrdesc.memattrs.typ == MemType_Device & S1.addrdesc.memattrs.device != DeviceType_GRE then {
      nTLSMD = if S1TranslationRegime() == EL2 then [SCTLR_EL2[28]] else [SCTLR_EL1[28]];
      if nTLSMD == 0b0 then {
        __tmp_246 : AddressDescriptor = S1.addrdesc;
        __tmp_246.fault = AArch64_AlignmentFault(acctype, iswrite, secondstage);
        S1.addrdesc = __tmp_246
      } else ()
    } else () else ()
  };
  if ((~(wasaligned) & acctype != AccType_IFETCH | acctype == AccType_DCZVA) & S1.addrdesc.memattrs.typ == MemType_Device) & ~(IsFault(S1.addrdesc)) then {
    __tmp_247 : AddressDescriptor = S1.addrdesc;
    __tmp_247.fault = AArch64_AlignmentFault(acctype, iswrite, secondstage);
    S1.addrdesc = __tmp_247
  } else ();
  if ~(IsFault(S1.addrdesc)) & permissioncheck then {
    __tmp_248 : AddressDescriptor = S1.addrdesc;
    __tmp_248.fault = AArch64_CheckPermission(S1.perms, vaddress, S1.level, S1.addrdesc.paddress.NS, acctype, iswrite);
    S1.addrdesc = __tmp_248
  } else ();
  if (~(IsFault(S1.addrdesc)) & S1.addrdesc.memattrs.typ == MemType_Device) & acctype == AccType_IFETCH then S1.addrdesc = AArch64_InstructionDevice(S1.addrdesc, vaddress, ipaddress, S1.level, acctype, iswrite, secondstage, s2fs1walk) else ();
  hwupdatewalk : bool = false;
  s2fs1walk = false;
  __tmp_249 : AddressDescriptor = S1.addrdesc;
  __tmp_249.fault = AArch64_CheckAndUpdateDescriptor(S1.descupdate, S1.addrdesc.fault, secondstage, vaddress, acctype, iswrite, s2fs1walk, hwupdatewalk);
  S1.addrdesc = __tmp_249;
  return(S1.addrdesc)
}

val AArch64_FullTranslate : (bits(64), AccType, bool, bool, int) -> AddressDescriptor effect {escape, rmem, rreg, undef, wmem}

function AArch64_FullTranslate (vaddress, acctype, iswrite, wasaligned, 'size) = {
  S1 : AddressDescriptor = AArch64_FirstStageTranslate(vaddress, acctype, iswrite, wasaligned, size);
  result : AddressDescriptor = undefined;
  hwupdatewalk : bool = undefined;
  s2fs1walk : bool = undefined;
  if ~(IsFault(S1)) & HasS2Translation() then {
    s2fs1walk = false;
    hwupdatewalk = false;
    result = AArch64_SecondStageTranslate(S1, vaddress, acctype, iswrite, wasaligned, s2fs1walk, size, hwupdatewalk)
  } else result = S1;
  return(result)
}

val AArch64_TranslateAddress : (bits(64), AccType, bool, bool, int) -> AddressDescriptor effect {escape, rmem, rreg, undef, wmem, wreg}

function AArch64_TranslateAddress (vaddress, acctype, iswrite, wasaligned, 'size) = {
  result : AddressDescriptor = AArch64_FullTranslate(vaddress, acctype, iswrite, wasaligned, size);
  if ~(acctype == AccType_PTW | acctype == AccType_IC | acctype == AccType_AT) & ~(IsFault(result)) then result.fault = AArch64_CheckDebug(vaddress, acctype, iswrite, size) else ();
  result.vaddress = ZeroExtend(vaddress);
  return(result)
}

val AArch64_aset_MemSingle : forall ('size : Int), 64 >= 0 & 8 * 'size >= 0.
  (bits(64), atom('size), AccType, bool, bits(8 * 'size)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function AArch64_aset_MemSingle (address, size, acctype, wasaligned, value_name) = {
  assert('size == 1 | 'size == 2 | 'size == 4 | 'size == 8 | 'size == 16, "((size == 1) || ((size == 2) || ((size == 4) || ((size == 8) || (size == 16)))))");
  assert(address == Align(address, 'size), "(address == Align(address, size))");
  memaddrdesc : AddressDescriptor = undefined;
  iswrite : bool = true;
  memaddrdesc = AArch64_TranslateAddress(address, acctype, iswrite, wasaligned, 'size);
  if IsFault(memaddrdesc) then AArch64_Abort(address, memaddrdesc.fault) else ();
  if memaddrdesc.memattrs.shareable then ClearExclusiveByAddress(memaddrdesc.paddress, ProcessorID(), 'size) else ();
  accdesc : AccessDescriptor = CreateAccessDescriptor(acctype);
  aset__Mem(memaddrdesc, 'size, accdesc, value_name);
  ()
}

val aset_Mem : forall ('size : Int), 64 >= 0 & 8 * 'size >= 0.
  (bits(64), atom('size), AccType, bits(8 * 'size)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function aset_Mem (address, size, acctype, value_name__arg) = {
  value_name = value_name__arg;
  i : int = undefined;
  iswrite : bool = true;
  if BigEndian() then value_name = BigEndianReverse(value_name) else ();
  aligned : bool = AArch64_CheckAlignment(address, 'size, acctype, iswrite);
  atomic : bool = undefined;
  if 'size != 16 | ~(acctype == AccType_VEC | acctype == AccType_VECSTREAM) then atomic = aligned else atomic = address == Align(address, 8);
  c : Constraint = undefined;
  if ~(atomic) then {
    assert('size > 1, "(size > 1)");
    AArch64_aset_MemSingle(address, 1, acctype, aligned, slice(value_name, 0, 8));
    if ~(aligned) then {
      c = ConstrainUnpredictable(Unpredictable_DEVPAGE2);
      assert(c == Constraint_FAULT | c == Constraint_NONE, "((c == Constraint_FAULT) || (c == Constraint_NONE))");
      if c == Constraint_NONE then aligned = true else ()
    } else ();
    foreach (i from 1 to ('size - 1) by 1 in inc)
      AArch64_aset_MemSingle(address + i, 1, acctype, aligned, slice(value_name, 8 * i, 8))
  } else if 'size == 16 & (acctype == AccType_VEC | acctype == AccType_VECSTREAM) then {
    AArch64_aset_MemSingle(address, 8, acctype, aligned, slice(value_name, 0, 64));
    AArch64_aset_MemSingle(address + 8, 8, acctype, aligned, slice(value_name, 64, 64))
  } else AArch64_aset_MemSingle(address, 'size, acctype, aligned, value_name);
  ()
}

val AArch64_aget_MemSingle : forall ('size : Int), 64 >= 0 & 8 * 'size >= 0.
  (bits(64), atom('size), AccType, bool) -> bits(8 * 'size) effect {escape, rmem, rreg, undef, wmem, wreg}

function AArch64_aget_MemSingle (address, size, acctype, wasaligned) = {
  assert('size == 1 | 'size == 2 | 'size == 4 | 'size == 8 | 'size == 16, "((size == 1) || ((size == 2) || ((size == 4) || ((size == 8) || (size == 16)))))");
  assert(address == Align(address, 'size), "(address == Align(address, size))");
  memaddrdesc : AddressDescriptor = undefined;
  value_name : bits(8 * 'size) = undefined;
  iswrite : bool = false;
  memaddrdesc = AArch64_TranslateAddress(address, acctype, iswrite, wasaligned, 'size);
  if IsFault(memaddrdesc) then AArch64_Abort(address, memaddrdesc.fault) else ();
  accdesc : AccessDescriptor = CreateAccessDescriptor(acctype);
  value_name = aget__Mem(memaddrdesc, 'size, accdesc);
  return(value_name)
}

val aget_Mem : forall ('size : Int), 64 >= 0 & 8 * 'size >= 0.
  (bits(64), atom('size), AccType) -> bits(8 * 'size) effect {escape, rmem, rreg, undef, wmem, wreg}

function aget_Mem (address, size, acctype) = {
  assert('size == 1 | 'size == 2 | 'size == 4 | 'size == 8 | 'size == 16, "((size == 1) || ((size == 2) || ((size == 4) || ((size == 8) || (size == 16)))))");
  value_name : bits(8 * 'size) = undefined;
  i : int = undefined;
  iswrite : bool = false;
  aligned : bool = AArch64_CheckAlignment(address, 'size, acctype, iswrite);
  atomic : bool = undefined;
  if 'size != 16 | ~(acctype == AccType_VEC | acctype == AccType_VECSTREAM) then atomic = aligned else atomic = address == Align(address, 8);
  c : Constraint = undefined;
  if ~(atomic) then {
    assert('size > 1, "(size > 1)");
    value_name = __SetSlice_bits(8 * 'size, 8, value_name, 0, AArch64_aget_MemSingle(address, 1, acctype, aligned));
    if ~(aligned) then {
      c = ConstrainUnpredictable(Unpredictable_DEVPAGE2);
      assert(c == Constraint_FAULT | c == Constraint_NONE, "((c == Constraint_FAULT) || (c == Constraint_NONE))");
      if c == Constraint_NONE then aligned = true else ()
    } else ();
    foreach (i from 1 to ('size - 1) by 1 in inc)
      value_name = __SetSlice_bits(8 * 'size, 8, value_name, 8 * i, AArch64_aget_MemSingle(address + i, 1, acctype, aligned))
  } else if 'size == 16 & (acctype == AccType_VEC | acctype == AccType_VECSTREAM) then {
    value_name = __SetSlice_bits(8 * 'size, 64, value_name, 0, AArch64_aget_MemSingle(address, 8, acctype, aligned));
    value_name = __SetSlice_bits(8 * 'size, 64, value_name, 64, AArch64_aget_MemSingle(address + 8, 8, acctype, aligned))
  } else value_name = AArch64_aget_MemSingle(address, 'size, acctype, aligned);
  if BigEndian() then value_name = BigEndianReverse(value_name) else ();
  return(value_name)
}

val aarch64_memory_vector_single_nowb : forall ('datasize : Int) ('esize : Int) ('selem : Int).
  (atom('datasize), atom('esize), int, int, MemOp, int, bool, atom('selem), int, bool) -> unit effect {escape, rmem, wmem, undef, wreg, rreg}

function aarch64_memory_vector_single_nowb (datasize, esize, index, m, memop, n, replicate, selem, t__arg, wback) = {
  assert(constraint('datasize >= 0 & 'selem >= 1 & 'esize >= 0));
  t : int = t__arg;
  CheckFPAdvSIMDEnabled64();
  address : bits(64) = undefined;
  offs : bits(64) = undefined;
  rval : bits(128) = undefined;
  element : bits('esize) = undefined;
  s : int = undefined;
  let 'ebytes : {'n, true. atom('n)} = ex_int(esize / 8);
  assert(constraint(8 * 'ebytes = 'esize));
  if n == 31 then {
    CheckSPAlignment();
    address = aget_SP()
  } else address = aget_X(n);
  offs = Zeros();
  if replicate then foreach (s from 0 to (selem - 1) by 1 in inc) {
    element = aget_Mem(address + offs, ebytes, AccType_VEC);
    let 'v : {'n, true. atom('n)} = ex_int(datasize / esize) in {
      assert(constraint('esize * 'v = 'datasize));
      aset_V(t, replicate_bits(element, v))
    };
    offs = offs + ebytes;
    t = (t + 1) % 32
  } else foreach (s from 0 to (selem - 1) by 1 in inc) {
    rval = aget_V(t);
    if memop == MemOp_LOAD then {
      rval = aset_Elem(rval, index, esize, aget_Mem(address + offs, ebytes, AccType_VEC));
      aset_V(t, rval)
    } else aset_Mem(address + offs, ebytes, AccType_VEC, aget_Elem(rval, index, esize));
    offs = offs + ebytes;
    t = (t + 1) % 32
  };
  if wback then {
    if m != 31 then offs = aget_X(m)
    else ();
    if n == 31 then aset_SP(address + offs) else aset_X(n, address + offs)
  } else ()
}

val aarch64_memory_vector_multiple_nowb : forall ('datasize : Int) ('esize : Int) ('elements : Int) ('rpt : Int) ('selem : Int).
  (atom('datasize), atom('elements), atom('esize), int, MemOp, int, atom('rpt), atom('selem), int, bool) -> unit effect {escape, rmem, wmem, undef, wreg, rreg}

function aarch64_memory_vector_multiple_nowb (datasize, elements, esize, m, memop, n, rpt, selem, t, wback) = {
  assert(constraint('datasize in {8, 16, 32, 64, 128} & ('rpt >= 1 & ('elements >= 1 & ('selem >= 1 & 'esize >= 0)))), "datasize constraint");
  CheckFPAdvSIMDEnabled64();
  address : bits(64) = undefined;
  offs : bits(64) = undefined;
  rval : bits('datasize) = undefined;
  e : int = undefined;
  r : int = undefined;
  s : int = undefined;
  tt : int = undefined;
  let 'ebytes = ex_int(esize / 8);
  assert(constraint(8 * 'ebytes = 'esize));
  if n == 31 then {
    CheckSPAlignment();
    address = aget_SP()
  } else address = aget_X(n);
  offs = Zeros();
  foreach (r from 0 to (rpt - 1) by 1 in inc)
    foreach (e from 0 to (elements - 1) by 1 in inc) {
      tt = (t + r) % 32;
      foreach (s from 0 to (selem - 1) by 1 in inc) {
        rval = aget_V(tt);
        if memop == MemOp_LOAD then {
          rval = aset_Elem(rval, e, esize, aget_Mem(address + offs, ebytes, AccType_VEC));
          aset_V(tt, rval)
        } else aset_Mem(address + offs, ebytes, AccType_VEC, aget_Elem(rval, e, esize));
        offs = offs + ebytes;
        tt = (tt + 1) % 32
      }
    };
  if wback then {
    if m != 31 then offs = aget_X(m)
    else ();
    if n == 31 then aset_SP(address + offs) else aset_X(n, address + offs)
  } else ()
}

val aarch64_memory_single_simdfp_register : (AccType, int, ExtendType, int, MemOp, int, bool, int, int, bool) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function aarch64_memory_single_simdfp_register (acctype, 'datasize, extend_type, 'm, memop, 'n, postindex, 'shift, 't, wback) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  offset : bits(64) = ExtendReg(m, extend_type, shift);
  CheckFPAdvSIMDEnabled64();
  address : bits(64) = undefined;
  data : bits('datasize) = undefined;
  if n == 31 then {
    CheckSPAlignment();
    address = aget_SP()
  } else address = aget_X(n);
  if ~(postindex) then address = address + offset else ();
  match memop {
    MemOp_STORE => {
      data = aget_V(t);
      aset_Mem(address, datasize / 8, acctype, data)
    },
    MemOp_LOAD => {
      data = aget_Mem(address, datasize / 8, acctype);
      aset_V(t, data)
    }
  };
  if wback then {
    if postindex then address = address + offset else ();
    if n == 31 then aset_SP(address) else aset_X(n, address)
  } else ()
}

val aarch64_memory_single_simdfp_immediate_signed_postidx : (AccType, int, MemOp, int, bits(64), bool, int, bool) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function aarch64_memory_single_simdfp_immediate_signed_postidx (acctype, 'datasize, memop, 'n, offset, postindex, 't, wback) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  CheckFPAdvSIMDEnabled64();
  address : bits(64) = undefined;
  data : bits('datasize) = undefined;
  if n == 31 then {
    CheckSPAlignment();
    address = aget_SP()
  } else address = aget_X(n);
  if ~(postindex) then address = address + offset else ();
  match memop {
    MemOp_STORE => {
      data = aget_V(t);
      aset_Mem(address, datasize / 8, acctype, data)
    },
    MemOp_LOAD => {
      data = aget_Mem(address, datasize / 8, acctype);
      aset_V(t, data)
    }
  };
  if wback then {
    if postindex then address = address + offset else ();
    if n == 31 then aset_SP(address) else aset_X(n, address)
  } else ()
}

val aarch64_memory_single_simdfp_immediate_signed_offset_normal : (AccType, int, MemOp, int, bits(64), bool, int, bool) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function aarch64_memory_single_simdfp_immediate_signed_offset_normal (acctype, 'datasize, memop, 'n, offset, postindex, 't, wback) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  CheckFPAdvSIMDEnabled64();
  address : bits(64) = undefined;
  data : bits('datasize) = undefined;
  if n == 31 then {
    CheckSPAlignment();
    address = aget_SP()
  } else address = aget_X(n);
  if ~(postindex) then address = address + offset else ();
  match memop {
    MemOp_STORE => {
      data = aget_V(t);
      aset_Mem(address, datasize / 8, acctype, data)
    },
    MemOp_LOAD => {
      data = aget_Mem(address, datasize / 8, acctype);
      aset_V(t, data)
    }
  };
  if wback then {
    if postindex then address = address + offset else ();
    if n == 31 then aset_SP(address) else aset_X(n, address)
  } else ()
}

val aarch64_memory_ordered : forall ('datasize : Int) ('regsize : Int).
  (AccType, atom('datasize), MemOp, int, atom('regsize), int) -> unit effect {escape, undef, wreg, rreg, rmem, wmem}

function aarch64_memory_ordered (acctype, datasize, memop, n, regsize, t) = {
  assert(constraint('datasize in {8, 16, 32, 64, 128} & 'regsize >= 0), "datasize constraint");
  address : bits(64) = undefined;
  data : bits('datasize) = undefined;
  let 'dbytes = ex_int(datasize / 8);
  assert(constraint(8 * 'dbytes = 'datasize));
  if n == 31 then {
    CheckSPAlignment();
    address = aget_SP()
  } else address = aget_X(n);
  match memop {
    MemOp_STORE => {
      data = aget_X(t);
      aset_Mem(address, dbytes, acctype, data)
    },
    MemOp_LOAD => {
      data = aget_Mem(address, dbytes, acctype);
      aset_X(t, ZeroExtend(data, regsize))
    }
  }
}

val memory_ordered_decode : (bits(2), bits(1), bits(1), bits(1), bits(5), bits(1), bits(5), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_ordered_decode (size, o2, L, o1, Rs, o0, Rt2, Rn, Rt) = {
  __unconditional = true;
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  t2 : int = UInt(Rt2);
  s : int = UInt(Rs);
  acctype : AccType = if o0 == 0b0 then AccType_LIMITEDORDERED else AccType_ORDERED;
  memop : MemOp = if L == 0b1 then MemOp_LOAD else MemOp_STORE;
  elsize : int = shl_int(8, UInt(size));
  regsize : int = if elsize == 64 then 64 else 32;
  datasize : int = elsize;
  aarch64_memory_ordered(acctype, datasize, memop, n, regsize, t)
}

val aarch64_memory_orderedrcpc : forall ('datasize : Int) ('regsize : Int).
  (AccType, atom('datasize), int, atom('regsize), int) -> unit effect {escape, undef, wreg, rreg, rmem, wmem}

function aarch64_memory_orderedrcpc (acctype, datasize, n, regsize, t) = {
  assert(constraint('datasize in {8, 16, 32, 64, 128} & 'regsize >= 0), "datasize constraint");
  address : bits(64) = undefined;
  data : bits('datasize) = undefined;
  let 'dbytes = ex_int(datasize / 8);
  assert(constraint(8 * 'dbytes = 'datasize));
  if n == 31 then {
    CheckSPAlignment();
    address = aget_SP()
  } else address = aget_X(n);
  data = aget_Mem(address, dbytes, acctype);
  aset_X(t, ZeroExtend(data, regsize))
}

val memory_orderedrcpc_decode : (bits(2), bits(1), bits(1), bits(1), bits(5), bits(1), bits(3), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_orderedrcpc_decode (size, V, A, R, Rs, o3, opc, Rn, Rt) = {
  __unconditional = true;
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  s : int = UInt(Rs);
  acctype : AccType = AccType_ORDERED;
  elsize : int = shl_int(8, UInt(size));
  regsize : int = if elsize == 64 then 64 else 32;
  datasize : int = elsize;
  aarch64_memory_orderedrcpc(acctype, datasize, n, regsize, t)
}

val aarch64_memory_literal_simdfp : forall ('size : Int).
  (bits(64), atom('size), int) -> unit effect {escape, undef, wreg, rreg, rmem, wmem}

function aarch64_memory_literal_simdfp (offset, size, t) = {
  assert(constraint('size >= 0));
  assert(constraint('size in {4,8,16}));
  address : bits(64) = aget_PC() + offset;
  data : bits(8 * 'size) = undefined;
  CheckFPAdvSIMDEnabled64();
  data = aget_Mem(address, size, AccType_VEC);
  aset_V(t, data)
}

val aarch64_memory_literal_general : forall ('size : Int).
  (MemOp, bits(64), bool, atom('size), int) -> unit effect {escape, undef, wreg, rreg, rmem, wmem}

function aarch64_memory_literal_general (memop, offset, signed, size, t) = {
  address : bits(64) = aget_PC() + offset;
  data : bits('size) = undefined;
  match memop {
    MemOp_LOAD => {
      assert(constraint('size >= 0));
      let 'bytes = size / 8;
      assert(constraint(8 * 'bytes = 'size));
      data = aget_Mem(address, bytes, AccType_NORMAL);
      if signed then aset_X(t, SignExtend(data, 64)) else aset_X(t, data)
    },
    MemOp_PREFETCH => Prefetch(address, __GetSlice_int(5, t, 0))
  }
}

val memory_literal_general_decode : (bits(2), bits(1), bits(19), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_literal_general_decode (opc, V, imm19, Rt) = {
  __unconditional = true;
  t : int = UInt(Rt);
  memop : MemOp = MemOp_LOAD;
  signed : bool = false;
  size : int = undefined;
  offset : bits(64) = undefined;
  match opc {
    0b00 => size = 4,
    0b01 => size = 8,
    0b10 => {
      size = 4;
      signed = true
    },
    0b11 => memop = MemOp_PREFETCH
  };
  offset = SignExtend(imm19 @ 0b00, 64);
  aarch64_memory_literal_general(memop, offset, signed, 8 * size, t)
}

val aarch64_memory_atomicops_swp : forall 'regsize. (int, AccType, int, atom('regsize), int, AccType, int) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function aarch64_memory_atomicops_swp ('datasize, ldacctype, 'n, regsize, 's, stacctype, 't) = {
  assert(constraint('regsize >= 0), "regsize constraint");
  let 'dbytes = ex_int(datasize / 8);
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  address : bits(64) = undefined;
  data : bits('datasize) = undefined;
  if n == 31 then {
    CheckSPAlignment();
    address = aget_SP()
  } else address = aget_X(n);
  data = aget_Mem(address, datasize / 8, ldacctype);
  aset_Mem(address, datasize / 8, stacctype, aget_X(s));
  aset_X(t, ZeroExtend(data, regsize))
}

val aarch64_memory_atomicops_st : (int, AccType, int, MemAtomicOp, int, AccType) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function aarch64_memory_atomicops_st ('datasize, ldacctype, 'n, op, 's, stacctype) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  address : bits(64) = undefined;
  value_name : bits('datasize) = undefined;
  data : bits('datasize) = undefined;
  result : bits('datasize) = undefined;
  value_name = aget_X(s);
  if n == 31 then {
    CheckSPAlignment();
    address = aget_SP()
  } else address = aget_X(n);
  data = aget_Mem(address, datasize / 8, ldacctype);
  match op {
    MemAtomicOp_ADD => result = data + value_name,
    MemAtomicOp_BIC => result = data & ~(value_name),
    MemAtomicOp_EOR => result = data ^ value_name,
    MemAtomicOp_ORR => result = data | value_name,
    MemAtomicOp_SMAX => result = if SInt(data) > SInt(value_name) then data else value_name,
    MemAtomicOp_SMIN => result = if SInt(data) > SInt(value_name) then value_name else data,
    MemAtomicOp_UMAX => result = if UInt(data) > UInt(value_name) then data else value_name,
    MemAtomicOp_UMIN => result = if UInt(data) > UInt(value_name) then value_name else data
  };
  aset_Mem(address, datasize / 8, stacctype, result)
}

val aarch64_memory_atomicops_ld : forall 'regsize. (int, AccType, int, MemAtomicOp, atom('regsize), int, AccType, int) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function aarch64_memory_atomicops_ld ('datasize, ldacctype, 'n, op, regsize, 's, stacctype, 't) = {
  assert(constraint('regsize >= 0), "regsize constraint");
  let 'dbytes = ex_int(datasize / 8);
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  address : bits(64) = undefined;
  value_name : bits('datasize) = undefined;
  data : bits('datasize) = undefined;
  result : bits('datasize) = undefined;
  value_name = aget_X(s);
  if n == 31 then {
    CheckSPAlignment();
    address = aget_SP()
  } else address = aget_X(n);
  data = aget_Mem(address, datasize / 8, ldacctype);
  match op {
    MemAtomicOp_ADD => result = data + value_name,
    MemAtomicOp_BIC => result = data & ~(value_name),
    MemAtomicOp_EOR => result = data ^ value_name,
    MemAtomicOp_ORR => result = data | value_name,
    MemAtomicOp_SMAX => result = if SInt(data) > SInt(value_name) then data else value_name,
    MemAtomicOp_SMIN => result = if SInt(data) > SInt(value_name) then value_name else data,
    MemAtomicOp_UMAX => result = if UInt(data) > UInt(value_name) then data else value_name,
    MemAtomicOp_UMIN => result = if UInt(data) > UInt(value_name) then value_name else data
  };
  aset_Mem(address, datasize / 8, stacctype, result);
  aset_X(t, ZeroExtend(data, regsize))
}

val aarch64_memory_atomicops_cas_single : forall 'regsize. (int, AccType, int, atom('regsize), int, AccType, int) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function aarch64_memory_atomicops_cas_single ('datasize, ldacctype, 'n, regsize, 's, stacctype, 't) = {
  assert(constraint('regsize >= 0), "regsize constraint");
  let 'dbytes = ex_int(datasize / 8);
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  address : bits(64) = undefined;
  comparevalue : bits('datasize) = undefined;
  newvalue : bits('datasize) = undefined;
  data : bits('datasize) = undefined;
  comparevalue = aget_X(s);
  newvalue = aget_X(t);
  if n == 31 then {
    CheckSPAlignment();
    address = aget_SP()
  } else address = aget_X(n);
  data = aget_Mem(address, datasize / 8, ldacctype);
  if data == comparevalue then aset_Mem(address, datasize / 8, stacctype, newvalue) else ();
  aset_X(s, ZeroExtend(data, regsize))
}

val aarch64_memory_atomicops_cas_pair : forall 'regsize. (int, AccType, int, atom('regsize), int, AccType, int) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function aarch64_memory_atomicops_cas_pair ('datasize, ldacctype, 'n, regsize, 's, stacctype, 't) = {
  assert(constraint('regsize >= 0), "regsize constraint");
  let 'dbytes = ex_int(datasize / 8);
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  address : bits(64) = undefined;
  comparevalue : bits(2 * 'datasize) = undefined;
  newvalue : bits(2 * 'datasize) = undefined;
  data : bits(2 * 'datasize) = undefined;
  s1 : bits('datasize) = aget_X(s);
  s2 : bits('datasize) = aget_X(s + 1);
  t1 : bits('datasize) = aget_X(t);
  t2 : bits('datasize) = aget_X(t + 1);
  comparevalue = if BigEndian() then s1 @ s2 else s2 @ s1;
  newvalue = if BigEndian() then t1 @ t2 else t2 @ t1;
  if n == 31 then {
    CheckSPAlignment();
    address = aget_SP()
  } else address = aget_X(n);
  data = aget_Mem(address, (2 * datasize) / 8, ldacctype);
  if data == comparevalue then aset_Mem(address, (2 * datasize) / 8, stacctype, newvalue) else ();
  if BigEndian() then {
    aset_X(s, ZeroExtend(slice(data, datasize, datasize), regsize));
    aset_X(s + 1, ZeroExtend(slice(data, 0, datasize), regsize))
  } else {
    aset_X(s, ZeroExtend(slice(data, 0, datasize), regsize));
    aset_X(s + 1, ZeroExtend(slice(data, datasize, datasize), regsize))
  }
}

val AArch64_SetExclusiveMonitors : (bits(64), int) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function AArch64_SetExclusiveMonitors (address, 'size) = {
  acctype : AccType = AccType_ATOMIC;
  iswrite : bool = false;
  aligned : bool = address != Align(address, size);
  memaddrdesc : AddressDescriptor = AArch64_TranslateAddress(address, acctype, iswrite, aligned, size);
  if IsFault(memaddrdesc) then () else ();
  if memaddrdesc.memattrs.shareable then MarkExclusiveGlobal(memaddrdesc.paddress, ProcessorID(), size) else ();
  MarkExclusiveLocal(memaddrdesc.paddress, ProcessorID(), size);
  AArch64_MarkExclusiveVA(address, ProcessorID(), size)
}

val AArch64_ExclusiveMonitorsPass : (bits(64), int) -> bool effect {escape, rmem, rreg, undef, wmem, wreg}

function AArch64_ExclusiveMonitorsPass (address, 'size) = {
  acctype : AccType = AccType_ATOMIC;
  iswrite : bool = true;
  aligned : bool = address == Align(address, size);
  secondstage : bool = undefined;
  if ~(aligned) then {
    secondstage = false;
    AArch64_Abort(address, AArch64_AlignmentFault(acctype, iswrite, secondstage))
  } else ();
  passed : bool = AArch64_IsExclusiveVA(address, ProcessorID(), size);
  if ~(passed) then return(false) else ();
  memaddrdesc : AddressDescriptor = AArch64_TranslateAddress(address, acctype, iswrite, aligned, size);
  if IsFault(memaddrdesc) then AArch64_Abort(address, memaddrdesc.fault) else ();
  passed = IsExclusiveLocal(memaddrdesc.paddress, ProcessorID(), size);
  if passed then {
    ClearExclusiveLocal(ProcessorID());
    if memaddrdesc.memattrs.shareable then passed = IsExclusiveGlobal(memaddrdesc.paddress, ProcessorID(), size) else ()
  } else ();
  return(passed)
}

val AArch32_SelfHostedSecurePrivilegedInvasiveDebugEnabled : unit -> bool effect {escape, rreg, undef}

function AArch32_SelfHostedSecurePrivilegedInvasiveDebugEnabled () = {
  if ~(HaveEL(EL3)) & ~(IsSecure()) then return(false) else ();
  return(DBGEN == HIGH & SPIDEN == HIGH)
}

val AArch32_GenerateDebugExceptionsFrom : (bits(2), bool) -> bool effect {escape, rreg, undef}

function AArch32_GenerateDebugExceptionsFrom (from, secure) = {
  mask : bits(1) = undefined;
  if from == EL0 & ~(ELStateUsingAArch32(EL1, secure)) then {
    mask = undefined;
    return(AArch64_GenerateDebugExceptionsFrom(from, secure, mask))
  } else ();
  if ([DBGOSLSR[1]] == 0b1 | DoubleLockStatus()) | Halted() then return(false) else ();
  enabled : bool = undefined;
  spd : bits(2) = undefined;
  if HaveEL(EL3) & secure then {
    spd = if ELUsingAArch32(EL3) then slice(SDCR, 14, 2) else slice(MDCR_EL3, 14, 2);
    if [spd[1]] == 0b1 then enabled = [spd[0]] == 0b1 else enabled = AArch32_SelfHostedSecurePrivilegedInvasiveDebugEnabled();
    if from == EL0 then enabled = enabled | [SDER[0]] == 0b1 else ()
  } else enabled = from != EL2;
  return(enabled)
}

val AArch32_GenerateDebugExceptions : unit -> bool effect {escape, rreg, undef}

function AArch32_GenerateDebugExceptions () = return(AArch32_GenerateDebugExceptionsFrom(PSTATE.EL, IsSecure()))

val DebugExceptionReturnSS : bits(32) -> bits(1) effect {escape, rreg, undef}

function DebugExceptionReturnSS spsr = {
  assert((Halted() | Restarting()) | PSTATE.EL != EL0, "((Halted() || Restarting()) || ((PSTATE).EL != EL0))");
  SS_bit : bits(1) = 0b0;
  ELd : bits(2) = undefined;
  mask : bits(1) = undefined;
  enabled_at_dest : bool = undefined;
  secure : bool = undefined;
  valid_name : bool = undefined;
  dest : bits(2) = undefined;
  enabled_at_source : bool = undefined;
  if [MDSCR_EL1[0]] == 0b1 then {
    if Restarting() then enabled_at_source = false else if UsingAArch32() then enabled_at_source = AArch32_GenerateDebugExceptions() else enabled_at_source = AArch64_GenerateDebugExceptions();
    if IllegalExceptionReturn(spsr) then dest = PSTATE.EL else {
      (valid_name, dest) = ELFromSPSR(spsr);
      assert(valid_name, "valid")
    };
    secure = IsSecureBelowEL3() | dest == EL3;
    if ELUsingAArch32(dest) then enabled_at_dest = AArch32_GenerateDebugExceptionsFrom(dest, secure) else {
      mask = [spsr[9]];
      enabled_at_dest = AArch64_GenerateDebugExceptionsFrom(dest, secure, mask)
    };
    ELd = DebugTargetFrom(secure);
    if (~(ELUsingAArch32(ELd)) & ~(enabled_at_source)) & enabled_at_dest then SS_bit = [spsr[21]] else ()
  } else ();
  return(SS_bit)
}

val SetPSTATEFromPSR : bits(32) -> unit effect {escape, rreg, undef, wreg}

function SetPSTATEFromPSR spsr__arg = {
  spsr = spsr__arg;
  PSTATE.SS = DebugExceptionReturnSS(spsr);
  if IllegalExceptionReturn(spsr) then PSTATE.IL = 0b1 else {
    PSTATE.IL = [spsr[20]];
    if [spsr[4]] == 0b1 then AArch32_WriteMode(slice(spsr, 0, 5)) else {
      PSTATE.nRW = 0b0;
      PSTATE.EL = slice(spsr, 2, 2);
      PSTATE.SP = [spsr[0]]
    }
  };
  if PSTATE.IL == 0b1 & PSTATE.nRW == 0b1 then if ConstrainUnpredictableBool(Unpredictable_ILZEROT) then spsr = __SetSlice_bits(32, 1, spsr, 5, 0b0) else () else ();
  (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V) = slice(spsr, 28, 4);
  if PSTATE.nRW == 0b1 then {
    PSTATE.Q = [spsr[27]];
    PSTATE.IT = RestoredITBits(spsr);
    PSTATE.GE = slice(spsr, 16, 4);
    PSTATE.E = [spsr[9]];
    (PSTATE.A @ PSTATE.I @ PSTATE.F) = slice(spsr, 6, 3);
    PSTATE.T = [spsr[5]]
  } else (PSTATE.D @ PSTATE.A @ PSTATE.I @ PSTATE.F) = slice(spsr, 6, 4);
  if HavePANExt() then PSTATE.PAN = [spsr[22]] else ();
  if HaveUAOExt() then PSTATE.UAO = [spsr[23]] else ();
  ()
}

val DRPSInstruction : unit -> unit effect {wreg, rreg, undef, escape}

function DRPSInstruction () = {
  SynchronizeContext();
  if (HaveRASExt() & [aget_SCTLR()[21]] == 0b1) & ConstrainUnpredictableBool(Unpredictable_IESBinDebug) then ErrorSynchronizationBarrier(MBReqDomain_FullSystem, MBReqTypes_All) else ();
  SetPSTATEFromPSR(aget_SPSR());
  if UsingAArch32() then {
    (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V @ PSTATE.Q @ PSTATE.GE @ PSTATE.SS @ PSTATE.A @ PSTATE.I @ PSTATE.F) = undefined : bits(13);
    PSTATE.IT = 0x00;
    PSTATE.T = 0b1;
    DLR = undefined : bits(32);
    DSPSR = undefined : bits(32)
  } else {
    (PSTATE.N @ PSTATE.Z @ PSTATE.C @ PSTATE.V @ PSTATE.SS @ PSTATE.D @ PSTATE.A @ PSTATE.I @ PSTATE.F) = undefined : bits(9);
    DLR_EL0 = undefined : bits(64);
    DSPSR_EL0 = undefined : bits(32)
  };
  UpdateEDSCRFields();
  ()
}

val aarch64_branch_unconditional_dret : unit -> unit effect {escape, rreg, undef, wreg}

function aarch64_branch_unconditional_dret () = DRPSInstruction()

val AArch64_ExceptionReturn : (bits(64), bits(32)) -> unit effect {escape, rreg, undef, wreg}

function AArch64_ExceptionReturn (new_pc__arg, spsr) = {
  new_pc = new_pc__arg;
  SynchronizeContext();
  iesb_req : bool = undefined;
  if HaveRASExt() & [aget_SCTLR()[21]] == 0b1 then {
    ErrorSynchronizationBarrier(MBReqDomain_FullSystem, MBReqTypes_All);
    iesb_req = true;
    TakeUnmaskedPhysicalSErrorInterrupts(iesb_req)
  } else ();
  SetPSTATEFromPSR(spsr);
  ClearExclusiveLocal(ProcessorID());
  SendEventLocal();
  if PSTATE.IL == 0b1 then {
    new_pc = __SetSlice_bits(64, 32, new_pc, 32, undefined);
    new_pc = __SetSlice_bits(64, 2, new_pc, 0, undefined)
  } else if UsingAArch32() then if PSTATE.T == 0b0 then new_pc = __SetSlice_bits(64, 1, new_pc, 0, 0b0) else new_pc = __SetSlice_bits(64, 2, new_pc, 0, 0b00) else new_pc = AArch64_BranchAddr(new_pc);
  if UsingAArch32() then BranchTo(slice(new_pc, 0, 32), BranchType_UNKNOWN) else BranchToAddr(new_pc, BranchType_ERET)
}

val aarch64_branch_unconditional_eret : (bool, bool) -> unit effect {escape, rreg, undef, wreg}

function aarch64_branch_unconditional_eret (pac, use_key_a) = {
  AArch64_CheckForERetTrap(pac, use_key_a);
  target : bits(64) = aget_ELR();
  if pac then if use_key_a then target = AuthIA(aget_ELR(), aget_SP()) else target = AuthIB(aget_ELR(), aget_SP()) else ();
  AArch64_ExceptionReturn(target, aget_SPSR())
}

val AArch32_GeneralExceptionsToAArch64 : unit -> bool effect {escape, rreg, undef}

function AArch32_GeneralExceptionsToAArch64 () = return(PSTATE.EL == EL0 & ~(ELUsingAArch32(EL1)) | ((HaveEL(EL2) & ~(IsSecure())) & ~(ELUsingAArch32(EL2))) & [HCR_EL2[27]] == 0b1)

val AArch32_EnterHypMode : (ExceptionRecord, bits(32), int) -> unit effect {escape, rreg, undef, wreg}

function AArch32_EnterHypMode (exception, preferred_exception_return, 'vect_offset) = {
  SynchronizeContext();
  assert((HaveEL(EL2) & ~(IsSecure())) & ELUsingAArch32(EL2), "((HaveEL(EL2) && !(IsSecure())) && ELUsingAArch32(EL2))");
  spsr : bits(32) = GetPSRFromPSTATE();
  if ~(exception.typ == Exception_IRQ | exception.typ == Exception_FIQ) then AArch32_ReportHypEntry(exception) else ();
  AArch32_WriteMode(M32_Hyp);
  aset_SPSR(spsr);
  ELR_hyp = preferred_exception_return;
  PSTATE.T = [HSCTLR[30]];
  PSTATE.SS = 0b0;
  if ~(HaveEL(EL3)) | [aget_SCR_GEN()[3]] == 0b0 then PSTATE.A = 0b1 else ();
  if ~(HaveEL(EL3)) | [aget_SCR_GEN()[1]] == 0b0 then PSTATE.I = 0b1 else ();
  if ~(HaveEL(EL3)) | [aget_SCR_GEN()[2]] == 0b0 then PSTATE.F = 0b1 else ();
  PSTATE.E = [HSCTLR[25]];
  PSTATE.IL = 0b0;
  PSTATE.IT = 0x00;
  BranchTo(slice(HVBAR, 5, 27) @ __GetSlice_int(5, vect_offset, 0), BranchType_UNKNOWN);
  EndOfInstruction()
}

val AArch32_TakeUndefInstrException__0 : unit -> unit effect {escape, undef, wreg, rreg}

val AArch32_TakeUndefInstrException__1 : ExceptionRecord -> unit effect {escape, rreg, undef, wreg}

overload AArch32_TakeUndefInstrException = {
  AArch32_TakeUndefInstrException__0,
  AArch32_TakeUndefInstrException__1
}

function AArch32_TakeUndefInstrException__0 () = {
  exception : ExceptionRecord = ExceptionSyndrome(Exception_Uncategorized);
  AArch32_TakeUndefInstrException(exception)
}

function AArch32_TakeUndefInstrException__1 exception = {
  route_to_hyp : bool = ((HaveEL(EL2) & ~(IsSecure())) & PSTATE.EL == EL0) & [HCR[27]] == 0b1;
  preferred_exception_return : bits(32) = ThisInstrAddr();
  vect_offset : int = 4;
  lr_offset : int = if CurrentInstrSet() == InstrSet_A32 then 4 else 2;
  if PSTATE.EL == EL2 then AArch32_EnterHypMode(exception, preferred_exception_return, vect_offset) else if route_to_hyp then AArch32_EnterHypMode(exception, preferred_exception_return, 20) else AArch32_EnterMode(M32_Undef, preferred_exception_return, lr_offset, vect_offset)
}

val UnallocatedEncoding : unit -> unit effect {escape, rreg, undef, wreg}

function UnallocatedEncoding () = {
  if UsingAArch32() & AArch32_ExecutingCP10or11Instr() then FPEXC = __SetSlice_bits(32, 1, FPEXC, 29, 0b0) else ();
  if UsingAArch32() & ~(AArch32_GeneralExceptionsToAArch64()) then AArch32_TakeUndefInstrException() else AArch64_UndefinedFault()
}

val aarch64_system_exceptions_runtime_hvc : bits(16) -> unit effect {escape, rreg, undef, wreg}

function aarch64_system_exceptions_runtime_hvc imm = {
  if (~(HaveEL(EL2)) | PSTATE.EL == EL0) | PSTATE.EL == EL1 & IsSecure() then UnallocatedEncoding() else ();
  hvc_enable : bits(1) = if HaveEL(EL3) then [SCR_EL3[8]] else ~([HCR_EL2[29]]);
  if hvc_enable == 0b0 then AArch64_UndefinedFault() else AArch64_CallHypervisor(imm)
}

val system_exceptions_runtime_hvc_decode : (bits(3), bits(16), bits(3), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function system_exceptions_runtime_hvc_decode (opc, imm16, op2, LL) = {
  __unconditional = true;
  imm : bits(16) = imm16;
  aarch64_system_exceptions_runtime_hvc(imm)
}

val aarch64_memory_single_general_register : forall 'regsize. (AccType, int, ExtendType, int, MemOp, int, bool, atom('regsize), int, bool, int, bool) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function aarch64_memory_single_general_register (acctype, 'datasize, extend_type, 'm, memop, 'n, postindex, regsize, 'shift, signed, 't, wback__arg) = {
  assert(constraint('regsize >= 0), "regsize constraint");
  let 'dbytes = ex_int(datasize / 8);
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  wback = wback__arg;
  offset : bits(64) = ExtendReg(m, extend_type, shift);
  address : bits(64) = undefined;
  data : bits('datasize) = undefined;
  wb_unknown : bool = false;
  rt_unknown : bool = false;
  c : Constraint = undefined;
  if ((memop == MemOp_LOAD & wback) & n == t) & n != 31 then {
    c = ConstrainUnpredictable(Unpredictable_WBOVERLAPLD);
    assert(c == Constraint_WBSUPPRESS | c == Constraint_UNKNOWN | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_WBSUPPRESS) || ((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP))))");
    match c {
      Constraint_WBSUPPRESS => wback = false,
      Constraint_UNKNOWN => wb_unknown = true,
      Constraint_UNDEF => UnallocatedEncoding(),
      Constraint_NOP => EndOfInstruction()
    }
  } else ();
  if ((memop == MemOp_STORE & wback) & n == t) & n != 31 then {
    c = ConstrainUnpredictable(Unpredictable_WBOVERLAPST);
    assert(c == Constraint_NONE | c == Constraint_UNKNOWN | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_NONE) || ((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP))))");
    match c {
      Constraint_NONE => rt_unknown = false,
      Constraint_UNKNOWN => rt_unknown = true,
      Constraint_UNDEF => UnallocatedEncoding(),
      Constraint_NOP => EndOfInstruction()
    }
  } else ();
  if n == 31 then {
    if memop != MemOp_PREFETCH then CheckSPAlignment() else ();
    address = aget_SP()
  } else address = aget_X(n);
  if ~(postindex) then address = address + offset else ();
  match memop {
    MemOp_STORE => {
      if rt_unknown then data = undefined else data = aget_X(t);
      aset_Mem(address, datasize / 8, acctype, data)
    },
    MemOp_LOAD => {
      data = aget_Mem(address, datasize / 8, acctype);
      if signed then aset_X(t, SignExtend(data, regsize)) else aset_X(t, ZeroExtend(data, regsize))
    },
    MemOp_PREFETCH => Prefetch(address, __GetSlice_int(5, t, 0))
  };
  if wback then {
    if wb_unknown then address = undefined else if postindex then address = address + offset else ();
    if n == 31 then aset_SP(address) else aset_X(n, address)
  } else ()
}

val aarch64_memory_single_general_immediate_unsigned : forall 'regsize. (AccType, int, MemOp, int, bits(64), bool, atom('regsize), bool, int, bool) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function aarch64_memory_single_general_immediate_unsigned (acctype, 'datasize, memop, 'n, offset, postindex, regsize, signed, 't, wback__arg) = {
  assert(constraint('regsize >= 0), "regsize constraint");
  let 'dbytes = ex_int(datasize / 8);
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  wback = wback__arg;
  address : bits(64) = undefined;
  data : bits('datasize) = undefined;
  wb_unknown : bool = false;
  rt_unknown : bool = false;
  c : Constraint = undefined;
  if ((memop == MemOp_LOAD & wback) & n == t) & n != 31 then {
    c = ConstrainUnpredictable(Unpredictable_WBOVERLAPLD);
    assert(c == Constraint_WBSUPPRESS | c == Constraint_UNKNOWN | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_WBSUPPRESS) || ((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP))))");
    match c {
      Constraint_WBSUPPRESS => wback = false,
      Constraint_UNKNOWN => wb_unknown = true,
      Constraint_UNDEF => UnallocatedEncoding(),
      Constraint_NOP => EndOfInstruction()
    }
  } else ();
  if ((memop == MemOp_STORE & wback) & n == t) & n != 31 then {
    c = ConstrainUnpredictable(Unpredictable_WBOVERLAPST);
    assert(c == Constraint_NONE | c == Constraint_UNKNOWN | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_NONE) || ((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP))))");
    match c {
      Constraint_NONE => rt_unknown = false,
      Constraint_UNKNOWN => rt_unknown = true,
      Constraint_UNDEF => UnallocatedEncoding(),
      Constraint_NOP => EndOfInstruction()
    }
  } else ();
  if n == 31 then {
    if memop != MemOp_PREFETCH then CheckSPAlignment() else ();
    address = aget_SP()
  } else address = aget_X(n);
  if ~(postindex) then address = address + offset else ();
  match memop {
    MemOp_STORE => {
      if rt_unknown then data = undefined else data = aget_X(t);
      aset_Mem(address, datasize / 8, acctype, data)
    },
    MemOp_LOAD => {
      data = aget_Mem(address, datasize / 8, acctype);
      if signed then aset_X(t, SignExtend(data, regsize)) else aset_X(t, ZeroExtend(data, regsize))
    },
    MemOp_PREFETCH => Prefetch(address, __GetSlice_int(5, t, 0))
  };
  if wback then {
    if wb_unknown then address = undefined else if postindex then address = address + offset else ();
    if n == 31 then aset_SP(address) else aset_X(n, address)
  } else ()
}

val aarch64_memory_single_general_immediate_signed_postidx : forall 'regsize. (AccType, int, MemOp, int, bits(64), bool, atom('regsize), bool, int, bool) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function aarch64_memory_single_general_immediate_signed_postidx (acctype, 'datasize, memop, 'n, offset, postindex, regsize, signed, 't, wback__arg) = {
  assert(constraint('regsize >= 0), "regsize constraint");
  let 'dbytes = ex_int(datasize / 8);
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  wback = wback__arg;
  address : bits(64) = undefined;
  data : bits('datasize) = undefined;
  wb_unknown : bool = false;
  rt_unknown : bool = false;
  c : Constraint = undefined;
  if ((memop == MemOp_LOAD & wback) & n == t) & n != 31 then {
    c = ConstrainUnpredictable(Unpredictable_WBOVERLAPLD);
    assert(c == Constraint_WBSUPPRESS | c == Constraint_UNKNOWN | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_WBSUPPRESS) || ((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP))))");
    match c {
      Constraint_WBSUPPRESS => wback = false,
      Constraint_UNKNOWN => wb_unknown = true,
      Constraint_UNDEF => UnallocatedEncoding(),
      Constraint_NOP => EndOfInstruction()
    }
  } else ();
  if ((memop == MemOp_STORE & wback) & n == t) & n != 31 then {
    c = ConstrainUnpredictable(Unpredictable_WBOVERLAPST);
    assert(c == Constraint_NONE | c == Constraint_UNKNOWN | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_NONE) || ((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP))))");
    match c {
      Constraint_NONE => rt_unknown = false,
      Constraint_UNKNOWN => rt_unknown = true,
      Constraint_UNDEF => UnallocatedEncoding(),
      Constraint_NOP => EndOfInstruction()
    }
  } else ();
  if n == 31 then {
    if memop != MemOp_PREFETCH then CheckSPAlignment() else ();
    address = aget_SP()
  } else address = aget_X(n);
  if ~(postindex) then address = address + offset else ();
  match memop {
    MemOp_STORE => {
      if rt_unknown then data = undefined else data = aget_X(t);
      aset_Mem(address, datasize / 8, acctype, data)
    },
    MemOp_LOAD => {
      data = aget_Mem(address, datasize / 8, acctype);
      if signed then aset_X(t, SignExtend(data, regsize)) else aset_X(t, ZeroExtend(data, regsize))
    },
    MemOp_PREFETCH => Prefetch(address, __GetSlice_int(5, t, 0))
  };
  if wback then {
    if wb_unknown then address = undefined else if postindex then address = address + offset else ();
    if n == 31 then aset_SP(address) else aset_X(n, address)
  } else ()
}

val aarch64_memory_single_general_immediate_signed_pac : (int, bits(64), int, bool, bool) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function aarch64_memory_single_general_immediate_signed_pac ('n, offset, 't, use_key_a, wback__arg) = {
  wback = wback__arg;
  address : bits(64) = undefined;
  data : bits(64) = undefined;
  wb_unknown : bool = false;
  c : Constraint = undefined;
  if (wback & n == t) & n != 31 then {
    c = ConstrainUnpredictable(Unpredictable_WBOVERLAPLD);
    assert(c == Constraint_WBSUPPRESS | c == Constraint_UNKNOWN | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_WBSUPPRESS) || ((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP))))");
    match c {
      Constraint_WBSUPPRESS => wback = false,
      Constraint_UNKNOWN => wb_unknown = true,
      Constraint_UNDEF => UnallocatedEncoding(),
      Constraint_NOP => EndOfInstruction()
    }
  } else ();
  if n == 31 then {
    CheckSPAlignment();
    address = aget_SP()
  } else address = aget_X(n);
  if use_key_a then address = AuthDA(address, aget_X(31)) else address = AuthDB(address, aget_X(31));
  address = address + offset;
  data = aget_Mem(address, 8, AccType_NORMAL);
  aset_X(t, data);
  if wback then {
    if wb_unknown then address = undefined else ();
    if n == 31 then aset_SP(address) else aset_X(n, address)
  } else ()
}

val aarch64_memory_single_general_immediate_signed_offset_unpriv : forall 'regsize. (AccType, int, MemOp, int, bits(64), bool, atom('regsize), bool, int, bool) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function aarch64_memory_single_general_immediate_signed_offset_unpriv (acctype, 'datasize, memop, 'n, offset, postindex, regsize, signed, 't, wback__arg) = {
  assert(constraint('regsize >= 0), "regsize constraint");
  let 'dbytes = ex_int(datasize / 8);
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  wback = wback__arg;
  address : bits(64) = undefined;
  data : bits('datasize) = undefined;
  wb_unknown : bool = false;
  rt_unknown : bool = false;
  c : Constraint = undefined;
  if ((memop == MemOp_LOAD & wback) & n == t) & n != 31 then {
    c = ConstrainUnpredictable(Unpredictable_WBOVERLAPLD);
    assert(c == Constraint_WBSUPPRESS | c == Constraint_UNKNOWN | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_WBSUPPRESS) || ((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP))))");
    match c {
      Constraint_WBSUPPRESS => wback = false,
      Constraint_UNKNOWN => wb_unknown = true,
      Constraint_UNDEF => UnallocatedEncoding(),
      Constraint_NOP => EndOfInstruction()
    }
  } else ();
  if ((memop == MemOp_STORE & wback) & n == t) & n != 31 then {
    c = ConstrainUnpredictable(Unpredictable_WBOVERLAPST);
    assert(c == Constraint_NONE | c == Constraint_UNKNOWN | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_NONE) || ((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP))))");
    match c {
      Constraint_NONE => rt_unknown = false,
      Constraint_UNKNOWN => rt_unknown = true,
      Constraint_UNDEF => UnallocatedEncoding(),
      Constraint_NOP => EndOfInstruction()
    }
  } else ();
  if n == 31 then {
    if memop != MemOp_PREFETCH then CheckSPAlignment() else ();
    address = aget_SP()
  } else address = aget_X(n);
  if ~(postindex) then address = address + offset else ();
  match memop {
    MemOp_STORE => {
      if rt_unknown then data = undefined else data = aget_X(t);
      aset_Mem(address, datasize / 8, acctype, data)
    },
    MemOp_LOAD => {
      data = aget_Mem(address, datasize / 8, acctype);
      if signed then aset_X(t, SignExtend(data, regsize)) else aset_X(t, ZeroExtend(data, regsize))
    },
    MemOp_PREFETCH => Prefetch(address, __GetSlice_int(5, t, 0))
  };
  if wback then {
    if wb_unknown then address = undefined else if postindex then address = address + offset else ();
    if n == 31 then aset_SP(address) else aset_X(n, address)
  } else ()
}

val aarch64_memory_single_general_immediate_signed_offset_normal : forall 'regsize. (AccType, int, MemOp, int, bits(64), bool, atom('regsize), bool, int, bool) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function aarch64_memory_single_general_immediate_signed_offset_normal (acctype, 'datasize, memop, 'n, offset, postindex, regsize, signed, 't, wback__arg) = {
  assert(constraint('regsize >= 0), "regsize constraint");
  let 'dbytes = ex_int(datasize / 8);
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  wback = wback__arg;
  address : bits(64) = undefined;
  data : bits('datasize) = undefined;
  wb_unknown : bool = false;
  rt_unknown : bool = false;
  c : Constraint = undefined;
  if ((memop == MemOp_LOAD & wback) & n == t) & n != 31 then {
    c = ConstrainUnpredictable(Unpredictable_WBOVERLAPLD);
    assert(c == Constraint_WBSUPPRESS | c == Constraint_UNKNOWN | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_WBSUPPRESS) || ((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP))))");
    match c {
      Constraint_WBSUPPRESS => wback = false,
      Constraint_UNKNOWN => wb_unknown = true,
      Constraint_UNDEF => UnallocatedEncoding(),
      Constraint_NOP => EndOfInstruction()
    }
  } else ();
  if ((memop == MemOp_STORE & wback) & n == t) & n != 31 then {
    c = ConstrainUnpredictable(Unpredictable_WBOVERLAPST);
    assert(c == Constraint_NONE | c == Constraint_UNKNOWN | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_NONE) || ((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP))))");
    match c {
      Constraint_NONE => rt_unknown = false,
      Constraint_UNKNOWN => rt_unknown = true,
      Constraint_UNDEF => UnallocatedEncoding(),
      Constraint_NOP => EndOfInstruction()
    }
  } else ();
  if n == 31 then {
    if memop != MemOp_PREFETCH then CheckSPAlignment() else ();
    address = aget_SP()
  } else address = aget_X(n);
  if ~(postindex) then address = address + offset else ();
  match memop {
    MemOp_STORE => {
      if rt_unknown then data = undefined else data = aget_X(t);
      aset_Mem(address, datasize / 8, acctype, data)
    },
    MemOp_LOAD => {
      data = aget_Mem(address, datasize / 8, acctype);
      if signed then aset_X(t, SignExtend(data, regsize)) else aset_X(t, ZeroExtend(data, regsize))
    },
    MemOp_PREFETCH => Prefetch(address, __GetSlice_int(5, t, 0))
  };
  if wback then {
    if wb_unknown then address = undefined else if postindex then address = address + offset else ();
    if n == 31 then aset_SP(address) else aset_X(n, address)
  } else ()
}

val aarch64_memory_pair_simdfp_postidx : forall ('datasize : Int).
  (AccType, atom('datasize), MemOp, int, bits(64), bool, int, int, bool) -> unit effect {escape, undef, rreg, wreg, rmem, wmem}

function aarch64_memory_pair_simdfp_postidx (acctype, datasize, memop, n, offset, postindex, t, t2, wback) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  CheckFPAdvSIMDEnabled64();
  address : bits(64) = undefined;
  data1 : bits('datasize) = undefined;
  data2 : bits('datasize) = undefined;
  rt_unknown : bool = false;
  if memop == MemOp_LOAD & t == t2 then {
    c : Constraint = ConstrainUnpredictable(Unpredictable_LDPOVERLAP);
    assert(c == Constraint_UNKNOWN | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP)))");
    match c {
      Constraint_UNKNOWN => rt_unknown = true,
      Constraint_UNDEF => UnallocatedEncoding(),
      Constraint_NOP => EndOfInstruction()
    }
  } else ();
  if n == 31 then {
    CheckSPAlignment();
    address = aget_SP()
  } else address = aget_X(n);
  if ~(postindex) then address = address + offset
  else ();
  match memop {
    MemOp_STORE => {
      data1 = aget_V(t);
      data2 = aget_V(t2);
      aset_Mem(address + 0, dbytes, acctype, data1);
      aset_Mem(address + dbytes, dbytes, acctype, data2)
    },
    MemOp_LOAD => {
      data1 = aget_Mem(address + 0, dbytes, acctype);
      data2 = aget_Mem(address + dbytes, dbytes, acctype);
      if rt_unknown then {
        data1 = undefined;
        data2 = undefined
      } else ();
      aset_V(t, data1);
      aset_V(t2, data2)
    }
  };
  if wback then {
    if postindex then address = address + offset
    else ();
    if n == 31 then aset_SP(address) else aset_X(n, address)
  } else ()
}

val aarch64_memory_pair_simdfp_noalloc : forall ('datasize : Int).
  (AccType, atom('datasize), MemOp, int, bits(64), bool, int, int, bool) -> unit effect {escape, undef, rreg, wreg, rmem, wmem}

function aarch64_memory_pair_simdfp_noalloc (acctype, datasize, memop, n, offset, postindex, t, t2, wback) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  CheckFPAdvSIMDEnabled64();
  address : bits(64) = undefined;
  data1 : bits('datasize) = undefined;
  data2 : bits('datasize) = undefined;
  rt_unknown : bool = false;
  if memop == MemOp_LOAD & t == t2 then {
    c : Constraint = ConstrainUnpredictable(Unpredictable_LDPOVERLAP);
    assert(c == Constraint_UNKNOWN | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP)))");
    match c {
      Constraint_UNKNOWN => rt_unknown = true,
      Constraint_UNDEF => UnallocatedEncoding(),
      Constraint_NOP => EndOfInstruction()
    }
  } else ();
  if n == 31 then {
    CheckSPAlignment();
    address = aget_SP()
  } else address = aget_X(n);
  if ~(postindex) then address = address + offset
  else ();
  match memop {
    MemOp_STORE => {
      data1 = aget_V(t);
      data2 = aget_V(t2);
      aset_Mem(address + 0, dbytes, acctype, data1);
      aset_Mem(address + dbytes, dbytes, acctype, data2)
    },
    MemOp_LOAD => {
      data1 = aget_Mem(address + 0, dbytes, acctype);
      data2 = aget_Mem(address + dbytes, dbytes, acctype);
      if rt_unknown then {
        data1 = undefined;
        data2 = undefined
      } else ();
      aset_V(t, data1);
      aset_V(t2, data2)
    }
  };
  if wback then {
    if postindex then address = address + offset
    else ();
    if n == 31 then aset_SP(address) else aset_X(n, address)
  } else ()
}

val aarch64_memory_pair_general_postidx : forall ('datasize : Int).
  (AccType, atom('datasize), MemOp, int, bits(64), bool, bool, int, int, bool) -> unit effect {escape, undef, rreg, wreg, rmem, wmem}

function aarch64_memory_pair_general_postidx (acctype, datasize, memop, n, offset, postindex, signed, t, t2, wback__arg) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  wback = wback__arg;
  address : bits(64) = undefined;
  data1 : bits('datasize) = undefined;
  data2 : bits('datasize) = undefined;
  rt_unknown : bool = false;
  wb_unknown : bool = false;
  if ((memop == MemOp_LOAD & wback) & (t == n | t2 == n)) & n != 31 then {
    c : Constraint = ConstrainUnpredictable(Unpredictable_WBOVERLAPLD);
    assert(c == Constraint_WBSUPPRESS | c == Constraint_UNKNOWN | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_WBSUPPRESS) || ((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP))))");
    match c {
      Constraint_WBSUPPRESS => wback = false,
      Constraint_UNKNOWN => wb_unknown = true,
      Constraint_UNDEF => UnallocatedEncoding(),
      Constraint_NOP => EndOfInstruction()
    }
  } else ();
  if ((memop == MemOp_STORE & wback) & (t == n | t2 == n)) & n != 31 then {
    c : Constraint = ConstrainUnpredictable(Unpredictable_WBOVERLAPST);
    assert(c == Constraint_NONE | c == Constraint_UNKNOWN | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_NONE) || ((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP))))");
    match c {
      Constraint_NONE => rt_unknown = false,
      Constraint_UNKNOWN => rt_unknown = true,
      Constraint_UNDEF => UnallocatedEncoding(),
      Constraint_NOP => EndOfInstruction()
    }
  } else ();
  if memop == MemOp_LOAD & t == t2 then {
    c : Constraint = ConstrainUnpredictable(Unpredictable_LDPOVERLAP);
    assert(c == Constraint_UNKNOWN | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP)))");
    match c {
      Constraint_UNKNOWN => rt_unknown = true,
      Constraint_UNDEF => UnallocatedEncoding(),
      Constraint_NOP => EndOfInstruction()
    }
  } else ();
  if n == 31 then {
    CheckSPAlignment();
    address = aget_SP()
  } else address = aget_X(n);
  if ~(postindex) then address = address + offset
  else ();
  match memop {
    MemOp_STORE => {
      if rt_unknown & t == n then data1 = undefined
      else data1 = aget_X(t);
      if rt_unknown & t2 == n then data2 = undefined
      else data2 = aget_X(t2);
      aset_Mem(address + 0, dbytes, acctype, data1);
      aset_Mem(address + dbytes, dbytes, acctype, data2)
    },
    MemOp_LOAD => {
      data1 = aget_Mem(address + 0, dbytes, acctype);
      data2 = aget_Mem(address + dbytes, dbytes, acctype);
      if rt_unknown then {
        data1 = undefined;
        data2 = undefined
      } else ();
      if signed then {
        aset_X(t, SignExtend(data1, 64));
        aset_X(t2, SignExtend(data2, 64))
      } else {
        aset_X(t, data1);
        aset_X(t2, data2)
      }
    }
  };
  if wback then {
    if wb_unknown then address = undefined
    else if postindex then address = address + offset
    else ();
    if n == 31 then aset_SP(address) else aset_X(n, address)
  } else ()
}

val aarch64_memory_pair_general_noalloc : forall ('datasize : Int).
  (AccType, atom('datasize), MemOp, int, bits(64), bool, int, int, bool) -> unit effect {escape, undef, rreg, wreg, rmem, wmem}

function aarch64_memory_pair_general_noalloc (acctype, datasize, memop, n, offset, postindex, t, t2, wback) = let 'dbytes = ex_int(datasize / 8) in {
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  address : bits(64) = undefined;
  data1 : bits('datasize) = undefined;
  data2 : bits('datasize) = undefined;
  rt_unknown : bool = false;
  if memop == MemOp_LOAD & t == t2 then {
    c : Constraint = ConstrainUnpredictable(Unpredictable_LDPOVERLAP);
    assert(c == Constraint_UNKNOWN | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP)))");
    match c {
      Constraint_UNKNOWN => rt_unknown = true,
      Constraint_UNDEF => UnallocatedEncoding(),
      Constraint_NOP => EndOfInstruction()
    }
  } else ();
  if n == 31 then {
    CheckSPAlignment();
    address = aget_SP()
  } else address = aget_X(n);
  if ~(postindex) then address = address + offset
  else ();
  match memop {
    MemOp_STORE => {
      if rt_unknown & t == n then data1 = undefined
      else data1 = aget_X(t);
      if rt_unknown & t2 == n then data2 = undefined
      else data2 = aget_X(t2);
      aset_Mem(address + 0, dbytes, acctype, data1);
      aset_Mem(address + dbytes, dbytes, acctype, data2)
    },
    MemOp_LOAD => {
      data1 = aget_Mem(address + 0, dbytes, acctype);
      data2 = aget_Mem(address + dbytes, dbytes, acctype);
      if rt_unknown then {
        data1 = undefined;
        data2 = undefined
      } else ();
      aset_X(t, data1);
      aset_X(t2, data2)
    }
  };
  if wback then {
    if postindex then address = address + offset
    else ();
    if n == 31 then aset_SP(address) else aset_X(n, address)
  } else ()
}

val aarch64_memory_exclusive_single : forall ('datasize : Int) 'elsize ('regsize : Int).
  (AccType, atom('datasize), atom('elsize), MemOp, int, bool, atom('regsize), int, int, int) -> unit effect {escape, undef, rreg, wreg, rmem, wmem}

function aarch64_memory_exclusive_single (acctype, datasize, elsize, memop, n, pair, regsize, s, t, t2) = {
  assert(constraint('regsize >= 0), "destsize constraint");
  let 'dbytes = ex_int(datasize / 8);
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  address : bits(64) = undefined;
  data : bits('datasize) = undefined;
  rt_unknown : bool = false;
  rn_unknown : bool = false;
  if (memop == MemOp_LOAD & pair) & t == t2 then {
    c : Constraint = ConstrainUnpredictable(Unpredictable_LDPOVERLAP);
    assert(c == Constraint_UNKNOWN | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP)))");
    match c {
      Constraint_UNKNOWN => rt_unknown = true,
      Constraint_UNDEF => UnallocatedEncoding(),
      Constraint_NOP => EndOfInstruction()
    }
  } else ();
  if memop == MemOp_STORE then {
    if s == t | pair & s == t2 then {
      c : Constraint = ConstrainUnpredictable(Unpredictable_DATAOVERLAP);
      assert(c == Constraint_UNKNOWN | c == Constraint_NONE | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_UNKNOWN) || ((c == Constraint_NONE) || ((c == Constraint_UNDEF) || (c == Constraint_NOP))))");
      match c {
        Constraint_UNKNOWN => rt_unknown = true,
        Constraint_NONE => rt_unknown = false,
        Constraint_UNDEF => UnallocatedEncoding(),
        Constraint_NOP => EndOfInstruction()
      }
    } else ();
    if s == n & n != 31 then {
      c : Constraint = ConstrainUnpredictable(Unpredictable_BASEOVERLAP);
      assert(c == Constraint_UNKNOWN | c == Constraint_NONE | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_UNKNOWN) || ((c == Constraint_NONE) || ((c == Constraint_UNDEF) || (c == Constraint_NOP))))");
      match c {
        Constraint_UNKNOWN => rn_unknown = true,
        Constraint_NONE => rn_unknown = false,
        Constraint_UNDEF => UnallocatedEncoding(),
        Constraint_NOP => EndOfInstruction()
      }
    } else ()
  } else ();
  if n == 31 then {
    CheckSPAlignment();
    address = aget_SP()
  } else if rn_unknown then address = undefined
  else address = aget_X(n);
  secondstage : bool = undefined;
  iswrite : bool = undefined;
  match memop {
    MemOp_STORE => {
      if rt_unknown then data = undefined
      else if pair then let 'v = ex_int(datasize / 2) in {
        assert(constraint(2 * 'v = 'datasize));
        el1 : bits('v) = aget_X(t);
        el2 : bits('v) = aget_X(t2);
        data = if BigEndian() then el1 @ el2 else el2 @ el1
      } else data = aget_X(t);
      status : bits(1) = 0b1;
      if AArch64_ExclusiveMonitorsPass(address, dbytes) then {
        aset_Mem(address, dbytes, acctype, data);
        status = ExclusiveMonitorsStatus()
      } else ();
      aset_X(s, ZeroExtend(status, 32))
    },
    MemOp_LOAD => {
      AArch64_SetExclusiveMonitors(address, dbytes);
      if pair then {
        assert(constraint(- 'elsize + 'datasize > 0 & 'elsize >= 0));
        if rt_unknown then aset_X(t, undefined : bits(32)) else if elsize == 32 then {
          data = aget_Mem(address, dbytes, acctype);
          if BigEndian() then {
            aset_X(t, slice(data, elsize, negate(elsize) + datasize));
            aset_X(t2, slice(data, 0, elsize))
          } else {
            aset_X(t, slice(data, 0, elsize));
            aset_X(t2, slice(data, elsize, negate(elsize) + datasize))
          }
        } else {
          if address != Align(address, dbytes) then {
            iswrite = false;
            secondstage = false;
            AArch64_Abort(address, AArch64_AlignmentFault(acctype, iswrite, secondstage))
          } else ();
          aset_X(t, aget_Mem(address + 0, 8, acctype));
          aset_X(t2, aget_Mem(address + 8, 8, acctype))
        }
      } else {
        data = aget_Mem(address, dbytes, acctype);
        aset_X(t, ZeroExtend(data, regsize))
      }
    }
  }
}

val memory_exclusive_single_decode : (bits(2), bits(1), bits(1), bits(1), bits(5), bits(1), bits(5), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_exclusive_single_decode (size, o2, L, o1, Rs, o0, Rt2, Rn, Rt) = {
  __unconditional = true;
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  t2 : int = UInt(Rt2);
  s : int = UInt(Rs);
  acctype : AccType = if o0 == 0b1 then AccType_ORDERED else AccType_ATOMIC;
  pair : bool = false;
  memop : MemOp = if L == 0b1 then MemOp_LOAD else MemOp_STORE;
  elsize : int = shl_int(8, UInt(size));
  regsize : int = if elsize == 64 then 64 else 32;
  datasize : int = if pair then elsize * 2 else elsize;
  aarch64_memory_exclusive_single(acctype, datasize, elsize, memop, n, pair, regsize, s, t, t2)
}

val aarch64_memory_exclusive_pair : forall ('datasize : Int) ('regsize : Int) ('elsize : Int).
  (AccType, atom('datasize), atom('elsize), MemOp, int, bool, atom('regsize), int, int, int) -> unit effect {escape, undef, rreg, wreg, rmem, wmem}

function aarch64_memory_exclusive_pair (acctype, datasize, elsize, memop, n, pair, regsize, s, t, t2) = {
  assert(constraint('regsize >= 0), "regsize constraint");
  let 'dbytes = ex_int(datasize / 8);
  assert(constraint('datasize in {8, 16, 32, 64, 128}), "datasize constraint");
  assert(constraint(8 * 'dbytes = 'datasize), "dbytes constraint");
  address : bits(64) = undefined;
  data : bits('datasize) = undefined;
  rt_unknown : bool = false;
  rn_unknown : bool = false;
  if (memop == MemOp_LOAD & pair) & t == t2 then {
    c : Constraint = ConstrainUnpredictable(Unpredictable_LDPOVERLAP);
    assert(c == Constraint_UNKNOWN | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_UNKNOWN) || ((c == Constraint_UNDEF) || (c == Constraint_NOP)))");
    match c {
      Constraint_UNKNOWN => rt_unknown = true,
      Constraint_UNDEF => UnallocatedEncoding(),
      Constraint_NOP => EndOfInstruction()
    }
  } else ();
  if memop == MemOp_STORE then {
    if s == t | pair & s == t2 then {
      c : Constraint = ConstrainUnpredictable(Unpredictable_DATAOVERLAP);
      assert(c == Constraint_UNKNOWN | c == Constraint_NONE | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_UNKNOWN) || ((c == Constraint_NONE) || ((c == Constraint_UNDEF) || (c == Constraint_NOP))))");
      match c {
        Constraint_UNKNOWN => rt_unknown = true,
        Constraint_NONE => rt_unknown = false,
        Constraint_UNDEF => UnallocatedEncoding(),
        Constraint_NOP => EndOfInstruction()
      }
    } else ();
    if s == n & n != 31 then {
      c : Constraint = ConstrainUnpredictable(Unpredictable_BASEOVERLAP);
      assert(c == Constraint_UNKNOWN | c == Constraint_NONE | c == Constraint_UNDEF | c == Constraint_NOP, "((c == Constraint_UNKNOWN) || ((c == Constraint_NONE) || ((c == Constraint_UNDEF) || (c == Constraint_NOP))))");
      match c {
        Constraint_UNKNOWN => rn_unknown = true,
        Constraint_NONE => rn_unknown = false,
        Constraint_UNDEF => UnallocatedEncoding(),
        Constraint_NOP => EndOfInstruction()
      }
    } else ()
  } else ();
  if n == 31 then {
    CheckSPAlignment();
    address = aget_SP()
  } else if rn_unknown then address = undefined
  else address = aget_X(n);
  secondstage : bool = undefined;
  iswrite : bool = undefined;
  match memop {
    MemOp_STORE => {
      if rt_unknown then data = undefined
      else if pair then let 'v = ex_int(datasize / 2) in {
        assert(constraint(2 * 'v = 'datasize));
        el1 : bits('v) = aget_X(t);
        el2 : bits('v) = aget_X(t2);
        data = if BigEndian() then el1 @ el2 else el2 @ el1
      } else data = aget_X(t);
      status : bits(1) = 0b1;
      if AArch64_ExclusiveMonitorsPass(address, dbytes) then {
        aset_Mem(address, dbytes, acctype, data);
        status = ExclusiveMonitorsStatus()
      } else ();
      aset_X(s, ZeroExtend(status, 32))
    },
    MemOp_LOAD => {
      AArch64_SetExclusiveMonitors(address, dbytes);
      if pair then {
        assert(constraint(- 'elsize + 'datasize > 0 & 'elsize >= 0), "datasize constraint");
        if rt_unknown then aset_X(t, undefined : bits(32)) else if elsize == 32 then {
         data = aget_Mem(address, dbytes, acctype);
          if BigEndian() then {
            aset_X(t, slice(data, elsize, negate(elsize) + datasize));
            aset_X(t2, slice(data, 0, elsize))
          } else {
            aset_X(t, slice(data, 0, elsize));
            aset_X(t2, slice(data, elsize, negate(elsize) + datasize))
          }
        } else {
          if address != Align(address, dbytes) then {
            iswrite = false;
            secondstage = false;
            AArch64_Abort(address, AArch64_AlignmentFault(acctype, iswrite, secondstage))
          } else ();
          aset_X(t, aget_Mem(address + 0, 8, acctype));
          aset_X(t2, aget_Mem(address + 8, 8, acctype))
        }
      } else {
        data = aget_Mem(address, dbytes, acctype);
        aset_X(t, ZeroExtend(data, regsize))
      }
    }
  }
}

val memory_exclusive_pair_decode : (bits(1), bits(1), bits(1), bits(1), bits(5), bits(1), bits(5), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_exclusive_pair_decode (sz, o2, L, o1, Rs, o0, Rt2, Rn, Rt) = {
  __unconditional = true;
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  t2 : int = UInt(Rt2);
  s : int = UInt(Rs);
  acctype : AccType = if o0 == 0b1 then AccType_ORDERED else AccType_ATOMIC;
  pair : bool = true;
  memop : MemOp = if L == 0b1 then MemOp_LOAD else MemOp_STORE;
  elsize : int = shl_int(32, UInt(sz));
  regsize : int = if elsize == 64 then 64 else 32;
  datasize : int = if pair then elsize * 2 else elsize;
  aarch64_memory_exclusive_pair(acctype, datasize, elsize, memop, n, pair, regsize, s, t, t2)
}

val aarch64_integer_crc : forall ('size : Int).
  (bool, int, int, int, atom('size)) -> unit effect {escape, undef, rreg, wreg}

function aarch64_integer_crc (crc32c, d, m, n, size) = {
  assert(constraint('size in {8,16,32,64}));
  if ~(HaveCRCExt()) then UnallocatedEncoding() else ();
  acc : bits(32) = aget_X(n);
  val_name : bits('size) = aget_X(m);
  poly : bits(32) = __GetSlice_int(32, if crc32c then 517762881 else 79764919, 0);
  tempacc : bits('size + 32) = BitReverse(acc) @ Zeros(size);
  tempval : bits('size + 32) = BitReverse(val_name) @ Zeros(32);
  aset_X(d, BitReverse(Poly32Mod2(tempacc ^ tempval, poly)))
}

val system_exceptions_debug_exception_decode : (bits(3), bits(16), bits(3), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function system_exceptions_debug_exception_decode (opc, imm16, op2, LL) = {
  __unconditional = true;
  target_level : bits(2) = LL;
  if LL == 0b00 then UnallocatedEncoding() else ();
  if ~(Halted()) then AArch64_UndefinedFault() else ();
  aarch64_system_exceptions_debug_exception(target_level)
}

val system_barriers_decode : (bits(1), bits(2), bits(3), bits(4), bits(4), bits(2), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function system_barriers_decode (L, op0, op1, CRn, CRm, opc, Rt) = {
  __unconditional = true;
  op : MemBarrierOp = undefined;
  domain : MBReqDomain = undefined;
  types : MBReqTypes = undefined;
  match opc {
    0b00 => op = MemBarrierOp_DSB,
    0b01 => op = MemBarrierOp_DMB,
    0b10 => op = MemBarrierOp_ISB,
    _ => UnallocatedEncoding()
  };
  match slice(CRm, 2, 2) {
    0b00 => domain = MBReqDomain_OuterShareable,
    0b01 => domain = MBReqDomain_Nonshareable,
    0b10 => domain = MBReqDomain_InnerShareable,
    0b11 => domain = MBReqDomain_FullSystem
  };
  match slice(CRm, 0, 2) {
    0b01 => types = MBReqTypes_Reads,
    0b10 => types = MBReqTypes_Writes,
    0b11 => types = MBReqTypes_All,
    _ => {
      types = MBReqTypes_All;
      domain = MBReqDomain_FullSystem
    }
  };
  aarch64_system_barriers(domain, op, types)
}

val memory_vector_single_postinc_aarch64_memory_vector_single_nowb__decode : (bits(1), bits(1), bits(1), bits(5), bits(3), bits(1), bits(2), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_vector_single_postinc_aarch64_memory_vector_single_nowb__decode (Q, L, R, Rm, opcode, S, size, Rn, Rt) = {
  __unconditional = true;
  t : int = UInt(Rt);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  wback : bool = true;
  scale : int = UInt(slice(opcode, 1, 2));
  selem : int = UInt([opcode[0]] @ R) + 1;
  replicate : bool = false;
  index : int = undefined;
  match scale {
    3 => {
      if L == 0b0 | S == 0b1 then UnallocatedEncoding() else ();
      scale = UInt(size);
      replicate = true
    },
    0 => index = UInt((Q @ S) @ size),
    1 => {
      if [size[0]] == 0b1 then UnallocatedEncoding() else ();
      index = UInt((Q @ S) @ [size[1]])
    },
    2 => {
      if [size[1]] == 0b1 then UnallocatedEncoding() else ();
      if [size[0]] == 0b0 then index = UInt(Q @ S) else {
        if S == 0b1 then UnallocatedEncoding() else ();
        index = UInt(Q);
        scale = 3
      }
    }
  };
  memop : MemOp = if L == 0b1 then MemOp_LOAD else MemOp_STORE;
  let 'datasize : {|128, 64|} = if Q == 0b1 then 128 else 64;
  esize : int = shl_int(8, scale);
  aarch64_memory_vector_single_nowb(datasize, esize, index, m, memop, n, replicate, selem, t, wback)
}

val memory_vector_single_nowb_aarch64_memory_vector_single_nowb__decode : (bits(1), bits(1), bits(1), bits(3), bits(1), bits(2), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_vector_single_nowb_aarch64_memory_vector_single_nowb__decode (Q, L, R, opcode, S, size, Rn, Rt) = {
  __unconditional = true;
  t : int = UInt(Rt);
  n : int = UInt(Rn);
  m : int = undefined;
  wback : bool = false;
  scale : int = UInt(slice(opcode, 1, 2));
  selem : int = UInt([opcode[0]] @ R) + 1;
  replicate : bool = false;
  index : int = undefined;
  match scale {
    3 => {
      if L == 0b0 | S == 0b1 then UnallocatedEncoding() else ();
      scale = UInt(size);
      replicate = true
    },
    0 => index = UInt((Q @ S) @ size),
    1 => {
      if [size[0]] == 0b1 then UnallocatedEncoding() else ();
      index = UInt((Q @ S) @ [size[1]])
    },
    2 => {
      if [size[1]] == 0b1 then UnallocatedEncoding() else ();
      if [size[0]] == 0b0 then index = UInt(Q @ S) else {
        if S == 0b1 then UnallocatedEncoding() else ();
        index = UInt(Q);
        scale = 3
      }
    }
  };
  memop : MemOp = if L == 0b1 then MemOp_LOAD else MemOp_STORE;
  let 'datasize : {|128, 64|} = if Q == 0b1 then 128 else 64;
  esize : int = shl_int(8, scale);
  aarch64_memory_vector_single_nowb(datasize, esize, index, m, memop, n, replicate, selem, t, wback)
}

val memory_single_simdfp_register_aarch64_memory_single_simdfp_register__decode : (bits(2), bits(1), bits(2), bits(5), bits(3), bits(1), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_single_simdfp_register_aarch64_memory_single_simdfp_register__decode (size, V, opc, Rm, option_name, S, Rn, Rt) = {
  __unconditional = true;
  wback : bool = false;
  postindex : bool = false;
  scale : int = UInt([opc[1]] @ size);
  if scale > 4 then UnallocatedEncoding() else ();
  if [option_name[1]] == 0b0 then UnallocatedEncoding() else ();
  extend_type : ExtendType = DecodeRegExtend(option_name);
  shift : int = if S == 0b1 then scale else 0;
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  m : int = UInt(Rm);
  acctype : AccType = AccType_VEC;
  memop : MemOp = if [opc[0]] == 0b1 then MemOp_LOAD else MemOp_STORE;
  datasize : int = shl_int(8, scale);
  aarch64_memory_single_simdfp_register(acctype, datasize, extend_type, m, memop, n, postindex, shift, t, wback)
}

val memory_single_simdfp_immediate_unsigned_aarch64_memory_single_simdfp_immediate_signed_postidx__decode : (bits(2), bits(1), bits(2), bits(12), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_single_simdfp_immediate_unsigned_aarch64_memory_single_simdfp_immediate_signed_postidx__decode (size, V, opc, imm12, Rn, Rt) = {
  __unconditional = true;
  wback : bool = false;
  postindex : bool = false;
  scale : int = UInt([opc[1]] @ size);
  if scale > 4 then UnallocatedEncoding() else ();
  offset : bits(64) = LSL(ZeroExtend(imm12, 64), scale);
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  acctype : AccType = AccType_VEC;
  memop : MemOp = if [opc[0]] == 0b1 then MemOp_LOAD else MemOp_STORE;
  datasize : int = shl_int(8, scale);
  aarch64_memory_single_simdfp_immediate_signed_postidx(acctype, datasize, memop, n, offset, postindex, t, wback)
}

val memory_single_simdfp_immediate_signed_preidx_aarch64_memory_single_simdfp_immediate_signed_postidx__decode : (bits(2), bits(1), bits(2), bits(9), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_single_simdfp_immediate_signed_preidx_aarch64_memory_single_simdfp_immediate_signed_postidx__decode (size, V, opc, imm9, Rn, Rt) = {
  __unconditional = true;
  wback : bool = true;
  postindex : bool = false;
  scale : int = UInt([opc[1]] @ size);
  if scale > 4 then UnallocatedEncoding() else ();
  offset : bits(64) = SignExtend(imm9, 64);
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  acctype : AccType = AccType_VEC;
  memop : MemOp = if [opc[0]] == 0b1 then MemOp_LOAD else MemOp_STORE;
  datasize : int = shl_int(8, scale);
  aarch64_memory_single_simdfp_immediate_signed_postidx(acctype, datasize, memop, n, offset, postindex, t, wback)
}

val memory_single_simdfp_immediate_signed_postidx_aarch64_memory_single_simdfp_immediate_signed_postidx__decode : (bits(2), bits(1), bits(2), bits(9), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_single_simdfp_immediate_signed_postidx_aarch64_memory_single_simdfp_immediate_signed_postidx__decode (size, V, opc, imm9, Rn, Rt) = {
  __unconditional = true;
  wback : bool = true;
  postindex : bool = true;
  scale : int = UInt([opc[1]] @ size);
  if scale > 4 then UnallocatedEncoding() else ();
  offset : bits(64) = SignExtend(imm9, 64);
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  acctype : AccType = AccType_VEC;
  memop : MemOp = if [opc[0]] == 0b1 then MemOp_LOAD else MemOp_STORE;
  datasize : int = shl_int(8, scale);
  aarch64_memory_single_simdfp_immediate_signed_postidx(acctype, datasize, memop, n, offset, postindex, t, wback)
}

val memory_single_simdfp_immediate_signed_offset_normal_aarch64_memory_single_simdfp_immediate_signed_offset_normal__decode : (bits(2), bits(1), bits(2), bits(9), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_single_simdfp_immediate_signed_offset_normal_aarch64_memory_single_simdfp_immediate_signed_offset_normal__decode (size, V, opc, imm9, Rn, Rt) = {
  __unconditional = true;
  wback : bool = false;
  postindex : bool = false;
  scale : int = UInt([opc[1]] @ size);
  if scale > 4 then UnallocatedEncoding() else ();
  offset : bits(64) = SignExtend(imm9, 64);
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  acctype : AccType = AccType_VEC;
  memop : MemOp = if [opc[0]] == 0b1 then MemOp_LOAD else MemOp_STORE;
  datasize : int = shl_int(8, scale);
  aarch64_memory_single_simdfp_immediate_signed_offset_normal(acctype, datasize, memop, n, offset, postindex, t, wback)
}

val memory_single_general_register_aarch64_memory_single_general_register__decode : (bits(2), bits(1), bits(2), bits(5), bits(3), bits(1), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_single_general_register_aarch64_memory_single_general_register__decode (size, V, opc, Rm, option_name, S, Rn, Rt) = {
  __unconditional = true;
  wback : bool = false;
  postindex : bool = false;
  scale : int = UInt(size);
  if [option_name[1]] == 0b0 then UnallocatedEncoding() else ();
  extend_type : ExtendType = DecodeRegExtend(option_name);
  shift : int = if S == 0b1 then scale else 0;
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  m : int = UInt(Rm);
  acctype : AccType = AccType_NORMAL;
  memop : MemOp = undefined;
  signed : bool = undefined;
  regsize : int = undefined;
  if [opc[1]] == 0b0 then {
    memop = if [opc[0]] == 0b1 then MemOp_LOAD else MemOp_STORE;
    regsize = if size == 0b11 then 64 else 32;
    signed = false
  } else if size == 0b11 then {
    memop = MemOp_PREFETCH;
    if [opc[0]] == 0b1 then UnallocatedEncoding() else ()
  } else {
    memop = MemOp_LOAD;
    if size == 0b10 & [opc[0]] == 0b1 then UnallocatedEncoding() else ();
    regsize = if [opc[0]] == 0b1 then 32 else 64;
    signed = true
  };
  datasize : int = shl_int(8, scale);
  aarch64_memory_single_general_register(acctype, datasize, extend_type, m, memop, n, postindex, regsize, shift, signed, t, wback)
}

val memory_single_general_immediate_unsigned_aarch64_memory_single_general_immediate_unsigned__decode : (bits(2), bits(1), bits(2), bits(12), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_single_general_immediate_unsigned_aarch64_memory_single_general_immediate_unsigned__decode (size, V, opc, imm12, Rn, Rt) = {
  __unconditional = true;
  wback : bool = false;
  postindex : bool = false;
  scale : int = UInt(size);
  offset : bits(64) = LSL(ZeroExtend(imm12, 64), scale);
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  acctype : AccType = AccType_NORMAL;
  memop : MemOp = undefined;
  signed : bool = undefined;
  regsize : int = undefined;
  if [opc[1]] == 0b0 then {
    memop = if [opc[0]] == 0b1 then MemOp_LOAD else MemOp_STORE;
    regsize = if size == 0b11 then 64 else 32;
    signed = false
  } else if size == 0b11 then {
    memop = MemOp_PREFETCH;
    if [opc[0]] == 0b1 then UnallocatedEncoding() else ()
  } else {
    memop = MemOp_LOAD;
    if size == 0b10 & [opc[0]] == 0b1 then UnallocatedEncoding() else ();
    regsize = if [opc[0]] == 0b1 then 32 else 64;
    signed = true
  };
  datasize : int = shl_int(8, scale);
  aarch64_memory_single_general_immediate_unsigned(acctype, datasize, memop, n, offset, postindex, regsize, signed, t, wback)
}

val memory_single_general_immediate_unsigned_aarch64_memory_single_general_immediate_signed_postidx__decode : (bits(2), bits(1), bits(2), bits(12), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_single_general_immediate_unsigned_aarch64_memory_single_general_immediate_signed_postidx__decode (size, V, opc, imm12, Rn, Rt) = {
  __unconditional = true;
  wback : bool = false;
  postindex : bool = false;
  scale : int = UInt(size);
  offset : bits(64) = LSL(ZeroExtend(imm12, 64), scale);
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  acctype : AccType = AccType_NORMAL;
  memop : MemOp = undefined;
  signed : bool = undefined;
  regsize : int = undefined;
  if [opc[1]] == 0b0 then {
    memop = if [opc[0]] == 0b1 then MemOp_LOAD else MemOp_STORE;
    regsize = if size == 0b11 then 64 else 32;
    signed = false
  } else if size == 0b11 then UnallocatedEncoding() else {
    memop = MemOp_LOAD;
    if size == 0b10 & [opc[0]] == 0b1 then UnallocatedEncoding() else ();
    regsize = if [opc[0]] == 0b1 then 32 else 64;
    signed = true
  };
  datasize : int = shl_int(8, scale);
  aarch64_memory_single_general_immediate_signed_postidx(acctype, datasize, memop, n, offset, postindex, regsize, signed, t, wback)
}

val memory_single_general_immediate_signed_preidx_aarch64_memory_single_general_immediate_signed_postidx__decode : (bits(2), bits(1), bits(2), bits(9), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_single_general_immediate_signed_preidx_aarch64_memory_single_general_immediate_signed_postidx__decode (size, V, opc, imm9, Rn, Rt) = {
  __unconditional = true;
  wback : bool = true;
  postindex : bool = false;
  scale : int = UInt(size);
  offset : bits(64) = SignExtend(imm9, 64);
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  acctype : AccType = AccType_NORMAL;
  memop : MemOp = undefined;
  signed : bool = undefined;
  regsize : int = undefined;
  if [opc[1]] == 0b0 then {
    memop = if [opc[0]] == 0b1 then MemOp_LOAD else MemOp_STORE;
    regsize = if size == 0b11 then 64 else 32;
    signed = false
  } else if size == 0b11 then UnallocatedEncoding() else {
    memop = MemOp_LOAD;
    if size == 0b10 & [opc[0]] == 0b1 then UnallocatedEncoding() else ();
    regsize = if [opc[0]] == 0b1 then 32 else 64;
    signed = true
  };
  datasize : int = shl_int(8, scale);
  aarch64_memory_single_general_immediate_signed_postidx(acctype, datasize, memop, n, offset, postindex, regsize, signed, t, wback)
}

val memory_single_general_immediate_signed_postidx_aarch64_memory_single_general_immediate_signed_postidx__decode : (bits(2), bits(1), bits(2), bits(9), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_single_general_immediate_signed_postidx_aarch64_memory_single_general_immediate_signed_postidx__decode (size, V, opc, imm9, Rn, Rt) = {
  __unconditional = true;
  wback : bool = true;
  postindex : bool = true;
  scale : int = UInt(size);
  offset : bits(64) = SignExtend(imm9, 64);
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  acctype : AccType = AccType_NORMAL;
  memop : MemOp = undefined;
  signed : bool = undefined;
  regsize : int = undefined;
  if [opc[1]] == 0b0 then {
    memop = if [opc[0]] == 0b1 then MemOp_LOAD else MemOp_STORE;
    regsize = if size == 0b11 then 64 else 32;
    signed = false
  } else if size == 0b11 then UnallocatedEncoding() else {
    memop = MemOp_LOAD;
    if size == 0b10 & [opc[0]] == 0b1 then UnallocatedEncoding() else ();
    regsize = if [opc[0]] == 0b1 then 32 else 64;
    signed = true
  };
  datasize : int = shl_int(8, scale);
  aarch64_memory_single_general_immediate_signed_postidx(acctype, datasize, memop, n, offset, postindex, regsize, signed, t, wback)
}

val memory_single_general_immediate_signed_pac_decode : (bits(2), bits(1), bits(1), bits(1), bits(9), bits(1), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_single_general_immediate_signed_pac_decode (size, V, M, S, imm9, W, Rn, Rt) = {
  __unconditional = true;
  if ~(HavePACExt()) | size != 0b11 then UnallocatedEncoding() else ();
  t : int = UInt(Rt);
  n : int = UInt(Rn);
  wback : bool = W == 0b1;
  use_key_a : bool = M == 0b0;
  S10 : bits(10) = S @ imm9;
  scale : int = 3;
  offset : bits(64) = LSL(SignExtend(S10, 64), scale);
  aarch64_memory_single_general_immediate_signed_pac(n, offset, t, use_key_a, wback)
}

val memory_single_general_immediate_signed_offset_unpriv_aarch64_memory_single_general_immediate_signed_offset_unpriv__decode : (bits(2), bits(1), bits(2), bits(9), bits(5), bits(5)) -> unit effect {escape, undef, rreg, wreg, rmem, wmem}

function memory_single_general_immediate_signed_offset_unpriv_aarch64_memory_single_general_immediate_signed_offset_unpriv__decode (size, V, opc, imm9, Rn, Rt) = {
  __unconditional = true;
  wback : bool = false;
  postindex : bool = false;
  scale : int = UInt(size);
  offset : bits(64) = SignExtend(imm9, 64);
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  acctype : AccType = AccType_UNPRIV;
  if ((HaveNVExt() & HaveEL(EL2)) & [HCR_EL2[42]] == 0b1) & [HCR_EL2[43]] == 0b1 then
    acctype = AccType_NORMAL
  else ();
  memop : MemOp = undefined;
  signed : bool = undefined;
  regsize : int = undefined;
  if [opc[1]] == 0b0 then {
    memop = if [opc[0]] == 0b1 then MemOp_LOAD else MemOp_STORE;
    regsize = if size == 0b11 then 64 else 32;
    signed = false
  } else if size == 0b11 then UnallocatedEncoding() else {
    memop = MemOp_LOAD;
    if size == 0b10 & [opc[0]] == 0b1 then UnallocatedEncoding() else ();
    regsize = if [opc[0]] == 0b1 then 32 else 64;
    signed = true
  };
  datasize : int = shl_int(8, scale);
  aarch64_memory_single_general_immediate_signed_offset_unpriv(acctype, datasize, memop, n, offset, postindex, regsize, signed, t, wback)
}

val memory_single_general_immediate_signed_offset_normal_aarch64_memory_single_general_immediate_signed_offset_normal__decode : (bits(2), bits(1), bits(2), bits(9), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_single_general_immediate_signed_offset_normal_aarch64_memory_single_general_immediate_signed_offset_normal__decode (size, V, opc, imm9, Rn, Rt) = {
  __unconditional = true;
  wback : bool = false;
  postindex : bool = false;
  scale : int = UInt(size);
  offset : bits(64) = SignExtend(imm9, 64);
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  acctype : AccType = AccType_NORMAL;
  memop : MemOp = undefined;
  signed : bool = undefined;
  regsize : int = undefined;
  if [opc[1]] == 0b0 then {
    memop = if [opc[0]] == 0b1 then MemOp_LOAD else MemOp_STORE;
    regsize = if size == 0b11 then 64 else 32;
    signed = false
  } else if size == 0b11 then {
    memop = MemOp_PREFETCH;
    if [opc[0]] == 0b1 then UnallocatedEncoding() else ()
  } else {
    memop = MemOp_LOAD;
    if size == 0b10 & [opc[0]] == 0b1 then UnallocatedEncoding() else ();
    regsize = if [opc[0]] == 0b1 then 32 else 64;
    signed = true
  };
  datasize : int = shl_int(8, scale);
  aarch64_memory_single_general_immediate_signed_offset_normal(acctype, datasize, memop, n, offset, postindex, regsize, signed, t, wback)
}

val memory_pair_simdfp_preidx_aarch64_memory_pair_simdfp_postidx__decode : (bits(2), bits(1), bits(1), bits(7), bits(5), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_pair_simdfp_preidx_aarch64_memory_pair_simdfp_postidx__decode (opc, V, L, imm7, Rt2, Rn, Rt) = {
  __unconditional = true;
  wback : bool = true;
  postindex : bool = false;
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  t2 : int = UInt(Rt2);
  acctype : AccType = AccType_VEC;
  memop : MemOp = if L == 0b1 then MemOp_LOAD else MemOp_STORE;
  if opc == 0b11 then UnallocatedEncoding() else ();
  scale : int = 2 + UInt(opc);
  datasize : int = shl_int(8, scale);
  offset : bits(64) = LSL(SignExtend(imm7, 64), scale);
  aarch64_memory_pair_simdfp_postidx(acctype, datasize, memop, n, offset, postindex, t, t2, wback)
}

val memory_pair_simdfp_postidx_aarch64_memory_pair_simdfp_postidx__decode : (bits(2), bits(1), bits(1), bits(7), bits(5), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_pair_simdfp_postidx_aarch64_memory_pair_simdfp_postidx__decode (opc, V, L, imm7, Rt2, Rn, Rt) = {
  __unconditional = true;
  wback : bool = true;
  postindex : bool = true;
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  t2 : int = UInt(Rt2);
  acctype : AccType = AccType_VEC;
  memop : MemOp = if L == 0b1 then MemOp_LOAD else MemOp_STORE;
  if opc == 0b11 then UnallocatedEncoding() else ();
  scale : int = 2 + UInt(opc);
  datasize : int = shl_int(8, scale);
  offset : bits(64) = LSL(SignExtend(imm7, 64), scale);
  aarch64_memory_pair_simdfp_postidx(acctype, datasize, memop, n, offset, postindex, t, t2, wback)
}

val memory_pair_simdfp_offset_aarch64_memory_pair_simdfp_postidx__decode : (bits(2), bits(1), bits(1), bits(7), bits(5), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_pair_simdfp_offset_aarch64_memory_pair_simdfp_postidx__decode (opc, V, L, imm7, Rt2, Rn, Rt) = {
  __unconditional = true;
  wback : bool = false;
  postindex : bool = false;
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  t2 : int = UInt(Rt2);
  acctype : AccType = AccType_VEC;
  memop : MemOp = if L == 0b1 then MemOp_LOAD else MemOp_STORE;
  if opc == 0b11 then UnallocatedEncoding() else ();
  scale : int = 2 + UInt(opc);
  datasize : int = shl_int(8, scale);
  offset : bits(64) = LSL(SignExtend(imm7, 64), scale);
  aarch64_memory_pair_simdfp_postidx(acctype, datasize, memop, n, offset, postindex, t, t2, wback)
}

val memory_pair_simdfp_noalloc_aarch64_memory_pair_simdfp_noalloc__decode : (bits(2), bits(1), bits(1), bits(7), bits(5), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_pair_simdfp_noalloc_aarch64_memory_pair_simdfp_noalloc__decode (opc, V, L, imm7, Rt2, Rn, Rt) = {
  __unconditional = true;
  wback : bool = false;
  postindex : bool = false;
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  t2 : int = UInt(Rt2);
  acctype : AccType = AccType_VECSTREAM;
  memop : MemOp = if L == 0b1 then MemOp_LOAD else MemOp_STORE;
  if opc == 0b11 then UnallocatedEncoding() else ();
  scale : int = 2 + UInt(opc);
  datasize : int = shl_int(8, scale);
  offset : bits(64) = LSL(SignExtend(imm7, 64), scale);
  aarch64_memory_pair_simdfp_noalloc(acctype, datasize, memop, n, offset, postindex, t, t2, wback)
}

val memory_pair_general_preidx_aarch64_memory_pair_general_postidx__decode : (bits(2), bits(1), bits(1), bits(7), bits(5), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_pair_general_preidx_aarch64_memory_pair_general_postidx__decode (opc, V, L, imm7, Rt2, Rn, Rt) = {
  __unconditional = true;
  wback : bool = true;
  postindex : bool = false;
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  t2 : int = UInt(Rt2);
  acctype : AccType = AccType_NORMAL;
  memop : MemOp = if L == 0b1 then MemOp_LOAD else MemOp_STORE;
  if (L @ [opc[0]]) == 0b01 | opc == 0b11 then UnallocatedEncoding() else ();
  signed : bool = [opc[0]] != 0b0;
  scale : int = 2 + UInt([opc[1]]);
  datasize : int = shl_int(8, scale);
  offset : bits(64) = LSL(SignExtend(imm7, 64), scale);
  aarch64_memory_pair_general_postidx(acctype, datasize, memop, n, offset, postindex, signed, t, t2, wback)
}

val memory_pair_general_postidx_aarch64_memory_pair_general_postidx__decode : (bits(2), bits(1), bits(1), bits(7), bits(5), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_pair_general_postidx_aarch64_memory_pair_general_postidx__decode (opc, V, L, imm7, Rt2, Rn, Rt) = {
  __unconditional = true;
  wback : bool = true;
  postindex : bool = true;
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  t2 : int = UInt(Rt2);
  acctype : AccType = AccType_NORMAL;
  memop : MemOp = if L == 0b1 then MemOp_LOAD else MemOp_STORE;
  if (L @ [opc[0]]) == 0b01 | opc == 0b11 then UnallocatedEncoding() else ();
  signed : bool = [opc[0]] != 0b0;
  scale : int = 2 + UInt([opc[1]]);
  datasize : int = shl_int(8, scale);
  offset : bits(64) = LSL(SignExtend(imm7, 64), scale);
  aarch64_memory_pair_general_postidx(acctype, datasize, memop, n, offset, postindex, signed, t, t2, wback)
}

val memory_pair_general_offset_aarch64_memory_pair_general_postidx__decode : (bits(2), bits(1), bits(1), bits(7), bits(5), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_pair_general_offset_aarch64_memory_pair_general_postidx__decode (opc, V, L, imm7, Rt2, Rn, Rt) = {
  __unconditional = true;
  wback : bool = false;
  postindex : bool = false;
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  t2 : int = UInt(Rt2);
  acctype : AccType = AccType_NORMAL;
  memop : MemOp = if L == 0b1 then MemOp_LOAD else MemOp_STORE;
  if (L @ [opc[0]]) == 0b01 | opc == 0b11 then UnallocatedEncoding() else ();
  signed : bool = [opc[0]] != 0b0;
  scale : int = 2 + UInt([opc[1]]);
  datasize : int = shl_int(8, scale);
  offset : bits(64) = LSL(SignExtend(imm7, 64), scale);
  aarch64_memory_pair_general_postidx(acctype, datasize, memop, n, offset, postindex, signed, t, t2, wback)
}

val memory_pair_general_noalloc_aarch64_memory_pair_general_noalloc__decode : (bits(2), bits(1), bits(1), bits(7), bits(5), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_pair_general_noalloc_aarch64_memory_pair_general_noalloc__decode (opc, V, L, imm7, Rt2, Rn, Rt) = {
  __unconditional = true;
  wback : bool = false;
  postindex : bool = false;
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  t2 : int = UInt(Rt2);
  acctype : AccType = AccType_STREAM;
  memop : MemOp = if L == 0b1 then MemOp_LOAD else MemOp_STORE;
  if [opc[0]] == 0b1 then UnallocatedEncoding() else ();
  scale : int = 2 + UInt([opc[1]]);
  datasize : int = shl_int(8, scale);
  offset : bits(64) = LSL(SignExtend(imm7, 64), scale);
  aarch64_memory_pair_general_noalloc(acctype, datasize, memop, n, offset, postindex, t, t2, wback)
}

val memory_literal_simdfp_decode : (bits(2), bits(1), bits(19), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_literal_simdfp_decode (opc, V, imm19, Rt) = {
  __unconditional = true;
  t : int = UInt(Rt);
  size : int = undefined;
  offset : bits(64) = undefined;
  match opc {
    0b00 => size = 4,
    0b01 => size = 8,
    0b10 => size = 16,
    0b11 => UnallocatedEncoding()
  };
  offset = SignExtend(imm19 @ 0b00, 64);
  aarch64_memory_literal_simdfp(offset, size, t)
}

val memory_atomicops_swp_decode : (bits(2), bits(1), bits(1), bits(1), bits(5), bits(1), bits(3), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_atomicops_swp_decode (size, V, A, R, Rs, o3, opc, Rn, Rt) = {
  __unconditional = true;
  if ~(HaveAtomicExt()) then UnallocatedEncoding() else ();
  t : int = UInt(Rt);
  n : int = UInt(Rn);
  s : int = UInt(Rs);
  datasize : int = shl_int(8, UInt(size));
  regsize : int = if datasize == 64 then 64 else 32;
  ldacctype : AccType = if A == 0b1 & Rt != 0b11111 then AccType_ORDEREDRW else AccType_ATOMICRW;
  stacctype : AccType = if R == 0b1 then AccType_ORDEREDRW else AccType_ATOMICRW;
  aarch64_memory_atomicops_swp(datasize, ldacctype, n, regsize, s, stacctype, t)
}

val memory_atomicops_st_decode : (bits(2), bits(1), bits(1), bits(1), bits(5), bits(1), bits(3), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_atomicops_st_decode (size, V, A, R, Rs, o3, opc, Rn, Rt) = {
  __unconditional = true;
  if ~(HaveAtomicExt()) then UnallocatedEncoding() else ();
  n : int = UInt(Rn);
  s : int = UInt(Rs);
  datasize : int = shl_int(8, UInt(size));
  regsize : int = if datasize == 64 then 64 else 32;
  ldacctype : AccType = AccType_ATOMICRW;
  stacctype : AccType = if R == 0b1 then AccType_ORDEREDRW else AccType_ATOMICRW;
  op : MemAtomicOp = undefined;
  match opc {
    0b000 => op = MemAtomicOp_ADD,
    0b001 => op = MemAtomicOp_BIC,
    0b010 => op = MemAtomicOp_EOR,
    0b011 => op = MemAtomicOp_ORR,
    0b100 => op = MemAtomicOp_SMAX,
    0b101 => op = MemAtomicOp_SMIN,
    0b110 => op = MemAtomicOp_UMAX,
    0b111 => op = MemAtomicOp_UMIN
  };
  aarch64_memory_atomicops_st(datasize, ldacctype, n, op, s, stacctype)
}

val memory_atomicops_ld_decode : (bits(2), bits(1), bits(1), bits(1), bits(5), bits(1), bits(3), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_atomicops_ld_decode (size, V, A, R, Rs, o3, opc, Rn, Rt) = {
  __unconditional = true;
  if ~(HaveAtomicExt()) then UnallocatedEncoding() else ();
  t : int = UInt(Rt);
  n : int = UInt(Rn);
  s : int = UInt(Rs);
  datasize : int = shl_int(8, UInt(size));
  regsize : int = if datasize == 64 then 64 else 32;
  ldacctype : AccType = if A == 0b1 & Rt != 0b11111 then AccType_ORDEREDRW else AccType_ATOMICRW;
  stacctype : AccType = if R == 0b1 then AccType_ORDEREDRW else AccType_ATOMICRW;
  op : MemAtomicOp = undefined;
  match opc {
    0b000 => op = MemAtomicOp_ADD,
    0b001 => op = MemAtomicOp_BIC,
    0b010 => op = MemAtomicOp_EOR,
    0b011 => op = MemAtomicOp_ORR,
    0b100 => op = MemAtomicOp_SMAX,
    0b101 => op = MemAtomicOp_SMIN,
    0b110 => op = MemAtomicOp_UMAX,
    0b111 => op = MemAtomicOp_UMIN
  };
  aarch64_memory_atomicops_ld(datasize, ldacctype, n, op, regsize, s, stacctype, t)
}

val memory_atomicops_cas_single_decode : (bits(2), bits(1), bits(1), bits(1), bits(5), bits(1), bits(5), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_atomicops_cas_single_decode (size, o2, L, o1, Rs, o0, Rt2, Rn, Rt) = {
  __unconditional = true;
  if ~(HaveAtomicExt()) then UnallocatedEncoding() else ();
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  s : int = UInt(Rs);
  datasize : int = shl_int(8, UInt(size));
  regsize : int = if datasize == 64 then 64 else 32;
  ldacctype : AccType = if L == 0b1 then AccType_ORDEREDRW else AccType_ATOMICRW;
  stacctype : AccType = if o0 == 0b1 then AccType_ORDEREDRW else AccType_ATOMICRW;
  aarch64_memory_atomicops_cas_single(datasize, ldacctype, n, regsize, s, stacctype, t)
}

val memory_atomicops_cas_pair_decode : (bits(1), bits(1), bits(1), bits(1), bits(5), bits(1), bits(5), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_atomicops_cas_pair_decode (sz, o2, L, o1, Rs, o0, Rt2, Rn, Rt) = {
  __unconditional = true;
  if ~(HaveAtomicExt()) then UnallocatedEncoding() else ();
  if [Rs[0]] == 0b1 then UnallocatedEncoding() else ();
  if [Rt[0]] == 0b1 then UnallocatedEncoding() else ();
  n : int = UInt(Rn);
  t : int = UInt(Rt);
  s : int = UInt(Rs);
  datasize : int = shl_int(32, UInt(sz));
  regsize : int = datasize;
  ldacctype : AccType = if L == 0b1 then AccType_ORDEREDRW else AccType_ATOMICRW;
  stacctype : AccType = if o0 == 0b1 then AccType_ORDEREDRW else AccType_ATOMICRW;
  aarch64_memory_atomicops_cas_pair(datasize, ldacctype, n, regsize, s, stacctype, t)
}

val integer_pac_strip_dp_1src_decode : (bits(1), bits(1), bits(5), bits(1), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_pac_strip_dp_1src_decode (sf, S, opcode2, D, Rn, Rd) = {
  __unconditional = true;
  data : bool = D == 0b1;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  if ~(HavePACExt()) then UnallocatedEncoding() else ();
  if n != 31 then UnallocatedEncoding() else ();
  aarch64_integer_pac_strip_dp_1src(d, data)
}

val integer_pac_pacib_dp_1src_decode : (bits(1), bits(1), bits(5), bits(1), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_pac_pacib_dp_1src_decode (sf, S, opcode2, Z, Rn, Rd) = {
  __unconditional = true;
  source_is_sp : bool = false;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  if ~(HavePACExt()) then UnallocatedEncoding() else ();
  if Z == 0b0 then if n == 31 then source_is_sp = true else () else if n != 31 then UnallocatedEncoding() else ();
  aarch64_integer_pac_pacib_dp_1src(d, n, source_is_sp)
}

val integer_pac_pacia_dp_1src_decode : (bits(1), bits(1), bits(5), bits(1), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_pac_pacia_dp_1src_decode (sf, S, opcode2, Z, Rn, Rd) = {
  __unconditional = true;
  source_is_sp : bool = false;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  if ~(HavePACExt()) then UnallocatedEncoding() else ();
  if Z == 0b0 then if n == 31 then source_is_sp = true else () else if n != 31 then UnallocatedEncoding() else ();
  aarch64_integer_pac_pacia_dp_1src(d, n, source_is_sp)
}

val integer_pac_pacga_dp_2src_decode : (bits(1), bits(1), bits(1), bits(5), bits(6), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_pac_pacga_dp_2src_decode (sf, op, S, Rm, opcode2, Rn, Rd) = {
  __unconditional = true;
  source_is_sp : bool = false;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  if ~(HavePACExt()) then UnallocatedEncoding() else ();
  if m == 31 then source_is_sp = true else ();
  aarch64_integer_pac_pacga_dp_2src(d, m, n, source_is_sp)
}

val integer_pac_pacdb_dp_1src_decode : (bits(1), bits(1), bits(5), bits(1), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_pac_pacdb_dp_1src_decode (sf, S, opcode2, Z, Rn, Rd) = {
  __unconditional = true;
  source_is_sp : bool = false;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  if ~(HavePACExt()) then UnallocatedEncoding() else ();
  if Z == 0b0 then if n == 31 then source_is_sp = true else () else if n != 31 then UnallocatedEncoding() else ();
  aarch64_integer_pac_pacdb_dp_1src(d, n, source_is_sp)
}

val integer_pac_pacda_dp_1src_decode : (bits(1), bits(1), bits(5), bits(1), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_pac_pacda_dp_1src_decode (sf, S, opcode2, Z, Rn, Rd) = {
  __unconditional = true;
  source_is_sp : bool = false;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  if ~(HavePACExt()) then UnallocatedEncoding() else ();
  if Z == 0b0 then if n == 31 then source_is_sp = true else () else if n != 31 then UnallocatedEncoding() else ();
  aarch64_integer_pac_pacda_dp_1src(d, n, source_is_sp)
}

val integer_pac_autib_dp_1src_decode : (bits(1), bits(1), bits(5), bits(1), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_pac_autib_dp_1src_decode (sf, S, opcode2, Z, Rn, Rd) = {
  __unconditional = true;
  source_is_sp : bool = false;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  if ~(HavePACExt()) then UnallocatedEncoding() else ();
  if Z == 0b0 then if n == 31 then source_is_sp = true else () else if n != 31 then UnallocatedEncoding() else ();
  aarch64_integer_pac_autib_dp_1src(d, n, source_is_sp)
}

val integer_pac_autia_dp_1src_decode : (bits(1), bits(1), bits(5), bits(1), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_pac_autia_dp_1src_decode (sf, S, opcode2, Z, Rn, Rd) = {
  __unconditional = true;
  source_is_sp : bool = false;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  if ~(HavePACExt()) then UnallocatedEncoding() else ();
  if Z == 0b0 then if n == 31 then source_is_sp = true else () else if n != 31 then UnallocatedEncoding() else ();
  aarch64_integer_pac_autia_dp_1src(d, n, source_is_sp)
}

val integer_pac_autdb_dp_1src_decode : (bits(1), bits(1), bits(5), bits(1), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_pac_autdb_dp_1src_decode (sf, S, opcode2, Z, Rn, Rd) = {
  __unconditional = true;
  source_is_sp : bool = false;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  if ~(HavePACExt()) then UnallocatedEncoding() else ();
  if Z == 0b0 then if n == 31 then source_is_sp = true else () else if n != 31 then UnallocatedEncoding() else ();
  aarch64_integer_pac_autdb_dp_1src(d, n, source_is_sp)
}

val integer_pac_autda_dp_1src_decode : (bits(1), bits(1), bits(5), bits(1), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_pac_autda_dp_1src_decode (sf, S, opcode2, Z, Rn, Rd) = {
  __unconditional = true;
  source_is_sp : bool = false;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  if ~(HavePACExt()) then UnallocatedEncoding() else ();
  if Z == 0b0 then if n == 31 then source_is_sp = true else () else if n != 31 then UnallocatedEncoding() else ();
  aarch64_integer_pac_autda_dp_1src(d, n, source_is_sp)
}

val integer_insext_insert_movewide_decode : (bits(1), bits(2), bits(2), bits(16), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_insext_insert_movewide_decode (sf, opc, hw, imm16, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  let 'datasize : {|64, 32|} = if sf == 0b1 then 64 else 32;
  imm : bits(16) = imm16;
  pos : int = undefined;
  opcode : MoveWideOp = undefined;
  match opc {
    0b00 => opcode = MoveWideOp_N,
    0b10 => opcode = MoveWideOp_Z,
    0b11 => opcode = MoveWideOp_K,
    _ => UnallocatedEncoding()
  };
  if sf == 0b0 & [hw[1]] == 0b1 then UnallocatedEncoding() else ();
  pos = UInt(hw @ 0x0);
  aarch64_integer_insext_insert_movewide(d, datasize, imm, opcode, pos)
}

val integer_crc_decode : (bits(1), bits(1), bits(1), bits(5), bits(3), bits(1), bits(2), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_crc_decode (sf, op, S, Rm, opcode2, C, sz, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  if sf == 0b1 & sz != 0b11 then UnallocatedEncoding() else ();
  if sf == 0b0 & sz == 0b11 then UnallocatedEncoding() else ();
  size : int = shl_int(8, UInt(sz));
  crc32c : bool = C == 0b1;
  aarch64_integer_crc(crc32c, d, m, n, size)
}

val integer_arithmetic_rev_decode : (bits(1), bits(1), bits(5), bits(2), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_arithmetic_rev_decode (sf, S, opcode2, opc, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  let 'datasize : {|64, 32|} = if sf == 0b1 then 64 else 32;
  container_size : int = undefined;
  match opc {
    0b00 => Unreachable(),
    0b01 => container_size = 16,
    0b10 => container_size = 32,
    0b11 => {
      if sf == 0b0 then UnallocatedEncoding() else ();
      container_size = 64
    }
  };
  aarch64_integer_arithmetic_rev(container_size, d, datasize, n)
}

val float_move_fp_select_decode : (bits(1), bits(1), bits(2), bits(5), bits(4), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function float_move_fp_select_decode (M, S, typ, Rm, cond, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  datasize : int = undefined;
  match typ {
    0b00 => datasize = 32,
    0b01 => datasize = 64,
    0b10 => UnallocatedEncoding(),
    0b11 => if HaveFP16Ext() then datasize = 16 else UnallocatedEncoding()
  };
  condition : bits(4) = cond;
  aarch64_float_move_fp_select(condition, d, datasize, m, n)
}

val float_move_fp_imm_decode : (bits(1), bits(1), bits(2), bits(8), bits(5), bits(5)) -> unit effect {escape, undef, rreg, wreg}

function float_move_fp_imm_decode (M, S, typ, imm8, imm5, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  datasize : int = undefined;
  match typ {
    0b00 => datasize = 32,
    0b01 => datasize = 64,
    0b10 => UnallocatedEncoding(),
    0b11 => if HaveFP16Ext() then datasize = 16
    else UnallocatedEncoding()
  };
  let 'datasize2 = ex_int(datasize);
  assert(constraint('datasize2 in {16, 32, 64}));
  imm : bits('datasize2) = VFPExpandImm(imm8);
  aarch64_float_move_fp_imm(d, datasize2, imm)
}

val aarch64_float_convert_int_split :
  (int, int, int, int, FPConvOp, int, FPRounding, bool) -> unit effect {undef, escape, wreg, rreg}

function aarch64_float_convert_int_split (d, fltsize, intsize, n, op, part, rounding, unsigned) = {
  let fltsize : {|16,32,64,128|} = match fltsize { 16 => 16,  32 => 32,  64 => 64,  128 => 128 } in
  let intsize : {|32,64|} = match intsize { 32 => 32,  64 => 64 } in
  aarch64_float_convert_int (d, fltsize, intsize, n, op, part, rounding, unsigned);
}

val float_convert_int_decode : (bits(1), bits(1), bits(2), bits(2), bits(3), bits(5), bits(5)) -> unit effect {escape, undef, rreg, wreg}

function float_convert_int_decode (sf, S, typ, rmode, opcode, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  let 'intsize : {|32, 64|} = if sf == 0b1 then 64 else 32;
  fltsize : int = undefined;
  op : FPConvOp = undefined;
  rounding : FPRounding = undefined;
  unsigned : bool = undefined;
  part : int = undefined;
  match typ {
    0b00 => fltsize = 32,
    0b01 => fltsize = 64,
    0b10 => {
      if (slice(opcode, 1, 2) @ rmode) != 0xD then UnallocatedEncoding() else ();
      fltsize = 128
    },
    0b11 => if HaveFP16Ext() then fltsize = 16
    else UnallocatedEncoding()
  };
  match slice(opcode, 1, 2) @ rmode {
    [bitzero] @ [bitzero] @ _ : bits(1) @ _ : bits(1) => {
      rounding = FPDecodeRounding(rmode);
      unsigned = [opcode[0]] == 0b1;
      op = FPConvOp_CVT_FtoI
    },
    0x4 => {
      rounding = FPRoundingMode(FPCR);
      unsigned = [opcode[0]] == 0b1;
      op = FPConvOp_CVT_ItoF
    },
    0x8 => {
      rounding = FPRounding_TIEAWAY;
      unsigned = [opcode[0]] == 0b1;
      op = FPConvOp_CVT_FtoI
    },
    0xC => {
      if fltsize != 16 & fltsize != intsize then UnallocatedEncoding() else ();
      op = if [opcode[0]] == 0b1 then FPConvOp_MOV_ItoF else FPConvOp_MOV_FtoI;
      part = 0
    },
    0xD => {
      if intsize : int != 64 | fltsize != 128 then UnallocatedEncoding() else ();
      op = if [opcode[0]] == 0b1 then FPConvOp_MOV_ItoF else FPConvOp_MOV_FtoI;
      part = 1;
      fltsize = 64
    },
    0xF => {
      if ~(HaveFJCVTZSExt()) then UnallocatedEncoding() else ();
      rounding = FPRounding_ZERO;
      unsigned = [opcode[0]] == 0b1;
      op = FPConvOp_CVT_FtoI_JS
    },
    _ => UnallocatedEncoding()
  };
  let 'fltsize2 = ex_int(fltsize);
  assert(constraint('fltsize2 >= 0));
  aarch64_float_convert_int_split(d, fltsize2, intsize, n, op, part, rounding, unsigned)
}

val float_convert_fp_decode : (bits(1), bits(1), bits(2), bits(2), bits(5), bits(5)) -> unit effect {escape, undef, rreg, wreg}

function float_convert_fp_decode (M, S, typ, opc, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  if typ == opc then UnallocatedEncoding() else ();
  srcsize : int = undefined;
  match typ {
    0b00 => srcsize = 32,
    0b01 => srcsize = 64,
    0b10 => UnallocatedEncoding(),
    0b11 => srcsize = 16
  };
  dstsize : int = undefined;
  match opc {
    0b00 => dstsize = 32,
    0b01 => dstsize = 64,
    0b10 => UnallocatedEncoding(),
    0b11 => dstsize = 16
  };
  let 'dstsize2 = ex_int(dstsize) in let 'srcsize2 = ex_int(srcsize) in {
    assert(constraint('srcsize2 >= 0 & 'dstsize2 >= 0));
    aarch64_float_convert_fp(d, dstsize2, n, srcsize2)
  }
}

val float_convert_fix_decode : (bits(1), bits(1), bits(2), bits(2), bits(3), bits(6), bits(5), bits(5)) -> unit effect {escape, undef, rreg, wreg}

function float_convert_fix_decode (sf, S, typ, rmode, opcode, scale, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  intsize : int = if sf == 0b1 then 64 else 32;
  fltsize : int = undefined;
  op : FPConvOp = undefined;
  rounding : FPRounding = undefined;
  unsigned : bool = undefined;
  match typ {
    0b00 => fltsize = 32,
    0b01 => fltsize = 64,
    0b10 => UnallocatedEncoding(),
    0b11 => if HaveFP16Ext() then fltsize = 16
    else UnallocatedEncoding()
  };
  if sf == 0b0 & [scale[5]] == 0b0 then UnallocatedEncoding() else ();
  fracbits : int = 64 - UInt(scale);
  match slice(opcode, 1, 2) @ rmode {
    0x3 => {
      rounding = FPRounding_ZERO;
      unsigned = [opcode[0]] == 0b1;
      op = FPConvOp_CVT_FtoI
    },
    0x4 => {
      rounding = FPRoundingMode(FPCR);
      unsigned = [opcode[0]] == 0b1;
      op = FPConvOp_CVT_ItoF
    },
    _ => UnallocatedEncoding()
  };
  let 'fltsize2 = ex_int(fltsize) in let 'intsize2 = ex_int(intsize) in {
    assert(constraint('fltsize2 >= 0 & 'intsize2 >= 0));
    aarch64_float_convert_fix(d, fltsize2, fracbits, intsize2, n, op, rounding, unsigned)
  }
}

val float_compare_uncond_decode : (bits(1), bits(1), bits(2), bits(5), bits(2), bits(5), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function float_compare_uncond_decode (M, S, typ, Rm, op, Rn, opc) = {
  __unconditional = true;
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  datasize : int = undefined;
  match typ {
    0b00 => datasize = 32,
    0b01 => datasize = 64,
    0b10 => UnallocatedEncoding(),
    0b11 => if HaveFP16Ext() then datasize = 16 else UnallocatedEncoding()
  };
  signal_all_nans : bool = [opc[1]] == 0b1;
  cmp_with_zero : bool = [opc[0]] == 0b1;
  aarch64_float_compare_uncond(cmp_with_zero, datasize, m, n, signal_all_nans)
}

val float_compare_cond_decode : (bits(1), bits(1), bits(2), bits(5), bits(4), bits(5), bits(1), bits(4)) -> unit effect {escape, rreg, undef, wreg}

function float_compare_cond_decode (M, S, typ, Rm, cond, Rn, op, nzcv) = {
  __unconditional = true;
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  datasize : int = undefined;
  match typ {
    0b00 => datasize = 32,
    0b01 => datasize = 64,
    0b10 => UnallocatedEncoding(),
    0b11 => if HaveFP16Ext() then datasize = 16 else UnallocatedEncoding()
  };
  signal_all_nans : bool = op == 0b1;
  condition : bits(4) = cond;
  flags : bits(4) = nzcv;
  aarch64_float_compare_cond(condition, datasize, flags, m, n, signal_all_nans)
}

val float_arithmetic_unary_decode : (bits(1), bits(1), bits(2), bits(2), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_unary_decode (M, S, typ, opc, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  datasize : int = undefined;
  match typ {
    0b00 => datasize = 32,
    0b01 => datasize = 64,
    0b10 => UnallocatedEncoding(),
    0b11 => if HaveFP16Ext() then datasize = 16 else UnallocatedEncoding()
  };
  fpop : FPUnaryOp = undefined;
  match opc {
    0b00 => fpop = FPUnaryOp_MOV,
    0b01 => fpop = FPUnaryOp_ABS,
    0b10 => fpop = FPUnaryOp_NEG,
    0b11 => fpop = FPUnaryOp_SQRT
  };
  aarch64_float_arithmetic_unary(d, datasize, fpop, n)
}

val float_arithmetic_round_decode : (bits(1), bits(1), bits(2), bits(3), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_round_decode (M, S, typ, rmode, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  datasize : int = undefined;
  match typ {
    0b00 => datasize = 32,
    0b01 => datasize = 64,
    0b10 => UnallocatedEncoding(),
    0b11 => if HaveFP16Ext() then datasize = 16 else UnallocatedEncoding()
  };
  exact : bool = false;
  rounding : FPRounding = undefined;
  match rmode {
    [bitzero] @ _ : bits(1) @ _ : bits(1) => rounding = FPDecodeRounding(slice(rmode, 0, 2)),
    0b100 => rounding = FPRounding_TIEAWAY,
    0b101 => UnallocatedEncoding(),
    0b110 => {
      rounding = FPRoundingMode(FPCR);
      exact = true
    },
    0b111 => rounding = FPRoundingMode(FPCR)
  };
  aarch64_float_arithmetic_round(d, datasize, exact, n, rounding)
}

val float_arithmetic_mul_product_decode : (bits(1), bits(1), bits(2), bits(5), bits(1), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_mul_product_decode (M, S, typ, Rm, op, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  datasize : int = undefined;
  match typ {
    0b00 => datasize = 32,
    0b01 => datasize = 64,
    0b10 => UnallocatedEncoding(),
    0b11 => if HaveFP16Ext() then datasize = 16 else UnallocatedEncoding()
  };
  negated : bool = op == 0b1;
  aarch64_float_arithmetic_mul_product(d, datasize, m, n, negated)
}

val float_arithmetic_mul_addsub_decode : (bits(1), bits(1), bits(2), bits(1), bits(5), bits(1), bits(5), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_mul_addsub_decode (M, S, typ, o1, Rm, o0, Ra, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  a : int = UInt(Ra);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  datasize : int = undefined;
  match typ {
    0b00 => datasize = 32,
    0b01 => datasize = 64,
    0b10 => UnallocatedEncoding(),
    0b11 => if HaveFP16Ext() then datasize = 16 else UnallocatedEncoding()
  };
  opa_neg : bool = o1 == 0b1;
  op1_neg : bool = o0 != o1;
  aarch64_float_arithmetic_mul_addsub(a, d, datasize, m, n, op1_neg, opa_neg)
}

val float_arithmetic_maxmin_decode : (bits(1), bits(1), bits(2), bits(5), bits(2), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_maxmin_decode (M, S, typ, Rm, op, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  datasize : int = undefined;
  match typ {
    0b00 => datasize = 32,
    0b01 => datasize = 64,
    0b10 => UnallocatedEncoding(),
    0b11 => if HaveFP16Ext() then datasize = 16 else UnallocatedEncoding()
  };
  operation : FPMaxMinOp = undefined;
  match op {
    0b00 => operation = FPMaxMinOp_MAX,
    0b01 => operation = FPMaxMinOp_MIN,
    0b10 => operation = FPMaxMinOp_MAXNUM,
    0b11 => operation = FPMaxMinOp_MINNUM
  };
  aarch64_float_arithmetic_maxmin(d, datasize, m, n, operation)
}

val float_arithmetic_div_decode : (bits(1), bits(1), bits(2), bits(5), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_div_decode (M, S, typ, Rm, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  datasize : int = undefined;
  match typ {
    0b00 => datasize = 32,
    0b01 => datasize = 64,
    0b10 => UnallocatedEncoding(),
    0b11 => if HaveFP16Ext() then datasize = 16 else UnallocatedEncoding()
  };
  aarch64_float_arithmetic_div(d, datasize, m, n)
}

val float_arithmetic_addsub_decode : (bits(1), bits(1), bits(2), bits(5), bits(1), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function float_arithmetic_addsub_decode (M, S, typ, Rm, op, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  datasize : int = undefined;
  match typ {
    0b00 => datasize = 32,
    0b01 => datasize = 64,
    0b10 => UnallocatedEncoding(),
    0b11 => if HaveFP16Ext() then datasize = 16 else UnallocatedEncoding()
  };
  sub_op : bool = op == 0b1;
  aarch64_float_arithmetic_addsub(d, datasize, m, n, sub_op)
}

val branch_unconditional_register_decode : (bits(1), bits(1), bits(2), bits(5), bits(4), bits(1), bits(1), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function branch_unconditional_register_decode (Z, opc, op, op2, op3, A, M, Rn, Rm) = {
  __unconditional = true;
  n : int = UInt(Rn);
  branch_type : BranchType = undefined;
  m : int = UInt(Rm);
  pac : bool = A == 0b1;
  use_key_a : bool = M == 0b0;
  source_is_sp : bool = Z == 0b1 & m == 31;
  if ~(pac) & m != 0 then UnallocatedEncoding() else if pac & ~(HavePACExt()) then UnallocatedEncoding() else ();
  match op {
    0b00 => branch_type = BranchType_JMP,
    0b01 => branch_type = BranchType_CALL,
    0b10 => branch_type = BranchType_RET,
    _ => UnallocatedEncoding()
  };
  if pac then {
    if Z == 0b0 & m != 31 then UnallocatedEncoding() else ();
    if branch_type == BranchType_RET then {
      if n != 31 then UnallocatedEncoding() else ();
      n = 30;
      source_is_sp = true
    } else ()
  } else ();
  aarch64_branch_unconditional_register(branch_type, m, n, pac, source_is_sp, use_key_a)
}

val branch_unconditional_eret_decode : (bits(4), bits(5), bits(4), bits(1), bits(1), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function branch_unconditional_eret_decode (opc, op2, op3, A, M, Rn, op4) = {
  __unconditional = true;
  if PSTATE.EL == EL0 then UnallocatedEncoding() else ();
  pac : bool = A == 0b1;
  use_key_a : bool = M == 0b0;
  if ~(pac) & op4 != 0b00000 then UnallocatedEncoding() else if pac & (~(HavePACExt()) | op4 != 0b11111) then UnallocatedEncoding() else ();
  if Rn != 0b11111 then UnallocatedEncoding() else ();
  aarch64_branch_unconditional_eret(pac, use_key_a)
}

val branch_unconditional_dret_decode : (bits(4), bits(5), bits(6), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function branch_unconditional_dret_decode (opc, op2, op3, Rt, op4) = {
  __unconditional = true;
  if ~(Halted()) | PSTATE.EL == EL0 then UnallocatedEncoding() else ();
  aarch64_branch_unconditional_dret()
}

val AArch64_CheckSystemAccess : (bits(2), bits(3), bits(4), bits(4), bits(3), bits(5), bits(1)) -> unit effect {escape, undef, rreg, wreg}

function AArch64_CheckSystemAccess (op0, op1, crn, crm, op2, rt, read) = {
  unallocated : bool = false;
  need_secure : bool = false;
  min_EL : bits(2) = undefined;
  rcs_el0_trap : bool = undefined;
  if (((HaveEL(EL2) & ~(IsSecure())) & [HCR_EL2[20]] == 0b1) & (op0 & 0b01) == 0b01) & (crn & 0xB) == 0xB then {
    rcs_el0_trap = undefined;
    if PSTATE.EL == EL0 & rcs_el0_trap then AArch64_SystemRegisterTrap(EL2, op0, op2, op1, crn, rt, crm, read) else if PSTATE.EL == EL1 then AArch64_SystemRegisterTrap(EL2, op0, op2, op1, crn, rt, crm, read) else ()
  } else ();
  match op1 {
    [bitzero] @ [bitzero] @ _ : bits(1) => min_EL = EL1,
    0b010 => min_EL = EL1,
    0b011 => min_EL = EL0,
    0b100 => min_EL = EL2,
    0b101 => {
      if ~(HaveVirtHostExt()) then UnallocatedEncoding() else ();
      min_EL = EL2
    },
    0b110 => min_EL = EL3,
    0b111 => {
      min_EL = EL1;
      need_secure = true
    }
  };
  if UInt(PSTATE.EL) < UInt(min_EL) then
    if ((((PSTATE.EL == EL1 & min_EL == EL2) & HaveNVExt()) & ~(IsSecure())) & HaveEL(EL2)) & [HCR_EL2[42]] == 0b1 then AArch64_SystemRegisterTrap(EL2, op0, op2, op1, crn, rt, crm, read) else UnallocatedEncoding()
  else if need_secure & ~(IsSecure()) then UnallocatedEncoding() else if AArch64_CheckUnallocatedSystemAccess(op0, op1, crn, crm, op2, read) then UnallocatedEncoding() else ();
  target_el : bits(2) = undefined;
  take_trap : bool = undefined;
  (take_trap, target_el) = AArch64_CheckAdvSIMDFPSystemRegisterTraps(op0, op1, crn, crm, op2, read);
  if take_trap then AArch64_AdvSIMDFPAccessTrap(target_el) else ();
  (take_trap, target_el) = AArch64_CheckSystemRegisterTraps(op0, op1, crn, crm, op2, read);
  if take_trap then AArch64_SystemRegisterTrap(target_el, op0, op2, op1, crn, rt, crm, read) else ()
}

val system_sysops_decode : (bits(1), bits(2), bits(3), bits(4), bits(4), bits(3), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function system_sysops_decode (L, op0, op1, CRn, CRm, op2, Rt) = {
  __unconditional = true;
  AArch64_CheckSystemAccess(0b01, op1, CRn, CRm, op2, Rt, L);
  t : int = UInt(Rt);
  sys_op0 : int = 1;
  sys_op1 : int = UInt(op1);
  sys_op2 : int = UInt(op2);
  sys_crn : int = UInt(CRn);
  sys_crm : int = UInt(CRm);
  has_result : bool = L == 0b1;
  aarch64_system_sysops(has_result, sys_crm, sys_crn, sys_op0, sys_op1, sys_op2, t)
}

val system_register_system_decode : (bits(1), bits(1), bits(3), bits(4), bits(4), bits(3), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function system_register_system_decode (L, o0, op1, CRn, CRm, op2, Rt) = {
  __unconditional = true;
  AArch64_CheckSystemAccess(0b1 @ o0, op1, CRn, CRm, op2, Rt, L);
  t : int = UInt(Rt);
  sys_op0 : int = 2 + UInt(o0);
  sys_op1 : int = UInt(op1);
  sys_op2 : int = UInt(op2);
  sys_crn : int = UInt(CRn);
  sys_crm : int = UInt(CRm);
  read : bool = L == 0b1;
  aarch64_system_register_system(read, sys_crm, sys_crn, sys_op0, sys_op1, sys_op2, t)
}

val system_register_cpsr_decode : (bits(1), bits(2), bits(3), bits(4), bits(4), bits(3), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function system_register_cpsr_decode (L, op0, op1, CRn, CRm, op2, Rt) = {
  __unconditional = true;
  AArch64_CheckSystemAccess(0b00, op1, 0x4, CRm, op2, 0b11111, 0b0);
  operand : bits(4) = CRm;
  field : PSTATEField = undefined;
  match op1 @ op2 {
    0b000011 => {
      if ~(HaveUAOExt()) then UnallocatedEncoding() else ();
      field = PSTATEField_UAO
    },
    0b000100 => {
      if ~(HavePANExt()) then UnallocatedEncoding() else ();
      field = PSTATEField_PAN
    },
    0b000101 => field = PSTATEField_SP,
    0b011110 => field = PSTATEField_DAIFSet,
    0b011111 => field = PSTATEField_DAIFClr,
    _ => UnallocatedEncoding()
  };
  if (op1 == 0b011 & PSTATE.EL == EL0) & (IsInHost() | [SCTLR_EL1[9]] == 0b0) then AArch64_SystemRegisterTrap(EL1, 0b00, op2, op1, 0x4, 0b11111, CRm, 0b0) else ();
  aarch64_system_register_cpsr(field, operand)
}

val AArch64_CheckForSMCUndefOrTrap : bits(16) -> unit effect {escape, rreg, undef, wreg}

function AArch64_CheckForSMCUndefOrTrap imm = {
  if PSTATE.EL == EL0 then UnallocatedEncoding() else ();
  route_to_el2 : bool = undefined;
  if ~(HaveEL(EL3)) then if (HaveEL(EL2) & ~(IsSecure())) & PSTATE.EL == EL1 then if (HaveNVExt() & [HCR_EL2[42]] == 0b1) & [HCR_EL2[19]] == 0b1 then route_to_el2 = true else UnallocatedEncoding() else UnallocatedEncoding() else route_to_el2 = ((HaveEL(EL2) & ~(IsSecure())) & PSTATE.EL == EL1) & [HCR_EL2[19]] == 0b1;
  exception : ExceptionRecord = undefined;
  vect_offset : int = undefined;
  if route_to_el2 then {
    preferred_exception_return : bits(64) = ThisInstrAddr();
    vect_offset = 0;
    exception = ExceptionSyndrome(Exception_MonitorCall);
    __tmp_4 : bits(25) = exception.syndrome;
    __tmp_4 = __SetSlice_bits(25, 16, __tmp_4, 0, imm);
    exception.syndrome = __tmp_4;
    AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset)
  } else ()
}

val aarch64_system_exceptions_runtime_smc : bits(16) -> unit effect {escape, rreg, undef, wreg}

function aarch64_system_exceptions_runtime_smc imm = {
  AArch64_CheckForSMCUndefOrTrap(imm);
  if [SCR_EL3[7]] == 0b1 then AArch64_UndefinedFault() else AArch64_CallSecureMonitor(imm)
}

val system_exceptions_runtime_smc_decode : (bits(3), bits(16), bits(3), bits(2)) -> unit effect {escape, rreg, undef, wreg}

function system_exceptions_runtime_smc_decode (opc, imm16, op2, LL) = {
  __unconditional = true;
  imm : bits(16) = imm16;
  aarch64_system_exceptions_runtime_smc(imm)
}

val ReservedValue : unit -> unit effect {escape, rreg, undef, wreg}

function ReservedValue () = if UsingAArch32() & ~(AArch32_GeneralExceptionsToAArch64()) then AArch32_TakeUndefInstrException() else AArch64_UndefinedFault()

val memory_vector_multiple_postinc_aarch64_memory_vector_multiple_nowb__decode : (bits(1), bits(1), bits(5), bits(4), bits(2), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_vector_multiple_postinc_aarch64_memory_vector_multiple_nowb__decode (Q, L, Rm, opcode, size, Rn, Rt) = {
  __unconditional = true;
  t : int = UInt(Rt);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  wback : bool = true;
  memop : MemOp = if L == 0b1 then MemOp_LOAD else MemOp_STORE;
  let 'datasize : {|128, 64|} = if Q == 0b1 then 128 else 64;
  esize : int = shl_int(8, UInt(size));
  elements : int = datasize / esize;
  rpt : int = undefined;
  selem : int = undefined;
  match opcode {
    0x0 => {
      rpt = 1;
      selem = 4
    },
    0x2 => {
      rpt = 4;
      selem = 1
    },
    0x4 => {
      rpt = 1;
      selem = 3
    },
    0x6 => {
      rpt = 3;
      selem = 1
    },
    0x7 => {
      rpt = 1;
      selem = 1
    },
    0x8 => {
      rpt = 1;
      selem = 2
    },
    0xA => {
      rpt = 2;
      selem = 1
    },
    _ => UnallocatedEncoding()
  };
  if (size @ Q) == 0b110 & selem != 1 then ReservedValue() else ();
  aarch64_memory_vector_multiple_nowb(datasize, elements, esize, m, memop, n, rpt, selem, t, wback)
}

val memory_vector_multiple_nowb_aarch64_memory_vector_multiple_nowb__decode : (bits(1), bits(1), bits(4), bits(2), bits(5), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_vector_multiple_nowb_aarch64_memory_vector_multiple_nowb__decode (Q, L, opcode, size, Rn, Rt) = {
  __unconditional = true;
  t : int = UInt(Rt);
  n : int = UInt(Rn);
  m : int = undefined;
  wback : bool = false;
  memop : MemOp = if L == 0b1 then MemOp_LOAD else MemOp_STORE;
  let 'datasize : {|128, 64|} = if Q == 0b1 then 128 else 64;
  esize : int = shl_int(8, UInt(size));
  elements : int = datasize / esize;
  rpt : int = undefined;
  selem : int = undefined;
  match opcode {
    0x0 => {
      rpt = 1;
      selem = 4
    },
    0x2 => {
      rpt = 4;
      selem = 1
    },
    0x4 => {
      rpt = 1;
      selem = 3
    },
    0x6 => {
      rpt = 3;
      selem = 1
    },
    0x7 => {
      rpt = 1;
      selem = 1
    },
    0x8 => {
      rpt = 1;
      selem = 2
    },
    0xA => {
      rpt = 2;
      selem = 1
    },
    _ => UnallocatedEncoding()
  };
  if (size @ Q) == 0b110 & selem != 1 then ReservedValue() else ();
  aarch64_memory_vector_multiple_nowb(datasize, elements, esize, m, memop, n, rpt, selem, t, wback)
}

val integer_logical_shiftedreg_decode : (bits(1), bits(2), bits(2), bits(1), bits(5), bits(6), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_logical_shiftedreg_decode (sf, opc, shift, N, Rm, imm6, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  let 'datasize : {|64, 32|} = if sf == 0b1 then 64 else 32;
  setflags : bool = undefined;
  op : LogicalOp = undefined;
  match opc {
    0b00 => {
      op = LogicalOp_AND;
      setflags = false
    },
    0b01 => {
      op = LogicalOp_ORR;
      setflags = false
    },
    0b10 => {
      op = LogicalOp_EOR;
      setflags = false
    },
    0b11 => {
      op = LogicalOp_AND;
      setflags = true
    }
  };
  if sf == 0b0 & [imm6[5]] == 0b1 then ReservedValue() else ();
  shift_type : ShiftType = DecodeShift(shift);
  shift_amount : int = UInt(imm6);
  invert : bool = N == 0b1;
  aarch64_integer_logical_shiftedreg(d, datasize, invert, m, n, op, setflags, shift_amount, shift_type)
}

val integer_insext_extract_immediate_decode : (bits(1), bits(2), bits(1), bits(1), bits(5), bits(6), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_insext_extract_immediate_decode (sf, op21, N, o0, Rm, imms, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  let 'datasize : {|64, 32|} = if sf == 0b1 then 64 else 32;
  lsb : int = undefined;
  if N != sf then UnallocatedEncoding() else ();
  if sf == 0b0 & [imms[5]] == 0b1 then ReservedValue() else ();
  lsb = UInt(imms);
  aarch64_integer_insext_extract_immediate(d, datasize, lsb, m, n)
}

val integer_arithmetic_addsub_shiftedreg_decode : (bits(1), bits(1), bits(1), bits(2), bits(5), bits(6), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_arithmetic_addsub_shiftedreg_decode (sf, op, S, shift, Rm, imm6, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  let 'datasize : {|64, 32|} = if sf == 0b1 then 64 else 32;
  sub_op : bool = op == 0b1;
  setflags : bool = S == 0b1;
  if shift == 0b11 then ReservedValue() else ();
  if sf == 0b0 & [imm6[5]] == 0b1 then ReservedValue() else ();
  shift_type : ShiftType = DecodeShift(shift);
  shift_amount : int = UInt(imm6);
  aarch64_integer_arithmetic_addsub_shiftedreg(d, datasize, m, n, setflags, shift_amount, shift_type, sub_op)
}

val integer_arithmetic_addsub_immediate_decode : (bits(1), bits(1), bits(1), bits(2), bits(12), bits(5), bits(5)) -> unit effect {escape, undef, rreg, wreg}

function integer_arithmetic_addsub_immediate_decode (sf, op, S, shift, imm12, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  let 'datasize : {|64, 32|} = if sf == 0b1 then 64 else 32;
  sub_op : bool = op == 0b1;
  setflags : bool = S == 0b1;
  imm : bits('datasize) = undefined;
  match shift {
    0b00 => imm = ZeroExtend(imm12, datasize),
    0b01 => imm = ZeroExtend(imm12 @ Zeros(12), datasize),
    [bitone] @ _ : bits(1) => ReservedValue()
  };
  aarch64_integer_arithmetic_addsub_immediate(d, datasize, imm, n, setflags, sub_op)
}

val integer_arithmetic_addsub_extendedreg_decode : (bits(1), bits(1), bits(1), bits(2), bits(5), bits(3), bits(3), bits(5), bits(5)) -> unit effect {escape, rreg, undef, wreg}

function integer_arithmetic_addsub_extendedreg_decode (sf, op, S, opt, Rm, option_name, imm3, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  m : int = UInt(Rm);
  let 'datasize : {|64, 32|} = if sf == 0b1 then 64 else 32;
  sub_op : bool = op == 0b1;
  setflags : bool = S == 0b1;
  extend_type : ExtendType = DecodeRegExtend(option_name);
  shift : int = UInt(imm3);
  if shift > 4 then ReservedValue() else ();
  aarch64_integer_arithmetic_addsub_extendedreg(d, datasize, extend_type, m, n, setflags, shift, sub_op)
}

val DecodeBitMasks : forall ('M : Int), 1 >= 0 & 6 >= 0 & 6 >= 0 & 'M >= 0 & 'M >= 0.
  (bits(1), bits(6), bits(6), bool) -> (bits('M), bits('M)) effect {escape, rreg, undef, wreg}

function DecodeBitMasks (immN, imms, immr, immediate) = {
  tmask : bits(64) = undefined;
  wmask : bits(64) = undefined;
  tmask_and : bits(6) = undefined;
  wmask_and : bits(6) = undefined;
  tmask_or : bits(6) = undefined;
  wmask_or : bits(6) = undefined;
  levels : bits(6) = undefined;
  let 'len = HighestSetBit(immN @ ~(imms));
  assert('len >= 0);
  if len < 1 then ReservedValue() else ();
  assert('M >= shl_int(1, len), "(M >= (1 << len))");
  levels = ZeroExtend(Ones(len), 6);
  if immediate & (imms & levels) == levels then ReservedValue() else ();
  S : int = UInt(imms & levels);
  R : int = UInt(immr & levels);
  diff : int = S - R;
  tmask_and = __GetSlice_int(6, diff, 0) | ~(levels);
  tmask_or = __GetSlice_int(6, diff, 0) & levels;
  tmask = Ones(64);
  tmask = tmask & replicate_bits(replicate_bits([tmask_and[0]], 1) @ Ones(1), 32) | replicate_bits(Zeros(1) @ replicate_bits([tmask_or[0]], 1), 32);
  tmask = tmask & replicate_bits(replicate_bits([tmask_and[1]], 2) @ Ones(2), 16) | replicate_bits(Zeros(2) @ replicate_bits([tmask_or[1]], 2), 16);
  tmask = tmask & replicate_bits(replicate_bits([tmask_and[2]], 4) @ Ones(4), 8) | replicate_bits(Zeros(4) @ replicate_bits([tmask_or[2]], 4), 8);
  tmask = tmask & replicate_bits(replicate_bits([tmask_and[3]], 8) @ Ones(8), 4) | replicate_bits(Zeros(8) @ replicate_bits([tmask_or[3]], 8), 4);
  tmask = tmask & replicate_bits(replicate_bits([tmask_and[4]], 16) @ Ones(16), 2) | replicate_bits(Zeros(16) @ replicate_bits([tmask_or[4]], 16), 2);
  tmask = tmask & replicate_bits(replicate_bits([tmask_and[5]], 32) @ Ones(32), 1) | replicate_bits(Zeros(32) @ replicate_bits([tmask_or[5]], 32), 1);
  wmask_and = immr | ~(levels);
  wmask_or = immr & levels;
  wmask = Zeros(64);
  wmask = wmask & replicate_bits(Ones(1) @ replicate_bits([wmask_and[0]], 1), 32) | replicate_bits(replicate_bits([wmask_or[0]], 1) @ Zeros(1), 32);
  wmask = wmask & replicate_bits(Ones(2) @ replicate_bits([wmask_and[1]], 2), 16) | replicate_bits(replicate_bits([wmask_or[1]], 2) @ Zeros(2), 16);
  wmask = wmask & replicate_bits(Ones(4) @ replicate_bits([wmask_and[2]], 4), 8) | replicate_bits(replicate_bits([wmask_or[2]], 4) @ Zeros(4), 8);
  wmask = wmask & replicate_bits(Ones(8) @ replicate_bits([wmask_and[3]], 8), 4) | replicate_bits(replicate_bits([wmask_or[3]], 8) @ Zeros(8), 4);
  wmask = wmask & replicate_bits(Ones(16) @ replicate_bits([wmask_and[4]], 16), 2) | replicate_bits(replicate_bits([wmask_or[4]], 16) @ Zeros(16), 2);
  wmask = wmask & replicate_bits(Ones(32) @ replicate_bits([wmask_and[5]], 32), 1) | replicate_bits(replicate_bits([wmask_or[5]], 32) @ Zeros(32), 1);
  if __GetSlice_int(1, diff, 6) != 0b0 then wmask = wmask & tmask
  else wmask = wmask | tmask;
  return((slice(wmask, 0, 'M), slice(tmask, 0, 'M)))
}

val integer_logical_immediate_decode : (bits(1), bits(2), bits(1), bits(6), bits(6), bits(5), bits(5)) -> unit effect {escape, undef, rreg, wreg}

function integer_logical_immediate_decode (sf, opc, N, immr, imms, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  let 'datasize : {|64, 32|} = if sf == 0b1 then 64 else 32;
  setflags : bool = undefined;
  op : LogicalOp = undefined;
  match opc {
    0b00 => {
      op = LogicalOp_AND;
      setflags = false
    },
    0b01 => {
      op = LogicalOp_ORR;
      setflags = false
    },
    0b10 => {
      op = LogicalOp_EOR;
      setflags = false
    },
    0b11 => {
      op = LogicalOp_AND;
      setflags = true
    }
  };
  imm : bits('datasize) = undefined;
  if sf == 0b0 & N != 0b0 then ReservedValue() else ();
  __anon1 : bits('datasize) = undefined;
  (imm, __anon1) = DecodeBitMasks(N, imms, immr, true) : (bits('datasize), bits('datasize));
  aarch64_integer_logical_immediate(d, datasize, imm, n, op, setflags)
}

val integer_bitfield_decode : (bits(1), bits(2), bits(1), bits(6), bits(6), bits(5), bits(5)) -> unit effect {escape, undef, rreg, wreg}

function integer_bitfield_decode (sf, opc, N, immr, imms, Rn, Rd) = {
  __unconditional = true;
  d : int = UInt(Rd);
  n : int = UInt(Rn);
  let 'datasize : {|64, 32|} = if sf == 0b1 then 64 else 32;
  inzero : bool = undefined;
  extend : bool = undefined;
  R : int = undefined;
  S : int = undefined;
  wmask : bits('datasize) = undefined;
  tmask : bits('datasize) = undefined;
  match opc {
    0b00 => {
      inzero = true;
      extend = true
    },
    0b01 => {
      inzero = false;
      extend = false
    },
    0b10 => {
      inzero = true;
      extend = false
    },
    0b11 => UnallocatedEncoding()
  };
  if sf == 0b1 & N != 0b1 then ReservedValue() else ();
  if sf == 0b0 & ((N != 0b0 | [immr[5]] != 0b0) | [imms[5]] != 0b0) then ReservedValue() else ();
  R = UInt(immr);
  S = UInt(imms);
  (wmask, tmask) = DecodeBitMasks(N, imms, immr, false) : (bits('datasize), bits('datasize));
  aarch64_integer_bitfield(R, S, d, datasize, extend, inzero, n, tmask, wmask)
}
