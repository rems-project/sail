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

val AArch64_SecondStageTranslate : (AddressDescriptor, bits(64), AccType, bool, bool, bool, int, bool) -> AddressDescriptor effect {rreg, escape, rmem, undef, wmem}

val AArch64_CheckAndUpdateDescriptor : (DescriptorUpdate, FaultRecord, bool, bits(64), AccType, bool, bool, bool) -> FaultRecord effect {escape, rreg, rmem, wmem, undef}

register __unconditional : bool

val __UNKNOWN_integer : unit -> int

function __UNKNOWN_integer () = return(0)

register __ThisInstrEnc : __InstrEnc

register __ThisInstr : bits(32)

register __Memory : bits(52)

register __BranchTaken : bool

register _R : vector(31, dec, bits(64))

register _PC : bits(64)

register VTTBR_EL2 : bits(64)

register VTCR_EL2 : bits(32)

register VBAR_EL3 : bits(64)

register VBAR_EL2 : bits(64)

register VBAR_EL1 : bits(64)

register VBAR : bits(32)

val ThisInstrAddr : forall ('N : Int), 'N >= 0. unit -> bits('N) effect {rreg}

function ThisInstrAddr () = return(slice(_PC, 0, 'N))

val ThisInstr : unit -> bits(32) effect {rreg}

function ThisInstr () = return(__ThisInstr)

register TTBR1_EL2 : bits(64)

register TTBR1_EL1 : bits(64)

register TTBR0_EL3 : bits(64)

register TTBR0_EL2 : bits(64)

register TTBR0_EL1 : bits(64)

register TCR_EL3 : bits(32)

register TCR_EL2 : bits(64)

register TCR_EL1 : bits(64)

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

register SCTLR_EL3 : bits(32)

register SCTLR_EL2 : bits(32)

register SCTLR_EL1 : bits(32)

register SCTLR : bits(32)

register SCR_EL3 : bits(32)

register SCR : bits(32)

val ProcessorID : unit -> int

function ProcessorID () = return(0)

val __UNKNOWN_PrefetchHint : unit -> PrefetchHint

function __UNKNOWN_PrefetchHint () = return(Prefetch_READ)

register PSTATE : ProcState

register OSLSR_EL1 : bits(32)

register OSDLR_EL1 : bits(32)

val __UNKNOWN_MemType : unit -> MemType

function __UNKNOWN_MemType () = return(MemType_Normal)

val __UNKNOWN_MemOp : unit -> MemOp

function __UNKNOWN_MemOp () = return(MemOp_LOAD)

let MemHint_RWA : vector(2, dec, bit) = 0b11

let MemHint_RA : vector(2, dec, bit) = 0b10

let MemHint_No : vector(2, dec, bit) = 0b00

let MemAttr_WT : vector(2, dec, bit) = 0b10

let MemAttr_WB : vector(2, dec, bit) = 0b11

let MemAttr_NC : vector(2, dec, bit) = 0b00

register MDSCR_EL1 : bits(32)

register MDCR_EL3 : bits(32)

register MDCR_EL2 : bits(32)

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

register LR_mon : bits(32)

val __UNKNOWN_InstrSet : unit -> InstrSet

function __UNKNOWN_InstrSet () = return(InstrSet_A64)

register ID_AA64DFR0_EL1 : bits(64)

val Hint_Prefetch : (bits(64), PrefetchHint, int, bool) -> unit

function Hint_Prefetch (address, hint, 'target, stream) = ()

val Hint_Branch : BranchType -> unit

function Hint_Branch hint = ()

val HaveAnyAArch32 : unit -> bool

function HaveAnyAArch32 () = return(false)

register HVBAR : bits(32)

register HSR : bits(32)

register HSCTLR : bits(32)

register HPFAR_EL2 : bits(64)

register HPFAR : bits(32)

register HIFAR : bits(32)

register HDFAR : bits(32)

register HCR_EL2 : bits(64)

register HCR2 : bits(32)

register HCR : bits(32)

val __UNKNOWN_Fault : unit -> Fault

function __UNKNOWN_Fault () = return(Fault_None)

register FPEXC : bits(32)

register FAR_EL3 : bits(64)

register FAR_EL2 : bits(64)

register FAR_EL1 : bits(64)

val __UNKNOWN_boolean : unit -> bool

function __UNKNOWN_boolean () = return(false)

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

val TakeUnmaskedPhysicalSErrorInterrupts : bool -> unit effect {escape}

function TakeUnmaskedPhysicalSErrorInterrupts iesb_req = assert(false, "FALSE")

val StopInstructionPrefetchAndEnableITR : unit -> unit effect {escape}

function StopInstructionPrefetchAndEnableITR () = assert(false, "FALSE")

val __UNKNOWN_Exception : unit -> Exception

function __UNKNOWN_Exception () = return(Exception_Uncategorized)

val ErrorSynchronizationBarrier : (MBReqDomain, MBReqTypes) -> unit

function ErrorSynchronizationBarrier (domain, types) = ()

val EndOfInstruction : unit -> unit

function EndOfInstruction () = ()

register ESR_EL3 : bits(32)

register ESR_EL2 : bits(32)

register ESR_EL1 : bits(32)

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

let DebugHalt_Watchpoint : vector(6, dec, bit) = 0b101011

let DebugHalt_Breakpoint : vector(6, dec, bit) = 0b000111

let DebugException_VectorCatch : vector(4, dec, bit) = 0x5

register DSPSR_EL0 : bits(32)

register DSPSR : bits(32)

register DLR_EL0 : bits(64)

register DLR : bits(32)

register DBGWVR_EL1 : vector(16, dec, bits(64))

register DBGWCR_EL1 : vector(16, dec, bits(32))

register DBGPRCR_EL1 : bits(32)

register DBGPRCR : bits(32)

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

val ClearExclusiveByAddress : (FullAddress, int, int) -> unit

function ClearExclusiveByAddress (paddress, 'processorid, 'size) = ()

val CTI_SignalEvent : CrossTriggerIn -> unit effect {escape}

function CTI_SignalEvent id = assert(false, "FALSE")

register CONTEXTIDR_EL2 : bits(32)

register CONTEXTIDR_EL1 : bits(32)

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

val PAMax : unit -> int

function PAMax () = return(__IMPDEF_integer("Maximum Physical Address Size"))

val __IMPDEF_boolean : string -> bool

function __IMPDEF_boolean x = {
  if x == "Condition valid for trapped T32" then return(true) else if x == "Has Dot Product extension" then return(true) else if x == "Has RAS extension" then return(true) else if x == "Has SHA512 and SHA3 Crypto instructions" then return(true) else if x == "Has SM3 and SM4 Crypto instructions" then return(true) else if x == "Has basic Crypto instructions" then return(true) else if x == "Have CRC extension" then return(true) else if x == "Report I-cache maintenance fault in IFSR" then return(true) else if x == "Reserved Control Space EL0 Trapped" then return(true) else if x == "Translation fault on misprogrammed contiguous bit" then return(true) else if x == "UNDEF unallocated CP15 access at NS EL0" then return(true) else if x == "UNDEF unallocated CP15 access at NS EL0" then return(true) else ();
  return(false)
}

val ThisInstrLength : unit -> int effect {rreg}

function ThisInstrLength () = return(if __ThisInstrEnc == __T16 then 16 else 32)

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

val HaveExtendedExecuteNeverExt : unit -> bool

function HaveExtendedExecuteNeverExt () = return(HasArchVersion(ARMv8p2))

val HaveDirtyBitModifierExt : unit -> bool

function HaveDirtyBitModifierExt () = return(HasArchVersion(ARMv8p1))

val HaveCommonNotPrivateTransExt : unit -> bool

function HaveCommonNotPrivateTransExt () = return(HasArchVersion(ARMv8p2))

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

function ConstrainUnpredictableInteger (low, high, which) = {
  c : Constraint = ConstrainUnpredictable(which);
  if c == Constraint_UNKNOWN then return((c, low)) else return((c, undefined : int))
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

val BigEndianReverse : forall ('width : Int), 'width >= 0 & 'width >= 0.
  bits('width) -> bits('width) effect {escape}

function BigEndianReverse value_name = {
  assert('width == 8 | 'width == 16 | 'width == 32 | 'width == 64 | 'width == 128);
  let 'half = 'width / 2;
  assert(constraint('half * 2 = 'width));
  if 'width == 8 then return(value_name) else ();
  return(BigEndianReverse(slice(value_name, 0, half)) @ BigEndianReverse(slice(value_name, half, 'width - half)))
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

val Replicate : forall ('M : Int) ('N : Int), 'M >= 0 & 'N >= 0.
  bits('M) -> bits('N) effect {escape}

function Replicate x = {
  assert('N % 'M == 0, "((N MOD M) == 0)");
  let 'p = ex_int('N / 'M);
  assert(constraint('N = 'p * 'M));
  return(replicate_bits(x, p))
}

val Zeros__0 : forall ('N : Int), 'N >= 0. atom('N) -> bits('N)

val Zeros__1 : forall ('N : Int), 'N >= 0. unit -> bits('N)

overload Zeros = {Zeros__0, Zeros__1}

function Zeros__0 N = return(replicate_bits(0b0, 'N))

function Zeros__1 () = return(Zeros('N))

val ZeroExtend__0 : forall ('M : Int) ('N : Int), 'M >= 0 & 'N >= 0.
  (bits('M), atom('N)) -> bits('N) effect {escape}

val ZeroExtend__1 : forall ('M : Int) ('N : Int), 'M >= 0 & 'N >= 0.
  bits('M) -> bits('N) effect {escape}

overload ZeroExtend = {ZeroExtend__0, ZeroExtend__1}

function ZeroExtend__0 (x, N) = {
  assert('N >= 'M);
  return(Zeros('N - 'M) @ x)
}

function ZeroExtend__1 x = return(ZeroExtend(x, 'N))

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

val LSL_C : forall ('N : Int), 'N >= 0 & 'N >= 0 & 1 >= 0.
  (bits('N), int) -> (bits('N), bits(1)) effect {escape}

function LSL_C (x, 'shift) = {
  assert(shift > 0, "(shift > 0)");
  extended_x : bits('shift + 'N) = x @ Zeros(shift);
  result : bits('N) = slice(extended_x, 0, 'N);
  carry_out : bits(1) = [extended_x['N]];
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

val LSInstructionSyndrome : unit -> bits(11) effect {escape}

function LSInstructionSyndrome () = {
  assert(false, "FALSE");
  return(Zeros(11))
}

val IsZero : forall ('N : Int), 'N >= 0. bits('N) -> bool

function IsZero x = return(x == Zeros('N))

val AddWithCarry : forall ('N : Int), 'N >= 0 & 'N >= 0 & 1 >= 0 & 'N >= 0 & 4 >= 0.
  (bits('N), bits('N), bits(1)) -> (bits('N), bits(4))

function AddWithCarry (x, y, carry_in) = {
  unsigned_sum : int = UInt(x) + UInt(y) + UInt(carry_in);
  signed_sum : int = SInt(x) + SInt(y) + UInt(carry_in);
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
  if c == Constraint_UNKNOWN then return((c, Zeros('width))) else return((c, undefined : bits('width)))
}

val SignExtend__0 : forall ('M : Int) ('N : Int), 'M >= 0 & 'N >= 0.
  (bits('M), atom('N)) -> bits('N) effect {escape}

val SignExtend__1 : forall ('M : Int) ('N : Int), 'M >= 0 & 'N >= 0.
  bits('M) -> bits('N) effect {escape}

overload SignExtend = {SignExtend__0, SignExtend__1}

function SignExtend__0 (x, N) = {
  assert('N >= 'M);
  return(replicate_bits([x['M - 1]], 'N - 'M) @ x)
}

function SignExtend__1 x = return(SignExtend(x, 'N))

val Ones__0 : forall ('N : Int), 'N >= 0. atom('N) -> bits('N)

val Ones__1 : forall ('N : Int), 'N >= 0. unit -> bits('N)

overload Ones = {Ones__0, Ones__1}

function Ones__0 N = return(replicate_bits(0b1, 'N))

function Ones__1 () = return(Ones('N))

val IsOnes : forall ('N : Int), 'N >= 0. bits('N) -> bool

function IsOnes x = return(x == Ones('N))

val ExcVectorBase : unit -> bits(32) effect {rreg}

function ExcVectorBase () = if [SCTLR[13]] == 0b1 then return(Ones(16) @ Zeros(16)) else return(slice(VBAR, 5, 27) @ Zeros(5))

val Align__0 : (int, int) -> int

val Align__1 : forall ('N : Int), 'N >= 0 & 'N >= 0. (bits('N), int) -> bits('N)

overload Align = {Align__0, Align__1}

function Align__0 ('x, 'y) = return(y * (x / y))

function Align__1 (x, 'y) = return(__GetSlice_int('N, Align(UInt(x), y), 0))

val aset__Mem : forall ('size : Int), 8 * 'size >= 0.
  (AddressDescriptor, atom('size), AccessDescriptor, bits(8 * 'size)) -> unit effect {escape, rreg}

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
  (AddressDescriptor, atom('size), AccessDescriptor) -> bits(8 * 'size) effect {escape, rreg}

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
  if setflags then (PSTATE.N, PSTATE.Z, PSTATE.C, PSTATE.V) = nzcv else ();
  if d == 31 & ~(setflags) then aset_SP(result) else aset_X(d, result)
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

val IsSecure : unit -> bool effect {escape, rreg, undef}

function IsSecure () = {
  if (HaveEL(EL3) & ~(UsingAArch32())) & PSTATE.EL == EL3 then return(true) else if (HaveEL(EL3) & UsingAArch32()) & PSTATE.M == M32_Monitor then return(true) else ();
  return(IsSecureBelowEL3())
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

val HaveAArch32EL : bits(2) -> bool

function HaveAArch32EL el = {
  if ~(HaveEL(el)) then return(false) else if ~(HaveAnyAArch32()) then return(false) else if HighestELUsingAArch32() then return(true) else if el == HighestEL() then return(false) else if el == EL0 then return(true) else ();
  return(true)
}

val Halted : unit -> bool effect {rreg}

function Halted () = return(~(slice(EDSCR, 0, 6) == 0b000001 | slice(EDSCR, 0, 6) == 0b000010))

val ExternalSecureInvasiveDebugEnabled : unit -> bool effect {escape, rreg, undef}

function ExternalSecureInvasiveDebugEnabled () = {
  if ~(HaveEL(EL3)) & ~(IsSecure()) then return(false) else ();
  return(ExternalInvasiveDebugEnabled() & SPIDEN == HIGH)
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
    (PSTATE.SS, PSTATE.A, PSTATE.I, PSTATE.F) = undefined : bits(4);
    PSTATE.IT = 0x00;
    PSTATE.T = 0b1
  } else
    (PSTATE.SS, PSTATE.D, PSTATE.A, PSTATE.I, PSTATE.F) = undefined : bits(5);
  PSTATE.IL = 0b0;
  StopInstructionPrefetchAndEnableITR();
  EDSCR[5 .. 0] = reason;
  UpdateEDSCRFields();
  ()
}

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

val HaltOnBreakpointOrWatchpoint : unit -> bool effect {escape, rreg, undef}

function HaltOnBreakpointOrWatchpoint () = return((HaltingAllowed() & [EDSCR[14]] == 0b1) & [OSLSR_EL1[1]] == 0b0)

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
    WVR_match = vaddress[top - mask2 + 1 - 1 + mask2 .. mask2] == DBGWVR_EL1[n][top - mask2 + 1 - 1 + mask2 .. mask2];
    if WVR_match & ~(IsZero(DBGWVR_EL1[n][mask2 - bottom2 - 1 + bottom2 .. bottom2])) then
      WVR_match = ConstrainUnpredictableBool(Unpredictable_WPMASKEDBITS)
    else ()
  } else
    WVR_match = vaddress[top - bottom2 + 1 - 1 + bottom2 .. bottom2] == DBGWVR_EL1[n][top - bottom2 + 1 - 1 + bottom2 .. bottom2];
  return(WVR_match & byte_select_match)
}

val IsZero_slice : forall 'n, 'n >= 0.
  (bits('n), int, int) -> bool effect {escape}

function IsZero_slice (xs, i, 'l) = {
  assert(constraint('l >= 0));
  IsZero(slice(xs, i, l))
}

val IsOnes_slice : forall 'n, 'n >= 0.
  (bits('n), int, int) -> bool effect {escape}

function IsOnes_slice (xs, i, 'l) = {
  assert(constraint('l >= 0));
  IsOnes(slice(xs, i, l))
}

val ZeroExtend_slice_append : forall 'n 'm 'o, 'n >= 0 & 'm >= 0 & 'o >= 0.
  (bits('n), int, int, bits('m)) -> bits('o) effect {escape}

function ZeroExtend_slice_append (xs, i, 'l, ys) = {
  assert(constraint('l >= 0));
  ZeroExtend(slice(xs, i, l) @ ys)
}

val AArch64_TranslationTableWalk : (bits(52), bits(64), AccType, bool, bool, bool, int) -> TLBRecord effect {escape, rreg, rmem, wmem, undef}

function AArch64_TranslationTableWalk (ipaddress, vaddress, acctype, iswrite, secondstage, s2fs1walk, 'size) = {
  if ~(secondstage) then assert(~(ELUsingAArch32(S1TranslationRegime()))) else assert(((HaveEL(EL2) & ~(IsSecure())) & ~(ELUsingAArch32(EL2))) & HasS2Translation());
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
      basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsZero_slice(inputaddr, inputsize, top - inputsize + 1);
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
        basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsZero_slice(inputaddr, inputsize, top - inputsize + 1);
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
        basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsOnes_slice(inputaddr, inputsize, top - inputsize + 1);
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
      basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsZero_slice(inputaddr, inputsize, top - inputsize + 1);
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
        basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsZero_slice(inputaddr, inputsize, top - inputsize + 1);
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
        basefound = (inputsize >= inputsize_min & inputsize <= inputsize_max) & IsOnes_slice(inputaddr, inputsize, top - inputsize + 1);
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
  let 'baselowerbound = (3 + inputsize - ((3 - level) * stride + grainsize)) : int;
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
    index : bits(52) = ZeroExtend_slice_append(inputaddr, addrselectbottom, addrselecttop - addrselectbottom + 1, 0b000);
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
  IsZero(slice(xs, i, l))
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
  if ~(IsZero_slice2(vaddress, PAMax(), Top + 1 - PAMax())) then {
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

val AArch64_MaybeZeroRegisterUppers : unit -> unit effect {wreg, undef, rreg, escape}

function AArch64_MaybeZeroRegisterUppers () = {
  assert(UsingAArch32(), "UsingAArch32()");
  include_R15_name : bool = undefined;
  last : range(14, 30) = undefined;
  first : atom(0) = 0;
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
    if (n : int != 15 : int | include_R15_name) & ConstrainUnpredictableBool(Unpredictable_ZEROUPPER) then {
      __tmp_3 : bits(64) = _R[n];
      __tmp_3[63 .. 32] = Zeros(32);
      _R[n] = __tmp_3
    } else ();
  ()
}

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

function AArch64_SecondStageTranslate (S1, vaddress, acctype, iswrite, wasaligned, s2fs1walk, 'size, hwupdatewalk) = {
  assert(HasS2Translation(), "HasS2Translation()");
  s2_enabled : bool = [HCR_EL2[0]] == 0b1 | [HCR_EL2[12]] == 0b1;
  secondstage : bool = true;
  result : AddressDescriptor = undefined;
  S2 : TLBRecord = undefined;
  ipaddress : bits(52) = undefined;
  if s2_enabled then {
    ipaddress = slice(S1.paddress.physicaladdress, 0, 52);
    S2 = AArch64_TranslationTableWalk(ipaddress, vaddress, acctype, iswrite, secondstage, s2fs1walk, size);
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
    if ((~(s2fs1walk) & ~(IsFault(S2.addrdesc))) & S2.addrdesc.memattrs.typ == MemType_Device) & acctype == AccType_IFETCH then S2.addrdesc = AArch64_InstructionDevice(S2.addrdesc, vaddress, ipaddress, S2.level, acctype, iswrite, secondstage, s2fs1walk) else ();
    if ((s2fs1walk & ~(IsFault(S2.addrdesc))) & [HCR_EL2[2]] == 0b1) & S2.addrdesc.memattrs.typ == MemType_Device then {
      __tmp_73 : AddressDescriptor = S2.addrdesc;
      __tmp_73.fault = AArch64_PermissionFault(ipaddress, S2.level, acctype, iswrite, secondstage, s2fs1walk);
      S2.addrdesc = __tmp_73
    } else ();
    __tmp_74 : AddressDescriptor = S2.addrdesc;
    __tmp_74.fault = AArch64_CheckAndUpdateDescriptor(S2.descupdate, S2.addrdesc.fault, secondstage, vaddress, acctype, iswrite, s2fs1walk, hwupdatewalk);
    S2.addrdesc = __tmp_74;
    result = CombineS1S2Desc(S1, S2.addrdesc)
  } else result = S1;
  return(result)
}

function AArch64_CheckAndUpdateDescriptor (result, fault, secondstage, vaddress, acctype, iswrite, s2fs1walk, hwupdatewalk__arg) = {
  hwupdatewalk = hwupdatewalk__arg;
  hw_update_AF : bool = undefined;
  if result.AF then if fault.typ == Fault_None then hw_update_AF = true else if ConstrainUnpredictable(Unpredictable_AFUPDATE) == Constraint_TRUE then hw_update_AF = true else hw_update_AF = false else ();
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
    if hw_update_AF then desc = __SetSlice_bits(64, 1, desc, 10, 0b1) else ();
    if hw_update_AP then desc = __SetSlice_bits(64, 1, desc, 7, if secondstage then 0b1 else 0b0) else ();
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
    EL3 => priv_match = EL3_match,
    EL2 => priv_match = EL2_match,
    EL1 => priv_match = EL1_match,
    EL0 => priv_match = EL0_match
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

val AArch64_WatchpointMatch : (int, bits(64), int, bool, bool) -> bool

function AArch64_WatchpointMatch (n, vaddress, size, ispriv, iswrite) = false

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

val AArch64_TakeException : (bits(2), ExceptionRecord, bits(64), int) -> unit effect {escape, rreg, undef, wreg}

function AArch64_TakeException (target_el, exception, preferred_exception_return, vect_offset__arg) = {
  vect_offset = vect_offset__arg;
  SynchronizeContext();
  assert((HaveEL(target_el) & ~(ELUsingAArch32(target_el))) & UInt(target_el) >= UInt(PSTATE.EL), "((HaveEL(target_el) && !(ELUsingAArch32(target_el))) && (UInt(target_el) >= UInt((PSTATE).EL)))");
  from_32 : bool = UsingAArch32();
  if from_32 then AArch64_MaybeZeroRegisterUppers() else ();
  if UInt(target_el) > UInt(PSTATE.EL) then {
    lower_32 : bool = undefined;
    if target_el == EL3 then if ~(IsSecure()) & HaveEL(EL2) then lower_32 = ELUsingAArch32(EL2) else lower_32 = ELUsingAArch32(EL1) else if (IsInHost() & PSTATE.EL == EL0) & target_el == EL2 then lower_32 = ELUsingAArch32(EL0) else lower_32 = ELUsingAArch32(target_el - 1);
    vect_offset = vect_offset + (if lower_32 then 1536 else 1024)
  } else if PSTATE.SP == 0b1 then vect_offset = vect_offset + 512 else ();
  spsr : bits(32) = GetPSRFromPSTATE();
  if HaveUAOExt() then PSTATE.UAO = 0b0 else ();
  if ~(exception.typ == Exception_IRQ | exception.typ == Exception_FIQ) then AArch64_ReportException(exception, target_el) else ();
  PSTATE.EL = target_el;
  PSTATE.nRW = 0b0;
  PSTATE.SP = 0b1;
  aset_SPSR(spsr);
  aset_ELR(preferred_exception_return);
  PSTATE.SS = 0b0;
  (PSTATE.D, PSTATE.A, PSTATE.I, PSTATE.F) = 0xF;
  PSTATE.IL = 0b0;
  if from_32 then {
    PSTATE.IT = 0x00;
    PSTATE.T = 0b0
  } else ();
  if (HavePANExt() & (PSTATE.EL == EL1 | PSTATE.EL == EL2 & ELIsInHost(EL0))) & [aget_SCTLR()[23]] == 0b0 then PSTATE.PAN = 0b1 else ();
  BranchTo(slice(aget_VBAR(), 11, 53) @ __GetSlice_int(11, vect_offset, 0), BranchType_EXCEPTION);
  iesb_req : bool = undefined;
  if HaveRASExt() & [aget_SCTLR()[21]] == 0b1 then {
    ErrorSynchronizationBarrier(MBReqDomain_FullSystem, MBReqTypes_All);
    iesb_req = true;
    TakeUnmaskedPhysicalSErrorInterrupts(iesb_req)
  } else ();
  EndOfInstruction()
}

val AArch64_WatchpointException : (bits(64), FaultRecord) -> unit effect {escape, rreg, undef, wreg}

function AArch64_WatchpointException (vaddress, fault) = {
  assert(PSTATE.EL != EL3, "((PSTATE).EL != EL3)");
  route_to_el2 : bool = ((HaveEL(EL2) & ~(IsSecure())) & (PSTATE.EL == EL0 | PSTATE.EL == EL1)) & ([HCR_EL2[27]] == 0b1 | [MDCR_EL2[8]] == 0b1);
  preferred_exception_return : bits(64) = ThisInstrAddr();
  vect_offset : int = 0;
  exception : ExceptionRecord = AArch64_AbortSyndrome(Exception_Watchpoint, fault, vaddress);
  if PSTATE.EL == EL2 | route_to_el2 then AArch64_TakeException(EL2, exception, preferred_exception_return, vect_offset) else AArch64_TakeException(EL1, exception, preferred_exception_return, vect_offset)
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
  if target_mode == M32_FIQ then (PSTATE.A, PSTATE.I, PSTATE.F) = 0b111 else if target_mode == M32_Abort | target_mode == M32_IRQ then (PSTATE.A, PSTATE.I) = 0b11 else PSTATE.I = 0b1;
  PSTATE.E = [SCTLR[25]];
  PSTATE.IL = 0b0;
  PSTATE.IT = 0x00;
  if HavePANExt() & [SCTLR[23]] == 0b0 then PSTATE.PAN = 0b1 else ();
  BranchTo(slice(ExcVectorBase(), 5, 27) @ __GetSlice_int(5, vect_offset, 0), BranchType_UNKNOWN);
  EndOfInstruction()
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

val aarch64_memory_single_general_immediate_unsigned : forall ('datasize : Int) ('regsize : Int).
  (AccType, atom('datasize), MemOp, int, bits(64), bool, atom('regsize), bool, int, bool) -> unit effect {escape, undef, rreg, wreg, wmem, rmem}

function aarch64_memory_single_general_immediate_unsigned (acctype, datasize, memop, n, offset, postindex, regsize, signed, t, wback__arg) = {
  assert(constraint('regsize >= 0), "destsize constraint");
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
  if ~(postindex) then address = address + offset
  else ();
  match memop {
    MemOp_STORE => {
      if rt_unknown then data = undefined
      else data = aget_X(t);
      aset_Mem(address, dbytes, acctype, data)
    },
    MemOp_LOAD => {
      data = aget_Mem(address, dbytes, acctype);
      if signed then aset_X(t, SignExtend(data, regsize)) else aset_X(t, ZeroExtend(data, regsize))
    },
    MemOp_PREFETCH => Prefetch(address, __GetSlice_int(5, t, 0))
  };
  if wback then {
    if wb_unknown then address = undefined
    else if postindex then address = address + offset
    else ();
    if n == 31 then aset_SP(address) else aset_X(n, address)
  } else ()
}

val aarch64_memory_single_general_immediate_signed_postidx : forall ('datasize : Int) ('regsize : Int).
  (AccType, atom('datasize), MemOp, int, bits(64), bool, atom('regsize), bool, int, bool) -> unit effect {escape, undef, rreg, wreg, wmem, rmem}

function aarch64_memory_single_general_immediate_signed_postidx (acctype, datasize, memop, n, offset, postindex, regsize, signed, t, wback__arg) = {
  assert(constraint('regsize >= 0), "destsize constraint");
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
  if ~(postindex) then address = address + offset
  else ();
  match memop {
    MemOp_STORE => {
      if rt_unknown then data = undefined
      else data = aget_X(t);
      aset_Mem(address, dbytes, acctype, data)
    },
    MemOp_LOAD => {
      data = aget_Mem(address, dbytes, acctype);
      if signed then aset_X(t, SignExtend(data, regsize)) else aset_X(t, ZeroExtend(data, regsize))
    },
    MemOp_PREFETCH => Prefetch(address, __GetSlice_int(5, t, 0))
  };
  if wback then {
    if wb_unknown then address = undefined
    else if postindex then address = address + offset
    else ();
    if n == 31 then aset_SP(address) else aset_X(n, address)
  } else ()
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

val ReservedValue : unit -> unit effect {escape, rreg, undef, wreg}

function ReservedValue () = if UsingAArch32() & ~(AArch32_GeneralExceptionsToAArch64()) then AArch32_TakeUndefInstrException() else AArch64_UndefinedFault()

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
