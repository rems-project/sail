$include <flow.sail>

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

type TUBE_Type = vector(32, inc, bit)

type ScheduleIRQ_Type = vector(32, inc, bit)

type ClearIRQ_Type = vector(32, inc, bit)

type ScheduleFIQ_Type = vector(32, inc, bit)

type ClearFIQ_Type = vector(32, inc, bit)

type TargetCPU_Type = vector(32, inc, bit)

type AbortRgn64Lo1_Type = vector(32, inc, bit)

type AbortRgn64Lo1_Hi_Type = vector(32, inc, bit)

type AbortRgn64Hi1_Type = vector(32, inc, bit)

type AbortRgn64Hi1_Hi_Type = vector(32, inc, bit)

type AbortRgn64Lo2_Type = vector(32, inc, bit)

type AbortRgn64Lo2_Hi_Type = vector(32, inc, bit)

type AbortRgn64Hi2_Type = vector(32, inc, bit)

type AbortRgn64Hi2_Hi_Type = vector(32, inc, bit)

type AXIAbortCtl_Type = vector(32, inc, bit)

type GTE_API_Type = vector(32, inc, bit)

type GTE_API_PARAM_Type = vector(32, inc, bit)

type GTE_API_STATUS_Type = vector(32, inc, bit)

type PPURBAR_Type = vector(32, inc, bit)

type PPURSER_Type = vector(32, inc, bit)

type PPURACR_Type = vector(32, inc, bit)

type GTE_API_STATUS_64_Type = vector(32, inc, bit)

type GTE_API_STATUS_64_HI_Type = vector(32, inc, bit)

type GTE_API_PARAM_64_Type = vector(32, inc, bit)

type GTE_API_PARAM_64_HI_Type = vector(32, inc, bit)

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

type SCRType = vector(32, inc, bit)

type SCTLRType = vector(32, inc, bit)

type MAIRType = vector(64, inc, bit)

type ESRType = vector(32, inc, bit)

type FPCRType = vector(32, inc, bit)

type FPSRType = vector(32, inc, bit)

type FPSCRType = vector(32, inc, bit)

type CPSRType = vector(32, inc, bit)

type APSRType = vector(32, inc, bit)

type ITSTATEType = vector(8, inc, bit)

type CPACRType = vector(32, inc, bit)

type CNTKCTLType = vector(32, inc, bit)

enum GTEParamType = {GTEParam_WORD, GTEParam_LIST, GTEParam_EOACCESS}

type GTE_PPU_SizeEn_Type = vector(32, inc, bit)

type GTEExtObsAccess_Type = vector(16, inc, bit)

type GTEASAccess_Type = vector(32, inc, bit)

type GTEASRecordedAccess_Type = vector(32, inc, bit)

enum AccType = {
  AccType_NORMAL,
  AccType_VEC,
  AccType_STREAM,
  AccType_VECSTREAM,
  AccType_ATOMIC,
  AccType_ORDERED,
  AccType_UNPRIV,
  AccType_IFETCH,
  AccType_PTW,
  AccType_DC,
  AccType_IC,
  AccType_DCZVA,
  AccType_AT
}

enum MemType = {MemType_Normal, MemType_Device}

enum DeviceType = {
  DeviceType_GRE,
  DeviceType_nGRE,
  DeviceType_nGnRE,
  DeviceType_nGnRnE
}

struct MemAttrHints = {
  attrs : vector(2, inc, bit),
  hints : vector(2, inc, bit),
  transient : bool
}

struct MemoryAttributes = {
  typ : MemType,
  device : DeviceType,
  inner : MemAttrHints,
  outer : MemAttrHints,
  shareable : bool,
  outershareable : bool
}
