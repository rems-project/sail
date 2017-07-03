
typedef boolean = enumerate {FALSE; TRUE}

typedef signal = enumerate {LOW; HIGH}

typedef __RetCode =
  enumerate {__RC_OK;
  __RC_UNDEFINED;
  __RC_UNPREDICTABLE;
  __RC_SEE;
  __RC_IMPLEMENTATION_DEFINED;
  __RC_SUBARCHITECTURE_DEFINED;
  __RC_EXCEPTION_TAKEN;
  __RC_ASSERT_FAILED;
  __RC_UNMATCHED_CASE}

typedef TUBE_Type = bit[32]

typedef ScheduleIRQ_Type = bit[32]

typedef ClearIRQ_Type = bit[32]

typedef ScheduleFIQ_Type = bit[32]

typedef ClearFIQ_Type = bit[32]

typedef TargetCPU_Type = bit[32]

typedef AbortRgn64Lo1_Type = bit[32]

typedef AbortRgn64Lo1_Hi_Type = bit[32]

typedef AbortRgn64Hi1_Type = bit[32]

typedef AbortRgn64Hi1_Hi_Type = bit[32]

typedef AbortRgn64Lo2_Type = bit[32]

typedef AbortRgn64Lo2_Hi_Type = bit[32]

typedef AbortRgn64Hi2_Type = bit[32]

typedef AbortRgn64Hi2_Hi_Type = bit[32]

typedef AXIAbortCtl_Type = bit[32]

typedef GTE_API_Type = bit[32]

typedef GTE_API_PARAM_Type = bit[32]

typedef GTE_API_STATUS_Type = bit[32]

typedef PPURBAR_Type = bit[32]

typedef PPURSER_Type = bit[32]

typedef PPURACR_Type = bit[32]

typedef GTE_API_STATUS_64_Type = bit[32]

typedef GTE_API_STATUS_64_HI_Type = bit[32]

typedef GTE_API_PARAM_64_Type = bit[32]

typedef GTE_API_PARAM_64_HI_Type = bit[32]

typedef MemAtomicOp =
  enumerate {MemAtomicOp_ADD;
  MemAtomicOp_BIC;
  MemAtomicOp_EOR;
  MemAtomicOp_ORR;
  MemAtomicOp_SMAX;
  MemAtomicOp_SMIN;
  MemAtomicOp_UMAX;
  MemAtomicOp_UMIN;
  MemAtomicOp_SWP}

typedef SCRType = bit[32]

typedef SCTLRType = bit[32]

typedef MAIRType = bit[64]

typedef ESRType = bit[32]

typedef FPCRType = bit[32]

typedef FPSRType = bit[32]

typedef FPSCRType = bit[32]

typedef CPSRType = bit[32]

typedef APSRType = bit[32]

typedef ITSTATEType = bit[8]

typedef CPACRType = bit[32]

typedef CNTKCTLType = bit[32]

typedef GTEParamType = enumerate {GTEParam_WORD; GTEParam_LIST; GTEParam_EOACCESS}

typedef GTE_PPU_SizeEn_Type = bit[32]

typedef GTEExtObsAccess_Type = bit[16]

typedef GTEASAccess_Type = bit[32]

typedef GTEASRecordedAccess_Type = bit[32]

typedef AccType =
  enumerate {AccType_NORMAL;
  AccType_VEC;
  AccType_STREAM;
  AccType_VECSTREAM;
  AccType_ATOMIC;
  AccType_ORDERED;
  AccType_UNPRIV;
  AccType_IFETCH;
  AccType_PTW;
  AccType_DC;
  AccType_IC;
  AccType_DCZVA;
  AccType_AT}

typedef MemType = enumerate {MemType_Normal; MemType_Device}

typedef DeviceType =
  enumerate {DeviceType_GRE; DeviceType_nGRE; DeviceType_nGnRE; DeviceType_nGnRnE}

typedef MemAttrHints = const struct {bit[2] attrs; bit[2] hints; bool transient;}

typedef MemoryAttributes =
  const struct {MemType type;
  DeviceType device;
  MemAttrHints inner;
  MemAttrHints outer;
  bool shareable;
  bool outershareable;}
