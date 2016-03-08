(* 265-bit capability is really 257 bits including tag *)
typedef Capability = register bits [256:0] {
  256:      tag;
  255..248: reserved; (* padding *)
  247..224: otype;
  223..208: sw_perms;
  207:      access_KR2C;
  206:      access_KR1C;
  205:      access_KCC;
  204:      access_KDC;
  203:      access_EPCC;
  202:      reserved;
  201:      permit_set_type;
  200:      permit_seal;
  199:      permit_store_ephemeral_cap;
  198:      permit_store_cap;
  197:      permit_load_cap;
  196:      permit_store;
  195:      permit_load;
  194:      permit_execute;
  193:      non_ephemeral;
  192:      sealed;
  191..128: cursor;
  127..64:  base;
  63 .. 0:  length;
}

register Capability PCC
register Capability C00 (* aka default data capability, DDC *)
register Capability C01
register Capability C02
register Capability C03
register Capability C04
register Capability C05
register Capability C06
register Capability C07
register Capability C08
register Capability C09
register Capability C10
register Capability C11
register Capability C12
register Capability C13
register Capability C14
register Capability C15
register Capability C16
register Capability C17
register Capability C18
register Capability C19
register Capability C20
register Capability C21
register Capability C22
register Capability C23
register Capability C24 (* aka return code capability, RCC *)
register Capability C25
register Capability C26 (* aka invoked data capability, IDC *)
register Capability C27 (* aka kernel reserved capability 1, KR1C *)
register Capability C28 (* aka kernel reserved capability 2, KR2C *)
register Capability C29 (* aka kernel code capability, KCC *)
register Capability C30 (* aka kernel data capability, KDC *)
register Capability C31 (* aka exception program counter capability, EPCC *)

let (vector <0, 32, inc, (Capability)>) CapRegs =
  [ C00, C01, C02, C03, C04, C05, C06, C07, C08, C09, C10,
  C11, C12, C13, C14, C15, C16, C17, C18, C19, C20,
  C21, C22, C23, C24, C25, C26, C27, C28, C29, C30, C31
  ]

typedef CapEx = enumerate {
  CapEx_None; 
  CapEx_LengthVioloation;
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



function (bit[8]) CapExCode((CapEx) ex) =
  switch(ex) {
    case CapEx_None                         -> 0x00
    case CapEx_LengthVioloation             -> 0x01
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
    case CapEx_AccessEPCCViolation          -> 0x1a
    case CapEx_AccessKDCViolation           -> 0x1b
    case CapEx_AccessKCCViolation           -> 0x1c
    case CapEx_AccessKR1CViolation          -> 0x1d
    case CapEx_AccessKR2CViolation          -> 0x1e
  }

typedef CapCauseReg = register bits [15:0] {
  15..8: ExcCode;
  7..0:  RegNum;
}

register CapCauseReg CapCause

function unit raise_c2_exception((CapEx) capEx, (bit[8]) regnum) =
  {
    (CapCause.ExcCode) := CapExCode(capEx);
    (CapCause.RegNum)  := regnum;
    SignalException(C2E);
  }

function unit raise_c2_exception_v((bit[8]) regnum) =
  switch(regnum[4..0]) {
   case 0b11011 -> raise_c2_exception(CapEx_AccessKR1CViolation, regnum)
   case 0b11100 -> raise_c2_exception(CapEx_AccessKR2CViolation, regnum)
   case 0b11101 -> raise_c2_exception(CapEx_AccessKCCViolation, regnum)
   case 0b11110 -> raise_c2_exception(CapEx_AccessKDCViolation, regnum)
   case 0b11111 -> raise_c2_exception(CapEx_AccessEPCCViolation, regnum)
   case _       -> assert(false, Some("should only call for cap reg violation"))
  }

function unit raise_c2_exception_noreg((CapEx) capEx) =
  raise_c2_exception(capEx, 0xff)

function bool register_inaccessible((regno) r) = 
  ~(switch(r) {
    case 0b11011 -> (PCC.access_KR1C)
    case 0b11100 -> (PCC.access_KR2C)
    case 0b11101 -> (PCC.access_KCC)
    case 0b11110 -> (PCC.access_KDC)
    case 0b11111 -> (PCC.access_EPCC)
    case _       -> bitone
  })
