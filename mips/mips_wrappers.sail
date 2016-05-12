function unit effect {wmem} MEMw_wrapper(addr, size, data) = MEMw(addr, size, data)
function bool effect {wmem} MEMw_conditional_wrapper(addr, size, data) =
  MEMw_conditional(addr, size, data)

function bit[64] addrWrapper((bit[64]) addr, (MemAccessType) accessType, (WordType) width) =
    addr

function (bit[64]) TranslateAddress ((bit[64]) vAddr, (MemAccessType) accessType) = {
    incrementCP0Count();
    if (vAddr[1..0] != 0b00) then (* bad PC alignment *)
      exit (SignalExceptionBadAddr(AdEL, vAddr))
    else
      TLBTranslate(vAddr, accessType)
}

function unit SignalException ((Exception) ex) = SignalExceptionMIPS(ex)

function unit ERETHook() = ()
