function unit effect {wmem} MEMw_wrapper(addr, size, data) = MEMw(addr, size, data)
function bool effect {wmem} MEMw_conditional_wrapper(addr, size, data) =
  MEMw_conditional(addr, size, data)

function bit[64] addrWrapper((bit[64]) addr, (MemAccessType) accessType, (WordType) width) =
    addr

function (option<Exception>, option<bit[64]>) TranslateAddress ((bit[64]) vAddr, (MemAccessType) accessType) = 
    TLBTranslate(vAddr, accessType)
