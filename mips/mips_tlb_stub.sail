function option<TLBIndexT> tlbSearch((bit[64]) VAddr) = None

function (bit[64]) TLBTranslate ((bit[64]) vAddr, (MemAccessType) accessType) = 
      vAddr
