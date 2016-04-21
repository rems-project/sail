function unit effect {wmem} MEMw_wrapper(addr, size, data) = MEMw(addr, size, data)
function bool effect {wmem} MEMw_conditional_wrapper(addr, size, data) =
  MEMw_conditional(addr, size, data)