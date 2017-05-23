val extern forall Nat 'n. (bit[64], [:'n:]) -> (bit[8 * 'n]) effect  {rmem} MEMr

let (bit[64]) ea = 0
let (bit[16]) _ = MEMr(ea, 1) (* The 1 should be 2 to pass checking *)
