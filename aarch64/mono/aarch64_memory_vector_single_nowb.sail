val aarch64_memory_vector_single_nowb : forall ('datasize : Int) ('esize : Int) ('selem : Int).
  (atom('datasize), atom('esize), int, int, MemOp, int, bool, atom('selem), int, bool) -> unit effect {escape, rmem, wmem, undef, wreg, rreg}

function aarch64_memory_vector_single_nowb (datasize, esize, index, m, memop, n, replicate, selem, t__arg, wback) = {
  assert(constraint('datasize >= 0 & 'selem >= 1 & 'esize >= 0));
  t = t__arg;
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
      aset_V(t, replicate_bits(element, 'v))
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
