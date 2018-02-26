/* Needed set constraint */

val aarch64_memory_literal_simdfp : forall ('size : Int).
  (bits(64), atom('size), int) -> unit effect {escape, undef, wreg, rreg, rmem, wmem}

function aarch64_memory_literal_simdfp (offset, size, t) = {
  assert(constraint('size >= 0));
  assert(constraint('size in {4,8,16}));
  address : bits(64) = aget_PC() + offset;
  data : bits(8 * 'size) = undefined;
  CheckFPAdvSIMDEnabled64();
  data = aget_Mem(address, size, AccType_VEC);
  aset_V(t, data)
}
