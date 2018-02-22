/* Ideally we'd rewrite these to take the bit size */

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

/* like this, which would be difficult otherwise... */

val aarch64_memory_literal_general : forall ('size : Int).
  (MemOp, bits(64), bool, atom('size), int) -> unit effect {escape, undef, wreg, rreg, rmem, wmem}

function aarch64_memory_literal_general (memop, offset, signed, size, t) = {
  address : bits(64) = aget_PC() + offset;
  data : bits('size) = undefined;
  match memop {
    MemOp_LOAD => {
      assert(constraint('size >= 0));
      let 'bytes = size / 8;
      assert(constraint(8 * 'bytes = 'size));
      data = aget_Mem(address, bytes, AccType_NORMAL);
      if signed then aset_X(t, SignExtend(data, 64)) else aset_X(t, data)
    },
    MemOp_PREFETCH => Prefetch(address, __GetSlice_int(5, t, 0))
  }
}

val memory_literal_general_decode : (bits(2), bits(1), bits(19), bits(5)) -> unit effect {escape, rmem, rreg, undef, wmem, wreg}

function memory_literal_general_decode (opc, V, imm19, Rt) = {
  __unconditional = true;
  t : int = UInt(Rt);
  memop : MemOp = MemOp_LOAD;
  signed : bool = false;
  size : int = undefined;
  offset : bits(64) = undefined;
  match opc {
    0b00 => size = 4,
    0b01 => size = 8,
    0b10 => {
      size = 4;
      signed = true
    },
    0b11 => memop = MemOp_PREFETCH
  };
  offset = SignExtend(imm19 @ 0b00, 64);
  aarch64_memory_literal_general(memop, offset, signed, 8 * size, t)
}
