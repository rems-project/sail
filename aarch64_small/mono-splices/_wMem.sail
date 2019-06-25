function _wMem(write_buffer, desc, size, acctype, exclusive, value) = {
  let s = write_buffer.size;
  if s == 0 then {
    struct { acctype = acctype,
      exclusive = exclusive,
      address = (desc.paddress).physicaladdress,
      value = ZeroExtend(value),
      size = size
    }
  } else {
    assert(write_buffer.acctype == acctype);
    assert(write_buffer.exclusive == exclusive);
    assert((write_buffer.address + s) : bits(64) == (desc.paddress).physicaladdress);
  assert((s * 8) + ('N * 8) <= 128);
    value1 : bits(128) = sail_shiftleft(ZeroExtend(value), s * 8);
    value1[((s * 8) - 1) .. 0] = (write_buffer.value)[((s * 8) - 1) .. 0];
    { write_buffer with
      value = value1,
      size = s + size
    }
  }
}

val flush_write_buffer2 : forall 'n, 'n in {1,2,4,8,16}. (write_buffer_type, int('n)) -> unit effect {escape,wmv}

function flush_write_buffer2 (write_buffer, s) ={
  match write_buffer.acctype {
    AccType_NORMAL   => wMem_Val_NORMAL (write_buffer.address, s, (write_buffer.value)[((s * 8) - 1) .. 0]),
    AccType_STREAM   => wMem_Val_NORMAL (write_buffer.address, s, (write_buffer.value)[((s * 8) - 1) .. 0]),
    AccType_UNPRIV   => wMem_Val_NORMAL (write_buffer.address, s, (write_buffer.value)[((s * 8) - 1) .. 0]),
    AccType_ORDERED  => wMem_Val_ORDERED (write_buffer.address, s, (write_buffer.value)[((s * 8) - 1) .. 0]),
    _  => not_implemented("unrecognised memory access")
  };
}

function flush_write_buffer(write_buffer) = {
  assert(write_buffer.exclusive == false);
  let s : range(0,16) = write_buffer.size;
  assert (s == 1 | s == 2 | s == 4 | s == 8 | s == 16);
  flush_write_buffer2(write_buffer, s);
}

val flush_write_buffer_exclusive2 : forall 'n, 'n in {1,2,4,8,16}. (write_buffer_type, int('n)) -> bool effect {escape, wmv}
function flush_write_buffer_exclusive2(write_buffer, s) = {
  match write_buffer.acctype {
    AccType_ATOMIC   => wMem_Val_ATOMIC(write_buffer.address, s, (write_buffer.value)[((s * 8) - 1) .. 0]),
    AccType_ORDERED  => wMem_Val_ATOMIC_ORDERED(write_buffer.address, s, (write_buffer.value)[((s * 8) - 1) .. 0]),
    _  => { not_implemented("unrecognised memory access"); false; }
  };
}

function flush_write_buffer_exclusive(write_buffer) = {
  assert(write_buffer.exclusive);
  let s = write_buffer.size;
  assert (s == 1 | s == 2 | s == 4 | s == 8 | s == 16);
  flush_write_buffer_exclusive2(write_buffer, s);
}
