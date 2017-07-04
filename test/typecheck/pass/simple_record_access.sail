typedef signal = enumerate {LOW; HIGH}

typedef Bit32 = bit[32]

typedef Record =
  const struct {signal rsig;
  Bit32 bitfield;}

register bit[32] R0

val Record -> unit effect {wreg} test

function unit test ((Record) r) =
{
  R0 := r.bitfield;
}
