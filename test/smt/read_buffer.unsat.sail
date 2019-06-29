default Order dec

$include <prelude.sail>

val "eq_anything" : forall ('a: Type). ('a, 'a) -> bool
overload operator == = {eq_anything}

enum AccType = AccType_NORMAL | AccType_VEC | AccType_IFETCH

struct read_buffer_type = {
  acctype : AccType,
  exclusive : bool,
  address : bits(64),
  size : nat,
}

let empty_read_buffer : read_buffer_type =  struct { 
  size = 0,
  acctype = AccType_NORMAL,
  exclusive = false,
  address = sail_zeros(64)
}

function set_exclusive(rb: read_buffer_type) -> read_buffer_type = {
  { rb with exclusive = true }
}

function test(rb': read_buffer_type, flag: bool) -> read_buffer_type = {
  rb : read_buffer_type = rb';
  rb.acctype = AccType_IFETCH;

  if flag then {
    rb = set_exclusive(rb)
  };

  return { rb with address = sail_ones(64) }
}

$property
function prop() -> bool = {
  let rb = test(empty_read_buffer, true);
  rb.acctype == AccType_IFETCH & rb.address == sail_ones(64) & rb.exclusive == true
}