default Order dec
$include <prelude.sail>

type hpmidx = range(3, 31)
private enum event_csr = {EV_EVENT, EV_COUNTER}
register written_event_index : option((hpmidx, event_csr)) = None()
