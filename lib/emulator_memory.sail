
$sail_internal

$ifndef _EMULATOR_MEMORY

$ifdef _DEFAULT_DEC
$include <vector_dec.sail>
$else
$include <vector_inc.sail>
$endif

//! Read memory
$ifdef SYMBOLIC
val read_mem# = monadic "read_mem" : forall ('a: Type) 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)
$else
val read_mem# : forall ('a: Type) 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)

val __read_mem# = monadic "emulator_read_mem" : forall 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    (int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)

function read_mem#(_, addrsize, addr, n) = __read_mem#(addrsize, addr, n)
$endif

//! Read memory, but signal to the emulator that this is an ifetch read
$ifdef SYMBOLIC
val read_mem_ifetch# = monadic "read_mem_ifetch" : forall ('a: Type) 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)
$else
val read_mem_ifetch# : forall ('a: Type) 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)

val __read_mem_ifetch# = monadic "emulator_read_mem_ifetch" : forall 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    (int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)

function read_mem_ifetch#(_, addrsize, addr, n) = __read_mem_ifetch#(addrsize, addr, n)
$endif

//! Read memory, and signal to the emulator that this read should be treated as an exclusive access
$ifdef SYMBOLIC
val read_mem_exclusive# = "read_mem_exclusive" : forall ('a: Type) 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)
$else
val read_mem_exclusive# : forall ('a: Type) 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)

val __read_mem_exclusive# = monadic "emulator_read_mem_exclusive" : forall 'n 'addrsize, 'n >= 0 & 'addrsize in {32, 64}.
    (int('addrsize), bits('addrsize), int('n)) -> bits(8 * 'n)

function read_mem_exclusive#(_, addrsize, addr, n) = __read_mem_exclusive#(addrsize, addr, n)
$endif

//! Write memory
$ifdef SYMBOLIC
val write_mem# = monadic "write_mem" : forall ('a: Type) 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool
$else
val write_mem# : forall ('a: Type) 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool

val __write_mem# = monadic "emulator_write_mem" : forall 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
    (int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool

function write_mem#(_, addrsize, addr, n, value) = __write_mem#(addrsize, addr, n, value)
$endif

//! Write memory, and signal to the emulator that this read should be treated as an exclusive access
val write_mem_exclusive# = monadic { isla: "write_mem_exclusive" } : forall ('a: Type) 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
    ('a, int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool

val __write_mem_exclusive# = monadic "emulator_write_mem_exclusive" : forall 'n 'addrsize, 'n > 0 & 'addrsize in {32, 64}.
    (int('addrsize), bits('addrsize), int('n), bits(8 * 'n)) -> bool

function write_mem_exclusive#(_, addrsize, addr, n, value) = __write_mem_exclusive#(addrsize, addr, n, value)

val read_tag# = monadic "read_tag_bool"  : forall 'addrsize, 'addrsize in {32, 64}. (int('addrsize), bits('addrsize)) -> bool

val write_tag# = monadic "write_tag_bool" : forall 'addrsize, 'addrsize in {32, 64}. (int('addrsize), bits('addrsize), bool) -> unit

$endif
