$include <smt.sail>
$include <flow.sail>
$include <arith.sail>
default Order dec
type bits ('n : Int) = bitvector('n, dec)
val operator & = "and_bool" : (bool, bool) -> bool
val eq_vec = {ocaml: "eq_list", lem: "eq_vec"} : forall 'n. (bits('n), bits('n)) -> bool
overload operator == = {eq_int, eq_vec}
val mult_int = {ocaml: "mult", lem: "integerMult"} : (int, int) -> int
overload operator * = {mult_range, mult_int, mult_real}
val replicate_bits = "replicate_bits" : forall 'n 'm. (bits('n), atom('m)) -> bits('n * 'm)
overload operator < = {lt_atom, lt_int}
val "extz_vec" : forall 'n 'm. (atom('m),bitvector('n, dec)) -> bitvector('m, dec) effect pure
val extzv : forall 'n 'm. (implicit('m), bitvector('n, dec)) -> bitvector('m, dec) effect pure
function extzv(m, v) = extz_vec(m,v)
val bitvector_concat = {ocaml: "append", lem: "concat_vec", c: "append"} : forall ('n : Int) ('m : Int).
  (bits('n), bits('m)) -> bits('n + 'm)
overload append = {bitvector_concat}
val bitvector_cast_in = "zeroExtend" : forall 'n. bits('n) -> bits('n) effect pure
val bitvector_cast_out = "zeroExtend" : forall 'n. bits('n) -> bits('n) effect pure
val bitvector_length = "length" : forall 'n. bits('n) -> atom('n)
overload length = {bitvector_length}
overload __size = {length}
val add_bits = {ocaml: "add_vec", lem: "add_vec"} : forall 'n. (bits('n), bits('n)) -> bits('n)
overload operator + = {add_bits}
val vector_update_subrange = {
  ocaml: "update_subrange",
  lem: "update_subrange_vec_dec"
} : forall 'n 'm 'o, 0 <= 'o <= 'm < 'n. (bits('n), atom('m), atom('o), bits('m - ('o - 1))) -> bits('n)


/* Test generation of casts across case splits (e.g., going from bits('m) to bits(32)) */

val foo : forall 'm 'n, 'm in {8,16} & 'n in {32,64}. (implicit('n), bits('m)) -> bits('n) effect pure

function foo(n, x) =
  let y : bits(16) = extzv(x) in
  match 'n {
    32 => y@y,
    64 => let z = y@y@y@y in let dfsf = 4 in z
  }

val foo_if : forall 'm 'n, 'm in {8,16} & 'n in {32,64}. (implicit('n), bits('m)) -> bits('n) effect pure

function foo_if(n, x) =
  let y : bits(16) = extzv(x) in
  if n == 32
  then y@y
  else /* 64 */ let z = y@y@y@y in let dfsf = 4 in z

val use : bits(16) -> unit effect pure

function use(x) = ()

val bar : forall 'n, 'n in {8,16}. bits('n) -> unit effect pure

function bar(x) =
  match 'n {
    8 => use(x@x),
   16 => use(x)
  }

val bar_if : forall 'n, 'n in {8,16}. bits('n) -> unit effect pure

function bar_if(x) =
  if 'n == 8
  then use(x@x)
  else /* 16 */ use(x)

val ret : forall 'm 'n, 'm in {8,16} & 'n in {32,64}. (implicit('n), bits('m)) -> bits('n) effect {undef}

function ret(n, x) =
  let y : bits(16) = extzv(x) in
  match 'n {
    32 => return y@y,
    64 => let z = y@y@y@y in { dfsf = 4; return z; undefined }
  }

val assign : forall 'm 'n, 'm in {8,16} & 'n in {32,64}. (implicit('n), bits('m)) -> bits('n) effect {undef}

function assign(n, x) = {
  let y : bits(16) = extzv(x);
  r : bits('n) = undefined;
  match 'n {
    32 => r = y@y,
    64 => { let z = y@y@y@y; let dfsf = 4; r = z }
  };
  r
}

val assign2 : forall 'm, 'm in {8,16}. bits('m) -> bits(32)

function assign2(x) = {
  y : bits('m) = x;
  r : bits(32) = 0x00000000;
  match 'm {
     8 => { y = y + 0x01; r = extzv(y) },
    16 => r = extzv(y)
  };
  r
}

val assign3 : forall 'm, 'm in {8,16}. bits('m) -> bits('m)

function assign3(x) = {
  y : bits('m) = x;
  match 'm {
    8 => y = y + 0x01,
   16 => y[7..0] = 0x89
  };
  y
}

/* Adding casts for top-level pattern matches */

val foo2 : forall 'm 'n, 'm in {8,16} & 'n in {32,64}. (atom('n), bits('m)) -> bits('n) effect pure

function foo2(32,x) =
  let y : bits(16) = extzv(x) in
  y@y
and foo2(64,x) =
  let y : bits(16) = extzv(x) in
  let z = y@y@y@y in let dfsf = 4 in z

val foo3 : forall 'm 'n, 'n in {4,8}. (atom('n), bits('m)) -> bits(8 * 'n) effect pure

function foo3(4,x) =
  let y : bits(16) = extzv(x) in
  y@y
and foo3(8,x) =
  let y : bits(16) = extzv(x) in
  let z = y@y@y@y in let dfsf = 4 in z

/* Casting an argument isn't supported yet 
val bar2 : forall 'n, 'n in {8,16}. (atom('n),bits('n)) -> unit effect pure

function bar2(8,x) =
  use(x@x)
and bar2(16,x) =
  use(x)
*/


val run : unit -> unit effect {escape,undef}

function run () = {
    bar(0x12);
    bar(0x3456);
    assert((ret(0x34) : bits(32)) == 0x00340034);
    assert((ret(0x34) : bits(64)) == 0x0034003400340034);
    assert((ret(0x3456) : bits(32)) == 0x34563456);
    assert((ret(0x3456) : bits(64)) == 0x3456345634563456);
    assert((assign(0x12) : bits(32)) == 0x00120012);
    assert((assign(0x1234) : bits(32)) == 0x12341234);
    assert((assign(0x12) : bits(64)) == 0x0012001200120012);
    assert((assign(0x1234) : bits(64)) == 0x1234123412341234);
    assert(assign2(0x12) == 0x00000013);
    assert(assign2(0x1234) == 0x00001234);
    assert(assign3(0x12) == 0x13);
    assert(assign3(0x1234) == 0x1289);
    assert(foo2(32,0x12) == 0x00120012);
    assert(foo2(64,0x12) == 0x0012001200120012);
    assert(foo3(4,0x12) == 0x00120012);
    assert(foo3(8,0x12) == 0x0012001200120012);
}
