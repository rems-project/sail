$include <smt.sail>
$include <flow.sail>
default Order dec
type bits ('n : Int) = vector('n, dec, bit)
val operator & = "and_bool" : (bool, bool) -> bool
val eq_vec = {ocaml: "eq_list", lem: "eq_vec"} : forall 'n. (bits('n), bits('n)) -> bool
overload operator == = {eq_int, eq_vec}
val mult_int = {ocaml: "mult", lem: "integerMult"} : (int, int) -> int
overload operator * = {mult_range, mult_int, mult_real}
val replicate_bits = "replicate_bits" : forall 'n 'm. (bits('n), atom('m)) -> bits('n * 'm)
overload operator < = {lt_atom, lt_int}
val "extz_vec" : forall 'n 'm. (atom('m),vector('n, dec, bit)) -> vector('m, dec, bit) effect pure
val extzv : forall 'n 'm. vector('n, dec, bit) -> vector('m, dec, bit) effect pure
function extzv(v) = extz_vec(sizeof('m),v)
val bitvector_concat = {ocaml: "append", lem: "concat_vec", c: "append"} : forall ('n : Int) ('m : Int).
  (bits('n), bits('m)) -> bits('n + 'm)
overload append = {bitvector_concat}
val bitvector_cast_in = "zeroExtend" : forall 'n. bits('n) -> bits('n) effect pure
val bitvector_cast_out = "zeroExtend" : forall 'n. bits('n) -> bits('n) effect pure
val bitvector_length = "length" : forall 'n. bits('n) -> atom('n)
overload length = {bitvector_length}

/* Test generation of casts across case splits (e.g., going from bits('m) to bits(32)) */

val foo : forall 'm 'n, 'm in {8,16} & 'n in {32,64}. bits('m) -> bits('n) effect pure

function foo(x) =
  let y : bits(16) = extzv(x) in
  match 'n {
    32 => y@y,
    64 => let z = y@y@y@y in let dfsf = 4 in z
  }

val use : bits(16) -> unit effect pure

function use(x) = ()

val bar : forall 'n, 'n in {8,16}. bits('n) -> unit effect pure

function bar(x) =
  match 'n {
    8 => use(x@x),
   16 => use(x)
  }

val ret : forall 'm 'n, 'm in {8,16} & 'n in {32,64}. bits('m) -> bits('n) effect {undef}

function ret(x) =
  let y : bits(16) = extzv(x) in
  match 'n {
    32 => return y@y,
    64 => let z = y@y@y@y in { dfsf = 4; return z; undefined }
  }

/* TODO: Assignments need more plumbing

val assign : forall 'm 'n, 'm in {8,16} & 'n in {32,64}. bits('m) -> bits('n) effect {undef}

function assign(x) = {
  let y : bits(16) = extzv(x);
  r : bits('n) = undefined;
  match 'n {
    32 => r = y@y,
    64 => { let z = y@y@y@y; let dfsf = 4; r = z }
  };
  r
}
*/

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
/*    assert((assign(0x12) : bits(32)) == 0x00120012);
    assert((assign(0x1234) : bits(32)) == 0x12341234);
    assert((assign(0x12) : bits(64)) == 0x0012001200120012);
    assert((assign(0x1234) : bits(64)) == 0x1234123412341234);*/
    assert(foo2(32,0x12) == 0x00120012);
    assert(foo2(64,0x12) == 0x0012001200120012);
    assert(foo3(4,0x12) == 0x00120012);
    assert(foo3(8,0x12) == 0x0012001200120012);
}