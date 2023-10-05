default Order dec
$include <prelude.sail>
$include <smt.sail>

val extzv : forall 'n 'm, 'm >= 0 & 'n >= 0. (implicit('m), bitvector('n, dec)) -> bitvector('m, dec) effect pure
function extzv(m, v) = sail_mask(m, v)


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

val ret : forall 'm 'n, 'm in {8,16} & 'n in {32,64}. (implicit('n), bits('m)) -> bits('n)

function ret(n, x) =
  let y : bits(16) = extzv(x) in
  match 'n {
    32 => return y@y,
    64 => let z = y@y@y@y in { dfsf = 4; return z; undefined }
  }

val assign : forall 'm 'n, 'm in {8,16} & 'n in {32,64}. (implicit('n), bits('m)) -> bits('n)

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

/* Test that matching on a variable which happens to fix a bitvector variable's
   size updates the environment properly. */

val assign4 : forall 'm, 'm in {1,2}. (implicit('m),bits(8*'m)) -> bits(8*'m)

function assign4(m,x) = {
  y : bits(8*'m) = x;
  match m {
    1 => y = y + 0x01,
    2 => y[7..0] = 0x89
  };
  y
}

/* The same as assign4, except with a distinct type variable. */

val assign5 : forall 'm 'n, 'm in {1,2} & 'n == 8 * 'm. (implicit('m),bits('n)) -> bits('n)

function assign5(m,x) = {
  y : bits('n) = x;
  match m {
    1 => y = y + 0x01,
    2 => y[7..0] = 0x89
  };
  y
}

/* Perform a check that resolves the size of a mutable variable, then use it.
   This doesn't actually need a cast in Lem (because the type system can't
   check the subrange), but the rewrite doesn't know that and the intermediate
   Sail representations wouldn't typecheck anyway.
*/

val refine_mutable_exp1 : forall 'n, 'n in {32,64}. (int('n), bits('n)) -> bits('n)

function refine_mutable_exp1(n, x) = {
  y : bits('n) = x;
  let z: bits(2) = if n > 36 then y[35..34] else y[7..6];
  y[1..0] = z;
  y
}

/* Similar, but forgetting the reason that the subrange is valid and having to
   assert it.
 */

val refine_mutable_exp2 : forall 'n, 'n in {32,64}. (int('n), bits('n)) -> bits('n)

function refine_mutable_exp2(n, x) = {
  y : bits('n) = x;
  let b : bool = n > 36;
  let z: bits(2) = if b then { assert('n > 36); y[35..34] } else y[7..6];
  y[1..0] = z;
  y
}

/* Adding casts for top-level pattern matches */

val foo2 : forall 'm 'n, 'm in {8,16} & 'n in {32,64}. (int('n), bits('m)) -> bits('n) effect pure

function foo2(32,x) =
  let y : bits(16) = extzv(x) in
  y@y
and foo2(64,x) =
  let y : bits(16) = extzv(x) in
  let z = y@y@y@y in let dfsf = 4 in z

val foo3 : forall 'm 'n, 'm >= 0 & 'n in {4,8}. (int('n), bits('m)) -> bits(8 * 'n) effect pure

function foo3(4,x) =
  let y : bits(16) = extzv(x) in
  y@y
and foo3(8,x) =
  let y : bits(16) = extzv(x) in
  let z = y@y@y@y in let dfsf = 4 in z

/* Casting an argument isn't supported yet 
val bar2 : forall 'n, 'n in {8,16}. (int('n),bits('n)) -> unit effect pure

function bar2(8,x) =
  use(x@x)
and bar2(16,x) =
  use(x)
*/


val run : unit -> unit

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
    assert(assign4(0x12) == 0x13);
    assert(assign4(0x1234) == 0x1289);
    assert(assign5(0x12) == 0x13);
    assert(assign5(0x1234) == 0x1289);
    assert(refine_mutable_exp1(32,0x12345678) == 0x12345679);
    assert(refine_mutable_exp1(64,0x12345678abcdef05) == 0x12345678ABCDEF06);
    assert(refine_mutable_exp2(32,0x12345678) == 0x12345679);
    assert(refine_mutable_exp2(64,0x12345678abcdef05) == 0x12345678ABCDEF06);
    assert(foo2(32,0x12) == 0x00120012);
    assert(foo2(64,0x12) == 0x0012001200120012);
    assert(foo3(4,0x12) == 0x00120012);
    assert(foo3(8,0x12) == 0x0012001200120012);
}
