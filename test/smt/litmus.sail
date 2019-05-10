default Order dec

$include <prelude.sail>
$include <regfp.sail>

register x0 : bits(32)
register x1 : bits(32)
register x2 : bits(32)
register x3 : bits(32)

function wX(r: bits(2), v: bits(32)) -> unit = {
  match r {
    0b00 => x0 = v,
    0b01 => x1 = v,
    0b10 => x2 = v,
    0b11 => x3 = v
  }
}

function rX(r: bits(2)) -> bits(32) = {
  match r {
    0b00 => x0,
    0b01 => x1,
    0b10 => x2,
    0b11 => x3
  }
}

overload X = {rX, wX}

scattered union ast

val execute : ast -> bool

union clause ast = LOAD : (bits(2), bits(2))

function clause execute(LOAD(rd, rs)) = {
  X(rd) = __read_mem(Read_plain, 32, X(rs), 4);
  true
}

union clause ast = STORE : (bits(2), bits(2))

function clause execute(STORE(rd, rs)) = {
  let addr = X(rd);
  __write_mem(Write_plain, 32, addr, 4, X(rs))
}

/*
RISCV LB
"PodRW Rfe PodRW Rfe"
Cycle=Rfe PodRW Rfe PodRW
Relax=PodRW
Safe=Rfe
Generator=diy7 (version 7.51+4(dev))
Prefetch=0:x=F,0:y=W,1:y=F,1:x=W
Com=Rf Rf
Orig=PodRW Rfe PodRW Rfe
{
0:x6=x; 0:x7=1; 0:x8=y;
1:x6=y; 1:x7=1; 1:x8=x;
}
 P0          | P1          ;
 lw x5,0(x6) | lw x5,0(x6) ;
 sw x7,0(x8) | sw x7,0(x8) ;
exists
(0:x5=1 /\ 1:x5=1)
*/

$property
function P0() -> bool = {
  let i1 = execute(LOAD(0b00, 0b01));
  let i2 = execute(STORE(0b10, 0b11));
  i1 & i2
}

$property
function P1() -> bool = {
  let i1 = execute(LOAD(0b00, 0b01));
  let i2 = execute(STORE(0b10, 0b11));
  i1 & i2
}
