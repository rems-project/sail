default Order dec

typedef myunion = const union {
  (exist 'n, 'n in {8,16}. ([:'n:],bit['n])) MyConstr;
}

val bit[2] -> myunion effect pure make

function make(v) =
  (* Can't mention these below without running into exp/nexp parsing conflict! *)
  let eight = 8 in let sixteen = 16 in
  switch v {
    case 0b00 -> MyConstr( (  eight,  0x12) )
    case 0b01 -> MyConstr( (sixteen,0x1234) )
    case 0b10 -> MyConstr( (  eight,  0x56) )
    case 0b11 -> MyConstr( (sixteen,0x5678) )
  }

val myunion -> bit[32] effect pure use

function use(MyConstr('n)) = {
  switch n {
    case (n,v) -> extz(v)
  }
}
val unit -> bool effect pure run

function run () = {
  use(make(0b00)) == 0x00000012 &
  use(make(0b01)) == 0x00001234 &
  use(make(0b10)) == 0x00000056 &
  use(make(0b11)) == 0x00005678
}
