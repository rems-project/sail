(* Check case splitting on a vector *)

default Order dec

val bit[32] -> nat effect pure test

function nat test((bit[2]) sel : (bit[30]) _) = {
  switch (sel) {
    case 0b00 -> 5
    case 0b10 -> 1
    case _ -> 0
  }
}

val unit -> bool effect pure run

function run () = {
  test(0x0f353533) == 5 &
  test(0x84534656) == 1 &
  test(0xf3463903) == 0
}
