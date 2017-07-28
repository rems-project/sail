
register bool reg

let (exist 'n, 0 <= 'n & 'n <= 4. [:'n:]) A = 4

let ([|0:4|]) B = A

val unit -> exist 'n, 'n in {0, 1}. [:'n:] effect {rreg} test

function test () =
{
  if reg
  then 0
  else 1
}
