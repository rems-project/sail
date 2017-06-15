
val forall Nat 'n, Nat 'm. ([:'n + 20:], [:'m:]) -> [:'n + 20 + 'm:] effect pure plus

val forall Nat 'n, 'n <= -10. [:'n:] -> [:'n:] effect pure minus_ten_id 

val forall Nat 'n, 'n >= 10. [:'n:] -> [:'n:] effect pure ten_id

val forall Nat 'N, 'N >= 63. [|10:'N|] -> [|10:'N|] effect pure branch

function forall Nat 'N, 'N >= 63. [|10:'N|] branch x =
{
  switch x {
    case ([|10:30|]) y -> y
    case ([:31:]) _ -> sizeof 'N
    case ([|31:40|]) _ -> plus(60,3)
  }
}
and branch (([|51:63|]) _) = ten_id(sizeof 'N)
