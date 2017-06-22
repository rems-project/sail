
val forall Nat 'n, Nat 'm. ([:'n + 20:], [:'m:]) -> [:'n + 20 + 'm:] effect pure plus

val forall Nat 'n, 'n >= 10. [:'n:] -> [:'n:] effect pure ten_id

val forall Nat 'N, 'N >= 63. [|10:'N|] -> [|10:'N|] effect pure branch

function forall Nat 'N, 'N >= 63. [|10:'N|] branch x = ten_id(plus(sizeof 'N, 1))
