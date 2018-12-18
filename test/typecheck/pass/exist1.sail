let v1 : {|0, 1|} = 0

val test : bool -> {|0, 1|}

function test flag = if flag then 0 else 1

let v2 : range(0, 1) = test(true)

val add : forall 'a 'b. (atom('a), atom('b)) -> atom('a + 'b)

let v3 : {|3, 4|} = 3

let v4 : {'q, 'q in {0, 1}. atom('q + 3)} = v3

let v5 = add(test(true), 4)

let v6 : atom(4) = 4

val unit_fn : atom(4) -> unit

function unit_fn x : atom(4) = ()

val s_add : forall 'a. (atom('a), atom('a)) -> atom('a + 'a)

let v7 : {'k, 'k == 4. atom('k)} = 4

let v8 = s_add(v7, 4)
