
let (exist 'n, 'n in {0, 1}. [:'n:]) v1 = 0

val bool -> exist 'n, 'n in {0, 1}. [:'n:] effect pure test

function test flag =
{
  if flag then 0 else 1
}

let ([|0:1|]) v2 = test(true)

val forall 'a, 'b. ([:'a:], [:'b:]) -> [:'a + 'b:] effect pure add

let (exist 'k, 'k in {3, 4}. [:'k:]) v3 = 3

let (exist 'q, 'q in {0, 1}. [:'q + 3:]) v4 = v3

let v5 = add(test(true), 4)

let ([:4:]) v6 = 4

function unit unit_fn (([:4:]) x) = ()

val forall 'a. ([:'a:], [:'a:]) -> [:'a + 'a:] effect pure s_add

let (exist 'k, 'k = 4. [:'k:]) v7 = 4

(* let v8 = s_add(test(true), 4) *)

let (exist 'n, 0 = 0. [:'n:]) v9 = 100

let (int) v10 = v9

typedef Int = exist 'n, 0 = 0. [:'n:]

val int -> Int effect pure existential_int
val forall 'n, 'm. range<'n,'m> -> exist 'e, 'n <= 'e & 'e <= 'm. [:'e:] effect pure existential_range

overload existential [existential_int; existential_range]

let (exist 'n, 0 = 0. [:'n:]) v11 = existential(v10)

let (exist 'e, 0 <= 'e & 'e <= 3. [:'e:]) v12 = existential(([|0:3|]) 2)

let (Int) v13 = existential(v10)
