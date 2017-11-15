default Order dec

register (bit[64]) GPR00 (* should never be read or written *)
register (bit[64]) GPR01
register (bit[64]) GPR02
register (bit[64]) GPR03
register (bit[64]) GPR04
register (bit[64]) GPR05
register (bit[64]) GPR06
register (bit[64]) GPR07
register (bit[64]) GPR08
register (bit[64]) GPR09
register (bit[64]) GPR10
register (bit[64]) GPR11
register (bit[64]) GPR12
register (bit[64]) GPR13
register (bit[64]) GPR14
register (bit[64]) GPR15
register (bit[64]) GPR16
register (bit[64]) GPR17
register (bit[64]) GPR18
register (bit[64]) GPR19
register (bit[64]) GPR20
register (bit[64]) GPR21
register (bit[64]) GPR22
register (bit[64]) GPR23
register (bit[64]) GPR24
register (bit[64]) GPR25
register (bit[64]) GPR26
register (bit[64]) GPR27
register (bit[64]) GPR28
register (bit[64]) GPR29
register (bit[64]) GPR30
register (bit[64]) GPR31

let (vector <0, 32, inc, (register<(bit[64])>) >) GPR =
  [ GPR00, GPR01, GPR02, GPR03, GPR04, GPR05, GPR06, GPR07, GPR08, GPR09, GPR10,
  GPR11, GPR12, GPR13, GPR14, GPR15, GPR16, GPR17, GPR18, GPR19, GPR20,
  GPR21, GPR22, GPR23, GPR24, GPR25, GPR26, GPR27, GPR28, GPR29, GPR30, GPR31
  ]

val forall Nat 'n, Nat 'l, Type 'a, 'l >= 0. (vector<'n,'l,dec,'a>, [|'n - 'l + 1:'n|]) -> 'a effect pure vector_access_dec
val forall Nat 'n, Nat 'l, Type 'a, 'l >= 0. (vector<'n,'l,inc,'a>, [|'n:'n + 'l - 1|]) -> 'a effect pure vector_access_inc

overload vector_access [vector_access_inc; vector_access_dec]

val forall Num 'n, Num 'm, Order 'ord. (vector<'n,'m,'ord,bit>, vector<'n,'m,'ord,bit>) -> bool effect pure eq_vec

overload (deinfix ==) [eq_vec]

val extern forall Num 'l, Num 'm. ([:'l:], [:'m:], int) -> vector<'l,'m,dec,bit> effect pure to_vec_dec

val cast forall Nat 'n, Nat 'l. [|0:1|] -> vector<'n,'l,dec,bit> effect pure cast_01_vec
function forall Num 'n, Num 'l. (vector<'n,'l,dec,bit>) cast_01_vec i = to_vec_dec (sizeof 'n, sizeof 'l, i)
val cast forall Nat 'n, Nat 'm, Order 'ord. vector<'n,'m,'ord,bit> -> [|0:2**'m - 1|] effect pure unsigned
val cast forall Type 'a. register<'a> -> 'a effect {rreg} reg_deref

val (bit[5], bit[64]) -> unit effect {wreg} wGPR

function unit wGPR (idx, v) =
{
  if idx == 0 then () else GPR[idx] := v
}

function unit test () =
{
  wGPR(0b00001) := 0
}
