default Nat 'i
default Order 'o
default bool b
default forall 'a. list<'a> b
val forall 'a, 'b . ('a * 'b) -> 'b effect pure snd
val forall Type 'i, 'b. ('i * 'b) -> 'i effect pure fst
typedef int_list [name = "il"] = list<nat>
typedef reco = const struct forall 'i, 'a, 'b. { 'a['i] v; 'b w; }
typedef maybe = const union forall 'a. { Nne; 'a Sme; }
typedef colors = enumerate { red; green; blue }
typedef creg = register bits [5:10] { 5 : h ; 6..7 : j}
let bool e = true
let bit v = bitzero
let ( bit [ 32 ] ) v1 = 0b101

(* scattered function definition and union definition *)
scattered typedef ast = const union
scattered function ast f

union ast member  bit * bit * bit A
function clause f (  A (a,b,c) ) = C(a)

union ast member  bit * bit B
function clause f (  B (a,b) ) = C(a)

union ast member  bit C
function clause f (  C (a) ) = C(a)

end ast
end f

function bit sw s = switch s { case 0 -> bitzero }

function bit main _ = {ignore(sw(0)); v1[0] }

