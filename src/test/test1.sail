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
typedef creg = register bits [5:'i] { 5 : h ; 6..7 : j}
let bool e = true

function unit main _ = ()