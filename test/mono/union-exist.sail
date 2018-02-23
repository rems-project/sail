default Order dec
type bits ('n : Int) = vector('n, dec, bit)
val operator & = "and_bool" : (bool, bool) -> bool
val eq_vec = {ocaml: "eq_list", lem: "eq_vec"} : forall 'n. (bits('n), bits('n)) -> bool
val eq_int = {ocaml: "eq_int", lem: "eq"} : (int, int) -> bool
overload operator == = {eq_int, eq_vec}
val vector_subrange = {ocaml: "subrange", lem: "subrange_vec_dec"} : forall ('n : Int) ('m : Int) ('o : Int), 'o <= 'm <= 'n.
  (bits('n), atom('m), atom('o)) -> bits('m - ('o - 1))


union myunion = {
  MyConstr : {'n, 'n in {8,16}. (atom('n),bits('n))}
}

val make : bits(2) -> myunion

function make(v) =
  /* Can't mention these below without running into exp/nexp parsing conflict! */
  let eight = 8 in let sixteen = 16 in
  let r : {'n, 'n in {8,16}. (atom('n),bits('n))} = match v {
    0b00 => (  eight,  0x12),
    0b01 => (sixteen,0x1234),
    0b10 => (  eight,  0x56),
    0b11 => (sixteen,0x5678)
  } in MyConstr(r)

val use : myunion -> bits(32)

function use(MyConstr((n,v) as (atom('n),bits('n)))) = extz(v)

val run : unit -> unit effect {escape}

function run () = {
  assert(use(make(0b00)) == 0x00000012);
  assert(use(make(0b01)) == 0x00001234);
  assert(use(make(0b10)) == 0x00000056);
  assert(use(make(0b11)) == 0x00005678);
}
