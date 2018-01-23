default Order inc

val add_range = {ocaml: "add", lem: "integerAdd"}: forall ('n : Int) ('m : Int) ('o : Int) ('p : Int).
  (range('n, 'm), range('o, 'p)) -> range('n + 'o, 'm + 'p)

val sub_range = {ocaml: "sub", lem: "integerMinus"}: forall ('n : Int) ('m : Int) ('o : Int) ('p : Int).
  (range('n, 'm), range('o, 'p)) -> range('n - 'p, 'm - 'o)

val lt_range_atom = {ocaml: "lt", lem: "lt"}: forall ('n : Int) ('m : Int) ('o : Int).
  (range('n, 'm), atom('o)) -> bool

val lteq_range_atom = {ocaml: "lteq", lem: "lteq"}: forall ('n : Int) ('m : Int) ('o : Int).
  (range('n, 'm), atom('o)) -> bool

val gt_range_atom = {ocaml: "gt", lem: "gt"}: forall ('n : Int) ('m : Int) ('o : Int).
  (range('n, 'm), atom('o)) -> bool

val gteq_range_atom = {ocaml: "gteq", lem: "gteq"}: forall ('n : Int) ('m : Int) ('o : Int).
  (range('n, 'm), atom('o)) -> bool

val lt_atom_range = {ocaml: "lt", lem: "lt"}: forall ('n : Int) ('m : Int) ('o : Int).
  (atom('n), range('m, 'o)) -> bool

val lteq_atom_range = {ocaml: "lteq", lem: "lteq"}: forall ('n : Int) ('m : Int) ('o : Int).
  (atom('n), range('m, 'o)) -> bool

val gt_atom_range = {ocaml: "gt", lem: "gt"}: forall ('n : Int) ('m : Int) ('o : Int).
  (atom('n), range('m, 'o)) -> bool

val gteq_atom_range = {ocaml: "gteq", lem: "gteq"}: forall ('n : Int) ('m : Int) ('o : Int).
  (atom('n), range('m, 'o)) -> bool

overload operator + = {add_range}

overload operator - = {sub_range}

overload operator < = {lt_atom_range, lt_range_atom}

overload operator <= = {lteq_atom_range, lteq_range_atom}

overload operator > = {gt_atom_range, gt_range_atom}

overload operator >= = {gteq_atom_range, gteq_range_atom}

val branch : range(0, 63) -> range(0, 63)

function branch x = if x > 31 then x - 32 else x + 32
