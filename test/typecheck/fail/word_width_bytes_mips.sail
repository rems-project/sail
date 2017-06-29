typedef WordType = enumerate {B; H; W; D}

(* This fails because it's not true for all combinations of 'r and WordType *)
(* Needs existential types, i.e. return type should be exists Nat 'r, 'r in {1,2,4,8}. [:'r:] *)
function forall Nat 'r, 'r IN {1,2,4,8}. wordWidthBytes((WordType) w) =
  switch(w) {
    case B -> 1
    case H -> 2
    case W -> 4
    case D -> 8
  }
