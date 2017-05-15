typedef WordType = enumerate {B; H; W; D}

function forall Nat 'r, 'r IN {1,2,4,8}. [:'r:] wordWidthBytes((WordType) w) =
  switch(w) {
    case B -> 1
    case H -> 2
    case W -> 4
    case D -> 16
  }
