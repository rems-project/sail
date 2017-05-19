typedef WordType = enumerate { B; H; W; D}

function forall Nat 'r, 'r IN {1,2,4,8}. [:'r:] wordWidthBytes((WordType) w) =
  switch(w) {
    case B -> 1
    case H -> 2
    case W -> 4
    case D -> 8
  }

let alignment_width = 16

function (bool) isAddressAligned (addr, (WordType) wordType) =
  let a = unsigned(addr) in
  ((a quot alignment_width) == (a + wordWidthBytes(wordType) - 1) quot alignment_width)
