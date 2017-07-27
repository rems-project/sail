typedef ty = list<(bit[8])>

function bool foo ((ty) l) =
  switch l {
    case _ :: _ -> false
    case _ -> true
  }