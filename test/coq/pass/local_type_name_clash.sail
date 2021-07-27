// Check behaviour when types and definitions have the same name

struct name1 = {
  el: int
}

val use1 : int -> int
function use1(i) = {
  let name1 = i;
  let x : name1 = struct {el = name1};
  x.el
}

val use2 : int -> int
function use2(name1) = {
  let x : name1 = struct {el = name1};
  x.el
}
