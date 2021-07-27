// Check behaviour when types and definitions have the same name

struct name1 = {
  el: int
}

val use1 : int -> int
function use1(i) = {
  let x : name1 = struct {el = i};
  x.el
}

val name1 : int -> int
function name1(i) = i

val use2 : int -> int
function use2(i) = {
  let x : name1 = struct {el = i};
  name1(x.el)
}

val name2 : int -> int
function name2(i) = i

val use3 : int -> int
function use3(i) = name2(i)

struct name2 = {
  el: int
}

val use : int -> int
function use(i) = {
  let x = name1(i);
  let y : name1 = struct {el = x};
  let z : name2 = struct {el = y.el};
  name2(z.el)
}
