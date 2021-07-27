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

struct name3 = {
  el: int
}

let name3 : int = 5

val use : unit -> int
function use(i) = {
  let x1 = name1(name3);
  let x2 : name1 = struct {el = x1};
  let x3 : name2 = struct {el = x2.el};
  let x4 : name3 = struct {el = x3.el};
  name2(x4.el)
}
