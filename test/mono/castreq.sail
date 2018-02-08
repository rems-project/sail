
val foo : forall 'm 'n, 'm in {8,16} & 'n in {32,64}. bits('m) -> bits('n) effect pure

function foo(x) =
  let y : bits(16) = extzv(x) in
  match 'n {
    32 => y@y,
    64 => let z = y@y@y@y in let dfsf = 4 in z
  }

val use : bits(16) -> unit effect pure

function use(x) = ()

val bar : forall 'n, 'n in {8,16}. bits('n) -> unit effect pure

function bar(x) =
  match 'n {
    8 => use(x@x),
   16 => use(x)
  }

val ret : forall 'm 'n, 'm in {8,16} & 'n in {32,64}. bits('m) -> bits('n) effect {undef}

function ret(x) =
  let y : bits(16) = extzv(x) in
  match 'n {
    32 => return y@y,
    64 => let z = y@y@y@y in { dfsf = 4; return z; undefined }
  }

val assign : forall 'm 'n, 'm in {8,16} & 'n in {32,64}. bits('m) -> bits('n) effect {undef}

function assign(x) = {
  let y : bits(16) = extzv(x);
  r : bits('n) = undefined;
  match 'n {
    32 => r = y@y,
    64 => { let z = y@y@y@y; let dfsf = 4; r = z }
  };
  r
}


val foo2 : forall 'm 'n, 'm in {8,16} & 'n in {32,64}. (atom('n), bits('m)) -> bits('n) effect pure

function foo2(32,x) =
  let y : bits(16) = extzv(x) in
  y@y
and foo2(64,x) =
  let y : bits(16) = extzv(x) in
  let z = y@y@y@y in let dfsf = 4 in z

val bar2 : forall 'n, 'n in {8,16}. (atom('n),bits('n)) -> unit effect pure

function bar2(8,x) =
  use(x@x)
and bar2(16,x) =
  use(x)


