import List :: *;
import BitPat :: *;
import Recipe :: *;

typedef function Tuple2#(GCol#(ut), t1) f(t0 k) ContCore#(type ut, type t0, type t1);
typedef ContCore#(Bit#(0), t0, t1) Cont#(type t0, type t1);

function Bool getGuard(Guarded#(a) x) = x.guard;
function a getVal(Guarded#(a) x) = x.val;

function Recipe rCase(st subj, List#(function Guarded#(Recipe) f(st s)) ps);
  function Guarded#(Recipe) app (function Guarded#(Recipe) f(st s)) = f(subj);
  List#(Guarded#(Recipe)) rs = map(app, ps);
  return rOneMatch(map(getGuard, rs), map(getVal, rs), rAct(noAction));
endfunction

function Pat#(Maybe#(a), t0, t1) pat_Some(Pat#(a, t0, t1) p);
  function Cont#(t0, t1) k(Maybe#(a) s) =
    case (s) matches
      tagged Valid {.x0} : p(x0);
      .* : fail(p(?));
    endcase;
  return k;
endfunction

function Pat#(Maybe#(a), t0, t0) pat_None();
  function Cont#(t0, t0) k(Maybe#(a) s) =
    case (s) matches
      tagged Valid {.x0} : none(True);
      .* : none(False);
    endcase;
  return k;
endfunction

function Bool not(Bool b) = !b;
function Bool and(Bool a, Bool b) = (a && b);
function Bool eq(t a, t b) provisos (Eq#(t)) = (a == b);
function Bool neq(t a, t b) provisos (Eq#(t)) = (a /= b);
function Bit#(n) add_vec(Bit#(n) a, Bit#(n) b) = (a + b);
function Bit#(m) sign_extend(Bit#(n) a, t len) provisos (Add#(k, n, m)) = signExtend(a);
function Bit#(m) zzzero_extend(Bit#(n) a, t len) provisos (Add#(k, n, m)) = zeroExtend(a);
function Bit#(m) vector_subrange(Bit#(n) a, Integer hi, Integer lo) = a[lo:hi];
