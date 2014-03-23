(* hack to display log messages. Syntax: LOG(0) := "log message"; *)
val extern forall Type 'a . nat -> 'a effect { wmem , rmem }  LOG

register (bit[1]) GPR0
register (bit[1]) GPR1

let (vector <0, 2, inc, (register<bit[1] >)>) GPR = [ GPR0, GPR1 ]

(* if we access GPR with a bit or a nat - doing the conversion in the
   caller, works as expected *)
function unit good ((bit)  RA ) =
{
  LOG(0) := "good";
  (nat) x := GPR[RA];
}

function unit good2 ((nat)  RA ) =
{
  LOG(0) := "good2";
  (nat) x := GPR[RA];
}

(* but here, the first to_num_inc(RA) somehow inhibits the cast,
   yielding to_num_inc(GPR0) instead of to_num_inc(0b0) *)
function unit bad ((bit[1])  RA ) =
{
  LOG(0) := "oldbad";
  (nat) x := GPR[RA];
}

(* and now, another bug - when DCR contains registers of bits instead of bit[0] *)

register (bit) DCR0
register (bit) DCR1

let (vector <0, 2, inc, (register<bit >)>) DCR = [ DCR0, DCR1 ]

(* also fails only when passing RA as a vector, nat and bit work fine as
   above;
   error message is different though, and very disturbing:
   "error: No matching patterns in case", corresponding to the DCR[RA]
   expression *)
function unit bad2 ((bit[1])  RA ) =
{
  LOG(0) := "oldbad2";
  (nat) x := DCR[RA];
}


function unit main () = {
  LOG(0) := "init";

  GPR[0] := 0b0;
  GPR[1] := 0b1;

  DCR[0] := bitzero;
  DCR[1] := bitone;

  good(bitzero);
  good2(0);

  (* a first bug *)
  bad(0b0);

  (* another bug :-) comment out first one to see it *)
  bad2(0b0);
}
