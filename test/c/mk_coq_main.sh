#!/bin/bash

OUT="_coqbuild_$1/main.v"

cat <<EOF > "$OUT"
From SailStdpp Require Import State_monad State_lifting.
Require Import String.
Require Import List.
Import ListNotations.
Open Scope string.

Goal True.
EOF
if grep -q "Definition main '(tt : unit) : unit :=" "_coqbuild_$1/$1.v"; then
  cat <<EOF >> "$OUT"
let result := eval vm_compute in (main tt) in
match result with
| tt => idtac "OK"
| _ => idtac "Fail (unexpected result):" result
end.
exact I.
Qed.
EOF
else
  if grep -q 'initial_regstate' "_coqbuild_$1/$1.v"; then
    REGSTATE="initial_regstate"
  else
    REGSTATE='init_regstate'
  fi
  cat <<EOF >> "$OUT"
set (outerr := ltac:(
let result := eval vm_compute in (liftState register_accessors (main tt) (init_state $REGSTATE) default_choice) in
match result with
  | [(Value tt,?state,_)] => idtac "OK"; exact (state.(ss_output), "")
  | [(Ex (Failure ?s),?state,_)] => idtac "Fail:" s; exact (state.(ss_output), "Assertion failed: " ++ s)
  | _ => idtac "Fail (unexpected result):" result; exact ("","")
end)).
Redirect "output" (let t := eval vm_compute in (fst outerr) in idtac t).
Redirect "error" (let t := eval vm_compute in (snd outerr) in idtac t).
exact I.
Qed.
EOF
fi
