#!/bin/bash

OUT="_coqbuild_$1/main.v"

cat <<EOF > "$OUT"
From Sail Require Import State_monad State_lifting.
Require Import String.
Require Import List.
Import ListNotations.

Goal True.
EOF
if grep -q "Definition main '(tt : unit) : unit :=" "_coqbuild_$1/$1.v"; then
  cat <<EOF >> "$OUT"
let result := eval cbv in (main tt) in
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
    REGSTATE='tt'
  fi
  cat <<EOF >> "$OUT"
let result := eval cbv in (liftState register_accessors (main tt) (init_state $REGSTATE) default_choice) in
match result with
  | [(Value tt,_,_)] => idtac "OK"
  | [(Ex (Failure ?s),_,_)] => idtac "Fail:" s
  | _ => idtac "Fail (unexpected result):" result
end.
exact I.
Qed.
EOF
fi
