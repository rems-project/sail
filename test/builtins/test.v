Require Import Sail2_state_monad.
Require Import Sail2_state_lifting.
Require Import String.
Require Import List.
Import ListNotations.

Goal True.
let result := eval cbv in (liftState register_accessors (main tt) (init_state tt)) in
match result with
  | [(Value tt,_)] => idtac "OK"
  | [(Ex (Failure ?s),_)] => idtac "Fail:" s
  | _ => idtac "Fail"
end.
exact I.
Qed.
