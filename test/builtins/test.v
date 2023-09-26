From Sail Require Import State_monad State_lifting.
Require Import String.
Require Import List.
Import ListNotations.

Goal True.
let result := eval cbv in (liftState register_accessors (main tt) (init_state tt) default_choice) in
match result with
  | [(Value tt,_,_)] => idtac "OK"
  | [(Ex (Failure ?s),_,_)] => idtac "Fail:" s
  | _ => idtac "Fail (unexpected result):" result
end.
exact I.
Qed.
