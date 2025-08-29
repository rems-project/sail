open Specif

(** val coq_Fix_F_sub :
    ('a1 -> ('a1 coq_sig -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let rec coq_Fix_F_sub f_sub x =
  f_sub x (fun y -> coq_Fix_F_sub f_sub (let Coq_exist a = y in a))

(** val coq_Fix_sub : ('a1 -> ('a1 coq_sig -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

let coq_Fix_sub =
  coq_Fix_F_sub
