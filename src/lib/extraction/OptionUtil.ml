open List0

(** val is_none : 'a1 option -> bool **)

let is_none = function
| Some _ -> false
| None -> true

(** val is_some : 'a1 option -> bool **)

let is_some = function
| Some _ -> true
| None -> false

(** val option_bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

let option_bind o f =
  match o with
  | Some x -> f x
  | None -> None

(** val option_map2 :
    ('a1 -> 'a2 -> 'a3) -> 'a1 option -> 'a2 option -> 'a3 option **)

let option_map2 f o_UU2081_ o_UU2082_ =
  match o_UU2081_ with
  | Some x -> (match o_UU2082_ with
               | Some y -> Some (f x y)
               | None -> None)
  | None -> None

(** val option_join :
    ('a1 -> 'a1 -> 'a1) -> 'a1 option -> 'a1 option -> 'a1 option **)

let option_join f o_UU2081_ o_UU2082_ =
  match o_UU2081_ with
  | Some x -> (match o_UU2082_ with
               | Some y -> Some (f x y)
               | None -> Some x)
  | None -> o_UU2082_

(** val option_bind2 :
    ('a1 -> 'a1 -> 'a1 option) -> 'a1 option -> 'a1 option -> 'a1 option **)

let option_bind2 f o_UU2081_ o_UU2082_ =
  match o_UU2081_ with
  | Some x -> (match o_UU2082_ with
               | Some y -> f x y
               | None -> None)
  | None -> None

(** val option_all' :
    'a1 list option -> 'a1 option list -> 'a1 list option **)

let rec option_all' acc xs =
  match acc with
  | Some acc0 ->
    (match xs with
     | [] -> Some (rev acc0)
     | o :: xs0 ->
       (match o with
        | Some x -> option_all' (Some (x :: acc0)) xs0
        | None -> None))
  | None -> None

(** val option_all : 'a1 option list -> 'a1 list option **)

let option_all xs =
  option_all' (Some []) xs

(** val option_is : ('a1 -> bool) -> 'a1 option -> bool **)

let option_is f = function
| Some x -> f x
| None -> false
