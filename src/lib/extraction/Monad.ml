[@@@warning "-a"]
open Ast
open Datatypes

type ('v, 'c, 'p, 'a) t =
| Pure of 'a
| Early_return of 'v
| Exit of 'v
| Exception of 'v
| Runtime_type_error of Parse_ast.l
| Match_failure of Parse_ast.l
| Assertion_failed of string
| Call of id * 'v list * ('c -> ('v, 'c, 'p, 'a) t)
| Read_var of 'p * ('v -> ('v, 'c, 'p, 'a) t)
| Write_var of 'p * 'v * (unit -> ('v, 'c, 'p, 'a) t)
| Get_config of Parse_ast.l * string list * typ * ('v -> ('v, 'c, 'p, 'a) t)
| Get_undefined of Parse_ast.l * typ * ('v -> ('v, 'c, 'p, 'a) t)

(** val bind :
    ('a1, 'a2, 'a3, 'a4) t -> ('a4 -> ('a1, 'a2, 'a3, 'a5) t) -> ('a1, 'a2,
    'a3, 'a5) t **)

let rec bind m f =
  match m with
  | Pure x -> f x
  | Early_return v -> Early_return v
  | Exit v -> Exit v
  | Exception v -> Exception v
  | Runtime_type_error l -> Runtime_type_error l
  | Match_failure l -> Match_failure l
  | Assertion_failed msg -> Assertion_failed msg
  | Call (id0, args, cont) -> Call (id0, args, (fun v -> bind (cont v) f))
  | Read_var (r, cont) -> Read_var (r, (fun v -> bind (cont v) f))
  | Write_var (r, v, cont) -> Write_var (r, v, (fun u -> bind (cont u) f))
  | Get_config (l, key, t0, cont) ->
    Get_config (l, key, t0, (fun v -> bind (cont v) f))
  | Get_undefined (l, t0, cont) ->
    Get_undefined (l, t0, (fun v -> bind (cont v) f))

(** val fmap :
    ('a4 -> 'a5) -> ('a1, 'a2, 'a3, 'a4) t -> ('a1, 'a2, 'a3, 'a5) t **)

let rec fmap f = function
| Pure x -> Pure (f x)
| Early_return v -> Early_return v
| Exit v -> Exit v
| Exception v -> Exception v
| Runtime_type_error l -> Runtime_type_error l
| Match_failure l -> Match_failure l
| Assertion_failed msg -> Assertion_failed msg
| Call (id0, args, cont) -> Call (id0, args, (fun v -> fmap f (cont v)))
| Read_var (r, cont) -> Read_var (r, (fun v -> fmap f (cont v)))
| Write_var (r, v, cont) -> Write_var (r, v, (fun u -> fmap f (cont u)))
| Get_config (l, key, t0, cont) ->
  Get_config (l, key, t0, (fun v -> fmap f (cont v)))
| Get_undefined (l, t0, cont) ->
  Get_undefined (l, t0, (fun v -> fmap f (cont v)))

(** val pure : 'a4 -> ('a1, 'a2, 'a3, 'a4) t **)

let pure x =
  Pure x

(** val lift_option : Parse_ast.l -> 'a4 option -> ('a1, 'a2, 'a3, 'a4) t **)

let lift_option l = function
| Some y -> Pure y
| None -> Runtime_type_error l

(** val lift_sum : (Parse_ast.l, 'a4) sum -> ('a1, 'a2, 'a3, 'a4) t **)

let lift_sum = function
| Coq_inl l -> Runtime_type_error l
| Coq_inr r -> Pure r

(** val sequence :
    ('a1, 'a2, 'a3, 'a4) t list -> ('a1, 'a2, 'a3, 'a4 list) t **)

let rec sequence = function
| [] -> pure []
| m :: ms -> bind m (fun x -> bind (sequence ms) (fun xs -> pure (x :: xs)))

(** val get_config :
    Parse_ast.l -> string list -> typ -> ('a1, 'a2, 'a3, 'a1) t **)

let get_config l key typ0 =
  Get_config (l, key, typ0, pure)

(** val get_undefined : Parse_ast.l -> typ -> ('a1, 'a2, 'a3, 'a1) t **)

let get_undefined l typ0 =
  Get_undefined (l, typ0, pure)

(** val throw : 'a1 -> ('a1, 'a2, 'a3, 'a4) t **)

let throw v =
  Exception v

type ('v, 'a) caught =
| Continue of 'a
| Caught of 'v

(** val catch :
    ('a1, 'a2, 'a3, 'a4) t -> ('a1, 'a2, 'a3, ('a1, 'a4) caught) t **)

let catch = function
| Pure x -> Pure (Continue x)
| Early_return v -> Early_return v
| Exit v -> Exit v
| Exception v -> Pure (Caught v)
| Runtime_type_error l -> Runtime_type_error l
| Match_failure l -> Match_failure l
| Assertion_failed msg -> Assertion_failed msg
| Call (id0, args, cont) ->
  Call (id0, args, (fun v -> fmap (fun x -> Continue x) (cont v)))
| Read_var (r, cont) ->
  Read_var (r, (fun v -> fmap (fun x -> Continue x) (cont v)))
| Write_var (r, v, cont) ->
  Write_var (r, v, (fun _ -> fmap (fun x -> Continue x) (cont ())))
| Get_config (l, key, t0, cont) ->
  Get_config (l, key, t0, (fun v -> fmap (fun x -> Continue x) (cont v)))
| Get_undefined (l, t0, cont) ->
  Get_undefined (l, t0, (fun v -> fmap (fun x -> Continue x) (cont v)))
