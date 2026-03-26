open Datatypes
open Base
open Countable
open Decidable
open Mapset
open Numbers
open Option

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'a gmap_dep_ne =
| GNode001 of 'a gmap_dep_ne
| GNode010 of 'a
| GNode011 of 'a * 'a gmap_dep_ne
| GNode100 of 'a gmap_dep_ne
| GNode101 of 'a gmap_dep_ne * 'a gmap_dep_ne
| GNode110 of 'a gmap_dep_ne * 'a
| GNode111 of 'a gmap_dep_ne * 'a * 'a gmap_dep_ne

type 'a gmap_dep =
| GEmpty
| GNodes of 'a gmap_dep_ne

type ('k, 'a) gmap = { gmap_car : 'a gmap_dep }

(** val gmap_dep_ne_eq_dec :
    ('a1, 'a1) coq_RelDecision -> ('a1 gmap_dep_ne, 'a1 gmap_dep_ne)
    coq_RelDecision **)

let rec gmap_dep_ne_eq_dec x t1 t2 =
  match t1 with
  | GNode001 r1 ->
    (match t2 with
     | GNode001 r2 -> gmap_dep_ne_eq_dec x r1 r2
     | _ -> false)
  | GNode010 x1 ->
    (match t2 with
     | GNode010 x2 -> decide (decide_rel x x1 x2)
     | _ -> false)
  | GNode011 (x1, r1) ->
    (match t2 with
     | GNode011 (x2, r2) ->
       if decide (decide_rel x x1 x2)
       then gmap_dep_ne_eq_dec x r1 r2
       else false
     | _ -> false)
  | GNode100 l1 ->
    (match t2 with
     | GNode100 l2 -> gmap_dep_ne_eq_dec x l1 l2
     | _ -> false)
  | GNode101 (l1, r1) ->
    (match t2 with
     | GNode101 (l2, r2) ->
       if gmap_dep_ne_eq_dec x l1 l2
       then gmap_dep_ne_eq_dec x r1 r2
       else false
     | _ -> false)
  | GNode110 (l1, x1) ->
    (match t2 with
     | GNode110 (l2, x2) ->
       if gmap_dep_ne_eq_dec x l1 l2
       then decide (decide_rel x x1 x2)
       else false
     | _ -> false)
  | GNode111 (l1, x1, r1) ->
    (match t2 with
     | GNode111 (l2, x2, r2) ->
       if gmap_dep_ne_eq_dec x l1 l2
       then if decide (decide_rel x x1 x2)
            then gmap_dep_ne_eq_dec x r1 r2
            else false
       else false
     | _ -> false)

(** val gmap_dep_eq_dec :
    ('a1, 'a1) coq_RelDecision -> ('a1 gmap_dep, 'a1 gmap_dep) coq_RelDecision **)

let gmap_dep_eq_dec x x0 y =
  match x0 with
  | GEmpty -> (match y with
               | GEmpty -> true
               | GNodes _ -> false)
  | GNodes g ->
    (match y with
     | GEmpty -> false
     | GNodes g0 -> decide_rel (gmap_dep_ne_eq_dec x) g g0)

(** val gmap_eq_dec :
    ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a2, 'a2)
    coq_RelDecision -> (('a1, 'a2) gmap, ('a1, 'a2) gmap) coq_RelDecision **)

let gmap_eq_dec _ _ x x0 y =
  let { gmap_car = gmap_car0 } = x0 in
  let { gmap_car = gmap_car1 } = y in
  decide_rel (gmap_dep_eq_dec x) gmap_car0 gmap_car1

(** val coq_GNode :
    'a1 gmap_dep -> (__ * 'a1) option -> 'a1 gmap_dep -> 'a1 gmap_dep **)

let coq_GNode ml mx mr =
  match ml with
  | GEmpty ->
    (match mx with
     | Some p0 ->
       let (_, x) = p0 in
       (match mr with
        | GEmpty -> GNodes (GNode010 x)
        | GNodes r -> GNodes (GNode011 (x, r)))
     | None ->
       (match mr with
        | GEmpty -> GEmpty
        | GNodes r -> GNodes (GNode001 r)))
  | GNodes l ->
    (match mx with
     | Some p0 ->
       let (_, x) = p0 in
       (match mr with
        | GEmpty -> GNodes (GNode110 (l, x))
        | GNodes r -> GNodes (GNode111 (l, x, r)))
     | None ->
       (match mr with
        | GEmpty -> GNodes (GNode100 l)
        | GNodes r -> GNodes (GNode101 (l, r))))

(** val gmap_dep_ne_case :
    'a1 gmap_dep_ne -> ('a1 gmap_dep -> (__ * 'a1) option -> 'a1 gmap_dep ->
    'a2) -> 'a2 **)

let gmap_dep_ne_case t f =
  match t with
  | GNode001 r -> f GEmpty None (GNodes r)
  | GNode010 x -> f GEmpty (Some (__, x)) GEmpty
  | GNode011 (x, r) -> f GEmpty (Some (__, x)) (GNodes r)
  | GNode100 l -> f (GNodes l) None GEmpty
  | GNode101 (l, r) -> f (GNodes l) None (GNodes r)
  | GNode110 (l, x) -> f (GNodes l) (Some (__, x)) GEmpty
  | GNode111 (l, x, r) -> f (GNodes l) (Some (__, x)) (GNodes r)

(** val gmap_dep_ne_lookup :
    Big_int_Z.big_int -> 'a1 gmap_dep_ne -> 'a1 option **)

let rec gmap_dep_ne_lookup i = function
| GNode001 r ->
  ((fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
     (fun i0 -> gmap_dep_ne_lookup i0 r)
     (fun _ -> None)
     (fun _ -> None)
     i)
| GNode010 x ->
  ((fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
     (fun _ -> None)
     (fun _ -> None)
     (fun _ -> Some x)
     i)
| GNode011 (x, r) ->
  ((fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
     (fun i0 -> gmap_dep_ne_lookup i0 r)
     (fun _ -> None)
     (fun _ -> Some x)
     i)
| GNode100 l ->
  ((fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
     (fun _ -> None)
     (fun i0 -> gmap_dep_ne_lookup i0 l)
     (fun _ -> None)
     i)
| GNode101 (l, r) ->
  ((fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
     (fun i0 -> gmap_dep_ne_lookup i0 r)
     (fun i0 -> gmap_dep_ne_lookup i0 l)
     (fun _ -> None)
     i)
| GNode110 (l, x) ->
  ((fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
     (fun _ -> None)
     (fun i0 -> gmap_dep_ne_lookup i0 l)
     (fun _ -> Some x)
     i)
| GNode111 (l, x, r) ->
  ((fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
     (fun i0 -> gmap_dep_ne_lookup i0 r)
     (fun i0 -> gmap_dep_ne_lookup i0 l)
     (fun _ -> Some x)
     i)

(** val gmap_dep_lookup : Big_int_Z.big_int -> 'a1 gmap_dep -> 'a1 option **)

let gmap_dep_lookup i = function
| GEmpty -> None
| GNodes t -> gmap_dep_ne_lookup i t

(** val gmap_lookup :
    ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a1, 'a2, ('a1, 'a2)
    gmap) coq_Lookup **)

let gmap_lookup _ h k mt =
  gmap_dep_lookup (h.encode k) mt.gmap_car

(** val gmap_empty :
    ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a1, 'a2) gmap
    coq_Empty **)

let gmap_empty _ _ =
  { gmap_car = GEmpty }

(** val gmap_dep_ne_singleton :
    Big_int_Z.big_int -> 'a1 -> 'a1 gmap_dep_ne **)

let rec gmap_dep_ne_singleton i x =
  (fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
    (fun i0 -> GNode001 (gmap_dep_ne_singleton i0 x))
    (fun i0 -> GNode100 (gmap_dep_ne_singleton i0 x))
    (fun _ -> GNode010 x)
    i

(** val gmap_partial_alter_aux :
    (Big_int_Z.big_int -> __ -> 'a1 gmap_dep_ne -> 'a1 gmap_dep) -> ('a1
    option -> 'a1 option) -> Big_int_Z.big_int -> 'a1 gmap_dep -> 'a1 gmap_dep **)

let gmap_partial_alter_aux go f i = function
| GEmpty ->
  (match f None with
   | Some x -> GNodes (gmap_dep_ne_singleton i x)
   | None -> GEmpty)
| GNodes t -> go i __ t

(** val gmap_dep_ne_partial_alter :
    ('a1 option -> 'a1 option) -> Big_int_Z.big_int -> 'a1 gmap_dep_ne -> 'a1
    gmap_dep **)

let rec gmap_dep_ne_partial_alter f i = function
| GNode001 r ->
  ((fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
     (fun i0 ->
     match gmap_dep_ne_partial_alter f i0 r with
     | GEmpty -> GEmpty
     | GNodes r0 -> GNodes (GNode001 r0))
     (fun i0 ->
     match f None with
     | Some x0 ->
       let l = gmap_dep_ne_singleton i0 x0 in GNodes (GNode101 (l, r))
     | None -> GNodes (GNode001 r))
     (fun _ ->
     match f None with
     | Some a ->
       let p0 = (__, a) in let (_, x0) = p0 in GNodes (GNode011 (x0, r))
     | None -> GNodes (GNode001 r))
     i)
| GNode010 x0 ->
  ((fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
     (fun i0 ->
     match f None with
     | Some x1 ->
       let r = gmap_dep_ne_singleton i0 x1 in GNodes (GNode011 (x0, r))
     | None -> GNodes (GNode010 x0))
     (fun i0 ->
     match f None with
     | Some x1 ->
       let l = gmap_dep_ne_singleton i0 x1 in GNodes (GNode110 (l, x0))
     | None -> GNodes (GNode010 x0))
     (fun _ ->
     match f (Some x0) with
     | Some a -> let p0 = (__, a) in let (_, x1) = p0 in GNodes (GNode010 x1)
     | None -> GEmpty)
     i)
| GNode011 (x0, r) ->
  ((fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
     (fun i0 ->
     match gmap_dep_ne_partial_alter f i0 r with
     | GEmpty -> GNodes (GNode010 x0)
     | GNodes r0 -> GNodes (GNode011 (x0, r0)))
     (fun i0 ->
     match f None with
     | Some x1 ->
       let l = gmap_dep_ne_singleton i0 x1 in GNodes (GNode111 (l, x0, r))
     | None -> GNodes (GNode011 (x0, r)))
     (fun _ ->
     match f (Some x0) with
     | Some a ->
       let p0 = (__, a) in let (_, x1) = p0 in GNodes (GNode011 (x1, r))
     | None -> GNodes (GNode001 r))
     i)
| GNode100 l ->
  ((fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
     (fun i0 ->
     match f None with
     | Some x0 ->
       let r = gmap_dep_ne_singleton i0 x0 in GNodes (GNode101 (l, r))
     | None -> GNodes (GNode100 l))
     (fun i0 ->
     match gmap_dep_ne_partial_alter f i0 l with
     | GEmpty -> GEmpty
     | GNodes l0 -> GNodes (GNode100 l0))
     (fun _ ->
     match f None with
     | Some a ->
       let p0 = (__, a) in let (_, x0) = p0 in GNodes (GNode110 (l, x0))
     | None -> GNodes (GNode100 l))
     i)
| GNode101 (l, r) ->
  ((fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
     (fun i0 ->
     match gmap_dep_ne_partial_alter f i0 r with
     | GEmpty -> GNodes (GNode100 l)
     | GNodes r0 -> GNodes (GNode101 (l, r0)))
     (fun i0 ->
     match gmap_dep_ne_partial_alter f i0 l with
     | GEmpty -> GNodes (GNode001 r)
     | GNodes l0 -> GNodes (GNode101 (l0, r)))
     (fun _ ->
     match f None with
     | Some a ->
       let p0 = (__, a) in let (_, x0) = p0 in GNodes (GNode111 (l, x0, r))
     | None -> GNodes (GNode101 (l, r)))
     i)
| GNode110 (l, x0) ->
  ((fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
     (fun i0 ->
     match f None with
     | Some x1 ->
       let r = gmap_dep_ne_singleton i0 x1 in GNodes (GNode111 (l, x0, r))
     | None -> GNodes (GNode110 (l, x0)))
     (fun i0 ->
     match gmap_dep_ne_partial_alter f i0 l with
     | GEmpty -> GNodes (GNode010 x0)
     | GNodes l0 -> GNodes (GNode110 (l0, x0)))
     (fun _ ->
     match f (Some x0) with
     | Some a ->
       let p0 = (__, a) in let (_, x1) = p0 in GNodes (GNode110 (l, x1))
     | None -> GNodes (GNode100 l))
     i)
| GNode111 (l, x0, r) ->
  ((fun f2p1 f2p f1 p ->
  if Big_int_Z.le_big_int p Big_int_Z.unit_big_int then f1 () else
  let (q,r) = Big_int_Z.quomod_big_int p (Big_int_Z.big_int_of_int 2) in
  if Big_int_Z.eq_big_int r Big_int_Z.zero_big_int then f2p q else f2p1 q)
     (fun i0 ->
     match gmap_dep_ne_partial_alter f i0 r with
     | GEmpty -> GNodes (GNode110 (l, x0))
     | GNodes r0 -> GNodes (GNode111 (l, x0, r0)))
     (fun i0 ->
     match gmap_dep_ne_partial_alter f i0 l with
     | GEmpty -> GNodes (GNode011 (x0, r))
     | GNodes l0 -> GNodes (GNode111 (l0, x0, r)))
     (fun _ ->
     match f (Some x0) with
     | Some a ->
       let p0 = (__, a) in let (_, x1) = p0 in GNodes (GNode111 (l, x1, r))
     | None -> GNodes (GNode101 (l, r)))
     i)

(** val gmap_dep_partial_alter :
    ('a1 option -> 'a1 option) -> Big_int_Z.big_int -> 'a1 gmap_dep -> 'a1
    gmap_dep **)

let gmap_dep_partial_alter f i x =
  gmap_partial_alter_aux (fun x0 _ -> gmap_dep_ne_partial_alter f x0) f i x

(** val gmap_partial_alter :
    ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a1, 'a2, ('a1, 'a2)
    gmap) coq_PartialAlter **)

let gmap_partial_alter _ h f k pat =
  let { gmap_car = mt } = pat in
  { gmap_car = (gmap_dep_partial_alter f (h.encode k) mt) }

(** val gmap_dep_ne_fmap :
    ('a1 -> 'a2) -> 'a1 gmap_dep_ne -> 'a2 gmap_dep_ne **)

let rec gmap_dep_ne_fmap f = function
| GNode001 r -> GNode001 (gmap_dep_ne_fmap f r)
| GNode010 x0 -> GNode010 (f x0)
| GNode011 (x0, r) -> GNode011 ((f x0), (gmap_dep_ne_fmap f r))
| GNode100 l -> GNode100 (gmap_dep_ne_fmap f l)
| GNode101 (l, r) -> GNode101 ((gmap_dep_ne_fmap f l), (gmap_dep_ne_fmap f r))
| GNode110 (l, x0) -> GNode110 ((gmap_dep_ne_fmap f l), (f x0))
| GNode111 (l, x0, r) ->
  GNode111 ((gmap_dep_ne_fmap f l), (f x0), (gmap_dep_ne_fmap f r))

(** val gmap_dep_fmap : ('a1 -> 'a2) -> 'a1 gmap_dep -> 'a2 gmap_dep **)

let gmap_dep_fmap f = function
| GEmpty -> GEmpty
| GNodes t -> GNodes (gmap_dep_ne_fmap f t)

(** val gmap_fmap :
    ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> (__ -> __) -> ('a1,
    __) gmap -> ('a1, __) gmap **)

let gmap_fmap _ _ f pat =
  let { gmap_car = mt } = pat in { gmap_car = (gmap_dep_fmap f mt) }

(** val gmap_dep_omap_aux :
    ('a1 gmap_dep_ne -> 'a2 gmap_dep) -> 'a1 gmap_dep -> 'a2 gmap_dep **)

let gmap_dep_omap_aux go = function
| GEmpty -> GEmpty
| GNodes t' -> go t'

(** val gmap_dep_ne_omap :
    ('a1 -> 'a2 option) -> 'a1 gmap_dep_ne -> 'a2 gmap_dep **)

let rec gmap_dep_ne_omap f x =
  gmap_dep_ne_case x (fun ml mx mr ->
    coq_GNode (gmap_dep_omap_aux (fun x0 -> gmap_dep_ne_omap f x0) ml)
      (mbind (Obj.magic (fun _ _ -> option_bind)) (fun pat ->
        let (_, x0) = pat in
        fmap (Obj.magic (fun _ _ -> option_fmap)) (fun x1 -> (__, x1))
          (Obj.magic f x0))
        (Obj.magic mx))
      (gmap_dep_omap_aux (fun x0 -> gmap_dep_ne_omap f x0) mr))

(** val gmap_dep_omap :
    ('a1 -> 'a2 option) -> 'a1 gmap_dep -> 'a2 gmap_dep **)

let gmap_dep_omap f =
  gmap_dep_omap_aux (gmap_dep_ne_omap f)

(** val gmap_omap :
    ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> (__ -> __ option) ->
    ('a1, __) gmap -> ('a1, __) gmap **)

let gmap_omap _ _ f pat =
  let { gmap_car = mt } = pat in { gmap_car = (gmap_dep_omap f mt) }

(** val gmap_merge_aux :
    ('a1 gmap_dep_ne -> 'a2 gmap_dep_ne -> 'a3 gmap_dep) -> ('a1 option ->
    'a2 option -> 'a3 option) -> 'a1 gmap_dep -> 'a2 gmap_dep -> 'a3 gmap_dep **)

let gmap_merge_aux go f mt1 mt2 =
  match mt1 with
  | GEmpty ->
    (match mt2 with
     | GEmpty -> GEmpty
     | GNodes t2' -> gmap_dep_ne_omap (fun x -> f None (Some x)) t2')
  | GNodes t1' ->
    (match mt2 with
     | GEmpty -> gmap_dep_ne_omap (fun x -> f (Some x) None) t1'
     | GNodes t2' -> go t1' t2')

(** val diag_None' :
    ('a1 option -> 'a2 option -> 'a3 option) -> (__ * 'a1) option ->
    (__ * 'a2) option -> (__ * 'a3) option **)

let diag_None' f mx my =
  match mx with
  | Some p0 ->
    let (_, x) = p0 in
    (match my with
     | Some p1 ->
       let (_, y) = p1 in
       fmap (Obj.magic (fun _ _ -> option_fmap)) (fun x0 -> (__, x0))
         (Obj.magic f (Some x) (Some y))
     | None ->
       fmap (Obj.magic (fun _ _ -> option_fmap)) (fun x0 -> (__, x0))
         (Obj.magic f (Some x) None))
  | None ->
    (match my with
     | Some p0 ->
       let (_, y) = p0 in
       fmap (Obj.magic (fun _ _ -> option_fmap)) (fun x -> (__, x))
         (Obj.magic f None (Some y))
     | None -> None)

(** val gmap_dep_ne_merge :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 gmap_dep_ne -> 'a2
    gmap_dep_ne -> 'a3 gmap_dep **)

let rec gmap_dep_ne_merge f x x0 =
  gmap_dep_ne_case x (fun ml1 mx1 mr1 ->
    gmap_dep_ne_case x0 (fun ml2 mx2 mr2 ->
      coq_GNode
        (gmap_merge_aux (fun x1 x2 -> gmap_dep_ne_merge f x1 x2) f ml1 ml2)
        (diag_None' f mx1 mx2)
        (gmap_merge_aux (fun x1 x2 -> gmap_dep_ne_merge f x1 x2) f mr1 mr2)))

(** val gmap_dep_merge :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 gmap_dep -> 'a2 gmap_dep
    -> 'a3 gmap_dep **)

let gmap_dep_merge f =
  gmap_merge_aux (gmap_dep_ne_merge f) f

(** val gmap_merge :
    ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> (__ option -> __
    option -> __ option) -> ('a1, __) gmap -> ('a1, __) gmap -> ('a1, __) gmap **)

let gmap_merge _ _ f pat pat0 =
  let { gmap_car = mt1 } = pat in
  let { gmap_car = mt2 } = pat0 in { gmap_car = (gmap_dep_merge f mt1 mt2) }

(** val gmap_fold_aux :
    (Big_int_Z.big_int -> 'a2 -> 'a1 gmap_dep_ne -> 'a2) -> Big_int_Z.big_int
    -> 'a2 -> 'a1 gmap_dep -> 'a2 **)

let gmap_fold_aux go i y = function
| GEmpty -> y
| GNodes t -> go i y t

(** val gmap_dep_ne_fold :
    (Big_int_Z.big_int -> 'a1 -> 'a2 -> 'a2) -> Big_int_Z.big_int -> 'a2 ->
    'a1 gmap_dep_ne -> 'a2 **)

let rec gmap_dep_ne_fold f x x0 x1 =
  gmap_dep_ne_case x1 (fun ml mx mr ->
    gmap_fold_aux (fun x2 x3 x4 -> gmap_dep_ne_fold f x2 x3 x4)
      ((fun x -> Big_int_Z.succ_big_int (Big_int_Z.mult_int_big_int 2 x)) x)
      (gmap_fold_aux (fun x2 x3 x4 -> gmap_dep_ne_fold f x2 x3 x4)
        (Big_int_Z.mult_int_big_int 2 x)
        (match mx with
         | Some p0 -> let (_, x2) = p0 in f (Pos.reverse x) x2 x0
         | None -> x0)
        ml)
      mr)

(** val gmap_dep_fold :
    (Big_int_Z.big_int -> 'a1 -> 'a2 -> 'a2) -> Big_int_Z.big_int -> 'a2 ->
    'a1 gmap_dep -> 'a2 **)

let gmap_dep_fold f =
  gmap_fold_aux (gmap_dep_ne_fold f)

(** val gmap_fold :
    ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a1 -> 'a2 -> __ ->
    __) -> __ -> ('a1, 'a2) gmap -> __ **)

let gmap_fold _ h f y pat =
  let { gmap_car = mt } = pat in
  gmap_dep_fold (fun i x ->
    match h.decode i with
    | Some k -> f k x
    | None -> id) Big_int_Z.unit_big_int y mt

type 'k gset = ('k, unit) gmap mapset'

(** val gset_singleton :
    ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a1, 'a1 gset)
    coq_Singleton **)

let gset_singleton eqDecision0 h =
  mapset_singleton (fun _ -> gmap_empty eqDecision0 h)
    (Obj.magic (fun _ -> gmap_partial_alter eqDecision0 h))

(** val gset_union :
    ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> 'a1 gset coq_Union **)

let gset_union eqDecision0 h =
  mapset_union (Obj.magic (fun _ _ _ -> gmap_merge eqDecision0 h))

(** val gset_intersection :
    ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> 'a1 gset
    coq_Intersection **)

let gset_intersection eqDecision0 h =
  mapset_intersection (Obj.magic (fun _ _ _ -> gmap_merge eqDecision0 h))

(** val gset_subseteq_dec :
    ('a1, 'a1) coq_RelDecision -> 'a1 coq_Countable -> ('a1 gset, 'a1 gset)
    coq_RelDecision **)

let gset_subseteq_dec eqDecision0 h =
  mapset_subseteq_dec (Obj.magic (fun _ _ -> gmap_fmap eqDecision0 h))
    (Obj.magic (fun _ -> gmap_lookup eqDecision0 h)) (fun _ ->
    gmap_empty eqDecision0 h)
    (Obj.magic (fun _ -> gmap_partial_alter eqDecision0 h))
    (Obj.magic (fun _ _ -> gmap_omap eqDecision0 h))
    (Obj.magic (fun _ _ _ -> gmap_merge eqDecision0 h))
    (Obj.magic (fun _ _ -> gmap_fold eqDecision0 h)) eqDecision0
    (gmap_eq_dec eqDecision0 h unit_eq_dec)
