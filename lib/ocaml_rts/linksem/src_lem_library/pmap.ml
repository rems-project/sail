(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* Modified by Susmit Sarkar 2010-11-30 *)
(* $Id: map.ml 10468 2010-05-25 13:29:43Z frisch $ *)

(* A map from ordered keys *)

type ('key,'a) rep =
    Empty
  | Node of ('key,'a) rep * 'key * 'a * ('key,'a) rep * int

let height = function
    Empty -> 0
  | Node(_,_,_,_,h) -> h

let create l x d r =
  let hl = height l and hr = height r in
  Node(l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))

let singleton x d = Node(Empty, x, d, Empty, 1)
    
let bal l x d r =
  let hl = match l with Empty -> 0 | Node(_,_,_,_,h) -> h in
  let hr = match r with Empty -> 0 | Node(_,_,_,_,h) -> h in
  if hl > hr + 2 then begin
    match l with
      Empty -> invalid_arg "Map.bal"
    | Node(ll, lv, ld, lr, _) ->
        if height ll >= height lr then
          create ll lv ld (create lr x d r)
        else begin
          match lr with
                Empty -> invalid_arg "Map.bal"
          | Node(lrl, lrv, lrd, lrr, _)->
              create (create ll lv ld lrl) lrv lrd (create lrr x d r)
        end
  end else if hr > hl + 2 then begin
    match r with
      Empty -> invalid_arg "Map.bal"
    | Node(rl, rv, rd, rr, _) ->
        if height rr >= height rl then
          create (create l x d rl) rv rd rr
        else begin
          match rl with
            Empty -> invalid_arg "Map.bal"
          | Node(rll, rlv, rld, rlr, _) ->
              create (create l x d rll) rlv rld (create rlr rv rd rr)
        end
  end else
    Node(l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))
      
let empty = Empty
    
let is_empty = function Empty -> true | _ -> false
    
let rec add cmp x data = function
    Empty ->
      Node(Empty, x, data, Empty, 1)
  | Node(l, v, d, r, h) ->
      let c = cmp x v in
      if c = 0 then
        Node(l, x, data, r, h)
      else if c < 0 then
        bal (add cmp x data l) v d r
      else
        bal l v d (add cmp x data r)
	  
let rec find cmp x = function
        Empty ->
          raise Not_found
      | Node(l, v, d, r, _) ->
          let c = cmp x v in
          if c = 0 then d
          else find cmp x (if c < 0 then l else r)

let rec mem cmp x = function
    Empty ->
      false
  | Node(l, v, d, r, _) ->
      let c = cmp x v in
      c = 0 || mem cmp x (if c < 0 then l else r)

let rec min_binding = function
    Empty -> raise Not_found
  | Node(Empty, x, d, r, _) -> (x, d)
  | Node(l, x, d, r, _) -> min_binding l

let rec max_binding = function
    Empty -> raise Not_found
  | Node(l, x, d, Empty, _) -> (x, d)
  | Node(l, x, d, r, _) -> max_binding r
	
let rec remove_min_binding = function
    Empty -> invalid_arg "Map.remove_min_elt"
  | Node(Empty, x, d, r, _) -> r
  | Node(l, x, d, r, _) -> bal (remove_min_binding l) x d r

let merge t1 t2 =
  match (t1, t2) with
    (Empty, t) -> t
  | (t, Empty) -> t
  | (_, _) ->
      let (x, d) = min_binding t2 in
      bal t1 x d (remove_min_binding t2)
	
let rec remove cmp x = function
    Empty ->
      Empty
  | Node(l, v, d, r, h) ->
      let c = cmp x v in
      if c = 0 then
        merge l r
      else if c < 0 then
        bal (remove cmp x l) v d r
      else
        bal l v d (remove cmp x r)

let rec iter f = function
    Empty -> ()
  | Node(l, v, d, r, _) ->
      iter f l; f v d; iter f r

let rec map f = function
    Empty ->
      Empty
  | Node(l, v, d, r, h) ->
      let l' = map f l in
      let d' = f d in
      let r' = map f r in
      Node(l', v, d', r', h)
	
let rec mapi f = function
    Empty ->
      Empty
  | Node(l, v, d, r, h) ->
      let l' = mapi f l in
      let d' = f v d in
      let r' = mapi f r in
      Node(l', v, d', r', h)

let rec fold f m accu =
  match m with
    Empty -> accu
  | Node(l, v, d, r, _) ->
      fold f r (f v d (fold f l accu))

let rec for_all p = function
    Empty -> true
  | Node(l, v, d, r, _) -> p v d && for_all p l && for_all p r

let rec exists p = function
    Empty -> false
  | Node(l, v, d, r, _) -> p v d || exists p l || exists p r
      
let filter cmp p s =
  let rec filt accu = function
    | Empty -> accu
    | Node(l, v, d, r, _) ->
        filt (filt (if p v d then add cmp v d accu else accu) l) r in
  filt Empty s

let partition cmp p s =
  let rec part (t, f as accu) = function
    | Empty -> accu
    | Node(l, v, d, r, _) ->
        part (part (if p v d then (add cmp v d t, f) else (t, add cmp v d f)) l) r in
  part (Empty, Empty) s
    
    (* Same as create and bal, but no assumptions are made on the
       relative heights of l and r. *)

let rec join cmp l v d r =
  match (l, r) with
    (Empty, _) -> add cmp v d r
  | (_, Empty) -> add cmp v d l
  | (Node(ll, lv, ld, lr, lh), Node(rl, rv, rd, rr, rh)) ->
      if lh > rh + 2 then bal ll lv ld (join cmp lr v d r) else
      if rh > lh + 2 then bal (join cmp l v d rl) rv rd rr else
      create l v d r

	(* Merge two trees l and r into one.
	   All elements of l must precede the elements of r.
	   No assumption on the heights of l and r. *)

let concat cmp t1 t2 =
  match (t1, t2) with
    (Empty, t) -> t
  | (t, Empty) -> t
  | (_, _) ->
      let (x, d) = min_binding t2 in
      join cmp t1 x d (remove_min_binding t2)

let concat_or_join cmp t1 v d t2 =
  match d with
  | Some d -> join cmp t1 v d t2
  | None -> concat cmp t1 t2

let rec split cmp x = function
    Empty ->
      (Empty, None, Empty)
  | Node(l, v, d, r, _) ->
      let c = cmp x v in
      if c = 0 then (l, Some d, r)
      else if c < 0 then
        let (ll, pres, rl) = split cmp x l in (ll, pres, join cmp rl v d r)
      else
        let (lr, pres, rr) = split cmp x r in (join cmp l v d lr, pres, rr)
	  
let rec merge cmp f s1 s2 =
  match (s1, s2) with
    (Empty, Empty) -> Empty
  | (Node (l1, v1, d1, r1, h1), _) when h1 >= height s2 ->
      let (l2, d2, r2) = split cmp v1 s2 in
      concat_or_join cmp (merge cmp f l1 l2) v1 (f v1 (Some d1) d2) (merge cmp f r1 r2)
  | (_, Node (l2, v2, d2, r2, h2)) ->
      let (l1, d1, r1) = split cmp v2 s1 in
      concat_or_join cmp (merge cmp f l1 l2) v2 (f v2 d1 (Some d2)) (merge cmp f r1 r2)
  | _ ->
      assert false

type ('key,'a) enumeration = End | More of 'key * 'a * ('key,'a) rep * ('key,'a) enumeration

let rec cons_enum m e =
  match m with
    Empty -> e
  | Node(l, v, d, r, _) -> cons_enum l (More(v, d, r, e))
	
let compare cmp_key cmp_a m1 m2 =
  let rec compare_aux e1 e2 =
    match (e1, e2) with
      (End, End) -> 0
    | (End, _)  -> -1
    | (_, End) -> 1
    | (More(v1, d1, r1, e1), More(v2, d2, r2, e2)) ->
        let c = cmp_key v1 v2 in
        if c <> 0 then c else
        let c = cmp_a d1 d2 in
        if c <> 0 then c else
        compare_aux (cons_enum r1 e1) (cons_enum r2 e2)
  in compare_aux (cons_enum m1 End) (cons_enum m2 End)

let equal cmp_key cmp_a m1 m2 =
  let rec equal_aux e1 e2 =
    match (e1, e2) with
      (End, End) -> true
    | (End, _)  -> false
    | (_, End) -> false
    | (More(v1, d1, r1, e1), More(v2, d2, r2, e2)) ->
        cmp_key v1 v2 = 0 && cmp_a d1 d2 &&
        equal_aux (cons_enum r1 e1) (cons_enum r2 e2)
      in equal_aux (cons_enum m1 End) (cons_enum m2 End)

let rec cardinal = function
    Empty -> 0
  | Node(l, _, _, r, _) -> cardinal l + 1 + cardinal r

let rec bindings_aux accu = function
    Empty -> accu
  | Node(l, v, d, r, _) -> bindings_aux ((v, d) :: bindings_aux accu r) l

let bindings s =
  bindings_aux [] s
    
let choose = min_binding


(* Wrapper functions now *)

type ('key,'a) map = {cmp:'key -> 'key -> int; m:('key,'a) rep}

let empty cmp = {cmp = cmp; m = Empty}
let is_empty m = is_empty m.m
let mem k m = mem m.cmp k m.m
let add k a m = {m with m = add m.cmp k a m.m}
let singleton cmp k a = {cmp = cmp; m = singleton k a} 
let remove k m = {m with m = remove m.cmp k m.m}
let merge f a b = {cmp = a.cmp; (* does not matter, a and b should have the same comparison function *)
		   m = merge a.cmp f a.m b.m;}
let union a b = merge (fun k o1 o2 ->
  match (o1, o2) with
    | (_, Some v) -> Some v
    | (Some v, _) -> Some v
    | (_, _) -> None) a b
 let compare f a b = compare a.cmp f a.m b.m
let equal f a b = equal a.cmp f a.m b.m
let iter f m = iter f m.m
let fold f m b = fold f m.m b
let for_all f m = for_all f m.m
let exist f m = exists f m.m
let filter f m = {m with m = filter m.cmp f m.m}
let partition f m = 
  let m1,m2 = partition m.cmp f m.m in
  ({m with m = m1},{m with m = m2})
let cardinal m = cardinal m.m
let domain m = Pset.from_list m.cmp (List.map fst (bindings m.m))
let range cmp m = Pset.from_list cmp (List.map snd (bindings m.m))
let bindings_list m = bindings m.m
let bindings cmp m = Pset.from_list cmp (bindings m.m)
let min_binding m = min_binding m.m
let max_binding m = max_binding m.m
let choose m = choose m.m
let split k m = 
  let (m1,opt,m2) = split m.cmp k m.m in
  ({m with m = m1},opt,{m with m = m2})
let find k m = find m.cmp k m.m
let lookup k m = try Some (find k m) with Not_found -> None
let map f m = {m with m = map f m.m}
let mapi f m = {m with m = mapi f m.m}

let from_set f s = Pset.fold (fun k m -> (add k (f k) m)) s (empty (Pset.get_elem_compare s))
