(**************************************************************************)
(*                        Lem                                             *)
(*                                                                        *)
(*          Dominic Mulligan, University of Cambridge                     *)
(*          Francesco Zappa Nardelli, INRIA Paris-Rocquencourt            *)
(*          Gabriel Kerneis, University of Cambridge                      *)
(*          Kathy Gray, University of Cambridge                           *)
(*          Peter Boehm, University of Cambridge (while working on Lem)   *)
(*          Peter Sewell, University of Cambridge                         *)
(*          Scott Owens, University of Kent                               *)
(*          Thomas Tuerk, University of Cambridge                         *)
(*                                                                        *)
(*  The Lem sources are copyright 2010-2013                               *)
(*  by the UK authors above and Institut National de Recherche en         *)
(*  Informatique et en Automatique (INRIA).                               *)
(*                                                                        *)
(*  All files except ocaml-lib/pmap.{ml,mli} and ocaml-libpset.{ml,mli}   *)
(*  are distributed under the license below.  The former are distributed  *)
(*  under the LGPLv2, as in the LICENSE file.                             *)
(*                                                                        *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*  notice, this list of conditions and the following disclaimer.         *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*  notice, this list of conditions and the following disclaimer in the   *)
(*  documentation and/or other materials provided with the distribution.  *)
(*  3. The names of the authors may not be used to endorse or promote     *)
(*  products derived from this software without specific prior written    *)
(*  permission.                                                           *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    *)
(*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    *)
(*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       *)
(*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     *)
(*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         *)
(*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER  *)
(*  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       *)
(*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   *)
(*  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         *)
(**************************************************************************)

(** finite map library *)

module type Fmap = sig
  type k
  module S : Set.S with type elt = k
  type 'a t
  val empty : 'a t
  val is_empty : 'a t -> bool
  val from_list : (k * 'a) list -> 'a t
  val from_list2 : k list -> 'a list -> 'a t
  val insert : 'a t -> (k * 'a) -> 'a t
  (* Keys from the right argument replace those from the left *)
  val union : 'a t -> 'a t -> 'a t
  val big_union : 'a t list -> 'a t
  val merge : (k -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
  val apply : 'a t -> k -> 'a option
  val in_dom : k -> 'a t -> bool
  val map : (k -> 'a -> 'b) -> 'a t -> 'b t
  val domains_overlap : 'a t -> 'b t -> k option
  val domains_disjoint : 'a t list -> bool
  val iter : (k -> 'a -> unit) -> 'a t -> unit
  val fold : ('b -> k -> 'a -> 'b) -> 'b -> 'a t -> 'b
  val remove : 'a t -> k -> 'a t
  val pp_map : (Format.formatter -> k -> unit) -> 
               (Format.formatter -> 'a -> unit) -> 
               Format.formatter -> 
               'a t ->
               unit
  val domain : 'a t -> S.t
end

module Fmap_map(Key : Set.OrderedType) : Fmap 
                  with type k = Key.t and module S = Set.Make(Key) = struct

  type k = Key.t
  module S = Set.Make(Key)

  module M = Map.Make(Key)
  module D = Util.Duplicate(S)

  type 'a t = 'a M.t
  let empty = M.empty
  let is_empty m = M.is_empty m
  let from_list l = List.fold_left (fun m (k,v) -> M.add k v m) M.empty l
  let from_list2 l1 l2 = List.fold_left2 (fun m k v -> M.add k v m) M.empty l1 l2
  let insert m (k,v) = M.add k v m
  let union m1 m2 = 
    M.merge (fun k v1 v2 -> match v2 with | None -> v1 | Some _ -> v2) m1 m2
  let merge f m1 m2 = M.merge f m1 m2
  let apply m k = 
    try
      Some(M.find k m)
    with
      | Not_found -> None
  let in_dom k m = M.mem k m
  let map f m = M.mapi f m
  let rec domains_overlap m1 m2 = 
    M.fold 
      (fun k _ res ->
         if M.mem k m1 then
           Some(k)
         else
           res)
      m2
      None
  let iter f m = M.iter f m
  let fold f m base = M.fold (fun k v res -> f res k v) base m
  let remove m k = M.remove k m
  let pp_map pp_key pp_val ppf m =
    let l = M.fold (fun k v l -> (k,v)::l) m [] in
      Format.fprintf ppf "@[%a@]"
        (Pp.lst "@\n"
           (fun ppf (k,v) -> 
              Format.fprintf ppf "@[<2>%a@ |->@ %a@]"
                pp_key k
                pp_val v))
        l
  let big_union l = List.fold_left union empty l
  let domains_disjoint maps =
    match D.duplicates (List.concat (List.map (fun m -> List.map fst (M.bindings m)) maps)) with
      | D.No_dups _ -> true
      | D.Has_dups _ -> false

  let domain m =
    M.fold (fun k _ s -> S.add k s) m S.empty
end

