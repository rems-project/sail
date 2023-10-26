(* Copyright 2017-2019 Arm Limited
 * SPDX-Licence-Identifier: BSD-3-Clause
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * 1. Redistributions of source code must retain the above copyright notice, this
 *    list of conditions and the following disclaimer.
 * 
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 * 
 * 3. Neither the name of the copyright holder nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *)
(*
 *
 * Copyright (c) 2001-2003,
 *  George C. Necula    <necula@cs.berkeley.edu>
 *  Scott McPeak        <smcpeak@cs.berkeley.edu>
 *  Wes Weimer          <weimer@cs.berkeley.edu>
 *  Ben Liblit          <liblit@cs.berkeley.edu>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * 1. Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * 3. The names of the contributors may not be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
 * IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER
 * OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 *)

(****************************************************************
 * Visitor support code
 *
 * The code in this file is copied from George Necula's excellent
 * CIL project (https://people.eecs.berkeley.edu/~necula/cil/)
 * with minor change to allow it to be used with an arbitrary AST,
 * taken from ASLi.
 ****************************************************************)

(****************************************************************
 * Visit action
 *
 * Visitor methods can request one of four actions on the AST.
 ****************************************************************)

(** Different visiting actions. 'a will be instantiated with various AST types. *)
type 'a visit_action =
  | SkipChildren  (** Do not visit the children. Return the node as it is. *)
  | DoChildren
      (** Continue with the children of this node. Rebuild the node on
     return if any of the children changes (use == test) *)
  | ChangeTo of 'a  (** Replace the expression with the given one *)
  | ChangeDoChildrenPost of 'a * ('a -> 'a)
      (** First consider that the entire exp is replaced by the first
     parameter. Then continue with the children. On return rebuild the
     node if any of the children has changed and then apply the
     function on the node *)

(****************************************************************
 * Visitor engine
 *
 * These functions implement the various actions a visitor can
 * request and provide helper functions for writing visitors.
 *
 * Note that the visitor functions implement a space-saving optimisation:
 * if the result would be identical to the input value, they return the
 * input value to avoid allocating another copy of the object.
 * This optimisation is supported by the mapNoCopy, mapNoCopyList
 * and doVisitList functions.
 *
 * This code is changed from the CIL original by replacing the
 * "cilVisitor" type by "'v" so that the code is independent of
 * the particular AST it is used with.
 ****************************************************************)

(*** Define the visiting engine ****)
(* visit all the nodes in an tree *)
let do_visit (vis : 'v) (action : 'a visit_action) (children : 'v -> 'a -> 'a) (node : 'a) : 'a =
  match action with
  | SkipChildren -> node
  | ChangeTo node' -> node'
  | DoChildren -> children vis node
  | ChangeDoChildrenPost (node', f) -> f (children vis node')

let change_do_children node' = ChangeDoChildrenPost (node', fun n -> n)

(* map_no_copy is like map but avoid copying the list if the function does not
 * change the elements. *)
let rec map_no_copy (f : 'a -> 'a) = function
  | [] -> []
  | i :: resti as li ->
      let i' = f i in
      let resti' = map_no_copy f resti in
      if i' != i || resti' != resti then i' :: resti' else li

let rec map_no_copy_list (f : 'a -> 'a list) = function
  | [] -> []
  | i :: resti as li -> (
      let il' = f i in
      let resti' = map_no_copy_list f resti in
      match il' with [i'] when i' == i && resti' == resti -> li | _ -> il' @ resti'
    )

(* not part of original cil framework *)
let map_no_copy_opt (f : 'a -> 'a) : 'a option -> 'a option = function
  | None -> None
  | Some x as ox ->
      let x' = f x in
      if x' == x then ox else Some x'

(* A visitor for lists *)
let do_visit_list (vis : 'v) (action : 'a list visit_action) (children : 'v -> 'a -> 'a) (node : 'a) : 'a list =
  match action with
  | SkipChildren -> [node]
  | ChangeTo nodes' -> nodes'
  | DoChildren -> [children vis node]
  | ChangeDoChildrenPost (nodes', f) -> f (map_no_copy (fun n -> children vis n) nodes')

(****************************************************************
 * End
 ****************************************************************)
