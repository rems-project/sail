(*Require Import Sail_impl_base*)
Require Import Sail2_values.
Require Import Sail2_prompt_monad.
Require Import Sail2_prompt.
Require Import Sail2_state_monad.
(*
(* State monad wrapper around prompt monad *)

val liftState : forall 'regval 'regs 'a 'e. register_accessors 'regs 'regval -> monad 'regval 'a 'e -> monadS 'regs 'a 'e
let rec liftState ra s = match s with
  | (Done a)             -> returnS a
  | (Read_mem rk a sz k) -> bindS (read_mem_bytesS rk a sz) (fun v -> liftState ra (k v))
  | (Read_tag t k)       -> bindS (read_tagS t)             (fun v -> liftState ra (k v))
  | (Write_memv a k)     -> bindS (write_mem_bytesS a)      (fun v -> liftState ra (k v))
  | (Write_tagv t k)     -> bindS (write_tagS t)            (fun v -> liftState ra (k v))
  | (Read_reg r k)       -> bindS (read_regvalS ra r)       (fun v -> liftState ra (k v))
  | (Excl_res k)         -> bindS (excl_resultS ())         (fun v -> liftState ra (k v))
  | (Undefined k)        -> bindS (undefined_boolS ())      (fun v -> liftState ra (k v))
  | (Write_ea wk a sz k) -> seqS (write_mem_eaS wk a sz)    (liftState ra k)
  | (Write_reg r v k)    -> seqS (write_regvalS ra r v)     (liftState ra k)
  | (Footprint k)        -> liftState ra k
  | (Barrier _ k)        -> liftState ra k
  | (Fail descr)         -> failS descr
  | (Error descr)        -> failS descr
  | (Exception e)        -> throwS e
end


val iterS_aux : forall 'rv 'a 'e. integer -> (integer -> 'a -> monadS 'rv unit 'e) -> list 'a -> monadS 'rv unit 'e
let rec iterS_aux i f xs = match xs with
  | x :: xs -> f i x >>$ iterS_aux (i + 1) f xs
  | [] -> returnS ()
  end

declare {isabelle} termination_argument iterS_aux = automatic

val iteriS : forall 'rv 'a 'e. (integer -> 'a -> monadS 'rv unit 'e) -> list 'a -> monadS 'rv unit 'e
let iteriS f xs = iterS_aux 0 f xs

val iterS : forall 'rv 'a 'e. ('a -> monadS 'rv unit 'e) -> list 'a -> monadS 'rv unit 'e
let iterS f xs = iteriS (fun _ x -> f x) xs

val foreachS : forall 'a 'rv 'vars 'e.
  list 'a -> 'vars -> ('a -> 'vars -> monadS 'rv 'vars 'e) -> monadS 'rv 'vars 'e
let rec foreachS xs vars body = match xs with
  | [] -> returnS vars
  | x :: xs ->
     body x vars >>$= fun vars ->
     foreachS xs vars body
end

declare {isabelle} termination_argument foreachS = automatic


val whileS : forall 'rv 'vars 'e. 'vars -> ('vars -> monadS 'rv bool 'e) ->
                ('vars -> monadS 'rv 'vars 'e) -> monadS 'rv 'vars 'e
let rec whileS vars cond body s =
  (cond vars >>$= (fun cond_val s' ->
  if cond_val then
    (body vars >>$= (fun vars s'' -> whileS vars cond body s'')) s'
  else returnS vars s')) s

val untilS : forall 'rv 'vars 'e. 'vars -> ('vars -> monadS 'rv bool 'e) ->
                ('vars -> monadS 'rv 'vars 'e) -> monadS 'rv 'vars 'e
let rec untilS vars cond body s =
  (body vars >>$= (fun vars s' ->
  (cond vars >>$= (fun cond_val s'' ->
  if cond_val then returnS vars s'' else untilS vars cond body s'')) s')) s
*)
