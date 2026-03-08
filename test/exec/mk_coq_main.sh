#!/bin/bash

OUT="_coqbuild_$1/main.v"

if grep -q 'ConcurrencyInterface' "_coqbuild_$1/$1.v"; then
  if grep -q 'ConcurrencyInterfaceV2' "_coqbuild_$1/$1.v"; then
    V2=true
  fi
  if grep -q 'sail_model_init.*: unit :=' "_coqbuild_$1/$1.v"; then
    RUN="main tt"
  else
    RUN="Defs.bind0 (sail_model_init tt) (main tt)"
  fi
  cat <<EOF > "$OUT"
  From SailStdpp Require Import Base.
  Require Import String.
  Require Import List.
  Import ListNotations.
  Open Scope string.
  From stdpp Require base.
  
  From Coq Require FMapAVL OrderedType OrderedTypeEx.
  Module NMap := FMapAVL.Make(OrderedTypeEx.N_as_OT).
  
  Record state := {
    state_memory : NMap.t (definitions.bv 8);
    state_tags : NMap.t bool;
    state_regs : regstate;
    state_cycles : Z;
    state_output : string;
  }.
  
  Definition init_state := {| state_memory := NMap.empty _; state_tags := NMap.empty _; state_regs := init_regstate; state_cycles := 0; state_output := "" |}.
  
  Definition write_message (st : state) (msg : string) :=
    {| state_memory := st.(state_memory); state_tags := st.(state_tags); state_regs := st.(state_regs); state_cycles := st.(state_cycles); state_output := String.append st.(state_output) msg |}.
  
  (* NB: write and read wrongly assume that PAs are tag aligned *)
  
EOF
  if [ -z "$V2" ]; then
  cat <<EOF >> "$OUT"
  Definition write_mem (st : state) n (req : Interface.WriteReq.t n) :=
    let base_addr := mword_to_N req.(Interface.WriteReq.pa) in
    let addrs := State_monad.genlist (fun i => base_addr + N.of_nat i)%N (N.to_nat n) in
    let write_byte i m := NMap.add (base_addr + i)%N (definitions.bv_extract (8 * i) 8 req.(Interface.WriteReq.value)) m in
    let tag := opt_def false req.(Interface.WriteReq.tag) in
    {| state_memory := N.recursion st.(state_memory) write_byte n;
       state_tags := NMap.add base_addr tag st.(state_tags);
       state_regs := st.(state_regs);
       state_cycles := st.(state_cycles);
       state_output := st.(state_output)
    |}.
  
  Definition read_mem (st : state) n (req : Interface.ReadReq.t n) : definitions.bv (8 * n) * option bool :=
    let base_addr := mword_to_N req.(Interface.ReadReq.pa) in
    let read_byte i v := definitions.bv_or (definitions.bv_shiftl (definitions.bv_zero_extend (8 * n) (opt_def (definitions.bv_0 8) (NMap.find (base_addr + i)%N st.(state_memory)))) (definitions.Z_to_bv (8 * n)%N (Z.of_N (8 * i)))) v in
    let value := N.recursion (definitions.bv_0 (8 * n)) read_byte n in
    let tag := if req.(Interface.ReadReq.tag) then Some (opt_def false (NMap.find base_addr st.(state_tags))) else None in
    (value, tag).
EOF
  else
  cat <<EOF >> "$OUT"
  Definition write_mem (st : state) (req : Interface.MemReq.t) (value : definitions.bv (8 * Interface.MemReq.size req)) (tags : definitions.bv (Interface.MemReq.num_tag req)) :=
    let n := req.(Interface.MemReq.size) in
    let nt := req.(Interface.MemReq.num_tag) in
    let base_addr := mword_to_N req.(Interface.MemReq.address) in
    let addrs := State_monad.genlist (fun i => base_addr + N.of_nat i)%N (N.to_nat n) in
    let write_byte i m := NMap.add (base_addr + i)%N (definitions.bv_extract (8 * i) 8 value) m in
    let cap_size := N.pow 2 Arch.cap_size_log in
    let write_tag i m := NMap.add (base_addr + i * cap_size)%N (MachineWord.MachineWord.get_bit tags i) m in
    let new_tags :=
      if Z.of_N nt >? 0 then N.recursion st.(state_tags) write_tag nt else NMap.add (mword_to_N (definitions.bv_and req.(Interface.MemReq.address) (definitions.bv_opp (definitions.Z_to_bv _ (Z.of_N cap_size))))) false st.(state_tags)
    in
    {| state_memory := N.recursion st.(state_memory) write_byte n;
       state_tags := new_tags;
       state_regs := st.(state_regs);
       state_cycles := st.(state_cycles);
       state_output := st.(state_output)
    |}.
  
  Definition read_mem (st : state) (req : Interface.MemReq.t) : definitions.bv (8 * (Interface.MemReq.size req)) * definitions.bv (Interface.MemReq.num_tag req) :=
    let n := req.(Interface.MemReq.size) in
    let nt := req.(Interface.MemReq.num_tag) in
    let base_addr := mword_to_N req.(Interface.MemReq.address) in
    let read_byte i v := definitions.bv_or (definitions.bv_shiftl (definitions.bv_zero_extend (8 * n) (opt_def (definitions.bv_0 8) (NMap.find (base_addr + i)%N st.(state_memory)))) (definitions.Z_to_bv (8 * n)%N (Z.of_N (8 * i)))) v in
    let cap_size := N.pow 2 Arch.cap_size_log in
    let read_tag i v := MachineWord.MachineWord.set_bit v i (opt_def false (NMap.find (base_addr + i * cap_size)%N st.(state_tags))) in
    let value := N.recursion (definitions.bv_0 (8 * n)) read_byte n in
    let tag := N.recursion (definitions.bv_0 nt) read_tag nt in
    (value, tag).
EOF
  fi
  cat <<EOF >> "$OUT"
  
  Definition read_reg (st : state) (r : register) : type_of_register r := register_lookup r st.(state_regs).
  Definition write_reg (st : state) (r : register) (v : type_of_register r) : state :=
    {| state_memory := st.(state_memory);
       state_tags := st.(state_tags);
       state_regs := register_set r v st.(state_regs);
       state_cycles := st.(state_cycles);
       state_output := st.(state_output);
    |}.
  
  Definition cycle_count (st : state) : state :=
    {| state_memory := st.(state_memory); state_tags := st.(state_tags); state_regs := st.(state_regs); state_cycles := st.(state_cycles) + 1; state_output := st.(state_output) |}.
  
  Fixpoint run (t : M unit) (st : state) : string + {T : Type & Interface.outcome _ T} :=
    match t with
    | Interface.Ret _ => inl st.(state_output)
    | Interface.Next out k =>
      match out in Interface.outcome _ T return (T -> _) -> _ with
      | Interface.Message msg => fun k => run (k tt) (write_message st msg)
      | Interface.Choose _ty => fun k => run (k base.inhabitant) st
EOF
  if [ -z "$V2" ]; then
  cat <<EOF >> "$OUT"
      | Interface.MemWrite n req => fun k => run (k (inl None)) (write_mem st n req)
      | Interface.MemRead n req => fun k => run (k (inl (read_mem st n req))) st
      | Interface.TakeException _ => fun k => run (k tt) st
      | Interface.ReturnException _ => fun k => run (k tt) st
EOF
  else
  cat <<EOF >> "$OUT"
      | Interface.MemWrite req v tags => fun k => run (k (inl None)) (write_mem st req v tags)
      | Interface.MemRead req => fun k => run (k (inl (read_mem st req))) st
      | Interface.TakeException _ => fun k => run (k tt) st
      | Interface.ReturnException => fun k => run (k tt) st
EOF
  fi
  cat <<EOF >> "$OUT"
      | Interface.Barrier _ => fun k => run (k tt) st
      | Interface.CycleCount => fun k => run (k tt) (cycle_count st)
      | Interface.GetCycleCount => fun k => run (k st.(state_cycles)) st
      | Interface.RegRead r _ => fun k => run (k (read_reg st r)) st
      | Interface.RegWrite r _ v => fun k => run (k tt) (write_reg st r v)
      | _ => fun _ => inr (existT _ out)
      end k
    end. 
  
  Goal True.
  set (outerr := ltac:(
  let result := eval vm_compute in (run ($RUN) init_state) in
  match result with
    | inl ?msg => idtac "OK"; exact (msg, "")
    | _ => idtac "Fail (unexpected result):" result; exact ("","")
  end)).
  Redirect "output" (let t := eval vm_compute in (fst outerr) in idtac t).
  Redirect "error" (let t := eval vm_compute in (snd outerr) in idtac t).
  exact I.
  Qed.
EOF
else
  cat <<EOF > "$OUT"
  From SailStdpp Require Import State_monad State_lifting.
  Require Import String.
  Require Import List.
  Import ListNotations.
  Open Scope string.
  
  Goal True.
EOF
  if grep -q "Definition main '(tt : unit) : unit :=" "_coqbuild_$1/$1.v"; then
    cat <<EOF >> "$OUT"
  let result := eval vm_compute in (main tt) in
  match result with
  | tt => idtac "OK"
  | _ => idtac "Fail (unexpected result):" result
  end.
  exact I.
  Qed.
EOF
  else
    if grep -q 'initial_regstate' "_coqbuild_$1/$1.v"; then
      REGSTATE="initial_regstate"
    else
      REGSTATE='init_regstate'
    fi
    if grep -q 'sail_model_init.*: unit :=' "_coqbuild_$1/$1.v"; then
      RUN="main tt"
    else
      RUN="Prompt_monad.bind0 (sail_model_init tt) (main tt)"
    fi
    cat <<EOF >> "$OUT"
  set (outerr := ltac:(
  let result := eval vm_compute in (liftState register_accessors ($RUN) (init_state $REGSTATE) default_choice) in
  match result with
    | [(Value tt,?state,_)] => idtac "OK"; exact (state.(ss_output), "")
    | [(Ex (Failure ?s),?state,_)] => idtac "Fail:" s; exact (state.(ss_output), "Assertion failed: " ++ s ++ "
")
    | _ => idtac "Fail (unexpected result):" result; exact ("","")
  end)).
  Redirect "output" (let t := eval vm_compute in (fst outerr) in idtac t).
  Redirect "error" (let t := eval vm_compute in (snd outerr) in idtac t).
  exact I.
  Qed.
EOF
  fi
fi
