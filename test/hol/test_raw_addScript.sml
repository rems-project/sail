open HolKernel boolLib bossLib Parse
open intLib bitLib wordsLib integer_wordLib
open optionLib combinLib finite_mapLib bitstringLib
open state_monadTheory state_monad_lemmasTheory
open sail_valuesAuxiliaryTheory stateAuxiliaryTheory
open cheriTheory hoareTheory

val _ = new_theory "test_raw_add";

val _ = Globals.max_print_depth := 50;

(* MIPS register names
   ftp://www.linux-mips.org/pub/linux/mips/doc/ABI/MIPS-N32-ABI-Handbook.pdf
 *)
val gpr_names_def = Define`
  gpr_names = [
    "zero";
    "at";
    "v0"; "v1";
    "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7";
    "t4"; "t5"; "t6"; "t7";
    "s0"; "s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7";
    "t8"; "t9";
    "kt0"; "kt1";
    "gp";
    "sp";
    "s8";
    "ra"]`;

val PrePost_write_regS = Q.store_thm("PrePost_write_regS",
  `PrePost (λs. P (Value ()) (s with regstate := reg.write_to v s.regstate)) (write_regS reg v) P`,
  rw[write_regS_def,PrePost_updateS]);

val PrePost_assert_expS_T = Q.store_thm("PrePost_assert_expS_T",
  `exp ⇒ PrePost (P (Value ())) (assert_expS exp msg) P`,
  rw[assert_expS_def,PrePost_returnS]);

val PrePost_maybe_failS_SOME = Q.store_thm("PrePost_maybe_failS_SOME",
  `PrePost (P (Value x)) (maybe_failS msg (SOME x)) P`,
  rw[maybe_failS_def,PrePost_returnS]);

(*
val PrePost_MEMw_wrapper = Q.store_thm("PrePost_MEMw_wrapper",
  `PrePost P (MEMw_wrapper addr size data) Q`,
  MEMw_wrapper_def
  |> SIMP_RULE(srw_ss()++boolSimps.LET_ss)[]
  |> CONV_RULE(STRIP_QUANT_CONV(RAND_CONV(RATOR_CONV(RATOR_CONV(RAND_CONV(RAND_CONV(EVAL)))))))
*)

val PrePost_init_cp0_state = Q.store_thm("PrePost_init_cp0_state",
  `PrePost (λs. P (Value ())
    (s with regstate :=
        s.regstate with CP0Status :=
            Mk_StatusReg (update_subrange_vec_dec (get_StatusReg s.regstate.CP0Status) 22 22 (cast_unit_vec0 B1))))
    (init_cp0_state())
    P`,
  EVAL_TAC \\ rw[]);

(*
val PrePost_init_cp2_state = Q.store_thm("PrePost_init_cp2_state",
  `PrePost P (init_cp2_state ()) Q`,
  rw[init_cp2_state_def]
  PrePost_def
  f"foreach"
  hyp stateTheory.foreachS_def
  \\ match_mp_tac PrePost_seqS
  \\ qexists_tac`P1`
  \\ conj_tac
  >- (
    match_mp_tac PrePost_seqS
    \\ qexists_tac`P2`
    \\ conj_tac
    >- (
      match_mp_tac PrePost_seqS
      \\ qexists_tac`P3`
      \\ conj_tac
      PrePost_strengthen_pre
      PrePost_write_regS


``init_cp2_state () s`` |> EVAL
init_cp2_state_def
|> SIMP_RULE (srw_ss()++boolSimps.LET_ss) []
f"init_cp2_state"
|>
*)

val install_code_def = Define`
  install_code initialPC (code:word32 list) =
    iteriS (λi c. MEMw_wrapper (initialPC + 4w*(i2w i)) 4 c) code`;

val clocked_whileS_def = Define`
  clocked_whileS clock vars cond body s =
    if 0n < clock then
      bindS (cond vars)
        (λcond_val s'.
          if cond_val then
            bindS (body vars) (λvars' s''. clocked_whileS (clock-1) vars' cond body s'') s'
          else returnS vars s') s
    else
      failS "timeout" s`;

val install_and_run_def = Define`
  install_and_run code clock =
    seqS
      (seqS (install_code 0x9000000040000000w code) (init_registers 0x9000000040000000w))
      (clocked_whileS clock () (λunit_var. fetch_and_execute ()) (λunit_var. returnS ()))`;

(* obtained from
     objdump -d test_raw_add.elf
   (with the cheri mips binutils version of objdump)

test_raw_add.elf:     file format elf64-bigmips

Disassembly of section .text:

9000000040000000 <start>:
9000000040000000:	24130001 	li	s3,1
9000000040000004:	24140002 	li	s4,2
9000000040000008:	02742020 	add	a0,s3,s4
900000004000000c:	240c0001 	li	t0,1
9000000040000010:	24050002 	li	a1,2
9000000040000014:	00ac2820 	add	a1,a1,t0
9000000040000018:	240c0001 	li	t0,1
900000004000001c:	24060002 	li	a2,2
9000000040000020:	01863020 	add	a2,t0,a2
9000000040000024:	24070001 	li	a3,1
9000000040000028:	00e73820 	add	a3,a3,a3
900000004000002c:	240c0001 	li	t0,1
9000000040000030:	240d0002 	li	t1,2
9000000040000034:	240e0003 	li	t2,3
9000000040000038:	018d7820 	add	t3,t0,t1
900000004000003c:	01ee4020 	add	a4,t3,t2
9000000040000040:	240c0001 	li	t0,1
9000000040000044:	240dffff 	li	t1,-1
9000000040000048:	018d4820 	add	a5,t0,t1
900000004000004c:	240cffff 	li	t0,-1
9000000040000050:	240dffff 	li	t1,-1
9000000040000054:	018d5020 	add	a6,t0,t1
9000000040000058:	240cffff 	li	t0,-1
900000004000005c:	240d0002 	li	t1,2
9000000040000060:	018d5820 	add	a7,t0,t1
9000000040000064:	240c0001 	li	t0,1
9000000040000068:	240dfffe 	li	t1,-2
900000004000006c:	018d8020 	add	s0,t0,t1
9000000040000070:	4082d000 	mtc0	v0,$26
	...
900000004000007c:	4082b800 	mtc0	v0,$23

9000000040000080 <end>:
9000000040000080:	1000ffff 	b	9000000040000080 <end>
9000000040000084:	00000000 	nop
*)


val test_raw_add_insts_def = Define`test_raw_add_insts =
  [0x24130001w:word32
  ;0x24140002w
  ;0x02742020w
  ;0x240c0001w
  ;0x24050002w
  ;0x00ac2820w
  ;0x240c0001w
  ;0x24060002w
  ;0x01863020w
  ;0x24070001w
  ;0x00e73820w
  ;0x240c0001w
  ;0x240d0002w
  ;0x240e0003w
  ;0x018d7820w
  ;0x01ee4020w
  ;0x240c0001w
  ;0x240dffffw
  ;0x018d4820w
  ;0x240cffffw
  ;0x240dffffw
  ;0x018d5020w
  ;0x240cffffw
  ;0x240d0002w
  ;0x018d5820w
  ;0x240c0001w
  ;0x240dfffew
  ;0x018d8020w
  ;0x4082d000w]`;

fun check_name n =
  EVAL ``EL ^(numSyntax.term_of_int n) gpr_names``;

val test_raw_add_post_def = Define`
  test_raw_add_post s = (
    bindS (rGPR 19w) (λs3. (* check_name 19 *)
    seqS (assert_expS (s3 = 1w) "add modified first input") (
    bindS (rGPR 20w) (λs4. (* check_name 20 *)
    seqS (assert_expS (s4 = 2w) "add modified second input") (
    bindS (rGPR 04w) (λa0. (* check_name 04 *)
    seqS (assert_expS (a0 = 3w) "add failed") (
    bindS (rGPR 05w) (λa1. (* check_name 05 *)
    seqS (assert_expS (a1 = 3w) "add into first input failed") (
    bindS (rGPR 06w) (λa2. (* check_name 06 *)
    seqS (assert_expS (a2 = 3w) "add into second input failed") (
    bindS (rGPR 07w) (λa3. (* check_name 07 *)
    seqS (assert_expS (a3 = 2w) "add into both inputs failed") (
    bindS (rGPR 08w) (λa4. (* check_name 08 *)
    seqS (assert_expS (a4 = 6w) "add-to-add pipeline failed") (
    bindS (rGPR 09w) (λa5. (* check_name 09 *)
    seqS (assert_expS (a5 = 0w) "positive plus negative to zero failed") (
    bindS (rGPR 10w) (λa6. (* check_name 10 *)
    seqS (assert_expS (a6 = 0xfffffffffffffffew) "negative plus negative to negative failed") (
    bindS (rGPR 11w) (λa7. (* check_name 11 *)
    seqS (assert_expS (a7 = 1w) "negative plus positive to positive failed") (
    bindS (rGPR 16w) (λs0. (* check_name 16 *)
    (assert_expS (s0 = 0xffffffffffffffffw) "positive plus negative to negative failed")))))))))))))))))))))) s
    = {(Value (),s)})`;

(*
EVAL ``(LENGTH s.regstate.GPR = 32) ⇒
       (bindS (rGPR 19w) (λs3. assert_expS (s3 = 1w) "fail") s = {(Value (),s)})``
|> SIMP_RULE (srw_ss())[]
*)

(* not true - m could produce lots of values that f collapses
val bindS_eq_sing_Value = Q.store_thm("bindS_eq_sing_Value",
  `(bindS m f s = {(Value x,s')}) ⇔
   ∃y s''. (m s = {(Value y,s'')}) ∧ (f y s'' = {(Value x,s')})`,
  rw[bindS_def] \\ reverse EQ_TAC >- ( rw[] \\ rw[] )
  \\ rw[]
  \\ Cases_on `m s` \\ fs[]
  \\ Cases_on`t` \\ fs[]
  >- ( BasicProvers.EVERY_CASE_TAC \\ fs[] )

  \\ CONV_TAC(LAND_CONV(REWR_CONV pred_setTheory.EXTENSION))
  \\ rw[pairTheory.pair_case_eq, pairTheory.FORALL_PROD,
        state_monadTheory.result_case_eq,PULL_EXISTS]
  \\ metis_tac[pairTheory.PAIR_EQ]
*)

(*
annoying because it depends on LENGTH s.regstate.GPR

EVAL ``rGPR 19w s``

val test_raw_add_post_eq =
  ``test_raw_add_post s``
  |> SIMP_CONV (srw_ss()) [test_raw_add_post_def]
*)

(*

val decoded_insts1 =
  listLib.MAP_CONV EVAL ``MAP decode ^(rhs(concl test_raw_add_insts_def))``

val (SOME_is, oty) = decoded_insts1 |> concl |> rhs |> listSyntax.dest_list
val asts = map rand SOME_is
val ls2 = listLib.MAP_CONV EVAL ``MAP SOME ^(listSyntax.mk_list(asts,optionSyntax.dest_option oty))``;
val test_raw_add_asts_def = Define`
  test_raw_add_asts = ^(rand(lhs(concl ls2)))`;

val decoded_insts = TRANS decoded_insts1 (SYM ls2)
  |> ONCE_REWRITE_RULE[GSYM test_raw_add_insts_def, GSYM test_raw_add_asts_def]
*)

(*
This is currently a non-starter, but something like it should be possible and
better than a manual PrePost proof! Perhaps with the right curated compset?
update: now it works! see compset below

EVAL ``install_code 0x9000000040000000w test_raw_add_insts s``
*)

val instance_Sail_values_Bitvector_Machine_word_mword_dict_thms =
  let
    val def = sail_valuesTheory.instance_Sail_values_Bitvector_Machine_word_mword_dict_def
    val tm = lhs(concl def)
    val rty = type_of tm
    val tyop = #1 (dest_type rty)
    val fields = TypeBase.fields_of rty
    fun mktm (fieldname,_) =
      Term[QUOTE(tyop^"_"^fieldname^" "), ANTIQUOTE tm]
    val thms = map (SIMP_CONV (srw_ss()) [def] o mktm) fields
  in LIST_CONJ thms end

val cap_addr_mask_thm =
  CONV_RULE(RAND_CONV EVAL)
    cheriTheory.cap_addr_mask_def

val seqS_returnS = Q.store_thm("seqS_returnS",
  `seqS (returnS x) f = f`,
  rw[FUN_EQ_THM] \\ EVAL_TAC \\ rw[IN_DEF]);

val seqS_returnS_s = Q.store_thm("seqS_returnS_s",
  `seqS (λs. returnS x (f s)) g = (λs. g (f s))`,
  rw[FUN_EQ_THM] \\ EVAL_TAC \\ rw[IN_DEF]);

val bindS_returnS_s = Q.store_thm("bindS_returnS_s",
  `bindS (λs. returnS v (f s)) g = (λs. g v (f s))`,
  rw[FUN_EQ_THM] \\ EVAL_TAC \\ rw[IN_DEF]);

val bindS_returnS_1 = Q.store_thm("bindS_returnS_1",
  `bindS (returnS v) f = f v`,
  rw[FUN_EQ_THM] \\ EVAL_TAC \\ rw[IN_DEF]);

val bindS_readS = Q.store_thm("bindS_readS",
  `bindS (readS f) m = (λs. m (f s) s)`,
  rw[FUN_EQ_THM] \\ EVAL_TAC \\ rw[IN_DEF]);

(*
val cstest = wordsLib.words_compset();
val () = computeLib.extend_compset [
  computeLib.Convs [
    (``bindS``, 2, HO_REWR_CONV bindS_returnS_s)
  ],
  computeLib.Defs [
    state_monadTheory.readS_def
  ]
] cstest;

computeLib.CBV_CONV cstest ``bindS (λs. returnS x s) g``
*)

val cs = wordsLib.words_compset();
val eval = computeLib.CBV_CONV cs;
val () = computeLib.extend_compset [
  computeLib.Extenders [
    optionLib.OPTION_rws,
    pairLib.add_pair_compset,
    combinLib.add_combin_compset,
    listLib.list_rws,
    pred_setLib.add_pred_set_compset,
    finite_mapLib.add_finite_map_compset,
    intReduce.add_int_compset,
    integer_wordLib.add_integer_word_compset,
    bitstringLib.add_bitstring_compset
  ],
  (* sail stuff *)
  (*
  computeLib.Defs (map #2 (ThmSetData.theory_data {settype = "compute", thy = "sail_values"})),
  *)
  computeLib.Defs [
    lemTheory.w2ui_def,
    lem_listTheory.list_combine_def,
    lem_machine_wordTheory.size_itself_def,
    sail_valuesTheory.make_the_value_def,
    sail_valuesTheory.nat_of_int_def,
    sail_valuesTheory.bool_of_bitU_def,
    sail_valuesTheory.bitU_of_bool_def,
    sail_valuesTheory.of_bits_failwith_def,
    sail_valuesTheory.size_itself_int_def,
    sail_valuesTheory.subrange_list_def,
    sail_valuesTheory.subrange_list_dec_def,
    sail_valuesTheory.subrange_list_inc_def,
    sail_valuesTheory.bools_of_int_def,
    sail_valuesTheory.bools_of_nat_def,
    sail_valuesTheory.take_list_def,
    sail_valuesTheory.drop_list_def,
    sail_valuesTheory.mem_bytes_of_bits_def,
    sail_valuesTheory.bytes_of_bits_def,
    sail_valuesTheory.byte_chunks_def,
    sail_valuesAuxiliaryTheory.bools_of_nat_aux_rw,
    sail_valuesAuxiliaryTheory.reverse_endianness_list_rw,
    sail_valuesAuxiliaryTheory.index_list_rw,
    (* sail_valuesTheory.instance_Sail_values_Bitvector_Machine_word_mword_dict_def, *)
    instance_Sail_values_Bitvector_Machine_word_mword_dict_thms,
    sail_valuesTheory.just_list_def,
    sail_valuesTheory.maybe_failwith_def,
    sail_valuesTheory.int_of_mword_def,
    sail_operators_mwordsTheory.and_vec_def,
    sail_operators_mwordsTheory.add_vec_def,
    sail_operators_mwordsTheory.subrange_vec_dec_def,
    sail_operators_mwordsTheory.vec_of_bits_def,
    sail_operators_mwordsTheory.reverse_endianness_def
  ],
  computeLib.Tys [
    ``:bitU``,
    ``:'a bits Bitvector_class``,
    ``:'a sequential_state``,
    ``:('a,'b) result``
  ],
  (* state monad *)
  computeLib.Defs [
    stateTheory.iteriS_def,
    stateAuxiliaryTheory.iterS_aux_rw,
    state_monadTheory.assert_expS_def,
    state_monadTheory.write_mem_eaS_def,
    state_monadTheory.write_mem_valS_def,
    state_monadTheory.write_tagS_def,
    state_monadTheory.write_mem_bytesS_def,
    state_monadTheory.updateS_def,
    state_monadTheory.maybe_failS_def,
    (*
    seqS_returnS,
    bindS_returnS_1,
    bindS_readS,
    *)
    bindS_def, returnS_def, seqS_def, readS_def
  ],
  (*
  computeLib.Convs [
    (``bindS``, 2, RAND_CONV eval THENC (RATOR_CONV(RAND_CONV eval)) THENC
                   HO_REWR_CONV bindS_returnS_s),
    (``seqS``, 2, RAND_CONV eval THENC (RATOR_CONV(RAND_CONV eval)) THENC HO_REWR_CONV seqS_returnS_s)
  ],
  *)
  (* cheri/mips model *)
  computeLib.Defs [
    decode_def,
    MEMw_wrapper_def,
    cap_addr_mask_thm,
    mips_extrasTheory.MEMea_def,
    mips_extrasTheory.MEMval_def,
    mips_extrasTheory.get_slice_int0_def,
    mips_extrasTheory.get_slice_int_bl_def,
    mips_extrasTheory.write_tag_bool_def,
    to_bits_def
  ],
  (* test_raw_add *)
  computeLib.Defs [
    test_raw_add_insts_def,
    install_code_def
  ]
]  cs;

(*

(computeLib.CBV_CONV cs (*THENC
 SIMP_CONV (srw_ss())
   [seqS_returnS_s,
    bindS_returnS_s]*))
  ``MEMw_wrapper (0x9000000040000000w + 4w * i2w 1) 4 (0x24140002w:word32) s``

computeLib.CBV_CONV cs
  `` OPTION_MAP v2w
             (just_list
                [SOME F; SOME F; SOME F; SOME F; SOME F; SOME F; SOME F;
                 SOME F; SOME F; SOME F; SOME F; SOME F; SOME F; SOME F;
                 SOME F; SOME F; SOME F; SOME F; SOME F; SOME F; SOME F;
                 SOME F; SOME F; SOME F; SOME F; SOME F; SOME F; SOME F;
                 SOME F; SOME F; SOME F; SOME F; SOME F; SOME T; SOME T;
                 SOME T; SOME T; SOME T; SOME T; SOME T; SOME F ])``
*)

val install_code_result =
  computeLib.CBV_CONV cs
    ``install_code 0x9000000040000000w test_raw_add_insts s``

(*
install_code_result
|> concl |> rhs |> rator |> rand
|> pairSyntax.dest_pair |> #2
|> dest_comb
*)

(*
maybe better to say something about looking up the code, and ignore the other effects..?

val code_installed_def = Define`
  code_installed initPC code s s' =
    let addrs = index_list (w2i initPC) (w2i initPC + 4 * (&LENGTH code)) 1 in
    s' = s with
      <| memstate :=
         s.memstate |++
           list_combine
             addrs (FLAT (MAP (REVERSE o THE o byte_chunks o MAP bitU_of_bool o w2v o reverse_endianness) code))
       ; tagstate := s.tagstate |++ MAP (λaddr. (w2i(cap_addr_mask && i2w addr), B0)) addrs
       ; write_ea := SOME (Write_plain, w2i initPC + 4 * (&LENGTH code) - 4, 4i)
       |>`;
*)

(* this is better, but not quite right yet...
val code_installed_def = Define`
  code_installed initPC code s =
    ∀k i. (k = w2i initPC + 4 * &i) ∧ i < LENGTH code ⇒
      case byte_chunks (MAP bitU_of_bool (w2v (reverse_endianness (EL i code)))) of
      | SOME chunks =>
        (FLOOKUP s.memstate (k+0) = SOME (EL 0 (REVERSE chunks))) ∧
        (FLOOKUP s.memstate (k+1) = SOME (EL 1 (REVERSE chunks))) ∧
        (FLOOKUP s.memstate (k+2) = SOME (EL 2 (REVERSE chunks))) ∧
        (FLOOKUP s.memstate (k+3) = SOME (EL 3 (REVERSE chunks)))
      | NONE => F`;
*)

val test_raw_add_thm = Q.store_thm("test_raw_add_thm",
  `PrePost
      (λs. 20 ≤ LENGTH s.regstate.GPR)
      (install_and_run test_raw_add_insts 100000)
      (λ_ s.  test_raw_add_post s)`,
  rw[install_and_run_def]
  \\ match_mp_tac PrePost_seqS
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`install_code initPC`
  \\ qexists_tac`λs. code_installed initPC test_raw_add_insts s ∧
                     init_registers_post s`
  (*
  \\ conj_tac
  >- (
    match_mp_tac PrePost_seqS \\ simp[]
    \\ qexists_tac`code_installed initPC test_raw_add_insts`
    \\ conj_tac
    >- (
      rw[PrePost_def,Abbr`initPC`]
      \\ fs[install_code_result]
      \\ BasicProvers.VAR_EQ_TAC
      \\ rw[code_installed_def]
      \\ pop_assum mp_tac
      \\ CONV_TAC(LAND_CONV(computeLib.CBV_CONV cs))
      \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[wordsTheory.NUMERAL_LESS_THM]))
      \\ strip_tac \\ BasicProvers.VAR_EQ_TAC
      \\ CONV_TAC(computeLib.CBV_CONV cs)

    )
    \\ cheat )
  *)
  \\ cheat);

(*
computeLib.CBV_CONV cs ``decode (EL 1 test_raw_add_insts)``

val th1 = EVAL ``THE (decode (EL 1 test_raw_add_insts))``

val s1 = EVAL ``init_cp0_state () (init_state (regs:regstate) o1 seed)``

val th2 = ``execute ^(rhs(concl th1)) ^s1``
  |> SIMP_CONV(srw_ss())[execute_def]
  |> SIMP_RULE(srw_ss())[execute_ADDIU_def]

f"bindS"
type_of ``execute ast ``
f"init_state"
execute_ADDIU_def
type_of``OPTION_BIND``
tyabbrev_info"M"
val (_, execute_rng) = dom_rng (type_of``execute``)
val (mdom, mrng) = dom_rng execute_rng
val state_ty = ``:regstate sequential_state``
dest_thy_type state_ty
TypeBase.fields_of state_ty
disable_tyabbrev_printing"rel"
dest_type``:unit M``

f"vec_of_bits"
f"of_bits_fail"
f"maybe_failw"
f"nat_of_int"
f"just_list"
f"sfunpow"
show_assums := true
*)

val _ = export_theory ();
