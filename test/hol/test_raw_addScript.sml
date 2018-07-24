open HolKernel boolLib bossLib Parse
open intLib bitLib wordsLib integer_wordLib
open optionLib combinLib finite_mapLib bitstringLib
open state_monadTheory state_monad_lemmasTheory
open sail_valuesAuxiliaryTheory stateAuxiliaryTheory
open cheriTheory hoareTheory

val _ = new_theory "test_raw_add";

val _ = Globals.max_print_depth := 10;

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
      (seqS (install_code 0x40000000w code) (init_registers 0x9000000040000000w))
      (clocked_whileS clock () (λunit_var. fetch_and_execute ()) (λunit_var. returnS ()))`;

val PrePost_clocked_whileS_unit_T = Q.store_thm("PrePost_clocked_whileS_unit_T",
  `0 < k ∧
   PrePostE P (cond ()) (λb s. b ∧ R s) (K (K F)) ∧
   PrePost R (seqS (body ()) (clocked_whileS (k-1) () cond body)) Q
   ⇒ PrePost P (clocked_whileS k () cond body) Q`,
  rw[PrePost_def,PrePostE_def]
  \\ fs[Once clocked_whileS_def]
  \\ rfs[]
  \\ fs[bindS_def]
  \\ last_x_assum(qspec_then`s`mp_tac)
  \\ simp[]
  \\ disch_then(qspec_then`x`mp_tac)
  \\ simp[]
  \\ CASE_TAC \\ simp[]
  \\ BasicProvers.FULL_CASE_TAC \\ fs[]
  \\ strip_tac
  \\ rpt BasicProvers.VAR_EQ_TAC \\ fs[]
  \\ first_x_assum drule
  \\ simp[seqS_def, bindS_def,PULL_EXISTS]
  \\ disch_then match_mp_tac
  \\ BasicProvers.VAR_EQ_TAC
  \\ metis_tac[]);

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

fun mk_record_thms def =
  let
    val tm = lhs(concl (SPEC_ALL def))
    val rty = type_of tm
    val tyop = #1 (dest_type rty)
    val fields = TypeBase.fields_of rty
    fun mktm (fieldname,_) =
      Term[QUOTE(tyop^"_"^fieldname^" "), ANTIQUOTE tm]
    val thms = map (SIMP_CONV (srw_ss()) [def] o mktm) fields
  in LIST_CONJ thms end

val capRegToCapStruct_thms =
  mk_record_thms cheriTheory.capRegToCapStruct_def

val instance_Sail_values_Bitvector_Machine_word_mword_dict_thms =
  mk_record_thms sail_valuesTheory.instance_Sail_values_Bitvector_Machine_word_mword_dict_def

val default_cap_thms =
  mk_record_thms cheriTheory.default_cap_def

val nextPC_ref_thms =
  mk_record_thms cheri_typesTheory.nextPC_ref_def

val delayedPCC_ref_thms =
  mk_record_thms cheri_typesTheory.delayedPCC_ref_def

val delayedPC_ref_thms =
  mk_record_thms cheri_typesTheory.delayedPC_ref_def

val PCC_ref_thms =
  mk_record_thms cheri_typesTheory.PCC_ref_def

val PC_ref_thms =
  mk_record_thms cheri_typesTheory.PC_ref_def

val GPR_ref_thms =
  mk_record_thms cheri_typesTheory.GPR_ref_def

val nextPCC_ref_thms =
  mk_record_thms cheri_typesTheory.nextPCC_ref_def

val C_ref_thms =
  let
    fun get_def n = fetch"cheri_types"("C"^(StringCvt.padLeft#"0" 2(Int.toString n))^"_ref_def")
  in
    List.tabulate(32, mk_record_thms o get_def)
  end

val TLBEntry_ref_thms =
  let
    fun get_def n = fetch"cheri_types"("TLBEntry"^(StringCvt.padLeft#"0" 2(Int.toString n))^"_ref_def")
  in
    List.tabulate(64, mk_record_thms o get_def)
  end

val CP0Count_ref_thms =
  mk_record_thms cheri_typesTheory.CP0Count_ref_def

val CP0Compare_ref_thms =
  mk_record_thms cheri_typesTheory.CP0Compare_ref_def

val CP0Status_ref_thms =
  mk_record_thms cheri_typesTheory.CP0Status_ref_def

val CP0BadVAddr_ref_thms =
  mk_record_thms cheri_typesTheory.CP0BadVAddr_ref_def

val CP0EPC_ref_thms =
  mk_record_thms cheri_typesTheory.CP0EPC_ref_def

val CP0Cause_ref_thms =
  mk_record_thms cheri_typesTheory.CP0Cause_ref_def

val UART_WRITTEN_ref_thms =
  mk_record_thms cheri_typesTheory.UART_WRITTEN_ref_def

val UART_WDATA_ref_thms =
  mk_record_thms cheri_typesTheory.UART_WDATA_ref_def

val inCCallDelay_ref_thms =
  mk_record_thms cheri_typesTheory.inCCallDelay_ref_def

val TLBRandom_ref_thms =
  mk_record_thms cheri_typesTheory.TLBRandom_ref_def

val TLBWired_ref_thms =
  mk_record_thms cheri_typesTheory.TLBWired_ref_def

val TLBContext_ref_thms =
  mk_record_thms cheri_typesTheory.TLBContext_ref_def

val TLBXContext_ref_thms =
  mk_record_thms cheri_typesTheory.TLBXContext_ref_def

val TLBEntryHi_ref_thms =
  mk_record_thms cheri_typesTheory.TLBEntryHi_ref_def

val cap_addr_mask_thm =
  CONV_RULE(RAND_CONV EVAL)
    cheriTheory.cap_addr_mask_def

val branchPending_ref_thms =
  mk_record_thms cheri_typesTheory.branchPending_ref_def

val inBranchDelay_ref_thms =
  mk_record_thms cheri_typesTheory.inBranchDelay_ref_def

val instCount_ref_thms =
  mk_record_thms cheri_typesTheory.instCount_ref_def

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

val LENGTH_CapRegs = save_thm("LENGTH_CapRegs",
  EVAL ``LENGTH CapRegs``);

val LENGTH_TLBEntries = save_thm("LENGTH_TLBEntries",
  EVAL ``LENGTH TLBEntries``);

val cs0 = listLib.list_compset();
val () = computeLib.extend_compset [ computeLib.Defs [ CapRegs_def, TLBEntries_def ] ] cs0;

val EL_CapRegs = save_thm("EL_CapRegs",
  let
    fun f n = computeLib.CBV_CONV cs0 ``EL ^(numSyntax.term_of_int n) CapRegs``
  in
    LIST_CONJ (
      List.tabulate(LENGTH_CapRegs |> concl |> rhs |> numSyntax.int_of_term, f)
    )
  end);
val HD_CapRegs = computeLib.CBV_CONV cs0 ``HD CapRegs``;

val EL_TLBEntries = save_thm("EL_TLBEntries",
  let
    fun f n = computeLib.CBV_CONV cs0 ``EL ^(numSyntax.term_of_int n) TLBEntries``
  in
    LIST_CONJ (
      List.tabulate(LENGTH_TLBEntries |> concl |> rhs |> numSyntax.int_of_term, f)
    )
  end);
val HD_TLBEntries = computeLib.CBV_CONV cs0 ``HD TLBEntries``;

val bcs = computeLib.bool_compset();
val () = computeLib.extend_compset [
   computeLib.Tys [``:regstate``],
   computeLib.Defs (map #2 (ThmSetData.theory_data {settype = "compute", thy = "cheri_types" })),
  (* these should come out of regstate but seem not to... *)
  computeLib.Defs [
    cheri_typesTheory.regstate_brss__0_accfupds,
    cheri_typesTheory.regstate_brss__1_accfupds,
    cheri_typesTheory.regstate_brss__2_accfupds,
    cheri_typesTheory.regstate_brss__3_accfupds,
    cheri_typesTheory.regstate_brss__4_accfupds,
    cheri_typesTheory.regstate_brss__5_accfupds,
    cheri_typesTheory.regstate_brss__6_accfupds
  ],
   computeLib.Extenders [ combinLib.add_combin_compset ]
   ] bcs;
fun mk_regstate_record_thms def =
  let
    val tm = lhs(concl (SPEC_ALL def))
    val rty = type_of tm
    val tyop = #1 (dest_type rty)
    val fields = TypeBase.fields_of rty
    fun mktm (fieldname,_) =
      Term[QUOTE(tyop^"_"^fieldname^" "), ANTIQUOTE tm]
    val tms = map mktm fields
    fun expand tm =
      let
        val tm = SIMP_CONV (srw_ss()) [] tm |> concl |> rand
      in
        (PURE_ONCE_REWRITE_CONV[def] THENC
         (computeLib.CBV_CONV bcs))
        tm
      end
    fun expand2 tm =
      (RAND_CONV(REWR_CONV def) THENC
       (computeLib.CBV_CONV bcs))
      tm
    val thms = map expand tms
    val thms2 = map expand2 tms
  in LIST_CONJ (thms@thms2) end
val initial_regstate_thms =
  mk_regstate_record_thms cheriTheory.initial_regstate_def

val init_state_thms =
  mk_record_thms state_monadTheory.init_state_def

val cs = wordsLib.words_compset();
val eval = computeLib.CBV_CONV cs;
val () = computeLib.extend_compset [
  computeLib.Extenders [
    optionLib.OPTION_rws,
    pairLib.add_pair_compset,
    combinLib.add_combin_compset,
    listLib.list_rws,
    listLib.add_rich_list_compset,
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
    listTheory.LUPDATE_compute, (* TODO: add better compset for LUPDATE! *)
    (* listTheory.EL_LUPDATE, *)
    pred_setTheory.UNION_EMPTY,
    lemTheory.w2ui_def,
    lem_listTheory.list_combine_def,
    lem_machine_wordTheory.size_itself_def,
    sail_instr_kindsTheory.read_is_exclusive_def |> SIMP_RULE std_ss [FUN_EQ_THM],
    sail_valuesTheory.update_list_dec_def,
    sail_valuesTheory.update_list_inc_def,
    sail_valuesTheory.pow2_def,
    sail_valuesTheory.pow0_def,
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
    sail_valuesTheory.bits_of_mem_bytes_def,
    sail_valuesTheory.bits_of_bytes_def,
    sail_valuesTheory.byte_chunks_def,
    sail_valuesTheory.access_bv_dec_def,
    sail_valuesTheory.access_list_def,
    sail_valuesTheory.access_list_inc_def,
    sail_valuesAuxiliaryTheory.bools_of_nat_aux_rw,
    sail_valuesAuxiliaryTheory.reverse_endianness_list_rw,
    sail_valuesAuxiliaryTheory.index_list_rw,
    sail_valuesAuxiliaryTheory.repeat_rw,
    sail_valuesAuxiliaryTheory.pad_list_rw,
    (* sail_valuesTheory.instance_Sail_values_Bitvector_Machine_word_mword_dict_def, *)
    instance_Sail_values_Bitvector_Machine_word_mword_dict_thms,
    sail_valuesTheory.just_list_def,
    sail_valuesTheory.maybe_failwith_def,
    sail_valuesTheory.int_of_mword_def,
    sail_valuesTheory.make_the_value_def,
    sail_valuesTheory.access_list_dec_def,
    sail_valuesTheory.access_list_inc_def,
    sail_valuesTheory.exts_bv_def,
    sail_valuesTheory.exts_bits_def,
    sail_valuesTheory.ext_list_def,
    sail_operatorsTheory.arith_op_bv_int_def,
    sail_operators_mwordsTheory.concat_vec_def,
    sail_operators_mwordsTheory.access_vec_dec_def,
    sail_operators_mwordsTheory.replicate_bits_def,
    sail_operators_mwordsTheory.and_vec_def,
    sail_operators_mwordsTheory.add_vec_def,
    sail_operators_mwordsTheory.add_vec_int_def,
    sail_operators_mwordsTheory.update_subrange_vec_dec_def,
    sail_operators_mwordsTheory.subrange_vec_dec_def,
    sail_operators_mwordsTheory.vec_of_bits_def,
    sail_operators_mwordsTheory.sub_vec_int_def,
    sail_operators_mwordsTheory.reverse_endianness_def
  ],
  computeLib.Tys [
    ``:bitU``,
    ``:'a bits Bitvector_class``,
    ``:'a sequential_state``,
    ``:regstate``,
    ``:CapStruct``,
    ``:AccessLevel``,
    ``:MemAccessType``,
    ``:Exception``,
    ``:CauseReg``,
    ``:StatusReg``,
    ``:exception``,
    ``:read_kind``,
    ``:ast``,
    ``:'a ex``,
    ``:('a,'b,'c) register_ref``,
    ``:('a,'b) result``
  ],
  (* these should come out of regstate but seem not to... *)
  computeLib.Defs [
    cheri_typesTheory.regstate_brss__0_accfupds,
    cheri_typesTheory.regstate_brss__1_accfupds,
    cheri_typesTheory.regstate_brss__2_accfupds,
    cheri_typesTheory.regstate_brss__3_accfupds,
    cheri_typesTheory.regstate_brss__4_accfupds,
    cheri_typesTheory.regstate_brss__5_accfupds,
    cheri_typesTheory.regstate_brss__6_accfupds
  ],
  (* state monad *)
  computeLib.Defs [
    stateTheory.iteriS_def,
    stateTheory.or_boolS_def,
    stateAuxiliaryTheory.iterS_aux_rw,
    stateAuxiliaryTheory.foreachS_rw,
    state_monadTheory.assert_expS_def,
    state_monadTheory.write_mem_eaS_def,
    state_monadTheory.write_mem_valS_def,
    state_monadTheory.write_tagS_def,
    state_monadTheory.write_mem_bytesS_def,
    state_monadTheory.updateS_def,
    state_monadTheory.maybe_failS_def,
    state_monadTheory.read_regS_def,
    state_monadTheory.write_regS_def,
    (* delete the following two in interactive proof *)
    state_monadTheory.read_memS_def,
    state_monadTheory.read_mem_bytesS_def,
    (*
    seqS_returnS,
    bindS_returnS_1,
    bindS_readS,
    *)
    liftRS_def,
    early_returnS_def, catch_early_returnS_def, throwS_def,
    bindS_def, returnS_def, seqS_def, readS_def, try_catchS_def
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
    initial_regstate_thms,
    init_state_thms,
    decode_def,
    MEMw_wrapper_def,
    MEMr_wrapper_def,
    sign_extend1_def, (* delete this one in interactive proof *)
    mips_extrasTheory.sign_extend0_def,
    cap_addr_mask_thm,
    init_registers_def,
    init_cp0_state_def,
    init_cp2_state_def,
    cp2_next_pc_def,
    writeCapReg_def,
    LENGTH_TLBEntries,
    EL_TLBEntries, HD_TLBEntries,
    LENGTH_CapRegs,
    EL_CapRegs, HD_CapRegs,
    default_cap_thms,
    nextPC_ref_thms,
    delayedPCC_ref_thms,
    delayedPC_ref_thms,
    nextPCC_ref_thms,
    PCC_ref_thms,
    PC_ref_thms,
    GPR_ref_thms,
    branchPending_ref_thms,
    inBranchDelay_ref_thms,
    instCount_ref_thms,
    CP0Count_ref_thms,
    CP0Compare_ref_thms,
    CP0Status_ref_thms,
    CP0BadVAddr_ref_thms,
    CP0EPC_ref_thms,
    CP0Cause_ref_thms,
    LIST_CONJ TLBEntry_ref_thms,
    LIST_CONJ C_ref_thms,
    UART_WRITTEN_ref_thms,
    UART_WDATA_ref_thms,
    inCCallDelay_ref_thms,
    TLBRandom_ref_thms,
    TLBWired_ref_thms,
    TLBContext_ref_thms,
    TLBXContext_ref_thms,
    TLBEntryHi_ref_thms,
    TLBIndexMax_def,
    capStructToCapReg_def,
    capRegToCapStruct_thms,
    capStructToMemBits256_def,
    get_TLBEntry_valid_def,
    get_StatusReg_def,
    get_StatusReg_EXL_def,
    get_StatusReg_ERL_def,
    get_StatusReg_KSU_def,
    get_StatusReg_IE_def,
    get_CauseReg_IP_def,
    get_CauseReg_def,
    grantsAccess_def,
    int_of_AccessLevel_def,
    getCapBase_def,
    getCapTop_def,
    getCapPerms_def,
    cast_unit_vec0_def,
    set_StatusReg_BEV_def,
    set_StatusReg_EXL_def,
    fetch_and_execute_def,
    execute_def,
    execute_ADDIU_def,
    (* delete for interactive proof?
    execute_ADD_def |> SIMP_RULE std_ss [sign_extend1_def],
    *)
    execute_ADD_def,
    TranslatePC_def,
    TLBTranslate_def,
    TLBTranslate2_def,
    tlbSearch_def,
    tlbEntryMatch_def,
    SignalExceptionTLB_def,
    SignalException_def,
    SignalExceptionMIPS_def,
    ExceptionCode_def,
    TLBTranslateC_def, (* delete this one in interactive proof *)
    setCapOffset_def,
    set_CauseReg_BD_def,
    set_CauseReg_ExcCode_def,
    set_ContextReg_BadVPN2_def,
    set_XContextReg_XBadVPN2_def,
    set_XContextReg_XR_def,
    get_TLBEntryHiReg_def,
    set_TLBEntryHiReg_R_def,
    set_TLBEntryHiReg_VPN2_def,
    getAccessLevel_def,
    incrementCP0Count_def,
    mips_extrasTheory.skip_def,
    mips_extrasTheory.MEMea_def,
    mips_extrasTheory.MEMval_def,
    mips_extrasTheory.get_slice_int0_def,
    mips_extrasTheory.get_slice_int_bl_def,
    mips_extrasTheory.write_tag_bool_def,
    mips_extrasTheory.MEMr_def,
    zeros0_def,
    ones_def,
    bool_to_bits_def,
    bits_to_bool_def,
    bit_to_bool_def,
    to_bits_def,
    neq_bool_def,
    NotWordVal_def,
    MAX_PA_def,
    MAX_VA_def,
    MAX0_def,
    rGPR_def,
    wGPR_def
  ],
  (*
  (* delete these for interactive...  or always...*)
  computeLib.Defs (map #2 (ThmSetData.theory_data {settype = "compute", thy = "cheri" })),
  computeLib.Defs (map #2 (ThmSetData.theory_data {settype = "compute", thy = "cheri_types" })),
  computeLib.Defs (map #2 (ThmSetData.theory_data {settype = "compute", thy = "mips_extras" })),
  *)
  (* test_raw_add *)
  computeLib.Defs [
    test_raw_add_insts_def,
    install_code_def,
    install_and_run_def,
    clocked_whileS_def
  ]
]  cs;

val empty_state = ``init_state initial_regstate``;

val init_registers_result =
  ``init_registers vinitPC s``
  |> computeLib.CBV_CONV cs

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
    ``install_code 0x40000000w test_raw_add_insts s``

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

val code_installed_def = Define`
  code_installed initPC code s =
    ∀k i. (k = w2ui initPC + 4 * &i) ∧ i < LENGTH code ⇒
      case byte_chunks (MAP bitU_of_bool (w2v (reverse_endianness (EL i code)))) of
      | SOME chunks =>
        (FLOOKUP s.memstate (k+0) = SOME (EL 0 (REVERSE chunks))) ∧
        (FLOOKUP s.memstate (k+1) = SOME (EL 1 (REVERSE chunks))) ∧
        (FLOOKUP s.memstate (k+2) = SOME (EL 2 (REVERSE chunks))) ∧
        (FLOOKUP s.memstate (k+3) = SOME (EL 3 (REVERSE chunks)))
      | NONE => F`;

val registers_inited_def = Define`
  registers_inited initPC s =
    (s.regstate.nextPC = initPC)
    ∧ (s.regstate.CP0Status = Mk_StatusReg 0x400000w)
    ∧ (s.regstate.nextPCC = capStructToCapReg default_cap)
    (* ∧ a bunch of stuff about s.CX *)`;

(*
val cycle_result =
  computeLib.CBV_CONV cs ``fetch_and_execute () s``
  |> SIMP_RULE(srw_ss())[]
*)

(*
val result1 =
  ``install_and_run test_raw_add_insts 1 ^empty_state``
  |> time (computeLib.CBV_CONV cs)
*)

(*
doing this for 2 clock ticks blows up because I haven't got the right definitions in the compset...
trying with everything in cheri and cheri_types and mips_extra doesn't help...
update: works after adding LUPDATE_compute
*)
(*
val result2 =
  ``install_and_run test_raw_add_insts 2 ^empty_state``
  |> time (computeLib.CBV_CONV cs)
*)

(* 12s for 20 steps *)
(*
val result3 =
  ``install_and_run test_raw_add_insts 20 ^empty_state``
  |> time (computeLib.CBV_CONV cs)
*)

(* 15s to completion *)
val result4 =
  ``install_and_run test_raw_add_insts 40 ^empty_state``
  |> time (computeLib.CBV_CONV cs)

(*
val tm1 =
result |> concl |> rhs |> funpow 4 rand
|> rator |> rator |> rator |> rand |> rator |> rator |> rator |> rand |> rator |> rator |> rand
|> rator |> rand
|> CHANGED_CONV(computeLib.CBV_CONV cs)
type_of``B0``

val tm2 = ``initial_regstate.branchPending``
computeLib.CBV_CONV cs tm1
computeLib.CBV_CONV cs tm2
computeLib.CBV_CONV cs ``initial_regstate.branchPending``
dest_term tm1
dest_term tm2

set_trace"simplifier"0;
SIMP_CONV (srw_ss())[initial_regstate_thms] tm1
SIMP_CONV (srw_ss())[initial_regstate_thms] tm2
|> concl |> rhs |> aconv tm1

rator tm1
rator tm2

m``regstate_branchPending r = regstate_brss__2_branchPending (regstate_brss__sf2 r)``
*)

(*
val updates =
install_code_result
|> concl |> rhs
|> rator |> rand
|> rand |> rator
|> rand |> rand
|> finite_mapSyntax.strip_fupdate
|> #2
*)

val test_raw_add_thm = Q.store_thm("test_raw_add_thm",
  `PrePost
      (λs. s = init_state initial_regstate)
      (install_and_run test_raw_add_insts 40)
      (λ_ s.  test_raw_add_post s)`,
  rw[PrePost_def]
  \\ pop_assum(mp_tac o REWRITE_RULE[result4])
  \\ simp_tac (std_ss ++ pred_setLib.PRED_SET_ss) []
  \\ strip_tac \\ BasicProvers.VAR_EQ_TAC
  \\ ONCE_REWRITE_TAC[test_raw_add_post_def]
  \\ CONV_TAC(LAND_CONV(computeLib.CBV_CONV cs))
  \\ REFL_TAC);

(* interactive approach to slighly more general theorem

val TLBEntries_zero_def = Define`
  TLBEntries_zero rs ⇔
    (rs.TLBEntry00 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry01 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry02 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry03 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry04 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry05 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry06 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry07 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry08 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry09 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry10 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry11 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry12 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry13 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry14 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry15 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry16 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry17 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry18 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry19 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry20 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry21 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry22 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry23 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry24 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry25 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry26 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry27 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry28 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry29 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry30 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry31 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry32 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry33 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry34 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry35 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry36 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry37 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry38 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry39 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry40 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry41 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry42 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry43 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry44 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry45 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry46 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry47 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry48 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry49 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry50 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry51 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry52 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry53 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry54 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry55 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry56 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry57 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry58 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry59 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry60 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry61 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry62 = Mk_TLBEntry 0w) ∧
    (rs.TLBEntry63 = Mk_TLBEntry 0w)`;

val init_registers_result_initial =
  init_registers_result
  |> Q.GEN`s`
  |> Q.SPEC`<| regstate := initial_regstate |>`
  |> concl |> rhs |> rator |> rand |> rand |> rator |> rand |> rand
  |> funpow 4 RAND_CONV (SIMP_CONV (srw_ss()) [])
  |> concl |> rhs

val test_raw_add_thm = Q.store_thm("test_raw_add_thm",
  `PrePost
      (λs.
        (*
        ((s.regstate.GPR = REPLICATE 64 0w) ∧
         (s.regstate.branchPending = 0w) ∧
         (s.regstate.UART_WRITTEN = 0w) ∧
         (s.regstate.TLBRandom = 0w) ∧
         (s.regstate.TLBWired = 0w) ∧
         (TLBEntries_zero s.regstate) ∧
         (s.regstate.nextPCC = 0w) ∧
         (s.regstate.CP0Count = 0w) ∧
         (s.regstate.CP0Status = Mk_StatusReg 0w) ∧
         (s.regstate.CP0Compare = 0w))
         *)
         s.regstate = initial_regstate
        )
      (install_and_run test_raw_add_insts 100000)
      (λ_ s.  test_raw_add_post s)`,
  rw[install_and_run_def]
  \\ match_mp_tac PrePost_seqS
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`install_code initPC`
  \\ qmatch_goalsub_abbrev_tac`init_registers vinitPC`
  \\ qexists_tac`λs. code_installed initPC test_raw_add_insts s ∧
                     (* registers_inited vinitPC s ∧ *)
                     (s.regstate = ^init_registers_result_initial
                      (*^(init_registers_result |> concl |> rhs |> rator |> rand |> rand |> rator |> rand |> rand )*))
                      (*
                      <| nextPC := vinitPC ;
                         CP0Status := Mk_StatusReg 0x400000w;
                         nextPCC := capStructToCapReg default_cap |> )
                         *)
                         (*
                     ((s.regstate.branchPending = 0w) ∧
                      (s.regstate.GPR = REPLICATE 64 0w) ∧
                      (s.regstate.UART_WRITTEN = 0w) ∧
                      (s.regstate.TLBRandom = 0w) ∧
                      (s.regstate.TLBWired = 0w) ∧
                      (TLBEntries_zero s.regstate) ∧
                      (s.regstate.CP0Count = 0w) ∧
                      (s.regstate.CP0Compare = 0w)) *)`
  \\ conj_tac
  >- (
    match_mp_tac PrePost_seqS \\ simp[]
    \\ qexists_tac`λs. code_installed initPC test_raw_add_insts s ∧
                       (s.regstate = initial_regstate)
                       (*
                       ((s.regstate.branchPending = 0w) ∧
                        (s.regstate.GPR = REPLICATE 64 0w) ∧
                        (s.regstate.UART_WRITTEN = 0w) ∧
                        (s.regstate.TLBRandom = 0w) ∧
                        (s.regstate.TLBWired = 0w) ∧
                        (TLBEntries_zero s.regstate) ∧
                        (s.regstate.nextPCC = 0w) ∧
                        (s.regstate.CP0Count = 0w) ∧
                        (s.regstate.CP0Status = Mk_StatusReg 0w) ∧
                        (s.regstate.CP0Compare = 0w))*)`
    \\ conj_tac
    >- (
      rw[PrePost_def,Abbr`initPC`]
      \\ fs[install_code_result]
      \\ BasicProvers.VAR_EQ_TAC
      \\ rw[code_installed_def]
      \\ pop_assum mp_tac
      \\ CONV_TAC(LAND_CONV(computeLib.CBV_CONV cs))
      \\ CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[wordsTheory.NUMERAL_LESS_THM]))
      \\ strip_tac \\ BasicProvers.VAR_EQ_TAC \\ CONV_TAC(computeLib.CBV_CONV cs))
    \\ rw[PrePost_def,Abbr`initPC`]
    \\ pop_assum(assume_tac o REWRITE_RULE [init_registers_result,pred_setTheory.IN_INSERT,pred_setTheory.NOT_IN_EMPTY])
    \\ BasicProvers.VAR_EQ_TAC
    \\ qmatch_goalsub_abbrev_tac`v2w l1`
    (*
    \\ simp[registers_inited_def]
    *)
    \\ fs[code_installed_def]
    (*
    \\ fs[code_installed_def,Abbr`l1`(*,TLBEntries_zero_def*)]
    \\ CONV_TAC (computeLib.CBV_CONV cs)
    *)
    )
  \\ match_mp_tac (GEN_ALL PrePost_clocked_whileS_unit_T)
  \\ simp[seqS_returnS]
  \\ qmatch_goalsub_abbrev_tac`_.regstate = RS`
  \\ qmatch_goalsub_abbrev_tac`PrePostE CI`
  \\ qexists_tac`λs. code_installed initPC test_raw_add_insts s ∧
                     (s.regstate = RS with
                       <| GPR := LUPDATE 1w (32-1-19) RS.GPR
                        ; instCount := 1
                        ; CP0Count := 1w
                        ; TLBRandom := TLBIndexMax
                        ; PC := vinitPC
                        ; nextPC := vinitPC + 4w;
                        |>) `
  \\ fs[]
  \\ conj_tac
  >- (
    rw[PrePostE_def]
    \\ rw[fetch_and_execute_def]
    \\ simp[PrePost_def]
    \\ gen_tac \\ strip_tac \\ gen_tac
    \\ `s.regstate = RS` by fs[Abbr`CI`]
    \\ qunabbrev_tac`RS`
    \\ qunabbrev_tac`vinitPC`
    \\ rpt(CHANGED_TAC(CONV_TAC(LAND_CONV(computeLib.CBV_CONV cs)) \\ ASM_REWRITE_TAC[]))
    \\ ASM_REWRITE_TAC[TLBTranslateC_def]
    \\ rpt(CHANGED_TAC(CONV_TAC(LAND_CONV (computeLib.CBV_CONV cs)) \\ ASM_REWRITE_TAC []))
    \\ ASM_REWRITE_TAC[read_memS_def, read_mem_bytesS_def]
    (*
    \\ `s.regstate.nextPC = vinitPC` by fs[Abbr`CI`,registers_inited_def]
    \\ `(s.regstate.branchPending = 0w) ∧
        (s.regstate.GPR = REPLICATE 64 0w) ∧
        (s.regstate.UART_WRITTEN = 0w) ∧
        (s.regstate.TLBRandom = 0w) ∧
        (s.regstate.TLBWired = 0w) ∧
        (TLBEntries_zero s.regstate) ∧
        (s.regstate.nextPCC = capStructToCapReg default_cap) ∧
        (s.regstate.CP0Count = 0w) ∧
        (s.regstate.CP0Status = Mk_StatusReg 0x400000w) ∧
        (s.regstate.CP0Compare = 0w)` by fs[Abbr`CI`, registers_inited_def]
    \\ ntac 11 (pop_assum mp_tac)
    \\ PURE_REWRITE_TAC[AND_IMP_INTRO]
    \\ PURE_REWRITE_TAC[TLBEntries_zero_def]
    \\ CONV_TAC(LAND_CONV (computeLib.CBV_CONV cs))
    \\ PURE_REWRITE_TAC[GSYM AND_IMP_INTRO]
    \\ qunabbrev_tac`vinitPC`
    \\ ntac (10+64) strip_tac \\ ASM_REWRITE_TAC[]
    \\ rpt(CHANGED_TAC(CONV_TAC(LAND_CONV (computeLib.CBV_CONV cs)) \\ ASM_REWRITE_TAC []))
    \\ ASM_REWRITE_TAC[TLBTranslateC_def]
    \\ rpt(CHANGED_TAC(CONV_TAC(LAND_CONV (computeLib.CBV_CONV cs)) \\ ASM_REWRITE_TAC []))
    \\ ASM_REWRITE_TAC[read_memS_def, read_mem_bytesS_def]
    *)
    \\ ASM_SIMP_TAC (bool_ss ++ boolSimps.LET_ss) [bindS_returnS_1, bindS_readS]
    \\ qmatch_goalsub_abbrev_tac`bindS (bindS m1 m2) m3 ss`
    \\ qunabbrev_tac`m1`
    \\ `ss.memstate = s.memstate` by simp[Abbr`ss`]
    \\ CHANGED_TAC(CONV_TAC(LAND_CONV (computeLib.CBV_CONV cs)) \\ ASM_REWRITE_TAC [])
    \\ qunabbrev_tac`m2`
    \\ CONV_TAC(DEPTH_CONV BETA_CONV)
    \\ qmatch_goalsub_abbrev_tac`just_list ls`
    \\ qmatch_goalsub_abbrev_tac`f ls`
    \\ qunabbrev_tac`ls`
    \\ CHANGED_TAC(CONV_TAC(LAND_CONV (computeLib.CBV_CONV cs)) \\ ASM_REWRITE_TAC [])
    \\ `code_installed initPC test_raw_add_insts s` by fs[Abbr`CI`]
    \\ pop_assum(mp_tac o SIMP_RULE(srw_ss())[code_installed_def])
    \\ disch_then(qspec_then`0`mp_tac)
    \\ impl_tac >- EVAL_TAC
    \\ disch_then(mp_tac o CONV_RULE(RATOR_CONV(computeLib.CBV_CONV cs)))
    \\ qunabbrev_tac`initPC`
    \\ disch_then(mp_tac o CONV_RULE(computeLib.CBV_CONV cs))
    \\ strip_tac
    \\ map_every qunabbrev_tac[`f`,`m3`]
    \\ CHANGED_TAC(ASM_REWRITE_TAC[sign_extend1_def])
    \\ CHANGED_TAC(CONV_TAC(LAND_CONV (computeLib.CBV_CONV cs)) \\ ASM_REWRITE_TAC [])
    \\ qunabbrev_tac`ss`
    \\ CHANGED_TAC(CONV_TAC(LAND_CONV (computeLib.CBV_CONV cs)) \\ ASM_REWRITE_TAC [])
    \\ SIMP_TAC (srw_ss()) []
    \\ strip_tac \\ BasicProvers.VAR_EQ_TAC
    \\ fs[code_installed_def,Abbr`CI`]
    \\ ONCE_REWRITE_TAC[cheri_typesTheory.regstate_component_equality]
    \\ CONV_TAC(computeLib.CBV_CONV cs)
    \\ rpt AP_THM_TAC \\ AP_TERM_TAC \\ CONV_TAC(computeLib.CBV_CONV cs) )
  \\ qunabbrev_tac`RS`
  \\ qunabbrev_tac`CI`
  \\ CONV_TAC (PATH_CONV"llrar"(computeLib.CBV_CONV cs))
  \\ qmatch_goalsub_abbrev_tac`v2w ll`
  \\ match_mp_tac (GEN_ALL PrePost_clocked_whileS_unit_T)
  \\ simp[seqS_returnS]
  \\ qmatch_goalsub_abbrev_tac`_.regstate = RS`
  \\ qmatch_goalsub_abbrev_tac`PrePostE CI`
  \\ qexists_tac`λs. code_installed initPC test_raw_add_insts s ∧
                     (s.regstate = RS with
                       <| GPR := LUPDATE 2w (32-1-20) RS.GPR
                        ; instCount := 2
                        ; CP0Count := 2w
                        ; TLBRandom := 62w
                        ; PC := vinitPC + 4w
                        ; nextPC := vinitPC + 8w;
                        |>) `
  \\ fs[]
  \\ conj_tac
  >- (
    rw[PrePostE_def]
    \\ rw[fetch_and_execute_def]
    \\ simp[PrePost_def]
    \\ gen_tac \\ strip_tac \\ gen_tac
    \\ `s.regstate = RS` by fs[Abbr`CI`]
    \\ qunabbrev_tac`RS`
    \\ qunabbrev_tac`vinitPC`
    \\ qunabbrev_tac`ll`
    \\ rpt(CHANGED_TAC(CONV_TAC(LAND_CONV(computeLib.CBV_CONV cs)) \\ ASM_REWRITE_TAC[]))
    \\ ASM_REWRITE_TAC[TLBTranslateC_def]
    \\ rpt(CHANGED_TAC(CONV_TAC(LAND_CONV (computeLib.CBV_CONV cs)) \\ ASM_REWRITE_TAC []))
    \\ ASM_REWRITE_TAC[read_memS_def, read_mem_bytesS_def]
    \\ ASM_SIMP_TAC (bool_ss ++ boolSimps.LET_ss) [bindS_returnS_1, bindS_readS]
    \\ qmatch_goalsub_abbrev_tac`bindS (bindS m1 m2) m3 ss`
    \\ qunabbrev_tac`m1`
    \\ `ss.memstate = s.memstate` by simp[Abbr`ss`]
    \\ CHANGED_TAC(CONV_TAC(LAND_CONV (computeLib.CBV_CONV cs)) \\ ASM_REWRITE_TAC [])
    \\ qunabbrev_tac`m2`
    \\ CONV_TAC(DEPTH_CONV BETA_CONV)
    \\ qmatch_goalsub_abbrev_tac`just_list ls`
    \\ qmatch_goalsub_abbrev_tac`f ls`
    \\ qunabbrev_tac`ls`
    \\ CHANGED_TAC(CONV_TAC(LAND_CONV (computeLib.CBV_CONV cs)) \\ ASM_REWRITE_TAC [])
    \\ `code_installed initPC test_raw_add_insts s` by fs[Abbr`CI`]
    \\ pop_assum(mp_tac o SIMP_RULE(srw_ss())[code_installed_def])
    \\ disch_then(qspec_then`1`mp_tac)
    \\ impl_tac >- EVAL_TAC
    \\ disch_then(mp_tac o CONV_RULE(RATOR_CONV(computeLib.CBV_CONV cs)))
    \\ qunabbrev_tac`initPC`
    \\ disch_then(mp_tac o CONV_RULE(computeLib.CBV_CONV cs))
    \\ strip_tac
    \\ map_every qunabbrev_tac[`f`,`m3`]
    \\ CHANGED_TAC(ASM_REWRITE_TAC[sign_extend1_def])
    \\ CHANGED_TAC(CONV_TAC(LAND_CONV (computeLib.CBV_CONV cs)) \\ ASM_REWRITE_TAC [])
    \\ qunabbrev_tac`ss`
    \\ CHANGED_TAC(CONV_TAC(LAND_CONV (computeLib.CBV_CONV cs)) \\ ASM_REWRITE_TAC [])
    \\ SIMP_TAC (srw_ss()) []
    \\ strip_tac \\ BasicProvers.VAR_EQ_TAC
    \\ fs[code_installed_def,Abbr`CI`]
    \\ ONCE_REWRITE_TAC[cheri_typesTheory.regstate_component_equality]
    \\ qmatch_goalsub_abbrev_tac`v2w ll`
    \\ CONV_TAC(computeLib.CBV_CONV cs)
    \\ rpt AP_THM_TAC \\ AP_TERM_TAC \\ CONV_TAC(computeLib.CBV_CONV cs))
  \\ qunabbrev_tac`RS`
  \\ qunabbrev_tac`CI`
  \\ CONV_TAC (PATH_CONV"llrar"(computeLib.CBV_CONV cs))
  \\ match_mp_tac (GEN_ALL PrePost_clocked_whileS_unit_T)
  \\ simp[seqS_returnS]
  \\ qmatch_goalsub_abbrev_tac`_.regstate = RS`
  \\ qexists_tac`λs. code_installed initPC test_raw_add_insts s ∧
                     (s.regstate = RS with
                       <| GPR := LUPDATE 3w (32-1-4) RS.GPR
                        ; instCount := 3
                        ; CP0Count := 3w
                        ; TLBRandom := 62w
                        ; PC := vinitPC + 8w
                        ; nextPC := vinitPC + 12w;
                        |>) `
  \\ fs[]
  \\ conj_tac
  >- (
    rw[PrePostE_def]
    \\ rw[fetch_and_execute_def]
    \\ simp[PrePost_def]
    \\ gen_tac \\ strip_tac \\ gen_tac
    \\ qunabbrev_tac`RS`
    \\ qunabbrev_tac`vinitPC`
    \\ qunabbrev_tac`ll`
    \\ rpt(CHANGED_TAC(CONV_TAC(LAND_CONV(computeLib.CBV_CONV cs)) \\ ASM_REWRITE_TAC[]))
    \\ ASM_REWRITE_TAC[TLBTranslateC_def]
    \\ rpt(CHANGED_TAC(CONV_TAC(LAND_CONV (computeLib.CBV_CONV cs)) \\ ASM_REWRITE_TAC []))
    \\ ASM_REWRITE_TAC[read_memS_def, read_mem_bytesS_def]
    \\ ASM_SIMP_TAC (bool_ss ++ boolSimps.LET_ss) [bindS_returnS_1, bindS_readS]
    \\ qmatch_goalsub_abbrev_tac`bindS (bindS m1 m2) m3 ss`
    \\ qunabbrev_tac`m1`
    \\ `ss.memstate = s.memstate` by simp[Abbr`ss`]
    \\ CHANGED_TAC(CONV_TAC(LAND_CONV (computeLib.CBV_CONV cs)) \\ ASM_REWRITE_TAC [])
    \\ qunabbrev_tac`m2`
    \\ CONV_TAC(DEPTH_CONV BETA_CONV)
    \\ qmatch_goalsub_abbrev_tac`just_list ls`
    \\ qmatch_goalsub_abbrev_tac`f ls`
    \\ qunabbrev_tac`ls`
    \\ CHANGED_TAC(CONV_TAC(LAND_CONV (computeLib.CBV_CONV cs)) \\ ASM_REWRITE_TAC [])
    \\ qpat_assum`code_installed _ _ _`(mp_tac o SIMP_RULE(srw_ss())[code_installed_def])
    \\ disch_then(qspec_then`2`mp_tac)
    \\ impl_tac >- EVAL_TAC
    \\ disch_then(mp_tac o CONV_RULE(RATOR_CONV(computeLib.CBV_CONV cs)))
    \\ qunabbrev_tac`initPC`
    \\ disch_then(mp_tac o CONV_RULE(computeLib.CBV_CONV cs))
    \\ strip_tac
    \\ map_every qunabbrev_tac[`f`,`m3`]
    \\ CHANGED_TAC(ASM_REWRITE_TAC[sign_extend1_def])
    \\ CHANGED_TAC(CONV_TAC(LAND_CONV (computeLib.CBV_CONV cs)) \\ ASM_REWRITE_TAC [])
    \\ qunabbrev_tac`ss`
    \\ CHANGED_TAC(ASM_REWRITE_TAC[execute_ADD_def, sign_extend1_def])
    \\ qmatch_asmsub_abbrev_tac`v2w ll`
    \\ CHANGED_TAC(CONV_TAC(LAND_CONV (computeLib.CBV_CONV cs)) \\ ASM_REWRITE_TAC [])
    \\ simp[]
    \\ strip_tac \\ BasicProvers.VAR_EQ_TAC
    \\ fs[code_installed_def]
    \\ ONCE_REWRITE_TAC[cheri_typesTheory.regstate_component_equality]
    \\ rpt(conj_tac >- CONV_TAC(computeLib.CBV_CONV cs))
    \\ rpt AP_THM_TAC \\ AP_TERM_TAC \\ CONV_TAC(computeLib.CBV_CONV cs))
(*

    top_goal() |> #2 |> rand |> rator |> rand |> rand |> rator |> rator |> rand |> rand
    |> listSyntax.dest_list |> #1 |> length
    top_goal() |> #2 |> dest_imp |> #1 |> funpow 5 rand
    |> rand |> rand |> rator |> rand |> rator |> rand |> rand |> rator |> rator |> rand
    |> rator |> rator |> rand |> rand

    computeLib.CBV_CONV cs ``LENGTH (LUPDATE 1n 2 [3;4;9;8;7;76;3;8;9;9;9;9;0;0;0])``

    |> rator |> rand |> rand
    |> rator |> rand |> rator

  execute_ADD_def
  |> SIMP_RULE std_ss [sign_extend1_def]
  |> SPEC_ALL
  |> concl |> rhs

``SignalException XTLBRefillL s``
|> SIMP_CONV(srw_ss())[SignalException_def]
|> concl |> rhs |> rator |> rand
|> dest_abs |> #2 |> rator

``
(capRegToCapStruct
                    (v2w
                       [T; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                        F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; T; T; T;
                        T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T;
                        T; T; T; T; T; T; T; T; T; T; F; F; F; F; F; F; F; F;
                        F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                        F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                        F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                        F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                        F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                        F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F; F;
                        F; F; F; F; F; F; F; F; F; F; F; F; F; T; T; T; T; T;
                        T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T;
                        T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T;
                        T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T; T;
                        T; T; T; T; T])).CapStruct_access_system_regs
``
(*
set_trace"simplifier"0
SIMP_CONV (srw_ss()) []
``
regstate_brss__6_TLBRandom
(regstate_brss__6_nextPC_fupd (K 0x9000000040000004w)
(regstate_brss__6_PC_fupd (K 0x9000000040000000w)
                  (regstate_brss__sf6 s.regstate)))``

    top_goal() |> #2 |> dest_imp |> #1 |> dest_exists |> #2 |> strip_conj |> last
    |> dest_exists |> #2 |> strip_conj |> last |> rand
    |> rator |> funpow 13 rand

    top_goal() |> #2 |> dest_imp |> #1 |> funpow 5 rand
    |> rator |> rator |> rator
    |> rand |> rand |> rator |> rand |> rator |> rand |> rand |> rand
    |> rator

    top_goal() |> #1 |> el 9 |> lhs
    |> computeLib.CBV_CONV cs |> concl |> rhs |> rator

    |> rator |> funpow 13 rand

    top_goal() |> #1 |> el 2 |> rand |> rhs |> rator
    \\ pop_assum(SUBST_ALL_TAC)
*)
*)

  \\ cheat);
*)

(*
computeLib.CBV_CONV cs ``decode (EL 1 test_raw_add_insts)``

val th1 = EVAL ``THE (decode (EL 1 test_raw_add_insts))``

val s1 = EVAL ``init_cp0_state () (init_state (regs:regstate))``

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
