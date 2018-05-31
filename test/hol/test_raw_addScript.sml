open HolKernel boolLib bossLib Parse
open intLib bitLib wordsLib
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

EVAL ``install_code 0x9000000040000000w test_raw_add_insts s``
*)

val test_raw_add_thm = Q.store_thm("test_raw_add_thm",
  `PrePost
      (λ_. T)
      (install_and_run test_raw_add_insts 100000)
      (λ_ s.  test_raw_add_post s)`,
  (*
  rw[install_and_run_def]
  \\ match_mp_tac PrePost_seqS
  \\ simp[]
  \\ qmatch_goalsub_abbrev_tac`install_code initPC`

  \\ qexists_tac`λs. code_installed initPC test_raw_add_insts s ∧
                     init_registers_post s`
  \\ conj_tac
  >- (
    match_mp_tac PrePost_seqS \\ simp[]
    \\ qexists_tac`code_installed initPC test_raw_add_insts`
    \\ conj_tac
    >- cheat
    \\ cheat )
  fetch_and_execute_def
  *)
cheat);

(*
val cs = wordsLib.words_compset();
val () = computeLib.extend_compset [
  computeLib.Extenders [
    intReduce.add_int_compset
  ],
  (* sail stuff *)
  computeLib.Defs [
    sail_valuesTheory.nat_of_int_def,
    sail_operators_mwordsTheory.subrange_vec_dec_def
  ],
  (* cheri/mips model *)
  computeLib.Defs [
    decode_def
  ],
  (* addition test *)
  computeLib.Defs [
    test_raw_add_insts_def
  ]
]  cs;

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
