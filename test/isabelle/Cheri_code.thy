theory Cheri_code
  imports Cheri_lemmas "HOL-Library.Code_Char" "HOL-Library.Code_Target_Nat" "HOL-Library.Code_Target_Int"
begin

declare [[code abort: failwith]]

code_datatype
  DADDIU DADDU DADDI DADD ADD ADDI ADDU ADDIU DSUBU DSUB SUB SUBU AND0 ANDI OR0
  ORI NOR XOR0 XORI LUI DSLL DSLL32 DSLLV DSRA DSRA32 DSRAV DSRL DSRL32 DSRLV SLL
  SLLV SRA SRAV SRL SRLV SLT SLTI SLTU SLTIU MOVN MOVZ MFHI MFLO MTHI MTLO MUL
  MULT MULTU DMULT DMULTU MADD MADDU MSUB MSUBU DIV DIVU DDIV DDIVU J JAL JR JALR
  BEQ BCMPZ SYSCALL BREAK WAIT TRAPREG TRAPIMM Load Store LWL LWR SWL SWR LDL LDR
  SDL SDR CACHE SYNC MFC0 HCF MTC0 TLBWI TLBWR TLBR TLBP RDHWR ERET CGetPerm
  CGetType CGetBase CGetLen CGetTag CGetSealed CGetOffset CGetPCC
  CGetPCCSetOffset CGetCause CSetCause CReadHwr CWriteHwr CAndPerm CToPtr CSub
  CPtrCmp CIncOffset CIncOffsetImmediate CSetOffset CSetBounds
  CSetBoundsImmediate CSetBoundsExact CClearTag CMOVX ClearRegs CFromPtr
  CBuildCap CCopyType CCheckPerm CCheckType CTestSubset CSeal CCSeal CUnseal
  CCall CReturn CBX CBZ CJALR CLoad CStore CSC CLC C2Dump RI CGetAddr

(* Fake termination proofs of loops for code generation *)
lemma whileM_dom: "whileM_dom (vars, cond, body)" sorry
termination whileM using whileM_dom by auto
lemma whileS_dom: "whileS_dom (vars, cond, body, s)" sorry
termination whileS using whileS_dom by auto

lemma liftS_whileM: "\<lbrakk>whileM vars cond body\<rbrakk>\<^sub>S = whileS vars (liftS \<circ> cond) (liftS \<circ> body)"
  by (intro ext liftState_whileM[OF whileS_dom whileM_dom])

(* Pre-lift main loop to state monad to gain some performance *)
fun mainS :: "unit \<Rightarrow> (regstate, unit, exception) monadS" where
  "mainS () = \<lbrakk>main ()\<rbrakk>\<^sub>S"

schematic_goal liftS_main[symmetric, code]: "?m = mainS"
  by (intro ext)
     (simp add: main_def liftState_simp liftS_whileM comp_def del: whileM.simps whileS.simps
           cong: bindS_cong if_cong)

fun print_endline' :: "String.literal \<Rightarrow> unit" where "print_endline' _ = ()"
lemma [code]: "print_endline s = print_endline' (String.implode s)" by auto

fun prerr_endline' :: "String.literal \<Rightarrow> unit" where "prerr_endline' _ = ()"
lemma [code]: "prerr_endline s = prerr_endline' (String.implode s)" by auto

fun prerr_string' :: "String.literal \<Rightarrow> unit" where "prerr_string' _ = ()"
lemma [code]: "prerr_string s = prerr_string' (String.implode s)" by auto

fun putchar' :: "char \<Rightarrow> unit" where "putchar' _ = ()"
lemma [code]: "putchar c = putchar' (char_of_nat (nat c))" by auto

code_identifier code_module List \<rightharpoonup> (OCaml) "List0"
code_printing constant String.implode \<rightharpoonup> (OCaml) "!(let l = _ in let res = Bytes.create (List.length l) in let rec imp i = function | [] -> res | c :: l -> Bytes.set res i c; imp (i + 1) l in imp 0 l)"

code_printing constant print_endline' \<rightharpoonup> (OCaml) "Pervasives.print'_endline"
code_printing constant prerr_endline' \<rightharpoonup> (OCaml) "Pervasives.prerr'_endline"
code_printing constant prerr_string' \<rightharpoonup> (OCaml) "Pervasives.prerr'_string"
code_printing constant putchar' \<rightharpoonup> (OCaml) "Pervasives.print'_char"

declare insert_code[code del]
declare union_coset_filter[code del]

lemma set_union_append[code]: "(set xs) \<union> (set ys) = set (xs @ ys)"
  by auto

lemma set_insert_Cons[code]: "insert x (set xs) = set (x # xs)"
  by auto

declare ast.case[code]

fun write_char_mem :: "int \<Rightarrow> char \<Rightarrow> (regstate, unit, exception) monadS" where
  "write_char_mem addr c =
     bindS (write_mem_eaS BC_bitU_list Write_plain (bits_of_int 64 addr) 1) (\<lambda>_.
     bindS (write_mem_valS BC_bitU_list (bits_of_nat 8 (nat_of_char c))) (\<lambda>_.
     returnS ()))"

definition "initial_state \<equiv> init_state initial_regstate\<lparr>memstate := (\<lambda>_. Some [B0, B0, B0, B0, B0, B0, B0, B0])\<rparr>"

code_printing constant elf_entry \<rightharpoonup> (OCaml) "(Arith.Int'_of'_integer (Elf'_loader.elf'_entry _))"
code_printing constant get_time_ns \<rightharpoonup> (OCaml) "(Arith.Int'_of'_integer (Big'_int.big'_int'_of'_int (Pervasives.int'_of'_float (1e9 *. Unix.gettimeofday _))))"

export_code mainS initial_state liftState get_regval set_regval bindS returnS iteriS iterS
  write_char_mem integer_of_int int_of_integer "op + :: int \<Rightarrow> int \<Rightarrow> int" prerr_results
  in OCaml file "cheri_export.ml"

end
