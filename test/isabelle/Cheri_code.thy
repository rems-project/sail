theory Cheri_code
  imports Cheri_lemmas "HOL-Library.Code_Char" "HOL-Library.Code_Target_Nat" "HOL-Library.Code_Target_Int"
begin

declare [[code abort: failwith]]

code_datatype
  DADDIU DADDU DADDI DADD ADD ADDI ADDU ADDIU DSUBU DSUB SUB SUBU AND0 ANDI OR0 
  ORI NOR XOR0 XORI LUI DSLL DSLL32 DSLLV DSRA DSRA32 DSRAV DSRL DSRL32 DSRLV SLL
  SLLV SRA SRAV SRL SRLV SLT SLTI SLTU SLTIU MOVN MOVZ MFHI MFLO MTHI MTLO MUL
  MULT MULTU DMULT DMULTU MADD MADDU MSUB MSUBU DIV DIVU DDIV DDIVU J JAL JR JALR
  BEQ BCMPZ SYSCALL_THREAD_START ImplementationDefinedStopFetching SYSCALL BREAK
  WAIT TRAPREG TRAPIMM Load Store LWL LWR SWL SWR LDL LDR SDL SDR CACHE PREF SYNC
  MFC0 HCF MTC0 TLBWI TLBWR TLBR TLBP RDHWR ERET CGetPerm CGetType CGetBase
  CGetLen CGetTag CGetSealed CGetOffset CGetPCC CGetPCCSetOffset CGetCause
  CSetCause CReadHwr CWriteHwr CAndPerm CToPtr CSub CPtrCmp CIncOffset
  CIncOffsetImmediate CSetOffset CSetBounds CSetBoundsImmediate CSetBoundsExact
  CClearTag CMOVX ClearRegs CFromPtr CBuildCap CCopyType CCheckPerm CCheckType
  CTestSubset CSeal CCSeal CUnseal CCall CReturn CBX CBZ CJALR CLoad CStore CSC
  CLC C2Dump RI CGetAddr

termination whileM sorry

fun prerr_endline' :: "String.literal \<Rightarrow> unit" where "prerr_endline' _ = ()"
lemma [code]: "prerr_endline s = prerr_endline' (String.implode s)" by auto

fun putchar' :: "char \<Rightarrow> unit" where "putchar' _ = ()"
lemma [code]: "putchar c = putchar' (char_of_nat (nat c))" by auto

code_identifier code_module List \<rightharpoonup> (OCaml) "List0"
code_printing constant String.implode \<rightharpoonup> (OCaml) "!(let l = _ in let res = Bytes.create (List.length l) in let rec imp i = function | [] -> res | c :: l -> Bytes.set res i c; imp (i + 1) l in imp 0 l)"

code_printing constant prerr_endline' \<rightharpoonup> (OCaml) "Pervasives.prerr'_endline"
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

definition "initial_state \<equiv> init_state initial_regstate (\<lambda>seed. (False, seed)) 0"

code_printing constant elf_entry \<rightharpoonup> (OCaml) "(Arith.Int'_of'_integer (Elf'_loader.elf'_entry _))"
code_printing constant get_time_ns \<rightharpoonup> (OCaml) "(Arith.Int'_of'_integer (Big'_int.big'_int'_of'_int (Pervasives.int'_of'_float (1e9 *. Unix.gettimeofday _))))"

export_code main initial_state liftState get_regval set_regval bindS returnS iteriS iterS
  write_char_mem integer_of_int int_of_integer "op + :: int \<Rightarrow> int \<Rightarrow> int" prerr_results
  in OCaml file "cheri_export.ml"

end
