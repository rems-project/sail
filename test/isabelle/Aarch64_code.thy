theory Aarch64_code
  imports
    Aarch64_lemmas
    "HOL-Library.Code_Char"
    "HOL-Library.Code_Target_Nat"
    "HOL-Library.Code_Target_Int"
    "HOL-Library.Code_Real_Approx_By_Float"
begin

declare [[code abort: failwith]]

termination shl_int by lexicographic_order
termination while sorry
termination whileM sorry
termination untilM sorry

declare insert_code[code del]
declare union_coset_filter[code del]

lemma [code]: "(set xs) \<union> (set ys) = set (xs @ ys)"
  by auto

lemma [code]: "insert x (set xs) = set (x # xs)"
  by auto

declare [[code drop:
  "less :: real \<Rightarrow> real \<Rightarrow> bool"
  "less_eq :: real \<Rightarrow> real \<Rightarrow> bool"
  "floor :: real \<Rightarrow> int"]]

code_printing constant "floor :: real \<Rightarrow> int" \<rightharpoonup> (OCaml) "(Int'_of'_integer (Big'_int.big'_int'_of'_int (Pervasives.int'_of'_float (Pervasives.floor _))))"

code_identifier constant ASR \<rightharpoonup> (OCaml) "Aarch64.asr0"
code_identifier constant LSL \<rightharpoonup> (OCaml) "Aarch64.lsl0"
code_identifier constant LSR \<rightharpoonup> (OCaml) "Aarch64.lsr0"

fun prerr_endline' :: "String.literal \<Rightarrow> unit" where "prerr_endline' _ = ()"
lemma [code]: "prerr_endline s = prerr_endline' (String.implode s)" by auto

fun putchar' :: "char \<Rightarrow> unit" where "putchar' _ = ()"
lemma [code]: "putchar c = putchar' (char_of_nat (nat c))" by auto

code_identifier code_module List \<rightharpoonup> (OCaml) "List0"
code_printing constant String.implode \<rightharpoonup> (OCaml) "!(let l = _ in let res = Bytes.create (List.length l) in let rec imp i = function | [] -> res | c :: l -> Bytes.set res i c; imp (i + 1) l in imp 0 l)"

code_printing constant prerr_endline' \<rightharpoonup> (OCaml) "Pervasives.prerr'_endline"
code_printing constant putchar' \<rightharpoonup> (OCaml) "Pervasives.print'_char"

fun write_char_mem :: "int \<Rightarrow> char \<Rightarrow> (regstate, unit, exception) monadS" where
  "write_char_mem addr c =
     bindS (write_mem_eaS BC_bitU_list Write_plain (bits_of_int 64 addr) 1) (\<lambda>_.
     bindS (write_mem_valS BC_bitU_list (bits_of_nat 8 (nat_of_char c))) (\<lambda>_.
     returnS ()))"

definition "initial_state \<equiv> init_state initial_regstate"

code_printing constant elf_entry \<rightharpoonup> (OCaml) "(Int'_of'_integer (Elf'_loader.elf'_entry _))"
termination BigEndianReverse sorry
export_code main initial_state liftState get_regval set_regval bindS returnS iteriS iterS write_char_mem integer_of_int int_of_integer "op + :: int \<Rightarrow> int \<Rightarrow> int" prerr_results in OCaml module_name "Aarch64" file "aarch64_export.ml"

end
