theory Sail_values_lemmas
  imports Sail_values
begin

lemma nat_of_int_nat_simps[simp]: "nat_of_int = nat" by (auto simp: nat_of_int_def)

termination reverse_endianness_list by (lexicographic_order simp add: drop_list_def)

termination index_list
  by (relation "measure (\<lambda>(i, j, step). nat ((j - i + step) * sgn step))") auto

lemma just_list_map_Some[simp]: "just_list (map Some v) = Some v" by (induction v) auto

lemma just_list_None_iff[simp]: "just_list xs = None \<longleftrightarrow> None \<in> set xs"
  by (induction xs) (auto split: option.splits)

lemma just_list_Some_iff[simp]: "just_list xs = Some ys \<longleftrightarrow> xs = map Some ys"
  by (induction xs arbitrary: ys) (auto split: option.splits)

lemma just_list_cases:
  assumes "just_list xs = y"
  obtains (None) "None \<in> set xs" and "y = None"
        | (Some) ys where "xs = map Some ys" and "y = Some ys"
  using assms by (cases y) auto

lemma bitops_bitU_of_bool[simp]:
  "and_bit (bitU_of_bool x) (bitU_of_bool y) = bitU_of_bool (x \<and> y)"
  "or_bit (bitU_of_bool x) (bitU_of_bool y) = bitU_of_bool (x \<or> y)"
  "xor_bit (bitU_of_bool x) (bitU_of_bool y) = bitU_of_bool ((x \<or> y) \<and> \<not>(x \<and> y))"
  "not_bit (bitU_of_bool x) = bitU_of_bool (\<not>x)"
  "not_bit \<circ> bitU_of_bool = bitU_of_bool \<circ> Not"
  by (auto simp: bitU_of_bool_def not_bit_def)

lemma image_bitU_of_bool_B0_B1: "bitU_of_bool ` bs \<subseteq> {B0, B1}"
  by (auto simp: bitU_of_bool_def split: if_splits)

lemma bool_of_bitU_bitU_of_bool[simp]:
  "bool_of_bitU \<circ> bitU_of_bool = Some"
  "bool_of_bitU \<circ> (bitU_of_bool \<circ> f) = Some \<circ> f"
  "bool_of_bitU (bitU_of_bool x) = Some x"
  by (intro ext, auto simp: bool_of_bitU_def bitU_of_bool_def)+

abbreviation "BC_bitU_list \<equiv> instance_Sail_values_Bitvector_list_dict instance_Sail_values_BitU_Sail_values_bitU_dict"
lemmas BC_bitU_list_def = instance_Sail_values_Bitvector_list_dict_def instance_Sail_values_BitU_Sail_values_bitU_dict_def
abbreviation "BC_mword \<equiv> instance_Sail_values_Bitvector_Machine_word_mword_dict"
lemmas BC_mword_defs = instance_Sail_values_Bitvector_Machine_word_mword_dict_def
  length_mword_def access_mword_def access_mword_inc_def access_mword_dec_def
  (*update_mword_def update_mword_inc_def update_mword_dec_def*)
  subrange_list_def subrange_list_inc_def subrange_list_dec_def
  update_subrange_list_def update_subrange_list_inc_def update_subrange_list_dec_def

lemma BC_mword_simps[simp]:
  "unsigned_method BC_mword a = Some (uint a)"
  "signed_method BC_mword a = Some (sint a)"
  "length_method BC_mword (a :: ('a :: len) word) = int (LENGTH('a))"
  by (auto simp: BC_mword_defs word_size)

lemma nat_of_bits_aux_bl_to_bin_aux:
  "nat_of_bools_aux acc bs = nat (bl_to_bin_aux bs (int acc))"
  by (induction acc bs rule: nat_of_bools_aux.induct)
     (auto simp: Bit_def intro!: arg_cong[where f = nat] arg_cong2[where f = bl_to_bin_aux] split: if_splits)

lemma nat_of_bits_bl_to_bin[simp]: "nat_of_bools bs = nat (bl_to_bin bs)"
  by (auto simp: nat_of_bools_def bl_to_bin_def nat_of_bits_aux_bl_to_bin_aux)

lemma unsigned_bits_of_mword[simp]:
  "unsigned_method BC_bitU_list (bits_of_method BC_mword a) = Some (uint a)"
  by (auto simp: BC_bitU_list_def BC_mword_defs unsigned_of_bits_def unsigned_of_bools_def)

lemma bits_of_bitU_list[simp]:
  "bits_of_method BC_bitU_list v = v"
  "of_bits_method BC_bitU_list v = Some v"
  by (auto simp: BC_bitU_list_def)

lemma access_list_dec_rev_nth:
  assumes "0 \<le> i" and "nat i < size xs"
  shows "access_list_dec xs i = rev xs ! (nat i)"
  using assms
  by (auto simp: access_list_dec_def access_list_inc_def length_list_def rev_nth
           intro!: arg_cong2[where f = List.nth])

lemma access_bv_dec_mword[simp]:
  fixes w :: "('a::len) word"
  assumes "0 \<le> n" and "nat n < LENGTH('a)"
  shows "access_bv_dec BC_mword w n = bitU_of_bool (w !! (nat n))"
  using assms
  by (auto simp: access_bv_dec_def access_list_def access_list_dec_rev_nth BC_mword_defs rev_map test_bit_bl word_size)

end
