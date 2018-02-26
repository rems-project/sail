theory Sail_values_lemmas
  imports Sail_values
begin

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

abbreviation "BC_bitU_list \<equiv> instance_Sail_values_Bitvector_list_dict instance_Sail_values_BitU_Sail_values_bitU_dict"
lemmas BC_bitU_list_def = instance_Sail_values_Bitvector_list_dict_def instance_Sail_values_BitU_Sail_values_bitU_dict_def
abbreviation "BC_mword \<equiv> instance_Sail_values_Bitvector_Machine_word_mword_dict"
lemmas BC_mword_def = instance_Sail_values_Bitvector_Machine_word_mword_dict_def

lemma image_bitU_of_bool_B0_B1: "bitU_of_bool ` bs \<subseteq> {B0, B1}"
  by (auto simp: bitU_of_bool_def split: if_splits)

lemma bool_of_bitU_bitU_of_bool[simp]: "bool_of_bitU \<circ> bitU_of_bool = id"
  by (intro ext) (auto simp: bool_of_bitU_def bitU_of_bool_def)

lemma nat_of_bits_aux_bl_to_bin_aux:
  assumes "set bs \<subseteq> {B0, B1}"
  shows "nat_of_bits_aux acc bs = nat (bl_to_bin_aux (map bool_of_bitU bs) (int acc))"
  by (use assms in \<open>induction acc bs rule: nat_of_bits_aux.induct\<close>)
     (auto simp: Bit_def bool_of_bitU_def intro!: arg_cong[where f = nat] arg_cong2[where f = bl_to_bin_aux])

lemma nat_of_bits_bl_to_bin[simp]: "nat_of_bits (map bitU_of_bool bs) = nat (bl_to_bin bs)"
  by (auto simp: nat_of_bits_def bl_to_bin_def nat_of_bits_aux_bl_to_bin_aux image_bitU_of_bool_B0_B1)

lemma unsigned_bits_of_mword:
  "unsigned_method BC_bitU_list (bits_of_method BC_mword a) = unsigned_method BC_mword a"
  by (auto simp: BC_bitU_list_def BC_mword_def unsigned_of_bits_def)

lemma unsigned_bits_of_bitU_list:
  "unsigned_method BC_bitU_list (bits_of_method BC_bitU_list a) = unsigned_method BC_bitU_list a"
  by (auto simp: BC_bitU_list_def)

end
