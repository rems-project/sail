theory "Sail_operators_mwords_lemmas"
  imports Sail_operators_mwords
begin

lemmas uint_simps[simp] = uint_maybe_def uint_fail_def uint_oracle_def
lemmas sint_simps[simp] = sint_maybe_def sint_fail_def sint_oracle_def

lemma bools_of_bits_oracle_just_list[simp]:
  assumes "just_list (map bool_of_bitU bus) = Some bs"
  shows "bools_of_bits_oracle bus = return bs"
proof -
  have f: "foreachM bus bools (\<lambda>b bools. bool_of_bitU_oracle b \<bind> (\<lambda>b. return (bools @ [b]))) = return (bools @ bs)"
    if "just_list (map bool_of_bitU bus) = Some bs" for bus bs bools
  proof (use that in \<open>induction bus arbitrary: bs bools\<close>)
    case (Cons bu bus bs)
    obtain b bs' where bs: "bs = b # bs'" and bu: "bool_of_bitU bu = Some b"
      using Cons.prems by (cases bu) (auto split: option.splits)
    then show ?case
      using Cons.prems Cons.IH[where bs = bs' and bools = "bools @ [b]"]
      by (cases bu) (auto simp: bool_of_bitU_oracle_def split: option.splits)
  qed auto
  then show ?thesis using f[OF assms, of "[]"] unfolding bools_of_bits_oracle_def
    by auto
qed

lemma of_bits_mword_return_of_bl[simp]:
  assumes "just_list (map bool_of_bitU bus) = Some bs"
  shows "of_bits_oracle BC_mword bus = return (of_bl bs)"
    and "of_bits_fail BC_mword bus = return (of_bl bs)"
  by (auto simp: of_bits_oracle_def of_bits_fail_def maybe_fail_def assms BC_mword_defs)

lemma vec_of_bits_of_bl[simp]:
  assumes "just_list (map bool_of_bitU bus) = Some bs"
  shows "vec_of_bits_maybe bus = Some (of_bl bs)"
    and "vec_of_bits_fail bus = return (of_bl bs)"
    and "vec_of_bits_oracle bus = return (of_bl bs)"
    and "vec_of_bits_failwith bus = of_bl bs"
    and "vec_of_bits bus = of_bl bs"
  unfolding vec_of_bits_maybe_def vec_of_bits_fail_def vec_of_bits_oracle_def
            vec_of_bits_failwith_def vec_of_bits_def
  by (auto simp: assms)

lemmas access_vec_dec_test_bit[simp] = access_bv_dec_mword[folded access_vec_dec_def]

lemma access_vec_inc_test_bit[simp]:
  fixes w :: "('a::len) word"
  assumes "n \<ge> 0" and "nat n < LENGTH('a)"
  shows "access_vec_inc w n = bitU_of_bool (w !! (LENGTH('a) - 1 - nat n))"
  using assms
  by (auto simp: access_vec_inc_def access_bv_inc_def access_list_def BC_mword_defs rev_nth test_bit_bl)

lemma bool_of_bitU_monadic_simps[simp]:
  "bool_of_bitU_fail B0 = return False"
  "bool_of_bitU_fail B1 = return True"
  "bool_of_bitU_fail BU = Fail ''bool_of_bitU''"
  "bool_of_bitU_oracle B0 = return False"
  "bool_of_bitU_oracle B1 = return True"
  "bool_of_bitU_oracle BU = undefined_bool ()"
  unfolding bool_of_bitU_fail_def bool_of_bitU_oracle_def
  by auto

lemma update_vec_dec_simps[simp]:
  "update_vec_dec_maybe w i B0 = Some (set_bit w (nat i) False)"
  "update_vec_dec_maybe w i B1 = Some (set_bit w (nat i) True)"
  "update_vec_dec_maybe w i BU = None"
  "update_vec_dec_fail w i B0 = return (set_bit w (nat i) False)"
  "update_vec_dec_fail w i B1 = return (set_bit w (nat i) True)"
  "update_vec_dec_fail w i BU = Fail ''bool_of_bitU''"
  "update_vec_dec_oracle w i B0 = return (set_bit w (nat i) False)"
  "update_vec_dec_oracle w i B1 = return (set_bit w (nat i) True)"
  "update_vec_dec_oracle w i BU = undefined_bool () \<bind> (\<lambda>b. return (set_bit w (nat i) b))"
  "update_vec_dec w i B0 = set_bit w (nat i) False"
  "update_vec_dec w i B1 = set_bit w (nat i) True"
  unfolding update_vec_dec_maybe_def update_vec_dec_fail_def update_vec_dec_oracle_def update_vec_dec_def
  by (auto simp: update_mword_dec_def update_mword_bool_dec_def maybe_failwith_def)

lemma len_of_minus_One_minus_nonneg_lt_len_of[simp]:
  "n \<ge> 0 \<Longrightarrow> nat (int LENGTH('a::len) - 1 - n) < LENGTH('a)"
  by (metis diff_mono diff_zero len_gt_0 nat_eq_iff2 nat_less_iff order_refl zle_diff1_eq)

declare extz_vec_def[simp]
declare exts_vec_def[simp]
declare concat_vec_def[simp]

lemma msb_Bits_msb[simp]:
  "msb w = bitU_of_bool (Bits.msb w)"
  by (auto simp: msb_def most_significant_def BC_mword_defs word_msb_alt split: list.splits)

declare and_vec_def[simp]
declare or_vec_def[simp]
declare xor_vec_def[simp]
declare not_vec_def[simp]

lemma arith_vec_simps[simp]:
  "add_vec l r = l + r"
  "sub_vec l r = l - r"
  "mult_vec l r = (ucast l) * (ucast r)"
  unfolding add_vec_def sub_vec_def mult_vec_def
  by (auto simp: int_of_mword_def word_add_def word_sub_wi word_mult_def)

declare adds_vec_def[simp]
declare subs_vec_def[simp]
declare mults_vec_def[simp]

lemma arith_vec_int_simps[simp]:
  "add_vec_int l r = l + (word_of_int r)"
  "sub_vec_int l r = l - (word_of_int r)"
  "mult_vec_int l r = (ucast l) * (word_of_int r)"
  unfolding add_vec_int_def sub_vec_int_def mult_vec_int_def
  by (auto simp: arith_op_bv_int_def BC_mword_defs word_add_def word_sub_wi word_mult_def)

end
