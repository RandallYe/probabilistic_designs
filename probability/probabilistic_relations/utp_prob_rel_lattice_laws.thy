section \<open> Probabilistic relation programming \<close>

theory utp_prob_rel_lattice_laws
  imports 
    (* "HOL.limits" *)
    "HOL.Series"
    "utp_prob_rel_lattice"
    (* "utp_prob_rel_prog" *)
begin 

term "convergent"
subsection \<open> @{text "ureal"} laws \<close>
lemma ureal2ereal_mono:
  "\<lbrakk>a < b\<rbrakk> \<Longrightarrow> ureal2ereal a < ureal2ereal b"
  by (simp add: less_ureal.rep_eq)

lemma ureal2real_mono:
  assumes "a \<le> b"
  shows "ureal2real a \<le> ureal2real b"
  apply (simp add: ureal_defs)
  by (metis assms atLeastAtMost_iff dual_order.eq_iff ereal_less_eq(1) ereal_times(2) 
      less_eq_ureal.rep_eq real_of_ereal_positive_mono ureal2ereal)

lemma ureal2real_mono_strict:
  assumes "a < b"
  shows "ureal2real a < ureal2real b"
  apply (simp add: ureal_defs)
  by (metis abs_ereal_ge0 assms atLeastAtMost_iff ereal_infty_less(1) ereal_less_real_iff ereal_real 
      ereal_times(1) linorder_not_less ureal2ereal ureal2ereal_mono)


lemma ureal_lower_bound: "ureal2real x \<ge> 0"
  using real_of_ereal_pos ureal2ereal ureal2real_def by auto

lemma ureal_upper_bound: "ureal2real x \<le> 1"
  using real_of_ereal_le_1 ureal2ereal ureal2real_def by auto

(*
lemma ureal_bound_fun: "`@(rvfun_of_prfun (r\<^sup>\<Up>)) \<ge> 0 \<and> @(rvfun_of_prfun (r\<^sup>\<Up>)) \<le> 1`"
  apply (simp add: ureal_defs)
  using real_of_ereal_le_1 real_of_ereal_pos ureal2ereal by force

lemma ureal_bound_fun': "\<forall>s. rvfun_of_prfun (r\<^sup>\<Up>) s \<ge> 0 \<and> rvfun_of_prfun (r\<^sup>\<Up>) s \<le> 1"
  apply (simp add: ureal_defs)
  using real_of_ereal_le_1 real_of_ereal_pos ureal2ereal by force
*)

lemma ureal_minus_larger_zero:
  assumes "a \<le> (e::ureal)"
  shows "a - e = 0"
  apply (simp add: minus_ureal_def )
  apply (simp add: less_ureal_def ureal_defs)
  by (metis assms atLeastAtMost_iff ereal_0_le_uminus_iff ereal_diff_nonpos ereal_minus_eq_PInfty_iff 
      ereal_times(1) less_eq_ureal.rep_eq max.absorb1 min_def ureal2ereal ureal2ereal_inverse 
      zero_ureal.rep_eq)

lemma ureal_minus_less:
  assumes "e > (0::ureal)" "a > 0"
  shows "a - e < a"
  apply (simp add: minus_ureal_def )
  apply (simp add: less_ureal_def ureal_defs)
  by (smt (verit, del_insts) assms(1) assms(2) atLeastAtMost_iff ereal2ureal'_inverse ereal_between(1) 
      ereal_less_PInfty ereal_times(1) ereal_x_minus_x less_ureal.rep_eq linorder_not_less max_def 
      min.absorb1 minus_ureal.rep_eq nle_le ureal2ereal)

lemma ureal_larger_minus_greater:
  assumes "a \<ge> (e::ureal)" "a < b"
  shows "a - e < b - e"
  apply (simp add: minus_ureal_def less_ureal_def ureal_defs)
  by (smt (z3) antisym_conv2 assms(1) assms(2) atLeastAtMost_iff diff_add_eq_ereal 
      ereal2ureal'_inverse ereal_diff_gr0 ereal_diff_le_mono_left ereal_diff_positive 
      ereal_minus(7) ereal_minus_le_iff ereal_minus_minus ereal_minus_mono ereal_times(2) 
      less_eq_ureal.rep_eq less_le_not_le linorder_not_le max.boundedI max_absorb1 max_absorb2 
      min_absorb1 order.trans order_eq_refl ureal2ereal ureal2ereal_inject)

lemma ureal_minus_larger_less:
  assumes "(e::ureal) > d" "a \<ge> e"
  shows "a - e < a - d"
  apply (simp add: minus_ureal_def )
  apply (simp add: less_ureal_def ureal_defs)
  by (smt (verit, best) assms(1) assms(2) atLeastAtMost_iff ereal2ureal'_inverse 
      ereal_diff_le_mono_left ereal_diff_positive ereal_less_PInfty ereal_mono_minus_cancel 
      ereal_times(1) less_eq_ureal.rep_eq linorder_not_less max_def min_def order_le_less_trans 
      order_less_imp_le ureal2ereal)

lemma ureal_plus_larger_greater:
  assumes "(e::ureal) < d" "a + d < 1"
  shows "a + e < a + d"
  apply (simp add: plus_ureal_def less_ureal_def ureal_defs)
  by (smt (z3) abs_ereal_ge0 assms(1) assms(2) atLeastAtMost_iff ereal_less_PInfty ereal_less_add 
      ereal_times(1) less_ureal.rep_eq max_def min_def not_less_iff_gr_or_eq order_le_less_trans 
      plus_ureal.rep_eq ureal2ereal ureal2ereal_inverse)

lemma ureal_minus_larger_zero_unit:
  assumes "a \<le> (e::ureal)"
  shows "a - (a - e) = a"
  apply (simp add: minus_ureal_def )
  apply (simp add: less_ureal_def ureal_defs)
  by (metis assms atLeastAtMost_iff ereal_diff_nonpos ereal_minus(7) ereal_minus_eq_PInfty_iff 
      less_eq_ureal.rep_eq max.absorb1 max_def min_def ureal2ereal ureal2ereal_inverse zero_ureal.rep_eq)

lemma ureal_minus_larger_zero_less:
  assumes "a \<le> (e::ureal)"
  shows "a - (a - e) \<le> e"
  by (simp add: ureal_minus_larger_zero_unit assms)

lemma ureal_minus_less_assoc:
  assumes "a \<ge> (e::ureal)"
  shows "a - (a - e) = a - a + e"
  apply (simp add: minus_ureal_def )
  apply (simp add: less_ureal_def ureal_defs)
  by (smt (z3) Orderings.order_eq_iff abs_ereal_one assms atLeastAtMost_iff diff_add_eq_ereal 
      ereal2ureal'_inverse ereal_diff_positive ereal_minus_eq_PInfty_iff ereal_minus_minus 
      ereal_x_minus_x less_eq_ureal.rep_eq max_absorb2 min.commute min_absorb1 minus_ureal.rep_eq 
      one_ureal.rep_eq plus_ureal.rep_eq ureal2ereal ureal2ereal_inject ureal_minus_larger_zero)

lemma ureal_minus_less_diff:
  assumes "a \<ge> (e::ureal)"
  shows "a - (a - e) = e"
  apply (simp add: ureal_minus_less_assoc assms)
  by (simp add: ureal_minus_larger_zero)

lemma ureal_plus_less_1_unit:
  assumes "a + (e::ureal) < 1"
  shows "a + e - a = e"
  by (smt (z3) assms atLeastAtMost_iff ereal_0_le_uminus_iff ereal_diff_add_inverse 
      ereal_diff_positive ereal_le_add_self ereal_minus_le_iff max.absorb1 max_absorb2 min_def 
      minus_ureal.rep_eq not_less_iff_gr_or_eq one_ureal.rep_eq plus_ureal.rep_eq ureal2ereal 
      ureal2ereal_inverse)

lemma ureal_plus_eq_1_minus_eq:
  assumes "a + (e::ureal) \<ge> 1"
  shows "a + e - a = 1 - a"
  by (metis assms atLeastAtMost_iff less_ureal.rep_eq linorder_not_le one_ureal.rep_eq ureal2ereal 
      verit_la_disequality)

lemma ureal_plus_eq_1_minus_less:
  assumes "a + (e::ureal) \<ge> 1"
  shows "a + e - a \<le> e"
  by (smt (verit, ccfv_SIG) add.commute assms atLeastAtMost_iff ereal_diff_positive ereal_minus_le_iff 
      ereal_times(1) less_eq_ureal.rep_eq max_absorb2 min_def minus_ureal.rep_eq one_ureal.rep_eq plus_ureal.rep_eq ureal2ereal)

lemma ureal_real2ureal_smaller:
  assumes "r \<ge> 0"
  shows "ureal2real (real2ureal r) \<le> r"
  apply (simp add: ureal_defs)
  by (simp add: assms ereal2ureal'_inverse real_le_ereal_iff)

lemma ureal_minus_larger_than_real_minus:
  shows "ureal2real a - ureal2real e \<le> ureal2real (a - e)"
  apply (simp add: ureal_defs minus_ureal_def)
  by (smt (verit, del_insts) abs_ereal_ge0 atLeastAtMost_iff ereal2ureal'_inverse ereal_less_eq(1) 
      max_def min_def nle_le real_ereal_1 real_of_ereal_le_0 real_of_ereal_le_1 real_of_ereal_minus 
      real_of_ereal_pos ureal2ereal)

lemma ureal_plus_greater:
  assumes "e > (0::ureal)" "a < (1::ureal)"
  shows "a + e > a"
  apply (simp add: plus_ureal_def )
  apply (simp add: less_ureal_def ureal_defs)
  by (smt (verit, del_insts) abs_ereal_zero add_nonneg_nonneg assms(1) assms(2) atLeastAtMost_iff 
      ereal2ureal'_inverse ereal_between(2) ereal_eq_0(1) ereal_le_add_self ereal_less_PInfty 
      ereal_real less_ureal.rep_eq linorder_not_less max.absorb1 max.cobounded1 max_def min.absorb3 
      min_def one_ureal.rep_eq real_of_ereal_le_0 zero_less_one_ereal zero_ureal.rep_eq)

lemma ureal_gt_zero:
  assumes "a > (0::\<real>)"
  shows "real2ureal a > 0"
  apply (simp add: ureal_defs)
  using assms ereal2ureal'_inverse less_ureal.rep_eq zero_ureal.rep_eq by auto

lemma ureal2real_eq:
  assumes "ureal2real a = ureal2real b"
  shows "a = b"
  by (metis assms linorder_neq_iff ureal2real_mono_strict)

lemma ureal_1_minus_1_minus_r_r: 
  "((1::\<real>) - rvfun_of_prfun (\<lambda>\<s>::'a \<times> 'b. (1::ureal) - r \<s>) (a, b)) = rvfun_of_prfun r (a, b)"
  apply (simp add: ureal_defs)
  by (smt (verit, ccfv_threshold) Orderings.order_eq_iff abs_ereal_ge0 atLeastAtMost_iff 
      ereal_diff_positive ereal_less_eq(1) ereal_times(1) max_def minus_ureal.rep_eq one_ureal.rep_eq 
      real_ereal_1 real_of_ereal_minus ureal2ereal)

lemma ureal_1_minus_real: 
  "ureal2real ((1::ureal) - s) = 1 - ureal2real s"
  apply (simp add: ureal_defs)
  by (metis abs_ereal_ge0 atLeastAtMost_iff ereal_diff_positive ereal_less_eq(1) ereal_times(1) 
      max_def min.absorb2 min_def minus_ureal.rep_eq one_ureal.rep_eq real_ereal_1 
      real_of_ereal_minus ureal2ereal)

lemma ureal_zero_0: "real_of_ereal (ureal2ereal (0::ureal)) = 0"
  by (simp add: zero_ureal.rep_eq)

lemma ureal_one_1: "real_of_ereal (ureal2ereal (1::ureal)) = 1"
  by (simp add: one_ureal.rep_eq)

lemma ureal2real_distr:
  assumes "a \<ge> b"
  shows "ureal2real (a - b) = ureal2real a - ureal2real b"
  by (smt (verit) assms ereal_diff_positive less_eq_ureal.rep_eq max_def minus_ureal.rep_eq o_apply 
      real_of_ereal_minus ureal2real_def ureal2real_mono ureal_minus_larger_than_real_minus)

lemma ureal2real_mult_strict_left_mono:
  assumes "p > 0" "c \<ge> 0" "c < d"
  shows "(ureal2real p) * c < ureal2real p * d"
  by (smt (verit) assms(1) assms(2) assms(3) mult_le_less_imp_less ureal2real_mono_strict ureal_lower_bound)

lemma ereal_1_div:
  assumes "n \<noteq> 0"
  shows "(1::ereal) / ereal (n::\<real>) = ereal (1/n)"
  by (simp add: one_ereal_def assms)

lemma ereal_div:
  assumes "n \<noteq> 0" "m \<noteq> PInfty" "m \<noteq> MInfty"
  shows "(m::ereal) / ereal (n::\<real>) = ereal (real_of_ereal m/n)"
  apply (simp add: divide_ereal_def)
  apply (auto)
  using assms apply blast
  by (metis assms(2) assms(3) divide_inverse real_of_ereal.simps(1) times_ereal.simps(1) uminus_ereal.cases)

lemma real2uereal_inverse:
  assumes "r \<ge> 0" "r \<le> 1"
  shows "real_of_ereal (ureal2ereal (ereal2ureal' r)) = real_of_ereal r"
  apply (subst ereal2ureal'_inverse)
  apply (simp add: atLeastAtMost_def)
  apply (simp add: assms(1) assms(2) divide_le_eq_1 order_less_le)
  by (auto)

lemma real2uereal_inverse':
  assumes "r \<ge> 0" "r \<le> 1"
  shows "real_of_ereal (ureal2ereal (ereal2ureal' (ereal r))) = r"
  by (simp add: real2uereal_inverse assms)

lemma real2uereal_min_inverse':
  assumes "r \<ge> 0" "r \<le> 1"
  shows "real_of_ereal (ureal2ereal (ereal2ureal' (min (ereal r) (1::ereal)))) = r"
  by (simp add: assms(1) assms(2) real2uereal_inverse')

lemma ureal2rereal_inverse: "ereal2ureal (ereal (ureal2real u)) = u"
  apply (simp add: ureal_defs)
  by (smt (verit, best) Orderings.order_eq_iff atLeastAtMost_iff ereal_less(2) ereal_less_eq(1) 
      ereal_max ereal_real ereal_times(1) min_def real_of_ereal_le_0 type_definition.Rep_inverse 
      type_definition_ureal ureal2ereal)

(*
lemma real2uereal_inverse:
  assumes "n \<ge> 0" "d \<ge> 0" "n \<le> d"
  shows "real_of_ereal (ureal2ereal (ereal2ureal' (ereal ((n::\<real>) / (d::\<real>))))) = n / d"
  apply (subst ereal2ureal'_inverse)
  apply (simp add: atLeastAtMost_def)
  apply (simp add: assms(1) assms(2) assms(3) divide_le_eq_1 order_less_le)
  by (auto)
*)
subsection \<open> Infinite sum \<close>
lemma rvfun_prob_sum1_summable:
  assumes "is_final_distribution p"
  shows "\<forall>s. 0 \<le> p s \<and> p s \<le> 1" 
        "(\<Sum>\<^sub>\<infinity> s. p (s\<^sub>1, s)) = (1::\<real>)"
        "(\<lambda>s. p (s\<^sub>1, s)) summable_on UNIV"
        "\<exists>s'. p (s\<^sub>1, s') > 0"
  using assms apply (simp add: dist_defs expr_defs)
  using assms is_dist_def is_sum_1_def apply (metis (no_types, lifting) curry_conv infsum_cong)
proof (rule ccontr)
  assume a1: "\<not> (\<lambda>s. p (s\<^sub>1, s)) summable_on UNIV"
  from a1 have f1: "(\<Sum>\<^sub>\<infinity>s. p (s\<^sub>1, s)) = (0::\<real>)"
    by (simp add: infsum_def)
  then show "False"
    by (metis assms case_prod_eta curry_case_prod is_dist_def is_sum_1_def zero_neq_one)
next
  show "\<exists>s'::'b. (0::\<real>) < p (s\<^sub>1, s')"
    apply (rule ccontr)
  proof -
    assume a1: "\<not> (\<exists>s'::'b. (0::\<real>) < p (s\<^sub>1, s'))"
    then have "\<forall>s'. (0::\<real>) = p (s\<^sub>1, s')"
      by (meson assms is_final_distribution_prob is_final_prob_altdef order_neq_le_trans)
    then have "(\<Sum>\<^sub>\<infinity> s. p (s\<^sub>1, s)) = 0"
      by simp
    then show "false"
      by (smt (verit, best) assms curry_conv infsum_cong is_dist_def is_sum_1_def)
  qed
qed

lemma rvfun_prob_sum_leq_1_summable:
  assumes "is_final_sub_dist p"
  shows "\<forall>s. 0 \<le> p s \<and> p s \<le> 1" 
        "(\<Sum>\<^sub>\<infinity> s. p (s\<^sub>1, s)) \<le> (1::\<real>)"
        "(\<Sum>\<^sub>\<infinity> s. p (s\<^sub>1, s)) > (0::\<real>)"
        "(\<lambda>s. p (s\<^sub>1, s)) summable_on UNIV"
        "(\<lambda>s. p (s\<^sub>1, s)) summable_on A"
  using assms apply (simp add: dist_defs expr_defs)
  using assms is_sub_dist_def is_sum_leq_1_def apply (metis (no_types, lifting) curry_conv infsum_cong)
  using assms is_sub_dist_def is_sum_leq_1_def apply (metis case_prod_eta curry_case_prod)
proof (rule ccontr)
  assume a1: "\<not> (\<lambda>s. p (s\<^sub>1, s)) summable_on UNIV"
  from a1 have f1: "(\<Sum>\<^sub>\<infinity>s. p (s\<^sub>1, s)) = (0::\<real>)"
    by (simp add: infsum_def)
  have f2: "(\<Sum>\<^sub>\<infinity>s. p (s\<^sub>1, s)) > (0::\<real>)"
    using assms case_prod_eta curry_case_prod is_sub_dist_def is_sum_leq_1_def
    by (metis a1 infsum_not_zero_is_summable)
  then show "False"
    by (simp add: f1)
next
  show "(\<lambda>s::'b. p (s\<^sub>1, s)) summable_on A"
    by (smt (verit, best) UNIV_I assms curry_conv infsum_not_exists is_sub_dist_def is_sum_leq_1_def 
        subsetI summable_on_cong summable_on_subset_banach)
qed

text \<open> A probability distribution function is probabilistic, whose final states forms a distribution, 
and summable (convergent). \<close>
lemma pdrfun_prob_sum1_summable:
  assumes "is_final_distribution (rvfun_of_prfun (f::('s\<^sub>1, 's\<^sub>2) prfun))"
  shows "\<forall>s. 0 \<le> f s \<and> f s \<le> 1"
        "\<forall>s. 0 \<le> ureal2real (f s) \<and> ureal2real (f s) \<le> 1"
        "(\<Sum>\<^sub>\<infinity> s. ureal2real (f (s\<^sub>1, s))) = (1::\<real>)"
        "(\<lambda>s. ureal2real (f (s\<^sub>1, s))) summable_on UNIV"
  using assms apply (simp add: dist_defs expr_defs)
  apply (simp add: ureal_defs)
     apply (auto)
  using less_eq_ureal.rep_eq ureal2ereal zero_ureal.rep_eq apply force
  apply (metis one_ureal.rep_eq top_greatest top_ureal.rep_eq ureal2ereal_inject)
  using real_of_ereal_pos ureal2ereal ureal2real_def apply auto[1]
    apply (simp add: ureal_upper_bound)
proof -
  have "\<forall>s\<^sub>1::'s\<^sub>1. (\<Sum>\<^sub>\<infinity> s. ((curry (rvfun_of_prfun f)) s\<^sub>1) s) = 1"
    using assms by (simp add: is_dist_def is_sum_1_def)
  then show dist: "(\<Sum>\<^sub>\<infinity>s::'s\<^sub>2. ureal2real (f (s\<^sub>1, s))) = (1::\<real>)"
    by (simp add: ureal_defs)
  show "(\<lambda>s::'s\<^sub>2. ureal2real (f (s\<^sub>1, s))) summable_on UNIV"
    apply (rule ccontr)
    by (metis dist infsum_not_exists zero_neq_one)
qed

lemma pdrfun_prob_sum1_summable':
  assumes "is_final_distribution (rvfun_of_prfun (f::('s\<^sub>1, 's\<^sub>2) prfun))"
  shows "\<forall>s. 0 \<le> f s \<and> f s \<le> 1"
        "\<forall>s. 0 \<le> rvfun_of_prfun f s \<and> rvfun_of_prfun f s \<le> 1"
        "(\<Sum>\<^sub>\<infinity> s. rvfun_of_prfun f (s\<^sub>1, s)) = (1::\<real>)"
        "(\<lambda>s. rvfun_of_prfun f (s\<^sub>1, s)) summable_on UNIV"
  apply (simp add: assms pdrfun_prob_sum1_summable(1))
  using assms rvfun_prob_sum1_summable(1) apply blast
  apply (simp add: assms rvfun_prob_sum1_summable(2))
  by (simp add: assms rvfun_prob_sum1_summable(3))

lemma pdrfun_product_summable:
  assumes "is_final_distribution (rvfun_of_prfun (f::('s\<^sub>1, 's\<^sub>2) prfun))"
  shows "(\<lambda>s. (ureal2real (f (s\<^sub>1, s))) * (ureal2real (g (s\<^sub>1, s)))) summable_on UNIV"
  apply (subst summable_on_iff_abs_summable_on_real)
  apply (rule abs_summable_on_comparison_test[where g = "\<lambda>s. (ureal2real (f (s\<^sub>1, s)))"])
  apply (metis assms infsum_not_exists pdrfun_prob_sum1_summable(3) 
      summable_on_iff_abs_summable_on_real zero_neq_one)
  by (simp add: mult_right_le_one_le ureal_lower_bound ureal_upper_bound)

lemma pdrfun_product_summable_swap:
  assumes "is_final_distribution (rvfun_of_prfun (f::('s\<^sub>1, 's\<^sub>2) prfun))"
  shows "(\<lambda>s. (ureal2real (g (s\<^sub>1, s))) * (ureal2real (f (s\<^sub>1, s)))) summable_on UNIV"
  using pdrfun_product_summable by (smt (verit, ccfv_threshold) assms mult_commute_abs summable_on_cong)

lemma pdrfun_product_summable':
  assumes "is_final_distribution (rvfun_of_prfun (f::('s\<^sub>1, 's\<^sub>2) prfun))"
  shows "(\<lambda>s. (ureal2real (f (s\<^sub>1, s))) * (ureal2real (g (s, s')))) summable_on UNIV"
  apply (subst summable_on_iff_abs_summable_on_real)
  apply (rule abs_summable_on_comparison_test[where g = "\<lambda>s. (ureal2real (f (s\<^sub>1, s)))"])
  apply (metis assms infsum_not_exists pdrfun_prob_sum1_summable(3) 
      summable_on_iff_abs_summable_on_real zero_neq_one)
  by (simp add: mult_right_le_one_le ureal_lower_bound ureal_upper_bound)

lemma pdrfun_product_summable'_swap:
  assumes "is_final_distribution (rvfun_of_prfun (f::('s\<^sub>1, 's\<^sub>2) prfun))"
  shows "(\<lambda>s. (ureal2real (g (s, s'))) * (ureal2real (f (s\<^sub>1, s)))) summable_on UNIV"
  using pdrfun_product_summable' by (smt (verit, ccfv_threshold) assms mult_commute_abs summable_on_cong)

lemma ureal2real_summable_eq:
  assumes "(\<lambda>s. ureal2real (f (s\<^sub>1, s))) summable_on UNIV"
  shows "(\<lambda>s. real_of_ereal (ureal2ereal (f (s\<^sub>1, s)))) summable_on UNIV"
  using assms ureal_defs by auto

lemma pdrfun_product_summable'':
  assumes "is_final_distribution (rvfun_of_prfun (f::('s\<^sub>1, 's\<^sub>2) prfun))"
  shows "(\<lambda>s. real_of_ereal (ureal2ereal (f (s\<^sub>1, s))) * real_of_ereal (ureal2ereal (g (s, s')))) 
    summable_on UNIV"
  apply (subst summable_on_iff_abs_summable_on_real)
  apply (rule abs_summable_on_comparison_test[where g = "\<lambda>s. real_of_ereal (ureal2ereal (f (s\<^sub>1, s)))"])
  using ureal2real_summable_eq apply (metis assms infsum_not_exists pdrfun_prob_sum1_summable(3) 
      summable_on_iff_abs_summable_on_real zero_neq_one)
  by (smt (z3) atLeastAtMost_iff mult_nonneg_nonneg mult_right_le_one_le real_norm_def 
      real_of_ereal_le_1 real_of_ereal_pos ureal2ereal)

lemma summable_on_ureal_product:
  assumes P_summable: "(\<lambda>v\<^sub>0. real_of_ereal (ureal2ereal (P (s, v\<^sub>0)))) summable_on UNIV"
  shows "(\<lambda>v\<^sub>0::'c time_scheme. real_of_ereal (ureal2ereal (P (s, v\<^sub>0))) * 
        real_of_ereal (ureal2ereal (x (v\<^sub>0, b)))) summable_on UNIV"
  apply (subst summable_on_iff_abs_summable_on_real)
  apply (rule abs_summable_on_comparison_test[where g = "\<lambda>x. real_of_ereal (ureal2ereal (P (s, x)))"])
  apply (subst summable_on_iff_abs_summable_on_real[symmetric])
  using assms apply blast
  by (smt (verit) atLeastAtMost_iff mult_nonneg_nonneg mult_right_le_one_le real_norm_def 
      real_of_ereal_le_1 real_of_ereal_pos ureal2ereal)

subsection \<open> @{term "is_prob"} \<close>
lemma ureal_is_prob: "is_prob (rvfun_of_prfun P)"
  by (simp add: is_prob_def rvfun_of_prfun_def ureal_lower_bound ureal_upper_bound)

lemma ureal_1_minus_is_prob: "is_prob ((1)\<^sub>e - rvfun_of_prfun P)"
  by (simp add: is_prob_def rvfun_of_prfun_def ureal_lower_bound ureal_upper_bound)

subsection \<open> Inverse between @{term "rvfun"} and @{term "prfun"}  \<close>
lemma rvfun_inverse: 
  assumes "is_prob P"
  shows "rvfun_of_prfun (prfun_of_rvfun P) = P"
  apply (simp add: ureal_defs)
  apply (expr_auto)
proof -
  fix a b
  have "\<forall>s. P s \<ge> 0 \<and> P s \<le> 1"
    by (metis (mono_tags, lifting) SEXP_def assms is_prob_def taut_def)
  then show "real_of_ereal (ureal2ereal (ereal2ureal' (min (max (0::ereal) (ereal (P (a, b)))) (1::ereal)))) = P (a, b)"
    by (simp add: ereal2ureal'_inverse)
qed

lemma prfun_inverse: 
  shows " prfun_of_rvfun (rvfun_of_prfun P) = P"
  apply (simp add: ureal_defs)
  apply (expr_auto)
  by (smt (verit, best) atLeastAtMost_iff ereal_le_real_iff ereal_less_eq(1) ereal_real' 
      ereal_times(2) max.bounded_iff min_absorb1 nle_le real_of_ereal_le_0 
      type_definition.Rep_inverse type_definition_ureal ureal2ereal zero_ereal_def)

subsection \<open> Laws of type @{type rvfun} \<close>
lemma Sigma_Un_distrib2:
  shows "Sigma A (\<lambda>s. B s) \<union> Sigma A (\<lambda>s. C s) = Sigma A (\<lambda>s. (B s \<union> C s))"
  apply (simp add: Sigma_def)
  by (auto)

lemma prel_Sigma_UNIV_divide:
  assumes "is_final_distribution q"
  shows "Sigma (UNIV) (\<lambda>v\<^sub>0. {s'. q(v\<^sub>0, s') > (0::real)}) \<union> (Sigma (UNIV) (\<lambda>v\<^sub>0. {s'. q(v\<^sub>0, s') = (0::real)})) 
    = Sigma (UNIV) (\<lambda>v\<^sub>0. UNIV)"
  apply (simp add: Sigma_Un_distrib2)
  apply (auto)
  by (metis antisym_conv2 assms rvfun_prob_sum1_summable(1))

lemma rvfun_infsum_1_finite_subset:
  assumes "is_final_distribution p"
  shows "\<forall>S::\<bbbP> \<real>. open S \<longrightarrow> (1::\<real>) \<in> S \<longrightarrow> 
    (\<exists>X::\<bbbP> 'a. finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> (\<Sum>s::'a\<in>Y. p (s\<^sub>1, s)) \<in> S))"
proof -
  have "(\<Sum>\<^sub>\<infinity>s::'a. p (s\<^sub>1, s)) = (1::\<real>)"
    by (simp add: assms(1) rvfun_prob_sum1_summable(2))
  then have "has_sum (\<lambda>s::'a. p (s\<^sub>1, s)) UNIV (1::\<real>)"
    by (metis has_sum_infsum infsum_not_exists zero_neq_one)
  then have "(sum (\<lambda>s::'a. p (s\<^sub>1, s)) \<longlongrightarrow> (1::\<real>)) (finite_subsets_at_top UNIV)"
    using has_sum_def by blast
  then have "\<forall>S::\<bbbP> \<real>. open S \<longrightarrow> (1::\<real>) \<in> S \<longrightarrow> (\<forall>\<^sub>F x::\<bbbP> 'a in finite_subsets_at_top UNIV. (\<Sum>s::'a\<in>x. p (s\<^sub>1, s)) \<in> S)"
    by (simp add: tendsto_def)
  thus ?thesis
    by (simp add: eventually_finite_subsets_at_top)
qed

lemma rvfun_product_summable:
  assumes "is_final_sub_dist p" "is_prob q"
  shows "(\<lambda>s::'a. p (x, s) * q (s, y)) summable_on UNIV"
  apply (subst summable_on_iff_abs_summable_on_real)
  apply (rule abs_summable_on_comparison_test[where g = "\<lambda>s::'a. p (x, s)"])
  apply (metis assms(1) rvfun_prob_sum_leq_1_summable(4) summable_on_iff_abs_summable_on_real)
  by (simp add: assms(1) assms(2) is_prob mult_left_le rvfun_prob_sum_leq_1_summable(1))

lemma rvfun_product_summable_dist:
  assumes "is_final_distribution p"
  assumes "\<forall>s. q s \<le> 1 \<and> q s \<ge> 0"
  shows "(\<lambda>s::'a. p (x, s) * q (s, y)) summable_on UNIV"
  apply (subst summable_on_iff_abs_summable_on_real)
  apply (rule abs_summable_on_comparison_test[where g = "\<lambda>s::'a. p (x, s)"])
  apply (metis assms(1) rvfun_prob_sum1_summable(3) summable_on_iff_abs_summable_on_real)
  using assms(2) by (smt (verit) SEXP_def mult_right_le_one_le norm_mult real_norm_def)

lemma rvfun_product_prob_dist_leq_1:
  assumes "is_final_distribution p"
  assumes "is_prob q"
  shows "(\<Sum>\<^sub>\<infinity> s::'a. p (x, s) * q (s, y)) \<le> (1::\<real>)"
proof -
  have "(\<Sum>\<^sub>\<infinity> s::'a. p (x, s) * q (s, y)) \<le> (\<Sum>\<^sub>\<infinity> s::'a. p (x, s))"
    apply (subst infsum_mono)
    apply (simp add: assms(1) assms(2) is_prob rvfun_product_summable_dist)
    apply (simp add: assms(1) rvfun_prob_sum1_summable(3))
    apply (simp add: assms(1) assms(2) is_prob mult_right_le_one_le rvfun_prob_sum1_summable(1))
    by simp
  also have "... = 1"
    by (metis assms(1) rvfun_prob_sum1_summable(2))
  then show ?thesis
    using calculation by presburger
qed

lemma rvfun_product_prob_sub_dist_leq_1:
  assumes "is_final_sub_dist p"
  assumes "is_prob q"
  shows "(\<Sum>\<^sub>\<infinity> s::'a. p (x, s) * q (s, y)) \<le> (1::\<real>)"
proof -
  have "(\<Sum>\<^sub>\<infinity> s::'a. p (x, s) * q (s, y)) \<le> (\<Sum>\<^sub>\<infinity> s::'a. p (x, s))"
    apply (subst infsum_mono)
    apply (simp add: assms(1) assms(2) is_prob rvfun_product_summable)
    apply (simp add: assms(1) rvfun_prob_sum_leq_1_summable(4))
    apply (simp add: assms(1) assms(2) is_prob mult_right_le_one_le rvfun_prob_sum_leq_1_summable(1))
    by simp
  also have "... \<le> 1"
    by (metis assms(1) rvfun_prob_sum_leq_1_summable(2))
  then show ?thesis
    using calculation by linarith
qed
    

lemma rvfun_product_summable_summable:
  assumes "\<forall>x. ((curry p) x) summable_on UNIV"
  assumes "is_prob p" "is_prob q"
  shows "(\<lambda>s::'a. p (x, s) * q (s, y)) summable_on UNIV"
  apply (subst summable_on_iff_abs_summable_on_real)
  apply (rule abs_summable_on_comparison_test[where g = "\<lambda>s::'a. p (x, s)"])
   apply (subst summable_on_iff_abs_summable_on_real)
  apply (smt (verit, del_insts) abs_of_nonneg assms(1) assms(2) curry_conv is_prob real_norm_def summable_on_cong)
  by (simp add: assms(2) assms(3) is_prob mult_left_le)

lemma rvfun_product_summable':
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "(\<lambda>s::'a. p (x, s) * q (s, y)) summable_on UNIV"
  apply (rule rvfun_product_summable_dist)
  apply (simp add: assms(1))
  using assms(2) rvfun_prob_sum1_summable(1) by blast

lemma rvfun_joint_prob_summable_on_product: 
  assumes "is_final_prob p"
  assumes "is_final_prob q"
  assumes "(\<lambda>s'::'a. p (s\<^sub>1, s')) summable_on UNIV \<or> (\<lambda>s'::'a. q (s\<^sub>1, s')) summable_on UNIV"
  shows "(\<lambda>s'::'a. p (s\<^sub>1, s') * q (s\<^sub>1, s')) summable_on UNIV"
proof (cases "(\<lambda>s'::'a. p (s\<^sub>1, s')) summable_on UNIV")
  case True
  then show ?thesis 
    apply (subst summable_on_iff_abs_summable_on_real)
    apply (rule abs_summable_on_comparison_test[where g = "\<lambda>s'::'a. p (s\<^sub>1, s')"])
    apply (subst summable_on_iff_abs_summable_on_real[symmetric])
    using assms(3) apply blast
    apply (simp add: assms(1) assms(2) is_final_prob_altdef)
    by (simp add: assms(1) assms(2) is_final_prob_altdef mult_right_le_one_le)
next
  case False
  then have "(\<lambda>s'::'a. q (s\<^sub>1, s')) summable_on UNIV"
    using assms(3) by blast
  then show ?thesis 
    apply (subst summable_on_iff_abs_summable_on_real)
    apply (rule abs_summable_on_comparison_test[where g = "\<lambda>s'::'a. q (s\<^sub>1, s')"])
    apply (subst summable_on_iff_abs_summable_on_real[symmetric])
    using assms(3) apply blast
    apply (simp add: assms(1) assms(2) is_final_prob_altdef)
    by (simp add: assms(1) assms(2) is_final_prob_altdef mult_left_le_one_le)
qed

lemma rvfun_joint_prob_summable_on_product_dist:
  assumes "is_final_distribution p"
  assumes "\<forall>s. q s \<le> 1 \<and> q s \<ge> 0"
  shows "(\<lambda>s::'a. p (x, s) * q (x, s)) summable_on UNIV"
    apply (subst summable_on_iff_abs_summable_on_real)
    apply (rule abs_summable_on_comparison_test[where g = "\<lambda>s::'a. p (x, s)"])
    apply (metis assms(1) rvfun_prob_sum1_summable(3) summable_on_iff_abs_summable_on_real)
  using assms(2) by (smt (verit) SEXP_def mult_right_le_one_le norm_mult real_norm_def)

lemma rvfun_joint_prob_summable_on_product_dist':
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "(\<lambda>s::'a. p (x, s) * q (x, s)) summable_on UNIV"
  apply (rule rvfun_joint_prob_summable_on_product_dist)
  apply (simp add: assms(1))
  using assms(2) rvfun_prob_sum1_summable(1) by blast

lemma rvfun_joint_prob_sum_ge_zero:
  assumes "\<forall>s. P s \<ge> (0::\<real>)" "\<forall>s. Q s \<ge> 0" 
          "\<forall>s\<^sub>1. (\<lambda>s'. P (s\<^sub>1, s') * Q (s\<^sub>1, s')) summable_on UNIV"
          "\<forall>s\<^sub>1. \<exists>s'. P (s\<^sub>1, s') > 0 \<and> Q (s\<^sub>1, s') > 0"
  shows "\<forall>s\<^sub>1. ((\<Sum>\<^sub>\<infinity> s'. P (s\<^sub>1, s') * Q (s\<^sub>1, s')) > 0)"
proof (rule allI)
  fix s\<^sub>1
  let ?P = "\<lambda>s'. P (s\<^sub>1, s') > 0 \<and> Q (s\<^sub>1, s') > 0"
  have f1: "?P (SOME s'. ?P s')"
    apply (rule someI_ex[where P="?P"])
    using assms by blast
  have f2: "(\<lambda>s. P (s\<^sub>1, s) * Q (s\<^sub>1, s)) (SOME s'. ?P s') \<le> (\<Sum>\<^sub>\<infinity>s'. P (s\<^sub>1, s') * Q (s\<^sub>1, s'))"
    apply (rule infsum_geq_element)
    apply (simp add: assms(1-2))
    apply (simp add: assms(3))
    by auto
  also have f3: "... > 0"
    by (smt (verit, ccfv_threshold) f1 f2 mult_pos_pos)
  then show "(0::\<real>) < (\<Sum>\<^sub>\<infinity>s'::'b. P (s\<^sub>1, s') * Q (s\<^sub>1, s'))"
    by linarith
qed

lemma prfun_in_0_1: "(curry (rvfun_of_prfun Q)) x y \<ge> 0 \<and> (curry (rvfun_of_prfun Q)) x y \<le> 1"
  by (simp add: is_prob ureal_is_prob)

lemma prfun_in_0_1': "(rvfun_of_prfun Q) s \<ge> 0 \<and> (rvfun_of_prfun Q) s \<le> 1"
  apply (simp add: ureal_defs)
  apply (auto)
  using real_of_ereal_pos ureal2ereal apply fastforce
  using ureal2real_def ureal_upper_bound by auto

(* The first component of pairs, which infsum is over, can be discarded. *)
(* The basic observation is that 
    A = {(s::'a, v\<^sub>0::'a) | s v\<^sub>0. put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s}
is resulted from an injective function 
  (\<lambda>v\<^sub>0. (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0)) 
from (UNIV::'a set) which the right summation is over.

Informally speaking, every v\<^sub>0 in UNIV has a corresponding (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0) in A, and no more, 
thus summations are equal. 
*)
lemma prfun_infsum_over_pair_fst_discard:
  assumes "is_final_distribution (rvfun_of_prfun (P::'a prhfun))"
  shows "(\<Sum>\<^sub>\<infinity> (s::'a, v\<^sub>0::'a) \<in> {(s::'a, v\<^sub>0::'a) | s v\<^sub>0. put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s}. rvfun_of_prfun P (s\<^sub>1, v\<^sub>0)) = 
   (\<Sum>\<^sub>\<infinity> v\<^sub>0::'a. rvfun_of_prfun P (s\<^sub>1, v\<^sub>0))"
  apply (simp add: pdrfun_prob_sum1_summable' assms)
  \<comment> \<open> Definition of @{term "infsum"} \<close>
  apply (rule infsumI)
  apply (simp add: has_sum_def)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
proof -
  fix S::"\<bbbP> \<real>"
  assume a1: "open S"
  assume a2: "(1::\<real>) \<in> S"
  \<comment> \<open>How to improve this proof? Forward proof. Focus on the goal f0 9 lines below \<close>
  have "(\<Sum>\<^sub>\<infinity>s::'a. rvfun_of_prfun P (s\<^sub>1, s)) = (1::\<real>)"
    by (simp add: pdrfun_prob_sum1_summable' assms)
  then have "has_sum (\<lambda>s::'a. rvfun_of_prfun P (s\<^sub>1, s)) UNIV (1::\<real>)"
    by (metis has_sum_infsum infsum_not_exists zero_neq_one)
  then have "(sum (\<lambda>s::'a. rvfun_of_prfun P (s\<^sub>1, s)) \<longlongrightarrow> (1::\<real>)) (finite_subsets_at_top UNIV)"
    using has_sum_def by blast
  then have "\<forall>\<^sub>F x::\<bbbP> 'a in finite_subsets_at_top UNIV. (\<Sum>s::'a\<in>x. rvfun_of_prfun P (s\<^sub>1, s)) \<in> S"
    using a1 a2 tendsto_def by blast
  then have f0: "\<exists>X::\<bbbP> 'a. finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> 
      (\<Sum>s::'a\<in>Y. rvfun_of_prfun P (s\<^sub>1, s)) \<in> S)"
    by (simp add: eventually_finite_subsets_at_top)
  then show "\<exists>X::'a rel. finite X \<and> X \<subseteq> {uu::'a \<times> 'a. \<exists>v\<^sub>0::'a. uu = (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0)} \<and>
          (\<forall>Y::'a rel.
              finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> {uu::'a \<times> 'a. \<exists>v\<^sub>0::'a. uu = (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0)} \<longrightarrow>
              (\<Sum>x::'a \<times> 'a\<in>Y. case x of (s::'a, v\<^sub>0::'a) \<Rightarrow> rvfun_of_prfun P (s\<^sub>1, v\<^sub>0)) \<in> S)"
  proof -
    assume a11: "\<exists>X::\<bbbP> 'a. finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> 
      (\<Sum>s::'a\<in>Y. rvfun_of_prfun P (s\<^sub>1, s)) \<in> S)"
    have f1: "finite
       {uu::'a \<times> 'a. \<exists>v\<^sub>0::'a. v\<^sub>0 \<in> (SOME X::\<bbbP> 'a.
          finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> (\<Sum>s::'a\<in>Y. rvfun_of_prfun P (s\<^sub>1, s)) \<in> S))
        \<and> uu = (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0)}"
      apply (subst finite_Collect_bounded_ex)
      apply (smt (verit, ccfv_threshold) CollectD a11 rev_finite_subset someI_ex subset_iff)
      by (auto)
    show ?thesis
      (* Construct a witness from existing X from f0 using SOME (indifinite description) *)
      apply (rule_tac x = "{(put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0) | v\<^sub>0 . 
        v\<^sub>0 \<in> (SOME X::\<bbbP> 'a. finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> 
        (\<Sum>s::'a\<in>Y. rvfun_of_prfun P (s\<^sub>1, s)) \<in> S))}" in exI)
      apply (rule conjI)
      using f1 apply (smt (verit, best) Collect_mono rev_finite_subset)
      apply (auto)
    proof -
      fix Y::"'a rel"
      assume a111: "finite Y"
      assume a112: "{uu::'a \<times> 'a.
        \<exists>v\<^sub>0::'a.
           uu = (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0) \<and>
           v\<^sub>0 \<in> (SOME X::\<bbbP> 'a. finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> (\<Sum>s::'a\<in>Y. rvfun_of_prfun P (s\<^sub>1, s)) \<in> S))}
       \<subseteq> Y"
      assume a113: "Y \<subseteq> {uu::'a \<times> 'a. \<exists>v\<^sub>0::'a. uu = (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0)}"
      have f11: "(\<Sum>s::'a\<in>Range Y. rvfun_of_prfun P (s\<^sub>1, s)) \<in> S"
        using a11 a111 a112
        by (smt (verit, del_insts) Range_iff finite_Range mem_Collect_eq subset_iff verit_sko_ex_indirect)
      have f12: "inj_on (\<lambda>v\<^sub>0. (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0)) (Range Y)"
        using inj_on_def by blast
      have f13: "(\<Sum>x::'a \<times> 'a\<in>Y. case x of (s::'a, v\<^sub>0::'a) \<Rightarrow> rvfun_of_prfun P (s\<^sub>1, v\<^sub>0)) = 
            (\<Sum>s::'a\<in>Range Y. rvfun_of_prfun P (s\<^sub>1, s))"
        apply (rule sum.reindex_cong[where l = "(\<lambda>v\<^sub>0. (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0))" and B = "Range Y"]) 
        apply (simp add: f12)
        using a113 by (auto)
      show "(\<Sum>x::'a \<times> 'a\<in>Y. case x of (s::'a, v\<^sub>0::'a) \<Rightarrow> rvfun_of_prfun P (s\<^sub>1, v\<^sub>0)) \<in> S"
        using f11 f13 by presburger
    qed
  qed
qed

lemma prfun_minus_distribution:
  fixes X Y :: "'a prhfun"
  assumes "X \<ge> Y"
  shows "rvfun_of_prfun X - rvfun_of_prfun Y = rvfun_of_prfun (X - Y)"
  apply (subst fun_eq_iff)
  apply (rule allI)
  apply (simp add: ureal_defs)
  by (smt (verit, del_insts) abs_ereal_ge0 assms atLeastAtMost_iff ereal_diff_positive 
      ereal_less_eq(1) ereal_times(1) le_fun_def less_eq_ureal.rep_eq max_def minus_ureal.rep_eq 
      nle_le real_of_ereal_minus ureal2ereal)

subsection \<open> Probabilistic programs \<close>
subsubsection \<open> Bottom and Top \<close>
lemma ureal_bot_zero: "\<bottom> = \<^bold>0"
  by (metis bot_apply bot_ureal.rep_eq ureal2ereal_inject zero_ureal.rep_eq)

lemma ureal_top_one: "\<top> = \<^bold>1"
  by (metis one_ureal.rep_eq top_apply top_ureal.rep_eq ureal2ereal_inject)

lemma ureal_zero: "rvfun_of_prfun \<^bold>0 = (0)\<^sub>e"
  apply (simp add: ureal_defs)
  by (simp add: zero_ureal.rep_eq)

lemma ureal_zero': "prfun_of_rvfun (0)\<^sub>e = \<^bold>0"
  apply (simp add: ureal_defs)
  by (metis SEXP_apply ureal2ereal_inverse zero_ureal.rep_eq)

lemma ureal_one: "rvfun_of_prfun \<^bold>1 = (1)\<^sub>e"
  apply (simp add: ureal_defs)
  by (simp add: one_ureal.rep_eq)

lemma ureal_one': "prfun_of_rvfun (1)\<^sub>e = \<^bold>1"
  apply (simp add: ureal_defs)
  by (metis SEXP_def one_ereal_def one_ureal.rep_eq ureal2ereal_inverse)

lemma ureal_bottom_least: "\<^bold>0 \<le> P"
  apply (simp add: le_fun_def pfun_defs ureal_defs)
  apply (auto)
  by (metis bot.extremum bot_ureal.rep_eq ureal2ereal_inject zero_ureal.rep_eq)

lemma ureal_bottom_least': "0\<^sub>p \<le> P"
  apply (simp add: pfun_defs)
  by (rule ureal_bottom_least)

lemma ureal_top_greatest: "P \<le> \<^bold>1"
  apply (simp add: le_fun_def pfun_defs ureal_defs)
  apply (auto)
  using less_eq_ureal.rep_eq one_ureal.rep_eq ureal2ereal by auto

lemma ureal_top_greatest': "P \<le> 1\<^sub>p"
  by (metis le_fun_def one_ureal.rep_eq pone_def top_greatest top_ureal.rep_eq ureal2ereal_inject)

subsubsection \<open> Skip \<close>
lemma rvfun_skip_f_is_prob: "is_prob II\<^sub>f"
  by (simp add: is_prob_def iverson_bracket_def)

lemma rvfun_skip_f_is_dist: "is_final_distribution II\<^sub>f"
  apply (simp add: dist_defs expr_defs)
  by (simp add: infsum_singleton)

lemma rvfun_skip_inverse: "rvfun_of_prfun (prfun_of_rvfun II\<^sub>f) = II\<^sub>f"
  by (simp add: is_prob_def iverson_bracket_def rvfun_inverse)

lemma rvfun_skip\<^sub>_f_simp: "II\<^sub>f = (\<lambda>(s, s'). if s = s' then 1 else 0)"
  by (expr_auto)

theorem prfun_skip: 
  assumes "wb_lens x"
  shows "(II::'a prhfun) = (x := $x)"
  apply (simp add: pfun_defs)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (rel_auto)
  by (simp add: assms)+

theorem prfun_skip':
  shows "rvfun_of_prfun (II) = pskip\<^sub>_f"
  apply (simp add: pfun_defs)
  using rvfun_skip_inverse by blast

lemma prfun_skip_id: "II\<^sub>p (s, s) = 1"
  apply (simp add: pfun_defs ureal_defs)
  by (simp add: ereal2ureal_def iverson_bracket_def one_ereal_def one_ureal_def rel_skip)

lemma prfun_skip_not_id: 
  assumes "s \<noteq> s'"
  shows "II\<^sub>p (s, s') = 0"
  apply (simp add: pfun_defs ureal_defs)
  by (simp add: assms ereal2ureal_def iverson_bracket_def rel_skip zero_ureal_def)

subsubsection \<open> Assignment \<close>
lemma rvfun_assignment_is_prob: "is_prob (passigns_f \<sigma>)"
  by (simp add: is_prob_def iverson_bracket_def)

lemma rvfun_assignment_is_dist: "is_final_distribution (passigns_f \<sigma>)"
  apply (simp add: dist_defs expr_defs)
  apply (rel_auto)
  by (simp add: infsum_singleton)

lemma rvfun_assignment_inverse: "rvfun_of_prfun (prfun_of_rvfun (passigns_f \<sigma>)) = (passigns_f \<sigma>)"
  by (simp add: is_prob_def iverson_bracket_def rvfun_inverse)

subsubsection \<open> Probabilistic choice \<close>
term "(rvfun_of_prfun r)\<^sup>\<Up>"
lemma rvfun_pchoice_is_prob: 
  assumes "is_prob P" "is_prob Q"
  shows "is_prob (P \<oplus>\<^sub>f\<^bsub>(rvfun_of_prfun r)\<^sup>\<Up>\<^esub> Q)"
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: assms(1) assms(2) is_prob prfun_in_0_1')
  by (simp add: assms(1) assms(2) convex_bound_le is_final_prob_altdef is_prob_final_prob prfun_in_0_1')

lemma rvfun_pchoice_is_prob': 
  assumes "is_prob P" "is_prob Q"
  shows "is_prob (P \<oplus>\<^sub>f\<^bsub>(\<lambda>s. ureal2real r)\<^esub> Q)"
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: assms(1) assms(2) is_prob ureal_lower_bound ureal_upper_bound)
  by (simp add: assms(1) assms(2) convex_bound_le is_final_prob_altdef is_prob_final_prob 
      ureal_lower_bound ureal_upper_bound)

lemma rvfun_pchoice_is_dist: 
  assumes "is_final_distribution P" "is_final_distribution Q"
  shows "is_final_distribution (P \<oplus>\<^sub>f\<^bsub>(rvfun_of_prfun r)\<^sup>\<Up>\<^esub> Q)"
  apply (simp add: dist_defs expr_defs, auto)
  apply (simp add: assms(1) assms(2) prfun_in_0_1' rvfun_prob_sum1_summable(1))
  apply (simp add: assms(1) assms(2) convex_bound_le prfun_in_0_1' rvfun_prob_sum1_summable(1))
  apply (subst infsum_add)
  apply (simp add: assms(1) rvfun_prob_sum1_summable(3) summable_on_cmult_right)
   apply (subst summable_on_cmult_right)
  apply (simp add: assms(2) rvfun_prob_sum1_summable(3))+
  apply (subst infsum_cmult_right)
  apply (simp add: assms(1) rvfun_prob_sum1_summable(3) summable_on_cmult_right)
  apply (subst infsum_cmult_right)
  apply (simp add: assms(2) rvfun_prob_sum1_summable(3) summable_on_cmult_right)
  by (simp add: assms(1) assms(2) rvfun_prob_sum1_summable(2))

lemma rvfun_pchoice_is_dist': 
  assumes "is_final_distribution P" "is_final_distribution Q"
  shows "is_final_distribution (P \<oplus>\<^sub>f\<^bsub>(\<lambda>s. ureal2real r)\<^esub> Q)"
  apply (simp add: dist_defs expr_defs, auto)
  apply (simp add: assms(1) assms(2) rvfun_prob_sum1_summable(1) ureal_lower_bound ureal_upper_bound)
  apply (simp add: assms(1) assms(2) convex_bound_le rvfun_prob_sum1_summable(1) ureal_lower_bound ureal_upper_bound)
  apply (subst infsum_add)
  apply (simp add: assms(1) rvfun_prob_sum1_summable(3) summable_on_cmult_right)
  apply (subst summable_on_cmult_right)
  apply (simp add: assms(2) rvfun_prob_sum1_summable(3))+
  apply (subst infsum_cmult_right)
  apply (simp add: assms(1) rvfun_prob_sum1_summable(3) summable_on_cmult_right)
  apply (subst infsum_cmult_right)
  apply (simp add: assms(2) rvfun_prob_sum1_summable(3) summable_on_cmult_right)
  by (simp add: assms(1) assms(2) rvfun_prob_sum1_summable(2))

lemma rvfun_pchoice_inverse:
  assumes "is_prob P" "is_prob Q"
  shows "rvfun_of_prfun (prfun_of_rvfun (P \<oplus>\<^sub>f\<^bsub>(rvfun_of_prfun r)\<^esub> Q)) = (P \<oplus>\<^sub>f\<^bsub>(rvfun_of_prfun r)\<^esub> Q)"
  apply (simp add: dist_defs expr_defs)
  apply (rule rvfun_inverse)
  apply (simp add: is_prob_def expr_defs, auto)
  apply (simp add: assms(1) assms(2) is_prob prfun_in_0_1')
  by (simp add: assms(1) assms(2) convex_bound_le is_prob prfun_in_0_1')

lemma rvfun_pchoice_inverse_pre:
  assumes "is_prob P" "is_prob Q"
  shows "rvfun_of_prfun (prfun_of_rvfun (P \<oplus>\<^sub>f\<^bsub>(rvfun_of_prfun r)\<^sup>\<Up>\<^esub> Q)) = (P \<oplus>\<^sub>f\<^bsub>(rvfun_of_prfun r)\<^sup>\<Up>\<^esub> Q)"
  apply (simp add: dist_defs expr_defs)
  apply (rule rvfun_inverse)
  apply (simp add: is_prob_def expr_defs, auto)
  apply (simp add: assms(1) assms(2) is_prob prfun_in_0_1')
  by (simp add: assms(1) assms(2) convex_bound_le is_prob prfun_in_0_1')

lemma rvfun_pchoice_inverse_pre': 
  assumes "is_prob P" "is_prob Q"
  shows "rvfun_of_prfun (prfun_of_rvfun (pchoice_f P [(rvfun_of_prfun r)\<^sup>\<Up>]\<^sub>e Q)) = pchoice_f P [(rvfun_of_prfun r)\<^sup>\<Up>]\<^sub>e Q"
  apply (simp add: dist_defs expr_defs)
  apply (rule rvfun_inverse)
  apply (simp add: is_prob_def expr_defs, auto)
  apply (simp add: assms(1) assms(2) is_prob prfun_in_0_1')
  by (simp add: assms(1) assms(2) convex_bound_le is_prob prfun_in_0_1')

lemma rvfun_pchoice_inverse_c: 
  assumes "is_prob P" "is_prob Q"
  shows "rvfun_of_prfun (prfun_of_rvfun (P \<oplus>\<^sub>f\<^bsub>(\<lambda>s. ureal2real r)\<^esub> Q)) = (P \<oplus>\<^sub>f\<^bsub>(\<lambda>s. ureal2real r)\<^esub> Q)"
  apply (simp add: dist_defs expr_defs)
  apply (rule rvfun_inverse)
  apply (simp add: is_prob_def expr_defs, auto)
   apply (simp add: assms(1) assms(2) is_prob ureal_lower_bound ureal_upper_bound)
  by (simp add: assms(1) assms(2) convex_bound_le is_final_prob_altdef is_prob_final_prob 
      ureal_lower_bound ureal_upper_bound)

lemma rvfun_pchoice_inverse_c': 
  assumes "is_prob P" "is_prob Q"
  assumes "0 \<le> r \<and> r \<le> (1::\<real>)"
  shows "rvfun_of_prfun (prfun_of_rvfun (pchoice_f P [(\<lambda>s. ureal2real r)]\<^sub>e Q)) = (pchoice_f P [(\<lambda>s. ureal2real r)]\<^sub>e Q)"
  apply (simp add: dist_defs expr_defs)
  apply (rule rvfun_inverse)
  apply (simp add: is_prob_def expr_defs, auto)
   apply (simp add: assms(1) assms(2) is_prob ureal_lower_bound ureal_upper_bound)
  by (simp add: assms(1) assms(2) convex_bound_le is_final_prob_altdef is_prob_final_prob 
      ureal_lower_bound ureal_upper_bound)

theorem prfun_pchoice_altdef: 
  "if\<^sub>p r then P else Q 
    = prfun_of_rvfun (@(rvfun_of_prfun r) * @(rvfun_of_prfun P) + (1 - @(rvfun_of_prfun (r))) * @(rvfun_of_prfun Q))\<^sub>e"
  by (simp add: pfun_defs ureal_defs)

theorem prfun_pchoice_commute: "if\<^sub>p r then P else Q = if\<^sub>p 1 - r then Q else P"
  apply (simp add: pfun_defs)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (expr_auto)
  apply (simp add: ureal_1_minus_1_minus_r_r)
  apply (simp add: ureal_defs)
  apply (rule disjI2)
  by (metis Orderings.order_eq_iff abs_ereal_ge0 atLeastAtMost_iff ereal_diff_positive ereal_less_eq(1) 
      ereal_times(1) max.absorb2 minus_ureal.rep_eq one_ureal.rep_eq real_ereal_1 real_of_ereal_minus 
      ureal2ereal)

theorem prfun_pchoice_zero: "if\<^sub>p 0 then P else Q = Q"
  apply (simp add: pfun_defs)
  apply (simp add: ureal_defs)
  apply (simp add: ureal_zero_0)
  apply (subst fun_eq_iff, auto)
  by (metis abs_ereal_ge0 add_0 atLeastAtMost_iff ereal_less_eq(1) ereal_real ereal_times(1) 
      max.absorb2 max_min_same(1) min.commute plus_ureal.rep_eq ureal2ereal ureal2ereal_inverse 
      zero_ureal.rep_eq)

theorem prfun_pchoice_one: "if\<^sub>p 1 then P else Q = P"
  apply (simp add: pfun_defs)
  apply (simp add: ureal_defs)
  apply (simp add: ureal_one_1)
  apply (subst fun_eq_iff, auto)
  by (metis abs_ereal_ge0 add_0 atLeastAtMost_iff ereal_less_eq(1) ereal_real ereal_times(1) 
      max.absorb2 max_min_same(1) min.commute plus_ureal.rep_eq ureal2ereal ureal2ereal_inverse 
      zero_ureal.rep_eq)

theorem prfun_pchoice_zero': 
  fixes w\<^sub>1 :: "'a \<Rightarrow> ureal"
  assumes "`w\<^sub>1 = 0`"
  shows "P \<oplus>\<^bsub>w\<^sub>1\<^sup>\<Up>\<^esub> Q = Q"
  apply (simp add: pfun_defs)
proof -
  have f1: "rvfun_of_prfun (w\<^sub>1\<^sup>\<Up>) = (0)\<^sub>e"
    apply (simp add: ureal_defs)
    apply (subst fun_eq_iff, auto)
    by (metis (mono_tags, lifting) SEXP_def assms real_of_ereal_0 taut_def zero_ureal.rep_eq)
  show "prfun_of_rvfun (pchoice_f (rvfun_of_prfun P) (rvfun_of_prfun (w\<^sub>1\<^sup>\<Up>)) (rvfun_of_prfun Q)) = Q"
    apply (simp add: f1 SEXP_def)
    by (simp add: prfun_inverse)
qed

lemma prfun_condition_pre: "(rvfun_of_prfun r)\<^sup>\<Up> (a, b) = ureal2real (r a)"
  by (simp add: rvfun_of_prfun_def)

theorem prfun_pchoice_assoc:
  fixes w\<^sub>1 :: "'a \<Rightarrow> ureal"
  assumes "\<forall>s. ((1 - ureal2real (w\<^sub>1 s)) * (1 - ureal2real (w\<^sub>2 s))) = (1 - ureal2real (r\<^sub>2 s))"
  assumes "\<forall>s. (ureal2real (w\<^sub>1 s)) = (ureal2real (r\<^sub>1 s) * ureal2real (r\<^sub>2 s))"
  shows "P \<oplus>\<^bsub>w\<^sub>1\<^sup>\<Up>\<^esub> (Q \<oplus>\<^bsub>(w\<^sub>2\<^sup>\<Up>)\<^esub> R) = (P \<oplus>\<^bsub>r\<^sub>1\<^sup>\<Up>\<^esub> Q) \<oplus>\<^bsub>r\<^sub>2\<^sup>\<Up>\<^esub> R" (is "?lhs = ?rhs")
proof -
  have f0: "\<forall>s. ((1 - ureal2real (w\<^sub>1 s)) * (1 - ureal2real (w\<^sub>2 s))) = 
    (1 - ureal2real (w\<^sub>1 s) - ureal2real (w\<^sub>2 s) + ureal2real (w\<^sub>1 s) * ureal2real (w\<^sub>2 s))"
    by (metis diff_add_eq diff_diff_eq2 left_diff_distrib mult.commute mult_1)
  then have f1: "\<forall>s. (1 - ureal2real (w\<^sub>1 s) - ureal2real (w\<^sub>2 s) + ureal2real (w\<^sub>1 s) * ureal2real (w\<^sub>2 s))
    = ((1 - ureal2real (r\<^sub>2 s)))"
    using assms(1) by presburger
  then have f2: "\<forall>s. (ureal2real (r\<^sub>2 s)) = (ureal2real (w\<^sub>1 s) + ureal2real (w\<^sub>2 s) - ureal2real (w\<^sub>1 s) * ureal2real (w\<^sub>2 s))"
    by (smt (verit, del_insts) SEXP_apply)
  have f3: "\<forall>s. (ureal2real (w\<^sub>1 s)) = (ureal2real (r\<^sub>1 s) * (ureal2real (w\<^sub>1 s) + ureal2real (w\<^sub>2 s) - ureal2real (w\<^sub>1 s) * ureal2real (w\<^sub>2 s)))"
    using assms(2) f2 by (simp)
  have P_eq: "\<forall>a b. ((rvfun_of_prfun w\<^sub>1)\<^sup>\<Up> (a, b) * (rvfun_of_prfun P) (a, b) = 
      ((rvfun_of_prfun r\<^sub>2)\<^sup>\<Up> (a, b) * ((rvfun_of_prfun r\<^sub>1)\<^sup>\<Up> (a, b) * (rvfun_of_prfun P) (a, b))))"
    apply (auto)
    by (simp add: assms(2) rvfun_of_prfun_def)
  have Q_eq: "\<forall>a b. ((((1::\<real>) - (rvfun_of_prfun w\<^sub>1)\<^sup>\<Up> (a, b)) * ((rvfun_of_prfun w\<^sub>2)\<^sup>\<Up> (a, b) * (rvfun_of_prfun Q) (a, b)))
    = ((rvfun_of_prfun r\<^sub>2)\<^sup>\<Up> (a, b) * (((1::\<real>) - (rvfun_of_prfun r\<^sub>1)\<^sup>\<Up> (a, b)) * (rvfun_of_prfun Q) (a, b))))"
    apply (simp add: prfun_condition_pre)
    apply (rule allI)
    apply (rule disjI2)
  proof -
    fix a
    have "rvfun_of_prfun r\<^sub>2 a * ((1::\<real>) - rvfun_of_prfun r\<^sub>1 a) = rvfun_of_prfun r\<^sub>2 a - rvfun_of_prfun r\<^sub>2 a * rvfun_of_prfun r\<^sub>1 a"
      by (simp add: right_diff_distrib)
    also have "... = rvfun_of_prfun r\<^sub>2 a - rvfun_of_prfun w\<^sub>1 a"
      by (simp add: assms(2) rvfun_of_prfun_def)
    also have "... = rvfun_of_prfun w\<^sub>2 a - rvfun_of_prfun w\<^sub>1 a * rvfun_of_prfun w\<^sub>2 a"
      using f2 by (simp add: rvfun_of_prfun_def)
    then show "((1::\<real>) - rvfun_of_prfun w\<^sub>1 a) * rvfun_of_prfun w\<^sub>2 a = rvfun_of_prfun r\<^sub>2 a * ((1::\<real>) - rvfun_of_prfun r\<^sub>1 a)"
      by (simp add: calculation left_diff_distrib)
  qed
  have R_eq: "\<forall>a b. ((((1::\<real>) - (rvfun_of_prfun w\<^sub>1)\<^sup>\<Up> (a, b)) * (((1::\<real>) - (rvfun_of_prfun w\<^sub>2)\<^sup>\<Up> (a, b)) * (rvfun_of_prfun R) (a, b)))
    = (((1::\<real>) - (rvfun_of_prfun r\<^sub>2)\<^sup>\<Up> (a, b)) * (rvfun_of_prfun R) (a, b)))"
    apply (simp add: prfun_condition_pre)
    apply (rule allI)
    apply (rule disjI2)
    by (simp add: assms(1) rvfun_of_prfun_def)
  
  show ?thesis
    apply (simp add: pfun_defs)
    apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
    apply (simp add: dist_defs expr_defs)
    apply (subst rvfun_inverse)
     apply (smt (verit, del_insts) SEXP_apply is_prob_def mult_nonneg_nonneg mult_right_le_one_le prfun_in_0_1' taut_def)
    apply (subst rvfun_inverse)
     apply (smt (verit, del_insts) SEXP_apply is_prob_def mult_nonneg_nonneg mult_right_le_one_le prfun_in_0_1' taut_def)
    apply (subst fun_eq_iff)
    apply (auto)
    apply (subst distrib_left)+
    using P_eq Q_eq R_eq by (smt (verit, ccfv_SIG) SEXP_def prod.simps(2) rvfun_of_prfun_def)
qed

theorem prfun_pchoice_assigns:
  "(if\<^sub>p r then x := e else y := f) = 
    prfun_of_rvfun (@(rvfun_of_prfun r) * \<lbrakk>\<lbrakk>x := e\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e + (1 - @(rvfun_of_prfun r)) * \<lbrakk>\<lbrakk>y := f\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"
  apply (simp add: pfun_defs)
  apply (simp add: rvfun_assignment_inverse)
  by (expr_auto)

thm "rvfun_pchoice_inverse"
lemma prfun_pchoice_assigns_inverse:
  shows "rvfun_of_prfun ((x := e) \<oplus>\<^bsub>r\<^sup>\<Up>\<^esub> (y := f)) 
       = (pchoice_f (\<lbrakk>\<lbrakk>x := e\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>) ((rvfun_of_prfun r)\<^sup>\<Up>)\<^sub>e (\<lbrakk>\<lbrakk>y := f\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>))"
  apply (simp only: passigns_def pchoice_def)
  apply (simp add: rvfun_assignment_inverse)
  apply (simp add: dist_defs expr_defs)
  apply (subst rvfun_inverse)
  apply (simp add: is_prob_def prfun_in_0_1')
  apply (subst fun_eq_iff)
  apply (auto)
  by (simp add: rvfun_of_prfun_def)+

lemma prfun_pchoice_assigns_inverse_c:
  shows "rvfun_of_prfun ((x := e) \<oplus>\<^bsub>(\<lambda>s. ureal2real r)\<^esub> (y := f)) 
       = (pchoice_f (\<lbrakk>\<lbrakk>x := e\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e) (ureal2real \<guillemotleft>r\<guillemotright>)\<^sub>e (\<lbrakk>\<lbrakk>y := f\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e))"
  apply (simp add: pfun_defs)
  apply (simp add: rvfun_assignment_inverse)
  apply (simp add: dist_defs expr_defs)
  apply (subst rvfun_inverse)
  apply (simp add: is_prob_def prfun_in_0_1')
  apply (subst fun_eq_iff)
  apply (auto)
  by (metis SEXP_def abs_ereal_ge0 atLeastAtMost_iff comp_def ereal2ureal_def ereal_less_eq(1) 
      ereal_real ereal_times(1) max.absorb1 max.absorb2 min_def rvfun_of_prfun_def 
      type_definition.Rep_inverse type_definition_ureal ureal2ereal ureal2real_def)+

lemma prfun_pchoice_assigns_inverse_c':
  shows "rvfun_of_prfun ((x := e) \<oplus>\<^bsub>[(\<lambda>s. ureal2real r)]\<^sub>e\<^esub> (y := f)) 
       = (pchoice_f (\<lbrakk>\<lbrakk>x := e\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e) (ureal2real \<guillemotleft>r\<guillemotright>)\<^sub>e (\<lbrakk>\<lbrakk>y := f\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e))"
  by (simp add: prfun_pchoice_assigns_inverse_c)

subsubsection \<open> Conditional choice \<close>
lemma rvfun_pcond_is_prob: 
  assumes "is_prob P" "is_prob Q"
  shows "is_prob (P \<lhd>\<^sub>f b \<rhd> Q)"
  by (smt (verit, best) SEXP_def assms(1) assms(2) is_prob_def taut_def)

lemma rvfun_pcond_altdef: "(P \<lhd>\<^sub>f b \<rhd> Q) = (\<lbrakk>b\<rbrakk>\<^sub>\<I> * P + \<lbrakk>\<not>b\<rbrakk>\<^sub>\<I>\<^sub>e * Q)\<^sub>e"
  by (expr_auto)

lemma rvfun_pcond_is_dist: 
  assumes "is_final_distribution P" "is_final_distribution Q"
  shows "is_final_distribution (P \<lhd>\<^sub>f (b\<^sup>\<Up>) \<rhd> Q)"
  apply (simp add: dist_defs expr_defs, auto)
  apply (simp add: assms is_final_distribution_prob is_final_prob_altdef)+
  by (smt (verit, best) assms(1) assms(2) curry_conv infsum_cong is_dist_def is_sum_1_def)

lemma rvfun_pcond_inverse:
  assumes "is_prob P" "is_prob Q"
  shows "rvfun_of_prfun (prfun_of_rvfun (P \<lhd>\<^sub>f b \<rhd> Q)) = (P \<lhd>\<^sub>f b \<rhd> Q)"
  by (simp add: assms(1) assms(2) rvfun_inverse rvfun_pcond_is_prob)

lemma prfun_pcond_altdef: 
  shows "if\<^sub>c b then P else Q = prfun_of_rvfun (\<lbrakk>b\<rbrakk>\<^sub>\<I> * @(rvfun_of_prfun P) + \<lbrakk>\<not>b\<rbrakk>\<^sub>\<I>\<^sub>e * @(rvfun_of_prfun Q))\<^sub>e"
  apply (simp add: pfun_defs)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  by (expr_auto)

lemma prfun_pcond_id: 
  shows "(if\<^sub>c b then P else P) = P"
  apply (simp add: pfun_defs)
  apply (expr_auto)
  by (simp add: prfun_inverse)

lemma prfun_pcond_pchoice_eq: 
  shows "if\<^sub>c b then P else Q = (if\<^sub>p \<lbrakk>b\<rbrakk>\<^sub>\<I> then P else Q)"
  apply (simp add: pfun_defs)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (simp add: rvfun_pcond_altdef)
proof -
  have f0: "rvfun_of_prfun (\<lambda>x::'a \<times> 'b. ereal2ureal (ereal ((\<lbrakk>b\<rbrakk>\<^sub>\<I>) x))) = \<lbrakk>b\<rbrakk>\<^sub>\<I>"
    apply (simp add: ureal_defs)
    apply (simp add: expr_defs)
    by (simp add: ereal2ureal'_inverse)
  show "[\<lambda>\<s>::'a \<times> 'b. (\<lbrakk>b\<rbrakk>\<^sub>\<I>) \<s> * rvfun_of_prfun P \<s> + (\<lbrakk>[\<lambda>\<s>::'a \<times> 'b. \<not> b \<s>]\<^sub>e\<rbrakk>\<^sub>\<I>) \<s> * rvfun_of_prfun Q \<s>]\<^sub>e =
    rvfun_of_prfun P \<oplus>\<^sub>f\<^bsub>rvfun_of_prfun (\<lambda>x::'a \<times> 'b. ereal2ureal (ereal ((\<lbrakk>b\<rbrakk>\<^sub>\<I>) x)))\<^esub> rvfun_of_prfun Q"
    apply (simp add: f0)
    apply (subst fun_eq_iff)
    apply (auto)
    by (metis SEXP_def iverson_bracket_not)
qed

lemma prfun_pcond_mono: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2; Q\<^sub>1 \<le> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (if\<^sub>c b then P\<^sub>1 else Q\<^sub>1) \<le> (if\<^sub>c b then P\<^sub>2 else Q\<^sub>2)"
  apply (simp add: pcond_def ureal_defs)
  apply (simp add: le_fun_def)
  apply (auto)
  apply (simp add: ureal_defs)
  apply (smt (z3) atLeastAtMost_iff ereal_less_eq(1) ereal_less_eq(4) ereal_real ereal_times(1) 
      max.absorb1 max.absorb2 min.absorb1 real_of_ereal_le_0 ureal2ereal ureal2ereal_inverse)
  apply (simp add: ureal_defs)
  by (smt (z3) atLeastAtMost_iff ereal_less_eq(1) ereal_less_eq(4) ereal_real ereal_times(1) 
      max.absorb1 max.absorb2 min.absorb1 real_of_ereal_le_0 ureal2ereal ureal2ereal_inverse)

subsubsection \<open> Sequential composition \<close>
lemma rvfun_seqcomp_dist_is_prob: 
  assumes "is_final_distribution p" "is_prob q"
  shows "is_prob (pseqcomp_f p q)"
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: assms(1) assms(2) infsum_nonneg is_prob rvfun_prob_sum1_summable(1))
proof -
  fix a b
  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (a, v\<^sub>0) * q (v\<^sub>0, b)) \<le> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (a, v\<^sub>0))"
    apply (subst infsum_mono)
    apply (simp add: assms(1) assms(2) is_prob rvfun_product_summable_dist)
    apply (simp add: assms(1) rvfun_prob_sum1_summable(3))
    apply (simp add: assms(1) assms(2) is_prob mult_right_le_one_le rvfun_prob_sum1_summable(1))
    by simp
  also have "... = 1"
    by (metis assms(1) rvfun_prob_sum1_summable(2))
  then show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (a, v\<^sub>0) * q (v\<^sub>0, b)) \<le> (1::\<real>)"
    using calculation by presburger
qed

lemma rvfun_seqcomp_subdist_is_prob: 
  assumes "is_final_sub_dist p" "is_prob q"
  shows "is_prob (pseqcomp_f p q)"
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: assms(1) assms(2) infsum_nonneg is_prob rvfun_prob_sum_leq_1_summable(1))
proof -
  fix a b
  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (a, v\<^sub>0) * q (v\<^sub>0, b)) \<le> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (a, v\<^sub>0))"
    apply (subst infsum_mono)
    apply (simp add: assms(1) assms(2) is_prob rvfun_product_summable)
    apply (simp add: assms(1) rvfun_prob_sum_leq_1_summable(4))
    apply (simp add: assms(1) assms(2) is_prob mult_right_le_one_le rvfun_prob_sum_leq_1_summable(1))
    by simp
  then show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (a, v\<^sub>0) * q (v\<^sub>0, b)) \<le> (1::\<real>)"
    by (smt (verit, ccfv_SIG) assms(1) curry_conv dual_order.refl infsum_cong is_sub_dist_def 
        is_sum_leq_1_def)
qed

(*
lemma rvfun_seqcomp_summable_is_prob: 
  assumes "\<forall>s\<^sub>1. ((curry p) s\<^sub>1) summable_on UNIV"
  assumes "is_prob p" "is_prob q"
  shows "is_prob (pseqcomp_f p q)"
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: assms(2) assms(3) infsum_nonneg is_prob)
proof -
  fix a b
  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (a, v\<^sub>0) * q (v\<^sub>0, b)) \<le> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (a, v\<^sub>0))"
    apply (subst infsum_mono)
    apply (simp add: assms is_prob rvfun_product_summable_summable)
      apply (metis assms(1) case_prod_eta curry_case_prod)
    apply (simp add: assms(2) assms(3) is_prob mult_left_le)
    by simp
  also have "... \<le> 1"
    sledgehammer
  then show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (a, v\<^sub>0) * q (v\<^sub>0, b)) \<le> (1::\<real>)"
    using calculation by presburger
qed
*)

lemma rvfun_cond_prob_abs_summable_on_product:
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "(\<lambda>(v\<^sub>0::'a, s::'a). p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) abs_summable_on 
          Sigma (UNIV) (\<lambda>v\<^sub>0. {s'. q(v\<^sub>0, s') > (0::real)})"
  apply (subst abs_summable_on_Sigma_iff)
  apply (rule conjI)
  apply (auto)
proof -
  fix x::"'a"

  have f1: "(\<lambda>xa::'a. \<bar>p (s\<^sub>1, x) * q (x, xa)\<bar>) = (\<lambda>xa::'a. p (s\<^sub>1, x) * q (x, xa))"
    apply (subst abs_of_nonneg)
    by (simp add: assms(1) assms(2) rvfun_prob_sum1_summable(1))+
  have f2: "(\<lambda>xa::'a. p (s\<^sub>1, x) * q (x, xa)) summable_on {s'::'a. (0::\<real>) < q (x, s')}"
    apply (rule summable_on_cmult_right)
    apply (rule summable_on_subset_banach[where A="UNIV"])
    using assms(1) assms(2) rvfun_prob_sum1_summable(3) apply metis
    by (simp)
  show "(\<lambda>xa::'a. \<bar>p (s\<^sub>1, x) * q (x, xa)\<bar>) summable_on {s'::'a. (0::\<real>) < q (x, s')}"
    using f1 f2 by presburger
next
  have f1: "(\<lambda>x::'a. \<bar>\<Sum>\<^sub>\<infinity>y::'a\<in>{s'::'a. (0::\<real>) < q (x, s')}. \<bar>p (s\<^sub>1, x) * q (x, y)\<bar>\<bar>) =
      (\<lambda>x::'a. \<Sum>\<^sub>\<infinity>y::'a\<in>{s'::'a. (0::\<real>) < q (x, s')}. p (s\<^sub>1, x) * q (x, y))"
    apply (subst abs_of_nonneg)
    apply (subst abs_of_nonneg)
    apply (simp add: assms(1) assms(2) rvfun_prob_sum1_summable(1))+
     apply (simp add: assms(1) assms(2) infsum_nonneg rvfun_prob_sum1_summable(1))
    apply (subst abs_of_nonneg)
    by (simp add: assms(1) assms(2) rvfun_prob_sum1_summable(1))+
  then have f2: "... = (\<lambda>x::'a. p (s\<^sub>1, x) * (\<Sum>\<^sub>\<infinity>y::'a\<in>{s'::'a. (0::\<real>) < q (x, s')}. q (x, y)))"
    using infsum_cmult_right' by fastforce
  have f3: "... = (\<lambda>x::'a. p (s\<^sub>1, x))"
    apply (rule ext)
    proof -
      fix x
      have f31: "(\<Sum>\<^sub>\<infinity>y::'a\<in>{s'::'a. (0::\<real>) < q (x, s')}. q (x, y)) = 
        (\<Sum>\<^sub>\<infinity>y::'a\<in>{s'::'a. (0::\<real>) < q (x, s')} \<union> {s'::'a. (0::\<real>) = q (x, s')}. q (x, y))"
        apply (rule infsum_cong_neutral)
        by force+
      then have f32: "... = (\<Sum>\<^sub>\<infinity>y::'a. q (x, y))"
        by (smt (verit, del_insts) assms(2) infsum_cong infsum_mult_subset_right mult_cancel_left1 
              rvfun_prob_sum1_summable(1))
      then have f33: "... = 1"
        by (simp add: assms(2) rvfun_prob_sum1_summable(2))
      then show "p (s\<^sub>1, x) * (\<Sum>\<^sub>\<infinity>y::'a\<in>{s'::'a. (0::\<real>) < q (x, s')}. q (x, y)) = p (s\<^sub>1, x)"
        using f31 f32 by auto
    qed
  have f4: "infsum (\<lambda>x::'a. \<Sum>\<^sub>\<infinity>y::'a\<in>{s'::'a. (0::\<real>) < q (x, s')}. p (s\<^sub>1, x) * q (x, y)) UNIV = 
      infsum (\<lambda>x::'a. p (s\<^sub>1, x)) UNIV"
    using f2 f3 by presburger
  then have f5: "... = 1"
    by (simp add: assms(1) rvfun_prob_sum1_summable(2))
    
  have f6: "(\<lambda>x::'a. \<Sum>\<^sub>\<infinity>y::'a\<in>{s'::'a. (0::\<real>) < q (x, s')}. p (s\<^sub>1, x) * q (x, y)) summable_on UNIV"
    using f4 f5 infsum_not_exists by fastforce
    
  show "(\<lambda>x::'a. \<bar>\<Sum>\<^sub>\<infinity>y::'a\<in>{s'::'a. (0::\<real>) < q (x, s')}. \<bar>p (s\<^sub>1, x) * q (x, y)\<bar>\<bar>) summable_on UNIV"
    using f1 f6 by presburger
qed

lemma rvfun_cond_prob_product_summable_on_sigma_possible_sets:
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "(\<lambda>(v\<^sub>0::'a, s::'a). p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) summable_on 
          Sigma (UNIV) (\<lambda>v\<^sub>0. {s'. q(v\<^sub>0, s') > (0::real)})"
  apply (subst summable_on_iff_abs_summable_on_real)
  using rvfun_cond_prob_abs_summable_on_product assms(1) assms(2) by fastforce

lemma rvfun_cond_prob_product_summable_on_sigma_impossible_sets:
  shows "(\<lambda>(v\<^sub>0::'a, s::'a). p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) summable_on (Sigma (UNIV) (\<lambda>v\<^sub>0. {s'. q(v\<^sub>0, s') = (0::real)}))"
  apply (simp add: summable_on_def)
  apply (rule_tac x = "0" in exI)
  apply (rule has_sum_0)
  by force

lemma rvfun_cond_prob_product_summable_on_UNIV:
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "(\<lambda>(v\<^sub>0::'a, s::'a). p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) summable_on Sigma (UNIV) (\<lambda>v\<^sub>0. UNIV)"
proof -
  let ?A1 = "Sigma (UNIV) (\<lambda>v\<^sub>0. {s'. q(v\<^sub>0, s') > (0::real)})"
  let ?A2 = "Sigma (UNIV) (\<lambda>v\<^sub>0. {s'. q(v\<^sub>0, s') = (0::real)})"
  let ?f = "(\<lambda>(v\<^sub>0::'a, s::'a). p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s))"

  have "?f summable_on (?A1 \<union> ?A2)"
    apply (rule summable_on_Un_disjoint)
    apply (simp add: assms(1) assms(2) rvfun_cond_prob_product_summable_on_sigma_possible_sets)
    apply (simp add: rvfun_cond_prob_product_summable_on_sigma_impossible_sets)
    by fastforce
  then show ?thesis
    by (simp add: assms(2) prel_Sigma_UNIV_divide)
qed

lemma rvfun_cond_prob_product_summable_on_UNIV_2:
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows " (\<lambda>(s::'a, v\<^sub>0::'a). p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) summable_on UNIV \<times> UNIV"
    apply (subst product_swap[symmetric])
    apply (subst summable_on_reindex)
    apply simp
    proof -
      have f0: "(\<lambda>(s::'a, v\<^sub>0::'a). p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) \<circ> prod.swap = (\<lambda>(v\<^sub>0::'a, s::'a). p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s))"
        by (simp add: comp_def)
      show "(\<lambda>(s::'a, v\<^sub>0::'a). p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) \<circ> prod.swap summable_on UNIV \<times> UNIV"
        using assms(1) assms(2) f0 rvfun_cond_prob_product_summable_on_UNIV by fastforce
    qed

lemma rvfun_cond_prob_infsum_pcomp_swap:
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "(\<Sum>\<^sub>\<infinity>s::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. \<Sum>\<^sub>\<infinity>s::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s))"
  apply (rule infsum_swap_banach)
  using assms(1) assms(2) rvfun_cond_prob_product_summable_on_UNIV_2 by fastforce

lemma rvfun_infsum_pcomp_sum_1:
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "(\<Sum>\<^sub>\<infinity>s::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) = 1"
  apply (simp add: assms rvfun_cond_prob_infsum_pcomp_swap)
  apply (simp add: infsum_cmult_right')
  by (simp add: assms rvfun_prob_sum1_summable)

lemma rvfun_infsum_pcomp_summable:
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "(\<lambda>s::'a. (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s))) summable_on UNIV"
  apply (rule infsum_not_zero_is_summable)
  by (simp add: assms(1) assms(2) rvfun_infsum_pcomp_sum_1)

lemma rvfun_infsum_pcomp_lessthan_1:
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "\<forall>s::'a. (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) \<le> 1"
proof (rule allI, rule ccontr)
  fix s::"'a"
  assume a1: "\<not> ((\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) \<le> 1)"
  then have f0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) > 1"
    by simp
  have "(\<Sum>\<^sub>\<infinity>s::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) = (\<Sum>\<^sub>\<infinity>s::'a\<in>{s}\<union>(-{s}). \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s))"
    by force
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) + (\<Sum>\<^sub>\<infinity>s::'a\<in>(-{s}). \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s))"
    apply (subst infsum_Un_disjoint)
    apply simp
    apply (rule summable_on_subset_banach[where A="UNIV"])
    by (simp_all add: rvfun_infsum_pcomp_summable assms(1) assms(2))
  also have "... > 1"
    by (smt (verit, del_insts) assms(1) assms(2) f0 infsum_nonneg mult_nonneg_nonneg rvfun_prob_sum1_summable(1))
  then show "False"
    using rvfun_infsum_pcomp_sum_1 assms(1) assms(2) calculation by fastforce
  qed

lemma rvfun_seqcomp_is_dist: 
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "is_final_distribution (pseqcomp_f p q)"
  apply (simp add: dist_defs expr_defs, auto)
  apply (simp add: assms(1) assms(2) infsum_nonneg rvfun_prob_sum1_summable(1))
  defer
  apply (simp_all add: lens_defs)
  apply (simp add: assms(1) assms(2) rvfun_infsum_pcomp_sum_1)
proof (rule ccontr)
  fix s\<^sub>1::"'a" and s::"'a"
  let ?f = "\<lambda>s. (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s))"
  assume a1: " \<not> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) \<le> (1::\<real>)"
  then have f0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) > 1"
    by force
  have f1: "(\<lambda>s::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) summable_on UNIV"
    apply (rule infsum_not_zero_summable[where x = 1])
    by (simp add: assms(1) assms(2) rvfun_infsum_pcomp_sum_1)+
  have f2: "(\<Sum>\<^sub>\<infinity>ss::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, ss)) = 
    (\<Sum>\<^sub>\<infinity>ss::'a\<in>{s} \<union> {ss. ss \<noteq> s}. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, ss))"
    by (metis (mono_tags, lifting) CollectI DiffD2 UNIV_I UnCI infsum_cong_neutral insert_iff)
  also have f3: "... = (\<Sum>\<^sub>\<infinity>ss::'a\<in>{s}. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, ss)) + 
    (\<Sum>\<^sub>\<infinity>ss::'a\<in>{ss. ss \<noteq> s}. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, ss))"
    apply (rule infsum_Un_disjoint)
    apply simp
    using f1 summable_on_subset_banach apply blast
    by simp
  also have f4: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) + 
    (\<Sum>\<^sub>\<infinity>ss::'a\<in>{ss. ss \<noteq> s}. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, ss))"
    by simp
  also have f5: "... > 1"
    by (smt (verit, del_insts) a1 assms(1) assms(2) infsum_nonneg mult_nonneg_nonneg 
          rvfun_prob_sum1_summable(1))
  have f6: "(\<Sum>\<^sub>\<infinity>ss::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, ss)) > 1"
    using calculation f5 by presburger
  show "False"
    using rvfun_infsum_pcomp_sum_1 f6 assms(1) assms(2) by fastforce
qed

lemma rvfun_seqcomp_inverse: 
  assumes "is_final_distribution p"
  assumes "is_prob q"
  shows "rvfun_of_prfun (prfun_of_rvfun (pseqcomp_f p q)) = pseqcomp_f p q"
  apply (subst rvfun_inverse)
  apply (simp add: assms rvfun_seqcomp_dist_is_prob)
  using assms(1) assms(2) rvfun_seqcomp_is_dist by blast

lemma rvfun_seqcomp_inverse_subdist: 
  assumes "is_final_sub_dist p"
  assumes "is_prob q"
  shows "rvfun_of_prfun (prfun_of_rvfun (pseqcomp_f p q)) = pseqcomp_f p q"
  apply (subst rvfun_inverse)
  apply (simp add: assms rvfun_seqcomp_subdist_is_prob)
  using assms(1) assms(2) rvfun_seqcomp_is_dist by blast

(*
lemma rvfun_seqcomp_inverse_summable: 
  assumes "((curry p) s\<^sub>1) summable_on UNIV"
  assumes "is_prob p" "is_prob q"
  shows "rvfun_of_prfun (prfun_of_rvfun (pseqcomp_f p q)) = pseqcomp_f p q"
  apply (subst rvfun_inverse)
  apply (simp add: assms rvfun_seqcomp_is_prob)
  using assms(1) assms(2) rvfun_is_dist_pcomp by blast
*)

lemma prfun_zero_right: "P ; \<^bold>0 = \<^bold>0"
  apply (simp add: pfun_defs ureal_zero)
  apply (simp add: ureal_defs)
  by (simp add: SEXP_def ereal2ureal_def subst_app_expr_def zero_ureal_def)

lemma prfun_zero_right': "P ; 0\<^sub>p = 0\<^sub>p"
  by (simp add: prfun_zero_right pzero_def)

lemma prfun_zero_left: "\<^bold>0 ; P = \<^bold>0"
  apply (simp add: pfun_defs ureal_zero)
  apply (simp add: ureal_defs)
  by (simp add: SEXP_def ereal2ureal_def subst_app_expr_def zero_ureal_def)

lemma prfun_zero_left': "0\<^sub>p ; P = 0\<^sub>p"
  by (simp add: prfun_zero_left pzero_def)

print_classes
lemma prfun_pseqcomp_mono: 
  fixes P\<^sub>1 :: "'s prhfun"
  assumes "\<forall>a b. (\<lambda>v\<^sub>0::'s. real_of_ereal 
    (ureal2ereal (P\<^sub>1 (a, v\<^sub>0))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (v\<^sub>0, b)))) summable_on UNIV"
  assumes "\<forall>a b. (\<lambda>v\<^sub>0::'s. real_of_ereal 
    (ureal2ereal (P\<^sub>2 (a, v\<^sub>0))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (v\<^sub>0, b)))) summable_on UNIV"
  shows "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2; Q\<^sub>1 \<le> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (P\<^sub>1 ; Q\<^sub>1) \<le> (P\<^sub>2 ; Q\<^sub>2)"
  apply (simp add: pfun_defs)
  apply (simp add: le_fun_def)
  apply (simp add: ureal_defs)
  apply (expr_auto)
proof -
  fix a b :: "'s"
  assume a1: "\<forall>(a::'s) b::'s. P\<^sub>1 (a, b) \<le> P\<^sub>2 (a, b)"
  assume a2: "\<forall>(a::'s) b::'s. Q\<^sub>1 (a, b) \<le> Q\<^sub>2 (a, b)"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'s.
                real_of_ereal (ureal2ereal (P\<^sub>1 (a, v\<^sub>0))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (v\<^sub>0, b))))"
  let ?rhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'s.
                real_of_ereal (ureal2ereal (P\<^sub>2 (a, v\<^sub>0))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (v\<^sub>0, b))))"

  have "?lhs \<le> ?rhs"
    apply (rule infsum_mono)
    apply (simp add: assms(1))
    apply (simp add: assms(2))
    by (metis a1 a2 atLeastAtMost_iff ereal_less_PInfty ereal_times(1) less_eq_ureal.rep_eq 
        linorder_not_less mult_mono real_of_ereal_pos real_of_ereal_positive_mono ureal2ereal)
  then show " ereal2ureal' (min (max (0::ereal) (ereal ?lhs)) (1::ereal)) \<le> 
       ereal2ureal' (min (max (0::ereal) (ereal ?rhs)) (1::ereal))"
    by (smt (z3) atLeastAtMost_iff ereal2ureal'_inverse ereal_less_eq(3) ereal_less_eq(4) 
        ereal_less_eq(7) ereal_max_0 less_eq_ureal.rep_eq linorder_le_cases max.absorb_iff2 
        min.absorb1 min.absorb2) 
qed

theorem prfun_seqcomp_left_unit: "II ; (P::'a prhfun) = P"
  apply (simp add: pseqcomp_def pskip_def)
  apply (simp add: rvfun_skip_inverse)
  apply (expr_auto)
  apply (simp add: infsum_mult_singleton_left_1)
  by (simp add: prfun_inverse)

theorem prfun_seqcomp_right_unit: "(P::'a prhfun) ; II = P"
  apply (simp add: pseqcomp_def pskip_def)
  apply (simp add: rvfun_skip_inverse)
  apply (expr_auto)
  apply (simp add: infsum_mult_singleton_right)
  by (simp add: prfun_inverse)

lemma prfun_passign_simp: "(x := e) = prfun_of_rvfun (\<lbrakk> \<lbrakk>x := e\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"
  by (simp add: pfun_defs expr_defs)

theorem prfun_passign_comp: 
  (* assumes "$x \<sharp> f" "x \<bowtie> y" *)
  shows "(x := e) ; (y := f) = prfun_of_rvfun (\<lbrakk> \<lbrakk>(x := e) \<Zcomp> (y := f)\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"
  apply (simp add: pseqcomp_def passigns_def)
  apply (simp add: rvfun_assignment_inverse)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (rel_auto)
  apply (subst infsum_mult_singleton_left_1)
  apply simp
  by (smt (verit, best) infsum_0 mult_cancel_left1 mult_cancel_right1)

lemma prfun_prob_choice_is_sum_1:
  assumes "0 \<le> r \<and> r \<le> 1"
  assumes "is_final_distribution (rvfun_of_prfun (P::'a prhfun))"
  assumes "is_final_distribution (rvfun_of_prfun Q)"
  shows "(\<Sum>\<^sub>\<infinity>s::'a. r * rvfun_of_prfun P (s\<^sub>1, s) + ((1::\<real>) - r ) * rvfun_of_prfun Q (s\<^sub>1, s)) = (1::\<real>)"
proof -
  have f1: "(\<Sum>\<^sub>\<infinity>s::'a. r  * rvfun_of_prfun P (s\<^sub>1, s) + ((1::\<real>) - r ) * rvfun_of_prfun Q (s\<^sub>1, s)) = 
    (\<Sum>\<^sub>\<infinity>s::'a. r * rvfun_of_prfun P (s\<^sub>1, s)) + (\<Sum>\<^sub>\<infinity>s::'a. ((1::\<real>) - r ) * rvfun_of_prfun Q (s\<^sub>1, s))"
    apply (rule infsum_add)
    apply (simp add: assms(2) rvfun_prob_sum1_summable(3) summable_on_cmult_right)
    by (simp add: assms(3) rvfun_prob_sum1_summable(3) summable_on_cmult_right)
  also have f2: "... = r * (\<Sum>\<^sub>\<infinity>s::'a. rvfun_of_prfun P (s\<^sub>1, s)) + 
          (1 - r) * (\<Sum>\<^sub>\<infinity>s::'a. rvfun_of_prfun Q (s\<^sub>1, s))"
    apply (subst infsum_cmult_right)
    apply (simp add: assms(2) rvfun_prob_sum1_summable(3) summable_on_cmult_right)
    apply (subst infsum_cmult_right)
    apply (simp add: assms(3) rvfun_prob_sum1_summable(3) summable_on_cmult_right)
    by simp
  show ?thesis
    apply (simp add: f1 f2)
    by (simp add: assms rvfun_prob_sum1_summable(2))
qed

lemma prfun_prob_choice_is_sum_1':
  assumes "0 \<le> r \<and> r \<le> 1"
  assumes "is_final_distribution (p)"
  assumes "is_final_distribution (q)"
  shows "(\<Sum>\<^sub>\<infinity>s::'a. r * p (s\<^sub>1, s) + ((1::\<real>) - r ) * q (s\<^sub>1, s)) = (1::\<real>)"
proof -
  have f1: "(\<Sum>\<^sub>\<infinity>s::'a. r  * p (s\<^sub>1, s) + ((1::\<real>) - r ) * q (s\<^sub>1, s)) = 
    (\<Sum>\<^sub>\<infinity>s::'a. r * p (s\<^sub>1, s)) + (\<Sum>\<^sub>\<infinity>s::'a. ((1::\<real>) - r ) * q (s\<^sub>1, s))"
    apply (rule infsum_add)
    apply (simp add: assms(2) rvfun_prob_sum1_summable(3) summable_on_cmult_right)
    by (simp add: assms(3) rvfun_prob_sum1_summable(3) summable_on_cmult_right)
  also have f2: "... = r * (\<Sum>\<^sub>\<infinity>s::'a. p (s\<^sub>1, s)) + 
          (1 - r) * (\<Sum>\<^sub>\<infinity>s::'a. q (s\<^sub>1, s))"
    apply (subst infsum_cmult_right)
    apply (simp add: assms(2) rvfun_prob_sum1_summable(3) summable_on_cmult_right)
    apply (subst infsum_cmult_right)
    apply (simp add: assms(3) rvfun_prob_sum1_summable(3) summable_on_cmult_right)
    by simp
  show ?thesis
    apply (simp add: f1 f2)
    by (simp add: assms rvfun_prob_sum1_summable(2))
qed

theorem prfun_seqcomp_left_one_point: "x := e ; P = prfun_of_rvfun (([ x\<^sup>< \<leadsto> e\<^sup>< ] \<dagger> @(rvfun_of_prfun P)))\<^sub>e"
  apply (simp add: pfun_defs expr_defs)
  apply (subst rvfun_inverse)
  apply (simp add: dist_defs expr_defs)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (rel_auto)
  by (simp add: infsum_mult_singleton_left_1)

lemma prfun_infsum_over_pair_subset_1:
  assumes "is_final_distribution (rvfun_of_prfun (P::'a prhfun))"
  shows "(\<Sum>\<^sub>\<infinity> (s::'a, v\<^sub>0::'a). rvfun_of_prfun P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) = 1"
proof -
  have f1: "(\<Sum>\<^sub>\<infinity> (s::'a, v\<^sub>0::'a). rvfun_of_prfun P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) = 
        (\<Sum>\<^sub>\<infinity> (s::'a, v\<^sub>0::'a) \<in> {(s::'a, v\<^sub>0::'a) | s v\<^sub>0. put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s}. rvfun_of_prfun P (s\<^sub>1, v\<^sub>0))"
    apply (rule infsum_cong_neutral)
    apply force
    using DiffD2 prod.collapse apply fastforce
    by force
  have f2: "(\<Sum>\<^sub>\<infinity> (s::'a, v\<^sub>0::'a) \<in> {(s::'a, v\<^sub>0::'a) | s v\<^sub>0. put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s}. rvfun_of_prfun P (s\<^sub>1, v\<^sub>0)) = 1"
    apply (subst prfun_infsum_over_pair_fst_discard)
    apply (simp add: assms)
    by (simp add: assms rvfun_prob_sum1_summable(2))
  show ?thesis
    using f1 f2 by presburger
qed

lemma prfun_infsum_swap:
  assumes "is_final_distribution (rvfun_of_prfun (P::'a prhfun))"
  shows "(\<Sum>\<^sub>\<infinity>s::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. rvfun_of_prfun P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) = 
  (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. \<Sum>\<^sub>\<infinity>s::'a. rvfun_of_prfun P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>)))"
  apply (rule infsum_swap_banach)
  apply (simp add: summable_on_def)
  apply (rule_tac x = "1" in exI)
  by (smt (verit, best) assms has_sum_infsum infsum_cong infsum_not_exists prfun_infsum_over_pair_subset_1 split_cong)

lemma prfun_infsum_infsum_subset_1:
  assumes "is_final_distribution (rvfun_of_prfun (P::'a prhfun))"
  shows "(\<Sum>\<^sub>\<infinity>s::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. rvfun_of_prfun P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) =
       (1::\<real>)"
  apply (simp add: assms prfun_infsum_swap)
proof -
  have f0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (\<Sum>\<^sub>\<infinity>s::'a. rvfun_of_prfun P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>)))) 
    = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (rvfun_of_prfun P (s\<^sub>1, v\<^sub>0) * (\<Sum>\<^sub>\<infinity>s::'a. (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>)))))"
    apply (subst infsum_cmult_right)
    apply (simp add: infsum_singleton_summable)
    by (simp)
  then have f1: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (rvfun_of_prfun P (s\<^sub>1, v\<^sub>0) * 1))"
    by (simp add: infsum_singleton)
  then show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. \<Sum>\<^sub>\<infinity>s::'a. rvfun_of_prfun P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) = (1::\<real>)"
    using f0 assms rvfun_prob_sum1_summable(2) by force
qed 

theorem prel_seqcomp_assoc: 
  assumes "is_final_distribution (rvfun_of_prfun P)"
          "is_final_distribution (rvfun_of_prfun Q)"
          "is_final_distribution (rvfun_of_prfun R)"
  shows "(P::'a prhfun) ; (Q ; R) = (P ; Q) ; R"
  apply (simp add: pfun_defs)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (subst rvfun_inverse)
   apply (expr_auto add: dist_defs)
  apply (simp add: infsum_nonneg is_prob ureal_is_prob)
   apply (subst rvfun_infsum_pcomp_lessthan_1)
  apply (simp add: assms)+
  apply (subst rvfun_inverse)
  using assms(1) rvfun_seqcomp_dist_is_prob ureal_is_prob apply blast
  apply (expr_auto)
proof -
  fix a and b :: "'a"
  let ?q = "\<lambda>(v\<^sub>0, b). (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a. rvfun_of_prfun Q (v\<^sub>0, v\<^sub>0') * rvfun_of_prfun R (v\<^sub>0', b))"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. rvfun_of_prfun P (a, v\<^sub>0) *
          (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a. rvfun_of_prfun Q (v\<^sub>0, v\<^sub>0') * rvfun_of_prfun R (v\<^sub>0', b)))"
  let ?lhs' = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a.(\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a.  
      rvfun_of_prfun P (a, v\<^sub>0) * rvfun_of_prfun Q (v\<^sub>0, v\<^sub>0') * rvfun_of_prfun R (v\<^sub>0', b)))"
  let ?rhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a.
          (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a. rvfun_of_prfun P (a, v\<^sub>0') * rvfun_of_prfun Q (v\<^sub>0', v\<^sub>0)) 
          * rvfun_of_prfun R (v\<^sub>0, b))"
  let ?rhs' = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a. 
          rvfun_of_prfun P (a, v\<^sub>0') * rvfun_of_prfun Q (v\<^sub>0', v\<^sub>0) * rvfun_of_prfun R (v\<^sub>0, b)))"

  have lhs_1: "(\<forall>v\<^sub>0::'a. rvfun_of_prfun P (a, v\<^sub>0) *
          (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a. rvfun_of_prfun Q (v\<^sub>0, v\<^sub>0') * rvfun_of_prfun R (v\<^sub>0', b))
      = (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a. 
          rvfun_of_prfun P (a, v\<^sub>0) * rvfun_of_prfun Q (v\<^sub>0, v\<^sub>0') * rvfun_of_prfun R (v\<^sub>0', b)))"
    apply (rule allI)
    by (metis (no_types, lifting) ab_semigroup_mult_class.mult_ac(1) infsum_cmult_right' infsum_cong)
  then have lhs_eq: "?lhs = ?lhs'"
    by presburger

  have rhs_1: "(\<forall>v\<^sub>0::'a. (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a. rvfun_of_prfun P (a, v\<^sub>0') * rvfun_of_prfun Q (v\<^sub>0', v\<^sub>0)) 
          * rvfun_of_prfun R (v\<^sub>0, b)
      = (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a. 
          rvfun_of_prfun P (a, v\<^sub>0') * rvfun_of_prfun Q (v\<^sub>0', v\<^sub>0) * rvfun_of_prfun R (v\<^sub>0, b)))"
    apply (rule allI)
    by (metis (mono_tags, lifting) infsum_cmult_left' infsum_cong)
  then have rhs_eq: "?rhs = ?rhs'"
    by presburger

  have lhs_rhs_eq: "?lhs' = ?rhs'"
    apply (rule infsum_swap_banach)
    apply (subst summable_on_iff_abs_summable_on_real)
    apply (subst abs_summable_on_Sigma_iff)
    apply (rule conjI)
    apply (auto)
    apply (subst abs_of_nonneg)
    apply (simp add: is_prob ureal_is_prob)
    apply (subst mult.assoc)
    apply (rule summable_on_cmult_right)
    apply (rule rvfun_product_summable')
    apply (simp add: assms)+
    apply (subst abs_of_nonneg)
    apply (subst abs_of_nonneg)
    apply (simp add: is_prob ureal_is_prob)
    apply (simp add: assms(1) assms(2) assms(3) infsum_nonneg rvfun_prob_sum1_summable(1))
    apply (subst abs_of_nonneg)
    apply (simp add: is_prob ureal_is_prob)
    apply (subst mult.assoc)
    apply (subst infsum_cmult_right)
    apply (rule rvfun_product_summable')
    apply (simp add: assms)+
    apply (subst summable_on_iff_abs_summable_on_real)
    apply (rule abs_summable_on_comparison_test[where g = "\<lambda>s::'a. rvfun_of_prfun P (a, s)"])
    using assms(1) summable_on_iff_abs_summable_on_real apply (metis pdrfun_prob_sum1_summable'(4))
    apply (subgoal_tac "(\<Sum>\<^sub>\<infinity>y::'a. rvfun_of_prfun Q (x, y) * rvfun_of_prfun R (y, b)) \<le> 1")
    using infsum_nonneg mult_right_le_one_le prfun_in_0_1'
    apply (smt (verit, ccfv_SIG) mult_nonneg_nonneg real_norm_def)
    apply (subst rvfun_infsum_pcomp_lessthan_1)
    by (simp add: assms)+

  then show "?lhs = ?rhs"
    using lhs_eq rhs_eq by presburger
qed

term "((P::'a \<times> 'a \<Rightarrow> ureal) ; \<lbrakk>b\<^sup>\<Up>\<rbrakk>\<^sub>\<I>)"
(*
P ; if b then Q else R
= \<Sum> vv. P[vv/v'] * (if b then Q else R)[vv/v]
= \<Sum> vv. P[vv/v'] * (\<lbrakk>b\<rbrakk>*Q + \<lbrakk>\<not>b\<rbrakk>*R)[vv/v]
= \<Sum> vv. P[vv/v'] * (\<lbrakk>b\<rbrakk>*Q)[vv/v] + \<Sum> vv. P[vv/v'] * (\<lbrakk>\<not>b\<rbrakk>*R)[vv/v]
= \<Sum> vv. P[vv/v'] * (\<lbrakk>b\<rbrakk>*Q)[vv/v] + \<Sum> vv. P[vv/v'] * (\<lbrakk>\<not>b\<rbrakk>*R)[vv/v]

*)
theorem prfun_seqcomp_pcond_subdist:
  fixes Q R ::"'a prhfun"
  assumes "is_final_sub_dist (rvfun_of_prfun (P::'a prhfun))"
  shows "P ; (if\<^sub>c b\<^sup>\<Up> then Q else R) = prfun_of_rvfun (
        @(pseqcomp_f (rvfun_of_prfun P) (rvfun_of_prfun (\<lbrakk>b\<^sup>\<Up>\<rbrakk>\<^sub>\<I> * Q)\<^sub>e)) + 
        @(pseqcomp_f (rvfun_of_prfun P) (rvfun_of_prfun (\<lbrakk>\<not>((b)\<^sup>\<Up>)\<rbrakk>\<^sub>\<I>\<^sub>e * R)\<^sub>e)))\<^sub>e"
    apply (simp add: pchoice_def pseqcomp_def pcond_def)
    apply (subst rvfun_pcond_inverse)
    using ureal_is_prob apply blast+
    apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
    apply (subst fun_eq_iff)
    apply (rel_auto)
  proof -
    fix a ba
    let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. rvfun_of_prfun P (a, v\<^sub>0) * (if b v\<^sub>0 then rvfun_of_prfun Q (v\<^sub>0, snd (a, ba)) else rvfun_of_prfun R (v\<^sub>0, snd (a, ba))))"
    let ?rhs_1 = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a.
          rvfun_of_prfun P (a, v\<^sub>0) * rvfun_of_prfun (\<lambda>\<s>::'a \<times> 'a. ereal2ureal (ereal (if b (fst \<s>) then 1::\<real> else (0::\<real>))) * Q \<s>) (v\<^sub>0, ba))"
    let ?rhs_2 = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a.
          rvfun_of_prfun P (a, v\<^sub>0) * rvfun_of_prfun (\<lambda>\<s>::'a \<times> 'a. ereal2ureal (ereal (if \<not> b (fst \<s>) then 1::\<real> else (0::\<real>))) * R \<s>) (v\<^sub>0, ba))"
    have f1: "\<forall>v\<^sub>0. rvfun_of_prfun (\<lambda>\<s>::'a \<times> 'a. ereal2ureal (ereal (if b (fst \<s>) then 1::\<real> else (0::\<real>))) * Q \<s>) (v\<^sub>0, ba)
      = (if b v\<^sub>0 then rvfun_of_prfun Q (v\<^sub>0, ba) else 0)"
      by (smt (verit) SEXP_def fst_conv lambda_one lambda_zero o_def one_ereal_def one_ureal_def 
          real_of_ereal_0 rvfun_of_prfun_def ureal2real_def zero_ereal_def zero_ureal.rep_eq zero_ureal_def)
    have f2: "\<forall>v\<^sub>0. rvfun_of_prfun (\<lambda>\<s>::'a \<times> 'a. ereal2ureal (ereal (if \<not> b (fst \<s>) then 1::\<real> else (0::\<real>))) * R \<s>) (v\<^sub>0, ba)
      = (if b v\<^sub>0 then 0 else rvfun_of_prfun R (v\<^sub>0, ba))"
      by (smt (verit, best) SEXP_def fst_conv lambda_one lambda_zero o_def one_ereal_def one_ureal_def real_of_ereal_0 rvfun_of_prfun_def ureal2real_def zero_ereal_def zero_ureal.rep_eq zero_ureal_def)
    have f3: "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. 
        (rvfun_of_prfun P (a, v\<^sub>0) * rvfun_of_prfun (\<lambda>\<s>::'a \<times> 'a. ereal2ureal (ereal (if b (fst \<s>) then 1::\<real> else (0::\<real>))) * Q \<s>) (v\<^sub>0, ba)) + 
        (rvfun_of_prfun P (a, v\<^sub>0) * rvfun_of_prfun (\<lambda>\<s>::'a \<times> 'a. ereal2ureal (ereal (if \<not> b (fst \<s>) then 1::\<real> else (0::\<real>))) * R \<s>) (v\<^sub>0, ba)))"
      apply (subst infsum_cong[where g = "\<lambda>v\<^sub>0. (rvfun_of_prfun P (a, v\<^sub>0) * rvfun_of_prfun (\<lambda>\<s>::'a \<times> 'a. ereal2ureal (ereal (if b (fst \<s>) then 1::\<real> else (0::\<real>))) * Q \<s>) (v\<^sub>0, ba)) + 
        (rvfun_of_prfun P (a, v\<^sub>0) * rvfun_of_prfun (\<lambda>\<s>::'a \<times> 'a. ereal2ureal (ereal (if \<not> b (fst \<s>) then 1::\<real> else (0::\<real>))) * R \<s>) (v\<^sub>0, ba))"])
       apply (simp add: f1 f2)
      by simp
    show "?lhs = ?rhs_1 + ?rhs_2"
      apply (simp add: f3)
      apply (subst infsum_add)
      apply (subst rvfun_product_summable)
      using assms apply force
      using ureal_is_prob apply blast
      apply simp
      apply (subst rvfun_product_summable)
      using assms apply force
      using ureal_is_prob apply blast
       apply simp
      by simp
  qed

subsubsection \<open> Normalisation \<close>
theorem rvfun_uniform_dist_empty_zero:  "(x \<^bold>\<U> {}) = rvfun_of_prfun \<^bold>0"
  apply (simp add: dist_defs ureal_defs)
  apply (expr_auto)
  by (simp add: ureal_zero_0)

lemma rvfun_uniform_dist_is_prob:
  assumes "finite (A::'a set)"
  assumes "vwb_lens x"
  shows "is_prob ((x \<^bold>\<U> A))"
proof (cases "A = {}")
  case True
  show ?thesis 
    apply (simp add: True)
    apply (simp add: rvfun_uniform_dist_empty_zero)
    by (simp add: ureal_is_prob)
next
  case False
  then show ?thesis 
    apply (simp add: dist_defs)
    apply (expr_auto)
    apply (simp add: infsum_nonneg)
    apply (rel_auto)
  proof -
    fix a xa
    have "{s::'a. \<exists>xb::'a\<in>A. put\<^bsub>x\<^esub> a xb = put\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> a xa) s} = 
        {s::'a. \<exists>xb::'a\<in>A. put\<^bsub>x\<^esub> a xb = put\<^bsub>x\<^esub> a s}"
    using assms(2) by auto
    also have "... = {s::'a. \<exists>xb::'a\<in>A. xb = s}"
      by (metis assms(2) vwb_lens_wb wb_lens_weak weak_lens.view_determination)
    then have "(1::\<real>) * real (card {s::'a. \<exists>xb::'a\<in>A. put\<^bsub>x\<^esub> a xb = put\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> a xa) s}) = real (card A)"
      by (simp add: calculation)
    then have "(\<Sum>\<^sub>\<infinity>v::'a. if \<exists>xb::'a\<in>A. put\<^bsub>x\<^esub> a xb = put\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> a xa) v then 1::\<real> else (0::\<real>)) \<ge> 1"
      apply (subst infsum_constant_finite_states)
      apply (smt (verit, best) Collect_mem_eq Collect_mono_iff assms(1) assms(2) mem_Collect_eq 
            mwb_lens_weak rev_finite_subset vwb_lens.axioms(2) weak_lens.put_get)
      by (smt (verit, best) False assms(1) card_eq_0_iff lambda_one le_square mult.right_neutral 
          mult_cancel_left1 mult_le_mono2 of_nat_1 of_nat_eq_0_iff of_nat_le_iff of_nat_mult rev_finite_subset someI_ex)
    then show "(1::\<real>) /  (\<Sum>\<^sub>\<infinity>v::'a. if \<exists>xb::'a\<in>A. put\<^bsub>x\<^esub> a xb = put\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> a xa) v then 1::\<real> else (0::\<real>))
         \<le> (1::\<real>)"
      by force
  qed
qed

lemma rvfun_normalisation_is_dist:
  assumes "\<forall>s. p s \<ge> 0"
  assumes "\<forall>s. \<exists>s'. p (s, s') > 0"
  assumes "\<forall>s. (\<lambda>v\<^sub>0. p (s, v\<^sub>0)) summable_on UNIV"
  shows "is_final_distribution (\<^bold>N p)"
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: assms infsum_nonneg)
  apply (smt (verit, best) UNIV_I assms(1) divide_le_eq_1 infsum_geq_element infsum_not_zero_summable)
proof -
  fix s\<^sub>1::"'a"
  have f1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. p (s\<^sub>1, v\<^sub>0)) \<ge> p (s\<^sub>1, (SOME s'. p (s\<^sub>1, s') > 0))"
    apply (rule infsum_geq_element)
    using assms(1) apply blast
    using assms(3) apply simp
    by auto
  have f2: "... > 0"
    by (smt (verit, best) assms(2) f1 someI_ex)
  have f3: "(\<Sum>\<^sub>\<infinity>s::'b. p (s\<^sub>1, s) / (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. p (s\<^sub>1, v\<^sub>0))) = 
        (\<Sum>\<^sub>\<infinity>s::'b. (p (s\<^sub>1, s) * (1 / (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. p (s\<^sub>1, v\<^sub>0)))))"
    by auto
  also have f4: "... = (\<Sum>\<^sub>\<infinity>s::'b. p (s\<^sub>1, s)) * (1 / (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. p (s\<^sub>1, v\<^sub>0)))"
    by (metis infsum_cmult_left')
  also have f5: "... = 1"
    using f2 by auto
  thus "(\<Sum>\<^sub>\<infinity>s::'b. p (s\<^sub>1, s) / (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. p (s\<^sub>1, v\<^sub>0))) = (1::\<real>)"
    using calculation by presburger
qed

text \<open> The possible values of @{text "x"} are chosen from a set @{text "A"} and they are equally 
likely to be observed in a program constructed by @{text "uniform_dist x A"} }.
\<close>
lemma rvfun_uniform_dist_is_dist:
  assumes "finite (A::'b set)"
  assumes "vwb_lens x"
  assumes "A \<noteq> {}"
  shows "is_final_distribution ((x \<^bold>\<U> A))"
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: infsum_nonneg)
  apply (smt (verit) divide_le_eq_1 infsum_0 infsum_geq_element infsum_not_exists)
  apply (rel_auto)
proof -
  fix s\<^sub>1::"'a"
  let ?f = "\<lambda>s. (if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = s then 1::\<real> else (0::\<real>)) /
          (\<Sum>\<^sub>\<infinity>v::'b. if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> s v then 1::\<real> else (0::\<real>))"
  have one_dvd_card_A: "\<forall>s. ((\<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = s) \<longrightarrow> 
      (((1::\<real>) / (card {v. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> s v})) = ((1::\<real>) / (card A))))"
    apply (auto)
    apply (simp add: assms(2))
    apply (subgoal_tac "{v::'b. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> s\<^sub>1 v} = A")
    apply (simp)
    apply (subst set_eq_iff)
    apply (auto)
  proof (rule ccontr)
    fix xa::"'b" and xb::"'b" and  xaa::"'b"
    assume a1: "xa \<in> A"
    assume a2: "xaa \<in> A"
    assume a3: "put\<^bsub>x\<^esub> s\<^sub>1 xaa = put\<^bsub>x\<^esub> s\<^sub>1 xb"
    assume a4: "\<not> xb \<in> A"
    from a2 a4 have "xaa \<noteq> xb"
      by auto
    then have "put\<^bsub>x\<^esub> s\<^sub>1 xaa \<noteq> put\<^bsub>x\<^esub> s\<^sub>1 xb"
      using assms(2) by (meson vwb_lens_wb wb_lens_weak weak_lens.view_determination)
    thus "False"
      using a3 by blast
  qed

  have "finite {put\<^bsub>x\<^esub> s\<^sub>1 xa | xa. xa \<in> A}"
    apply (rule finite_image_set)
    using assms(1) by auto
  then have finite_states: "finite {s. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = s}"
    by (smt (verit, del_insts) Collect_cong)
  
  have "inj_on (\<lambda>xa. put\<^bsub>x\<^esub> s\<^sub>1 xa) A"
    by (meson assms(2) inj_onI vwb_lens_wb wb_lens_def weak_lens.view_determination)
  then have card_A: "card ((\<lambda>xa. put\<^bsub>x\<^esub> s\<^sub>1 xa) ` A ) = card A"
    using card_image by blast
  have set_as_f_image: "{s. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = s} = ((\<lambda>xa. put\<^bsub>x\<^esub> s\<^sub>1 xa) ` A )"
    by blast
  have "(\<Sum>\<^sub>\<infinity>s::'a. ?f s) = (\<Sum>\<^sub>\<infinity>s::'a. (if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = s then 1::\<real> else (0::\<real>)) 
      / (card {v. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> s v}))"
    apply (subst infsum_constant_finite_states)
    apply (subst finite_Collect_bex)
    apply (simp add: assms(1))
    apply (auto)
    apply (subgoal_tac "\<forall>xa. (put\<^bsub>x\<^esub> s\<^sub>1 y = put\<^bsub>x\<^esub> s xa) \<longrightarrow> y = xa")
    apply (smt (verit, ccfv_SIG) assms(1) mem_Collect_eq rev_finite_subset subset_iff)
    using weak_lens.view_determination vwb_lens_wb wb_lens_weak assms(2) by metis
  also have "... = (\<Sum>\<^sub>\<infinity>s::'a. (if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = s then 
                ((1::\<real>) / (card {v. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> s v}))
              else (0::\<real>)))"
    apply (rule infsum_cong)
    by simp
  also have "... = (\<Sum>\<^sub>\<infinity>s::'a. (if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = s then 
                ((1::\<real>) / (card A)) else (0::\<real>)))"
    apply (rule infsum_cong)
    using one_dvd_card_A by presburger
  also have "... = ((1::\<real>) / (card A)) * (card {s. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = s})"
    apply (rule infsum_constant_finite_states)
    using finite_states by blast
  also have "... = ((1::\<real>) / (card A)) * (card A)"
    using card_A set_as_f_image by presburger
  also have "... = 1"
    by (simp add: assms(1) assms(3))
  then show "(\<Sum>\<^sub>\<infinity>s::'a.
          (if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = s then 1::\<real> else (0::\<real>)) /
          (\<Sum>\<^sub>\<infinity>v::'b. if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> s v then 1::\<real> else (0::\<real>))) =
       (1::\<real>)"
    using calculation by presburger
qed

lemma rvfun_uniform_dist_empty_is_zero:
  assumes "vwb_lens x"
  shows "\<forall>v. ((x \<^bold>\<U> {}) ; (\<lbrakk>$x\<^sup>< = \<guillemotleft>v\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e)) = rvfun_of_prfun 0\<^sub>p"
  apply (auto, simp add: rvfun_uniform_dist_empty_zero)
  apply (simp add: pfun_defs ureal_defs)
  apply (expr_auto)
  by (simp add: ureal_zero_0)

lemma rvfun_uniform_dist_is_uniform:
  assumes "finite (A::'b set)"
  assumes "vwb_lens x"
  assumes "A \<noteq> {}"
  shows "\<forall>v \<in> A. ((x \<^bold>\<U> A) ; (\<lbrakk>$x\<^sup>< = \<guillemotleft>v\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e) = (1/card \<guillemotleft>A\<guillemotright>)\<^sub>e)"
  apply (simp add: dist_defs pfun_defs)
  apply (expr_auto)
  apply (rel_auto)
proof -
  fix v::"'b" and s\<^sub>1::"'a"
  assume a1: "v \<in> A"
  let ?f1 = "\<lambda>v\<^sub>0. (if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = v\<^sub>0 then 1::\<real> else (0::\<real>))"
  let ?f2 = "\<lambda>v\<^sub>0. (if get\<^bsub>x\<^esub> v\<^sub>0 = v then 1::\<real> else (0::\<real>))"
  let ?f = "\<lambda>v\<^sub>0. (if (\<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = v\<^sub>0) \<and> (get\<^bsub>x\<^esub> v\<^sub>0 = v) then 1::\<real> else (0::\<real>))"
  let ?sum = "\<lambda>v\<^sub>0. (\<Sum>\<^sub>\<infinity>v::'b. if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> v\<^sub>0 v then 1::\<real> else (0::\<real>))"

  have one_dvd_card_A: "\<forall>s. ((\<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = s) \<longrightarrow> 
      (((1::\<real>) / (card {v. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> s v})) = ((1::\<real>) / (card A))))"
    apply (auto)
    apply (simp add: assms(2))
    apply (subgoal_tac "{v::'b. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> s\<^sub>1 v} = A")
    apply (simp)
    apply (subst set_eq_iff)
    apply (auto)
  proof (rule ccontr)
    fix xa::"'b" and xb::"'b" and  xaa::"'b"
    assume a1: "xa \<in> A"
    assume a2: "xaa \<in> A"
    assume a3: "put\<^bsub>x\<^esub> s\<^sub>1 xaa = put\<^bsub>x\<^esub> s\<^sub>1 xb"
    assume a4: "\<not> xb \<in> A"
    from a2 a4 have "xaa \<noteq> xb"
      by auto
    then have "put\<^bsub>x\<^esub> s\<^sub>1 xaa \<noteq> put\<^bsub>x\<^esub> s\<^sub>1 xb"
      using assms(2) by (meson vwb_lens_wb wb_lens_weak weak_lens.view_determination)
    thus "False"
      using a3 by blast
  qed

  have "finite {put\<^bsub>x\<^esub> s\<^sub>1 xa | xa. xa \<in> A}"
    apply (rule finite_image_set)
    using assms(1) by auto
  then have "finite {v\<^sub>0. (\<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = v\<^sub>0)}"
    by (smt (verit, del_insts) Collect_cong)
  then have finite_states: "finite {v\<^sub>0. (\<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = v\<^sub>0) \<and> (get\<^bsub>x\<^esub> v\<^sub>0 = v)}"
    apply (rule rev_finite_subset[where B = "{v\<^sub>0. (\<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = v\<^sub>0)}"])
    by auto

  have card_singleton: "card {v\<^sub>0. (\<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = v\<^sub>0) \<and> (get\<^bsub>x\<^esub> v\<^sub>0 = v)} = Suc (0)"
    apply (simp add: card_1_singleton_iff)
    apply (rule_tac x = "put\<^bsub>x\<^esub> s\<^sub>1 v" in exI)
    using a1 assms(2) by auto

  have "\<forall>v\<^sub>0. ?f1 v\<^sub>0 * ?f2 v\<^sub>0 = ?f v\<^sub>0"
    by (auto)
  then have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. ?f1 v\<^sub>0 * ?f2 v\<^sub>0 / ?sum v\<^sub>0) = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. ?f0 v\<^sub>0 / ?sum v\<^sub>0)"
    by auto
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. ?f0 v\<^sub>0 / (card {v. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> v\<^sub>0 v}))"
    apply (subst infsum_constant_finite_states)
    apply (subst finite_Collect_bex)
    apply (simp add: assms(1))
    apply (auto)
    apply (subgoal_tac "\<forall>xa. (put\<^bsub>x\<^esub> s\<^sub>1 y = put\<^bsub>x\<^esub> v\<^sub>0 xa) \<longrightarrow> y = xa")
    apply (smt (verit, ccfv_SIG) assms(1) mem_Collect_eq rev_finite_subset subset_iff)
    using weak_lens.view_determination vwb_lens_wb wb_lens_weak assms(2) by metis
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if (\<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = v\<^sub>0) \<and> (get\<^bsub>x\<^esub> v\<^sub>0 = v) then 
                ((1::\<real>) / (card {v. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> v\<^sub>0 v}))
              else (0::\<real>)))"
    apply (rule infsum_cong)
    by simp
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if (\<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = v\<^sub>0) \<and> (get\<^bsub>x\<^esub> v\<^sub>0 = v) then 
                ((1::\<real>) / (card A)) else (0::\<real>)))"
    apply (rule infsum_cong)
    using one_dvd_card_A by presburger
  also have "... = ((1::\<real>) / (card A)) * (card {v\<^sub>0. (\<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = v\<^sub>0) \<and> (get\<^bsub>x\<^esub> v\<^sub>0 = v)})"
    apply (rule infsum_constant_finite_states)
    using finite_states by blast
  also have "... = ((1::\<real>) / (card A))"
    using card_singleton by simp
  then show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. ?f1 v\<^sub>0 * ?f2 v\<^sub>0 / ?sum v\<^sub>0) = (1::\<real>) / real (card A)"
    using calculation by presburger
  qed

lemma rvfun_uniform_dist_inverse:
  assumes "finite (A::'b set)"
  assumes "vwb_lens x"
  assumes "A \<noteq> {}"
  shows "rvfun_of_prfun (prfun_of_rvfun (x \<^bold>\<U> A)) = (x \<^bold>\<U> A)"
  apply (subst rvfun_inverse)
  apply (simp add: assms(1) assms(2) rvfun_uniform_dist_is_prob)
  by simp

theorem rvfun_uniform_dist_altdef:
  assumes "finite (A::'a set)"
  assumes "vwb_lens x"
  assumes "A \<noteq> {}"
  shows "(x \<^bold>\<U> A) = (\<lbrakk>\<lbrakk>\<Union> v \<in> A. x := \<guillemotleft>v\<guillemotright>\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e / card \<guillemotleft>A\<guillemotright>)\<^sub>e"
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (rel_auto)
  apply (subst infsum_constant_finite_states)
  apply (smt (verit, best) Collect_mem_eq Collect_mono_iff assms(1) assms(2) mem_Collect_eq 
      mwb_lens_weak rev_finite_subset vwb_lens.axioms(2) weak_lens.put_get)
proof -
  fix a::"'b" and xa::"'a"
  assume a1: "xa \<in> A"
  have "{s::'a. \<exists>xb::'a\<in>A. put\<^bsub>x\<^esub> a xb = put\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> a xa) s} = 
        {s::'a. \<exists>xb::'a\<in>A. put\<^bsub>x\<^esub> a xb = put\<^bsub>x\<^esub> a s}"
    using assms(2) by auto
  also have "... = {s::'a. \<exists>xb::'a\<in>A. xb = s}"
    by (metis assms(2) vwb_lens_wb wb_lens_weak weak_lens.view_determination)
  then show "(1::\<real>) * real (card {s::'a. \<exists>xb::'a\<in>A. put\<^bsub>x\<^esub> a xb = put\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> a xa) s}) = real (card A)"
    by (simp add: calculation)
qed

theorem prfun_uniform_dist_altdef':
  assumes "finite (A::'a set)"
  assumes "vwb_lens x"
  assumes "A \<noteq> {}"
  shows "rvfun_of_prfun (prfun_of_rvfun (x \<^bold>\<U> A)) = (\<lbrakk>\<lbrakk>\<Union> v \<in> A. x := \<guillemotleft>v\<guillemotright>\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e / card \<guillemotleft>A\<guillemotright>)\<^sub>e"
  by (metis assms(1) assms(2) assms(3) rvfun_uniform_dist_inverse rvfun_uniform_dist_altdef)

theorem prfun_uniform_dist_left:
  assumes "finite (A::'a set)"
  assumes "vwb_lens x"
  assumes "A \<noteq> {}"
  shows "(prfun_of_rvfun (x \<^bold>\<U> A)) ; P = 
    prfun_of_rvfun ((\<Sum>v \<in> \<guillemotleft>A\<guillemotright>. (([ x\<^sup>< \<leadsto> \<guillemotleft>v\<guillemotright> ] \<dagger> @(rvfun_of_prfun P)))) / card (\<guillemotleft>A\<guillemotright>))\<^sub>e"
  apply (simp add: pseqcomp_def)
  apply (subst prfun_uniform_dist_altdef')
  apply (simp_all add: assms)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (expr_auto)
  apply (rel_auto)
proof -
  fix a and b :: "'b"
  let ?fl_1 = "\<lambda>v\<^sub>0. (if \<exists>xa::'a\<in>A. put\<^bsub>x\<^esub> a xa = v\<^sub>0 then 1::\<real> else (0::\<real>))"
  let ?fl_2 = "\<lambda>v\<^sub>0. rvfun_of_prfun P (v\<^sub>0, b) / real (card A)"

  have "finite {put\<^bsub>x\<^esub> a xa | xa. xa \<in> A}"
    apply (rule finite_image_set)
    using assms(1) by auto
  then have finite_states: "finite {v\<^sub>0. \<exists>xa::'a\<in>A. put\<^bsub>x\<^esub> a xa = v\<^sub>0}"
    by (smt (verit, del_insts) Collect_cong)

  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?fl_1 v\<^sub>0 * rvfun_of_prfun P (v\<^sub>0, b) / real (card A))
    = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?fl_1 v\<^sub>0 * ?fl_2 v\<^sub>0)"
    by auto
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b \<in> {v\<^sub>0. \<exists>xa::'a\<in>A. put\<^bsub>x\<^esub> a xa = v\<^sub>0}. ?fl_2 v\<^sub>0)"
    apply (subst infsum_mult_subset_left)
    by simp
  also have "... = (\<Sum> v\<^sub>0::'b \<in> {v\<^sub>0. \<exists>xa::'a\<in>A. put\<^bsub>x\<^esub> a xa = v\<^sub>0}. ?fl_2 v\<^sub>0)"
    apply (rule infsum_finite)
    by (simp add: finite_states)
  also have fl: "... = (\<Sum> v\<^sub>0::'b \<in> {v\<^sub>0. \<exists>xa::'a\<in>A. put\<^bsub>x\<^esub> a xa = v\<^sub>0}. rvfun_of_prfun P (v\<^sub>0, b)) / real (card A)"
    by (metis (mono_tags, lifting) sum.cong sum_divide_distrib)

  have inj_on_A: "inj_on (\<lambda>xa. put\<^bsub>x\<^esub> a xa) A"
    by (meson assms(2) inj_onI vwb_lens_wb wb_lens_def weak_lens.view_determination)

  have frl: "(\<Sum> v\<^sub>0::'b \<in> {v\<^sub>0. \<exists>xa::'a\<in>A. put\<^bsub>x\<^esub> a xa = v\<^sub>0}. rvfun_of_prfun P (v\<^sub>0, b)) 
    = (\<Sum>v::'a\<in>A. rvfun_of_prfun P (put\<^bsub>x\<^esub> a v, b))"
    apply (rule sum.reindex_cong[where l = "(\<lambda>xa. put\<^bsub>x\<^esub> a xa)"])
    apply (simp add: inj_on_A)
     apply blast
    by simp

  show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?fl_1 v\<^sub>0 * rvfun_of_prfun P (v\<^sub>0, b) / real (card A)) = 
        (\<Sum>v::'a\<in>A. rvfun_of_prfun P (put\<^bsub>x\<^esub> a v, b)) / real (card A)"
    using calculation fl frl by presburger
qed

subsubsection \<open> Parallel composition \<close>
lemma rvfun_parallel_f_is_prob: 
  assumes "\<forall>s. p s * q s \<ge> 0"
  shows "is_prob (p \<parallel>\<^sub>f q)"
  apply (simp add: dist_defs)
  apply (expr_auto)
   apply (simp add: assms infsum_nonneg)
proof -
  fix a b
  show "p (a, b) * q (a, b) / (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. p (a, v\<^sub>0) * q (a, v\<^sub>0)) \<le> (1::\<real>)"
  proof (cases "(\<lambda>s'. p (a, s') * q (a, s')) summable_on UNIV")
    assume "(\<lambda>s'::'b. p (a, s') * q (a, s')) summable_on UNIV"
    then show "p (a, b) * q (a, b) / (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. p (a, v\<^sub>0) * q (a, v\<^sub>0)) \<le> (1::\<real>)"
      oops
  next
    assume "\<not> ((\<lambda>s'::'b. p (a, s') * q (a, s')) summable_on UNIV)"
    (* division_ring_divide_zero *)
    then show "p (a, b) * q (a, b) / (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. p (a, v\<^sub>0) * q (a, v\<^sub>0)) \<le> (1::\<real>)" 
      by (simp add: infsum_not_exists)
qed

lemma divide_eq: "\<lbrakk>p = q \<and> P = Q\<rbrakk> \<Longrightarrow> (p::\<real>) / P = q / Q"
  by simp

(*
lhs_pq=0    rhs_qr=0    pqr=0       result (lhs = rhs)
T           T           ?           eq
T           F           T           eq
T           F           F           !eq
F           T           T           eq
F           T           F           !eq
F           F           ?           eq

lhs_pq = 0: 
    not p * q summable_on
        or
    !s. p * q = 0
lhs_pq != 0: 
    p * q summable_on UNIV
        and
    not (!s. p * q = 0)
lhs_qr = 0: 
    not q * r summable_on
        or
    !s. q * r = 0
lhs_qr != 0: 
    q * r summable_on UNIV
        and
    not (!s. q * r = 0)
pqr != 0
    p * q * r summable_on UNIV
        and
    not (!s. p * q * r = 0)
*)
theorem rvfun_parallel_f_assoc:
  assumes 
    "\<forall>s. (\<Sum>\<^sub>\<infinity>v\<^sub>0. p (s, v\<^sub>0) * q (s, v\<^sub>0)) = 0 \<longrightarrow> 
         ((\<Sum>\<^sub>\<infinity>v\<^sub>0. q (s, v\<^sub>0) * r (s, v\<^sub>0)) = 0 \<or> (\<Sum>\<^sub>\<infinity>v\<^sub>0. p (s, v\<^sub>0) * q (s, v\<^sub>0) * r (s, v\<^sub>0)) = 0)"
    "\<forall>s. (\<Sum>\<^sub>\<infinity>v\<^sub>0. q (s, v\<^sub>0) * r (s, v\<^sub>0)) = 0 \<longrightarrow> 
         ((\<Sum>\<^sub>\<infinity>v\<^sub>0. p (s, v\<^sub>0) * q (s, v\<^sub>0)) = 0 \<or> (\<Sum>\<^sub>\<infinity>v\<^sub>0. p (s, v\<^sub>0) * q (s, v\<^sub>0) * r (s, v\<^sub>0)) = 0)"
  shows "(p \<parallel>\<^sub>f q) \<parallel>\<^sub>f r = p \<parallel>\<^sub>f (q \<parallel>\<^sub>f r)"
  apply (simp add: dist_defs)
  apply (simp add: fun_eq_iff)
  apply (rule allI)+
  apply (rule divide_eq)
  apply (expr_auto)
  apply (subst mult.assoc[symmetric])
proof -
  fix a::"'a"
  let ?lhs_pq = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. p (a, v\<^sub>0) * q (a, v\<^sub>0))"
  let ?rhs_qr = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. q (a, v\<^sub>0) * r (a, v\<^sub>0))"
  let ?pqr = "(\<lambda>v\<^sub>0. p (a, v\<^sub>0) * q (a, v\<^sub>0) * r (a, v\<^sub>0))"

  let ?lhs = "?lhs_pq * (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?pqr v\<^sub>0 / ?lhs_pq)"
  let ?rhs = "?rhs_qr * (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?pqr v\<^sub>0 / ?rhs_qr)"

  show "?lhs = ?rhs"
  (* 1: pq *)
  proof (cases "?lhs_pq = 0")
    case True
    assume T_pq: "?lhs_pq = 0"
    then have lhs_0: "?lhs = 0"
      using mult_eq_0_iff by blast
    then show ?thesis 
    (* 2: qr *)
    proof (cases "?rhs_qr = 0")
      case True
      assume T_qr: "?rhs_qr = 0"
      then have rhs_0: "?rhs = 0"
        using mult_eq_0_iff by blast
      then show ?thesis 
        using lhs_0 by presburger
    next
      case False
      assume F_qr: "\<not>?rhs_qr = 0"
      from T_pq F_qr assms(1) have "(\<Sum>\<^sub>\<infinity>v\<^sub>0. ?pqr v\<^sub>0) = 0"
        by blast
      then have F_qr_summable: 
        "((?pqr summable_on UNIV) \<and> has_sum ?pqr UNIV 0) \<or> \<not> ?pqr summable_on UNIV"
        apply (subst infset_0_not_summable_or_sum_to_zero)
        by simp+
      then show ?thesis 
      (* 3: pqr *)
      proof (cases "((?pqr summable_on UNIV) \<and> has_sum ?pqr UNIV 0)")
        case True
        then have "has_sum (\<lambda>v\<^sub>0::'b. ?pqr v\<^sub>0 / ?rhs_qr) UNIV (0 / ?rhs_qr)"
          using has_sum_cdiv_left by fastforce
        then have sum_rhs_pqr_0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?pqr v\<^sub>0 / ?rhs_qr) = 0"
          by (simp add: infsumI)
        have sum_lhs_pqr_0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?pqr v\<^sub>0 / ?lhs_pq) = 0"
          by (simp add: T_pq)
        then show ?thesis 
          using sum_rhs_pqr_0 by simp
      next
        case False
        then have F_qr_summable_F: "\<not> ?pqr summable_on UNIV"
          using F_qr_summable by blast
        (* have "\<not>(\<lambda>v\<^sub>0::'b. ?pqr v\<^sub>0 / ?lhs_pq) summable_on UNIV"
          apply (subst not_summable_on_cdiv_left') *)
        have "\<not>(\<lambda>v\<^sub>0::'b. ?pqr v\<^sub>0 / ?rhs_qr) summable_on UNIV"
          apply (subst not_summable_on_cdiv_left')
          by (simp add: F_qr F_qr_summable_F)+
        then have sum_rhs_pqr_0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?pqr v\<^sub>0 / ?rhs_qr) = 0"
          using infsum_not_zero_summable by blast
        then show ?thesis 
          by (simp add: lhs_0)
      qed
    qed
  next
    case False
    assume F_pq: "\<not>?lhs_pq = 0"
    then show ?thesis 
    (* 2: qr *)
    proof (cases "?rhs_qr = 0")
      case True
      assume T_qr: "?rhs_qr = 0"
      then have rhs_0: "?rhs = 0"
        using mult_eq_0_iff by blast
      from T_qr F_pq assms(2) have "(\<Sum>\<^sub>\<infinity>v\<^sub>0. ?pqr v\<^sub>0) = 0"
        by blast
      then have F_pq_summable: 
        "((?pqr summable_on UNIV) \<and> has_sum ?pqr UNIV 0) \<or> \<not> ?pqr summable_on UNIV"
        apply (subst infset_0_not_summable_or_sum_to_zero)
        by simp+
      then show ?thesis 
      (* 3: pqr *)
      proof (cases "((?pqr summable_on UNIV) \<and> has_sum ?pqr UNIV 0)")
        case True
        then have "has_sum (\<lambda>v\<^sub>0::'b. ?pqr v\<^sub>0 / ?lhs_pq) UNIV (0 / ?lhs_pq)"
          using has_sum_cdiv_left by fastforce
        then have sum_lhs_pqr_0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?pqr v\<^sub>0 / ?lhs_pq) = 0"
          by (simp add: infsumI)
        have sum_rhs_pqr_0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?pqr v\<^sub>0 / ?rhs_qr) = 0"
          by (simp add: T_qr)
        then show ?thesis 
          using sum_lhs_pqr_0 by simp
      next
        case False
        then have F_pq_summable_F: "\<not> ?pqr summable_on UNIV"
          using F_pq_summable by blast
        have "\<not>(\<lambda>v\<^sub>0::'b. ?pqr v\<^sub>0 / ?lhs_pq) summable_on UNIV"
          apply (subst not_summable_on_cdiv_left')
          by (simp add: F_pq F_pq_summable_F)+
        then have sum_lhs_pqr_0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?pqr v\<^sub>0 / ?lhs_pq) = 0"
          using infsum_not_zero_summable by blast
        then show ?thesis 
          by (simp add: rhs_0)
      qed
    next
      case False
      assume F_qr: "\<not>?rhs_qr = 0"
      show ?thesis
      (* 3: pqr *)
      proof (cases "?pqr summable_on UNIV")
        case True
        assume F_pqr: "?pqr summable_on UNIV"
        have F_lhs_pqr: "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?lhs_pq * ?pqr v\<^sub>0 / ?lhs_pq)"
          apply (subst infsum_cmult_right[symmetric])
          using F_pqr summable_on_cdiv_left' apply fastforce
          by simp
        have F_lhs_pqr': "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?pqr v\<^sub>0)"
          by (simp add: F_pq)
        have F_rhs_pqr: "?rhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?rhs_qr * ?pqr v\<^sub>0 / ?rhs_qr)"
          apply (subst infsum_cmult_right[symmetric])
          using F_pqr summable_on_cdiv_left' apply fastforce
          by simp
        have F_rhs_pqr': "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?pqr v\<^sub>0)"
          by (simp add: F_qr)
        show ?thesis 
          using F_lhs_pqr F_lhs_pqr' F_rhs_pqr F_rhs_pqr' by presburger
      next
        case False
        assume F_pqr: "\<not>?pqr summable_on UNIV"
        have F_lhs_pqr: "\<not>(\<lambda>v\<^sub>0::'b. ?pqr v\<^sub>0 / ?lhs_pq) summable_on UNIV"
          apply (subst not_summable_on_cdiv_left')
          by (simp add: F_pq F_pqr)+
        then have sum_lhs_pqr_0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?pqr v\<^sub>0 / ?lhs_pq) = 0"
          using infsum_not_zero_summable by blast
        have F_rhs_pqr: "\<not>(\<lambda>v\<^sub>0::'b. ?pqr v\<^sub>0 / ?rhs_qr) summable_on UNIV"
          apply (subst not_summable_on_cdiv_left')
          by (simp add: F_qr F_pqr)+
        then have sum_rhs_pqr_0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?pqr v\<^sub>0 / ?rhs_qr) = 0"
          using infsum_not_zero_summable by blast
        then show ?thesis
          by (simp add: sum_lhs_pqr_0)
      qed
    qed
  qed
qed

text \<open> A specific variant of associativity when @{text "p"}, @{text "q"}, and @{text "r"} all have 
non-negative real values. 
\<close>
theorem rvfun_parallel_f_assoc_nonneg:
  assumes "\<forall>s. p s \<ge> 0" "\<forall>s. q s \<ge> 0" "\<forall>s. r s \<ge> 0"
    "\<forall>s. (\<not> (\<lambda>v\<^sub>0. p (s, v\<^sub>0) * q (s, v\<^sub>0)) summable_on UNIV) \<longrightarrow> 
         ((\<forall>v\<^sub>0. q (s, v\<^sub>0) * r (s, v\<^sub>0) = 0) \<or> (\<not> (\<lambda>v\<^sub>0. q (s, v\<^sub>0) * r (s, v\<^sub>0)) summable_on UNIV))"
    "\<forall>s. (\<not> (\<lambda>v\<^sub>0. q (s, v\<^sub>0) * r (s, v\<^sub>0)) summable_on UNIV) \<longrightarrow> 
         ((\<forall>v\<^sub>0. p (s, v\<^sub>0) * q (s, v\<^sub>0) = 0) \<or> (\<not> (\<lambda>v\<^sub>0. p (s, v\<^sub>0) * q (s, v\<^sub>0)) summable_on UNIV))"
  shows "(p \<parallel>\<^sub>f q) \<parallel>\<^sub>f r = p \<parallel>\<^sub>f (q \<parallel>\<^sub>f r)"
  apply (rule rvfun_parallel_f_assoc)
  apply (auto)
proof -
  fix s
  let ?pq = "\<lambda>v\<^sub>0::'b. p (s, v\<^sub>0) * q (s, v\<^sub>0)"
  let ?qr = "\<lambda>v\<^sub>0::'b. q (s, v\<^sub>0) * r (s, v\<^sub>0)"
  let ?pqr = "\<lambda>v\<^sub>0::'b. p (s, v\<^sub>0) * q (s, v\<^sub>0) * r (s, v\<^sub>0)"

  assume a1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?pq v\<^sub>0) = (0::\<real>)"
  assume a2: "\<not> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b.  ?pqr v\<^sub>0) = (0::\<real>)"

  have pq_0: "(\<forall>s. ?pq s = 0) \<or> \<not> ?pq summable_on UNIV"
    by (smt (verit) UNIV_I a1 assms(1) assms(2) infsum_geq_element mult_nonneg_nonneg nle_le)
  show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?qr v\<^sub>0) = (0::\<real>)"
  proof (cases "(\<forall>s. ?pq s = 0)")
    case True
    then have "(\<forall>s. ?pqr s = 0)"
      using mult_eq_0_iff by blast
    then have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b.  ?pqr v\<^sub>0) = (0::\<real>)"
      by (meson infsum_0)
    then show ?thesis 
      using a2 by blast
  next
    case False
    then have "\<not> ?pq summable_on UNIV"
      using pq_0 by blast
    then show ?thesis
      using assms(4) by (meson infsum_0 infsum_not_exists)
  qed
next
  fix s
  let ?pq = "\<lambda>v\<^sub>0::'b. p (s, v\<^sub>0) * q (s, v\<^sub>0)"
  let ?qr = "\<lambda>v\<^sub>0::'b. q (s, v\<^sub>0) * r (s, v\<^sub>0)"
  let ?pqr = "\<lambda>v\<^sub>0::'b. p (s, v\<^sub>0) * q (s, v\<^sub>0) * r (s, v\<^sub>0)"

  assume a1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?qr v\<^sub>0) = (0::\<real>)"
  assume a2: "\<not> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b.  ?pqr v\<^sub>0) = (0::\<real>)"

  have qr_0: "(\<forall>s. ?qr s = 0) \<or> \<not> ?qr summable_on UNIV"
    by (smt (verit) UNIV_I a1 assms(2) assms(3) infsum_geq_element mult_nonneg_nonneg nle_le)
  show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?pq v\<^sub>0) = (0::\<real>)"
  proof (cases "(\<forall>s. ?qr s = 0)")
    case True
    then have "(\<forall>s. ?pqr s = 0)"
      using mult_eq_0_iff by auto
    then have "(\<Sum>\<^sub>\<infinity>v\<^sub>0.  ?pqr v\<^sub>0) = (0::\<real>)"
      by (meson infsum_0)
    then show ?thesis 
      using a2 by blast
  next
    case False
    then have "\<not> ?qr summable_on UNIV"
      using qr_0 by blast
    then show ?thesis
      using assms(5) by (meson infsum_0 infsum_not_exists)
  qed
qed

theorem rvfun_parallel_f_assoc_prob:
  assumes "\<forall>s::'a. is_prob ((curry p) s)"
          "\<forall>s::'a. is_prob ((curry q) s)" 
          "\<forall>s::'a. is_prob ((curry r) s)"
  assumes  "\<forall>s::'a. ((curry q) s) summable_on UNIV"
  shows "(p \<parallel>\<^sub>f q) \<parallel>\<^sub>f r = p \<parallel>\<^sub>f (q \<parallel>\<^sub>f r)"
proof -
  fix a::"'a"
  have a1: "\<forall>s. p s \<ge> 0 \<and> p s \<le> 1"
    using assms(1) by (expr_auto add: dist_defs)

  have a2: "\<forall>s. q s \<ge> 0 \<and> q s \<le> 1"
    using assms(2) by (expr_auto add: dist_defs)

  have a3: "\<forall>s. r s \<ge> 0 \<and> r s \<le> 1"
    using assms(3) by (expr_auto add: dist_defs)

  have pq_summable: "\<forall>s. (\<lambda>v\<^sub>0::'b. p (s, v\<^sub>0) * q (s, v\<^sub>0)) summable_on UNIV"
  proof (rule allI)
    fix s
    show "(\<lambda>v\<^sub>0::'b. p (s, v\<^sub>0) * q (s, v\<^sub>0)) summable_on UNIV"
      apply (subst summable_on_iff_abs_summable_on_real)
      apply (rule abs_summable_on_comparison_test[where g = "\<lambda>x. q (s, x)"])
      apply (subst summable_on_iff_abs_summable_on_real[symmetric])
      using assms(4) apply (metis (no_types, lifting) curry_def summable_on_cong)
      by (simp add: a1 a2 mult_left_le_one_le)
  qed

  have qr_summable: "\<forall>s. (\<lambda>v\<^sub>0::'b. q (s, v\<^sub>0) * r (s, v\<^sub>0)) summable_on UNIV"
  proof (rule allI)
    fix s
    show "(\<lambda>v\<^sub>0::'b. q (s, v\<^sub>0) * r (s, v\<^sub>0)) summable_on UNIV"
      apply (subst summable_on_iff_abs_summable_on_real)
      apply (rule abs_summable_on_comparison_test[where g = "\<lambda>x. q (s, x)"])
      apply (subst summable_on_iff_abs_summable_on_real[symmetric])
      using assms(4) apply (metis (no_types, lifting) curry_def summable_on_cong)
      by (simp add: a2 a3 mult_right_le_one_le)
  qed
  
  show ?thesis
    apply (rule rvfun_parallel_f_assoc_nonneg)
    apply (simp add: a1 a2 a3)+
    using pq_summable apply presburger
    using qr_summable by presburger
qed

theorem rvfun_parallel_f_assoc_prob':
  assumes "\<forall>s::'a. is_prob ((curry p) s)"
          "\<forall>s::'a. is_prob ((curry q) s)" 
          "\<forall>s::'a. is_prob ((curry r) s)"
  assumes "\<forall>s::'a. ((curry p) s) summable_on UNIV \<and> ((curry r) s) summable_on UNIV"
  shows "(p \<parallel>\<^sub>f q) \<parallel>\<^sub>f r = p \<parallel>\<^sub>f (q \<parallel>\<^sub>f r)"
proof -
  fix a::"'a"
  have a1: "\<forall>s. p s \<ge> 0 \<and> p s \<le> 1"
    using assms(1) by (expr_auto add: dist_defs)

  have a2: "\<forall>s. q s \<ge> 0 \<and> q s \<le> 1"
    using assms(2) by (expr_auto add: dist_defs)

  have a3: "\<forall>s. r s \<ge> 0 \<and> r s \<le> 1"
    using assms(3) by (expr_auto add: dist_defs)

  have pq_summable: "\<forall>s. (\<lambda>v\<^sub>0::'b. p (s, v\<^sub>0) * q (s, v\<^sub>0)) summable_on UNIV"
  proof (rule allI)
    fix s
    show "(\<lambda>v\<^sub>0::'b. p (s, v\<^sub>0) * q (s, v\<^sub>0)) summable_on UNIV"
      apply (subst summable_on_iff_abs_summable_on_real)
      apply (rule abs_summable_on_comparison_test[where g = "\<lambda>x. p (s, x)"])
      apply (subst summable_on_iff_abs_summable_on_real[symmetric])
      using assms(4) apply (metis (no_types, lifting) curry_def summable_on_cong)
      by (simp add: a1 a2 mult_right_le_one_le)
  qed

  have qr_summable: "\<forall>s. (\<lambda>v\<^sub>0::'b. q (s, v\<^sub>0) * r (s, v\<^sub>0)) summable_on UNIV"
  proof (rule allI)
    fix s
    show "(\<lambda>v\<^sub>0::'b. q (s, v\<^sub>0) * r (s, v\<^sub>0)) summable_on UNIV"
      apply (subst summable_on_iff_abs_summable_on_real)
      apply (rule abs_summable_on_comparison_test[where g = "\<lambda>x. r (s, x)"])
      apply (subst summable_on_iff_abs_summable_on_real[symmetric])
      using assms(4) apply (metis (no_types, lifting) curry_def summable_on_cong)
      by (simp add: a2 a3 mult_left_le_one_le)
  qed
  
  show ?thesis
    apply (rule rvfun_parallel_f_assoc_nonneg)
    apply (simp add: a1 a2 a3)+
    using pq_summable apply presburger
    using qr_summable by presburger
qed

(*
theorem prel_parallel_assoc_f:
  fixes P Q R :: "('s\<^sub>1, 's\<^sub>2) rvfun"
  assumes "\<forall>s. P s \<ge> 0" "\<forall>s. Q s \<ge> 0" "\<forall>s. R s \<ge> 0"
    "\<forall>s. ((\<lambda>v\<^sub>0. P (s, v\<^sub>0) * Q (s, v\<^sub>0)) summable_on UNIV)"
    "\<forall>s. ((\<lambda>v\<^sub>0. Q (s, v\<^sub>0) * R (s, v\<^sub>0)) summable_on UNIV)"
  assumes "\<forall>s\<^sub>1. \<exists>s'. (P) (s\<^sub>1, s') > 0 \<and> (Q) (s\<^sub>1, s') > 0"
  assumes "\<forall>s\<^sub>1. \<exists>s'. (Q) (s\<^sub>1, s') > 0 \<and> (R) (s\<^sub>1, s') > 0"
  shows "(P \<parallel> Q) \<parallel> R = P \<parallel> (Q \<parallel> R)"
  apply (simp add: pfun_defs)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (subst prel_of_rfrel_inverse)
  apply (expr_auto add: dist_defs)
  apply (simp add: assms(1) assms(2) infsum_nonneg)
  apply (subgoal_tac "P (s\<^sub>1, s) * Q (s\<^sub>1, s) \<le> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s\<^sub>2.  P (s\<^sub>1, v\<^sub>0) * Q (s\<^sub>1, v\<^sub>0))")
  apply (smt (verit, ccfv_SIG) assms(1) assms(2) divide_le_eq_1 mult_nonneg_nonneg)
  apply (rule infsum_geq_element)
  apply (simp add: assms(1) assms(2))
  apply (simp add: assms(4))+
  apply (subst infsum_cdiv_left)
  apply (simp add: assms(4))
  apply (simp)
  defer
  apply (subst prel_of_rfrel_inverse)
  apply (expr_auto add: dist_defs)
  apply (simp add: assms(2) assms(3) infsum_nonneg)
  apply (subgoal_tac "Q (s\<^sub>1, s) * R (s\<^sub>1, s) \<le> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s\<^sub>2.  Q (s\<^sub>1, v\<^sub>0) * R (s\<^sub>1, v\<^sub>0))")
  apply (smt (verit, ccfv_SIG) assms(2) assms(3) divide_le_eq_1 mult_nonneg_nonneg)
  apply (rule infsum_geq_element)
  apply (simp add: assms(2) assms(3))
  apply (simp add: assms(5))+
  apply (subst infsum_cdiv_left)
  apply (simp add: assms(5))
  apply (simp)
  defer
  apply (rule prel_parallel_f_assoc_nonneg)
  apply (simp add: assms(1-3))+
  apply (simp add: assms(4))
  apply (simp add: assms(5))
  apply (smt (verit, ccfv_threshold) assms(1) assms(2) assms(4) assms(6) infsum_geq_element 
      iso_tuple_UNIV_I mult_nonneg_nonneg mult_pos_pos)
  by (smt (verit, ccfv_threshold) assms(2) assms(3) assms(5) assms(7) infsum_geq_element 
      iso_tuple_UNIV_I mult_nonneg_nonneg mult_pos_pos)

theorem prel_parallel_assoc_p:
  fixes P Q R :: "('s\<^sub>1, 's\<^sub>2) prel"
  assumes "\<forall>s\<^sub>1. \<exists>s'. (rfrel_of_prel P) (s\<^sub>1, s') > 0 \<and> (rfrel_of_prel Q) (s\<^sub>1, s') > 0"
  assumes "\<forall>s\<^sub>1. \<exists>s'. (rfrel_of_prel Q) (s\<^sub>1, s') > 0 \<and> (rfrel_of_prel R) (s\<^sub>1, s') > 0"
  shows "(P \<parallel> Q) \<parallel> R = P \<parallel> (Q \<parallel> R)"
  apply (simp add: prel_defs)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (subst prel_of_rfrel_inverse)
  apply (expr_auto add: dist_defs)
  apply (simp add: infsum_nonneg prel_in_0_1')
  apply (subgoal_tac "rfrel_of_prel P (s\<^sub>1, s) * rfrel_of_prel Q (s\<^sub>1, s) \<le>
       (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s\<^sub>2. rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * rfrel_of_prel Q (s\<^sub>1, v\<^sub>0))")
  apply (smt (verit, ccfv_SIG) divide_le_eq_1_pos divide_nonneg_nonpos mult_nonneg_nonneg prel_in_0_1')
  apply (rule infsum_geq_element)
  apply (simp add: prel_in_0_1')
  apply (subst prel_joint_prob_summable_on_product_dist')
  apply (simp add: prel_is_dist)+
  apply (subst infsum_cdiv_left)
  using prel_joint_prob_summable_on_product_dist' apply (simp add: infsum_not_zero_summable)
  apply (simp)
  defer
  apply (subst prel_of_rfrel_inverse)
  apply (expr_auto add: dist_defs)
  apply (simp add: infsum_nonneg prel_in_0_1')
  apply (subgoal_tac "rfrel_of_prel Q (s\<^sub>1, s) * rfrel_of_prel R (s\<^sub>1, s) \<le>
       (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s\<^sub>2. rfrel_of_prel Q (s\<^sub>1, v\<^sub>0) * rfrel_of_prel R (s\<^sub>1, v\<^sub>0))")
  apply (smt (verit, ccfv_SIG) divide_le_eq_1_pos divide_nonneg_nonpos mult_nonneg_nonneg prel_in_0_1')
  apply (rule infsum_geq_element)
  apply (simp add: prel_in_0_1')
  apply (subst prel_joint_prob_summable_on_product_dist')
  apply (simp add: prel_is_dist)+
  apply (subst infsum_cdiv_left)
  using prel_joint_prob_summable_on_product_dist' apply (simp add: infsum_not_zero_summable)
  apply (simp)
  defer
  apply (rule prel_parallel_f_assoc_prob)
  apply (simp add: prel_is_prob)+
  apply (smt (verit) infsum_not_exists is_dist_def is_sum_1_def prel_is_dist)
proof -
  fix s\<^sub>1
  let ?P = "\<lambda>s'. (rfrel_of_prel P) (s\<^sub>1, s') > 0 \<and> (rfrel_of_prel Q) (s\<^sub>1, s') > 0"
  have f1: "?P (SOME s'. ?P s')"
    apply (rule someI_ex[where P="?P"])
    using assms by blast
  have f2: "(\<lambda>s. (rfrel_of_prel P) (s\<^sub>1, s) * (rfrel_of_prel Q) (s\<^sub>1, s)) (SOME s'. ?P s') \<le> 
    (\<Sum>\<^sub>\<infinity>s'. (rfrel_of_prel P) (s\<^sub>1, s') * (rfrel_of_prel Q) (s\<^sub>1, s'))"
    apply (rule infsum_geq_element)
    apply (simp add: prel_in_0_1')
    apply (subst prel_joint_prob_summable_on_product)
    apply (simp add: prel_is_prob)+
    by (simp add: prel_summable)+
  also have f3: "... > 0"
    by (smt (verit, ccfv_threshold) f1 f2 mult_pos_pos)
  then show "\<not> (\<Sum>\<^sub>\<infinity>s::'s\<^sub>2. rfrel_of_prel P (s\<^sub>1, s) * rfrel_of_prel Q (s\<^sub>1, s)) = (0::\<real>)"
    by linarith
next
  fix s\<^sub>1
  let ?P = "\<lambda>s'. (rfrel_of_prel Q) (s\<^sub>1, s') > 0 \<and> (rfrel_of_prel R) (s\<^sub>1, s') > 0"
  have f1: "?P (SOME s'. ?P s')"
    apply (rule someI_ex[where P="?P"])
    using assms by blast
  have f2: "(\<lambda>s. (rfrel_of_prel Q) (s\<^sub>1, s) * (rfrel_of_prel R) (s\<^sub>1, s)) (SOME s'. ?P s') \<le> 
    (\<Sum>\<^sub>\<infinity>s'. (rfrel_of_prel Q) (s\<^sub>1, s') * (rfrel_of_prel R) (s\<^sub>1, s'))"
    apply (rule infsum_geq_element)
    apply (simp add: prel_in_0_1')
    apply (subst prel_joint_prob_summable_on_product)
    apply (simp add: prel_is_prob)+
    by (simp add: prel_summable)+
  also have f3: "... > 0"
    by (smt (verit, ccfv_threshold) f1 f2 mult_pos_pos)
  then show "\<not> (\<Sum>\<^sub>\<infinity>s::'s\<^sub>2. rfrel_of_prel Q (s\<^sub>1, s) * rfrel_of_prel R (s\<^sub>1, s)) = (0::\<real>)"
    by linarith
qed

theorem prel_parallel_commute:
  fixes P Q::"('a, 'b) rfrel"
  shows "P \<parallel> Q = Q \<parallel> P"
  apply (simp add: prel_defs)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  by (simp add: mult.commute)

theorem prel_parallel_commute':
  fixes P Q::"('a, 'b) prel"
  shows "P \<parallel> Q = Q \<parallel> P"
  apply (simp add: prel_defs)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  by (simp add: mult.commute)

theorem prel_parallel_commute'':
  fixes P ::"('a, 'b) rfrel" and Q :: "('a, 'b) prel"
  shows "P \<parallel> Q = Q \<parallel> P"
  apply (simp add: prel_defs)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  by (simp add: mult.commute)

theorem prel_parallel_commute''':
  fixes P ::"('a, 'b) prel" and Q :: "('a, 'b) rfrel"
  shows "P \<parallel> Q = Q \<parallel> P"
  apply (simp add: prel_defs)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  by (simp add: mult.commute)

text \<open>Any nonzero constant is a left identity in parallel with a distribution. \<close>
theorem prel_parallel_left_identity:
  assumes "is_final_distribution Q"
  assumes "c \<noteq> 0"
  shows "(\<lambda>s. c) \<parallel> Q = prel_of_rfrel Q"
  apply (simp add: prel_defs dist_defs)
  apply (expr_auto)
  apply (subst infsum_cmult_right)
  apply (simp add: assms prel_prob_sum1_summable(3))
  by (simp add: assms prel_prob_sum1_summable(2))

theorem prel_parallel_left_identity':
  assumes "c \<noteq> 0"
  shows "(\<lambda>s. c) \<parallel> Q = Q"
  apply (simp add: prel_defs dist_defs)
  apply (expr_auto)
  apply (subst infsum_cmult_right)
  apply (simp add: prel_summable)
  apply (simp add: assms)
  apply (subst prel_sum_1)
  apply (simp)
  by (simp add: rfrel_of_prel_inverse)

text \<open>Any nonzero constant is a right identity in parallel with a distribution. \<close>
theorem prel_parallel_right_identity:
  assumes "is_final_distribution Q"
  assumes "c \<noteq> 0"
  shows "Q \<parallel> (\<lambda>s. c) = prel_of_rfrel Q"
  apply (simp add: prel_defs dist_defs)
  apply (expr_auto)
  apply (subst infsum_cmult_left)
  apply (simp add: assms prel_prob_sum1_summable(3))
  by (simp add: assms prel_prob_sum1_summable(2))

theorem prel_parallel_right_identity':
  assumes "c \<noteq> 0"
  shows "Q \<parallel> (\<lambda>s. c) = Q"
  apply (simp add: prel_defs dist_defs)
  apply (expr_auto)
  apply (subst infsum_cmult_left)
  apply (simp add: prel_summable)
  apply (simp add: assms)
  apply (subst prel_sum_1)
  apply (simp)
  by (simp add: rfrel_of_prel_inverse)

theorem prel_parallel_right_zero:
  fixes Q :: "('a, 'b) rfrel"
  shows "(Q \<parallel> 0\<^sub>f) = 0\<^sub>p"
  apply (simp add: prel_defs dist_defs)
  by (expr_auto)

theorem prel_parallel_left_zero:
  fixes Q :: "('a, 'b) rfrel"
  shows "(0\<^sub>f \<parallel> Q) = 0\<^sub>p"
  apply (simp add: prel_defs dist_defs)
  by (expr_auto)

term "(\<Sum>v\<in>\<guillemotleft>A\<guillemotright>. ([ x\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright> ] \<dagger> P))\<^sub>e"
term "([ x\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright> ] \<dagger> P)\<^sub>e"
term "(\<Sum>v\<in>\<guillemotleft>A\<guillemotright>. (\<lbrakk>$x\<^sup>> = \<guillemotleft>v\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * ([ x\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright> ] \<dagger> P)))\<^sub>e"
term "(\<Sum>v\<in>\<guillemotleft>A\<guillemotright>. (\<lbrakk>\<lbrakk>x := \<guillemotleft>v\<guillemotright>\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e * ([ x\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright> ] \<dagger> P)))\<^sub>e"

text \<open> The parallel composition of a @{text "P"} with a uniform distribution is just a normalised 
summation of @{text "P"} with @{text "x"} in its final states substituted for each value in @{text "A"}.\<close>
theorem prel_parallel_uniform_dist:
  fixes P ::"('a, 'a) rfrel"
  assumes "finite A"
  assumes "vwb_lens x"
  assumes "A \<noteq> {}"
  shows "(x \<^bold>\<U> A) \<parallel> P = 
    prel_of_rfrel ((\<Sum>v\<in>\<guillemotleft>A\<guillemotright>. (\<lbrakk>\<lbrakk>x := \<guillemotleft>v\<guillemotright>\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e * ([ x\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright> ] \<dagger> P)))
                      / (\<Sum> v\<in>\<guillemotleft>A\<guillemotright>. ([ x\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright> ] \<dagger> P)))\<^sub>e"
  apply (subst uniform_dist_altdef)
  apply (simp add: assms(1-3))+
  apply (simp add: dist_defs prel_defs)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (expr_auto add: rel)
proof -
  fix a and xa
  assume a1: "xa \<in> A"

  let ?lhs_1 = "(real (card A) * (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. 
    (if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> a xa = v\<^sub>0 then 1::\<real> else (0::\<real>)) * P (a, v\<^sub>0) / real (card A)))"
  let ?lhs = "P (a, put\<^bsub>x\<^esub> a xa) / ?lhs_1"

  let ?rhs_1 = "(\<Sum>v::'b\<in>A. 
    (if put\<^bsub>x\<^esub> a v = put\<^bsub>x\<^esub> a xa then 1::\<real> else (0::\<real>)) * P (a, put\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> a xa) v))"
  let ?rhs_2 = "(\<Sum>v::'b\<in>A. P (a, put\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> a xa) v))"
  let ?rhs = "?rhs_1 / ?rhs_2"

  have "finite {put\<^bsub>x\<^esub> a xa | xa. xa \<in> A}"
    apply (rule finite_image_set)
    using assms(1) by auto
  then have finite_states: "finite {v\<^sub>0::'a. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> a xa = v\<^sub>0}"
    by (smt (verit, del_insts) Collect_cong)

  have set_eq: "{v\<^sub>0::'a. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> a xa = v\<^sub>0} = {put\<^bsub>x\<^esub> a xa | xa. xa \<in> A}"
    by (smt (verit, del_insts) Collect_cong)

  have f1: "(real (card A) * (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> a xa = v\<^sub>0 then 1::\<real> else (0::\<real>)) 
                                * P (a, v\<^sub>0) / real (card A))
            )
      = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> a xa = v\<^sub>0 then 1::\<real> else (0::\<real>)) * P (a, v\<^sub>0))"
    apply (subst infsum_cdiv_left)
    apply (subst infsum_mult_subset_left_summable)
    apply (rule summable_on_finite)
    using finite_states apply blast
    by (simp add: assms(1))

  have denominator_1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a \<in> {v\<^sub>0::'a. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> a xa = v\<^sub>0}. P (a, v\<^sub>0)) = 
      (\<Sum>v\<^sub>0::'a \<in> {v\<^sub>0::'a. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> a xa = v\<^sub>0}. P (a, v\<^sub>0))"
    using finite_states infsum_finite by blast
  also have denominator_2: "... = (\<Sum>v::'b\<in>A. P (a, put\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> a xa) v))"
    apply (simp add: set_eq)
    apply (subst sum.reindex_cong[where A="{uu::'a. \<exists>xa::'b. uu = put\<^bsub>x\<^esub> a xa \<and> xa \<in> A}" and 
         B = "A" and l = "\<lambda>xa. put\<^bsub>x\<^esub> a xa" and h = "\<lambda>v. P (a, put\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> a xa) v)"])
    apply (meson assms(2) inj_onI vwb_lens.axioms(1) wb_lens_def weak_lens.view_determination)
    apply (simp add: Setcompr_eq_image)
    apply (simp add: assms(2))
    by blast

  have numerator_1: "?rhs_1
    = (\<Sum>v::'b\<in>A. (if xa = v then 1::\<real> else (0::\<real>)) * P (a, put\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> a xa) v))"
    by (smt (verit, ccfv_SIG) assms(2) mwb_lens.axioms(1) sum.cong vwb_lens.axioms(2) 
        weak_lens.view_determination)
  have numerator_2: "... = 
    (\<Sum>v::'b\<in>{xa} \<union> (A - {xa}). (if xa = v then 1::\<real> else (0::\<real>)) * P (a, put\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> a xa) v))"
    using a1 insert_Diff by force
  have numerator_3: "... = (\<Sum>v::'b\<in>{xa}. P (a, put\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> a xa) v))"
    apply (subst sum_Un[where A = "{xa}" and B = "A - {xa}" and 
          f = "\<lambda>v::'b. (if xa = v then 1::\<real> else (0::\<real>)) * P (a, put\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> a xa) v)"])
    apply simp
    using assms(1) apply blast
    using sum.not_neutral_contains_not_neutral by fastforce
  have numerator_4: "... = P (a, put\<^bsub>x\<^esub> a xa)"
    by (simp add: assms(2))
  show "?lhs = ?rhs"
    apply (simp add: f1)
    apply (subst infsum_mult_subset_left)
    using denominator_1 denominator_2 numerator_1 numerator_2 numerator_3 numerator_4 by presburger
qed

term "([ x\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright> ] \<dagger> P)\<^sub>e"
term "(\<exists>v \<in> A. ([ x\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright> ] \<dagger> P) > 0)\<^sub>e"
lemma prel_parallel_uniform_dist':
  fixes P ::"('a, 'a) rfrel"
  assumes "finite A"
  assumes "vwb_lens x"
  assumes "A \<noteq> {}"
  assumes "\<forall>s. P s \<ge> 0"
  (* assumes "(\<exists>v \<in> A. ([ x\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright> ] \<dagger> P) > 0)\<^sub>e" *)
  assumes "\<forall>s. \<exists>v \<in> A. P (s, put\<^bsub>x\<^esub> s v) > 0"
  shows "rfrel_of_prel ((x \<^bold>\<U> A) \<parallel> P) = 
      ((\<Sum>v\<in>\<guillemotleft>A\<guillemotright>. (\<lbrakk>\<lbrakk>x := \<guillemotleft>v\<guillemotright>\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e * ([ x\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright> ] \<dagger> P))) / (\<Sum> v\<in>\<guillemotleft>A\<guillemotright>. ([ x\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright> ] \<dagger> P)))\<^sub>e"
  apply (subst prel_parallel_uniform_dist) 
  apply (simp add: assms)+
  apply (subst prel_of_rfrel_inverse)
  apply (expr_auto add: dist_defs rel)
  prefer 4
  apply (simp)
  using assms(4) apply (simp add: sum_nonneg)
  apply (smt (verit, ccfv_SIG) assms(4) divide_le_eq_1 mult_cancel_right1 mult_not_zero sum_mono sum_nonneg)
proof -
  fix s\<^sub>1
  let ?set = "{put\<^bsub>x\<^esub> s\<^sub>1 xa | xa. xa \<in> A}"
  let ?lhs_1 = "\<lambda>s. (\<Sum>v::'b\<in>A. (if put\<^bsub>x\<^esub> s\<^sub>1 v = s then 1::\<real> else (0::\<real>)) * P (s\<^sub>1, put\<^bsub>x\<^esub> s v))"
  let ?lhs_2 = "\<lambda>s. (\<Sum>v::'b\<in>A. P (s\<^sub>1, put\<^bsub>x\<^esub> s v))"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>s::'a. ?lhs_1 s / ?lhs_2 s)"

  have finite_set: "finite {put\<^bsub>x\<^esub> s\<^sub>1 xa | xa. xa \<in> A}"
    apply (rule finite_image_set)
    using assms(1) by auto

  have sum_not_zero: "(\<Sum>v::'b\<in>A. P (s\<^sub>1, put\<^bsub>x\<^esub> s\<^sub>1 v)) \<noteq> 0"
    using assms(5) by (smt (verit, del_insts) assms(1) assms(4) sum_nonneg_0)

  have "?lhs = (\<Sum>\<^sub>\<infinity>s::'a \<in> ?set \<union> (UNIV - ?set). ?lhs_1 s / ?lhs_2 s)"
    by auto
  also have "... = (\<Sum>\<^sub>\<infinity>s::'a \<in> ?set. ?lhs_1 s / ?lhs_2 s)"
    apply (rule infsum_cong_neutral)
    apply fastforce
    apply (smt (verit, del_insts) CollectI DiffD2 divide_eq_0_iff mult_eq_0_iff 
        sum.not_neutral_contains_not_neutral)
    by fastforce
  also have "... = (\<Sum>s::'a \<in> ?set. ?lhs_1 s / ?lhs_2 s)"
    using finite_set infsum_finite by blast
  also have "... = (\<Sum>s::'a \<in> ?set. P (s\<^sub>1, s) / (\<Sum>v::'b\<in>A. P (s\<^sub>1, put\<^bsub>x\<^esub> s\<^sub>1 v)))"
    apply (subst sum.cong[where A = "?set" and B = "?set" and 
          h = "\<lambda>s. P (s\<^sub>1, s) / (\<Sum>v::'b\<in>A. P (s\<^sub>1, put\<^bsub>x\<^esub> s\<^sub>1 v))"])
    apply (simp)
    defer
    apply (simp)
    proof -
      fix xa
      assume a1: "xa \<in> {uu::'a. \<exists>xa::'b. uu = put\<^bsub>x\<^esub> s\<^sub>1 xa \<and> xa \<in> A}"
      let ?lhs_1 = "(\<Sum>v::'b\<in>A. (if put\<^bsub>x\<^esub> s\<^sub>1 v = xa then 1::\<real> else (0::\<real>)) * P (s\<^sub>1, put\<^bsub>x\<^esub> xa v))"
  
      have denominator_eq: "(\<Sum>v::'b\<in>A. P (s\<^sub>1, put\<^bsub>x\<^esub> xa v)) = (\<Sum>v::'b\<in>A. P (s\<^sub>1, put\<^bsub>x\<^esub> s\<^sub>1 v))"
        using a1 assms(2) by force
      
      have numerator_eq: "?lhs_1 = (\<Sum>v::'b\<in>{get\<^bsub>x\<^esub> xa} \<union> (A - {get\<^bsub>x\<^esub> xa}). 
        (if put\<^bsub>x\<^esub> s\<^sub>1 v = xa then 1::\<real> else (0::\<real>)) * P (s\<^sub>1, put\<^bsub>x\<^esub> xa v))"
        using a1 assms(2) insert_Diff by fastforce
      also have "... = (\<Sum>v::'b\<in>{get\<^bsub>x\<^esub> xa}.  
                    (if put\<^bsub>x\<^esub> s\<^sub>1 v = xa then 1::\<real> else (0::\<real>)) * P (s\<^sub>1, put\<^bsub>x\<^esub> xa v))"
        apply (subst sum_Un[where A = "{get\<^bsub>x\<^esub> xa}" and B = "A - {get\<^bsub>x\<^esub> xa}" and 
          f = "\<lambda>v. (if put\<^bsub>x\<^esub> s\<^sub>1 v = xa then 1::\<real> else (0::\<real>)) * P (s\<^sub>1, put\<^bsub>x\<^esub> xa v)"])
        apply blast
        using assms(1) apply blast
        by (smt (verit) Diff_disjoint Diff_iff add_cancel_left_right assms(2) finite.emptyI 
            insert_disjoint(2) mult_not_zero sum.empty sum.not_neutral_contains_not_neutral 
            vwb_lens_def wb_lens_weak weak_lens.put_get)
      also have "... = P (s\<^sub>1, put\<^bsub>x\<^esub> xa (get\<^bsub>x\<^esub> xa))"
        using a1 assms(2) by force
      also have "... = P (s\<^sub>1, xa)"
        by (simp add: assms(2))
      then show "(\<Sum>v::'b\<in>A. (if put\<^bsub>x\<^esub> s\<^sub>1 v = xa then 1::\<real> else (0::\<real>)) * P (s\<^sub>1, put\<^bsub>x\<^esub> xa v)) /
         (\<Sum>v::'b\<in>A. P (s\<^sub>1, put\<^bsub>x\<^esub> xa v)) =
         P (s\<^sub>1, xa) / (\<Sum>v::'b\<in>A. P (s\<^sub>1, put\<^bsub>x\<^esub> s\<^sub>1 v))"
        using calculation denominator_eq by presburger
    qed
  also have "... = (\<Sum>s::'a \<in> ?set. P (s\<^sub>1, s)) / (\<Sum>v::'b\<in>A. P (s\<^sub>1, put\<^bsub>x\<^esub> s\<^sub>1 v))"
    by (smt (verit) sum.cong sum_divide_distrib)
  also have "... = 1"
    apply (subgoal_tac "(\<Sum>s::'a \<in> ?set. P (s\<^sub>1, s)) = (\<Sum>v::'b\<in>A. P (s\<^sub>1, put\<^bsub>x\<^esub> s\<^sub>1 v))")
    apply (simp add: sum_not_zero)
    apply (rule sum.reindex_cong[where l = "(\<lambda>xa. put\<^bsub>x\<^esub> s\<^sub>1 xa)" and B = "A"])
    apply (metis assms(2) inj_on_inverseI vwb_lens.axioms(1) wb_lens_weak weak_lens.put_get)
    apply (simp add: Setcompr_eq_image)
    by simp
  
  finally show "?lhs = (1::\<real>)"
    by meson
qed
*)

subsection \<open> Chains \<close>
subsubsection \<open> Increasing chains \<close>
theorem increasing_chain_mono:
  assumes "increasing_chain f"
  assumes "m \<le> n"
  shows "f m \<le> f n"
  using assms(1) assms(2) increasing_chain_def by blast

theorem increasing_chain_sup_eq_f0_constant:
  assumes "increasing_chain f"
  assumes "(\<Squnion>n::\<nat>. f n (s, s')) = f 0 (s, s')"
  shows "\<forall>n. f n (s, s') = f 0 (s, s')"
proof (rule ccontr)
  assume "\<not> (\<forall>n::\<nat>. f n (s, s') = f (0::\<nat>) (s, s'))"
  then have "\<exists>n. f n (s, s') \<noteq> f 0 (s, s')"
    by blast
  then have "\<exists>n. f n (s, s') > f 0 (s, s')"
    using increasing_chain_mono by (metis assms(1) le_funE less_eq_nat.simps(1) nless_le)
  then have "(\<Squnion>n::\<nat>. f n (s, s')) > f 0 (s, s')"
    by (metis SUP_lessD UNIV_I assms(2) nless_le)
  then show "false"
    by (simp add: assms(2))
qed

lemma increasing_chain_sup_subset_eq:
  assumes "increasing_chain f"
  shows "(\<Squnion>n::\<nat>. f (n + m)) = (\<Squnion>n::\<nat>. f n)"
proof -
  have f1: "(\<Squnion>n::nat. f (n + m)) = (\<Squnion>n\<in>{m..}. f n)"
    apply (simp add: image_def)
    by (metis (no_types, lifting) add.commute add.right_neutral atLeast_0 atLeast_iff image_add_atLeast le_add_same_cancel2 rangeE zero_le)
  have f2: "{..m-1} \<union> {(m::nat)..} = UNIV"
    by (metis Suc_pred' atLeast0LessThan atLeast_0 bot_nat_0.extremum bot_nat_0.not_eq_extremum ivl_disj_un_one(8) lessThan_Suc_atMost ref_lattice.inf_bot_right)
  then have f3: "(\<Squnion>n::nat. f n) = (\<Squnion>n::nat \<in> {..m-1} \<union> {(m::nat)..}. f n)"
    by (simp add: image_def)
  have f4: "(\<Squnion>n::nat \<in> {..m-1} \<union> {(m::nat)..}. f n) = (\<Squnion>n\<in>{..m-1}. f n) \<squnion> (\<Squnion>n\<in>{m..}. f n)"
    apply (subst SUP_union)
    by blast
  have f5: "(\<Squnion>n\<in>{..m-1}. f n) \<le> (\<Squnion>n\<in>{m..}. f n)"
    apply (subst SUP_le_iff)
    by (smt (verit) SUP_upper2 assms atLeast_iff increasing_chain_mono le_cases3)
  then have f6: "(\<Squnion>n\<in>{..m-1}. f n) \<squnion> (\<Squnion>n\<in>{m..}. f n) = (\<Squnion>n\<in>{m..}. f n)"
    apply (subst (asm) le_iff_sup)
    by blast
  show ?thesis
    using f1 f3 f4 f6 by presburger
qed

thm "SUP_least"
lemma increasing_chain_limit_exists_element:
  fixes f :: "nat \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun"
  assumes "increasing_chain f"
  assumes "\<exists>n. f n (s, s') > 0"
  shows "\<forall>e > 0. \<exists>m. f m (s, s') > (\<Squnion>n::\<nat>. f n (s, s')) - e"
  apply (rule ccontr)
  apply (auto)
proof -
  fix e
  assume pos: "(0::ureal) < e"
  assume a1: "\<forall>m::\<nat>. \<not> (\<Squnion>n::\<nat>. f n (s, s')) - e < f m (s, s')"

  from a1 have "\<forall>m::\<nat>. f m (s, s') \<le> (\<Squnion>n::\<nat>. f n (s, s')) - e"
    using linorder_not_less by blast
  then have sup_least: "(\<Squnion>n::\<nat>. f n (s, s')) \<le> (\<Squnion>n::\<nat>. f n (s, s')) - e"
    using SUP_least by metis
  have "(\<Squnion>n::\<nat>. f n (s, s')) \<ge> 0"
    using less_eq_ureal.rep_eq ureal2ereal zero_ureal.rep_eq by fastforce
  then have "(\<Squnion>n::\<nat>. f n (s, s')) > 0"
    using assms(2) by (metis Sup_upper linorder_not_le nle_le range_eqI)
  then show "false"
    using pos sup_least by (meson linorder_not_le ureal_minus_less)
qed

(* This is not valid
lemma increasing_chain_limit_exists_element':
  fixes f :: "nat \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun"
  assumes "increasing_chain f"
  shows "\<forall>e > 0. \<forall>s. \<exists>m. f m s > (\<Squnion>n::\<nat>. f n s) - e"
  apply (rule ccontr)
  apply (auto)
proof -
  fix e s s'
  assume pos: "(0::ureal) < e"
  assume a1: "\<forall>m::\<nat>. \<not> (\<Squnion>n::\<nat>. f n (s, s')) - e < f m (s, s')"

  from a1 have f1: "\<forall>m::\<nat>. f m (s, s') \<le> (\<Squnion>n::\<nat>. f n (s, s')) - e"
    using linorder_not_less by blast
  then have sup_least: "(\<Squnion>n::\<nat>. f n (s, s')) \<le> (\<Squnion>n::\<nat>. f n (s, s')) - e"
    using SUP_least by metis
  have sup_ge_0: "(\<Squnion>n::\<nat>. f n (s, s')) \<ge> 0"
    using less_eq_ureal.rep_eq ureal2ereal zero_ureal.rep_eq by fastforce
  show "false"
  proof (cases "\<exists>n. f n (s, s') > 0")
    case True
    then have "(\<Squnion>n::\<nat>. f n (s, s')) > 0"
      by (metis f1 linorder_not_less nless_le pos sup_ge_0 ureal_minus_larger_zero)
    then show ?thesis 
      using pos sup_least by (meson linorder_not_le ureal_minus_less)
  next
    (* This is not going to be sound because 0 \<le> 0 - (e::ureal) *)
    case False
    then have "\<forall>n. f n (s, s') = 0"
      by (metis linorder_not_less ureal_minus_larger_zero ureal_minus_larger_zero_unit)
    then show ?thesis 
      sledgehammer
  qed
qed
*)

(*
lemma 
  assumes "increasing_chain f"
  shows "(\<Squnion>n::\<nat>. (ureal2ereal (f n))) = ureal2ereal (\<Squnion>n::\<nat>. f n)"
  sledgehammer
*)
text \<open> This lemma represents limit in a complete lattice ereal. So (0 - e) is not equal to 0 as in ureal \<close>
lemma increasing_chain_limit_exists_element':
  fixes f :: "nat \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun"
  assumes "increasing_chain f"
  shows "\<forall>(e::ereal) > 0. \<forall>s. \<exists>m. ureal2ereal (f m s) > ureal2ereal (\<Squnion>n::\<nat>. f n s) - e"
  apply (rule ccontr)
  apply (auto)
proof -
  fix e s s'
  assume pos: "(0::ereal) < e"
  assume a1: "\<forall>m::\<nat>. \<not> ureal2ereal (\<Squnion>n::\<nat>. f n (s, s')) - e < ureal2ereal (f m (s, s'))"

  from a1 have f1: "\<forall>m::\<nat>. ureal2ereal (f m (s, s')) \<le> ureal2ereal (\<Squnion>n::\<nat>. f n (s, s')) - e"
    using linorder_not_less by blast
  then have sup_least: "(\<Squnion>n::\<nat>. (ureal2ereal (f n (s, s')))) \<le> ureal2ereal (\<Squnion>n::\<nat>. f n (s, s')) - e"
    using SUP_least by metis
  have SUP_ereal_eq_ereal_SUP: "(\<Squnion>n::\<nat>. (ureal2ereal (f n (s, s')))) = ureal2ereal (\<Squnion>n::\<nat>. f n (s, s'))"
    (* using ureal2ereal_inverse SUP_least SUP_upper UNIV_I atLeastAtMost_iff dual_order.trans 
        ereal2ureal'_inverse less_eq_ureal.rep_eq nle_le ureal2ereal
    by (metis )
    *)
    sorry
  have sup_ge_0: "(\<Squnion>n::\<nat>. f n (s, s')) \<ge> 0"
    using less_eq_ureal.rep_eq ureal2ereal zero_ureal.rep_eq by fastforce
  show "false"
  proof (cases "\<exists>n. f n (s, s') > 0")
    case True
    then have "(\<Squnion>n::\<nat>. f n (s, s')) > 0"
      by (metis a1 ereal_diff_le_self nless_le order_le_less_trans pos sup_ge_0 ureal2ereal_mono)
    then have "ureal2ereal (\<Squnion>n::\<nat>. f n (s, s')) > 0"
      by (metis ureal2ereal_mono zero_ureal.rep_eq)
    then show ?thesis 
      using pos sup_least 
      by (smt (verit, best) SUP_ereal_eq_ereal_SUP a1 abs_ereal_ge0 atLeastAtMost_iff ereal_between(1) 
          ereal_less_eq(1) ereal_times(1) less_SUP_iff nle_le ureal2ereal)
  next
    (* This is not going to be sound because 0 \<le> 0 - (e::ureal) *)
    case False
    then have "\<forall>n. f n (s, s') = 0"
      by (metis linorder_not_less ureal_minus_larger_zero ureal_minus_larger_zero_unit)
    then show ?thesis 
      using local.sup_least pos zero_ureal.rep_eq by force
  qed
qed

(*
lemma increasing_chain_limit_exists_element':
  fixes f :: "nat \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun"
  assumes "increasing_chain f"
  shows "\<forall>e > 0. \<forall>s. (\<exists>n. f n s > 0) \<longrightarrow> (\<exists>m. f m s > (\<Squnion>n::\<nat>. f n s) - e)"
  apply (rule ccontr)
  apply (auto)
proof -
  fix e s s' n
  assume pos: "(0::ureal) < e"
  assume a1: "\<forall>m::\<nat>. \<not> (\<Squnion>n::\<nat>. f n (s, s')) - e < f m (s, s')"
  assume a2: "(0::ureal) < f n (s, s')"

  from a1 have "\<forall>m::\<nat>. f m (s, s') \<le> (\<Squnion>n::\<nat>. f n (s, s')) - e"
    using linorder_not_less by blast
  then have sup_least: "(\<Squnion>n::\<nat>. f n (s, s')) \<le> (\<Squnion>n::\<nat>. f n (s, s')) - e"
    using SUP_least by metis
  have "(\<Squnion>n::\<nat>. f n (s, s')) \<ge> 0"
    using less_eq_ureal.rep_eq ureal2ereal zero_ureal.rep_eq by fastforce
  then have "(\<Squnion>n::\<nat>. f n (s, s')) > 0"
    using a2 by (metis Sup_upper linorder_not_le nle_le range_eqI)
  then show "false"
    using pos sup_least by (meson linorder_not_le ureal_minus_less)
qed

lemma increasing_chain_limit_exists_element':
  fixes f :: "nat \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun"
  assumes "increasing_chain f"
  assumes "\<exists>s. \<exists>n. f n s > 0"
  shows "\<forall>e > 0. \<exists>m. \<forall>s. f m s > (\<Squnion>n::\<nat>. f n s) - e"
  apply (rule ccontr)
  apply (auto)
proof -
  fix e
  assume pos: "(0::ureal) < e"
  assume a1: "\<forall>m::\<nat>. \<exists>(a::'s\<^sub>1) b::'s\<^sub>2. \<not> (\<Squnion>n::\<nat>. f n (a, b)) - e < f m (a, b)"

  have "\<exists>s\<^sub>m. \<forall>s. (\<Squnion>n::\<nat>. f n s\<^sub>m) - f m s\<^sub>m \<ge> (\<Squnion>n::\<nat>. f n s) - f m s"
    apply (auto)
    sorry

  from a1 have f1: "\<forall>m::\<nat>. \<exists> a b. f m (a, b) \<le> (\<Squnion>n::\<nat>. f n (a, b)) - e"
    using linorder_not_less by blast
  (*then have sup_least: "(\<Squnion>n::\<nat>. f n (s, s')) \<le> (\<Squnion>n::\<nat>. f n (s, s')) - e"
    using SUP_least by metis
  have "(\<Squnion>n::\<nat>. f n (s, s')) \<ge> 0"
    using less_eq_ureal.rep_eq ureal2ereal zero_ureal.rep_eq by fastforce
  then have "(\<Squnion>n::\<nat>. f n (s, s')) > 0"
    using assms(2) by (metis Sup_upper linorder_not_le nle_le range_eqI)
  then*) show "false"
    using pos sup_least by (meson linorder_not_le ureal_minus_less)
qed
*)

theorem increasing_chain_limit_is_lub:
  fixes f :: "nat \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun"
  assumes "increasing_chain f"
  (* We state the limits in real numbers because LIMSEQ_iff is only for type real_normed_vector,
  ureal is not of that type. *)
  shows "(\<lambda>n. ureal2real (f n (s, s'))) \<longlonglongrightarrow> (ureal2real (\<Squnion>n::\<nat>. f n (s, s')))"
proof (cases "\<exists>n. f n (s, s') > 0")
  case True
  show ?thesis
  apply (subst LIMSEQ_iff)
  apply (auto)
  proof -
    fix r
    assume a1: "(0::\<real>) < r"
    have sup_upper: "\<forall>n. ureal2real (f n (s, s')) - ureal2real (\<Squnion>n::\<nat>. f n (s, s')) \<le> 0"
      apply (auto)
      apply (rule ureal2real_mono)
      by (meson SUP_upper UNIV_I)
    then have dist_equal: "\<forall>n. \<bar>ureal2real (f n (s, s')) - ureal2real (\<Squnion>n::\<nat>. f n (s, s'))\<bar> = 
        ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f n (s, s'))"
      by auto
    from a1 have r_gt_0: "real2ureal r > 0"
      by (rule ureal_gt_zero)
    obtain m where P_m: "f m (s, s') > (\<Squnion>n::\<nat>. f n (s, s')) - real2ureal r"
      using r_gt_0 by (metis assms(1) True increasing_chain_limit_exists_element)
    have "\<exists>no::\<nat>. \<forall>n\<ge>no.  ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f n (s, s')) < r"
      apply (rule_tac x = "m" in exI)
      apply (auto)
    proof -
      fix n
      assume a2: "m \<le> n"
      then have "f m (s, s') \<le> f n (s, s')"
        by (metis assms(1) increasing_chain_mono le_fun_def)
      then have "(\<Squnion>n::\<nat>. f n (s, s')) - real2ureal r < f n (s, s')"
        using P_m by force
      then have "(\<Squnion>n::\<nat>. f n (s, s')) - (f n (s, s')) <
          (\<Squnion>n::\<nat>. f n (s, s')) - ((\<Squnion>n::\<nat>. f n (s, s')) - real2ureal r)"
        apply (rule ureal_minus_larger_less)
        by (meson SUP_upper UNIV_I)
      also have "... \<le> real2ureal r"
        by (metis nle_le ureal_minus_larger_zero_unit ureal_minus_less_diff)
      then have "(\<Squnion>n::\<nat>. f n (s, s')) - (f n (s, s')) < real2ureal r"
        using calculation by auto
      then have "ureal2real ((\<Squnion>n::\<nat>. f n (s, s')) - (f n (s, s'))) < ureal2real (real2ureal r)"
        using ureal2real_mono_strict by blast
      then have "ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f n (s, s')) < ureal2real (real2ureal r)"
        by (smt (verit, ccfv_threshold) ureal_minus_larger_than_real_minus)
      then show "ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f n (s, s')) < r"
        by (meson a1 less_eq_real_def order_less_le_trans ureal_real2ureal_smaller)
    qed
    then show "\<exists>no::\<nat>. \<forall>n\<ge>no. \<bar>ureal2real (f n (s, s')) - ureal2real (\<Squnion>n::\<nat>. f n (s, s'))\<bar> < r"
        using dist_equal by presburger
  qed
next
  case False
  then show ?thesis
    by (smt (verit, best) SUP_least bot.extremum bot_ureal.rep_eq eventually_sequentially 
        linorder_not_le nle_le tendsto_def ureal2ereal_inverse zero_ureal.rep_eq)
qed

theorem increasing_chain_limit_is_lub':
  fixes f :: "nat \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun"
  assumes "increasing_chain f"
  shows "\<forall>s s'. (\<lambda>n. ureal2real (f n (s, s'))) \<longlonglongrightarrow> (ureal2real (\<Squnion>n::\<nat>. f n (s, s')))"
  apply (auto)
  by (simp add: assms increasing_chain_limit_is_lub)

(*
term "\<Inter>"
lemma 
  assumes "A \<noteq> {}"
  shows "(\<Inter> m \<in> A. {n::nat. n \<ge> m}) = {n. \<forall>m\<in>A. n \<ge> m}"
  by blast

lemma nat_larger_exists:
  assumes "A \<noteq> {}"
  shows "\<exists>n::nat. \<forall>m \<in> A. n \<ge> m"
proof (rule ccontr, auto)
  assume "\<forall>n::\<nat>. \<exists>m::\<nat>\<in>A. \<not> m \<le> n"
  then have "\<forall>n::\<nat>. \<exists>m::\<nat>\<in>A.  m > n"
    by (simp add: linorder_not_le)
  then show "false"
    sorry
qed

lemma 
  assumes "A \<noteq> {}"
  shows "\<forall>s \<in> (\<Inter> m \<in> A. {n::nat. n \<ge> m}). (\<forall>m \<in> A. s \<in> {n::nat. n \<ge> m})"
  by blast

*)

lemma Inter_atLeast_not_empty_finite:
  assumes "A \<noteq> {}"
  assumes "finite A"
  shows "\<exists>n. \<forall>m \<in> A. n \<in> (\<lambda>m. {n::nat. n \<ge> m}) m"
  using assms(2) finite_nat_set_iff_bounded_le by auto

lemma Inter_atLeast_not_empty_finite':
  assumes "A \<noteq> {}"
  assumes "finite A"
  shows "\<exists>n. \<forall>m \<in> A. n \<in> {(m::nat)..}"
  using assms(2) finite_nat_set_iff_bounded_le by auto

(* This cannot be true because A may not have a greatest element.
lemma Inter_atLeast_not_empty':
  assumes "A \<noteq> {}"
  shows "\<exists>n::nat. \<forall>m \<in> A. n \<in> {(m::nat)..}"
  oops

lemma Inter_atLeast_not_empty:
  assumes "A \<noteq> {}"
  shows "\<exists>n. \<forall>m \<in> A. n \<in> {n::nat. n \<ge> m}"
  sorry
*)

lemma max_bounded_e:
  assumes "m \<in> A" "A \<noteq> {}" "finite A" "Max A \<le> n"
  shows "m \<le> n"
  by (meson Max.boundedE assms(1) assms(2) assms(3) assms(4))

text \<open> \<close>
theorem increasing_chain_limit_is_lub_all:
  fixes f :: "nat \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun"
  assumes "increasing_chain f"
  (* Suppose there are finite state pairs such that for each pair, it supreme is strictly larger than 
    its initial value. *)
  assumes "finite {s. ureal2real (\<Squnion>n::\<nat>. f n s) > ureal2real (f 0 s)}"
  shows "\<forall>r > 0::real. \<exists>no::nat. \<forall>n \<ge> no.
            \<forall>s s'. ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f n (s, s')) < r"
  apply (auto)
proof -
  fix r::"real"
  assume a1: "0 < r"
  have sup_upper: "\<forall>s s'. \<forall>n. ureal2real (f n (s, s')) - ureal2real (\<Squnion>n::\<nat>. f n (s, s')) \<le> 0"
    apply (auto)
    apply (rule ureal2real_mono)
    by (meson SUP_upper UNIV_I)
  then have dist_equal: "\<forall>s s'. \<forall>n. \<bar>ureal2real (f n (s, s')) - ureal2real (\<Squnion>n::\<nat>. f n (s, s'))\<bar> = 
      ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f n (s, s'))"
    by auto
  have limit_is_lub: "\<forall>s s'. (\<lambda>n. ureal2real (f n (s, s'))) \<longlonglongrightarrow> (ureal2real (\<Squnion>n::\<nat>. f n (s, s')))"
    by (simp add: assms increasing_chain_limit_is_lub)
  then have limit_is_lub_def: "\<forall>s s'. (\<exists>no::\<nat>. \<forall>n\<ge>no. norm (ureal2real (f n (s, s')) - ureal2real (\<Squnion>n::\<nat>. f n (s, s'))) < r)"
    using LIMSEQ_iff by (metis a1)
  then have limit_is_lub_def': "\<forall>s s'. \<exists>no::nat. \<forall>n \<ge> no. ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f n (s, s')) < r"
    by (simp add: dist_equal)

\<comment> \<open>The supreme of @{text "f"} is larger than its initial value @{text "f 0"} and the difference is at 
  least @{text "r"}. Therefore, a unique number @{text "no+1"} must exist such that @{text "f (no+1)"}
  inside the supreme minus @{text "r"} and @{text "f no"} outside the supreme minus @{text "r"}.
\<close>
  let ?P_larger_sup = "\<lambda>s s'. ((ureal2real (\<Squnion>n::\<nat>. f n (s, s')) > ureal2real (f 0 (s, s'))) \<and> 
      (ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f 0 (s, s'))) \<ge> r)"
  let ?P_mu_no = "\<lambda>s s'. \<lambda>no. (ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f (no+1) (s, s')) < r \<and> 
      ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f no (s, s')) \<ge> r)"
\<comment> \<open>The uniqueness is proved. \<close>
  have f_larger_supreme_unique_no: 
   "\<forall>s s'. ?P_larger_sup s s' \<longrightarrow> (\<exists>!no::nat. ?P_mu_no s s' no)"
    apply (auto)
    defer
    apply (smt (verit, best) assms(1) increasing_chain_mono le_fun_def nle_le not_less_eq_eq ureal2real_mono)
  proof -
    fix s s'
    assume a11: "ureal2real (f (0::\<nat>) (s, s')) < ureal2real (\<Squnion>n::\<nat>. f n (s, s'))"
    assume a12: "r \<le> ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f (0::\<nat>) (s, s'))"
    show "\<exists>no::\<nat>.
          ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f (Suc no) (s, s')) < r \<and>
          r \<le> ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f no (s, s'))"
      apply (rule ccontr, auto)
    proof -
      assume a110: "\<forall>no::\<nat>.
       ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f (Suc no) (s, s')) < r \<longrightarrow>
       \<not> r \<le> ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f no (s, s'))"
      then have f110: "\<forall>no::\<nat>.
       ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f (Suc no) (s, s')) < r \<longrightarrow>
       ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f no (s, s')) < r"
        by auto
      have f111: "\<exists>no::nat. ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f no (s, s')) < r"
        using limit_is_lub_def' by blast
      obtain no where P_no: "ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f no (s, s')) < r"
        using f111 by blast
      have "\<forall>m::nat. ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f (no - m) (s, s')) < r"
        apply (auto)
        apply (induct_tac m)
        using P_no minus_nat.diff_0 apply presburger
        by (smt (verit, best) Suc_diff_Suc a12 bot_nat_0.extremum f110 linorder_not_less nless_le 
              zero_less_diff)
      then have "ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f (no - no) (s, s')) < r"
        by blast
      then show "false"
        using a12 by force
    qed
  qed

\<comment> \<open>If @{text "f n"} is constant or @{text "f 0"} is inside the supreme minus @{text "r"}, then for 
  any number, the distance between @{text "f n"} and the supreme is less than @{text "r"}.\<close>
  have f_const_or_larger_dist_universal: "\<forall>s s'. 
      ((ureal2real (\<Squnion>n::\<nat>. f n (s, s')) = ureal2real (f 0 (s, s'))) \<or>
      (ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f 0 (s, s'))) < r)
      \<longrightarrow>
      (\<forall>no. ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f no (s, s')) < r)"
    apply (auto)
    apply (smt (verit) SUP_cong a1 assms(1) increasing_chain_sup_eq_f0_constant ureal2real_eq)
    by (smt (verit, best) assms(1) bot_nat_0.extremum increasing_chain_mono le_fun_def ureal2real_mono)

(*
  have f_const_or_larger_dist_universal': "\<forall>s s'. \<not> ?P_larger_sup s s'
      \<longrightarrow>
      (\<forall>no. ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f no (s, s')) < r)"
    apply (auto)
    apply (metis abs_ge_zero diff_ge_0_iff_ge dist_equal f_const_or_larger_dist_universal nless_le)
    using f_const_or_larger_dist_universal linorder_not_le by blast
*)

  let ?mu_no_set = "{THE no. ?P_mu_no s s' no | s s'. ?P_larger_sup s s'}"
\<comment> \<open>We use another form @{text "?mu_no_set1"} in order to prove it is finite more conveniently using 
 @{thm "finite_Collect_bounded_ex"}
\<close>
  let ?mu_no_set1 = "{THE no. ?P_mu_no (fst s) (snd s) no | s. ?P_larger_sup (fst s) (snd s)}"

  have mu_no_set_eq: "?mu_no_set = ?mu_no_set1"
    by auto

\<comment> \<open>A @{text "no"} is obtained as the maximum number of unique numbers for all states, and so for 
any number @{text "n \<ge> no"}, the distance between @{text "f n"} and the supreme is less than 
@{text "r"} for any state.
\<close>
  obtain no where P_no:
    "no = (if ?mu_no_set = {} then 0 else (Max ?mu_no_set + 1))"
    by blast

  have mu_no_set_rewrite: "?mu_no_set = (\<Union>(s, s') \<in> {(s, s'). ?P_larger_sup s s'}. 
      {uu. uu = (THE no::\<nat>. ?P_mu_no s s' no)})"
    by auto

  have f_larger_sup_finite: "finite {(s, s'). ?P_larger_sup s s'}"
  proof -
    have "{(s, s'). ?P_larger_sup s s'} \<subseteq> {s. ureal2real (\<Squnion>n::\<nat>. f n s) > ureal2real (f 0 s)}"
      by blast
    then show ?thesis
      using assms(2) rev_finite_subset by blast
  qed

  have "(\<forall>s s'. ?P_larger_sup s s' \<longrightarrow> finite {uu. uu = (THE no::\<nat>. ?P_mu_no s s' no)})"
    by simp

  have mu_no_set1_finite_iff: "(finite ?mu_no_set1) \<longleftrightarrow> (\<forall>s. ?P_larger_sup (fst s) (snd s) \<longrightarrow> 
        finite {uu. uu = (THE no. ?P_mu_no (fst s) (snd s) no)}) "
  proof -
    have "?mu_no_set1 = (\<Union>s\<in>{s. ?P_larger_sup (fst s) (snd s)}. 
            {uu. uu = (THE no. ?P_mu_no (fst s) (snd s) no)})"
      by auto
    with assms show ?thesis
      by simp
  qed

  then have mu_no_set1_finite: "finite ?mu_no_set1"
    by auto

  show "\<exists>no::\<nat>. \<forall>n\<ge>no. \<forall>(s::'s\<^sub>1) s'::'s\<^sub>2. ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f n (s, s')) < r"
    apply (rule_tac x = "no" in exI)
    apply (auto)
    apply (simp add: P_no)
  proof -
    fix n s s'
    assume a11: "(if \<forall>(s::'s\<^sub>1) s'::'s\<^sub>2.
              ureal2real (f (0::\<nat>) (s, s')) < ureal2real (\<Squnion>n::\<nat>. f n (s, s')) \<longrightarrow>
              \<not> r \<le> ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f (0::\<nat>) (s, s'))
        then 0::\<nat>
        else Max {uu::\<nat>. \<exists>(s::'s\<^sub>1) s'::'s\<^sub>2.
             uu = (THE no::\<nat>. ?P_mu_no s s' no) \<and>
             ?P_larger_sup s s'} + 1)
          \<le> n"

    show "ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f n (s, s')) < r"
    proof (cases "ureal2real (\<Squnion>n::\<nat>. f n (s, s')) = ureal2real (f 0 (s, s')) \<or> 
       \<not> r \<le> ureal2real (\<Squnion>n::\<nat>. f n (s, s')) - ureal2real (f (0::\<nat>) (s, s'))")
      case True
      then have "n \<ge> 0"
        by blast
      then show ?thesis
        using True f_const_or_larger_dist_universal by fastforce
    next
      case False
      then have max_leq_n: "(Max {uu::\<nat>. \<exists>(s::'s\<^sub>1) s'::'s\<^sub>2.
             uu = (THE no::\<nat>. ?P_mu_no s s' no) \<and> ?P_larger_sup s s'} + 1) \<le> n"
        by (smt (verit, ccfv_SIG) SUP_cong a1 a11)
      then have mu_no_in: "(THE no::\<nat>. ?P_mu_no s s' no) \<in> ?mu_no_set"
        apply (subst mem_Collect_eq)
        using False a1 by fastforce
      have mu_no_le_n: "(THE no::\<nat>. ?P_mu_no s s' no) \<le> n - 1"
        apply (rule max_bounded_e[where A = "?mu_no_set"])
        using mu_no_in apply blast
        using mu_no_in apply blast
        using mu_no_set1_finite mu_no_set_eq apply presburger
        using max_leq_n by (meson Nat.le_diff_conv2 add_leE)
      have P_mu_no: "?P_mu_no s s' (THE no::\<nat>. ?P_mu_no s s' no)"
        apply (rule theI')
        by (smt (verit, best) False Sup.SUP_cong f_larger_supreme_unique_no sup_upper)
      have "ureal2real (f ((THE no::\<nat>. ?P_mu_no s s' no) + (1::\<nat>)) (s, s')) \<le> ureal2real (f n (s,s'))"
        using mu_no_le_n by (metis (mono_tags, lifting) Nat.le_diff_conv2 add_leE assms(1) increasing_chain_mono le_fun_def max_leq_n ureal2real_mono)
      then show ?thesis
        using P_mu_no by linarith
    qed
  qed
qed


subsubsection \<open> Decreasing chains \<close>
theorem decreasing_chain_antitone:
  assumes "decreasing_chain f"
  assumes "m \<le> n"
  shows "f m \<ge> f n"
  using assms(1) assms(2) decreasing_chain_def by blast

theorem decreasing_chain_inf_eq_f0_constant:
  assumes "decreasing_chain f"
  assumes "(\<Sqinter>n::\<nat>. f n (s, s')) = f 0 (s, s')"
  shows "\<forall>n. f n (s, s') = f 0 (s, s')"
proof (rule ccontr)
  assume "\<not> (\<forall>n::\<nat>. f n (s, s') = f (0::\<nat>) (s, s'))"
  then have "\<exists>n. f n (s, s') \<noteq> f 0 (s, s')"
    by blast
  then have "\<exists>n. f n (s, s') < f 0 (s, s')"
    using decreasing_chain_antitone 
    by (metis assms(1) le_funE less_eq_nat.simps(1) order_neq_le_trans)
  then have "(\<Sqinter>n::\<nat>. f n (s, s')) < f 0 (s, s')"
    by (metis INF_lower assms(2) iso_tuple_UNIV_I less_le_not_le)
  then show "false"
    by (simp add: assms(2))
qed

lemma decreasing_chain_inf_subset_eq:
  assumes "decreasing_chain f"
  shows "(\<Sqinter>n::\<nat>. f (n + m)) = (\<Sqinter>n::\<nat>. f n)"
proof -
  have f1: "(\<Sqinter>n::nat. f (n + m)) = (\<Sqinter>n\<in>{m..}. f n)"
    apply (simp add: image_def)
    by (metis (no_types, lifting) add.commute add.right_neutral atLeast_0 atLeast_iff image_add_atLeast le_add_same_cancel2 rangeE zero_le)
  have f2: "{..m-1} \<union> {(m::nat)..} = UNIV"
    by (metis Suc_pred' atLeast0LessThan atLeast_0 bot_nat_0.extremum bot_nat_0.not_eq_extremum ivl_disj_un_one(8) lessThan_Suc_atMost ref_lattice.inf_bot_right)
  then have f3: "(\<Sqinter>n::nat. f n) = (\<Sqinter>n::nat \<in> {..m-1} \<union> {(m::nat)..}. f n)"
    by (simp add: image_def)
  have f4: "(\<Sqinter>n::nat \<in> {..m-1} \<union> {(m::nat)..}. f n) = (\<Sqinter>n\<in>{..m-1}. f n) \<sqinter> (\<Sqinter>n\<in>{m..}. f n)"
    apply (subst INF_union)
    by blast
  have f5: "(\<Sqinter>n\<in>{m..}. f n) \<le> (\<Sqinter>n\<in>{..m-1}. f n)"
    apply (rule INF_greatest)
    by (metis INF_lower add.commute assms atLeast_iff bot_nat_0.extremum decreasing_chain_antitone le_add_same_cancel2 order_trans)
  then have f6: "(\<Sqinter>n\<in>{..m-1}. f n) \<sqinter> (\<Sqinter>n\<in>{m..}. f n) = (\<Sqinter>n\<in>{m..}. f n)"
    apply (subst (asm) le_iff_inf)
    by (simp add: inf_commute)
  show ?thesis
    using f1 f3 f4 f6 by presburger
qed

lemma decreasing_chain_limit_exists_element:
  fixes f :: "nat \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun"
  assumes "decreasing_chain f"
  assumes "\<exists>n. f n (s, s') < 1"
  shows "\<forall> e > 0. \<exists>m. f m (s, s') < (\<Sqinter>n::\<nat>. f n (s, s')) + e"
  apply (rule ccontr)
  apply (auto)
proof -
  fix e
  assume pos: "(0::ureal) < e"
  assume a1: "\<forall>m::\<nat>. \<not> f m (s, s') < (\<Sqinter>n::\<nat>. f n (s, s')) + e"

  from a1 have "\<forall>m::\<nat>. f m (s, s') \<ge> (\<Sqinter>n::\<nat>. f n (s, s')) + e"
    by (meson linorder_not_le)
  then have inf_greatest: "(\<Sqinter>n::\<nat>. f n (s, s')) + e \<le> (\<Sqinter>n::\<nat>. f n (s, s'))"
    using INF_greatest by metis
  have "(\<Sqinter>n::\<nat>. f n (s, s')) \<le> 1"
    by (metis one_ureal.rep_eq top_greatest top_ureal.rep_eq ureal2ereal_inject)
  then have "(\<Sqinter>n::\<nat>. f n (s, s')) < 1"
    using assms(2) by (metis INF_lower UNIV_I linorder_not_less order_le_less)
  then show "false"
    using pos inf_greatest by (meson linorder_not_le ureal_plus_greater)
qed

theorem decreasing_chain_limit_is_glb:
  fixes f :: "nat \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun"
  assumes "decreasing_chain f"
  shows "(\<lambda>n. ureal2real (f n (s, s'))) \<longlonglongrightarrow> (ureal2real (\<Sqinter>n::\<nat>. f n (s, s')))"
proof (cases "\<exists>n. f n (s, s') < 1")
  case True
  show ?thesis
  apply (subst LIMSEQ_iff)
  apply (auto)
  proof -
    fix r
    assume a1: "(0::\<real>) < r"
    have sup_upper: "\<forall>n. ureal2real (f n (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) \<ge> 0"
      apply (auto)
      apply (rule ureal2real_mono)
      by (meson INF_lower UNIV_I)
    then have dist_equal: "\<forall>n. \<bar>ureal2real (f n (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s'))\<bar> = 
        ureal2real (f n (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s'))"
      by auto
    from a1 have r_gt_0: "real2ureal r > 0"
      by (rule ureal_gt_zero)
    obtain m where P_m: "f m (s, s') < (\<Sqinter>n::\<nat>. f n (s, s')) + real2ureal r"
      using r_gt_0 by (metis assms(1) True decreasing_chain_limit_exists_element)
    have "\<exists>no::\<nat>. \<forall>n\<ge>no.  ureal2real (f n (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < r"
      apply (rule_tac x = "m" in exI)
      apply (auto)
    proof -
      fix n
      assume a2: "m \<le> n"
      then have "f m (s, s') \<ge> f n (s, s')"
        by (metis assms(1) decreasing_chain_antitone le_fun_def)
      then have "f n (s, s') < (\<Sqinter>n::\<nat>. f n (s, s')) + real2ureal r"
        using P_m by force
      then have "(f n (s, s')) - (\<Sqinter>n::\<nat>. f n (s, s')) <
          ((\<Sqinter>n::\<nat>. f n (s, s')) + real2ureal r) - (\<Sqinter>n::\<nat>. f n (s, s'))"
        apply (subst ureal_larger_minus_greater)
        apply (meson INF_lower UNIV_I)
        apply meson
        by simp
      also have "... \<le> real2ureal r"
        by (metis linorder_not_le nle_le ureal_plus_eq_1_minus_less ureal_plus_less_1_unit)
      then have "(f n (s, s')) - (\<Sqinter>n::\<nat>. f n (s, s')) < real2ureal r"
        using calculation by auto
      then have "ureal2real ((f n (s, s')) - (\<Sqinter>n::\<nat>. f n (s, s'))) < ureal2real (real2ureal r)"
        by (rule ureal2real_mono_strict)
      then have "ureal2real (f n (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < ureal2real (real2ureal r)"
        by (smt (verit, ccfv_threshold) ureal_minus_larger_than_real_minus)
      then show "ureal2real (f n (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < r"
        by (meson a1 less_eq_real_def order_less_le_trans ureal_real2ureal_smaller)
    qed
    then show "\<exists>no::\<nat>. \<forall>n\<ge>no. \<bar>ureal2real (f n (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s'))\<bar> < r"
        using dist_equal by presburger
  qed
next
  case False
  then have "\<forall>n::\<nat>. f n (s::'s\<^sub>1, s'::'s\<^sub>2) = (1::ureal)"
    by (metis antisym_conv2 one_ureal.rep_eq top_greatest top_ureal.rep_eq ureal2ereal_inject)
  then show ?thesis
    by force
qed

theorem decreasing_chain_limit_is_lub_all:
  fixes f :: "nat \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun"
  assumes "decreasing_chain f"
  assumes "finite {s. ureal2real (\<Sqinter> n::\<nat>. f n s) < ureal2real (f 0 s)}"
  shows "\<forall>r > 0::real. \<exists>no::nat. \<forall>n \<ge> no.
            \<forall>s s'. ureal2real (f n (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < r"
  apply (auto)
proof -
  fix r::"real"
  assume a1: "0 < r"
  have sup_upper: "\<forall>s s'. \<forall>n. ureal2real (f n (s, s')) \<ge> ureal2real (\<Sqinter>v::\<nat>. f n (s, s'))"
    by (auto)
  then have dist_equal: "\<forall>s s'. \<forall>n. \<bar>ureal2real (f n (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s'))\<bar> = 
      ureal2real (f n (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s'))"
    by (simp add: Inf_lower ureal2real_mono)
  have limit_is_glb: "\<forall>s s'. (\<lambda>n. ureal2real (f n (s, s'))) \<longlonglongrightarrow> (ureal2real (\<Sqinter>n::\<nat>. f n (s, s')))"
    by (simp add: assms decreasing_chain_limit_is_glb)
  then have limit_is_glb_def: "\<forall>s s'. (\<exists>no::\<nat>. \<forall>n\<ge>no. norm (ureal2real (f n (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s'))) < r)"
    using LIMSEQ_iff by (metis a1)
  then have limit_is_glb_def': "\<forall>s s'. \<exists>no::nat. \<forall>n \<ge> no. ureal2real (f n (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < r"
    by (simp add: dist_equal)

\<comment> \<open>The infimum of @{text "f"} is less than its initial value @{text "f 0"} and the difference is at 
  least @{text "r"}. Therefore, a unique number @{text "no+1"} must exist such that @{text "f (no+1)"}
  inside the supreme minus @{text "r"} and @{text "f no"} outside the supreme minus @{text "r"}.
\<close>
  let ?P_less_inf = "\<lambda>s s'. ((ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < ureal2real (f 0 (s, s'))) \<and> 
      (ureal2real (f 0 (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s'))) \<ge> r)"
  let ?P_mu_no = "\<lambda>s s'. \<lambda>no. (ureal2real (f (no+1) (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < r \<and> 
      ureal2real (f no (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) \<ge> r)"
\<comment> \<open>The uniqueness is proved. \<close>
  have f_larger_supreme_unique_no: 
   "\<forall>s s'. ?P_less_inf s s' \<longrightarrow> (\<exists>!no::nat. ?P_mu_no s s' no)"
    apply (auto)
    defer
    apply (smt (verit, best) assms(1) decreasing_chain_antitone le_fun_def nle_le not_less_eq_eq ureal2real_mono)
  proof -
    fix s s'
    assume a11: "ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < ureal2real (f (0::\<nat>) (s, s'))"
    assume a12: "r \<le> ureal2real (f (0::\<nat>) (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s'))"
    show "\<exists>no::\<nat>.
          ureal2real (f (Suc no) (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < r \<and>
          r \<le> ureal2real (f no (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s'))"
      apply (rule ccontr, auto)
    proof -
      assume a110: "\<forall>no::\<nat>.
       ureal2real (f (Suc no) (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < r \<longrightarrow>
       \<not> r \<le> ureal2real (f no (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s'))"
      then have f110: "\<forall>no::\<nat>.
       ureal2real (f (Suc no) (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < r \<longrightarrow>
       ureal2real (f no (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < r"
        by auto
      have f111: "\<exists>no::nat. ureal2real (f no (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < r"
        using limit_is_glb_def' by blast
      obtain no where P_no: "ureal2real (f no (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < r"
        using f111 by blast
      have "\<forall>m::nat. ureal2real (f (no - m) (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < r"
        apply (auto)
        apply (induct_tac m)
        using P_no apply simp
        by (metis Suc_diff_Suc a12 diff_is_0_eq f110 linorder_not_less)
      then have "ureal2real (f (no - no) (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < r"
        by blast
      then show "false"
        using a12 by simp
    qed
  qed

\<comment> \<open>If @{text "f n"} is constant or @{text "f 0"} is inside the infimum minus @{text "r"}, then for 
  any number, the distance between @{text "f n"} and the infimum is less than @{text "r"}.\<close>
  have f_const_or_larger_dist_universal: "\<forall>s s'. 
      ((ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) = ureal2real (f 0 (s, s'))) \<or>
      (ureal2real (f 0 (s, s'))) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < r)
      \<longrightarrow>
      (\<forall>no. (ureal2real (f no (s, s'))) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < r)"
    apply (auto)
    apply (smt (verit, ccfv_threshold) Sup.SUP_cong a1 assms(1) decreasing_chain_inf_eq_f0_constant ureal2real_eq)
    by (smt (verit, ccfv_SIG) assms(1) decreasing_chain_antitone le_fun_def less_eq_nat.simps(1) ureal2real_mono)

  let ?mu_no_set = "{THE no. ?P_mu_no s s' no | s s'. ?P_less_inf s s'}"
\<comment> \<open>We use another form @{text "?mu_no_set1"} in order to prove it is finite more conveniently using 
 @{thm "finite_Collect_bounded_ex"}
\<close>
  let ?mu_no_set1 = "{THE no. ?P_mu_no (fst s) (snd s) no | s. ?P_less_inf (fst s) (snd s)}"

  have mu_no_set_eq: "?mu_no_set = ?mu_no_set1"
    by auto

\<comment> \<open>A @{text "no"} is obtained as the maximum number of unique numbers for all states, and so for 
any number @{text "n \<ge> no"}, the distance between @{text "f n"} and the supreme is less than 
@{text "r"} for any state.
\<close>
  obtain no where P_no:
    "no = (if ?mu_no_set = {} then 0 else (Max ?mu_no_set + 1))"
    by blast

  have mu_no_set_rewrite: "?mu_no_set = (\<Union>(s, s') \<in> {(s, s'). ?P_less_inf s s'}. 
      {uu. uu = (THE no::\<nat>. ?P_mu_no s s' no)})"
    by auto

  have f_less_inf_finite: "finite {(s, s'). ?P_less_inf s s'}"
  proof -
    have "{(s, s'). ?P_less_inf s s'} \<subseteq> {s. ureal2real (\<Sqinter>n::\<nat>. f n s) < ureal2real (f 0 s)}"
      by blast
    then show ?thesis
      using assms(2) rev_finite_subset by blast
  qed

  have "(\<forall>s s'. ?P_less_inf s s' \<longrightarrow> finite {uu. uu = (THE no::\<nat>. ?P_mu_no s s' no)})"
    by simp

  have mu_no_set1_finite_iff: "(finite ?mu_no_set1) \<longleftrightarrow> (\<forall>s. ?P_less_inf (fst s) (snd s) \<longrightarrow> 
        finite {uu. uu = (THE no. ?P_mu_no (fst s) (snd s) no)}) "
  proof -
    have "?mu_no_set1 = (\<Union>s\<in>{s. ?P_less_inf (fst s) (snd s)}. 
            {uu. uu = (THE no. ?P_mu_no (fst s) (snd s) no)})"
      by auto
    with assms show ?thesis
      by simp
  qed

  then have mu_no_set1_finite: "finite ?mu_no_set1"
    by auto

  show "\<exists>no::\<nat>. \<forall>n\<ge>no. \<forall>(s::'s\<^sub>1) s'::'s\<^sub>2. ureal2real (f n (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < r"
    apply (rule_tac x = "no" in exI)
    apply (auto)
    apply (simp add: P_no)
  proof -
    fix n s s'
    assume a11: "(if \<forall>(s::'s\<^sub>1) s'::'s\<^sub>2.
              ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < ureal2real (f (0::\<nat>) (s, s')) \<longrightarrow>
              \<not> r \<le> ureal2real (f (0::\<nat>) (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s'))
        then 0::\<nat>
        else Max {uu::\<nat>. \<exists>(s::'s\<^sub>1) s'::'s\<^sub>2.
             uu = (THE no::\<nat>. ?P_mu_no s s' no) \<and>
             ?P_less_inf s s'} + 1)
          \<le> n"

    show "ureal2real (f n (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) < r"
    proof (cases "ureal2real (\<Sqinter>n::\<nat>. f n (s, s')) = ureal2real (f 0 (s, s')) \<or> 
       \<not> r \<le> ureal2real (f (0::\<nat>) (s, s')) - ureal2real (\<Sqinter>n::\<nat>. f n (s, s'))")
      case True
      then have "n \<ge> 0"
        by blast
      then show ?thesis
        using True f_const_or_larger_dist_universal by fastforce
    next
      case False
      then have max_leq_n: "(Max {uu::\<nat>. \<exists>(s::'s\<^sub>1) s'::'s\<^sub>2.
             uu = (THE no::\<nat>. ?P_mu_no s s' no) \<and> ?P_less_inf s s'} + 1) \<le> n"
        by (smt (verit) Sup.SUP_cong a1 a11)
      then have mu_no_in: "(THE no::\<nat>. ?P_mu_no s s' no) \<in> ?mu_no_set"
        apply (subst mem_Collect_eq)
        using False a1 by fastforce
      have mu_no_le_n: "(THE no::\<nat>. ?P_mu_no s s' no) \<le> n - 1"
        apply (rule max_bounded_e[where A = "?mu_no_set"])
        using mu_no_in apply blast
        using mu_no_in apply blast
        using mu_no_set1_finite mu_no_set_eq apply presburger
        using max_leq_n by (meson Nat.le_diff_conv2 add_leE)
      have P_mu_no: "?P_mu_no s s' (THE no::\<nat>. ?P_mu_no s s' no)"
        apply (rule theI')
        using False a1 f_larger_supreme_unique_no by auto
      have "ureal2real (f ((THE no::\<nat>. ?P_mu_no s s' no) + (1::\<nat>)) (s, s')) \<ge> ureal2real (f n (s,s'))"
        using mu_no_le_n 
        by (smt (verit, best) Nat.le_diff_conv2 add_leD2 assms(1) decreasing_chain_antitone le_fun_def max_leq_n ureal2real_mono)
      then show ?thesis
        using P_mu_no by linarith
    qed
  qed
qed

subsection \<open> While loop \<close>
term "\<lambda>X. (if\<^sub>c b then (P ; X) else II)"
term "Inf"

print_locale "ord"
print_locale "order"
print_locale "lattice"
print_locale "bot"
print_locale "complete_lattice"

theorem Fwhile_mono:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  shows "mono (Fwhile b P)"
  apply (simp add: mono_def Fwhile_def)
  apply (auto)
  apply (subst prfun_pcond_mono)
  apply (subst prfun_pseqcomp_mono)
  apply (auto)
  by (simp add: assms pdrfun_product_summable'')+

theorem Fwhile_monoE:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  assumes "X \<le> Y"
  shows "Fwhile b P X \<le> Fwhile b P Y"
  by (simp add: Fwhile_mono assms(1) assms(2) monoD)
                                               
theorem mono_func_increasing_chain_is_increasing:
  assumes "increasing_chain c"
  assumes "mono F"
  shows "increasing_chain (\<lambda>n. F (c n))"
  apply (simp add: increasing_chain_def)
  using assms by (simp add: increasing_chain_mono monoD)

theorem mono_func_decreasing_chain_is_decreasing:
  assumes "decreasing_chain c"
  assumes "mono F"
  shows "decreasing_chain (\<lambda>n. F (c n))"
  apply (simp add: decreasing_chain_def)
  using assms by (simp add: decreasing_chain_antitone monoD)

lemma Fwhile_minus_distr:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  assumes "is_final_prob (rvfun_of_prfun (X::('s, 's) prfun))"
  assumes "is_final_prob (rvfun_of_prfun (Y::('s, 's) prfun))"
  assumes "X \<ge> Y"
  shows "(rvfun_of_prfun (Fwhile b P X) - rvfun_of_prfun (Fwhile b P Y)) = 
    ((\<lbrakk>b\<rbrakk>\<^sub>\<I>) * @(rvfun_of_prfun ((P ; (X - Y)))))\<^sub>e" (is "?lhs = ?rhs")
  apply (subst fun_eq_iff, auto)
proof -
  fix s s'
  let ?lhs = "rvfun_of_prfun (Fwhile b P X) (s, s') - rvfun_of_prfun (Fwhile b P Y) (s, s')"
  have f1: "rvfun_of_prfun (prfun_of_rvfun [\<lambda>\<s>::'s \<times> 's.
           (\<lbrakk>b\<rbrakk>\<^sub>\<I>) \<s> * rvfun_of_prfun (P ; X) \<s> + (\<lbrakk>[\<lambda>\<s>::'s \<times> 's. \<not> b \<s>]\<^sub>e\<rbrakk>\<^sub>\<I>) \<s> * rvfun_of_prfun II \<s>]\<^sub>e) (s, s') 
    = rvfun_of_prfun (prfun_of_rvfun  [\<lambda>\<s>::'s \<times> 's. (\<lbrakk>b\<rbrakk>\<^sub>\<I>) \<s> * rvfun_of_prfun (P ; X) \<s>]\<^sub>e) (s, s') + 
      rvfun_of_prfun (prfun_of_rvfun  [\<lambda>\<s>::'s \<times> 's. (\<lbrakk>[\<lambda>\<s>::'s \<times> 's. \<not> b \<s>]\<^sub>e\<rbrakk>\<^sub>\<I>) \<s> * rvfun_of_prfun II \<s>]\<^sub>e)(s, s')"
    by (smt (verit) SEXP_def iverson_bracket_def mult_cancel_left2 prfun_in_0_1' prfun_of_rvfun_def 
        rvfun_of_prfun_def ureal_real2ureal_smaller)
    
  have f2: "rvfun_of_prfun (prfun_of_rvfun [\<lambda>\<s>::'s \<times> 's.
           (\<lbrakk>b\<rbrakk>\<^sub>\<I>) \<s> * rvfun_of_prfun (P ; Y) \<s> + (\<lbrakk>[\<lambda>\<s>::'s \<times> 's. \<not> b \<s>]\<^sub>e\<rbrakk>\<^sub>\<I>) \<s> * rvfun_of_prfun II \<s>]\<^sub>e) (s, s') 
    = rvfun_of_prfun (prfun_of_rvfun  [\<lambda>\<s>::'s \<times> 's. (\<lbrakk>b\<rbrakk>\<^sub>\<I>) \<s> * rvfun_of_prfun (P ; Y) \<s>]\<^sub>e) (s, s') + 
      rvfun_of_prfun (prfun_of_rvfun  [\<lambda>\<s>::'s \<times> 's. (\<lbrakk>[\<lambda>\<s>::'s \<times> 's. \<not> b \<s>]\<^sub>e\<rbrakk>\<^sub>\<I>) \<s> * rvfun_of_prfun II \<s>]\<^sub>e)(s, s')"
    apply (simp add: prfun_of_rvfun_def)
    by (smt (verit) SEXP_def iverson_bracket_def mult_cancel_left2 prfun_in_0_1' prfun_of_rvfun_def 
        rvfun_of_prfun_def ureal_real2ureal_smaller)
  
  have f3: "?lhs = rvfun_of_prfun (prfun_of_rvfun  [\<lambda>\<s>::'s \<times> 's. (\<lbrakk>b\<rbrakk>\<^sub>\<I>) \<s> * rvfun_of_prfun (P ; X) \<s>]\<^sub>e) (s, s') -
    rvfun_of_prfun (prfun_of_rvfun  [\<lambda>\<s>::'s \<times> 's. (\<lbrakk>b\<rbrakk>\<^sub>\<I>) \<s> * rvfun_of_prfun (P ; Y) \<s>]\<^sub>e) (s, s')"
    apply (simp add: Fwhile_def) 
    apply (simp add: prfun_pcond_altdef)
    using f1 f2 by simp

  have f4: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. rvfun_of_prfun P (s, v\<^sub>0) * rvfun_of_prfun X (v\<^sub>0, s')) -
    (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. rvfun_of_prfun P (s, v\<^sub>0) * rvfun_of_prfun Y (v\<^sub>0, s')) = 
    (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. rvfun_of_prfun P (s, v\<^sub>0) * rvfun_of_prfun X (v\<^sub>0, s')) +
    (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. - (rvfun_of_prfun P (s, v\<^sub>0) * rvfun_of_prfun Y (v\<^sub>0, s')))"
    apply (subst infsum_uminus)
    by auto
  also have f5: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. rvfun_of_prfun P (s, v\<^sub>0) * rvfun_of_prfun X (v\<^sub>0, s') + 
    (- (rvfun_of_prfun P (s, v\<^sub>0) * rvfun_of_prfun Y (v\<^sub>0, s'))))"
    apply (subst infsum_add)
    apply (simp add: assms(1) is_final_dist_subdist rvfun_product_summable ureal_is_prob)
    apply (subst summable_on_uminus)
     apply (simp add: assms(1) is_final_dist_subdist rvfun_product_summable ureal_is_prob)
    by auto
  also have f6: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. rvfun_of_prfun P (s, v\<^sub>0) * (rvfun_of_prfun X (v\<^sub>0, s') - rvfun_of_prfun Y (v\<^sub>0, s')))"
    by (metis (mono_tags, opaque_lifting) ab_group_add_class.ab_diff_conv_add_uminus right_diff_distrib')
  also have f7: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. rvfun_of_prfun P (s, v\<^sub>0) * (rvfun_of_prfun (X-Y) (v\<^sub>0, s')))"
    using prfun_minus_distribution by (metis (mono_tags, opaque_lifting) assms(4) minus_apply)

  show "rvfun_of_prfun (Fwhile b P X) (s, s') - rvfun_of_prfun (Fwhile b P Y) (s, s') =
       (\<lbrakk>b\<rbrakk>\<^sub>\<I>) (s, s') * rvfun_of_prfun (P ; (X - Y)) (s, s')"
    apply (simp add: f3)
    (* apply (simp add: prfun_of_rvfun_def rvfun_of_prfun_def) *)
    apply (simp add: pfun_defs)
    apply (subst rvfun_seqcomp_inverse)
    apply (simp add: assms(1))
    apply (simp add: ureal_is_prob)
    apply (subst rvfun_seqcomp_inverse)
    apply (simp add: assms(1))
    apply (simp add: ureal_is_prob)
    apply (subst rvfun_seqcomp_inverse)
    apply (simp add: assms(1))
    apply (simp add: ureal_is_prob)
    apply (subst rvfun_inverse)
    apply (simp add: dist_defs)
    apply (expr_auto)
    apply (simp add: infsum_nonneg prfun_in_0_1')
    using rvfun_product_prob_dist_leq_1 assms(1) ureal_is_prob apply fastforce
    apply (subst rvfun_inverse)
    apply (simp add: dist_defs)
    apply (expr_auto)
    apply (simp add: infsum_nonneg prfun_in_0_1')
    using rvfun_product_prob_dist_leq_1 assms(1) ureal_is_prob apply fastforce
    apply (expr_auto)
    using calculation f7 by presburger
qed

lemma Fwhile_minus_distr':
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  assumes "is_final_prob (rvfun_of_prfun (X::('s, 's) prfun))"
  assumes "is_final_prob (rvfun_of_prfun (Y::('s, 's) prfun))"
  assumes "X \<ge> Y"
  shows "(ureal2real (Fwhile b P X (s,s')) - ureal2real (Fwhile b P Y (s,s'))) = 
    (\<lbrakk>b\<rbrakk>\<^sub>\<I>) (s,s') * ureal2real ((P ; (X - Y)) (s,s'))" (is "?lhs = ?rhs")
proof -
  have "(rvfun_of_prfun (Fwhile b P X) - rvfun_of_prfun (Fwhile b P Y)) = 
    ((\<lbrakk>b\<rbrakk>\<^sub>\<I>) * @(rvfun_of_prfun ((P ; (X - Y)))))\<^sub>e"
    using Fwhile_minus_distr assms(1) assms(2) assms(3) assms(4) by blast
  then have "(ureal2real (Fwhile b P X (s,s')) - ureal2real (Fwhile b P Y (s,s'))) = 
    (\<lbrakk>b\<rbrakk>\<^sub>\<I>) (s,s') * ureal2real ((P ; (X - Y)) (s,s'))"
    using rvfun_of_prfun_def by (smt (verit, del_insts) SEXP_def fun_diff_def)
  then show ?thesis
    by simp
qed

(*
lemma fzero_zero: "prfun_of_rvfun (rvfun_of_prfun \<^bold>0) = \<^bold>0"
  apply (simp add: ureal_defs)
  by (metis SEXP_def max.idem min.absorb1 real_of_ereal_0 ureal2ereal_inverse zero_ereal_def 
      zero_less_one_ereal zero_ureal.rep_eq)
*)

theorem pwhile_unfold:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  shows "while\<^sub>p b do P od = (if\<^sub>c b then (P ; (while\<^sub>p b do P od)) else II)"
proof -
  have m:"mono (\<lambda>X. (if\<^sub>c b then (P ; X) else II))"
    apply (simp add: mono_def, auto)
    apply (subst prfun_pcond_mono)
    apply (subst prfun_pseqcomp_mono)
    apply (auto)
    by (simp add: assms pdrfun_product_summable'')+
  have "(while\<^sub>p b do P od) = (\<mu>\<^sub>p X \<bullet> (if\<^sub>c b then (P ; X) else II))"
    by (simp add: pwhile_def Fwhile_def)
  also have "... = ((if\<^sub>c b then (P ; (\<mu>\<^sub>p X \<bullet> (if\<^sub>c b then (P ; X) else II))) else II))"
    apply (subst lfp_unfold)
    apply (simp add: m)
    by (simp add: lfp_const)
  also have "... = (if\<^sub>c b then (P ; (while\<^sub>p b do P od)) else II)"
    by (simp add: pwhile_def Fwhile_def)
  finally show ?thesis .
qed

theorem pwhile_false: 
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  shows "while\<^sub>p (false)\<^sub>e do P od = II"
  apply (subst pwhile_unfold)
  using assms apply presburger
  apply (simp add: pfun_defs)
  apply (expr_auto)
  apply (simp add: ureal_defs)
  apply (auto)
  apply (simp add: ereal2ureal'_inverse)
  by (metis ereal2ureal_def real_of_ereal_0 ureal2ereal_inverse zero_ereal_def zero_ureal.rep_eq zero_ureal_def)

theorem pwhile_true: "while\<^sub>p (true)\<^sub>e do P od = 0\<^sub>p"
  apply (simp add: pwhile_def pcond_def pzero_def)
  apply (rule antisym)
  apply (rule lfp_lowerbound)
  apply (simp add: Fwhile_def)
  apply (simp add: prfun_zero_right)
  apply (simp add: pfun_defs)
  apply (simp add: ureal_zero ureal_zero')
  by (rule ureal_bottom_least)

theorem pwhile_top_unfold:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  shows "while\<^sub>p\<^sup>\<top> b do P od = (if\<^sub>c b then (P ; (while\<^sub>p\<^sup>\<top> b do P od)) else II)"
proof -
  have m:"mono (\<lambda>X. (if\<^sub>c b then (P ; X) else II))"
    apply (simp add: mono_def, auto)
    apply (subst prfun_pcond_mono)
    apply (subst prfun_pseqcomp_mono)
    apply (auto)
    by (simp add: assms pdrfun_product_summable'')+
  have "(while\<^sub>p\<^sup>\<top> b do P od) = (\<nu>\<^sub>p X \<bullet> (if\<^sub>c b then (P ; X) else II))"
    by (simp add: pwhile_top_def Fwhile_def)
  also have "... = ((if\<^sub>c b then (P ; (\<nu>\<^sub>p X \<bullet> (if\<^sub>c b then (P ; X) else II))) else II))"
    apply (subst gfp_unfold)
    apply (simp add: m)
    by (simp add: lfp_const)
  also have "... = (if\<^sub>c b then (P ; (while\<^sub>p\<^sup>\<top> b do P od)) else II)"
    by (simp add: pwhile_top_def Fwhile_def)
  finally show ?thesis .
qed

theorem pwhile_top_false: 
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  shows "while\<^sub>p\<^sup>\<top> (false)\<^sub>e do P od = II"
  apply (subst pwhile_top_unfold)
  using assms apply presburger
  apply (simp add: pfun_defs)
  apply (expr_auto)
  apply (simp add: ureal_defs)
  apply (auto)
  apply (simp add: ereal2ureal'_inverse)
  by (metis ereal2ureal_def real_of_ereal_0 ureal2ereal_inverse zero_ereal_def zero_ureal.rep_eq zero_ureal_def)

theorem pwhile_top_true: "while\<^sub>p\<^sup>\<top> (true)\<^sub>e do P od = (\<nu>\<^sub>p X \<bullet> P ; X)"
  apply (simp add: pwhile_top_def)
  apply (simp add: Fwhile_def)
  apply (simp add: pcond_def)
  by (simp add: SEXP_def prfun_inverse)

subsubsection \<open> Iteration \<close>
text \<open> Can we use approximation chain in UTP (Ch. 2.7) to prove a unique fix point for a probabilistic 
iteration?
\<close>
lemma "iterate 0 b P 0\<^sub>p = 0\<^sub>p"
  by simp

lemma "iterate 0 b P 1\<^sub>p = 1\<^sub>p"
  by simp

lemma iterate_mono:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  shows "monotone (\<le>) (\<le>) (iterate n b P)"
  unfolding monotone_def apply (auto)
  apply (induction n)
   apply (auto)
  by (metis Fwhile_mono assms monoE)

lemma iterate_monoE:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  assumes "X \<le> Y"
  shows "(iterate n b P X) \<le> (iterate n b P Y)"
  by (metis assms(1) assms(2) iterate_mono monotone_def)

lemma iterate_increasing:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  shows "(iterate n b P 0\<^sub>p) \<le> (iterate (Suc n) b P 0\<^sub>p)"
  apply (induction n)
  apply (simp)
  using ureal_bottom_least' apply blast
  apply (simp)
  apply (subst Fwhile_monoE)
  by (simp add: assms)+

lemma iterate_increasing1:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  shows "(iterate n b P 0\<^sub>p) \<le> (iterate (n+m) b P 0\<^sub>p)"
  apply (induction m)
  apply (simp)
  by (metis (full_types) assms add_Suc_right dual_order.trans iterate_increasing)

lemma iterate_increasing2:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  assumes "n \<le> m"
  shows "(iterate n b P 0\<^sub>p) \<le> (iterate m b P 0\<^sub>p)"
  using iterate_increasing1 assms nat_le_iff_add by auto

lemma iterate_increasing_chain_bot:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  shows "Complete_Partial_Order.chain (\<le>) {(iterate n b P 0\<^sub>p) | n::nat. True}" 
    (is "Complete_Partial_Order.chain _ ?C")
proof (rule chainI)
  fix x y
  assume "x \<in> ?C" "y \<in> ?C"
  then show "x \<le> y \<or> y \<le> x"
    by (smt (verit) assms iterate_increasing2 mem_Collect_eq nle_le)
qed

lemma iterate_increasing_chain:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  shows "increasing_chain (\<lambda>n. (iterate n b P 0\<^sub>p))" 
    (is "increasing_chain ?C")
  apply (simp add: increasing_chain_def)
  by (simp add: assms iterate_increasing2)


lemma iterate_decreasing:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  shows "(iterate n b P 1\<^sub>p) \<ge> (iterate (Suc n) b P 1\<^sub>p)"
  apply (induction n)
  apply (metis le_fun_def linorder_not_le o_def one_ureal.rep_eq pone_def real_ereal_1 ureal2real_def 
      ureal2real_mono_strict ureal_upper_bound utp_prob_rel_lattice.iterate.simps(1))
  by (simp add: Fwhile_monoE assms)

lemma iterate_decreasing1:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  shows "(iterate n b P 1\<^sub>p) \<ge> (iterate (n+m) b P 1\<^sub>p)"
  apply (induction m)
  apply (simp)
  by (metis (no_types, opaque_lifting) assms gfp.leq_trans iterate_decreasing nat_arith.suc1)

lemma iterate_decreasing2:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  assumes "n \<le> m"
  shows "(iterate n b P 1\<^sub>p) \<ge> (iterate m b P 1\<^sub>p)"
  using iterate_decreasing1 assms using nat_le_iff_add by auto

lemma iterate_decreasing_chain_top:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  shows "Complete_Partial_Order.chain (\<ge>) {(iterate n b P 1\<^sub>p) | n::nat. True}" 
    (is "Complete_Partial_Order.chain _ ?C")
proof (rule chainI)
  fix x y
  assume "x \<in> ?C" "y \<in> ?C"
  then show "x \<le> y \<or> y \<le> x"
    by (smt (verit) assms iterate_decreasing2 mem_Collect_eq nle_le)
qed

lemma iterate_decreasing_chain:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  shows "decreasing_chain (\<lambda>n. (iterate n b P 1\<^sub>p))" 
    (is "decreasing_chain ?C")
  apply (simp add: decreasing_chain_def)
  by (simp add: assms iterate_decreasing2)

subsubsection \<open> Supreme \<close>
lemma sup_iterate_not_zero_strict_increasing:
  shows "(\<exists>n. iterate n b P 0\<^sub>p s \<noteq> 0) \<longleftrightarrow> 
        (ureal2real (iterate\<^sub>p (0::\<nat>) b P 0\<^sub>p s) < ureal2real (\<Squnion>n::\<nat>. iterate\<^sub>p n b P 0\<^sub>p s))"
  apply (rule iffI)
proof (rule ccontr)
  assume a1: "\<exists>n::\<nat>. \<not> iterate\<^sub>p n b P 0\<^sub>p s = (0::ureal)"
  assume a2: "\<not> ureal2real (iterate\<^sub>p (0::\<nat>) b P 0\<^sub>p s) < ureal2real (\<Squnion>n::\<nat>. iterate\<^sub>p n b P 0\<^sub>p s)"
  then have "(\<Squnion>n::\<nat>. iterate\<^sub>p n b P 0\<^sub>p s) = (iterate\<^sub>p (0::\<nat>) b P 0\<^sub>p s)"
    by (metis not_le_imp_less pzero_def ureal2real_mono_strict ureal_minus_larger_zero 
        ureal_minus_larger_zero_unit utp_prob_rel_lattice.iterate.simps(1))
  then have "\<forall>n. iterate n b P 0\<^sub>p s = (iterate\<^sub>p (0::\<nat>) b P 0\<^sub>p s)"
    by (metis SUP_upper bot.extremum bot_ureal.rep_eq iso_tuple_UNIV_I nle_le pzero_def 
        ureal2ereal_inverse utp_prob_rel_lattice.iterate.simps(1) zero_ureal.rep_eq)
  then show "false"
    by (metis a1 pzero_def utp_prob_rel_lattice.iterate.simps(1))
next
  assume "ureal2real (iterate\<^sub>p (0::\<nat>) b P 0\<^sub>p s) < ureal2real (\<Squnion>n::\<nat>. iterate\<^sub>p n b P 0\<^sub>p s)"
  then show "\<exists>n::\<nat>. \<not> iterate\<^sub>p n b P 0\<^sub>p s = (0::ureal)"
    by (smt (verit, best) SUP_bot_conv(2) bot_ureal.rep_eq ureal2ereal_inverse zero_ureal.rep_eq)
  qed

lemma sup_iterate_continuous_limit:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  assumes "finite {s::'s \<times> 's. \<exists>n. iterate n b P 0\<^sub>p s \<noteq> 0}"
  shows "(\<lambda>n. ureal2real (Fwhile b P (iterate n b P 0\<^sub>p) (s, s'))) \<longlonglongrightarrow> 
    ureal2real ((Fwhile b P (\<Squnion>n::nat. iterate n b P 0\<^sub>p)) (s, s'))"
  apply (subst LIMSEQ_iff)
  apply (auto)
proof -
  fix r
  assume a1: "(0::\<real>) < r"
  have f1: "\<forall>n. ureal2real (Fwhile b P (iterate\<^sub>p n b P 0\<^sub>p) (s, s')) \<le>
              ureal2real (Fwhile b P (\<Squnion>n::\<nat>. iterate\<^sub>p n b P 0\<^sub>p) (s, s'))"
    apply (auto)
    apply (rule ureal2real_mono)
    by (smt (verit) Fwhile_monoE SUP_upper UNIV_I assms le_fun_def)
  have f2: "\<forall>n. \<bar>ureal2real (Fwhile b P (iterate\<^sub>p n b P 0\<^sub>p) (s, s')) -
              ureal2real (Fwhile b P (\<Squnion>n::\<nat>. iterate\<^sub>p n b P 0\<^sub>p) (s, s'))\<bar> = 
    (ureal2real (Fwhile b P (\<Squnion>n::\<nat>. iterate\<^sub>p n b P 0\<^sub>p) (s, s')) - 
     ureal2real (Fwhile b P (iterate\<^sub>p n b P 0\<^sub>p) (s, s')))"
    using f1 by force

  (* *)
  let ?f = "(\<lambda>n. (iterate\<^sub>p n b P 0\<^sub>p))"

  have f3: "\<forall>n. \<forall>s s'. ureal2real (?f n (s, s')) \<le> ureal2real (\<Squnion>n::\<nat>. ?f n (s, s'))"
    apply (auto)
    apply (rule ureal2real_mono)
    by (smt (verit) Fwhile_monoE SUP_upper UNIV_I assms le_fun_def)
  (* have f4: "\<forall>n. \<bar>ureal2real (\<Squnion>n::\<nat>. ?f n (s, s')) - ureal2real (?f n (s, s'))\<bar> = 
      ureal2real (\<Squnion>n::\<nat>. ?f n (s, s')) - ureal2real (?f n (s, s'))"
    using f3 by force *)

  have Sn_limit_sup: "(\<lambda>n. ureal2real (?f n (s, s'))) \<longlonglongrightarrow> (ureal2real (\<Squnion>n::\<nat>. ?f n (s, s')))"
    apply (subst increasing_chain_limit_is_lub)
    apply (simp add: assms increasing_chain_def iterate_increasing2)
    by simp
  then have Sn_limit: "\<forall>r>0. \<exists>no::\<nat>. \<forall>n\<ge>no.
             \<bar>ureal2real (?f n (s, s')) - ureal2real (\<Squnion>n::\<nat>. ?f n (s, s'))\<bar> < r"
    using Sn_limit_sup LIMSEQ_iff by (smt (verit, del_insts) real_norm_def)
  have exist_N: "\<exists>no::\<nat>. \<forall>n\<ge>no. \<bar>ureal2real (?f n (s, s')) - ureal2real (\<Squnion>n::\<nat>. ?f n (s, s'))\<bar> < r"
    using Sn_limit a1 by blast
(*  
obtain N where P_N: "\<forall>n\<ge>N. \<bar>ureal2real (?f n (s, s')) - ureal2real (\<Squnion>n::\<nat>. ?f n (s, s'))\<bar> < r"
    using exist_N by blast

  have "\<forall>n. ureal2real (?f n (s, s')) \<le> ureal2real (\<Squnion>n::\<nat>. ?f n (s, s'))"
    by (meson SUP_upper UNIV_I ureal2real_mono)
  then have P_N': "\<forall>n\<ge>N. ureal2real (\<Squnion>n::\<nat>. ?f n (s, s')) - ureal2real (?f n (s, s')) < r"
    using P_N by force
*)

  have exist_NN: "\<exists>no::nat. \<forall>n \<ge> no.
            \<forall>s s'. ureal2real (\<Squnion>n::\<nat>. ?f n (s, s')) - ureal2real (?f n (s, s')) < r"
    apply (subst increasing_chain_limit_is_lub_all)
       apply (simp add: assms iterate_increasing_chain)
    using assms(2) sup_iterate_not_zero_strict_increasing apply (smt (verit) Collect_cong Sup.SUP_cong)
    by (simp add: a1)+

  obtain NN where P_NN: "\<forall>n\<ge>NN. \<forall>s s'. \<bar>ureal2real (?f n (s, s')) - ureal2real (\<Squnion>n::\<nat>. ?f n (s, s'))\<bar> < r"
    using exist_NN f3 by auto

  have P_NN': "\<forall>n\<ge>NN. \<forall>s s'. ureal2real (\<Squnion>n::\<nat>. ?f n (s, s')) - ureal2real (?f n (s, s')) < r"
    by (smt (verit, del_insts) P_NN)

  have "\<forall>n\<ge>NN. (ureal2real (Fwhile b P (\<Squnion>n::\<nat>. iterate\<^sub>p n b P 0\<^sub>p) (s, s')) - 
     ureal2real (Fwhile b P (iterate\<^sub>p n b P 0\<^sub>p) (s, s'))) < r"
    apply (auto)
    apply (subst Fwhile_minus_distr')
    apply (simp add: assms)
    apply (simp add: is_prob_final_prob ureal_is_prob)+
    apply (meson SUP_upper UNIV_I)
    apply (simp add: pseqcomp_def)
    apply (expr_auto)
  proof -
    fix n::nat
    assume a10: "NN \<le> n"
    assume a11: "b (s, s')"
    let ?lhs = "ureal2real
        (prfun_of_rvfun
          (\<lambda>\<s>::'s \<times> 's.
              \<Sum>\<^sub>\<infinity>v\<^sub>0::'s.
                rvfun_of_prfun P (fst \<s>, v\<^sub>0) *
                rvfun_of_prfun ((\<Squnion>n::\<nat>. iterate\<^sub>p n b P 0\<^sub>p) - iterate\<^sub>p n b P 0\<^sub>p) (v\<^sub>0, snd \<s>))
          (s, s'))"
    have f10: "\<forall>s s'. (ureal2real (\<Squnion>n::\<nat>. ?f n (s, s')) - ureal2real (?f n (s, s'))) = 
          (ureal2real ((\<Squnion>n::\<nat>. ?f n (s, s')) - (?f n (s, s'))))"
      by (metis f3 linorder_not_le ureal2real_distr ureal2real_mono_strict)
    have f11: "((\<Sum>\<^sub>\<infinity>v\<^sub>0::'s.
          ureal2real (P (s, v\<^sub>0)) *
          ureal2real ((\<Squnion>f::'s \<times> 's \<Rightarrow> ureal\<in>range (\<lambda>n::\<nat>. iterate\<^sub>p n b P 0\<^sub>p). f (v\<^sub>0, s')) - iterate\<^sub>p n b P 0\<^sub>p (v\<^sub>0, s'))))
      = ( (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s.
          ureal2real (P (s, v\<^sub>0)) * (ureal2real (\<Squnion>n::\<nat>. ?f n (v\<^sub>0, s')) - ureal2real (?f n (v\<^sub>0, s')))))"
      apply (rule infsum_cong)
      by (smt (verit, best) Sup.SUP_cong f10 image_image)
    have f12: "... < (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. ureal2real (P (s, v\<^sub>0)) * r)"
    proof -
      let ?lhs = "\<lambda>v\<^sub>0. ureal2real (P (s, v\<^sub>0)) *
        (ureal2real (\<Squnion>n::\<nat>. iterate\<^sub>p n b P 0\<^sub>p (v\<^sub>0, s')) - ureal2real (iterate\<^sub>p n b P 0\<^sub>p (v\<^sub>0, s')))"
      let ?rhs = "\<lambda>v\<^sub>0. ureal2real (P (s, v\<^sub>0)) * r"
      obtain v\<^sub>0 where P_v\<^sub>0: "P (s, v\<^sub>0) > 0"
        using assms rvfun_prob_sum1_summable(4)
        by (metis SEXP_def bot.extremum bot_ureal.rep_eq linorder_not_le nle_le rvfun_of_prfun_def 
            ureal2ereal_inverse ureal2real_mono ureal_lower_bound ureal_real2ureal_smaller zero_ureal.rep_eq)
      have lhs_0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. ?lhs v\<^sub>0) = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s \<in> ({v\<^sub>0} \<union> (-{v\<^sub>0})). ?lhs v\<^sub>0)"
        by auto
      have lhs_1: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s \<in> {v\<^sub>0}. ?lhs v\<^sub>0) + (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s \<in> -{v\<^sub>0}. ?lhs v\<^sub>0)"
        apply (rule infsum_Un_disjoint)
        apply auto[1]
        apply (simp add: f10)
        apply (rule summable_on_subset_banach[where A="UNIV"])
        apply (subst pdrfun_product_summable')
        by (simp add: assms)+
      have rhs_0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. ?rhs v\<^sub>0) = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s \<in> ({v\<^sub>0} \<union> (-{v\<^sub>0})). ?rhs v\<^sub>0)"
        by auto
      have rhs_1: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s\<in> ({v\<^sub>0}). ?rhs v\<^sub>0) + (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s\<in> ((-{v\<^sub>0})). ?rhs v\<^sub>0)"
        apply (rule infsum_Un_disjoint)
        apply auto[1]
        apply (rule summable_on_subset_banach[where A="UNIV"])
        apply (subst summable_on_cmult_left)
        apply (simp add: assms pdrfun_prob_sum1_summable(4))
        by (simp)+
      have lhs_0_rhs_0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'s \<in> -{v\<^sub>0}. ?lhs v\<^sub>0) \<le> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s\<in> ((-{v\<^sub>0})). ?rhs v\<^sub>0)"
        apply (rule infsum_mono)
        apply (simp add: f10)
        apply (rule summable_on_subset_banach[where A="UNIV"])
        apply (subst pdrfun_product_summable')
        apply (simp add: assms)+
        apply (rule summable_on_subset_banach[where A="UNIV"])
        apply (subst summable_on_cmult_left)
        apply (simp add: assms pdrfun_prob_sum1_summable(4))
        apply (simp)+
        by (smt (verit, ccfv_SIG) P_NN' Sup.SUP_cong a10 left_diff_distrib 
            linordered_comm_semiring_strict_class.comm_mult_strict_left_mono ureal_lower_bound)
      have lhs_2: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'s \<in> {v\<^sub>0}. ?lhs v\<^sub>0) = ?lhs v\<^sub>0"
        by (rule infsum_on_singleton)
      have rhs_2: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'s\<in> ({v\<^sub>0}). ?rhs v\<^sub>0) = ?rhs v\<^sub>0"
        by (rule infsum_on_singleton)
      have lhs_1_rhs_1: "?lhs v\<^sub>0 < ?rhs v\<^sub>0"
        by (smt (verit, best) P_NN' P_v\<^sub>0 Sup.SUP_cong a10 linordered_comm_semiring_strict_class.comm_mult_strict_left_mono ureal2real_mono_strict ureal_lower_bound)
      show ?thesis
        apply (simp only: lhs_0 rhs_0 lhs_1 rhs_1)
        using lhs_0_rhs_0 lhs_1_rhs_1 lhs_2 rhs_2 by linarith
    qed
    also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. ureal2real (P (s, v\<^sub>0))) * r"
      apply (rule infsum_cmult_left)
      by (simp add: assms pdrfun_prob_sum1_summable(4))
    also have "... = r"
      by (simp add: assms pdrfun_prob_sum1_summable(3))
    then have f13: "( (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s.
          ureal2real (P (s, v\<^sub>0)) * (ureal2real (\<Squnion>n::\<nat>. ?f n (v\<^sub>0, s')) - ureal2real (?f n (v\<^sub>0, s'))))) < r"
      using calculation by linarith

    have f14: "?lhs = ureal2real
        (real2ureal ( (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s.
          ureal2real (P (s, v\<^sub>0)) * (ureal2real (\<Squnion>n::\<nat>. ?f n (v\<^sub>0, s')) - ureal2real (?f n (v\<^sub>0, s'))))))"
      apply (simp add: prfun_of_rvfun_def)
      apply (simp add: rvfun_of_prfun_def)
      by (simp add: f11)
    show "?lhs  < r"
      apply (simp add: f14)
      using f13 by (smt (verit, del_insts) f11 infsum_nonneg mult_nonneg_nonneg ureal_lower_bound ureal_real2ureal_smaller)
  next
    show "(0::\<real>) < r"
      by (simp add: a1)
  qed

  then show "\<exists>no::\<nat>. \<forall>n\<ge>no.
             \<bar>ureal2real (Fwhile b P (iterate\<^sub>p n b P 0\<^sub>p) (s, s')) -
              ureal2real (Fwhile b P (\<Squnion>n::\<nat>. iterate\<^sub>p n b P 0\<^sub>p) (s, s'))\<bar> < r"
    apply (simp add: Fwhile_def)
    by (metis Fwhile_def f2)
qed

lemma sup_iterate_suc: "(\<Squnion>x \<in> {(iterate n b P 0\<^sub>p) | n::nat. True}. (Fwhile b P x)) = 
       (\<Squnion>n::nat. (iterate (Suc n) b P 0\<^sub>p))"
  apply (simp add: image_def)
  by metis

lemma sup_iterate_subset_eq:
  "(\<Squnion>n::nat. (iterate (Suc n) b P 0\<^sub>p)) = (\<Squnion>n::nat. (iterate n b P 0\<^sub>p))"
proof -
  have f1: "(\<Squnion>n::nat. (iterate (Suc n) b P 0\<^sub>p)) = (\<Squnion>n\<in>{1..}. (iterate n b P 0\<^sub>p))"
    apply (simp add: image_def)
    by (metis atLeast_iff bot_nat_0.extremum not0_implies_Suc not_less_eq_eq utp_prob_rel_lattice.iterate.simps(2))
  have "insert (0::nat) {1..} = UNIV"
    using UNIV_nat_eq atLeast_Suc_greaterThan by auto
  then have f2: "(\<Squnion>n::nat. (iterate n b P 0\<^sub>p)) = (\<Squnion>n::nat \<in> insert 0 {1..}. (iterate n b P 0\<^sub>p))"
    by (simp add: image_def)
  have f3: "(\<Squnion>n::nat \<in> insert 0 {1..}. (iterate n b P 0\<^sub>p)) = (iterate 0 b P 0\<^sub>p) \<squnion> (\<Squnion>n\<in>{1..}. (iterate n b P 0\<^sub>p))"
    apply (subst SUP_insert)
    using sup_commute by blast
  have f4: "... = (\<Squnion>n\<in>{1..}. (iterate n b P 0\<^sub>p))"
    using le_iff_sup  ureal_bottom_least' by auto
  show ?thesis
    using f1 f2 f3 f4 by presburger 
qed

lemma sup_iterate_continuous':
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  assumes "finite {s::'s \<times> 's. \<exists>n. iterate n b P 0\<^sub>p s \<noteq> 0}"
  (*
  shows "Fwhile   b P (Sup {(iterate n b P 0\<^sub>p) | n::nat. True}) = 
         Sup (Fwhile b P ` {(iterate n b P 0\<^sub>p) | n::nat. True})"
  *)
  (*
  shows "Fwhile b P (Sup {(iterate n b P 0\<^sub>p) | n::nat. True}) = 
       Sup ({Fwhile b P x | x. x \<in> {(iterate n b P 0\<^sub>p) | n::nat. True}})"
  *)
  shows "Fwhile b P (\<Squnion>n::nat. iterate n b P 0\<^sub>p) = (\<Squnion>x \<in> {(iterate n b P 0\<^sub>p) | n::nat. True}. (Fwhile b P x))"
  apply (subst fun_eq_iff)
  apply (auto)
proof -
  fix s s'
  let ?f = "\<lambda>n. Fwhile b P (iterate n b P 0\<^sub>p)"
  have "increasing_chain ?f"
    by (simp add: Fwhile_monoE assms increasing_chain_def iterate_increasing2)
  then have  "(\<lambda>n. ureal2real (?f n (s, s'))) \<longlonglongrightarrow> (ureal2real (\<Squnion>n::\<nat>. ?f n (s, s')))"
    by (rule increasing_chain_limit_is_lub) 
  then have  "ureal2real (\<Squnion>n::\<nat>. ?f n (s, s')) = ureal2real ((Fwhile b P (\<Squnion>n::nat. iterate n b P 0\<^sub>p)) (s, s'))"
    apply (subst LIMSEQ_unique[where X="(\<lambda>n. ureal2real (?f n (s, s')))" and a = "ureal2real (\<Squnion>n::\<nat>. ?f n (s, s'))" and 
           b = "ureal2real ((Fwhile b P (\<Squnion>n::nat. iterate n b P 0\<^sub>p)) (s, s'))"])
    apply meson
    apply (subst sup_iterate_continuous_limit)
    using assms(1) apply blast
    using assms(2) apply blast
    by (simp)+
    
  then have f1: "(\<Squnion>n::\<nat>. ?f n (s, s')) = ((Fwhile b P (\<Squnion>n::nat. iterate n b P 0\<^sub>p)) (s, s'))"
    using ureal2real_eq by blast

  have f2: "(\<Squnion>x::'s \<times> 's \<Rightarrow> ureal\<in> Fwhile b P ` {uu::'s \<times> 's \<Rightarrow> ureal. \<exists>n::\<nat>. uu = iterate\<^sub>p n b P 0\<^sub>p}. x (s, s'))
    = Sup ((\<lambda>x. x (s, s')) ` (Fwhile b P ` {uu::'s \<times> 's \<Rightarrow> ureal. \<exists>n::\<nat>. uu = iterate\<^sub>p n b P 0\<^sub>p}))"
    by auto
  have f3: "(\<Squnion>n::\<nat>. Fwhile b P (iterate\<^sub>p n b P 0\<^sub>p) (s, s')) = (Sup (range (\<lambda>n. Fwhile b P (iterate\<^sub>p n b P 0\<^sub>p) (s, s'))))"
    by simp
  have f4: "((\<lambda>x. x (s, s')) ` (Fwhile b P ` {uu::'s \<times> 's \<Rightarrow> ureal. \<exists>n::\<nat>. uu = iterate\<^sub>p n b P 0\<^sub>p})) = 
        (range (\<lambda>n. Fwhile b P (iterate\<^sub>p n b P 0\<^sub>p) (s, s')))"
    apply (simp add: image_def)
    by (auto)
  show "Fwhile b P (\<Squnion>n::\<nat>. iterate\<^sub>p n b P 0\<^sub>p) (s, s') =
       (\<Squnion>x::'s \<times> 's \<Rightarrow> ureal\<in>Fwhile b P ` {uu::'s \<times> 's \<Rightarrow> ureal. \<exists>n::\<nat>. uu = iterate\<^sub>p n b P 0\<^sub>p}. x (s, s'))"
    apply (simp add: f1[symmetric])
    using f4 by presburger
qed

theorem sup_iterate_continuous:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  assumes "finite {s::'s \<times> 's. \<exists>n. iterate n b P 0\<^sub>p s \<noteq> 0}"
  shows "Fwhile b P (\<Squnion>n::nat. iterate n b P 0\<^sub>p) = (\<Squnion>n::nat. (iterate n b P 0\<^sub>p))"
  apply (simp add: assms sup_iterate_continuous')
  using sup_iterate_suc sup_iterate_subset_eq by metis

subsubsection \<open> Infimum \<close>
lemma inf_iterate_not_zero_strict_decreasing:
  shows "(\<exists>n. iterate n b P 1\<^sub>p s \<noteq> 1) \<longleftrightarrow> 
        (ureal2real (iterate\<^sub>p (0::\<nat>) b P 1\<^sub>p s) > ureal2real (\<Sqinter>n::\<nat>. iterate\<^sub>p n b P 1\<^sub>p s))"
  apply (rule iffI)
proof (rule ccontr)
  assume a1: "\<exists>n::\<nat>. \<not> iterate\<^sub>p n b P 1\<^sub>p s = (1::ureal)"
  assume a2: "\<not> ureal2real (\<Sqinter>n::\<nat>. iterate\<^sub>p n b P 1\<^sub>p s) < ureal2real (iterate\<^sub>p (0::\<nat>) b P 1\<^sub>p s)"
  then have "(\<Sqinter>n::\<nat>. iterate\<^sub>p n b P 1\<^sub>p s) = (iterate\<^sub>p (0::\<nat>) b P 1\<^sub>p s)"
    by (metis linorder_not_less not_less_iff_gr_or_eq o_apply one_ureal.rep_eq pone_def real_ereal_1 
        ureal2real_def ureal2real_mono_strict ureal_upper_bound utp_prob_rel_lattice.iterate.simps(1))
  then have "\<forall>n. iterate n b P 1\<^sub>p s = (iterate\<^sub>p (0::\<nat>) b P 1\<^sub>p s)"
    by (smt (verit, best) INF_top_conv(2) UNIV_I linorder_not_less not_less_iff_gr_or_eq o_apply 
        one_ureal.rep_eq pone_def real_ereal_1 top_greatest ureal2real_def ureal2real_mono_strict 
        ureal_upper_bound utp_prob_rel_lattice.iterate.simps(1))
  then show "false"
    by (metis a1 pone_def utp_prob_rel_lattice.iterate.simps(1))
next
  assume "ureal2real (\<Sqinter>n::\<nat>. iterate\<^sub>p n b P 1\<^sub>p s) < ureal2real (iterate\<^sub>p (0::\<nat>) b P 1\<^sub>p s)"
  then show "\<exists>n::\<nat>. \<not> iterate\<^sub>p n b P 1\<^sub>p s = (1::ureal)"
    by (smt (verit, ccfv_threshold) INF_top_conv(2) one_ureal.rep_eq top_ureal.rep_eq ureal2ereal_inject)
  qed

lemma inf_iterate_continuous_limit:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  assumes "finite {s::'s \<times> 's. \<exists>n. iterate n b P 1\<^sub>p s \<noteq> 1}"
  shows "(\<lambda>n. ureal2real (Fwhile b P (iterate n b P 1\<^sub>p) (s, s'))) \<longlonglongrightarrow> 
    ureal2real ((Fwhile b P (\<Sqinter>n::nat. iterate n b P 1\<^sub>p)) (s, s'))"
  apply (subst LIMSEQ_iff)
  apply (auto)
proof -
  fix r
  assume a1: "(0::\<real>) < r"
  have f1: "\<forall>n. ureal2real (Fwhile b P (iterate\<^sub>p n b P 1\<^sub>p) (s, s')) \<ge>
              ureal2real (Fwhile b P (\<Sqinter>n::\<nat>. iterate\<^sub>p n b P 1\<^sub>p) (s, s'))"
    apply (auto)
    apply (rule ureal2real_mono)
    by (smt (verit) Fwhile_monoE INF_lower UNIV_I assms(1) le_fun_def)
  have f2: "\<forall>n. \<bar>ureal2real (Fwhile b P (iterate\<^sub>p n b P 1\<^sub>p) (s, s')) -
              ureal2real (Fwhile b P (\<Sqinter>n::\<nat>. iterate\<^sub>p n b P 1\<^sub>p) (s, s'))\<bar> = 
    (ureal2real (Fwhile b P (iterate\<^sub>p n b P 1\<^sub>p) (s, s')) -
        ureal2real (Fwhile b P (\<Sqinter>n::\<nat>. iterate\<^sub>p n b P 1\<^sub>p) (s, s')))"
    using f1 by force

  let ?f = "(\<lambda>n. (iterate\<^sub>p n b P 1\<^sub>p))"

  have f3: "\<forall>n. \<forall>s s'. ureal2real (?f n (s, s')) \<ge> ureal2real (\<Sqinter>n::\<nat>. ?f n (s, s'))"
    apply (auto)
    apply (rule ureal2real_mono)
    by (meson INF_lower UNIV_I)
 
  have Sn_limit_inf: "(\<lambda>n. ureal2real (?f n (s, s'))) \<longlonglongrightarrow> (ureal2real (\<Sqinter>n::\<nat>. ?f n (s, s')))"
    apply (subst decreasing_chain_limit_is_glb)
    apply (simp add: assms decreasing_chain_def iterate_decreasing2)
    by simp
  then have Sn_limit: "\<forall>r>0. \<exists>no::\<nat>. \<forall>n\<ge>no.
             \<bar>ureal2real (?f n (s, s')) - ureal2real (\<Sqinter>n::\<nat>. ?f n (s, s'))\<bar> < r"
    using Sn_limit_inf LIMSEQ_iff by (smt (verit, del_insts) real_norm_def)
  have exist_N: "\<exists>no::\<nat>. \<forall>n\<ge>no. \<bar>ureal2real (?f n (s, s')) - ureal2real (\<Sqinter>n::\<nat>. ?f n (s, s'))\<bar> < r"
    using Sn_limit a1 by blast

  have exist_NN: "\<exists>no::nat. \<forall>n \<ge> no.
            \<forall>s s'. ureal2real (?f n (s, s')) - ureal2real (\<Sqinter>n::\<nat>. ?f n (s, s')) < r"
    apply (subst decreasing_chain_limit_is_lub_all)
       apply (simp add: assms iterate_decreasing_chain)
    using assms(2) inf_iterate_not_zero_strict_decreasing apply (smt (verit) Collect_cong Sup.SUP_cong)
    by (simp add: a1)+

  obtain NN where P_NN: "\<forall>n\<ge>NN. \<forall>s s'. \<bar>ureal2real (?f n (s, s')) - ureal2real (\<Sqinter>n::\<nat>. ?f n (s, s'))\<bar> < r"
    using exist_NN f3 by auto

  have P_NN': "\<forall>n\<ge>NN. \<forall>s s'. ureal2real (?f n (s, s')) - ureal2real (\<Sqinter>n::\<nat>. ?f n (s, s')) < r"
    by (smt (verit, del_insts) P_NN)

  have "\<forall>n\<ge>NN. (ureal2real (Fwhile b P (iterate\<^sub>p n b P 1\<^sub>p) (s, s')) - 
            ureal2real (Fwhile b P (\<Sqinter>n::\<nat>. iterate\<^sub>p n b P 1\<^sub>p) (s, s'))) < r"
    apply (auto)
    apply (subst Fwhile_minus_distr')
    apply (simp add: assms)
    apply (simp add: is_prob_final_prob ureal_is_prob)+
    apply (meson INF_lower UNIV_I)
    apply (simp add: pseqcomp_def)
    apply (expr_auto)
  proof -
    fix n::nat
    assume a10: "NN \<le> n"
    assume a11: "b (s, s')"
    let ?lhs = "ureal2real
        (prfun_of_rvfun
          (\<lambda>\<s>::'s \<times> 's.
              \<Sum>\<^sub>\<infinity>v\<^sub>0::'s.
                rvfun_of_prfun P (fst \<s>, v\<^sub>0) *
                rvfun_of_prfun (iterate\<^sub>p n b P 1\<^sub>p - (\<Sqinter>n::\<nat>. iterate\<^sub>p n b P 1\<^sub>p)) (v\<^sub>0, snd \<s>))
          (s, s'))"
    have f10: "\<forall>s s'. (ureal2real (?f n (s, s')) - ureal2real (\<Sqinter>n::\<nat>. ?f n (s, s'))) = 
          (ureal2real ((?f n (s, s')) - (\<Sqinter>n::\<nat>. ?f n (s, s'))))"
      by (metis f3 linorder_not_le ureal2real_distr ureal2real_mono_strict)
    have f11: "((\<Sum>\<^sub>\<infinity>v\<^sub>0::'s.
          ureal2real (P (s, v\<^sub>0)) *
          ureal2real (iterate\<^sub>p n b P 1\<^sub>p (v\<^sub>0, s') - (\<Sqinter>f::'s \<times> 's \<Rightarrow> ureal\<in>range (\<lambda>n::\<nat>. iterate\<^sub>p n b P 1\<^sub>p). f (v\<^sub>0, s')))))
      = ( (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s.
          ureal2real (P (s, v\<^sub>0)) * (ureal2real (?f n (v\<^sub>0, s')) - ureal2real (\<Sqinter>n::\<nat>. ?f n (v\<^sub>0, s')))))"
      apply (rule infsum_cong)
      by (smt (verit, best) Sup.SUP_cong f10 image_image)
    have f12: "... < (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. ureal2real (P (s, v\<^sub>0)) * r)"
    proof -
      let ?lhs = "\<lambda>v\<^sub>0. ureal2real (P (s, v\<^sub>0)) *
        (ureal2real (iterate\<^sub>p n b P 1\<^sub>p (v\<^sub>0, s')) - ureal2real (\<Sqinter>n::\<nat>. iterate\<^sub>p n b P 1\<^sub>p (v\<^sub>0, s')))"
      let ?rhs = "\<lambda>v\<^sub>0. ureal2real (P (s, v\<^sub>0)) * r"
      obtain v\<^sub>0 where P_v\<^sub>0: "P (s, v\<^sub>0) > 0"
        using assms rvfun_prob_sum1_summable(4)
        by (smt (verit, ccfv_threshold) SEXP_def bot.extremum bot_ureal.rep_eq linorder_not_le nle_le 
            rvfun_of_prfun_def ureal2ereal_inverse ureal2real_mono_strict ureal_real2ureal_smaller zero_ureal.rep_eq)
      have lhs_0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. ?lhs v\<^sub>0) = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s \<in> ({v\<^sub>0} \<union> (-{v\<^sub>0})). ?lhs v\<^sub>0)"
        by auto
      have lhs_1: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s \<in> {v\<^sub>0}. ?lhs v\<^sub>0) + (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s \<in> -{v\<^sub>0}. ?lhs v\<^sub>0)"
        apply (rule infsum_Un_disjoint)
        apply auto[1]
        apply (simp add: f10)
        apply (rule summable_on_subset_banach[where A="UNIV"])
        apply (subst pdrfun_product_summable')
        by (simp add: assms)+
      have rhs_0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. ?rhs v\<^sub>0) = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s \<in> ({v\<^sub>0} \<union> (-{v\<^sub>0})). ?rhs v\<^sub>0)"
        by auto
      have rhs_1: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s\<in> ({v\<^sub>0}). ?rhs v\<^sub>0) + (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s\<in> ((-{v\<^sub>0})). ?rhs v\<^sub>0)"
        apply (rule infsum_Un_disjoint)
        apply auto[1]
        apply (rule summable_on_subset_banach[where A="UNIV"])
        apply (subst summable_on_cmult_left)
        apply (simp add: assms pdrfun_prob_sum1_summable(4))
        by (simp)+
      have lhs_0_rhs_0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'s \<in> -{v\<^sub>0}. ?lhs v\<^sub>0) \<le> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s\<in> ((-{v\<^sub>0})). ?rhs v\<^sub>0)"
        apply (rule infsum_mono)
        apply (simp add: f10)
        apply (rule summable_on_subset_banach[where A="UNIV"])
        apply (subst pdrfun_product_summable')
        apply (simp add: assms)+
        apply (rule summable_on_subset_banach[where A="UNIV"])
        apply (subst summable_on_cmult_left)
        apply (simp add: assms pdrfun_prob_sum1_summable(4))
        apply (simp)+
        by (smt (verit, ccfv_SIG) P_NN' Sup.SUP_cong a10 left_diff_distrib 
            linordered_comm_semiring_strict_class.comm_mult_strict_left_mono ureal_lower_bound)
      have lhs_2: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'s \<in> {v\<^sub>0}. ?lhs v\<^sub>0) = ?lhs v\<^sub>0"
        by (rule infsum_on_singleton)
      have rhs_2: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'s\<in> ({v\<^sub>0}). ?rhs v\<^sub>0) = ?rhs v\<^sub>0"
        by (rule infsum_on_singleton)
      have lhs_1_rhs_1: "?lhs v\<^sub>0 < ?rhs v\<^sub>0"
        by (smt (verit, best) P_NN' P_v\<^sub>0 Sup.SUP_cong a10 linordered_comm_semiring_strict_class.comm_mult_strict_left_mono ureal2real_mono_strict ureal_lower_bound)
      show ?thesis
        apply (simp only: lhs_0 rhs_0 lhs_1 rhs_1)
        using lhs_0_rhs_0 lhs_1_rhs_1 lhs_2 rhs_2 by linarith
    qed
    also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. ureal2real (P (s, v\<^sub>0))) * r"
      apply (rule infsum_cmult_left)
      by (simp add: assms pdrfun_prob_sum1_summable(4))
    also have "... = r"
      by (simp add: assms pdrfun_prob_sum1_summable(3))
    then have f13: "( (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s.
          ureal2real (P (s, v\<^sub>0)) * (ureal2real (?f n (v\<^sub>0, s')) - ureal2real (\<Sqinter>n::\<nat>. ?f n (v\<^sub>0, s'))))) < r"
      using calculation by linarith

    have f14: "?lhs = ureal2real
        (real2ureal ( (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s.
          ureal2real (P (s, v\<^sub>0)) * (ureal2real (?f n (v\<^sub>0, s')) - ureal2real (\<Sqinter>n::\<nat>. ?f n (v\<^sub>0, s'))))))"
      apply (simp add: prfun_of_rvfun_def)
      apply (simp add: rvfun_of_prfun_def)
      by (simp add: f11)
    show "?lhs  < r"
      apply (simp add: f14)
      using f13 by (smt (verit, del_insts) f11 infsum_nonneg mult_nonneg_nonneg ureal_lower_bound ureal_real2ureal_smaller)
  next
    show "(0::\<real>) < r"
      by (simp add: a1)
  qed

  then show "\<exists>no::\<nat>. \<forall>n\<ge>no.
             \<bar>ureal2real (Fwhile b P (iterate\<^sub>p n b P 1\<^sub>p) (s, s')) -
              ureal2real (Fwhile b P (\<Sqinter>n::\<nat>. iterate\<^sub>p n b P 1\<^sub>p) (s, s'))\<bar>
             < r"
    apply (simp add: Fwhile_def)
    by (metis Fwhile_def f2)
qed

lemma inf_iterate_suc: "(\<Sqinter>x \<in> {(iterate n b P 1\<^sub>p) | n::nat. True}. (Fwhile b P x)) = 
       (\<Sqinter>n::nat. (iterate (Suc n) b P 1\<^sub>p))"
  apply (simp add: image_def)
  by metis

lemma inf_iterate_subset_eq:
  "(\<Sqinter>n::nat. (iterate (Suc n) b P 1\<^sub>p)) = (\<Sqinter>n::nat. (iterate n b P 1\<^sub>p))"
proof -
  have f1: "(\<Sqinter>n::nat. (iterate (Suc n) b P 1\<^sub>p)) = (\<Sqinter>n\<in>{1..}. (iterate n b P 1\<^sub>p))"
    apply (simp add: image_def)
    by (metis atLeast_iff bot_nat_0.extremum not0_implies_Suc not_less_eq_eq utp_prob_rel_lattice.iterate.simps(2))
  have "insert (0::nat) {1..} = UNIV"
    using UNIV_nat_eq atLeast_Suc_greaterThan by auto
  then have f2: "(\<Sqinter>n::nat. (iterate n b P 1\<^sub>p)) = (\<Sqinter>n::nat \<in> insert 0 {1..}. (iterate n b P 1\<^sub>p))"
    by (simp add: image_def)
  have f3: "(\<Sqinter>n::nat \<in> insert 0 {1..}. (iterate n b P 1\<^sub>p)) = (iterate 0 b P 1\<^sub>p) \<sqinter> (\<Sqinter>n\<in>{1..}. (iterate n b P 1\<^sub>p))"
    apply (subst INF_insert)
    using sup_commute by blast
  have f4: "... = (\<Sqinter>n\<in>{1..}. (iterate n b P 1\<^sub>p))"
    by (smt (verit, del_insts) inf_top_left le_fun_def le_iff_inf pone_def ureal_top_greatest utp_prob_rel_lattice.iterate.simps(1))
  show ?thesis
    using f1 f2 f3 f4 by presburger 
qed

lemma inf_iterate_continuous':
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  assumes "finite {s::'s \<times> 's. \<exists>n. iterate n b P 1\<^sub>p s \<noteq> 1}"
  shows "Fwhile b P (\<Sqinter>n::nat. iterate n b P 1\<^sub>p) = (\<Sqinter>x \<in> {(iterate n b P 1\<^sub>p) | n::nat. True}. (Fwhile b P x))"
  apply (subst fun_eq_iff)
  apply (auto)
proof -
  fix s s'
  let ?f = "\<lambda>n. Fwhile b P (iterate n b P 1\<^sub>p)"
  have "decreasing_chain ?f"
    by (simp add: Fwhile_monoE assms decreasing_chain_def iterate_decreasing2)
  then have  "(\<lambda>n. ureal2real (?f n (s, s'))) \<longlonglongrightarrow> (ureal2real (\<Sqinter>n::\<nat>. ?f n (s, s')))"
    by (rule decreasing_chain_limit_is_glb) 
  then have  "ureal2real (\<Sqinter>n::\<nat>. ?f n (s, s')) = ureal2real ((Fwhile b P (\<Sqinter>n::nat. iterate n b P 1\<^sub>p)) (s, s'))"
    apply (subst LIMSEQ_unique[where X="(\<lambda>n. ureal2real (?f n (s, s')))" and a = "ureal2real (\<Sqinter>n::\<nat>. ?f n (s, s'))" and 
           b = "ureal2real ((Fwhile b P (\<Sqinter>n::nat. iterate n b P 1\<^sub>p)) (s, s'))"])
    apply meson
    apply (subst inf_iterate_continuous_limit)
    using assms(1) apply blast
    using assms(2) apply blast
    by (simp)+
    
  then have f1: "(\<Sqinter>n::\<nat>. ?f n (s, s')) = ((Fwhile b P (\<Sqinter>n::nat. iterate n b P 1\<^sub>p)) (s, s'))"
    using ureal2real_eq by blast

  have f2: "(\<Sqinter>x::'s \<times> 's \<Rightarrow> ureal\<in> Fwhile b P ` {uu::'s \<times> 's \<Rightarrow> ureal. \<exists>n::\<nat>. uu = iterate\<^sub>p n b P 1\<^sub>p}. x (s, s'))
    = Inf ((\<lambda>x. x (s, s')) ` (Fwhile b P ` {uu::'s \<times> 's \<Rightarrow> ureal. \<exists>n::\<nat>. uu = iterate\<^sub>p n b P 1\<^sub>p}))"
    by auto
  have f3: "(\<Sqinter>n::\<nat>. Fwhile b P (iterate\<^sub>p n b P 1\<^sub>p) (s, s')) = (Inf (range (\<lambda>n. Fwhile b P (iterate\<^sub>p n b P 1\<^sub>p) (s, s'))))"
    by simp
  have f4: "((\<lambda>x. x (s, s')) ` (Fwhile b P ` {uu::'s \<times> 's \<Rightarrow> ureal. \<exists>n::\<nat>. uu = iterate\<^sub>p n b P 1\<^sub>p})) = 
        (range (\<lambda>n. Fwhile b P (iterate\<^sub>p n b P 1\<^sub>p) (s, s')))"
    apply (simp add: image_def)
    by (auto)
  show "Fwhile b P (\<Sqinter>n::\<nat>. iterate\<^sub>p n b P 1\<^sub>p) (s, s') =
       (\<Sqinter>x::'s \<times> 's \<Rightarrow> ureal\<in>Fwhile b P ` {uu::'s \<times> 's \<Rightarrow> ureal. \<exists>n::\<nat>. uu = iterate\<^sub>p n b P 1\<^sub>p}. x (s, s'))"
    apply (simp add: f1[symmetric])
    using f4 by presburger
qed

theorem inf_iterate_continuous:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  assumes "finite {s::'s \<times> 's. \<exists>n. iterate n b P 1\<^sub>p s \<noteq> 1}"
  shows "Fwhile b P (\<Sqinter>n::nat. iterate n b P 1\<^sub>p) = (\<Sqinter>n::nat. (iterate n b P 1\<^sub>p))"
  apply (simp add: assms inf_iterate_continuous')
  using inf_iterate_suc inf_iterate_subset_eq by metis

subsubsection \<open> Kleene fixed-point theorem \<close>
theorem sup_continuous_lfp_iteration:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  assumes "finite {s::'s \<times> 's. \<exists>n. iterate n b P 0\<^sub>p s \<noteq> 0}"
  shows "while\<^sub>p b do P od = (\<Squnion>n::nat. (iterate n b P 0\<^sub>p))"
  apply (simp add: pwhile_def)
  apply (rule lfp_eqI)
  apply (simp add: Fwhile_mono assms)
  apply (simp add: assms sup_iterate_continuous)
proof -
  fix z
  assume a1: "Fwhile b P z = z"
  show "(\<Squnion>n::\<nat>. iterate\<^sub>p n b P 0\<^sub>p) \<le> z"
    apply (rule Sup_least)
    apply (simp add: image_def)
  proof -
    fix x
    assume a11: "\<exists>xa::\<nat>. x = iterate\<^sub>p xa b P 0\<^sub>p"
    have "\<forall>n. iterate\<^sub>p n b P 0\<^sub>p \<le> z"
      apply (rule allI)
      apply (induct_tac "n")
      apply (simp add: ureal_bottom_least')
      by (metis Fwhile_monoE a1 assms(1) utp_prob_rel_lattice.iterate.simps(2))
    then show "x \<le> z"
      using a11 by blast
  qed
qed

theorem inf_continuous_gfp_iteration:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  assumes "finite {s::'s \<times> 's. \<exists>n. iterate n b P 1\<^sub>p s \<noteq> 1}"
  shows "while\<^sub>p\<^sup>\<top> b do P od = (\<Sqinter>n::nat. (iterate n b P 1\<^sub>p))"
  apply (simp add: pwhile_top_def)
  apply (rule gfp_eqI)
  apply (simp add: Fwhile_mono assms)
  apply (simp add: assms inf_iterate_continuous)
proof -
  fix z
  assume a1: "Fwhile b P z = z"
  show "z \<le> (\<Sqinter>n::\<nat>. iterate\<^sub>p n b P 1\<^sub>p)"
    apply (rule Inf_greatest)
    apply (simp add: image_def)
  proof -
    fix x
    assume a11: "\<exists>xa::\<nat>. x = iterate\<^sub>p xa b P 1\<^sub>p"
    have "\<forall>n. iterate\<^sub>p n b P 1\<^sub>p \<ge> z"
      apply (rule allI)
      apply (induct_tac "n")
      apply (simp add: ureal_top_greatest')
      by (metis Fwhile_monoE a1 assms(1) utp_prob_rel_lattice.iterate.simps(2))
    then show "z \<le> x"
      using a11 by blast
  qed
qed

(*
theorem increasing_chain_limit_is_lub:
  fixes f :: "nat \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun"
  assumes "increasing_chain f"
  (* We state the limits in real numbers because LIMSEQ_iff is only for type real_normed_vector,
  ureal is not of that type. *)
  shows "(\<lambda>n. ureal2real (f n (s, s'))) \<longlonglongrightarrow> (ureal2real (\<Squnion>n::\<nat>. f n (s, s')))"
*)

(* abbreviation "Ftwhilen n b P X \<equiv> (Ftwhile b P X) ^^ n" *)
(*
lemma "Complete_Partial_Order.chain (\<le>) {(Ftwhile b P)}"
*)
(*
lemma "Complete_Partial_Order2.cont Sup (\<le>) Sup (\<le>) (Ftwhile b P)"
  apply (simp add: cont_def)
  apply (simp add: pfun_defs)
  apply (auto)
  oops
  

definition ptwhile :: "('a time_scheme \<times> 'a time_scheme \<Rightarrow> \<bool>) \<Rightarrow> 'a time_scheme prhfun 
  \<Rightarrow> 'a time_scheme prhfun" ("while\<^sub>p\<^sub>t _ do _ od") where
"ptwhile b P = (while\<^sub>p b do (P; t := $t + 1) od)"

term "$t"
term "(t+1)\<^sub>e"

thm "ptwhile_def"

theorem ptwhile_unfold:
  assumes "\<forall>s. (\<lambda>v\<^sub>0. real_of_ereal (ureal2ereal (P (s, v\<^sub>0)))) summable_on UNIV"
  shows "while\<^sub>p\<^sub>t b do P od = (if\<^sub>c b then (P; t := $t + 1 ; (while\<^sub>p\<^sub>t b do P od)) else II)"
  apply (simp add: ptwhile_def)
  apply (rule pwhile_unfold)
  apply (simp add: pfun_defs)
  apply (expr_auto add: ureal_defs rel)
proof -
  fix t::"enat" and more :: "'a"
  have f1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a time_scheme.
            real_of_ereal (ureal2ereal (P (\<lparr>t\<^sub>v = t, \<dots> = more\<rparr>, v\<^sub>0'))) *
            real_of_ereal
             (ureal2ereal
               (ereal2ureal'
                 (ereal
                   (if v\<^sub>0'\<lparr>t\<^sub>v := t\<^sub>v v\<^sub>0' + (1::enat)\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>))))))
    = (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a time_scheme\<in>{s. t\<^sub>v s = t\<^sub>v v\<^sub>0 - 1} \<union> -{s. t\<^sub>v s = t\<^sub>v v\<^sub>0 - 1}.
            real_of_ereal (ureal2ereal (P (\<lparr>t\<^sub>v = t, \<dots> = more\<rparr>, v\<^sub>0'))) *
            real_of_ereal
             (ureal2ereal
               (ereal2ureal'
                 (ereal
                   (if v\<^sub>0'\<lparr>t\<^sub>v := t\<^sub>v v\<^sub>0' + (1::enat)\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>))))))"
    by simp
  also have f2: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a time_scheme\<in>{s. t\<^sub>v s = t\<^sub>v v\<^sub>0 - 1}.
            real_of_ereal (ureal2ereal (P (\<lparr>t\<^sub>v = t, \<dots> = more\<rparr>, v\<^sub>0'))) *
            real_of_ereal
             (ureal2ereal
               (ereal2ureal'
                 (ereal
                   (if v\<^sub>0'\<lparr>t\<^sub>v := t\<^sub>v v\<^sub>0' + (1::enat)\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>))))))"
    apply (subst infsum_Un_disjoint)
    sorry
  also have f3: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a time_scheme\<in>{s. t\<^sub>v s = t\<^sub>v v\<^sub>0 - 1}.
            real_of_ereal (ureal2ereal (P (\<lparr>t\<^sub>v = t, \<dots> = more\<rparr>, v\<^sub>0'))))"
    sorry
  have f4: "(\<lambda>v\<^sub>0::'a time_scheme. (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a time_scheme\<in>{s. t\<^sub>v s = t\<^sub>v v\<^sub>0 - 1}.
            real_of_ereal (ureal2ereal (P (\<lparr>t\<^sub>v = t, \<dots> = more\<rparr>, v\<^sub>0'))))) summable_on UNIV"
    sorry
  show " (\<lambda>v\<^sub>0::'a time_scheme.
           real_of_ereal
            (ureal2ereal
              (ereal2ureal'
                (min (max (0::ereal)
                       (ereal
                         (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a time_scheme.
                            real_of_ereal (ureal2ereal (P (\<lparr>t\<^sub>v = t, \<dots> = more\<rparr>, v\<^sub>0'))) *
                            real_of_ereal
                             (ureal2ereal
                               (ereal2ureal'
                                 (ereal
                                   (if v\<^sub>0'\<lparr>t\<^sub>v := t\<^sub>v v\<^sub>0' + (1::enat)\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>))))))))
                  (1::ereal))))) summable_on
       UNIV"
    sorry
qed

theorem ptwhile_unique_fixed_point:
  assumes "H\<^sub>1 = (if\<^sub>c b then (P; t := $t + 1 ; H\<^sub>1) else II)"
  assumes "H\<^sub>2 = (if\<^sub>c b then (P; t := $t + 1 ; H\<^sub>2) else II)"
  shows "H\<^sub>1 = H\<^sub>2"
proof (rule ccontr)
  assume a1: "\<not>H\<^sub>1 = H\<^sub>2"
  have "(if\<^sub>c b then (P; t := $t + 1 ; H\<^sub>1) else II) = H\<^sub>1"
    apply (simp add: pfun_defs)
    apply (expr_auto add: rel)
  qed

  thm "le_fun_def"

(*
  (if\<^sub>c b then (P; t := $t + 1 ; H\<^sub>1) else II)
= 
  (if b then (P; t := $t + 1 ; H\<^sub>1) else II)
=
  (if b then (P; H\<^sub>1[t+1/t]) else II)
=
  (if b then (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a time_scheme. P(s, v\<^sub>0) * H\<^sub>1(v\<^sub>0[t+1/t], s')) else s'=s)
= 
  (\<lbrakk>b\<rbrakk>\<^sub>\<I>*(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a time_scheme. P(s, v\<^sub>0) * H\<^sub>1(v\<^sub>0[t+1/t], s')) + \<lbrakk>\<not>b\<rbrakk>\<^sub>\<I>*
*)

subsection \<open> \<close>

lemma
*)
end
