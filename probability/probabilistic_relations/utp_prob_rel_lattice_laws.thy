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

subsection \<open> Infinite sum \<close>
lemma rvfun_prob_sum1_summable:
  assumes "is_final_distribution p"
  shows "\<forall>s. 0 \<le> p s \<and> p s \<le> 1" 
        "(\<Sum>\<^sub>\<infinity> s. p (s\<^sub>1, s)) = (1::\<real>)"
        "(\<lambda>s. p (s\<^sub>1, s)) summable_on UNIV"
  using assms apply (simp add: dist_defs expr_defs)
  using assms is_dist_def is_sum_1_def apply (metis (no_types, lifting) curry_conv infsum_cong)
proof (rule ccontr)
  assume a1: "\<not> (\<lambda>s. p (s\<^sub>1, s)) summable_on UNIV"
  from a1 have f1: "(\<Sum>\<^sub>\<infinity>s. p (s\<^sub>1, s)) = (0::\<real>)"
    by (simp add: infsum_def)
  then show "False"
    by (metis assms case_prod_eta curry_case_prod is_dist_def is_sum_1_def zero_neq_one)
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
lemma is_prob: "\<lbrakk>is_prob P\<rbrakk> \<Longrightarrow> (\<forall>s. P s \<ge> 0 \<and> P s \<le> 1)"
  by (simp add: is_prob_def taut_def)

lemma ureal_is_prob: "is_prob (rvfun_of_prfun P)"
  by (simp add: is_prob_def rvfun_of_prfun_def ureal_lower_bound ureal_upper_bound)

lemma is_prob_final_prob: "\<lbrakk>is_prob P\<rbrakk> \<Longrightarrow> is_final_prob P"
  by (simp add: is_prob_def taut_def)

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
  assumes "is_final_distribution p"
  assumes "\<forall>s. q s \<le> 1 \<and> q s \<ge> 0"
  shows "(\<lambda>s::'a. p (x, s) * q (s, y)) summable_on UNIV"
  apply (subst summable_on_iff_abs_summable_on_real)
  apply (rule abs_summable_on_comparison_test[where g = "\<lambda>s::'a. p (x, s)"])
  apply (metis assms(1) rvfun_prob_sum1_summable(3) summable_on_iff_abs_summable_on_real)
  using assms(2) by (smt (verit) SEXP_def mult_right_le_one_le norm_mult real_norm_def)

lemma rvfun_product_summable':
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "(\<lambda>s::'a. p (x, s) * q (s, y)) summable_on UNIV"
  apply (rule rvfun_product_summable)
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
lemma rvfun_pchoice_is_prob: 
  assumes "is_prob P" "is_prob Q"
  assumes "\<forall>s. 0 \<le> r s \<and> r s \<le> (1::\<real>)"
  shows "is_prob (P \<oplus>\<^sub>f\<^bsub>r\<^esub> Q)"
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (smt (verit, del_insts) SEXP_def assms(1) assms(2) assms(3) is_prob_def mult_nonneg_nonneg 
      taut_def)
  by (simp add: assms(1) assms(2) assms(3) convex_bound_le is_prob)

lemma rvfun_pchoice_is_dist: 
  assumes "is_final_distribution P" "is_final_distribution Q"
  assumes "\<forall>s. 0 \<le> r s \<and> r s \<le> (1::\<real>)"
  shows "is_final_distribution (P \<oplus>\<^sub>f\<^bsub>(r\<^sup>\<Up>)\<^esub> Q)"
  apply (simp add: dist_defs expr_defs, auto)
  apply (simp add: assms(1) assms(2) assms(3) is_final_distribution_prob is_final_prob_altdef)
  apply (simp add: assms(1) assms(2) assms(3) convex_bound_le is_final_distribution_prob is_final_prob_altdef)
  apply (subst infsum_add)
  apply (simp add: assms(1) rvfun_prob_sum1_summable(3) summable_on_cmult_right)
  apply (simp add: assms(2) rvfun_prob_sum1_summable(3) summable_on_cmult_right)
  apply (subst infsum_cmult_right)
  apply (simp add: assms(1) rvfun_prob_sum1_summable(3) summable_on_cmult_right)
  apply (subst infsum_cmult_right)
  apply (simp add: assms(2) rvfun_prob_sum1_summable(3) summable_on_cmult_right)
  by (simp add: assms(1) assms(2) rvfun_prob_sum1_summable(2))

lemma rvfun_pchoice_inverse: 
  assumes "is_prob P" "is_prob Q"
  assumes "\<forall>s. 0 \<le> r s \<and> r s \<le> (1::\<real>)"
  shows "rvfun_of_prfun (prfun_of_rvfun (P \<oplus>\<^sub>f\<^bsub>(r\<^sup>\<Up>)\<^esub> Q)) = (P \<oplus>\<^sub>f\<^bsub>(r\<^sup>\<Up>)\<^esub> Q)"
  apply (simp add: dist_defs expr_defs)
  apply (rule rvfun_inverse)
  apply (simp add: is_prob_def expr_defs, auto)
  apply (simp add: assms(1) assms(2) assms(3) is_prob)
  by (simp add: assms(1) assms(2) assms(3) convex_bound_le is_prob)

lemma rvfun_pchoice_inverse': 
  assumes "is_prob P" "is_prob Q"
  assumes "\<forall>s. 0 \<le> r s \<and> r s \<le> (1::\<real>)"
  shows "rvfun_of_prfun (prfun_of_rvfun (pchoice_f P [(r\<^sup>\<Up>)]\<^sub>e Q)) = pchoice_f P [(r\<^sup>\<Up>)]\<^sub>e Q"
  apply (simp add: dist_defs expr_defs)
  apply (rule rvfun_inverse)
  apply (simp add: is_prob_def expr_defs, auto)
  apply (simp add: assms(1) assms(2) assms(3) is_prob)
  by (simp add: assms(1) assms(2) assms(3) convex_bound_le is_prob)

lemma rvfun_pchoice_inverse_c: 
  assumes "is_prob P" "is_prob Q"
  assumes "0 \<le> r \<and> r \<le> (1::\<real>)"
  shows "rvfun_of_prfun (prfun_of_rvfun (P \<oplus>\<^sub>f\<^bsub>(\<lambda>s. r)\<^esub> Q)) = (P \<oplus>\<^sub>f\<^bsub>(\<lambda>s. r)\<^esub> Q)"
  apply (simp add: dist_defs expr_defs)
  apply (rule rvfun_inverse)
  apply (simp add: is_prob_def expr_defs, auto)
  apply (simp add: assms(1) assms(2) assms(3) is_prob)
  by (simp add: assms(1) assms(2) assms(3) convex_bound_le is_prob)

lemma rvfun_pchoice_inverse_c': 
  assumes "is_prob P" "is_prob Q"
  assumes "0 \<le> r \<and> r \<le> (1::\<real>)"
  shows "rvfun_of_prfun (prfun_of_rvfun (pchoice_f P [(\<lambda>s. r)]\<^sub>e Q)) = (pchoice_f P [(\<lambda>s. r)]\<^sub>e Q)"
  apply (simp add: dist_defs expr_defs)
  apply (rule rvfun_inverse)
  apply (simp add: is_prob_def expr_defs, auto)
  apply (simp add: assms(1) assms(2) assms(3) is_prob)
  by (simp add: assms(1) assms(2) assms(3) convex_bound_le is_prob)

theorem prfun_pchoice_commute: "if\<^sub>p r then P else Q = if\<^sub>p 1 - r then Q else P"
  apply (simp add: pfun_defs)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  by (auto)

theorem prfun_pchoice_zero: "if\<^sub>p 0 then P else Q = Q"
  apply (simp add: pfun_defs)
  by (simp add: SEXP_def prfun_inverse)

theorem prfun_pchoice_zero': 
  fixes w\<^sub>1 :: "'a \<Rightarrow> \<real>"
  assumes "`w\<^sub>1 = 0`"
  shows "P \<oplus>\<^bsub>w\<^sub>1\<^sup>\<Up>\<^esub> Q = Q"
  apply (simp add: pfun_defs)
proof -
  have f0: "\<forall>s. w\<^sub>1 s = 0"
    by (metis (mono_tags, lifting) SEXP_def assms taut_def)
  show "prfun_of_rvfun (pchoice_f (rvfun_of_prfun P) (w\<^sub>1\<^sup>\<Up>) (rvfun_of_prfun Q)) = Q"
    apply (simp add: f0 SEXP_def)
    by (simp add: prfun_inverse)
qed

theorem prfun_pchoice_one: "if\<^sub>p 1 then P else Q = P"
  apply (simp add: pfun_defs)
  by (simp add: SEXP_def prfun_inverse)

theorem prfun_pchoice_assoc:
  fixes w\<^sub>1 :: "'a \<Rightarrow> \<real>"
  assumes "`0 \<le> w\<^sub>1 \<and> w\<^sub>1 \<le> 1`"
  assumes "`0 \<le> w\<^sub>2 \<and> w\<^sub>2 \<le> 1`"
  assumes "`0 \<le> r\<^sub>1 \<and> r\<^sub>1 \<le> 1`"
  assumes "`((1 - w\<^sub>1) * (1 - w\<^sub>2)) = (1 - r\<^sub>2)`"
  assumes "`(w\<^sub>1) = (r\<^sub>1 * r\<^sub>2)`"
  shows "P \<oplus>\<^bsub>w\<^sub>1\<^sup>\<Up>\<^esub> (Q \<oplus>\<^bsub>w\<^sub>2\<^sup>\<Up>\<^esub> R) = (P \<oplus>\<^bsub>r\<^sub>1\<^sup>\<Up>\<^esub> Q) \<oplus>\<^bsub>r\<^sub>2\<^sup>\<Up>\<^esub> R" (is "?lhs = ?rhs")
proof -
  have f0: "`((1 - w\<^sub>1) * (1 - w\<^sub>2)) = (1 - w\<^sub>1 - w\<^sub>2 + w\<^sub>1 * w\<^sub>2)`"
    apply (simp add: taut_def)
    by (smt (verit, del_insts) left_diff_distrib mult.commute mult_cancel_right1)
  then have f1: "`(1 - w\<^sub>1 - w\<^sub>2 + w\<^sub>1 * w\<^sub>2) = (1 - r\<^sub>2)`"
    by (smt (verit, ccfv_threshold) SEXP_def assms(4) taut_def)
  then have f2: "`(r\<^sub>2) = (w\<^sub>1 + w\<^sub>2 - w\<^sub>1 * w\<^sub>2)`"
    by (smt (verit, del_insts) SEXP_apply taut_def)
  then have f3: "`0 \<le> r\<^sub>2 \<and> r\<^sub>2 \<le> 1`"
    using assms(1-2) by (smt (verit) SEXP_def f0 mult_le_one mult_nonneg_nonneg taut_def)
  have f4: "`(w\<^sub>1) = (r\<^sub>1 * (w\<^sub>1 + w\<^sub>2 - w\<^sub>1 * w\<^sub>2))`"
    using assms(5) f2 by (simp add: taut_def)
  have f5: "\<forall>s. ((1::\<real>) - (w\<^sub>1\<^sup>\<Up>) s) * ((1::\<real>) - (w\<^sub>2\<^sup>\<Up>) s) = (1 - (r\<^sub>2\<^sup>\<Up>) s)"
    using assms(4) by (simp add: taut_def)
  have f6: "pchoice_f (rvfun_of_prfun P) (w\<^sub>1\<^sup>\<Up>)
    (\<lambda>\<s>::'a \<times> 'b. (w\<^sub>2\<^sup>\<Up>) \<s> * rvfun_of_prfun Q \<s> + ((1::\<real>) - (w\<^sub>2\<^sup>\<Up>) \<s>) * rvfun_of_prfun R \<s>) = 
    (\<lambda>s::'a \<times> 'b. (w\<^sub>1\<^sup>\<Up>) s * rvfun_of_prfun P s + 
        ((1::\<real>) - (w\<^sub>1\<^sup>\<Up>) s) * ((w\<^sub>2\<^sup>\<Up>) s * rvfun_of_prfun Q s + ((1::\<real>) - (w\<^sub>2\<^sup>\<Up>) s) * rvfun_of_prfun R s))"
    using SEXP_def by blast
  then have f7: "... = (\<lambda>s::'a \<times> 'b. (w\<^sub>1\<^sup>\<Up>) s * rvfun_of_prfun P s + 
        ((1::\<real>) - (w\<^sub>1\<^sup>\<Up>) s) * (w\<^sub>2\<^sup>\<Up>) s * rvfun_of_prfun Q s + ((1::\<real>) - (w\<^sub>1\<^sup>\<Up>) s) * ((1::\<real>) - (w\<^sub>2\<^sup>\<Up>) s) * rvfun_of_prfun R s)" 
    apply (simp add: distrib_left)
    by (simp add: add.assoc mult.commute mult.left_commute)
  then have f8: "... = (\<lambda>s::'a \<times> 'b. (w\<^sub>1\<^sup>\<Up>) s * rvfun_of_prfun P s + 
        ((1::\<real>) - (w\<^sub>1\<^sup>\<Up>) s) * (w\<^sub>2\<^sup>\<Up>) s * rvfun_of_prfun Q s + (1 - (r\<^sub>2\<^sup>\<Up>) s) * rvfun_of_prfun R s)"
    using f5 by fastforce
  have f5': "\<forall>s. (r\<^sub>2\<^sup>\<Up>) s * (r\<^sub>1\<^sup>\<Up>) s = (w\<^sub>1\<^sup>\<Up>) s"
    using assms(5) by (simp add: taut_def)
  have f5'': "\<forall>s. (r\<^sub>2\<^sup>\<Up>) s * ((1::\<real>) - (r\<^sub>1\<^sup>\<Up>) s) = ((1::\<real>) - (w\<^sub>1\<^sup>\<Up>) s) * (w\<^sub>2\<^sup>\<Up>) s"
    by (smt (verit, best) f5 f5' mult_cancel_left1 right_diff_distrib')
  have f9: "pchoice_f (\<lambda>s::'a \<times> 'b. (r\<^sub>1\<^sup>\<Up>) s * rvfun_of_prfun P s + ((1::\<real>) - (r\<^sub>1\<^sup>\<Up>) s) * rvfun_of_prfun Q s) (r\<^sub>2\<^sup>\<Up>) (rvfun_of_prfun R) 
    =  (\<lambda>s::'a \<times> 'b. (r\<^sub>2\<^sup>\<Up>) s * ((r\<^sub>1\<^sup>\<Up>) s * rvfun_of_prfun P s + ((1::\<real>) - (r\<^sub>1\<^sup>\<Up>) s) * rvfun_of_prfun Q s) + 
      ((1::\<real>) - (r\<^sub>2\<^sup>\<Up>) s) * rvfun_of_prfun R s)"
    using SEXP_def by blast
  then have f10: "... = (\<lambda>s::'a \<times> 'b. (r\<^sub>2\<^sup>\<Up>) s * (r\<^sub>1\<^sup>\<Up>) s * rvfun_of_prfun P s + (r\<^sub>2\<^sup>\<Up>) s * ((1::\<real>) - (r\<^sub>1\<^sup>\<Up>) s) * rvfun_of_prfun Q s + 
      ((1::\<real>) - (r\<^sub>2\<^sup>\<Up>) s) * rvfun_of_prfun R s)"
    apply (simp add: distrib_left)
    by (simp add: add.assoc mult.commute mult.left_commute)
  then have f11: "... = (\<lambda>s::'a \<times> 'b. (w\<^sub>1\<^sup>\<Up>) s * rvfun_of_prfun P s + 
        ((1::\<real>) - (w\<^sub>1\<^sup>\<Up>) s) * (w\<^sub>2\<^sup>\<Up>) s * rvfun_of_prfun Q s + (1 - (r\<^sub>2\<^sup>\<Up>) s) * rvfun_of_prfun R s)"
    using f5' f5'' by fastforce
  show ?thesis
    apply (simp add: pfun_defs)
    apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
    apply (subst rvfun_pchoice_inverse)
    using assms(2) apply (simp add: taut_def)
    using ureal_is_prob apply blast
    using ureal_is_prob apply blast
     apply (metis (mono_tags, lifting) SEXP_def assms(2) taut_def)
    apply (subst rvfun_pchoice_inverse)
    using ureal_is_prob apply blast
    using ureal_is_prob apply blast
    using assms(3) apply (simp add: taut_def)
    by (simp add: f10 f5 f5' f5'' f7)
qed

theorem prfun_pchoice_assigns:
  "(if\<^sub>p r then x := e else y := f) = prfun_of_rvfun (r * \<lbrakk>\<lbrakk>x := e\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e + (1 - r) * \<lbrakk>\<lbrakk>y := f\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"
  apply (simp add: pfun_defs)
  apply (simp add: rvfun_assignment_inverse)
  by (expr_auto)

lemma prfun_pchoice_assigns_inverse:
  assumes "\<forall>s. 0 \<le> r s \<and> r s \<le> 1"
  shows "rvfun_of_prfun (if\<^sub>p (r\<^sup>\<Up>) then (x := e) else (y := f)) 
       = (pchoice_f (\<lbrakk>\<lbrakk>x := e\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e) (r\<^sup>\<Up>)\<^sub>e (\<lbrakk>\<lbrakk>y := f\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e))"
  apply (simp add: pfun_defs)
  apply (simp add: rvfun_assignment_inverse)
  apply (subst rvfun_pchoice_inverse)
  apply (simp add: rvfun_assignment_is_prob)+
  apply (simp add: assms)
  by (simp add: SEXP_def)

lemma prfun_pchoice_assigns_inverse_c:
  assumes "\<forall>s::'a. 0 \<le> r \<and> r \<le> 1"
  shows "rvfun_of_prfun ((x := e) \<oplus>\<^bsub>(\<lambda>s. r)\<^esub> (y := f)) 
       = (pchoice_f (\<lbrakk>\<lbrakk>x := e\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e) (\<guillemotleft>r\<guillemotright>)\<^sub>e (\<lbrakk>\<lbrakk>y := f\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e))"
  apply (simp add: pfun_defs)
  apply (simp add: rvfun_assignment_inverse)
  apply (subst rvfun_pchoice_inverse_c)
  apply (simp add: rvfun_assignment_is_prob)+
  apply (simp add: assms)
  by (simp add: SEXP_def)

lemma prfun_pchoice_assigns_inverse_c':
  assumes "\<forall>s::'a. 0 \<le> r \<and> r \<le> 1"
  shows "rvfun_of_prfun ((x := e) \<oplus>\<^bsub>[(\<lambda>s. r)]\<^sub>e\<^esub> (y := f)) 
       = (pchoice_f (\<lbrakk>\<lbrakk>x := e\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e) (\<guillemotleft>r\<guillemotright>)\<^sub>e (\<lbrakk>\<lbrakk>y := f\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e))"
  apply (simp add: pfun_defs)
  apply (simp add: rvfun_assignment_inverse)
  apply (subst rvfun_pchoice_inverse_c)
  apply (simp add: rvfun_assignment_is_prob)+
  apply (simp add: assms)
  by (simp add: SEXP_def)

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
  by (expr_auto)

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
lemma rvfun_seqcomp_is_prob: 
  assumes "is_final_distribution p" "is_prob q"
  shows "is_prob (pseqcomp_f p q)"
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: assms(1) assms(2) infsum_nonneg is_prob rvfun_prob_sum1_summable(1))
proof -
  fix a b
  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (a, v\<^sub>0) * q (v\<^sub>0, b)) \<le> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (a, v\<^sub>0))"
    apply (subst infsum_mono)
    apply (simp add: assms(1) assms(2) is_prob rvfun_product_summable)
    apply (simp add: assms(1) rvfun_prob_sum1_summable(3))
    apply (simp add: assms(1) assms(2) is_prob mult_right_le_one_le rvfun_prob_sum1_summable(1))
    by simp
  also have "... = 1"
    by (metis assms(1) infsum_cong rvfun_prob_sum1_summable(2))
  then show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (a, v\<^sub>0) * q (v\<^sub>0, b)) \<le> (1::\<real>)"
    using calculation by presburger
qed

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

lemma rvfun_is_dist_pcomp: 
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
  apply (simp add: assms rvfun_seqcomp_is_prob)
  using assms(1) assms(2) rvfun_is_dist_pcomp by blast

lemma prfun_zero_right: "P ; \<^bold>0 = \<^bold>0"
  apply (simp add: pfun_defs ureal_zero)
  apply (simp add: ureal_defs)
  by (simp add: SEXP_def ereal2ureal_def subst_app_expr_def zero_ureal_def)

lemma prfun_zero_left: "\<^bold>0 ; P = \<^bold>0"
  apply (simp add: pfun_defs ureal_zero)
  apply (simp add: ureal_defs)
  by (simp add: SEXP_def ereal2ureal_def subst_app_expr_def zero_ureal_def)

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

theorem prel_seqcomp_left_one_point: "x := e ; P = prel_of_rfrel (([ x\<^sup>< \<leadsto> e\<^sup>< ] \<dagger> @(rfrel_of_prel P)))\<^sub>e"
  apply (simp add: pfun_defs expr_defs)
  apply (subst rvfun_inverse)
  apply (simp add: dist_defs expr_defs)
  apply (rel_auto)
  apply (simp add: infsum_singleton)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (rel_auto)
  by (simp add: infsum_mult_singleton_left_1)

lemma prel_infsum_over_pair_subset_1:
  "(\<Sum>\<^sub>\<infinity> (s::'a, v\<^sub>0::'a). rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) = 1"
proof -
  have "(\<Sum>\<^sub>\<infinity> (s::'a, v\<^sub>0::'a). rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) = 
        (\<Sum>\<^sub>\<infinity> (s::'a, v\<^sub>0::'a) \<in> {(s::'a, v\<^sub>0::'a) | s v\<^sub>0. put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s}. rfrel_of_prel P (s\<^sub>1, v\<^sub>0))"
    apply (rule infsum_cong_neutral)
    apply force
    using DiffD2 prod.collapse apply fastforce
    by force
  then show ?thesis
    by (metis prel_infsum_over_pair_fst_discard prel_sum_1)
qed

lemma prel_infsum_swap:
 "(\<Sum>\<^sub>\<infinity>s::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) = 
  (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. \<Sum>\<^sub>\<infinity>s::'a. rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>)))"
  apply (rule infsum_swap_banach)
  apply (simp add: summable_on_def)
  apply (rule_tac x = "1" in exI)
  by (smt (verit, best) has_sum_infsum infsum_cong infsum_not_exists prel_infsum_over_pair_subset_1 split_cong)

lemma prel_infsum_infsum_subset_1:
  "(\<Sum>\<^sub>\<infinity>s::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) =
       (1::\<real>)"
  apply (simp add: prel_infsum_swap)
proof -
  have f0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (\<Sum>\<^sub>\<infinity>s::'a. rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>)))) 
    = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * (\<Sum>\<^sub>\<infinity>s::'a. (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>)))))"
    apply (subst infsum_cmult_right)
    apply (simp add: infsum_singleton_summable)
    by (simp)
  then have f1: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * 1))"
    by (simp add: infsum_singleton)
  then show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. \<Sum>\<^sub>\<infinity>s::'a. rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) = (1::\<real>)"
    using f0 prel_sum_1 by force
qed 


term "prel_of_rfrel (\<lbrakk> ($x\<^sup>< = e) \<rbrakk>\<^sub>\<I>\<^sub>e)"

(* This realed function is not a distribution *)
(*
lemma "is_final_distribution (\<lbrakk> ($x\<^sup>< = e\<^sup><) \<rbrakk>\<^sub>\<I>\<^sub>e)"
  apply (expr_auto)
  apply (simp add: dist_defs)
  apply (auto)
*)

(*
theorem prel_right_one_point: "P ; prel_of_rfrel (\<lbrakk> ($x\<^sup>< = e\<^sup><) \<rbrakk>\<^sub>\<I>\<^sub>e) 
    = prel_of_rfrel (([ x\<^sup>> \<leadsto> e\<^sup>> ] \<dagger> @(rfrel_of_prel P)))\<^sub>e"
  apply (simp add: pfun_defs expr_defs)
  apply (subst rvfun_inverse)
   apply (simp add: dist_defs expr_defs)
   apply (auto)
  sorry
*)

(* This is not a valid law. *)
(*
theorem prel_right_one_point: "P ; x := e = prel_of_rfrel (([ x\<^sup>> \<leadsto> e\<^sup>> ] \<dagger> @(rfrel_of_prel P)))\<^sub>e"
  apply (simp add: pfun_defs)
  apply (simp add: prel_set_conv_assign)
  apply (expr_auto add: rel)
  apply (simp add: infsum_mult_subset_right)
  apply (subst prel_of_rfrel_inject)
  apply (simp add: dist_defs expr_defs)
  apply (rel_auto)
      apply (simp add: infsum_nonneg prel_in_0_1')
     apply (subgoal_tac "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) 
      \<le> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. rfrel_of_prel P (s\<^sub>1, v\<^sub>0))")
  apply (simp add: prel_sum_1)
     apply (rule infsum_mono)
  apply (simp add: prel_mult_subset_right_summable)
  apply (simp add: prel_summable)
  apply (simp add: prel_in_0_1')
  apply (simp add: prel_infsum_infsum_subset_1)
  apply (simp add: dist_defs expr_defs)
  apply (auto)
  apply (simp add: prel_in_0_1')+
  apply (simp add: lens_defs)
     apply (rule infsumI)
    apply (simp add: has_sum_def)
    apply (subst topological_tendstoI)
    apply (auto)
    apply (simp add: eventually_finite_subsets_at_top)
    apply (rule_tac x = "{v\<^sub>0. put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s}" in exI)
     apply (auto)
  sledgehammer
    apply (subgoal_tac "(\<Sum>v\<^sub>0::'a\<in>Y.
        (if put\<^bsub>x\<^esub> s\<^sub>1 (e s\<^sub>1) = v\<^sub>0 then 1::\<real> else (0::\<real>)) *
        (if put\<^bsub>y\<^esub> v\<^sub>0 (f v\<^sub>0) = put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> s\<^sub>1 (e s\<^sub>1)) (f (put\<^bsub>x\<^esub> s\<^sub>1 (e s\<^sub>1))) then 1::\<real> else (0::\<real>))) 
      = 1")
    apply presburger
    apply (simp add: sum.remove)
    apply (subst sum_nonneg_eq_0_iff)
    apply (simp)+
    apply force
  apply (subst infsum_mult_singleton_right)
  apply (simp add: infsum_mult_singleton_right_1 prel_in_0_1')
  apply (simp add: prel_infsum_infsum_mult_singleton_1)
  apply (simp add: dist_defs expr_defs)
  apply (auto)
  using prel_in_0_1' apply blast+
  apply (simp add: lens_defs)
  apply (simp add: prel_sum_1)
  apply (rel_auto)
  by (simp add: infsum_mult_singleton_left)
*)
(* In order to prove this law, we need to restrict P Q to distributions *)
(*
lemma passign_pif_simp:
  assumes "\<forall>s. 0 \<le> r s \<and> r s \<le> 1"
  shows "(x := c) ; (if\<^sub>p (r) then P else Q) = 
    prel_of_rfrel (r * ([ x\<^sup>> \<leadsto> c\<^sup>> ] \<dagger> @(rfrel_of_prel P)) +  (1-r) * ([ x\<^sup>> \<leadsto> c\<^sup>> ] \<dagger> @(rfrel_of_prel Q)))\<^sub>e"
  apply (simp add: pfun_defs expr_defs)
  apply (subst rvfun_inverse)
   apply (simp add: dist_defs expr_defs)
  apply (rel_auto)
  apply (simp add: infsum_singleton)
  apply (subst rvfun_inverse)
   apply (simp add: dist_defs expr_defs)
   apply (auto)
     apply (simp add: assms prel_in_0_1')
  apply (simp add: assms convex_bound_le prel_in_0_1')
  apply (subst prel_of_rfrel_inject)
    apply (simp add: dist_defs expr_defs)
    apply (auto)
     apply (simp add: assms infsum_nonneg rfrel_of_prel_in_0_1)
  apply (rel_auto)
  apply (subgoal_tac "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a.
          (if put\<^bsub>x\<^esub> a (c a) = v\<^sub>0 then 1::\<real> else (0::\<real>)) *
          (r (v\<^sub>0, b) * rfrel_of_prel P (v\<^sub>0, b) + ((1::\<real>) - r (v\<^sub>0, b)) * rfrel_of_prel Q (v\<^sub>0, b))) = 1")
     apply simp
  apply (rule infsumI)
    apply (simp add: has_sum_def)
    apply (subst topological_tendstoI)
    apply (auto)
    apply (simp add: eventually_finite_subsets_at_top)
    apply (rule_tac x = "{put\<^bsub>x\<^esub> a (c a)}" in exI)
    apply (auto)
  apply (subgoal_tac "(\<Sum>v\<^sub>0::'a\<in>Y.
          (if put\<^bsub>x\<^esub> a (c a) = v\<^sub>0 then 1::\<real> else (0::\<real>)) *
          (r (v\<^sub>0, b) * rfrel_of_prel P (v\<^sub>0, b) + ((1::\<real>) - r (v\<^sub>0, b)) * rfrel_of_prel Q (v\<^sub>0, b))) 
      = 1")
    apply presburger
    apply (simp add: sum.remove)
    apply (subgoal_tac "(\<Sum>v\<^sub>0::'a\<in>Y - {put\<^bsub>x\<^esub> a (c a)}.
          (if put\<^bsub>x\<^esub> a (c a) = v\<^sub>0 then 1::\<real> else (0::\<real>)) *
          (r (v\<^sub>0, b) * rfrel_of_prel P (v\<^sub>0, b) + ((1::\<real>) - r (v\<^sub>0, b)) * rfrel_of_prel Q (v\<^sub>0, b))) = 0")
    apply (subgoal_tac "r (put\<^bsub>x\<^esub> a (c a), b) * rfrel_of_prel P (put\<^bsub>x\<^esub> a (c a), b) + 
      ((1::\<real>) - r (put\<^bsub>x\<^esub> a (c a), b)) * rfrel_of_prel Q (put\<^bsub>x\<^esub> a (c a), b) = 1") 
    defer
    apply (smt (verit) DiffE mult_eq_0_iff singleton_iff sum.not_neutral_contains_not_neutral)
*)

theorem prel_seqcomp_assoc: "(P::'a phrel) ; (Q ; R) = (P ; Q) ; R"
  apply (simp add: pfun_defs)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (subst rvfun_inverse)
  apply (expr_auto add: dist_defs)
  apply (simp add: infsum_nonneg prel_in_0_1')
  apply (subst prel_infsum_pcomp_lessthan_1)
  apply (simp add: prel_is_dist)+
  apply (simp add: prel_infsum_pcomp_sum_1 prel_is_dist)
  apply (subst rvfun_inverse)
  apply (expr_auto add: dist_defs)
  apply (simp add: infsum_nonneg prel_in_0_1')
  apply (subst prel_infsum_pcomp_lessthan_1)
  apply (simp add: prel_is_dist)+
  apply (simp add: prel_infsum_pcomp_sum_1 prel_is_dist)
  apply (expr_auto)
proof -
  fix a and b :: "'a"
  let ?q = "\<lambda>(v\<^sub>0, b). (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a. rfrel_of_prel Q (v\<^sub>0, v\<^sub>0') * rfrel_of_prel R (v\<^sub>0', b))"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. rfrel_of_prel P (a, v\<^sub>0) *
          (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a. rfrel_of_prel Q (v\<^sub>0, v\<^sub>0') * rfrel_of_prel R (v\<^sub>0', b)))"
  let ?lhs' = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a.(\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a.  
      rfrel_of_prel P (a, v\<^sub>0) * rfrel_of_prel Q (v\<^sub>0, v\<^sub>0') * rfrel_of_prel R (v\<^sub>0', b)))"
  let ?rhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a.
          (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a. rfrel_of_prel P (a, v\<^sub>0') * rfrel_of_prel Q (v\<^sub>0', v\<^sub>0)) 
          * rfrel_of_prel R (v\<^sub>0, b))"
  let ?rhs' = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a. 
          rfrel_of_prel P (a, v\<^sub>0') * rfrel_of_prel Q (v\<^sub>0', v\<^sub>0) * rfrel_of_prel R (v\<^sub>0, b)))"

  have lhs_1: "(\<forall>v\<^sub>0::'a. rfrel_of_prel P (a, v\<^sub>0) *
          (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a. rfrel_of_prel Q (v\<^sub>0, v\<^sub>0') * rfrel_of_prel R (v\<^sub>0', b))
      = (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a. 
          rfrel_of_prel P (a, v\<^sub>0) * rfrel_of_prel Q (v\<^sub>0, v\<^sub>0') * rfrel_of_prel R (v\<^sub>0', b)))"
    apply (rule allI)
    by (metis (no_types, lifting) ab_semigroup_mult_class.mult_ac(1) infsum_cmult_right' infsum_cong)
  then have lhs_eq: "?lhs = ?lhs'"
    by presburger

  have rhs_1: "(\<forall>v\<^sub>0::'a. (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a. rfrel_of_prel P (a, v\<^sub>0') * rfrel_of_prel Q (v\<^sub>0', v\<^sub>0)) 
          * rfrel_of_prel R (v\<^sub>0, b)
      = (\<Sum>\<^sub>\<infinity>v\<^sub>0'::'a. 
          rfrel_of_prel P (a, v\<^sub>0') * rfrel_of_prel Q (v\<^sub>0', v\<^sub>0) * rfrel_of_prel R (v\<^sub>0, b)))"
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
    apply (simp add: prel_in_0_1')
    apply (subst mult.assoc)
    apply (rule summable_on_cmult_right)
    apply (rule prel_product_summable')
    apply (simp add: prel_is_dist)+
    apply (subst abs_of_nonneg)
    apply (subst abs_of_nonneg)
    apply (simp add: prel_in_0_1')
    apply (simp add: infsum_nonneg prel_in_0_1')
    apply (subst abs_of_nonneg)
    apply (simp add: prel_in_0_1')
    apply (subst mult.assoc)
    apply (subst infsum_cmult_right)
    apply (rule prel_product_summable')
    apply (simp add: prel_is_dist)+
    apply (subst summable_on_iff_abs_summable_on_real)
    apply (rule abs_summable_on_comparison_test[where g = "\<lambda>s::'a. rfrel_of_prel P (a, s)"])
    apply (metis prel_summable_on_subset summable_on_iff_abs_summable_on_real)
    apply (subgoal_tac "(\<Sum>\<^sub>\<infinity>y::'a. rfrel_of_prel Q (x, y) * rfrel_of_prel R (y, b)) \<le> 1")
    apply (simp add: infsum_nonneg mult_right_le_one_le prel_in_0_1')
    apply (subst prel_infsum_pcomp_lessthan_1)
    by (simp add: prel_is_dist)+

  then show "?lhs = ?rhs"
    using lhs_eq rhs_eq by presburger
qed

theorem "P ; (if\<^sub>p r then Q else R) = (if\<^sub>p r then (P ; Q) else (P ; R))"
  oops

subsection \<open> Chains \<close>
theorem increasing_chain_mono:
  assumes "increasing_chain f"
  assumes "m \<le> n"
  shows "f m \<le> f n"
  using assms(1) assms(2) increasing_chain_def by blast

theorem decreasing_chain_antitone:
  assumes "decreasing_chain f"
  assumes "m \<le> n"
  shows "f m \<ge> f n"
  using assms(1) assms(2) decreasing_chain_def by blast

thm "SUP_least"
lemma increasing_chain_limit_exists_element:
  fixes f :: "nat \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun"
  assumes "increasing_chain f"
  assumes "\<exists>n. f n (s, s') > 0"
  shows "\<forall> e > 0. \<exists>m. f m (s, s') > (\<Squnion>n::\<nat>. f n (s, s')) - e"
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
  apply (subst pcond_mono)
  apply (subst pseqcomp_mono)
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

lemma 
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  shows "(ureal2real (Fwhile b P X (s,s')) - ureal2real (Fwhile b P Y (s,s'))) = 
    ureal2real 1"
  apply (simp add: Fwhile_def)
  apply (simp add: prel_pcond_pchoice_eq)
  apply (simp add: pfun_defs)
  apply (simp add: rvfun_skip_inverse)
  apply (expr_auto add: rel)
  oops

theorem pwhile_unfold:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
  shows "while\<^sub>p b do P od = (if\<^sub>c b then (P ; (while\<^sub>p b do P od)) else II)"
proof -
  have m:"mono (\<lambda>X. (if\<^sub>c b then (P ; X) else II))"
    apply (simp add: mono_def, auto)
    apply (subst pcond_mono)
    apply (subst pseqcomp_mono)
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

lemma fzero_zero: "prfun_of_rvfun (rvfun_of_prfun \<^bold>0) = \<^bold>0"
  apply (simp add: ureal_defs)
  by (metis SEXP_def max.idem min.absorb1 real_of_ereal_0 ureal2ereal_inverse zero_ereal_def 
      zero_less_one_ereal zero_ureal.rep_eq)

theorem pwhile_true: "while\<^sub>p (true)\<^sub>e do P od = 0\<^sub>p"
  apply (simp add: pwhile_def pcond_def pzero_def)
  apply (rule antisym)
  apply (rule lfp_lowerbound)
  apply (simp add: Fwhile_def)
  apply (simp add: prfun_zero_right)
  apply (simp add: pfun_defs)
  apply (simp add: ureal_zero ureal_zero')
  by (rule ureal_bottom_least)

text \<open> Can we use approximation chain in UTP (Ch. 2.7) to prove a unique fix point for a probabilistic 
iteration?
\<close>
lemma "iterate 0 b P 0\<^sub>p = 0\<^sub>p"
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

lemma iterate_chain:
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

lemma iterate_continuous_limit:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
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
  have Sn_limit_sup: "(\<lambda>n. ureal2real (?f n (s, s'))) \<longlonglongrightarrow> (ureal2real (\<Squnion>n::\<nat>. ?f n (s, s')))"
    apply (subst increasing_chain_limit_is_lub)
    apply (simp add: assms increasing_chain_def iterate_increasing2)
    by simp
  then have Sn_limit: "\<forall>r>0. \<exists>no::\<nat>. \<forall>n\<ge>no.
             \<bar>ureal2real (?f n (s, s')) - ureal2real (\<Squnion>n::\<nat>. ?f n (s, s'))\<bar> < r"
    using Sn_limit_sup LIMSEQ_iff by (smt (verit, del_insts) real_norm_def)
  have exist_N: "\<exists>no::\<nat>. \<forall>n\<ge>no. \<bar>ureal2real (?f n (s, s')) - ureal2real (\<Squnion>n::\<nat>. ?f n (s, s'))\<bar> < r"
    using Sn_limit a1 by blast
  obtain N where P_N: "\<forall>n\<ge>N. \<bar>ureal2real (?f n (s, s')) - ureal2real (\<Squnion>n::\<nat>. ?f n (s, s'))\<bar> < r"
    using exist_N by blast
  have "\<forall>n. ureal2real (?f n (s, s')) \<le> ureal2real (\<Squnion>n::\<nat>. ?f n (s, s'))"
    by (meson SUP_upper UNIV_I ureal2real_mono)
  then have P_N': "\<forall>n\<ge>N. ureal2real (\<Squnion>n::\<nat>. ?f n (s, s')) - ureal2real (?f n (s, s')) < r"
    using P_N by force
  (* *)
  have "\<forall>n\<ge>N. (ureal2real (Fwhile b P (\<Squnion>n::\<nat>. iterate\<^sub>p n b P 0\<^sub>p) (s, s')) - 
     ureal2real (Fwhile b P (iterate\<^sub>p n b P 0\<^sub>p) (s, s'))) < r"
    sorry
  show " \<exists>no::\<nat>. \<forall>n\<ge>no.
             \<bar>ureal2real (Fwhile b P (iterate\<^sub>p n b P 0\<^sub>p) (s, s')) -
              ureal2real (Fwhile b P (\<Squnion>n::\<nat>. iterate\<^sub>p n b P 0\<^sub>p) (s, s'))\<bar> < r"
    apply (simp add: Fwhile_def)
    sorry
  qed

lemma iterate_continuous:
  assumes "is_final_distribution (rvfun_of_prfun (P::('s, 's) prfun))"
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
  then have "(\<lambda>n. ureal2real (?f n (s, s'))) \<longlonglongrightarrow> (ureal2real (\<Squnion>n::\<nat>. ?f n (s, s')))"
    by (rule increasing_chain_limit_is_lub) 
  then have "ureal2real (\<Squnion>n::\<nat>. ?f n (s, s')) = ureal2real ((Fwhile b P (\<Squnion>n::nat. iterate n b P 0\<^sub>p)) (s, s'))"
    using iterate_continuous_limit assms by (metis LIMSEQ_unique)
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
