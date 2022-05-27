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

lemma rvfun_assignment_inverse: "rvfun_of_prfun (prfun_of_rvfun (passigns_f \<sigma>)) = (passigns_f \<sigma>)"
  by (simp add: is_prob_def iverson_bracket_def rvfun_inverse)

subsubsection \<open> Conditional choice \<close>
lemma rvfun_pcond_is_prob: 
  assumes "is_prob P" "is_prob Q"
  shows "is_prob (P \<lhd>\<^sub>f b \<rhd> Q)"
  by (smt (verit, best) SEXP_def assms(1) assms(2) is_prob_def taut_def)

lemma rvfun_pcond_is_dist: 
  assumes "is_final_distribution P" "is_final_distribution Q"
  shows "is_final_distribution (P \<lhd>\<^sub>f b \<rhd> Q)"
  apply (simp add: dist_defs expr_defs, auto)
  apply (simp add: assms is_final_distribution_prob is_final_prob_altdef)+

lemma rvfun_assignment_inverse: "rvfun_of_prfun (prfun_of_rvfun (passigns_f \<sigma>)) = (passigns_f \<sigma>)"
  by (simp add: is_prob_def iverson_bracket_def rvfun_inverse)

lemma prfun_pcond_pchoice_eq: "(if\<^sub>c b then P else Q) = (if\<^sub>p \<lbrakk>b\<rbrakk>\<^sub>\<I> then P else Q)"
  apply (simp add: pfun_defs)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  by (expr_auto)

lemma pcond_mono: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2; Q\<^sub>1 \<le> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (if\<^sub>c b then P\<^sub>1 else Q\<^sub>1) \<le> (if\<^sub>c b then P\<^sub>2 else Q\<^sub>2)"
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
lemma prfun_zero_right: "P ; \<^bold>0 = \<^bold>0"
  apply (simp add: pfun_defs ureal_zero)
  apply (simp add: ureal_defs)
  by (simp add: SEXP_def ereal2ureal_def subst_app_expr_def zero_ureal_def)

lemma prfun_zero_left: "\<^bold>0 ; P = \<^bold>0"
  apply (simp add: pfun_defs ureal_zero)
  apply (simp add: ureal_defs)
  by (simp add: SEXP_def ereal2ureal_def subst_app_expr_def zero_ureal_def)


print_classes
lemma pseqcomp_mono: 
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
  (*
  proof -
    have f1: "\<forall>e ea. min (e::ereal) ea = (if e \<le> ea then e else ea)"
      using min_def by blast
    have f2: "\<forall>e ea. (e::ereal) \<le> max e ea"
      using max.cobounded1 by blast
    have f3: "\<forall>e ea eb. (max (e::ereal) ea \<le> eb) = (e \<le> eb \<and> ea \<le> eb)"
      using max.bounded_iff by blast
    have f4: "max (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b))))) (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b))))) \<le> max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b)))))"
      by (simp add: \<open>(\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. real_of_ereal (ureal2ereal ((P\<^sub>1::'s \<times> 's \<Rightarrow> ureal) (a::'s, v\<^sub>0))) * real_of_ereal (ureal2ereal ((Q\<^sub>1::'s \<times> 's \<Rightarrow> ureal) (v\<^sub>0, b::'s)))) \<le> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. real_of_ereal (ureal2ereal ((P\<^sub>2::'s \<times> 's \<Rightarrow> ureal) (a, v\<^sub>0))) * real_of_ereal (ureal2ereal ((Q\<^sub>2::'s \<times> 's \<Rightarrow> ureal) (v\<^sub>0, b))))\<close>)
    { assume "max (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b))))) (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b))))) \<le> 1"
      moreover
      { assume "(0::ereal) \<le> 1 \<and> ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b)))) \<le> 1"
        then have "max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b))))) = (if max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b))))) \<le> 1 then max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b))))) else 1) \<and> min (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b)))))) 1 = ureal2ereal (ereal2ureal' (min (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b)))))) 1))"
          by (simp add: ereal2ureal'_inverse)
        moreover
        { assume "\<not> max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b))))) = ureal2ereal (ereal2ureal' (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b)))))))"
          then have "\<not> max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b))))) \<le> 1"
            using f2 by (smt (z3) atLeastAtMost_iff ereal2ureal'_inverse) }
        ultimately have "max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b))))) \<le> 1 \<longrightarrow> ureal2ereal (ereal2ureal' (min (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b)))))) 1)) \<le> ureal2ereal (ereal2ureal' (min (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b)))))) 1))"
          using f4 f3 f2 f1 by (smt (z3)) }
      ultimately have "max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b))))) \<le> 1 \<longrightarrow> ureal2ereal (ereal2ureal' (min (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b)))))) 1)) \<le> ureal2ereal (ereal2ureal' (min (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b)))))) 1)) \<or> \<not> (0::ereal) \<le> 1 \<or> \<not> ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b)))) \<le> 1"
        using f3 by blast }
    moreover
    { assume "\<not> max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b))))) \<le> 1"
      then have "ureal2ereal (ereal2ureal' (min (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b)))))) 1)) \<le> ureal2ereal (ereal2ureal' (min (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b)))))) 1)) \<or> ereal2ureal' (min (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b)))))) 1) \<le> ereal2ureal' (min (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b)))))) 1)"
        using f3 by (smt (z3) atLeastAtMost_iff ereal2ureal'_inverse le_cases3 min_def_raw) }
    ultimately show ?thesis
      using f3 by (smt (z3) \<open>(\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. real_of_ereal (ureal2ereal ((P\<^sub>1::'s \<times> 's \<Rightarrow> ureal) (a::'s, v\<^sub>0))) * real_of_ereal (ureal2ereal ((Q\<^sub>1::'s \<times> 's \<Rightarrow> ureal) (v\<^sub>0, b::'s)))) \<le> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. real_of_ereal (ureal2ereal ((P\<^sub>2::'s \<times> 's \<Rightarrow> ureal) (a, v\<^sub>0))) * real_of_ereal (ureal2ereal ((Q\<^sub>2::'s \<times> 's \<Rightarrow> ureal) (v\<^sub>0, b))))\<close> ereal_max less_eq_ureal.rep_eq)
  qed *)
    by (smt (z3) atLeastAtMost_iff ereal2ureal'_inverse ereal_less_eq(3) ereal_less_eq(4) 
        ereal_less_eq(7) ereal_max_0 less_eq_ureal.rep_eq linorder_le_cases max.absorb_iff2 
        min.absorb1 min.absorb2) 
qed

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
