section \<open> (Parametric) Coin flip_t \<close>

theory utp_prob_rel_lattice_coin
  imports 
    "UTP_prob_relations.utp_prob_rel" 
    "HOL-Analysis.Infinite_Set_Sum"
begin 

unbundle UTP_Syntax

declare [[show_types]]

subsection \<open> Single coin flip_t without time\<close>

datatype Tcoin = chead | ctail
thm "Tcoin.exhaust"

alphabet cstate = 
  c :: Tcoin

definition cflip:: "cstate prhfun" where
"cflip = if\<^sub>p 0.5 then (c := chead) else (c := ctail)"

definition cflip_loop where
"cflip_loop = while\<^sub>p (c\<^sup>< = ctail)\<^sub>e do cflip od"

definition cH :: "cstate rvhfun" where 
"cH = (\<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"

definition cH':: "cstate rvhfun" where  
"cH' = (\<lbrakk>c\<^sup>< = chead\<rbrakk>\<^sub>\<I>\<^sub>e * (\<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e) + \<lbrakk>\<not>c\<^sup>< = chead\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"

lemma "cH = cH'"
  apply (simp add: cH_def cH'_def)
  by (expr_auto)

lemma r_simp: "rvfun_of_prfun [\<lambda>\<s>::cstate \<times> cstate. p]\<^sub>e = (\<lambda>s. ureal2real p)"
  by (simp add: SEXP_def rvfun_of_prfun_def)

lemma cflip_is_dist: "is_final_distribution (rvfun_of_prfun cflip)"
  apply (simp add: cflip_def pfun_defs)
  apply (subst rvfun_assignment_inverse)+
  apply (simp add: r_simp)
  apply (subst rvfun_pchoice_inverse_c)
  apply (simp add: rvfun_assignment_is_prob)+
  using rvfun_pchoice_is_dist'
  using rvfun_assignment_is_dist by fastforce

lemma cflip_altdef: "rvfun_of_prfun cflip = (\<lbrakk>\<Squnion> v \<in> {ctail, chead}. c := \<guillemotleft>v\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e / 2)\<^sub>e"
  apply (simp add: cflip_def pfun_defs)
  apply (subst rvfun_assignment_inverse)+
  apply (simp add: r_simp)
  apply (subst rvfun_pchoice_inverse_c)
  apply (simp add: rvfun_assignment_is_prob)+
  apply (pred_auto)
  by (simp add: ereal2ureal_def real2uereal_inverse' ureal2real_def)+

lemma cstate_UNIV_set: "(UNIV::\<bbbP> cstate) = {\<lparr>c\<^sub>v = chead\<rparr>, \<lparr>c\<^sub>v = ctail\<rparr>}"
  apply (auto)
  by (metis Tcoin.exhaust cstate.cases)

lemma cstate_head: "{s::cstate. c\<^sub>v s = chead} = {\<lparr>c\<^sub>v = chead\<rparr>}"
  apply (subst set_eq_iff)
  by (auto)

lemma cstate_tail: "{s::cstate. c\<^sub>v s = ctail} = {\<lparr>c\<^sub>v = ctail\<rparr>}"
  apply (subst set_eq_iff)
  by (auto)

lemma cstate_rel_UNIV_set:
  "{s::cstate \<times> cstate. True} = {(\<lparr>c\<^sub>v = chead\<rparr>, \<lparr>c\<^sub>v = chead\<rparr>), 
  (\<lparr>c\<^sub>v = chead\<rparr>, \<lparr>c\<^sub>v = ctail\<rparr>),  (\<lparr>c\<^sub>v = ctail\<rparr>, \<lparr>c\<^sub>v = ctail\<rparr>), (\<lparr>c\<^sub>v = ctail\<rparr>, \<lparr>c\<^sub>v = chead\<rparr>)}"
  apply (simp)
  apply (subst set_eq_iff)
  apply (rule allI)
  apply (rule iffI)
  apply (clarify)
  using cstate_UNIV_set apply blast
  apply (clarify)
  by blast

lemma ureal2real_1_2: "ureal2real (ereal2ureal (ereal (1::\<real>))) / (2::\<real>) = (1::\<real>) / (2::\<real>)"
  apply (simp add: ureal_defs)
  using real_1 by presburger

lemma sum_1_2: "(sum ((^) ((1::\<real>) / (2::\<real>))) {Suc (0::\<nat>)..n} +
               ((1::\<real>) / (2::\<real>)) ^ n / (2::\<real>)) = 
  (sum ((^) ((1::\<real>) / (2::\<real>))) {Suc (0::\<nat>)..n+1})"
  by (metis (no_types, lifting) One_nat_def Suc_1 Suc_eq_plus1 add_is_0 less_Suc0 one_neq_zero 
      one_power2 power_Suc power_add power_one_over sum.cl_ivl_Suc times_divide_eq_left times_divide_eq_right)

lemma sum_geometric_series: 
  (* "(sum ((^) ((1::\<real>) / (2::\<real>))) {Suc (0::\<nat>)..n + (1::\<nat>)}) = (1 - 1 / 2 ^ (n+2)) / (1 - 1/2) - 1" *)
  "(sum ((^) ((1::\<real>) / (2::\<real>))) {Suc (0::\<nat>)..n + (1::\<nat>)}) = 1 - 1 / 2 ^ (n+1)"
  apply (induction n)
  apply (simp)
  by (simp add: power_one_over sum_gp)

lemma sum_geometric_series_1: 
  "(sum ((^) ((1::\<real>) / (2::\<real>))) {1..n + (1::\<nat>)}) = 1 - 1 / 2 ^ (n+1)"
  apply (induction n)
   apply (simp)
  using One_nat_def sum_geometric_series by presburger

lemma sum_geometric_series': 
  "(sum ((^) ((1::\<real>) / (2::\<real>))) {Suc (0::\<nat>)..n}) = 1 - 1 / 2 ^ (n)"
  apply (induction n)
  apply (simp)
  by (simp add: power_one_over sum_gp)

lemma sum_geometric_series_ureal:
  "ureal2real (ereal2ureal (ereal (sum ((^) ((1::\<real>) / (2::\<real>))) {Suc (0::\<nat>)..n + (1::\<nat>)}))) / (2::\<real>)
  = (1 - 1 / 2 ^ (n+1))/2"
  apply (subst sum_geometric_series)
  apply (simp add: ureal_defs)
  apply (subst real2uereal_inverse)
  using max.cobounded1 apply blast
   apply simp
  apply (simp add: max_def)
  by (smt (z3) one_le_power)

lemma iterate_cflip_bottom_simp:
  shows "iter\<^sub>p 0 (c\<^sup>< = ctail)\<^sub>e cflip 0\<^sub>p = 0\<^sub>p"
        "iter\<^sub>p (Suc 0) (c\<^sup>< = ctail)\<^sub>e cflip 0\<^sub>p = (\<lbrakk>$c\<^sup>< = chead \<and> $c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)"
        "iter\<^sub>p (n+2) (c\<^sup>< = ctail)\<^sub>e cflip 0\<^sub>p = 
              (\<lbrakk>$c\<^sup>< = chead \<and> $c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e + 
               \<lbrakk>$c\<^sup>< = ctail \<and> $c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e * (\<Sum>i\<in>{1..\<guillemotleft>n+1\<guillemotright>}. (1/2)^i))\<^sub>e"
  apply (auto)
  apply (simp add: loopfunc_def)
  apply (simp add: prfun_zero_right')
  apply (simp add: pfun_defs)
  apply (subst rvfun_skip_inverse)
  apply (subst ureal_zero)
  apply (simp add: ureal_defs)
  apply (subst fun_eq_iff)
  apply (pred_auto)
  apply (meson Tcoin.exhaust)
  apply (induct_tac n)
  apply (simp)
  apply (simp add: loopfunc_def)
  apply (simp add: prfun_zero_right')
  apply (simp add: pfun_defs)
  apply (subst rvfun_skip_inverse)+
  apply (subst ureal_zero)
  apply (subst rvfun_pcond_inverse)
  apply (metis ureal_is_prob ureal_zero)
  apply (simp add: rvfun_skip_f_is_prob)
  apply (subst cflip_altdef)
  apply (subst rvfun_inverse)
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: infsum_nonneg iverson_bracket_def)
  apply (pred_auto)
  apply (simp add: cstate_UNIV_set)
  apply (smt (verit, ccfv_SIG) prfun_in_0_1' rvfun_skip_inverse)
  apply (simp add: prfun_of_rvfun_def)
  apply (simp only: skip_def)
  apply (expr_auto add: assigns_r_def)
  apply (simp add: real2ureal_def)
  apply (smt (verit, best) SEXP_def case_prod_conv cstate.select_convs(1) cstate.surjective div_0 infsum_0 mult_cancel_right1 real2ureal_def rvfun_skip\<^sub>_f_simp skip_def snd_conv)
  apply (meson Tcoin.exhaust)
  apply (simp add: cstate_UNIV_set)
  apply (pred_auto)
  apply (simp add: real2ureal_def)
  using real2ureal_def apply blast+
  apply (simp add: cstate_UNIV_set)
  apply (pred_auto)
  using real2ureal_def apply blast+
  apply (simp add: cstate_UNIV_set)
  apply (pred_auto)
  using real2ureal_def apply blast+
  (* *)
  apply (simp)
  apply (subst loopfunc_def)
  apply (subst pseqcomp_def)
  apply (subst pcond_def)
  apply (subst cflip_altdef)
  apply (subst rvfun_inverse)
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: infsum_nonneg  prfun_in_0_1')
  apply (pred_auto)
  apply (simp add: cstate_UNIV_set)
  apply (simp add: rvfun_of_prfun_def)
  apply (auto)
  apply (smt (verit, best) field_sum_of_halves ureal_upper_bound)
  using ureal_upper_bound apply blast
  apply (subst prfun_of_rvfun_def)
  apply (subst rvfun_of_prfun_def)+
  apply (expr_auto)
  apply (simp add: cstate_UNIV_set)
  apply (pred_auto)
  defer
  apply (subst prfun_skip_id)
  apply (simp add: one_ureal.rep_eq real2ureal_def ureal2real_def)
  using Tcoin.exhaust apply blast
  apply (metis (full_types) Tcoin.exhaust cstate.select_convs(1) ereal_real o_def prfun_skip_not_id real2ureal_def ureal2real_def zero_ereal_def zero_ureal.rep_eq)
  apply (subst infsum_0)
  apply (subst ureal_defs)
  apply (smt (verit, best) divide_eq_0_iff ereal_max min.absorb2 min.commute mult_eq_0_iff o_apply real_of_ereal_0 ureal2ereal_inverse ureal2real_def zero_ereal_def zero_less_one_ereal zero_ureal.rep_eq)
  using real2ureal_def apply presburger
  using Tcoin.exhaust apply blast
  apply (subst infsum_0)
  apply (subst ureal_defs)
  apply (smt (verit, best) divide_eq_0_iff ereal_max min.absorb2 min.commute mult_eq_0_iff o_apply real_of_ereal_0 ureal2ereal_inverse ureal2real_def zero_ereal_def zero_less_one_ereal zero_ureal.rep_eq)
  using real2ureal_def apply blast
  apply (metis (full_types) Tcoin.exhaust cstate.ext_inject o_def prfun_skip_not_id real2ureal_def real_of_ereal_0 ureal2real_def zero_ureal.rep_eq)
  apply (subst ureal2real_1_2)
  apply (subst sum_1_2)
  apply (subst sum_geometric_series_ureal)
  apply (subst sum_geometric_series')
  apply (subst ureal_defs)+
proof -
  fix n
  have f1: "((1::\<real>) / (2::\<real>) + ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ (n + (1::\<nat>))) / (2::\<real>)) = 
        ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ (n + 2))"
    by (simp add: add.assoc diff_divide_distrib)
  have f2: "((3::\<real>) * ((1::\<real>) / (2::\<real>)) ^ n / (4::\<real>) + ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ n)) =  
          ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ (n+2))"
    apply (auto)
    by (simp add: power_one_over)
  show "ereal2ureal' (min (max (0::ereal) (ereal ((1::\<real>) / (2::\<real>) + ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ (n + (1::\<nat>))) / (2::\<real>)))) (1::ereal)) =
       ereal2ureal' (min (max (0::ereal) (ereal ((3::\<real>) * ((1::\<real>) / (2::\<real>)) ^ n / (4::\<real>) + ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ n)))) (1::ereal))"
    using f1 f2 by presburger
qed

lemma cflip_drop_initial_segments_eq: 
  "(\<Squnion>n::\<nat>. iter\<^sub>p (n+2) (c\<^sup>< = ctail)\<^sub>e cflip 0\<^sub>p) = (\<Squnion>n::\<nat>. iter\<^sub>p (n) (c\<^sup>< = ctail)\<^sub>e cflip 0\<^sub>p)"
  apply (rule increasing_chain_sup_subset_eq)
  apply (rule iterate_increasing_chain)
  by (simp add: cflip_is_dist)

lemma cflip_iterate_limit_sup:
  assumes "f = (\<lambda>n. (iter\<^sub>p (n+2) (c\<^sup>< = ctail)\<^sub>e cflip 0\<^sub>p))"
  shows "(\<lambda>n. ureal2real (f n s)) \<longlonglongrightarrow> (ureal2real (\<Squnion>n::\<nat>. f n s))"
  apply (simp only: assms)
  apply (subst LIMSEQ_ignore_initial_segment[where k = "2"])
  apply (subst increasing_chain_sup_subset_eq[where m = "2"])
  apply (rule increasing_chain_fun)
  apply (rule iterate_increasing_chain)
  apply (simp add: cflip_is_dist)
  apply (subst increasing_chain_limit_is_lub')
  apply (simp add: increasing_chain_def)
  apply (auto)
  apply (rule le_funI)
  by (smt (verit, ccfv_threshold) cflip_is_dist iterate_increasing2 le_fun_def)

lemma fa: "(\<lambda>n::\<nat>. ureal2real (ereal2ureal (ereal ((1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ n)))))
  = (\<lambda>n::\<nat>. ((1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ n)))"
  apply (subst fun_eq_iff)
  apply (auto)
  apply (simp add: ureal_defs)
  apply (subst real2uereal_inverse)
   apply (meson max.cobounded1)
   apply simp
proof -
  fix x
  have f1: "(max (0::ereal) (ereal ((1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ x)))) = 
    (ereal ((1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ x)))"
    apply (simp add: max_def)
    by (smt (z3) one_le_power)
  show "real_of_ereal (max (0::ereal) (ereal ((1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ x)))) =
       (1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ x)"
    by (simp add: f1)
qed

lemma fb: 
  " (\<lambda>n::\<nat>. (1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ n)) \<longlonglongrightarrow> (1::\<real>)"
proof -
  have f0: "(\<lambda>n::\<nat>. ((1::\<real>) - ((1::\<real>) / (2::\<real>)) ^ (n+1))) = (\<lambda>n::\<nat>. (1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ n))"
    apply (subst fun_eq_iff)
    apply (auto)
    using power_one_over by blast
  have f1: "(\<lambda>n::\<nat>. ((1::\<real>) - ((1::\<real>) / (2::\<real>)) ^ (n+1))) \<longlonglongrightarrow> (1 - 0)"
    apply (rule tendsto_diff)
    apply (auto)
    apply (rule LIMSEQ_power_zero)
    by simp
  show ?thesis
    using f0 f1 by auto
qed

lemma cflip_iterate_limit_cH:
  assumes "f = (\<lambda>n. (iter\<^sub>p (n+2) (c\<^sup>< = ctail)\<^sub>e cflip 0\<^sub>p))"
  shows "(\<lambda>n. ureal2real (f n s)) \<longlonglongrightarrow> ((\<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e s)"
  apply (simp only: assms)
  apply (subst iterate_cflip_bottom_simp(3))
  apply (subst sum_geometric_series_1)
  apply (pred_auto)
  apply (simp add: fa)
  apply (simp add: fb)
  apply (metis LIMSEQ_const_iff nle_le real2ureal_def ureal_lower_bound ureal_real2ureal_smaller)
  apply (metis comp_def one_ereal_def one_ureal.rep_eq one_ureal_def real_ereal_1 tendsto_const ureal2real_def)
  apply (metis LIMSEQ_const_iff nle_le real2ureal_def ureal_lower_bound ureal_real2ureal_smaller)
  by (meson Tcoin.exhaust)+

lemma fh:
  assumes "f = (\<lambda>n. (iter\<^sub>p (n+2) (c\<^sup>< = ctail)\<^sub>e cflip 0\<^sub>p))"
  shows "((\<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e s) = (ureal2real (\<Squnion>n::\<nat>. f n s))"
  apply (subst LIMSEQ_unique[where X = "(\<lambda>n. ureal2real (f n s))" and a = "((\<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e s)" and 
          b = "(ureal2real (\<Squnion>n::\<nat>. f n s))"])
  using cflip_iterate_limit_cH apply (simp add: assms)
  using cflip_iterate_limit_sup apply (simp add: assms)
  by auto

lemma fi: "(\<Squnion>n::\<nat>. iter\<^sub>p (n+2) (c\<^sup>< = ctail)\<^sub>e cflip 0\<^sub>p) = 
  (\<lambda>x::cstate \<times> cstate. ereal2ureal (ereal ((\<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e x)))"
  apply (simp only: fh)
  apply (simp add: ureal2rereal_inverse)
  using SUP_apply by fastforce

lemma coin_flip_loop: "cflip_loop = prfun_of_rvfun cH"
  apply (simp add: cflip_loop_def cH_def prfun_of_rvfun_def real2ureal_def)
  apply (subst sup_continuous_lfp_iteration)
  apply (simp add: cflip_is_dist)
  apply (rule finite_subset[where B = "{s::cstate \<times> cstate. True}"])
  apply force
  apply (metis cstate_rel_UNIV_set finite.emptyI finite.insertI)
  apply (simp only: cflip_drop_initial_segments_eq[symmetric])
  apply (simp only: fi)
  by auto

subsubsection \<open> Using unique fixed point theorem \<close>
lemma cstate_set_simp: "{s::cstate. s = \<lparr>c\<^sub>v = ctail\<rparr> \<or> s = \<lparr>c\<^sub>v = chead\<rparr>} = {\<lparr>c\<^sub>v = chead\<rparr>, \<lparr>c\<^sub>v = ctail\<rparr>}"
  by fastforce

lemma cflip_iterdiff_simp:
  shows "(iterdiff 0 (c\<^sup>< = ctail)\<^sub>e cflip 1\<^sub>p) = 1\<^sub>p"
        "(iterdiff (n+1) (c\<^sup>< = ctail)\<^sub>e cflip 1\<^sub>p) =  prfun_of_rvfun ((\<lbrakk>c\<^sup>< = ctail\<rbrakk>\<^sub>\<I>\<^sub>e * (1/2)^\<guillemotleft>n\<guillemotright>)\<^sub>e)"
proof -
  show "(iterdiff 0 (c\<^sup>< = ctail)\<^sub>e cflip 1\<^sub>p) = 1\<^sub>p"
    by (auto)

  show "(iterdiff (n+1) (c\<^sup>< = ctail)\<^sub>e cflip 1\<^sub>p) = prfun_of_rvfun ((\<lbrakk>c\<^sup>< = ctail\<rbrakk>\<^sub>\<I>\<^sub>e * (1/2)^\<guillemotleft>n\<guillemotright>)\<^sub>e)"
    apply (induction n)
    apply (simp add: pfun_defs)
    apply (subst cflip_altdef)
    apply (subst ureal_zero)
    apply (subst ureal_one)
    apply (subst rvfun_seqcomp_inverse)
    using cflip_altdef cflip_is_dist apply presburger
    apply (simp add: ureal_is_prob)
    apply (metis ureal_is_prob ureal_one)
    apply (simp add: prfun_of_rvfun_def)
    apply (expr_auto add: rel assigns_r_def)
    apply (subst infsum_cdiv_left)
    apply (rule infsum_constant_finite_states_summable)
    apply (simp)
    apply (subst infsum_constant_finite_states)
    apply (simp)
    apply (simp only: cstate_set_simp)
    apply (simp add: real2ureal_def)
    apply (simp only: add_Suc)
    apply (simp only: iterdiff.simps(2))
    apply (simp only: pcond_def)
    apply (simp only: pseqcomp_def)
    apply (subst rvfun_seqcomp_inverse)
    using cflip_altdef cflip_is_dist apply presburger
    apply (simp add: ureal_is_prob)
    apply (simp add: prfun_of_rvfun_def)
    apply (subst rvfun_inverse)
    apply (expr_auto add: dist_defs)
    apply (simp add: power_le_one)
    apply (subst cflip_altdef)
    apply (expr_auto add: rel assigns_r_def)  
    defer
    apply (simp add: pfun_defs)
    apply (subst ureal_zero)
    apply simp
  proof -
    fix n
    let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::cstate.
           (if v\<^sub>0 = \<lparr>c\<^sub>v = ctail\<rparr> \<or> v\<^sub>0 = \<lparr>c\<^sub>v = chead\<rparr> then 1::\<real> else (0::\<real>)) *
           ((if c\<^sub>v v\<^sub>0 = ctail then 1::\<real> else (0::\<real>)) * ((1::\<real>) / (2::\<real>)) ^ n) /
           (2::\<real>))"
    have "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::cstate.
           (if \<lparr>c\<^sub>v = ctail\<rparr> = v\<^sub>0 then ((1::\<real>) / (2::\<real>)) ^ n / 2 else (0::\<real>)))"
      apply (rule infsum_cong)
      by auto
    also have "... = (((1::\<real>) / (2::\<real>)) ^ n / (2::\<real>))"
      apply (subst infsum_constant_finite_states)
      apply (simp)
      by simp
    then show "real2ureal ?lhs = real2ureal (((1::\<real>) / (2::\<real>)) ^ n / (2::\<real>))"
      using calculation by presburger
  qed
qed

lemma cflip_iterdiff_tendsto_0:
  "\<forall>s::cstate \<times> cstate. (\<lambda>n::\<nat>. ureal2real (iterdiff n (c\<^sup>< = ctail)\<^sub>e cflip 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
proof 
  fix s
  have "(\<lambda>n::\<nat>. ureal2real (iterdiff (n+1) (c\<^sup>< = ctail)\<^sub>e cflip 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    apply (subst cflip_iterdiff_simp)
    apply (simp add: prfun_of_rvfun_def)
    apply (expr_auto)
    apply (subst real2ureal_inverse)
    apply (simp)
    apply (simp add: power_le_one)
    apply (simp add: LIMSEQ_realpow_zero)
    apply (subst real2ureal_inverse)
    by (simp)+
  then show "(\<lambda>n::\<nat>. ureal2real (iterdiff n (c\<^sup>< = ctail)\<^sub>e cflip 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    by (rule LIMSEQ_offset[where k = 1])
qed

lemma cH_is_fp: "\<F> (c\<^sup>< = ctail)\<^sub>e cflip (prfun_of_rvfun cH) = prfun_of_rvfun cH"
  apply (simp add: cH_def loopfunc_def)
  apply (simp add: pfun_defs)
  apply (subst cflip_altdef)
  apply (subst rvfun_skip_inverse)
  apply (subst rvfun_seqcomp_inverse)
  using cflip_altdef cflip_is_dist apply presburger
  apply (subst rvfun_inverse)
  apply (expr_auto add: dist_defs)
  apply (subst rvfun_inverse)
  apply (expr_auto add: dist_defs)
  apply (expr_auto add: prfun_of_rvfun_def skip_def)
  using Tcoin.exhaust apply blast
  apply (pred_auto)
  apply (subst infsum_cdiv_left)
  apply (rule infsum_constant_finite_states_summable)
  apply (simp)
  apply (subst infsum_constant_finite_states)
  apply (simp)
  apply (smt (verit, del_insts) Collect_cong One_nat_def Suc_1 Tcoin.distinct(1) UNIV_def card.empty 
      card.insert cstate.ext_inject cstate_UNIV_set dbl_simps(3) dbl_simps(5) empty_iff 
      finite.emptyI finite.insertI insert_iff mem_Collect_eq mult_numeral_1_right 
      nonzero_mult_div_cancel_left numeral_One of_nat_1 of_nat_mult of_nat_numeral)
  using Tcoin.exhaust by blast

lemma coin_flip_loop': "cflip_loop = prfun_of_rvfun cH"
  apply (simp add: cflip_loop_def)
  apply (subst unique_fixed_point_lfp_gfp'[where fp = "prfun_of_rvfun cH"])
  using cflip_is_dist apply auto[1]
  apply (metis (no_types, lifting) Collect_mono_iff cstate_rel_UNIV_set finite.emptyI finite_insert rev_finite_subset)
  using cflip_iterdiff_tendsto_0 apply (simp)
  using cH_is_fp apply blast
  by simp

subsubsection \<open> Termination \<close>
lemma cH_inverse: "rvfun_of_prfun (prfun_of_rvfun cH) = cH"
  apply (subst rvfun_inverse)
  by (expr_simp_1 add: cH_def dist_defs)+

text \<open> The probability of @{text "c'"} being @{text "head"} is 1, and so almost-sure termination.\<close>
lemma coin_flip_termination_prob: "rvfun_of_prfun cflip_loop ; \<lbrakk>c\<^sup>< = chead\<rbrakk>\<^sub>\<I>\<^sub>e = (1)\<^sub>e"
  apply (simp add: coin_flip_loop' cH_inverse)
  apply (simp add: cH_def)
  apply (expr_auto)
proof -
  let ?lhs_f = "\<lambda>v\<^sub>0. (if c\<^sub>v v\<^sub>0 = chead then 1::\<real> else (0::\<real>))"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::cstate. ?lhs_f v\<^sub>0 * ?lhs_f v\<^sub>0 )"
  have "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::cstate. ?lhs_f v\<^sub>0)"
    apply (rule infsum_cong)
    by (auto)
  also have "... = 1"
    apply (subst infsum_constant_finite_states)
    apply (metis cstate_UNIV_set finite.emptyI finite.insertI rev_finite_subset top_greatest)
    by (simp add: cstate_head)
  then show "?lhs = (1::\<real>)"
    using calculation by presburger
qed

text \<open> The probability of @{text "c'"} not being @{text "head"} is 0, and so impossible for non-termination.\<close>
lemma coin_flip_nontermination_prob: "rvfun_of_prfun cflip_loop ; \<lbrakk>\<not>c\<^sup>< = chead\<rbrakk>\<^sub>\<I>\<^sub>e = (0)\<^sub>e"
  apply (simp add: coin_flip_loop' cH_inverse)
  apply (simp add: cH_def)
  apply (expr_auto)
proof -
  let ?lhs_t = "\<lambda>v\<^sub>0. (if c\<^sub>v v\<^sub>0 = chead then 1::\<real> else (0::\<real>))"
  let ?lhs_f = "\<lambda>v\<^sub>0. (if \<not>c\<^sub>v v\<^sub>0 = chead then 1::\<real> else (0::\<real>))"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::cstate. ?lhs_t v\<^sub>0 * ?lhs_f v\<^sub>0 )"
  have "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::cstate. 0)"
    apply (rule infsum_cong)
    by (auto)
  then show "?lhs = (0::\<real>)"
    by force
qed

subsection \<open> Single coin flip_t (variable probability)\<close>
definition cpflip :: "ureal \<Rightarrow> cstate prhfun" where
"cpflip p = if\<^sub>p \<guillemotleft>p\<guillemotright> then (c := chead) else (c := ctail)"

definition cpflip_loop :: "ureal \<Rightarrow> cstate prhfun" where
"cpflip_loop p = while\<^sub>p (c\<^sup>< = ctail)\<^sub>e do cpflip p od"

definition cpH :: "ureal \<Rightarrow> cstate rvhfun" where 
"cpH p = (\<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"

definition cpH':: "ureal \<Rightarrow> cstate rvhfun" where  
"cpH' p = (\<lbrakk>c\<^sup>< = chead\<rbrakk>\<^sub>\<I>\<^sub>e * (\<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e) + \<lbrakk>\<not>c\<^sup>< = chead\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"

lemma "cpH p = cpH' p"
  apply (simp add: cpH_def cpH'_def)
  by (expr_auto)

lemma cpflip_is_dist: "is_final_distribution (rvfun_of_prfun (cpflip p))"
  apply (simp add: cpflip_def pfun_defs)
  apply (subst rvfun_assignment_inverse)+
  apply (simp add: r_simp)
  apply (subst rvfun_pchoice_inverse_c)
  apply (simp add: rvfun_assignment_is_prob)+
  apply (subst rvfun_pchoice_is_dist')
  by (simp add: rvfun_assignment_is_dist)+

lemma cpflip_altdef: "rvfun_of_prfun (cpflip p) = 
  (\<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e * (ureal2real \<guillemotleft>p\<guillemotright>) + \<lbrakk>c\<^sup>> = ctail\<rbrakk>\<^sub>\<I>\<^sub>e * (ureal2real (1 - \<guillemotleft>p\<guillemotright>)))\<^sub>e"
  apply (simp add: cpflip_def pfun_defs)
  apply (subst rvfun_assignment_inverse)+
  apply (simp add: r_simp)
  apply (subst rvfun_pchoice_inverse_c)
  apply (simp add: rvfun_assignment_is_prob)+
  apply (pred_auto)
  by (simp add: ureal_1_minus_real)

lemma cpflip_altdef': "rvfun_of_prfun (cpflip p) = 
  (\<lbrakk>c := chead\<rbrakk>\<^sub>\<I>\<^sub>e * (ureal2real \<guillemotleft>p\<guillemotright>) + \<lbrakk>c := ctail\<rbrakk>\<^sub>\<I>\<^sub>e * (ureal2real (1 - \<guillemotleft>p\<guillemotright>)))\<^sub>e"
  apply (simp add: cpflip_def pfun_defs)
  apply (subst rvfun_assignment_inverse)+
  apply (simp add: r_simp)
  apply (subst rvfun_pchoice_inverse_c)
  apply (simp add: rvfun_assignment_is_prob)+
  apply (pred_auto)
  by (simp add: ureal_1_minus_real)

subsubsection \<open> Using unique fixed point theorem \<close>
lemma cpflip_sum_1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::cstate. (if c\<^sub>v v\<^sub>0 = chead then 1::\<real> else (0::\<real>)) * ureal2real p + 
      (if c\<^sub>v v\<^sub>0 = ctail then 1::\<real> else (0::\<real>)) * ureal2real ((1::ureal) - p)) = (1::\<real>)"
  apply (subst infsum_add)
  apply (subst summable_on_cmult_left)
  apply (rule infsum_constant_finite_states_summable)
  apply (simp add: cstate_head)+
  apply (subst summable_on_cmult_left)
  apply (rule infsum_constant_finite_states_summable)
  apply (metis cstate_UNIV_set finite.emptyI finite_insert rev_finite_subset top_greatest)
  apply (simp)
  apply (subst infsum_cmult_left)
  apply (rule infsum_constant_finite_states_summable)
  apply (simp add: cstate_head)+
  apply (subst infsum_cmult_left)
  apply (rule infsum_constant_finite_states_summable)
  apply (metis cstate_UNIV_set finite.emptyI finite_insert rev_finite_subset top_greatest)
  apply (subst infsum_constant_finite_states)
  apply (simp add: cstate_head)+
  apply (subst infsum_constant_finite_states)
  apply (simp add: cstate_tail)+
  using ureal_1_minus_real by fastforce

lemma cpflip_iterdiff_simp:
  shows "(iterdiff 0 (c\<^sup>< = ctail)\<^sub>e (cpflip p) 1\<^sub>p) = 1\<^sub>p"
        "(iterdiff (n+1) (c\<^sup>< = ctail)\<^sub>e (cpflip p) 1\<^sub>p) =  prfun_of_rvfun ((\<lbrakk>c\<^sup>< = ctail\<rbrakk>\<^sub>\<I>\<^sub>e * (ureal2real (1 - \<guillemotleft>p\<guillemotright>))^\<guillemotleft>n\<guillemotright>)\<^sub>e)"
proof -
  show "(iterdiff 0 (c\<^sup>< = ctail)\<^sub>e (cpflip p) 1\<^sub>p) = 1\<^sub>p"
    by (auto)

  show "(iterdiff (n+1) (c\<^sup>< = ctail)\<^sub>e (cpflip p) 1\<^sub>p) = prfun_of_rvfun ((\<lbrakk>c\<^sup>< = ctail\<rbrakk>\<^sub>\<I>\<^sub>e * (ureal2real (1 - \<guillemotleft>p\<guillemotright>))^\<guillemotleft>n\<guillemotright>)\<^sub>e)"
    apply (induction n)
    apply (simp add: pfun_defs)
    apply (subst cpflip_altdef)
    apply (subst ureal_zero)
    apply (subst ureal_one)
    apply (subst rvfun_seqcomp_inverse)
    using cpflip_altdef cpflip_is_dist apply presburger
    apply (simp add: ureal_is_prob)
    apply (metis ureal_is_prob ureal_one)
    apply (simp add: prfun_of_rvfun_def)
    apply (expr_auto add: rel)
    using cpflip_sum_1 apply presburger

    apply (simp only: add_Suc)
    apply (simp only: iterdiff.simps(2))
    apply (simp only: pcond_def)
    apply (simp only: pseqcomp_def)
    apply (subst rvfun_seqcomp_inverse)
    using cpflip_altdef cpflip_is_dist apply presburger
    apply (simp add: ureal_is_prob)
    apply (simp add: prfun_of_rvfun_def)
    apply (subst rvfun_inverse)
    apply (expr_auto add: dist_defs)
    using ureal_lower_bound apply presburger
    apply (subst power_le_one)
    using ureal_lower_bound apply presburger
    using ureal_upper_bound apply blast
    apply (simp)
    apply (subst cpflip_altdef)
    apply (expr_auto add: rel)
    defer
    apply (simp add: pfun_defs)
    apply (subst ureal_zero)
    apply simp
  proof -
    fix n
    let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::cstate.
           ((if c\<^sub>v v\<^sub>0 = chead then 1::\<real> else (0::\<real>)) * ureal2real p +
            (if c\<^sub>v v\<^sub>0 = ctail then 1::\<real> else (0::\<real>)) * ureal2real ((1::ureal) - p)) *
           ((if c\<^sub>v v\<^sub>0 = ctail then 1::\<real> else (0::\<real>)) * ureal2real ((1::ureal) - p) ^ n))"
    have "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::cstate.
           (if \<lparr>c\<^sub>v = ctail\<rparr> = v\<^sub>0 then ureal2real ((1::ureal) - p) ^ (n+1) else (0::\<real>)))"
      apply (rule infsum_cong)
      by auto
    also have "... =  ureal2real ((1::ureal) - p) ^ (n+1)"
      apply (subst infsum_constant_finite_states)
      apply (simp)
      by simp
    then show "real2ureal ?lhs = real2ureal (ureal2real ((1::ureal) - p) * ureal2real ((1::ureal) - p) ^ n)"
      using calculation by auto
  qed
qed

lemma cpflip_iterdiff_tendsto_0:
  assumes "p \<noteq> 0"
  shows "\<forall>s::cstate \<times> cstate. (\<lambda>n::\<nat>. ureal2real (iterdiff n (c\<^sup>< = ctail)\<^sub>e (cpflip p) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
proof 
  fix s
  have "(\<lambda>n::\<nat>. ureal2real (iterdiff (n+1) (c\<^sup>< = ctail)\<^sub>e (cpflip p) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    apply (subst cpflip_iterdiff_simp)
    apply (simp add: prfun_of_rvfun_def)
    apply (expr_auto)
    apply (subst real2ureal_inverse)
    apply (simp add: ureal_lower_bound)
    apply (subst power_le_one)
    using ureal_lower_bound apply blast
    using ureal_upper_bound apply blast
    apply (simp)
    apply (subst LIMSEQ_realpow_zero)
    using ureal_lower_bound apply blast
    apply (smt (verit, best) assms real2eureal_inverse ureal2real_eq ureal_1_minus_real ureal_lower_bound zero_ereal_def zero_ureal_def)
    apply (simp)
    apply (subst real2ureal_inverse)
    by (simp)+
    
  then show "(\<lambda>n::\<nat>. ureal2real (iterdiff n (c\<^sup>< = ctail)\<^sub>e (cpflip p) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    by (rule LIMSEQ_offset[where k = 1])
qed

lemma cpH_is_fp: "\<F> (c\<^sup>< = ctail)\<^sub>e (cpflip p) (prfun_of_rvfun (cpH p)) = prfun_of_rvfun (cpH p)"
  apply (simp add: cpH_def loopfunc_def)
  apply (simp add: pfun_defs)
  apply (subst cpflip_altdef)
  apply (subst rvfun_skip_inverse)
  apply (subst rvfun_seqcomp_inverse)
  using cpflip_altdef cpflip_is_dist apply presburger
  apply (subst rvfun_inverse)
  apply (expr_auto add: dist_defs)
  apply (subst rvfun_inverse)
  apply (expr_auto add: dist_defs)
  apply (expr_auto add: prfun_of_rvfun_def skip_def)
  using Tcoin.exhaust apply blast
  using cpflip_sum_1 apply presburger
  using Tcoin.exhaust by blast

text \<open>Not surprisingly, as long as @{text "p"} is larger than 0, @{text "cpflip_loop"} almost surely
 terminates. \<close>
lemma cpflip_loop:
  assumes "p \<noteq> 0"
  shows "cpflip_loop p = prfun_of_rvfun (cpH p)"
  apply (simp add: cpflip_loop_def)
  apply (subst unique_fixed_point_lfp_gfp'[where fp = "prfun_of_rvfun (cpH p)"])
  using cpflip_is_dist apply auto[1]
  apply (metis (no_types, lifting) Collect_mono_iff cstate_rel_UNIV_set finite.emptyI finite_insert rev_finite_subset)
  using cpflip_iterdiff_tendsto_0 apply (simp add: assms)
  using cpH_is_fp apply blast
  by simp


subsection \<open> Coin flip_t with time \<close>
alphabet coin_t_state = time +
  coin :: Tcoin
             
thm "coin_t_state.simps"
definition flip_t:: "coin_t_state prhfun" where
"flip_t = (prfun_of_rvfun (coin \<^bold>\<U> {chead, ctail}))"

definition flip_t_loop where
"flip_t_loop = while\<^sub>p\<^sub>t (coin\<^sup>< = ctail)\<^sub>e do flip_t od"

(*
definition Ht:: "coin_t_state rvhfun" where 
"Ht = (\<lbrakk>coin\<^sup>> = chead \<and> $t\<^sup>> \<ge> $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1/2)^(($t\<^sup>> - $t\<^sup>< - 1)) * (1/2))\<^sub>e"
*)
definition Ht:: "coin_t_state rvhfun" where 
"Ht = (\<lbrakk>coin\<^sup>< = ctail\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>coin\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> $t\<^sup>> \<ge> $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1/2)^(($t\<^sup>> - $t\<^sup>< - 1)) * (1/2) + 
      \<lbrakk>\<not>coin\<^sup>< = ctail\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>coin\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>$t\<^sup>> = $t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e )\<^sub>e"

lemma flip_is_dist: "is_final_distribution (rvfun_of_prfun flip_t)"
  apply (simp add: flip_t_def)
  apply (subst rvfun_uniform_dist_inverse)
  apply (simp)+
  using rvfun_uniform_dist_is_dist
  by (metis coin_vwb_lens finite.emptyI finite.insertI insert_not_empty)

lemma flip_t_altdef: "rvfun_of_prfun flip_t = (\<lbrakk>\<Squnion> v \<in> {ctail, chead}. coin := \<guillemotleft>v\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e / 2)\<^sub>e"
  apply (simp add: flip_t_def)
  apply (subst prfun_uniform_dist_altdef')
  apply simp+
  by (pred_auto)

definition flip_t_alt :: "coin_t_state rvhfun" where
"flip_t_alt \<equiv> (\<lbrakk>coin\<^sup>> \<in> {chead, ctail} \<and> $t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 2)\<^sub>e"

lemma flip_t: "(Pt flip_t) = prfun_of_rvfun flip_t_alt"
  apply (simp add: flip_t_def Pt_def flip_t_alt_def)
  apply (simp add: prfun_uniform_dist_left)
  apply (simp add: pfun_defs)
  apply (simp add: rvfun_assignment_inverse)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (simp add: fun_eq_iff)
  apply (rule allI)+
  by (expr_auto add: rel assigns_r_def)

lemma flip_t_set_eq: 
  "\<forall>t. {s::coin_t_state. (coin\<^sub>v s = chead \<or> coin\<^sub>v s = ctail) \<and> t\<^sub>v s = Suc t} = 
       {\<lparr>t\<^sub>v = Suc t, coin\<^sub>v = chead\<rparr>, \<lparr>t\<^sub>v = Suc t, coin\<^sub>v = ctail\<rparr>}"
  by (auto)

lemma flip_t_set_eq': 
  "\<forall>t. {s::coin_t_state. coin\<^sub>v s = ctail \<and> s \<in> {v\<^sub>0::coin_t_state. t\<^sub>v v\<^sub>0 = Suc t}} = 
       {\<lparr>t\<^sub>v = Suc t, coin\<^sub>v = ctail\<rparr>}"
  by auto

lemma flip_t_set_eq'': "\<forall>t. {s::coin_t_state. coin\<^sub>v s = cc \<and> t\<^sub>v s = t} = {\<lparr>t\<^sub>v = t, coin\<^sub>v = cc\<rparr>}"
  by auto

lemma flip_t_set_eq''': 
  "\<forall>t. ((\<lambda>n::\<nat>. \<lparr>t\<^sub>v = Suc t + n, coin\<^sub>v = chead\<rparr>) ` UNIV) = {v\<^sub>0. coin\<^sub>v v\<^sub>0 = chead \<and> Suc t \<le> t\<^sub>v v\<^sub>0}"
    apply auto
    by (smt (verit, ccfv_threshold) UNIV_I add_Suc coin_t_state.surjective image_iff nat_le_iff_add old.unit.exhaust)

lemma flip_t_is_dist: "is_final_distribution flip_t_alt"
  apply (simp add: dist_defs flip_t_alt_def)
  apply (expr_auto)
  apply (subst infsum_cdiv_left)
   apply (rule infsum_constant_finite_states_summable)
  using flip_t_set_eq apply (metis finite.simps)
  apply (subst infsum_constant_finite_states)
  using flip_t_set_eq apply (metis finite.simps)
  using flip_t_set_eq 
  by (smt (verit, best) Collect_cong One_nat_def Suc_1 Tcoin.distinct(1) card.empty card.insert 
      coin_t_state.ext_inject field_sum_of_halves finite.emptyI finite.insertI insert_absorb 
      insert_not_empty of_nat_1 of_nat_add one_add_one singletonD time.ext_inject)

(*
lemma H_is_dist: "is_final_distribution Ht"
  apply (simp add: dist_defs H_def)
  apply (simp add: expr_defs)
  apply (auto)
  apply (smt (verit, best) field_sum_of_halves power_le_one)
  apply (simp add: lens_defs)
proof -
  fix s\<^sub>1::"coin_t_state"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>s::coin_t_state.
          (if coin\<^sub>v s = chead \<and> Suc (t\<^sub>v s\<^sub>1) \<le> t\<^sub>v s then 1::\<real> else (0::\<real>)) *
          ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - Suc (t\<^sub>v s\<^sub>1)) / (2::\<real>))"
  let ?set = "{s::coin_t_state. coin\<^sub>v s = chead \<and> Suc (t\<^sub>v s\<^sub>1) \<le> t\<^sub>v s}"

  (*
  thm "infsum_reindex"
  have "(\<Sum>\<^sub>\<infinity>t::nat \<in> {t. t \<ge> Suc (t\<^sub>v s\<^sub>1)}. ((1::\<real>) / (2::\<real>)) ^ (t - Suc (t\<^sub>v s\<^sub>1) + 1)) = 1"
    apply (subst infsum_reindex[where h = "\<lambda>s::coin_t_state. t\<^sub>v s" and A = "?set"])
*)
  have f1: "?lhs = (\<Sum>\<^sub>\<infinity>s::coin_t_state \<in> ?set \<union> -?set.
          (if coin\<^sub>v s = chead \<and> Suc (t\<^sub>v s\<^sub>1) \<le> t\<^sub>v s then 1::\<real> else (0::\<real>)) *
          ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - Suc (t\<^sub>v s\<^sub>1)) / (2::\<real>))"
    by auto
  moreover have "... = (\<Sum>\<^sub>\<infinity>s::coin_t_state \<in> ?set.
          (if coin\<^sub>v s = chead \<and> Suc (t\<^sub>v s\<^sub>1) \<le> t\<^sub>v s then 1::\<real> else (0::\<real>)) *
          ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - Suc (t\<^sub>v s\<^sub>1)) / (2::\<real>))"
    apply (rule infsum_cong_neutral)
    apply force
    apply simp
    by blast
  moreover have "... = (\<Sum>\<^sub>\<infinity>s::coin_t_state \<in> ?set. ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - Suc (t\<^sub>v s\<^sub>1)) / (2::\<real>))"
    by (smt (verit) infsum_cong mem_Collect_eq mult_cancel_right2)
  moreover have "... = (\<Sum>\<^sub>\<infinity>s::coin_t_state \<in> ?set. ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - Suc (t\<^sub>v s\<^sub>1) + 1))"
    by auto
  moreover have "... = (\<Sum>\<^sub>\<infinity>t::nat \<in> {t. t \<ge> Suc (t\<^sub>v s\<^sub>1)}. ((1::\<real>) / (2::\<real>)) ^ (t - Suc (t\<^sub>v s\<^sub>1) + 1))"
    apply (subst infsum_reindex_bij_betw[symmetric, where g = "\<lambda>s::coin_t_state. t\<^sub>v s" and A = "?set"])
    apply (simp add: bij_betw_def)
    apply (rule conjI)
    apply (simp add: inj_on_def)
    apply auto
    apply (simp add: image_def)
    apply (rule_tac x = "\<lparr>t\<^sub>v = x, coin\<^sub>v = chead\<rparr>" in exI)
    by simp
  moreover have "... = (\<Sum>\<^sub>\<infinity>t::nat. ((1::\<real>) / (2::\<real>)) ^ (t + 1))"
    apply (subst infsum_reindex_bij_betw[symmetric, where g = "\<lambda>n. n + Suc (t\<^sub>v s\<^sub>1)" and A = "UNIV"])
    apply auto
    apply (simp add: bij_betw_def)
    apply (rule conjI)
    apply (simp add: inj_on_def)
    apply (simp add: image_def)
    apply (auto)
    by (simp add: add.commute le_iff_add)
  moreover have "... = 1"
    (* Intend to prove it as follows.
      Use "HOL-Analysis.Infinite_Set_Sum.infsetsum_infsum" 
          to turn infsum to infsetsum
      also use HOL-Analysis.Infinite_Set_Sum.abs_summable_equivalent
          to establish HOL-Analysis.Infinite_Set_Sum.abs_summable_on = abs_summable_on
      Use "HOL-Analysis.Infinite_Set_Sum.infsetsum_nat"
          to turn infsetsum to sums over series suminf
      Use "HOL.Series.suminf_geometric"
          to calculate geometric progression
    *)
    sorry
  ultimately show "?lhs = (1::\<real>)"
    by presburger
qed
*)

lemma Ht_is_fp: "\<F> (coin\<^sup>< = ctail)\<^sub>e (Pt flip_t) (prfun_of_rvfun (Ht)) = prfun_of_rvfun (Ht)"
  apply (simp add: Ht_def loopfunc_def)
  apply (simp add: pfun_defs flip_t)
  apply (subst flip_t_alt_def)
  apply (subst rvfun_skip_inverse)
  apply (subst rvfun_skip\<^sub>_f_simp)
  apply (subst rvfun_seqcomp_inverse)
  using flip_t_alt_def flip_t_is_dist rvfun_inverse rvfun_prob_sum1_summable'(1) apply force
  using ureal_is_prob apply blast
  apply (subst rvfun_inverse)
  apply (expr_auto add: dist_defs)
  apply (subst rvfun_inverse)
  apply (expr_auto add: dist_defs)
  apply (smt (verit, del_insts) One_nat_def add.commute plus_1_eq_Suc power_0 power_le_one_iff power_one_over power_one_right sum_1_2 sum_geometric_series')
  apply (expr_auto add: prfun_of_rvfun_def skip_def)
  using Tcoin.exhaust apply blast
  using Tcoin.exhaust apply blast
proof -
  fix t t\<^sub>v'
  assume a1: "Suc t \<le> t\<^sub>v'"
  let ?f1 = "\<lambda>v\<^sub>0::coin_t_state. (if (coin\<^sub>v v\<^sub>0 = chead \<or> coin\<^sub>v v\<^sub>0 = ctail) \<and> t\<^sub>v v\<^sub>0 = Suc t then 1::\<real> else (0::\<real>))"
  let ?f2 = "\<lambda>v\<^sub>0::coin_t_state. ((if coin\<^sub>v v\<^sub>0 = ctail then 1::\<real> else (0::\<real>)) * (if Suc (t\<^sub>v v\<^sub>0) \<le> t\<^sub>v' then 1::\<real> else (0::\<real>)) *
            ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v' - Suc (t\<^sub>v v\<^sub>0)) / (2::\<real>) +
            (if \<not> coin\<^sub>v v\<^sub>0 = ctail then 1::\<real> else (0::\<real>)) * (if t\<^sub>v' = t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)))"
  have set_eq_1: "{s::coin_t_state. coin\<^sub>v s = ctail \<and> t\<^sub>v s = Suc t \<and> Suc (t\<^sub>v s) \<le> t\<^sub>v'} = 
        (if Suc (Suc t) \<le> t\<^sub>v' then {\<lparr>t\<^sub>v = Suc t, coin\<^sub>v = ctail\<rparr>} else {})"
    by auto

  have set_eq_2: "{s::coin_t_state. coin\<^sub>v s = chead \<and> t\<^sub>v' = t\<^sub>v s \<and> t\<^sub>v s = Suc t} = 
        (if (Suc t) = t\<^sub>v' then {\<lparr>t\<^sub>v = Suc t, coin\<^sub>v = chead\<rparr>} else {})"
    apply (simp)
    apply (rule impI)
    apply (subst set_eq_iff)
    by (smt (verit, best) coin_t_state.equality coin_t_state.select_convs(1) mem_Collect_eq old.unit.exhaust singleton_iff time.select_convs(1))
  
  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state. ?f1 v\<^sub>0 * ?f2 v\<^sub>0 / (2::\<real>)) =
        (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state. (if coin\<^sub>v v\<^sub>0 = ctail \<and> t\<^sub>v v\<^sub>0 = Suc t \<and> Suc (t\<^sub>v v\<^sub>0) \<le> t\<^sub>v' then 1 else 0) * 
            ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v' - Suc (t\<^sub>v v\<^sub>0)) / (2::\<real>) / 2  + 
           (if coin\<^sub>v v\<^sub>0 = chead \<and> t\<^sub>v'  = t\<^sub>v v\<^sub>0 \<and> t\<^sub>v v\<^sub>0 = Suc t then 1 else 0) / 2)"
    apply (rule infsum_cong)
    by (auto)
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state. (if coin\<^sub>v v\<^sub>0 = ctail \<and> t\<^sub>v v\<^sub>0 = Suc t \<and> Suc (t\<^sub>v v\<^sub>0) \<le> t\<^sub>v' then 
                (((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v' - Suc (Suc t)) / (2::\<real>) / 2) else 0) + 
           (if coin\<^sub>v v\<^sub>0 = chead \<and> t\<^sub>v'  = t\<^sub>v v\<^sub>0 \<and> t\<^sub>v v\<^sub>0 = Suc t then 1/2 else 0))"
    apply (rule infsum_cong)
    by (auto)
  also have "... = (((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v' - Suc t) / (2::\<real>))"
    apply (subst infsum_add)
    apply (rule infsum_constant_finite_states_summable)
    apply (simp add: set_eq_1)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, best) finite.emptyI finite.intros(2) flip_t_set_eq mem_Collect_eq rev_finite_subset subset_eq)
    apply (subst infsum_constant_finite_states)
    apply (simp add: set_eq_1)
    apply (subst infsum_constant_finite_states)
    apply (simp add: set_eq_2)
    apply (simp add: set_eq_1 set_eq_2)
    by (smt (verit, ccfv_threshold) Suc_diff_le a1 add.commute diff_Suc_Suc divide_divide_eq_left le_antisym not_less_eq_eq plus_1_eq_Suc power_Suc2 power_one_over sum_1_2 sum_geometric_series')
  then show "real2ureal
        (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state. ?f1 v\<^sub>0 * ?f2 v\<^sub>0 / (2::\<real>)) =
       real2ureal (((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v' - Suc t) / (2::\<real>))"
    using calculation by presburger    
next
  fix t t\<^sub>v'
  assume a1: "\<not> Suc t \<le> t\<^sub>v'"

  show "real2ureal
        (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state.
           (if (coin\<^sub>v v\<^sub>0 = chead \<or> coin\<^sub>v v\<^sub>0 = ctail) \<and> t\<^sub>v v\<^sub>0 = Suc t then 1::\<real> else (0::\<real>)) *
           ((if coin\<^sub>v v\<^sub>0 = ctail then 1::\<real> else (0::\<real>)) * (if Suc (t\<^sub>v v\<^sub>0) \<le> t\<^sub>v' then 1::\<real> else (0::\<real>)) *
            ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v' - Suc (t\<^sub>v v\<^sub>0)) /
            (2::\<real>) +
            (if \<not> coin\<^sub>v v\<^sub>0 = ctail then 1::\<real> else (0::\<real>)) * (if t\<^sub>v' = t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>))) /
           (2::\<real>)) = real2ureal (0::\<real>)"
    apply (subst infsum_0)
    using a1 apply force
    by simp
qed

lemma Pt_flip_finite: "\<forall>s. finite {s'::coin_t_state. (0::ureal) < Pt flip_t (s, s')}"
proof
  fix s 
  show "finite {s'::coin_t_state. (0::ureal) < Pt flip_t (s, s')} "
    apply (simp add: flip_t)
    apply (simp add: rvfun_ge_zero)
    apply (simp add: flip_t_alt_def)
    apply (pred_auto)
    by (simp add: flip_t_set_eq)
qed

(* * \<lbrakk>$t\<^sup>> = $t\<^sup>< + 1 + \<guillemotleft>n\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e  *)
(*
[coin'=ctail]*[t'=t+1]/2 + [coin'=chead]*[t'=t+1]/2
  iterdiff (n+1) (coin\<^sup>< = ctail)\<^sub>e (Pt flip_t) 1\<^sub>p 
= [coin=ctail] * (
    ([coin'=ctail]*[t'=t+1]/2 + [coin'=chead]*[t'=t+1]/2) ; 
    (iterdiff (n+1) (coin\<^sup>< = ctail)\<^sub>e (Pt flip_t) 1\<^sub>p)
  ) + [\<not>coin' = ctail] * 0
= [coin=ctail] * (
    ([coin'=ctail]*[t'=t+1]/2 + [coin'=chead]*[t'=t+1]/2) ; 
    [coin=ctail]*[t'=t+n]*(1/2)^n
  )
 = [coin=ctail] * [t'=t+n+1]*(1/2)^(n+1)
*)
lemma flip_t_iterdiff_simp:
  shows "(iterdiff 0 (coin\<^sup>< = ctail)\<^sub>e (Pt flip_t) 1\<^sub>p) = 1\<^sub>p"
        "(iterdiff (n+1) (coin\<^sup>< = ctail)\<^sub>e (Pt flip_t) 1\<^sub>p) = 
            prfun_of_rvfun ((\<lbrakk>coin\<^sup>< = ctail\<rbrakk>\<^sub>\<I>\<^sub>e * (1/2)^\<guillemotleft>n\<guillemotright>)\<^sub>e)"
proof -
  show "(iterdiff 0 (coin\<^sup>< = ctail)\<^sub>e (Pt flip_t) 1\<^sub>p) = 1\<^sub>p"
    by (auto)

  show "(iterdiff (n+1) (coin\<^sup>< = ctail)\<^sub>e (Pt flip_t) 1\<^sub>p) = 
            prfun_of_rvfun ((\<lbrakk>coin\<^sup>< = ctail\<rbrakk>\<^sub>\<I>\<^sub>e * (1/2)^\<guillemotleft>n\<guillemotright>)\<^sub>e)"
    apply (induction n)
    apply (simp add: pfun_defs)
    apply (subst flip_t)
    apply (subst ureal_zero)
    apply (subst ureal_one)
    apply (subst rvfun_seqcomp_inverse)
    apply (simp add: flip_t_is_dist rvfun_inverse rvfun_prob_sum1_summable'(1))
    apply (metis ureal_is_prob ureal_one)
    apply (subst rvfun_inverse)
    apply (simp add: flip_t_is_dist rvfun_prob_sum1_summable'(1))
    apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
    apply (expr_auto add: rel assigns_r_def)
    apply (simp add: flip_t_alt_def)
    apply (pred_auto)
    apply (subst infsum_cdiv_left)
    apply (rule infsum_constant_finite_states_summable)
    apply (simp add: flip_t_set_eq)
    apply (subst infsum_constant_finite_states)
    apply (simp add: flip_t_set_eq)
     apply (simp add: flip_t_set_eq)
    apply (simp only: add_Suc)
    apply (simp only: iterdiff.simps(2))
    apply (simp only: pcond_def)
    apply (simp only: pseqcomp_def)
    apply (subst rvfun_seqcomp_inverse)
    apply (simp add: flip_t flip_t_is_dist rvfun_inverse rvfun_prob_sum1_summable'(1))
    apply (simp add: ureal_is_prob)
    apply (simp add: prfun_of_rvfun_def)
    apply (subst rvfun_inverse)
    apply (expr_auto add: dist_defs)
    apply (simp add: power_le_one)
    apply (subst flip_t)
    apply (expr_auto add: rel assigns_r_def)  
    defer
    apply (simp add: pfun_defs)
    apply (subst ureal_zero)
    apply simp
    apply (subst rvfun_inverse)
    using flip_t_is_dist rvfun_prob_sum1_summable'(1) apply blast
    apply (simp add: flip_t_alt_def)
    apply (expr_auto add: rel assigns_r_def)
  proof -
    fix n t
    let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state.
           (if (coin\<^sub>v v\<^sub>0 = chead \<or> coin\<^sub>v v\<^sub>0 = ctail) \<and> t\<^sub>v v\<^sub>0 = Suc t then 1::\<real> else (0::\<real>)) *
           ((if coin\<^sub>v v\<^sub>0 = ctail then 1::\<real> else (0::\<real>)) * ((1::\<real>) / (2::\<real>)) ^ n) /
           (2::\<real>))"
    have "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state \<in> {v\<^sub>0. t\<^sub>v v\<^sub>0 = Suc t}.
           (if coin\<^sub>v v\<^sub>0 = ctail then ((1::\<real>) / (2::\<real>)) ^ n / 2 else (0::\<real>)))"
      apply (rule infsum_cong_neutral)
      apply blast
      apply auto[1]
      by simp
    also have "... = (((1::\<real>) / (2::\<real>)) ^ n / (2::\<real>))"
      apply (subst infsum_constant_finite_states_subset)
      apply (smt (verit, del_insts) Collect_mono finite.emptyI finite_insert flip_t_set_eq mem_Collect_eq rev_finite_subset)
      apply (simp only: flip_t_set_eq')
      by simp

    then show "real2ureal ?lhs = real2ureal (((1::\<real>) / (2::\<real>)) ^ n / (2::\<real>))"
      using calculation by presburger
  qed
qed

lemma flip_t_iterdiff_tendsto_0:
  "\<forall>s. (\<lambda>n::\<nat>. ureal2real (iterdiff n (coin\<^sup>< = ctail)\<^sub>e (Pt flip_t) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
proof 
  fix s
  have "(\<lambda>n::\<nat>. ureal2real (iterdiff (n+1) (coin\<^sup>< = ctail)\<^sub>e (Pt flip_t) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    apply (subst flip_t_iterdiff_simp)
    apply (simp add: prfun_of_rvfun_def)
    apply (expr_auto)
    apply (subst real2ureal_inverse)
    apply (simp)
    apply (simp add: power_le_one)
    apply (simp add: LIMSEQ_realpow_zero)
    apply (subst real2ureal_inverse)
    by (simp)+
  then show "(\<lambda>n::\<nat>. ureal2real (iterdiff n (coin\<^sup>< = ctail)\<^sub>e (Pt flip_t) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    by (rule LIMSEQ_offset[where k = 1])
qed

lemma flip_t_loop: "flip_t_loop = prfun_of_rvfun Ht"
  apply (simp add: flip_t_loop_def ptwhile_def)
  apply (subst unique_fixed_point_lfp_gfp_finite_final'[where fp = "prfun_of_rvfun Ht"])
  apply (simp add: flip_t flip_t_is_dist rvfun_inverse rvfun_prob_sum1_summable'(1))
  using Pt_flip_finite apply blast
  using flip_t_iterdiff_tendsto_0 apply (simp)
  using Ht_is_fp apply blast
  by simp

subsubsection \<open> Termination and average termination time \<close>
lemma Ht_inverse: "rvfun_of_prfun (prfun_of_rvfun Ht) = Ht"
  apply (subst rvfun_inverse)
  apply (expr_simp_1 add: Ht_def dist_defs)
  apply (smt (verit, del_insts) divide_nonneg_nonneg power_0 power_le_one_iff power_one_over sum_1_2 sum_geometric_series')
  by simp

lemma coin_flip_t_termination_prob: "rvfun_of_prfun flip_t_loop ; \<lbrakk>coin\<^sup>< = chead\<rbrakk>\<^sub>\<I>\<^sub>e = (1)\<^sub>e"
  apply (simp add: flip_t_loop)
  apply (simp add: Ht_inverse)
  apply (simp add: Ht_def)
  apply (expr_auto)
proof -
  fix t coin
  let ?lhs_f = "\<lambda>v\<^sub>0. (if coin\<^sub>v v\<^sub>0 = chead then 1::\<real> else (0::\<real>))"
  let ?lhs_f2 = "\<lambda>v\<^sub>0. (if t\<^sub>v v\<^sub>0 = t then 1::\<real> else (0::\<real>))"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state. ?lhs_f v\<^sub>0 * ?lhs_f2 v\<^sub>0 * ?lhs_f v\<^sub>0 )"
  have "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state. if coin\<^sub>v v\<^sub>0 = chead \<and> t\<^sub>v v\<^sub>0 = t then 1::\<real> else (0::\<real>))"
    apply (rule infsum_cong)
    by (auto)
  also have "... = 1"
    apply (subst infsum_constant_finite_states)
    by (simp add: flip_t_set_eq'')+
  then show "?lhs = (1::\<real>)"
    using calculation by presburger
next
  fix t
  let ?lhs_f = "\<lambda>v\<^sub>0. (if coin\<^sub>v v\<^sub>0 = chead then 1::\<real> else (0::\<real>))"
  let ?lhs_f2 = "\<lambda>v\<^sub>0. (if Suc t \<le> t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>))"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state. ?lhs_f v\<^sub>0 * ?lhs_f2 v\<^sub>0 *((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc t) * ?lhs_f v\<^sub>0 / 2)"

  have reindex: "infsum (\<lambda>v\<^sub>0::coin_t_state. ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc t) / (2::\<real>))
    ((\<lambda>n::\<nat>. \<lparr>t\<^sub>v = Suc t + n, coin\<^sub>v = chead\<rparr>) ` UNIV)
    = infsum (\<lambda>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n / (2::\<real>)) UNIV"
    apply (subst infsum_reindex)
    apply (simp add: inj_def)
    by (simp add: infsum_cong)

  have set_eq: "((\<lambda>n::\<nat>. \<lparr>t\<^sub>v = Suc t + n, coin\<^sub>v = chead\<rparr>) ` UNIV) = {v\<^sub>0. coin\<^sub>v v\<^sub>0 = chead \<and> Suc t \<le> t\<^sub>v v\<^sub>0}"
    apply auto
    by (smt (verit, ccfv_threshold) UNIV_I add_Suc coin_t_state.surjective image_iff nat_le_iff_add old.unit.exhaust)

  have "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state. if coin\<^sub>v v\<^sub>0 = chead \<and> Suc t \<le> t\<^sub>v v\<^sub>0 then (((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc t)/2) else (0::\<real>))"
    apply (rule infsum_cong)
    by (auto)
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state \<in> {v\<^sub>0. coin\<^sub>v v\<^sub>0 = chead \<and> Suc t \<le> t\<^sub>v v\<^sub>0}.
       ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc t) / (2::\<real>))"
    apply (rule infsum_cong_neutral)
    by (auto)
  also have "... = infsum (\<lambda>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n / (2::\<real>)) UNIV"
    using reindex using set_eq by auto
  thm "geometric_sum"
  thm "eventually_sequentially"
  also have "... = 1"
    apply (subst infsetsum_infsum[symmetric])
    apply (simp add: abs_summable_on_nat_iff')
    apply (subst infsetsum_nat)
    apply (simp add: abs_summable_on_nat_iff')
    apply auto
    using power_half_series sums_unique by fastforce
  then show "?lhs = (1::\<real>)"
    using calculation by presburger
qed

lemma coin_flip_t_expected_termination_time: 
  "rvfun_of_prfun flip_t_loop ; (\<guillemotleft>real\<guillemotright> (t\<^sup><))\<^sub>e = (\<lbrakk>coin\<^sup>< = ctail\<rbrakk>\<^sub>\<I>\<^sub>e * (t\<^sup>< + 2)  + \<lbrakk>\<not>coin\<^sup>< = ctail\<rbrakk>\<^sub>\<I>\<^sub>e * t\<^sup>< )\<^sub>e"
  apply (simp add: flip_t_loop)
  apply (simp add: Ht_inverse)
  apply (pred_auto add: Ht_def)
proof -
  fix t coint
  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state.
          (if coin\<^sub>v v\<^sub>0 = chead then 1::\<real> else (0::\<real>)) * (if t\<^sub>v v\<^sub>0 = t then 1::\<real> else (0::\<real>)) * real (t\<^sub>v v\<^sub>0)) 
    = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state. (if coin\<^sub>v v\<^sub>0 = chead \<and> t\<^sub>v v\<^sub>0 = t then real (t) else (0::\<real>)))"
    apply (rule infsum_cong)
    by (auto)
  also have "... = real t"
    apply (subst infsum_constant_finite_states)
    apply (simp add: flip_t_set_eq'')
    by (simp add: flip_t_set_eq'')
  also show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state.
          (if coin\<^sub>v v\<^sub>0 = chead then 1::\<real> else (0::\<real>)) * (if t\<^sub>v v\<^sub>0 = t then 1::\<real> else (0::\<real>)) * real (t\<^sub>v v\<^sub>0)) =
       real t"
    using calculation by blast
next
  fix t
  let ?f = "(\<lambda>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ (n) * ((real t + real n)))"
  have reindex: "infsum (\<lambda>v\<^sub>0::coin_t_state. ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc t) * real (t\<^sub>v v\<^sub>0) / (2::\<real>))
    ((\<lambda>n::\<nat>. \<lparr>t\<^sub>v = Suc t + n, coin\<^sub>v = chead\<rparr>) ` UNIV)
    = infsum (\<lambda>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n * real (Suc t + n) / (2::\<real>)) UNIV"
    apply (subst infsum_reindex)
    apply (simp add: inj_def)
    by (simp add: infsum_cong)

  have summable_f: "summable ?f"
    using summable_1_2_power_n_t_n by blast

  have summable_f_1: "summable (\<lambda>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n * ((1::\<real>) + (real t + real n)))"
    proof -
    have f1: "(\<lambda>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n * ((1::\<real>) + (real t + real n))) = 
          (\<lambda>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n * ((1::\<real>) + real t)  + ((1::\<real>) / (2::\<real>)) ^ n * (real n))"
      by (metis (mono_tags, opaque_lifting) mult_of_nat_commute of_nat_Suc of_nat_add plus_nat.simps(2) ring_class.ring_distribs(2))

    have f2: "(\<lambda>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n * real n) = (\<lambda>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n * n)"
      by simp
    show "summable (\<lambda>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n * ((1::\<real>) + (real t + real n)))"
      apply (simp add: f1)
      apply (subst summable_add)
      apply (rule summable_mult2)
      apply (rule summable_geometric)
      apply simp
      apply (subst summable_cong[where g = "(\<lambda>n::\<nat>. (n / (2::\<real>)^n))"])
      apply (simp add: power_divide)
      using summable_n_2_power_n apply blast
      by simp
  qed

  have summable_f_suc_n: "summable (\<lambda>n. ?f (Suc n))"
    apply (subst summable_Suc_iff)
    using summable_f by auto
  obtain l where P_l: "(\<lambda>n. ?f (Suc n)) sums l"
    using summable_f_suc_n by blast

  have sum_f0: "(\<lambda>n. ?f (Suc n)) sums l \<longleftrightarrow> ?f sums (l + ?f 0)"
    apply (subst sums_Suc_iff)
    by simp

  have suminf_f_l: "?f sums (l + ?f 0)"
    using P_l sum_f0 by blast

  have suminf_f_l': "suminf ?f = l + real t"
    using suminf_f_l sums_unique by force

  have suminf_n_2_power_n: "(\<Sum>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n * ((1::\<real>) + (real t + real n)) / (2::\<real>)) =  
        (\<Sum>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n / 2 +  ((1::\<real>) / (2::\<real>)) ^ n * (real t + real n) / (2::\<real>))"
    apply (rule suminf_cong)
    by (simp add: ring_class.ring_distribs(1))
  also have suminf_n_2_power_n': 
    "... = (\<Sum>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n / 2) +  (\<Sum>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n * (real t + real n) / (2::\<real>))"
    apply (subst suminf_add)
    using summable_2_power_n apply blast
    apply (rule summable_comparison_test[where g = "(\<lambda>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n * ((1::\<real>) + (real t + real n)))"])
    apply (auto)
    using summable_f_1 by blast
  also have suminf_n_2_power_n'': 
    "... = (\<Sum>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n / 2) +  (\<Sum>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n * (real t + real n)) / (2::\<real>)"
    apply (subst suminf_divide[where f = "\<lambda>n. ((1::\<real>) / (2::\<real>)) ^ n * (real t + real n)"])
    apply (rule summable_comparison_test[where g = "(\<lambda>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n * ((1::\<real>) + (real t + real n)))"])
    apply (auto)
    using summable_f_1 by blast
  also have suminf_n_2_power_n''': "... = 1 + (\<Sum>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n * (real t + real n)) / (2::\<real>)"
    using power_half_series sums_unique by fastforce
  also have suminf_n_2_power_n'''': "... = 1 + (l + real t) / 2"
    using suminf_f_l' by presburger

  have suminf_f_suc_n: "(\<Sum>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n * ((1::\<real>) + (real t + real n)) / (2::\<real>)) = suminf (\<lambda>n. ?f (Suc n))"
    by (metis (no_types, opaque_lifting) mult.commute mult_cancel_left2 nat_arith.suc1 of_nat_Suc of_nat_add power_Suc times_divide_eq_right)
  have "l = 1 + (l + real t) / 2"
    using P_l calculation suminf_f_l' suminf_f_suc_n sums_unique by auto
  then have suminf_f_suc_n_l: "l = 2 + real t"
    by (smt (z3) field_sum_of_halves)

  have f0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state.
          (if coin\<^sub>v v\<^sub>0 = chead then 1::\<real> else (0::\<real>)) * (if Suc t \<le> t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) *
          ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc t) * real (t\<^sub>v v\<^sub>0) / (2::\<real>)) = 
        (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state.
          (if coin\<^sub>v v\<^sub>0 = chead \<and> Suc t \<le> t\<^sub>v v\<^sub>0 then (((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc t) *
          real (t\<^sub>v v\<^sub>0) /  (2::\<real>)) else (0::\<real>)))"
    apply (rule infsum_cong)
    by (auto)
  have f1: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state \<in> {v\<^sub>0. coin\<^sub>v v\<^sub>0 = chead \<and> Suc t \<le> t\<^sub>v v\<^sub>0}. 
    (((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc t) * real (t\<^sub>v v\<^sub>0) /  (2::\<real>)))"
    apply (rule infsum_cong_neutral)
    by (auto)
  have f2: "... = infsum (\<lambda>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n * real (Suc t + n) / (2::\<real>)) UNIV"
    using reindex flip_t_set_eq''' by force
  have f3: "... = (2::\<real>) + real t"
    apply (subst infsetsum_infsum[symmetric])
    apply (simp add: abs_summable_on_nat_iff')
    using summable_f_1 apply blast
    apply (subst infsetsum_nat)
    apply (simp add: abs_summable_on_nat_iff')
    using summable_f_1 apply blast
    apply auto
    using calculation suminf_f_l' suminf_f_suc_n_l by linarith
    
  show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state.
          (if coin\<^sub>v v\<^sub>0 = chead then 1::\<real> else (0::\<real>)) * (if Suc t \<le> t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) *
          ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc t) *
          real (t\<^sub>v v\<^sub>0) / (2::\<real>)) = (2::\<real>) + real t "
    using f0 f1 f2 f3 by presburger
qed

subsection \<open> Single coin flip_t (variable probability) with time \<close>
definition flip_t_p:: "ureal \<Rightarrow> coin_t_state prhfun" where
"flip_t_p p = if\<^sub>p \<guillemotleft>p\<guillemotright> then (coin := chead) else (coin := ctail)"

definition flip_t_p_loop where
"flip_t_p_loop p = while\<^sub>p\<^sub>t (coin\<^sup>< = ctail)\<^sub>e do flip_t_p p od"

definition Ht_p:: "ureal \<Rightarrow> coin_t_state rvhfun" where 
"Ht_p p = 
  (\<lbrakk>coin\<^sup>< = ctail\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>coin\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> $t\<^sup>> \<ge> $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1-ureal2real \<guillemotleft>p\<guillemotright>)^(($t\<^sup>> - $t\<^sup>< - 1)) * (ureal2real \<guillemotleft>p\<guillemotright>) + 
   \<lbrakk>\<not>coin\<^sup>< = ctail\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>coin\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>$t\<^sup>> = $t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e )\<^sub>e"

lemma flip_t_p_is_dist: "is_final_distribution (rvfun_of_prfun (flip_t_p p))"
  apply (simp add: flip_t_p_def pchoice_def)
  apply (subst rvfun_pchoice_inverse)
  apply (simp add: ureal_is_prob)
  apply (simp add: ureal_is_prob)
  apply (simp add: rvfun2ureal)
  apply (subst rvfun_pchoice_is_dist_c)
  apply (simp add: passigns_def rvfun_assignment_inverse rvfun_assignment_is_dist)+
  using ureal_lower_bound apply force
  apply (simp add: ureal_upper_bound)
  by simp

lemma flip_t_p_altdef: "rvfun_of_prfun (flip_t_p p) = 
  (\<lbrakk>coin\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> + \<lbrakk>coin\<^sup>> = ctail\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>))\<^sub>e"
  apply (simp add: flip_t_p_def)
  apply (subst prfun_pchoice_altdef)
  apply (subst rvfun_pchoice_inverse)
  using ureal_is_prob apply blast+
  apply (simp add: pfun_defs)
  apply (subst rvfun_assignment_inverse)+
  apply (simp add: rvfun_of_prfun_def)
  by (pred_auto)

definition pt_flip_t_p_alt :: "ureal \<Rightarrow> coin_t_state rvhfun" where
"pt_flip_t_p_alt p \<equiv> (\<lbrakk>coin\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> + 
                      \<lbrakk>coin\<^sup>> = ctail\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1 - ureal2real \<guillemotleft>p\<guillemotright>))\<^sub>e"

lemma pt_flip_t_p: "(Pt (flip_t_p p)) = prfun_of_rvfun (pt_flip_t_p_alt p)"
  apply (simp add: Pt_def pt_flip_t_p_alt_def)
  apply (simp add: pseqcomp_def)
  apply (simp add: flip_t_p_altdef)
  apply (simp add: pfun_defs)
  apply (simp add: rvfun_assignment_inverse)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (simp add: fun_eq_iff)
  apply (rule allI)+
  apply (expr_simp_1)
  apply (pred_auto)
  defer
  apply (smt (verit, best) coin_t_state.surjective infsum_0 mult_eq_0_iff time.ext_inject time.update_convs(1))
  defer
  apply (smt (verit, best) coin_t_state.surjective infsum_0 mult_eq_0_iff time.ext_inject time.update_convs(1))
  apply (meson Tcoin.exhaust)
proof -
  fix t::\<nat>
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state.
          ((if coin\<^sub>v v\<^sub>0 = chead then 1::\<real> else (0::\<real>)) * (if t\<^sub>v v\<^sub>0 = t then 1::\<real> else (0::\<real>)) * ureal2real p +
           (if coin\<^sub>v v\<^sub>0 = ctail then 1::\<real> else (0::\<real>)) * (if t\<^sub>v v\<^sub>0 = t then 1::\<real> else (0::\<real>)) *
           ((1::\<real>) - ureal2real p)) *
          (if \<lparr>t\<^sub>v = Suc t, coin\<^sub>v = chead\<rparr> = v\<^sub>0\<lparr>t\<^sub>v := Suc (t\<^sub>v v\<^sub>0)\<rparr> then 1::\<real> else (0::\<real>)))"
  have "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state. (if coin\<^sub>v v\<^sub>0 = chead \<and> t\<^sub>v v\<^sub>0 = t then ureal2real p else (0::\<real>)))"
    by (smt (verit, best) Tcoin.distinct(1) coin_t_state.select_convs(1) coin_t_state.surjective 
        infsum_cong mult_cancel_left1 mult_cancel_right1 old.unit.exhaust time.update_convs(1))
  moreover have "... = ureal2real p"
    apply (subst infsum_constant_finite_states_subset)
    by (simp add: flip_t_set_eq'')+
  then show "?lhs = ureal2real p"
    using calculation by presburger
next
  fix t::\<nat>
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state.
          ((if coin\<^sub>v v\<^sub>0 = chead then 1::\<real> else (0::\<real>)) * (if t\<^sub>v v\<^sub>0 = t then 1::\<real> else (0::\<real>)) * ureal2real p +
           (if coin\<^sub>v v\<^sub>0 = ctail then 1::\<real> else (0::\<real>)) * (if t\<^sub>v v\<^sub>0 = t then 1::\<real> else (0::\<real>)) *
           ((1::\<real>) - ureal2real p)) *
          (if \<lparr>t\<^sub>v = Suc t, coin\<^sub>v = ctail\<rparr> = v\<^sub>0\<lparr>t\<^sub>v := Suc (t\<^sub>v v\<^sub>0)\<rparr> then 1::\<real> else (0::\<real>)))"
  have "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state. (if coin\<^sub>v v\<^sub>0 = ctail \<and> t\<^sub>v v\<^sub>0 = t then ((1::\<real>) - ureal2real p) else (0::\<real>)))"
    by (smt (verit, ccfv_SIG) Tcoin.distinct(1) coin_t_state.select_convs(1) coin_t_state.surjective 
        infsum_cong mult_cancel_left1 mult_cancel_right1 old.unit.exhaust time.update_convs(1))
  moreover have "... = (1::\<real>) - ureal2real p"
    apply (subst infsum_constant_finite_states_subset)
    by (simp add: flip_t_set_eq'')+
  then show "?lhs = (1::\<real>) - ureal2real p"
    using calculation by presburger
qed

lemma Pt_flip_t_p_1: "(\<Sum>\<^sub>\<infinity>s::coin_t_state.
          (if coin\<^sub>v s = chead then 1::\<real> else (0::\<real>)) * (if t\<^sub>v s = Suc tt then 1::\<real> else (0::\<real>)) * ureal2real p +
          (if coin\<^sub>v s = ctail then 1::\<real> else (0::\<real>)) * (if t\<^sub>v s = Suc tt then 1::\<real> else (0::\<real>)) *
          ((1::\<real>) - ureal2real p)) = 1" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>\<^sub>\<infinity>s::coin_t_state.
          (if coin\<^sub>v s = chead \<and> t\<^sub>v s = Suc tt then ureal2real p else (0::\<real>)) +
          (if coin\<^sub>v s = ctail \<and> t\<^sub>v s = Suc tt then ((1::\<real>) - ureal2real p) else (0::\<real>)))"
    apply (rule infsum_cong)
    by simp
  moreover have "... = 1"
    apply (subst infsum_add)
    apply (simp add: flip_t_set_eq'' infsum_constant_finite_states_summable)+
    apply (subst infsum_constant_finite_states_subset)
    apply (simp add: flip_t_set_eq'')+
    apply (subst infsum_constant_finite_states_subset)
    by (simp add: flip_t_set_eq'')+
  then show ?thesis
    using calculation by presburger
qed

lemma pt_flip_t_p_is_dist: "is_final_distribution (pt_flip_t_p_alt p)"
  apply (simp add: dist_defs pt_flip_t_p_alt_def)
  apply (expr_auto)
  apply (simp add: ureal_lower_bound ureal_upper_bound)+
  using Pt_flip_t_p_1 by blast

lemma Ht_p_inverse: "rvfun_of_prfun (prfun_of_rvfun (Ht_p p)) = (Ht_p p)"
  apply (subst rvfun_inverse)
  apply (simp add: Ht_p_def dist_defs)
  apply (expr_auto)
  apply (simp add: ureal_lower_bound ureal_upper_bound)
  apply (simp add: mult_le_one power_le_one_iff ureal_lower_bound ureal_upper_bound)
  by simp

lemma pt_flip_t_p_alt_inverse: "rvfun_of_prfun (prfun_of_rvfun (pt_flip_t_p_alt p)) = pt_flip_t_p_alt p"
  apply (subst rvfun_inverse)
  apply (simp add: pt_flip_t_p_alt_def dist_defs)
  apply (expr_auto)
  by (simp add: ureal_lower_bound ureal_upper_bound)+

lemma Ht_p_is_fp: "\<F> (coin\<^sup>< = ctail)\<^sub>e (Pt (flip_t_p p)) (prfun_of_rvfun (Ht_p p)) = prfun_of_rvfun (Ht_p p)"
  apply (simp add: loopfunc_def)
  apply (simp add: pfun_defs pt_flip_t_p)
  apply (subst Ht_p_inverse)
  apply (subst pt_flip_t_p_alt_inverse)
  apply (subst rvfun_skip_inverse)
  apply (subst rvfun_skip\<^sub>_f_simp)
  apply (subst rvfun_seqcomp_inverse)
  using pt_flip_t_p_is_dist apply blast
  apply (metis Ht_p_inverse ureal_is_prob)
  apply (subst pt_flip_t_p_alt_def)
  apply (subst Ht_p_def)
  apply (subst Ht_p_def)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (simp add: fun_eq_iff)
  apply (pred_auto)
  defer
  apply (simp add: infsum_0)
  apply (meson Tcoin.exhaust)+
  apply (simp add: infsum_0)
proof -
  fix t t\<^sub>v'
  assume a1: "Suc t \<le> t\<^sub>v'"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state.
          ((if coin\<^sub>v v\<^sub>0 = chead then 1::\<real> else (0::\<real>)) * (if t\<^sub>v v\<^sub>0 = Suc t then 1::\<real> else (0::\<real>)) * ureal2real p +
           (if coin\<^sub>v v\<^sub>0 = ctail then 1::\<real> else (0::\<real>)) * (if t\<^sub>v v\<^sub>0 = Suc t then 1::\<real> else (0::\<real>)) *
           ((1::\<real>) - ureal2real p)) *
          ((if coin\<^sub>v v\<^sub>0 = ctail then 1::\<real> else (0::\<real>)) * (if Suc (t\<^sub>v v\<^sub>0) \<le> t\<^sub>v' then 1::\<real> else (0::\<real>)) *
           ((1::\<real>) - ureal2real p) ^ (t\<^sub>v' - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p +
           (if \<not> coin\<^sub>v v\<^sub>0 = ctail then 1::\<real> else (0::\<real>)) * (if t\<^sub>v' = t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>))))"

  have set_eq_1: "{s::coin_t_state. coin\<^sub>v s = ctail \<and> t\<^sub>v s = Suc t \<and> Suc (t\<^sub>v s) \<le> t\<^sub>v'} = 
        (if Suc (Suc t) \<le> t\<^sub>v' then {\<lparr>t\<^sub>v = Suc t, coin\<^sub>v = ctail\<rparr>} else {})"
    by auto

  have set_eq_2: "{s::coin_t_state. coin\<^sub>v s = chead \<and> t\<^sub>v s = Suc t \<and> t\<^sub>v' = t\<^sub>v s } = 
        (if (Suc t) = t\<^sub>v' then {\<lparr>t\<^sub>v = Suc t, coin\<^sub>v = chead\<rparr>} else {})"
    apply (simp)
    apply (rule impI)
    apply (subst set_eq_iff)
    by (smt (verit, best) coin_t_state.equality coin_t_state.select_convs(1) mem_Collect_eq old.unit.exhaust singleton_iff time.select_convs(1))
  
  have "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state.
          ((if coin\<^sub>v v\<^sub>0 = chead \<and> t\<^sub>v v\<^sub>0 = Suc t \<and> t\<^sub>v' = t\<^sub>v v\<^sub>0 then ureal2real p else (0::\<real>)) +
           (if coin\<^sub>v v\<^sub>0 = ctail \<and> t\<^sub>v v\<^sub>0 = Suc t \<and> Suc (t\<^sub>v v\<^sub>0) \<le> t\<^sub>v' then 
              ((1::\<real>) - ureal2real p)*((1::\<real>) - ureal2real p) ^ (t\<^sub>v' - Suc (Suc t)) * ureal2real p else (0::\<real>))))"
    apply (rule infsum_cong)
    by (auto)
  also have "... = ((1::\<real>) - ureal2real p) ^ (t\<^sub>v' - Suc t) * ureal2real p"
    apply (subst infsum_add)
    apply (rule infsum_constant_finite_states_summable)
    using set_eq_2 apply (smt (verit, del_insts) Collect_cong finite.simps)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, best) finite.emptyI finite.intros(2) flip_t_set_eq mem_Collect_eq rev_finite_subset subset_eq)
    apply (subst infsum_constant_finite_states)
    using set_eq_2 apply (smt (verit, del_insts) Collect_cong finite.simps)
    apply (subst infsum_constant_finite_states)
    apply (simp add: set_eq_1)
    apply (simp add: set_eq_1 set_eq_2)
    by (metis Suc_diff_Suc Suc_le_eq a1 le_antisym mult.commute not_less_eq_eq power_Suc2)
  then show "?lhs = ((1::\<real>) - ureal2real p) ^ (t\<^sub>v' - Suc t) * ureal2real p"
    using calculation by presburger    
qed

lemma Pt_flip_t_p_finite: "\<forall>s. finite {s'::coin_t_state. (0::ureal) < Pt (flip_t_p p) (s, s')}"
proof
  fix s::coin_t_state 
  have "{s'::coin_t_state.
      (coin\<^sub>v s' = chead \<longrightarrow> (t\<^sub>v s' = Suc (t\<^sub>v s) \<longrightarrow> (0::\<real>) < ureal2real p) \<and> t\<^sub>v s' = Suc (t\<^sub>v s)) \<and>
      (\<not> coin\<^sub>v s' = chead \<longrightarrow>
       (coin\<^sub>v s' = ctail \<longrightarrow> (t\<^sub>v s' = Suc (t\<^sub>v s) \<longrightarrow> ureal2real p < (1::\<real>)) \<and> t\<^sub>v s' = Suc (t\<^sub>v s)) \<and> coin\<^sub>v s' = ctail)}
    = {s'::coin_t_state.
      (coin\<^sub>v s' = chead \<longrightarrow> ((0::\<real>) < ureal2real p) \<and> t\<^sub>v s' = Suc (t\<^sub>v s)) \<and>
      (\<not> coin\<^sub>v s' = chead \<longrightarrow> (ureal2real p < (1::\<real>)) \<and> t\<^sub>v s' = Suc (t\<^sub>v s))}"
    apply auto
    using Tcoin.exhaust by blast+
  moreover have "... \<subseteq> {s'::coin_t_state. t\<^sub>v s' = Suc (t\<^sub>v s)}"
    by blast

  moreover have "finite {s'::coin_t_state. t\<^sub>v s' = Suc (t\<^sub>v s)}"
    by (smt (verit, del_insts) Collect_cong Tcoin.exhaust finite.simps flip_t_set_eq)
  then show "finite {s'::coin_t_state. (0::ureal) < Pt (flip_t_p p) (s, s')}"
    apply (simp add: pt_flip_t_p)
    apply (simp add: rvfun_ge_zero)
    apply (simp add: pt_flip_t_p_alt_def)
    by (pred_auto)
qed

lemma flip_t_p_iterdiff_simp:
  shows "(iterdiff 0 (coin\<^sup>< = ctail)\<^sub>e (Pt (flip_t_p p)) 1\<^sub>p) = 1\<^sub>p"
        "(iterdiff (n+1) (coin\<^sup>< = ctail)\<^sub>e (Pt (flip_t_p p)) 1\<^sub>p) = 
            prfun_of_rvfun ((\<lbrakk>coin\<^sup>< = ctail\<rbrakk>\<^sub>\<I>\<^sub>e * (1 - ureal2real \<guillemotleft>p\<guillemotright>)^\<guillemotleft>n\<guillemotright>)\<^sub>e)"
proof -
  show "(iterdiff 0 (coin\<^sup>< = ctail)\<^sub>e (Pt (flip_t_p p)) 1\<^sub>p) = 1\<^sub>p"
    by (auto)

  show "(iterdiff (n+1) (coin\<^sup>< = ctail)\<^sub>e (Pt (flip_t_p p)) 1\<^sub>p) = 
            prfun_of_rvfun ((\<lbrakk>coin\<^sup>< = ctail\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>)^\<guillemotleft>n\<guillemotright>)\<^sub>e)"
    apply (induction n)
    apply (simp add: pfun_defs)
    apply (subst pt_flip_t_p)
    apply (subst pt_flip_t_p_alt_inverse)
    apply (subst ureal_zero)
    apply (subst ureal_one)
    apply (subst rvfun_seqcomp_inverse)
    using pt_flip_t_p_is_dist apply fastforce
    apply (metis ureal_is_prob ureal_one)
    apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
    apply (expr_auto add: rel assigns_r_def)
    apply (simp add: pt_flip_t_p_alt_def)
    apply (pred_auto)
    using Pt_flip_t_p_1 apply blast
    
    apply (simp only: add_Suc)
    apply (simp only: iterdiff.simps(2))
    apply (simp only: pcond_def)
    apply (simp only: pseqcomp_def)
    apply (subst rvfun_seqcomp_inverse)
    using pt_flip_t_p pt_flip_t_p_alt_inverse pt_flip_t_p_is_dist apply presburger
    apply (simp add: ureal_is_prob)
    apply (subst pt_flip_t_p)
    apply (subst pt_flip_t_p_alt_inverse)
    apply (subst rvfun_inverse)
    apply (expr_auto add: dist_defs)
    using ureal_lower_bound apply (simp add: ureal_upper_bound)
    apply (simp add: power_le_one_iff ureal_lower_bound ureal_upper_bound)
    apply (subst pt_flip_t_p_alt_def)
    apply (subst pzero_def)
    apply (subst ureal_zero)
    apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
    apply (expr_auto add: rel assigns_r_def)
  proof -
    fix n t
    let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state.
          ((if coin\<^sub>v v\<^sub>0 = chead then 1::\<real> else (0::\<real>)) * (if t\<^sub>v v\<^sub>0 = Suc t then 1::\<real> else (0::\<real>)) * ureal2real p +
           (if coin\<^sub>v v\<^sub>0 = ctail then 1::\<real> else (0::\<real>)) * (if t\<^sub>v v\<^sub>0 = Suc t then 1::\<real> else (0::\<real>)) *
           ((1::\<real>) - ureal2real p)) *
          ((if coin\<^sub>v v\<^sub>0 = ctail then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) ^ n))"
    have "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state. (if coin\<^sub>v v\<^sub>0 = ctail \<and> t\<^sub>v v\<^sub>0 = Suc t 
          then ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p) ^ n else (0::\<real>)))"
      apply (rule infsum_cong_neutral)
      apply blast
      apply auto[1]
      by simp
    also have "... = ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p) ^ n"
      apply (subst infsum_constant_finite_states_subset)
      apply (smt (verit, del_insts) Collect_mono finite.emptyI finite_insert flip_t_set_eq mem_Collect_eq rev_finite_subset)
      apply (subgoal_tac "{s::coin_t_state. (coin\<^sub>v s = ctail \<and> t\<^sub>v s = Suc t) \<and> s \<in> UNIV} = 
            {s::coin_t_state. coin\<^sub>v s = ctail \<and> t\<^sub>v s = Suc t}")
      using flip_t_set_eq'' apply simp
      by simp

    then show "?lhs = ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p) ^ n"
      using calculation by presburger
  qed
qed

lemma flip_t_p_iterdiff_tendsto_0:
  assumes "p \<noteq> 0"
  shows "\<forall>s. (\<lambda>n::\<nat>. ureal2real (iterdiff n (coin\<^sup>< = ctail)\<^sub>e (Pt (flip_t_p p)) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
proof 
  fix s
  have "(\<lambda>n::\<nat>. ureal2real (iterdiff (n+1) (coin\<^sup>< = ctail)\<^sub>e (Pt (flip_t_p p)) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    apply (subst flip_t_p_iterdiff_simp)
    apply (simp add: prfun_of_rvfun_def)
    apply (expr_auto)
    apply (subst real2ureal_inverse)
    apply (simp add: ureal_upper_bound)
    apply (simp add: power_le_one ureal_lower_bound ureal_upper_bound)
    apply (subst LIMSEQ_realpow_zero)
    apply (simp add: ureal_upper_bound)
    apply (smt (verit, ccfv_threshold) assms linorder_not_le ureal2real_distr ureal2real_inverse 
      ureal_lower_bound ureal_minus_larger_zero verit_comp_simplify1(1))
    apply (simp)
    by (simp add: real2ureal_inverse)
  then show "(\<lambda>n::\<nat>. ureal2real (iterdiff n (coin\<^sup>< = ctail)\<^sub>e (Pt (flip_t_p p)) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    by (rule LIMSEQ_offset[where k = 1])
qed

lemma flip_t_p_loop: 
  assumes "p \<noteq> 0"
  shows "flip_t_p_loop p = prfun_of_rvfun (Ht_p p)"
  apply (simp add: flip_t_p_loop_def ptwhile_def)
  apply (subst unique_fixed_point_lfp_gfp_finite_final'[where fp = "prfun_of_rvfun (Ht_p p)"])
  using pt_flip_t_p pt_flip_t_p_alt_inverse pt_flip_t_p_is_dist apply presburger
  using Pt_flip_t_p_finite apply blast
  using flip_t_p_iterdiff_tendsto_0 assms apply (simp)
  using Ht_p_is_fp apply blast
  by simp

subsubsection \<open> Termination and average termination time \<close>
lemma coin_flip_t_p_termination_prob: 
  assumes "p \<noteq> 0"
  shows "rvfun_of_prfun (flip_t_p_loop p) ; \<lbrakk>coin\<^sup>< = chead\<rbrakk>\<^sub>\<I>\<^sub>e = (1)\<^sub>e"
  apply (simp add: flip_t_p_loop assms)
  apply (subst Ht_p_inverse)
  apply (simp add: Ht_p_def)
  apply (expr_auto)
proof -
  fix t coin
  let ?lhs_f = "\<lambda>v\<^sub>0. (if coin\<^sub>v v\<^sub>0 = chead then 1::\<real> else (0::\<real>))"
  let ?lhs_f2 = "\<lambda>v\<^sub>0. (if t\<^sub>v v\<^sub>0 = t then 1::\<real> else (0::\<real>))"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state. ?lhs_f v\<^sub>0 * ?lhs_f2 v\<^sub>0 * ?lhs_f v\<^sub>0 )"
  have "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state. if coin\<^sub>v v\<^sub>0 = chead \<and> t\<^sub>v v\<^sub>0 = t then 1::\<real> else (0::\<real>))"
    apply (rule infsum_cong)
    by (auto)
  also have "... = 1"
    apply (subst infsum_constant_finite_states)
    by (simp add: flip_t_set_eq'')+
  then show "?lhs = (1::\<real>)"
    using calculation by presburger
next
  fix t
  let ?lhs_f = "\<lambda>v\<^sub>0. (if coin\<^sub>v v\<^sub>0 = chead then 1::\<real> else (0::\<real>))"
  let ?lhs_f2 = "\<lambda>v\<^sub>0. (if Suc t \<le> t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>))"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state. ?lhs_f v\<^sub>0 * ?lhs_f2 v\<^sub>0 * ((1::\<real>) - ureal2real p) ^ (t\<^sub>v v\<^sub>0 - Suc t) *
          ureal2real p * ?lhs_f v\<^sub>0)"

  have reindex: "infsum (\<lambda>v\<^sub>0::coin_t_state. (((1::\<real>) - ureal2real p) ^ (t\<^sub>v v\<^sub>0 - Suc t) * ureal2real p))
    ((\<lambda>n::\<nat>. \<lparr>t\<^sub>v = Suc t + n, coin\<^sub>v = chead\<rparr>) ` UNIV)
    = infsum (\<lambda>n::\<nat>. (((1::\<real>) - ureal2real p) ^ n * ureal2real p)) UNIV"
    apply (subst infsum_reindex)
    apply (simp add: inj_def)
    by (metis cancel_ab_semigroup_add_class.add_diff_cancel_left' comp_apply time.select_convs(1))

  have set_eq: "((\<lambda>n::\<nat>. \<lparr>t\<^sub>v = Suc t + n, coin\<^sub>v = chead\<rparr>) ` UNIV) = {v\<^sub>0. coin\<^sub>v v\<^sub>0 = chead \<and> Suc t \<le> t\<^sub>v v\<^sub>0}"
    apply auto
    by (smt (verit, ccfv_threshold) UNIV_I add_Suc coin_t_state.surjective image_iff nat_le_iff_add old.unit.exhaust)

  have f1: "(\<lambda>n::\<nat>. \<bar>((1::\<real>) - ureal2real p) ^ n * ureal2real p\<bar>) = (\<lambda>n::\<nat>. ((1::\<real>) - ureal2real p) ^ n * ureal2real p)"
    by (meson abs_of_nonneg ge_iff_diff_ge_0 mult_nonneg_nonneg ureal_lower_bound ureal_upper_bound zero_le_power)
  
  have "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state. if coin\<^sub>v v\<^sub>0 = chead \<and> Suc t \<le> t\<^sub>v v\<^sub>0 then
        (((1::\<real>) - ureal2real p) ^ (t\<^sub>v v\<^sub>0 - Suc t) * ureal2real p) else (0::\<real>))"
    apply (rule infsum_cong)
    by (auto)
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state \<in> {v\<^sub>0. coin\<^sub>v v\<^sub>0 = chead \<and> Suc t \<le> t\<^sub>v v\<^sub>0}.
       (((1::\<real>) - ureal2real p) ^ (t\<^sub>v v\<^sub>0 - Suc t) * ureal2real p))"
    apply (rule infsum_cong_neutral)
    by (auto)
  also have "... = infsum (\<lambda>n::\<nat>. (((1::\<real>) - ureal2real p) ^ n * ureal2real p)) UNIV"
    using reindex using set_eq by auto
  also have "... = 1"
    apply (subst infsetsum_infsum[symmetric])
    apply (simp add: abs_summable_on_nat_iff')
    apply (simp only: f1)
    apply (simp add: mult.commute)
    apply (smt (verit) ureal_lower_bound ureal_upper_bound)
    apply (subst infsetsum_nat)
    apply (simp add: abs_summable_on_nat_iff')
    apply (simp only: f1)
    apply (simp add: mult.commute)
    apply (smt (verit) ureal_lower_bound ureal_upper_bound)
    apply (auto)
    apply (simp only: mult.commute)
    apply (subst suminf_mult)
    apply (subst summable_geometric)
    apply (smt (verit, best) assms real_norm_def ureal2rereal_inverse ureal_lower_bound ureal_upper_bound 
          zero_ereal_def zero_ureal.abs_eq)
    apply (simp)
    apply (subst suminf_geometric)
    apply (smt (verit, best) assms real_norm_def ureal2rereal_inverse ureal_lower_bound ureal_upper_bound 
          zero_ereal_def zero_ureal.abs_eq)
    by (metis (no_types, opaque_lifting) assms cancel_ab_semigroup_add_class.diff_right_commute 
        cancel_comm_monoid_add_class.diff_cancel cancel_comm_monoid_add_class.diff_zero 
        divide_self_if minus_diff_eq mult.right_neutral times_divide_eq_right ureal2rereal_inverse 
        zero_ereal_def zero_ureal.abs_eq)
  then show "?lhs = (1::\<real>)"
    using calculation by presburger
qed

lemma coin_flip_t_p_expected_termination_time: 
  assumes "p \<noteq> 0"
  shows "rvfun_of_prfun (flip_t_p_loop p) ; (\<guillemotleft>real\<guillemotright> (t\<^sup><))\<^sub>e 
      = (\<lbrakk>coin\<^sup>< = ctail\<rbrakk>\<^sub>\<I>\<^sub>e * (t\<^sup>< + 1/ureal2real \<guillemotleft>p\<guillemotright>)  + \<lbrakk>\<not>coin\<^sup>< = ctail\<rbrakk>\<^sub>\<I>\<^sub>e * t\<^sup>< )\<^sub>e"
  apply (simp add: flip_t_p_loop assms)
  apply (subst Ht_p_inverse)
  apply (pred_auto add: Ht_p_def)
proof -
  fix t coint
  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state.
          (if coin\<^sub>v v\<^sub>0 = chead then 1::\<real> else (0::\<real>)) * (if t\<^sub>v v\<^sub>0 = t then 1::\<real> else (0::\<real>)) * real (t\<^sub>v v\<^sub>0)) 
    = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state. (if coin\<^sub>v v\<^sub>0 = chead \<and> t\<^sub>v v\<^sub>0 = t then real (t) else (0::\<real>)))"
    apply (rule infsum_cong)
    by (auto)
  also have "... = real t"
    apply (subst infsum_constant_finite_states)
    apply (simp add: flip_t_set_eq'')
    by (simp add: flip_t_set_eq'')
  also show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state. (if coin\<^sub>v v\<^sub>0 = chead then 1::\<real> else (0::\<real>)) * 
      (if t\<^sub>v v\<^sub>0 = t then 1::\<real> else (0::\<real>)) * real (t\<^sub>v v\<^sub>0)) = real t"
    using calculation by blast
next
  fix t

  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state.
          (if coin\<^sub>v v\<^sub>0 = chead then 1::\<real> else (0::\<real>)) * (if Suc t \<le> t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) *
          ((1::\<real>) - ureal2real p) ^ (t\<^sub>v v\<^sub>0 - Suc t) * ureal2real p * real (t\<^sub>v v\<^sub>0))"
  let ?f1 = "(\<lambda>n::\<nat>. ((1::\<real>) - ureal2real p) ^ (n) * (real (Suc t) + real n))"
  let ?f = "(\<lambda>n::\<nat>. ?f1 n * ureal2real p)"

  have reindex: "infsum (\<lambda>v\<^sub>0::coin_t_state. ((1::\<real>) - ureal2real p) ^ (t\<^sub>v v\<^sub>0 - Suc t) * ureal2real p * real (t\<^sub>v v\<^sub>0))
      ((\<lambda>n::\<nat>. \<lparr>t\<^sub>v = Suc t + n, coin\<^sub>v = chead\<rparr>) ` UNIV)
    = infsum (\<lambda>n::\<nat>. ((1::\<real>) - ureal2real p) ^ n * ureal2real p * real (Suc t + n)) UNIV"
    apply (subst infsum_reindex)
    apply (simp add: inj_def)
    by (metis (no_types, lifting) cancel_ab_semigroup_add_class.add_diff_cancel_left' comp_apply 
        time.select_convs(1))

  \<comment> \<open> Prove the function is summable over @{text "\<nat>"} based on the ratio test, that is, 
  the sequence decreases at least a ratio (less than 1) after some n. \<close>
  have summable_n_p_power_n: "summable (\<lambda>n::\<nat>. ((1::\<real>) - ureal2real p) ^ n * real n)"
  (* n:                                0,       1,           2,          3,         4         5, 6*)
  (* ((1::\<real>) - p) ^ n * n:            0,      1*(1-p)^1,  2*(1-p)^2,  3*(1-p)^3, 4*(1-p)^4 *)
  (* ((1::\<real>) - p) ^ (n+1) * (n+1): 1*(1-p)^1, 2*(1-p)^2,  3*(1-p)^3,  4*(1-p)^4, 5*(1-p)^5,*)
  (* ratio ((n+1)/n) * (1-p):         x,       2*(1-p),    (3/2)*(1-p), (4/3)*(1-p),  ... ,  *)
  proof -
    let ?n = "(nat \<lfloor>((1::\<real>) - ureal2real p) / ureal2real p\<rfloor>)"
    let ?one_p = "((1::\<real>) - ureal2real p)"
    have less: "?one_p < (ureal2real p) * (real ?n + 1)"
      by (smt (verit, del_insts) assms floor_eq_iff mult.commute nat_floor_neg of_nat_nat 
          pos_divide_less_eq ureal2rereal_inverse ureal_lower_bound zero_ereal_def zero_le_floor zero_ureal.abs_eq)
    have f1: "?one_p * real (?n + (1::\<nat>) + (1::\<nat>)) = ?one_p * ((real (?n) + 1) + 1)"
      by auto
    have f2: "... = (1 * (real (?n) + 1) - (ureal2real p) * (real (?n) + 1) + ?one_p)"
      by (simp add: distrib_left left_diff_distrib')
    have f3: "... = ((real (?n) + 1) + ?one_p - (ureal2real p) * (real (?n) + 1))"
      by auto
    have f4: "... < (real (?n) + 1)"
      using less by linarith
    (* have "\<exists>n. (real n / real (n+1)) > (1 - ureal2real p)"
      apply (rule_tac x = "nat \<lfloor>(1- ureal2real p) / (ureal2real p)\<rfloor> + 1" in exI) *)

    show ?thesis
      apply (subst summable_ratio_test[where c="(real (?n+1+1) / real (?n+1)) * ?one_p" and N="?n + 1"])
      apply (smt (verit, best) add_gr_0 divide_less_eq_1_pos f2 f4 mult_of_nat_commute of_nat_0_less_iff of_nat_1 of_nat_add times_divide_eq_left)
      apply auto
      apply (subst abs_of_nonneg)
      apply (simp add: ureal_upper_bound)
      apply (subst abs_of_nonneg)
      apply (simp add: ureal_upper_bound)
      proof -
        fix n::\<nat>
        assume a1: "Suc ?n \<le> n"
        have f0: "((1::\<real>) + real (Suc ?n))/real (Suc ?n) = ((2::\<real>) + real ?n) / ((1::\<real>) + real ?n)"
          by auto
        have "\<forall>m n. n > 0 \<and> m \<ge> n \<longrightarrow> ((1::\<real>) + real m)/real m \<le> ((1::\<real>) + real n)/real n"
          apply auto
          proof -
            fix m and n :: \<nat>
            assume a0: "0 < n"
            assume a1: "n \<le> m"
            have "real n + real m * real n \<le> real m + real m * real n"
              using a1 by fastforce
            then have "(1 + real m) * real n \<le> (1 + real n) * real m"
              by (simp add: distrib_left mult.commute)
            then show "((1::\<real>) + real m) / real m \<le> ((1::\<real>) + real n) / real n "
              using a0 a1
              by (smt (verit, del_insts) le_divide_eq linorder_not_less mult_imp_div_pos_le 
                  mult_of_nat_commute of_nat_0_le_iff of_nat_le_iff order_le_less times_divide_eq_right)
            qed
        then have "((1::\<real>) + real n)/real n \<le> ((2::\<real>) + real ?n) / ((1::\<real>) + real ?n)"
          using a1 f0 by (metis zero_less_Suc)
        then have "((1::\<real>) + real n) \<le> (((2::\<real>) + real ?n) * (real n) / ((1::\<real>) + real ?n))"
          by (smt (verit, ccfv_SIG) a1 divide_divide_eq_left divide_divide_eq_right divide_minus_left 
              divide_self_if field_sum_of_halves linorder_not_le mult.commute mult_cancel_left2 
              mult_of_nat_commute nat_1_add_1 nonzero_mult_div_cancel_left numerals(1) 
              of_nat_0_less_iff of_nat_1 of_nat_Suc of_nat_eq_0_iff of_nat_le_iff of_nat_less_0_iff 
              pos_divide_less_eq times_divide_eq_left times_divide_times_eq)
        then have "?one_p ^ n * ((1::\<real>) + real n) \<le> 
              ?one_p ^ n * (((2::\<real>) + real ?n) * (real n) / ((1::\<real>) + real ?n))"
          apply (subst ordered_comm_semiring_class.comm_mult_left_mono)
          apply blast
          by (simp add: ureal_upper_bound)+
        then have "?one_p ^ n * ((1::\<real>) + real n) \<le> 
          ((2::\<real>) + real ?n) * (?one_p ^ n * real n) / ((1::\<real>) + real ?n)" 
          by (simp add: Groups.mult_ac(3))
        then have "?one_p * (?one_p ^ n * ((1::\<real>) + real n)) \<le> 
          ?one_p * (((2::\<real>) + real ?n) * (?one_p ^ n * real n) / ((1::\<real>) + real ?n))"
          apply (subst ordered_comm_semiring_class.comm_mult_left_mono)
          apply blast
          by (simp add: ureal_upper_bound)+
        
        then show "?one_p * ?one_p ^ n * ((1::\<real>) + real n) \<le> 
          ((2::\<real>) + real ?n) * ?one_p * (?one_p ^ n * real n) / ((1::\<real>) + real ?n)"
          by (simp add: Groups.mult_ac(3) mult.commute)
      qed
  qed

  have summable_f_1: "summable (\<lambda>n::\<nat>. ((1::\<real>) - ureal2real p) ^ n * ureal2real p * ((1::\<real>) + (real t + real n)))"
  proof -
    have f1: "(\<lambda>n::\<nat>. ((1::\<real>) - ureal2real p) ^ n * ureal2real p * ((1::\<real>) + (real t + real n))) = 
          (\<lambda>n::\<nat>. ureal2real p * (((1::\<real>) - ureal2real p) ^ n * ((1::\<real>) + (real t + real n))))"
      using mult.commute by fastforce

    have f2: "(\<lambda>n::\<nat>. ((1::\<real>) - ureal2real p) ^ n * ((1::\<real>) + (real t + real n))) = 
          (\<lambda>n::\<nat>. ((1::\<real>) - ureal2real p) ^ n * ((1::\<real>) + real t)  + ((1::\<real>) - ureal2real p) ^ n * (real n))"
      by (metis (mono_tags, opaque_lifting) mult_of_nat_commute of_nat_Suc of_nat_add plus_nat.simps(2) 
          ring_class.ring_distribs(2))

    have f3: "(\<lambda>n::\<nat>. ((1::\<real>) - ureal2real p) ^ n * real n) = (\<lambda>n::\<nat>. ((1::\<real>) - ureal2real p) ^ n * n)"
      by simp

    show ?thesis
      apply (simp add: f1)
      apply (rule disjI2)
      apply (simp add: f2)
      apply (subst summable_add)
      apply (rule summable_mult2)
      apply (rule summable_geometric)
      apply (smt (verit, best) assms real_norm_def ureal2rereal_inverse ureal_lower_bound 
          ureal_upper_bound zero_ereal_def zero_ureal.abs_eq)
      apply auto
      using summable_n_p_power_n by blast
  qed

  have summable_f_1': "summable (\<lambda>n::\<nat>. \<bar>((1::\<real>) - ureal2real p) ^ n * ureal2real p * ((1::\<real>) + (real t + real n))\<bar>)"
    apply (subst abs_of_nonneg)
    apply (simp add: ureal_lower_bound ureal_upper_bound)
    using summable_f_1 by blast


  have summable_f1: "summable ?f1"
  proof -
    have f1: "(\<lambda>n::\<nat>. ((1::\<real>) - ureal2real p) ^ n * (real (Suc t) + real n)) = 
          (\<lambda>n::\<nat>. ((1::\<real>) - ureal2real p) ^ n * (1 + real t)  + ((1::\<real>) - ureal2real p) ^ n * (n))"
      using  mult.commute ring_class.ring_distribs(2)
      by (metis (mono_tags, opaque_lifting) of_nat_Suc)
    show ?thesis
      apply (simp only: f1)
      apply (subst summable_add)
      apply (rule summable_mult2)
      apply (rule summable_geometric)
      apply (smt (verit, best) assms real_norm_def ureal2rereal_inverse ureal_lower_bound 
          ureal_upper_bound zero_ereal_def zero_ureal.abs_eq)
      using summable_n_p_power_n apply blast
      by simp
  qed

  have summable_f: "summable ?f"
    using summable_f1 summable_mult2 by blast

  have summable_f_suc_n: "summable (\<lambda>n. ?f (Suc n))"
    apply (subst summable_Suc_iff)
    using summable_f by auto
  obtain l where P_l: "(\<lambda>n. ?f (Suc n)) sums l"
    using summable_f_suc_n by blast

  have sum_f0: "(\<lambda>n. ?f (Suc n)) sums l \<longleftrightarrow> ?f sums (l + ?f 0)"
    apply (subst sums_Suc_iff)
    by simp

  have suminf_f_l: "?f sums (l + ?f 0)"
    using P_l sum_f0 by blast

  have suminf_f_l': "suminf ?f = l + real (Suc t) * ureal2real p"
    using suminf_f_l sums_unique by force

  have suminf_f_l'': "(\<Sum>n::\<nat>. ((1::\<real>) - ureal2real p) ^ n * ureal2real p * ((1::\<real>) + (real t + real n))) =
        suminf ?f"
    by (metis (no_types, opaque_lifting) add.commute add_Suc_right mult.assoc mult.commute of_nat_Suc of_nat_add)

  have suminf_n_p_power_n: "(\<Sum>n::\<nat>. ?f (Suc n)) =  
        (\<Sum>n::\<nat>. ((1::\<real>) - ureal2real p) ^ Suc n * 1 * ureal2real p + 
            ((1::\<real>) - ureal2real p) ^ Suc n * (real (Suc t) + real (n)) * ureal2real p)"
    apply (rule suminf_cong)
    by (metis (no_types, opaque_lifting) add_Suc_right distrib_left mult.commute of_nat_Suc of_nat_add)
  also have suminf_n_p_power_n': 
    "... = (\<Sum>n::\<nat>. ((1::\<real>) - ureal2real p) ^ Suc n * ureal2real p) +
           (\<Sum>n::\<nat>. ((1::\<real>) - ureal2real p) * ?f (n))"
    apply (subst suminf_add)
    apply (rule summable_mult2)
    apply (subst summable_Suc_iff)
    apply (rule summable_geometric)
    apply (smt (verit, best) assms real_norm_def ureal2rereal_inverse ureal_lower_bound 
        ureal_upper_bound zero_ereal_def zero_ureal.abs_eq)
    using summable_f apply force
    by (smt (verit, ccfv_SIG) mult.assoc power_Suc suminf_cong)
  also have suminf_n_p_power_n': 
    "... = (\<Sum>n::\<nat>. ((1::\<real>) - ureal2real p) ^ n * (((1::\<real>) - ureal2real p) * ureal2real p)) +
           (\<Sum>n::\<nat>. ((1::\<real>) - ureal2real p) * ?f (n))"
    by (simp add: mult.commute mult.left_commute)
  also have suminf_n_p_power_n'': 
    "... = ((1::\<real>) - ureal2real p) +   ((1::\<real>) - ureal2real p) * (\<Sum>n::\<nat>. ?f (n))"
    apply (subst suminf_mult2[symmetric])
    apply (rule summable_geometric)
    apply (smt (verit, best) assms real_norm_def ureal2rereal_inverse ureal_lower_bound 
        ureal_upper_bound zero_ereal_def zero_ureal.abs_eq)
    apply (subst suminf_geometric)
    apply (smt (verit, best) assms real_norm_def ureal2rereal_inverse ureal_lower_bound 
        ureal_upper_bound zero_ereal_def zero_ureal.abs_eq)
    apply (subst suminf_mult)
    using summable_f apply blast
    by (smt (verit, best) assms mult_cancel_right2 nonzero_mult_div_cancel_right times_divide_eq_left 
        ureal2rereal_inverse zero_ereal_def zero_ureal.abs_eq)
  also have suminf_n_p_power_n''': 
    "... = ((1::\<real>) - ureal2real p) + ((1::\<real>) - ureal2real p) * (l + real (Suc t) * ureal2real p)"
    using suminf_f_l' by force

  have suminf_f_suc_n: 
    "l = ((1::\<real>) - ureal2real p) + ((1::\<real>) - ureal2real p) * (l + real (Suc t) * ureal2real p)"
    using P_l calculation suminf_f_l' sums_unique by auto
  then have "ureal2real p * l = ((1::\<real>) - ureal2real p) + ((1::\<real>) - ureal2real p) * real (Suc t) * ureal2real p"
    using mult.assoc mult_cancel_right2 right_diff_distrib ring_class.ring_distribs(2) 
    by (smt (verit) left_diff_distrib' mult.commute)
  then have suminf_f_suc_n_l: "l = ((1::\<real>) - ureal2real p) * (1 + real (Suc t) * ureal2real p) / ureal2real p"
    by (smt (verit, ccfv_SIG) mult.assoc mult_right_cancel nonzero_mult_div_cancel_left 
        nonzero_mult_divide_mult_cancel_left nonzero_mult_divide_mult_cancel_right of_nat_0 
        of_nat_neq_0 power.simps(1) ring_class.ring_distribs(1) suminf_f_l suminf_f_l' sums_unique)

  have ff0: "((1::\<real>) - ureal2real p) * ((1::\<real>) + real (Suc t) * ureal2real p) / ureal2real p + real (Suc t) * ureal2real p 
    = 1 *              ((1::\<real>) + real (Suc t) * ureal2real p) / ureal2real p 
      - ureal2real p * ((1::\<real>) + real (Suc t) * ureal2real p) / ureal2real p 
      + real (Suc t) * ureal2real p"
    by (simp add: diff_divide_distrib left_diff_distrib)
  have ff1: "... = 1 / (ureal2real p) + real (Suc t) - 1"
    by (smt (verit, best) add_divide_eq_iff assms nonzero_mult_div_cancel_left ureal2rereal_inverse 
        zero_ereal_def zero_ureal.abs_eq)

  have f0: "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state. (if coin\<^sub>v v\<^sub>0 = chead \<and> Suc t \<le> t\<^sub>v v\<^sub>0 then 
        ((1::\<real>) - ureal2real p) ^ (t\<^sub>v v\<^sub>0 - Suc t) * ureal2real p * real (t\<^sub>v v\<^sub>0) else (0::\<real>)))"
    apply (rule infsum_cong)
    by (auto)
  have f1: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_t_state \<in> {v\<^sub>0. coin\<^sub>v v\<^sub>0 = chead \<and> Suc t \<le> t\<^sub>v v\<^sub>0}. 
    ((1::\<real>) - ureal2real p) ^ (t\<^sub>v v\<^sub>0 - Suc t) * ureal2real p * real (t\<^sub>v v\<^sub>0))"
    apply (rule infsum_cong_neutral)
    by (auto)
  have f2: "... = infsum (\<lambda>n::\<nat>. ((1::\<real>) - ureal2real p) ^ n * ureal2real p * real (Suc t + n)) UNIV"
    using reindex flip_t_set_eq''' by force
  have f3: "... = real t + (1::\<real>) / ureal2real p"
    apply (subst infsetsum_infsum[symmetric])
    apply (simp add: abs_summable_on_nat_iff')
    using summable_f_1' apply blast
    apply (subst infsetsum_nat)
    apply (simp add: abs_summable_on_nat_iff')
    using summable_f_1' apply blast
    apply auto
    apply (simp only: suminf_f_l'' suminf_f_l' suminf_f_suc_n_l)
    by (simp only: ff0 ff1)
    
  show "?lhs = real t + (1::\<real>) / ureal2real p"
    using f0 f1 f2 f3 by presburger
qed

end