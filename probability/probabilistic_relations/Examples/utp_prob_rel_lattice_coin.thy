section \<open> Probabilistic relation programming example 1 \<close>

theory utp_prob_rel_lattice_coin
  imports 
    "../utp_prob_rel" 
begin 

unbundle UTP_Syntax

declare [[show_types]]

subsection \<open> Single coin flip without time\<close>

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
  shows "iterate\<^sub>p 0 (c\<^sup>< = ctail)\<^sub>e cflip 0\<^sub>p = 0\<^sub>p"
        "iterate\<^sub>p (Suc 0) (c\<^sup>< = ctail)\<^sub>e cflip 0\<^sub>p = (\<lbrakk>$c\<^sup>< = chead \<and> $c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)"
        "iterate\<^sub>p (n+2) (c\<^sup>< = ctail)\<^sub>e cflip 0\<^sub>p = 
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
  "(\<Squnion>n::\<nat>. iterate\<^sub>p (n+2) (c\<^sup>< = ctail)\<^sub>e cflip 0\<^sub>p) = (\<Squnion>n::\<nat>. iterate\<^sub>p (n) (c\<^sup>< = ctail)\<^sub>e cflip 0\<^sub>p)"
  apply (rule increasing_chain_sup_subset_eq)
  apply (rule iterate_increasing_chain)
  by (simp add: cflip_is_dist)

lemma cflip_iterate_limit_sup:
  assumes "f = (\<lambda>n. (iterate\<^sub>p (n+2) (c\<^sup>< = ctail)\<^sub>e cflip 0\<^sub>p))"
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
  assumes "f = (\<lambda>n. (iterate\<^sub>p (n+2) (c\<^sup>< = ctail)\<^sub>e cflip 0\<^sub>p))"
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
  assumes "f = (\<lambda>n. (iterate\<^sub>p (n+2) (c\<^sup>< = ctail)\<^sub>e cflip 0\<^sub>p))"
  shows "((\<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e s) = (ureal2real (\<Squnion>n::\<nat>. f n s))"
  apply (subst LIMSEQ_unique[where X = "(\<lambda>n. ureal2real (f n s))" and a = "((\<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e s)" and 
          b = "(ureal2real (\<Squnion>n::\<nat>. f n s))"])
  using cflip_iterate_limit_cH apply (simp add: assms)
  using cflip_iterate_limit_sup apply (simp add: assms)
  by auto

lemma fi: "(\<Squnion>n::\<nat>. iterate\<^sub>p (n+2) (c\<^sup>< = ctail)\<^sub>e cflip 0\<^sub>p) = 
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
text \<open> The probability of @{text "c'"} being @{text "head"} is 1, and so almost-sure termination.\<close>
lemma coin_flip_termination_prob: "cH ; \<lbrakk>c\<^sup>< = chead\<rbrakk>\<^sub>\<I>\<^sub>e = (1)\<^sub>e"
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
lemma coin_flip_nontermination_prob: "cH ; \<lbrakk>\<not>c\<^sup>< = chead\<rbrakk>\<^sub>\<I>\<^sub>e = (0)\<^sub>e"
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

subsection \<open> Single coin flip (variable probability)\<close>
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

subsection \<open> Coin flip with time \<close>
alphabet coin_state = time +
  coin :: Tcoin

thm "coin_state.simps"
definition flip:: "coin_state prhfun" where
"flip = (prfun_of_rvfun (coin \<^bold>\<U> {chead, ctail}))"

definition flip_loop where
"flip_loop = while\<^sub>p\<^sub>t (coin\<^sup>< = ctail)\<^sub>e do flip od"

definition H:: "coin_state \<times> coin_state \<Rightarrow> \<real>" where 
"H = (\<lbrakk>coin\<^sup>> = chead \<and> $t\<^sup>> \<ge> $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1/2)^(($t\<^sup>> - $t\<^sup>< - 1)) * (1/2))\<^sub>e"

lemma flip_is_dist: "is_final_distribution (rvfun_of_prfun flip)"
  apply (simp add: flip_def)
  apply (subst rvfun_uniform_dist_inverse)
  apply (simp)+
  using rvfun_uniform_dist_is_dist
  by (metis coin_vwb_lens finite.emptyI finite.insertI insert_not_empty)

lemma flip_altdef: "rvfun_of_prfun flip = (\<lbrakk>\<Squnion> v \<in> {ctail, chead}. coin := \<guillemotleft>v\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e / 2)\<^sub>e"
  apply (simp add: flip_def)
  apply (subst prfun_uniform_dist_altdef')
  apply simp+
  by (pred_auto)

definition flip_t_alt :: "coin_state rvhfun" where
"flip_t_alt \<equiv> (\<lbrakk>coin\<^sup>> \<in> {chead, ctail} \<and> $t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 2)\<^sub>e"

lemma flip_t: "(Pt flip) = prfun_of_rvfun flip_t_alt"
  apply (simp add: flip_def Pt_def flip_t_alt_def)
  apply (simp add: prfun_uniform_dist_left)
  apply (simp add: pfun_defs)
  apply (simp add: rvfun_assignment_inverse)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (simp add: fun_eq_iff)
  apply (rule allI)+
  by (expr_auto add: rel assigns_r_def)

lemma flip_t_set_eq: 
  "\<forall>t. {s::coin_state. (coin\<^sub>v s = chead \<or> coin\<^sub>v s = ctail) \<and> t\<^sub>v s = Suc t} = 
  {\<lparr>t\<^sub>v = Suc t, coin\<^sub>v = chead\<rparr>, \<lparr>t\<^sub>v = Suc t, coin\<^sub>v = ctail\<rparr>}"
  by (auto)

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
      coin_state.ext_inject field_sum_of_halves finite.emptyI finite.insertI insert_absorb 
      insert_not_empty of_nat_1 of_nat_add one_add_one singletonD time.ext_inject)

lemma iterate_tflip_bottom_simp:
  shows "iterate\<^sub>p 0 (coin\<^sup>< = ctail)\<^sub>e (Pt flip) 0\<^sub>p = 0\<^sub>p"
        "iterate\<^sub>p (Suc 0) (coinc\<^sup>< = ctail)\<^sub>e (Pt flip) 0\<^sub>p = (\<lbrakk>$coin\<^sup>< = chead \<and> $coin\<^sup>> = chead \<and> $t\<^sup>> = $t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e)"
        "iterate\<^sub>p (n+2) (coin\<^sup>< = ctail)\<^sub>e (Pt flip) 0\<^sub>p = 
              (\<lbrakk>$coin\<^sup>< = chead \<and> $coin\<^sup>> = chead \<and> $t\<^sup>> = $t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e + 
               \<lbrakk>$coin\<^sup>< = ctail \<and> $coin\<^sup>> = chead \<and> $t\<^sup>> \<ge> $t\<^sup>< + 1 \<and> $t\<^sup>> \<le> $t\<^sup>< + \<guillemotleft>n\<guillemotright> + 1\<rbrakk>\<^sub>\<I>\<^sub>e 
                * (\<Sum>i\<in>{1..\<guillemotleft>n+1\<guillemotright>}. (1/2)^i))\<^sub>e"
  sorry
  (*apply (auto)
  apply (simp add: loopfunc_def)
  apply (simp add: prfun_zero_right')
  apply (simp add: pfun_defs)
  apply (subst rvfun_skip_inverse)
  apply (subst ureal_zero)
  apply (simp add: ureal_defs)
  apply (subst fun_eq_iff)
  apply (expr_auto)
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
  apply (expr_auto)
  apply (simp add: real2ureal_def)
  apply (simp add: infsum_0 iverson_bracket_def real2ureal_def rel_skip)
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
*)

lemma H_is_dist: "is_final_distribution H"
  apply (simp add: dist_defs H_def)
  apply (simp add: expr_defs)
  apply (auto)
  apply (smt (verit, best) field_sum_of_halves power_le_one)
  apply (simp add: lens_defs)
proof -
  fix s\<^sub>1::"coin_state"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>s::coin_state.
          (if coin\<^sub>v s = chead \<and> Suc (t\<^sub>v s\<^sub>1) \<le> t\<^sub>v s then 1::\<real> else (0::\<real>)) *
          ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - Suc (t\<^sub>v s\<^sub>1)) / (2::\<real>))"
  let ?set = "{s::coin_state. coin\<^sub>v s = chead \<and> Suc (t\<^sub>v s\<^sub>1) \<le> t\<^sub>v s}"

  (*
  thm "infsum_reindex"
  have "(\<Sum>\<^sub>\<infinity>t::nat \<in> {t. t \<ge> Suc (t\<^sub>v s\<^sub>1)}. ((1::\<real>) / (2::\<real>)) ^ (t - Suc (t\<^sub>v s\<^sub>1) + 1)) = 1"
    apply (subst infsum_reindex[where h = "\<lambda>s::coin_state. t\<^sub>v s" and A = "?set"])
*)
  have f1: "?lhs = (\<Sum>\<^sub>\<infinity>s::coin_state \<in> ?set \<union> -?set.
          (if coin\<^sub>v s = chead \<and> Suc (t\<^sub>v s\<^sub>1) \<le> t\<^sub>v s then 1::\<real> else (0::\<real>)) *
          ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - Suc (t\<^sub>v s\<^sub>1)) / (2::\<real>))"
    by auto
  moreover have "... = (\<Sum>\<^sub>\<infinity>s::coin_state \<in> ?set.
          (if coin\<^sub>v s = chead \<and> Suc (t\<^sub>v s\<^sub>1) \<le> t\<^sub>v s then 1::\<real> else (0::\<real>)) *
          ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - Suc (t\<^sub>v s\<^sub>1)) / (2::\<real>))"
    apply (rule infsum_cong_neutral)
    apply force
    apply simp
    by blast
  moreover have "... = (\<Sum>\<^sub>\<infinity>s::coin_state \<in> ?set. ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - Suc (t\<^sub>v s\<^sub>1)) / (2::\<real>))"
    by (smt (verit) infsum_cong mem_Collect_eq mult_cancel_right2)
  moreover have "... = (\<Sum>\<^sub>\<infinity>s::coin_state \<in> ?set. ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - Suc (t\<^sub>v s\<^sub>1) + 1))"
    by auto
  moreover have "... = (\<Sum>\<^sub>\<infinity>t::nat \<in> {t. t \<ge> Suc (t\<^sub>v s\<^sub>1)}. ((1::\<real>) / (2::\<real>)) ^ (t - Suc (t\<^sub>v s\<^sub>1) + 1))"
    apply (subst infsum_reindex_bij_betw[symmetric, where g = "\<lambda>s::coin_state. t\<^sub>v s" and A = "?set"])
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

lemma "finite {s::coin_state \<times> coin_state. \<exists>n::\<nat>. \<not> iterate\<^sub>t n (coin\<^sup>< = ctail)\<^sub>e flip 0\<^sub>p s = (0::ureal)}"
proof -
  have f0: "iterate\<^sub>t (n + 2) (coin\<^sup>< = ctail)\<^sub>e flip 0\<^sub>p = 
          (\<lbrakk>$coin\<^sup>< = chead \<and> $coin\<^sup>> = chead \<and> $t\<^sup>> = $t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e + 
           \<lbrakk>$coin\<^sup>< = ctail \<and> $coin\<^sup>> = chead \<and> $t\<^sup>> \<ge> $t\<^sup>< + 1 \<and> $t\<^sup>> \<le> $t\<^sup>< + \<guillemotleft>n\<guillemotright> + 1\<rbrakk>\<^sub>\<I>\<^sub>e 
           * (\<Sum>i\<in>{1..\<guillemotleft>n+1\<guillemotright>}. (1/2)^i))\<^sub>e"
    by (simp only: iterate_tflip_bottom_simp)

  have "\<not> (iterate\<^sub>t (n + 2) (coin\<^sup>< = ctail)\<^sub>e flip 0\<^sub>p (\<lparr>t\<^sub>v = tt, coin\<^sub>v = chead\<rparr>, \<lparr>t\<^sub>v = tt, coin\<^sub>v = chead\<rparr>) 
        = (0::ureal))"
    apply (subst f0)
    apply (expr_auto)
    using one_ereal_def one_ureal_def by auto

  have "(iterate\<^sub>t (n + 2) (coin\<^sup>< = ctail)\<^sub>e flip 0\<^sub>p (\<lparr>t\<^sub>v = x, coin\<^sub>v = ctail\<rparr>, \<lparr>t\<^sub>v = y, coin\<^sub>v = ctail\<rparr>) 
        = (0::ureal))"
    apply (subst f0)
    apply (expr_auto)
    by (simp add: zero_ereal_def zero_ureal_def)

  have "{s::coin_state \<times> coin_state. \<exists>n::\<nat>. \<not> iterate\<^sub>t (n) (coin\<^sup>< = ctail)\<^sub>e flip 0\<^sub>p s = (0::ureal)}
    = {s::coin_state \<times> coin_state. \<exists>n::\<nat>. \<not> iterate\<^sub>t (n+2) (coin\<^sup>< = ctail)\<^sub>e flip 0\<^sub>p s = (0::ureal)}"
    apply (subst set_eq_iff)
    apply (rule allI)+
    apply (rule iffI)
    apply (simp add: expr_defs lens_defs)
    using iterate_increasing2
    apply (smt (z3) Suc_eq_plus1 flip_t flip_t_is_dist is_final_distribution_prob is_final_prob_prob 
        iterate_increasing1 le_funD nle_le pzero_def rvfun_inverse ureal_bottom_least' iterate.simps(2))
    apply (simp add: expr_defs lens_defs)
    by (metis utp_prob_rel_lattice.iterate.simps(2))

  text \<open> From the formula above and below, we can see this set is not finite because there are infinite 
    number of states to satisfy @{text "t\<^sub>v (fst s) = t\<^sub>v (snd s)"} where @{text "t"} could be any natural number. \<close>
  have "{s::coin_state \<times> coin_state. \<exists>n::\<nat>. \<not> iterate\<^sub>t (n+2) (coin\<^sup>< = ctail)\<^sub>e flip 0\<^sub>p s = (0::ureal)}
    = {s::coin_state \<times> coin_state. (coin\<^sub>v (fst s) = chead \<and> coin\<^sub>v (snd s) = chead \<and> t\<^sub>v (fst s) = t\<^sub>v (snd s))
      \<or> (coin\<^sub>v (fst s) = ctail \<and> coin\<^sub>v (snd s) = chead \<and> t\<^sub>v (snd s) \<ge> t\<^sub>v (fst s) + 1)}"
    apply (simp only: iterate_tflip_bottom_simp)
    apply (subst set_eq_iff)
    apply (simp add: expr_defs lens_defs)
    apply (rule allI)+
    apply (rule conjI)
    apply (metis one_ereal_def one_ureal_def zero_neq_one)
    apply (rule impI)
    apply (rule iffI)
    apply (metis zero_ereal_def zero_ureal_def)
    apply (auto)
    apply (smt (verit, best) Suc_eq_plus1 add_Suc_shift field_sum_of_halves nat_le_iff_add power_one_over real2eureal_inverse sum_1_2 sum_geometric_series sum_geometric_series_ureal ureal_lower_bound zero_ereal_def zero_ureal_def)
    by (smt (verit, best) Suc_eq_plus1 add_Suc_shift field_sum_of_halves nat_le_iff_add power_one_over real2eureal_inverse sum_1_2 sum_geometric_series sum_geometric_series_ureal ureal_lower_bound zero_ereal_def zero_ureal_def)

  have "finite {s::coin_state \<times> coin_state. \<exists>n::\<nat>. \<not> iterate\<^sub>t (n+2) (coin\<^sup>< = ctail)\<^sub>e flip 0\<^sub>p s = (0::ureal)}"
    apply (simp only: iterate_tflip_bottom_simp)
  qed 

lemma "flip_loop = H"
  apply (simp add: flip_loop_def H_def)
  apply (simp add: ptwhile_def)
  apply (subst sup_continuous_lfp_iteration)
  apply (metis flip_t flip_t_is_dist is_dist_def is_final_prob_prob rvfun_inverse)
  apply (simp)
  apply (subst rvfun_inverse)
  apply (simp add: is_prob_def iverson_bracket_def)
  using H_is_dist H_def 
  apply (simp add: dist_defs expr_defs, auto)
  apply (simp add: )
  apply (simp add: pseqcomp_def)
  apply (subst rvfun_seqcomp_inverse)
  apply (simp add: flip_is_dist)
  using ureal_is_prob apply blast
  apply (subst rvfun_seqcomp_is_dist)
  apply (simp add: flip_is_dist)
  apply (expr_auto)
  apply (simp add: passigns_def rvfun_assignment_inverse rvfun_assignment_is_dist)
  apply (simp)
  apply (simp add: pfun_defs)
  apply (simp add: flip_altdef)
  apply (expr_auto)
  apply (subst rvfun_inverse)
  apply (simp add: is_prob_def)
   apply (rel_simp)
  sorry

lemma "H ; ($t\<^sup><)\<^sub>e = "
end