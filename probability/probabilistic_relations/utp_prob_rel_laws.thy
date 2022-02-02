section \<open> Probabilistic relation programming laws \<close>

theory utp_prob_rel_laws
  imports 
    "utp_prob_rel_prog"
begin 

declare [[show_types]]

lemma infsum_singleton: 
  "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if c = v\<^sub>0 then (m::\<real>) else 0)) = m"
  apply (rule infsumI)
  apply (simp add: has_sum_def)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
  apply (rule_tac x = "{c}" in exI)
  by (auto)

lemma infsum_singleton_1: 
  "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if v\<^sub>0 = c then (m::\<real>) else 0)) = m"
  by (smt (verit, del_insts) infsum_cong infsum_singleton)

lemma infsum_mult_singleton_left: 
  "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. ((if v\<^sub>0 = c then (1::\<real>) else 0) * (P v\<^sub>0))) = P c"
  apply (rule infsumI)
  apply (simp add: has_sum_def)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
  apply (rule_tac x = "{c}" in exI)
  apply (auto)
  by (simp add: sum.remove)

lemma infsum_mult_singleton_right: 
  "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. ((P v\<^sub>0) * (if v\<^sub>0 = c then (1::\<real>) else 0))) = P c"
  using infsum_mult_singleton_left
  by (metis (no_types, lifting) infsum_cong mult.commute)

lemma infsum_mult_singleton_left_1: 
  "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. ((if c = v\<^sub>0 then (1::\<real>) else 0) * (P v\<^sub>0))) = P c"
  using infsum_mult_singleton_left
  by (smt (verit) infsum_cong)

lemma infsum_mult_singleton_right_1: 
  "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. ((P v\<^sub>0) * (if c = v\<^sub>0 then (1::\<real>) else 0))) = P c"
  using infsum_mult_singleton_right
  by (smt (verit) infsum_cong)

lemma infsum_mult_singleton_1:
  "(\<Sum>\<^sub>\<infinity>s::'a. 
      (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if c = v\<^sub>0 then 1::\<real> else (0::\<real>)) 
                * (if f v\<^sub>0 = s then 1::\<real> else (0::\<real>)))
   ) = (1::\<real>)"
  apply (rule infsumI)
  apply (simp add: has_sum_def)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
  apply (rule_tac x="{f c}" in exI)
  apply (auto)
  apply (subgoal_tac "(\<Sum>s::'a\<in>Y. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if c = v\<^sub>0 then 1::\<real> else (0::\<real>)) * 
    (if f v\<^sub>0 = s then 1::\<real> else (0::\<real>)))
    = 1")
  apply presburger
  apply (simp add: sum.remove)
  apply (subgoal_tac "(\<Sum>s::'a\<in>Y - {f c}. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if c = v\<^sub>0 then 1::\<real> else (0::\<real>)) * 
    (if f v\<^sub>0 = s then 1::\<real> else (0::\<real>)))
    = 0")
  prefer 2
  apply (subst sum_nonneg_eq_0_iff)
  apply (simp)+
  apply (simp add: infsum_nonneg)
  apply (smt (verit, best) Diff_iff infsum_0 insert_iff mult_not_zero)
  apply (simp)
  apply (rule infsumI)
  apply (simp add: has_sum_def)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
  apply (rule_tac x = "{c}" in exI)
  apply (auto)
  apply (subgoal_tac "(\<Sum>v\<^sub>0::'a\<in>Ya.
        (if c = v\<^sub>0 then 1::\<real> else (0::\<real>)) *
        (if f v\<^sub>0 = f c then 1::\<real> else (0::\<real>))) 
    = 1")
  apply simp
  apply (simp add: sum.remove)
  by (smt (verit, ccfv_SIG) Diff_insert_absorb mk_disjoint_insert mult_cancel_left1 
      sum.not_neutral_contains_not_neutral)

lemma infsum_mult_subset_left: 
  "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. ((if b v\<^sub>0 then (1::\<real>) else 0) * (P v\<^sub>0))) = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a \<in> {v\<^sub>0. b v\<^sub>0}. (P v\<^sub>0))"
  apply (rule infsum_cong_neutral)
  by simp+

term "set_of_prel P"
term "\<lambda>s. (set_of_prel P) s"
term "(case \<s> of (\<sigma>::'a, \<rho>::'a) \<Rightarrow> Pair \<sigma>) (v\<^sub>0::'a)"

theorem prel_left_unit: "II ; P = P"
  apply (simp add: prob_rel_defs expr_defs)
  apply (subst prel_of_set_inverse)
   apply (simp add: dist_defs)
  apply (smt (verit, best) infsum_cong infsum_mult_singleton_left mult_cancel_right1)
  apply (simp add: lens_defs)
  apply (subgoal_tac "\<forall>s. (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a.
           (if (case s of (\<sigma>::'a, \<rho>::'a) \<Rightarrow> Pair \<sigma>) v\<^sub>0 \<in> II then 1::\<real> else (0::\<real>)) *
           set_of_prel P ((case s of (\<sigma>::'a, \<rho>::'a) \<Rightarrow> \<lambda>u::'a. (u, \<rho>)) v\<^sub>0)) = (set_of_prel P) s")
  apply (subgoal_tac "prel_of_set (\<lambda>\<s>::'a \<times> 'a.
         \<Sum>\<^sub>\<infinity>v\<^sub>0::'a.
           (if (case \<s> of (\<sigma>::'a, \<rho>::'a) \<Rightarrow> Pair \<sigma>) v\<^sub>0 \<in> II then 1::\<real> else (0::\<real>)) *
           set_of_prel P ((case \<s> of (\<sigma>::'a, \<rho>::'a) \<Rightarrow> \<lambda>u::'a. (u, \<rho>)) v\<^sub>0)) =
    prel_of_set (set_of_prel P)")
  using set_of_prel_inverse apply auto[1]
   apply presburger
  apply (auto)
  by (simp add: infsum_mult_singleton_left_1)

theorem prel_right_unit: "P ; II = P"
  apply (simp add: prob_rel_defs expr_defs)
  apply (subst prel_of_set_inverse)
  apply (simp add: dist_defs)
  apply (smt (verit, best) infsum_cong infsum_mult_singleton_left mult_cancel_right1)
  apply (simp add: lens_defs)
  apply (subgoal_tac "\<forall>s. (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a.
           set_of_prel P ((case s of (\<sigma>::'a, \<rho>::'a) \<Rightarrow> Pair \<sigma>) v\<^sub>0) *
           (if (case s of (\<sigma>::'a, \<rho>::'a) \<Rightarrow> \<lambda>u::'a. (u, \<rho>)) v\<^sub>0 \<in> II then 1::\<real> else (0::\<real>))) 
        = (set_of_prel P) s")
  apply (subgoal_tac "(\<lambda>s::'a \<times> 'a.
         \<Sum>\<^sub>\<infinity>v\<^sub>0::'a.
           set_of_prel P ((case s of (\<sigma>::'a, \<rho>::'a) \<Rightarrow> Pair \<sigma>) v\<^sub>0) *
           (if (case s of (\<sigma>::'a, \<rho>::'a) \<Rightarrow> \<lambda>u::'a. (u, \<rho>)) v\<^sub>0 \<in> II then 1::\<real> else (0::\<real>))) =
        (set_of_prel P)")
  using set_of_prel_inverse apply auto[1]
   apply presburger
  apply (auto)
  using infsum_mult_singleton_right by metis

term "(x := e) :: 's phrel"                                                                                                                                           
term "prel_of_set (\<lbrakk> x\<^sup>> = e \<rbrakk>\<^sub>\<I>\<^sub>e)"
term "prel_of_set (\<lbrakk> \<lbrakk>\<langle>[x \<leadsto> e]\<rangle>\<^sub>a\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"
term "prel_of_set (\<lbrakk> \<lbrakk>((y := f)::'a rel)\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"
term "((x := e):: 's phrel) = prel_of_set (\<lbrakk> \<lbrakk>x := e\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"
lemma passign_simp: "(x := e) = prel_of_set (\<lbrakk> \<lbrakk>x := e\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"
  by (simp add: prob_rel_defs expr_defs)

term "(x := e) \<Zcomp> (y := f)"  

lemma prel_assign_is_prob: "is_prob (\<lbrakk> \<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"
  by (simp add: prob_rel_defs expr_defs dist_defs)

(*
lemma "is_prob ( set_of_prel ((x := e) ; (y := f)))"
  apply (simp add: prob_rel_defs)
  apply (subst prel_of_set_inverse)
   apply (subst prel_of_set_inverse)
   apply (simp add: dist_defs expr_defs)
   apply (subst prel_of_set_inverse)
    apply (simp add: dist_defs expr_defs)
  apply (simp add: dist_defs expr_defs)
*)
  
lemma passign_comp: 
  (* assumes "$x \<sharp> f" "x \<bowtie> y" *)
  shows "(x := e) ; (y := f) = prel_of_set (\<lbrakk> \<lbrakk>(x := e) \<Zcomp> (y := f)\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"
    apply (simp add: prob_rel_defs expr_defs)
    apply (subst prel_of_set_inverse)
   apply (simp add: dist_defs)
   apply (rel_auto)
   apply (simp add: infsum_singleton)
    apply (subst prel_of_set_inverse)
   apply (simp add: dist_defs)
  apply (rel_auto)
   apply (simp add: infsum_singleton)
    apply (subst prel_of_set_inject)
    (* Left is_prob *)
    apply (simp add: dist_defs expr_defs)
    apply (auto)
    apply (simp add: infsum_nonneg)
    apply (rel_auto)
     apply (subgoal_tac "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if put\<^bsub>x\<^esub> s\<^sub>1 (e s\<^sub>1) = v\<^sub>0 then 1::\<real> else (0::\<real>)) * 
      (if put\<^bsub>y\<^esub> v\<^sub>0 (f v\<^sub>0) = s then 1::\<real> else (0::\<real>))) 
      = (if put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> s\<^sub>1 (e s\<^sub>1)) (f (put\<^bsub>x\<^esub> s\<^sub>1 (e s\<^sub>1))) = s then 1 else 0)")
    apply (simp)
    apply (rule infsumI)
    apply (simp add: has_sum_def)
    apply (auto)
    apply (subst topological_tendstoI)
    apply (auto)
    apply (simp add: eventually_finite_subsets_at_top)
    apply (rule_tac x = "{put\<^bsub>x\<^esub> s\<^sub>1 (e s\<^sub>1)}" in exI)
    apply (auto)
    apply (subgoal_tac "(\<Sum>v\<^sub>0::'a\<in>Y.
        (if put\<^bsub>x\<^esub> s\<^sub>1 (e s\<^sub>1) = v\<^sub>0 then 1::\<real> else (0::\<real>)) *
        (if put\<^bsub>y\<^esub> v\<^sub>0 (f v\<^sub>0) = put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> s\<^sub>1 (e s\<^sub>1)) (f (put\<^bsub>x\<^esub> s\<^sub>1 (e s\<^sub>1))) then 1::\<real> else (0::\<real>))) 
      = 1")
    apply presburger
    apply (simp add: sum.remove)
    apply (subst sum_nonneg_eq_0_iff)
    apply (simp)+
    apply force
    (* *)
    apply (subst topological_tendstoI)
    apply (auto)
    apply (simp add: eventually_finite_subsets_at_top)
    apply (rule_tac x = "{put\<^bsub>x\<^esub> s\<^sub>1 (e s\<^sub>1)}" in exI)
    apply (auto)
    apply (subgoal_tac "(\<Sum>v\<^sub>0::'a\<in>Y. (if put\<^bsub>x\<^esub> s\<^sub>1 (e s\<^sub>1) = v\<^sub>0 then 1::\<real> else (0::\<real>)) * 
        (if put\<^bsub>y\<^esub> v\<^sub>0 (f v\<^sub>0) = s then 1::\<real> else (0::\<real>))) 
      = 0")
    apply presburger
    apply (simp add: sum.remove)
    apply (subst sum_nonneg_eq_0_iff)
       apply (simp)+
    (* *)
    apply (rel_auto)
    using infsum_mult_singleton_1 apply fastforce
    
    (* Right is_dist *)
    apply (simp add: dist_defs expr_defs)
     apply (rel_auto)
     apply (simp add: infsum_singleton)

    (* *)
    apply (rel_auto)
    apply (subst infsum_mult_singleton_left_1)
    apply simp
    by (smt (verit, best) infsum_0 mult_cancel_left1 mult_cancel_right1)

lemma prel_is_dist: "\<forall>s\<^sub>1::'s\<^sub>1. is_dist ((curry (set_of_prel Q)) s\<^sub>1)"
  using set_of_prel by force

lemma prel_is_prob: "\<forall>s\<^sub>1::'s\<^sub>1. is_prob ((curry (set_of_prel Q)) s\<^sub>1)"
  by (meson is_dist_def prel_is_dist)

lemma prel_in_0_1: "(curry (set_of_prel Q)) x y \<ge> 0 \<and> (curry (set_of_prel Q)) x y \<le> 1"
  using prel_is_prob 
  by (smt (verit) SEXP_def is_prob_def taut_def)

lemma prel_in_0_1': "(set_of_prel Q) s \<ge> 0 \<and> (set_of_prel Q) s \<le> 1"
  using prel_in_0_1 curry_conv
  by (metis case_prod_curry split_def)

lemma prel_sum_1: "(\<Sum>\<^sub>\<infinity>s::'a. set_of_prel P (s\<^sub>1, s)) = (1::\<real>)"
  using prel_is_dist
  by (metis (mono_tags, lifting) curry_def infsum_cong is_dist_def is_sum_1_def)

lemma prel_summable: "(\<lambda>x::'a. set_of_prel P (s\<^sub>1, x)) summable_on UNIV"
proof (rule ccontr)
  assume a1: "\<not> (\<lambda>x::'a. set_of_prel P (s\<^sub>1, x)) summable_on UNIV"
  from a1 have "(\<Sum>\<^sub>\<infinity>s::'a. set_of_prel P (s\<^sub>1, s)) = (0::\<real>)"
    by (simp add: infsum_def)
  then show "False"
    by (simp add: prel_sum_1)
qed

lemma real_space_complete: "complete (UNIV::real set)"
  by (simp add: complete_def convergentD real_Cauchy_convergent)

lemma prel_summable_on_subset:
  shows "(\<lambda>x::'a. set_of_prel P (s\<^sub>1, x)) summable_on A"
  apply (rule summable_on_subset[where A="UNIV" and B = "A"])
  apply (simp add: real_space_complete)
  apply simp
  apply (simp add: prel_summable)
  by simp

lemma infsum_mult_subset_summable:
  shows "(\<lambda>v\<^sub>0. (if b v\<^sub>0 then (1::\<real>) else 0) * (set_of_prel P (s\<^sub>1, v\<^sub>0))) summable_on UNIV"
  apply (subgoal_tac "(\<lambda>v\<^sub>0. (if b v\<^sub>0 then (1::\<real>) else 0) * (set_of_prel P (s\<^sub>1, v\<^sub>0))) summable_on UNIV
    \<longleftrightarrow> (\<lambda>x::'a. set_of_prel P (s\<^sub>1, x)) summable_on {x. b x}")
  apply (simp add: prel_summable_on_subset)
  apply (rule summable_on_cong_neutral)
  by simp+


lemma prel_infsum_infsum_mult_singleton_1:
  "(\<Sum>\<^sub>\<infinity>s::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if c = v\<^sub>0 then 1::\<real> else (0::\<real>)) * set_of_prel P (v\<^sub>0, s)) = (1::\<real>)"
  apply (subst infsum_mult_singleton_left_1)
  by (simp add: prel_sum_1)

(*
lemma "(\<Sum>\<^sub>\<infinity>s. r (s\<^sub>1, s) * set_of_prel P (s\<^sub>1, s) + ((1::\<real>) - r (s\<^sub>1, s)) * set_of_prel Q (s\<^sub>1, s))
  = ((\<Sum>\<^sub>\<infinity>s. r (s\<^sub>1, s) * ( set_of_prel P (s\<^sub>1, s) - set_of_prel Q (s\<^sub>1, s))) + (\<Sum>\<^sub>\<infinity>s. set_of_prel Q (s\<^sub>1, s)))"
proof -
  have "(\<Sum>\<^sub>\<infinity>s. r (s\<^sub>1, s) * set_of_prel P (s\<^sub>1, s) + ((1::\<real>) - r (s\<^sub>1, s)) * set_of_prel Q (s\<^sub>1, s)) 
    = (\<Sum>\<^sub>\<infinity>s. set_of_prel Q (s\<^sub>1, s) + r (s\<^sub>1, s) * (set_of_prel P (s\<^sub>1, s) - set_of_prel Q (s\<^sub>1, s)))"
    apply (rule infsum_cong)
    by (smt (verit, ccfv_SIG) distrib_right mult_cancel_right1 right_diff_distrib)
  also have "... = (\<Sum>\<^sub>\<infinity>s. set_of_prel Q (s\<^sub>1, s)) + (\<Sum>\<^sub>\<infinity>s. r (s\<^sub>1, s) * (set_of_prel P (s\<^sub>1, s) - set_of_prel Q (s\<^sub>1, s)))"
    apply (rule infsum_add)
     apply (simp add: prel_summable)
    sorry
  also have "... = 1 + (\<Sum>\<^sub>\<infinity>s. r (s\<^sub>1, s) * (set_of_prel P (s\<^sub>1, s) - set_of_prel Q (s\<^sub>1, s)))"
    by (simp add: prel_sum_1)
qed

lemma prel_prob_choice_is_dist:
  assumes "\<forall>s. 0 \<le> r s \<and> r s \<le> 1"
  shows "(\<Sum>\<^sub>\<infinity>s::'a. r (s\<^sub>1, s) * set_of_prel P (s\<^sub>1, s) + 
          ((1::\<real>) - r (s\<^sub>1, s)) * set_of_prel Q (s\<^sub>1, s)) = (1::\<real>)"
  apply (rule infsumI)
  apply (simp add: has_sum_def)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
  oops
*)

lemma prel_prob_choice_is_sum_1:
  assumes "0 \<le> r \<and> r \<le> 1"
  shows "(\<Sum>\<^sub>\<infinity>s::'a. r * set_of_prel P (s\<^sub>1, s) + 
          ((1::\<real>) - r ) * set_of_prel Q (s\<^sub>1, s)) = (1::\<real>)"
proof -
  have f1: "(\<Sum>\<^sub>\<infinity>s::'a. r  * set_of_prel P (s\<^sub>1, s) + 
          ((1::\<real>) - r ) * set_of_prel Q (s\<^sub>1, s)) = 
    (\<Sum>\<^sub>\<infinity>s::'a. r * set_of_prel P (s\<^sub>1, s)) + 
          (\<Sum>\<^sub>\<infinity>s::'a. ((1::\<real>) - r ) * set_of_prel Q (s\<^sub>1, s))"
      apply (rule infsum_add)
      using assms by (simp add: prel_summable summable_on_cmult_right)+
  also have f2: "... = r * (\<Sum>\<^sub>\<infinity>s::'a. set_of_prel P (s\<^sub>1, s)) + 
          (1 - r) * (\<Sum>\<^sub>\<infinity>s::'a. set_of_prel Q (s\<^sub>1, s))"
      apply (subst infsum_cmult_right)
      apply (simp add: prel_summable)
      apply (subst infsum_cmult_right)
      apply (simp add: prel_summable)
      by simp
  then show ?thesis
    by (simp add: f1 prel_sum_1)
qed

theorem prel_left_one_point: "x := e ; P = prel_of_set (([ x\<^sup>< \<leadsto> e\<^sup>< ] \<dagger> @(set_of_prel P)))\<^sub>e"
  apply (simp add: prob_rel_defs expr_defs)
  apply (subst prel_of_set_inverse)

  apply (simp add: dist_defs expr_defs)
  apply (rel_auto)
   apply (simp add: infsum_singleton)

  apply (subst prel_of_set_inject)
  apply (simp add: dist_defs expr_defs)
  apply (rel_auto)
  apply (simp add: infsum_nonneg prel_in_0_1')
  apply (simp add: infsum_mult_singleton_left_1 prel_in_0_1')
  apply (simp add: prel_infsum_infsum_mult_singleton_1)
  apply (simp add: dist_defs expr_defs)
  apply (auto)
  using prel_in_0_1' apply blast+
  apply (simp add: lens_defs)
  apply (simp add: prel_sum_1)
  apply (rel_auto)
  by (simp add: infsum_mult_singleton_left_1)

theorem prel_right_one_point: "P ; x := e = prel_of_set (([ x\<^sup>> \<leadsto> e\<^sup>> ] \<dagger> @(set_of_prel P)))\<^sub>e"
  apply (simp add: prob_rel_defs expr_defs)
  apply (subst prel_of_set_inverse)

  apply (simp add: dist_defs expr_defs)
  apply (rel_auto)
   apply (simp add: infsum_singleton)

  apply (subst prel_of_set_inject)
  apply (simp add: dist_defs expr_defs)
  apply (rel_auto)
      apply (simp add: infsum_nonneg prel_in_0_1')
  apply (subgoal_tac "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. set_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) \<le> 
    (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. set_of_prel P (s\<^sub>1, v\<^sub>0))")
  apply (simp add: prel_sum_1)
     apply (rule infsum_mono)
  defer
       apply (simp add: prel_summable)
  apply (simp add: prel_in_0_1')
  apply (subgoal_tac "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. set_of_prel P (s\<^sub>1, v\<^sub>0) * 
    (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) = 1")
  apply simp
     apply (rule infsumI)
    apply (simp add: has_sum_def)
    apply (auto)
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

(* In order to prove this law, we need to restrict P Q to distributions *)
(*
lemma passign_pif_simp:
  assumes "\<forall>s. 0 \<le> r s \<and> r s \<le> 1"
  shows "(x := c) ; (if\<^sub>p (r) then P else Q) = 
    prel_of_set (r * ([ x\<^sup>> \<leadsto> c\<^sup>> ] \<dagger> @(set_of_prel P)) +  (1-r) * ([ x\<^sup>> \<leadsto> c\<^sup>> ] \<dagger> @(set_of_prel Q)))\<^sub>e"
  apply (simp add: prob_rel_defs expr_defs)
  apply (subst prel_of_set_inverse)
   apply (simp add: dist_defs expr_defs)
  apply (rel_auto)
  apply (simp add: infsum_singleton)
  apply (subst prel_of_set_inverse)
   apply (simp add: dist_defs expr_defs)
   apply (auto)
     apply (simp add: assms prel_in_0_1')
  apply (simp add: assms convex_bound_le prel_in_0_1')
  apply (subst prel_of_set_inject)
    apply (simp add: dist_defs expr_defs)
    apply (auto)
     apply (simp add: assms infsum_nonneg set_of_prel_in_0_1)
  apply (rel_auto)
  apply (subgoal_tac "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a.
          (if put\<^bsub>x\<^esub> a (c a) = v\<^sub>0 then 1::\<real> else (0::\<real>)) *
          (r (v\<^sub>0, b) * set_of_prel P (v\<^sub>0, b) + ((1::\<real>) - r (v\<^sub>0, b)) * set_of_prel Q (v\<^sub>0, b))) = 1")
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
          (r (v\<^sub>0, b) * set_of_prel P (v\<^sub>0, b) + ((1::\<real>) - r (v\<^sub>0, b)) * set_of_prel Q (v\<^sub>0, b))) 
      = 1")
    apply presburger
    apply (simp add: sum.remove)
    apply (subgoal_tac "(\<Sum>v\<^sub>0::'a\<in>Y - {put\<^bsub>x\<^esub> a (c a)}.
          (if put\<^bsub>x\<^esub> a (c a) = v\<^sub>0 then 1::\<real> else (0::\<real>)) *
          (r (v\<^sub>0, b) * set_of_prel P (v\<^sub>0, b) + ((1::\<real>) - r (v\<^sub>0, b)) * set_of_prel Q (v\<^sub>0, b))) = 0")
    apply (subgoal_tac "r (put\<^bsub>x\<^esub> a (c a), b) * set_of_prel P (put\<^bsub>x\<^esub> a (c a), b) + 
      ((1::\<real>) - r (put\<^bsub>x\<^esub> a (c a), b)) * set_of_prel Q (put\<^bsub>x\<^esub> a (c a), b) = 1") 
    defer
    apply (smt (verit) DiffE mult_eq_0_iff singleton_iff sum.not_neutral_contains_not_neutral)
*)

end
