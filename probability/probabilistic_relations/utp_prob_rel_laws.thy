section \<open> Probabilistic relation programming laws \<close>

theory utp_prob_rel_laws
  imports 
    "utp_prob_rel_prog"
begin 

declare [[show_types]]

lemma infsum_mult_singleton_eq: 
  "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. ((if v\<^sub>0 = c then (1::\<real>) else 0) * (P v\<^sub>0))) = P c"
  apply (rule infsumI)
  apply (simp add: has_sum_def)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
  apply (rule_tac x = "{c}" in exI)
  apply (auto)
  by (simp add: sum.remove)

lemma infsum_mult_singleton_eq_1: 
  "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. ((if c = v\<^sub>0 then (1::\<real>) else 0) * (P v\<^sub>0))) = P c"
  using infsum_mult_singleton_eq
  by (smt (verit) infsum_cong)

lemma infsum_mult_singleton_eq_2: 
  "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. ((P v\<^sub>0) * (if v\<^sub>0 = c then (1::\<real>) else 0))) = P c"
  by (metis (no_types, lifting) infsum_cong infsum_mult_singleton_eq mult.commute)

term "set_of_prel P"
term "\<lambda>s. (set_of_prel P) s"
term "(case \<s> of (\<sigma>::'a, \<rho>::'a) \<Rightarrow> Pair \<sigma>) (v\<^sub>0::'a)"

lemma prel_left_unit: "II ; P = P"
  apply (simp add: prob_rel_defs expr_defs)
  apply (subst prel_of_set_inverse)
   apply (simp add: is_prob_def)
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
  using infsum_mult_singleton_eq_1 by metis

lemma prel_right_unit: "P ; II = P"
  apply (simp add: prob_rel_defs expr_defs)
  apply (subst prel_of_set_inverse)
   apply (simp add: is_prob_def)
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
  using infsum_mult_singleton_eq_2 by metis

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
    apply (simp add: is_prob_def)
    apply (subst prel_of_set_inverse)
    apply (simp add: is_prob_def)
    apply (subst prel_of_set_inject)
    (* Left is_prob *)
    apply (simp add: dist_defs expr_defs)
    apply (auto)
    apply (simp add: infsum_nonneg)
    apply (rel_auto)
    apply (subgoal_tac "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if put\<^bsub>x\<^esub> a (e a) = v\<^sub>0 then 1::\<real> else (0::\<real>)) * 
        (if put\<^bsub>y\<^esub> v\<^sub>0 (f v\<^sub>0) = b then 1::\<real> else (0::\<real>))) 
      = (if put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> a (e a)) (f (put\<^bsub>x\<^esub> a (e a))) = b then 1 else 0)")
    apply (simp)
    apply (rule infsumI)
    apply (simp add: has_sum_def)
    apply (auto)
    apply (subst topological_tendstoI)
    apply (auto)
    apply (simp add: eventually_finite_subsets_at_top)
    apply (rule_tac x = "{put\<^bsub>x\<^esub> a (e a)}" in exI)
    apply (auto)
    apply (subgoal_tac "(\<Sum>v\<^sub>0::'a\<in>Y.
        (if put\<^bsub>x\<^esub> a (e a) = v\<^sub>0 then 1::\<real> else (0::\<real>)) *
        (if put\<^bsub>y\<^esub> v\<^sub>0 (f v\<^sub>0) = put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> a (e a)) (f (put\<^bsub>x\<^esub> a (e a))) then 1::\<real> else (0::\<real>))) 
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
    apply (rule_tac x = "{put\<^bsub>x\<^esub> a (e a)}" in exI)
    apply (auto)
    apply (subgoal_tac "(\<Sum>v\<^sub>0::'a\<in>Y. (if put\<^bsub>x\<^esub> a (e a) = v\<^sub>0 then 1::\<real> else (0::\<real>)) * 
        (if put\<^bsub>y\<^esub> v\<^sub>0 (f v\<^sub>0) = b then 1::\<real> else (0::\<real>))) 
      = 0")
    apply presburger
    apply (simp add: sum.remove)
    apply (subst sum_nonneg_eq_0_iff)
    apply (simp)+
    
    (* Right is_prob *)
    apply (simp add: is_prob_def)
    apply (rel_auto)
    apply (rule infsumI)
    apply (simp add: has_sum_def)
    apply (subst topological_tendstoI)
    apply (auto)
    apply (simp add: eventually_finite_subsets_at_top)
    apply (rule_tac x = "{put\<^bsub>x\<^esub> a (e a)}" in exI)
    apply (auto)
    apply (subgoal_tac "(\<Sum>v\<^sub>0::'a\<in>Y.
        (if put\<^bsub>x\<^esub> a (e a) = v\<^sub>0 then 1::\<real> else (0::\<real>)) *
        (if put\<^bsub>y\<^esub> v\<^sub>0 (f v\<^sub>0) = put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> a (e a)) (f (put\<^bsub>x\<^esub> a (e a))) then 1::\<real> else (0::\<real>))) 
      = 1")
    apply presburger
    apply (simp add: sum.remove)
    apply (subst sum_nonneg_eq_0_iff)
    apply (simp)+
    apply force
    (* *)
    apply (rule infsumI)
    apply (simp add: has_sum_def)
    apply (subst topological_tendstoI)
    apply (auto)
    apply (simp add: eventually_finite_subsets_at_top)
    apply (rule_tac x = "{put\<^bsub>x\<^esub> a (e a)}" in exI)
    apply (auto)
    apply (subgoal_tac "(\<Sum>v\<^sub>0::'a\<in>Y. (if put\<^bsub>x\<^esub> a (e a) = v\<^sub>0 then 1::\<real> else (0::\<real>)) * 
        (if put\<^bsub>y\<^esub> v\<^sub>0 (f v\<^sub>0) = b then 1::\<real> else (0::\<real>))) 
      = 0")
    apply presburger
    apply (simp add: sum.remove)
    apply (subst sum_nonneg_eq_0_iff)
    by (simp)+


end
