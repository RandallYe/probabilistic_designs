section \<open> Example of probabilistic relation programming: cancer diagnosis \<close>

theory utp_prob_rel_cancer_diagnosis
  imports 
    "UTP_prob_relations.utp_prob_rel_lattice_laws" 
begin 

unbundle UTP_Syntax

declare [[show_types]]

datatype LabTest = Pos | Neg

alphabet state = 
  c :: bool
  lt :: LabTest

(*
definition Init :: "ureal \<Rightarrow> ureal \<Rightarrow> ureal \<Rightarrow> state prhfun" where
"Init p\<^sub>1 p\<^sub>2 p\<^sub>3 = (if\<^sub>p p\<^sub>1 then (c := True) else (c := False)) ; 
       (if\<^sub>c (c\<^sup><) then 
          (if\<^sub>p p\<^sub>2 then (lt := Pos) else (lt := Neg)) 
        else 
          (if\<^sub>p p\<^sub>3 then (lt := Pos) else (lt := Neg))
  )"

definition T:: "state prhfun \<Rightarrow> state prhfun \<Rightarrow> state prhfun \<Rightarrow> state prhfun" where
"T p\<^sub>1 p\<^sub>2 p\<^sub>3 \<equiv> (Init p\<^sub>1 p\<^sub>2 p\<^sub>3) \<parallel> ((lt := Pos)::state prhfun)"

definition FirstTest:: "state prhfun \<Rightarrow> state prhfun \<Rightarrow> state prhfun \<Rightarrow> state prhfun" where
"FirstTest p\<^sub>1 p\<^sub>2 p\<^sub>3 \<equiv> (Init p\<^sub>1 p\<^sub>2 p\<^sub>3) \<parallel> \<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e"

lemma 
  assumes "p\<^sub>1 = 0.002" "p\<^sub>2 = 0.86" "p\<^sub>3 = 0.05"
  shows "Init p\<^sub>1 p\<^sub>2 p\<^sub>3 = (\<lbrakk>lt\<^sup>> = Pos \<and> c\<^sup>> = True\<rbrakk>\<^sub>\<I>\<^sub>e * 0.002 * 0.86)\<^sub>e"
*)


abbreviation "p\<^sub>1 \<equiv> 0.002"
abbreviation "p\<^sub>2 \<equiv> 0.89"
abbreviation "p\<^sub>3 \<equiv> 0.05"

definition TestRel :: "state prhfun" where
" TestRel = (if\<^sub>c (c\<^sup><) then 
    (if\<^sub>p p\<^sub>2 then (lt := Pos) else (lt := Neg)) 
  else 
    (if\<^sub>p p\<^sub>3 then (lt := Pos) else (lt := Neg))
  )
"

definition Init :: "state prhfun" where
"Init = 
  (if\<^sub>p p\<^sub>1 then (c := True) else (c := False)) ; 
  TestRel
"

lemma TestRel_simp: 
  "TestRel = prfun_of_rvfun (
    (\<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * p\<^sub>2) + 
    (\<lbrakk>lt\<^sup>> = Neg\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e *(1-p\<^sub>2)) + 
    (\<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>\<not>c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e *p\<^sub>3) + 
    (\<lbrakk>lt\<^sup>> = Neg\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>\<not>c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e *(1-p\<^sub>3)))\<^sub>e"
  apply (simp only: TestRel_def)
  apply (simp add: prfun_seqcomp_right_unit)
  apply (simp add: prfun_pcond_altdef)
  apply (simp only: pchoice_def passigns_def)
  apply (simp only: rvfun_assignment_inverse)
  apply (simp only: rvfun_of_prfun_const)
  apply (subst rvfun_pchoice_inverse_c''')
  apply (simp add: rvfun_assignment_is_prob)
  apply (simp add: rvfun_assignment_is_prob)
  apply (simp)
  apply (subst rvfun_pchoice_inverse_c''')
  apply (simp add: rvfun_assignment_is_prob)
  apply (simp add: rvfun_assignment_is_prob)
  apply (simp)
  apply (expr_simp_1 add: rel)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (subst fun_eq_iff)
  by (pred_simp)

lemma 
  shows "Init = prfun_of_rvfun (
    (\<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * p\<^sub>1 * p\<^sub>2) + 
    (\<lbrakk>lt\<^sup>> = Neg\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * p\<^sub>1 * (1-p\<^sub>2)) + 
    (\<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>\<not>c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * (1-p\<^sub>1) * p\<^sub>2) + 
    (\<lbrakk>lt\<^sup>> = Neg\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>\<not>c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * (1-p\<^sub>1) * (1-p\<^sub>2))
)\<^sub>e"
  (* apply (simp only: Init_def)
  apply (simp add: TestRel_simp)
  apply (simp only: pseqcomp_def)
  *)

  apply (simp only: Init_def TestRel_def)
  apply (simp only: pcond_def)
  apply (simp only: pseqcomp_def)
(*
  apply (subst rvfun_pcond_inverse)
  using ureal_is_prob apply blast+
  apply (subst prfun_pchoice_assigns_inverse_c')+
  apply (expr_simp_1)
*)

(*
  apply (subst prfun_pchoice_altdef)+
  apply (subst rvfun_pchoice_inverse)
  using ureal_is_prob apply blast+
  apply (subst rvfun_pchoice_inverse)
  using ureal_is_prob apply blast+
  apply (subst rvfun_pchoice_inverse)
  using ureal_is_prob apply blast+
  apply (simp add: dist_defs expr_defs lens_defs ureal_defs)
  apply (pred_auto)
  apply (subst prfun_pchoice_assigns_inverse_c')+
*)
(*
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (simp add: dist_defs expr_defs ureal_defs)
  apply (subst fun_eq_iff)
  apply (pred_auto)
*)
  apply (subst prfun_pchoice_altdef)+
  apply (simp add: prfun_pcond_altdef)
  apply (subst rvfun_pchoice_inverse)
  using ureal_is_prob apply blast+
  apply (subst rvfun_pchoice_inverse)
  using ureal_is_prob apply blast+
  apply (simp add: pseqcomp_def)
  apply (subst rvfun_pchoice_inverse)
  using ureal_is_prob apply blast+

  apply (subst rvfun_inverse)
  apply (expr_simp_1 add: ureal_defs is_prob_def)
  apply (pred_auto)
  apply (subst real2uereal_inverse')
  apply simp+
  apply (subst real2uereal_inverse')
  apply simp+

  apply (simp add: pfun_defs)

end
