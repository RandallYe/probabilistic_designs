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

definition TestRel_altdef :: "state rvhfun" where
"TestRel_altdef = (
    (\<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * p\<^sub>2) + 
    (\<lbrakk>lt\<^sup>> = Neg\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e *(1-p\<^sub>2)) + 
    (\<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>\<not>c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e *p\<^sub>3) + 
    (\<lbrakk>lt\<^sup>> = Neg\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>\<not>c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e *(1-p\<^sub>3)))\<^sub>e"

lemma TestRel_simp: 
  "TestRel = prfun_of_rvfun TestRel_altdef"
  apply (simp only: TestRel_def TestRel_altdef_def)
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

lemma TestRel_altdef_final: "is_final_distribution TestRel_altdef"
  apply (simp add: dist_defs expr_defs TestRel_altdef_def)
  apply (pred_auto)
proof -
  fix c
  have pos_false: "{s::state. lt\<^sub>v s = Pos \<and> \<not> c\<^sub>v s} = {\<lparr>c\<^sub>v = False,lt\<^sub>v = Pos\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
    by simp+
  have neg_false: "{s::state. lt\<^sub>v s = Neg \<and> \<not> c\<^sub>v s} = {\<lparr>c\<^sub>v = False,lt\<^sub>v = Neg\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
    by simp+
  have summable_pos_false: "(\<lambda>x::state. if lt\<^sub>v x = Pos \<and> \<not> c\<^sub>v x then 1::\<real> else (0::\<real>)) summable_on UNIV"
    apply (rule infsum_constant_finite_states_summable)
    by (simp add: pos_false)
  have summable_neg_false: "(\<lambda>x::state. if lt\<^sub>v x = Neg \<and> \<not> c\<^sub>v x then 1::\<real> else (0::\<real>)) summable_on UNIV"
    apply (rule infsum_constant_finite_states_summable)
    by (simp add: neg_false)
  have "(\<Sum>\<^sub>\<infinity>s::state.
          (if lt\<^sub>v s = Pos then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v s then 1::\<real> else (0::\<real>)) / (20::\<real>) +
          (if lt\<^sub>v s = Neg then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v s then 1::\<real> else (0::\<real>)) * (19::\<real>) / (20::\<real>)) =
       (\<Sum>\<^sub>\<infinity>s::state.
          (if lt\<^sub>v s = Pos \<and> \<not> c\<^sub>v s then 1::\<real> else (0::\<real>)) / (20::\<real>) +
          (if lt\<^sub>v s = Neg \<and> \<not> c\<^sub>v s then 1::\<real> else (0::\<real>)) * (19::\<real>) / (20::\<real>))"
    by (smt (verit, ccfv_SIG) infsum_cong mult_cancel_right1 mult_eq_0_iff)
  also have "... = (\<Sum>\<^sub>\<infinity>s::state. (if lt\<^sub>v s = Pos \<and> \<not> c\<^sub>v s then 1::\<real> else (0::\<real>)) / (20::\<real>)) +
          (\<Sum>\<^sub>\<infinity>s::state. (if lt\<^sub>v s = Neg \<and> \<not> c\<^sub>v s then 1::\<real> else (0::\<real>)) * (19::\<real>) / (20::\<real>))"
    apply (subst infsum_add)
    apply (rule summable_on_cdiv_left)
    using summable_pos_false apply blast
    apply (rule summable_on_cdiv_left)
    apply (rule summable_on_cmult_left)
    using summable_neg_false apply blast
    by simp
  also have "... = 1"
    apply (subst infsum_cdiv_left)
    using summable_pos_false apply blast
    apply (subst infsum_cdiv_left)
    apply (rule summable_on_cmult_left)
    using summable_neg_false apply blast
    apply (subst infsum_constant_finite_states)
     apply (simp add: pos_false)
    apply (subst infsum_cmult_left)
    using summable_neg_false apply blast
    apply (subst infsum_constant_finite_states)
    apply (simp add: neg_false)
    by (simp add: pos_false neg_false)
  then show "(\<Sum>\<^sub>\<infinity>s::state.
          (if lt\<^sub>v s = Pos then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v s then 1::\<real> else (0::\<real>)) / (20::\<real>) +
          (if lt\<^sub>v s = Neg then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v s then 1::\<real> else (0::\<real>)) * (19::\<real>) / (20::\<real>)) =
       (1::\<real>)"
    using calculation by presburger
next
  fix c
  have pos_true: "{s::state. lt\<^sub>v s = Pos \<and> c\<^sub>v s} = {\<lparr>c\<^sub>v = True,lt\<^sub>v = Pos\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
    by simp+
  have neg_true: "{s::state. lt\<^sub>v s = Neg \<and> c\<^sub>v s} = {\<lparr>c\<^sub>v = True,lt\<^sub>v = Neg\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
    by simp+
  have summable_pos_true: "(\<lambda>x::state. if lt\<^sub>v x = Pos \<and> c\<^sub>v x then 1::\<real> else (0::\<real>)) summable_on UNIV"
    apply (rule infsum_constant_finite_states_summable)
    by (simp add: pos_true)
  have summable_neg_true: "(\<lambda>x::state. if lt\<^sub>v x = Neg \<and> c\<^sub>v x then 1::\<real> else (0::\<real>)) summable_on UNIV"
    apply (rule infsum_constant_finite_states_summable)
    by (simp add: neg_true)
  have "(\<Sum>\<^sub>\<infinity>s::state.
          (if lt\<^sub>v s = Pos then 1::\<real> else (0::\<real>)) * (if c\<^sub>v s then 1::\<real> else (0::\<real>)) * (89::\<real>) / (100::\<real>) +
          (if lt\<^sub>v s = Neg then 1::\<real> else (0::\<real>)) * (if c\<^sub>v s then 1::\<real> else (0::\<real>)) * (11::\<real>) / (100::\<real>)) =
       (\<Sum>\<^sub>\<infinity>s::state.
          (if lt\<^sub>v s = Pos \<and> c\<^sub>v s then 1::\<real> else (0::\<real>))* (89::\<real>) / (100::\<real>) +
          (if lt\<^sub>v s = Neg \<and> c\<^sub>v s then 1::\<real> else (0::\<real>)) * (11::\<real>) / (100::\<real>))"
    by (smt (verit, ccfv_SIG) infsum_cong mult_cancel_right1 mult_eq_0_iff)
  also have "... = (\<Sum>\<^sub>\<infinity>s::state. (if lt\<^sub>v s = Pos \<and> c\<^sub>v s then 1::\<real> else (0::\<real>)) * (89::\<real>) / (100::\<real>)) +
          (\<Sum>\<^sub>\<infinity>s::state. (if lt\<^sub>v s = Neg \<and> c\<^sub>v s then 1::\<real> else (0::\<real>)) * (11::\<real>) / (100::\<real>))"
    apply (subst infsum_add)
    apply (rule summable_on_cdiv_left)
    apply (rule summable_on_cmult_left)
    using summable_pos_true apply blast
    apply (rule summable_on_cdiv_left)
    apply (rule summable_on_cmult_left)
    using summable_neg_true apply blast
    by simp
  also have "... = 1"
    apply (subst infsum_cdiv_left)
    apply (rule summable_on_cmult_left)
    using summable_pos_true apply blast
    apply (subst infsum_cdiv_left)
     apply (rule summable_on_cmult_left)
    using summable_neg_true apply blast
    apply (subst infsum_cmult_left)
    using summable_pos_true apply blast
    apply (subst infsum_constant_finite_states)
     apply (simp add: pos_true)
    apply (subst infsum_cmult_left)
    using summable_neg_true apply blast
    apply (subst infsum_constant_finite_states)
    apply (simp add: neg_true)
    by (simp add: pos_true neg_true)

  then show "(\<Sum>\<^sub>\<infinity>s::state.
          (if lt\<^sub>v s = Pos then 1::\<real> else (0::\<real>)) * (if c\<^sub>v s then 1::\<real> else (0::\<real>)) * (89::\<real>) / (100::\<real>) +
          (if lt\<^sub>v s = Neg then 1::\<real> else (0::\<real>)) * (if c\<^sub>v s then 1::\<real> else (0::\<real>)) * (11::\<real>) / (100::\<real>)) =
       (1::\<real>)"
    using calculation by presburger
qed

lemma Init_simp:
  shows "Init = prfun_of_rvfun (
    (\<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * p\<^sub>1 * p\<^sub>2) + 
    (\<lbrakk>lt\<^sup>> = Neg\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * p\<^sub>1 * (1-p\<^sub>2)) + 
    (\<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>\<not>c\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * (1-p\<^sub>1) * p\<^sub>3) + 
    (\<lbrakk>lt\<^sup>> = Neg\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>\<not>c\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * (1-p\<^sub>1) * (1-p\<^sub>3))
)\<^sub>e"
  apply (simp only: Init_def)
  apply (simp add: TestRel_simp)
  apply (simp only: pseqcomp_def)
  apply (subst rvfun_inverse) 
  using TestRel_altdef_final rvfun_prob_sum1_summable'(1) apply blast
  apply (subst prfun_pchoice_assigns_inverse_c')
  apply (simp add: TestRel_altdef_def)
  apply (expr_simp_1)
  apply (simp add: real2eureal_inverse)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (subst fun_eq_iff)
  apply (pred_auto)
proof -
  fix lt c
  let ?f = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if v\<^sub>0 = \<lparr>c\<^sub>v = True, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (500::\<real>) +
           (499::\<real>) * (if v\<^sub>0 = \<lparr>c\<^sub>v = False, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (500::\<real>)) *
          ((if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (89::\<real>) / (100::\<real>) +
           (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) / (20::\<real>)))"
  have "?f = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if v\<^sub>0 = \<lparr>c\<^sub>v = True, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (500::\<real>) +
           (499::\<real>) * (if v\<^sub>0 = \<lparr>c\<^sub>v = False, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (500::\<real>)) *
          ((if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) / (20::\<real>)))"
    by (smt (verit) divide_eq_0_iff infsum_cong mult_eq_0_iff)
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((499::\<real>) * (if v\<^sub>0 = \<lparr>c\<^sub>v = False, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (500::\<real>)) *
          ((if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) / (20::\<real>)))"
    by (simp add: infsum_cong)
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0 \<in> {\<lparr>c\<^sub>v = False, lt\<^sub>v = lt\<rparr>}. ((499::\<real>) / (10000::\<real>)))"
    apply (subst infsum_cong_neutral[where S="UNIV" and T="{\<lparr>c\<^sub>v = False, lt\<^sub>v = lt\<rparr>}" and 
         f = "\<lambda>v\<^sub>0. ((499::\<real>) * (if v\<^sub>0 = \<lparr>c\<^sub>v = False, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (500::\<real>)) *
          ((if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) / (20::\<real>))" and
         g = "\<lambda>v\<^sub>0. ((499::\<real>) / (10000::\<real>))"])
    apply blast
    by simp+
  also have "... = ((499::\<real>) / (10000::\<real>))"
    by simp
  then show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if v\<^sub>0 = \<lparr>c\<^sub>v = True, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (500::\<real>) +
           (499::\<real>) * (if v\<^sub>0 = \<lparr>c\<^sub>v = False, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (500::\<real>)) *
          ((if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (89::\<real>) / (100::\<real>) +
           (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) / (20::\<real>))) *
       (10000::\<real>) = (499::\<real>)"
    using calculation by linarith
next
  fix lt c
  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if v\<^sub>0 = \<lparr>c\<^sub>v = True, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (500::\<real>) +
           (499::\<real>) * (if v\<^sub>0 = \<lparr>c\<^sub>v = False, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (500::\<real>)) *
          ((if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (89::\<real>) / (100::\<real>) +
           (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) / (20::\<real>)))
    = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state. ((if v\<^sub>0 = \<lparr>c\<^sub>v = True, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) * (89::\<real>) / (50000::\<real>)))"
    apply (subst infsum_cong[where g = "\<lambda>v\<^sub>0::state. ((if v\<^sub>0 = \<lparr>c\<^sub>v = True, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) * (89::\<real>) / (50000::\<real>))"])
    by auto
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state\<in>{\<lparr>c\<^sub>v = True, lt\<^sub>v = lt\<rparr>}. ((89::\<real>) / (50000::\<real>)))"
    apply (subst infsum_cong_neutral[where S="UNIV" and T="{\<lparr>c\<^sub>v = True, lt\<^sub>v = lt\<rparr>}" and 
         f = "\<lambda>v\<^sub>0. (if v\<^sub>0 = \<lparr>c\<^sub>v = True, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) * (89::\<real>) / (50000::\<real>)" and
         g = "\<lambda>v\<^sub>0. ((89::\<real>) / (50000::\<real>))"])
    by simp+
  then show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if v\<^sub>0 = \<lparr>c\<^sub>v = True, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (500::\<real>) +
           (499::\<real>) * (if v\<^sub>0 = \<lparr>c\<^sub>v = False, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (500::\<real>)) *
          ((if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (89::\<real>) / (100::\<real>) +
           (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) / (20::\<real>))) *
       (50000::\<real>) = (89::\<real>)"
    using calculation by fastforce
next
  fix lt c
  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if v\<^sub>0 = \<lparr>c\<^sub>v = True, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (500::\<real>) +
           (499::\<real>) * (if v\<^sub>0 = \<lparr>c\<^sub>v = False, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (500::\<real>)) *
          ((if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (11::\<real>) / (100::\<real>) +
           (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (19::\<real>) / (20::\<real>))) =
      (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((9481::\<real>) * (if v\<^sub>0 = \<lparr>c\<^sub>v = False, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (10000::\<real>)))"
    apply (subst infsum_cong[where g = "\<lambda>v\<^sub>0::state. ((9481::\<real>) * (if v\<^sub>0 = \<lparr>c\<^sub>v = False, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (10000::\<real>))"])
    by auto
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state\<in>{\<lparr>c\<^sub>v = False, lt\<^sub>v = lt\<rparr>}. ((9481::\<real>) / (10000::\<real>)))"
    apply (subst infsum_cong_neutral[where S="UNIV" and T="{\<lparr>c\<^sub>v = False, lt\<^sub>v = lt\<rparr>}" and 
         f = "\<lambda>v\<^sub>0. ((9481::\<real>) * (if v\<^sub>0 = \<lparr>c\<^sub>v = False, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (10000::\<real>))" and
         g = "\<lambda>v\<^sub>0. ((9481::\<real>) / (10000::\<real>))"])
    by simp+
  then show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
        ((if v\<^sub>0 = \<lparr>c\<^sub>v = True, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (500::\<real>) +
         (499::\<real>) * (if v\<^sub>0 = \<lparr>c\<^sub>v = False, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (500::\<real>)) *
        ((if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (11::\<real>) / (100::\<real>) +
         (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (19::\<real>) / (20::\<real>))) *
     (10000::\<real>) = (9481::\<real>)"
    using calculation by fastforce
next
  fix lt c
  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if v\<^sub>0 = \<lparr>c\<^sub>v = True, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (500::\<real>) +
           (499::\<real>) * (if v\<^sub>0 = \<lparr>c\<^sub>v = False, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (500::\<real>)) *
          ((if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (11::\<real>) / (100::\<real>) +
           (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (19::\<real>) / (20::\<real>)))
      = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state. (if v\<^sub>0 = \<lparr>c\<^sub>v = True, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) *(11::\<real>) / (50000::\<real>))"
    apply (subst infsum_cong[where g = "\<lambda>v\<^sub>0::state. (if v\<^sub>0 = \<lparr>c\<^sub>v = True, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) *(11::\<real>) / (50000::\<real>)"])
    by auto
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state\<in>{\<lparr>c\<^sub>v = True, lt\<^sub>v = lt\<rparr>}. ((11::\<real>) / (50000::\<real>)))"
    apply (subst infsum_cong_neutral[where S="UNIV" and T="{\<lparr>c\<^sub>v = True, lt\<^sub>v = lt\<rparr>}" and 
         f = "\<lambda>v\<^sub>0. (if v\<^sub>0 = \<lparr>c\<^sub>v = True, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) *(11::\<real>) / (50000::\<real>)" and
         g = "\<lambda>v\<^sub>0. ((11::\<real>) / (50000::\<real>))"])
    by simp+
  then show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if v\<^sub>0 = \<lparr>c\<^sub>v = True, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (500::\<real>) +
           (499::\<real>) * (if v\<^sub>0 = \<lparr>c\<^sub>v = False, lt\<^sub>v = lt\<rparr> then 1::\<real> else (0::\<real>)) / (500::\<real>)) *
          ((if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (11::\<real>) / (100::\<real>) +
           (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (19::\<real>) / (20::\<real>))) *
       (50000::\<real>) = (11::\<real>)"
    using calculation by force
qed

(*
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
*)
end
