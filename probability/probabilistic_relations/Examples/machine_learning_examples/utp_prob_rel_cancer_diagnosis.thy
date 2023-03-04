section \<open> Example of probabilistic relation programming: cancer diagnosis \<close>

text \<open> If a randomly selected patient has a lab test for cancer, such as breast cancer, and 
the result is positive. Then what's the probability that the patient has cancer? \<close>

theory utp_prob_rel_cancer_diagnosis
  imports 
    "UTP_prob_relations.utp_prob_rel_lattice_laws" 
begin 

unbundle UTP_Syntax

declare [[show_types]]

datatype LabTest = Pos | Neg

text \<open> @{text "c"}: true for cancer and false for no cancer. \<close>
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

text \<open> The probability of a randomly selected patient has a cancer. It is the base rate or the prior. \<close>
abbreviation "p\<^sub>1 \<equiv> 0.002"
text \<open> The sensitivity of the lab test or the true positive rate. \<close>
abbreviation "p\<^sub>2 \<equiv> 0.89"
text \<open> The false negative rate and the specificity of the lab test or the true negative rate: @{text "1 - p\<^sub>3"}. \<close>
abbreviation "p\<^sub>3 \<equiv> 0.05"

definition TestAction :: "state prhfun" where
" TestAction = (if\<^sub>c (c\<^sup><) then 
    (if\<^sub>p p\<^sub>2 then (lt := Pos) else (lt := Neg))
  else 
    (if\<^sub>p p\<^sub>3 then (lt := Pos) else (lt := Neg))
  )
"

definition TestResultPos :: "state prhfun" where
" TestResultPos = (if\<^sub>c (c\<^sup><) then 
    (if\<^sub>p p\<^sub>2 then (lt := Pos) else (lt := Neg))
  else 
    (if\<^sub>p p\<^sub>3 then (lt := Pos) else (lt := Neg))
  )
"

definition TestAction_altdef :: "state rvhfun" where
"TestAction_altdef = (
    (\<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * p\<^sub>2) + 
    (\<lbrakk>lt\<^sup>> = Neg\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e *(1-p\<^sub>2)) + 
    (\<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>\<not>c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e *p\<^sub>3) + 
    (\<lbrakk>lt\<^sup>> = Neg\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>\<not>c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e *(1-p\<^sub>3))
)\<^sub>e"

(* P(A|B) = P(B|A) * P(A) / P(B) 
here A is "Cancer" and B is "Test is positive"
  P(Cancer | Test=Pos) = P(Test=Pos|Cancer) * P(Cancer) / P(Test=Pos)

where
  P(Cancer) = p\<^sub>1               -- the base rate
  P(Test=Pos|Cancer) = p\<^sub>2 -- sensitivity
  P(Test=Pos)             -- not directly known

Actually,
  P(Test=Pos) 
= P(Test=Pos|Cancer) * P(Cancer) + P(Test=Pos|\<not>Cancer) * P(\<not>Cancer)
= p\<^sub>2 * p\<^sub>1 + (1 - P(Test=Neg|\<not>Cancer)) * (1 - p\<^sub>1)
= p\<^sub>2 * p\<^sub>1 + (1 - (1-p\<^sub>3)) * (1 - p\<^sub>1)
= p\<^sub>2 * p\<^sub>1 + p\<^sub>3 * (1 - p\<^sub>1)

So,
  P(Cancer | Test=Pos) = p\<^sub>2 * p\<^sub>1 / (p\<^sub>2 * p\<^sub>1 + p\<^sub>3 * (1 - p\<^sub>1))
*)
text \<open> Initial knowledge, or prior. \<close>
definition Init :: "state prhfun" where
"Init = (if\<^sub>p p\<^sub>1 then (c := True) else (c := False)) ; TestAction"

definition Init_altdef :: "state rvhfun" where
"Init_altdef = (
    (\<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * p\<^sub>1 * p\<^sub>2) + 
    (\<lbrakk>lt\<^sup>> = Neg\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * p\<^sub>1 * (1 - p\<^sub>2)) + 
    (\<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>\<not>c\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * (1-p\<^sub>1) * p\<^sub>3) + 
    (\<lbrakk>lt\<^sup>> = Neg\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>\<not>c\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * (1-p\<^sub>1) * (1 - p\<^sub>3))
)\<^sub>e"

text \<open> The result of the first lab test is positive. \<close>
definition FirstTest :: "state prhfun" where
"FirstTest = (Init \<parallel> \<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e)"

definition FirstTest_altdef :: "state rvhfun" where
"FirstTest_altdef = (
    ((\<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * p\<^sub>1 * p\<^sub>2) + (\<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>\<not>c\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * (1 - p\<^sub>1) * p\<^sub>3)) / 
    (p\<^sub>1 * p\<^sub>2 + (1 - p\<^sub>1) * p\<^sub>3)
)\<^sub>e"

text \<open> The result of the second lab test (which is independent to the first one) is also positive. \<close>
definition SecondTest :: "state prhfun" where
"SecondTest = ((FirstTest ; TestAction) \<parallel> \<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e)"

definition SecondTest_altdef :: "state rvhfun" where
"SecondTest_altdef = (
    ((\<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * p\<^sub>1 * p\<^sub>2 * p\<^sub>2) + (\<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>\<not>c\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * (1 - p\<^sub>1) * p\<^sub>3 * p\<^sub>3)) / 
    (p\<^sub>1 * p\<^sub>2 * p\<^sub>2 + (1 - p\<^sub>1) * p\<^sub>3 * p\<^sub>3)
)\<^sub>e"

definition SecondTest_pos :: "state prhfun" where
"SecondTest_pos = ((FirstTest ; TestAction) \<parallel> \<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e)"

definition SecondTest_pos_altdef :: "state rvhfun" where
"SecondTest_pos_altdef = (
    ((\<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * p\<^sub>1 * p\<^sub>2 * p\<^sub>2) + (\<lbrakk>lt\<^sup>> = Pos\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>\<not>c\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * (1 - p\<^sub>1) * p\<^sub>3 * p\<^sub>3)) / 
    (p\<^sub>1 * p\<^sub>2 * p\<^sub>2 + (1 - p\<^sub>1) * p\<^sub>3 * p\<^sub>3)
)\<^sub>e"

lemma TestAction: "TestAction = prfun_of_rvfun TestAction_altdef"
  apply (simp only: TestAction_def TestAction_altdef_def)
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

lemma pos_false: "{s::state. lt\<^sub>v s = Pos \<and> \<not> c\<^sub>v s} = {\<lparr>c\<^sub>v = False,lt\<^sub>v = Pos\<rparr>}"
  apply (simp add: set_eq_iff)
  apply (rule allI)
  apply (rule iffI)
  by simp+
lemma neg_false: "{s::state. lt\<^sub>v s = Neg \<and> \<not> c\<^sub>v s} = {\<lparr>c\<^sub>v = False,lt\<^sub>v = Neg\<rparr>}"
  apply (simp add: set_eq_iff)
  apply (rule allI)
  apply (rule iffI)
  by simp+
lemma summable_pos_false: "(\<lambda>x::state. if lt\<^sub>v x = Pos \<and> \<not> c\<^sub>v x then 1::\<real> else (0::\<real>)) summable_on UNIV"
  apply (rule infsum_constant_finite_states_summable)
  by (simp add: pos_false)
lemma summable_neg_false: "(\<lambda>x::state. if lt\<^sub>v x = Neg \<and> \<not> c\<^sub>v x then 1::\<real> else (0::\<real>)) summable_on UNIV"
  apply (rule infsum_constant_finite_states_summable)
  by (simp add: neg_false)
lemma pos_true: "{s::state. lt\<^sub>v s = Pos \<and> c\<^sub>v s} = {\<lparr>c\<^sub>v = True,lt\<^sub>v = Pos\<rparr>}"
  apply (simp add: set_eq_iff)
  apply (rule allI)
  apply (rule iffI)
  by simp+
lemma neg_true: "{s::state. lt\<^sub>v s = Neg \<and> c\<^sub>v s} = {\<lparr>c\<^sub>v = True,lt\<^sub>v = Neg\<rparr>}"
  apply (simp add: set_eq_iff)
  apply (rule allI)
  apply (rule iffI)
  by simp+
lemma summable_pos_true: "(\<lambda>x::state. if lt\<^sub>v x = Pos \<and> c\<^sub>v x then 1::\<real> else (0::\<real>)) summable_on UNIV"
  apply (rule infsum_constant_finite_states_summable)
  by (simp add: pos_true)
lemma summable_neg_true: "(\<lambda>x::state. if lt\<^sub>v x = Neg \<and> c\<^sub>v x then 1::\<real> else (0::\<real>)) summable_on UNIV"
  apply (rule infsum_constant_finite_states_summable)
  by (simp add: neg_true)
lemma TestAction_altdef_final: "is_final_distribution TestAction_altdef"
  apply (simp add: dist_defs expr_defs TestAction_altdef_def)
  apply (pred_auto)
proof -
  fix c
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
  shows "Init = prfun_of_rvfun Init_altdef"
  apply (simp only: Init_def Init_altdef_def)
  apply (simp add: TestAction)
  apply (simp only: pseqcomp_def)
  apply (subst rvfun_inverse) 
  using TestAction_altdef_final rvfun_prob_sum1_summable'(1) apply blast
  apply (subst prfun_pchoice_assigns_inverse_c')
  apply (simp add: TestAction_altdef_def)
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

lemma FirstTest: "FirstTest = prfun_of_rvfun FirstTest_altdef"
  apply (simp add: FirstTest_def FirstTest_altdef_def)
  apply (simp add: Init_simp)
  apply (simp add: pfun_defs)
  apply (subst rvfun_inverse)
  apply (simp add: Init_altdef_def)
  apply (expr_simp_1 add: dist_defs)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (subst fun_eq_iff)
  apply (simp add: Init_altdef_def dist_defs)
  apply (pred_auto) 
proof -
  fix c
  have f1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
           ((if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (89::\<real>) / (50000::\<real>) +
            (if lt\<^sub>v v\<^sub>0 = Neg then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (11::\<real>) / (50000::\<real>) +
            (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (499::\<real>) / (10000::\<real>) +
            (9481::\<real>) * ((if lt\<^sub>v v\<^sub>0 = Neg then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>))) / (10000::\<real>)) *
           (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>))) = 
        (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
           ((if lt\<^sub>v v\<^sub>0 = Pos \<and> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (89::\<real>) / (50000::\<real>) +
            (if lt\<^sub>v v\<^sub>0 = Pos \<and> \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (499::\<real>) / (10000::\<real>)))"
    apply (rule infsum_cong)
    by simp
  also have f2: "... = (89::\<real>) / (50000::\<real>) + (499::\<real>) / (10000::\<real>)"
    apply (subst infsum_add)
    apply (simp add: summable_on_cdiv_left summable_on_cmult_left summable_pos_true)
    apply (simp add: summable_on_cdiv_left summable_on_cmult_left summable_pos_false)
    apply (subst infsum_cdiv_left)
    using summable_on_cmult_left summable_pos_true apply blast
    apply (subst infsum_cmult_left)
    using summable_pos_true apply blast
    apply (subst infsum_cdiv_left)
    using summable_on_cmult_left summable_pos_false apply blast
    apply (subst infsum_cmult_left)
    using summable_pos_false apply blast
    apply (subst infsum_constant_finite_states)
    using pos_true apply force
    apply (subst infsum_constant_finite_states)
    using pos_false apply force
    using pos_false pos_true by force
  show "(161177::\<real>) /
       ((1250::\<real>) *
        (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
           ((if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (89::\<real>) / (50000::\<real>) +
            (if lt\<^sub>v v\<^sub>0 = Neg then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (11::\<real>) / (50000::\<real>) +
            (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (499::\<real>) / (10000::\<real>) +
            (9481::\<real>) * ((if lt\<^sub>v v\<^sub>0 = Neg then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>))) / (10000::\<real>)) *
           (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>)))) = (2495::\<real>)"
    by (simp add: f1 f2)
next
  fix c
  have f1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
           ((if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (89::\<real>) / (50000::\<real>) +
            (if lt\<^sub>v v\<^sub>0 = Neg then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (11::\<real>) / (50000::\<real>) +
            (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (499::\<real>) / (10000::\<real>) +
            (9481::\<real>) * ((if lt\<^sub>v v\<^sub>0 = Neg then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>))) / (10000::\<real>)) *
           (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>))) =
      (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
           ((if lt\<^sub>v v\<^sub>0 = Pos \<and> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (89::\<real>) / (50000::\<real>) +
            (if lt\<^sub>v v\<^sub>0 = Pos \<and> \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (499::\<real>) / (10000::\<real>)))"
    apply (rule infsum_cong)
    by simp
  have f2: "... = (89::\<real>) / (50000::\<real>) + (499::\<real>) / (10000::\<real>)"
    apply (subst infsum_add)
    apply (simp add: summable_on_cdiv_left summable_on_cmult_left summable_pos_true)
    apply (simp add: summable_on_cdiv_left summable_on_cmult_left summable_pos_false)
    apply (subst infsum_cdiv_left)
    using summable_on_cmult_left summable_pos_true apply blast
    apply (subst infsum_cmult_left)
    using summable_pos_true apply blast
    apply (subst infsum_cdiv_left)
    using summable_on_cmult_left summable_pos_false apply blast
    apply (subst infsum_cmult_left)
    using summable_pos_false apply blast
    apply (subst infsum_constant_finite_states)
    using pos_true apply force
    apply (subst infsum_constant_finite_states)
    using pos_false apply force
    using pos_false pos_true by force
  show "(28747::\<real>) /
       ((6250::\<real>) *
        (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
           ((if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (89::\<real>) / (50000::\<real>) +
            (if lt\<^sub>v v\<^sub>0 = Neg then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (11::\<real>) / (50000::\<real>) +
            (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (499::\<real>) / (10000::\<real>) +
            (9481::\<real>) * ((if lt\<^sub>v v\<^sub>0 = Neg then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>))) / (10000::\<real>)) *
           (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>)))) = (89::\<real>)"
    by (simp add: f1 f2)
qed

text \<open> What's the probability that the patient has cancer, given a positive test? @{text "P(Cancer | Test=Pos)"} \<close>
lemma "rvfun_of_prfun FirstTest ; \<lbrakk>c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e = ((p\<^sub>1 * p\<^sub>2) / (p\<^sub>1 * p\<^sub>2 + (1 - p\<^sub>1) * p\<^sub>3))\<^sub>e"
  apply (simp add: FirstTest_altdef_def FirstTest)
  apply (subst rvfun_inverse)
  apply (expr_simp_1 add: dist_defs)
  apply (pred_auto)
proof -
  have f1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
       ((89::\<real>) * ((if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>))) / (8::\<real>) +
        (2495::\<real>) * ((if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>))) / (8::\<real>)) *
       (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) / (323::\<real>)) = 
    (\<Sum>\<^sub>\<infinity>v\<^sub>0::state. (((if c\<^sub>v v\<^sub>0 \<and> lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>))) * ((89::\<real>) / (8::\<real>) / (323::\<real>))))"
    apply (rule infsum_cong)
    by simp
  also have f2: "... = ((89::\<real>) / (8::\<real>) / (323::\<real>))"
    apply (subst infsum_cmult_left)
    apply (smt (verit) summable_on_cong summable_pos_true)
    apply (simp)
    apply (subst infsum_constant_finite_states)
    using finite.simps pos_true apply auto[1]
    by (smt (verit) Collect_cong One_nat_def card.empty card.insert empty_iff finite.emptyI of_nat_1 pos_true)
  show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
       ((89::\<real>) * ((if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>))) / (8::\<real>) +
        (2495::\<real>) * ((if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>))) / (8::\<real>)) *
       (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) / (323::\<real>)) * (2584::\<real>) = (89::\<real>) "
    using f1 f2 by linarith
qed

text \<open> What's the probability that the patient has no cancer, given a positive test? @{text "P(\<not>Cancer | Test=Pos)"} \<close>
lemma "rvfun_of_prfun FirstTest ; \<lbrakk>\<not>c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e = ((1 - p\<^sub>1) * p\<^sub>3 / (p\<^sub>1 * p\<^sub>2 + (1 - p\<^sub>1) * p\<^sub>3))\<^sub>e"
  apply (simp add: FirstTest_altdef_def FirstTest)
  apply (subst rvfun_inverse)
  apply (expr_simp_1 add: dist_defs)
  apply (pred_auto)
proof -
  have f1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
       ((89::\<real>) * ((if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>))) / (8::\<real>) +
        (2495::\<real>) * ((if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>))) / (8::\<real>)) *
       (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) / (323::\<real>)) = 
    (\<Sum>\<^sub>\<infinity>v\<^sub>0::state. (((if \<not> c\<^sub>v v\<^sub>0 \<and> lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>))) * ((2495::\<real>) / (8::\<real>) / (323::\<real>))))"
    apply (rule infsum_cong)
    by simp
  also have f2: "... = ((2495::\<real>) / (8::\<real>) / (323::\<real>))"
    apply (subst infsum_cmult_left)
    apply (smt (verit) summable_on_cong summable_pos_false)
    apply (simp)
    apply (subst infsum_constant_finite_states)
    using finite.simps pos_false apply auto[1]
    by (smt (verit) Collect_cong One_nat_def card.empty card.insert empty_iff finite.emptyI of_nat_1 pos_false)
  show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
       ((89::\<real>) * ((if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>))) / (8::\<real>) +
        (2495::\<real>) * ((if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>))) / (8::\<real>)) *
       (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) / (323::\<real>)) * (2584::\<real>) = (2495::\<real>)"
    using f1 f2 by linarith
qed

lemma SecondTest: "(FirstTest ; TestAction) = prfun_of_rvfun SecondTest_altdef"
  apply (simp add: SecondTest_def SecondTest_altdef_def)
  apply (simp add: FirstTest TestAction)
  apply (simp add: pseqcomp_def)
  apply (subst rvfun_inverse)
  apply (simp add: FirstTest_altdef_def)
   apply (expr_simp_1 add: dist_defs)
  apply (subst rvfun_inverse)
  apply (simp add: TestAction_altdef_def)
  apply (expr_simp_1 add: dist_defs)
  
lemma SecondTest: "SecondTest = prfun_of_rvfun SecondTest_altdef"
  apply (simp add: SecondTest_def SecondTest_altdef_def)
  apply (simp add: FirstTest)
  apply (simp add: pfun_defs)
  apply (subst rvfun_inverse)
  apply (simp add: FirstTest_altdef_def)
  apply (expr_simp_1 add: dist_defs)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (subst fun_eq_iff)
  apply (simp add: FirstTest_altdef_def dist_defs)
  apply (pred_auto) 
proof -
  fix c
  have f1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
           ((89::\<real>) * ((if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>))) / (8::\<real>) +
            (2495::\<real>) * ((if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>))) / (8::\<real>)) *
           (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>)) / (323::\<real>)) = 
        (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
           (((if c\<^sub>v v\<^sub>0 \<and> lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>))) * ((89::\<real>) / (8::\<real>)  / (323::\<real>)) +
            ((if \<not> c\<^sub>v v\<^sub>0 \<and> lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>))) * ((2495::\<real>) / (8::\<real>) / (323::\<real>))))"
    apply (rule infsum_cong)
    by simp
  also have f2: "... = ((89::\<real>) / (8::\<real>)  / (323::\<real>)) + ((2495::\<real>) / (8::\<real>) / (323::\<real>))"
    apply (subst infsum_add)
    apply (subst summable_on_cmult_left)
    apply (smt (verit) summable_on_cong summable_pos_true)
    apply (simp)
    apply (subst summable_on_cmult_left)
    apply (smt (verit) summable_on_cong summable_pos_false)
     apply (simp)
    apply (subst infsum_cmult_left)
     apply (smt (verit, ccfv_SIG) summable_on_cong summable_pos_true)
    apply (subst infsum_cmult_left)
    apply (smt (verit, ccfv_SIG) summable_on_cong summable_pos_false)
    apply (subst infsum_constant_finite_states)
    using finite.simps pos_true apply auto[1]
    apply (subst infsum_constant_finite_states)
    using finite.simps pos_false apply auto[1]
    by (metis (no_types, lifting) Collect_cong One_nat_def card.empty card.insert equals0D finite.emptyI mult_cancel_right2 of_nat_1 pos_false pos_true)
  show "(12722005::\<real>) / ((646::\<real>) *
        (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
           ((89::\<real>) * ((if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>))) / (8::\<real>) +
            (2495::\<real>) * ((if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>))) / (8::\<real>)) *
           (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>)) /
           (323::\<real>))) = (12475::\<real>)"
    apply (simp only: f1 f2)
next
  fix c
  have f1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
           ((if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (89::\<real>) / (50000::\<real>) +
            (if lt\<^sub>v v\<^sub>0 = Neg then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (11::\<real>) / (50000::\<real>) +
            (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (499::\<real>) / (10000::\<real>) +
            (9481::\<real>) * ((if lt\<^sub>v v\<^sub>0 = Neg then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>))) / (10000::\<real>)) *
           (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>))) =
      (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
           ((if lt\<^sub>v v\<^sub>0 = Pos \<and> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (89::\<real>) / (50000::\<real>) +
            (if lt\<^sub>v v\<^sub>0 = Pos \<and> \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (499::\<real>) / (10000::\<real>)))"
    apply (rule infsum_cong)
    by simp
  have f2: "... = (89::\<real>) / (50000::\<real>) + (499::\<real>) / (10000::\<real>)"
    apply (subst infsum_add)
    apply (simp add: summable_on_cdiv_left summable_on_cmult_left summable_pos_true)
    apply (simp add: summable_on_cdiv_left summable_on_cmult_left summable_pos_false)
    apply (subst infsum_cdiv_left)
    using summable_on_cmult_left summable_pos_true apply blast
    apply (subst infsum_cmult_left)
    using summable_pos_true apply blast
    apply (subst infsum_cdiv_left)
    using summable_on_cmult_left summable_pos_false apply blast
    apply (subst infsum_cmult_left)
    using summable_pos_false apply blast
    apply (subst infsum_constant_finite_states)
    using pos_true apply force
    apply (subst infsum_constant_finite_states)
    using pos_false apply force
    using pos_false pos_true by force
  show "(28747::\<real>) /
       ((6250::\<real>) *
        (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
           ((if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (89::\<real>) / (50000::\<real>) +
            (if lt\<^sub>v v\<^sub>0 = Neg then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (11::\<real>) / (50000::\<real>) +
            (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (499::\<real>) / (10000::\<real>) +
            (9481::\<real>) * ((if lt\<^sub>v v\<^sub>0 = Neg then 1::\<real> else (0::\<real>)) * (if \<not> c\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>))) / (10000::\<real>)) *
           (if lt\<^sub>v v\<^sub>0 = Pos then 1::\<real> else (0::\<real>)))) = (89::\<real>)"
    by (simp add: f1 f2)
qed

end
