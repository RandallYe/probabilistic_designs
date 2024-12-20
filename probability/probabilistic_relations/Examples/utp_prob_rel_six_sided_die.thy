section \<open> Throw two six-sided dice \<close>
text \<open>This example is from Section 15 of the Hehner's paper ``A probability perspective''.
The invariant of the program for an equal result is 
@{text "\<lbrakk>u' = v'\<rbrakk>\<^sub>\<I> * \<lbrakk>t' \<ge> t+1\<rbrakk>\<^sub>\<I> * (5/6)^(t'-t-1) * (1/6)"}.
This program cannot guarantee absolute termination (see Section 2.3 of ``
Abstraction Refinement and Proof for Probabilistic Systems''), but it is almost-certain 
termination.
The probability for non-termination is @{text "\<lbrakk>u' \<noteq> v'\<rbrakk>\<^sub>\<I> * \<lbrakk>t' \<ge> t+1\<rbrakk>\<^sub>\<I> * (5/6)^(t'-t)"}. When 
@{text "t'"} tends to @{text "\<infinity>"}, then the probability tends to 0.
\<close>

theory utp_prob_rel_six_sided_die
  imports 
    "UTP_prob_relations.utp_prob_rel" 
    "HOL-Analysis.Infinite_Set_Sum"
begin 

unbundle UTP_Syntax

declare [[show_types]]
subsection \<open> Knuth and Yao's algorithm to simulate six-sided die using a fair coin \<close>

datatype S = s1 | s2 | s3 | s4
datatype D = o0 | o1 | o2 | o3

subsubsection \<open> State space \<close>
alphabet state = time +
  s   :: S
  d   :: D
definition outcome :: "S \<Rightarrow> D \<Rightarrow> state prhfun" where
"outcome s\<^sub>1 d\<^sub>1 = (s := \<guillemotleft>s\<^sub>1\<guillemotright>; d := \<guillemotleft>d\<^sub>1\<guillemotright>)"

definition step_outcome :: "ureal \<Rightarrow> S \<Rightarrow> S \<Rightarrow> D \<Rightarrow> D \<Rightarrow> state prhfun" where
"step_outcome p s\<^sub>1 s\<^sub>2 d\<^sub>1 d\<^sub>2 = (if\<^sub>p \<guillemotleft>p\<guillemotright> then outcome s\<^sub>1 d\<^sub>1 else outcome s\<^sub>2 d\<^sub>2)"

definition step :: "ureal \<Rightarrow> S \<Rightarrow> S \<Rightarrow> D \<Rightarrow> D \<Rightarrow> state prhfun" where
"step p s\<^sub>1 s\<^sub>2 d\<^sub>1 d\<^sub>2 =  step_outcome p s\<^sub>1 s\<^sub>2 d\<^sub>1 d\<^sub>2 ; t := t + 1"

abbreviation "step1 p \<equiv> step p s2 s3 o0 o0"
abbreviation "step2 p \<equiv> step p s1 s4 o0 o1"
abbreviation "step3 p \<equiv> step p s4 s4 o2 o3"

definition dice :: "ureal \<Rightarrow> state prhfun" where 
"dice p = 
  s := s1 ; d := o0; t := 0;
  while\<^sub>p (\<not> s\<^sup>< = s4)\<^sub>e do 
    (step1 p ; (if\<^sub>c s\<^sup>< = s2 then step2 p else step3 p))
  od"

lemma outcome_simp: "rvfun_of_prfun (outcome s\<^sub>1 d\<^sub>1)
    = (\<lbrakk>s\<^sup>> = \<guillemotleft>s\<^sub>1\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>d\<^sup>> = \<guillemotleft>d\<^sub>1\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"
  apply (simp add: outcome_def prfun_passign_comp)
  apply (subst rvfun_inverse)
  apply (simp add: assigns_comp rvfun_assignment_is_prob)
  by (pred_auto)

lemma state_ib_simp: "\<forall>s::state. (
  (if s\<^sub>v s = s\<^sub>1 then 1::\<real> else (0::\<real>)) * 
  (if d\<^sub>v s = d\<^sub>1 then 1::\<real> else (0::\<real>)) *
  (if t\<^sub>v s = tt then 1::\<real> else (0::\<real>))
= (if s\<^sub>v s = s\<^sub>1 \<and> d\<^sub>v s = d\<^sub>1 \<and> t\<^sub>v s = tt then 1::\<real> else (0::\<real>)))"
  by auto

lemma outcome_dist: "is_final_distribution (rvfun_of_prfun (outcome s\<^sub>1 d\<^sub>1))"
  apply (simp add: outcome_simp)
  apply (simp add: dist_defs)
  apply (expr_auto)
proof -
  fix t
  let ?lhs = "(\<Sum>\<^sub>\<infinity>s::state.
          (if s\<^sub>v s = s\<^sub>1 then 1::\<real> else (0::\<real>)) * (if d\<^sub>v s = d\<^sub>1 then 1::\<real> else (0::\<real>)) *
          (if t\<^sub>v s = t then 1::\<real> else (0::\<real>)))"
  have f1: "?lhs = (\<Sum>\<^sub>\<infinity>s::state. (if s\<^sub>v s = s\<^sub>1 \<and> d\<^sub>v s = d\<^sub>1 \<and> t\<^sub>v s = t then 1::\<real> else (0::\<real>)))"
    apply (rule infsum_cong)
    by auto
  show "?lhs = (1::\<real>)"
    apply (simp add: f1)
    apply (rule infsum_singleton_cond_unique)
    by (smt (verit, del_insts) old.unit.exhaust state.select_convs(1) state.select_convs(2) state.surjective time.select_convs(1) time_ext_def)
qed

lemma step_outcome_simp: "rvfun_of_prfun (step_outcome p s\<^sub>1 s\<^sub>2 d\<^sub>1 d\<^sub>2)  = 
  (
    \<lbrakk>s\<^sup>> = \<guillemotleft>s\<^sub>1\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>d\<^sup>> = \<guillemotleft>d\<^sub>1\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> +
    \<lbrakk>s\<^sup>> = \<guillemotleft>s\<^sub>2\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>d\<^sup>> = \<guillemotleft>d\<^sub>2\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>)
  )\<^sub>e"
  apply (simp only: step_outcome_def pchoice_def)
  apply (subst rvfun_pchoice_inverse)
  using ureal_is_prob apply blast+
  apply (simp only: outcome_simp)
  apply (simp add: ureal_defs)
  by (simp add: mult.commute)

lemma step_outcome_dist: "is_final_distribution (rvfun_of_prfun (step_outcome p s\<^sub>1 s\<^sub>2 d\<^sub>1 d\<^sub>2))"
  apply (simp add: step_outcome_def pchoice_def)
  apply (subst rvfun_pchoice_inverse)
  apply (simp add: ureal_is_prob)+
  apply (simp add: rvfun_of_prfun_def)
  apply (subst rvfun_pchoice_is_dist')
  by (metis SEXP_def outcome_dist rvfun_of_prfun_def)+

lemma "\<forall>s d. (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if s\<^sub>v v\<^sub>0 = s\<^sub>1 then 1::\<real> else (0::\<real>)) * (if d\<^sub>v v\<^sub>0 = d\<^sub>1 then 1::\<real> else (0::\<real>)) *
           (if t\<^sub>v v\<^sub>0 = t then 1::\<real> else (0::\<real>)) *
           ureal2real p +
           (if s\<^sub>v v\<^sub>0 = s\<^sub>2 then 1::\<real> else (0::\<real>)) * (if d\<^sub>v v\<^sub>0 = d\<^sub>1 then 1::\<real> else (0::\<real>)) *
           (if t\<^sub>v v\<^sub>0 = t then 1::\<real> else (0::\<real>)) *
           ((1::\<real>) - ureal2real p)) *
          (if \<lparr>t\<^sub>v = Suc t, s\<^sub>v = s, d\<^sub>v = d\<rparr> = v\<^sub>0\<lparr>t\<^sub>v := Suc (t\<^sub>v v\<^sub>0)\<rparr> then 1::\<real> else (0::\<real>)))
  = (if s\<^sub>v v\<^sub>0 = s\<^sub>1 \<and> d\<^sub>v v\<^sub>0 = d\<^sub>1 \<and> t\<^sub>v v\<^sub>0 = t)"

lemma step_altdef:
  "rvfun_of_prfun (step p s\<^sub>1 s\<^sub>2 d\<^sub>1 d\<^sub>2) = (
    \<lbrakk>s\<^sup>> = \<guillemotleft>s\<^sub>1\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>d\<^sup>> = \<guillemotleft>d\<^sub>1\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> +
    \<lbrakk>s\<^sup>> = \<guillemotleft>s\<^sub>2\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>d\<^sup>> = \<guillemotleft>d\<^sub>2\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>)
  )\<^sub>e"
  apply (simp only: step_def)
  apply (simp only: pseqcomp_def)
  apply (subst rvfun_seqcomp_inverse)+
  apply (simp add: step_outcome_dist)+
  apply (simp add: ureal_is_prob)
  apply (simp add: pfun_defs)
  apply (subst rvfun_assignment_inverse)
  apply (simp only: step_outcome_simp)
  apply (expr_simp_1)
  apply (pred_auto)
  apply (subst fun_eq_iff)
  
  
  oops

end