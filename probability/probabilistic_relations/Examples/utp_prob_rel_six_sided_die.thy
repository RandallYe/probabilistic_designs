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

definition loop_body :: "ureal \<Rightarrow> state prhfun" where 
"loop_body p = (step1 p ; (if\<^sub>c s\<^sup>< = s2 then step2 p else step3 p))"

definition dice :: "ureal \<Rightarrow> state prhfun" where 
"dice p = 
  s := s1 ; d := o0; t := 0;
  while\<^sub>p (\<not> s\<^sup>< = s4)\<^sub>e do 
    loop_body p
  od"

lemma outcome_simp: "rvfun_of_prfun (outcome s\<^sub>1 d\<^sub>1)
    = (\<lbrakk>s\<^sup>> = \<guillemotleft>s\<^sub>1\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>d\<^sub>1\<guillemotright> \<and> t\<^sup>> = t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"
  apply (simp add: outcome_def prfun_passign_comp)
  apply (subst rvfun_inverse)
  apply (simp add: assigns_comp rvfun_assignment_is_prob)
  by (pred_auto)

lemma "(\<lbrakk>s\<^sup>> = \<guillemotleft>s\<^sub>1\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>d\<^sup>> = \<guillemotleft>d\<^sub>1\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e = (\<lbrakk>s\<^sup>> = \<guillemotleft>s\<^sub>1\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>d\<^sub>1\<guillemotright> \<and> t\<^sup>> = t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"
  apply (subst iverson_bracket_conj)
  apply (subst iverson_bracket_conj)
  by (simp add: mult.assoc)

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
  apply (rule infsum_singleton_cond_unique)
  by (smt (verit, del_insts) old.unit.exhaust state.select_convs(1) state.select_convs(2) state.surjective time.select_convs(1) time_ext_def)

lemma step_outcome_simp: "rvfun_of_prfun (step_outcome p s\<^sub>1 s\<^sub>2 d\<^sub>1 d\<^sub>2)  = 
  (
    \<lbrakk>s\<^sup>> = \<guillemotleft>s\<^sub>1\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>d\<^sub>1\<guillemotright> \<and> t\<^sup>> = t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> +
    \<lbrakk>s\<^sup>> = \<guillemotleft>s\<^sub>2\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>d\<^sub>2\<guillemotright> \<and> t\<^sup>> = t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>)
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

lemma step_altdef:
  "rvfun_of_prfun (step p s\<^sub>1 s\<^sub>2 d\<^sub>1 d\<^sub>2) = (
    \<lbrakk>s\<^sup>> = \<guillemotleft>s\<^sub>1\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>d\<^sub>1\<guillemotright> \<and> t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> +
    \<lbrakk>s\<^sup>> = \<guillemotleft>s\<^sub>2\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>d\<^sub>2\<guillemotright> \<and> t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>)
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
  apply (subst fun_eq_iff)
  apply (rule allI)
proof -
  fix x :: "state \<times> state"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if get\<^bsub>s\<^esub> v\<^sub>0 = s\<^sub>1 \<and> get\<^bsub>d\<^esub> v\<^sub>0 = d\<^sub>1 \<and> get\<^bsub>t\<^esub> v\<^sub>0 = get\<^bsub>t\<^esub> (fst x) then 1::\<real> else (0::\<real>)) * ureal2real p +
           (if get\<^bsub>s\<^esub> v\<^sub>0 = s\<^sub>2 \<and> get\<^bsub>d\<^esub> v\<^sub>0 = d\<^sub>2 \<and> get\<^bsub>t\<^esub> v\<^sub>0 = get\<^bsub>t\<^esub> (fst x) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
          (if \<langle>\<lambda>s::state. put\<^bsub>t\<^esub> s (Suc (get\<^bsub>t\<^esub> s))\<rangle>\<^sub>a (v\<^sub>0, snd x) then 1::\<real> else (0::\<real>)))"
  let ?rhs_1 = "(if get\<^bsub>s\<^esub> (snd x) = s\<^sub>1 \<and> get\<^bsub>d\<^esub> (snd x) = d\<^sub>1 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (get\<^bsub>t\<^esub> (fst x)) then 1::\<real> else (0::\<real>)) * ureal2real p"
  let ?rhs_2 = "(if get\<^bsub>s\<^esub> (snd x) = s\<^sub>2 \<and> get\<^bsub>d\<^esub> (snd x) = d\<^sub>2 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (get\<^bsub>t\<^esub> (fst x)) then 1::\<real> else (0::\<real>)) *
       ((1::\<real>) - ureal2real p)"

  have s1: "{s::state. s\<^sub>v s = s\<^sub>1 \<and> d\<^sub>v s = d\<^sub>1 \<and> t\<^sub>v s = t\<^sub>v (fst x) \<and> snd x = s\<lparr>t\<^sub>v := Suc (t\<^sub>v s)\<rparr>}
    = (if snd x = \<lparr>t\<^sub>v = Suc (t\<^sub>v (fst x)), s\<^sub>v = s\<^sub>1, d\<^sub>v = d\<^sub>1\<rparr> then {\<lparr>t\<^sub>v = t\<^sub>v (fst x), s\<^sub>v = s\<^sub>1, d\<^sub>v = d\<^sub>1\<rparr>} else {})"
    by auto
  then have fin_s1: "finite {s::state. s\<^sub>v s = s\<^sub>1 \<and> d\<^sub>v s = d\<^sub>1 \<and> t\<^sub>v s = t\<^sub>v (fst x) \<and> snd x = s\<lparr>t\<^sub>v := Suc (t\<^sub>v s)\<rparr>}"
    by auto

  have s2: "{s::state. s\<^sub>v s = s\<^sub>2 \<and> d\<^sub>v s = d\<^sub>2 \<and> t\<^sub>v s = t\<^sub>v (fst x) \<and> snd x = s\<lparr>t\<^sub>v := Suc (t\<^sub>v s)\<rparr>}
   = (if snd x = \<lparr>t\<^sub>v = Suc (t\<^sub>v (fst x)), s\<^sub>v = s\<^sub>2, d\<^sub>v = d\<^sub>2\<rparr> then {\<lparr>t\<^sub>v = t\<^sub>v (fst x), s\<^sub>v = s\<^sub>2, d\<^sub>v = d\<^sub>2\<rparr>} else {})"
    by auto
  then have fin_s2: "finite {s::state. s\<^sub>v s = s\<^sub>2 \<and> d\<^sub>v s = d\<^sub>2 \<and> t\<^sub>v s = t\<^sub>v (fst x) \<and> snd x = s\<lparr>t\<^sub>v := Suc (t\<^sub>v s)\<rparr>}"
    by auto

  have sum_s1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state. (if get\<^bsub>s\<^esub> v\<^sub>0 = s\<^sub>1 \<and> get\<^bsub>d\<^esub> v\<^sub>0 = d\<^sub>1 \<and> get\<^bsub>t\<^esub> v\<^sub>0 = get\<^bsub>t\<^esub> (fst x) \<and> 
          \<langle>\<lambda>s::state. put\<^bsub>t\<^esub> s (Suc (get\<^bsub>t\<^esub> s))\<rangle>\<^sub>a (v\<^sub>0, snd x) then 1::\<real> else (0::\<real>)) * ureal2real p) 
    = ?rhs_1"
    apply (subst infsum_cmult_left')
    apply (subst infsum_constant_finite_states)
    apply (pred_auto)
    using fin_s1 apply blast
    apply pred_auto
    using s1 apply force
    apply (metis (no_types, lifting) card.empty less_numeral_extra(3) s1 state.select_convs(2))
    apply (metis (no_types, lifting) card.empty less_numeral_extra(3) s1 state.select_convs(1))
    by (metis (no_types, lifting) card.empty less_numeral_extra(3) s1 time.select_convs(1))

  have sum_s2: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state. (if get\<^bsub>s\<^esub> v\<^sub>0 = s\<^sub>2 \<and> get\<^bsub>d\<^esub> v\<^sub>0 = d\<^sub>2 \<and> get\<^bsub>t\<^esub> v\<^sub>0 = get\<^bsub>t\<^esub> (fst x) \<and> 
          \<langle>\<lambda>s::state. put\<^bsub>t\<^esub> s (Suc (get\<^bsub>t\<^esub> s))\<rangle>\<^sub>a (v\<^sub>0, snd x) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p))
    = ?rhs_2"
    apply (subst infsum_cmult_left')
    apply (subst infsum_constant_finite_states)
    apply (pred_auto)
    using fin_s2 apply blast
    apply pred_auto
    using s2 apply force
    apply (metis (no_types, lifting) card.empty less_numeral_extra(3) s2 state.select_convs(2))
    apply (metis (no_types, lifting) card.empty less_numeral_extra(3) s2 state.select_convs(1))
    by (metis (no_types, lifting) card.empty less_numeral_extra(3) s2 time.select_convs(1))

  have f1: "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if get\<^bsub>s\<^esub> v\<^sub>0 = s\<^sub>1 \<and> get\<^bsub>d\<^esub> v\<^sub>0 = d\<^sub>1 \<and> get\<^bsub>t\<^esub> v\<^sub>0 = get\<^bsub>t\<^esub> (fst x) \<and> 
            \<langle>\<lambda>s::state. put\<^bsub>t\<^esub> s (Suc (get\<^bsub>t\<^esub> s))\<rangle>\<^sub>a (v\<^sub>0, snd x) then 1::\<real> else (0::\<real>)) * ureal2real p +
           (if get\<^bsub>s\<^esub> v\<^sub>0 = s\<^sub>2 \<and> get\<^bsub>d\<^esub> v\<^sub>0 = d\<^sub>2 \<and> get\<^bsub>t\<^esub> v\<^sub>0 = get\<^bsub>t\<^esub> (fst x) \<and> 
            \<langle>\<lambda>s::state. put\<^bsub>t\<^esub> s (Suc (get\<^bsub>t\<^esub> s))\<rangle>\<^sub>a (v\<^sub>0, snd x) then 1::\<real> else (0::\<real>)) *
           ((1::\<real>) - ureal2real p)))"
    apply (rule infsum_cong)
    by auto
  have f2: "... = ?rhs_1 + ?rhs_2"
    apply (subst infsum_add)
    apply (cases "ureal2real p = (0::\<real>)")
    apply simp
    apply (subst summable_on_cmult_left')
    apply simp
    apply (subst infsum_constant_finite_states_summable)
    apply (pred_auto)
    apply (simp add: fin_s1)+
    apply (cases "ureal2real p = (1::\<real>)")
    apply simp
    apply (subst summable_on_cmult_left')
    apply simp
    apply (subst infsum_constant_finite_states_summable)
    apply (pred_auto)
    apply (simp add: fin_s2)
    apply (simp)
    using sum_s1 sum_s2 by presburger
  from f1 f2 show "?lhs = ?rhs_1 + ?rhs_2"
    by presburger
qed

lemma singleton_set_simp: "{s::state. s\<^sub>v s = s\<^sub>1 \<and> d\<^sub>v s = d\<^sub>1 \<and> t\<^sub>v s = t\<^sub>1} = {\<lparr>t\<^sub>v = t\<^sub>1, s\<^sub>v = s\<^sub>1, d\<^sub>v = d\<^sub>1\<rparr>}"
  by auto

lemma step_is_dist: "is_final_distribution (rvfun_of_prfun (step p s\<^sub>1 s\<^sub>2 d\<^sub>1 d\<^sub>2))"
  apply (simp add: step_altdef)
  apply (expr_auto add: dist_defs)
  defer
  apply (simp add: ureal_lower_bound ureal_upper_bound)+
  defer
  apply (simp add: ureal_lower_bound ureal_upper_bound)+
  apply (subst infsum_constant_finite_states_cmult_2)
  apply (simp add: singleton_set_simp)+
  apply (subst infsum_constant_finite_states_cmult_2)
  apply (simp add: singleton_set_simp)+
  apply (subst infsum_constant_finite_states_cmult_2)
  by (simp add: singleton_set_simp)+

(*
\<Sum>\<^sub>\<infinity> v\<^sub>0. 
(
  \<lbrakk>s\<^sup>> = \<guillemotleft>s2\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o0\<guillemotright> \<and> t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> +
  \<lbrakk>s\<^sup>> = \<guillemotleft>s3\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o0\<guillemotright> \<and> t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>)
)[v\<^sub>0/v\<^sup>>] *
(
  \<lbrakk>s\<^sup>< = \<guillemotleft>s2\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>s\<^sup>> = \<guillemotleft>s1\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o0\<guillemotright> \<and> t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> +
  \<lbrakk>s\<^sup>< = \<guillemotleft>s2\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o1\<guillemotright> \<and> t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>) +
  \<lbrakk>\<not>s\<^sup>< = \<guillemotleft>s2\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o2\<guillemotright> \<and> t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> +
  \<lbrakk>\<not>s\<^sup>< = \<guillemotleft>s2\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o3\<guillemotright> \<and> t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>)
)[v\<^sub>0/v\<^sup><]

= 

\<Sum>\<^sub>\<infinity> v\<^sub>0. 
(
  \<lbrakk>s\<^sub>v v\<^sub>0 = \<guillemotleft>s2\<guillemotright> \<and> d\<^sub>v v\<^sub>0 = \<guillemotleft>o0\<guillemotright> \<and> t\<^sub>v v\<^sub>0 = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> +
  \<lbrakk>s\<^sub>v v\<^sub>0 = \<guillemotleft>s3\<guillemotright> \<and> d\<^sub>v v\<^sub>0  = \<guillemotleft>o0\<guillemotright> \<and> t\<^sub>v v\<^sub>0  = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>)
) *
(
  \<lbrakk>s\<^sub>v v\<^sub>0 = \<guillemotleft>s2\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>s\<^sup>> = \<guillemotleft>s1\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o0\<guillemotright> \<and> t\<^sup>> = t\<^sub>v v\<^sub>0 + 1\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> +
  \<lbrakk>s\<^sub>v v\<^sub>0 = \<guillemotleft>s2\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o1\<guillemotright> \<and> t\<^sup>> = t\<^sub>v v\<^sub>0 + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>) +
  \<lbrakk>\<not>s\<^sub>v v\<^sub>0 = \<guillemotleft>s2\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o2\<guillemotright> \<and> t\<^sup>> = t\<^sub>v v\<^sub>0 + 1\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> +
  \<lbrakk>\<not>s\<^sub>v v\<^sub>0 = \<guillemotleft>s2\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o3\<guillemotright> \<and> t\<^sup>> = t\<^sub>v v\<^sub>0 + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>)
)

= 

\<Sum>\<^sub>\<infinity> v\<^sub>0. 
(
  \<lbrakk>s\<^sub>v v\<^sub>0 = \<guillemotleft>s2\<guillemotright> \<and> d\<^sub>v v\<^sub>0 = \<guillemotleft>o0\<guillemotright> \<and> t\<^sub>v v\<^sub>0 = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> * 
    \<lbrakk>s\<^sub>v v\<^sub>0 = \<guillemotleft>s2\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>s\<^sup>> = \<guillemotleft>s1\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o0\<guillemotright> \<and> t\<^sup>> = t\<^sub>v v\<^sub>0 + 1\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> +
  \<lbrakk>s\<^sub>v v\<^sub>0 = \<guillemotleft>s2\<guillemotright> \<and> d\<^sub>v v\<^sub>0 = \<guillemotleft>o0\<guillemotright> \<and> t\<^sub>v v\<^sub>0 = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> * 
    \<lbrakk>s\<^sub>v v\<^sub>0 = \<guillemotleft>s2\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o1\<guillemotright> \<and> t\<^sup>> = t\<^sub>v v\<^sub>0 + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>) +
  \<lbrakk>s\<^sub>v v\<^sub>0 = \<guillemotleft>s3\<guillemotright> \<and> d\<^sub>v v\<^sub>0  = \<guillemotleft>o0\<guillemotright> \<and> t\<^sub>v v\<^sub>0  = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>) *
    \<lbrakk>\<not>s\<^sub>v v\<^sub>0 = \<guillemotleft>s2\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o2\<guillemotright> \<and> t\<^sup>> = t\<^sub>v v\<^sub>0 + 1\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> +
  \<lbrakk>s\<^sub>v v\<^sub>0 = \<guillemotleft>s3\<guillemotright> \<and> d\<^sub>v v\<^sub>0  = \<guillemotleft>o0\<guillemotright> \<and> t\<^sub>v v\<^sub>0  = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>) *
    \<lbrakk>\<not>s\<^sub>v v\<^sub>0 = \<guillemotleft>s2\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o3\<guillemotright> \<and> t\<^sup>> = t\<^sub>v v\<^sub>0 + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>)
) 

= 
  \<lbrakk>s\<^sup>> = \<guillemotleft>s1\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o0\<guillemotright> \<and> t\<^sup>> = t\<^sup>< + 2\<rbrakk>\<^sub>\<I>\<^sub>e * (ureal2real \<guillemotleft>p\<guillemotright>) * (ureal2real \<guillemotleft>p\<guillemotright>) +
  \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o1\<guillemotright> \<and> t\<^sup>> = t\<^sup>< + 2\<rbrakk>\<^sub>\<I>\<^sub>e * (ureal2real \<guillemotleft>p\<guillemotright>) * (1- ureal2real \<guillemotleft>p\<guillemotright>) +
  \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o2\<guillemotright> \<and> t\<^sup>> = t\<^sup>< + 2\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>) * (ureal2real \<guillemotleft>p\<guillemotright>) +
  \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o3\<guillemotright> \<and> t\<^sup>> = t\<^sup>< + 2\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>) * (1- ureal2real \<guillemotleft>p\<guillemotright>)

*)

lemma loop_body_altdef: "rvfun_of_prfun (loop_body p) = (
    \<lbrakk>s\<^sup>> = \<guillemotleft>s1\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o0\<guillemotright> \<and> t\<^sup>> = t\<^sup>< + 2\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> * ureal2real \<guillemotleft>p\<guillemotright> +
    \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o1\<guillemotright> \<and> t\<^sup>> = t\<^sup>< + 2\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> * (1- ureal2real \<guillemotleft>p\<guillemotright>) +
    \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o2\<guillemotright> \<and> t\<^sup>> = t\<^sup>< + 2\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>) * ureal2real \<guillemotleft>p\<guillemotright> +
    \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o3\<guillemotright> \<and> t\<^sup>> = t\<^sup>< + 2\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>) * (1- ureal2real \<guillemotleft>p\<guillemotright>)
  )\<^sub>e"

  apply (simp add: loop_body_def)
(*
  apply (subst prfun_seqcomp_pcond_subdist')
   apply (simp add: is_dist_subdist step_is_dist)
*)
  apply (simp only: pseqcomp_def pcond_def)
  apply (subst rvfun_pcond_inverse)
  apply (simp add: ureal_is_prob)
  apply (simp add: ureal_is_prob)
  apply (subst rvfun_seqcomp_inverse)
  using step_is_dist apply auto[1]
  apply (subst rvfun_pcond_is_prob)
  apply (simp add: ureal_is_prob)
  apply (simp add: ureal_is_prob)
  apply simp
  apply (simp add: rvfun_pcond_altdef)
  apply (simp add: step_altdef)
  apply (expr_simp_1)
  apply (subst fun_eq_iff)
  apply (rule allI)
proof -
  fix x :: "state \<times> state"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if get\<^bsub>s\<^esub> v\<^sub>0 = s2 \<and> get\<^bsub>d\<^esub> v\<^sub>0 = o0 \<and> get\<^bsub>t\<^esub> v\<^sub>0 = Suc (get\<^bsub>t\<^esub> (fst x)) then 1::\<real> else (0::\<real>)) * ureal2real p +
           (if get\<^bsub>s\<^esub> v\<^sub>0 = s3 \<and> get\<^bsub>d\<^esub> v\<^sub>0 = o0 \<and> get\<^bsub>t\<^esub> v\<^sub>0 = Suc (get\<^bsub>t\<^esub> (fst x)) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
          ((if get\<^bsub>s\<^esub> v\<^sub>0 = s2 then 1::\<real> else (0::\<real>)) *
           ((if get\<^bsub>s\<^esub> (snd x) = s1 \<and> get\<^bsub>d\<^esub> (snd x) = o0 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (get\<^bsub>t\<^esub> v\<^sub>0) then 1::\<real> else (0::\<real>)) * ureal2real p +
            (if get\<^bsub>s\<^esub> (snd x) = s4 \<and> get\<^bsub>d\<^esub> (snd x) = o1 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (get\<^bsub>t\<^esub> v\<^sub>0) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) +
           (if \<not> get\<^bsub>s\<^esub> v\<^sub>0 = s2 then 1::\<real> else (0::\<real>)) *
           ((if get\<^bsub>s\<^esub> (snd x) = s4 \<and> get\<^bsub>d\<^esub> (snd x) = o2 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (get\<^bsub>t\<^esub> v\<^sub>0) then 1::\<real> else (0::\<real>)) * ureal2real p +
            (if get\<^bsub>s\<^esub> (snd x) = s4 \<and> get\<^bsub>d\<^esub> (snd x) = o3 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (get\<^bsub>t\<^esub> v\<^sub>0) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p))))"
  have set1: "{sa::state. get\<^bsub>s\<^esub> sa = s2 \<and> get\<^bsub>d\<^esub> sa = o0 \<and> get\<^bsub>t\<^esub> sa = Suc (get\<^bsub>t\<^esub> (fst x)) \<and> get\<^bsub>s\<^esub> (snd x) = s1 \<and> get\<^bsub>d\<^esub> (snd x) = o0 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (get\<^bsub>t\<^esub> sa)}
    = (if get\<^bsub>s\<^esub> (snd x) = s1 \<and> get\<^bsub>d\<^esub> (snd x) = o0 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (Suc (get\<^bsub>t\<^esub> (fst x))) then 
        {\<lparr>t\<^sub>v = Suc (get\<^bsub>t\<^esub> (fst x)), s\<^sub>v = s2, d\<^sub>v = o0\<rparr>} else {})"
    apply (simp)
    apply (clarify)
    by (smt (verit) Collect_cong d_def lens.simps(1) s_def singleton_set_simp t_def)

  have set2: "{sa::state. get\<^bsub>s\<^esub> sa = s2 \<and> get\<^bsub>d\<^esub> sa = o0 \<and> get\<^bsub>t\<^esub> sa = Suc (get\<^bsub>t\<^esub> (fst x)) \<and> get\<^bsub>s\<^esub> (snd x) = s4 \<and> get\<^bsub>d\<^esub> (snd x) = o1 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (get\<^bsub>t\<^esub> sa)}
    = (if get\<^bsub>s\<^esub> (snd x) = s4 \<and> get\<^bsub>d\<^esub> (snd x) = o1 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (Suc (get\<^bsub>t\<^esub> (fst x))) then 
        {\<lparr>t\<^sub>v = Suc (get\<^bsub>t\<^esub> (fst x)), s\<^sub>v = s2, d\<^sub>v = o0\<rparr>} else {})"
    apply (simp)
    apply (clarify)
    by (smt (verit) Collect_cong d_def lens.simps(1) s_def singleton_set_simp t_def)

  have set3: " {sa::state. get\<^bsub>s\<^esub> sa = s3 \<and> get\<^bsub>d\<^esub> sa = o0 \<and> get\<^bsub>t\<^esub> sa = Suc (get\<^bsub>t\<^esub> (fst x)) \<and> get\<^bsub>s\<^esub> (snd x) = s4 \<and> get\<^bsub>d\<^esub> (snd x) = o2 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (get\<^bsub>t\<^esub> sa)}
    = (if get\<^bsub>s\<^esub> (snd x) = s4 \<and> get\<^bsub>d\<^esub> (snd x) = o2 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (Suc (get\<^bsub>t\<^esub> (fst x))) then 
        {\<lparr>t\<^sub>v = Suc (get\<^bsub>t\<^esub> (fst x)), s\<^sub>v = s3, d\<^sub>v = o0\<rparr>} else {})"
    apply (simp)
    apply (clarify)
    by (smt (verit) Collect_cong d_def lens.simps(1) s_def singleton_set_simp t_def)

  have set4: "{sa::state. get\<^bsub>s\<^esub> sa = s3 \<and> get\<^bsub>d\<^esub> sa = o0 \<and> get\<^bsub>t\<^esub> sa = Suc (get\<^bsub>t\<^esub> (fst x)) \<and> get\<^bsub>s\<^esub> (snd x) = s4 \<and> get\<^bsub>d\<^esub> (snd x) = o3 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (get\<^bsub>t\<^esub> sa)}
    = (if get\<^bsub>s\<^esub> (snd x) = s4 \<and> get\<^bsub>d\<^esub> (snd x) = o3 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (Suc (get\<^bsub>t\<^esub> (fst x))) then 
        {\<lparr>t\<^sub>v = Suc (get\<^bsub>t\<^esub> (fst x)), s\<^sub>v = s3, d\<^sub>v = o0\<rparr>} else {})"
    apply (simp)
    apply (clarify)
    by (smt (verit) Collect_cong d_def lens.simps(1) s_def singleton_set_simp t_def)
  
  have f1: "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          (if get\<^bsub>s\<^esub> v\<^sub>0 = s2 \<and> get\<^bsub>d\<^esub> v\<^sub>0 = o0 \<and> get\<^bsub>t\<^esub> v\<^sub>0 = Suc (get\<^bsub>t\<^esub> (fst x)) \<and> 
               get\<^bsub>s\<^esub> (snd x) = s1 \<and> get\<^bsub>d\<^esub> (snd x) = o0 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (get\<^bsub>t\<^esub> v\<^sub>0) then 1::\<real> else (0::\<real>)) * (ureal2real p * ureal2real p) +
            (if get\<^bsub>s\<^esub> v\<^sub>0 = s2 \<and> get\<^bsub>d\<^esub> v\<^sub>0 = o0 \<and> get\<^bsub>t\<^esub> v\<^sub>0 = Suc (get\<^bsub>t\<^esub> (fst x)) \<and> 
               get\<^bsub>s\<^esub> (snd x) = s4 \<and> get\<^bsub>d\<^esub> (snd x) = o1 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (get\<^bsub>t\<^esub> v\<^sub>0) then 1::\<real> else (0::\<real>)) * (ureal2real p * ((1::\<real>) - ureal2real p)) +
           (if get\<^bsub>s\<^esub> v\<^sub>0 = s3 \<and> get\<^bsub>d\<^esub> v\<^sub>0 = o0 \<and> get\<^bsub>t\<^esub> v\<^sub>0 = Suc (get\<^bsub>t\<^esub> (fst x)) \<and>
              get\<^bsub>s\<^esub> (snd x) = s4 \<and> get\<^bsub>d\<^esub> (snd x) = o2 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (get\<^bsub>t\<^esub> v\<^sub>0) then 1::\<real> else (0::\<real>)) * (((1::\<real>) - ureal2real p) * ureal2real p) + 
          (if get\<^bsub>s\<^esub> v\<^sub>0 = s3 \<and> get\<^bsub>d\<^esub> v\<^sub>0 = o0 \<and> get\<^bsub>t\<^esub> v\<^sub>0 = Suc (get\<^bsub>t\<^esub> (fst x)) \<and>
              get\<^bsub>s\<^esub> (snd x) = s4 \<and> get\<^bsub>d\<^esub> (snd x) = o3 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (get\<^bsub>t\<^esub> v\<^sub>0) then 1::\<real> else (0::\<real>)) * (((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p)))"
    apply (rule infsum_cong)
    by simp
  show "?lhs = (if get\<^bsub>s\<^esub> (snd x) = s1 \<and> get\<^bsub>d\<^esub> (snd x) = o0 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (Suc (get\<^bsub>t\<^esub> (fst x))) then 1::\<real> else (0::\<real>)) * ureal2real p * ureal2real p +
       (if get\<^bsub>s\<^esub> (snd x) = s4 \<and> get\<^bsub>d\<^esub> (snd x) = o1 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (Suc (get\<^bsub>t\<^esub> (fst x))) then 1::\<real> else (0::\<real>)) * ureal2real p * ((1::\<real>) - ureal2real p) +
       (if get\<^bsub>s\<^esub> (snd x) = s4 \<and> get\<^bsub>d\<^esub> (snd x) = o2 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (Suc (get\<^bsub>t\<^esub> (fst x))) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ureal2real p +
       (if get\<^bsub>s\<^esub> (snd x) = s4 \<and> get\<^bsub>d\<^esub> (snd x) = o3 \<and> get\<^bsub>t\<^esub> (snd x) = Suc (Suc (get\<^bsub>t\<^esub> (fst x))) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p)"
    apply (simp only: f1)
    apply (subst infsum_constant_finite_states_4)
    apply (simp add: set1)
    apply (simp add: set2)
    apply (simp add: set3)
    apply (simp add: set4)
    by (simp add: set1 set2 set3 set4)
qed

end