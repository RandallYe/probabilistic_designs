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

text \<open> \<close>
datatype S = s1 | s2 | s3 | s4
datatype D = o0 | o1 | o2 | o3

subsubsection \<open> State space \<close>

alphabet state = time +
  s   :: S
  d   :: D

text \<open> The outcome of a flip: its state and outcome may be changed\<close>
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

definition dice_loop :: "ureal \<Rightarrow> state prhfun" where 
"dice_loop p = while\<^sub>p (\<not> s\<^sup>< = s4)\<^sub>e do  loop_body p od"

definition dice :: "ureal \<Rightarrow> state prhfun" where 
"dice p = s := s1 ; d := o0; t := 0; dice_loop p"

definition Ht :: "ureal \<Rightarrow> state rvhfun" where 
"Ht p = (
    \<lbrakk>\<not> s\<^sup>< = s4\<rbrakk>\<^sub>\<I>\<^sub>e * (
      \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o1\<guillemotright> \<and> t\<^sup>> \<ge> t\<^sup>< + 2 \<and> (t\<^sup>> - t\<^sup><) mod 2 = 0\<rbrakk>\<^sub>\<I>\<^sub>e * 
        (ureal2real \<guillemotleft>p\<guillemotright>) ^ ((t\<^sup>> - t\<^sup>< - 2)) * ureal2real \<guillemotleft>p\<guillemotright> * (1 - ureal2real \<guillemotleft>p\<guillemotright>) +
      \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o2\<guillemotright> \<and> t\<^sup>> \<ge> t\<^sup>< + 2 \<and> (t\<^sup>> - t\<^sup><) mod 2 = 0\<rbrakk>\<^sub>\<I>\<^sub>e * 
        (ureal2real \<guillemotleft>p\<guillemotright>) ^ ((t\<^sup>> - t\<^sup>< - 2)) * (1 - ureal2real \<guillemotleft>p\<guillemotright>) * ureal2real \<guillemotleft>p\<guillemotright> +
      \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o3\<guillemotright> \<and> t\<^sup>> \<ge> t\<^sup>< + 2 \<and> (t\<^sup>> - t\<^sup><) mod 2 = 0\<rbrakk>\<^sub>\<I>\<^sub>e * 
        (ureal2real \<guillemotleft>p\<guillemotright>) ^ ((t\<^sup>> - t\<^sup>< - 2)) * (1 - ureal2real \<guillemotleft>p\<guillemotright>) * (1 - ureal2real \<guillemotleft>p\<guillemotright>)
    ) + \<lbrakk>s\<^sup>< = s4 \<and> s\<^sup>> = s\<^sup>< \<and> d\<^sup>> = d\<^sup>< \<and> t\<^sup>> = t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e 
  )\<^sub>e
"

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

lemma singleton_set_finite': "finite {s::state. s\<^sub>v s = s\<^sub>1 \<and> d\<^sub>v s = d\<^sub>1 \<and> t\<^sub>v s = t\<^sub>1}"
  by (simp add: singleton_set_simp)

lemma singleton_set_finite: "finite {s::state. s\<^sub>v s = s\<^sub>1 \<and> d\<^sub>v s = d\<^sub>1 \<and> t\<^sub>v s = t\<^sub>1 \<and> P}"
  apply (rule rev_finite_subset[where B="{s::state. s\<^sub>v s = s\<^sub>1 \<and> d\<^sub>v s = d\<^sub>1 \<and> t\<^sub>v s = t\<^sub>1}"])
  apply (simp add: singleton_set_simp)
  by fastforce

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

lemma loop_body_is_dist: "is_final_distribution (rvfun_of_prfun (loop_body p))"
  apply (simp add: loop_body_altdef dist_defs)
  apply (expr_auto)
             apply (simp add: mult_le_one ureal_lower_bound ureal_upper_bound)
  apply (simp add: ureal_lower_bound ureal_upper_bound)
  apply (simp add: mult_le_one ureal_lower_bound ureal_upper_bound)
  apply (simp add: ureal_lower_bound ureal_upper_bound)
  apply (simp add: mult_le_one ureal_lower_bound ureal_upper_bound)
  apply (simp add: mult_le_one ureal_lower_bound ureal_upper_bound)
  apply (simp add: ureal_lower_bound ureal_upper_bound)
  apply (simp add: mult_le_one ureal_lower_bound ureal_upper_bound)
  apply (simp add: ureal_lower_bound ureal_upper_bound)
  apply (simp add: mult_le_one ureal_lower_bound ureal_upper_bound)
   apply (simp add: mult_le_one ureal_lower_bound ureal_upper_bound)
proof -
  fix t :: "\<nat>"
  have "(\<Sum>\<^sub>\<infinity>s::state.
          (if s\<^sub>v s = s1 \<and> d\<^sub>v s = o0 \<and> t\<^sub>v s = Suc (Suc t) then 1::\<real> else (0::\<real>)) * (ureal2real p * ureal2real p) +
          (if s\<^sub>v s = s4 \<and> d\<^sub>v s = o1 \<and> t\<^sub>v s = Suc (Suc t) then 1::\<real> else (0::\<real>)) * (ureal2real p * ((1::\<real>) - ureal2real p)) +
          (if s\<^sub>v s = s4 \<and> d\<^sub>v s = o2 \<and> t\<^sub>v s = Suc (Suc t) then 1::\<real> else (0::\<real>)) * (((1::\<real>) - ureal2real p) * ureal2real p) +
          (if s\<^sub>v s = s4 \<and> d\<^sub>v s = o3 \<and> t\<^sub>v s = Suc (Suc t) then 1::\<real> else (0::\<real>)) * (((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p))) = 1"
    apply (subst infsum_constant_finite_states_4)
    apply (simp add: singleton_set_simp)+
    by (smt (verit, ccfv_SIG) distrib_left mult.commute mult_cancel_left1)
  then show "(\<Sum>\<^sub>\<infinity>s::state.
          (if s\<^sub>v s = s1 \<and> d\<^sub>v s = o0 \<and> t\<^sub>v s = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p * ureal2real p +
          (if s\<^sub>v s = s4 \<and> d\<^sub>v s = o1 \<and> t\<^sub>v s = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p * ((1::\<real>) - ureal2real p) +
          (if s\<^sub>v s = s4 \<and> d\<^sub>v s = o2 \<and> t\<^sub>v s = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ureal2real p +
          (if s\<^sub>v s = s4 \<and> d\<^sub>v s = o3 \<and> t\<^sub>v s = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p)) = 1"
    by (metis (no_types, lifting) infsum_cong mult.assoc)
qed

lemma loop_body_altdef': "(loop_body p) = prfun_of_rvfun (
    \<lbrakk>s\<^sup>> = \<guillemotleft>s1\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o0\<guillemotright> \<and> t\<^sup>> = t\<^sup>< + 2\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> * ureal2real \<guillemotleft>p\<guillemotright> +
    \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o1\<guillemotright> \<and> t\<^sup>> = t\<^sup>< + 2\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> * (1- ureal2real \<guillemotleft>p\<guillemotright>) +
    \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o2\<guillemotright> \<and> t\<^sup>> = t\<^sup>< + 2\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>) * ureal2real \<guillemotleft>p\<guillemotright> +
    \<lbrakk>s\<^sup>> = \<guillemotleft>s4\<guillemotright> \<and> d\<^sup>> = \<guillemotleft>o3\<guillemotright> \<and> t\<^sup>> = t\<^sup>< + 2\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>) * (1- ureal2real \<guillemotleft>p\<guillemotright>)
  )\<^sub>e"
  by (metis loop_body_altdef prfun_inverse)

lemma Ht_is_fp: "\<F> (\<not> s\<^sup>< = \<guillemotleft>s4\<guillemotright>)\<^sub>e (loop_body p) (prfun_of_rvfun (Ht p)) = prfun_of_rvfun (Ht p)"
  apply (simp add: Ht_def loopfunc_def pskip_def)
  apply (simp only: prfun_pcond_altdef)
  apply (simp add: pseqcomp_def)
  apply (subst rvfun_seqcomp_inverse)
  apply (simp add: loop_body_is_dist)
  using ureal_is_prob apply blast
  apply (subst rvfun_inverse)
  apply (expr_simp_1)
  apply (simp add: is_prob_def)
  apply (pred_auto)
  apply (simp add: ureal_lower_bound ureal_upper_bound)+
  apply (metis ureal2real_mult_dist ureal2real_power_dist ureal_1_minus_real ureal_upper_bound)
  apply (metis ureal2real_mult_dist ureal2real_power_dist ureal_1_minus_real ureal_upper_bound)
  apply (simp add: ureal_lower_bound ureal_upper_bound)
  apply (simp add: ureal_lower_bound ureal_upper_bound)
  apply (metis ureal2real_mult_dist ureal2real_power_dist ureal_1_minus_real ureal_upper_bound)
  apply (metis ureal2real_mult_dist ureal2real_power_dist ureal_1_minus_real ureal_upper_bound)
  apply (simp add: ureal_lower_bound ureal_upper_bound)
  apply (simp add: ureal_lower_bound ureal_upper_bound)
  apply (metis ureal2real_mult_dist ureal2real_power_dist ureal_1_minus_real ureal_upper_bound)
  apply (metis ureal2real_mult_dist ureal2real_power_dist ureal_1_minus_real ureal_upper_bound)
  apply (simp add: loop_body_altdef)
  apply (expr_auto)
  proof -
    fix t::"\<nat>" and s::"S" and d::"D" and t\<^sub>v'::"\<nat>" and s\<^sub>v'::S and d\<^sub>v'::"D"
    have set1: "{s::state. s\<^sub>v s = s1 \<and> d\<^sub>v s = o0 \<and> t\<^sub>v s = Suc (Suc t) \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>)}
      = (if Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>) then {\<lparr>t\<^sub>v = Suc (Suc t), s\<^sub>v = s1, d\<^sub>v = o0\<rparr>} else {})"
      by force
    have set2: "{s::state. s\<^sub>v s = s4 \<and> d\<^sub>v s = o1 \<and> t\<^sub>v s = Suc (Suc t) \<and> t\<^sub>v' = Suc (Suc t)} 
      =  (if t\<^sub>v' = Suc (Suc t) then {\<lparr>t\<^sub>v = Suc (Suc t), s\<^sub>v = s4, d\<^sub>v = o1\<rparr>} else {})"
      by auto
    have set3: "{s::state. s\<^sub>v s = s4 \<and> d\<^sub>v s = o2 \<and> t\<^sub>v s = Suc (Suc t) \<and> t\<^sub>v' = Suc (Suc t)} 
      =  (if t\<^sub>v' = Suc (Suc t) then {\<lparr>t\<^sub>v = Suc (Suc t), s\<^sub>v = s4, d\<^sub>v = o2\<rparr>} else {})"
      by auto
    have set4: "{s::state. s\<^sub>v s = s4 \<and> d\<^sub>v s = o3 \<and> t\<^sub>v s = Suc (Suc t) \<and> t\<^sub>v' = Suc (Suc t)} 
      =  (if t\<^sub>v' = Suc (Suc t) then {\<lparr>t\<^sub>v = Suc (Suc t), s\<^sub>v = s4, d\<^sub>v = o3\<rparr>} else {})"
      by auto
    have f1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if s\<^sub>v v\<^sub>0 = s1 \<and> d\<^sub>v v\<^sub>0 = o0 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p * ureal2real p +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o1 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p * ((1::\<real>) - ureal2real p) +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o2 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ureal2real p +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o3 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p)) *
          ( 
            (if \<not> s\<^sub>v v\<^sub>0 = s4 then 1::\<real> else (0::\<real>)) *
            ( 
              (if Suc (Suc (t\<^sub>v v\<^sub>0)) \<le> t\<^sub>v' \<and> (t\<^sub>v' - t\<^sub>v v\<^sub>0) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
              (ureal2real p) ^ (t\<^sub>v' - Suc (Suc (t\<^sub>v v\<^sub>0))) * ureal2real p * ((1::\<real>) - ureal2real p)
            ) +
            (if s\<^sub>v v\<^sub>0 = s4 \<and> s4 = s\<^sub>v v\<^sub>0 \<and> o1 = d\<^sub>v v\<^sub>0 \<and> t\<^sub>v' = t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>))
          )
        ) = 
        (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if s\<^sub>v v\<^sub>0 = s1 \<and> d\<^sub>v v\<^sub>0 = o0 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>) 
            then 1::\<real> else (0::\<real>)) * (ureal2real p * ureal2real p *(ureal2real p) ^ (t\<^sub>v' - Suc (Suc (Suc (Suc t)))) * ureal2real p * ((1::\<real>) - ureal2real p)) +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o1 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) \<and> t\<^sub>v' = Suc (Suc t) then 1::\<real> else (0::\<real>)) * (ureal2real p * ((1::\<real>) - ureal2real p)))
        )
        "
      apply (rule infsum_cong)
      by fastforce
    have f1': "... = real (card {s::state. s\<^sub>v s = s1 \<and> d\<^sub>v s = o0 \<and> t\<^sub>v s = Suc (Suc t) \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>)}) *
        ((ureal2real p) ^ (t\<^sub>v' - (Suc (Suc t))) * ureal2real p * ((1::\<real>) - ureal2real p)) +
      real (card {s::state. s\<^sub>v s = s4 \<and> d\<^sub>v s = o1 \<and> t\<^sub>v s = Suc (Suc t) \<and> t\<^sub>v' = Suc (Suc t)}) * (ureal2real p * ((1::\<real>) - ureal2real p))"
      apply (subst infsum_constant_finite_states_cmult_2)
      apply (rule rev_finite_subset[where B="{s::state. s\<^sub>v s = s1 \<and> d\<^sub>v s = o0 \<and> t\<^sub>v s = Suc (Suc t)}"])
      apply (simp add: singleton_set_simp)
      apply auto
      apply (rule rev_finite_subset[where B="{s::state. s\<^sub>v s = s4 \<and> d\<^sub>v s = o1 \<and> t\<^sub>v s = Suc (Suc t)}"])
      apply (simp add: singleton_set_simp)
       apply auto
      by (metis (no_types, lifting) Suc_diff_Suc Suc_le_eq Suc_lessD card.empty less_numeral_extra(3) mult.assoc power_Suc set1)
  
    have f2: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if s\<^sub>v v\<^sub>0 = s1 \<and> d\<^sub>v v\<^sub>0 = o0 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p * ureal2real p +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o1 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p * ((1::\<real>) - ureal2real p) +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o2 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ureal2real p +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o3 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p)) *
          ((if \<not> s\<^sub>v v\<^sub>0 = s4 then 1::\<real> else (0::\<real>)) *
           ((if Suc (Suc (t\<^sub>v v\<^sub>0)) \<le> t\<^sub>v' \<and> (t\<^sub>v' - t\<^sub>v v\<^sub>0) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) * ureal2real p ^ (t\<^sub>v' - Suc (Suc (t\<^sub>v v\<^sub>0))) * ((1::\<real>) - ureal2real p) *
            ureal2real p) +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> s4 = s\<^sub>v v\<^sub>0 \<and> o2 = d\<^sub>v v\<^sub>0 \<and> t\<^sub>v' = t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)))) =
        (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if s\<^sub>v v\<^sub>0 = s1 \<and> d\<^sub>v v\<^sub>0 = o0 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>) 
            then 1::\<real> else (0::\<real>)) * (ureal2real p * ureal2real p *(ureal2real p) ^ (t\<^sub>v' - Suc (Suc (Suc (Suc t))))  * ((1::\<real>) - ureal2real p) * ureal2real p) +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o2 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) \<and> t\<^sub>v' = Suc (Suc t) then 1::\<real> else (0::\<real>)) * (((1::\<real>) - ureal2real p) * ureal2real p))
        )"
      apply (rule infsum_cong)
      by fastforce
    have f2': "... = real (card {s::state. s\<^sub>v s = s1 \<and> d\<^sub>v s = o0 \<and> t\<^sub>v s = Suc (Suc t) \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>)}) *
        ((ureal2real p) ^ (t\<^sub>v' - (Suc (Suc t))) * ((1::\<real>) - ureal2real p) * ureal2real p) +
      real (card {s::state. s\<^sub>v s = s4 \<and> d\<^sub>v s = o2 \<and> t\<^sub>v s = Suc (Suc t) \<and> t\<^sub>v' = Suc (Suc t)}) * (((1::\<real>) - ureal2real p) * ureal2real p)"
      apply (subst infsum_constant_finite_states_cmult_2)
      apply (rule rev_finite_subset[where B="{s::state. s\<^sub>v s = s1 \<and> d\<^sub>v s = o0 \<and> t\<^sub>v s = Suc (Suc t)}"])
      apply (simp add: singleton_set_simp)
      apply auto
      apply (rule rev_finite_subset[where B="{s::state. s\<^sub>v s = s4 \<and> d\<^sub>v s = o2 \<and> t\<^sub>v s = Suc (Suc t)}"])
      apply (simp add: singleton_set_simp)
      apply auto
      by (metis (no_types, lifting) Suc_diff_Suc Suc_le_eq Suc_lessD card.empty less_numeral_extra(3) mult.assoc power_Suc set1)
    have f3: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if s\<^sub>v v\<^sub>0 = s1 \<and> d\<^sub>v v\<^sub>0 = o0 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p * ureal2real p +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o1 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p * ((1::\<real>) - ureal2real p) +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o2 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ureal2real p +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o3 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p)) *
          ((if \<not> s\<^sub>v v\<^sub>0 = s4 then 1::\<real> else (0::\<real>)) *
           ((if Suc (Suc (t\<^sub>v v\<^sub>0)) \<le> t\<^sub>v' \<and> (t\<^sub>v' - t\<^sub>v v\<^sub>0) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) * ureal2real p ^ (t\<^sub>v' - Suc (Suc (t\<^sub>v v\<^sub>0))) * ((1::\<real>) - ureal2real p) *
            ((1::\<real>) - ureal2real p)) +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> s4 = s\<^sub>v v\<^sub>0 \<and> o3 = d\<^sub>v v\<^sub>0 \<and> t\<^sub>v' = t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)))) = 
        (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if s\<^sub>v v\<^sub>0 = s1 \<and> d\<^sub>v v\<^sub>0 = o0 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>) 
            then 1::\<real> else (0::\<real>)) * (ureal2real p * ureal2real p *(ureal2real p) ^ (t\<^sub>v' - Suc (Suc (Suc (Suc t))))  * ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p)) +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o3 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) \<and> t\<^sub>v' = Suc (Suc t) then 1::\<real> else (0::\<real>)) * (((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p)))
        )"
      apply (rule infsum_cong)
      by fastforce
    have f3': "... = real (card {s::state. s\<^sub>v s = s1 \<and> d\<^sub>v s = o0 \<and> t\<^sub>v s = Suc (Suc t) \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>)}) *
        ((ureal2real p) ^ (t\<^sub>v' - (Suc (Suc t))) * ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p)) +
      real (card {s::state. s\<^sub>v s = s4 \<and> d\<^sub>v s = o3 \<and> t\<^sub>v s = Suc (Suc t) \<and> t\<^sub>v' = Suc (Suc t)}) * (((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p))"
      apply (subst infsum_constant_finite_states_cmult_2)
      apply (rule rev_finite_subset[where B="{s::state. s\<^sub>v s = s1 \<and> d\<^sub>v s = o0 \<and> t\<^sub>v s = Suc (Suc t)}"])
      apply (simp add: singleton_set_simp)
      apply auto
      apply (rule rev_finite_subset[where B="{s::state. s\<^sub>v s = s4 \<and> d\<^sub>v s = o3 \<and> t\<^sub>v s = Suc (Suc t)}"])
      apply (simp add: singleton_set_simp)
      apply auto
      by (metis (no_types, lifting) Suc_diff_Suc Suc_le_eq Suc_lessD card.empty less_numeral_extra(3) mult.assoc power_Suc set1)
  
    have f4: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if s\<^sub>v v\<^sub>0 = s1 \<and> d\<^sub>v v\<^sub>0 = o0 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p * ureal2real p +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o1 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p * ((1::\<real>) - ureal2real p) +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o2 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ureal2real p +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o3 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p)) *
          ((if \<not> s\<^sub>v v\<^sub>0 = s4 then 1::\<real> else (0::\<real>)) *
           ((if s\<^sub>v' = s4 \<and> d\<^sub>v' = o1 \<and> Suc (Suc (t\<^sub>v v\<^sub>0)) \<le> t\<^sub>v' \<and> (t\<^sub>v' - t\<^sub>v v\<^sub>0) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) * ureal2real p ^ (t\<^sub>v' - Suc (Suc (t\<^sub>v v\<^sub>0))) *
            ureal2real p * ((1::\<real>) - ureal2real p) +
            (if s\<^sub>v' = s4 \<and> d\<^sub>v' = o2 \<and> Suc (Suc (t\<^sub>v v\<^sub>0)) \<le> t\<^sub>v' \<and> (t\<^sub>v' - t\<^sub>v v\<^sub>0) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) * ureal2real p ^ (t\<^sub>v' - Suc (Suc (t\<^sub>v v\<^sub>0))) *
            ((1::\<real>) - ureal2real p) *  ureal2real p +
            (if s\<^sub>v' = s4 \<and> d\<^sub>v' = o3 \<and> Suc (Suc (t\<^sub>v v\<^sub>0)) \<le> t\<^sub>v' \<and> (t\<^sub>v' - t\<^sub>v v\<^sub>0) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) * ureal2real p ^ (t\<^sub>v' - Suc (Suc (t\<^sub>v v\<^sub>0))) *
            ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p)) +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> s\<^sub>v' = s\<^sub>v v\<^sub>0 \<and> d\<^sub>v' = d\<^sub>v v\<^sub>0 \<and> t\<^sub>v' = t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)))) = 
          (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if s\<^sub>v v\<^sub>0 = s1 \<and> d\<^sub>v v\<^sub>0 = o0 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p * ureal2real p +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o1 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p * ((1::\<real>) - ureal2real p) +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o2 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ureal2real p +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o3 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p)) *
          ((if \<not> s\<^sub>v v\<^sub>0 = s4 then 1::\<real> else (0::\<real>)) *
           ((if s\<^sub>v' = s4 \<and> d\<^sub>v' = o1 \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) * ureal2real p ^ (t\<^sub>v' - Suc (Suc (t\<^sub>v v\<^sub>0))) *
            ureal2real p * ((1::\<real>) - ureal2real p) +
            (if s\<^sub>v' = s4 \<and> d\<^sub>v' = o2 \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) * ureal2real p ^ (t\<^sub>v' - Suc (Suc (t\<^sub>v v\<^sub>0))) *
            ((1::\<real>) - ureal2real p) *  ureal2real p +
            (if s\<^sub>v' = s4 \<and> d\<^sub>v' = o3 \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) * ureal2real p ^ (t\<^sub>v' - Suc (Suc (t\<^sub>v v\<^sub>0))) *
            ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p)) +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> s\<^sub>v' = s\<^sub>v v\<^sub>0 \<and> d\<^sub>v' = d\<^sub>v v\<^sub>0 \<and> t\<^sub>v' = Suc (Suc t) then 1::\<real> else (0::\<real>))))"
        apply (rule infsum_cong)
      by auto
  (*
      have " ... =
        (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if s\<^sub>v v\<^sub>0 = s1 \<and> d\<^sub>v v\<^sub>0 = o0 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) \<and> s\<^sub>v' = s4 \<and> d\<^sub>v' = o1 \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>) 
            then 1::\<real> else (0::\<real>)) * ureal2real p ^ (t\<^sub>v' - Suc (Suc (t))) * ureal2real p * ((1::\<real>) - ureal2real p) +
           (if s\<^sub>v v\<^sub>0 = s1 \<and> d\<^sub>v v\<^sub>0 = o0 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) \<and> s\<^sub>v' = s4 \<and> d\<^sub>v' = o2 \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>) 
            then 1::\<real> else (0::\<real>)) * ureal2real p ^ (t\<^sub>v' - Suc (Suc (t))) * ((1::\<real>) - ureal2real p) * ureal2real p +
           (if s\<^sub>v v\<^sub>0 = s1 \<and> d\<^sub>v v\<^sub>0 = o0 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) \<and> s\<^sub>v' = s4 \<and> d\<^sub>v' = o3 \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>) 
            then 1::\<real> else (0::\<real>)) * ureal2real p ^ (t\<^sub>v' - Suc (Suc (t))) * ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p) +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o1 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) \<and> s\<^sub>v' = s\<^sub>v v\<^sub>0 \<and> d\<^sub>v' = d\<^sub>v v\<^sub>0 \<and> t\<^sub>v' = t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p * ((1::\<real>) - ureal2real p) +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o2 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) \<and> s\<^sub>v' = s\<^sub>v v\<^sub>0 \<and> d\<^sub>v' = d\<^sub>v v\<^sub>0 \<and> t\<^sub>v' = t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ureal2real p +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o3 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) \<and> s\<^sub>v' = s\<^sub>v v\<^sub>0 \<and> d\<^sub>v' = d\<^sub>v v\<^sub>0 \<and> t\<^sub>v' = t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p)))"
      apply (rule infsum_cong)
        by presburger
  *)
  
    have mod_not: "(Suc (Suc t) \<le> t\<^sub>v' \<and> (t\<^sub>v' - t) mod (2::\<nat>) = Suc (0::\<nat>)) \<longrightarrow> \<not>(t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>)"
      apply auto
      by (simp add: mod2_eq_if)
  
    have mod_not': "(Suc (Suc t) \<le> t\<^sub>v' \<and> (t\<^sub>v' - t) mod (2::\<nat>) = Suc (0::\<nat>)) \<longrightarrow> \<not>t\<^sub>v' = Suc (Suc t)"
      by auto
  
    show "prfun_of_rvfun
          (\<lambda>\<s>::state \<times> state.
              (if \<not> s\<^sub>v (fst \<s>) = s4 then 1::\<real> else (0::\<real>)) *
              (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
                 ((if s\<^sub>v v\<^sub>0 = s1 \<and> d\<^sub>v v\<^sub>0 = o0 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc (t\<^sub>v (fst \<s>))) then 1::\<real> else (0::\<real>)) * ureal2real p * ureal2real p +
                  (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o1 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc (t\<^sub>v (fst \<s>))) then 1::\<real> else (0::\<real>)) * ureal2real p * ((1::\<real>) - ureal2real p) +
                  (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o2 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc (t\<^sub>v (fst \<s>))) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ureal2real p +
                  (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o3 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc (t\<^sub>v (fst \<s>))) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p)) *
                 ((if \<not> s\<^sub>v v\<^sub>0 = s4 then 1::\<real> else (0::\<real>)) *
                  ((if s\<^sub>v (snd \<s>) = s4 \<and> d\<^sub>v (snd \<s>) = o1 \<and> Suc (Suc (t\<^sub>v v\<^sub>0)) \<le> t\<^sub>v (snd \<s>) \<and> (t\<^sub>v (snd \<s>) - t\<^sub>v v\<^sub>0) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
                   ureal2real p ^ (t\<^sub>v (snd \<s>) - Suc (Suc (t\<^sub>v v\<^sub>0))) *
                   ureal2real p *
                   ((1::\<real>) - ureal2real p) +
                   (if s\<^sub>v (snd \<s>) = s4 \<and> d\<^sub>v (snd \<s>) = o2 \<and> Suc (Suc (t\<^sub>v v\<^sub>0)) \<le> t\<^sub>v (snd \<s>) \<and> (t\<^sub>v (snd \<s>) - t\<^sub>v v\<^sub>0) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
                   ureal2real p ^ (t\<^sub>v (snd \<s>) - Suc (Suc (t\<^sub>v v\<^sub>0))) *
                   ((1::\<real>) - ureal2real p) *
                   ureal2real p +
                   (if s\<^sub>v (snd \<s>) = s4 \<and> d\<^sub>v (snd \<s>) = o3 \<and> Suc (Suc (t\<^sub>v v\<^sub>0)) \<le> t\<^sub>v (snd \<s>) \<and> (t\<^sub>v (snd \<s>) - t\<^sub>v v\<^sub>0) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
                   ureal2real p ^ (t\<^sub>v (snd \<s>) - Suc (Suc (t\<^sub>v v\<^sub>0))) *
                   ((1::\<real>) - ureal2real p) *
                   ((1::\<real>) - ureal2real p)) +
                  (if s\<^sub>v v\<^sub>0 = s4 \<and> s\<^sub>v (snd \<s>) = s\<^sub>v v\<^sub>0 \<and> d\<^sub>v (snd \<s>) = d\<^sub>v v\<^sub>0 \<and> t\<^sub>v (snd \<s>) = t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)))) +
              (if s\<^sub>v (fst \<s>) = s4 then 1::\<real> else (0::\<real>)) * rvfun_of_prfun (prfun_of_rvfun (\<lambda>\<s>::state \<times> state. if II \<s> then 1::\<real> else (0::\<real>))) \<s>)
          (\<lparr>t\<^sub>v = t, s\<^sub>v = s, d\<^sub>v = d\<rparr>, \<lparr>t\<^sub>v = t\<^sub>v', s\<^sub>v = s\<^sub>v', d\<^sub>v = d\<^sub>v'\<rparr>) =
         prfun_of_rvfun
          (\<lambda>\<s>::state \<times> state.
              (if \<not> s\<^sub>v (fst \<s>) = s4 then 1::\<real> else (0::\<real>)) *
              ((if s\<^sub>v (snd \<s>) = s4 \<and> d\<^sub>v (snd \<s>) = o1 \<and> Suc (Suc (t\<^sub>v (fst \<s>))) \<le> t\<^sub>v (snd \<s>) \<and> (t\<^sub>v (snd \<s>) - t\<^sub>v (fst \<s>)) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
               ureal2real p ^ (t\<^sub>v (snd \<s>) - Suc (Suc (t\<^sub>v (fst \<s>)))) *
               ureal2real p *
               ((1::\<real>) - ureal2real p) +
               (if s\<^sub>v (snd \<s>) = s4 \<and> d\<^sub>v (snd \<s>) = o2 \<and> Suc (Suc (t\<^sub>v (fst \<s>))) \<le> t\<^sub>v (snd \<s>) \<and> (t\<^sub>v (snd \<s>) - t\<^sub>v (fst \<s>)) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
               ureal2real p ^ (t\<^sub>v (snd \<s>) - Suc (Suc (t\<^sub>v (fst \<s>)))) *
               ((1::\<real>) - ureal2real p) *
               ureal2real p +
               (if s\<^sub>v (snd \<s>) = s4 \<and> d\<^sub>v (snd \<s>) = o3 \<and> Suc (Suc (t\<^sub>v (fst \<s>))) \<le> t\<^sub>v (snd \<s>) \<and> (t\<^sub>v (snd \<s>) - t\<^sub>v (fst \<s>)) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
               ureal2real p ^ (t\<^sub>v (snd \<s>) - Suc (Suc (t\<^sub>v (fst \<s>)))) *
               ((1::\<real>) - ureal2real p) *
               ((1::\<real>) - ureal2real p)) +
              (if s\<^sub>v (fst \<s>) = s4 \<and> s\<^sub>v (snd \<s>) = s\<^sub>v (fst \<s>) \<and> d\<^sub>v (snd \<s>) = d\<^sub>v (fst \<s>) \<and> t\<^sub>v (snd \<s>) = t\<^sub>v (fst \<s>) then 1::\<real> else (0::\<real>)))
          (\<lparr>t\<^sub>v = t, s\<^sub>v = s, d\<^sub>v = d\<rparr>, \<lparr>t\<^sub>v = t\<^sub>v', s\<^sub>v = s\<^sub>v', d\<^sub>v = d\<^sub>v'\<rparr>)"
      apply (simp add: prfun_of_rvfun_def)
      apply (rule conjI)
      apply clarsimp
      apply (rule conjI, rule impI)
      apply (simp only: f1 f1' set1 set2)
      apply (cases "Suc (Suc t) = t\<^sub>v'")
      apply force
      apply (smt (verit, ccfv_threshold) One_nat_def card.empty card_1_singleton_iff even_add even_diff_nat even_iff_mod_2_eq_zero le_antisym mult_cancel_left1 mult_cancel_right1 not_less_eq_eq odd_one of_nat_0 of_nat_1 plus_1_eq_Suc)
      apply (simp add: rvfun_of_prfun_def)
      apply (pred_auto)
      using ureal2real_inverse apply blast+
      apply (rule impI, rule conjI)+
      apply clarsimp
      apply (simp only: f2 f2' set1 set3)
      apply (cases "Suc (Suc t) = t\<^sub>v'")
      apply force
      apply (smt (verit, ccfv_threshold) One_nat_def card.empty card_1_singleton_iff even_add even_diff_nat even_iff_mod_2_eq_zero le_antisym mult_cancel_left1 mult_cancel_right1 not_less_eq_eq odd_one of_nat_0 of_nat_1 plus_1_eq_Suc)
      apply (simp add: rvfun_of_prfun_def)
      apply (pred_auto)
      using ureal2real_inverse apply blast+
      apply (rule impI, rule conjI)+
      apply clarsimp
      apply (simp only: f3 f3' set1 set4)
      apply (cases "Suc (Suc t) = t\<^sub>v'")
      apply force
      apply (smt (verit, ccfv_threshold) One_nat_def card.empty card_1_singleton_iff even_add even_diff_nat even_iff_mod_2_eq_zero le_antisym mult_cancel_left1 mult_cancel_right1 not_less_eq_eq odd_one of_nat_0 of_nat_1 plus_1_eq_Suc)
      apply (simp add: rvfun_of_prfun_def)
      apply (pred_auto)
      using ureal2real_inverse apply blast+
      apply (rule impI, rule conjI)+
      apply clarsimp
      defer
      apply clarsimp
      apply (rule conjI)
      apply (simp add: rvfun_of_prfun_def)
      apply pred_auto
      using ureal2real_inverse apply blast+
      apply (simp add: rvfun_of_prfun_def)
      apply (rule conjI)
      apply pred_auto
      apply (rule impI)+
      using ureal2real_inverse apply blast+
      apply (simp only: f4)
      proof -
        assume a1: "Suc (Suc t) \<le> t\<^sub>v' \<longrightarrow> d\<^sub>v' = o1 \<longrightarrow> s\<^sub>v' = s4 \<longrightarrow> (t\<^sub>v' - t) mod (2::\<nat>) = Suc (0::\<nat>)"
        assume a2: "Suc (Suc t) \<le> t\<^sub>v' \<longrightarrow> d\<^sub>v' = o2 \<longrightarrow> s\<^sub>v' = s4 \<longrightarrow> (t\<^sub>v' - t) mod (2::\<nat>) = Suc (0::\<nat>)"
        assume a3: "Suc (Suc t) \<le> t\<^sub>v' \<longrightarrow> d\<^sub>v' = o3 \<longrightarrow> s\<^sub>v' = s4 \<longrightarrow> (t\<^sub>v' - t) mod (2::\<nat>) = Suc (0::\<nat>)"
        from a1 have f51: "\<not> (s\<^sub>v' = s4 \<and> d\<^sub>v' = o1 \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>))"
          using Suc_leD mod_not by presburger
        from a2 have f52: "\<not> (s\<^sub>v' = s4 \<and> d\<^sub>v' = o2 \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>))"
          using Suc_leD mod_not by presburger
        from a3 have f53: "\<not> (s\<^sub>v' = s4 \<and> d\<^sub>v' = o3 \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>))"
          using Suc_leD mod_not by presburger
        have f54: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
            ((if s\<^sub>v v\<^sub>0 = s1 \<and> d\<^sub>v v\<^sub>0 = o0 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p * ureal2real p +
             (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o1 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p * ((1::\<real>) - ureal2real p) +
             (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o2 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ureal2real p +
             (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o3 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p)) *
            ((if \<not> s\<^sub>v v\<^sub>0 = s4 then 1::\<real> else (0::\<real>)) *
             ((if s\<^sub>v' = s4 \<and> d\<^sub>v' = o1 \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
              ureal2real p ^ (t\<^sub>v' - Suc (Suc (t\<^sub>v v\<^sub>0))) *
              ureal2real p *
              ((1::\<real>) - ureal2real p) +
              (if s\<^sub>v' = s4 \<and> d\<^sub>v' = o2 \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
              ureal2real p ^ (t\<^sub>v' - Suc (Suc (t\<^sub>v v\<^sub>0))) *
              ((1::\<real>) - ureal2real p) *
              ureal2real p +
              (if s\<^sub>v' = s4 \<and> d\<^sub>v' = o3 \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
              ureal2real p ^ (t\<^sub>v' - Suc (Suc (t\<^sub>v v\<^sub>0))) *
              ((1::\<real>) - ureal2real p) *
              ((1::\<real>) - ureal2real p)) +
             (if s\<^sub>v v\<^sub>0 = s4 \<and> s\<^sub>v' = s\<^sub>v v\<^sub>0 \<and> d\<^sub>v' = d\<^sub>v v\<^sub>0 \<and> t\<^sub>v' = Suc (Suc t) then 1::\<real> else (0::\<real>)))) = 
            (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
            ((if s\<^sub>v v\<^sub>0 = s1 \<and> d\<^sub>v v\<^sub>0 = o0 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p * ureal2real p +
             (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o1 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p * ((1::\<real>) - ureal2real p) +
             (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o2 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ureal2real p +
             (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o3 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p)) *
            ((if s\<^sub>v v\<^sub>0 = s4 \<and> s\<^sub>v' = s\<^sub>v v\<^sub>0 \<and> d\<^sub>v' = d\<^sub>v v\<^sub>0 \<and> t\<^sub>v' = Suc (Suc t) then 1::\<real> else (0::\<real>))))"
          apply (rule infsum_cong)
          using a1 a2 a3 f51 f52 f53 by (smt (verit, ccfv_threshold) mult_eq_0_iff)
        have f55: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
            (
             (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o1 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) \<and> s\<^sub>v' = s4 \<and> d\<^sub>v' = o1 \<and> t\<^sub>v' = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p * ((1::\<real>) - ureal2real p) +
             (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o2 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) \<and> s\<^sub>v' = s4 \<and> d\<^sub>v' = o2 \<and> t\<^sub>v' = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ureal2real p +
             (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o3 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) \<and> s\<^sub>v' = s4 \<and> d\<^sub>v' = o3 \<and> t\<^sub>v' = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p))
            )"
          apply (rule infsum_cong)
          by (smt (verit, del_insts) S.distinct(5) a1 a2 a3 le_Suc_eq mod_not' mult_cancel_left mult_cancel_right1)
        have f56: "... = 0"
          by (smt (verit) a1 a2 a3 infsum_0 le_Suc_eq mod_not' mult_cancel_left1)
        show "real2ureal
         (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
            ((if s\<^sub>v v\<^sub>0 = s1 \<and> d\<^sub>v v\<^sub>0 = o0 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p * ureal2real p +
             (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o1 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p * ((1::\<real>) - ureal2real p) +
             (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o2 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ureal2real p +
             (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o3 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p)) *
            ((if \<not> s\<^sub>v v\<^sub>0 = s4 then 1::\<real> else (0::\<real>)) *
             ((if s\<^sub>v' = s4 \<and> d\<^sub>v' = o1 \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
              ureal2real p ^ (t\<^sub>v' - Suc (Suc (t\<^sub>v v\<^sub>0))) *
              ureal2real p *
              ((1::\<real>) - ureal2real p) +
              (if s\<^sub>v' = s4 \<and> d\<^sub>v' = o2 \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
              ureal2real p ^ (t\<^sub>v' - Suc (Suc (t\<^sub>v v\<^sub>0))) *
              ((1::\<real>) - ureal2real p) *
              ureal2real p +
              (if s\<^sub>v' = s4 \<and> d\<^sub>v' = o3 \<and> Suc (Suc (Suc (Suc t))) \<le> t\<^sub>v' \<and> (t\<^sub>v' - Suc (Suc t)) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
              ureal2real p ^ (t\<^sub>v' - Suc (Suc (t\<^sub>v v\<^sub>0))) *
              ((1::\<real>) - ureal2real p) *
              ((1::\<real>) - ureal2real p)) +
             (if s\<^sub>v v\<^sub>0 = s4 \<and> s\<^sub>v' = s\<^sub>v v\<^sub>0 \<and> d\<^sub>v' = d\<^sub>v v\<^sub>0 \<and> t\<^sub>v' = Suc (Suc t) then 1::\<real> else (0::\<real>)))) =
          real2ureal (0::\<real>)"
          using f51 f52 f53 f54 f55 f56 by presburger
      qed
    qed

lemma loop_body_iterdiff_simp:
  shows "(iter\<^sub>d 0 (\<not> s\<^sup>< = s4)\<^sub>e (loop_body p) 1\<^sub>p) = 1\<^sub>p"
        "(iter\<^sub>d (n+1) (\<not> s\<^sup>< = s4)\<^sub>e (loop_body p) 1\<^sub>p) =  prfun_of_rvfun ((\<lbrakk>\<not> s\<^sup>< = s4\<rbrakk>\<^sub>\<I>\<^sub>e * 
            (ureal2real \<guillemotleft>p\<guillemotright>)^\<guillemotleft>2*n\<guillemotright>)\<^sub>e)"
proof -
  show "(iter\<^sub>d 0 (\<not> s\<^sup>< = s4)\<^sub>e (loop_body p) 1\<^sub>p) = 1\<^sub>p"
    by auto
  show "(iter\<^sub>d (n+1) (\<not> s\<^sup>< = s4)\<^sub>e (loop_body p) 1\<^sub>p) =  prfun_of_rvfun ((\<lbrakk>\<not> s\<^sup>< = s4\<rbrakk>\<^sub>\<I>\<^sub>e * (ureal2real \<guillemotleft>p\<guillemotright>)^\<guillemotleft>2*n\<guillemotright>)\<^sub>e)"
    apply (induction n)
    apply (simp)
    apply (subst prfun_seqcomp_one)
    using loop_body_is_dist apply auto[1]
    apply (simp add: pfun_defs)
    apply (subst ureal_zero)
    apply (subst ureal_one)
    apply (simp add: prfun_of_rvfun_def)
    apply (pred_auto)
    apply (simp only: add_Suc)
    apply (simp only: iterdiff.simps(2))
    apply (simp only: pcond_def)
    apply (simp only: pseqcomp_def)
    apply (subst rvfun_seqcomp_inverse)
    using loop_body_is_dist apply auto[1]
    apply (simp add: ureal_is_prob)
    apply (subst rvfun_inverse)
    apply (expr_auto add: dist_defs)
    apply (simp add: mult_le_one power_le_one ureal_lower_bound ureal_upper_bound)
    apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
    apply (simp only: loop_body_altdef)
    apply (expr_auto)
    defer
    apply (simp add: pzero_def rvfun_of_prfun_def ureal2real_0)
  proof -
    fix n::"\<nat>" and t::"\<nat>" and s::"S"
    let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if s\<^sub>v v\<^sub>0 = s1 \<and> d\<^sub>v v\<^sub>0 = o0 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p * ureal2real p +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o1 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ureal2real p *
           ((1::\<real>) - ureal2real p) +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o2 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) *
           ureal2real p +
           (if s\<^sub>v v\<^sub>0 = s4 \<and> d\<^sub>v v\<^sub>0 = o3 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p) *
           ((1::\<real>) - ureal2real p)) *
          ((if \<not> s\<^sub>v v\<^sub>0 = s4 then 1::\<real> else (0::\<real>)) * (ureal2real p) ^ ((2::\<nat>) * n)))"
    have f1: "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state. ((if s\<^sub>v v\<^sub>0 = s1 \<and> d\<^sub>v v\<^sub>0 = o0 \<and> t\<^sub>v v\<^sub>0 = Suc (Suc t) then 1::\<real> else (0::\<real>)) * 
            (ureal2real p *ureal2real p * (ureal2real p) ^ ((2::\<nat>) * n))))"
      apply (rule infsum_cong)
      by auto
    then have f2: "... = (ureal2real p * ureal2real p * (ureal2real p) ^ ((2::\<nat>) * n))"
      apply (subst infsum_constant_finite_states_cmult_1)
      using singleton_set_finite' apply blast
      by (simp add: singleton_set_simp)
    show "?lhs = ureal2real p * (ureal2real p * ureal2real p ^ ((2::\<nat>) * n))"
      by (simp only: f1 f2)
  qed
qed

lemma loop_body_iterdiff_tendsto_0:
  assumes "p < 1"
  shows "\<forall>s::state \<times> state. (\<lambda>n::\<nat>. ureal2real (iter\<^sub>d n (\<not> s\<^sup>< = s4)\<^sub>e (loop_body p) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
proof 
  fix s
  have "(\<lambda>n::\<nat>. ureal2real (iterdiff (n+1) (\<not> s\<^sup>< = s4)\<^sub>e (loop_body p) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    apply (subst loop_body_iterdiff_simp)
    apply (simp add: prfun_of_rvfun_def)
    apply (expr_auto)
    apply (subst real2ureal_inverse)
    apply (simp add: ureal_upper_bound)
    apply (simp add: power_le_one ureal_lower_bound ureal_upper_bound)
    apply (subgoal_tac "(\<lambda>n::\<nat>. (ureal2real p ^ 2) ^ n) \<longlonglongrightarrow> (0::\<real>)")
    apply (simp add: power_mult)
    apply (subst LIMSEQ_realpow_zero)
    using zero_le_power2 apply blast
    using assms
    apply (metis abs_square_less_1 less_eq_real_def linorder_not_less real_sqrt_abs real_sqrt_unique ureal2real_mono_strict ureal_lower_bound ureal_upper_bound)
    apply (simp)
    by (simp add: real2ureal_inverse)
  then show "(\<lambda>n::\<nat>. ureal2real (iter\<^sub>d n (\<not> s\<^sup>< = s4)\<^sub>e (loop_body p) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    by (rule LIMSEQ_offset[where k = 1])
qed

theorem dice_loop_simp: 
  assumes "p < 1"
  shows "dice_loop p = prfun_of_rvfun (Ht p)"
  apply (simp add: dice_loop_def)
  apply (subst unique_fixed_point_lfp_gfp_finite_final'[where fp = "prfun_of_rvfun (Ht p)"])
  apply (simp add: loop_body_is_dist)
  apply (simp add: loop_body_altdef')
  apply (simp add: rvfun_ge_zero)
  apply pred_auto
  prefer 3
  using Ht_is_fp apply presburger
  prefer 3
  apply simp
  defer
  using assms loop_body_iterdiff_tendsto_0 apply blast
proof -
  fix t :: "nat"
  let ?lhs = "{s'::state.
         (s\<^sub>v s' = s1 \<and> d\<^sub>v s' = o0 \<and> t\<^sub>v s' = Suc (Suc t) \<longrightarrow> (0::\<real>) < ureal2real p * ureal2real p) \<and>
         (
            (d\<^sub>v s' = o0 \<longrightarrow> s\<^sub>v s' = s1 \<longrightarrow> \<not> t\<^sub>v s' = Suc (Suc t)) \<longrightarrow>
            (s\<^sub>v s' = s4 \<and> d\<^sub>v s' = o1 \<and> t\<^sub>v s' = Suc (Suc t) \<longrightarrow> (0::\<real>) < ureal2real p * ((1::\<real>) - ureal2real p)) \<and>
            (
              (d\<^sub>v s' = o1 \<longrightarrow> s\<^sub>v s' = s4 \<longrightarrow> \<not> t\<^sub>v s' = Suc (Suc t)) \<longrightarrow>
              (s\<^sub>v s' = s4 \<and> d\<^sub>v s' = o2 \<and> t\<^sub>v s' = Suc (Suc t) \<longrightarrow> (0::\<real>) < ((1::\<real>) - ureal2real p) * ureal2real p) \<and>
              (
                (d\<^sub>v s' = o2 \<longrightarrow> s\<^sub>v s' = s4 \<longrightarrow> \<not> t\<^sub>v s' = Suc (Suc t)) \<longrightarrow>
                (s\<^sub>v s' = s4 \<and> d\<^sub>v s' = o3 \<and> t\<^sub>v s' = Suc (Suc t) \<longrightarrow> (0::\<real>) < ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p)) 
                \<and> d\<^sub>v s' = o3 \<and> s\<^sub>v s' = s4 \<and> t\<^sub>v s' = Suc (Suc t)
              )
            )
        )
       }"
  have set_p_0: "{s'::state.
    (d\<^sub>v s' = o0 \<longrightarrow> s\<^sub>v s' = s1 \<longrightarrow> \<not> t\<^sub>v s' = Suc (Suc t)) \<and>
    ((d\<^sub>v s' = o0 \<longrightarrow> s\<^sub>v s' = s1 \<longrightarrow> \<not> t\<^sub>v s' = Suc (Suc t)) \<longrightarrow>
     (d\<^sub>v s' = o1 \<longrightarrow> s\<^sub>v s' = s4 \<longrightarrow> \<not> t\<^sub>v s' = Suc (Suc t)) \<and>
     ((d\<^sub>v s' = o1 \<longrightarrow> s\<^sub>v s' = s4 \<longrightarrow> \<not> t\<^sub>v s' = Suc (Suc t)) \<longrightarrow>
      (d\<^sub>v s' = o2 \<longrightarrow> s\<^sub>v s' = s4 \<longrightarrow> \<not> t\<^sub>v s' = Suc (Suc t)) \<and>
      ((d\<^sub>v s' = o2 \<longrightarrow> s\<^sub>v s' = s4 \<longrightarrow> \<not> t\<^sub>v s' = Suc (Suc t)) \<longrightarrow> d\<^sub>v s' = o3 \<and> s\<^sub>v s' = s4 \<and> t\<^sub>v s' = Suc (Suc t))))}
    = {s'::state.  d\<^sub>v s' = o3 \<and> s\<^sub>v s' = s4 \<and> t\<^sub>v s' = Suc (Suc t)}"
    by fastforce
  have set_p_1: "{s'::state.
      (d\<^sub>v s' = o0 \<longrightarrow> s\<^sub>v s' = s1 \<longrightarrow> \<not> t\<^sub>v s' = Suc (Suc t)) \<longrightarrow>
      (d\<^sub>v s' = o1 \<longrightarrow> s\<^sub>v s' = s4 \<longrightarrow> \<not> t\<^sub>v s' = Suc (Suc t)) \<and>
      ((d\<^sub>v s' = o1 \<longrightarrow> s\<^sub>v s' = s4 \<longrightarrow> \<not> t\<^sub>v s' = Suc (Suc t)) \<longrightarrow>
       (d\<^sub>v s' = o2 \<longrightarrow> s\<^sub>v s' = s4 \<longrightarrow> \<not> t\<^sub>v s' = Suc (Suc t)) \<and>
       ((d\<^sub>v s' = o2 \<longrightarrow> s\<^sub>v s' = s4 \<longrightarrow> \<not> t\<^sub>v s' = Suc (Suc t)) \<longrightarrow>
        (d\<^sub>v s' = o3 \<longrightarrow> s\<^sub>v s' = s4 \<longrightarrow> \<not> t\<^sub>v s' = Suc (Suc t)) \<and> d\<^sub>v s' = o3 \<and> s\<^sub>v s' = s4 \<and> t\<^sub>v s' = Suc (Suc t)))} 
    =  {s'::state. d\<^sub>v s' = o0 \<and> s\<^sub>v s' = s1 \<and> t\<^sub>v s' = Suc (Suc t)}"
    by auto
  have set_p_0_1: "{s'::state.
      (d\<^sub>v s' = o0 \<longrightarrow> s\<^sub>v s' = s1 \<longrightarrow> \<not> t\<^sub>v s' = Suc (Suc t)) \<longrightarrow>
      (d\<^sub>v s' = o1 \<longrightarrow> s\<^sub>v s' = s4 \<longrightarrow> \<not> t\<^sub>v s' = Suc (Suc t)) \<longrightarrow>
      (d\<^sub>v s' = o2 \<longrightarrow> s\<^sub>v s' = s4 \<longrightarrow> \<not> t\<^sub>v s' = Suc (Suc t)) \<longrightarrow> d\<^sub>v s' = o3 \<and> s\<^sub>v s' = s4 \<and> t\<^sub>v s' = Suc (Suc t)}
    = {s'::state. (d\<^sub>v s' = o0 \<and> s\<^sub>v s' = s1 \<and> t\<^sub>v s' = Suc (Suc t)) \<or>
        (d\<^sub>v s' = o1 \<and> s\<^sub>v s' = s4 \<and> t\<^sub>v s' = Suc (Suc t)) \<or>
        (d\<^sub>v s' = o2 \<and> s\<^sub>v s' = s4 \<and> t\<^sub>v s' = Suc (Suc t)) \<or> 
         d\<^sub>v s' = o3 \<and> s\<^sub>v s' = s4 \<and> t\<^sub>v s' = Suc (Suc t)}"
    by fastforce
  have set_p_0_1': "... = {\<lparr>t\<^sub>v = Suc (Suc t), s\<^sub>v = s1, d\<^sub>v = o0\<rparr>, \<lparr>t\<^sub>v = Suc (Suc t), s\<^sub>v = s4, d\<^sub>v = o1\<rparr>, 
               \<lparr>t\<^sub>v = Suc (Suc t), s\<^sub>v = s4, d\<^sub>v = o2\<rparr>, \<lparr>t\<^sub>v = Suc (Suc t), s\<^sub>v = s4, d\<^sub>v = o3\<rparr>}"
    apply (simp add: Collect_disj_eq)
    by (smt (verit, ccfv_SIG) Collect_cong Set.empty_def Suc_n_not_le_n Un_empty Un_insert_left 
        Un_insert_right card.empty card_1_singleton_iff finite.simps finite_insert mem_Collect_eq 
        not_less_eq_eq set_p_1 singletonD singleton_conv singleton_conv2 singleton_set_simp sup_bot_left)
  show "finite ?lhs"
    proof (cases "p = 0")
      case True
      then show ?thesis 
        apply (simp add: ureal2real_0 set_p_0)
        by (metis (no_types, lifting) Collect_cong singleton_set_finite')
    next
      assume False: "\<not> p = (0::ureal)"
      then show ?thesis 
        proof (cases "p = 1")
          case True
          then show ?thesis 
          apply (simp add: ureal2real_1 set_p_1)
          by (metis (no_types, lifting) Collect_cong singleton_set_finite')
        next
          assume FFalse: "\<not> p = (1::ureal)"
          from False FFalse have f1: "((0::\<real>) < ureal2real p * ureal2real p)"
            by (metis not_real_square_gt_zero ureal2real_0 ureal2real_inverse)
          from False FFalse have f2: "(0::\<real>) < ureal2real p * ((1::\<real>) - ureal2real p)"
            by (metis diff_gt_0_iff_gt dual_order.eq_iff f1 linorder_not_le ureal2real_1 ureal2real_inverse ureal_lower_bound ureal_upper_bound zero_less_mult_iff)
          from False FFalse have f3: "(0::\<real>) < ((1::\<real>) - ureal2real p) * ureal2real p"
            by (metis diff_gt_0_iff_gt dual_order.eq_iff f1 linorder_not_le ureal2real_1 ureal2real_inverse ureal_lower_bound ureal_upper_bound zero_less_mult_iff)
          from False FFalse have f4: "(0::\<real>) < ((1::\<real>) - ureal2real p) * ((1::\<real>) - ureal2real p)"
            by (metis f2 zero_less_mult_iff)
          from f1 f2 f3 f4 show ?thesis
            apply (auto)
            by (simp add: set_p_0_1 set_p_0_1')
        qed
    qed
  qed

  term "((s,d) := (s1,o0)):: state prhfun"

end