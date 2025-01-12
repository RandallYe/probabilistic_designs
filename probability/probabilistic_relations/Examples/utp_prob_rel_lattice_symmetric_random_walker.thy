section \<open> Example of probabilistic relation programming: simple random walk \<close>

theory utp_prob_rel_lattice_symmetric_random_walker
  imports 
    "UTP_prob_relations.utp_prob_rel_lattice_laws" 
    "HOL-Analysis.Infinite_Set_Sum"
    "HOL.Binomial"
begin 

unbundle UTP_Syntax

declare [[show_types]]

subsection \<open> Definitions \<close>

subsubsection \<open> Distribution functions \<close>
text \<open> The distribution function of the while loop below. \<close>
fun mu_lp :: "real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" ("\<mu>\<^sub>l\<^sub>p") where 
"\<mu>\<^sub>l\<^sub>p p 0 0 = 1" |
"\<mu>\<^sub>l\<^sub>p p 0 (Suc n) = 0" |
"\<mu>\<^sub>l\<^sub>p p (Suc m) 0 = 0" |
"\<mu>\<^sub>l\<^sub>p p (Suc m) (Suc n) = p * (\<mu>\<^sub>l\<^sub>p p m n) + (1 - p) * (\<mu>\<^sub>l\<^sub>p p (Suc (Suc m)) n)" 

thm "mu_lp.induct"

lemma mu_lp_nonneg: 
  assumes "p \<ge> 0" "p \<le> 1"
  shows "(\<mu>\<^sub>l\<^sub>p p m n) \<ge> 0"
(* https://stackoverflow.com/questions/19011374/induction-on-recursive-function-with-a-twist *)
  using assms 
proof (induct p m n rule: mu_lp.induct)
  case (1 p)
  then show ?case by simp
next
  case (2 p n)
  then show ?case by simpv
next
  case (3 p m)
  then show ?case by simp
next
  case (4 p m n)
  then show ?case by fastforce
qed

lemma mu_lp_zero:
  assumes "m > 0"
  assumes "n > 0"
  assumes "m > n"
  shows "(\<mu>\<^sub>l\<^sub>p p m n) = 0"
  using assms 
proof (induct p m n rule: mu_lp.induct)
  case (1 p)
  then show ?case by fastforce
next
  case (2 p n)
  then show ?case by blast
next
  case (3 p m)
  then show ?case by blast
next
  case (4 p m n)
  then show ?case
    by (metis (no_types, opaque_lifting) add_0 less_Suc_eq mu_lp.simps(3) mu_lp.simps(4) mult_zero_right not_less_eq old.nat.exhaust)
qed

lemma mu_lp_zero':
  shows "m > 0 \<Longrightarrow> n > 0 \<Longrightarrow> m > n \<Longrightarrow> (\<mu>\<^sub>l\<^sub>p p m n) = 0"
proof (induct p m n rule: mu_lp.induct)
  case (4 p m n)
  thus ?case by (metis (no_types, opaque_lifting) add_0 less_Suc_eq mu_lp.simps(3) mu_lp.simps(4) mult_zero_right not_less_eq old.nat.exhaust)
qed auto

lemma mu_lp_leq_1:
  shows "p \<ge> 0 \<Longrightarrow> p \<le> 1 \<Longrightarrow> (\<mu>\<^sub>l\<^sub>p p m n) \<le> 1"
proof (induct p m n rule: mu_lp.induct)
  case (4 p m n)
  thus ?case by (smt (verit) mu_lp.simps(4) mult_left_le)
qed auto

lemma mu_lp_all_left:
  assumes "m = n"
  shows "\<mu>\<^sub>l\<^sub>p p m n = p ^ m"
  using assms
proof (induct p m n rule: mu_lp.induct)
  case (1 p)
  then show ?case by simp
next
  case (2 p n)
  then show ?case by simp
next
  case (3 p m)
  then show ?case by simp
next
  case (4 p m n)
  then show ?case
    by (smt (verit, del_insts) bot_nat_0.not_eq_extremum less_Suc_eq mu_lp.simps(3) mu_lp.simps(4) mu_lp_zero' mult_cancel_right1 nat.inject power_Suc)
qed


subsubsection \<open> Programs \<close>
alphabet state = time + 
  x :: nat

definition step:: "ureal \<Rightarrow> state prhfun" where
"step p = if\<^sub>p \<guillemotleft>p\<guillemotright> then (x := x - 1) else (x := x + 1)"

definition srw_loop where
"srw_loop p  = while\<^sub>p\<^sub>t (x\<^sup>< > 0)\<^sub>e do step p od"

definition Ht:: "ureal \<Rightarrow> state rvhfun" where 
"Ht p = ((\<lbrakk>\<not>x\<^sup>< > 0\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>x\<^sup>> = x\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e) + 
        \<lbrakk>x\<^sup>< > 0\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>x\<^sup>> = 0\<rbrakk>\<^sub>\<I>\<^sub>e * (
          \<lbrakk>t\<^sup>> \<ge> t\<^sup>< + x\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>(t\<^sup>> - (t\<^sup>< + x\<^sup><)) mod 2 = 0\<rbrakk>\<^sub>\<I>\<^sub>e * (\<mu>\<^sub>l\<^sub>p (ureal2real \<guillemotleft>p\<guillemotright>) (x\<^sup>< - 1) (t\<^sup>> - t\<^sup>< - 1)) * (ureal2real \<guillemotleft>p\<guillemotright>) +
          \<lbrakk>t\<^sup>> \<ge> t\<^sup>< + x\<^sup>< + 2\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>(t\<^sup>> - (t\<^sup>< + x\<^sup>< + 2)) mod 2 = 0\<rbrakk>\<^sub>\<I>\<^sub>e * (\<mu>\<^sub>l\<^sub>p (ureal2real \<guillemotleft>p\<guillemotright>) (x\<^sup>< + 1) (t\<^sup>> - t\<^sup>< - 1)) * (1 - ureal2real \<guillemotleft>p\<guillemotright>)
        )
  )\<^sub>e"

definition Pt_step_alt :: "ureal \<Rightarrow> state rvhfun" where
"Pt_step_alt p \<equiv> (\<lbrakk>x\<^sup>> = x\<^sup>< - 1 \<and> $t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (ureal2real \<guillemotleft>p\<guillemotright>) + 
                  \<lbrakk>x\<^sup>> = x\<^sup>< + 1 \<and> $t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1 - ureal2real \<guillemotleft>p\<guillemotright>))\<^sub>e"

lemma step_simp: "rvfun_of_prfun (step p)  = 
  (
    \<lbrakk>x\<^sup>> = x\<^sup>< - 1 \<and> t\<^sup>> = t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * ureal2real \<guillemotleft>p\<guillemotright> +
    \<lbrakk>x\<^sup>> = x\<^sup>< + 1 \<and> t\<^sup>> = t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * (1- ureal2real \<guillemotleft>p\<guillemotright>)
  )\<^sub>e"
  apply (simp only: step_def pchoice_def)
  apply (subst rvfun_pchoice_inverse)
  using ureal_is_prob apply blast+
  apply (simp add: pfun_defs)
  apply (subst rvfun_assignment_inverse)+
  apply (simp add: rvfun_of_prfun_def)
  apply (expr_simp_1)
  by (pred_auto)

lemma Pt_step_simp: "rvfun_of_prfun (Pt (step p)) = Pt_step_alt p"
  apply (simp add: Pt_def)
  apply (simp only: pseqcomp_def)
  apply (subst rvfun_seqcomp_inverse)+
  apply (simp add: step_def)
  apply (subst pvfun_pchoice_is_dist)
  apply (simp add: pvfun_assignment_is_dist)+
  using ureal_is_prob apply blast
  apply (simp add: step_simp pvfun_assignment_inverse)
  apply (simp add: Pt_step_alt_def)
  apply (expr_simp_1)
  apply (subst fun_eq_iff)
  apply (rule allI)
proof -
  fix xa :: "state \<times> state"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if get\<^bsub>x\<^esub> v\<^sub>0 = get\<^bsub>x\<^esub> (fst xa) - Suc (0::\<nat>) \<and> get\<^bsub>t\<^esub> v\<^sub>0 = get\<^bsub>t\<^esub> (fst xa) then 1::\<real> else (0::\<real>)) * ureal2real p +
           (if get\<^bsub>x\<^esub> v\<^sub>0 = Suc (get\<^bsub>x\<^esub> (fst xa)) \<and> get\<^bsub>t\<^esub> v\<^sub>0 = get\<^bsub>t\<^esub> (fst xa) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
          (if \<langle>\<lambda>s::state. put\<^bsub>t\<^esub> s (Suc (get\<^bsub>t\<^esub> s))\<rangle>\<^sub>a (v\<^sub>0, snd xa) then 1::\<real> else (0::\<real>)))"
  let ?rhs = "(if get\<^bsub>x\<^esub> (snd xa) = get\<^bsub>x\<^esub> (fst xa) - Suc (0::\<nat>) \<and> get\<^bsub>t\<^esub> (snd xa) = Suc (get\<^bsub>t\<^esub> (fst xa)) then 1::\<real> else (0::\<real>)) *
       ureal2real p + (if get\<^bsub>x\<^esub> (snd xa) = Suc (get\<^bsub>x\<^esub> (fst xa)) \<and> get\<^bsub>t\<^esub> (snd xa) = Suc (get\<^bsub>t\<^esub> (fst xa)) then 1::\<real> else (0::\<real>)) *
       ((1::\<real>) - ureal2real p)"

  have s1: "{s::state. x\<^sub>v s = x\<^sub>v (fst xa) - Suc (0::\<nat>) \<and> t\<^sub>v s = t\<^sub>v (fst xa) \<and> snd xa = s\<lparr>t\<^sub>v := Suc (t\<^sub>v s)\<rparr>} 
      = (if snd xa = \<lparr>t\<^sub>v = Suc (t\<^sub>v (fst xa)), x\<^sub>v = x\<^sub>v (fst xa) - Suc (0::\<nat>)\<rparr> then {\<lparr>t\<^sub>v = t\<^sub>v (fst xa), x\<^sub>v = x\<^sub>v (fst xa) - Suc (0::\<nat>)\<rparr>} else {})"
    by auto
  have s2: "{s::state. x\<^sub>v s = Suc (x\<^sub>v (fst xa)) \<and> t\<^sub>v s = t\<^sub>v (fst xa) \<and> snd xa = s\<lparr>t\<^sub>v := Suc (t\<^sub>v s)\<rparr>} 
      = (if snd xa = \<lparr>t\<^sub>v = Suc (t\<^sub>v (fst xa)), x\<^sub>v = Suc (x\<^sub>v (fst xa))\<rparr> then {\<lparr>t\<^sub>v = t\<^sub>v (fst xa), x\<^sub>v = Suc (x\<^sub>v (fst xa))\<rparr>} else {})"
    by auto
  have f1: "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          (if get\<^bsub>x\<^esub> v\<^sub>0 = get\<^bsub>x\<^esub> (fst xa) - Suc (0::\<nat>) \<and> get\<^bsub>t\<^esub> v\<^sub>0 = get\<^bsub>t\<^esub> (fst xa) \<and> 
            \<langle>\<lambda>s::state. put\<^bsub>t\<^esub> s (Suc (get\<^bsub>t\<^esub> s))\<rangle>\<^sub>a (v\<^sub>0, snd xa) then 1::\<real> else (0::\<real>)) * ureal2real p +
           (if get\<^bsub>x\<^esub> v\<^sub>0 = Suc (get\<^bsub>x\<^esub> (fst xa)) \<and> get\<^bsub>t\<^esub> v\<^sub>0 = get\<^bsub>t\<^esub> (fst xa) \<and> 
            \<langle>\<lambda>s::state. put\<^bsub>t\<^esub> s (Suc (get\<^bsub>t\<^esub> s))\<rangle>\<^sub>a (v\<^sub>0, snd xa) then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p))"
    apply (rule infsum_cong)
    by simp
  have f2: "... = ?rhs"
    apply (subst infsum_constant_finite_states_cmult_2)
    apply (pred_auto)
    using s1 apply simp
    apply (pred_auto)
    using s2 apply simp
    apply (pred_auto)
    apply (smt (z3) One_nat_def card.empty card.insert empty_iff finite.intros(1) mult_if_delta of_nat_0 of_nat_1 s1 s2 show_unit.elims state.simps(1) state.surjective)
    apply (smt (verit, ccfv_threshold) One_nat_def card.empty card.insert empty_iff eq_add_iff2 finite.intros(1) mult_cancel_right2 of_nat_0 of_nat_1 s1 s2 show_unit.elims state.simps(1) state.surjective)
    using s1 s2 apply force
    using s1 s2 by force+

  then show "?lhs = ?rhs"
    using f1 by presburger
qed

lemma Pt_step_dist: "is_final_distribution (rvfun_of_prfun (Pt (step p)))"
  apply (simp add: Pt_def)
  apply (simp only: pseqcomp_def)
  apply (subst rvfun_seqcomp_inverse)+
  apply (simp add: step_def)
  apply (subst pvfun_pchoice_is_dist) 
  apply (simp add: pvfun_assignment_is_dist)+
  using ureal_is_prob apply blast
  apply (subst rvfun_seqcomp_is_dist)
  apply (simp only: step_def)
  apply (subst pvfun_pchoice_is_dist)
  by (simp add: pvfun_assignment_is_dist)+

lemma Ht_is_fp: "\<F> (x\<^sup>< > 0)\<^sub>e (Pt (step p)) (prfun_of_rvfun (Ht p)) = prfun_of_rvfun (Ht p)"
  apply (simp add: Ht_def loopfunc_def pskip_def)
  apply (simp only: prfun_pcond_altdef rvfun_skip_inverse)
  apply (simp add: pseqcomp_def)
  apply (subst rvfun_seqcomp_inverse)
  apply (simp add: Pt_step_dist)
  using ureal_is_prob apply blast
  apply (subst rvfun_inverse)
  apply (expr_auto)
  apply (simp only: is_prob_def expr_defs)
  apply (rule allI, rule conjI)
  apply (smt (verit, best) mu_lp_nonneg mult_nonneg_nonneg ureal_lower_bound ureal_upper_bound)
  apply (auto)
  apply (meson mu_lp_leq_1 mult_le_one ureal_lower_bound ureal_upper_bound)
  apply (metis diff_Suc_1 gr0_conv_Suc mu_lp.simps(4) mu_lp_leq_1 mult.commute numeral_1_eq_Suc_0 one_eq_numeral_iff ureal_lower_bound ureal_upper_bound)
  apply (metis diff_Suc_1 gr0_conv_Suc mu_lp.simps(4) mu_lp_leq_1 mult.commute numeral_1_eq_Suc_0 numeral_eq_one_iff ureal_lower_bound ureal_upper_bound)
  apply (metis mu_lp.simps(4) mu_lp_leq_1 mult.commute odd_Suc_minus_one ureal_lower_bound ureal_upper_bound)
  apply (metis diff_Suc_1 gr0_conv_Suc mu_lp.simps(4) mu_lp_leq_1 mult.commute numeral_1_eq_Suc_0 numeral_eq_one_iff ureal_lower_bound ureal_upper_bound)
  apply (simp add: Pt_step_simp Pt_step_alt_def)
  apply (expr_auto)
proof -
  fix t::"\<nat>" and x::"\<nat>" and t\<^sub>v':: "\<nat>" and x\<^sub>v'::"\<nat>"
  let ?b1 = "\<lambda>\<s>::state \<times> state. \<lambda>v\<^sub>0::state. x\<^sub>v v\<^sub>0 = x\<^sub>v (fst \<s>) - Suc (0::\<nat>) \<and> t\<^sub>v v\<^sub>0 = Suc (t\<^sub>v (fst \<s>))"
  let ?b2 = "\<lambda>\<s>::state \<times> state. \<lambda>v\<^sub>0::state. x\<^sub>v v\<^sub>0 = Suc (x\<^sub>v (fst \<s>)) \<and> t\<^sub>v v\<^sub>0 = Suc (t\<^sub>v (fst \<s>))"
  let ?b3 = "\<lambda>\<s>::state \<times> state. \<lambda>v\<^sub>0::state. x\<^sub>v v\<^sub>0 = (0::\<nat>) \<and> t\<^sub>v (snd \<s>) = t\<^sub>v v\<^sub>0 \<and> x\<^sub>v (snd \<s>) = x\<^sub>v v\<^sub>0"
  let ?b4 = "\<lambda>\<s>::state \<times> state. \<lambda>v\<^sub>0::state. (0::\<nat>) < x\<^sub>v v\<^sub>0 \<and> x\<^sub>v (snd \<s>) = (0::\<nat>) \<and> 
                t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0 \<le> t\<^sub>v (snd \<s>) \<and> (t\<^sub>v (snd \<s>) - (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0)) mod (2::\<nat>) = (0::\<nat>)"
  let ?b5 = "\<lambda>\<s>::state \<times> state. \<lambda>v\<^sub>0::state. (0::\<nat>) < x\<^sub>v v\<^sub>0 \<and> x\<^sub>v (snd \<s>) = (0::\<nat>) \<and> 
                Suc (Suc (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0)) \<le> t\<^sub>v (snd \<s>) \<and> 
                (t\<^sub>v (snd \<s>) - Suc (Suc (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0))) mod (2::\<nat>) = (0::\<nat>)"
  

  let ?lhs = "\<lambda>\<s>::state \<times> state. (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
               ((if ?b1 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p +
                (if ?b2 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
               ((if x\<^sub>v v\<^sub>0 = (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if t\<^sub>v (snd \<s>) = t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if x\<^sub>v (snd \<s>) = x\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) +
                (if (0::\<nat>) < x\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if x\<^sub>v (snd \<s>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
                ((if t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0 \<le> t\<^sub>v (snd \<s>) then 1::\<real> else (0::\<real>)) * (if (t\<^sub>v (snd \<s>) - (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0)) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
                 \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v v\<^sub>0 - Suc (0::\<nat>)) (t\<^sub>v (snd \<s>) - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p +
                 (if Suc (Suc (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0)) \<le> t\<^sub>v (snd \<s>) then 1::\<real> else (0::\<real>)) *
                 (if (t\<^sub>v (snd \<s>) - Suc (Suc (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0))) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
                 \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v v\<^sub>0)) (t\<^sub>v (snd \<s>) - Suc (t\<^sub>v v\<^sub>0)) * ((1::\<real>) - ureal2real p))))"
  have "?lhs \<s> = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
               ((if ?b1 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p +
                (if ?b2 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
               ((if ?b3 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) +
                (if ?b4 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) *
                  \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v v\<^sub>0 - Suc (0::\<nat>)) (t\<^sub>v (snd \<s>) - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p +
                (if ?b5 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) *
                  \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v v\<^sub>0)) (t\<^sub>v (snd \<s>) - Suc (t\<^sub>v v\<^sub>0)) * ((1::\<real>) - ureal2real p)
                ))"
    apply (rule infsum_cong)
    by (simp)
  also have "... =  (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
               (((if ?b1 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p) * 
                 (if ?b3 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) +
                ((if ?b2 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
                (if ?b3 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>))
              ) + 
              (((if ?b1 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p) *
               ((if ?b4 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) *
                  \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v v\<^sub>0 - Suc (0::\<nat>)) (t\<^sub>v (snd \<s>) - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p) +
               ((if ?b1 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p) *
               ((if ?b5 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) *
                  \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v v\<^sub>0)) (t\<^sub>v (snd \<s>) - Suc (t\<^sub>v v\<^sub>0)) * ((1::\<real>) - ureal2real p)) + 
               ((if ?b2 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
               ((if ?b4 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) *
                  \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v v\<^sub>0 - Suc (0::\<nat>)) (t\<^sub>v (snd \<s>) - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p) +
               ((if ?b2 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
               ((if ?b5 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) *
                  \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v v\<^sub>0)) (t\<^sub>v (snd \<s>) - Suc (t\<^sub>v v\<^sub>0)) * ((1::\<real>) - ureal2real p))
            )
        )"
    apply (rule infsum_cong)
    by (simp add: comm_semiring_class.distrib distrib_left)
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
       (if ?b1 \<s> v\<^sub>0 \<and> ?b3 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p +
       ((if ?b1 \<s> v\<^sub>0 \<and> ?b4 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) * (ureal2real p * 
                  \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v v\<^sub>0 - Suc (0::\<nat>)) (t\<^sub>v (snd \<s>) - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p)) +
       ((if ?b1 \<s> v\<^sub>0 \<and> ?b5 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) * (ureal2real p *
          \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v v\<^sub>0)) (t\<^sub>v (snd \<s>) - Suc (t\<^sub>v v\<^sub>0)) * ((1::\<real>) - ureal2real p))) + 
       ((if ?b2 \<s> v\<^sub>0 \<and> ?b4 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) * (((1::\<real>) - ureal2real p) *
          \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v v\<^sub>0 - Suc (0::\<nat>)) (t\<^sub>v (snd \<s>) - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p)) +
       ((if ?b2 \<s> v\<^sub>0 \<and> ?b5 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) * (((1::\<real>) - ureal2real p) *
          \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v v\<^sub>0)) (t\<^sub>v (snd \<s>) - Suc (t\<^sub>v v\<^sub>0)) * ((1::\<real>) - ureal2real p))
       )
    )"
    apply (rule infsum_cong)
    by (smt (verit) less_Suc_eq_0_disj less_numeral_extra(3) mult.assoc mult_cancel_left1 mult_eq_0_iff)
  also have "... =  (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
               ((if ?b1 \<s> v\<^sub>0 \<and> ?b3 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p) +
               ((if ?b2 \<s> v\<^sub>0 \<and> ?b3 \<s> v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) +
               ((if ?b1 \<s> v\<^sub>0 \<and> (0::\<nat>) < x\<^sub>v v\<^sub>0 \<and> 
                    x\<^sub>v (snd \<s>) = (0::\<nat>) \<and> t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0 \<le> t\<^sub>v (snd \<s>) \<and> (t\<^sub>v (snd \<s>) - (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0)) mod (2::\<nat>) = (0::\<nat>) 
                 then 1::\<real> else (0::\<real>)) * \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v v\<^sub>0 - Suc (0::\<nat>)) (t\<^sub>v (snd \<s>) - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p) +
               ((if ?b2 \<s> v\<^sub>0 \<and> (0::\<nat>) < x\<^sub>v v\<^sub>0 \<and> 
                    x\<^sub>v (snd \<s>) = (0::\<nat>) \<and> Suc (Suc (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0)) \<le> t\<^sub>v (snd \<s>) \<and> (t\<^sub>v (snd \<s>) - Suc (Suc (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0))) mod (2::\<nat>) = (0::\<nat>) 
                then 1::\<real> else (0::\<real>)) * \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v v\<^sub>0)) (t\<^sub>v (snd \<s>) - Suc (t\<^sub>v v\<^sub>0)) * ((1::\<real>) - ureal2real p)) +
               ((if ?b1 \<s> v\<^sub>0  \<and> (0::\<nat>) < x\<^sub>v v\<^sub>0 \<and> 
                    x\<^sub>v (snd \<s>) = (0::\<nat>) \<and> t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0 \<le> t\<^sub>v (snd \<s>) \<and> (t\<^sub>v (snd \<s>) - (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0)) mod (2::\<nat>) = (0::\<nat>) 
                 then 1::\<real> else (0::\<real>)) * \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v v\<^sub>0 - Suc (0::\<nat>)) (t\<^sub>v (snd \<s>) - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p) +
               ((if ?b2 \<s> v\<^sub>0 \<and> (0::\<nat>) < x\<^sub>v v\<^sub>0 \<and> 
                    x\<^sub>v (snd \<s>) = (0::\<nat>) \<and> Suc (Suc (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0)) \<le> t\<^sub>v (snd \<s>) \<and> (t\<^sub>v (snd \<s>) - Suc (Suc (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0))) mod (2::\<nat>) = (0::\<nat>) 
                then 1::\<real> else (0::\<real>)) * \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v v\<^sub>0)) (t\<^sub>v (snd \<s>) - Suc (t\<^sub>v v\<^sub>0)) * ((1::\<real>) - ureal2real p))
        )"
    apply (rule infsum_cong)
    sledgehammer
    by (simp)
  show "prfun_of_rvfun
        (\<lambda>\<s>::state \<times> state.
            (if (0::\<nat>) < x\<^sub>v (fst \<s>) then 1::\<real> else (0::\<real>)) * ?lhs \<s> +
            (if x\<^sub>v (fst \<s>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if II \<s> then 1::\<real> else (0::\<real>)))
        (\<lparr>t\<^sub>v = t, x\<^sub>v = x\<rparr>, \<lparr>t\<^sub>v = t\<^sub>v', x\<^sub>v = x\<^sub>v'\<rparr>) =
       prfun_of_rvfun
        (\<lambda>\<s>::state \<times> state.
            (if x\<^sub>v (fst \<s>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if t\<^sub>v (snd \<s>) = t\<^sub>v (fst \<s>) then 1::\<real> else (0::\<real>)) * (if x\<^sub>v (snd \<s>) = x\<^sub>v (fst \<s>) then 1::\<real> else (0::\<real>)) +
            (if (0::\<nat>) < x\<^sub>v (fst \<s>) then 1::\<real> else (0::\<real>)) * (if x\<^sub>v (snd \<s>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
            ((if t\<^sub>v (fst \<s>) + x\<^sub>v (fst \<s>) \<le> t\<^sub>v (snd \<s>) then 1::\<real> else (0::\<real>)) * (if (t\<^sub>v (snd \<s>) - (t\<^sub>v (fst \<s>) + x\<^sub>v (fst \<s>))) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
             \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst \<s>) - Suc (0::\<nat>)) (t\<^sub>v (snd \<s>) - Suc (t\<^sub>v (fst \<s>))) *
             ureal2real p +
             (if Suc (Suc (t\<^sub>v (fst \<s>) + x\<^sub>v (fst \<s>))) \<le> t\<^sub>v (snd \<s>) then 1::\<real> else (0::\<real>)) *
             (if (t\<^sub>v (snd \<s>) - Suc (Suc (t\<^sub>v (fst \<s>) + x\<^sub>v (fst \<s>)))) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
             \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst \<s>))) (t\<^sub>v (snd \<s>) - Suc (t\<^sub>v (fst \<s>))) *
             ((1::\<real>) - ureal2real p)))
        (\<lparr>t\<^sub>v = t, x\<^sub>v = x\<rparr>, \<lparr>t\<^sub>v = t\<^sub>v', x\<^sub>v = x\<^sub>v'\<rparr>)"
  qed

subsection \<open> Distributions \<close>
thm "fact_prod"
term "fact 2"
term "even"

context semiring_char_0
begin
text \<open> @{text "fact2 (n-1)"} \<close>
(* fact2 0 = (-1)!! = 1 
   fact2 1 = (0)!! = 1 
   fact2 n = (n-1)!! 
*)
definition fact2 :: "nat \<Rightarrow> 'a"
  where fact2_prod: "fact2 n = (
    if n = 0 \<or> n = 1 then 1 else 
      (if even (n-1) 
      then (of_nat (\<Prod>i\<in>{1..((n-1) div 2)}. 2*i)) 
      else (of_nat (\<Prod>i\<in>{1..(n div 2)}. 2*i-1))
      )
    )"
end

lemma "(fact2 0::\<nat>) = 1"
  by (simp add: fact2_prod)

lemma "(fact2 1::\<nat>) = 1"
  by (simp add: fact2_prod)

lemma "(fact2 2::\<nat>) = 1"
  by (simp add: fact2_prod)

lemma "(fact2 3::\<nat>) = 2"
  by (simp add: fact2_prod)

lemma "(fact2 4::\<nat>) = 3"
  apply (simp add: fact2_prod)
  by (metis (no_types, lifting) One_nat_def add_Suc diff_Suc_1 le_add_same_cancel1 mult_2 
      mult_numeral_1_right numeral_1_eq_Suc_0 numeral_3_eq_3 plus_1_eq_Suc prod.nat_ivl_Suc' 
      prod_neutral_const zero_less_one_class.zero_le_one)

definition p_n :: "nat \<Rightarrow> \<real>" where
"p_n n = (-1)^(n-1) * ((1/2::\<real>) gchoose n)"

subsection \<open> Theorems \<close>
lemma rvfun_of_prfun_1_2: "rvfun_of_prfun (\<lambda>x::state \<times> state. ereal2ureal (ereal ((1::\<real>) / (2::\<real>))))
  = ((1::\<real>) / (2::\<real>))\<^sub>e"
  apply (simp add: ureal_defs)
  by (simp add: real2uereal_inverse)

lemma rvfun_of_prfun_1_2': 
  "rvfun_of_prfun [\<lambda>x::state \<times> state. ereal2ureal (ereal ((1::\<real>) / (2::\<real>)))]\<^sub>e
  = (\<lambda>s. ureal2real (1/2))"
  apply (simp add: ureal_defs)
  by (simp add: SEXP_def ereal_1_div)

lemma rvfun_of_prfun_1_2'': 
  "rvfun_of_prfun [\<lambda>x::state \<times> state. ereal2ureal (ereal ((1::\<real>) / (2::\<real>)))]\<^sub>e
  = ((1::\<real>) / (2::\<real>))\<^sub>e"
  apply (simp add: ureal_defs)
  by (simp add: real2uereal_inverse)

lemma srw_move_t: "(Pt move) = prfun_of_rvfun move_t_alt"
  apply (simp add: move_def Pt_def move_t_alt_def)
  apply (simp add: pseqcomp_def)
  apply (simp add: pchoice_def)
  apply (subst rvfun_inverse)
  apply (simp add: rvfun_of_prfun_1_2')
  apply (rule rvfun_pchoice_is_prob')
  using ureal_is_prob apply blast
  using ureal_is_prob apply blast
  apply (simp only: rvfun_of_prfun_1_2'')
  apply (simp add: pfun_defs)
  apply (simp add: rvfun_assignment_inverse)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (simp add: fun_eq_iff)
  apply (rule allI)+
  apply (pred_auto)
  defer
  apply (simp add: infsum_0)
  defer
  apply (simp add: infsum_0)+
proof -
  fix t::\<nat> and x::\<nat>
  assume a1: "\<not> Suc x = x - Suc (0::\<nat>)"
  let ?f1 = "\<lambda>v\<^sub>0. ((if v\<^sub>0 = \<lparr>t\<^sub>v = t, x\<^sub>v = x - Suc (0::\<nat>)\<rparr> then 1::\<real> else (0::\<real>)))"
  let ?f2 = "\<lambda>v\<^sub>0. (if v\<^sub>0 = \<lparr>t\<^sub>v = t, x\<^sub>v = Suc x\<rparr> then 1::\<real> else (0::\<real>))"
  let ?f3 = "\<lambda>v\<^sub>0. (if \<lparr>t\<^sub>v = Suc t, x\<^sub>v = Suc x\<rparr> = v\<^sub>0\<lparr>t\<^sub>v := Suc (t\<^sub>v v\<^sub>0)\<rparr> then 1::\<real> else (0::\<real>))"

  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state. (?f1 v\<^sub>0 / (2::\<real>) +  ?f2 v\<^sub>0 / (2::\<real>)) * ?f3 v\<^sub>0) = 
        (\<Sum>\<^sub>\<infinity>v\<^sub>0::state. (if v\<^sub>0 = \<lparr>t\<^sub>v = t, x\<^sub>v = Suc x\<rparr> \<and> \<lparr>t\<^sub>v = Suc t, x\<^sub>v = Suc x\<rparr> = v\<^sub>0\<lparr>t\<^sub>v := Suc (t\<^sub>v v\<^sub>0)\<rparr> 
            then (1/2) else (0::\<real>)))"
    apply (rule infsum_cong)
    by (smt (verit, best) a1 div_0 mult_cancel_left2 mult_cancel_right2 state.simps(1) time.update_convs(1))
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state. (if v\<^sub>0 = \<lparr>t\<^sub>v = t, x\<^sub>v = Suc x\<rparr> then (1/2) else (0::\<real>)))"
    apply (rule infsum_cong)
    by simp
  also have "... = 1/2"
    by (simp add: infsum_singleton_1)
  finally show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state. (?f1 v\<^sub>0 / (2::\<real>) +  ?f2 v\<^sub>0 / (2::\<real>)) * ?f3 v\<^sub>0) * (2::\<real>) = (1::\<real>)"
    by linarith
next
  fix t::\<nat> and x::\<nat>
  assume a1: "\<not> x - Suc (0::\<nat>) = Suc x"
  let ?f1 = "\<lambda>v\<^sub>0. ((if v\<^sub>0 = \<lparr>t\<^sub>v = t, x\<^sub>v = x - Suc (0::\<nat>)\<rparr> then 1::\<real> else (0::\<real>)))"
  let ?f2 = "\<lambda>v\<^sub>0. (if v\<^sub>0 = \<lparr>t\<^sub>v = t, x\<^sub>v = Suc x\<rparr> then 1::\<real> else (0::\<real>))"
  let ?f3 = "\<lambda>v\<^sub>0. (if \<lparr>t\<^sub>v = Suc t, x\<^sub>v = x - Suc (0::\<nat>)\<rparr> = v\<^sub>0\<lparr>t\<^sub>v := Suc (t\<^sub>v v\<^sub>0)\<rparr> then 1::\<real> else (0::\<real>))"

  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state. (?f1 v\<^sub>0 / (2::\<real>) +  ?f2 v\<^sub>0 / (2::\<real>)) * ?f3 v\<^sub>0) = 
        (\<Sum>\<^sub>\<infinity>v\<^sub>0::state. (if v\<^sub>0 = \<lparr>t\<^sub>v = t, x\<^sub>v = x - Suc (0::\<nat>)\<rparr> \<and> \<lparr>t\<^sub>v = Suc t, x\<^sub>v = x - Suc (0::\<nat>)\<rparr> = v\<^sub>0\<lparr>t\<^sub>v := Suc (t\<^sub>v v\<^sub>0)\<rparr> 
            then (1/2) else (0::\<real>)))"
    apply (rule infsum_cong)
    by (smt (verit, best) a1 div_0 mult_cancel_left2 mult_cancel_right2 state.simps(1) time.update_convs(1))
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state. (if v\<^sub>0 = \<lparr>t\<^sub>v = t, x\<^sub>v = x - Suc (0::\<nat>)\<rparr> then (1/2) else (0::\<real>)))"
    apply (rule infsum_cong)
    by simp
  also have "... = 1/2"
    by (simp add: infsum_singleton_1)
  finally show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state. (?f1 v\<^sub>0 / (2::\<real>) +  ?f2 v\<^sub>0 / (2::\<real>)) * ?f3 v\<^sub>0) * (2::\<real>) = (1::\<real>)"
    by linarith
qed

lemma move_t_alt_is_dist: "is_final_distribution move_t_alt"
  apply (simp add: dist_defs move_t_alt_def)
  apply (expr_auto)
proof -
  fix t::\<nat> and x::\<nat>
  assume a1: " \<not> x - Suc (0::\<nat>) = Suc x"
  let ?f = "\<lambda>s. (if x\<^sub>v s = Suc x then 1::\<real> else (0::\<real>)) * (if t\<^sub>v s = Suc t then 1::\<real> else (0::\<real>)) / (2::\<real>) +
          (if x\<^sub>v s = x - Suc (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if t\<^sub>v s = Suc t then 1::\<real> else (0::\<real>)) / (2::\<real>)"
  have "(\<Sum>\<^sub>\<infinity>s::state. ?f s) = 
    (\<Sum>\<^sub>\<infinity>s::state. (if x\<^sub>v s = Suc x \<and> t\<^sub>v s = Suc t then 1/2 else 0) + 
                     (if x\<^sub>v s = x - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc t then 1/2 else 0))"
    apply (rule infsum_cong)
    by simp
  also have "... = 1"
    apply (subst infsum_add)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (z3) Collect_mono finite.emptyI finite_insert old.unit.exhaust rev_finite_subset singleton_conv state.surjective)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (z3) Collect_mono finite.emptyI finite_insert old.unit.exhaust rev_finite_subset singleton_conv state.surjective)
    apply (subst infsum_singleton_cond_unique)
    apply (metis (mono_tags, opaque_lifting) old.unit.exhaust state.select_convs(1) state.surjective time.select_convs(1))
    apply (subst infsum_singleton_cond_unique)
    apply (metis (mono_tags, opaque_lifting) old.unit.exhaust state.select_convs(1) state.surjective time.select_convs(1))
    by simp
  finally show "(\<Sum>\<^sub>\<infinity>s::state. ?f s) = 1"
    by meson
qed

lemma srw_iterdiff_simp:
  shows "(iterdiff 0 (x\<^sup>< > 0)\<^sub>e (Pt move) 1\<^sub>p) = 1\<^sub>p"
        "(iterdiff (n+1) (x\<^sup>< > 0)\<^sub>e (Pt move) 1\<^sub>p) = 
            prfun_of_rvfun ((\<lbrakk>x\<^sup>< > 0\<rbrakk>\<^sub>\<I>\<^sub>e * (5/6)^\<guillemotleft>n\<guillemotright>)\<^sub>e)"
  apply force
proof -
  show "(iterdiff (n+1) (x\<^sup>< > 0)\<^sub>e (Pt move) 1\<^sub>p) = 
            prfun_of_rvfun ((\<lbrakk>x\<^sup>< > 0\<rbrakk>\<^sub>\<I>\<^sub>e * (5/6)^\<guillemotleft>n\<guillemotright>)\<^sub>e)"
    sorry
qed
  
lemma srw_iter_seq_tendsto_0:
  "\<forall>s::state \<times> state. (\<lambda>n::\<nat>. ureal2real (iterdiff n (x\<^sup>< > 0)\<^sub>e (Pt move) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
proof 
  fix s
  have "(\<lambda>n::\<nat>. ureal2real (iterdiff (n+1) (x\<^sup>< > 0)\<^sub>e (Pt move) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    sorry
  then show "(\<lambda>n::\<nat>. ureal2real (iterdiff n (x\<^sup>< > 0)\<^sub>e (Pt move) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    by (rule LIMSEQ_offset[where k = 1])
qed

lemma Ht_is_dist: "is_final_distribution Ht"
  apply (simp add: dist_defs Ht_def)
  apply (simp add: expr_defs)
  apply (pred_auto)
  defer
  apply (smt (verit, best) divide_nonneg_nonneg le_divide_eq_1_pos power_le_one_iff)
  defer
proof -
  fix t
  let ?f = "\<lambda>s. (if t\<^sub>v s = t then 1::\<real> else (0::\<real>)) * (if x\<^sub>v s = (0::\<nat>) then 1::\<real> else (0::\<real>))"
  have "(\<Sum>\<^sub>\<infinity>s::state. ?f s) 
      = (\<Sum>\<^sub>\<infinity>s::state. (if t\<^sub>v s = t \<and> x\<^sub>v s = (0::\<nat>) then 1::\<real> else (0::\<real>)))"
    apply (rule infsum_cong)
    by force
  also have "... = 1"
    apply (rule infsum_singleton_cond_unique)
    apply (auto)
    by (meson state.select_convs(1) time.select_convs(1))
  finally show "(\<Sum>\<^sub>\<infinity>s::state. ?f s) = (1::\<real>)"
    by blast
next
  fix t::\<nat> and x::\<nat>
  assume a1: "(0::\<nat>) < x"
  let ?f1 = "\<lambda>s. (if x\<^sub>v s = (0::\<nat>) then 1::\<real> else (0::\<real>))"
  let ?f2 = "\<lambda>s. (if t + x \<le> t\<^sub>v s then 1::\<real> else (0::\<real>))"

  have set_eq: "{s. x\<^sub>v s = (0::\<nat>) \<and> t + x \<le> t\<^sub>v s} = {y::state. \<exists>xa::\<nat>. y = \<lparr>t\<^sub>v = t + x + xa, x\<^sub>v = 0::\<nat>\<rparr>}"
    apply (subst set_eq_iff)
    apply (auto)
    apply (rule_tac x = "t\<^sub>v xa - (t + x)" in exI)
    by simp
  have "(\<Sum>\<^sub>\<infinity>s::state. ?f1 s * ?f2 s * ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - (t + x)) / (2::\<real>)) = 
        (\<Sum>\<^sub>\<infinity>s::state. (if x\<^sub>v s = (0::\<nat>) \<and> t + x \<le> t\<^sub>v s then 
          ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - (t + x)) / (2::\<real>) else (0::\<real>)))"
    apply (rule infsum_cong)
    by force
  also have "... = (\<Sum>\<^sub>\<infinity>s::state \<in> {s. x\<^sub>v s = (0::\<nat>) \<and> t + x \<le> t\<^sub>v s}. 
                      ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - (t + x)) / (2::\<real>))"
    by (smt (verit, ccfv_SIG) DiffD2 Diff_UNIV IntE empty_iff infsum_cong_neutral mem_Collect_eq)
  also have "... = infsum (\<lambda>s. ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - (t + x)) / (2::\<real>)) ((\<lambda>n::\<nat>. \<lparr>t\<^sub>v = t + x + n, x\<^sub>v = 0\<rparr>) ` UNIV)"
    apply (simp add: image_def)
    using set_eq by presburger
  (* \<open>infsum g (h ` A) = infsum (g \<circ> h) A\<close> *)
  also have "...  = (\<Sum>\<^sub>\<infinity>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n / 2 )"
    apply (subst infsum_reindex)
    apply (simp add: inj_def)
    apply (rule infsum_cong)
    by (auto)
  also have "... = 1"
    apply (subst infsetsum_infsum[symmetric])
    apply (simp add: abs_summable_on_nat_iff')
    apply (subst infsetsum_nat)
    apply (simp add: abs_summable_on_nat_iff')
    apply auto
    using power_half_series sums_unique by fastforce
  finally show "(\<Sum>\<^sub>\<infinity>s::state. ?f1 s * ?f2 s * ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - (t + x)) / (2::\<real>)) = (1::\<real>)"
    by meson
qed

lemma Ht_is_fp: "\<F> (x\<^sup>< > 0)\<^sub>e (Pt move) (prfun_of_rvfun (Ht)) = prfun_of_rvfun (Ht)"
  apply (simp add: Ht_def loopfunc_def)
  apply (simp add: pfun_defs srw_move_t)
  apply (subst rvfun_skip_inverse)
  apply (subst rvfun_skip\<^sub>_f_simp)
  apply (subst rvfun_seqcomp_inverse)
  apply (simp add: move_t_alt_is_dist rvfun_inverse rvfun_prob_sum1_summable'(1))
  using ureal_is_prob apply blast
  apply (subst rvfun_inverse)
  apply (simp add: move_t_alt_is_dist rvfun_prob_sum1_summable'(1))
  apply (subst rvfun_inverse)
  apply (expr_auto add: dist_defs)
  apply (subgoal_tac "((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - (t + x))  \<le> 1")
  apply (smt (verit, ccfv_threshold) divide_le_eq_1_pos divide_nonneg_nonneg power_le_one)
  apply (simp add: power_le_one_iff)
  apply (simp only: move_t_alt_def)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (expr_simp_1)
  apply (pred_auto)
  defer
  apply (simp add: infsum_0)+
proof -
  fix t and x and t\<^sub>v'::\<nat>
  assume a1: "(0::\<nat>) < x"
  assume a2: "t + x \<le> t\<^sub>v'"
  let ?f = "\<lambda>v\<^sub>0::state.
          ((if x\<^sub>v v\<^sub>0 = Suc x then 1::\<real> else (0::\<real>)) * (if t\<^sub>v v\<^sub>0 = Suc t then 1::\<real> else (0::\<real>)) / (2::\<real>) +
           (if x\<^sub>v v\<^sub>0 = x - Suc (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if t\<^sub>v v\<^sub>0 = Suc t then 1::\<real> else (0::\<real>)) / (2::\<real>)) *
          ((if x\<^sub>v v\<^sub>0 = (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if t\<^sub>v' = t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) *
           (if x\<^sub>v v\<^sub>0 = (0::\<nat>) then 1::\<real> else (0::\<real>)) +
           (if (0::\<nat>) < x\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0 \<le> t\<^sub>v' then 1::\<real> else (0::\<real>)) *
           ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v' - (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0)) / (2::\<real>))"

  have set_eq_0: "{s::state. x\<^sub>v s = x - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc t \<and> x\<^sub>v s = (0::\<nat>) \<and> t\<^sub>v' = t\<^sub>v s} = 
        (if x = Suc 0 \<and> t\<^sub>v' = Suc t then {s::state. x\<^sub>v s = x - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc t} else {})"
    apply (auto)
    using a1 by linarith
  have card_set_0: "card {s::state. x\<^sub>v s = x - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc t \<and> x\<^sub>v s = (0::\<nat>) \<and> t\<^sub>v' = t\<^sub>v s} = 
    (if x = Suc 0 \<and> t\<^sub>v' = Suc t then 1 else 0)"
    apply (simp add: set_eq_0)
    apply (auto)
    by (smt (verit, best) card_1_singleton old.unit.exhaust state.select_convs(1) state.surjective time.select_convs(1))

  have set_eq_1: "{s::state. x\<^sub>v s = Suc x \<and> t\<^sub>v s = Suc t \<and> (0::\<nat>) < x\<^sub>v s \<and> Suc t + Suc x \<le> t\<^sub>v'} = 
    (if Suc t + Suc x \<le> t\<^sub>v' then {s::state. x\<^sub>v s = Suc x \<and> t\<^sub>v s = Suc t} else {})"
    by auto
  have card_set_1: "card {s::state. x\<^sub>v s = Suc x \<and> t\<^sub>v s = Suc t \<and> (0::\<nat>) < x\<^sub>v s \<and> Suc t + Suc x \<le> t\<^sub>v'} 
    = (if Suc t + Suc x \<le> t\<^sub>v' then 1 else 0)"
    apply (simp only: set_eq_1)
    apply auto
    by (smt (verit, best) card_1_singleton old.unit.exhaust state.select_convs(1) state.surjective time.select_convs(1))

  have set_eq_2: "{s::state. x\<^sub>v s = x - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc t \<and> (0::\<nat>) < x\<^sub>v s \<and> Suc t + x - Suc (0::\<nat>) \<le> t\<^sub>v'}
     = (if x > Suc 0 \<and> Suc t + x - Suc (0::\<nat>) \<le> t\<^sub>v' then {s::state. x\<^sub>v s = x - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc t} else {})"
    by (auto)
  have card_set_2: "card {s::state. x\<^sub>v s = x - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc t \<and> (0::\<nat>) < x\<^sub>v s \<and> Suc t + x - Suc (0::\<nat>) \<le> t\<^sub>v'} 
    = (if x > Suc 0 \<and> Suc t + x - Suc (0::\<nat>) \<le> t\<^sub>v' then 1 else 0)"
    apply (simp only: set_eq_2)
    apply (auto)
    by (smt (verit, best) card_1_singleton old.unit.exhaust state.select_convs(1) state.surjective time.select_convs(1))

  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state. ?f v\<^sub>0) = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state. 
          ((if x\<^sub>v v\<^sub>0 = Suc x \<and> t\<^sub>v v\<^sub>0 = Suc t then 1/2 else (0::\<real>)) +
           (if x\<^sub>v v\<^sub>0 = x - Suc (0::\<nat>) \<and> t\<^sub>v v\<^sub>0 = Suc t then 1/2 else (0::\<real>))) *
          ((if x\<^sub>v v\<^sub>0 = (0::\<nat>) \<and> t\<^sub>v' = t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) +
           (if (0::\<nat>) < x\<^sub>v v\<^sub>0 \<and> t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0 \<le> t\<^sub>v' then ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v' - (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0)) / (2::\<real>) else (0::\<real>))
           ))"
    apply (rule infsum_cong)
    by simp
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state. 
          (if x\<^sub>v v\<^sub>0 = x - Suc (0::\<nat>) \<and> t\<^sub>v v\<^sub>0 = Suc t \<and> x\<^sub>v v\<^sub>0 = (0::\<nat>) \<and> t\<^sub>v' = t\<^sub>v v\<^sub>0 then 1/2 else 0) + 
          (if x\<^sub>v v\<^sub>0 = Suc x \<and> t\<^sub>v v\<^sub>0 = Suc t \<and> (0::\<nat>) < x\<^sub>v v\<^sub>0 \<and> Suc t + Suc x \<le> t\<^sub>v' then 
            ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v' - (Suc t + Suc x)) / (2::\<real>) / 2 else 0) + 
          (if x\<^sub>v v\<^sub>0 = x - Suc (0::\<nat>) \<and> t\<^sub>v v\<^sub>0 = Suc t \<and> (0::\<nat>) < x\<^sub>v v\<^sub>0 \<and> Suc t + x - Suc (0::\<nat>) \<le> t\<^sub>v' then 
            ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v' - (Suc t + x - Suc (0::\<nat>))) / (2::\<real>) / 2 else 0))"
    apply (rule infsum_cong)
    by (auto)
  also have "... = ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v' - (t + x)) / 2"
    apply (subst infsum_add)
    apply (subst summable_on_add)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_threshold) Collect_mem_eq Collect_mono_iff Zero_not_Suc card.infinite card_1_singleton finite.simps old.unit.exhaust rev_finite_subset state.surjective)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_threshold) Collect_mem_eq Collect_mono_iff Zero_not_Suc card.infinite card_1_singleton finite.simps old.unit.exhaust rev_finite_subset state.surjective)
    apply (simp)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_threshold) Collect_mem_eq Collect_mono_iff Zero_not_Suc card.infinite card_1_singleton finite.simps old.unit.exhaust rev_finite_subset state.surjective)
    apply (subst infsum_add)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_threshold) Collect_mem_eq Collect_mono_iff Zero_not_Suc card.infinite card_1_singleton finite.simps old.unit.exhaust rev_finite_subset state.surjective)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_threshold) Collect_mem_eq Collect_mono_iff Zero_not_Suc card.infinite card_1_singleton finite.simps old.unit.exhaust rev_finite_subset state.surjective)
    apply (subst infsum_constant_finite_states)
    apply (smt (verit, del_insts) Collect_mem_eq Collect_mono card.infinite card_1_singleton finite.simps nat.distinct(1) old.unit.exhaust rev_finite_subset state.surjective)
    apply (subst infsum_constant_finite_states)
    apply (smt (verit, del_insts) Collect_mem_eq Collect_mono card.infinite card_1_singleton finite.simps nat.distinct(1) old.unit.exhaust rev_finite_subset state.surjective)
    apply (subst infsum_constant_finite_states)
    apply (smt (verit, del_insts) Collect_mem_eq Collect_mono card.infinite card_1_singleton finite.simps nat.distinct(1) old.unit.exhaust rev_finite_subset state.surjective)
    apply (simp only: card_set_0 card_set_1 card_set_2)
    apply (auto)
    sledgehammer
    by simp

    show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state. ?f v\<^sub>0) * (2::\<real>) = ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v' - (t + x))"
  qed

end
