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
  then show ?case by simp
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

lemma mu_lp_p_m:
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

lemma mu_lp_p_m_plus_1:
  shows "(\<mu>\<^sub>l\<^sub>p p m m) * p = \<mu>\<^sub>l\<^sub>p p (m+1) (m+1)"
  using mu_lp_p_m by fastforce

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

lemma Pt_step_is_dist: "is_final_distribution (rvfun_of_prfun (Pt (step p)))"
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
  apply (simp add: Pt_step_is_dist)
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
  apply (simp add: Pt_step_simp Pt_step_alt_def skip_def)
  apply (pred_auto)
  proof -
    fix t::"\<nat>" and x::"\<nat>" and t\<^sub>v':: "\<nat>" and x\<^sub>v'::"\<nat>"
    let ?b1 = "\<lambda>s::state \<times> state. \<lambda>v\<^sub>0::state. x\<^sub>v v\<^sub>0 = x\<^sub>v (fst s) - Suc (0::\<nat>) \<and> t\<^sub>v v\<^sub>0 = Suc (t\<^sub>v (fst s))"
    let ?b2 = "\<lambda>s::state \<times> state. \<lambda>v\<^sub>0::state. x\<^sub>v v\<^sub>0 = Suc (x\<^sub>v (fst s)) \<and> t\<^sub>v v\<^sub>0 = Suc (t\<^sub>v (fst s))"
    let ?b3 = "\<lambda>s::state \<times> state. \<lambda>v\<^sub>0::state. x\<^sub>v v\<^sub>0 = (0::\<nat>) \<and> t\<^sub>v (snd s) = t\<^sub>v v\<^sub>0 \<and> x\<^sub>v (snd s) = x\<^sub>v v\<^sub>0"
    let ?b4 = "\<lambda>s::state \<times> state. \<lambda>v\<^sub>0::state. (0::\<nat>) < x\<^sub>v v\<^sub>0 \<and> x\<^sub>v (snd s) = (0::\<nat>) \<and> 
                  t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0 \<le> t\<^sub>v (snd s) \<and> (t\<^sub>v (snd s) - (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0)) mod (2::\<nat>) = (0::\<nat>)"
    let ?b5 = "\<lambda>s::state \<times> state. \<lambda>v\<^sub>0::state. (0::\<nat>) < x\<^sub>v v\<^sub>0 \<and> x\<^sub>v (snd s) = (0::\<nat>) \<and> 
                  Suc (Suc (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0)) \<le> t\<^sub>v (snd s) \<and> 
                  (t\<^sub>v (snd s) - Suc (Suc (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0))) mod (2::\<nat>) = (0::\<nat>)"
    
    let ?lhs = "\<lambda>s::state \<times> state. (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
                 ((if ?b1 s v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p +
                  (if ?b2 s v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
                 ((if x\<^sub>v v\<^sub>0 = (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if t\<^sub>v (snd s) = t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if x\<^sub>v (snd s) = x\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) +
                  (if (0::\<nat>) < x\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if x\<^sub>v (snd s) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
                  ((if t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0 \<le> t\<^sub>v (snd s) then 1::\<real> else (0::\<real>)) * (if (t\<^sub>v (snd s) - (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0)) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
                   \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v v\<^sub>0 - Suc (0::\<nat>)) (t\<^sub>v (snd s) - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p +
                   (if Suc (Suc (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0)) \<le> t\<^sub>v (snd s) then 1::\<real> else (0::\<real>)) *
                   (if (t\<^sub>v (snd s) - Suc (Suc (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0))) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
                   \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v v\<^sub>0)) (t\<^sub>v (snd s) - Suc (t\<^sub>v v\<^sub>0)) * ((1::\<real>) - ureal2real p))))"
    let ?rhs = "(\<lambda>s::state \<times> state.
              (if x\<^sub>v (fst s) = (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if t\<^sub>v (snd s) = t\<^sub>v (fst s) then 1::\<real> else (0::\<real>)) *
              (if x\<^sub>v (snd s) = x\<^sub>v (fst s) then 1::\<real> else (0::\<real>)) +
              (if (0::\<nat>) < x\<^sub>v (fst s) then 1::\<real> else (0::\<real>)) * (if x\<^sub>v (snd s) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
              ((if t\<^sub>v (fst s) + x\<^sub>v (fst s) \<le> t\<^sub>v (snd s) then 1::\<real> else (0::\<real>)) *
               (if (t\<^sub>v (snd s) - (t\<^sub>v (fst s) + x\<^sub>v (fst s))) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
               \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst s) - Suc (0::\<nat>)) (t\<^sub>v (snd s) - Suc (t\<^sub>v (fst s))) *
               ureal2real p +
               (if Suc (Suc (t\<^sub>v (fst s) + x\<^sub>v (fst s))) \<le> t\<^sub>v (snd s) then 1::\<real> else (0::\<real>)) *
               (if (t\<^sub>v (snd s) - Suc (Suc (t\<^sub>v (fst s) + x\<^sub>v (fst s)))) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
               \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst s))) (t\<^sub>v (snd s) - Suc (t\<^sub>v (fst s))) *
               ((1::\<real>) - ureal2real p)))"
  
    have "prfun_of_rvfun
          (\<lambda>\<s>::state \<times> state.
              (if (0::\<nat>) < x\<^sub>v (fst \<s>) then 1::\<real> else (0::\<real>)) * ?lhs \<s> +
              (if x\<^sub>v (fst \<s>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if snd \<s> = fst \<s> then 1::\<real> else (0::\<real>)))
        = prfun_of_rvfun ?rhs"
      apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
      apply (simp only: fun_eq_iff) 
      apply (rule allI)
      proof -
        fix x :: "state \<times> state"
    
        have s1: "{s::state. (x\<^sub>v s = x\<^sub>v (fst x) - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc (t\<^sub>v (fst x))) \<and> x\<^sub>v s = (0::\<nat>) \<and> t\<^sub>v (snd x) = t\<^sub>v s \<and> x\<^sub>v (snd x) = x\<^sub>v s} 
          = (if x\<^sub>v (fst x) - Suc (0::\<nat>) = 0 \<and> x\<^sub>v (snd x) = 0 \<and> Suc (t\<^sub>v (fst x)) = t\<^sub>v (snd x) then {\<lparr>t\<^sub>v = Suc (t\<^sub>v (fst x)), x\<^sub>v = 0\<rparr>} else {})"
          by (smt (verit, best) Collect_cong Collect_empty_eq old.unit.exhaust singleton_conv state.surjective)
        then have fin_s1: "finite {s::state. (x\<^sub>v s = x\<^sub>v (fst x) - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc (t\<^sub>v (fst x))) \<and> x\<^sub>v s = (0::\<nat>) \<and> t\<^sub>v (snd x) = t\<^sub>v s \<and> x\<^sub>v (snd x) = x\<^sub>v s}"
          by auto
    
        have s2: "{s::state. (x\<^sub>v s = x\<^sub>v (fst x) - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc (t\<^sub>v (fst x))) \<and> (0::\<nat>) < x\<^sub>v s 
            \<and> x\<^sub>v (snd x) = (0::\<nat>) \<and> t\<^sub>v s + x\<^sub>v s \<le> t\<^sub>v (snd x) \<and> (t\<^sub>v (snd x) - (t\<^sub>v s + x\<^sub>v s)) mod (2::\<nat>) = (0::\<nat>)}
          = (if x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>) \<le> t\<^sub>v (snd x) \<and>
                (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>))) mod (2::\<nat>) = (0::\<nat>) then 
              {\<lparr>t\<^sub>v = Suc (t\<^sub>v (fst x)), x\<^sub>v = x\<^sub>v (fst x) - Suc (0::\<nat>)\<rparr>} else {})"
          by (auto)
        then have fin_s2: "finite {s::state. (x\<^sub>v s = x\<^sub>v (fst x) - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc (t\<^sub>v (fst x))) \<and> (0::\<nat>) < x\<^sub>v s 
            \<and> x\<^sub>v (snd x) = (0::\<nat>) \<and> t\<^sub>v s + x\<^sub>v s \<le> t\<^sub>v (snd x) \<and> (t\<^sub>v (snd x) - (t\<^sub>v s + x\<^sub>v s)) mod (2::\<nat>) = (0::\<nat>)}"
          by auto
    
        have s3: " {s::state. (x\<^sub>v s = x\<^sub>v (fst x) - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc (t\<^sub>v (fst x))) \<and> (0::\<nat>) < x\<^sub>v s \<and>
          x\<^sub>v (snd x) = (0::\<nat>) \<and> Suc (Suc (t\<^sub>v s + x\<^sub>v s)) \<le> t\<^sub>v (snd x) \<and> (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v s + x\<^sub>v s))) mod (2::\<nat>) = (0::\<nat>)}
          = (if x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                Suc (Suc (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>))) \<le> t\<^sub>v (snd x) \<and>
                (t\<^sub>v (snd x) - Suc (Suc (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>)))) mod (2::\<nat>) = (0::\<nat>) then 
              {\<lparr>t\<^sub>v = Suc (t\<^sub>v (fst x)), x\<^sub>v = x\<^sub>v (fst x) - Suc (0::\<nat>)\<rparr>} else {})"
          by (auto)
        then have fin_s3: "finite {s::state. (x\<^sub>v s = x\<^sub>v (fst x) - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc (t\<^sub>v (fst x))) \<and> (0::\<nat>) < x\<^sub>v s \<and>
          x\<^sub>v (snd x) = (0::\<nat>) \<and> Suc (Suc (t\<^sub>v s + x\<^sub>v s)) \<le> t\<^sub>v (snd x) \<and> (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v s + x\<^sub>v s))) mod (2::\<nat>) = (0::\<nat>)}"
          by auto
    
        have s4: "{s::state. (x\<^sub>v s = Suc (x\<^sub>v (fst x)) \<and> t\<^sub>v s = Suc (t\<^sub>v (fst x))) \<and> (0::\<nat>) < x\<^sub>v s \<and> 
              x\<^sub>v (snd x) = (0::\<nat>) \<and> t\<^sub>v s + x\<^sub>v s \<le> t\<^sub>v (snd x) \<and> (t\<^sub>v (snd x) - (t\<^sub>v s + x\<^sub>v s)) mod (2::\<nat>) = (0::\<nat>)}
          = (if Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                Suc (t\<^sub>v (fst x)) + Suc (x\<^sub>v (fst x)) \<le> t\<^sub>v (snd x) \<and>
                (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)) + Suc (x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>) then 
              {\<lparr>t\<^sub>v = Suc (t\<^sub>v (fst x)), x\<^sub>v = Suc (x\<^sub>v (fst x))\<rparr>} else {})"
          by auto
        then have fin_s4: "finite {s::state. (x\<^sub>v s = Suc (x\<^sub>v (fst x)) \<and> t\<^sub>v s = Suc (t\<^sub>v (fst x))) \<and> (0::\<nat>) < x\<^sub>v s \<and> 
              x\<^sub>v (snd x) = (0::\<nat>) \<and> t\<^sub>v s + x\<^sub>v s \<le> t\<^sub>v (snd x) \<and> (t\<^sub>v (snd x) - (t\<^sub>v s + x\<^sub>v s)) mod (2::\<nat>) = (0::\<nat>)}"
          by auto
    
        have s5: "{s::state. (x\<^sub>v s = Suc (x\<^sub>v (fst x)) \<and> t\<^sub>v s = Suc (t\<^sub>v (fst x))) \<and> (0::\<nat>) < x\<^sub>v s \<and>
          x\<^sub>v (snd x) = (0::\<nat>) \<and> Suc (Suc (t\<^sub>v s + x\<^sub>v s)) \<le> t\<^sub>v (snd x) \<and> (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v s + x\<^sub>v s))) mod (2::\<nat>) = (0::\<nat>)}
          = (if Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                Suc (Suc (Suc (t\<^sub>v (fst x))) + Suc (x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x) \<and>
                (t\<^sub>v (snd x) - (Suc (Suc (Suc (t\<^sub>v (fst x))) + Suc (x\<^sub>v (fst x))))) mod (2::\<nat>) = (0::\<nat>) then 
              {\<lparr>t\<^sub>v = Suc (t\<^sub>v (fst x)), x\<^sub>v = Suc (x\<^sub>v (fst x))\<rparr>} else {})"
          by auto
        then have fin_s5: "finite {s::state. (x\<^sub>v s = Suc (x\<^sub>v (fst x)) \<and> t\<^sub>v s = Suc (t\<^sub>v (fst x))) \<and> (0::\<nat>) < x\<^sub>v s \<and>
          x\<^sub>v (snd x) = (0::\<nat>) \<and> Suc (Suc (t\<^sub>v s + x\<^sub>v s)) \<le> t\<^sub>v (snd x) \<and> (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v s + x\<^sub>v s))) mod (2::\<nat>) = (0::\<nat>)}"
          by auto
    
        have lhs_1: "?lhs x = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
                   ((if ?b1 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p +
                    (if ?b2 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
                   ((if ?b3 x v\<^sub>0 then 1::\<real> else (0::\<real>)) +
                    (if ?b4 x v\<^sub>0 then 1::\<real> else (0::\<real>)) *
                      \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v v\<^sub>0 - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p +
                    (if ?b5 x v\<^sub>0 then 1::\<real> else (0::\<real>)) *
                      \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v v\<^sub>0)) (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) * ((1::\<real>) - ureal2real p)
                    ))"
        apply (rule infsum_cong)
        by (simp)
        also have lhs_2: "... =  (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
                     (((if ?b1 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p) * 
                       (if ?b3 x v\<^sub>0 then 1::\<real> else (0::\<real>)) +
                      ((if ?b2 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
                      (if ?b3 x v\<^sub>0 then 1::\<real> else (0::\<real>))
                    ) + 
                    (((if ?b1 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p) *
                     ((if ?b4 x v\<^sub>0 then 1::\<real> else (0::\<real>)) *
                        \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v v\<^sub>0 - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p) +
                     ((if ?b1 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p) *
                     ((if ?b5 x v\<^sub>0 then 1::\<real> else (0::\<real>)) *
                        \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v v\<^sub>0)) (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) * ((1::\<real>) - ureal2real p)) + 
                     ((if ?b2 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
                     ((if ?b4 x v\<^sub>0 then 1::\<real> else (0::\<real>)) *
                        \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v v\<^sub>0 - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p) +
                     ((if ?b2 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
                     ((if ?b5 x v\<^sub>0 then 1::\<real> else (0::\<real>)) *
                        \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v v\<^sub>0)) (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) * ((1::\<real>) - ureal2real p))
                  )
              )"
          apply (rule infsum_cong)
          by (simp add: comm_semiring_class.distrib distrib_left)
        also have lhs_3: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
             (if ?b1 x v\<^sub>0 \<and> ?b3 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p +
             ((if ?b1 x v\<^sub>0 \<and> ?b4 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * (ureal2real p * 
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v v\<^sub>0 - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p)) +
             ((if ?b1 x v\<^sub>0 \<and> ?b5 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * (ureal2real p *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v v\<^sub>0)) (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) * ((1::\<real>) - ureal2real p))) + 
             ((if ?b2 x v\<^sub>0 \<and> ?b4 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * (((1::\<real>) - ureal2real p) *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v v\<^sub>0 - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) * ureal2real p)) +
             ((if ?b2 x v\<^sub>0 \<and> ?b5 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * (((1::\<real>) - ureal2real p) *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v v\<^sub>0)) (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) * ((1::\<real>) - ureal2real p))
             )
          )"
          apply (rule infsum_cong)
          by (smt (verit) less_Suc_eq_0_disj less_numeral_extra(3) mult.assoc mult_cancel_left1 mult_eq_0_iff)
        also have lhs_4: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
             (if ?b1 x v\<^sub>0 \<and> ?b3 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * ureal2real p +
             ((if ?b1 x v\<^sub>0 \<and> ?b4 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * (ureal2real p * 
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ureal2real p)) +
             ((if ?b1 x v\<^sub>0 \<and> ?b5 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * (ureal2real p *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x) - Suc (0::\<nat>))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ((1::\<real>) - ureal2real p))) + 
             ((if ?b2 x v\<^sub>0 \<and> ?b4 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * (((1::\<real>) - ureal2real p) *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) ( Suc (x\<^sub>v (fst x)) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ureal2real p)) +
             ((if ?b2 x v\<^sub>0 \<and> ?b5 x v\<^sub>0 then 1::\<real> else (0::\<real>)) * (((1::\<real>) - ureal2real p) *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (Suc (x\<^sub>v (fst x)))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ((1::\<real>) - ureal2real p))
             )
          )"
          apply (rule infsum_cong)
          by (smt (verit) mult_cancel_left1)
        also have lhs_5: "... =  card {v\<^sub>0. ?b1 x v\<^sub>0 \<and> ?b3 x v\<^sub>0} * ureal2real p + 
            card {v\<^sub>0. ?b1 x v\<^sub>0 \<and> ?b4 x v\<^sub>0} * (ureal2real p * 
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ureal2real p) + 
            card {v\<^sub>0. ?b1 x v\<^sub>0 \<and> ?b5 x v\<^sub>0} * (ureal2real p *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x) - Suc (0::\<nat>))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ((1::\<real>) - ureal2real p)) + 
            card {v\<^sub>0. ?b2 x v\<^sub>0 \<and> ?b4 x v\<^sub>0} * (((1::\<real>) - ureal2real p) *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) ( Suc (x\<^sub>v (fst x)) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ureal2real p) + 
            card {v\<^sub>0. ?b2 x v\<^sub>0 \<and> ?b5 x v\<^sub>0} * (((1::\<real>) - ureal2real p) *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (Suc (x\<^sub>v (fst x)))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ((1::\<real>) - ureal2real p))
          "
          apply (subst infsum_constant_finite_states_cmult_5)
          using fin_s1 apply blast
          using fin_s2 apply blast
          using fin_s3 apply blast
          using fin_s4 apply blast
          using fin_s5 apply blast
          by linarith
        also have lhs_6: "... = (if x\<^sub>v (fst x) - Suc (0::\<nat>) = 0 \<and> x\<^sub>v (snd x) = 0 \<and> Suc (t\<^sub>v (fst x)) = t\<^sub>v (snd x)then 1 else 0) * ureal2real p + 
            (if x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>) \<le> t\<^sub>v (snd x) \<and>
                  (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>))) mod (2::\<nat>) = (0::\<nat>) then 1 else 0) * (ureal2real p * 
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ureal2real p) +
            (if (x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  Suc (Suc (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>))) \<le> t\<^sub>v (snd x) \<and>
                  (t\<^sub>v (snd x) - Suc (Suc (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * (ureal2real p *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x) - Suc (0::\<nat>))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ((1::\<real>) - ureal2real p)) +
            (if Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  Suc (t\<^sub>v (fst x)) + Suc (x\<^sub>v (fst x)) \<le> t\<^sub>v (snd x) \<and>
                  (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)) + Suc (x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>) then 1 else 0) * (((1::\<real>) - ureal2real p) *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) ( Suc (x\<^sub>v (fst x)) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ureal2real p) + 
            (if Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  Suc (Suc (Suc (t\<^sub>v (fst x))) + Suc (x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x) \<and>
                  (t\<^sub>v (snd x) - (Suc (Suc (Suc (t\<^sub>v (fst x))) + Suc (x\<^sub>v (fst x))))) mod (2::\<nat>) = (0::\<nat>) then 1 else 0) * (((1::\<real>) - ureal2real p) *
                \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (Suc (x\<^sub>v (fst x)))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) * ((1::\<real>) - ureal2real p))"
          using s1 s2 s3 s4 s5 by (smt (verit) One_nat_def card.empty card_1_singleton_iff of_nat_0 of_nat_1)
        (* Rewrite these inequalities*)
        have t'_ieq_1: "(Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>) \<le> t\<^sub>v (snd x)) = (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x))"
          by simp
        have even_1: "((t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>))) mod (2::\<nat>) = (0::\<nat>)) =
              ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>))"
          using One_nat_def add_Suc diff_Suc_1 by presburger
        
        have t'_ieq_2: "(Suc (Suc (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>))) \<le> t\<^sub>v (snd x)) = (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x))"
          by simp
      
        have even_2: "(Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<Longrightarrow> 
              ((t\<^sub>v (snd x) - Suc (Suc ((t\<^sub>v (fst x)) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) =
              ((t\<^sub>v (snd x) - ((t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>))"
          by fastforce
        
        have t'_ieq_3: "(Suc (t\<^sub>v (fst x)) + Suc (x\<^sub>v (fst x)) \<le> t\<^sub>v (snd x)) =
                        (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x))"
          by auto
        have even_3: "((t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)) + Suc (x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) = 
                ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>))"
          by presburger
      
        have t'_ieq_4: "(Suc (Suc (Suc (t\<^sub>v (fst x))) + Suc (x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) =
                        (Suc (Suc (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))))) \<le> t\<^sub>v (snd x))"
          by auto
        have even_4: "(Suc (Suc (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))))) \<le> t\<^sub>v (snd x)) \<Longrightarrow>
                ((t\<^sub>v (snd x) - (Suc (Suc (Suc (t\<^sub>v (fst x))) + Suc (x\<^sub>v (fst x))))) mod (2::\<nat>) = (0::\<nat>)) = 
                ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>))"
          by fastforce
      
        have operand_2_split: "
       \<comment> \<open>2\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p)
          = 
       \<comment> \<open>2.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 2) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p) +
       \<comment> \<open>2.2\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 2) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p)"
          by (smt (verit, del_insts) cancel_comm_monoid_add_class.diff_zero diff_add_inverse2 diff_diff_cancel 
              diff_diff_left le_Suc_eq mult_not_zero nat_1_add_1 not_less_eq_eq one_mod_two_eq_one plus_1_eq_Suc)
        
        have operands_2_3_merge: "
       \<comment> \<open>2\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and>
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p) +
       \<comment> \<open>3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - ((t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x) - Suc (0::\<nat>))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ((1::\<real>) - ureal2real p))
          =
       \<comment> \<open>2.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 2) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p) +
       \<comment> \<open>2.2+3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * ((\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 2) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p +
                     (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ((1::\<real>) - ureal2real p)))"
          apply (simp only: operand_2_split)
          by (simp add: distrib_left)
        have operands_2_3_merge': "... = 
       \<comment> \<open>2.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 2) (x\<^sub>v (fst x) - 2)) * ureal2real p) +
       \<comment> \<open>2.2+3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x))))))"
          using mu_lp.simps(4) by (smt (verit) Suc_diff_Suc add.commute add_Suc diff_add_inverse2 
             diff_is_0_eq le_Suc_eq le_numeral_extra(3) left_diff_distrib' mu_lp.elims mult.commute 
             nat_1_add_1 not_less_eq_eq plus_1_eq_Suc zero_less_Suc zero_less_diff)
      
        have operand_4_split: " 
       \<comment> \<open>4\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) ( Suc (x\<^sub>v (fst x)) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p)
        =
       \<comment> \<open>4.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x)) (x\<^sub>v (fst x))) * ureal2real p) + 
       \<comment> \<open>4.2\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) ( Suc (x\<^sub>v (fst x)) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p)"
          using le_Suc_eq not_less_eq_eq by auto
      
        have operands_4_5_merge: " 
       \<comment> \<open>4\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) ( Suc (x\<^sub>v (fst x)) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p) + 
       \<comment> \<open>5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (Suc (x\<^sub>v (fst x)))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ((1::\<real>) - ureal2real p)) 
        =
       \<comment> \<open>4.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x)) (x\<^sub>v (fst x))) * ureal2real p) + 
       \<comment> \<open>4.2 + 5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * ((\<mu>\<^sub>l\<^sub>p (ureal2real p) ( Suc (x\<^sub>v (fst x)) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p +
                  (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (Suc (x\<^sub>v (fst x)))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ((1::\<real>) - ureal2real p)))"
          apply (simp only: operand_4_split)
          by (simp add: distrib_left)
        have operands_4_5_merge': "... = 
       \<comment> \<open>4.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x)) (x\<^sub>v (fst x))) * ureal2real p) + 
       \<comment> \<open>4.2 + 5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x))) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x))))))"
          using mu_lp.simps(4)
          by (smt (verit) Suc_diff_Suc add.commute bot_nat_0.not_eq_extremum diff_Suc_Suc diff_add_inverse 
              diff_is_0_eq distrib_left le_Suc_eq mu_lp.simps(3) mult.commute plus_1_eq_Suc zero_less_diff)
      
        have lhs_7: "(if (0::\<nat>) < x\<^sub>v (fst x) then 1::\<real> else (0::\<real>)) * ?lhs x +
                  (if x\<^sub>v (fst x) = (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if snd x = fst x then 1::\<real> else (0::\<real>))
          = 
       \<comment> \<open>1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) = 0 \<and> x\<^sub>v (snd x) = 0 \<and> Suc (t\<^sub>v (fst x)) = t\<^sub>v (snd x)then 1 else 0) * ureal2real p + 
       \<comment> \<open>2\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>) \<le> t\<^sub>v (snd x) \<and>
                  (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>))) mod (2::\<nat>) = (0::\<nat>) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p) +
       \<comment> \<open>3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> (x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  Suc (Suc (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>))) \<le> t\<^sub>v (snd x) \<and>
                  (t\<^sub>v (snd x) - Suc (Suc (Suc (t\<^sub>v (fst x)) + x\<^sub>v (fst x) - Suc (0::\<nat>)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x) - Suc (0::\<nat>))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ((1::\<real>) - ureal2real p)) +
       \<comment> \<open>4\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  Suc (t\<^sub>v (fst x)) + Suc (x\<^sub>v (fst x)) \<le> t\<^sub>v (snd x) \<and>
                  (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)) + Suc (x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) ( Suc (x\<^sub>v (fst x)) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p) + 
       \<comment> \<open>5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  Suc (Suc (Suc (t\<^sub>v (fst x))) + Suc (x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x) \<and>
                  (t\<^sub>v (snd x) - (Suc (Suc (Suc (t\<^sub>v (fst x))) + Suc (x\<^sub>v (fst x))))) mod (2::\<nat>) = (0::\<nat>) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (Suc (x\<^sub>v (fst x)))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ((1::\<real>) - ureal2real p)) +
       \<comment> \<open>6\<close> (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>))"
          apply (simp only: lhs_1 lhs_2 lhs_3 lhs_4 lhs_5 lhs_6)
          by auto
        have lhs_8: "... = 
       \<comment> \<open>1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) = 0 \<and> x\<^sub>v (snd x) = 0 \<and> Suc (t\<^sub>v (fst x)) = t\<^sub>v (snd x)then 1 else 0) * ureal2real p + 
       \<comment> \<open>2\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p) +
       \<comment> \<open>3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - ((t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x) - Suc (0::\<nat>))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ((1::\<real>) - ureal2real p)) +
       \<comment> \<open>4\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) ( Suc (x\<^sub>v (fst x)) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ureal2real p) + 
       \<comment> \<open>5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (Suc (x\<^sub>v (fst x)))) (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x))))) * ((1::\<real>) - ureal2real p)) +
       \<comment> \<open>6\<close> (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>))"
          using t'_ieq_1 t'_ieq_2 t'_ieq_3 t'_ieq_4 even_1 even_2 even_3 even_4 by (smt (verit) One_nat_def add.commute add_Suc_right diff_Suc_1)
        have lhs_9: "... = 
       \<comment> \<open>1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) = 0 \<and> x\<^sub>v (snd x) = 0 \<and> Suc (t\<^sub>v (fst x)) = t\<^sub>v (snd x)then 1 else 0) * ureal2real p + 
       \<comment> \<open>2.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 2) (x\<^sub>v (fst x) - 2)) * ureal2real p) +
       \<comment> \<open>2.2+3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>4.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x)) (x\<^sub>v (fst x))) * ureal2real p) + 
       \<comment> \<open>4.2 + 5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x))) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>6\<close> (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>))"
          using operands_2_3_merge operands_2_3_merge' operands_4_5_merge operands_4_5_merge' by (smt (verit, best))
      
        have lhs_10: "... =
       \<comment> \<open>1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) = 0 \<and> x\<^sub>v (snd x) = 0 \<and> Suc (t\<^sub>v (fst x)) = t\<^sub>v (snd x)then 1 else 0) * ureal2real p + 
       \<comment> \<open>2.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 1) (x\<^sub>v (fst x) - 1))) +
       \<comment> \<open>2.2+3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>4.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) + 1) (x\<^sub>v (fst x) + 1))) + 
       \<comment> \<open>4.2 + 5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x))) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>6\<close> (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>))"
          using mu_lp_p_m_plus_1
          by (smt (verit, ccfv_threshold) One_nat_def Suc_1 Suc_pred diff_diff_left left_diff_distrib mu_lp_p_m mult.assoc mult.commute plus_1_eq_Suc power_Suc)
      
        have lhs_11: "... = 
       \<comment> \<open>1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) = 0 \<and> x\<^sub>v (snd x) = 0 \<and> Suc (t\<^sub>v (fst x)) = t\<^sub>v (snd x)then 1 else 0) * ureal2real p + 
       \<comment> \<open>2.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>2.2+3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>4.1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) = t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) + 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) + 
       \<comment> \<open>4.2 + 5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x))) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>6\<close> (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>))"
          by (smt (verit) add.commute add_Suc_right cancel_ab_semigroup_add_class.add_diff_cancel_left' diff_commute mult_cancel_left plus_1_eq_Suc)
      
        have lhs_12: "... =
       \<comment> \<open>1\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) = 0 \<and> x\<^sub>v (snd x) = 0 \<and> Suc (t\<^sub>v (fst x)) = t\<^sub>v (snd x)then 1 else 0) * ureal2real p + 
       \<comment> \<open>2.1+2.2+3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>4.1+4.2+5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) + 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) + 
       \<comment> \<open>6\<close> (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>))"
          by simp
      
        have lhs_13: "... =
       \<comment> \<open> Rewrite 1 \<close>
       \<comment> \<open>1\<close> (if x\<^sub>v (fst x) = 1 \<and> x\<^sub>v (snd x) = 0 \<and> (t\<^sub>v (fst x) + x\<^sub>v (fst x) = t\<^sub>v (snd x)) then 1 else 0) * (
              ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) + 
       \<comment> \<open>2.1+2.2+3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>4.1+4.2+5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) + 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) + 
       \<comment> \<open>6\<close> (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>))"
          by (simp)
      
        have lhs_14: "... =
       \<comment> \<open> Rewrite 1: from (t\<^sub>v (fst x) + x\<^sub>v (fst x) = t\<^sub>v (snd x)) to (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<close>
       \<comment> \<open>1\<close> (if x\<^sub>v (fst x) = 1 \<and> x\<^sub>v (snd x) = 0 \<and> (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<and> 
                ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * (
              ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) + 
       \<comment> \<open>2.1+2.2+3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (fst x) - Suc (0::\<nat>) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>4.1+4.2+5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) + 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) + 
       \<comment> \<open>6\<close> (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>))"
          by (smt (z3) Suc_1 Suc_diff_1 Suc_eq_plus1 bot_nat_0.not_eq_extremum 
              cancel_comm_monoid_add_class.diff_zero diff_diff_cancel diff_self_eq_0 mod_less mu_lp.simps(2) mult.commute mult_if_delta nat_le_linear)
      
        have lhs_15: "... =
       \<comment> \<open> Rewrite 1: from (t\<^sub>v (fst x) + x\<^sub>v (fst x) = t\<^sub>v (snd x)) to (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<close>
       \<comment> \<open>1+2.1+2.2+3\<close> (if x\<^sub>v (fst x) \<ge> 1 \<and> x\<^sub>v (snd x) = 0 \<and> (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<and>
                ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * (
              ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>4.1+4.2+5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> Suc (x\<^sub>v (fst x)) > 0 \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) + 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) + 
       \<comment> \<open>6\<close> (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>))"
          by fastforce
      
        have lhs_16: "... =
       \<comment> \<open> Rewrite 1: from (t\<^sub>v (fst x) + x\<^sub>v (fst x) = t\<^sub>v (snd x)) to (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<close>
       \<comment> \<open>1+2.1+2.2+3\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (snd x) = 0 \<and> (t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x)) \<and>
                ((t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * (
              ureal2real p * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) +
       \<comment> \<open>4.1+4.2+5\<close> (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (snd x) = 0 \<and> 
                  (Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x)) \<and>
                  ((t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>)) then 1 else 0) * 
                (((1::\<real>) - ureal2real p) * (\<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) + 1) (t\<^sub>v (snd x) - (Suc (t\<^sub>v (fst x)))))) + 
       \<comment> \<open>6\<close> (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>))"
          by fastforce
   
        have rhs_1: "?rhs x =
          (if x\<^sub>v (fst x) = (0::\<nat>) \<and> snd x = fst x then 1::\<real> else (0::\<real>)) +
          (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (snd x) = (0::\<nat>) \<and> t\<^sub>v (fst x) + x\<^sub>v (fst x) \<le> t\<^sub>v (snd x) \<and> 
              (t\<^sub>v (snd x) - (t\<^sub>v (fst x) + x\<^sub>v (fst x))) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
            \<mu>\<^sub>l\<^sub>p (ureal2real p) (x\<^sub>v (fst x) - Suc (0::\<nat>)) (t\<^sub>v (snd x) - Suc (t\<^sub>v (fst x))) * ureal2real p +
          (if (0::\<nat>) < x\<^sub>v (fst x) \<and> x\<^sub>v (snd x) = (0::\<nat>) \<and> Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x))) \<le> t\<^sub>v (snd x) \<and>
              (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x) + x\<^sub>v (fst x)))) mod (2::\<nat>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
            \<mu>\<^sub>l\<^sub>p (ureal2real p) (Suc (x\<^sub>v (fst x))) (t\<^sub>v (snd x) - Suc (t\<^sub>v (fst x))) * ((1::\<real>) - ureal2real p)"
          by auto
      
        show "(if (0::\<nat>) < x\<^sub>v (fst x) then 1::\<real> else (0::\<real>)) * ?lhs x +
                (if x\<^sub>v (fst x) = (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if snd x = fst x then 1::\<real> else (0::\<real>)) 
          = ?rhs x"
          apply (simp only: lhs_7 lhs_8 lhs_9 lhs_10 lhs_11 lhs_12 lhs_13 lhs_14 lhs_15 lhs_16)
          apply (simp only: rhs_1)
          by auto
      qed
    then show "prfun_of_rvfun
          (\<lambda>\<s>::state \<times> state.
              (if (0::\<nat>) < x\<^sub>v (fst \<s>) then 1::\<real> else (0::\<real>)) * ?lhs \<s> +
              (if x\<^sub>v (fst \<s>) = (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if snd \<s> = fst \<s> then 1::\<real> else (0::\<real>)))
          (\<lparr>t\<^sub>v = t, x\<^sub>v = x\<rparr>, \<lparr>t\<^sub>v = t\<^sub>v', x\<^sub>v = x\<^sub>v'\<rparr>) = prfun_of_rvfun ?rhs (\<lparr>t\<^sub>v = t, x\<^sub>v = x\<rparr>, \<lparr>t\<^sub>v = t\<^sub>v', x\<^sub>v = x\<^sub>v'\<rparr>)"
      by presburger
  qed

(*
iterdiff 0 (x\<^sup>< > 0)\<^sub>e (Pt (step p)) = 1\<^sub>p
iterdiff 1 _ _ = [x>0]
iterdiff 2 _ _ = [x=1]*(1-p) + [x>1]
iterdiff 3 _ _ 
  = 
    [x>0]([x-1=1]*p*(1-p) + [x-1>1]*p + [x+1=1]*(1-p)^2 + [x+1>1]*(1-p))
  =
    [x>0]([x=2]*p*(1-p) + [x>2]*p + [x=0]*(1-p)^2 + [x>0]*(1-p))
  =   (Combine: i.e [x>0](1-p) = [x=1](1-p) + [x=2](1-p) + [x>2](1-p))
    [x=1]*(1-p) + [x=2](p*(1-p) + (1-p)) + [x>2]*(p + (1-p))
  =   (p + 1 - p = 1) 
    [x=1]*(1-p) + [x=2](p*(1-p) + (1-p)) + [x>2]

iterdiff 4 _ _ 
  = 
    [x>0]([x-1=1]p(1-p) + [x-1=2]p(p*(1-p) + (1-p)) + [x-1>2]p +
          [x+1=1](1-p)^2 + [x+1=2](1-p)(p*(1-p) + (1-p)) + [x+1>2](1-p))
  =
    [x=1](1-p)(p*(1-p) + (1-p)) + [x=2](p(1-p) + (1-p)) + [x=3](p(p*(1-p) + (1-p)) + (1-p)) + [x > 3]

Assume (pdiff\<^sub>n\<^sup>0 = pdiff\<^sub>n\<^sup>n = 0)
  iterdiff n _ _ = (\<Sum>i:{1..n-1}. [x=i] * pdiff\<^sub>n\<^sup>i) + [x>n-1]
then
  iterdiff (Suc n) _ _ 
  =
    (\<Sum>i:{2..n}. [x=i]*p*pdiff\<^sub>n\<^sup>i\<^sup>-\<^sup>1) + [x>n]*p +
    (\<Sum>i:{0..n-2}. [x=i]*(1-p)*pdiff\<^sub>n\<^sup>i\<^sup>+\<^sup>1) + [x>n-2]*(1-p)
  =   (Combine)
    [x=1]*(1-p)*pdiff\<^sub>n\<^sup>2 + (\<Sum>i:{2..n-2}. [x=i]*(p*pdiff\<^sub>n\<^sup>i\<^sup>-\<^sup>1 + (1-p)*pdiff\<^sub>n\<^sup>i\<^sup>+\<^sup>1)) + 
    [x=n-1]*(p*pdiff\<^sub>n\<^sup>n\<^sup>-\<^sup>2 + (1-p)) + [x=n]*(p*pdiff\<^sub>n\<^sup>n\<^sup>-\<^sup>1 + (1-p)) + [x>n]
*)
fun pdiff :: "real \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real" where
"pdiff p 0 _ = 0" |
"pdiff p _ 0 = 0" |
"pdiff p _ (Suc 0) = 1" |
"pdiff p (Suc 0) (Suc (Suc 0)) = 1-p" |
"pdiff p (Suc i) (Suc (Suc 0)) = 1" |
\<comment> \<open>pdiff 1 (Suc n)\<close>
"pdiff p (Suc 0) (Suc n) = (1-p) * pdiff p 2 n " |
"pdiff p (Suc i) (Suc n) = (if i \<le> n - 2 
  then 
    p * pdiff p i n + (1-p) * pdiff p (Suc (Suc i)) n 
  else 
    p * pdiff p i n + (1-p)
)"

value "pdiff p 0 1"
value "pdiff p 1 1"
value "pdiff p 0 2"
value "pdiff p 1 2"
value "pdiff p 2 2"
value "pdiff p 3 2"
value "pdiff p 5 2"
value "pdiff p 1 3"
value "pdiff p 2 3"
value "pdiff p 3 3"
value "pdiff p 5 3"
value "pdiff p 1 4"
value "pdiff p 2 4"
value "pdiff p 3 4"
value "pdiff p 5 4"
thm "pdiff.induct"
thm "pdiff.elims"
thm "pdiff.simps"

lemma pdiff_1: "m \<ge> n \<Longrightarrow> pdiff p (Suc m) (Suc n) = 1"
proof (induct p m n rule: pdiff.induct)
  case (1 p uu)
  then show ?case by auto
next
  case (2 p v)
  then show ?case by auto
next
  case (3 p v)
  then show ?case by auto
next
  case (4 p)
  then show ?case by auto
next
  case (5 p v)
  then show ?case by auto
next
  case (6 p va)
  then show ?case by auto
next
  case ("7_1" p va vb)
  then show ?case by auto
next
  case ("7_2" p v va)
  then show ?case by auto
qed

lemma pdiff_geq_0: 
  assumes "(p::real) \<ge> 0" "(p::real) \<le> 1"
  shows "pdiff p m n \<ge> 0"
  using assms
proof (induct p m n rule: pdiff.induct)
  case (1 p uu)
  then show ?case by auto
next
  case (2 p v)
  then show ?case by auto
next
  case (3 p v)
  then show ?case by auto
next
  case (4 p)
  then show ?case by auto
next
  case (5 p v)
  then show ?case by auto
next
  case (6 p va)
  then show ?case by auto
next
  case ("7_1" p va vb)
  then show ?case by auto
next
  case ("7_2" p v va)
  then show ?case by auto
qed

lemma pdiff_leq_1: 
  assumes "(p::real) \<ge> 0" "(p::real) \<le> 1"
  shows "pdiff p m n \<le> 1"
  using assms
proof (induct p m n rule: pdiff.induct)
  case (1 p uu)
  then show ?case by auto
next
  case (2 p v)
  then show ?case by auto
next
  case (3 p v)
  then show ?case by auto
next
  case (4 p)
  then show ?case by auto
next
  case (5 p v)
  then show ?case by auto
next
  case (6 p va)
  then show ?case by (simp add: mult_le_one pdiff_geq_0)
next
  case ("7_1" p va vb)
  then show ?case
    by (smt (verit, ccfv_threshold) mult_left_le pdiff.simps(7))
next
  case ("7_2" p v va)
  then show ?case
    by (smt (verit, best) mult_left_le pdiff.simps(7))
qed

lemma pdiff_7_1_simps: 
  assumes "m \<ge> 2" "n \<ge> 3"
  shows "pdiff p m n = p * pdiff p (m-1) (n-1) + (1-p) * pdiff p (Suc m) (n-1)"
  using assms
  proof (induct p m n rule: pdiff.induct)
    case (1 p uu)
    then show ?case by auto
  next
    case (2 p v)
    then show ?case by auto
  next
    case (3 p v)
    then show ?case by auto
  next
    case (4 p)
    then show ?case by auto
  next
    case (5 p v)
    then show ?case by auto
  next
    case (6 p va)
    then show ?case by auto
  next
    case ("7_1" p va vb)
    then show ?case using pdiff_1 by force
  next
    case ("7_2" p v va)
    then show ?case by (simp add: pdiff_1)
  qed

lemma pdiff_7_2_simps: 
  assumes "m \<ge> 2" "\<not> (m-1 \<le> (n-1) - 2)" "n \<ge> 3"
  shows "pdiff p m n = p * pdiff p (m-1) (n-1) + (1-p)"
  using assms
  proof (induct p m n rule: pdiff.induct)
    case (1 p uu)
    then show ?case by auto
  next
    case (2 p v)
    then show ?case by auto
  next
    case (3 p v)
    then show ?case by auto
  next
    case (4 p)
    then show ?case by auto
  next
    case (5 p v)
    then show ?case by auto
  next
    case (6 p va)
    then show ?case by auto
  next
    case ("7_1" p va vb)
    then show ?case using pdiff_1 by force
  next
    case ("7_2" p v va)
    then show ?case by (simp add: pdiff_1)
  qed

  thm "eventually_mono"
lemma 
  assumes "m > 0" 
  assumes "(p::real) \<ge> 0" "(p::real) \<le> 1"
  shows "(\<lambda>n::\<nat>. pdiff p m (Suc n)) \<longlonglongrightarrow> (0::\<real>)"
  apply (rule decreasing_tendsto)
  apply (simp add: assms(2) assms(3) pdiff_geq_0)
  apply (subst eventually_sequentially)
proof -
  fix x :: "real"
  assume a1: "(0::\<real>) < x"

  show "\<exists>N::\<nat>. \<forall>n::\<nat>. N \<le> n \<longrightarrow> pdiff p m (Suc n) < x"
    using assms a1
    proof (induct p m xa rule: pdiff.induct)
      case (1 p uu)
      then show ?case by auto
    next
      case (2 p v)
      then show ?case by auto
    next
      case (3 p v)
      then show ?case by auto
    next
      case (4 p)
      then show ?case by auto
    next
      case (5 p v)
      then show ?case sorry
    next
      case (6 p va)
      then show ?case sorry
    next
      case ("7_1" p va vb)
      then show ?case sorry
    next
      case ("7_2" p v va)
      then show ?case sorry
    qed

(*
(x\<^sup>< > 0) * ((\<lbrakk>x\<^sup>> = x\<^sup>< - 1 \<and> $t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (ureal2real \<guillemotleft>p\<guillemotright>) + \<lbrakk>x\<^sup>> = x\<^sup>< + 1 \<and> $t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1 - ureal2real \<guillemotleft>p\<guillemotright>))
; 1)
= 
(x\<^sup>< > 0) 

(x\<^sup>< > 0) * ((\<lbrakk>x\<^sup>> = x\<^sup>< - 1 \<and> $t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (ureal2real \<guillemotleft>p\<guillemotright>) + \<lbrakk>x\<^sup>> = x\<^sup>< + 1 \<and> $t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1 - ureal2real \<guillemotleft>p\<guillemotright>))
; [])()
*)
lemma loop_body_iterdiff_simp:
  shows "(iter\<^sub>d 0 (x\<^sup>< > 0)\<^sub>e (Pt (step p)) 1\<^sub>p) = 1\<^sub>p"
        "(iter\<^sub>d (Suc n) (x\<^sup>< > 0)\<^sub>e (Pt (step p)) 1\<^sub>p) = prfun_of_rvfun ((\<lbrakk>x\<^sup>< > 0\<rbrakk>\<^sub>\<I>\<^sub>e * pdiff (ureal2real \<guillemotleft>p\<guillemotright>) ($x\<^sup><) (\<guillemotleft>n\<guillemotright>+1))\<^sub>e)"
proof -
  show "(iter\<^sub>d 0 (x\<^sup>< > 0)\<^sub>e (Pt (step p)) 1\<^sub>p) = 1\<^sub>p"
    by auto
  show "(iter\<^sub>d (Suc n) (x\<^sup>< > 0)\<^sub>e (Pt (step p)) 1\<^sub>p) = prfun_of_rvfun ((\<lbrakk>x\<^sup>< > 0\<rbrakk>\<^sub>\<I>\<^sub>e * pdiff (ureal2real \<guillemotleft>p\<guillemotright>) ($x\<^sup><) (\<guillemotleft>n\<guillemotright>+1))\<^sub>e)"
    apply (induction n)
    apply (simp)
    apply (subst prfun_seqcomp_one)
    using Pt_step_is_dist apply auto[1]
    apply (simp add: pfun_defs)
    apply (subst ureal_zero)
    apply (subst ureal_one)
    apply (simp add: prfun_of_rvfun_def)
     apply (pred_auto)
    apply (metis Suc_diff_1 pdiff.simps(3))
    apply (simp only: add_Suc)
    apply (simp only: iterdiff.simps(2))
    apply (simp only: pcond_def)
    apply (simp only: pseqcomp_def)
    apply (subst rvfun_seqcomp_inverse)
    using Pt_step_is_dist apply auto[1]
    apply (simp add: ureal_is_prob)
    apply (subst rvfun_inverse)
    apply (expr_auto add: dist_defs)
    using pdiff_geq_0 ureal_lower_bound ureal_upper_bound apply presburger
    using pdiff_leq_1 ureal_lower_bound ureal_upper_bound apply blast

    apply (simp add: mult_le_one power_le_one ureal_lower_bound ureal_upper_bound)+
    apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
    apply (simp only: Pt_step_simp Pt_step_alt_def)
    apply (expr_auto)
    defer
    apply (simp add: pzero_def rvfun_of_prfun_def ureal2real_0)
  proof -
    fix n::"\<nat>" and ta::"\<nat>" and xa::"\<nat>"
    assume a1: "(0::\<nat>) < xa"

    let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if x\<^sub>v v\<^sub>0 = xa - Suc (0::\<nat>) \<and> t\<^sub>v v\<^sub>0 = Suc ta then 1::\<real> else (0::\<real>)) * ureal2real p +
           (if x\<^sub>v v\<^sub>0 = Suc xa \<and> t\<^sub>v v\<^sub>0 = Suc ta then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
          ((if (0::\<nat>) < x\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * pdiff (ureal2real p) (x\<^sub>v v\<^sub>0) (Suc n)))"

    have set1: "{s::state. x\<^sub>v s = xa - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc ta \<and> (0::\<nat>) < x\<^sub>v s} = 
        (if xa > Suc 0 then {\<lparr>t\<^sub>v = Suc ta, x\<^sub>v = xa - Suc (0::\<nat>)\<rparr>} else {})"
      by auto

    have set2: "{s::state. x\<^sub>v s = Suc xa \<and> t\<^sub>v s = Suc ta \<and> (0::\<nat>) < x\<^sub>v s} = 
        {\<lparr>t\<^sub>v = Suc ta, x\<^sub>v = Suc xa\<rparr>}"
      by auto
    have "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if x\<^sub>v v\<^sub>0 = xa - Suc (0::\<nat>) \<and> t\<^sub>v v\<^sub>0 = Suc ta \<and> (0::\<nat>) < x\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * 
              (ureal2real p * pdiff (ureal2real p) (xa - Suc (0::\<nat>)) (Suc n)) +
           (if x\<^sub>v v\<^sub>0 = Suc xa \<and> t\<^sub>v v\<^sub>0 = Suc ta \<and> (0::\<nat>) < x\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * 
              (((1::\<real>) - ureal2real p) * pdiff (ureal2real p) (Suc xa) (Suc n))))"
      apply (rule infsum_cong)
      by force
    also have "... = (if xa > Suc 0 then (ureal2real p * pdiff (ureal2real p) (xa - Suc (0::\<nat>)) (Suc n)) else 0) + 
        ((1::\<real>) - ureal2real p) * pdiff (ureal2real p) (Suc xa) (Suc n)"
      apply (subst infsum_constant_finite_states_cmult_2)
      apply (simp add: set1)
      apply (simp add: set2)
      by (simp add: set1 set2)
    also have "... = pdiff (ureal2real p) xa (Suc (Suc n))"
      apply (cases "xa > Suc 0")
      apply (simp)
      apply (cases "xa - 1 \<le> (Suc n) - 2")
      apply (rule sym)
      apply (subst pdiff_7_1_simps)
      apply simp+
      apply (cases "n = 0")
      apply (smt (verit) Suc_diff_Suc Suc_pred a1 mult_cancel_left1 pdiff.simps(3) pdiff.simps(5))
      apply (rule sym)
      apply (subst pdiff_7_1_simps)
      apply simp+
      apply (cases "xa = 0")
      using a1 apply blast
      apply (cases "n = 0")
      using Suc_lessI apply fastforce
      by (metis Suc_1 less_antisym linorder_less_linear not0_implies_Suc not_less0 numeral_1_eq_Suc_0 one_eq_numeral_iff pdiff.simps(6))
    then show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state.
          ((if x\<^sub>v v\<^sub>0 = xa - Suc (0::\<nat>) \<and> t\<^sub>v v\<^sub>0 = Suc ta then 1::\<real> else (0::\<real>)) * ureal2real p +
           (if x\<^sub>v v\<^sub>0 = Suc xa \<and> t\<^sub>v v\<^sub>0 = Suc ta then 1::\<real> else (0::\<real>)) * ((1::\<real>) - ureal2real p)) *
          ((if (0::\<nat>) < x\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * pdiff (ureal2real p) (x\<^sub>v v\<^sub>0) (Suc n))) =
       pdiff (ureal2real p) xa (Suc (Suc n))"
      using calculation by presburger
  qed
qed

lemma loop_body_iterdiff_tendsto_0:
  assumes "p < 1"
  shows "\<forall>s::state \<times> state. (\<lambda>n::\<nat>. ureal2real (iter\<^sub>d n (x\<^sup>< > 0)\<^sub>e (Pt (step p)) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
proof 
  fix s
  have f1: "(\<lambda>n::\<nat>. ureal2real (iterdiff (Suc n) (x\<^sup>< > 0)\<^sub>e (Pt (step p)) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    apply (subst loop_body_iterdiff_simp)
    apply (simp add: prfun_of_rvfun_def)
    apply (expr_auto)
    apply (subst real2ureal_inverse)
    using pdiff_geq_0 ureal_lower_bound ureal_upper_bound apply presburger
    apply (simp add: pdiff_leq_1 ureal_lower_bound ureal_upper_bound)
    defer
    apply (simp add: real2ureal_inverse)
    sledgehammer
    sorry
  then show "(\<lambda>n::\<nat>. ureal2real (iter\<^sub>d n (x\<^sup>< > 0)\<^sub>e (Pt (step p)) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    apply (subst (asm) Suc_eq_plus1)
    by (rule LIMSEQ_offset[where k = 1])
qed

(*
while\<^sub>p\<^sub>t (x\<^sup>< > 0)\<^sub>e do 
  if c = F then (c := F \<oplus>\<^bsub>pFF\<^esub> c := B) else (c := F \<oplus>\<^bsub>pBF\<^esub> c := B);
  if c = F then (o := H \<oplus>\<^bsub>pFH\<^esub> o := T) else (o := H \<oplus>\<^bsub>pBH\<^esub> o := T);
od

(\<lbrakk>c = F \<and> c' = F \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFF * pFH +
\<lbrakk>c = F \<and> c' = F \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFF * pFT +
\<lbrakk>c = F \<and> c' = B \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFB * pBH +
\<lbrakk>c = F \<and> c' = B \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFB * pBT +
\<lbrakk>c = B \<and> c' = F \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBF * pFH +
\<lbrakk>c = B \<and> c' = F \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBF * pFT +
\<lbrakk>c = B \<and> c' = B \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBB * pBH +
\<lbrakk>c = B \<and> c' = B \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBB * pBT) 

(
\<lbrakk>c = F \<and> c0 = F \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFF * pFH +
\<lbrakk>c = F \<and> c0 = F \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFF * pFT +
\<lbrakk>c = F \<and> c0 = B \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFB * pBH +
\<lbrakk>c = F \<and> c0 = B \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFB * pBT +
\<lbrakk>c = B \<and> c0 = F \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBF * pFH +
\<lbrakk>c = B \<and> c0 = F \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBF * pFT +
\<lbrakk>c = B \<and> c0 = B \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBB * pBH +
\<lbrakk>c = B \<and> c0 = B \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBB * pBT
) * 
 (
\<lbrakk>c = F \<and> c' = F \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFF * pFH +
\<lbrakk>c = F \<and> c' = F \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFF * pFT +
\<lbrakk>c = F \<and> c' = B \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFB * pBH +
\<lbrakk>c = F \<and> c' = B \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pFB * pBT +
\<lbrakk>c = B \<and> c' = F \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBF * pFH +
\<lbrakk>c = B \<and> c' = F \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBF * pFT +
\<lbrakk>c = B \<and> c' = B \<and> o' = H \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBB * pBH +
\<lbrakk>c = B \<and> c' = B \<and> o' = T \<and> t' = t + 1\<rbrakk>\<^sub>\<I> * pBB * pBT
)

*)

end
