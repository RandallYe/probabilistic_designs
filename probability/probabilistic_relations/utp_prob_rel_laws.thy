section \<open> Probabilistic relation programming laws \<close>

theory utp_prob_rel_laws
  imports 
    "utp_prob_rel_prog"
begin 

declare [[show_types]]

subsection \<open> Laws of @{text infsum} \<close>

lemma infsum_singleton: 
  "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if c = v\<^sub>0 then (m::\<real>) else 0)) = m"
  apply (rule infsumI)
  apply (simp add: has_sum_def)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
  apply (rule_tac x = "{c}" in exI)
  by (auto)

lemma infsum_singleton_summable:
  assumes "m \<noteq> 0"
  shows "(\<lambda>v\<^sub>0. (if c = v\<^sub>0 then (m::\<real>) else 0)) summable_on UNIV"
proof (rule ccontr)
  assume a1: "\<not> (\<lambda>v\<^sub>0::'a. if c = v\<^sub>0 then m else (0::\<real>)) summable_on UNIV"
  from a1 have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if c = v\<^sub>0 then (m::\<real>) else 0)) = (0::\<real>)"
    by (simp add: infsum_def)
  then show "False"
    by (simp add: infsum_singleton assms)
qed

lemma infsum_singleton_1: 
  "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if v\<^sub>0 = c then (m::\<real>) else 0)) = m"
  by (smt (verit, del_insts) infsum_cong infsum_singleton)

lemma infsum_singleton_cond_unique:
  assumes "\<exists>! v. b v"
  shows "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if b v\<^sub>0 then (m::\<real>) else 0)) = m"
  apply (rule infsumI)
  apply (simp add: has_sum_def)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
  apply (rule_tac x = "{THE v. b v}" in exI)
  apply (auto)
  by (smt (verit, ccfv_SIG) assms finite_insert mk_disjoint_insert sum.insert sum_nonneg 
      sum_nonpos theI)

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

lemma infsum_mult_subset_right: 
  "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. ((P v\<^sub>0) * (if b v\<^sub>0 then (1::\<real>) else 0))) = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a \<in> {v\<^sub>0. b v\<^sub>0}. (P v\<^sub>0))"
  apply (rule infsum_cong_neutral)
  by simp+

subsection \<open> Laws of type @{type prel} \<close>
lemma prel_is_dist: "is_final_distribution (set_of_prel (P::'a phrel))"
  using set_of_prel by force

lemma prel_prob_sum1_summable:
  assumes "is_final_distribution p"
  shows "\<forall>s. 0 \<le> p s \<and> p s \<le> 1" 
        "(\<Sum>\<^sub>\<infinity> s. p (s\<^sub>1, s)) = (1::\<real>)"
        "(\<lambda>s. p (s\<^sub>1, s)) summable_on UNIV"
  using assms apply (simp add: dist_defs expr_defs)
  using assms is_dist_def is_sum_1_def apply (metis (no_types, lifting) curry_conv infsum_cong)
proof (rule ccontr)
  assume a1: "\<not> (\<lambda>s. p (s\<^sub>1, s)) summable_on UNIV"
  from a1 have f1: "(\<Sum>\<^sub>\<infinity>s. p (s\<^sub>1, s)) = (0::\<real>)"
    by (simp add: infsum_def)
  then show "False"
    by (metis assms case_prod_eta curry_case_prod is_dist_def is_sum_1_def zero_neq_one)
qed

lemma prel_is_prob: "\<forall>s\<^sub>1::'s\<^sub>1. is_prob ((curry (set_of_prel Q)) s\<^sub>1)"
  using is_dist_def set_of_prel by fastforce

lemma prel_in_0_1: "(curry (set_of_prel Q)) x y \<ge> 0 \<and> (curry (set_of_prel Q)) x y \<le> 1"
  using prel_is_prob 
  by (smt (verit) SEXP_def is_prob_def taut_def)

lemma prel_in_0_1': "(set_of_prel Q) s \<ge> 0 \<and> (set_of_prel Q) s \<le> 1"
  using prel_in_0_1 curry_conv
  by (metis case_prod_curry split_def)

lemma prel_sum_1: "(\<Sum>\<^sub>\<infinity>s::'a. set_of_prel P (s\<^sub>1, s)) = (1::\<real>)"
  using prel_prob_sum1_summable(2) set_of_prel by fastforce

(* The first component of pairs, which infsum is over, can be discarded. *)
(* The basic observation is that 
    A = {(s::'a, v\<^sub>0::'a) | s v\<^sub>0. put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s}
is resulted from an injective function 
  (\<lambda>v\<^sub>0. (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0)) 
from (UNIV::'a set) which the right summation is over.

Informally speaking, every v\<^sub>0 in UNIV has a corresponding (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0) in A, and no more, 
thus summations are equal. 
*)
lemma prel_infsum_over_pair_fst_discard:
  "(\<Sum>\<^sub>\<infinity> (s::'a, v\<^sub>0::'a) \<in> {(s::'a, v\<^sub>0::'a) | s v\<^sub>0. put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s}. set_of_prel P (s\<^sub>1, v\<^sub>0)) = 
   (\<Sum>\<^sub>\<infinity> v\<^sub>0::'a. set_of_prel P (s\<^sub>1, v\<^sub>0))"
  apply (simp add: prel_sum_1)
  \<comment> \<open> Definition of @{term "infsum"} \<close>
  apply (rule infsumI)
  apply (simp add: has_sum_def)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
proof -
  fix S::"\<bbbP> \<real>"
  assume a1: "open S"
  assume a2: "(1::\<real>) \<in> S"
  \<comment> \<open>How to improve this proof? Forward proof. Focus on the goal f0 9 lines below \<close>
  have "(\<Sum>\<^sub>\<infinity>s::'a. set_of_prel P (s\<^sub>1, s)) = (1::\<real>)"
    by (simp add: prel_sum_1)
  then have "has_sum (\<lambda>s::'a. set_of_prel P (s\<^sub>1, s)) UNIV (1::\<real>)"
    by (metis has_sum_infsum infsum_not_exists zero_neq_one)
  then have "(sum (\<lambda>s::'a. set_of_prel P (s\<^sub>1, s)) \<longlongrightarrow> (1::\<real>)) (finite_subsets_at_top UNIV)"
    using has_sum_def by blast
  then have "\<forall>\<^sub>F x::\<bbbP> 'a in finite_subsets_at_top UNIV. (\<Sum>s::'a\<in>x. set_of_prel P (s\<^sub>1, s)) \<in> S"
    using a1 a2 tendsto_def by blast
  then have f0: "\<exists>X::\<bbbP> 'a. finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> 
      (\<Sum>s::'a\<in>Y. set_of_prel P (s\<^sub>1, s)) \<in> S)"
    by (simp add: eventually_finite_subsets_at_top)
  then show "\<exists>X::'a rel. finite X \<and> X \<subseteq> {uu::'a \<times> 'a. \<exists>v\<^sub>0::'a. uu = (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0)} \<and>
          (\<forall>Y::'a rel.
              finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> {uu::'a \<times> 'a. \<exists>v\<^sub>0::'a. uu = (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0)} \<longrightarrow>
              (\<Sum>x::'a \<times> 'a\<in>Y. case x of (s::'a, v\<^sub>0::'a) \<Rightarrow> set_of_prel P (s\<^sub>1, v\<^sub>0)) \<in> S)"
  proof -
    assume a11: "\<exists>X::\<bbbP> 'a. finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> 
      (\<Sum>s::'a\<in>Y. set_of_prel P (s\<^sub>1, s)) \<in> S)"
    have f1: "finite
       {uu::'a \<times> 'a. \<exists>v\<^sub>0::'a. v\<^sub>0 \<in> (SOME X::\<bbbP> 'a.
          finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> (\<Sum>s::'a\<in>Y. set_of_prel P (s\<^sub>1, s)) \<in> S))
        \<and> uu = (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0)}"
      apply (subst finite_Collect_bounded_ex)
      apply (smt (verit, ccfv_threshold) CollectD a11 rev_finite_subset someI_ex subset_iff)
      by (auto)
    show ?thesis
      (* Construct a witness from existing X from f0 using SOME (indifinite description) *)
      apply (rule_tac x = "{(put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0) | v\<^sub>0 . 
        v\<^sub>0 \<in> (SOME X::\<bbbP> 'a. finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> 
        (\<Sum>s::'a\<in>Y. set_of_prel P (s\<^sub>1, s)) \<in> S))}" in exI)
      apply (rule conjI)
      using f1 apply (smt (verit, best) Collect_mono rev_finite_subset)
      apply (auto)
    proof -
      fix Y::"'a rel"
      assume a111: "finite Y"
      assume a112: "{uu::'a \<times> 'a.
        \<exists>v\<^sub>0::'a.
           uu = (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0) \<and>
           v\<^sub>0 \<in> (SOME X::\<bbbP> 'a. finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> (\<Sum>s::'a\<in>Y. set_of_prel P (s\<^sub>1, s)) \<in> S))}
       \<subseteq> Y"
      assume a113: "Y \<subseteq> {uu::'a \<times> 'a. \<exists>v\<^sub>0::'a. uu = (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0)}"
      have f11: "(\<Sum>s::'a\<in>Range Y. set_of_prel P (s\<^sub>1, s)) \<in> S"
        using a11 a111 a112
        by (smt (verit, del_insts) Range_iff finite_Range mem_Collect_eq subset_iff verit_sko_ex_indirect)
      have f12: "inj_on (\<lambda>v\<^sub>0. (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0)) (Range Y)"
        using inj_on_def by blast
      have f13: "(\<Sum>x::'a \<times> 'a\<in>Y. case x of (s::'a, v\<^sub>0::'a) \<Rightarrow> set_of_prel P (s\<^sub>1, v\<^sub>0)) = 
            (\<Sum>s::'a\<in>Range Y. set_of_prel P (s\<^sub>1, s))"
        apply (rule sum.reindex_cong[where l = "(\<lambda>v\<^sub>0. (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0))" and B = "Range Y"]) 
        apply (simp add: f12)
        using a113 by (auto)
      show "(\<Sum>x::'a \<times> 'a\<in>Y. case x of (s::'a, v\<^sub>0::'a) \<Rightarrow> set_of_prel P (s\<^sub>1, v\<^sub>0)) \<in> S"
        using f11 f13 by presburger
    qed
  qed
qed

(*
lemma 
  assumes "finite Y"
  shows  "(\<Sum>x::'a \<times> 'a\<in>Y. case x of (ss::'a, s::'a) \<Rightarrow> P s) = (\<Sum>s::'a \<in> Range Y. P s)"
  sledgehammer

lemma prel_sum_1': "(\<Sum>\<^sub>\<infinity>(ss::'a, s::'a). set_of_prel P (s\<^sub>1, s)) = (1::\<real>)"
  apply (rule infsumI)
  apply (simp add: has_sum_def)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
proof -
  fix S::"\<bbbP> \<real>"
  assume a1: "open S"
  assume a2: "(1::\<real>) \<in> S"

  have "(\<Sum>\<^sub>\<infinity>s::'a. set_of_prel P (s\<^sub>1, s)) = (1::\<real>)"
    by (simp add: prel_sum_1)
  then have "has_sum (\<lambda>s::'a. set_of_prel P (s\<^sub>1, s)) UNIV (1::\<real>)"
    by (metis has_sum_infsum infsum_not_exists zero_neq_one)
  then have "(sum (\<lambda>s::'a. set_of_prel P (s\<^sub>1, s)) \<longlongrightarrow> (1::\<real>)) (finite_subsets_at_top UNIV)"
    using has_sum_def by blast
  then have "\<forall>\<^sub>F x::\<bbbP> 'a in finite_subsets_at_top UNIV. (\<Sum>s::'a\<in>x. set_of_prel P (s\<^sub>1, s)) \<in> S"
    using a1 a2 tendsto_def by blast
  then have "\<exists>X::\<bbbP> 'a. finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> 
      (\<Sum>s::'a\<in>Y. set_of_prel P (s\<^sub>1, s)) \<in> S)"
    by (simp add: eventually_finite_subsets_at_top)
  then show "\<exists>X::'a rel. finite X \<and> (\<forall>Y::'a rel. finite Y \<and> X \<subseteq> Y \<longrightarrow> 
    (\<Sum>(ss::'a, s::'a)\<in>Y. set_of_prel P (s\<^sub>1, s)) \<in> S)"
  proof -
    assume a11: "\<exists>X::\<bbbP> 'a. finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> 
      (\<Sum>s::'a\<in>Y. set_of_prel P (s\<^sub>1, s)) \<in> S)"
    have f1: "finite
       {uu::'a \<times> 'a. \<exists>x::'a. x \<in> (SOME X::\<bbbP> 'a.
          finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> (\<Sum>s::'a\<in>Y. set_of_prel P (s\<^sub>1, s)) \<in> S))
        \<and> uu = (x, x)}"
      apply (subst finite_Collect_bounded_ex)
      apply (smt (verit, ccfv_threshold) CollectD a11 rev_finite_subset someI_ex subset_iff)
      by (auto)
    show ?thesis
      apply (rule_tac x = "{(x, x) | x . 
        x \<in> (SOME X::\<bbbP> 'a. finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> 
        (\<Sum>s::'a\<in>Y. set_of_prel P (s\<^sub>1, s)) \<in> S))}" in exI)
      apply (rule conjI)
      using f1 apply (smt (verit, best) Collect_mono rev_finite_subset)
      apply (auto)
      sledgehammer
      apply (rule someI_ex)
qed
*)

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

lemma prel_mult_subset_left_summable:
  shows "(\<lambda>v\<^sub>0. (if b v\<^sub>0 then (1::\<real>) else 0) * (set_of_prel P (s\<^sub>1, v\<^sub>0))) summable_on UNIV"
  apply (subgoal_tac "(\<lambda>v\<^sub>0. (if b v\<^sub>0 then (1::\<real>) else 0) * (set_of_prel P (s\<^sub>1, v\<^sub>0))) summable_on UNIV
    \<longleftrightarrow> (\<lambda>x::'a. set_of_prel P (s\<^sub>1, x)) summable_on {x. b x}")
  apply (simp add: prel_summable_on_subset)
  apply (rule summable_on_cong_neutral)
  by simp+

lemma prel_mult_subset_right_summable:
  shows "(\<lambda>v\<^sub>0. (set_of_prel P (s\<^sub>1, v\<^sub>0)) * (if b v\<^sub>0 then (1::\<real>) else 0)) summable_on UNIV"
  apply (subst summable_on_cong[where 
        g = "(\<lambda>v\<^sub>0. (if b v\<^sub>0 then (1::\<real>) else 0) * (set_of_prel P (s\<^sub>1, v\<^sub>0)))"])
  using mult.commute apply blast
  by (simp add: prel_mult_subset_left_summable)

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

subsection \<open> Conversion from a set of realed functions to @{text "prel"} and then back to the set \<close>

lemma prel_set_conv_assign: "set_of_prel (prel_of_set (passigns_f \<sigma>)) = passigns_f \<sigma>"
  apply (subst prel_of_set_inverse)
  apply (simp add: dist_defs expr_defs, auto)
  apply (rel_auto)
  by (simp add: infsum_singleton)

lemma prel_set_conv_pchoice: 
  assumes "0 \<le> r \<and> r \<le> 1"
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "set_of_prel (prel_of_set (\<guillemotleft>r\<guillemotright> * (p) + (1 - \<guillemotleft>r\<guillemotright>) * (q))\<^sub>e) = (\<guillemotleft>r\<guillemotright> * (p) + (1 - \<guillemotleft>r\<guillemotright>) * (q))\<^sub>e"
    apply (subst prel_of_set_inverse)
    apply (simp add: dist_defs expr_defs, auto)
    apply (simp add: assms(1) assms(2) assms(3) prel_prob_sum1_summable(1))
    apply (simp add: assms(1) assms(2) assms(3) convex_bound_le prel_prob_sum1_summable(1))
    apply (subst infsum_add)
    apply (simp add: assms(2) prel_prob_sum1_summable(3) summable_on_cmult_right)
    apply (simp add: assms(3) prel_prob_sum1_summable(3) summable_on_cmult_right)
    apply (subst infsum_cmult_right)
    apply (simp add: assms(2) prel_prob_sum1_summable(3) summable_on_cmult_right)
    apply (subst infsum_cmult_right)
    apply (simp add: assms(3) prel_prob_sum1_summable(3) summable_on_cmult_right)
    by (simp add: assms(2) assms(3) prel_prob_sum1_summable(2))

(*
lemma prel_set_pchoice: 
  assumes "\<forall>s. 0 \<le> r s \<and> r s \<le> 1"
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "set_of_prel (prel_of_set (r * (p) + (1 - r) * (q))\<^sub>e) = (r * (p) + (1 - r) * (q))\<^sub>e"
proof -
  have f1: "\<forall>s. 0 \<le> p s \<and> p s \<le> 1"
    using assms(2) by (simp add: dist_defs expr_defs)
  have f2: "\<forall>s. 0 \<le> q s \<and> q s \<le> 1"
    using assms(3) by (simp add: dist_defs expr_defs)
  have f3: "(\<Sum>\<^sub>\<infinity>s::'b. r (s\<^sub>1, s) * p (s\<^sub>1, s) + ((1::\<real>) - r (s\<^sub>1, s)) * q (s\<^sub>1, s)) = 
    (\<Sum>\<^sub>\<infinity>s::'b. r (s\<^sub>1, s) * p (s\<^sub>1, s)) + (\<Sum>\<^sub>\<infinity>s::'b. ((1::\<real>) - r (s\<^sub>1, s)) * q (s\<^sub>1, s))"
    apply (rule infsum_add)
  show ?thesis
    apply (subst prel_of_set_inverse)
    apply (simp add: dist_defs expr_defs, auto)
    using assms(1) apply (simp add: f1 f2)
     apply (simp add: assms(1) convex_bound_le f1 f2)
*)
(*
lemma prel_set_pchoice: "set_of_prel (prel_of_set (r * @(set_of_prel P) + (1 - r) * @(set_of_prel Q))\<^sub>e) 
  = (\<lbrakk> \<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"
  apply (subst prel_of_set_inverse)
  apply (simp add: dist_defs expr_defs, auto)
  apply (rel_auto)
  by (simp add: infsum_singleton)
*)

subsection \<open> Laws of probabilistic relations \<close>
term "set_of_prel P"
term "\<lambda>s. (set_of_prel P) s"
term "(case \<s> of (\<sigma>::'a, \<rho>::'a) \<Rightarrow> Pair \<sigma>) (v\<^sub>0::'a)"

theorem prel_left_unit: "II ; P = P"
  apply (simp add: prel_defs expr_defs)
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
  apply (simp add: prel_defs expr_defs)
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
  by (simp add: prel_defs expr_defs)

term "(x := e) \<Zcomp> (y := f)"  

lemma prel_assign_is_prob: "is_prob (\<lbrakk> \<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"
  by (simp add: prel_defs expr_defs dist_defs)

theorem passign_comp: 
  (* assumes "$x \<sharp> f" "x \<bowtie> y" *)
  shows "(x := e) ; (y := f) = prel_of_set (\<lbrakk> \<lbrakk>(x := e) \<Zcomp> (y := f)\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"
  apply (simp add: prel_defs expr_defs)
  apply (subst prel_of_set_inverse)
  apply (simp add: dist_defs)
  apply (rel_auto)
  apply (simp add: infsum_singleton)
  apply (subst prel_of_set_inverse)
  apply (simp add: dist_defs)
  apply (rel_auto)
  apply (simp add: infsum_singleton)
  apply (rule HOL.arg_cong[where f="prel_of_set"])
  apply (rel_auto)
  apply (subst infsum_mult_singleton_left_1)
  apply simp
  by (smt (verit, best) infsum_0 mult_cancel_left1 mult_cancel_right1)

lemma prel_prob_choice_is_sum_1:
  assumes "0 \<le> r \<and> r \<le> 1"
  shows "(\<Sum>\<^sub>\<infinity>s::'a. r * set_of_prel P (s\<^sub>1, s) + ((1::\<real>) - r ) * set_of_prel Q (s\<^sub>1, s)) = (1::\<real>)"
proof -
  have f1: "(\<Sum>\<^sub>\<infinity>s::'a. r  * set_of_prel P (s\<^sub>1, s) + ((1::\<real>) - r ) * set_of_prel Q (s\<^sub>1, s)) = 
    (\<Sum>\<^sub>\<infinity>s::'a. r * set_of_prel P (s\<^sub>1, s)) + (\<Sum>\<^sub>\<infinity>s::'a. ((1::\<real>) - r ) * set_of_prel Q (s\<^sub>1, s))"
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
  apply (simp add: prel_defs expr_defs)
  apply (subst prel_of_set_inverse)
  apply (simp add: dist_defs expr_defs)
  apply (rel_auto)
  apply (simp add: infsum_singleton)
  apply (rule HOL.arg_cong[where f="prel_of_set"])
  apply (rel_auto)
  by (simp add: infsum_mult_singleton_left_1)

lemma prel_infsum_over_pair_subset_1:
  "(\<Sum>\<^sub>\<infinity> (s::'a, v\<^sub>0::'a). set_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) = 1"
proof -
  have "(\<Sum>\<^sub>\<infinity> (s::'a, v\<^sub>0::'a). set_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) = 
        (\<Sum>\<^sub>\<infinity> (s::'a, v\<^sub>0::'a) \<in> {(s::'a, v\<^sub>0::'a) | s v\<^sub>0. put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s}. set_of_prel P (s\<^sub>1, v\<^sub>0))"
    apply (rule infsum_cong_neutral)
    apply force
    using DiffD2 prod.collapse apply fastforce
    by force
  then show ?thesis
    by (metis prel_infsum_over_pair_fst_discard prel_sum_1)
qed

lemma prel_infsum_swap:
 "(\<Sum>\<^sub>\<infinity>s::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. set_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) = 
  (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. \<Sum>\<^sub>\<infinity>s::'a. set_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>)))"
  apply (rule infsum_swap_banach)
  apply (simp add: summable_on_def)
  apply (rule_tac x = "1" in exI)
  by (smt (verit, best) has_sum_infsum infsum_cong infsum_not_exists prel_infsum_over_pair_subset_1 split_cong)

lemma prel_infsum_infsum_subset_1:
  "(\<Sum>\<^sub>\<infinity>s::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. set_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) =
       (1::\<real>)"
  apply (simp add: prel_infsum_swap)
proof -
  have f0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (\<Sum>\<^sub>\<infinity>s::'a. set_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>)))) 
    = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (set_of_prel P (s\<^sub>1, v\<^sub>0) * (\<Sum>\<^sub>\<infinity>s::'a. (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>)))))"
    apply (subst infsum_cmult_right)
    apply (simp add: infsum_singleton_summable)
    by (simp)
  then have f1: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (set_of_prel P (s\<^sub>1, v\<^sub>0) * 1))"
    by (simp add: infsum_singleton)
  then show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. \<Sum>\<^sub>\<infinity>s::'a. set_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) = (1::\<real>)"
    using f0 prel_sum_1 by force
qed 


term "prel_of_set (\<lbrakk> ($x\<^sup>< = e) \<rbrakk>\<^sub>\<I>\<^sub>e)"

(* This realed function is not a distribution *)
(*
lemma "is_final_distribution (\<lbrakk> ($x\<^sup>< = e\<^sup><) \<rbrakk>\<^sub>\<I>\<^sub>e)"
  apply (expr_auto)
  apply (simp add: dist_defs)
  apply (auto)
*)

(*
theorem prel_right_one_point: "P ; prel_of_set (\<lbrakk> ($x\<^sup>< = e\<^sup><) \<rbrakk>\<^sub>\<I>\<^sub>e) 
    = prel_of_set (([ x\<^sup>> \<leadsto> e\<^sup>> ] \<dagger> @(set_of_prel P)))\<^sub>e"
  apply (simp add: prel_defs expr_defs)
  apply (subst prel_of_set_inverse)
   apply (simp add: dist_defs expr_defs)
   apply (auto)
  sorry
*)

(* This is not a valid law.
theorem prel_right_one_point: "P ; x := e = prel_of_set (([ x\<^sup>> \<leadsto> e\<^sup>> ] \<dagger> @(set_of_prel P)))\<^sub>e"
  apply (simp add: prel_defs expr_defs)
  apply (subst prel_of_set_inverse)

  apply (simp add: dist_defs expr_defs)
  apply (rel_auto)
   apply (simp add: infsum_singleton)

  apply (subst prel_of_set_inject)
  apply (simp add: dist_defs expr_defs)
  apply (rel_auto)
      apply (simp add: infsum_nonneg prel_in_0_1')
     apply (subgoal_tac "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. set_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) 
      \<le> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. set_of_prel P (s\<^sub>1, v\<^sub>0))")
  apply (simp add: prel_sum_1)
     apply (rule infsum_mono)
  apply (simp add: prel_mult_subset_right_summable)
  apply (simp add: prel_summable)
  apply (simp add: prel_in_0_1')
  apply (simp add: prel_infsum_infsum_subset_1)
  apply (simp add: dist_defs expr_defs)
  apply (auto)
  apply (simp add: prel_in_0_1')+
  apply (simp add: lens_defs)
     apply (rule infsumI)
    apply (simp add: has_sum_def)
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
*)
(* In order to prove this law, we need to restrict P Q to distributions *)
(*
lemma passign_pif_simp:
  assumes "\<forall>s. 0 \<le> r s \<and> r s \<le> 1"
  shows "(x := c) ; (if\<^sub>p (r) then P else Q) = 
    prel_of_set (r * ([ x\<^sup>> \<leadsto> c\<^sup>> ] \<dagger> @(set_of_prel P)) +  (1-r) * ([ x\<^sup>> \<leadsto> c\<^sup>> ] \<dagger> @(set_of_prel Q)))\<^sub>e"
  apply (simp add: prel_defs expr_defs)
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

subsection \<open> Substitutions \<close>

term "[ x \<leadsto> f ]"
term "(if\<^sub>p b then c else d)"
(*
lemma "prel_of_set ([ x\<^sup>> \<leadsto> e\<^sup>> ] \<dagger> (set_of_prel II\<^sub>p)) = (x := e)"
  apply (simp add: expr_defs prel_defs)
  apply (subst prel_of_set_inverse)
   apply (simp add: dist_defs)
   apply (simp add: infsum_singleton)
  apply (subst prel_of_set_inject)
    apply (simp add: dist_defs)
    apply (auto)

lemma "prel_of_set (\<sigma> \<dagger> (set_of_prel II\<^sub>p)) = (x := e)"
  apply (simp add: expr_defs prel_defs)
  apply (subst prel_of_set_inverse)
   apply (simp add: dist_defs)
   apply (simp add: infsum_singleton)
  apply (subst prel_of_set_inject)
    apply (simp add: dist_defs)
  apply (auto)
*)

end
