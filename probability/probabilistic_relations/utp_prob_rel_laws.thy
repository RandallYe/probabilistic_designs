section \<open> Probabilistic relation programming laws \<close>

theory utp_prob_rel_laws
  imports 
    "utp_prob_rel_prog"
begin 

declare [[show_types]]

subsection \<open> Useful lemmas  \<close>
lemma finite_image_set2':
  assumes "finite A" "finite B"
  shows "finite {(a, b). a \<in> A \<and> b \<in> B}"
  apply (rule finite_subset [where B = "\<Union>x \<in> A. \<Union>y \<in> B. {(x,y)}"])
  apply auto
  using assms(1) assms(2) by blast

lemma finite_image_set2'':
  assumes "finite B" "\<forall>x. finite (A x)"
  shows "finite {(a, b). b \<in> B \<and> a \<in> A b}"
  apply (rule finite_subset [where B = "\<Union>y \<in> B. \<Union>x \<in> A y. {(x,y)}"])
  apply auto
  using assms(1) assms(2) by blast


lemma card_1_singleton:
  assumes "\<exists>!x. P x"
  shows "card {x. P x} = Suc (0::\<nat>)"
  using assms card_1_singleton_iff by fastforce

lemma card_0_singleton:
  assumes "\<not>(\<exists>x. P x)"
  shows "card {x. P x} = (0::\<nat>)"
  using assms by auto

lemma card_0_false:
  shows "card {x. False} = (0::\<real>)"
  by simp

subsection \<open> Laws of @{text infsum} \<close>
lemma has_sum_cdiv_left:
  fixes f :: "'a \<Rightarrow> \<real>"
  assumes \<open>has_sum f A a\<close>
  shows "has_sum (\<lambda>x. f x / c) A (a / c)"
  apply (simp only : divide_inverse)
  using assms has_sum_cmult_left by blast

lemma infsum_cdiv_left:
  fixes f :: "'a \<Rightarrow> \<real>"
  assumes \<open>c \<noteq> 0 \<Longrightarrow> f summable_on A\<close>
  shows "infsum (\<lambda>x. f x / c) A = infsum f A / c"
  apply (simp only : divide_inverse)
  using infsum_cmult_left' by blast

lemma summable_on_cdiv_left:
  fixes f :: "'a \<Rightarrow> \<real>"
  assumes \<open>f summable_on A\<close>
  shows "(\<lambda>x. f x / c) summable_on A"
  using assms summable_on_def has_sum_cdiv_left by blast

lemma summable_on_cmult_left':
  fixes f :: "'a \<Rightarrow> \<real>"
  assumes \<open>c \<noteq> 0\<close>
  shows "(\<lambda>x. f x / c) summable_on A \<longleftrightarrow> f summable_on A"
  apply (simp only : divide_inverse)
  by (simp add: assms summable_on_cmult_left')

lemma infsum_geq_element:
  fixes f :: "'a \<Rightarrow> \<real>"
  assumes "\<forall>s. f s \<ge> 0"
  assumes "f summable_on A"
  assumes "s \<in> A"
  shows "f s \<le> infsum f A"
proof -
  have f0: "infsum f (A - {s}) \<ge> 0"
    by (simp add: assms(1) infsum_nonneg)
  have f1: "infsum f A = infsum f ({s} \<union> (A - {s}))"
    using assms(3) insert_Diff by force
  also have f2: "... = infsum f {s} + infsum f (A - {s})"
    apply (subst infsum_Un_disjoint)
    apply (simp_all)
    by (simp add: assms(2) summable_on_cofin_subset)
  show ?thesis
    using f0 f1 f2 by auto
qed

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

lemma infsum_constant_finite_states:
  assumes "finite {s. b s}"
  shows "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if b v\<^sub>0 then (m::\<real>) else 0)) = m * card {s. b s}"
  apply (rule infsumI)
  apply (simp add: has_sum_def)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
  apply (rule_tac x = "{v. b v}" in exI)
  apply (auto)
  using assms apply force
proof -
  fix S::"\<bbbP> \<real>" and Y::"\<bbbP> 'a"
  assume a1: "m * real (card (Collect b)) \<in> S"
  assume a2: "finite Y" 
  assume a3: " {v::'a. b v} \<subseteq> Y"
  have "(\<Sum>v\<^sub>0::'a\<in>Y. if b v\<^sub>0 then m else (0::\<real>)) = (\<Sum>v\<^sub>0::'a\<in>{v::'a. b v}. if b v\<^sub>0 then m else (0::\<real>))"
    by (smt (verit, best) DiffD2 a2 a3 mem_Collect_eq sum.mono_neutral_cong_right)
  moreover have "... = m * card {s. b s}"
    by auto
  ultimately show "(\<Sum>v\<^sub>0::'a\<in>Y. if b v\<^sub>0 then m else (0::\<real>)) \<in> S"
    using a1 by presburger
qed

lemma infsum_constant_finite_states_summable:
  assumes "finite {s. b s}"
  shows "(\<lambda>v\<^sub>0::'a. (if b v\<^sub>0 then (m::\<real>) else 0)) summable_on UNIV"
  apply (simp add: summable_on_def)
  apply (rule_tac x = "m * card {s. b s}" in exI)
  apply (simp add: has_sum_def)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
  apply (rule_tac x = "{v. b v}" in exI)
  apply (auto)
  using assms apply force
proof -
  fix S::"\<bbbP> \<real>" and Y::"\<bbbP> 'a"
  assume a1: "m * real (card (Collect b)) \<in> S"
  assume a2: "finite Y" 
  assume a3: " {v::'a. b v} \<subseteq> Y"
  have "(\<Sum>v\<^sub>0::'a\<in>Y. if b v\<^sub>0 then m else (0::\<real>)) = (\<Sum>v\<^sub>0::'a\<in>{v::'a. b v}. if b v\<^sub>0 then m else (0::\<real>))"
    by (smt (verit, best) DiffD2 a2 a3 mem_Collect_eq sum.mono_neutral_cong_right)
  moreover have "... = m * card {s. b s}"
    by auto
  ultimately show "(\<Sum>v\<^sub>0::'a\<in>Y. if b v\<^sub>0 then m else (0::\<real>)) \<in> S"
    using a1 by presburger
qed

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

lemma infsum_not_zero_summable:
  assumes "infsum f A = x"
  assumes "x \<noteq> 0"
  shows "f summable_on A"
  using assms(1) assms(2) infsum_not_exists by blast

lemma infsum_mult_subset_left_summable: 
  assumes "P summable_on UNIV"
  shows "(\<lambda>v\<^sub>0::'a. ((if b v\<^sub>0 then (m::\<real>) else 0) * (P v\<^sub>0))) summable_on UNIV"
  apply (subgoal_tac "(\<lambda>v\<^sub>0. (if b v\<^sub>0 then (m::\<real>) else 0) * (P v\<^sub>0)) summable_on UNIV
    \<longleftrightarrow> (\<lambda>x::'a. m * P x) summable_on {x. b x}")
  apply (metis assms subset_UNIV summable_on_cmult_right summable_on_subset_banach)
  apply (rule summable_on_cong_neutral)
  apply blast
  apply simp
  by auto

subsection \<open> Laws of type @{type prel} \<close>
lemma prel_is_dist: "is_final_distribution (rfrel_of_prel (P::('a, 'b) prel))"
  using rfrel_of_prel by force

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

lemma prel_is_prob: "\<forall>s\<^sub>1::'s\<^sub>1. is_prob ((curry (rfrel_of_prel Q)) s\<^sub>1)"
  using is_dist_def rfrel_of_prel by fastforce

lemma prel_in_0_1: "(curry (rfrel_of_prel Q)) x y \<ge> 0 \<and> (curry (rfrel_of_prel Q)) x y \<le> 1"
  using prel_is_prob 
  by (smt (verit) SEXP_def is_prob_def taut_def)

lemma prel_in_0_1': "(rfrel_of_prel Q) s \<ge> 0 \<and> (rfrel_of_prel Q) s \<le> 1"
  using prel_in_0_1 curry_conv
  by (metis case_prod_curry split_def)

lemma prel_sum_1: "(\<Sum>\<^sub>\<infinity>s::'a. rfrel_of_prel P (s\<^sub>1, s)) = (1::\<real>)"
  using prel_prob_sum1_summable(2) rfrel_of_prel by fastforce

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
  "(\<Sum>\<^sub>\<infinity> (s::'a, v\<^sub>0::'a) \<in> {(s::'a, v\<^sub>0::'a) | s v\<^sub>0. put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s}. rfrel_of_prel P (s\<^sub>1, v\<^sub>0)) = 
   (\<Sum>\<^sub>\<infinity> v\<^sub>0::'a. rfrel_of_prel P (s\<^sub>1, v\<^sub>0))"
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
  have "(\<Sum>\<^sub>\<infinity>s::'a. rfrel_of_prel P (s\<^sub>1, s)) = (1::\<real>)"
    by (simp add: prel_sum_1)
  then have "has_sum (\<lambda>s::'a. rfrel_of_prel P (s\<^sub>1, s)) UNIV (1::\<real>)"
    by (metis has_sum_infsum infsum_not_exists zero_neq_one)
  then have "(sum (\<lambda>s::'a. rfrel_of_prel P (s\<^sub>1, s)) \<longlongrightarrow> (1::\<real>)) (finite_subsets_at_top UNIV)"
    using has_sum_def by blast
  then have "\<forall>\<^sub>F x::\<bbbP> 'a in finite_subsets_at_top UNIV. (\<Sum>s::'a\<in>x. rfrel_of_prel P (s\<^sub>1, s)) \<in> S"
    using a1 a2 tendsto_def by blast
  then have f0: "\<exists>X::\<bbbP> 'a. finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> 
      (\<Sum>s::'a\<in>Y. rfrel_of_prel P (s\<^sub>1, s)) \<in> S)"
    by (simp add: eventually_finite_subsets_at_top)
  then show "\<exists>X::'a rel. finite X \<and> X \<subseteq> {uu::'a \<times> 'a. \<exists>v\<^sub>0::'a. uu = (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0)} \<and>
          (\<forall>Y::'a rel.
              finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> {uu::'a \<times> 'a. \<exists>v\<^sub>0::'a. uu = (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0)} \<longrightarrow>
              (\<Sum>x::'a \<times> 'a\<in>Y. case x of (s::'a, v\<^sub>0::'a) \<Rightarrow> rfrel_of_prel P (s\<^sub>1, v\<^sub>0)) \<in> S)"
  proof -
    assume a11: "\<exists>X::\<bbbP> 'a. finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> 
      (\<Sum>s::'a\<in>Y. rfrel_of_prel P (s\<^sub>1, s)) \<in> S)"
    have f1: "finite
       {uu::'a \<times> 'a. \<exists>v\<^sub>0::'a. v\<^sub>0 \<in> (SOME X::\<bbbP> 'a.
          finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> (\<Sum>s::'a\<in>Y. rfrel_of_prel P (s\<^sub>1, s)) \<in> S))
        \<and> uu = (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0)}"
      apply (subst finite_Collect_bounded_ex)
      apply (smt (verit, ccfv_threshold) CollectD a11 rev_finite_subset someI_ex subset_iff)
      by (auto)
    show ?thesis
      (* Construct a witness from existing X from f0 using SOME (indifinite description) *)
      apply (rule_tac x = "{(put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0) | v\<^sub>0 . 
        v\<^sub>0 \<in> (SOME X::\<bbbP> 'a. finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> 
        (\<Sum>s::'a\<in>Y. rfrel_of_prel P (s\<^sub>1, s)) \<in> S))}" in exI)
      apply (rule conjI)
      using f1 apply (smt (verit, best) Collect_mono rev_finite_subset)
      apply (auto)
    proof -
      fix Y::"'a rel"
      assume a111: "finite Y"
      assume a112: "{uu::'a \<times> 'a.
        \<exists>v\<^sub>0::'a.
           uu = (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0) \<and>
           v\<^sub>0 \<in> (SOME X::\<bbbP> 'a. finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> (\<Sum>s::'a\<in>Y. rfrel_of_prel P (s\<^sub>1, s)) \<in> S))}
       \<subseteq> Y"
      assume a113: "Y \<subseteq> {uu::'a \<times> 'a. \<exists>v\<^sub>0::'a. uu = (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0)}"
      have f11: "(\<Sum>s::'a\<in>Range Y. rfrel_of_prel P (s\<^sub>1, s)) \<in> S"
        using a11 a111 a112
        by (smt (verit, del_insts) Range_iff finite_Range mem_Collect_eq subset_iff verit_sko_ex_indirect)
      have f12: "inj_on (\<lambda>v\<^sub>0. (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0)) (Range Y)"
        using inj_on_def by blast
      have f13: "(\<Sum>x::'a \<times> 'a\<in>Y. case x of (s::'a, v\<^sub>0::'a) \<Rightarrow> rfrel_of_prel P (s\<^sub>1, v\<^sub>0)) = 
            (\<Sum>s::'a\<in>Range Y. rfrel_of_prel P (s\<^sub>1, s))"
        apply (rule sum.reindex_cong[where l = "(\<lambda>v\<^sub>0. (put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0), v\<^sub>0))" and B = "Range Y"]) 
        apply (simp add: f12)
        using a113 by (auto)
      show "(\<Sum>x::'a \<times> 'a\<in>Y. case x of (s::'a, v\<^sub>0::'a) \<Rightarrow> rfrel_of_prel P (s\<^sub>1, v\<^sub>0)) \<in> S"
        using f11 f13 by presburger
    qed
  qed
qed

(*
lemma 
  assumes "finite Y"
  shows  "(\<Sum>x::'a \<times> 'a\<in>Y. case x of (ss::'a, s::'a) \<Rightarrow> P s) = (\<Sum>s::'a \<in> Range Y. P s)"
  sledgehammer

lemma prel_sum_1': "(\<Sum>\<^sub>\<infinity>(ss::'a, s::'a). rfrel_of_prel P (s\<^sub>1, s)) = (1::\<real>)"
  apply (rule infsumI)
  apply (simp add: has_sum_def)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
proof -
  fix S::"\<bbbP> \<real>"
  assume a1: "open S"
  assume a2: "(1::\<real>) \<in> S"

  have "(\<Sum>\<^sub>\<infinity>s::'a. rfrel_of_prel P (s\<^sub>1, s)) = (1::\<real>)"
    by (simp add: prel_sum_1)
  then have "has_sum (\<lambda>s::'a. rfrel_of_prel P (s\<^sub>1, s)) UNIV (1::\<real>)"
    by (metis has_sum_infsum infsum_not_exists zero_neq_one)
  then have "(sum (\<lambda>s::'a. rfrel_of_prel P (s\<^sub>1, s)) \<longlongrightarrow> (1::\<real>)) (finite_subsets_at_top UNIV)"
    using has_sum_def by blast
  then have "\<forall>\<^sub>F x::\<bbbP> 'a in finite_subsets_at_top UNIV. (\<Sum>s::'a\<in>x. rfrel_of_prel P (s\<^sub>1, s)) \<in> S"
    using a1 a2 tendsto_def by blast
  then have "\<exists>X::\<bbbP> 'a. finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> 
      (\<Sum>s::'a\<in>Y. rfrel_of_prel P (s\<^sub>1, s)) \<in> S)"
    by (simp add: eventually_finite_subsets_at_top)
  then show "\<exists>X::'a rel. finite X \<and> (\<forall>Y::'a rel. finite Y \<and> X \<subseteq> Y \<longrightarrow> 
    (\<Sum>(ss::'a, s::'a)\<in>Y. rfrel_of_prel P (s\<^sub>1, s)) \<in> S)"
  proof -
    assume a11: "\<exists>X::\<bbbP> 'a. finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> 
      (\<Sum>s::'a\<in>Y. rfrel_of_prel P (s\<^sub>1, s)) \<in> S)"
    have f1: "finite
       {uu::'a \<times> 'a. \<exists>x::'a. x \<in> (SOME X::\<bbbP> 'a.
          finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> (\<Sum>s::'a\<in>Y. rfrel_of_prel P (s\<^sub>1, s)) \<in> S))
        \<and> uu = (x, x)}"
      apply (subst finite_Collect_bounded_ex)
      apply (smt (verit, ccfv_threshold) CollectD a11 rev_finite_subset someI_ex subset_iff)
      by (auto)
    show ?thesis
      apply (rule_tac x = "{(x, x) | x . 
        x \<in> (SOME X::\<bbbP> 'a. finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> 
        (\<Sum>s::'a\<in>Y. rfrel_of_prel P (s\<^sub>1, s)) \<in> S))}" in exI)
      apply (rule conjI)
      using f1 apply (smt (verit, best) Collect_mono rev_finite_subset)
      apply (auto)
      sledgehammer
      apply (rule someI_ex)
qed
*)

lemma prel_summable: "(\<lambda>x::'a. rfrel_of_prel P (s\<^sub>1, x)) summable_on UNIV"
proof (rule ccontr)
  assume a1: "\<not> (\<lambda>x::'a. rfrel_of_prel P (s\<^sub>1, x)) summable_on UNIV"
  from a1 have "(\<Sum>\<^sub>\<infinity>s::'a. rfrel_of_prel P (s\<^sub>1, s)) = (0::\<real>)"
    by (simp add: infsum_def)
  then show "False"
    by (simp add: prel_sum_1)
qed

lemma real_space_complete: "complete (UNIV::real set)"
  by (simp add: complete_def convergentD real_Cauchy_convergent)

lemma prel_summable_on_subset:
  shows "(\<lambda>x::'a. rfrel_of_prel P (s\<^sub>1, x)) summable_on A"
  apply (rule summable_on_subset[where A="UNIV" and B = "A"])
  apply (simp add: real_space_complete)
  apply simp
  apply (simp add: prel_summable)
  by simp

lemma prel_mult_subset_left_summable:
  shows "(\<lambda>v\<^sub>0. (if b v\<^sub>0 then (1::\<real>) else 0) * (rfrel_of_prel P (s\<^sub>1, v\<^sub>0))) summable_on UNIV"
  apply (subgoal_tac "(\<lambda>v\<^sub>0. (if b v\<^sub>0 then (1::\<real>) else 0) * (rfrel_of_prel P (s\<^sub>1, v\<^sub>0))) summable_on UNIV
    \<longleftrightarrow> (\<lambda>x::'a. rfrel_of_prel P (s\<^sub>1, x)) summable_on {x. b x}")
  apply (simp add: prel_summable_on_subset)
  apply (rule summable_on_cong_neutral)
  by simp+

lemma prel_mult_subset_right_summable:
  shows "(\<lambda>v\<^sub>0. (rfrel_of_prel P (s\<^sub>1, v\<^sub>0)) * (if b v\<^sub>0 then (1::\<real>) else 0)) summable_on UNIV"
  apply (subst summable_on_cong[where 
        g = "(\<lambda>v\<^sub>0. (if b v\<^sub>0 then (1::\<real>) else 0) * (rfrel_of_prel P (s\<^sub>1, v\<^sub>0)))"])
  using mult.commute apply blast
  by (simp add: prel_mult_subset_left_summable)

lemma prel_infsum_infsum_mult_singleton_1:
  "(\<Sum>\<^sub>\<infinity>s::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if c = v\<^sub>0 then 1::\<real> else (0::\<real>)) * rfrel_of_prel P (v\<^sub>0, s)) = (1::\<real>)"
  apply (subst infsum_mult_singleton_left_1)
  by (simp add: prel_sum_1)

(*
lemma "(\<Sum>\<^sub>\<infinity>s. r (s\<^sub>1, s) * rfrel_of_prel P (s\<^sub>1, s) + ((1::\<real>) - r (s\<^sub>1, s)) * rfrel_of_prel Q (s\<^sub>1, s))
  = ((\<Sum>\<^sub>\<infinity>s. r (s\<^sub>1, s) * ( rfrel_of_prel P (s\<^sub>1, s) - rfrel_of_prel Q (s\<^sub>1, s))) + (\<Sum>\<^sub>\<infinity>s. rfrel_of_prel Q (s\<^sub>1, s)))"
proof -
  have "(\<Sum>\<^sub>\<infinity>s. r (s\<^sub>1, s) * rfrel_of_prel P (s\<^sub>1, s) + ((1::\<real>) - r (s\<^sub>1, s)) * rfrel_of_prel Q (s\<^sub>1, s)) 
    = (\<Sum>\<^sub>\<infinity>s. rfrel_of_prel Q (s\<^sub>1, s) + r (s\<^sub>1, s) * (rfrel_of_prel P (s\<^sub>1, s) - rfrel_of_prel Q (s\<^sub>1, s)))"
    apply (rule infsum_cong)
    by (smt (verit, ccfv_SIG) distrib_right mult_cancel_right1 right_diff_distrib)
  also have "... = (\<Sum>\<^sub>\<infinity>s. rfrel_of_prel Q (s\<^sub>1, s)) + (\<Sum>\<^sub>\<infinity>s. r (s\<^sub>1, s) * (rfrel_of_prel P (s\<^sub>1, s) - rfrel_of_prel Q (s\<^sub>1, s)))"
    apply (rule infsum_add)
     apply (simp add: prel_summable)
    sorry
  also have "... = 1 + (\<Sum>\<^sub>\<infinity>s. r (s\<^sub>1, s) * (rfrel_of_prel P (s\<^sub>1, s) - rfrel_of_prel Q (s\<^sub>1, s)))"
    by (simp add: prel_sum_1)
qed

lemma prel_prob_choice_is_dist:
  assumes "\<forall>s. 0 \<le> r s \<and> r s \<le> 1"
  shows "(\<Sum>\<^sub>\<infinity>s::'a. r (s\<^sub>1, s) * rfrel_of_prel P (s\<^sub>1, s) + 
          ((1::\<real>) - r (s\<^sub>1, s)) * rfrel_of_prel Q (s\<^sub>1, s)) = (1::\<real>)"
  apply (rule infsumI)
  apply (simp add: has_sum_def)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
  oops
*)

lemma Sigma_Un_distrib2:
  shows "Sigma A (\<lambda>s. B s) \<union> Sigma A (\<lambda>s. C s) = Sigma A (\<lambda>s. (B s \<union> C s))"
  apply (simp add: Sigma_def)
  by (auto)

lemma prel_Sigma_UNIV_divide:
  assumes "is_final_distribution q"
  shows "Sigma (UNIV) (\<lambda>v\<^sub>0. {s'. q(v\<^sub>0, s') > (0::real)}) \<union> (Sigma (UNIV) (\<lambda>v\<^sub>0. {s'. q(v\<^sub>0, s') = (0::real)})) 
    = Sigma (UNIV) (\<lambda>v\<^sub>0. UNIV)"
  apply (simp add: Sigma_Un_distrib2)
  apply (auto)
  by (metis antisym_conv2 assms prel_prob_sum1_summable(1))

lemma prel_infsum_1_finite_subset:
  assumes "is_final_distribution p"
  shows "\<forall>S::\<bbbP> \<real>. open S \<longrightarrow> (1::\<real>) \<in> S \<longrightarrow> 
    (\<exists>X::\<bbbP> 'a. finite X \<and> (\<forall>Y::\<bbbP> 'a. finite Y \<and> X \<subseteq> Y \<longrightarrow> (\<Sum>s::'a\<in>Y. p (s\<^sub>1, s)) \<in> S))"
proof -
  have "(\<Sum>\<^sub>\<infinity>s::'a. p (s\<^sub>1, s)) = (1::\<real>)"
    by (simp add: assms(1) prel_prob_sum1_summable(2))
  then have "has_sum (\<lambda>s::'a. p (s\<^sub>1, s)) UNIV (1::\<real>)"
    by (metis has_sum_infsum infsum_not_exists zero_neq_one)
  then have "(sum (\<lambda>s::'a. p (s\<^sub>1, s)) \<longlongrightarrow> (1::\<real>)) (finite_subsets_at_top UNIV)"
    using has_sum_def by blast
  then have "\<forall>S::\<bbbP> \<real>. open S \<longrightarrow> (1::\<real>) \<in> S \<longrightarrow> (\<forall>\<^sub>F x::\<bbbP> 'a in finite_subsets_at_top UNIV. (\<Sum>s::'a\<in>x. p (s\<^sub>1, s)) \<in> S)"
    by (simp add: tendsto_def)
  thus ?thesis
    by (simp add: eventually_finite_subsets_at_top)
qed


subsection \<open> @{text "is_final_distribution"} \<close>

lemma prel_is_dist_skip: "is_final_distribution (pskip\<^sub>_f)"
  apply (simp add: dist_defs expr_defs)
  by (simp add: infsum_singleton)

lemma prel_is_dist_assign: "is_final_distribution (passigns_f \<sigma>)"
  apply (simp add: dist_defs expr_defs)
  apply (rel_auto)
  by (simp add: infsum_singleton)

subsubsection \<open> Probabilistic choice \<close>
text \<open>If @{text r} is a real-valued function over the initial state, the probabilistic choice of 
@{text p} and @{text q} (both are distributions of the final states) with weight @{text r} is also 
a distribution of the final state. \<close>
lemma prel_is_dist_pchoice: 
  assumes "\<forall>s. 0 \<le> r s \<and> r s \<le> (1::\<real>)"
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "is_final_distribution (pchoice_f p (\<lambda>(s, s'). r s) q)"
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

text \<open>This is a more specific case where @{text r} is a literal number. \<close>
lemma prel_is_dist_pchoice': 
  assumes "0 \<le> r \<and> r \<le> (1::\<real>)"
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "is_final_distribution (pchoice_f p (\<lambda>s. r) q)"
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

subsubsection \<open> Conditional choice \<close>

lemma prel_is_dist_pcond: 
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "is_final_distribution (pcond_f p (\<lambda>(s, s'). b s) q)"
  apply (simp add: dist_defs expr_defs, auto)
  using assms(1) prel_prob_sum1_summable(1) apply blast
  using assms(1) prel_prob_sum1_summable(1) apply blast
  using assms(2) prel_prob_sum1_summable(1) apply blast
  using assms(2) prel_prob_sum1_summable(1) apply blast
  by (smt (verit, best) assms(1) assms(2) curry_conv infsum_cong is_dist_def is_sum_1_def)
 
subsubsection \<open> Sequential composition \<close>

lemma prel_cond_prob_abs_summable_on_product:
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "(\<lambda>(v\<^sub>0::'a, s::'a). p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) abs_summable_on 
          Sigma (UNIV) (\<lambda>v\<^sub>0. {s'. q(v\<^sub>0, s') > (0::real)})"
  apply (subst abs_summable_on_Sigma_iff)
  apply (rule conjI)
  apply (auto)
proof -
  fix x::"'a"

  have f1: "(\<lambda>xa::'a. \<bar>p (s\<^sub>1, x) * q (x, xa)\<bar>) = (\<lambda>xa::'a. p (s\<^sub>1, x) * q (x, xa))"
    apply (subst abs_of_nonneg)
    by (simp add: assms(1) assms(2) prel_prob_sum1_summable(1))+
  have f2: "(\<lambda>xa::'a. p (s\<^sub>1, x) * q (x, xa)) summable_on {s'::'a. (0::\<real>) < q (x, s')}"
    apply (rule summable_on_cmult_right)
    apply (rule summable_on_subset_banach[where A="UNIV"])
    using assms(1) assms(2) prel_prob_sum1_summable(3) apply metis
    by (simp)
  show "(\<lambda>xa::'a. \<bar>p (s\<^sub>1, x) * q (x, xa)\<bar>) summable_on {s'::'a. (0::\<real>) < q (x, s')}"
    using f1 f2 by presburger
next
  have f1: "(\<lambda>x::'a. \<bar>\<Sum>\<^sub>\<infinity>y::'a\<in>{s'::'a. (0::\<real>) < q (x, s')}. \<bar>p (s\<^sub>1, x) * q (x, y)\<bar>\<bar>) =
      (\<lambda>x::'a. \<Sum>\<^sub>\<infinity>y::'a\<in>{s'::'a. (0::\<real>) < q (x, s')}. p (s\<^sub>1, x) * q (x, y))"
    apply (subst abs_of_nonneg)
    apply (subst abs_of_nonneg)
    apply (simp add: assms(1) assms(2) prel_prob_sum1_summable(1))+
     apply (simp add: assms(1) assms(2) infsum_nonneg prel_prob_sum1_summable(1))
    apply (subst abs_of_nonneg)
    by (simp add: assms(1) assms(2) prel_prob_sum1_summable(1))+
  then have f2: "... = (\<lambda>x::'a. p (s\<^sub>1, x) * (\<Sum>\<^sub>\<infinity>y::'a\<in>{s'::'a. (0::\<real>) < q (x, s')}. q (x, y)))"
    using infsum_cmult_right' by fastforce
  have f3: "... = (\<lambda>x::'a. p (s\<^sub>1, x))"
    apply (rule ext)
    proof -
      fix x
      have f31: "(\<Sum>\<^sub>\<infinity>y::'a\<in>{s'::'a. (0::\<real>) < q (x, s')}. q (x, y)) = 
        (\<Sum>\<^sub>\<infinity>y::'a\<in>{s'::'a. (0::\<real>) < q (x, s')} \<union> {s'::'a. (0::\<real>) = q (x, s')}. q (x, y))"
        apply (rule infsum_cong_neutral)
        by force+
      then have f32: "... = (\<Sum>\<^sub>\<infinity>y::'a. q (x, y))"
        by (smt (verit, del_insts) assms(2) infsum_cong infsum_mult_subset_right mult_cancel_left1 
              prel_prob_sum1_summable(1))
      then have f33: "... = 1"
        by (simp add: assms(2) prel_prob_sum1_summable(2))
      then show "p (s\<^sub>1, x) * (\<Sum>\<^sub>\<infinity>y::'a\<in>{s'::'a. (0::\<real>) < q (x, s')}. q (x, y)) = p (s\<^sub>1, x)"
        using f31 f32 by auto
    qed
  have f4: "infsum (\<lambda>x::'a. \<Sum>\<^sub>\<infinity>y::'a\<in>{s'::'a. (0::\<real>) < q (x, s')}. p (s\<^sub>1, x) * q (x, y)) UNIV = 
      infsum (\<lambda>x::'a. p (s\<^sub>1, x)) UNIV"
    using f2 f3 by presburger
  then have f5: "... = 1"
    by (simp add: assms(1) prel_prob_sum1_summable(2))
    
  have f6: "(\<lambda>x::'a. \<Sum>\<^sub>\<infinity>y::'a\<in>{s'::'a. (0::\<real>) < q (x, s')}. p (s\<^sub>1, x) * q (x, y)) summable_on UNIV"
    using f4 f5 infsum_not_exists by fastforce
    
  show "(\<lambda>x::'a. \<bar>\<Sum>\<^sub>\<infinity>y::'a\<in>{s'::'a. (0::\<real>) < q (x, s')}. \<bar>p (s\<^sub>1, x) * q (x, y)\<bar>\<bar>) summable_on UNIV"
    using f1 f6 by presburger
qed

lemma prel_cond_prob_product_summable_on_sigma_possible_sets:
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "(\<lambda>(v\<^sub>0::'a, s::'a). p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) summable_on 
          Sigma (UNIV) (\<lambda>v\<^sub>0. {s'. q(v\<^sub>0, s') > (0::real)})"
  apply (subst summable_on_iff_abs_summable_on_real)
  using prel_cond_prob_abs_summable_on_product assms(1) assms(2) by fastforce

lemma prel_cond_prob_product_summable_on_sigma_impossible_sets:
  shows "(\<lambda>(v\<^sub>0::'a, s::'a). p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) summable_on (Sigma (UNIV) (\<lambda>v\<^sub>0. {s'. q(v\<^sub>0, s') = (0::real)}))"
  apply (simp add: summable_on_def)
  apply (rule_tac x = "0" in exI)
  apply (rule has_sum_0)
  by force

lemma prel_cond_prob_product_summable_on_UNIV:
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "(\<lambda>(v\<^sub>0::'a, s::'a). p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) summable_on Sigma (UNIV) (\<lambda>v\<^sub>0. UNIV)"
proof -
  let ?A1 = "Sigma (UNIV) (\<lambda>v\<^sub>0. {s'. q(v\<^sub>0, s') > (0::real)})"
  let ?A2 = "Sigma (UNIV) (\<lambda>v\<^sub>0. {s'. q(v\<^sub>0, s') = (0::real)})"
  let ?f = "(\<lambda>(v\<^sub>0::'a, s::'a). p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s))"

  have "?f summable_on (?A1 \<union> ?A2)"
    apply (rule summable_on_Un_disjoint)
    apply (simp add: assms(1) assms(2) prel_cond_prob_product_summable_on_sigma_possible_sets)
    apply (simp add: prel_cond_prob_product_summable_on_sigma_impossible_sets)
    by fastforce
  then show ?thesis
    by (simp add: assms(2) prel_Sigma_UNIV_divide)
qed

lemma prel_cond_prob_product_summable_on_UNIV_2:
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows " (\<lambda>(s::'a, v\<^sub>0::'a). p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) summable_on UNIV \<times> UNIV"
    apply (subst product_swap[symmetric])
    apply (subst summable_on_reindex)
    apply simp
    proof -
      have f0: "(\<lambda>(s::'a, v\<^sub>0::'a). p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) \<circ> prod.swap = (\<lambda>(v\<^sub>0::'a, s::'a). p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s))"
        by (simp add: comp_def)
      show "(\<lambda>(s::'a, v\<^sub>0::'a). p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) \<circ> prod.swap summable_on UNIV \<times> UNIV"
        using assms(1) assms(2) f0 prel_cond_prob_product_summable_on_UNIV by fastforce
    qed

lemma prel_cond_prob_infsum_pcomp_swap:
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "(\<Sum>\<^sub>\<infinity>s::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. \<Sum>\<^sub>\<infinity>s::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s))"
  apply (rule infsum_swap_banach)
  using assms(1) assms(2) prel_cond_prob_product_summable_on_UNIV_2 by fastforce

lemma prel_infsum_pcomp_sum_1:
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "(\<Sum>\<^sub>\<infinity>s::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) = 1"
  apply (simp add: assms prel_cond_prob_infsum_pcomp_swap)
  apply (simp add: infsum_cmult_right')
  by (simp add: assms prel_prob_sum1_summable)

lemma prel_is_dist_pcomp: 
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "is_final_distribution (pcomp_f p q)"
  apply (simp add: dist_defs expr_defs, auto)
  apply (simp add: assms(1) assms(2) infsum_nonneg prel_prob_sum1_summable(1))
  defer
  apply (simp_all add: lens_defs)
  apply (simp add: assms(1) assms(2) prel_infsum_pcomp_sum_1)
proof (rule ccontr)
  fix s\<^sub>1::"'a" and s::"'a"
  let ?f = "\<lambda>s. (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s))"
  assume a1: " \<not> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) \<le> (1::\<real>)"
  then have f0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) > 1"
    by force
  have f1: "(\<lambda>s::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) summable_on UNIV"
    apply (rule infsum_not_zero_summable[where x = 1])
    by (simp add: assms(1) assms(2) prel_infsum_pcomp_sum_1)+
  have f2: "(\<Sum>\<^sub>\<infinity>ss::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, ss)) = 
    (\<Sum>\<^sub>\<infinity>ss::'a\<in>{s} \<union> {ss. ss \<noteq> s}. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, ss))"
    by (metis (mono_tags, lifting) CollectI DiffD2 UNIV_I UnCI infsum_cong_neutral insert_iff)
  also have f3: "... = (\<Sum>\<^sub>\<infinity>ss::'a\<in>{s}. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, ss)) + 
    (\<Sum>\<^sub>\<infinity>ss::'a\<in>{ss. ss \<noteq> s}. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, ss))"
    apply (rule infsum_Un_disjoint)
    apply simp
    using f1 summable_on_subset_banach apply blast
    by simp
  also have f4: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, s)) + 
    (\<Sum>\<^sub>\<infinity>ss::'a\<in>{ss. ss \<noteq> s}. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, ss))"
    by simp
  also have f5: "... > 1"
    by (smt (verit, del_insts) a1 assms(1) assms(2) infsum_nonneg mult_nonneg_nonneg 
          prel_prob_sum1_summable(1))
  have f6: "(\<Sum>\<^sub>\<infinity>ss::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (v\<^sub>0, ss)) > 1"
    using calculation f5 by presburger
  show "False"
    using prel_infsum_pcomp_sum_1 f6 assms(1) assms(2) by fastforce
qed

subsubsection \<open> Normalisation \<close>
lemma prel_is_dist_normalisation:
  assumes "\<forall>s. p s \<ge> 0"
  assumes "\<forall>s. \<exists>s'. p (s, s') > 0"
  assumes "\<forall>s. (\<lambda>v\<^sub>0. p (s, v\<^sub>0)) summable_on UNIV"
  shows "is_final_distribution (\<^bold>N p)"
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: assms infsum_nonneg)
  apply (smt (verit, best) UNIV_I assms(1) divide_le_eq_1 infsum_geq_element infsum_not_zero_summable)
proof -
  fix s\<^sub>1::"'a"
  have f1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. p (s\<^sub>1, v\<^sub>0)) \<ge> p (s\<^sub>1, (SOME s'. p (s\<^sub>1, s') > 0))"
    apply (rule infsum_geq_element)
    using assms(1) apply blast
    using assms(3) apply simp
    by auto
  have f2: "... > 0"
    by (smt (verit, best) assms(2) f1 someI_ex)
  have f3: "(\<Sum>\<^sub>\<infinity>s::'b. p (s\<^sub>1, s) / (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. p (s\<^sub>1, v\<^sub>0))) = 
        (\<Sum>\<^sub>\<infinity>s::'b. (p (s\<^sub>1, s) * (1 / (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. p (s\<^sub>1, v\<^sub>0)))))"
    by auto
  also have f4: "... = (\<Sum>\<^sub>\<infinity>s::'b. p (s\<^sub>1, s)) * (1 / (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. p (s\<^sub>1, v\<^sub>0)))"
    by (metis infsum_cmult_left')
  also have f5: "... = 1"
    using f2 by auto
  thus "(\<Sum>\<^sub>\<infinity>s::'b. p (s\<^sub>1, s) / (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. p (s\<^sub>1, v\<^sub>0))) = (1::\<real>)"
    using calculation by presburger
qed

(*
lemma prel_is_dist_normalisation:
  assumes "\<forall>s. p s \<ge> 0"
  assumes "\<forall>s. \<exists>s'. p (s, s') > 0"
  assumes "\<forall>s. (\<lambda>v\<^sub>0. p (s, v\<^sub>0)) summable_on UNIV"
  assumes "wb_lens x"
  shows "is_final_distribution (\<^bold>N\<^sub>\<alpha> x p)"
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: assms infsum_nonneg)
proof -
  fix s\<^sub>1::"'a" and s::"'b"
  have f1: "\<exists>v. put\<^bsub>x\<^esub> s v = s"
    apply (rule_tac x = "get\<^bsub>x\<^esub> s" in exI)
    by (simp add: assms(4))
  have f2: "p (s\<^sub>1, s) \<le> (\<Sum>\<^sub>\<infinity>v::'c. p (s\<^sub>1, put\<^bsub>x\<^esub> s v))"
    sledgehammer
  show "p (s\<^sub>1, s) / (\<Sum>\<^sub>\<infinity>v::'c. p (s\<^sub>1, put\<^bsub>x\<^esub> s v)) \<le> 1"
next
  fix s\<^sub>1::"'a"
  have f1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. p (s\<^sub>1, v\<^sub>0)) \<ge> p (s\<^sub>1, (SOME s'. p (s\<^sub>1, s') > 0))"
    apply (rule infsum_geq_element)
    using assms(1) apply blast
    using assms(3) apply simp
    by auto
  have f2: "... > 0"
    by (smt (verit, best) assms(2) f1 someI_ex)
  have f3: "(\<Sum>\<^sub>\<infinity>s::'b. p (s\<^sub>1, s) / (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. p (s\<^sub>1, v\<^sub>0))) = 
        (\<Sum>\<^sub>\<infinity>s::'b. (p (s\<^sub>1, s) * (1 / (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. p (s\<^sub>1, v\<^sub>0)))))"
    by auto
  also have f4: "... = (\<Sum>\<^sub>\<infinity>s::'b. p (s\<^sub>1, s)) * (1 / (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. p (s\<^sub>1, v\<^sub>0)))"
    by (metis infsum_cmult_left')
  also have f5: "... = 1"
    using f2 by auto
  thus "(\<Sum>\<^sub>\<infinity>s::'b. p (s\<^sub>1, s) / (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. p (s\<^sub>1, v\<^sub>0))) = (1::\<real>)"
    using calculation by presburger
qed
*)
text \<open> The possible values of @{text "x"} are chosen from a set @{text "A"} and they are equally 
likely to be observed in a program constructed by @{text "uniform_dist x A"} }.
\<close>
lemma prel_is_dist_uniform_dist:
  assumes "finite (A::'b set)"
  assumes "vwb_lens x"
  assumes "A \<noteq> {}"
  shows "is_final_distribution ((x \<^bold>\<U> A))"
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: infsum_nonneg)
  apply (smt (verit) divide_le_eq_1 infsum_0 infsum_geq_element infsum_not_exists)
  apply (rel_auto)
proof -
  fix s\<^sub>1::"'a"
  let ?f = "\<lambda>s. (if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = s then 1::\<real> else (0::\<real>)) /
          (\<Sum>\<^sub>\<infinity>v::'b. if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> s v then 1::\<real> else (0::\<real>))"
  have one_dvd_card_A: "\<forall>s. ((\<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = s) \<longrightarrow> 
      (((1::\<real>) / (card {v. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> s v})) = ((1::\<real>) / (card A))))"
    apply (auto)
    apply (simp add: assms(2))
    apply (subgoal_tac "{v::'b. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> s\<^sub>1 v} = A")
    apply (simp)
    apply (subst set_eq_iff)
    apply (auto)
  proof (rule ccontr)
    fix xa::"'b" and xb::"'b" and  xaa::"'b"
    assume a1: "xa \<in> A"
    assume a2: "xaa \<in> A"
    assume a3: "put\<^bsub>x\<^esub> s\<^sub>1 xaa = put\<^bsub>x\<^esub> s\<^sub>1 xb"
    assume a4: "\<not> xb \<in> A"
    from a2 a4 have "xaa \<noteq> xb"
      by auto
    then have "put\<^bsub>x\<^esub> s\<^sub>1 xaa \<noteq> put\<^bsub>x\<^esub> s\<^sub>1 xb"
      using assms(2) by (meson vwb_lens_wb wb_lens_weak weak_lens.view_determination)
    thus "False"
      using a3 by blast
  qed

  have "finite {put\<^bsub>x\<^esub> s\<^sub>1 xa | xa. xa \<in> A}"
    apply (rule finite_image_set)
    using assms(1) by auto
  then have finite_states: "finite {s. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = s}"
    by (smt (verit, del_insts) Collect_cong)
  
  have "inj_on (\<lambda>xa. put\<^bsub>x\<^esub> s\<^sub>1 xa) A"
    by (meson assms(2) inj_onI vwb_lens_wb wb_lens_def weak_lens.view_determination)
  then have card_A: "card ((\<lambda>xa. put\<^bsub>x\<^esub> s\<^sub>1 xa) ` A ) = card A"
    using card_image by blast
  have set_as_f_image: "{s. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = s} = ((\<lambda>xa. put\<^bsub>x\<^esub> s\<^sub>1 xa) ` A )"
    by blast
  have "(\<Sum>\<^sub>\<infinity>s::'a. ?f s) = (\<Sum>\<^sub>\<infinity>s::'a. (if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = s then 1::\<real> else (0::\<real>)) 
      / (card {v. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> s v}))"
    apply (subst infsum_constant_finite_states)
    apply (subst finite_Collect_bex)
    apply (simp add: assms(1))
    apply (auto)
    apply (subgoal_tac "\<forall>xa. (put\<^bsub>x\<^esub> s\<^sub>1 y = put\<^bsub>x\<^esub> s xa) \<longrightarrow> y = xa")
    apply (smt (verit, ccfv_SIG) assms(1) mem_Collect_eq rev_finite_subset subset_iff)
    using weak_lens.view_determination vwb_lens_wb wb_lens_weak assms(2) by metis
  also have "... = (\<Sum>\<^sub>\<infinity>s::'a. (if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = s then 
                ((1::\<real>) / (card {v. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> s v}))
              else (0::\<real>)))"
    apply (rule infsum_cong)
    by simp
  also have "... = (\<Sum>\<^sub>\<infinity>s::'a. (if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = s then 
                ((1::\<real>) / (card A)) else (0::\<real>)))"
    apply (rule infsum_cong)
    using one_dvd_card_A by presburger
  also have "... = ((1::\<real>) / (card A)) * (card {s. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = s})"
    apply (rule infsum_constant_finite_states)
    using finite_states by blast
  also have "... = ((1::\<real>) / (card A)) * (card A)"
    using card_A set_as_f_image by presburger
  also have "... = 1"
    by (simp add: assms(1) assms(3))
  then show "(\<Sum>\<^sub>\<infinity>s::'a.
          (if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = s then 1::\<real> else (0::\<real>)) /
          (\<Sum>\<^sub>\<infinity>v::'b. if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> s v then 1::\<real> else (0::\<real>))) =
       (1::\<real>)"
    using calculation by presburger
qed

lemma uniform_dist_is_uniform:
  assumes "finite (A::'b set)"
  assumes "vwb_lens x"
  assumes "A \<noteq> {}"
  shows "\<forall>v \<in> A. ((x \<^bold>\<U> A) ;\<^sub>f (\<lbrakk>$x\<^sup>< = \<guillemotleft>v\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e) = (1/card \<guillemotleft>A\<guillemotright>)\<^sub>e)"
  apply (simp add: dist_defs prel_defs)
  apply (expr_auto)
  apply (rel_auto)
proof -
  fix v::"'b" and s\<^sub>1::"'a"
  assume a1: "v \<in> A"
  let ?f1 = "\<lambda>v\<^sub>0. (if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = v\<^sub>0 then 1::\<real> else (0::\<real>))"
  let ?f2 = "\<lambda>v\<^sub>0. (if get\<^bsub>x\<^esub> v\<^sub>0 = v then 1::\<real> else (0::\<real>))"
  let ?f = "\<lambda>v\<^sub>0. (if (\<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = v\<^sub>0) \<and> (get\<^bsub>x\<^esub> v\<^sub>0 = v) then 1::\<real> else (0::\<real>))"
  let ?sum = "\<lambda>v\<^sub>0. (\<Sum>\<^sub>\<infinity>v::'b. if \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> v\<^sub>0 v then 1::\<real> else (0::\<real>))"

  have one_dvd_card_A: "\<forall>s. ((\<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = s) \<longrightarrow> 
      (((1::\<real>) / (card {v. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> s v})) = ((1::\<real>) / (card A))))"
    apply (auto)
    apply (simp add: assms(2))
    apply (subgoal_tac "{v::'b. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> s\<^sub>1 v} = A")
    apply (simp)
    apply (subst set_eq_iff)
    apply (auto)
  proof (rule ccontr)
    fix xa::"'b" and xb::"'b" and  xaa::"'b"
    assume a1: "xa \<in> A"
    assume a2: "xaa \<in> A"
    assume a3: "put\<^bsub>x\<^esub> s\<^sub>1 xaa = put\<^bsub>x\<^esub> s\<^sub>1 xb"
    assume a4: "\<not> xb \<in> A"
    from a2 a4 have "xaa \<noteq> xb"
      by auto
    then have "put\<^bsub>x\<^esub> s\<^sub>1 xaa \<noteq> put\<^bsub>x\<^esub> s\<^sub>1 xb"
      using assms(2) by (meson vwb_lens_wb wb_lens_weak weak_lens.view_determination)
    thus "False"
      using a3 by blast
  qed

  have "finite {put\<^bsub>x\<^esub> s\<^sub>1 xa | xa. xa \<in> A}"
    apply (rule finite_image_set)
    using assms(1) by auto
  then have "finite {v\<^sub>0. (\<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = v\<^sub>0)}"
    by (smt (verit, del_insts) Collect_cong)
  then have finite_states: "finite {v\<^sub>0. (\<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = v\<^sub>0) \<and> (get\<^bsub>x\<^esub> v\<^sub>0 = v)}"
    apply (rule rev_finite_subset[where B = "{v\<^sub>0. (\<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = v\<^sub>0)}"])
    by auto

  have card_singleton: "card {v\<^sub>0. (\<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = v\<^sub>0) \<and> (get\<^bsub>x\<^esub> v\<^sub>0 = v)} = Suc (0)"
    apply (simp add: card_1_singleton_iff)
    apply (rule_tac x = "put\<^bsub>x\<^esub> s\<^sub>1 v" in exI)
    using a1 assms(2) by auto

  have "\<forall>v\<^sub>0. ?f1 v\<^sub>0 * ?f2 v\<^sub>0 = ?f v\<^sub>0"
    by (auto)
  then have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. ?f1 v\<^sub>0 * ?f2 v\<^sub>0 / ?sum v\<^sub>0) = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. ?f0 v\<^sub>0 / ?sum v\<^sub>0)"
    by auto
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. ?f0 v\<^sub>0 / (card {v. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> v\<^sub>0 v}))"
    apply (subst infsum_constant_finite_states)
    apply (subst finite_Collect_bex)
    apply (simp add: assms(1))
    apply (auto)
    apply (subgoal_tac "\<forall>xa. (put\<^bsub>x\<^esub> s\<^sub>1 y = put\<^bsub>x\<^esub> v\<^sub>0 xa) \<longrightarrow> y = xa")
    apply (smt (verit, ccfv_SIG) assms(1) mem_Collect_eq rev_finite_subset subset_iff)
    using weak_lens.view_determination vwb_lens_wb wb_lens_weak assms(2) by metis
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if (\<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = v\<^sub>0) \<and> (get\<^bsub>x\<^esub> v\<^sub>0 = v) then 
                ((1::\<real>) / (card {v. \<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = put\<^bsub>x\<^esub> v\<^sub>0 v}))
              else (0::\<real>)))"
    apply (rule infsum_cong)
    by simp
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if (\<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = v\<^sub>0) \<and> (get\<^bsub>x\<^esub> v\<^sub>0 = v) then 
                ((1::\<real>) / (card A)) else (0::\<real>)))"
    apply (rule infsum_cong)
    using one_dvd_card_A by presburger
  also have "... = ((1::\<real>) / (card A)) * (card {v\<^sub>0. (\<exists>xa::'b\<in>A. put\<^bsub>x\<^esub> s\<^sub>1 xa = v\<^sub>0) \<and> (get\<^bsub>x\<^esub> v\<^sub>0 = v)})"
    apply (rule infsum_constant_finite_states)
    using finite_states by blast
  also have "... = ((1::\<real>) / (card A))"
    using card_singleton by simp
  then show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. ?f1 v\<^sub>0 * ?f2 v\<^sub>0 / ?sum v\<^sub>0) = (1::\<real>) / real (card A)"
    using calculation by presburger
  qed

subsubsection \<open> Parallel Composition \<close>
text \<open> We should consider two cases: 
  @{text "\<exists>s'. p (s\<^sub>1, s') > 0 \<and> q (s\<^sub>1, s') > 0"}
or
  @{text "\<not>\<exists>s'. p (s\<^sub>1, s') > 0 \<and> q (s\<^sub>1, s') > 0"}
\<close>

text \<open> We use the comparison test (@{url "https://en.wikipedia.org/wiki/Direct_comparison_test"}, 
more tests here @{url "https://en.wikipedia.org/wiki/Convergence_tests"})  to 
prove the convergence of this product of two functions. \<close>
lemma prel_joint_prob_summable_on_product: 
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "(\<lambda>s'::'a. p (s\<^sub>1, s') * q (s\<^sub>1, s')) summable_on UNIV"
  apply (subst summable_on_iff_abs_summable_on_real)
  apply (rule abs_summable_on_comparison_test[where g = "\<lambda>s'::'a. p (s\<^sub>1, s')"])
  apply (metis assms(1) prel_prob_sum1_summable(3) summable_on_iff_abs_summable_on_real)
  by (simp add: assms(1) assms(2) mult_right_le_one_le prel_prob_sum1_summable(1))

lemma prel_is_dist_pparallel: 
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  assumes "\<forall>s\<^sub>1. \<exists>s'::'a. p (s\<^sub>1, s') > 0 \<and> q (s\<^sub>1, s') > 0"
  shows "is_final_distribution (pparallel_f p q)"
  apply (simp add: dist_defs expr_defs, auto)
  apply (simp add: assms(1) assms(2) infsum_nonneg prel_prob_sum1_summable(1))
  apply (simp_all add: lens_defs)
  apply (subgoal_tac "p (s\<^sub>1, s) * q (s\<^sub>1, s) \<le> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (s\<^sub>1, v\<^sub>0))")
  apply (smt (verit, del_insts) assms(1) assms(2) divide_le_eq_1 mult_nonneg_nonneg prel_prob_sum1_summable(1))
proof -
  fix s\<^sub>1 s
  show "p (s\<^sub>1, s) * q (s\<^sub>1, s) \<le> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. p (s\<^sub>1, v\<^sub>0) * q (s\<^sub>1, v\<^sub>0))"
    apply (rule infsum_geq_element)
    apply (simp add: assms(1) assms(2) prel_prob_sum1_summable(1))
    apply (simp add: assms(1) assms(2) prel_joint_prob_summable_on_product)
    by (simp)
next
  fix s\<^sub>1
  let ?P = "\<lambda>s'. p (s\<^sub>1, s') > 0 \<and> q (s\<^sub>1, s') > 0"
  (* obtain s where Ps: "s = (SOME s'. ?P s')" 
    using assms(3) by blast*)
  have f1: "?P (SOME s'. ?P s')"
    apply (rule someI_ex[where P="?P"])
    using assms(3) by blast
  have f2: "(\<lambda>s. p (s\<^sub>1, s) * q (s\<^sub>1, s)) (SOME s'. ?P s') \<le> (\<Sum>\<^sub>\<infinity>s'::'a. p (s\<^sub>1, s') * q (s\<^sub>1, s'))"
    apply (rule infsum_geq_element)
    apply (simp add: assms(1) assms(2) prel_prob_sum1_summable(1))
     apply (simp add: assms(1) assms(2) prel_joint_prob_summable_on_product)
    by (simp)
  also have f3: "... > 0"
    by (smt (verit, best) f1 f2 mult_le_0_iff)
  have f4: "(\<Sum>\<^sub>\<infinity>s::'a. (p (s\<^sub>1, s) * q (s\<^sub>1, s) / (\<Sum>\<^sub>\<infinity>s'::'a. p (s\<^sub>1, s') * q (s\<^sub>1, s')))) =
    (\<Sum>\<^sub>\<infinity>s::'a. (p (s\<^sub>1, s) * q (s\<^sub>1, s) * (1 / (\<Sum>\<^sub>\<infinity>s'::'a. p (s\<^sub>1, s') * q (s\<^sub>1, s')))))"
    by force
  also have f5: "... = (\<Sum>\<^sub>\<infinity>s::'a. (p (s\<^sub>1, s) * q (s\<^sub>1, s))) * (1 / (\<Sum>\<^sub>\<infinity>s'::'a. p (s\<^sub>1, s') * q (s\<^sub>1, s')))"
    apply (rule infsum_cmult_left)
    by (simp add: infsum_not_zero_summable)
  also have f6: "... = 1"
    using f3 by auto
  show "(\<Sum>\<^sub>\<infinity>s::'a. (p (s\<^sub>1, s) * q (s\<^sub>1, s) / (\<Sum>\<^sub>\<infinity>s'::'a. p (s\<^sub>1, s') * q (s\<^sub>1, s')))) = (1::\<real>)"
    using f4 f5 f6 by presburger
qed

subsection \<open> Conversion from a set of realed functions to @{text "prel"} and then back to the set \<close>
lemma prel_set_conv_skip: "rfrel_of_prel (prel_of_rfrel pskip\<^sub>_f) = pskip\<^sub>_f"
  by (simp add: prel_is_dist_skip prel_of_rfrel_inverse)

lemma prel_set_conv_assign: "rfrel_of_prel (prel_of_rfrel (passigns_f \<sigma>)) = passigns_f \<sigma>"
  apply (subst prel_of_rfrel_inverse)
  apply (simp add: prel_is_dist_assign)
  by (simp)

lemma prel_set_conv_pchoice: 
  assumes "\<forall>s. 0 \<le> r s \<and> r s \<le> 1"
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "rfrel_of_prel (prel_of_rfrel (pchoice_f p (r\<^sup>\<Up>) q)) = pchoice_f p (r\<^sup>\<Up>) q"
  apply (subst prel_of_rfrel_inverse)
  apply (simp)
  using assms prel_is_dist_pchoice apply blast
  by (simp)

lemma prel_set_conv_pchoice': 
  assumes "0 \<le> r \<and> r \<le> 1"
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "rfrel_of_prel (prel_of_rfrel (pchoice_f p (\<lambda>s. r) q)) = (pchoice_f p (\<lambda>s. r) q)"
  apply (subst prel_of_rfrel_inverse)
  apply (simp)
  using assms prel_is_dist_pchoice' apply blast
  by (simp)


(* A more general case where r is a function. 
lemma prel_set_pchoice: 
  assumes "\<forall>s. 0 \<le> r s \<and> r s \<le> 1"
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "rfrel_of_prel (prel_of_rfrel (r * (p) + (1 - r) * (q))\<^sub>e) = (r * (p) + (1 - r) * (q))\<^sub>e"
proof -
  have f1: "\<forall>s. 0 \<le> p s \<and> p s \<le> 1"
    using assms(2) by (simp add: dist_defs expr_defs)
  have f2: "\<forall>s. 0 \<le> q s \<and> q s \<le> 1"
    using assms(3) by (simp add: dist_defs expr_defs)
  have f3: "(\<Sum>\<^sub>\<infinity>s::'b. r (s\<^sub>1, s) * p (s\<^sub>1, s) + ((1::\<real>) - r (s\<^sub>1, s)) * q (s\<^sub>1, s)) = 
    (\<Sum>\<^sub>\<infinity>s::'b. r (s\<^sub>1, s) * p (s\<^sub>1, s)) + (\<Sum>\<^sub>\<infinity>s::'b. ((1::\<real>) - r (s\<^sub>1, s)) * q (s\<^sub>1, s))"
    apply (rule infsum_add)
  show ?thesis
    apply (subst prel_of_rfrel_inverse)
    apply (simp add: dist_defs expr_defs, auto)
    using assms(1) apply (simp add: f1 f2)
     apply (simp add: assms(1) convex_bound_le f1 f2)
*)

lemma prel_set_conv_pcond: 
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "rfrel_of_prel (prel_of_rfrel (pcond_f p (\<lambda>(s, s'). b s) q)) = (pcond_f p (\<lambda>(s, s'). b s) q)"
  apply (subst prel_of_rfrel_inverse)
  apply (simp)
  using assms(1) assms(2) prel_is_dist_pcond apply blast
  by simp

lemma prel_set_conv_seqcomp: 
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  shows "rfrel_of_prel (prel_of_rfrel (pcomp_f p q)) = pcomp_f p q"
  apply (subst prel_of_rfrel_inverse)
   apply (simp)
  using assms(1) assms(2) prel_is_dist_pcomp apply blast
  by simp

lemma prel_set_conv_parallel: 
  assumes "is_final_distribution p"
  assumes "is_final_distribution q"
  assumes "\<forall>s\<^sub>1. \<exists>s'::'a. p (s\<^sub>1, s') > 0 \<and> q (s\<^sub>1, s') > 0"
  shows "rfrel_of_prel (prel_of_rfrel (pparallel_f p q)) = pparallel_f p q"
  apply (subst prel_of_rfrel_inverse)
  apply (simp)
  using assms(1) assms(2) assms(3) prel_is_dist_pparallel apply blast
  by simp

lemma prel_set_conv_uniform_dist:
  assumes "finite (A::'b set)"
  assumes "vwb_lens x"
  assumes "A \<noteq> {}"
  shows "rfrel_of_prel (prel_of_rfrel (x \<^bold>\<U> A)) = (x \<^bold>\<U> A)"
  apply (subst prel_of_rfrel_inverse)
  apply (simp)
  using assms(1) assms(2) assms(3) prel_is_dist_uniform_dist apply blast
  by simp

subsection \<open> Laws of probabilistic relations \<close>
term "rfrel_of_prel P"
term "\<lambda>s. (rfrel_of_prel P) s"
term "(case \<s> of (\<sigma>::'a, \<rho>::'a) \<Rightarrow> Pair \<sigma>) (v\<^sub>0::'a)"
term "(x := ($x + 1))::'a phrel"

subsubsection \<open> Skip and assignment \<close>
theorem prel_skip: 
  assumes "wb_lens x"
  shows "(II::'a phrel) = (x := $x)"
  apply (simp add: prel_defs)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (rel_auto)
  by (simp add: assms)+

subsubsection \<open> Sequential composition \<close>
theorem prel_seqcomp_left_unit: "II ; P = P"
  apply (simp add: prel_defs expr_defs)
  apply (subst prel_of_rfrel_inverse)
  apply (simp add: dist_defs)
  apply (smt (verit, best) infsum_cong infsum_mult_singleton_left mult_cancel_right1)
  apply (simp add: lens_defs)
  apply (subgoal_tac "\<forall>s. (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a.
         (if (case s of (\<sigma>::'a, \<rho>::'a) \<Rightarrow> Pair \<sigma>) v\<^sub>0 \<in> II then 1::\<real> else (0::\<real>)) *
         rfrel_of_prel P ((case s of (\<sigma>::'a, \<rho>::'a) \<Rightarrow> \<lambda>u::'a. (u, \<rho>)) v\<^sub>0)) = (rfrel_of_prel P) s")
  apply (subgoal_tac "prel_of_rfrel (\<lambda>\<s>::'a \<times> 'a.
       \<Sum>\<^sub>\<infinity>v\<^sub>0::'a.
         (if (case \<s> of (\<sigma>::'a, \<rho>::'a) \<Rightarrow> Pair \<sigma>) v\<^sub>0 \<in> II then 1::\<real> else (0::\<real>)) *
         rfrel_of_prel P ((case \<s> of (\<sigma>::'a, \<rho>::'a) \<Rightarrow> \<lambda>u::'a. (u, \<rho>)) v\<^sub>0)) =
  prel_of_rfrel (rfrel_of_prel P)")
  using rfrel_of_prel_inverse apply auto[1]
  apply presburger
  apply (auto)
  by (simp add: infsum_mult_singleton_left_1)

theorem prel_seqcomp_right_unit: "P ; II = P"
  apply (simp add: prel_defs expr_defs)
  apply (subst prel_of_rfrel_inverse)
  apply (simp add: dist_defs)
  apply (smt (verit, best) infsum_cong infsum_mult_singleton_left mult_cancel_right1)
  apply (simp add: lens_defs)
  apply (subgoal_tac "\<forall>s. (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a.
           rfrel_of_prel P ((case s of (\<sigma>::'a, \<rho>::'a) \<Rightarrow> Pair \<sigma>) v\<^sub>0) *
           (if (case s of (\<sigma>::'a, \<rho>::'a) \<Rightarrow> \<lambda>u::'a. (u, \<rho>)) v\<^sub>0 \<in> II then 1::\<real> else (0::\<real>))) 
        = (rfrel_of_prel P) s")
  apply (subgoal_tac "(\<lambda>s::'a \<times> 'a.
         \<Sum>\<^sub>\<infinity>v\<^sub>0::'a.
           rfrel_of_prel P ((case s of (\<sigma>::'a, \<rho>::'a) \<Rightarrow> Pair \<sigma>) v\<^sub>0) *
           (if (case s of (\<sigma>::'a, \<rho>::'a) \<Rightarrow> \<lambda>u::'a. (u, \<rho>)) v\<^sub>0 \<in> II then 1::\<real> else (0::\<real>))) =
        (rfrel_of_prel P)")
  using rfrel_of_prel_inverse apply auto[1]
  apply presburger
  apply (auto)
  using infsum_mult_singleton_right by metis

term "(x := e) :: 's phrel"                                                                                                                                           
term "prel_of_rfrel (\<lbrakk> x\<^sup>> = e \<rbrakk>\<^sub>\<I>\<^sub>e)"
term "prel_of_rfrel (\<lbrakk> \<lbrakk>\<langle>[x \<leadsto> e]\<rangle>\<^sub>a\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"
term "prel_of_rfrel (\<lbrakk> \<lbrakk>((y := f)::'a rel)\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"
term "((x := e):: 's phrel) = prel_of_rfrel (\<lbrakk> \<lbrakk>x := e\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"
lemma passign_simp: "(x := e) = prel_of_rfrel (\<lbrakk> \<lbrakk>x := e\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"
  by (simp add: prel_defs expr_defs)

term "(x := e) \<Zcomp> (y := f)"  

lemma prel_assign_is_prob: "is_prob (\<lbrakk> \<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"
  by (simp add: prel_defs expr_defs dist_defs)

theorem passign_comp: 
  (* assumes "$x \<sharp> f" "x \<bowtie> y" *)
  shows "(x := e) ; (y := f) = prel_of_rfrel (\<lbrakk> \<lbrakk>(x := e) \<Zcomp> (y := f)\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"
  apply (simp add: prel_defs expr_defs)
  apply (subst prel_of_rfrel_inverse)
  apply (simp add: dist_defs)
  apply (rel_auto)
  apply (simp add: infsum_singleton)
  apply (subst prel_of_rfrel_inverse)
  apply (simp add: dist_defs)
  apply (rel_auto)
  apply (simp add: infsum_singleton)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (rel_auto)
  apply (subst infsum_mult_singleton_left_1)
  apply simp
  by (smt (verit, best) infsum_0 mult_cancel_left1 mult_cancel_right1)

lemma prel_prob_choice_is_sum_1:
  assumes "0 \<le> r \<and> r \<le> 1"
  shows "(\<Sum>\<^sub>\<infinity>s::'a. r * rfrel_of_prel P (s\<^sub>1, s) + ((1::\<real>) - r ) * rfrel_of_prel Q (s\<^sub>1, s)) = (1::\<real>)"
proof -
  have f1: "(\<Sum>\<^sub>\<infinity>s::'a. r  * rfrel_of_prel P (s\<^sub>1, s) + ((1::\<real>) - r ) * rfrel_of_prel Q (s\<^sub>1, s)) = 
    (\<Sum>\<^sub>\<infinity>s::'a. r * rfrel_of_prel P (s\<^sub>1, s)) + (\<Sum>\<^sub>\<infinity>s::'a. ((1::\<real>) - r ) * rfrel_of_prel Q (s\<^sub>1, s))"
      apply (rule infsum_add)
      using assms by (simp add: prel_summable summable_on_cmult_right)+
  also have f2: "... = r * (\<Sum>\<^sub>\<infinity>s::'a. rfrel_of_prel P (s\<^sub>1, s)) + 
          (1 - r) * (\<Sum>\<^sub>\<infinity>s::'a. rfrel_of_prel Q (s\<^sub>1, s))"
      apply (subst infsum_cmult_right)
      apply (simp add: prel_summable)
      apply (subst infsum_cmult_right)
      apply (simp add: prel_summable)
      by simp
  then show ?thesis
    by (simp add: f1 prel_sum_1)
qed

theorem prel_seqcomp_left_one_point: "x := e ; P = prel_of_rfrel (([ x\<^sup>< \<leadsto> e\<^sup>< ] \<dagger> @(rfrel_of_prel P)))\<^sub>e"
  apply (simp add: prel_defs expr_defs)
  apply (subst prel_of_rfrel_inverse)
  apply (simp add: dist_defs expr_defs)
  apply (rel_auto)
  apply (simp add: infsum_singleton)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (rel_auto)
  by (simp add: infsum_mult_singleton_left_1)

lemma prel_infsum_over_pair_subset_1:
  "(\<Sum>\<^sub>\<infinity> (s::'a, v\<^sub>0::'a). rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) = 1"
proof -
  have "(\<Sum>\<^sub>\<infinity> (s::'a, v\<^sub>0::'a). rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) = 
        (\<Sum>\<^sub>\<infinity> (s::'a, v\<^sub>0::'a) \<in> {(s::'a, v\<^sub>0::'a) | s v\<^sub>0. put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s}. rfrel_of_prel P (s\<^sub>1, v\<^sub>0))"
    apply (rule infsum_cong_neutral)
    apply force
    using DiffD2 prod.collapse apply fastforce
    by force
  then show ?thesis
    by (metis prel_infsum_over_pair_fst_discard prel_sum_1)
qed

lemma prel_infsum_swap:
 "(\<Sum>\<^sub>\<infinity>s::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) = 
  (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. \<Sum>\<^sub>\<infinity>s::'a. rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>)))"
  apply (rule infsum_swap_banach)
  apply (simp add: summable_on_def)
  apply (rule_tac x = "1" in exI)
  by (smt (verit, best) has_sum_infsum infsum_cong infsum_not_exists prel_infsum_over_pair_subset_1 split_cong)

lemma prel_infsum_infsum_subset_1:
  "(\<Sum>\<^sub>\<infinity>s::'a. \<Sum>\<^sub>\<infinity>v\<^sub>0::'a. rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) =
       (1::\<real>)"
  apply (simp add: prel_infsum_swap)
proof -
  have f0: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (\<Sum>\<^sub>\<infinity>s::'a. rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>)))) 
    = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * (\<Sum>\<^sub>\<infinity>s::'a. (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>)))))"
    apply (subst infsum_cmult_right)
    apply (simp add: infsum_singleton_summable)
    by (simp)
  then have f1: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * 1))"
    by (simp add: infsum_singleton)
  then show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. \<Sum>\<^sub>\<infinity>s::'a. rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) = (1::\<real>)"
    using f0 prel_sum_1 by force
qed 


term "prel_of_rfrel (\<lbrakk> ($x\<^sup>< = e) \<rbrakk>\<^sub>\<I>\<^sub>e)"

(* This realed function is not a distribution *)
(*
lemma "is_final_distribution (\<lbrakk> ($x\<^sup>< = e\<^sup><) \<rbrakk>\<^sub>\<I>\<^sub>e)"
  apply (expr_auto)
  apply (simp add: dist_defs)
  apply (auto)
*)

(*
theorem prel_right_one_point: "P ; prel_of_rfrel (\<lbrakk> ($x\<^sup>< = e\<^sup><) \<rbrakk>\<^sub>\<I>\<^sub>e) 
    = prel_of_rfrel (([ x\<^sup>> \<leadsto> e\<^sup>> ] \<dagger> @(rfrel_of_prel P)))\<^sub>e"
  apply (simp add: prel_defs expr_defs)
  apply (subst prel_of_rfrel_inverse)
   apply (simp add: dist_defs expr_defs)
   apply (auto)
  sorry
*)

(* This is not a valid law.
theorem prel_right_one_point: "P ; x := e = prel_of_rfrel (([ x\<^sup>> \<leadsto> e\<^sup>> ] \<dagger> @(rfrel_of_prel P)))\<^sub>e"
  apply (simp add: prel_defs expr_defs)
  apply (subst prel_of_rfrel_inverse)

  apply (simp add: dist_defs expr_defs)
  apply (rel_auto)
   apply (simp add: infsum_singleton)

  apply (subst prel_of_rfrel_inject)
  apply (simp add: dist_defs expr_defs)
  apply (rel_auto)
      apply (simp add: infsum_nonneg prel_in_0_1')
     apply (subgoal_tac "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. rfrel_of_prel P (s\<^sub>1, v\<^sub>0) * (if put\<^bsub>x\<^esub> v\<^sub>0 (e v\<^sub>0) = s then 1::\<real> else (0::\<real>))) 
      \<le> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. rfrel_of_prel P (s\<^sub>1, v\<^sub>0))")
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
    prel_of_rfrel (r * ([ x\<^sup>> \<leadsto> c\<^sup>> ] \<dagger> @(rfrel_of_prel P)) +  (1-r) * ([ x\<^sup>> \<leadsto> c\<^sup>> ] \<dagger> @(rfrel_of_prel Q)))\<^sub>e"
  apply (simp add: prel_defs expr_defs)
  apply (subst prel_of_rfrel_inverse)
   apply (simp add: dist_defs expr_defs)
  apply (rel_auto)
  apply (simp add: infsum_singleton)
  apply (subst prel_of_rfrel_inverse)
   apply (simp add: dist_defs expr_defs)
   apply (auto)
     apply (simp add: assms prel_in_0_1')
  apply (simp add: assms convex_bound_le prel_in_0_1')
  apply (subst prel_of_rfrel_inject)
    apply (simp add: dist_defs expr_defs)
    apply (auto)
     apply (simp add: assms infsum_nonneg rfrel_of_prel_in_0_1)
  apply (rel_auto)
  apply (subgoal_tac "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a.
          (if put\<^bsub>x\<^esub> a (c a) = v\<^sub>0 then 1::\<real> else (0::\<real>)) *
          (r (v\<^sub>0, b) * rfrel_of_prel P (v\<^sub>0, b) + ((1::\<real>) - r (v\<^sub>0, b)) * rfrel_of_prel Q (v\<^sub>0, b))) = 1")
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
          (r (v\<^sub>0, b) * rfrel_of_prel P (v\<^sub>0, b) + ((1::\<real>) - r (v\<^sub>0, b)) * rfrel_of_prel Q (v\<^sub>0, b))) 
      = 1")
    apply presburger
    apply (simp add: sum.remove)
    apply (subgoal_tac "(\<Sum>v\<^sub>0::'a\<in>Y - {put\<^bsub>x\<^esub> a (c a)}.
          (if put\<^bsub>x\<^esub> a (c a) = v\<^sub>0 then 1::\<real> else (0::\<real>)) *
          (r (v\<^sub>0, b) * rfrel_of_prel P (v\<^sub>0, b) + ((1::\<real>) - r (v\<^sub>0, b)) * rfrel_of_prel Q (v\<^sub>0, b))) = 0")
    apply (subgoal_tac "r (put\<^bsub>x\<^esub> a (c a), b) * rfrel_of_prel P (put\<^bsub>x\<^esub> a (c a), b) + 
      ((1::\<real>) - r (put\<^bsub>x\<^esub> a (c a), b)) * rfrel_of_prel Q (put\<^bsub>x\<^esub> a (c a), b) = 1") 
    defer
    apply (smt (verit) DiffE mult_eq_0_iff singleton_iff sum.not_neutral_contains_not_neutral)
*)
subsubsection \<open> Probabilistic choice \<close>

theorem prel_pchoice_commute: "if\<^sub>p r then P else Q = if\<^sub>p 1 - r then Q else P"
  apply (simp add: prel_defs)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  by (auto)

theorem prel_pchoice_zero: "if\<^sub>p 0 then P else Q = Q"
  apply (simp add: prel_defs)
  by (simp add: SEXP_def rfrel_of_prel_inverse)

theorem prel_pchoice_zero': 
  fixes w\<^sub>1 :: "'a \<Rightarrow> \<real>"
  assumes "`w\<^sub>1 = 0`"
  shows "P \<oplus>\<^bsub>w\<^sub>1\<^sup>\<Up>\<^esub> Q = Q"
  apply (simp add: prel_defs)
proof -
  have f0: "\<forall>s. w\<^sub>1 s = 0"
    by (metis (mono_tags, lifting) SEXP_def assms taut_def)
  show "prel_of_rfrel (pchoice_f (rfrel_of_prel P) (w\<^sub>1\<^sup>\<Up>) (rfrel_of_prel Q)) = Q"
    apply (simp add: f0 SEXP_def)
    by (simp add: rfrel_of_prel_inverse)
qed

theorem prel_pchoice_one: "if\<^sub>p 1 then P else Q = P"
  apply (simp add: prel_defs)
  by (simp add: SEXP_def rfrel_of_prel_inverse)

theorem prel_pchoice_assoc:
  fixes w\<^sub>1 :: "'a \<Rightarrow> \<real>"
  assumes "`0 \<le> w\<^sub>1 \<and> w\<^sub>1 \<le> 1`"
  assumes "`0 \<le> w\<^sub>2 \<and> w\<^sub>2 \<le> 1`"
  assumes "`0 \<le> r\<^sub>1 \<and> r\<^sub>1 \<le> 1`"
  assumes "`((1 - w\<^sub>1) * (1 - w\<^sub>2)) = (1 - r\<^sub>2)`"
  assumes "`(w\<^sub>1) = (r\<^sub>1 * r\<^sub>2)`"
  shows "P \<oplus>\<^bsub>w\<^sub>1\<^sup>\<Up>\<^esub> (Q \<oplus>\<^bsub>w\<^sub>2\<^sup>\<Up>\<^esub> R) = (P \<oplus>\<^bsub>r\<^sub>1\<^sup>\<Up>\<^esub> Q) \<oplus>\<^bsub>r\<^sub>2\<^sup>\<Up>\<^esub> R" (is "?lhs = ?rhs")
proof -
  have f0: "`((1 - w\<^sub>1) * (1 - w\<^sub>2)) = (1 - w\<^sub>1 - w\<^sub>2 + w\<^sub>1 * w\<^sub>2)`"
    apply (simp add: taut_def)
    by (smt (verit, del_insts) left_diff_distrib mult.commute mult_cancel_right1)
  then have f1: "`(1 - w\<^sub>1 - w\<^sub>2 + w\<^sub>1 * w\<^sub>2) = (1 - r\<^sub>2)`"
    by (smt (verit, ccfv_threshold) SEXP_def assms(4) taut_def)
  then have f2: "`(r\<^sub>2) = (w\<^sub>1 + w\<^sub>2 - w\<^sub>1 * w\<^sub>2)`"
    by (smt (verit, del_insts) SEXP_apply taut_def)
  then have f3: "`0 \<le> r\<^sub>2 \<and> r\<^sub>2 \<le> 1`"
    using assms(1-2) by (smt (verit) SEXP_def f0 mult_le_one mult_nonneg_nonneg taut_def)
  have f4: "`(w\<^sub>1) = (r\<^sub>1 * (w\<^sub>1 + w\<^sub>2 - w\<^sub>1 * w\<^sub>2))`"
    using assms(5) f2 by (simp add: taut_def)
  have f5: "\<forall>s. ((1::\<real>) - (w\<^sub>1\<^sup>\<Up>) s) * ((1::\<real>) - (w\<^sub>2\<^sup>\<Up>) s) = (1 - (r\<^sub>2\<^sup>\<Up>) s)"
    using assms(4) by (simp add: taut_def)
  have f6: "pchoice_f (rfrel_of_prel P) (w\<^sub>1\<^sup>\<Up>)
    (\<lambda>\<s>::'a \<times> 'b. (w\<^sub>2\<^sup>\<Up>) \<s> * rfrel_of_prel Q \<s> + ((1::\<real>) - (w\<^sub>2\<^sup>\<Up>) \<s>) * rfrel_of_prel R \<s>) = 
    (\<lambda>s::'a \<times> 'b. (w\<^sub>1\<^sup>\<Up>) s * rfrel_of_prel P s + 
        ((1::\<real>) - (w\<^sub>1\<^sup>\<Up>) s) * ((w\<^sub>2\<^sup>\<Up>) s * rfrel_of_prel Q s + ((1::\<real>) - (w\<^sub>2\<^sup>\<Up>) s) * rfrel_of_prel R s))"
    using SEXP_def by blast
  then have f7: "... = (\<lambda>s::'a \<times> 'b. (w\<^sub>1\<^sup>\<Up>) s * rfrel_of_prel P s + 
        ((1::\<real>) - (w\<^sub>1\<^sup>\<Up>) s) * (w\<^sub>2\<^sup>\<Up>) s * rfrel_of_prel Q s + ((1::\<real>) - (w\<^sub>1\<^sup>\<Up>) s) * ((1::\<real>) - (w\<^sub>2\<^sup>\<Up>) s) * rfrel_of_prel R s)" 
    apply (simp add: distrib_left)
    by (simp add: add.assoc mult.commute mult.left_commute)
  then have f8: "... = (\<lambda>s::'a \<times> 'b. (w\<^sub>1\<^sup>\<Up>) s * rfrel_of_prel P s + 
        ((1::\<real>) - (w\<^sub>1\<^sup>\<Up>) s) * (w\<^sub>2\<^sup>\<Up>) s * rfrel_of_prel Q s + (1 - (r\<^sub>2\<^sup>\<Up>) s) * rfrel_of_prel R s)"
    using f5 by fastforce
  have f5': "\<forall>s. (r\<^sub>2\<^sup>\<Up>) s * (r\<^sub>1\<^sup>\<Up>) s = (w\<^sub>1\<^sup>\<Up>) s"
    using assms(5) by (simp add: taut_def)
  have f5'': "\<forall>s. (r\<^sub>2\<^sup>\<Up>) s * ((1::\<real>) - (r\<^sub>1\<^sup>\<Up>) s) = ((1::\<real>) - (w\<^sub>1\<^sup>\<Up>) s) * (w\<^sub>2\<^sup>\<Up>) s"
    by (smt (verit, best) f5 f5' mult_cancel_left1 right_diff_distrib')
  have f9: "pchoice_f (\<lambda>s::'a \<times> 'b. (r\<^sub>1\<^sup>\<Up>) s * rfrel_of_prel P s + ((1::\<real>) - (r\<^sub>1\<^sup>\<Up>) s) * rfrel_of_prel Q s) (r\<^sub>2\<^sup>\<Up>) (rfrel_of_prel R) 
    =  (\<lambda>s::'a \<times> 'b. (r\<^sub>2\<^sup>\<Up>) s * ((r\<^sub>1\<^sup>\<Up>) s * rfrel_of_prel P s + ((1::\<real>) - (r\<^sub>1\<^sup>\<Up>) s) * rfrel_of_prel Q s) + 
      ((1::\<real>) - (r\<^sub>2\<^sup>\<Up>) s) * rfrel_of_prel R s)"
    using SEXP_def by blast
  then have f10: "... = (\<lambda>s::'a \<times> 'b. (r\<^sub>2\<^sup>\<Up>) s * (r\<^sub>1\<^sup>\<Up>) s * rfrel_of_prel P s + (r\<^sub>2\<^sup>\<Up>) s * ((1::\<real>) - (r\<^sub>1\<^sup>\<Up>) s) * rfrel_of_prel Q s + 
      ((1::\<real>) - (r\<^sub>2\<^sup>\<Up>) s) * rfrel_of_prel R s)"
    apply (simp add: distrib_left)
    by (simp add: add.assoc mult.commute mult.left_commute)
  then have f11: "... = (\<lambda>s::'a \<times> 'b. (w\<^sub>1\<^sup>\<Up>) s * rfrel_of_prel P s + 
        ((1::\<real>) - (w\<^sub>1\<^sup>\<Up>) s) * (w\<^sub>2\<^sup>\<Up>) s * rfrel_of_prel Q s + (1 - (r\<^sub>2\<^sup>\<Up>) s) * rfrel_of_prel R s)"
    using f5' f5'' by fastforce
  show ?thesis
    apply (simp add: prel_defs)
    apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
    apply (subst prel_set_conv_pchoice)
    using assms(2) apply (simp add: taut_def)
      apply (simp add: prel_is_dist)+
    apply (subst prel_set_conv_pchoice)
    using assms(3) apply (simp add: taut_def)
    apply (simp add: prel_is_dist)+
    by (simp add: f10 f5 f5' f5'' f7)
qed

(*
lemma prel_pchoice_assoc:
  fixes w\<^sub>1 :: "'a \<Rightarrow> \<real>"
  assumes "`0 \<le> w\<^sub>1 \<and> w\<^sub>1 \<le> 1`"
  assumes "`0 \<le> w\<^sub>2 \<and> w\<^sub>2 \<le> 1`"
  assumes "`((1 - w\<^sub>1) * (1 - w\<^sub>2)) = (1 - r\<^sub>2)`" 
  assumes "`(w\<^sub>1) = (r\<^sub>1 * r\<^sub>2)`"
  shows "P \<oplus>\<^bsub>w\<^sub>1\<^sup>\<Up>\<^esub> (Q \<oplus>\<^bsub>w\<^sub>2\<^sup>\<Up>\<^esub> R) = (P \<oplus>\<^bsub>r\<^sub>1\<^sup>\<Up>\<^esub> Q) \<oplus>\<^bsub>r\<^sub>2\<^sup>\<Up>\<^esub> R" (is "?lhs = ?rhs")
proof (cases "`w\<^sub>1 = 0 \<and> w\<^sub>2 = 0`")
  case True
  then have f0: "`r\<^sub>2 = 0`"
    using assms(3-4) by (simp add: taut_def)
  have f1: "`w\<^sub>1 = 0`"
    using True by (simp add: taut_def)
  have f2: "`w\<^sub>2 = 0`"
    using True by (simp add: taut_def)
  have f3: "?lhs = R"
    apply (subst prel_pchoice_zero')
    using f1 apply auto
    apply (subst prel_pchoice_zero')
    using f2 by auto
  have f4: "?rhs = R"
    apply (rule prel_pchoice_zero')
    using f0 by auto
  show ?thesis 
    using f3 f4 by auto
next
  case False
  then have f: "\<forall>s. w\<^sub>1 s \<noteq> 0 \<or> w\<^sub>2 s \<noteq> 0"
    sledgehammer
  have f0: "`((1 - w\<^sub>1) * (1 - w\<^sub>2)) = (1 - w\<^sub>1 - w\<^sub>2 + w\<^sub>1 * w\<^sub>2)`"
    apply (simp add: taut_def)
    by (smt (verit, del_insts) left_diff_distrib mult.commute mult_cancel_right1)
  then have f1: "`(1 - w\<^sub>1 - w\<^sub>2 + w\<^sub>1 * w\<^sub>2) = (1 - r\<^sub>2)`"
    by (smt (verit, ccfv_threshold) SEXP_def assms(3) taut_def)
  then have f2: "`(r\<^sub>2) = (w\<^sub>1 + w\<^sub>2 - w\<^sub>1 * w\<^sub>2)`"
    by (smt (verit, del_insts) SEXP_apply taut_def)
  then have f3: "`0 \<le> r\<^sub>2 \<and> r\<^sub>2 \<le> 1`"
    using assms(1-2) by (smt (verit) SEXP_def f0 mult_le_one mult_nonneg_nonneg taut_def)
  have "`(w\<^sub>1) = (r\<^sub>1 * (w\<^sub>1 + w\<^sub>2 - w\<^sub>1 * w\<^sub>2))`"
    using assms(4) f2 by (simp add: taut_def)
  then have f4: "`0 \<le> r\<^sub>1 \<and> r\<^sub>1 \<le> 1`"
    sorry
  show ?thesis
    apply (simp add: prel_defs)
    apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
    apply (subst prel_set_conv_pchoice)
    using assms(2) apply (metis (mono_tags, lifting) taut_def SEXP_def)
    apply (simp add: prel_is_dist)+
    apply (subst prel_set_conv_pchoice)
    apply (simp add: assms(2))
       apply (simp add: prel_is_dist)+
  qed
*)
(*
lemma prel_pchoice_assoc:
  assumes "((1 - w\<^sub>1) * (1 - w\<^sub>2))\<^sub>e = (1 - r\<^sub>2)\<^sub>e" "(w\<^sub>1)\<^sub>e = (r\<^sub>1 * r\<^sub>2)\<^sub>e"
  shows "if\<^sub>p w\<^sub>1 then P else (if\<^sub>p w\<^sub>2 then Q else R) = if\<^sub>p r\<^sub>2 then (if\<^sub>p r\<^sub>1 then P else Q) else R"
  apply (simp add: prel_defs)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (subst prel_of_rfrel_inverse)
  apply (simp)
  using assms prel_is_dist_pchoice sledgehammer
  apply (subst prel_set_conv_pchoice)
  by (auto)
*)

subsubsection \<open> Normalisation \<close>
theorem uniform_dist_altdef:
  assumes "finite (A::'b set)"
  assumes "vwb_lens x"
  assumes "A \<noteq> {}"
  shows "(x \<^bold>\<U> A) = (\<lbrakk>\<lbrakk>\<Union> v \<in> A. x := \<guillemotleft>v\<guillemotright>\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e / card \<guillemotleft>A\<guillemotright>)\<^sub>e"
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (rel_auto)
  apply (subst infsum_constant_finite_states)
  apply (smt (verit, best) Collect_mem_eq Collect_mono_iff assms(1) assms(2) mem_Collect_eq 
      mwb_lens_weak rev_finite_subset vwb_lens.axioms(2) weak_lens.put_get)
proof -
  fix a::"'a" and xa::"'b"
  assume a1: "xa \<in> A"
  have "{s::'b. \<exists>xb::'b\<in>A. put\<^bsub>x\<^esub> a xb = put\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> a xa) s} = 
        {s::'b. \<exists>xb::'b\<in>A. put\<^bsub>x\<^esub> a xb = put\<^bsub>x\<^esub> a s}"
    using assms(2) by auto
  also have "... = {s::'b. \<exists>xb::'b\<in>A. xb = s}"
    by (metis assms(2) vwb_lens_wb wb_lens_weak weak_lens.view_determination)
  then show "(1::\<real>) * real (card {s::'b. \<exists>xb::'b\<in>A. put\<^bsub>x\<^esub> a xb = put\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> a xa) s}) = real (card A)"
    by (simp add: calculation)
qed

theorem uniform_dist_altdef':
  assumes "finite (A::'b set)"
  assumes "vwb_lens x"
  assumes "A \<noteq> {}"
  shows "rfrel_of_prel (prel_of_rfrel (x \<^bold>\<U> A)) = (\<lbrakk>\<lbrakk>\<Union> v \<in> A. x := \<guillemotleft>v\<guillemotright>\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e / card \<guillemotleft>A\<guillemotright>)\<^sub>e"
  by (metis assms(1) assms(2) assms(3) prel_set_conv_uniform_dist uniform_dist_altdef)

theorem prel_uniform_dist_left:
  assumes "finite (A::'a set)"
  assumes "vwb_lens x"
  assumes "A \<noteq> {}"
  shows "(prel_of_rfrel (x \<^bold>\<U> A)) ; P = 
    prel_of_rfrel ((\<Sum>v \<in> \<guillemotleft>A\<guillemotright>. (([ x\<^sup>< \<leadsto> \<guillemotleft>v\<guillemotright> ] \<dagger> @(rfrel_of_prel P)))) / card (\<guillemotleft>A\<guillemotright>))\<^sub>e"
  apply (simp add: prel_defs)
  apply (subst uniform_dist_altdef')
  apply (simp_all add: assms)
  apply (expr_auto)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (rel_auto)
proof -
  fix a and b :: "'b"
  let ?fl_1 = "\<lambda>v\<^sub>0. (if \<exists>xa::'a\<in>A. put\<^bsub>x\<^esub> a xa = v\<^sub>0 then 1::\<real> else (0::\<real>))"
  let ?fl_2 = "\<lambda>v\<^sub>0. rfrel_of_prel P (v\<^sub>0, b) / real (card A)"

  have "finite {put\<^bsub>x\<^esub> a xa | xa. xa \<in> A}"
    apply (rule finite_image_set)
    using assms(1) by auto
  then have finite_states: "finite {v\<^sub>0. \<exists>xa::'a\<in>A. put\<^bsub>x\<^esub> a xa = v\<^sub>0}"
    by (smt (verit, del_insts) Collect_cong)

  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?fl_1 v\<^sub>0 * rfrel_of_prel P (v\<^sub>0, b) / real (card A))
    = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?fl_1 v\<^sub>0 * ?fl_2 v\<^sub>0)"
    by auto
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'b \<in> {v\<^sub>0. \<exists>xa::'a\<in>A. put\<^bsub>x\<^esub> a xa = v\<^sub>0}. ?fl_2 v\<^sub>0)"
    apply (subst infsum_mult_subset_left)
    by simp
  also have "... = (\<Sum> v\<^sub>0::'b \<in> {v\<^sub>0. \<exists>xa::'a\<in>A. put\<^bsub>x\<^esub> a xa = v\<^sub>0}. ?fl_2 v\<^sub>0)"
    apply (rule infsum_finite)
    by (simp add: finite_states)
  also have fl: "... = (\<Sum> v\<^sub>0::'b \<in> {v\<^sub>0. \<exists>xa::'a\<in>A. put\<^bsub>x\<^esub> a xa = v\<^sub>0}. rfrel_of_prel P (v\<^sub>0, b)) / real (card A)"
    by (metis (mono_tags, lifting) sum.cong sum_divide_distrib)

  have inj_on_A: "inj_on (\<lambda>xa. put\<^bsub>x\<^esub> a xa) A"
    by (meson assms(2) inj_onI vwb_lens_wb wb_lens_def weak_lens.view_determination)

  have frl: "(\<Sum> v\<^sub>0::'b \<in> {v\<^sub>0. \<exists>xa::'a\<in>A. put\<^bsub>x\<^esub> a xa = v\<^sub>0}. rfrel_of_prel P (v\<^sub>0, b)) 
    = (\<Sum>v::'a\<in>A. rfrel_of_prel P (put\<^bsub>x\<^esub> a v, b))"
    apply (rule sum.reindex_cong[where l = "(\<lambda>xa. put\<^bsub>x\<^esub> a xa)"])
    apply (simp add: inj_on_A)
     apply blast
    by simp

  show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'b. ?fl_1 v\<^sub>0 * rfrel_of_prel P (v\<^sub>0, b) / real (card A)) = 
        (\<Sum>v::'a\<in>A. rfrel_of_prel P (put\<^bsub>x\<^esub> a v, b)) / real (card A)"
    using calculation fl frl by presburger
qed

subsubsection \<open> Parallel composition \<close>

theorem prel_parallel_assoc:
  "(P \<parallel> Q) \<parallel> R = P \<parallel> (Q \<parallel> R)"
  apply (simp add: prel_defs)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  oops

theorem prel_parallel_commute:
  fixes P::"'a phrel"
  shows "P \<parallel> Q = Q \<parallel> P"
  apply (simp add: prel_defs)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  by (simp add: mult.commute)

subsection \<open> Substitutions \<close>

term "[ x \<leadsto> f ]"
term "(if\<^sub>p b then c else d)"
(*
lemma "prel_of_rfrel ([ x\<^sup>> \<leadsto> e\<^sup>> ] \<dagger> (rfrel_of_prel II\<^sub>p)) = (x := e)"
  apply (simp add: expr_defs prel_defs)
  apply (subst prel_of_rfrel_inverse)
   apply (simp add: dist_defs)
   apply (simp add: infsum_singleton)
  apply (subst prel_of_rfrel_inject)
    apply (simp add: dist_defs)
    apply (auto)

lemma "prel_of_rfrel (\<sigma> \<dagger> (rfrel_of_prel II\<^sub>p)) = (x := e)"
  apply (simp add: expr_defs prel_defs)
  apply (subst prel_of_rfrel_inverse)
   apply (simp add: dist_defs)
   apply (simp add: infsum_singleton)
  apply (subst prel_of_rfrel_inject)
    apply (simp add: dist_defs)
  apply (auto)
*)

end
