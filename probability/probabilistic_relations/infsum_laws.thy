section \<open> Laws related to @{text "infsum"} \<close>

theory infsum_laws
  imports 
    "HOL-Analysis.Infinite_Sum"
    "UTP2.utp" (* This is not necessary for this theory. The only reason for importing it here is
      because there is a syntax error without unbundle UTP_Syntax. For example, (0::\<nat>) cannot be
      correctly parsed. Please comment this line to see effect. This should be fixed. *)
    (* "utp_distribution" *)
begin 
unbundle UTP_Syntax
(*
print_bundles
declare [[show_types]]
*)
subsection \<open> Useful lemmas \<close>
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

lemma conditional_conds_conj: 
  "\<forall>s. (if b\<^sub>1 s then (1::\<real>) else (0::\<real>)) * (if b\<^sub>2 s then (1::\<real>) else (0::\<real>)) = 
    (if b\<^sub>1 s \<and> b\<^sub>2 s then 1 else 0)"
  apply (rule allI)
  by force

lemma conditional_conds_conj': 
  "\<forall>s. (if b\<^sub>1 s then (m::\<real>) else (0::\<real>)) * (if b\<^sub>2 s then (p::\<real>) else (0::\<real>)) = 
    (if b\<^sub>1 s \<and> b\<^sub>2 s then m * p else 0)"
  apply (rule allI)
  by simp

lemma conditional_cmult: "\<forall>s. (if b\<^sub>1 s then (m::\<real>) else (0::\<real>)) * c = 
    ((if b\<^sub>1 s then (m::\<real>) * c else (0::\<real>)))"
  apply (rule allI)
  by force

lemma conditional_cmult_1: "\<forall>s. (if b\<^sub>1 s then (1::\<real>) else (0::\<real>)) * c = 
    ((if b\<^sub>1 s then c else (0::\<real>)))"
  apply (rule allI)
  by force

subsection \<open> Laws of @{term infsum} \<close>
lemma infset_0_not_summable_or_sum_to_zero:
  assumes "infsum f A = 0"
  shows "(f summable_on A \<and> has_sum f A 0) \<or> \<not> f summable_on A"
  by (simp add: assms summable_iff_has_sum_infsum)

lemma infset_0_not_summable_or_zero:
  assumes "\<forall>s. f s \<ge> (0::\<real>)"
  assumes "infsum f A = 0"
  shows "(\<forall>s \<in> A. f s = 0) \<or> \<not> f summable_on A"
proof (rule ccontr)
  assume a1: "\<not> ((\<forall>s\<in>A. f s = (0)) \<or> \<not> f summable_on A)"
  then have f1: "(\<not> (\<forall>s\<in>A. f s = (0))) \<and> f summable_on A"
    by linarith
  then have "\<exists>x \<in> A. f x > 0"
    apply (simp add: Bex_def)
    apply (auto)
    apply (rule_tac x = "x" in exI)
    apply (simp)
    using assms(1) by (metis order_le_less)

  have ind_ge_0: "infsum f {(SOME x. x \<in>A \<and> f x > 0)} > 0"
    using a1 assms(1) assms(2) nonneg_infsum_le_0D by force

  have "infsum f {(SOME x. x \<in>A \<and> f x > 0)} \<le> infsum f A"
    apply (rule infsum_mono2)
    apply simp
    using f1 apply blast
    using a1 assms(1) assms(2) nonneg_infsum_le_0D apply force
    using assms(1) by blast
  then have "infsum f A > 0"
    using ind_ge_0 by linarith
  then show "False"
    using assms(2) by simp
qed

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

lemma summable_on_cdiv_left':
  fixes f :: "'a \<Rightarrow> \<real>"
  assumes \<open>c \<noteq> 0\<close>
  shows "(\<lambda>x. f x / c) summable_on A \<longleftrightarrow> f summable_on A"
  apply (simp only : divide_inverse)
  by (simp add: assms summable_on_cmult_left')

lemma not_summable_on_cdiv_left':
  fixes f :: "'a \<Rightarrow> \<real>"
  assumes \<open>c \<noteq> 0\<close>
  shows "\<not>(\<lambda>x. f x / c) summable_on A \<longleftrightarrow> \<not>f summable_on A"
  apply (simp only : divide_inverse)
  by (simp add: assms summable_on_cmult_left')

lemma summable_on_minus: 
  fixes f g :: "'a \<Rightarrow> \<real>"
  assumes \<open>f summable_on A\<close>
  assumes \<open>g summable_on A\<close>
  shows \<open>(\<lambda>x. f x - g x) summable_on A\<close>
  apply (subst add_uminus_conv_diff[symmetric])
  apply (subst summable_on_add)
  using assms(1) apply blast
  by (simp add: assms(2) summable_on_uminus)+

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

lemma infsum_geq_element':
  fixes f :: "'a \<Rightarrow> \<real>"
  assumes "\<forall>s. f s \<ge> 0"
  assumes "f summable_on A"
  assumes "s \<in> A"
  assumes "infsum f A = x"
  shows "f s \<le> x"
  by (metis assms(1) assms(2) assms(3) assms(4) infsum_geq_element)

lemma infsum_on_singleton:
  "(\<Sum>\<^sub>\<infinity>s \<in> {x}. f s) = f x"
  apply (rule infsumI)
  apply (simp add: has_sum_def)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
  apply (rule_tac x = "{x}" in exI)
  by (metis add.right_neutral finite.emptyI finite_insert insert_absorb insert_not_empty 
      subset_antisym subset_singleton_iff sum.empty sum.insert)
  
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

lemma infsum_cond_finite_states:
  assumes "finite {s. b s}"
  shows "(\<Sum>\<^sub>\<infinity>v\<^sub>0. (if b v\<^sub>0 then f v\<^sub>0 else (0::\<real>))) = (\<Sum>v\<^sub>0 \<in> {s. b s}. f v\<^sub>0)"
proof -
  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0. (if b v\<^sub>0 then f v\<^sub>0 else 0)) = (\<Sum>\<^sub>\<infinity>v\<^sub>0 \<in> {s. b s} \<union> (-{s. b s}). (if b v\<^sub>0 then f v\<^sub>0 else 0))"
    by auto
  moreover have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0 \<in> {s. b s}. (if b v\<^sub>0 then f v\<^sub>0 else 0))"
    apply (subst infsum_Un_disjoint)
    apply (simp add: assms)
    apply (smt (verit, ccfv_threshold) ComplD mem_Collect_eq summable_on_0)
    apply simp
    by (smt (verit, best) ComplD infsum_0 mem_Collect_eq)
  moreover have "... = (\<Sum>v\<^sub>0 \<in> {s. b s}. f v\<^sub>0)"
    using assms by force
  ultimately show ?thesis
    by presburger
qed

lemma infsum_cond_finite_states_summable:
  assumes "finite {s. b s}"
  shows "(\<lambda>v\<^sub>0. (if b v\<^sub>0 then f v\<^sub>0 else (0::\<real>))) summable_on UNIV"
proof -
  have "((\<lambda>v\<^sub>0. (if b v\<^sub>0 then f v\<^sub>0 else (0::\<real>))) summable_on UNIV) = 
      ((\<lambda>v\<^sub>0. (if b v\<^sub>0 then f v\<^sub>0 else (0::\<real>))) summable_on ({s. b s} \<union> -{s. b s}))"
    by auto
  moreover have "..."
    apply (rule summable_on_Un_disjoint)
    apply (simp add: assms)
    apply (smt (verit, ccfv_threshold) ComplD mem_Collect_eq summable_on_0)
    by simp
  ultimately show ?thesis
    by presburger
qed

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

lemma infsum_constant_finite_states_subset:
  assumes "finite {s. b s \<and> s \<in> A}"
  shows "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a \<in> A. (if b v\<^sub>0 then (m::\<real>) else 0)) = m * card ({s. b s \<and> s \<in> A})"
proof -
  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a \<in> A. (if b v\<^sub>0 then (m::\<real>) else 0)) = (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a \<in> {s. b s \<and> s \<in> A}. (m::\<real>))"
    apply (rule infsum_cong_neutral)
    apply simp
    apply auto[1]
    by simp
  then show ?thesis
    by simp
qed

lemma infsum_constant_finite_states_subset':
  assumes "finite {s. b s}"
  shows "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a \<in> A. (if b v\<^sub>0 then (m::\<real>) else 0)) = m * card ({s. b s \<and> s \<in> A})"
  apply (rule infsum_constant_finite_states_subset)
  using assms by force

lemma infsum_constant_finite_states_summable_2:
  assumes "finite {s. b\<^sub>1 s}" "finite {s. b\<^sub>2 s}"
  shows "(\<lambda>v\<^sub>0::'a. (if b\<^sub>1 v\<^sub>0 then (m::\<real>) else 0) + 
          (if b\<^sub>2 v\<^sub>0 then (n::\<real>) else 0)) summable_on UNIV"
  apply (subst summable_on_add)
  apply (simp add: assms(1) infsum_constant_finite_states_summable)
  by (simp add: assms(2) infsum_constant_finite_states_summable)+

lemma infsum_constant_finite_states_summable_3:
  assumes "finite {s. b\<^sub>1 s}" "finite {s. b\<^sub>2 s}" "finite {s. b\<^sub>3 s}"
  shows "(\<lambda>v\<^sub>0::'a. (if b\<^sub>1 v\<^sub>0 then (m::\<real>) else 0) + 
          (if b\<^sub>2 v\<^sub>0 then (n::\<real>) else 0) +
          (if b\<^sub>3 v\<^sub>0 then (p::\<real>) else 0)) summable_on UNIV"
  apply (subst summable_on_add)+
  apply (simp add: assms(1) infsum_constant_finite_states_summable)
  apply (simp add: assms(2) infsum_constant_finite_states_summable)+
  by (simp add: assms(3) infsum_constant_finite_states_summable)+

lemma infsum_constant_finite_states_summable_cmult_1:
  assumes "finite {s. b\<^sub>1 s}"
  shows "(\<lambda>v\<^sub>0::'a. (if b\<^sub>1 v\<^sub>0 then (m::\<real>) else 0) * c\<^sub>1) summable_on UNIV"
  apply (rule summable_on_cmult_left)
  by (simp add: assms(1) infsum_constant_finite_states_summable)

lemma infsum_constant_finite_states_cmult_1:
  assumes "finite {s. b\<^sub>1 s}"
  shows "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. (if b\<^sub>1 v\<^sub>0 then (m::\<real>) else 0) * c\<^sub>1) = m * card {s. b\<^sub>1 s} * c\<^sub>1"
  apply (subst infsum_cmult_left)
  using assms infsum_constant_finite_states_summable apply blast
  apply (subst infsum_constant_finite_states)
  using assms apply blast
  by auto

lemma infsum_constant_finite_states_summable_cmult_2:
  assumes "finite {s. b\<^sub>1 s}" "finite {s. b\<^sub>2 s}"
  shows "(\<lambda>v\<^sub>0::'a. (if b\<^sub>1 v\<^sub>0 then (m::\<real>) else 0) * c\<^sub>1 + 
          (if b\<^sub>2 v\<^sub>0 then (n::\<real>) else 0) * c\<^sub>2
    ) summable_on UNIV"
  apply (subst summable_on_add)
  apply (rule summable_on_cmult_left)
  apply (simp add: assms(1) infsum_constant_finite_states_summable)
  apply (rule summable_on_cmult_left)
  by (simp add: assms(2) infsum_constant_finite_states_summable)+

lemma infsum_constant_finite_states_cmult_2:
  assumes "finite {s. b\<^sub>1 s}" "finite {s. b\<^sub>2 s}"
  shows "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. 
          (if b\<^sub>1 v\<^sub>0 then (m::\<real>) else 0) * c\<^sub>1 + 
          (if b\<^sub>2 v\<^sub>0 then (n::\<real>) else 0) * c\<^sub>2) 
    = m * card {s. b\<^sub>1 s} * c\<^sub>1 + n * card {s. b\<^sub>2 s} * c\<^sub>2"
  apply (subst infsum_add)
  using assms(1) infsum_constant_finite_states_summable_cmult_1 apply blast
  using assms(2) infsum_constant_finite_states_summable_cmult_1 apply blast
  apply (subst infsum_constant_finite_states_cmult_1)
  using assms(1) apply blast
  apply (subst infsum_constant_finite_states_cmult_1)
  using assms(2) apply blast
  by blast

lemma infsum_constant_finite_states_summable_cmult_3:
  assumes "finite {s. b\<^sub>1 s}" "finite {s. b\<^sub>2 s}" "finite {s. b\<^sub>3 s}"
  shows "(\<lambda>v\<^sub>0::'a. (if b\<^sub>1 v\<^sub>0 then (m::\<real>) else 0) * c\<^sub>1 + 
          (if b\<^sub>2 v\<^sub>0 then (n::\<real>) else 0) * c\<^sub>2 + 
          (if b\<^sub>3 v\<^sub>0 then (p::\<real>) else 0) * c\<^sub>3
    ) summable_on UNIV"
  apply (subst summable_on_add)+
  apply (rule summable_on_cmult_left)
  apply (simp add: assms(1) infsum_constant_finite_states_summable)
  apply (rule summable_on_cmult_left)
  apply (simp add: assms(2) infsum_constant_finite_states_summable)+
  apply (rule summable_on_cmult_left)
  by (simp add: assms(3) infsum_constant_finite_states_summable)+

lemma infsum_constant_finite_states_cmult_3:
  assumes "finite {s. b\<^sub>1 s}" "finite {s. b\<^sub>2 s}" "finite {s. b\<^sub>3 s}"
  shows "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. 
          (if b\<^sub>1 v\<^sub>0 then (m::\<real>) else 0) * c\<^sub>1 + 
          (if b\<^sub>2 v\<^sub>0 then (n::\<real>) else 0) * c\<^sub>2 + 
          (if b\<^sub>3 v\<^sub>0 then (p::\<real>) else 0) * c\<^sub>3) 
    = m * card {s. b\<^sub>1 s} * c\<^sub>1 + n * card {s. b\<^sub>2 s} * c\<^sub>2 + p * card {s. b\<^sub>3 s} * c\<^sub>3"
  apply (subst infsum_add)
  using assms(1) assms(2) apply (rule infsum_constant_finite_states_summable_cmult_2)
  using assms(3) apply (rule infsum_constant_finite_states_summable_cmult_1)
  apply (subst infsum_constant_finite_states_cmult_1)
  using assms(3) apply blast
  apply (subst infsum_constant_finite_states_cmult_2)
  using assms(1) assms(2) by blast+

lemma infsum_constant_finite_states_summable_cmult_4:
  assumes "finite {s. b\<^sub>1 s}" "finite {s. b\<^sub>2 s}" "finite {s. b\<^sub>3 s}" "finite {s. b\<^sub>4 s}"
  shows "(\<lambda>v\<^sub>0::'a. (if b\<^sub>1 v\<^sub>0 then (m::\<real>) else 0) * c\<^sub>1 + 
          (if b\<^sub>2 v\<^sub>0 then (n::\<real>) else 0) * c\<^sub>2 + 
          (if b\<^sub>3 v\<^sub>0 then (p::\<real>) else 0) * c\<^sub>3 + 
          (if b\<^sub>4 v\<^sub>0 then (q::\<real>) else 0) * c\<^sub>4
    ) summable_on UNIV"
  apply (subst summable_on_add)+
  apply (rule summable_on_cmult_left)
  apply (simp add: assms(1) infsum_constant_finite_states_summable)
  apply (rule summable_on_cmult_left)
  apply (simp add: assms(2) infsum_constant_finite_states_summable)+
  apply (rule summable_on_cmult_left)
  apply (simp add: assms(3) infsum_constant_finite_states_summable)+
  apply (rule summable_on_cmult_left)
  by (simp add: assms(4) infsum_constant_finite_states_summable)+

lemma infsum_constant_finite_states_4:
  assumes "finite {s. b\<^sub>1 s}" "finite {s. b\<^sub>2 s}" "finite {s. b\<^sub>3 s}" "finite {s. b\<^sub>4 s}"
  shows "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. 
          (if b\<^sub>1 v\<^sub>0 then (m::\<real>) else 0) * c\<^sub>1 + 
          (if b\<^sub>2 v\<^sub>0 then (n::\<real>) else 0) * c\<^sub>2 + 
          (if b\<^sub>3 v\<^sub>0 then (p::\<real>) else 0) * c\<^sub>3+ 
          (if b\<^sub>4 v\<^sub>0 then (q::\<real>) else 0) * c\<^sub>4) 
    = m * card {s. b\<^sub>1 s} * c\<^sub>1 + n * card {s. b\<^sub>2 s} * c\<^sub>2 + p * card {s. b\<^sub>3 s} * c\<^sub>3 + q * card {s. b\<^sub>4 s} * c\<^sub>4"
  apply (subst infsum_add)
  using assms(1) assms(2) assms(3) apply (rule infsum_constant_finite_states_summable_cmult_3)
  using assms(4) apply (rule infsum_constant_finite_states_summable_cmult_1)
  apply (subst infsum_constant_finite_states_cmult_1)
  using assms(4) apply blast
  apply (subst infsum_constant_finite_states_cmult_3)
  using assms(1) assms(2) assms(3) by blast+

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

lemma infsum_mult_subset_left_summable: 
  "((\<lambda>v\<^sub>0::'a. (if b v\<^sub>0 then (1::\<real>) else 0) * (P v\<^sub>0)) summable_on UNIV) = 
   ((\<lambda>v\<^sub>0::'a. (P v\<^sub>0)) summable_on {v\<^sub>0. b v\<^sub>0})"
  apply (rule summable_on_cong_neutral)
  apply simp
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

lemma infsum_not_zero_is_summable:
  assumes "infsum f A \<noteq> 0"
  shows "f summable_on A"
  using assms infsum_not_exists by blast

lemma infsum_mult_subset_left_summable': 
  assumes "P summable_on UNIV"
  shows "(\<lambda>v\<^sub>0::'a. ((if b v\<^sub>0 then (m::\<real>) else 0) * (P v\<^sub>0))) summable_on UNIV"
  apply (subgoal_tac "(\<lambda>v\<^sub>0. (if b v\<^sub>0 then (m::\<real>) else 0) * (P v\<^sub>0)) summable_on UNIV
    \<longleftrightarrow> (\<lambda>x::'a. m * P x) summable_on {x. b x}")
  apply (metis assms subset_UNIV summable_on_cmult_right summable_on_subset_banach)
  apply (rule summable_on_cong_neutral)
  apply blast
  apply simp
  by auto

lemma infsum_mono_strict:
  fixes f :: "'a \<Rightarrow> \<real>"
  assumes "f summable_on A" and "g summable_on A"
  assumes \<open>\<And>x. x \<in> A \<Longrightarrow> f x < g x\<close>
  assumes "A \<noteq> {}"
  shows "infsum f A < infsum g A"
proof -
  have f0: \<open>\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x\<close>
    using assms(3) nless_le by blast
  then have f1: "infsum f A \<le> infsum g A"
    by (simp add: assms(1) assms(2) infsum_mono)
  have f2: "infsum g A = infsum (\<lambda>x. (g x - f x) + f x) A"
    by auto
  also have f3: "... = infsum (\<lambda>x. (g x - f x)) A + infsum f A"
    apply (subst infsum_add)
    using summable_on_minus assms(1) assms(2) apply blast
    apply (simp add: assms(1))
    by simp
  obtain x where P_x: "x \<in> A"
    using assms(4) by blast
  have f4: "\<And>x. x \<in> A \<Longrightarrow> (g x - f x) > 0"
    using assms(3) by auto
  have f5: "infsum (\<lambda>x. (g x - f x)) ((A - {x}) \<union> {x}) = infsum (\<lambda>x. (g x - f x)) (A - {x}) + infsum (\<lambda>x. (g x - f x)) {x}"
    apply (subst infsum_Un_disjoint)
    apply (simp add: P_x assms(1) assms(2) summable_on_Diff summable_on_minus)
    apply simp
    apply blast
    by (simp)
  have f6: "... \<ge> infsum (\<lambda>x. (g x - f x)) {x}"
    by (smt (verit) DiffD1 f0 infsum_nonneg)
  have f7: "... > 0"
    using f4 P_x f6 by fastforce
  have f8: "infsum (\<lambda>x. (g x - f x)) A > 0"
    by (metis P_x Un_commute f5 f7 insert_Diff insert_is_Un)
  then have "infsum f A \<noteq> infsum g A"
    using f2 f3 by linarith
  then show "infsum f A < infsum g A"
    using f1 nless_le by blast
qed

subsection \<open> Series \<close>

lemma summable_n_2_power_n: 
  "summable (\<lambda>n::\<nat>. (n / (2::\<real>)^n))" (is "summable ?f")
  (* n:           0, 1,   2,   3,   4 *)
  (*              0, 1/2, 2/4, 3/8, 4/16 *)
  (* (n+1)/(2*n): x, 1,   3/4, 4/6, 5/8, ... *)
  apply (subst summable_ratio_test[where c="3/4" and N="3"])
  apply auto
proof -
  fix n::\<nat>
  assume a1: "3 \<le> n"
  have f1: "((1::\<real>) + real n) / ((2::\<real>) * (2::\<real>) ^ n) = ((n+1) / (2* n)) * (?f n)"
    using a1 by auto
  have f2: "((1::\<real>) + real n) / 1 \<le> (3::\<real>) * real n / ((2::\<real>))"
    using a1 by force
  have f3: "((1::\<real>) + real n) / ((2::\<real>) * (2::\<real>) ^ n) \<le> (3::\<real>) * real n / (2) / ((2::\<real>) * (2::\<real>) ^ n)"
    apply (subst divide_right_mono[where c="((2::\<real>) * (2::\<real>) ^ n)"])
    using f2 apply force
    apply force
    by simp
  show "((1::\<real>) + real n) / ((2::\<real>) * (2::\<real>) ^ n) \<le> (3::\<real>) * real n / ((4::\<real>) * (2::\<real>) ^ n)"
    apply (simp only: f1)
    apply (auto)
    using f3 by force
qed

lemma summable_2_power_n: "summable (\<lambda>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n / (2::\<real>))"
  apply (rule summable_divide)
  apply (rule summable_geometric)
  by simp

(*
lemma summable_n_a_power_n: 
  assumes "a \<ge> 2"
  shows "summable (\<lambda>n::\<nat>. (n / (a::\<real>)^n))" (is "summable ?f")
  (* n:           0, 1,   2,      3,    4 *)
  (*              0, 1/a, 2/a^2, 3/a^3, 4/a^4 *)
  (* (n+1)/(a*n): x, 2/a, 3/a*2, 4/a*3, 5/a*4, ... *)
  apply (subst summable_ratio_test[where c="3/4" and N="3"])
  apply auto
proof -
  fix n::\<nat>
  assume a1: "3 \<le> n"
  have f0: "\<bar>a * a ^ n\<bar> = a * a ^ n"
    using assms by auto
  have f1: "\<bar>a ^ n\<bar> = a ^ n"
    using assms by auto
  have f1: "((1::\<real>) + real n) / ((a::\<real>) * (a::\<real>) ^ n) = ((n+1) / (a* n)) * (?f n)"
    using a1 by auto
  have f2: "((1::\<real>) + real n) / 1 \<le> (3::\<real>) * real n / (4/a)"
    apply auto
  have f3: "((1::\<real>) + real n) / ((2::\<real>) * (2::\<real>) ^ n) \<le> (3::\<real>) * real n / (2) / ((2::\<real>) * (2::\<real>) ^ n)"
    apply (subst divide_right_mono[where c="((2::\<real>) * (2::\<real>) ^ n)"])
    using f2 apply force
    apply force
    by simp
  show "((1::\<real>) + real n) / \<bar>a * a ^ n\<bar> \<le> (3::\<real>) * real n / ((4::\<real>) * \<bar>a ^ n\<bar>)"
    apply (simp only: f0)
    apply (simp only: f1)
    apply (auto)
    using f3 by force
qed
*)

lemma summable_1_2_power_n_t_n: 
  "summable (\<lambda>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ (n) * ((real (t::\<nat>) + real n)))" (is "summable ?f")
proof -
  have f1: "(\<lambda>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n * ((real t + real n))) = 
        (\<lambda>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n * (real t)  + ((1::\<real>) / (2::\<real>)) ^ n * (real n))"
    by (metis (mono_tags, opaque_lifting) mult_of_nat_commute of_nat_add ring_class.ring_distribs(2))

  have f2: "(\<lambda>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n * real n) = (\<lambda>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n * n)"
    by simp
  show "summable ?f"
    apply (simp add: f1)
     apply (subst summable_add)
    apply (rule summable_mult2)
    apply (rule summable_geometric)
    apply simp
    apply (subst summable_cong[where g = "(\<lambda>n::\<nat>. (n / (2::\<real>)^n))"])
    apply (simp add: power_divide)
    using summable_n_2_power_n apply blast
    by simp
qed

end
