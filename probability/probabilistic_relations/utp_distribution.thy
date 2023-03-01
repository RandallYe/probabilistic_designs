section \<open> Probabilistic distributions \<close>

theory utp_distribution
  imports 
    "HOL.Series" 
    "utp_iverson_bracket"
begin 

unbundle UTP_Syntax
print_bundles   

named_theorems dist_defs

subsection \<open> Probability and distributions \<close>
definition is_nonneg:: "(real, 's) expr \<Rightarrow> bool" where
[dist_defs]: "is_nonneg e = `0 \<le> e`"

definition is_prob:: "(real, 's) expr \<Rightarrow> bool" where
[dist_defs]: "is_prob e = `0 \<le> e \<and> e \<le> 1`"

definition is_sum_1:: "(real, 's) expr \<Rightarrow> bool" where
[dist_defs]: "is_sum_1 e = ((\<Sum>\<^sub>\<infinity> s. e s) = (1::\<real>))"

text \<open>We treat a real function whose probability is always zero for any state as not a subdistribution,
which allows us to conclude this function is summable or convergent. \<close>
definition is_sum_leq_1:: "(real, 's) expr \<Rightarrow> bool" where
[dist_defs]: "is_sum_leq_1 e = (((\<Sum>\<^sub>\<infinity> s. e s) \<le> (1::\<real>)) \<and> ((\<Sum>\<^sub>\<infinity> s. e s) > (0::\<real>)))"

definition is_dist:: "(real, 's) expr \<Rightarrow> bool" where
[dist_defs]: "is_dist e = (is_prob e \<and> is_sum_1 e)"

definition is_sub_dist:: "(real, 's) expr \<Rightarrow> bool" where
[dist_defs]: "is_sub_dist e = (is_prob e \<and> is_sum_leq_1 e)"

(* The final states of a program characterised by f is a distribution *)
abbreviation "is_final_distribution f \<equiv> (\<forall>s\<^sub>1::'s\<^sub>1. is_dist ((curry f) s\<^sub>1))"
abbreviation "is_final_sub_dist f \<equiv> (\<forall>s\<^sub>1::'s\<^sub>1. is_sub_dist ((curry f) s\<^sub>1))"
abbreviation "is_final_prob f \<equiv> (\<forall>s\<^sub>1::'s\<^sub>1. is_prob ((curry f) s\<^sub>1))"

(* Use the tautology notation 
abbreviation "is_final_distribution f \<equiv> `is_dist (@(curry f))`"
abbreviation "is_final_sub_dist f \<equiv> `is_sub_dist (@(curry f))`"
abbreviation "is_final_prob f \<equiv> `is_prob (@(curry f))`"
*)

full_exprs

subsection \<open> Normalisaiton \<close>
text \<open> Normalisation of a real-valued expression. 
If @{text "p"} is not summable, the infinite summation (@{text "\<Sum>\<^sub>\<infinity>"}) will be equal to 0 based on the 
definition of infsum, then this definition here will have a problem (divide-by-zero). We need to 
make sure that @{text "p"} is summable.
\<close>

definition dist_norm::"(real, 's) expr \<Rightarrow> (real, 's) expr" ("\<^bold>N _") where
[dist_defs]: "dist_norm p = (p / (\<Sum>\<^sub>\<infinity> s. \<guillemotleft>p\<guillemotright> s))\<^sub>e"

definition dist_norm_final ::"(real, 's\<^sub>1 \<times> 's\<^sub>2) expr \<Rightarrow> (real, 's\<^sub>1 \<times> 's\<^sub>2) expr" ("\<^bold>N\<^sub>f _") where
[dist_defs]: "dist_norm_final P = (P / (\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> P)))\<^sub>e"

thm "dist_norm_final_def"

definition dist_norm_alpha::"('v \<Longrightarrow> 's\<^sub>2) \<Rightarrow> (real, 's\<^sub>1 \<times> 's\<^sub>2) expr \<Rightarrow> (real, 's\<^sub>1 \<times> 's\<^sub>2) expr" ("\<^bold>N\<^sub>\<alpha> _ _") where
[dist_defs]: "dist_norm_alpha x P = (P / (\<Sum>\<^sub>\<infinity> v. ([ x\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright> ] \<dagger> P)))\<^sub>e"

thm "dist_norm_alpha_def"
expr_constructor dist_norm_alpha dist_norm

definition uniform_dist:: "('b \<Longrightarrow> 's) \<Rightarrow> \<bbbP> 'b \<Rightarrow> (real, 's \<times> 's) expr" (infix "\<^bold>\<U>" 60) where
[dist_defs]: "uniform_dist x A = \<^bold>N\<^sub>\<alpha> x (\<lbrakk>\<Squnion> v \<in> \<guillemotleft>A\<guillemotright>. x := \<guillemotleft>v\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e)"

lemma "(\<Squnion> v \<in> {}. x := \<guillemotleft>v\<guillemotright>) = false"
  by (pred_auto)

subsection \<open> Laws \<close>
lemma is_prob_ibracket: "is_prob (\<lbrakk>p\<rbrakk>\<^sub>\<I>\<^sub>e)"
  by (simp add: is_prob_def expr_defs)

lemma is_dist_subdist: "\<lbrakk>is_dist p\<rbrakk> \<Longrightarrow> is_sub_dist p"
  by (simp add: dist_defs)

lemma is_final_distribution_prob:
  assumes "is_final_distribution f"
  shows "is_final_prob f"
  using assms is_dist_def by blast

lemma is_final_prob_prob:
  assumes "is_final_prob f"
  shows "is_prob f"
  by (smt (verit, best) SEXP_def assms curry_conv is_prob_def prod.collapse taut_def)

lemma is_prob_final_prob: "\<lbrakk>is_prob P\<rbrakk> \<Longrightarrow> is_final_prob P"
  by (simp add: is_prob_def taut_def)

lemma is_prob: "\<lbrakk>is_prob P\<rbrakk> \<Longrightarrow> (\<forall>s. P s \<ge> 0 \<and> P s \<le> 1)"
  by (simp add: is_prob_def taut_def)

lemma is_final_prob_altdef:
  assumes "is_final_prob f"
  shows "\<forall>s s'. f (s, s') \<ge> 0 \<and> f (s, s') \<le> 1"
  by (metis (mono_tags, lifting) SEXP_def assms curry_conv is_prob_def taut_def)

lemma is_final_dist_subdist:
  assumes "is_final_distribution f"
  shows "is_final_sub_dist f"
  apply (simp add: dist_defs)
  by (smt (z3) SEXP_def assms cond_case_prod_eta curry_case_prod is_dist_def is_prob_def 
      is_sum_1_def order.refl taut_def)

lemma is_final_sub_dist_prob:
  assumes "is_final_sub_dist f"
  shows "is_final_prob f"
  apply (simp add: dist_defs)
  by (metis (mono_tags, lifting) SEXP_def assms curry_def is_prob is_sub_dist_def tautI)

lemma is_nonneg: "(is_nonneg e) \<longleftrightarrow> (\<forall>s. e s \<ge> 0)"
  apply (auto)
  by (simp add: is_nonneg_def taut_def)+

lemma is_nonneg2: "\<lbrakk>is_nonneg p; is_nonneg q\<rbrakk> \<Longrightarrow> is_nonneg (p*q)\<^sub>e"
  by (simp add: is_nonneg_def taut_def)+

lemma dist_norm_is_prob:
  assumes "is_nonneg e"
  assumes "infsum e UNIV > 0"
  shows "is_prob (\<^bold>N e)"
  apply (simp add: dist_defs expr_defs)
  apply (rule allI, rule conjI)
  apply (meson assms(1) assms(2) divide_nonneg_pos is_nonneg)
  apply (insert infsum_geq_element[where f = "e"])
  by (metis UNIV_I assms(1) assms(2) divide_le_eq_1_pos division_ring_divide_zero infsum_not_exists 
      is_nonneg linordered_nonzero_semiring_class.zero_le_one)
end
