section \<open> Probabilistic Designs \<close>

theory utp_distribution
  imports 
    "HOL.Series" 
    "HOL-Analysis.Infinite_Sum"
    "/Users/rye/Isabelle/New_UTP/UTP/utp"
    "utp_iverson_bracket"
begin 

unbundle UTP_Syntax
print_bundles   

declare [[show_types]]

named_theorems dist_defs

subsection \<open> Probability and distributions \<close>
definition is_prob:: "(real, 's) expr \<Rightarrow> bool" where
[dist_defs]: "is_prob e = `0 \<le> e \<and> e \<le> 1`"

definition is_sum_1:: "(real, 's) expr \<Rightarrow> bool" where
[dist_defs]: "is_sum_1 e = ((\<Sum>\<^sub>\<infinity> s. e s) = (1::\<real>))"

definition is_dist:: "(real, 's) expr \<Rightarrow> bool" where
[dist_defs]: "is_dist e = (is_prob e \<and> is_sum_1 e)"

(* The final states of a program characterised by f is a distribution *)
abbreviation "is_final_distribution f \<equiv> (\<forall>s\<^sub>1::'s\<^sub>1. is_dist ((curry f) s\<^sub>1))"
abbreviation "is_final_prob f \<equiv> (\<forall>s\<^sub>1::'s\<^sub>1. is_prob ((curry f) s\<^sub>1))"

(*
definition prob_prog::"('s\<^sub>1 \<leftrightarrow> 's\<^sub>2) \<Rightarrow> real" where
"prob_prog s = 1"
*)
(*
term "{1::nat..}"
lemma "is_dist (\<lambda>(m::nat,n). (1/2)^(n+m))"
  apply (simp add: dist_defs expr_defs)
  apply (auto)
  apply (simp add: power_le_one)
  sorry
*)

full_exprs

subsection \<open> Normalisaiton \<close>
text \<open> Normalisation of a real-valued expression. \<close>
(* If e is not summable, the infinite summation will be equal to 0 based on the definition of infsum,
then this definition here will have a problem (divide-by-zero). How to deal with it??
*)
(*
definition dist_norm::"(real, 's) expr \<Rightarrow> (real, 's) expr" ("\<^bold>N _") where
[dist_defs]: "dist_norm e = (e / (\<Sum>\<^sub>\<infinity> s. \<guillemotleft>e\<guillemotright> s))\<^sub>e"
*)
definition dist_norm::"(real, 's\<^sub>1 \<times> 's\<^sub>2) expr \<Rightarrow> (real, 's\<^sub>1 \<times> 's\<^sub>2) expr" ("\<^bold>N _") where
[dist_defs]: "dist_norm P = (P / (\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> P)))\<^sub>e"

definition dist_norm_alpha::"('v \<Longrightarrow> 's\<^sub>2) \<Rightarrow> (real, 's\<^sub>1 \<times> 's\<^sub>2) expr \<Rightarrow> (real, 's\<^sub>1 \<times> 's\<^sub>2) expr" ("\<^bold>N\<^sub>\<alpha> _ _") where
[dist_defs]: "dist_norm_alpha x P = (P / (\<Sum>\<^sub>\<infinity> v. ([ x\<^sup>> \<leadsto> \<guillemotleft>v\<guillemotright> ] \<dagger> P)))\<^sub>e"

expr_ctr dist_norm_alpha dist_norm

definition uniform_dist:: "('b \<Longrightarrow> 's) \<Rightarrow> \<bbbP> 'b \<Rightarrow> (real, 's \<times> 's) expr" (infix "\<^bold>\<U>" 60) where
[dist_defs]: "uniform_dist x A = \<^bold>N\<^sub>\<alpha> x (\<lbrakk>\<lbrakk>\<Union> v \<in> A. x := \<guillemotleft>v\<guillemotright>\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e)"

term "(\<Union> v \<in> {}. x := \<guillemotleft>v\<guillemotright>)"
term "false_pred"
lemma "(\<Union> v \<in> {}. x := \<guillemotleft>v\<guillemotright>) = false"
  by (simp add: false_pred_def)

term "x \<^bold>\<U> A"
(*
alphabet state = 
  n :: nat
  m :: nat

term "$n"
term "n"
term "n\<^sup><"
term "$n\<^sup><"
term "$n\<^sup>>"
term "\<^bold>v::('a state_scheme \<Longrightarrow> 'a state_scheme)"
term "$n"
term "($n+1)\<^sub>e"
term "(((1::\<real>)/2)^($n\<^sup><+$m\<^sup><))"
full_exprs
term "(0+f)\<^sub>e"
term "($x + @g)\<^sub>e"
term "($n\<^sup>> = $n\<^sup>< + 1)\<^sub>e"
term "(\<lbrakk>($n\<^sup>> = $n\<^sup>< + 1)\<^sub>e\<rbrakk>\<^sub>\<I>)"
*)

subsection \<open> Laws \<close>
lemma is_final_distribution_prob:
  assumes "is_final_distribution f"
  shows "is_final_prob f"
  using assms is_dist_def by blast

lemma is_final_prob_altdef:
  assumes "is_final_prob f"
  shows "\<forall>s s'. f (s, s') \<ge> 0 \<and> f (s, s') \<le> 1"
  by (metis (mono_tags, lifting) SEXP_def assms curry_conv is_prob_def taut_def)

end
