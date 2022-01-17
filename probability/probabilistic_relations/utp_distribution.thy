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

(* Incorrect syntax if HOL.Series is imported. *)
term "(\<forall>s. ((0 \<le> (e s)) \<and> ((e s) \<le> 1)))"
term "(\<forall>s. (0 \<le> e \<and> e \<le> 1))"
term "(\<forall>s. (conj (0 \<le> (e s)) ((e s) \<le> 1)))"

definition is_prob:: "(real, 's) expr \<Rightarrow> bool" where
"is_prob e = (\<forall>s. ((0 \<le> (e s)) \<and> ((e s) \<le> 1)))"

definition is_sum_1:: "(real, 's) expr \<Rightarrow> bool" where
"is_sum_1 e = ((\<Sum>s|True. e s) = 1)"
(*
"is_sum_1 e = ((\<Sum>s|True. e s) = 1)"
*)

definition is_dist:: "(real, 's) expr \<Rightarrow> bool" where
"is_dist e = (is_prob e \<and> is_sum_1 e)"

definition prob_prog::"(q's\<^sub>1 \<leftrightarrow> 's\<^sub>2) \<Rightarrow> real" where
"prob_prog s = 1"

lemma "is_dist (\<lambda>n. 2^(n+m))"
  oops

full_exprs
term "(f/(\<Sum>s|True. f))\<^sub>e"
definition normalisation::"(real, 's) expr \<Rightarrow> (real, 's) expr" ("\<^bold>N _") where
"normalisation e = (e/(\<Sum>s|True. \<guillemotleft>e\<guillemotright> s))\<^sub>e"

thm "normalisation_def"
thm "is_sum_1_def"

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

lemma "is_dist ((1/2)^($n+$m))\<^sub>e"
  apply (simp add: is_dist_def is_prob_def is_sum_1_def)
  apply (auto)
  apply (simp add: power_le_one)
  sledgehammer
end
