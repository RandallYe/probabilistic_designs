section \<open> Probabilistic Designs \<close>

theory utp_iverson_bracket
  imports "/Users/rye/Isabelle/New_UTP/UTP/utp"
begin 

declare [[show_types]]

subsection \<open> Iverson Bracket \<close>

term "(P)\<^sub>e"
term "(False)\<^sub>e"
term "(P)\<^sub>u"
term "\<lbrakk>P\<rbrakk>\<^sub>u"
full_exprs
term "(if P then 1 else 0)\<^sub>e"

definition ivbracket :: "'s pred \<Rightarrow> ('s \<Rightarrow> real)" ("\<lbrakk>_\<rbrakk>\<^sub>\<I>") where 
[expr_defs]: "\<lbrakk>P\<rbrakk>\<^sub>\<I> = (if P then 1 else 0)\<^sub>e"

lemma ivbracket_mono: "\<lbrakk> (P)\<^sub>u \<sqsupseteq> (Q)\<^sub>u \<rbrakk> \<Longrightarrow> \<lbrakk>P\<rbrakk>\<^sub>\<I> \<le> \<lbrakk>Q\<rbrakk>\<^sub>\<I>"
  apply (expr_auto)
  by (simp add: Collect_mono_iff le_funI ref_by_def)

lemma ivbracket_conj: "\<lbrakk>(P \<and> Q)\<^sub>e\<rbrakk>\<^sub>\<I> = \<lbrakk>P\<rbrakk>\<^sub>\<I> * \<lbrakk>Q\<rbrakk>\<^sub>\<I>"
  by (expr_auto)
  by (metis Collect_mem_eq SEXP_def ivbracket_def mult_cancel_right1 mult_not_zero 
      pred_ba.inf_top.neutr_eq_iff pred_set pred_set_def)

lemma ivbracket_disj: "\<lbrakk>\<lbrakk>(P)\<^sub>u \<or> (Q)\<^sub>u\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I> = \<lbrakk>P\<rbrakk>\<^sub>\<I> + \<lbrakk>Q\<rbrakk>\<^sub>\<I> - (\<lbrakk>P\<rbrakk>\<^sub>\<I> * \<lbrakk>Q\<rbrakk>\<^sub>\<I>)"
  apply (simp add: pred_disj pred_set)
  apply (simp add: SEXP_def)
  apply (simp add: ivbracket_def)
  apply (simp add: pred_set_def)
  apply (simp add: SEXP_def)
  apply (rule conjI)
  using true_pred_def apply fastforce
  apply (rule impI)
  apply (rule conjI)
  using true_pred_def apply fastforce
  apply (rule impI)
  sorry                                                   

lemma ivbracket_not: "\<lbrakk>\<lbrakk>\<not>(P)\<^sub>u\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I> = 1 - \<lbrakk>P\<rbrakk>\<^sub>\<I>"
  by (smt (z3) Collect_mem_eq SEXP_def boolean_algebra.disj_cancel_left disj_pred_def 
      false_pred_def ivbracket_conj ivbracket_def ivbracket_disj not_pred_def pred_UNIV 
      pred_ba.boolean_algebra.conj_cancel_left pred_empty pred_set_def set_pred_def 
      true_false_pred_expr(1))

subsection \<open> Inverse Iverson Bracket \<close>
axiomatization inivbracket :: "real \<Rightarrow> 's pred" ("\<^bold>\<langle>_\<^bold>\<rangle>\<^sub>\<I>") where 
ivivbracket_def: "(\<lbrakk>\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> (P)\<^sub>u) = (N \<le> \<lbrakk>P\<rbrakk>\<^sub>\<I>)"

lemma false_simp: "(\<lbrakk>false\<rbrakk>\<^sub>P)\<^sub>u = false"
  by (simp add: false_pred_def pred_empty)

lemma false_0: "\<lbrakk>\<lbrakk>false\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I> = 0"
  by (metis SEXP_def false_pred_def ivbracket_def pred_UNIV pred_empty true_false_pred_expr(2) true_pred_def)

lemma inivbracket_1: "\<^bold>\<langle>1\<^bold>\<rangle>\<^sub>\<I> = (true)\<^sub>e"
proof -
  have 1: "(\<lbrakk>\<^bold>\<langle>1\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> (\<lbrakk>false\<rbrakk>\<^sub>P)\<^sub>u) = (1 \<le> \<lbrakk>\<lbrakk>false\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>)"
    using ivivbracket_def 
    by (metis SEXP_def false_pred_def ivbracket_def pred_UNIV pred_empty pred_set true_pred_def)
  have 2: "(\<lbrakk>\<^bold>\<langle>1\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> false) = (1 \<le> (0::real))"
    using 1 by (simp add: false_simp false_0)
  then have 3: "(\<lbrakk>\<^bold>\<langle>1\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> false) = false"
    by simp
  then show ?thesis
    by (metis SEXP_def ivbracket_def ivivbracket_def not_one_le_zero pred_UNIV pred_set 
        ref_order.order_refl true_pred_def)
qed

lemma inivbracket_0: "\<^bold>\<langle>0\<^bold>\<rangle>\<^sub>\<I> = (false)\<^sub>e"
proof -
  have 1: "(\<lbrakk>\<^bold>\<langle>0\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> (\<lbrakk>false\<rbrakk>\<^sub>P)\<^sub>u) = (0 \<le> \<lbrakk>\<lbrakk>false\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>)"
    using ivivbracket_def 
    by (metis SEXP_def false_pred_def ivbracket_def pred_UNIV pred_empty pred_set true_pred_def)
  have 2: "(\<lbrakk>\<^bold>\<langle>0\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> false) = (0 \<le> (0::real))"
    using 1 by (simp add: false_simp false_0)
  then have 3: "(\<lbrakk>\<^bold>\<langle>0\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> false) = true"
    by simp
  then show ?thesis
    by (metis false_pred_def pred_ba.bot.extremum_uniqueI pred_empty pred_set)
qed

lemma ivbracket_approximate_inverse: "N \<le> \<lbrakk>\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>\<I>"
proof -
  have 1: "(\<lbrakk>\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> \<lbrakk>\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u) = (N \<le> \<lbrakk>\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>\<I>)"
    using ivivbracket_def
    by (metis SEXP_def ref_order.order_refl)
  then show ?thesis
    by auto
qed

lemma inivbracket_approximate_inverse: "\<lbrakk>\<^bold>\<langle>\<lbrakk>P\<rbrakk>\<^sub>\<I>\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> (P)\<^sub>u"
proof -
  have 1: "(\<lbrakk>\<^bold>\<langle>\<lbrakk>P\<rbrakk>\<^sub>\<I>\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> (P)\<^sub>u) = (\<lbrakk>P\<rbrakk>\<^sub>\<I> \<le> \<lbrakk>P\<rbrakk>\<^sub>\<I>)"
    using ivivbracket_def
    by (metis SEXP_def ref_order.order_refl)
  then show ?thesis
    by auto
qed

lemma inivbracket_N_0:
  assumes "N \<ge> 0"
  shows "(\<lbrakk>\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u = false) = (N = 0)"
proof -
  have 1: "(\<lbrakk>\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> (\<lbrakk>false\<rbrakk>\<^sub>P)\<^sub>u) = (N \<le> \<lbrakk>\<lbrakk>false\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>)"
    using ivivbracket_def
    by (metis false_0)
  have 2: "(\<lbrakk>\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> false) = (N \<le> (0::real))"
    using 1 by (simp add: false_simp false_0)
  then have 3: "(\<lbrakk>\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> false) = (N = (0::real))"
    using assms by auto
  then show ?thesis
    by (simp add: ref_order.dual_order.eq_iff)
qed

end
