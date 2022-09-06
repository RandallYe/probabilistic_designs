section \<open> Iverson Bracket \<close>

theory utp_iverson_bracket
  imports "UTP2.utp"
          "infsum_laws"
begin 

unbundle UTP_Syntax
print_bundles

(* Switch off lattice syntax from UTP *)
unbundle no_UTP_lattice_syntax
(* unbundle no_lattice_syntax *)
print_bundles

term "\<bottom>"

(* Switch on lattice syntax from HOL *)
unbundle lattice_syntax
term "\<bottom>"

declare [[show_types]]

(* named_theorems iverson_bracket_defs *)

subsection \<open> Iverson Bracket \<close>

(* syntax translation: \<s> *)
(* syntax _iversion_bracket :: "logic => logic" ("...") *)
definition iverson_bracket :: "'s pred \<Rightarrow> ('s \<Rightarrow> real)"  where 
[expr_defs]: "iverson_bracket P = (if P then 1 else 0)\<^sub>e"

syntax 
  "_e_iverson_bracket" :: "logic \<Rightarrow> logic" ("\<lbrakk>_\<rbrakk>\<^sub>\<I>\<^sub>e" 150)
  "_iverson_bracket" :: "logic \<Rightarrow> logic" ("\<lbrakk>_\<rbrakk>\<^sub>\<I>" 150)

translations
  "_e_iverson_bracket P" == "CONST iverson_bracket (P)\<^sub>e"
  "_iverson_bracket P" == "CONST iverson_bracket P"

definition nat_of_real_1 :: "real \<Rightarrow> nat" where
"nat_of_real_1 r = (if r = (1::\<real>) then (1) else 0)"

(* Declare your Iverson brackets operator as an expression constructor, to stop it being lifted *)
expr_constructor iverson_bracket

lemma iverson_bracket_mono: "\<lbrakk> (P) \<sqsupseteq> (Q) \<rbrakk> \<Longrightarrow> \<lbrakk>P\<rbrakk>\<^sub>\<I> \<le> \<lbrakk>Q\<rbrakk>\<^sub>\<I>"
  apply (simp add: ref_by_pred_is_leq)
  apply (simp add: iverson_bracket_def)
  apply (intro le_funI)
  by auto

lemma iverson_bracket_conj: "\<lbrakk>P \<and> Q\<rbrakk>\<^sub>\<I>\<^sub>e = (\<lbrakk>P\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>Q\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"
  by (expr_auto)

(* term "(a \<le> \<s> \<and> \<s> \<le> b)\<^sub>e" *)
lemma iverson_bracket_conj1 : "\<lbrakk>\<lambda>s. (a \<le> s \<and> s \<le> b)\<rbrakk>\<^sub>\<I> = (\<lbrakk>\<lambda>s. a \<le> s\<rbrakk>\<^sub>\<I> * \<lbrakk>\<lambda>s. s \<le> b\<rbrakk>\<^sub>\<I>)\<^sub>e"
  by (expr_auto)

lemma iverson_bracket_disj: "\<lbrakk>P \<or> Q\<rbrakk>\<^sub>\<I>\<^sub>e = (\<lbrakk>P\<rbrakk>\<^sub>\<I>\<^sub>e + \<lbrakk>Q\<rbrakk>\<^sub>\<I>\<^sub>e - (\<lbrakk>P\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>Q\<rbrakk>\<^sub>\<I>\<^sub>e))\<^sub>e"
  by (expr_auto)                          

lemma iverson_bracket_not: "\<lbrakk>\<not>P\<rbrakk>\<^sub>\<I>\<^sub>e = (1 - \<lbrakk>P\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"
  by (expr_auto)

lemma iverson_bracket_plus: "(\<lbrakk>\<lambda>s. s \<in> A\<rbrakk>\<^sub>\<I> + \<lbrakk>\<lambda>s. s \<in> B\<rbrakk>\<^sub>\<I>)\<^sub>e = (\<lbrakk>\<lambda>s. s \<in> A \<inter> B\<rbrakk>\<^sub>\<I> + \<lbrakk>\<lambda>s. s \<in> A \<union> B\<rbrakk>\<^sub>\<I>)\<^sub>e"
  by (expr_auto)

lemma iverson_bracket_inter : "\<lbrakk>\<lambda>s. s \<in> A \<inter> B\<rbrakk>\<^sub>\<I> = (\<lbrakk>\<lambda>s. s \<in> A\<rbrakk>\<^sub>\<I> * \<lbrakk>\<lambda>s. s \<in> B\<rbrakk>\<^sub>\<I>)\<^sub>e"
  by (expr_auto)

(* Infinite products give 1 (instead of 0), no matter how P is defined. *)
lemma infinite_prod_is_1:
  fixes P::"'b \<Rightarrow> real"
  assumes "\<not> finite (UNIV::'b set)"
  shows "(\<Prod> m|True. (P m)) = (1::real)"
  using assms by force

(* There are three theories in Isabelle regarding summation 
  1. Group_Big, where infinite sum is 0 and infinite product is 1
*)
term "sum"
term "(sum (\<lambda>s. (\<lbrakk>P\<rbrakk>\<^sub>\<I>)\<^sub>e s) A)"
term "(\<Sum>x\<in>\<guillemotleft>A\<guillemotright>. \<lbrakk>P\<rbrakk>\<^sub>\<I>)\<^sub>e"
(*
  2. Series, where n in "\<Sum>n" is over natural numbers.
*)
(* term "sums" *)
term "suminf"
(*
  3. Inf_Sum, where sums over possibly infinite sets
*)
(* term "\<Sum>\<^sub>\<infinity>" *)
term "infsum"
term "has_sum"
term "f summable_on A"
(*
  4. Inf_Set_Sum
*)
term "infsetsum"
(* term "\<Sum>\<^sub>a"*)

(* Infinite sums give 0, no matter how P is defined. *)
lemma infinite_sum_is_0:
  fixes P::"'b \<Rightarrow> real"
  assumes "\<not> finite (UNIV::'b set)"
  shows "(\<Sum> m|True. (P m)) = (0::real)"
  using assms by auto

(* So this theorem is only valid for finite (type of m)? ? ?*)
lemma iverson_bracket_forall_prod:
  fixes P::"'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "finite (UNIV::'b set)"
  shows "\<lbrakk>(\<forall>m. P m)\<rbrakk>\<^sub>\<I>\<^sub>e = (\<Prod> m|True. (\<lbrakk>(P \<guillemotleft>m\<guillemotright>)\<rbrakk>\<^sub>\<I>\<^sub>e))\<^sub>e"
  apply (expr_auto)
proof -
  fix x::"'a" and xa::"'b"
  assume a1: "\<not> P x xa"
  show "(\<Prod>m::'b\<in>UNIV. if P x m then 1::\<real> else (0::\<real>)) = (0::\<real>)"
    apply (rule prod_zero)
    apply (simp add: assms)
    using a1 by auto
qed

text \<open> We use @{text "\<Sum>\<^sub>\<infinity>"} (@{term "infsum"}) to take into account infinite sets that satisfy @{text "P"}. 
For this case, the summation is just equal to 0. Then this lemma is not true, and so we have added 
a finite assumption.
\<close>
lemma iverson_bracket_exist_sum:
  fixes P::"'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "`finite {m. P m}`"
  shows "\<lbrakk>(\<exists>m. P m)\<rbrakk>\<^sub>\<I>\<^sub>e = (\<lambda>s. (min (1::real) ((\<Sum>\<^sub>\<infinity> m. (\<lbrakk>(P \<guillemotleft>m\<guillemotright>)\<rbrakk>\<^sub>\<I>\<^sub>e))\<^sub>e s)))"
  apply (expr_auto)
  apply (subst infsum_constant_finite_states)
  using assms apply (simp add: taut_def)
  by (smt (verit, del_insts) assms SEXP_def taut_def mem_Collect_eq real_of_card sum_nonneg_leq_bound)

lemma iverson_bracket_exist_sum_1:
  fixes P::"'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "finite (UNIV::'b set)"
  shows "\<lbrakk>(\<exists>m. P m)\<rbrakk>\<^sub>\<I>\<^sub>e = (1 - (\<Prod> m|True. (\<lbrakk>(\<not>P \<guillemotleft>m\<guillemotright>)\<rbrakk>\<^sub>\<I>\<^sub>e)))\<^sub>e"
  apply (expr_auto)
  using assms by auto

(* The use of @{term card} implies finite *)
lemma iverson_bracket_card:
  fixes P::"'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "`finite ({m::'b. P m})`"
  shows "(card {m. P m})\<^sub>e = (\<Sum>\<^sub>\<infinity> m. (\<lbrakk>(P \<guillemotleft>m\<guillemotright>)\<rbrakk>\<^sub>\<I>\<^sub>e))\<^sub>e"
  apply (expr_auto)
  apply (subst infsum_constant_finite_states)
  using assms apply (simp add: taut_def)
  by force

text \<open> With the Iverson bracket, summation with index (LHS) can be defined without its index (RHS). 
As Donald E. Knuth mentioned in ``Two Notes on Notation'', the summation without indices (or limits) 
is better (not easily make a mistake when dealing with its index). \<close>
lemma iverson_bracket_summation:
  fixes P::"'s \<Rightarrow> bool" and f :: "'s \<Rightarrow> \<real>"
  shows "(\<Sum>\<^sub>\<infinity> k|P k. (f)\<^sub>e k) = (\<Sum>\<^sub>\<infinity> k. (f * \<lbrakk>P\<rbrakk>\<^sub>\<I>)\<^sub>e k)"
  by (simp add: infsum_mult_subset_right iverson_bracket_def)

lemma iverson_bracket_product:
  fixes P::"'s \<Rightarrow> bool"
  assumes "finite (UNIV::'s set)"
  shows "(\<Prod> m|P m. f m) = (\<Prod> m|True. (f ^ (\<guillemotleft>nat_of_real_1\<guillemotright> (\<lbrakk>P\<rbrakk>\<^sub>\<I>\<^sub>e)))\<^sub>e m)"
proof -
  let ?P = "\<lambda>m. (if P m then 1::\<real> else (0::\<real>))"
  let ?Q = "\<lambda>r. (if r = (1::\<real>) then 1::\<nat> else (0::\<nat>))"
  have f1: "(\<Prod>m::'s\<in>UNIV. f m ^ (?Q (?P m))) = (\<Prod>m::'s\<in>{m. \<not> P m} \<union> {m. P m}. f m ^ (?Q (?P m)))"
    by (simp add: Un_def)
  have f2: "... = (\<Prod>m::'s\<in>{m. \<not> P m}. f m ^ (?Q (?P m))) * (\<Prod>m::'s\<in>{m. P m}. f m ^ (?Q (?P m)))"
    apply (subst prod.union_inter_neutral)
    apply (meson assms rev_finite_subset subset_UNIV)
    apply (meson assms rev_finite_subset subset_UNIV)
    apply force
    by auto
  show ?thesis
    apply (simp add: expr_defs)
    apply (simp add: nat_of_real_1_def)
    using f1 f2 by auto
qed

lemma max_iverson_bracket:
  "(max x y)\<^sub>e = (x * (\<lbrakk>x > y\<rbrakk>\<^sub>\<I>\<^sub>e) + y * (\<lbrakk>x \<le> y\<rbrakk>\<^sub>\<I>\<^sub>e))\<^sub>e"
  by (expr_auto)

lemma min_iverson_bracket:
  "(min x y)\<^sub>e = (x * (\<lbrakk>x \<le> y\<rbrakk>\<^sub>\<I>\<^sub>e) + y * (\<lbrakk>x > y\<rbrakk>\<^sub>\<I>\<^sub>e))\<^sub>e"
  by (expr_auto)

lemma floor_iverson_bracket:
  "(real_of_int \<lfloor>x\<rfloor>)\<^sub>e = (\<Sum>\<^sub>\<infinity> n. n * \<lbrakk>((real_of_int) \<guillemotleft>n\<guillemotright> \<le> x \<and> x < (real_of_int) (\<guillemotleft>n\<guillemotright> + 1))\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"
  apply (expr_auto)
  apply (subst infsum_mult_subset_right)
proof -
  fix xa
  have "{v\<^sub>0::\<int>. real_of_int v\<^sub>0 \<le> x xa \<and> x xa < real_of_int v\<^sub>0 + (1::\<real>)} = {\<lfloor>x xa\<rfloor>}"
    by (smt (verit) Collect_cong floor_split singleton_conv)
  then show "real_of_int \<lfloor>x xa\<rfloor> =
       infsum real_of_int {v\<^sub>0::\<int>. real_of_int v\<^sub>0 \<le> x xa \<and> x xa < real_of_int v\<^sub>0 + (1::\<real>)}"
    by simp
qed

lemma ceiling_iverson_bracket:
  "(real_of_int \<lceil>x\<rceil>)\<^sub>e = (\<Sum>\<^sub>\<infinity> n. n * \<lbrakk>((real_of_int) \<guillemotleft>n - 1\<guillemotright> < x \<and> x \<le> (real_of_int) (\<guillemotleft>n\<guillemotright>))\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"
  apply (expr_auto)
  apply (subst infsum_mult_subset_right)
proof -
  fix xa
  have "{v\<^sub>0::\<int>. real_of_int v\<^sub>0 - (1::\<real>) < x xa \<and> x xa \<le> real_of_int v\<^sub>0} = {\<lceil>x xa\<rceil>}"
    by (smt (verit) Collect_cong ceiling_split singleton_conv)
  then show "real_of_int \<lceil>x xa\<rceil> =
       infsum real_of_int {v\<^sub>0::\<int>. real_of_int v\<^sub>0 - (1::\<real>) < x xa \<and> x xa \<le> real_of_int v\<^sub>0}"
    by simp
qed

subsection \<open> Inverse Iverson Bracket \<close>
(* Simon: maybe we need to find out a definition for inverse bracket using THE etc. 
TODO: leave this mechanisation as is now.
*)
axiomatization iverson_bracket_inv :: "('s \<Rightarrow> real) \<Rightarrow> 's pred" ("\<^bold>\<langle>_\<^bold>\<rangle>\<^sub>\<I>") where 
iverson_bracket_inv_def: "(\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I> \<sqsupseteq> (P)) = `(N \<le> \<lbrakk>P\<rbrakk>\<^sub>\<I>\<^sub>e)`"

expr_constructor iverson_bracket_inv

lemma false_0: "\<lbrakk>false\<rbrakk>\<^sub>\<I> = (0)\<^sub>e"
  by (pred_simp)

lemma iverson_bracket_inv_1: "\<^bold>\<langle>(1)\<^sub>e\<^bold>\<rangle>\<^sub>\<I> = true"
  by (smt (verit, best) SEXP_def false_pred_def iverson_bracket_def iverson_bracket_inv_def le_funI 
      le_fun_def order_antisym_conv pred_ba.order_eq_iff pred_ba.order_refl ref_by_fun_def 
      ref_lattice.bot_least ref_lattice.top_greatest ref_preorder.order_refl taut_True taut_def true_pred_def zero_neq_one)

lemma iverson_bracket_inv_0: "\<^bold>\<langle>(0)\<^sub>e\<^bold>\<rangle>\<^sub>\<I> = false"
  by (smt (verit, ccfv_SIG) SEXP_def false_0 iverson_bracket_inv_def pred_ba.bot.extremum 
      pred_ba.order_eq_iff taut_def)

lemma iverson_bracket_approximate_inverse: "`N \<le> \<lbrakk>\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>\<I>\<^sub>e`"
  by (metis SEXP_def iverson_bracket_inv_def pred_ba.order_refl)

lemma iverson_bracket_inv_approximate_inverse: "\<^bold>\<langle>\<lbrakk>P\<rbrakk>\<^sub>\<I>\<^bold>\<rangle>\<^sub>\<I> \<sqsupseteq> P"
  using iverson_bracket_inv_def by (smt (verit, ccfv_SIG) SEXP_def taut_def)

lemma iverson_bracket_inv_N_0:
  assumes "`N \<ge> 0`"
  shows "`\<not>(\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>)` = `N = 0`"
  by (smt (verit, best) SEXP_def assms false_pred_def iverson_bracket_approximate_inverse 
      iverson_bracket_def iverson_bracket_inv_def order_antisym_conv pred_ba.bot.extremum_unique taut_def)

lemma iverson_bracket_inv_mono: "\<lbrakk> `(M \<le> N)` \<rbrakk> \<Longrightarrow> \<^bold>\<langle>M\<^bold>\<rangle>\<^sub>\<I> \<sqsupseteq> \<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>"
  by (smt (verit) SEXP_def dual_order.trans iverson_bracket_approximate_inverse iverson_bracket_inv_def taut_def)

end
