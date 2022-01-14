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
term "(f + g)\<^sub>e::'s \<Rightarrow> real"
term "(f+g)\<^sup>e"
term "(if P then 1 else 0)\<^sub>e"

definition iverson_bracket :: "'s pred \<Rightarrow> ('s \<Rightarrow> real)" ("\<lbrakk>_\<rbrakk>\<^sub>\<I>") where 
[expr_defs]: "\<lbrakk>P\<rbrakk>\<^sub>\<I> = (if P then 1 else 0)\<^sub>e"

definition nat_of_real_1 :: "real \<Rightarrow> nat" where
"nat_of_real_1 r = (if r = (1::\<real>) then (1) else 0)"

(* Declare your Iverson brackets operator as an expression constructor, to stop it being lifted *)
expr_ctr iverson_bracket

lemma iverson_bracket_mono: "\<lbrakk> (P)\<^sub>u \<sqsupseteq> (Q)\<^sub>u \<rbrakk> \<Longrightarrow> \<lbrakk>P\<rbrakk>\<^sub>\<I> \<le> \<lbrakk>Q\<rbrakk>\<^sub>\<I>"
  apply (expr_auto)
  by (simp add: Collect_mono_iff le_funI ref_by_def)

term "\<lbrakk>P\<rbrakk>\<^sub>\<I>"
term "(0.5*\<lbrakk>P\<rbrakk>\<^sub>\<I>)\<^sub>e"
term "[\<lbrakk>P\<rbrakk>\<^sub>\<I>]\<^sub>e"
term "[\<lambda>s. \<lbrakk>P\<rbrakk>\<^sub>\<I> s * \<lbrakk>Q\<rbrakk>\<^sub>\<I> s]\<^sub>e"
term "(\<lbrakk>P\<rbrakk>\<^sub>\<I> * \<lbrakk>Q\<rbrakk>\<^sub>\<I>)\<^sub>e"

lemma iverson_bracket_conj: "\<lbrakk>(P \<and> Q)\<^sub>e\<rbrakk>\<^sub>\<I> = (\<lbrakk>P\<rbrakk>\<^sub>\<I> * \<lbrakk>Q\<rbrakk>\<^sub>\<I>)\<^sub>e"
  by (expr_auto)

lemma iverson_bracket_conj1 : "\<lbrakk>\<lambda>s. a \<le> s \<and> s \<le> b\<rbrakk>\<^sub>\<I> = (\<lbrakk>\<lambda>s. a \<le> s\<rbrakk>\<^sub>\<I> * \<lbrakk>\<lambda>s. s \<le> b\<rbrakk>\<^sub>\<I>)\<^sub>e"
  by (expr_auto)

lemma iverson_bracket_disj: "\<lbrakk>(P \<or> Q)\<^sub>e\<rbrakk>\<^sub>\<I> = (\<lbrakk>P\<rbrakk>\<^sub>\<I> + \<lbrakk>Q\<rbrakk>\<^sub>\<I> - (\<lbrakk>P\<rbrakk>\<^sub>\<I> * \<lbrakk>Q\<rbrakk>\<^sub>\<I>))\<^sub>e"
  by (expr_auto)                          

lemma iverson_bracket_not: "\<lbrakk>(\<not>P)\<^sub>e\<rbrakk>\<^sub>\<I> = (1 - \<lbrakk>P\<rbrakk>\<^sub>\<I>)\<^sub>e"
  by (expr_auto)

lemma iverson_bracket_plus: "(\<lbrakk>\<lambda>s. s \<in> A\<rbrakk>\<^sub>\<I> + \<lbrakk>\<lambda>s. s \<in> B\<rbrakk>\<^sub>\<I>)\<^sub>e = (\<lbrakk>\<lambda>s. s \<in> A \<inter> B\<rbrakk>\<^sub>\<I> + \<lbrakk>\<lambda>s. s \<in> A \<union> B\<rbrakk>\<^sub>\<I>)\<^sub>e"
  by (expr_auto)

lemma iverson_bracket_inter : "\<lbrakk>\<lambda>s. s \<in> A \<inter> B\<rbrakk>\<^sub>\<I> = (\<lbrakk>\<lambda>s. s \<in> A\<rbrakk>\<^sub>\<I> * \<lbrakk>\<lambda>s. s \<in> B\<rbrakk>\<^sub>\<I>)\<^sub>e"
  by (expr_auto)


term "(\<Prod> m|True. (\<lbrakk>(P \<guillemotleft>m\<guillemotright>)\<^sub>e\<rbrakk>\<^sub>\<I>))\<^sub>e"
term "\<lbrakk>(\<forall>m. P(m))\<^sub>e\<rbrakk>\<^sub>\<I>"
term "prod"
term "1 dvd 2"
thm "infinite_finite_induct"
term "(\<Prod> m|True. ((P::'a\<Rightarrow>real) m))"

(* Infinite products give 1 (instead of 0), no matter how P is defined. *)
lemma infinite_prod_is_1:
  fixes P::"'b \<Rightarrow> real"
  assumes "\<not> finite (UNIV::'b set)"
  shows "(\<Prod> m|True. (P m)) = (1::real)"
  using assms by force


(* There are three theories in Isabelle regarding summation 
  1. Group_Big, where infinite sum is 0 and infinite product is 1
*)
term "c" 
term "sum"
term "(sum (\<lambda>s. (\<lbrakk>P\<rbrakk>\<^sub>\<I>)\<^sub>e s) A)"
term "(\<Sum>x\<in>\<guillemotleft>A\<guillemotright>. \<lbrakk>P\<rbrakk>\<^sub>\<I>)\<^sub>e"
(*
  2. Series, where n in "\<Sum>n" is over natural numbers.
*)
term "sums"
term "suminf"
(*
  3. Inf_Sum, where sums over possibly infinite sets
*)
term "\<Sum>\<^sub>\<infinity>"
term "infsum"
term "has_sum"
term "summable_on"
(*
  4. Inf_Set_Sum
*)
term "infsetsum"
term "\<Sum>\<^sub>a"

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
  shows "\<lbrakk>(\<forall>m. P m)\<^sub>e\<rbrakk>\<^sub>\<I> = (\<Prod> m|True. (\<lbrakk>(P \<guillemotleft>m\<guillemotright>)\<^sub>e\<rbrakk>\<^sub>\<I>))\<^sub>e"
  apply (expr_auto)
proof -
  fix x::"'a" and xa::"'b"
  assume a1: "\<not> P x xa"
  show "(\<Prod>m::'b\<in>UNIV. if P x m then 1::\<real> else (0::\<real>)) = (0::\<real>)"
    apply (rule prod_zero)
    apply (simp add: assms)
    using a1 by auto
qed

term "(\<Sum> m|True. (\<lbrakk>(P \<guillemotleft>m\<guillemotright>)\<^sub>e\<rbrakk>\<^sub>\<I>))\<^sub>e"
term "\<lambda>s. (min (1::real) ((\<Sum> m|True. (\<lbrakk>(P \<guillemotleft>m\<guillemotright>)\<^sub>e\<rbrakk>\<^sub>\<I>))\<^sub>e s))"
(* term "(min (1::real) (\<Sum> m|True. (\<lbrakk>(P \<guillemotleft>m\<guillemotright>)\<^sub>e\<rbrakk>\<^sub>\<I>)))\<^sub>e" *)

(* How about infinite? *)
lemma iverson_bracket_exist_sum:
  fixes P::"'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "finite (UNIV::'b set)"
  shows "\<lbrakk>(\<exists>m. P m)\<^sub>e\<rbrakk>\<^sub>\<I> = (\<lambda>s. (min (1::real) ((\<Sum> m|True. (\<lbrakk>(P \<guillemotleft>m\<guillemotright>)\<^sub>e\<rbrakk>\<^sub>\<I>))\<^sub>e s)))"
  apply (expr_auto)
  by (smt (verit) UNIV_I assms sum_nonneg_leq_bound)

lemma iverson_bracket_exist_sum_1:
  fixes P::"'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "finite (UNIV::'b set)"
  shows "\<lbrakk>(\<exists>m. P m)\<^sub>e\<rbrakk>\<^sub>\<I> = (1 - (\<Prod> m|True. (\<lbrakk>(\<not>P \<guillemotleft>m\<guillemotright>)\<^sub>e\<rbrakk>\<^sub>\<I>)))\<^sub>e"
  apply (expr_auto)
  using assms by auto

(* The use of @{term card} implies (UNIV::'b set) is finite *)
lemma iverson_bracket_card:
  fixes P::"'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "finite (UNIV::'b set)"
  shows "(card {m. P m})\<^sub>e = (\<Sum> m|True. (\<lbrakk>(P \<guillemotleft>m\<guillemotright>)\<^sub>e\<rbrakk>\<^sub>\<I>))\<^sub>e"
  apply (expr_auto)
proof -
  fix x::"'a"
  let ?P = "\<lambda>m. if P x m then 1::\<real> else (0::\<real>)"
  have f1: "(\<Sum>m::'b\<in>UNIV. if P x m then 1::\<real> else (0::\<real>)) = 
        (\<Sum>m::'b\<in>{m. \<not> P x m} \<union> {m. P x m}. ?P m)"
    by (simp add: Un_def)
  have f2: "... = sum ?P {m. P x m} + 
      sum (\<lambda>m. if P x m then 1::\<real> else (0::\<real>)) {m. \<not>P x m}"
    apply (subst sum_Un)
    apply (metis assms boolean_algebra.disj_cancel_left finite_Un)
    apply (metis assms finite_Un ref_lattice.inf_bot_right)
    using sum.not_neutral_contains_not_neutral by auto
    
  show "(real (card (Collect (P x))) = (\<Sum>m::'b\<in>UNIV. ?P m))"
    using f1 f2 by force
qed

lemma iverson_bracket_summation:
  fixes P::"'s \<Rightarrow> bool"
  assumes "finite (UNIV::'s set)"
  shows "(\<Sum> m|True. (f * \<lbrakk>P\<rbrakk>\<^sub>\<I>)\<^sub>e m) = (\<Sum> m|P m. (f)\<^sub>e m)"
proof -
  let ?P = "\<lambda>m. (if P m then 1::\<real> else (0::\<real>))"
  have f1: "(\<Sum>m::'s\<in>UNIV. f m * ?P m) = (\<Sum>m::'s\<in>{m. \<not> P m} \<union> {m. P m}. f m * ?P m)"
    by (simp add: Un_def)
  have f2: "... = (\<Sum>m::'s\<in>{m. \<not> P m}. f m * ?P m) + (\<Sum>m::'s\<in>{m. P m}. f m * ?P m)"
    apply (subst sum_Un)
    apply (meson assms rev_finite_subset subset_UNIV)
    apply (meson assms rev_finite_subset subset_UNIV)
    using sum.not_neutral_contains_not_neutral by auto
  show ?thesis
    apply (simp add: expr_defs)
    by (simp add: f1 f2)
qed

lemma iverson_bracket_product:
  fixes P::"'s \<Rightarrow> bool"
  assumes "finite (UNIV::'s set)"
  shows "(\<Prod> m|True. (f ^ (\<guillemotleft>nat_of_real_1\<guillemotright> \<lbrakk>P\<rbrakk>\<^sub>\<I>))\<^sub>e m) = (\<Prod> m|P m. (f)\<^sub>e m)"
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
  "(\<guillemotleft>max\<guillemotright> \<guillemotleft>(x)\<guillemotright> \<guillemotleft>y\<guillemotright>)\<^sub>e = (\<guillemotleft>x\<guillemotright> * (\<lbrakk>(\<guillemotleft>x\<guillemotright> > \<guillemotleft>y\<guillemotright>)\<^sub>e\<rbrakk>\<^sub>\<I>) + \<guillemotleft>y\<guillemotright> * (\<lbrakk>(\<guillemotleft>x\<guillemotright> \<le> \<guillemotleft>y\<guillemotright>)\<^sub>e\<rbrakk>\<^sub>\<I>))\<^sub>e"
  (*"(\<guillemotleft>max\<guillemotright> \<guillemotleft>(x)\<guillemotright> \<guillemotleft>y\<guillemotright>) = (\<forall>s. (\<guillemotleft>x\<guillemotright> * (\<lbrakk>(\<guillemotleft>x\<guillemotright> > \<guillemotleft>y\<guillemotright>)\<^sub>e\<rbrakk>\<^sub>\<I> s) + \<guillemotleft>y\<guillemotright> * (\<lbrakk>(\<guillemotleft>x\<guillemotright> \<le> \<guillemotleft>y\<guillemotright>)\<^sub>e\<rbrakk>\<^sub>\<I> s)))"*)
  by (expr_auto)

lemma min_iverson_bracket:
  "(\<guillemotleft>min\<guillemotright> \<guillemotleft>(x)\<guillemotright> \<guillemotleft>y\<guillemotright>)\<^sub>e = (\<guillemotleft>x\<guillemotright> * (\<lbrakk>(\<guillemotleft>x\<guillemotright> \<le> \<guillemotleft>y\<guillemotright>)\<^sub>e\<rbrakk>\<^sub>\<I>) + \<guillemotleft>y\<guillemotright> * (\<lbrakk>(\<guillemotleft>x\<guillemotright> > \<guillemotleft>y\<guillemotright>)\<^sub>e\<rbrakk>\<^sub>\<I>))\<^sub>e"
  by (expr_auto)

(* Floor and ceiling functions *)
lemma floor_iverson_bracket:
  "(\<lfloor>\<guillemotleft>x\<guillemotright>\<rfloor>)\<^sub>e = (\<Sum>n|True. n*\<lbrakk>((real_of_int) \<guillemotleft>n\<guillemotright> \<le> \<guillemotleft>x\<guillemotright> \<and> \<guillemotleft>x\<guillemotright> < (real_of_int) (\<guillemotleft>n\<guillemotright>+1))\<^sub>e\<rbrakk>\<^sub>\<I>)\<^sub>e"
  apply (expr_auto)
  oops

lemma ceiling_iverson_bracket:
  "(\<lceil>\<guillemotleft>x\<guillemotright>\<rceil>)\<^sub>e = (\<Sum>n|True. n*\<lbrakk>((real_of_int) \<guillemotleft>n-1\<guillemotright> < \<guillemotleft>x\<guillemotright> \<and> \<guillemotleft>x\<guillemotright> \<le> (real_of_int) (\<guillemotleft>n\<guillemotright>))\<^sub>e\<rbrakk>\<^sub>\<I>)\<^sub>e"
  apply (expr_auto)
  oops

subsection \<open> Inverse Iverson Bracket \<close>
term "`(N \<le> \<lbrakk>P\<rbrakk>\<^sub>\<I>)`"
axiomatization iverson_bracket_inv :: "('s \<Rightarrow> real) \<Rightarrow> 's pred" ("\<^bold>\<langle>_\<^bold>\<rangle>\<^sub>\<I>") where 
iverson_bracket_inv_def: "(\<lbrakk>\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> (P)\<^sub>u) = `(N \<le> \<lbrakk>P\<rbrakk>\<^sub>\<I>)`"

expr_ctr iverson_bracket_inv

lemma false_0: "\<lbrakk>(false)\<^sub>e\<rbrakk>\<^sub>\<I> = (0)\<^sub>e"
  by (simp add: iverson_bracket_def)

term "(\<not> \<lbrakk>\<^bold>\<langle>(1)\<^sub>e\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u)"
term "\<lbrakk>\<^bold>\<langle>(1)\<^sub>e\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u = true"
(* Here (1::\<real>) is a constant and (1)\<^sub>e inside `_` cannot automatically become "(1)\<^sub>e s". 
 So `@((1)\<^sub>e) ... ` will be expanded to "\<forall>s. (\<lambda>ss. 1::\<real>) s ..."*)
term "`(@((1)\<^sub>e) \<le> \<lbrakk>(false)\<^sub>e\<rbrakk>\<^sub>\<I>)`"
lemma iverson_bracket_inv_1: "\<^bold>\<langle>(1)\<^sub>e\<^bold>\<rangle>\<^sub>\<I> = (true)\<^sub>e"
proof -
  (*have 1: "(\<lbrakk>\<^bold>\<langle>(1)\<^sub>e\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> (false)\<^sub>u) = `(@((1)\<^sub>e) \<le> \<lbrakk>(false)\<^sub>e\<rbrakk>\<^sub>\<I>)`"
    by (smt (verit) SEXP_def false_0 iverson_bracket_inv_def taut_def)
  then have 2: "(\<lbrakk>\<^bold>\<langle>(1)\<^sub>e\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> false) = (1 \<le> (0::real))"
    by (simp add: false_0)
  then have 3: "(\<lbrakk>\<^bold>\<langle>(1)\<^sub>e\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> false) = false"
    by simp
  (* A \<sqsupseteq> false \<longrightarrow> \<not> (A \<subseteq> {}) *)
  then have 4: "\<not> ((\<lbrakk>\<^bold>\<langle>(1)\<^sub>e\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> false))"
    by simp
  then *)
  have "\<lbrakk>\<^bold>\<langle>(1)\<^sub>e\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u = true"
    by (smt (verit, best) Collect_cong SEXP_def UNIV_def iverson_bracket_def iverson_bracket_inv_def 
        pred_set_def ref_order.order_refl taut_def true_pred_def)
  then show ?thesis
    by (metis pred_UNIV pred_set true_pred_def)
qed

lemma iverson_bracket_inv_0: "\<^bold>\<langle>(0)\<^sub>e\<^bold>\<rangle>\<^sub>\<I> = (false)\<^sub>e"
  by (smt (verit, ccfv_SIG) SEXP_def false_0 iverson_bracket_inv_def pred_ba.bot.extremum 
      pred_ba.order_eq_iff pred_set taut_def true_false_pred_expr(2))
(*
proof -
  have 1: "(\<lbrakk>\<^bold>\<langle>(0)\<^sub>e\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> (false)\<^sub>u) = `(@((0)\<^sub>e) \<le> \<lbrakk>(false)\<^sub>e\<rbrakk>\<^sub>\<I>)`"
    by (smt (verit, ccfv_threshold) SEXP_def false_0 iverson_bracket_inv_def taut_def)
  have 2: "(\<lbrakk>\<^bold>\<langle>(0)\<^sub>e\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> false) = (\<forall>s. 0 \<le> (0::real))"
    using 1 by (simp add: false_0)
  then have 3: "(\<lbrakk>\<^bold>\<langle>(0)\<^sub>e\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> false) = true"
    by simp
  then show ?thesis
    by (metis false_pred_def pred_ba.bot.extremum_uniqueI pred_empty pred_set)
qed
*)

lemma iverson_bracket_approximate_inverse: "`N \<le> \<lbrakk>\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>\<I>`"
  by (metis SEXP_def iverson_bracket_inv_def ref_order.order_refl)
(*
proof -
  have 1: "(\<lbrakk>\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> \<lbrakk>\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u) = `N \<le> \<lbrakk>\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>\<I>`"
    using iverson_bracket_inv_def
    by (metis SEXP_def ref_order.order_refl)
  then show ?thesis
    by auto
qed
*)

lemma iverson_bracket_inv_approximate_inverse: "(\<lbrakk>\<^bold>\<langle>\<lbrakk>P\<rbrakk>\<^sub>\<I>\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> (P)\<^sub>u)"
  using iverson_bracket_inv_def by fastforce
(*
proof -
  have 1: "(\<lbrakk>\<^bold>\<langle>\<lbrakk>P\<rbrakk>\<^sub>\<I>\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> (P)\<^sub>u) = `(\<lbrakk>P\<rbrakk>\<^sub>\<I> \<le> \<lbrakk>P\<rbrakk>\<^sub>\<I>)`"
    using iverson_bracket_inv_def
    by blast
  then show ?thesis
    by auto
qed
*)

term "(\<forall>s. \<not>(\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I> s))"
term "`\<not>(\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>)`"
lemma iverson_bracket_inv_N_0:
  assumes "`N \<ge> 0`"
  shows "`\<not>(\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>)` = `N = 0`"
proof -
  have 1: "(\<lbrakk>\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> (false)\<^sub>u) = `N \<le> \<lbrakk>(false)\<^sub>e\<rbrakk>\<^sub>\<I>`"
    using iverson_bracket_inv_def
    by force
  have 2: "(\<lbrakk>\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> false) = `N \<le> 0`"
    using 1 by (simp add: false_0)
  then have 3: "(\<lbrakk>\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> false) = `N = 0`"
    using assms nle_le by (smt (verit) SEXP_def taut_def)
  then have 4: "(\<lbrakk>\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u = false) = `N = 0`"
    by (simp add: pred_ba.bot.extremum_unique)
  then show ?thesis
    by (simp add: false_pred_def pred_set_def taut_def)
qed

term "`(M \<le> N)`"
lemma iverson_bracket_inv_mono: "\<lbrakk> `(M \<le> N)` \<rbrakk> \<Longrightarrow> \<lbrakk>\<^bold>\<langle>M\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u \<sqsupseteq> \<lbrakk>\<^bold>\<langle>N\<^bold>\<rangle>\<^sub>\<I>\<rbrakk>\<^sub>u"
  apply (expr_auto)
  by (metis (no_types, lifting) SEXP_def dual_order.trans iverson_bracket_approximate_inverse 
      iverson_bracket_inv_def pred_set_def taut_def)
  

end
