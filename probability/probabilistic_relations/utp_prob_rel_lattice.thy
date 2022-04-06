section \<open> Probabilistic relation programming \<close>

theory utp_prob_rel_lattice
  imports 
    (* "HOL.Series" *)
    "HOL-Analysis.Infinite_Sum" 
    "utp_iverson_bracket" 
    "utp_distribution"
    "infsum_laws"
begin 

unbundle UTP_Syntax

declare [[show_types]]

named_theorems pfun_defs and ureal_defs

subsection \<open> Design decisions \<close>

(* Should we use ennreal or ereal or even ureal?
  ereal: complete_linorder (linorder + complete_lattice), but ; is not mono. 
    Consider negative values for the subgoal of pseqcomp_mono.
    (P\<^sub>1 \<le> P\<^sub>2 \<Longrightarrow> Q\<^sub>1 \<le> Q\<^sub>2 \<Longrightarrow> x \<in> UNIV \<Longrightarrow> P\<^sub>1 (a, x) * Q\<^sub>1 (x, b) \<le> P\<^sub>2 (a, x) * Q\<^sub>2 (x, b))

  ennreal: complete_linorder, but ; is not mono
    Consider the subgoal of pseqcomp_mono. Using infsum_mono, we need to prove both sides are summable_on
      P\<^sub>1 \<le> P\<^sub>2 \<Longrightarrow> Q\<^sub>1 \<le> Q\<^sub>2 \<Longrightarrow>
         (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. P\<^sub>1 (a, v\<^sub>0) * Q\<^sub>1 (v\<^sub>0, b)) \<le> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. P\<^sub>2 (a, v\<^sub>0) * Q\<^sub>2 (v\<^sub>0, b))
    So we need to add assms that both "(\<lambda>v\<^sub>0::'a. P\<^sub>1 (a, v\<^sub>0) * Q\<^sub>1 (v\<^sub>0, b)) summable_on UNIV" and 
      "(\<lambda>v\<^sub>0::'a. P\<^sub>2 (a, v\<^sub>0) * Q\<^sub>2 (v\<^sub>0, b)) summable_on UNIV"
    However, in order to prove the loop body is mono: "mono (\<lambda>X. (P ; X) \<lhd>\<^sub>f b \<rhd> II)", one subgoal is 
      "\<forall>X. (\<lambda>v\<^sub>0::'a time_scheme. P (a, v\<^sub>0) * X (v\<^sub>0, b)) summable_on UNIV"
    We consider P is a probability distribution, (so P summable), but (P * X) is not necessary to 
    be summable for all X.

  ureal (probability):
    So if P\<^sub>1 summable, then (P\<^sub>1 (a, v\<^sub>0) * Q\<^sub>1 (v\<^sub>0, b)) summable. (if P\<^sub>1 is a distribution, then P\<^sub>1 summable).
    Since now X is ureal valued-functions, (P * X) is summable.
    But for parallel composition, both P and Q in P \<parallel> Q are not necessary to be ureal. But its result is
    probability.

  pdfun: probabilistic distribution functions:
    But pdfun cannot be compared using \<le>, so they don't form a complete lattice.
    
*)
type_synonym ('s\<^sub>1, 's\<^sub>2) rvfun = "(real, 's\<^sub>1 \<times> 's\<^sub>2) expr"
type_synonym 's rvhfun = "('s, 's) rvfun"

subsection \<open> Real numbers or non-negative extended real numbers \<close>
(*
type_synonym ('s\<^sub>1, 's\<^sub>2) erfun = "(ennreal, 's\<^sub>1 \<times> 's\<^sub>2) expr"
type_synonym 's erhfun = "('s, 's) erfun"

subsection \<open> Syntax \<close>
definition zero :: "'s erhfun" where
"zero = (0)\<^sub>e"

definition one :: "'s erhfun" where
"one = (1)\<^sub>e"

definition pskip :: "'s erhfun" ("II\<^sub>p") where
[pfun_defs]: "pskip = (\<lbrakk> \<lbrakk>II\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"

adhoc_overloading
  uskip pskip

term "II::'s rel"
term "II::'s erhfun"

definition passigns :: "('a, 'b) psubst \<Rightarrow> ('a, 'b) erfun" where 
[pfun_defs]: "passigns \<sigma> = (\<lbrakk> \<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"

adhoc_overloading
  uassigns passigns

term "(s := e)::'s erhfun"
term "(s := e)::'s rel"

definition pchoice :: "('s\<^sub>1, 's\<^sub>2) erfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun" 
  ("(_ \<oplus>\<^bsub>_\<^esub> _)" [61, 0, 60] 60) where
[pfun_defs]: "pchoice P r Q = ((r * P + (1 - r) * Q))\<^sub>e"

(* definition pchoice' :: "'s rfhrel \<Rightarrow> ('s, 's) erfun \<Rightarrow> ('s, 's) erfun \<Rightarrow> ('s, 's) erfun" 
    ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 0, 167] 167) where
[pfun_defs]: "pchoice' r P Q = real2ureal (r * @(rfrel_of_erfun P) + (1 - r) * @(rfrel_of_erfun Q))\<^sub>e"
*)

syntax 
  "_pchoice" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 61, 60] 60) 

translations
  "_pchoice r P Q" == "CONST pchoice P (r)\<^sub>e Q"
  "_pchoice r P Q" <= "_pchoice (r)\<^sub>e P Q"

term "if\<^sub>p 0.5 then P else Q"
term "if\<^sub>p R then P else Q"
term "if\<^sub>p R then P else Q = if\<^sub>p R then P else Q"

abbreviation pcond_f :: "('s\<^sub>1, 's\<^sub>2) erfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rpred \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun" 
("(3_ \<lhd>\<^sub>f _ \<rhd>/ _)" [61,0,60] 60) where 
"pcond_f P b Q \<equiv> (if b then P else Q)\<^sub>e"

(*TODO: should be this type, but I cannot make it type correct.
definition pseqcomp ::"('s\<^sub>1, 's\<^sub>2) erfun \<Rightarrow> ('s\<^sub>2, 's\<^sub>3) erfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>3) erfun" (infixl ";\<^sub>f" 59) where *)

definition pseqcomp ::"'s erhfun \<Rightarrow> 's erhfun \<Rightarrow> 's erhfun" (infixl ";\<^sub>f" 59) where
[pfun_defs]: "pseqcomp P Q = 
  (\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> (P)) * ([ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> (Q)))\<^sub>e"

consts
  pseqcomp_c :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl ";" 59)
adhoc_overloading
  pseqcomp_c pseqcomp

term "(P::'s erhfun) ; Q"

text \<open> Considering recursions @{text "X = P ; X"}, zero is one of its solution. But this solution is 
not very useful.  
\<close>
alphabet time = 
  t :: nat

term "lfp (\<lambda>X. (P::'s erhfun))"

definition pwhile :: "('a time_scheme \<times> 'a time_scheme \<Rightarrow> \<bool>) \<Rightarrow> 'a time_scheme erhfun 
  \<Rightarrow> 'a time_scheme erhfun" 
("while\<^sub>p _ do _ od") where
"pwhile b P = (\<nu> X \<bullet> ((P ; X) \<lhd>\<^sub>f b \<rhd> II))"

print_locale "complete_lattice"

lemma "(\<lambda>s. 1) < (\<lambda>s. 2::ereal)"
  by (simp add: less_fun_def le_fun_def)

lemma pcond_mono: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2; Q\<^sub>1 \<le> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (P\<^sub>1 \<lhd>\<^sub>f b \<rhd> Q\<^sub>1) \<le> (P\<^sub>2 \<lhd>\<^sub>f b \<rhd> Q\<^sub>2)"
  by (smt (verit, best) SEXP_def le_funE le_funI)

lemma pseqcomp_mono: 
  assumes "\<forall>a b. (\<lambda>v\<^sub>0::'a. P\<^sub>1 (a, v\<^sub>0) * Q\<^sub>1 (v\<^sub>0, b)) summable_on UNIV"
  assumes "\<forall>a b. (\<lambda>v\<^sub>0::'a. P\<^sub>2 (a, v\<^sub>0) * Q\<^sub>2 (v\<^sub>0, b)) summable_on UNIV"
  shows "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2; Q\<^sub>1 \<le> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (P\<^sub>1 ; Q\<^sub>1) \<le> (P\<^sub>2 ; Q\<^sub>2)"
  apply (simp add: pfun_defs)
  apply (rule le_funI)
  apply (rel_auto)
  apply (rule infsum_mono)
  apply (simp add: assms)
  apply (simp add: assms)
proof -
  fix a b x::"'a"
  assume a1: "P\<^sub>1 \<le> P\<^sub>2"
  assume a2: "Q\<^sub>1 \<le> Q\<^sub>2"
  assume a3: "x \<in> UNIV"
  from a1 have f1: "P\<^sub>1 (a, x) \<le> P\<^sub>2 (a, x)"
    by (simp add: le_funD)
  from a2 have f2: "Q\<^sub>1 (x, b) \<le> Q\<^sub>2 (x, b)"
    by (simp add: le_funD)
  have "P\<^sub>1 (a, x) * Q\<^sub>1 (x, b) \<le> P\<^sub>2 (a, x) * Q\<^sub>1 (x, b)"
    using a1 by (simp add: f1 mult_right_mono)
  also have "P\<^sub>2 (a, x) * Q\<^sub>1 (x, b) \<le> P\<^sub>2 (a, x) * Q\<^sub>2 (x, b)"
    using a2 by (simp add: f2 mult_left_mono)
  ultimately show "P\<^sub>1 (a, x) * Q\<^sub>1 (x, b) \<le> P\<^sub>2 (a, x) * Q\<^sub>2 (x, b)"
    by (simp add: a1 a2)
qed

theorem while_unfold:
  (* assumes "\<forall>s s' Q. (\<lambda>v\<^sub>0::'a. P (s, v\<^sub>0) * Q (v\<^sub>0, s')) summable_on UNIV" *)
  shows "while\<^sub>p b do P od = ((P ; (while\<^sub>p b do P od)) \<lhd>\<^sub>f b \<rhd> II)"
proof -
  have m:"mono (\<lambda>X. (P ; X) \<lhd>\<^sub>f b \<rhd> II)"
    apply (simp add: mono_def, auto)
    apply (subst pcond_mono)
    apply (subst pseqcomp_mono)
  have "(while\<^sub>p b do P od) = (\<nu> X \<bullet> ((P ; X) \<lhd>\<^sub>f b \<rhd> II))"
    by (simp add: pwhile_def)
  also have "... = ((P ; (\<nu> X \<bullet> (P ; X) \<lhd>\<^sub>f b \<rhd> II)) \<lhd>\<^sub>f b \<rhd> II)"
    apply (subst lfp_unfold)
  also have "... = ((P \<Zcomp> while b do P od) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    by (simp add: pwhile_def)
  finally show ?thesis .
qed
*)
subsection \<open> Unit real interval and probability functions \<close>

(* Unit real interval *)
typedef ureal = "{(0::ereal)..1}"
  morphisms ureal2ereal ereal2ureal'
  apply (rule_tac x = "0" in exI)
  by auto

find_theorems name:"ureal"
term "complete_lattice_class"
term "ennreal"

definition ereal2ureal where 
[ureal_defs]: "ereal2ureal x = ereal2ureal' (min (max 0 x) 1)"

definition real2ureal where
[ureal_defs]: "real2ureal x = ereal2ureal (ereal x)"

definition ureal2real where
[ureal_defs]: "ureal2real x = (real_of_ereal \<circ> ureal2ereal) x"

lemma enn2ereal_range: "ereal2ureal ` {0..1} = UNIV"
proof -
  have "\<exists>y \<in> {0..1}. x = ereal2ureal y" for x
    apply (auto simp: ereal2ureal_def max_absorb2)
    by (meson ereal2ureal'_cases)
  then show ?thesis
    by (auto simp: image_iff Bex_def)
qed

lemma type_definition_ureal': "type_definition ureal2ereal ereal2ureal {x. 0 \<le> x \<and> x \<le> 1}"
  using type_definition_ureal
  by (auto simp: type_definition_def ereal2ureal_def max_absorb2)

setup_lifting type_definition_ureal'

declare [[coercion ereal2ureal]]

instantiation ureal :: complete_linorder
begin

lift_definition top_ureal :: ureal is 1 by simp
lift_definition bot_ureal :: ureal is 0 by simp
lift_definition sup_ureal :: "ureal \<Rightarrow> ureal \<Rightarrow> ureal" is sup by (metis le_supI le_supI1)
lift_definition inf_ureal :: "ureal \<Rightarrow> ureal \<Rightarrow> ureal" is inf by (metis le_infI le_infI1)

lift_definition Inf_ureal :: "ureal set \<Rightarrow> ureal" is "inf 1 \<circ> Inf"
  by (simp add: le_Inf_iff)

lift_definition Sup_ureal :: "ureal set \<Rightarrow> ureal" is "sup 0 \<circ> Sup"
  by (metis Sup_le_iff comp_apply sup.absorb_iff2 sup.boundedI sup.left_idem zero_less_one_ereal)

lift_definition less_eq_ureal :: "ureal \<Rightarrow> ureal \<Rightarrow> bool" is "(\<le>)" .
lift_definition less_ureal :: "ureal \<Rightarrow> ureal \<Rightarrow> bool" is "(<)" .

instance
  apply standard
  using less_eq_ureal.rep_eq less_ureal.rep_eq apply force
  apply (simp add: less_eq_ureal.rep_eq)
  using less_eq_ureal.rep_eq apply auto[1]
  apply (simp add: less_eq_ureal.rep_eq ureal2ereal_inject)
  apply (simp add: inf_ureal.rep_eq less_eq_ureal.rep_eq)+
  apply (simp add: sup_ureal.rep_eq)
  apply (simp add: less_eq_ureal.rep_eq sup_ureal.rep_eq)
  apply (simp add: less_eq_ureal.rep_eq sup_ureal.rep_eq)
  apply (smt (verit) INF_lower Inf_ureal.rep_eq le_inf_iff less_eq_ureal.rep_eq nle_le)
  using INF_greatest Inf_ureal.rep_eq less_eq_ureal.rep_eq ureal2ereal apply auto[1]
  apply (metis Sup_le_iff Sup_ureal.rep_eq image_eqI inf_sup_ord(4) less_eq_ureal.rep_eq)
  using SUP_least Sup_ureal.rep_eq less_eq_ureal.rep_eq ureal2ereal apply auto[1]
  apply (smt (verit, best) Inf_ureal.rep_eq ccInf_empty image_empty inf_top.right_neutral 
  top_ureal.rep_eq ureal2ereal_inverse)
  apply (smt (verit) Sup_ureal.rep_eq bot_ureal.rep_eq ccSup_empty image_empty sup_bot.right_neutral 
  ureal2ereal_inverse)
  using less_eq_ureal.rep_eq by force
end


print_locale "comm_semiring_1"
print_locale "semiring_1_no_zero_divisors"
(*, semiring_1_no_zero_divisors, comm_semiring_1*)
(* distrib_right and distrib_left of semiring are not true for ureal 
  
  Clearly "(a::ureal) (b::ureal) c::ureal. (a + b) * c = a * c + b * c" may not be true, such as 
    (0.7 + 0.6) * 0.7 \<noteq> 0.7 * 0.7 + 0.6 * 0.7
*)
instantiation ureal :: "{one,zero,plus,times,mult_zero,
  zero_neq_one, semigroup_mult, semigroup_add, ab_semigroup_mult, ab_semigroup_add,
  monoid_add, monoid_mult, comm_monoid_add}"
begin

lift_definition one_ureal :: ureal is 1 by simp
lift_definition zero_ureal :: ureal is 0 by simp
lift_definition plus_ureal :: "ureal \<Rightarrow> ureal \<Rightarrow> ureal" is "\<lambda>a b. min 1 (a + b)" 
  by simp
lift_definition times_ureal :: "ureal \<Rightarrow> ureal \<Rightarrow> ureal" is "(*)"
  by (metis ereal_mult_mono ereal_zero_le_0_iff mult.comm_neutral)

instance
  apply standard 
  apply (smt (verit, best) monoid.right_neutral mult.left_commute mult.monoid_axioms times_ureal.rep_eq ureal2ereal_inverse)
  apply (metis mult.commute times_ureal.rep_eq ureal2ereal_inverse)
  apply transfer
  apply (smt (verit, ccfv_threshold) add.commute add.left_commute ereal_le_add_mono2 min.absorb1 min.absorb2 nle_le)
  apply (metis add.commute plus_ureal.rep_eq ureal2ereal_inject)
  apply (smt (verit, best) atLeastAtMost_iff comm_monoid_add_class.add_0 min.absorb2 plus_ureal.rep_eq 
      ureal2ereal ureal2ereal_inject zero_ureal.rep_eq)
  using one_ureal.rep_eq times_ureal.rep_eq ureal2ereal_inject apply force
  using one_ureal.rep_eq times_ureal.rep_eq ureal2ereal_inject apply force
  using times_ureal.rep_eq ureal2ereal_inject zero_ureal.rep_eq apply force
  using times_ureal.rep_eq ureal2ereal_inject zero_ureal.rep_eq apply force
  using one_ureal.rep_eq zero_ureal.rep_eq by fastforce
end

instantiation ureal :: minus
begin

lift_definition minus_ureal :: "ureal \<Rightarrow> ureal \<Rightarrow> ureal" is "\<lambda>a b. max 0 (a - b)"
  by (simp add: ereal_diff_le_mono_left)

instance ..

end

instance ureal :: numeral ..

instantiation ureal :: linear_continuum_topology
begin

definition open_ureal :: "ureal set \<Rightarrow> bool"
  where "(open :: ureal set \<Rightarrow> bool) = generate_topology (range lessThan \<union> range greaterThan)"

instance
proof
  show "\<exists>a b::ureal. a \<noteq> b"
    using zero_neq_one by (intro exI)
  show "\<And>(x::ureal) y::ureal. x < y \<Longrightarrow> \<exists>z::ureal. x < z \<and> z < y"
  proof transfer
    fix x y :: ereal
    assume a1: "(0::ereal) \<le> x \<and> x \<le> (1::ereal)"
    assume a2: "(0::ereal) \<le> y \<and> y \<le> (1::ereal)"
    assume a3: "x < y"
    from dense[OF this] obtain z where "x < z \<and> z < y" ..
    with a1 a2 show "\<exists>z::ereal\<in>{x::ereal. (0::ereal) \<le> x \<and> x \<le> (1::ereal)}. x < z \<and> z < y"
      by (intro bexI[of _ z]) (auto)
  qed
qed (rule open_ureal_def)

end

instance ureal :: ordered_comm_monoid_add 
proof 
  fix a b c::"ureal"
  assume *: "a \<le> b"
  then show "c + a \<le> c + b"
    by (smt (verit, best) Orderings.order_eq_iff ereal_add_le_add_iff less_eq_ureal.rep_eq min.mono plus_ureal.rep_eq)
  qed

(*
instantiation ureal :: inverse
begin

lift_definition inverse_ureal :: "ureal \<Rightarrow> ureal" is inverse

definition divide_ureal :: "ureal \<Rightarrow> ureal \<Rightarrow> ureal"
  where "x div y = x * inverse (y :: ureal)"

instance ..

end
*)

  subsubsection \<open> Probability functions \<close>
type_synonym ('s\<^sub>1, 's\<^sub>2) rfrel = "(\<real>, 's\<^sub>1 \<times> 's\<^sub>2) expr"
type_synonym 's rfhrel = "('s, 's) rfrel"

type_synonym ('s\<^sub>1, 's\<^sub>2) erfun = "(ureal, 's\<^sub>1 \<times> 's\<^sub>2) expr"
type_synonym 's erhfun = "('s, 's) erfun"

definition erfun_of_rfrel:: "('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun" where
[ureal_defs]: "erfun_of_rfrel f = (real2ureal f)\<^sub>e "

thm "erfun_of_rfrel_def"

definition rfrel_of_erfun where
[ureal_defs]: "rfrel_of_erfun f = (ureal2real f)\<^sub>e "

subsection \<open> Syntax \<close>

(* deadlock: zero and not a distribution *)
abbreviation zero_f ("0\<^sub>f") where
  "zero_f \<equiv> (\<lambda> s. 0::\<real>)"

(* This is underspecified and could be assigned an arbitrary value. 
TODO: How to deal with this?
*)
definition pzero :: "('s\<^sub>1, 's\<^sub>2) erfun" ("0\<^sub>p") where
[pfun_defs]: "pzero = erfun_of_rfrel zero_f"

(*
lemma deadlock_always: "`@(deadlock_state pzero)`"
  apply (simp add: pfun_defs)
  by (simp add: is_prob_def real2ureal_inverse)
*)

subsubsection \<open> Skip \<close>
(* The purpose of this abbreviation is to make later reference to this function inside pskip easier. *)
abbreviation pskip\<^sub>_f ("II\<^sub>f") where
  "pskip\<^sub>_f \<equiv> \<lbrakk> \<lbrakk>II\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>"

definition pskip :: "'s erhfun" ("II\<^sub>p") where
[pfun_defs]: "pskip = erfun_of_rfrel (pskip\<^sub>_f)"

adhoc_overloading
  uskip pskip

term "II::'s rel"
term "II::'s erhfun"
term "x := ($x + 1)"
term "x\<^sup>> := ($x\<^sup>< + 1)"

subsubsection \<open> Assignment \<close>
abbreviation passigns_f where 
"passigns_f \<sigma> \<equiv> \<lbrakk> \<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>"

definition passigns :: "('a, 'b) psubst \<Rightarrow> ('a, 'b) erfun" where 
[pfun_defs]: "passigns \<sigma> = erfun_of_rfrel (passigns_f \<sigma>)"

adhoc_overloading
  uassigns passigns

term "(s := e)::'s erhfun"
term "(s := e)::'s rel"

subsubsection \<open> Probabilistic choice \<close>
abbreviation pchoice_f :: "('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel" 
("(_ \<oplus>\<^sub>f\<^bsub>_\<^esub> _)" [61, 0, 60] 60) where 
"pchoice_f P r Q \<equiv> (r * P + (1 - r) * Q)\<^sub>e"

definition pchoice :: "('s\<^sub>1, 's\<^sub>2) erfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun" 
  ("(_ \<oplus>\<^bsub>_\<^esub> _)" [61, 0, 60] 60) where
[pfun_defs]: "pchoice P r Q = erfun_of_rfrel (pchoice_f (rfrel_of_erfun P) r (rfrel_of_erfun Q))"

(* definition pchoice' :: "'s rfhrel \<Rightarrow> ('s, 's) erfun \<Rightarrow> ('s, 's) erfun \<Rightarrow> ('s, 's) erfun" 
    ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 0, 167] 167) where
[pfun_defs]: "pchoice' r P Q = real2ureal (r * @(rfrel_of_erfun P) + (1 - r) * @(rfrel_of_erfun Q))\<^sub>e"
*)

syntax 
  "_pchoice" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 61, 60] 60) 

translations
  "_pchoice r P Q" == "CONST pchoice P (r)\<^sub>e Q"
  "_pchoice r P Q" <= "_pchoice (r)\<^sub>e P Q"

term "if\<^sub>p 0.5 then P else Q"
term "if\<^sub>p R then P else Q"
term "if\<^sub>p R then P else Q = if\<^sub>p R then P else Q"

text \<open> The definition @{text "lift_pre"} below lifts a real-valued function @{text r} over the initial 
state to over the initial and final states. In the definition of @{term "pchoice"}, we use a general 
function for the weight @{text r}, which is @{text "'s \<times> 's \<Rightarrow> \<real>"}. However, now we only consider 
the probabilistic choice whose weight is only over the initial state. Then @{text "lift_pre"} is 
useful to lift a such function to a more general function used in @{term "pchoice"}.
\<close>
abbreviation lift_pre where "lift_pre r \<equiv> (\<lambda>(s, s'). r s)"
notation lift_pre ("_\<^sup>\<Up>")
expr_ctr lift_pre

subsubsection \<open> Conditional choice \<close>
(* conditional choice *)
abbreviation pcond_f :: "('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rpred \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel" 
("(3_ \<lhd>\<^sub>f _ \<rhd>/ _)" [61,0,60] 60) where 
"pcond_f P b Q \<equiv> (if b then P else Q)\<^sub>e"

definition pcond :: "('s\<^sub>1, 's\<^sub>2) rpred \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun" where 
[pfun_defs]: "pcond b P Q \<equiv> erfun_of_rfrel (pcond_f (rfrel_of_erfun P) b (rfrel_of_erfun Q))"

syntax 
  "_pcond" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(if\<^sub>c (_)/ then (_)/ else (_))" [0, 61, 60] 60) 

translations
  "_pcond b P Q" == "CONST pcond (b)\<^sub>e P Q"
  "_pcond b P Q" <= "_pcond (b)\<^sub>e P Q"

term "if\<^sub>c True then P else Q"

subsubsection \<open> Sequential composition \<close>
term "(rfrel_of_erfun (P::('s erhfun)))\<lbrakk>v\<^sub>0/\<^bold>v\<^sup>>\<rbrakk>"
term "\<^bold>v\<^sup>>"
term "(\<Sum>\<^sub>\<infinity> v\<^sub>0. (P\<lbrakk>\<guillemotleft>v\<^sub>0\<guillemotright>/\<^bold>v\<^sup>>\<rbrakk>) * (Q\<lbrakk>\<guillemotleft>v\<^sub>0\<guillemotright>/\<^bold>v\<^sup><\<rbrakk>))\<^sub>e"
term "[ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> (rfrel_of_erfun (P::'s erhfun))"
term "(\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> P) * ([ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> Q))\<^sub>e"
term "(\<exists> v\<^sub>0. [ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> \<lbrakk>P\<rbrakk>\<^sub>P \<and> [ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> \<lbrakk>Q\<rbrakk>\<^sub>P)\<^sub>e"
term "if True then a else b"
term " 
  (\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> v\<^sub>0 ] \<dagger> @(rfrel_of_erfun P)) * ([ \<^bold>v\<^sup>< \<leadsto> v\<^sub>0 ] \<dagger> @(rfrel_of_erfun Q)))\<^sub>e"
thm "pred_seq_hom"

abbreviation pseqcomp_f :: "'s rfhrel \<Rightarrow> 's rfhrel \<Rightarrow> 's rfhrel" (infixl ";\<^sub>f" 59) where 
"pseqcomp_f P Q \<equiv> (\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> P) * ([ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> Q))\<^sub>e" 

definition pseqcomp :: "'s erhfun \<Rightarrow> 's erhfun \<Rightarrow> 's erhfun" (*(infixl ";\<^sub>p" 59)*) where
[pfun_defs]: "pseqcomp P Q = erfun_of_rfrel (pseqcomp_f (rfrel_of_erfun P) (rfrel_of_erfun Q))"

consts
  pseqcomp_c :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl ";" 59)
adhoc_overloading
  pseqcomp_c pseqcomp_f and 
  pseqcomp_c pseqcomp

term "(P::('s, 's) rfrel) ; Q"
term "(P::'s erhfun) ; Q"

subsubsection \<open> Parallel composition \<close>

abbreviation pparallel_f :: "('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel" (infixl "\<parallel>\<^sub>f" 58)
  where "pparallel_f P Q \<equiv> (\<^bold>N (P * Q)\<^sub>e)"

abbreviation pparallel_f' :: "('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel"
  where "pparallel_f' P Q \<equiv> ((P * Q) / (\<Sum>\<^sub>\<infinity> s'. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>s'\<guillemotright> ] \<dagger> P) * ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>s'\<guillemotright> ] \<dagger> Q)))\<^sub>e"

lemma pparallel_f_eq: "pparallel_f P Q = pparallel_f' P Q"
  apply (simp add: dist_defs)
  by (expr_auto)

text \<open> We provide four variants (different combinations of types for their parameters) of parallel 
composition for convenience and they use a same notation @{text "\<parallel>"}. All of them defines 
probabilistic programs of type @{typ "('a\<^sub>1, 'a\<^sub>2) erfun"}.
\<close>
definition pparallel :: "('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun" (infixl "\<parallel>\<^sub>p" 58) where
[pfun_defs]: "pparallel P Q = erfun_of_rfrel (pparallel_f P Q)"

definition pparallel_pp :: "('s\<^sub>1, 's\<^sub>2) erfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun" where
[pfun_defs]: "pparallel_pp P Q = pparallel (rfrel_of_erfun P) (rfrel_of_erfun Q)"

definition pparallel_fp :: "('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun" where
[pfun_defs]: "pparallel_fp P Q = pparallel P (rfrel_of_erfun Q)"

definition pparallel_pf :: "('s\<^sub>1, 's\<^sub>2) erfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun" where
[pfun_defs]: "pparallel_pf P Q = pparallel (rfrel_of_erfun P) Q"

no_notation Sublist.parallel (infixl "\<parallel>" 50)
consts
  parallel_c :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<parallel>" 58)

adhoc_overloading
  parallel_c pparallel and 
  parallel_c pparallel_pp and
  parallel_c pparallel_fp and
  parallel_c pparallel_pf and
  parallel_c Sublist.parallel

term "((P::('s, 's) rfrel) \<parallel> (Q::('s, 's) rfrel))"
term "((P::('s, 's) rfrel) \<parallel> (Q::('s, 's) erfun))"
term "((P::('s, 's) erfun) \<parallel> (Q::('s, 's) rfrel))"
term "((P::('s, 's) erfun) \<parallel> (Q::('s, 's) erfun))"
term "((P::'s list) \<parallel> Q)"
term "([] \<parallel> [a])"

subsubsection \<open> Recursion \<close>
alphabet time = 
  t :: nat

term "lfp (\<lambda>X. (P::'s erhfun))"

definition pwhile :: "('a time_scheme \<times> 'a time_scheme \<Rightarrow> \<bool>) \<Rightarrow> 'a time_scheme erhfun 
  \<Rightarrow> 'a time_scheme erhfun" 
("while\<^sub>p _ do _ od") where
"pwhile b P = (\<nu> X \<bullet> (if\<^sub>c b then (P ; X) else II))"

print_locale "complete_lattice"

lemma pcond_mono: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2; Q\<^sub>1 \<le> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (if\<^sub>c b then P\<^sub>1 else Q\<^sub>1) \<le> (if\<^sub>c b then P\<^sub>2 else Q\<^sub>2)"
  apply (simp add: pcond_def ureal_defs)
  apply (simp add: le_fun_def)
  apply (auto)
  apply (simp add: ureal_defs)
  apply (smt (z3) atLeastAtMost_iff ereal_less_eq(1) ereal_less_eq(4) ereal_real ereal_times(1) 
      max.absorb1 max.absorb2 min.absorb1 real_of_ereal_le_0 ureal2ereal ureal2ereal_inverse)
  apply (simp add: ureal_defs)
  by (smt (z3) atLeastAtMost_iff ereal_less_eq(1) ereal_less_eq(4) ereal_real ereal_times(1) 
      max.absorb1 max.absorb2 min.absorb1 real_of_ereal_le_0 ureal2ereal ureal2ereal_inverse)

print_classes
lemma pseqcomp_mono: 
  fixes P\<^sub>1 :: "'s erhfun"
  assumes "\<forall>a b. (\<lambda>v\<^sub>0::'s. real_of_ereal 
    (ureal2ereal (P\<^sub>1 (a, v\<^sub>0))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (v\<^sub>0, b)))) summable_on UNIV"
  assumes "\<forall>a b. (\<lambda>v\<^sub>0::'s. real_of_ereal 
    (ureal2ereal (P\<^sub>2 (a, v\<^sub>0))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (v\<^sub>0, b)))) summable_on UNIV"
  shows "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2; Q\<^sub>1 \<le> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (P\<^sub>1 ; Q\<^sub>1) \<le> (P\<^sub>2 ; Q\<^sub>2)"
  apply (simp add: pfun_defs)
  apply (simp add: le_fun_def)
  apply (simp add: ureal_defs)
  apply (expr_auto)
proof -
  fix a b :: "'s"
  assume a1: "\<forall>(a::'s) b::'s. P\<^sub>1 (a, b) \<le> P\<^sub>2 (a, b)"
  assume a2: "\<forall>(a::'s) b::'s. Q\<^sub>1 (a, b) \<le> Q\<^sub>2 (a, b)"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'s.
                real_of_ereal (ureal2ereal (P\<^sub>1 (a, v\<^sub>0))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (v\<^sub>0, b))))"
  let ?rhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::'s.
                real_of_ereal (ureal2ereal (P\<^sub>2 (a, v\<^sub>0))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (v\<^sub>0, b))))"

  have "?lhs \<le> ?rhs"
    apply (rule infsum_mono)
    apply (simp add: assms(1))
    apply (simp add: assms(2))
    by (metis a1 a2 atLeastAtMost_iff ereal_less_PInfty ereal_times(1) less_eq_ureal.rep_eq 
        linorder_not_less mult_mono real_of_ereal_pos real_of_ereal_positive_mono ureal2ereal)
  then show " ereal2ureal' (min (max (0::ereal) (ereal ?lhs)) (1::ereal)) \<le> 
       ereal2ureal' (min (max (0::ereal) (ereal ?rhs)) (1::ereal))"
  (*
  proof -
    have f1: "\<forall>e ea. min (e::ereal) ea = (if e \<le> ea then e else ea)"
      using min_def by blast
    have f2: "\<forall>e ea. (e::ereal) \<le> max e ea"
      using max.cobounded1 by blast
    have f3: "\<forall>e ea eb. (max (e::ereal) ea \<le> eb) = (e \<le> eb \<and> ea \<le> eb)"
      using max.bounded_iff by blast
    have f4: "max (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b))))) (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b))))) \<le> max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b)))))"
      by (simp add: \<open>(\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. real_of_ereal (ureal2ereal ((P\<^sub>1::'s \<times> 's \<Rightarrow> ureal) (a::'s, v\<^sub>0))) * real_of_ereal (ureal2ereal ((Q\<^sub>1::'s \<times> 's \<Rightarrow> ureal) (v\<^sub>0, b::'s)))) \<le> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. real_of_ereal (ureal2ereal ((P\<^sub>2::'s \<times> 's \<Rightarrow> ureal) (a, v\<^sub>0))) * real_of_ereal (ureal2ereal ((Q\<^sub>2::'s \<times> 's \<Rightarrow> ureal) (v\<^sub>0, b))))\<close>)
    { assume "max (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b))))) (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b))))) \<le> 1"
      moreover
      { assume "(0::ereal) \<le> 1 \<and> ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b)))) \<le> 1"
        then have "max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b))))) = (if max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b))))) \<le> 1 then max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b))))) else 1) \<and> min (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b)))))) 1 = ureal2ereal (ereal2ureal' (min (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b)))))) 1))"
          by (simp add: ereal2ureal'_inverse)
        moreover
        { assume "\<not> max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b))))) = ureal2ereal (ereal2ureal' (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b)))))))"
          then have "\<not> max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b))))) \<le> 1"
            using f2 by (smt (z3) atLeastAtMost_iff ereal2ureal'_inverse) }
        ultimately have "max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b))))) \<le> 1 \<longrightarrow> ureal2ereal (ereal2ureal' (min (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b)))))) 1)) \<le> ureal2ereal (ereal2ureal' (min (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b)))))) 1))"
          using f4 f3 f2 f1 by (smt (z3)) }
      ultimately have "max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b))))) \<le> 1 \<longrightarrow> ureal2ereal (ereal2ureal' (min (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b)))))) 1)) \<le> ureal2ereal (ereal2ureal' (min (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b)))))) 1)) \<or> \<not> (0::ereal) \<le> 1 \<or> \<not> ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b)))) \<le> 1"
        using f3 by blast }
    moreover
    { assume "\<not> max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b))))) \<le> 1"
      then have "ureal2ereal (ereal2ureal' (min (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b)))))) 1)) \<le> ureal2ereal (ereal2ureal' (min (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b)))))) 1)) \<or> ereal2ureal' (min (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>1 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>1 (s, b)))))) 1) \<le> ereal2ureal' (min (max 0 (ereal (\<Sum>\<^sub>\<infinity>s. real_of_ereal (ureal2ereal (P\<^sub>2 (a, s))) * real_of_ereal (ureal2ereal (Q\<^sub>2 (s, b)))))) 1)"
        using f3 by (smt (z3) atLeastAtMost_iff ereal2ureal'_inverse le_cases3 min_def_raw) }
    ultimately show ?thesis
      using f3 by (smt (z3) \<open>(\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. real_of_ereal (ureal2ereal ((P\<^sub>1::'s \<times> 's \<Rightarrow> ureal) (a::'s, v\<^sub>0))) * real_of_ereal (ureal2ereal ((Q\<^sub>1::'s \<times> 's \<Rightarrow> ureal) (v\<^sub>0, b::'s)))) \<le> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s. real_of_ereal (ureal2ereal ((P\<^sub>2::'s \<times> 's \<Rightarrow> ureal) (a, v\<^sub>0))) * real_of_ereal (ureal2ereal ((Q\<^sub>2::'s \<times> 's \<Rightarrow> ureal) (v\<^sub>0, b))))\<close> ereal_max less_eq_ureal.rep_eq)
  qed *)
    by (smt (z3) atLeastAtMost_iff ereal2ureal'_inverse ereal_less_eq(3) ereal_less_eq(4) 
        ereal_less_eq(7) ereal_max_0 less_eq_ureal.rep_eq linorder_le_cases max.absorb_iff2 
        min.absorb1 min.absorb2) 
qed

lemma summable_on_ureal_product:
  assumes P_summable: "(\<lambda>v\<^sub>0. real_of_ereal (ureal2ereal (P (s, v\<^sub>0)))) summable_on UNIV"
  shows "(\<lambda>v\<^sub>0::'c time_scheme. real_of_ereal (ureal2ereal (P (s, v\<^sub>0))) * 
        real_of_ereal (ureal2ereal (x (v\<^sub>0, b)))) summable_on UNIV"
  apply (subst summable_on_iff_abs_summable_on_real)
  apply (rule abs_summable_on_comparison_test[where g = "\<lambda>x. real_of_ereal (ureal2ereal (P (s, x)))"])
  apply (subst summable_on_iff_abs_summable_on_real[symmetric])
  using assms apply blast
  by (smt (verit) atLeastAtMost_iff mult_nonneg_nonneg mult_right_le_one_le real_norm_def 
      real_of_ereal_le_1 real_of_ereal_pos ureal2ereal)

theorem pwhile_unfold:
  assumes "\<forall>s. (\<lambda>v\<^sub>0. real_of_ereal (ureal2ereal (P (s, v\<^sub>0)))) summable_on UNIV"
  shows "while\<^sub>p b do P od = (if\<^sub>c b then (P ; (while\<^sub>p b do P od)) else II)"
proof -
  have m:"mono (\<lambda>X. (if\<^sub>c b then (P ; X) else II))"
    apply (simp add: mono_def, auto)
    apply (subst pcond_mono)
    apply (subst pseqcomp_mono)
    apply (auto)
    by (simp add: assms summable_on_ureal_product)+
  have "(while\<^sub>p b do P od) = (\<nu> X \<bullet> (if\<^sub>c b then (P ; X) else II))"
    by (simp add: pwhile_def)
  also have "... = ((if\<^sub>c b then (P ; (\<nu> X \<bullet> (if\<^sub>c b then (P ; X) else II))) else II))"
    apply (subst lfp_unfold)
    apply (simp add: m)
    by (simp add: lfp_const)
  also have "... = (if\<^sub>c b then (P ; (while\<^sub>p b do P od)) else II)"
    by (simp add: pwhile_def)
  finally show ?thesis .
qed

theorem pwhile_false: 
  assumes "\<forall>s. (\<lambda>v\<^sub>0. real_of_ereal (ureal2ereal (P (s, v\<^sub>0)))) summable_on UNIV"
  shows "while\<^sub>p (false)\<^sub>e do P od = II"
  apply (subst pwhile_unfold)
  using assms apply presburger
  apply (simp add: pfun_defs)
  apply (expr_auto)
  apply (simp add: ureal_defs)
  apply (auto)
  apply (simp add: ereal2ureal'_inverse)
  apply (metis ereal2ureal_def real_of_ereal_0 ureal2ereal_inverse zero_ereal_def zero_ureal.rep_eq zero_ureal_def)
  by (metis ereal2ureal_def real_of_ereal_0 ureal2ereal_inverse zero_ereal_def zero_ureal.rep_eq zero_ureal_def)

lemma fzero_zero: "rfrel_of_erfun (erfun_of_rfrel 0\<^sub>f) = 0\<^sub>f"
  apply (simp add: ureal_defs)
  by (metis SEXP_def real_of_ereal_0 ureal2ereal_inverse zero_ureal.rep_eq)

theorem pwhile_true: "while\<^sub>p (true)\<^sub>e do P od = 0\<^sub>p"
  apply (simp add: pwhile_def pcond_def pzero_def)
  apply (rule antisym)
  apply (rule lfp_lowerbound)
  apply (simp add: pseqcomp_def)
  apply (simp add: fzero_zero)
  apply (expr_auto)
  apply (simp add: fzero_zero)
  apply (simp add: ureal_defs)
  apply (smt (verit) SEXP_def atLeastAtMost_iff le_funI less_eq_ureal.rep_eq ureal2ereal ureal2ereal_inverse zero_ureal.rep_eq)
  done

(*
subsection \<open> Infsum \<close>
lemma summable_on_ureal_product: 
  fixes P :: "('s\<^sub>1, 's\<^sub>2) erfun"
  assumes "(\<lambda>v\<^sub>0. P (s, v\<^sub>0)) summable_on UNIV"
  shows "ureal2real o (\<lambda>v\<^sub>0. (P (s, v\<^sub>0))) summable_on UNIV"
  apply (simp add: summable_on_def)
  apply (simp add: has_sum_def)
  apply (rule_tac x = "ureal2real (infsum (\<lambda>v\<^sub>0. P (s, v\<^sub>0)) UNIV)" in exI)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
proof -
  fix s::'s\<^sub>1 and S::"\<bbbP> \<real>"
  assume "open S"
  assume "ureal2real (\<Sum>\<^sub>\<infinity>v\<^sub>0::'s\<^sub>2. P (s, v\<^sub>0)) \<in> S"

  have f1: "\<forall>S::\<bbbP> ureal. open S \<longrightarrow> (infsum (\<lambda>v\<^sub>0. P (s, v\<^sub>0)) UNIV) \<in> S \<longrightarrow> 
    (\<exists>X::\<bbbP> 's\<^sub>2. finite X \<and> (\<forall>Y::\<bbbP> 's\<^sub>2. finite Y \<and> X \<subseteq> Y \<longrightarrow> (\<Sum>s'::'s\<^sub>2\<in>Y. P (s, s')) \<in> S))"
  proof -
    have "has_sum (\<lambda>v\<^sub>0. P (s, v\<^sub>0)) UNIV (infsum (\<lambda>v\<^sub>0. P (s, v\<^sub>0)) UNIV)"
      by (simp add: assms)
    then have "(sum (\<lambda>v\<^sub>0. P (s, v\<^sub>0)) \<longlongrightarrow> (infsum (\<lambda>v\<^sub>0. P (s, v\<^sub>0)) UNIV)) (finite_subsets_at_top UNIV)"
      using has_sum_def by blast
    then have "\<forall>S::\<bbbP> ureal. open S \<longrightarrow> (infsum (\<lambda>v\<^sub>0. P (s, v\<^sub>0)) UNIV) \<in> S \<longrightarrow> 
        (\<forall>\<^sub>F x::\<bbbP> 's\<^sub>2 in finite_subsets_at_top UNIV. (\<Sum>s'::'s\<^sub>2\<in>x. P (s, s')) \<in> S)"
      by (simp add: tendsto_def)
    thus ?thesis
      by (simp add: eventually_finite_subsets_at_top)
  qed
  let ?S = "real2ureal ` S"
  from f1 have "open ?S \<longrightarrow> (infsum (\<lambda>v\<^sub>0. P (s, v\<^sub>0)) UNIV) \<in> ?S \<longrightarrow> 
    (\<exists>X::\<bbbP> 's\<^sub>2. finite X \<and> (\<forall>Y::\<bbbP> 's\<^sub>2. finite Y \<and> X \<subseteq> Y \<longrightarrow> (\<Sum>s'::'s\<^sub>2\<in>Y. P (s, s')) \<in> ?S))"
    by presburger

  have openS: "open ?S"
    apply (simp add: image_def real2ureal_def ereal2ureal_def)
  show "\<exists>X::\<bbbP> 's\<^sub>2. finite X \<and> (\<forall>Y::\<bbbP> 's\<^sub>2. finite Y \<and> X \<subseteq> Y \<longrightarrow> (\<Sum>x::'s\<^sub>2\<in>Y. ureal2real (P (s', x))) \<in> S)"
  qed

lemma summable_on_ureal_product: 
  fixes P :: "('s\<^sub>1, 's\<^sub>2) erfun"
  assumes "\<forall>s. (\<lambda>v\<^sub>0. P (s, v\<^sub>0)) summable_on UNIV"
  shows "\<forall>s. (\<lambda>v\<^sub>0. P (s, v\<^sub>0) * Q (s, v\<^sub>0)) summable_on UNIV"
  apply (auto)

  apply (subst summable_on_iff_abs_summable_on_real)
  apply (rule abs_summable_on_comparison_test[where g = "\<lambda>x. q (s, x)"])
  apply (subst summable_on_iff_abs_summable_on_real[symmetric])
  using assms(4) apply (metis (no_types, lifting) curry_def summable_on_cong)
*)

(*
subsection \<open> Syntax \<close>
definition zero :: "'s erhfun" where
"zero = (0)\<^sub>e"

definition one :: "'s erhfun" where
"one = (1)\<^sub>e"

definition pskip :: "'s erhfun" ("II\<^sub>p") where
[pfun_defs]: "pskip = (\<lbrakk> \<lbrakk>II\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"

adhoc_overloading
  uskip pskip

term "II::'s rel"
term "II::'s erhfun"

definition passigns :: "('a, 'b) psubst \<Rightarrow> ('a, 'b) erfun" where 
[pfun_defs]: "passigns \<sigma> = (\<lbrakk> \<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"

adhoc_overloading
  uassigns passigns

term "(s := e)::'s erhfun"
term "(s := e)::'s rel"

definition pchoice :: "('s\<^sub>1, 's\<^sub>2) erfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun" 
  ("(_ \<oplus>\<^bsub>_\<^esub> _)" [61, 0, 60] 60) where
[pfun_defs]: "pchoice P r Q = ((r * P + (1 - r) * Q))\<^sub>e"

(* definition pchoice' :: "'s rfhrel \<Rightarrow> ('s, 's) erfun \<Rightarrow> ('s, 's) erfun \<Rightarrow> ('s, 's) erfun" 
    ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 0, 167] 167) where
[pfun_defs]: "pchoice' r P Q = real2ureal (r * @(rfrel_of_erfun P) + (1 - r) * @(rfrel_of_erfun Q))\<^sub>e"
*)

syntax 
  "_pchoice" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 61, 60] 60) 

translations
  "_pchoice r P Q" == "CONST pchoice P (r)\<^sub>e Q"
  "_pchoice r P Q" <= "_pchoice (r)\<^sub>e P Q"

term "if\<^sub>p 0.5 then P else Q"
term "if\<^sub>p R then P else Q"
term "if\<^sub>p R then P else Q = if\<^sub>p R then P else Q"

abbreviation pcond_f :: "('s\<^sub>1, 's\<^sub>2) erfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rpred \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) erfun" 
("(3_ \<lhd>\<^sub>f _ \<rhd>/ _)" [61,0,60] 60) where 
"pcond_f P b Q \<equiv> (if b then P else Q)\<^sub>e"

(*TODO: should be this type, but I cannot make it type correct.
definition pseqcomp ::"('s\<^sub>1, 's\<^sub>2) erfun \<Rightarrow> ('s\<^sub>2, 's\<^sub>3) erfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>3) erfun" (infixl ";\<^sub>f" 59) where *)

definition pseqcomp ::"'s erhfun \<Rightarrow> 's erhfun \<Rightarrow> 's erhfun" (infixl ";\<^sub>f" 59) where
[pfun_defs]: "pseqcomp P Q = 
  (\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> (P)) * ([ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> (Q)))\<^sub>e"

consts
  pseqcomp_c :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl ";" 59)
adhoc_overloading
  pseqcomp_c pseqcomp

term "(P::'s erhfun) ; Q"

text \<open> Considering recursions @{text "X = P ; X"}, zero is one of its solution. But this solution is 
not very useful.  
\<close>
alphabet time = 
  t :: nat

term "lfp (\<lambda>X. (P::'s erhfun))"

definition pwhile :: "('a time_scheme \<times> 'a time_scheme \<Rightarrow> \<bool>) \<Rightarrow> 'a time_scheme erhfun 
  \<Rightarrow> 'a time_scheme erhfun" 
("while\<^sub>p _ do _ od") where
"pwhile b P = (\<nu> X \<bullet> ((P ; X) \<lhd>\<^sub>f b \<rhd> II))"

print_locale "complete_lattice"

lemma "(\<lambda>s. 1) < (\<lambda>s. 2::ereal)"
  by (simp add: less_fun_def le_fun_def)

lemma pcond_mono: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2; Q\<^sub>1 \<le> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (P\<^sub>1 \<lhd>\<^sub>f b \<rhd> Q\<^sub>1) \<le> (P\<^sub>2 \<lhd>\<^sub>f b \<rhd> Q\<^sub>2)"
  by (smt (verit, best) SEXP_def le_funE le_funI)

print_classes
lemma pseqcomp_mono: 
  assumes "\<forall>a b. (\<lambda>v\<^sub>0::'a. P\<^sub>1 (a, v\<^sub>0) * Q\<^sub>1 (v\<^sub>0, b)) summable_on UNIV"
  assumes "\<forall>a b. (\<lambda>v\<^sub>0::'a. P\<^sub>2 (a, v\<^sub>0) * Q\<^sub>2 (v\<^sub>0, b)) summable_on UNIV"
  shows "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2; Q\<^sub>1 \<le> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (P\<^sub>1 ; Q\<^sub>1) \<le> (P\<^sub>2 ; Q\<^sub>2)"
  apply (simp add: pfun_defs)
  apply (rule le_funI)
  apply (rel_auto)
  apply (rule infsum_mono)
  apply (simp add: assms)
  apply (simp add: assms)
proof -
  fix a b x::"'a"
  assume a1: "P\<^sub>1 \<le> P\<^sub>2"
  assume a2: "Q\<^sub>1 \<le> Q\<^sub>2"
  assume a3: "x \<in> UNIV"
  from a1 have f1: "P\<^sub>1 (a, x) \<le> P\<^sub>2 (a, x)"
    by (simp add: le_funD)
  from a2 have f2: "Q\<^sub>1 (x, b) \<le> Q\<^sub>2 (x, b)"
    by (simp add: le_funD)
  have "P\<^sub>1 (a, x) * Q\<^sub>1 (x, b) \<le> P\<^sub>2 (a, x) * Q\<^sub>1 (x, b)"
    using a1 ereal_mult_right_mono f1 less_eq_ureal.rep_eq times_ureal.rep_eq ureal2ereal by auto
  also have "P\<^sub>2 (a, x) * Q\<^sub>1 (x, b) \<le> P\<^sub>2 (a, x) * Q\<^sub>2 (x, b)"
    using a2 ereal_mult_left_mono f2 less_eq_ureal.rep_eq times_ureal.rep_eq ureal2ereal by auto
  ultimately show "P\<^sub>1 (a, x) * Q\<^sub>1 (x, b) \<le> P\<^sub>2 (a, x) * Q\<^sub>2 (x, b)"
    by (simp add: a1 a2)
qed

theorem while_unfold:
  assumes P_summable: "\<forall>s. (\<lambda>v\<^sub>0. P (s, v\<^sub>0)) summable_on UNIV"
  shows "while\<^sub>p b do P od = ((P ; (while\<^sub>p b do P od)) \<lhd>\<^sub>f b \<rhd> II)"
proof -
  have m:"mono (\<lambda>X. (P ; X) \<lhd>\<^sub>f b \<rhd> II)"
    apply (simp add: mono_def, auto)
    apply (subst pcond_mono)
    apply (subst pseqcomp_mono)
  have "(while\<^sub>p b do P od) = (\<nu> X \<bullet> ((P ; X) \<lhd>\<^sub>f b \<rhd> II))"
    by (simp add: pwhile_def)
  also have "... = ((P ; (\<nu> X \<bullet> (P ; X) \<lhd>\<^sub>f b \<rhd> II)) \<lhd>\<^sub>f b \<rhd> II)"
    apply (subst lfp_unfold)
  also have "... = ((P \<Zcomp> while b do P od) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    by (simp add: pwhile_def)
  finally show ?thesis .
qed
*)
subsubsection \<open> \<close>
print_classes
(*
instantiation ureal :: bot
begin
definition "bot = ereal2ureal 0"
instance by (intro_classes)
end

instantiation ureal :: top
begin
definition "top = ereal2ureal 1"
instance by (intro_classes)
end

instantiation ureal :: "{one,comm_monoid_add,zero_neq_one}"
begin

definition "0 = ereal2ureal 0"
definition "1 = ereal2ureal 1"
definition "a + b = ereal2ureal (ureal2ereal a + ureal2ereal b)"

lemma ureal_eq_0[simp]:
  "r = 0 \<longrightarrow> ereal2ureal r = 0"
  "r = 0 \<longrightarrow> 0 = ereal2ureal r"
  apply (auto)
  by (simp_all add: zero_ureal_def)

lemma ureal_eq_1[simp]:
  "r = 1 \<longrightarrow> ereal2ureal r = 1"
  "r = 1 \<longrightarrow> 1 = ereal2ureal r"
  unfolding one_ureal_def by simp_all

lemma ureal_add_zero: "(0::ureal) + a = a"
  apply (simp only: zero_ureal_def plus_ureal_def)
  by (smt (verit, ccfv_SIG) atLeastAtMost_iff ereal2ureal_inverse ureal2ereal_inverse)

lemma ureal_zero_neq_one: "0 \<noteq> (1::ureal)"
  apply (simp only: zero_ureal_def one_ureal_def)
  by (smt (verit, ccfv_threshold) atLeastAtMost_iff ereal2ureal_inject)

lemma ureal_add2: "ereal2ureal (ureal2ereal a + ureal2ereal b) = a + b"
  by (simp only: plus_ureal_def)

lemma ureal_add_commute: "(a::ureal) + b = b + a"
  apply (simp only: plus_ureal_def)
  by (smt (verit, best))

lemma ureal_add_assoc: "(a::ureal) + b + c = a + (b + c)"
  apply (simp only: plus_ureal_def)
  oops

instance  ...
apply
qed

end

instantiation ureal :: linorder
begin
  definition "x < (y::ureal) \<longleftrightarrow> ureal2ereal x < ureal2ereal y"
  definition "x \<le> (y::ureal) \<longleftrightarrow> ureal2ereal x \<le> ureal2ereal y"
instance 
  apply (intro_classes)
  using less_eq_ureal_def less_ureal_def apply fastforce
     apply (simp add: less_eq_ureal_def)
  using less_eq_ureal_def apply auto[1]
  apply (simp add: less_eq_ureal_def ureal2ereal_inject)
  using less_eq_ureal_def by fastforce
end

print_locale "complete_lattice"
print_classes

instantiation ureal :: complete_lattice
begin
(* definition "bot = (ereal2ureal 0)"
definition "top = (ereal2ureal 1)"
*)
(* definition "less_eq a b = (ureal2ereal a \<le> ureal2ereal b)"
definition "less a b = (ureal2ereal a < ureal2ereal b)"
*)
definition "sup a b = ereal2ureal (max (ureal2ereal a) (ureal2ereal b))"
definition "inf a b = ereal2ureal (min (ureal2ereal a) (ureal2ereal b))"

definition "Sup S = (SOME x :: ureal. (\<forall>y\<in>S. y \<le> x) \<and> (\<forall>z. (\<forall>y\<in>S. y \<le> z) \<longrightarrow> x \<le> z))"
definition "Inf S = (SOME x :: ureal. (\<forall>y\<in>S. x \<le> y) \<and> (\<forall>z. (\<forall>y\<in>S. z \<le> y) \<longrightarrow> z \<le> x))"
instance
  apply (intro_classes)
  apply (auto simp add: bot_ureal_def top_ureal_def less_eq_ureal_def less_ureal_def sup_ureal_def
      inf_ureal_def)
  apply (smt (verit, best) ureal2ereal_inverse)
  apply (smt (verit) ureal2ereal_inverse)
  apply (smt (verit) ureal2ereal_inverse)
  apply (smt (verit) ureal2ereal_inverse)
  apply (smt (verit) ureal2ereal_inverse)
  apply (smt (verit) ureal2ereal_inverse)
  apply (simp add: Inf_ureal_def)
  apply (transfer, simp add: top_ureal_def)
  sorry
end

type_synonym ('s\<^sub>1, 's\<^sub>2) rvfun = "(\<real>, 's\<^sub>1 \<times> 's\<^sub>2) expr"
type_synonym 's rvhfun = "('s, 's) rvfun"

type_synonym ('s\<^sub>1, 's\<^sub>2) pfun = "(ureal, 's\<^sub>1 \<times> 's\<^sub>2) expr"
type_synonym 's phfun = "('s, 's) pfun"

abbreviation "pmap f \<equiv> (\<lambda>v. ureal2ereal (f v))"

lemma pmap_if: "(\<lambda>s. pmap (if s = a then c else d)) = (\<lambda>s. (if s = a then pmap c else pmap d))"
  apply (subst fun_eq_iff)
  by (auto)

typedef ('s\<^sub>1, 's\<^sub>2) pdfun = "{f::('s\<^sub>1, 's\<^sub>2) pfun. (\<forall>s\<^sub>1::'s\<^sub>1. is_sum_1 (pmap ((curry f) s\<^sub>1)))}"
  morphisms of_pdfun of_pfun
  apply (simp add: dist_defs taut_def)
  apply (rule_tac x = "\<lambda>(a, b). if b = c then (ereal2ureal 1) else (ereal2ureal 0)" in exI)
  apply (auto)
proof -
  have "(\<Sum>\<^sub>\<infinity>s::'s\<^sub>2. pmap (If (s = c) (ereal2ureal (1::\<real>))) (ereal2ureal (0::\<real>)))
    = (\<Sum>\<^sub>\<infinity>s::'s\<^sub>2. (If (s = c) 1 0))"
    by (smt (verit, best) atLeastAtMost_iff infsum_cong ereal2ureal_inverse)
  also have "... = 1"
    by (rule infsum_singleton_1)
  ultimately show "(\<Sum>\<^sub>\<infinity>s::'s\<^sub>2. pmap (If (s = c) (ereal2ureal (1::\<real>))) (ereal2ureal (0::\<real>))) = 1"
    by presburger
qed

definition pskip :: "'s phfun" ("II\<^sub>p") where
[pfun_defs]: "pskip = (ereal2ureal (\<lbrakk> \<lbrakk>II\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>))\<^sub>e"

adhoc_overloading
  uskip pskip

term "II::'s rel"
term "II::'s phfun"

abbreviation passigns_f where 
"passigns_f \<sigma> \<equiv> \<lbrakk> \<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>"

definition passigns :: "('a, 'b) psubst \<Rightarrow> ('a, 'b) pfun" where 
[pfun_defs]: "passigns \<sigma> = (ereal2ureal (\<lbrakk> \<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>))\<^sub>e"

adhoc_overloading
  uassigns passigns

term "(s := e)::'s phfun"
term "(s := e)::'s rel"

definition pchoice :: "('s\<^sub>1, 's\<^sub>2) pfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) pfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) pfun" 
  ("(_ \<oplus>\<^bsub>_\<^esub> _)" [61, 0, 60] 60) where
[pfun_defs]: "pchoice P r Q = (ereal2ureal (r * P + (1 - r) * Q)\<^sub>e)\<^sub>e"
*)
(* definition pchoice' :: "'s rfhrel \<Rightarrow> ('s, 's) erfun \<Rightarrow> ('s, 's) erfun \<Rightarrow> ('s, 's) erfun" 
    ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 0, 167] 167) where
[pfun_defs]: "pchoice' r P Q = real2ureal (r * @(rfrel_of_erfun P) + (1 - r) * @(rfrel_of_erfun Q))\<^sub>e"
*)

syntax 
  "_pchoice" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 61, 60] 60) 

translations
  "_pchoice r P Q" == "CONST pchoice P (r)\<^sub>e Q"
  "_pchoice r P Q" <= "_pchoice (r)\<^sub>e P Q"

term "if\<^sub>p 0.5 then P else Q"
term "if\<^sub>p R then P else Q"
term "if\<^sub>p R then P else Q = if\<^sub>p R then P else Q"
*)

end
