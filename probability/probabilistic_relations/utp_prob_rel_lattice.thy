section \<open> Probabilistic relation programming \<close>

theory utp_prob_rel_lattice
  imports 
    (* "HOL.Series" *)
    "HOL-Analysis.Infinite_Sum" 
    "HOL-Library.Complete_Partial_Order2" 
    "utp_iverson_bracket" 
    "utp_distribution"
    "infsum_laws"
begin 

unbundle UTP_Syntax

declare [[show_types]]

named_theorems pfun_defs and ureal_defs and chains_defs

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

(* Should we lift operators for ureal and instantiate it for classes like "zero, one, add, minus, ..."?
If we instantiate ureal for these classes, we are able to write (0::ureal) + (1::ureal). 
Finally, we are able to define operators like probabilistic choice, sequential composition on ureal 
only, not on real. However, by this way, we also need to deal with infsum for ureal, and so ureal must 
be instantiated to a topological space and prove all related summation laws. It seems not 
straightforward to do so.

Either we can just instantiate ureal as a complete lattice and define these operators on real, but 
these operators have ureal parameters and result. The definition needs to deal with convert ureal 
to real, operation on reals, then convert the result back to ureal. Finally, we reuse all summation 
laws for real numbers. 
*)
(*
type_synonym ('s\<^sub>1, 's\<^sub>2) rvfun = "(real, 's\<^sub>1 \<times> 's\<^sub>2) expr"
type_synonym 's rvhfun = "('s, 's) rvfun"
*)
subsection \<open> Real numbers or non-negative extended real numbers \<close>
(*
type_synonym ('s\<^sub>1, 's\<^sub>2) prfun = "(ennreal, 's\<^sub>1 \<times> 's\<^sub>2) expr"
type_synonym 's prhfun = "('s, 's) prfun"

subsection \<open> Syntax \<close>
definition zero :: "'s prhfun" where
"zero = (0)\<^sub>e"

definition one :: "'s prhfun" where
"one = (1)\<^sub>e"

definition pskip :: "'s prhfun" ("II\<^sub>p") where
[pfun_defs]: "pskip = (\<lbrakk> \<lbrakk>II\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"

adhoc_overloading
  uskip pskip

term "II::'s rel"
term "II::'s prhfun"

definition passigns :: "('a, 'b) psubst \<Rightarrow> ('a, 'b) prfun" where 
[pfun_defs]: "passigns \<sigma> = (\<lbrakk> \<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"

adhoc_overloading
  uassigns passigns

term "(s := e)::'s prhfun"
term "(s := e)::'s rel"

definition pchoice :: "('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun" 
  ("(_ \<oplus>\<^bsub>_\<^esub> _)" [61, 0, 60] 60) where
[pfun_defs]: "pchoice P r Q = ((r * P + (1 - r) * Q))\<^sub>e"

(* definition pchoice' :: "'s rvhfun \<Rightarrow> ('s, 's) prfun \<Rightarrow> ('s, 's) prfun \<Rightarrow> ('s, 's) prfun" 
    ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 0, 167] 167) where
[pfun_defs]: "pchoice' r P Q = real2ureal (r * @(rvfun_of_prfun P) + (1 - r) * @(rvfun_of_prfun Q))\<^sub>e"
*)

syntax 
  "_pchoice" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 61, 60] 60) 

translations
  "_pchoice r P Q" == "CONST pchoice P (r)\<^sub>e Q"
  "_pchoice r P Q" <= "_pchoice (r)\<^sub>e P Q"

term "if\<^sub>p 0.5 then P else Q"
term "if\<^sub>p R then P else Q"
term "if\<^sub>p R then P else Q = if\<^sub>p R then P else Q"

abbreviation pcond_f :: "('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rpred \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun" 
("(3_ \<lhd>\<^sub>f _ \<rhd>/ _)" [61,0,60] 60) where 
"pcond_f P b Q \<equiv> (if b then P else Q)\<^sub>e"

(*TODO: should be this type, but I cannot make it type correct.
definition pseqcomp ::"('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>2, 's\<^sub>3) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>3) prfun" (infixl ";\<^sub>f" 59) where *)

definition pseqcomp ::"'s prhfun \<Rightarrow> 's prhfun \<Rightarrow> 's prhfun" (infixl ";\<^sub>f" 59) where
[pfun_defs]: "pseqcomp P Q = 
  (\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> (P)) * ([ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> (Q)))\<^sub>e"

consts
  pseqcomp_c :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl ";" 59)
adhoc_overloading
  pseqcomp_c pseqcomp

term "(P::'s prhfun) ; Q"

text \<open> Considering recursions @{text "X = P ; X"}, zero is one of its solution. But this solution is 
not very useful.  
\<close>
alphabet time = 
  t :: nat

term "lfp (\<lambda>X. (P::'s prhfun))"

definition pwhile :: "('a time_scheme \<times> 'a time_scheme \<Rightarrow> \<bool>) \<Rightarrow> 'a time_scheme prhfun 
  \<Rightarrow> 'a time_scheme prhfun" 
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

term "a::('a::linorder)"
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
type_synonym ('s\<^sub>1, 's\<^sub>2) rvfun = "(\<real>, 's\<^sub>1 \<times> 's\<^sub>2) expr"
type_synonym 's rvhfun = "('s, 's) rvfun"

text \<open> Probability functions which map state space to a real number between 0 and 1 (and so ureal)\<close>
type_synonym ('s\<^sub>1, 's\<^sub>2) prfun = "(ureal, 's\<^sub>1 \<times> 's\<^sub>2) expr"
type_synonym 's prhfun = "('s, 's) prfun"

definition prfun_of_rvfun:: "('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun" where
[ureal_defs]: "prfun_of_rvfun f = (real2ureal f)\<^sub>e "

thm "prfun_of_rvfun_def"

definition rvfun_of_prfun where
[ureal_defs]: "rvfun_of_prfun f = (ureal2real f)\<^sub>e "

subsection \<open> Syntax \<close>

(* deadlock: zero and not a distribution *)
abbreviation one_f ("\<^bold>1") where
  "one_f \<equiv> (\<lambda> s. 1::ureal)"

abbreviation zero_f ("\<^bold>0") where
  "zero_f \<equiv> (\<lambda> s. 0::ureal)"

definition pzero :: "('s\<^sub>1, 's\<^sub>2) prfun" ("0\<^sub>p") where
[pfun_defs]: "pzero = zero_f"

definition pone :: "('s\<^sub>1, 's\<^sub>2) prfun" ("1\<^sub>p") where
[pfun_defs]: "pone = one_f"


(*
lemma deadlock_always: "`@(deadlock_state pzero)`"
  apply (simp add: pfun_defs)
  by (simp add: is_prob_def real2ureal_inverse)
*)

subsubsection \<open> Skip \<close>
(* The purpose of this abbreviation is to make later reference to this function inside pskip easier. *)
abbreviation pskip\<^sub>_f ("II\<^sub>f") where
  "pskip\<^sub>_f \<equiv> \<lbrakk> \<lbrakk>II\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>"

definition pskip :: "'s prhfun" ("II\<^sub>p") where
[pfun_defs]: "pskip = prfun_of_rvfun (pskip\<^sub>_f)"

adhoc_overloading
  uskip pskip

term "II::'s rel"
term "II::'s prhfun"
term "x := ($x + 1)"
term "x\<^sup>> := ($x\<^sup>< + 1)"

subsubsection \<open> Assignment \<close>
abbreviation passigns_f where 
"passigns_f \<sigma> \<equiv> \<lbrakk> \<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>"

definition passigns :: "('a, 'b) psubst \<Rightarrow> ('a, 'b) prfun" where 
[pfun_defs]: "passigns \<sigma> = prfun_of_rvfun (passigns_f \<sigma>)"

adhoc_overloading
  uassigns passigns

term "(s := e)::'s prhfun"
term "(s := e)::'s rel"

subsubsection \<open> Probabilistic choice \<close>
abbreviation pchoice_f :: "('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun" 
("(_ \<oplus>\<^sub>f\<^bsub>_\<^esub> _)" [61, 0, 60] 60) where 
"pchoice_f P r Q \<equiv> (r * P + (1 - r) * Q)\<^sub>e"

definition pchoice :: "('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun" 
  ("(_ \<oplus>\<^bsub>_\<^esub> _)" [61, 0, 60] 60) where
[pfun_defs]: "pchoice P r Q = prfun_of_rvfun (pchoice_f (rvfun_of_prfun P) (rvfun_of_prfun r) (rvfun_of_prfun Q))"

(* definition pchoice' :: "'s rvhfun \<Rightarrow> ('s, 's) prfun \<Rightarrow> ('s, 's) prfun \<Rightarrow> ('s, 's) prfun" 
    ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 0, 167] 167) where
[pfun_defs]: "pchoice' r P Q = real2ureal (r * @(rvfun_of_prfun P) + (1 - r) * @(rvfun_of_prfun Q))\<^sub>e"
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
abbreviation pcond_f :: "('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rpred \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun" 
("(3_ \<lhd>\<^sub>f _ \<rhd>/ _)" [61,0,60] 60) where 
"pcond_f P b Q \<equiv> (if b then P else Q)\<^sub>e"

definition pcond :: "('s\<^sub>1, 's\<^sub>2) rpred \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun" where 
[pfun_defs]: "pcond b P Q \<equiv> prfun_of_rvfun (pcond_f (rvfun_of_prfun P) b (rvfun_of_prfun Q))"

syntax 
  "_pcond" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(if\<^sub>c (_)/ then (_)/ else (_))" [0, 61, 60] 60) 

translations
  "_pcond b P Q" == "CONST pcond (b)\<^sub>e P Q"
  "_pcond b P Q" <= "_pcond (b)\<^sub>e P Q"

term "if\<^sub>c True then P else Q"

subsubsection \<open> Sequential composition \<close>
term "(rvfun_of_prfun (P::('s prhfun)))\<lbrakk>v\<^sub>0/\<^bold>v\<^sup>>\<rbrakk>"
term "\<^bold>v\<^sup>>"
term "(\<Sum>\<^sub>\<infinity> v\<^sub>0. (P\<lbrakk>\<guillemotleft>v\<^sub>0\<guillemotright>/\<^bold>v\<^sup>>\<rbrakk>) * (Q\<lbrakk>\<guillemotleft>v\<^sub>0\<guillemotright>/\<^bold>v\<^sup><\<rbrakk>))\<^sub>e"
term "[ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> (rvfun_of_prfun (P::'s prhfun))"
term "(\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> P) * ([ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> Q))\<^sub>e"
term "(\<exists> v\<^sub>0. [ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> \<lbrakk>P\<rbrakk>\<^sub>P \<and> [ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> \<lbrakk>Q\<rbrakk>\<^sub>P)\<^sub>e"
term "if True then a else b"
term " 
  (\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> v\<^sub>0 ] \<dagger> @(rvfun_of_prfun P)) * ([ \<^bold>v\<^sup>< \<leadsto> v\<^sub>0 ] \<dagger> @(rvfun_of_prfun Q)))\<^sub>e"
thm "pred_seq_hom"

abbreviation pseqcomp_f :: "'s rvhfun \<Rightarrow> 's rvhfun \<Rightarrow> 's rvhfun" (infixl ";\<^sub>f" 59) where 
"pseqcomp_f P Q \<equiv> (\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> P) * ([ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> Q))\<^sub>e" 

definition pseqcomp :: "'s prhfun \<Rightarrow> 's prhfun \<Rightarrow> 's prhfun" (*(infixl ";\<^sub>p" 59)*) where
[pfun_defs]: "pseqcomp P Q = prfun_of_rvfun (pseqcomp_f (rvfun_of_prfun P) (rvfun_of_prfun Q))"

consts
  pseqcomp_c :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl ";" 59)
adhoc_overloading
  pseqcomp_c pseqcomp_f and 
  pseqcomp_c pseqcomp

term "(P::('s, 's) rvfun) ; Q"
term "(P::'s prhfun) ; Q"

lemma real_1: "real_of_ereal (ureal2ereal (ereal2ureal' (ereal (1::\<real>)))) = 1"
  by (simp add: ereal2ureal'_inverse)

subsubsection \<open> Parallel composition \<close>

abbreviation pparallel_f :: "('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun" (infixl "\<parallel>\<^sub>f" 58)
  where "pparallel_f P Q \<equiv> (\<^bold>N (P * Q)\<^sub>e)"

abbreviation pparallel_f' :: "('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun"
  where "pparallel_f' P Q \<equiv> ((P * Q) / (\<Sum>\<^sub>\<infinity> s'. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>s'\<guillemotright> ] \<dagger> P) * ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>s'\<guillemotright> ] \<dagger> Q)))\<^sub>e"

lemma pparallel_f_eq: "pparallel_f P Q = pparallel_f' P Q"
  apply (simp add: dist_defs)
  by (expr_auto)

text \<open> We provide four variants (different combinations of types for their parameters) of parallel 
composition for convenience and they use a same notation @{text "\<parallel>"}. All of them defines 
probabilistic programs of type @{typ "('a\<^sub>1, 'a\<^sub>2) prfun"}.
\<close>
definition pparallel :: "('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun" (infixl "\<parallel>\<^sub>p" 58) where
[pfun_defs]: "pparallel P Q = prfun_of_rvfun (pparallel_f P Q)"

definition pparallel_pp :: "('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun" where
[pfun_defs]: "pparallel_pp P Q = pparallel (rvfun_of_prfun P) (rvfun_of_prfun Q)"

definition pparallel_fp :: "('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun" where
[pfun_defs]: "pparallel_fp P Q = pparallel P (rvfun_of_prfun Q)"

definition pparallel_pf :: "('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun" where
[pfun_defs]: "pparallel_pf P Q = pparallel (rvfun_of_prfun P) Q"

no_notation Sublist.parallel (infixl "\<parallel>" 50)
consts
  parallel_c :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<parallel>" 58)

adhoc_overloading
  parallel_c pparallel and 
  parallel_c pparallel_pp and
  parallel_c pparallel_fp and
  parallel_c pparallel_pf and
  parallel_c Sublist.parallel

term "((P::('s, 's) rvfun) \<parallel> (Q::('s, 's) rvfun))"
term "((P::('s, 's) rvfun) \<parallel> (Q::('s, 's) prfun))"
term "((P::('s, 's) prfun) \<parallel> (Q::('s, 's) rvfun))"
term "((P::('s, 's) prfun) \<parallel> (Q::('s, 's) prfun))"
term "((P::'s list) \<parallel> Q)"
term "([] \<parallel> [a])"

subsubsection \<open> Recursion \<close>
alphabet time = 
  t :: nat

text \<open>In UTP, @{text "\<mu>"} and @{text "\<nu>"} are the weakest and strongest fix point, but there are 
gfp and lfp in Isabelle (see @{text "utp_pred.thy"}).
Here, we use the same order as Isabelle, opposite with UTP. So we define @{text "\<mu>\<^sub>p"} for the least 
fix point (also lfp in Isabelle).
\<close>
(* no_notation gfp ("\<mu>")
no_notation lfp ("\<nu>") 
*)

notation lfp ("\<mu>\<^sub>p")
notation gfp ("\<nu>\<^sub>p")

syntax
  "_mu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<mu>\<^sub>p _ \<bullet> _" [0, 10] 10)
  "_nu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<nu>\<^sub>p _ \<bullet> _" [0, 10] 10)

translations
  "\<nu>\<^sub>p X \<bullet> P" == "CONST gfp (\<lambda> X. P)"
  "\<mu>\<^sub>p X \<bullet> P" == "CONST lfp (\<lambda> X. P)"

term "\<mu>\<^sub>p X  \<bullet>  (X::'s prhfun)"
term "lfp (\<lambda>X. (P::'s prhfun))"

subsection \<open> Chains \<close> 
definition increasing_chain :: "(nat \<Rightarrow> 'a::complete_lattice) \<Rightarrow> bool" where
[chains_defs]: "increasing_chain f = (\<forall>m. \<forall>n. m \<le> n \<longrightarrow> f m \<le> f n)"

definition decreasing_chain :: "(nat \<Rightarrow> 'a::complete_lattice) \<Rightarrow> bool" where
[chains_defs]: "decreasing_chain f = (\<forall>m. \<forall>n. m \<le> n \<longrightarrow> f m \<ge> f n)"

subsection \<open> Fixed-point Laws \<close>
text \<open> Existence of a fixed point for a mono function F in ureal: See 
Knaster_Tarski under HOL/Examples
\<close>
lemma mu_id: "(\<mu>\<^sub>p (X::'a \<Rightarrow> ureal) \<bullet> X) = \<^bold>0"
  apply (simp add: lfp_def)
  by (metis bot.extremum_uniqueI bot_fun_def bot_ureal.rep_eq dual_order.refl less_eq_ureal.rep_eq 
      zero_ureal.rep_eq)

lemma mu_const: "(\<mu>\<^sub>p X \<bullet> P) = P"
  by (simp add: lfp_const)

lemma nu_id: "(\<nu>\<^sub>p (X::'a \<Rightarrow> ureal) \<bullet> X) = \<^bold>1"
  apply (simp add: gfp_def)
  using one_ureal_def top_ureal_def by auto

lemma nu_const: "(\<nu>\<^sub>p X \<bullet> P) = P"
  by (simp add: gfp_const)

term "Complete_Partial_Order.chain (\<le>) x"
term "monotone"
thm "Complete_Partial_Order.iterates.induct"
(*
lemma mu_refine_intro:
  assumes "(C \<Rightarrow> S) \<le> (F::'s prhfun \<Rightarrow> 's prhfun) (C \<Rightarrow> S)" "(C \<and> \<mu>\<^sub>p F) = (C \<and> \<nu>\<^sub>p F)"
  shows "(C \<Rightarrow> S) \<le> \<mu>\<^sub>p F"
proof -
  from assms(1) have "(C \<Rightarrow> S) \<le> \<nu>\<^sub>p F"
    by (simp add: gfp_upperbound )
  with assms show ?thesis
qed
*)

definition Fwhile :: "('a \<times> 'a) pred \<Rightarrow> 'a prhfun \<Rightarrow> 'a prhfun \<Rightarrow> 'a prhfun" where
[pfun_defs]: "Fwhile b P X  \<equiv> (if\<^sub>c b then (P ; X) else II)"

definition pwhile :: "('a \<times> 'a) pred \<Rightarrow> 'a prhfun \<Rightarrow> 'a prhfun" ("while\<^sub>p _ do _ od") where
[pfun_defs]: "pwhile b P = (\<mu>\<^sub>p X \<bullet> Fwhile b P X)"

definition pwhile_top :: "('a \<times> 'a) pred \<Rightarrow> 'a prhfun \<Rightarrow> 'a prhfun" ("while\<^sub>p\<^sup>\<top> _ do _ od") where
[pfun_defs]: "pwhile_top b P = (\<nu>\<^sub>p X \<bullet> Fwhile b P X)"

primrec iterate :: "\<nat> \<Rightarrow> ('a \<times> 'a) pred \<Rightarrow> 'a prhfun \<Rightarrow> 'a prhfun \<Rightarrow> 'a prhfun" ("iterate\<^sub>p") where
    "iterate 0 b P X = X"
  | "iterate (Suc n) b P X = (Fwhile b P (iterate n b P X))"

abbreviation "Ftwhile b P X \<equiv> Fwhile b (P ; t := $t + 1) X"
definition ptwhile :: "('a time_scheme \<times> 'a time_scheme) pred \<Rightarrow> 'a time_scheme prhfun \<Rightarrow> 'a time_scheme prhfun" 
("while\<^sub>p\<^sub>t _ do _ od") where
[pfun_defs]: "ptwhile b P = pwhile b (P ; t := $t + 1)"

abbreviation iteratet ("iterate\<^sub>t") where "iteratet n b P X \<equiv> iterate n b (P ; t := $t + 1) X"

term "iterate\<^sub>t 0 b P \<^bold>0 = \<^bold>0"

print_classes
subsubsection \<open> Lifting operators for ureal \<close>
(*
E = \<lbrakk>coin' = chead \<and> t' \<ge> t + 1\<rbrakk> * (1/2)^(t' - t - 1) * (1/2)
E0 = \<lbrakk>False\<rbrakk> * (1/2)^(t' - t - 1) * (1/2) = 0
E1 = \<lbrakk>coin' = chead \<and> 1 \<ge> t + 1\<rbrakk> * (1/2)^(1 - t - 1) * (1/2)
   = \<lbrakk>coin' = chead\<rbrakk> * (1/2)
E2 = \<lbrakk>coin' = chead \<and> 2 \<ge> t + 1\<rbrakk> * (1/2)^(2 - t - 1) * (1/2)
   = \<lbrakk>coin' = chead\<rbrakk> * (1/2)^(2 - 1) * (1/2) + \<lbrakk>coin' = chead\<rbrakk> * (1/2)^(2 -1 - 1) * (1/2) 
   = \<lbrakk>coin' = chead\<rbrakk> * (1/2)^(2) + \<lbrakk>coin' = chead\<rbrakk> * (1/2)
   = \<lbrakk>coin' = chead\<rbrakk> * (1/2)^(2) + E1 
   = \<lbrakk>coin' = chead\<rbrakk> * (3/4)
E3 = \<lbrakk>coin' = chead \<and> 3 \<ge> t + 1\<rbrakk> * (1/2)^(3 - t - 1) * (1/2)
   = \<lbrakk>coin' = chead\<rbrakk> * (1/2)^(3 - 1) * (1/2) + \<lbrakk>coin' = chead\<rbrakk> * (1/2)^(3 - 1 - 1) * (1/2) + \<lbrakk>coin' = chead\<rbrakk> * (1/2)^(3 - 2 - 1) * (1/2) 
   = \<lbrakk>coin' = chead\<rbrakk> * (1/2)^(3 - 1) * (1/2) + \<lbrakk>coin' = chead\<rbrakk> * (1/2)^(2 - 1) * (1/2) + \<lbrakk>coin' = chead\<rbrakk> * (1/2)^(0) * (1/2) 
   = \<lbrakk>coin' = chead\<rbrakk> * (1/2)^(3 - 1) * (1/2) + E2 
   = \<lbrakk>coin' = chead\<rbrakk> * (1/8 + 3/4)
   = \<lbrakk>coin' = chead\<rbrakk> * (7/8)
*)

(*
subsection \<open> Infsum \<close>
lemma summable_on_ureal_product: 
  fixes P :: "('s\<^sub>1, 's\<^sub>2) prfun"
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
  fixes P :: "('s\<^sub>1, 's\<^sub>2) prfun"
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
definition zero :: "'s prhfun" where
"zero = (0)\<^sub>e"

definition one :: "'s prhfun" where
"one = (1)\<^sub>e"

definition pskip :: "'s prhfun" ("II\<^sub>p") where
[pfun_defs]: "pskip = (\<lbrakk> \<lbrakk>II\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"

adhoc_overloading
  uskip pskip

term "II::'s rel"
term "II::'s prhfun"

definition passigns :: "('a, 'b) psubst \<Rightarrow> ('a, 'b) prfun" where 
[pfun_defs]: "passigns \<sigma> = (\<lbrakk> \<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"

adhoc_overloading
  uassigns passigns

term "(s := e)::'s prhfun"
term "(s := e)::'s rel"

definition pchoice :: "('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun" 
  ("(_ \<oplus>\<^bsub>_\<^esub> _)" [61, 0, 60] 60) where
[pfun_defs]: "pchoice P r Q = ((r * P + (1 - r) * Q))\<^sub>e"

(* definition pchoice' :: "'s rvhfun \<Rightarrow> ('s, 's) prfun \<Rightarrow> ('s, 's) prfun \<Rightarrow> ('s, 's) prfun" 
    ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 0, 167] 167) where
[pfun_defs]: "pchoice' r P Q = real2ureal (r * @(rvfun_of_prfun P) + (1 - r) * @(rvfun_of_prfun Q))\<^sub>e"
*)

syntax 
  "_pchoice" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 61, 60] 60) 

translations
  "_pchoice r P Q" == "CONST pchoice P (r)\<^sub>e Q"
  "_pchoice r P Q" <= "_pchoice (r)\<^sub>e P Q"

term "if\<^sub>p 0.5 then P else Q"
term "if\<^sub>p R then P else Q"
term "if\<^sub>p R then P else Q = if\<^sub>p R then P else Q"

abbreviation pcond_f :: "('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rpred \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun" 
("(3_ \<lhd>\<^sub>f _ \<rhd>/ _)" [61,0,60] 60) where 
"pcond_f P b Q \<equiv> (if b then P else Q)\<^sub>e"

(*TODO: should be this type, but I cannot make it type correct.
definition pseqcomp ::"('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>2, 's\<^sub>3) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>3) prfun" (infixl ";\<^sub>f" 59) where *)

definition pseqcomp ::"'s prhfun \<Rightarrow> 's prhfun \<Rightarrow> 's prhfun" (infixl ";\<^sub>f" 59) where
[pfun_defs]: "pseqcomp P Q = 
  (\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> (P)) * ([ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> (Q)))\<^sub>e"

consts
  pseqcomp_c :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl ";" 59)
adhoc_overloading
  pseqcomp_c pseqcomp

term "(P::'s prhfun) ; Q"

text \<open> Considering recursions @{text "X = P ; X"}, zero is one of its solution. But this solution is 
not very useful.  
\<close>
alphabet time = 
  t :: nat

term "lfp (\<lambda>X. (P::'s prhfun))"

definition pwhile :: "('a time_scheme \<times> 'a time_scheme \<Rightarrow> \<bool>) \<Rightarrow> 'a time_scheme prhfun 
  \<Rightarrow> 'a time_scheme prhfun" 
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
subsubsection \<open> instantiation of ureal \<close>
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
(* definition pchoice' :: "'s rvhfun \<Rightarrow> ('s, 's) prfun \<Rightarrow> ('s, 's) prfun \<Rightarrow> ('s, 's) prfun" 
    ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 0, 167] 167) where
[pfun_defs]: "pchoice' r P Q = real2ureal (r * @(rvfun_of_prfun P) + (1 - r) * @(rvfun_of_prfun Q))\<^sub>e"
*)
(*
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
