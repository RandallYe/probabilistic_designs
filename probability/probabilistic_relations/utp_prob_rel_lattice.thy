section \<open> Probabilistic relation programming \<close>

theory utp_prob_rel_lattice
  imports 
    "HOL-Analysis.Infinite_Sum" 
    "HOL-Library.Complete_Partial_Order2" 
    "utp_iverson_bracket" 
    "utp_distribution"
begin 

unbundle UTP_Syntax

named_theorems pfun_defs and ureal_defs and chains_defs

subsection \<open> Unit real interval @{text "ureal"}\<close>

typedef ureal = "{(0::ereal)..1}"
  morphisms ureal2ereal ereal2ureal'
  apply (rule_tac x = "0" in exI)
  by auto

find_theorems name:"ureal"

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

instantiation ureal :: "{one,zero,plus,times,mult_zero, zero_neq_one, semigroup_mult, semigroup_add, 
  ab_semigroup_mult, ab_semigroup_add, monoid_add, monoid_mult, comm_monoid_add}"
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

subsection \<open> Probability functions \<close>
type_synonym ('s\<^sub>1, 's\<^sub>2) rvfun = "(\<real>, 's\<^sub>1 \<times> 's\<^sub>2) expr"
type_synonym 's rvhfun = "('s, 's) rvfun"

type_synonym ('s\<^sub>1, 's\<^sub>2) prfun = "(ureal, 's\<^sub>1 \<times> 's\<^sub>2) expr"
type_synonym 's prhfun = "('s, 's) prfun"

definition prfun_of_rvfun:: "('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun" where
[ureal_defs]: "prfun_of_rvfun f = (real2ureal f)\<^sub>e "

definition rvfun_of_prfun where
[ureal_defs]: "rvfun_of_prfun f = (ureal2real f)\<^sub>e "

subsubsection \<open> Characterise an expression over the final state \<close>
abbreviation summable_on_final :: "('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> \<bool>" where
"summable_on_final p \<equiv> (\<forall>s. (\<lambda>s'. p (s,s')) summable_on UNIV)"

abbreviation summable_on_final2 :: "('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> \<bool>" where
"summable_on_final2 p q \<equiv> (\<forall>s. (\<lambda>s'. p(s,s') * q(s,s')) summable_on UNIV)"

abbreviation final_reachable :: "('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> \<bool>" where
"final_reachable p \<equiv> (\<forall>s. \<exists>s'. p (s, s') > 0)"

abbreviation final_reachable2 :: "('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> \<bool>" where
"final_reachable2 p q \<equiv> (\<forall>s. \<exists>s'. p (s, s') > 0 \<and> q (s, s') > 0)"

subsection \<open> Syntax \<close>
abbreviation one_r ("1\<^sub>R") where
  "one_r \<equiv> (\<lambda>s. 1::real)"

abbreviation zero_r ("0\<^sub>R") where
  "zero_r \<equiv> (\<lambda>s. 0::real)"

abbreviation one_f ("\<^bold>1") where
  "one_f \<equiv> (\<lambda>s. 1::ureal)"

abbreviation zero_f ("\<^bold>0") where
  "zero_f \<equiv> (\<lambda>s. 0::ureal)"

definition pzero :: "('s\<^sub>1, 's\<^sub>2) prfun" ("0\<^sub>p") where
[pfun_defs]: "pzero = zero_f"

definition pone :: "('s\<^sub>1, 's\<^sub>2) prfun" ("1\<^sub>p") where
[pfun_defs]: "pone = one_f"

subsubsection \<open> Skip \<close>
(* The purpose of this abbreviation is to make later reference to this function inside pskip easier. *)
abbreviation pskip\<^sub>_f ("II\<^sub>f") where
  "pskip\<^sub>_f \<equiv> \<lbrakk> II \<rbrakk>\<^sub>\<I>"

definition pskip :: "'s prhfun" ("II\<^sub>p") where
[pfun_defs]: "pskip = prfun_of_rvfun (pskip\<^sub>_f)"

adhoc_overloading
  uskip pskip

term "II::'s hrel"
term "II::'s prhfun"
term "x := ($x + 1)"
term "x\<^sup>> := ($x\<^sup>< + 1)"

subsubsection \<open> Assignment \<close>
abbreviation passigns_f where 
"passigns_f \<sigma> \<equiv> \<lbrakk> \<langle>\<sigma>\<rangle>\<^sub>a \<rbrakk>\<^sub>\<I>"

definition passigns :: "('a, 'b) psubst \<Rightarrow> ('a, 'b) prfun" where 
[pfun_defs]: "passigns \<sigma> = prfun_of_rvfun (passigns_f \<sigma>)"

adhoc_overloading
  uassigns passigns

term "(s := e)::'s prhfun"
term "(s := e)::'s hrel"

subsubsection \<open> Probabilistic choice \<close>
abbreviation pchoice_f :: "('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun" 
("(_ \<oplus>\<^sub>f\<^bsub>_\<^esub> _)" [61, 0, 60] 60) where 
"pchoice_f P r Q \<equiv> (r * P + (1 - r) * Q)\<^sub>e"

definition pchoice :: "('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun" 
  ("(_ \<oplus>\<^bsub>_\<^esub> _)" [61, 0, 60] 60) where
[pfun_defs]: "pchoice P r Q = prfun_of_rvfun (pchoice_f (rvfun_of_prfun P) (rvfun_of_prfun r) (rvfun_of_prfun Q))"

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
expr_constructor lift_pre

subsubsection \<open> Conditional choice \<close>
abbreviation pcond_f :: "('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) urel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun" 
("(3_ \<lhd>\<^sub>f _ \<rhd>/ _)" [61,0,60] 60) where 
"pcond_f P b Q \<equiv> (if b then P else Q)\<^sub>e"

definition pcond :: "('s\<^sub>1, 's\<^sub>2) urel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prfun" where 
[pfun_defs]: "pcond b P Q \<equiv> prfun_of_rvfun (pcond_f (rvfun_of_prfun P) b (rvfun_of_prfun Q))"

syntax 
  "_pcond" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(if\<^sub>c (_)/ then (_)/ else (_))" [0, 61, 60] 60) 

translations
  "_pcond b P Q" == "CONST pcond (b)\<^sub>e P Q"
  "_pcond b P Q" <= "_pcond (b)\<^sub>e P Q"

term "if\<^sub>c True then P else Q"

subsubsection \<open> Sequential composition \<close>
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

subsubsection \<open> Parallel composition \<close>

abbreviation pparallel_f :: "('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun" (infixl "\<parallel>\<^sub>f" 58)
  where "pparallel_f P Q \<equiv> (\<^bold>N\<^sub>f (P * Q)\<^sub>e)"

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
  t :: enat

text \<open>In UTP, @{text "\<mu>"} and @{text "\<nu>"} are the weakest and strongest fix point, but there are 
@{term "gfp"} and @{term "lfp"} in Isabelle (see @{text "utp_pred.thy"}).
Here, we use the same order as Isabelle, the opposite of UTP. So we define @{text "\<mu>\<^sub>p"} for the least 
fix point (also @{term "lfp"} in Isabelle).
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
text \<open>There are similar definitions @{term "incseq"} and @{term "decseq"} in the topological space. 
Our definition here is more restricted to complete lattices instead of general partial order 
@{class "order"}, and so we can prove more specific laws with it.
\<close>
definition increasing_chain :: "(nat \<Rightarrow> 'a::complete_lattice) \<Rightarrow> bool" where
[chains_defs]: "increasing_chain f = (\<forall>m. \<forall>n. m \<le> n \<longrightarrow> f m \<le> f n)"

definition decreasing_chain :: "(nat \<Rightarrow> 'a::complete_lattice) \<Rightarrow> bool" where
[chains_defs]: "decreasing_chain f = (\<forall>m. \<forall>n. m \<le> n \<longrightarrow> f m \<ge> f n)"

abbreviation finite_state_incseq ("\<F>\<S>\<^sup>") where 
"finite_state_incseq f \<equiv> finite {s. ureal2real (\<Squnion>n::\<nat>. f n s) > ureal2real (f 0 s)}"

abbreviation finite_state_decseq ("\<F>\<S>\<^sub>") where 
"finite_state_decseq f \<equiv> finite {s. ureal2real (\<Sqinter> n::\<nat>. f n s) < ureal2real (f 0 s)}"

subsection \<open> While loops \<close>
definition loopfunc :: "('a \<times> 'a) pred \<Rightarrow> 'a prhfun \<Rightarrow> 'a prhfun \<Rightarrow> 'a prhfun" ("\<F>") where
[pfun_defs]: "loopfunc b P X  \<equiv> (if\<^sub>c b then (P ; X) else II)"

definition pwhile :: "('a \<times> 'a) pred \<Rightarrow> 'a prhfun \<Rightarrow> 'a prhfun" ("while\<^sub>p _ do _ od") where
[pfun_defs]: "pwhile b P = (\<mu>\<^sub>p X \<bullet> \<F> b P X)"

definition pwhile_top :: "('a \<times> 'a) pred \<Rightarrow> 'a prhfun \<Rightarrow> 'a prhfun" ("while\<^sub>p\<^sup>\<top> _ do _ od") where
[pfun_defs]: "pwhile_top b P = (\<nu>\<^sub>p X \<bullet> \<F> b P X)"

primrec iterate :: "\<nat> \<Rightarrow> ('a \<times> 'a) pred \<Rightarrow> 'a prhfun \<Rightarrow> 'a prhfun \<Rightarrow> 'a prhfun" ("iter\<^sub>p") where
    "iterate 0 b P X = X"
  | "iterate (Suc n) b P X = (\<F> b P (iterate n b P X))"

text \<open> @{text "iterdiff"} constructs a form @{text "P ; (P ; ... ; (P ; X))"}. This particularly is 
used for @{text "X"} being @{text "1\<^sub>p"}.\<close>
primrec iterdiff :: "\<nat> \<Rightarrow> ('a \<times> 'a) pred \<Rightarrow> 'a prhfun \<Rightarrow> 'a prhfun \<Rightarrow> 'a prhfun" ("iter\<^sub>d") where
    "iterdiff 0 b P X = X"
  | "iterdiff (Suc n) b P X = (if\<^sub>c b then (P ; (iterdiff n b P X)) else 0\<^sub>p)"

definition "Pt (P::'a time_scheme prhfun) \<equiv> (P ; t := $t + 1)"

definition ptwhile :: "('a time_scheme \<times> 'a time_scheme) pred \<Rightarrow> 'a time_scheme prhfun \<Rightarrow> 'a time_scheme prhfun" 
("while\<^sub>p\<^sub>t _ do _ od") where
[pfun_defs]: "ptwhile b P = pwhile b (Pt P)"

abbreviation iteratet ("iterate\<^sub>t") where "iteratet n b P X \<equiv> iterate n b (Pt P) X"
term "iterate\<^sub>t 0 b P \<^bold>0 = \<^bold>0"

end
