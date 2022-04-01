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

named_theorems pfun_defs

(* Should we use ennreal or ereal or even real01?
  ereal: complete_linorder (linorder + complete_lattice), but ; is not mono. 
    Consider negative values for the subgoal of pseqcomp_mono.
    (P\<^sub>1 \<le> P\<^sub>2 \<Longrightarrow> Q\<^sub>1 \<le> Q\<^sub>2 \<Longrightarrow> x \<in> UNIV \<Longrightarrow> P\<^sub>1 (a, x) * Q\<^sub>1 (x, b) \<le> P\<^sub>2 (a, x) * Q\<^sub>2 (x, b))
  ennreal: complete_linorder, but ; is not mono
    Consider the subgoal of pseqcomp_mono. Using infsum_mono, we need to prove both sides are summable_on
    P\<^sub>1 \<le> P\<^sub>2 \<Longrightarrow>
       Q\<^sub>1 \<le> Q\<^sub>2 \<Longrightarrow>
       (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. P\<^sub>1 (a, v\<^sub>0) * Q\<^sub>1 (v\<^sub>0, b)) \<le> (\<Sum>\<^sub>\<infinity>v\<^sub>0::'a. P\<^sub>2 (a, v\<^sub>0) * Q\<^sub>2 (v\<^sub>0, b))
  real01:
    So if P\<^sub>1 summable, then (P\<^sub>1 (a, v\<^sub>0) * Q\<^sub>1 (v\<^sub>0, b)) summable. (if P\<^sub>1 is a distribution, then P\<^sub>1 summable)
  pdfun: probabilistic distribution functions.
    But pdfun cannot be compared.
*)
term "ennreal"
type_synonym ('s\<^sub>1, 's\<^sub>2) rvfun = "(real, 's\<^sub>1 \<times> 's\<^sub>2) expr"
type_synonym 's rvhfun = "('s, 's) rvfun"
type_synonym ('s\<^sub>1, 's\<^sub>2) erfun = "(ereal, 's\<^sub>1 \<times> 's\<^sub>2) expr"
type_synonym 's erhfun = "('s, 's) erfun"

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

(* definition pchoice' :: "'s rfhrel \<Rightarrow> ('s, 's) prel \<Rightarrow> ('s, 's) prel \<Rightarrow> ('s, 's) prel" 
    ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 0, 167] 167) where
[prel_defs]: "pchoice' r P Q = prel_of_rfrel (r * @(rfrel_of_prel P) + (1 - r) * @(rfrel_of_prel Q))\<^sub>e"
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

lemma pseqcomp_mono: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2; Q\<^sub>1 \<le> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (P\<^sub>1 ; Q\<^sub>1) \<le> (P\<^sub>2 ; Q\<^sub>2)"
  apply (simp add: pfun_defs)
  apply (rule le_funI)
  apply (rel_auto)
  apply (rule infsum_mono)
    defer
    defer
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
    using a1 sledgehammer
  show "P\<^sub>1 (a, x) * Q\<^sub>1 (x, b) \<le> P\<^sub>2 (a, x) * Q\<^sub>2 (x, b)"
    
    find_theorems "(?a::real) * ?b \<le> ?c * ?d"

theorem while_unfold:
  "while\<^sub>p b do P od = ((P ; (while\<^sub>p b do P od)) \<lhd>\<^sub>f b \<rhd> II)"
proof -
  have m:"mono (\<lambda>X. (P ; X) \<lhd>\<^sub>f b \<rhd> II)"
    unfolding mono_def sledgehammer
  have "(while b do P od) = (\<nu> X \<bullet> (P \<Zcomp> X) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    by (simp add: while_top_def)
  also have "... = ((P \<Zcomp> (\<nu> X \<bullet> (P \<Zcomp> X) \<^bold>\<lhd> b \<^bold>\<rhd> II)) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    by (subst lfp_unfold, simp_all add: m)
  also have "... = ((P \<Zcomp> while b do P od) \<^bold>\<lhd> b \<^bold>\<rhd> II)"
    by (simp add: while_top_def)
  finally show ?thesis .
qed

(*
typedef real01 = "{(0::real)..1}"
  morphisms real_of_real01 real01_of_real
  apply (rule_tac x = "0" in exI)
  by auto

find_theorems name:"real01"
term "complete_lattice_class"

instantiation real01 :: bot
begin
definition "bot = real01_of_real 0"
instance by (intro_classes)
end

instantiation real01 :: top
begin
definition "top = real01_of_real 1"
instance by (intro_classes)
end

instantiation real01 :: "{one,comm_monoid_add,zero_neq_one}"
begin

definition "0 = real01_of_real 0"
definition "1 = real01_of_real 1"
definition "a + b = real01_of_real (real_of_real01 a + real_of_real01 b)"

lemma real01_eq_0[simp]:
  "r = 0 \<longrightarrow> real01_of_real r = 0"
  "r = 0 \<longrightarrow> 0 = real01_of_real r"
  apply (auto)
  by (simp_all add: zero_real01_def)

lemma real01_eq_1[simp]:
  "r = 1 \<longrightarrow> real01_of_real r = 1"
  "r = 1 \<longrightarrow> 1 = real01_of_real r"
  unfolding one_real01_def by simp_all

lemma real01_add_zero: "(0::real01) + a = a"
  apply (simp only: zero_real01_def plus_real01_def)
  by (smt (verit, ccfv_SIG) atLeastAtMost_iff real01_of_real_inverse real_of_real01_inverse)

lemma real01_zero_neq_one: "0 \<noteq> (1::real01)"
  apply (simp only: zero_real01_def one_real01_def)
  by (smt (verit, ccfv_threshold) atLeastAtMost_iff real01_of_real_inject)

lemma real01_add2: "real01_of_real (real_of_real01 a + real_of_real01 b) = a + b"
  by (simp only: plus_real01_def)

lemma real01_add_commute: "(a::real01) + b = b + a"
  apply (simp only: plus_real01_def)
  by (smt (verit, best))

lemma real01_add_assoc: "(a::real01) + b + c = a + (b + c)"
  apply (simp only: plus_real01_def)
  oops

instance  ...
apply
qed

end

instantiation real01 :: linorder
begin
  definition "x < (y::real01) \<longleftrightarrow> real_of_real01 x < real_of_real01 y"
  definition "x \<le> (y::real01) \<longleftrightarrow> real_of_real01 x \<le> real_of_real01 y"
instance 
  apply (intro_classes)
  using less_eq_real01_def less_real01_def apply fastforce
     apply (simp add: less_eq_real01_def)
  using less_eq_real01_def apply auto[1]
  apply (simp add: less_eq_real01_def real_of_real01_inject)
  using less_eq_real01_def by fastforce
end

print_locale "complete_lattice"
print_classes

instantiation real01 :: complete_lattice
begin
(* definition "bot = (real01_of_real 0)"
definition "top = (real01_of_real 1)"
*)
(* definition "less_eq a b = (real_of_real01 a \<le> real_of_real01 b)"
definition "less a b = (real_of_real01 a < real_of_real01 b)"
*)
definition "sup a b = real01_of_real (max (real_of_real01 a) (real_of_real01 b))"
definition "inf a b = real01_of_real (min (real_of_real01 a) (real_of_real01 b))"

definition "Sup S = (SOME x :: real01. (\<forall>y\<in>S. y \<le> x) \<and> (\<forall>z. (\<forall>y\<in>S. y \<le> z) \<longrightarrow> x \<le> z))"
definition "Inf S = (SOME x :: real01. (\<forall>y\<in>S. x \<le> y) \<and> (\<forall>z. (\<forall>y\<in>S. z \<le> y) \<longrightarrow> z \<le> x))"
instance
  apply (intro_classes)
  apply (auto simp add: bot_real01_def top_real01_def less_eq_real01_def less_real01_def sup_real01_def
      inf_real01_def)
  apply (smt (verit, best) real_of_real01_inverse)
  apply (smt (verit) real_of_real01_inverse)
  apply (smt (verit) real_of_real01_inverse)
  apply (smt (verit) real_of_real01_inverse)
  apply (smt (verit) real_of_real01_inverse)
  apply (smt (verit) real_of_real01_inverse)
  apply (simp add: Inf_real01_def)
  apply (transfer, simp add: top_real01_def)
  sorry
end

type_synonym ('s\<^sub>1, 's\<^sub>2) rvfun = "(\<real>, 's\<^sub>1 \<times> 's\<^sub>2) expr"
type_synonym 's rvhfun = "('s, 's) rvfun"

type_synonym ('s\<^sub>1, 's\<^sub>2) pfun = "(real01, 's\<^sub>1 \<times> 's\<^sub>2) expr"
type_synonym 's phfun = "('s, 's) pfun"

abbreviation "pmap f \<equiv> (\<lambda>v. real_of_real01 (f v))"

lemma pmap_if: "(\<lambda>s. pmap (if s = a then c else d)) = (\<lambda>s. (if s = a then pmap c else pmap d))"
  apply (subst fun_eq_iff)
  by (auto)

typedef ('s\<^sub>1, 's\<^sub>2) pdfun = "{f::('s\<^sub>1, 's\<^sub>2) pfun. (\<forall>s\<^sub>1::'s\<^sub>1. is_sum_1 (pmap ((curry f) s\<^sub>1)))}"
  morphisms of_pdfun of_pfun
  apply (simp add: dist_defs taut_def)
  apply (rule_tac x = "\<lambda>(a, b). if b = c then (real01_of_real 1) else (real01_of_real 0)" in exI)
  apply (auto)
proof -
  have "(\<Sum>\<^sub>\<infinity>s::'s\<^sub>2. pmap (If (s = c) (real01_of_real (1::\<real>))) (real01_of_real (0::\<real>)))
    = (\<Sum>\<^sub>\<infinity>s::'s\<^sub>2. (If (s = c) 1 0))"
    by (smt (verit, best) atLeastAtMost_iff infsum_cong real01_of_real_inverse)
  also have "... = 1"
    by (rule infsum_singleton_1)
  ultimately show "(\<Sum>\<^sub>\<infinity>s::'s\<^sub>2. pmap (If (s = c) (real01_of_real (1::\<real>))) (real01_of_real (0::\<real>))) = 1"
    by presburger
qed

definition pskip :: "'s phfun" ("II\<^sub>p") where
[pfun_defs]: "pskip = (real01_of_real (\<lbrakk> \<lbrakk>II\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>))\<^sub>e"

adhoc_overloading
  uskip pskip

term "II::'s rel"
term "II::'s phfun"

abbreviation passigns_f where 
"passigns_f \<sigma> \<equiv> \<lbrakk> \<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>"

definition passigns :: "('a, 'b) psubst \<Rightarrow> ('a, 'b) pfun" where 
[pfun_defs]: "passigns \<sigma> = (real01_of_real (\<lbrakk> \<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>))\<^sub>e"

adhoc_overloading
  uassigns passigns

term "(s := e)::'s phfun"
term "(s := e)::'s rel"

definition pchoice :: "('s\<^sub>1, 's\<^sub>2) pfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rvfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) pfun \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) pfun" 
  ("(_ \<oplus>\<^bsub>_\<^esub> _)" [61, 0, 60] 60) where
[pfun_defs]: "pchoice P r Q = (real01_of_real (r * P + (1 - r) * Q)\<^sub>e)\<^sub>e"

(* definition pchoice' :: "'s rfhrel \<Rightarrow> ('s, 's) prel \<Rightarrow> ('s, 's) prel \<Rightarrow> ('s, 's) prel" 
    ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 0, 167] 167) where
[prel_defs]: "pchoice' r P Q = prel_of_rfrel (r * @(rfrel_of_prel P) + (1 - r) * @(rfrel_of_prel Q))\<^sub>e"
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
