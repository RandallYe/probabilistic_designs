section \<open> Probabilistic relation programming \<close>

theory utp_prob_rel_prog
  imports 
    "HOL.Series" 
    "HOL-Analysis.Infinite_Sum" 
    "utp_iverson_bracket" 
    "utp_distribution"
begin 

unbundle UTP_Syntax

declare [[show_types]]

named_theorems prel_defs

(* suggestion: typedef 0 \<le> p \<le> 1*)

(* typedef ('s\<^sub>1, 's\<^sub>2) prel = "{s::('s\<^sub>1 \<times> 's\<^sub>2 \<Rightarrow> \<real>). is_prob s}"
  morphisms set_of_prel prel_of_set
  using is_prob_def taut_def by force
*)
typedef ('s\<^sub>1, 's\<^sub>2) prel = "{s::('s\<^sub>1 \<times> 's\<^sub>2 \<Rightarrow> \<real>). (\<forall>s\<^sub>1::'s\<^sub>1. is_dist ((curry s) s\<^sub>1))}"
  morphisms set_of_prel prel_of_set
  apply (simp add: dist_defs taut_def)
  apply (rule_tac x = "\<lambda>(a,b). if b = c then 1 else 0" in exI)
  apply (auto)
  apply (rule infsumI)
  apply (simp add: has_sum_def)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
  apply (rule_tac x = "{c}" in exI)
  by (auto)

(*
  prel_of_set_cases:
    (\<And>y::?'s\<^sub>1 \<times> ?'s\<^sub>2 \<Rightarrow> \<real>.
        (?x::(?'s\<^sub>1, ?'s\<^sub>2) prel) = prel_of_set y \<Longrightarrow> y \<in> {s::?'s\<^sub>1 \<times> ?'s\<^sub>2 \<Rightarrow> \<real>. is_prob s} \<Longrightarrow> ?P::\<bool>) \<Longrightarrow>
    ?P
  prel_of_set_induct:
    (\<And>y::?'s\<^sub>1 \<times> ?'s\<^sub>2 \<Rightarrow> \<real>.
        y \<in> {s::?'s\<^sub>1 \<times> ?'s\<^sub>2 \<Rightarrow> \<real>. is_prob s} \<Longrightarrow> (?P::(?'s\<^sub>1, ?'s\<^sub>2) prel \<Rightarrow> \<bool>) (prel_of_set y)) \<Longrightarrow>
    ?P (?x::(?'s\<^sub>1, ?'s\<^sub>2) prel)
  prel_of_set_inject:
    (?x::?'s\<^sub>1 \<times> ?'s\<^sub>2 \<Rightarrow> \<real>) \<in> {s::?'s\<^sub>1 \<times> ?'s\<^sub>2 \<Rightarrow> \<real>. is_prob s} \<Longrightarrow>
    (?y::?'s\<^sub>1 \<times> ?'s\<^sub>2 \<Rightarrow> \<real>) \<in> {s::?'s\<^sub>1 \<times> ?'s\<^sub>2 \<Rightarrow> \<real>. is_prob s} \<Longrightarrow> (prel_of_set ?x = prel_of_set ?y) = (?x = ?y)
  prel_of_set_inverse:
    (?y::?'s\<^sub>1 \<times> ?'s\<^sub>2 \<Rightarrow> \<real>) \<in> {s::?'s\<^sub>1 \<times> ?'s\<^sub>2 \<Rightarrow> \<real>. is_dist s} \<Longrightarrow> set_of_prel (prel_of_set ?y) = ?y
  set_of_prel: set_of_prel (?x::(?'s\<^sub>1, ?'s\<^sub>2) prel) \<in> {s::?'s\<^sub>1 \<times> ?'s\<^sub>2 \<Rightarrow> \<real>. is_prob s}
  set_of_prel_cases:
    (?y::?'s\<^sub>1 \<times> ?'s\<^sub>2 \<Rightarrow> \<real>) \<in> {s::?'s\<^sub>1 \<times> ?'s\<^sub>2 \<Rightarrow> \<real>. is_prob s} \<Longrightarrow>
    (\<And>x::(?'s\<^sub>1, ?'s\<^sub>2) prel. ?y = set_of_prel x \<Longrightarrow> ?P::\<bool>) \<Longrightarrow> ?P
  set_of_prel_induct:
    (?y::?'s\<^sub>1 \<times> ?'s\<^sub>2 \<Rightarrow> \<real>) \<in> {s::?'s\<^sub>1 \<times> ?'s\<^sub>2 \<Rightarrow> \<real>. is_prob s} \<Longrightarrow>
    (\<And>x::(?'s\<^sub>1, ?'s\<^sub>2) prel. (?P::(?'s\<^sub>1 \<times> ?'s\<^sub>2 \<Rightarrow> \<real>) \<Rightarrow> \<bool>) (set_of_prel x)) \<Longrightarrow> ?P ?y
  set_of_prel_inject: (set_of_prel (?x::(?'s\<^sub>1, ?'s\<^sub>2) prel) = set_of_prel (?y::(?'s\<^sub>1, ?'s\<^sub>2) prel)) = (?x = ?y)
  set_of_prel_inverse: prel_of_set (set_of_prel (?x::(?'s\<^sub>1, ?'s\<^sub>2) prel)) = ?x
*)
find_theorems "prel.set_of_prel"
term "prel_of_set"
term "set_of_prel"
thm "prel_of_set_inverse"
thm "set_of_prel"

type_synonym 's phrel = "('s, 's) prel"

(* type_synonym ('s\<^sub>1, 's\<^sub>2) prel = "('s\<^sub>1 \<times> 's\<^sub>2 \<Rightarrow> \<real>)" *)
(* type_synonym 's phrel = "('s \<times> 's \<Rightarrow> \<real>)" *)

(* Nondeterministic probabilistic programming 
\<lambda>s:: s\<^sub>1 \<times> (s\<^sub>2 \<times> \<real>). \<lbrakk>P(fst s, fst snd s)\<rbrakk>\<^sub>\<I> = snd snd s
*)
(*term "\<lambda>s:: 's\<^sub>1 \<times> ('s\<^sub>2 \<times> \<real>). ((\<lbrakk>P(fst s, fst (snd s))\<rbrakk>\<^sub>\<I> s = snd (snd s)))"*)
type_synonym ('s\<^sub>1, 's\<^sub>2) prel2 = "('s\<^sub>1 \<leftrightarrow> ('s\<^sub>2 \<leftrightarrow> \<real>))"
(* example
datatype Da = s1 | s2 | s3 | s4
definition D :: "(Da, Da) prel2" where
"D = {(s1, {(s2, 0.5::\<real>), (s3,0.5)}), (s1, {(s3, 0.3), (s4,0.7)})}"

term "{(s1, {(s2, 0.5::\<real>), (s3,0.5)}), (s1, {(s3, 0.3), (s4,0.7)})}"
*)

text \<open> Reachable states of @{text P} from an initial state @{text s} are such states @{text s'} 
that have probability @{text "P (s, s')"} larger than 0. 
\<close>
definition reachable_states :: "('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> 's\<^sub>1 \<Rightarrow> 's\<^sub>2 set" where
[prel_defs]: "reachable_states P s = {s'. (curry (set_of_prel P)) s s' > 0}"

(*
text \<open> A deadlock state has no reachable states from it. \<close>
definition deadlock_state where
[prel_defs]: "deadlock_state P s = (reachable_states P s = {})"
*)

subsection \<open> Probabilistic programming \<close>
(* Priorities from larger (tighter) to smaller:
  II, :=\<^sub>p, pif then else, ;, \<parallel> 
*)

(*
(* deadlock: zero and not a distribution *)
definition pzero :: "('s\<^sub>1, 's\<^sub>2) prel" ("0\<^sub>p") where
[prel_defs]: "pzero = prel_of_set (\<lambda> s. 0)"

lemma deadlock_always: "`@(deadlock_state pzero)`"
  apply (simp add: prel_defs)
  by (simp add: is_prob_def prel_of_set_inverse)
*)

(* suggest by simon: bundle: notation here *)
(* ok *)
definition pskip :: "'s phrel" ("II\<^sub>p") where
[prel_defs]: "pskip = prel_of_set (\<lbrakk> \<lbrakk>II\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"

adhoc_overloading
  uskip pskip

term "II::'s rel"
term "II::'s phrel"
term "x := ($x + 1)"
term "x\<^sup>> := ($x\<^sup>< + 1)"

text \<open> The change of precedence of := in utp_rel.thy from 76 to 61 (otherwise x := x+1 won't be 
parsed correctly). But this change, as discussed in @{url \<open>https://github.com/isabelle-utp/UTP/pull/1\<close>} 
may cause a problem for \relcomp (\Zcomp) because its precedence is 75 now. After this change, \Zcomp will 
be bound stronger than := .
\<close>
term "((x := 1)::'s rel) \<Zcomp> y := c"

text \<open>As Simon recommended, we could use another annotation with difference precedence for relcomp. \<close>

notation relcomp (infixr ";;" 55)
term "x := $x + 1" (* OK. := (61) and + (65) *)
term "x := $x + 1 ;; P" 
term "x := $x + 1 \<Zcomp> P" (* Not parsed because \<Zcomp> (75) *)
term "x := $x + 1 ;; y := $y - 1" 
term "p \<union> q \<Zcomp> P" (* (p \<union> (q \<Zcomp> P)) *) (* \<union> (65) *)
term "p \<union> q ;; P" (* (p \<union> q) ;; P*)
term "p \<inter> q ;; P \<union> Q" (* (p \<inter> q) ;; (P \<union> Q) *) (* \<inter> (70) *)
term "p  \<inter> q \<Zcomp> P \<union> Q" (* (p \<inter> (q ;; P)) \<union> Q *)

term "((x := 1)::'s rel) ;; y := c"
term "((x := 1)::'s rel) ;; (y + 1)"
term "\<lambda>q. x"
term "if b then c else q"
term "1/2"
term "a - {}"
term "f o g"

definition passigns :: "('a, 'b) psubst \<Rightarrow> ('a, 'b) prel" where 
[prel_defs]: "passigns \<sigma> = prel_of_set (\<lbrakk> \<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"

adhoc_overloading
  uassigns passigns

term "(s := e)::'s phrel"
term "(s := e)::'s rel"
(* assignment *)
(*
definition passign :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) expr \<Rightarrow> 's phrel" (*(infix ":=\<^sub>p" 162)*) where
[prel_defs]: "passign x e = prel_of_set (\<lbrakk> \<lbrakk>(x := e)\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"

syntax 
  "_passign" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix ":=\<^sub>p" 30) 

translations
  "_passign x e" == "CONST passign x (e)\<^sub>e"
  "_passign x e" <= "_passign x (e)\<^sub>e"
*)
term "(x := 1)::'s rel"
term "(x := C)::'s phrel"
(* Question: what priority should I give? 
If the priority of :=\<^sub>p is larger (tighter) than + (65), then the syntax below is incorrect.
Otherwise, it should be correct
*)
(* term "x :=\<^sub>p 1 + p" *)
(* TODO: Simon: contact Christine about suggestion precedence ... reference from ITree: *)
term "(x := $x + 1)::'s rel"
term "(x := ($x + 1))::'s rel"
(* \<^bold>v shouldn't be the LHS of an assignment *)
term "(\<^bold>v\<^sup>> := $\<^bold>v\<^sup><)::'s phrel"
term "($\<^bold>v\<^sup>> = $\<^bold>v\<^sup><)"

term "((set_of_prel P))"
term "(r * @(set_of_prel P) + (1 - r) * @(set_of_prel  Q))\<^sub>e"

(* probabilistic choice *)
definition pchoice :: "('s, 's) prel \<Rightarrow> ('s \<times> 's \<Rightarrow> \<real>) \<Rightarrow> ('s, 's) prel \<Rightarrow> ('s, 's) prel" 
  ("(_ \<oplus>\<^bsub>_\<^esub> _)" [61, 0, 60] 60) where
[prel_defs]: "pchoice P r Q = prel_of_set (r * @(set_of_prel P) + (1 - r) * @(set_of_prel Q))\<^sub>e"

(* definition pchoice' :: "('s \<times> 's \<Rightarrow> \<real>) \<Rightarrow> ('s, 's) prel \<Rightarrow> ('s, 's) prel \<Rightarrow> ('s, 's) prel" 
    ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 0, 167] 167) where
[prel_defs]: "pchoice' r P Q = prel_of_set (r * @(set_of_prel P) + (1 - r) * @(set_of_prel Q))\<^sub>e"
*)

syntax 
  "_pchoice" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 61, 60] 60) 

translations
  "_pchoice r P Q" == "CONST pchoice P (r)\<^sub>e Q"
  "_pchoice r P Q" <= "_pchoice (r)\<^sub>e P Q"

term "if\<^sub>p 0.5 then P else Q"
term "if\<^sub>p R then P else Q"
term "if\<^sub>p R then P else Q = if\<^sub>p R then P else Q"

(* conditional choice *)
definition pcond :: "('s\<^sub>1, 's\<^sub>2) rpred \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel" where 
"pcond b P Q \<equiv> prel_of_set (if b then @(set_of_prel P) else @(set_of_prel Q))\<^sub>e"

(* sequential composition *)
term "(set_of_prel (P::('s phrel)))\<lbrakk>v\<^sub>0/\<^bold>v\<^sup>>\<rbrakk>"
term "\<^bold>v\<^sup>>"
term "(\<Sum>\<^sub>\<infinity> v\<^sub>0. (P\<lbrakk>\<guillemotleft>v\<^sub>0\<guillemotright>/\<^bold>v\<^sup>>\<rbrakk>) * (Q\<lbrakk>\<guillemotleft>v\<^sub>0\<guillemotright>/\<^bold>v\<^sup><\<rbrakk>))\<^sub>e"
term "[ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> (set_of_prel (P::'s phrel))"
term "(\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> P) * ([ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> Q))\<^sub>e"
term "(\<exists> v\<^sub>0. [ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> \<lbrakk>P\<rbrakk>\<^sub>P \<and> [ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> \<lbrakk>Q\<rbrakk>\<^sub>P)\<^sub>e"
term "if True then a else b"
term " 
  (\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> v\<^sub>0 ] \<dagger> @(set_of_prel P)) * ([ \<^bold>v\<^sup>< \<leadsto> v\<^sub>0 ] \<dagger> @(set_of_prel Q)))\<^sub>e"
thm "pred_seq_hom"

definition pcomp :: "'s phrel \<Rightarrow> 's phrel \<Rightarrow> 's phrel" (infixl ";\<^sub>p" 59) where
[prel_defs]: "pcomp P Q = prel_of_set 
    (\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> @(set_of_prel P)) * ([ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> @(set_of_prel Q)))\<^sub>e"


definition pparallel :: "('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel" (infixl "\<parallel>\<^sub>p" 58) where
[prel_defs]: "pparallel P Q = prel_of_set (\<^bold>\<N> (@(set_of_prel P) * @(set_of_prel Q))\<^sub>e)"

no_notation Sublist.parallel (infixl "\<parallel>" 50)
consts
  parallel_c :: "'a \<Rightarrow> 'a \<Rightarrow> 'c" (infixl "\<parallel>" 58)

adhoc_overloading
  parallel_c pparallel and parallel_c Sublist.parallel

term "((P::('s, 's) prel) \<parallel> Q)"
term "((P::'s list) \<parallel> Q)"
term "([] \<parallel> [a])"

bundle UTP_Prob_Rel_Syntax
begin

(* no_notation uskip ("II") *)
(* notation pskip ("II") *)
(* how to no_notation a notation that is given in the syntax translation, like below.

no_notation _assign (infix ":=" 76)
*)
(* no_notation (infixl "\<parallel>" 166) *)
(* no_notation If ("(if (_)/ then (_)/ else (_))" [0, 0, 10] 10) *)


(* notation passign (infix ":=" 162) *)
notation pcomp (infixl ";" 59)
(* notation pchoice ("(_ \<oplus>\<^bsub>_\<^esub> _)" [164, 0, 165] 164) *)
(* notation pparallel (infixl "\<parallel>" 166) *)

end

unbundle UTP_Prob_Rel_Syntax

(*
syntax 
  "_pcond" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(if (_)/ then (_)/ else (_))" [0, 0, 167] 167)

translations
  "_pcond P b Q" == "CONST pcond P b Q"
*) 
(*
consts pchoice_cond :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd" ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 0, 167] 167)

adhoc_overloading
  pchoice_cond pcond
  pchoice_cond pchoice'


term "if True then P else Q"
term "if\<^sub>p R then P else Q"
*)

subsection \<open> \<close>

end
