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

(* Real-valued functions whose domain is Cartesian product of initial and final states. *)
type_synonym ('s\<^sub>1, 's\<^sub>2) rfrel = "(\<real>, 's\<^sub>1 \<times> 's\<^sub>2) expr"
type_synonym 's rfhrel = "('s, 's) rfrel"

(* The final states of a program characterised by f is a distribution *)
abbreviation "is_final_distribution f \<equiv> (\<forall>s\<^sub>1::'s\<^sub>1. is_dist ((curry f) s\<^sub>1))"

\<comment> \<open>A question here: can we use existing PMFs as types for prel? Why a new type here. \<close>
typedef ('s\<^sub>1, 's\<^sub>2) prel = "{f::('s\<^sub>1, 's\<^sub>2) rfrel. is_final_distribution f}"
  morphisms rfrel_of_prel prel_of_rfrel
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

find_theorems "prel.rfrel_of_prel"
term "prel_of_rfrel"
term "rfrel_of_prel"
thm "prel_of_rfrel_inverse"
thm "rfrel_of_prel"

type_synonym 's phrel = "('s, 's) prel"

text \<open> Reachable states of @{text P} from an initial state @{text s} are such states @{text s'} 
that have probability @{text "P (s, s')"} larger than 0. 
\<close>
definition reachable_states :: "('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> 's\<^sub>1 \<Rightarrow> 's\<^sub>2 set" where
[prel_defs]: "reachable_states P s = {s'. (curry (rfrel_of_prel P)) s s' > 0}"

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
[prel_defs]: "pzero = prel_of_rfrel (\<lambda> s. 0)"

lemma deadlock_always: "`@(deadlock_state pzero)`"
  apply (simp add: prel_defs)
  by (simp add: is_prob_def prel_of_rfrel_inverse)
*)

subsubsection \<open> Skip \<close>
(* The purpose of this abbreviation is to make later reference to this function inside pskip easier. *)
abbreviation pskip\<^sub>_f ("II\<^sub>f") where
  "pskip\<^sub>_f \<equiv> \<lbrakk> \<lbrakk>II\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>"

definition pskip :: "'s phrel" ("II\<^sub>p") where
[prel_defs]: "pskip = prel_of_rfrel (pskip\<^sub>_f)"

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

subsubsection \<open> Assignment \<close>
abbreviation passigns_f where 
"passigns_f \<sigma> \<equiv> \<lbrakk> \<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>"

definition passigns :: "('a, 'b) psubst \<Rightarrow> ('a, 'b) prel" where 
[prel_defs]: "passigns \<sigma> = prel_of_rfrel (passigns_f \<sigma>)"

adhoc_overloading
  uassigns passigns

term "(s := e)::'s phrel"
term "(s := e)::'s rel"
(* assignment *)
(*
definition passign :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) expr \<Rightarrow> 's phrel" (*(infix ":=\<^sub>p" 162)*) where
[prel_defs]: "passign x e = prel_of_rfrel (\<lbrakk> \<lbrakk>(x := e)\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"

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

term "((rfrel_of_prel P))"
term "(r * @(rfrel_of_prel P) + (1 - r) * @(rfrel_of_prel  Q))\<^sub>e"

subsubsection \<open> Probabilistic choice \<close>
abbreviation pchoice_f ("(_ \<oplus>\<^sub>f\<^bsub>_\<^esub> _)" [61, 0, 60] 60) where 
"pchoice_f P r Q \<equiv> (r * P + (1 - r) * Q)\<^sub>e"

definition pchoice :: "('s, 's) prel \<Rightarrow> 's rfhrel \<Rightarrow> ('s, 's) prel \<Rightarrow> ('s, 's) prel" 
  ("(_ \<oplus>\<^bsub>_\<^esub> _)" [61, 0, 60] 60) where
[prel_defs]: "pchoice P r Q = prel_of_rfrel (pchoice_f (rfrel_of_prel P) r (rfrel_of_prel Q))"

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

text \<open> The definition @{text "lift_pre"} below lifts a real-valued function @{text r} over the initial 
state to over the initial and final states. In the definition of @{term "pchoice"}, we use a general 
function for the weight @{text r}, which is @{text "'s \<times> 's \<Rightarrow> \<real>"}. However, now we only consider 
the probabilistic choice whose weight is only over the initial state. Then @{text "lift_pre"} is 
useful to lift a such function to a more general function used in @{term "pchoice"}.
\<close>
abbreviation lift_pre where "lift_pre r \<equiv> (\<lambda>(s, s'). r s)"
notation lift_pre ("_\<^sup>\<Up>")
expr_ctr lift_pre

(* conditional choice *)
definition pcond :: "('s\<^sub>1, 's\<^sub>2) rpred \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel" where 
"pcond b P Q \<equiv> prel_of_rfrel (if b then @(rfrel_of_prel P) else @(rfrel_of_prel Q))\<^sub>e"

subsubsection \<open> Sequential composition \<close>
term "(rfrel_of_prel (P::('s phrel)))\<lbrakk>v\<^sub>0/\<^bold>v\<^sup>>\<rbrakk>"
term "\<^bold>v\<^sup>>"
term "(\<Sum>\<^sub>\<infinity> v\<^sub>0. (P\<lbrakk>\<guillemotleft>v\<^sub>0\<guillemotright>/\<^bold>v\<^sup>>\<rbrakk>) * (Q\<lbrakk>\<guillemotleft>v\<^sub>0\<guillemotright>/\<^bold>v\<^sup><\<rbrakk>))\<^sub>e"
term "[ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> (rfrel_of_prel (P::'s phrel))"
term "(\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> P) * ([ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> Q))\<^sub>e"
term "(\<exists> v\<^sub>0. [ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> \<lbrakk>P\<rbrakk>\<^sub>P \<and> [ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> \<lbrakk>Q\<rbrakk>\<^sub>P)\<^sub>e"
term "if True then a else b"
term " 
  (\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> v\<^sub>0 ] \<dagger> @(rfrel_of_prel P)) * ([ \<^bold>v\<^sup>< \<leadsto> v\<^sub>0 ] \<dagger> @(rfrel_of_prel Q)))\<^sub>e"
thm "pred_seq_hom"

abbreviation pcomp_f :: "'s rfhrel \<Rightarrow> 's rfhrel \<Rightarrow> 's rfhrel" (infixl ";\<^sub>f" 59) where 
"pcomp_f P Q \<equiv> (\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> P) * ([ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> Q))\<^sub>e" 

definition pcomp :: "'s phrel \<Rightarrow> 's phrel \<Rightarrow> 's phrel" (*(infixl ";\<^sub>p" 59)*) where
[prel_defs]: "pcomp P Q = prel_of_rfrel (pcomp_f (rfrel_of_prel P) (rfrel_of_prel Q))"

subsubsection \<open> Parallel composition \<close>

abbreviation pparallel_f :: "('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel" (infixl "\<parallel>\<^sub>f" 58)
  where "pparallel_f P Q \<equiv> (\<^bold>N (P * Q)\<^sub>e)"

abbreviation pparallel_f' :: "('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rfrel"
  where "pparallel_f' P Q \<equiv> ((P * Q) / (\<Sum>\<^sub>\<infinity> s'. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>s'\<guillemotright> ] \<dagger> P) * ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>s'\<guillemotright> ] \<dagger> Q)))\<^sub>e"

lemma pparallel_f_eq: "pparallel_f P Q = pparallel_f' P Q"
  apply (simp add: dist_defs)
  by (expr_auto)

definition pparallel :: "('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel" (infixl "\<parallel>\<^sub>p" 58) where
[prel_defs]: "pparallel P Q = prel_of_rfrel (pparallel_f (rfrel_of_prel P) (rfrel_of_prel Q))"

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
