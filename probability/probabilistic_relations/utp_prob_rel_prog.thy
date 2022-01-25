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

named_theorems prob_rel_defs

(* suggestion: typedef 0 \<le> p \<le> 1*)

typedef ('s\<^sub>1, 's\<^sub>2) prel = "{s::('s\<^sub>1 \<times> 's\<^sub>2 \<Rightarrow> \<real>). is_prob s}"
  morphisms set_of_prel prel_of_set
  using is_prob_def taut_def by force

term "prel_of_set"
term "set_of_prel"
thm "prel_of_set_inverse"

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
[prob_rel_defs]: "reachable_states P s = {s'. (curry (set_of_prel P)) s s' > 0}"

text \<open> A deadlock state has no reachable states from it. \<close>
definition deadlock_state where
[prob_rel_defs]: "deadlock_state P s = (reachable_states P s = {})"

subsection \<open> Probabilistic programming \<close>
(* deadlock: zero and not a distribution *)
definition pzero :: "('s\<^sub>1, 's\<^sub>2) prel" ("0\<^sub>p") where
[prob_rel_defs]: "pzero = prel_of_set (\<lambda> s. 0)"

lemma deadlock_always: "`@(deadlock_state pzero)`"
  apply (simp add: prob_rel_defs)
  by (simp add: is_prob_def prel_of_set_inverse)

(* suggest by simon: bundle: notation here *)
(* ok *)
definition pskip :: "'s phrel" where
[prob_rel_defs]: "pskip = prel_of_set (\<lbrakk> \<lbrakk>II\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"

(* assignment *)
definition passign :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) expr \<Rightarrow> 's phrel" (*(infix ":=\<^sub>p" 162)*) where
[prob_rel_defs]: "passign x e = prel_of_set (\<lbrakk> \<lbrakk>(x := e)\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"

syntax 
  "_passign" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix ":=\<^sub>p" 162) 

translations
  "_passign x e" == "CONST passign x (e)\<^sub>e"
  "_passign x e" <= "_passign x (e)\<^sub>e"

term "x := 1"
term "x := C"
term "x :=\<^sub>p (1)"
term "x :=\<^sub>p C"
term "((set_of_prel P))"
term "(r * @(set_of_prel P) + (1 - r) * @(set_of_prel  Q))\<^sub>e"

(* probabilistic choice *)
definition pchoice :: "('s, 's) prel \<Rightarrow> ('s \<times> 's \<Rightarrow> real) \<Rightarrow> ('s, 's) prel \<Rightarrow> ('s, 's) prel" 
  ("(_ \<oplus>\<^bsub>_\<^esub> _)" [164, 0, 165] 164) where
[prob_rel_defs]: "pchoice P r Q = prel_of_set (r * @(set_of_prel P) + (1 - r) * @(set_of_prel Q))\<^sub>e"

definition pchoice' :: "('s \<times> 's \<Rightarrow> real) \<Rightarrow> ('s, 's) prel \<Rightarrow> ('s, 's) prel \<Rightarrow> ('s, 's) prel" 
    ("(pif (_)/ then (_)/ else (_))" [0, 0, 167] 167) where
[prob_rel_defs]: "pchoice' r P Q = prel_of_set (r * @(set_of_prel P) + (1 - r) * @(set_of_prel Q))\<^sub>e"

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

definition pcomp :: "'s phrel \<Rightarrow> 's phrel \<Rightarrow> 's phrel" (infixl ";\<^sub>p" 163) where
[prob_rel_defs]: "pcomp P Q = prel_of_set 
  (\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> @(set_of_prel P)) * ([ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> @(set_of_prel Q)))\<^sub>e"

definition pparallel :: "('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel" (infixl "\<parallel>\<^sub>p" 166) where
[prob_rel_defs]: "pparallel P Q = prel_of_set \<^bold>\<N> (@(set_of_prel P) * @(set_of_prel Q))\<^sub>e"

term "\<^bold>v\<^sup>> := \<^bold>v\<^sup><"

bundle UTP_Prob_Rel_Syntax
begin

no_notation uskip ("II")
(* how to no_notation a notation that is given in the syntax translation, like below.

no_notation _assign (infix ":=" 76)
*)
(* no_notation (infixl "\<parallel>" 166) *)
(* no_notation If ("(if (_)/ then (_)/ else (_))" [0, 0, 10] 10) *)

notation pskip ("II")
(* notation passign (infix ":=" 162) *)
notation pcomp (infixl ";" 163)
(* notation pchoice ("(_ \<oplus>\<^bsub>_\<^esub> _)" [164, 0, 165] 164) *)
(* notation pparallel (infixl "\<parallel>" 166) *)

end

unbundle UTP_Prob_Rel_Syntax

consts
  parallel_c :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<^bold>\<parallel>" 164)

adhoc_overloading
  parallel_c pparallel and parallel_c Sublist.parallel

term "II"
term "\<^bold>v\<^sup>> := \<^bold>v\<^sup><"
term "$\<^bold>v\<^sup>> := $\<^bold>v\<^sup><"
term "(P;Q)"
term "((P::('s, 's) prel) \<^bold>\<parallel> Q)"
term "((P::'s list) \<^bold>\<parallel> Q)"
term "([] \<^bold>\<parallel> [a])"

(*
syntax 
  "_pcond" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(if (_)/ then (_)/ else (_))" [0, 0, 167] 167)

translations
  "_pcond P b Q" == "CONST pcond P b Q"
*) 
(*
consts pchoice_cond :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd" ("(pif (_)/ then (_)/ else (_))" [0, 0, 167] 167)

adhoc_overloading
  pchoice_cond pcond
  pchoice_cond pchoice'


term "if True then P else Q"
term "pif R then P else Q"
*)
term "pif R then P else Q"

subsection \<open> Syntactical examples \<close>
text \<open> Example 13 from Jim's draft report. 
Two robots, the Cyberman C and the Dalek D, attack Doctor Who’s Tardis once a day between them. 
C has a probability 1/2 of a successful attack, 
while D has a probability 3/10 of a successful attack. 
C attacks more often than D, with a probability of 3/5 on a particular day 
(and so D attacks with a probability of 2/5 on that day). 
What is the probability that there is a successful attack today?\<close>

datatype Attacker = C | D
datatype Status = S | F

alphabet DWTA_state = 
  r:: Attacker
  a:: Status

term "r := C"
term "r :=\<^sub>p (C)\<^sub>e"
term "(pif (3/5)\<^sub>e then (r := (C)\<^sub>e) else (r := (D)\<^sub>e))"
definition dwta where
"dwta = (pif 3/5 then (r := (C)\<^sub>e) else (r := (D)\<^sub>e))\<^sub>e"

subsection \<open> Distributions - Healthiness conditions \<close>
term "`is_dist (@(curry P))`"

text \<open> Is the final states of P from an initial state s a distribution? \<close>
abbreviation is_dist_final :: "('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> 's\<^sub>1 \<Rightarrow> \<bool>" where 
"is_dist_final P s \<equiv> is_dist ((curry P) s)"

text \<open> Is the final states of P from any initial state a distribution? \<close>
abbreviation is_dist_final_all :: "('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> \<bool>" where 
"is_dist_final_all P \<equiv> `is_dist (@(curry P))`"

(*
definition PROB1:: "('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel" where
"PROB1 P = (if PROB P then pzero else P)"
*)

lemma "\<not>is_dist_final_all pzero"
  by (simp add: dist_defs prob_rel_defs)

term "is_filter"
term "Rep_filter"
term "Abs_filter"
term "eventually"

lemma "has_sum (\<lambda>sa. if sa = s then 1::\<real> else (0::\<real>)) (UNIV) 1"
  apply (simp add: has_sum_def)
  apply (simp add: tendsto_def)
  apply (simp add: finite_subsets_at_top_def)
  apply (simp add: principal_def)
  apply (auto)
  sorry

lemma "is_dist_final_all II\<^sub>p"
  apply (simp add: prob_rel_defs Id_def expr_defs dist_defs)
  apply (auto)
  sorry


end
