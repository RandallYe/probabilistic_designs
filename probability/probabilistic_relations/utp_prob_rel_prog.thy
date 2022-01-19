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

type_synonym ('s\<^sub>1, 's\<^sub>2) prel = "('s\<^sub>1 \<times> 's\<^sub>2 \<Rightarrow> \<real>)"
type_synonym 's phrel = "('s \<times> 's \<Rightarrow> \<real>)"

(* Nondeterministic probabilistic programming 
\<lambda>s:: s\<^sub>1 \<times> (s\<^sub>2 \<times> \<real>). \<lbrakk>P(fst s, fst snd s)\<rbrakk>\<^sub>\<I> = snd snd s
*)
term "\<lambda>s:: 's\<^sub>1 \<times> ('s\<^sub>2 \<times> \<real>). ((\<lbrakk>P(fst s, fst (snd s))\<rbrakk>\<^sub>\<I> s = snd (snd s)))"
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
[prob_rel_defs]: "reachable_states P s = {s'. (curry P) s s' > 0}"

text \<open> A deadlock state has no reachable states from it. \<close>
definition deadlock_state where
[prob_rel_defs]: "deadlock_state P s = (reachable_states P s = {})"

subsection \<open> Probabilistic programming \<close>
(* deadlock: zero and not a distribution *)
definition pzero :: "('s\<^sub>1, 's\<^sub>2) prel" ("0\<^sub>p") where
[prob_rel_defs]: "pzero = (\<lambda> s. 0)"

lemma deadlock_always: "`@(deadlock_state pzero)`"
  by (simp add: prob_rel_defs)

(* ok *)
definition pskip :: "'s phrel" ("II\<^sub>p") where
[prob_rel_defs]: "pskip = \<lbrakk> \<lbrakk>II\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>"

(* assignment *)
definition passign :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) expr \<Rightarrow> 's phrel" (infix ":=\<^sub>p" 162) where
[prob_rel_defs]: "passign x e = \<lbrakk> \<lbrakk>(x := e)\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>"

(* probabilistic choice *)
definition pchoice :: "('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> real \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel" 
  ("(_ \<oplus>\<^bsub>_\<^esub> _)" [164, 0, 165] 164) where
[prob_rel_defs]: "pchoice P r Q = (\<guillemotleft>r\<guillemotright> * P + (1 - \<guillemotleft>r\<guillemotright>) * Q)\<^sub>e"

(* conditional choice *)
abbreviation pcond :: "('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) rpred \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel" where 
"pcond P b Q \<equiv> (if b then P else Q)\<^sub>e"

(* sequential composition *)
term "(P::('s phrel))\<lbrakk>v\<^sub>0/\<^bold>v\<^sup>>\<rbrakk>"
term "\<^bold>v\<^sup>>"
term "(\<Sum>\<^sub>\<infinity> v\<^sub>0. (P\<lbrakk>\<guillemotleft>v\<^sub>0\<guillemotright>/\<^bold>v\<^sup>>\<rbrakk>) * (Q\<lbrakk>\<guillemotleft>v\<^sub>0\<guillemotright>/\<^bold>v\<^sup><\<rbrakk>))\<^sub>e"
term "[ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> P::'s phrel"
term "(\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> P) * ([ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> Q))\<^sub>e"
term "(\<exists> v\<^sub>0. [ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> \<lbrakk>P\<rbrakk>\<^sub>P \<and> [ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> \<lbrakk>Q\<rbrakk>\<^sub>P)\<^sub>e"

definition pcomp :: "'s phrel \<Rightarrow> 's phrel \<Rightarrow> 's phrel" (infixl ";\<^sub>p" 163) where
[prob_rel_defs]: "pcomp P Q = (\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> P) * ([ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> Q))\<^sub>e"

definition pparallel :: "('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel" (infixl "\<parallel>\<^sub>p" 166) where
[prob_rel_defs]: "pparallel P Q = \<^bold>\<N> (P * Q)\<^sub>e"

subsection \<open> Distributions - Healthiness conditions \<close>
term "`is_dist (@(curry P))`"

text \<open> For any initial state @{text s}, its final  \<close>
abbreviation PROB :: "('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> \<bool>" where 
"PROB P \<equiv> `is_dist (@(curry P))`"

definition PROB1:: "('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel" where
"PROB1 P = (if PROB P then pzero else P)"

lemma "\<not>PROB pzero"
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

lemma "PROB II\<^sub>p"
  apply (simp add: prob_rel_defs Id_def expr_defs dist_defs)
  apply (auto)
  sorry


end
