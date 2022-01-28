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
    (?y::?'s\<^sub>1 \<times> ?'s\<^sub>2 \<Rightarrow> \<real>) \<in> {s::?'s\<^sub>1 \<times> ?'s\<^sub>2 \<Rightarrow> \<real>. is_prob s} \<Longrightarrow> set_of_prel (prel_of_set ?y) = ?y
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
(* Priorities from larger (tighter) to smaller:
  II, :=\<^sub>p, pif then else, ;, \<parallel> 
*)

(* deadlock: zero and not a distribution *)
definition pzero :: "('s\<^sub>1, 's\<^sub>2) prel" ("0\<^sub>p") where
[prob_rel_defs]: "pzero = prel_of_set (\<lambda> s. 0)"

lemma deadlock_always: "`@(deadlock_state pzero)`"
  apply (simp add: prob_rel_defs)
  by (simp add: is_prob_def prel_of_set_inverse)

(* suggest by simon: bundle: notation here *)
(* ok *)
definition pskip :: "'s phrel" ("II\<^sub>p") where
[prob_rel_defs]: "pskip = prel_of_set (\<lbrakk> \<lbrakk>II\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"

adhoc_overloading
  uskip pskip

term "II::'s rel"
term "II::'s phrel"
term "x := ($x + 1)"

definition passigns :: "('a, 'b) psubst \<Rightarrow> ('a, 'b) prel" where 
[prob_rel_defs]: "passigns \<sigma> = prel_of_set (\<lbrakk> \<lbrakk>\<langle>\<sigma>\<rangle>\<^sub>a\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"

adhoc_overloading
  uassigns passigns

term "(s := e)::'s phrel"
term "(s := e)::'s rel"
(* assignment *)
(*
definition passign :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) expr \<Rightarrow> 's phrel" (*(infix ":=\<^sub>p" 162)*) where
[prob_rel_defs]: "passign x e = prel_of_set (\<lbrakk> \<lbrakk>(x := e)\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>)"

syntax 
  "_passign" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix ":=\<^sub>p" 30) 

translations
  "_passign x e" == "CONST passign x (e)\<^sub>e"
  "_passign x e" <= "_passign x (e)\<^sub>e"
*)
term "(x := 1)::'s phrel"
term "(x := C)::'s phrel"
(* Question: what priority should I give? 
If the priority of :=\<^sub>p is larger (tighter) than + (65), then the syntax below is incorrect.
Otherwise, it should be correct
*)
(* term "x :=\<^sub>p 1 + p" *)
(* TODO: Simon: contact Christine about suggestion precedence ... reference from ITree: *)
term "(x := $x + 1)::'s rel"
term "(x := ($x + 1))::'s rel"
term "(\<^bold>v\<^sup>> := $\<^bold>v\<^sup><)::'s phrel"

term "((set_of_prel P))"
term "(r * @(set_of_prel P) + (1 - r) * @(set_of_prel  Q))\<^sub>e"

(* probabilistic choice *)
definition pchoice :: "('s, 's) prel \<Rightarrow> ('s \<times> 's \<Rightarrow> \<real>) \<Rightarrow> ('s, 's) prel \<Rightarrow> ('s, 's) prel" 
  ("(_ \<oplus>\<^bsub>_\<^esub> _)" [30, 0, 29] 29) where
[prob_rel_defs]: "pchoice P r Q = prel_of_set (r * @(set_of_prel P) + (1 - r) * @(set_of_prel Q))\<^sub>e"

(* definition pchoice' :: "('s \<times> 's \<Rightarrow> \<real>) \<Rightarrow> ('s, 's) prel \<Rightarrow> ('s, 's) prel \<Rightarrow> ('s, 's) prel" 
    ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 0, 167] 167) where
[prob_rel_defs]: "pchoice' r P Q = prel_of_set (r * @(set_of_prel P) + (1 - r) * @(set_of_prel Q))\<^sub>e"
*)

syntax 
  "_pchoice" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(if\<^sub>p (_)/ then (_)/ else (_))" [0, 30, 29] 29) 

translations
  "_pchoice r P Q" == "CONST pchoice P (r)\<^sub>e Q"
  "_pchoice r P Q" <= "_pchoice (r)\<^sub>e P Q"

term "if\<^sub>p 0.5 then P else Q"
term "if\<^sub>p R then P else Q"

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

definition pcomp :: "'s phrel \<Rightarrow> 's phrel \<Rightarrow> 's phrel" (infixl ";\<^sub>p" 28) where
[prob_rel_defs]: "pcomp P Q = prel_of_set 
    (\<Sum>\<^sub>\<infinity> v\<^sub>0. ([ \<^bold>v\<^sup>> \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> @(set_of_prel P)) * ([ \<^bold>v\<^sup>< \<leadsto> \<guillemotleft>v\<^sub>0\<guillemotright> ] \<dagger> @(set_of_prel Q)))\<^sub>e"

term "(P;\<^sub>p Q)"

definition pparallel :: "('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) prel" (infixl "\<parallel>\<^sub>p" 27) where
[prob_rel_defs]: "pparallel P Q = prel_of_set \<^bold>\<N> (@(set_of_prel P) * @(set_of_prel Q))\<^sub>e"

no_notation Sublist.parallel (infixl "\<parallel>" 50)
consts
  parallel_c :: "'a \<Rightarrow> 'a \<Rightarrow> 'c" (infixl "\<parallel>" 27)

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
notation pcomp (infixl ";" 28)
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
subsection \<open> Syntactical examples \<close>
subsubsection \<open> Doctor Who's Tardis Attacker \<close>
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

term "(r := C)::DWTA_state phrel"

term "(r := C) ; (if\<^sub>p (1/2) then (a := S) else (a := F))"

definition dwta where
"dwta = 
  (if\<^sub>p (3/5) 
    then ((r := C) ; (if\<^sub>p ( 1/2) then (a := S) else (a := F))) 
    else ((r := D) ; (if\<^sub>p (3/10) then (a := S) else (a := F)))
  )
"

term "C"
term "(r\<^sup>> = C)\<^sub>e"
term "\<lbrakk>(r\<^sup>> = C)\<^sub>e\<rbrakk>\<^sub>\<I>"
term "\<lbrakk> r\<^sup>> = C \<and> a\<^sup>> = S \<rbrakk>\<^sub>\<I>\<^sub>e"
term "(r := C)::DWTA_state phrel"

lemma passign_simp: "((r := C)::(DWTA_state, DWTA_state) prel) = prel_of_set (\<lbrakk> r\<^sup>> = C \<and> a\<^sup>> = a\<^sup>< \<rbrakk>\<^sub>\<I>\<^sub>e)"
  apply (simp add: prob_rel_defs expr_defs)
  apply (subst prel_of_set_inject)
  apply (simp add: is_prob_def)+
  by (rel_auto)

lemma dwta_scomp_simp: 
  "(((r := C)::(DWTA_state, DWTA_state) prel); (a := S)) = prel_of_set (\<lbrakk> r\<^sup>> = C \<and> a\<^sup>> = S \<rbrakk>\<^sub>\<I>\<^sub>e)"
  apply (simp add: prob_rel_defs expr_defs)
  apply (subst prel_of_set_inject)
  defer
  apply (simp add: is_prob_def)
  apply (subst prel_of_set_inverse)
  apply (simp add: is_prob_def)
  apply (subst prel_of_set_inverse)
  apply (simp add: is_prob_def)
  apply (rel_auto)
  apply (rule infsumI)
  apply (simp add: has_sum_def)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
  apply (rule_tac x = "{\<lparr>r\<^sub>v = C, a\<^sub>v = a\<^sub>v\<rparr>}" in exI)
  apply (auto)
  apply (simp add: sum.remove)
  apply (subgoal_tac "(\<Sum>v\<^sub>0::DWTA_state\<in>Y - {\<lparr>r\<^sub>v = C, a\<^sub>v = a\<^sub>v\<rparr>}.
  (if \<lparr>r\<^sub>v = C, a\<^sub>v = a\<^sub>v\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) * 
    (if v\<^sub>0\<lparr>a\<^sub>v := S\<rparr> = \<lparr>r\<^sub>v = C, a\<^sub>v = S\<rparr> then 1::\<real> else (0::\<real>))) = 0")
  apply simp
  apply (subst sum_nonneg_eq_0_iff)
  apply simp+
  apply (rule infsum_0)
  apply auto[1]
  apply (rule infsum_0)
  apply auto[1]
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: infsum_nonneg is_prob_def prel_of_set_inverse)
  apply (subst prel_of_set_inverse)
  apply (simp add: is_prob_def)
  apply (subst prel_of_set_inverse)
  apply (simp add: is_prob_def)
  apply (rel_auto)
  apply (subst infsumI[where x="if r\<^sub>v'=C \<and> a\<^sub>v'=S then 1 else 0"])
  apply (simp add: has_sum_def, auto)
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
  apply (rule_tac x = "{\<lparr>r\<^sub>v = C, a\<^sub>v = a\<rparr>}" in exI)
  apply (auto)
  apply (simp add: sum.remove)
  apply (subgoal_tac "(\<Sum>v\<^sub>0::DWTA_state\<in>Y - {\<lparr>r\<^sub>v = C, a\<^sub>v = a\<rparr>}.
    (if \<lparr>r\<^sub>v = C, a\<^sub>v = a\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) * 
    (if v\<^sub>0\<lparr>a\<^sub>v := S\<rparr> = \<lparr>r\<^sub>v = C, a\<^sub>v = S\<rparr> then 1::\<real> else (0::\<real>))) = 0")
  apply simp
  apply (subst sum_nonneg_eq_0_iff)
  apply simp+
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
  apply (rule_tac x = "{\<lparr>r\<^sub>v = C, a\<^sub>v = a\<rparr>}" in exI, auto)
  apply (subgoal_tac "(\<Sum>v\<^sub>0::DWTA_state\<in>Y.
           (if \<lparr>r\<^sub>v = C, a\<^sub>v = a\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) * 
  (if v\<^sub>0\<lparr>a\<^sub>v := S\<rparr> = \<lparr>r\<^sub>v = r\<^sub>v', a\<^sub>v = a\<^sub>v'\<rparr> then 1::\<real> else (0::\<real>))) = 0")
  apply simp
  apply (subst sum_nonneg_eq_0_iff)
  apply simp+
  apply (subst topological_tendstoI)
  apply (auto)
  apply (simp add: eventually_finite_subsets_at_top)
  apply (rule_tac x = "{\<lparr>r\<^sub>v = C, a\<^sub>v = a\<rparr>}" in exI, auto)
  apply (subgoal_tac "(\<Sum>v\<^sub>0::DWTA_state\<in>Y.
           (if \<lparr>r\<^sub>v = C, a\<^sub>v = a\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) * 
  (if v\<^sub>0\<lparr>a\<^sub>v := S\<rparr> = \<lparr>r\<^sub>v = r\<^sub>v', a\<^sub>v = a\<^sub>v'\<rparr> then 1::\<real> else (0::\<real>))) = 0")
  apply simp
  apply (subst sum_nonneg_eq_0_iff)
  by simp+

subsubsection \<open> x \<close>
alphabet state =
  x :: int

thm "utp_prob_rel_prog.state.cases"

term "(if\<^sub>p ( 1/2) then (x := 1) else (x := 2))"
term "(x := x + 1)"
term "x := (x + 1)"
(* Next is syntactically correct if the priority of :=\<^sub>p is larger than + (65) *)
term "(x := x + 1)"
term "(x := (x + 1))"
term "((if\<^sub>p ( 1/2) then ((x := 1)::(state, state) prel) else (x := 2)) ; (x := (x + 1)))"
term "v\<^sub>0 \<lparr>x\<^sub>v := x\<^sub>v v\<^sub>0 + (1::\<int>)\<rparr>"
term "\<lparr>x\<^sub>v = 0\<rparr>"

lemma "\<exists>x\<^sub>v'. v\<^sub>0\<lparr>x\<^sub>v := x\<^sub>v v\<^sub>0 + (1::\<int>)\<rparr> = \<lparr>x\<^sub>v = x\<^sub>v'\<rparr>"
  by (meson utp_prob_rel_prog.state.cases)

term "suminf"
term "sum"

lemma "((if\<^sub>p ( 1/2) then ((x := 1)::(state, state) prel) else (x := 2)) ; (x := (x + 1)))
  = (if\<^sub>p ( 1/2) then (x := 2) else (x := 3))"
  apply (simp add: prob_rel_defs)
  apply (expr_auto)
  apply (subst prel_of_set_inverse)
  apply (subst prel_of_set_inverse, auto, simp add: dist_defs)
   apply (subst prel_of_set_inverse, auto, simp add: dist_defs)
   apply (simp add: dist_defs)
  apply (subst prel_of_set_inverse, auto, simp add: dist_defs)
  apply (subst prel_of_set_inverse, auto, simp add: dist_defs)
  apply (subst prel_of_set_inverse, auto, simp add: dist_defs)
  apply (subst prel_of_set_inverse, auto, simp add: dist_defs)
  apply (subst prel_of_set_inverse, auto, simp add: dist_defs)
  apply (subst prel_of_set_inject)
  apply (simp add: dist_defs expr_defs)
  apply (auto)
     apply (simp add: infsum_nonneg)
    apply (rel_auto)
proof -
  fix x\<^sub>v'::"int"
  let ?x11 = "\<lambda>v\<^sub>0. (if \<lparr>x\<^sub>v = 1::\<int>\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) / (2::\<real>)"
  let ?x12 = "\<lambda>v\<^sub>0. (if \<lparr>x\<^sub>v = 2::\<int>\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) / (2::\<real>)"
  let ?x1 = "\<lambda>v\<^sub>0. ((if \<lparr>x\<^sub>v = 1::\<int>\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) / (2::\<real>) +
           (if \<lparr>x\<^sub>v = 2::\<int>\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) / (2::\<real>))" 
  let ?x2 = "\<lambda>v\<^sub>0. (if v\<^sub>0\<lparr>x\<^sub>v := x\<^sub>v v\<^sub>0 + (1::\<int>)\<rparr> = \<lparr>x\<^sub>v = x\<^sub>v'\<rparr> then 1::\<real> else (0::\<real>))"
  let ?f = "\<lambda>v\<^sub>0. ?x1 v\<^sub>0 * ?x2 v\<^sub>0"
  have "has_sum ?x11 UNIV (1/2)"
    apply (simp add: has_sum_def)
    apply (subst  topological_tendstoI)
    apply (auto)
    proof -
    fix S::"\<bbbP> \<real>"
    assume a1: "open S"
    assume a2: "(1::\<real>) / (2::\<real>) \<in> S"
    show " \<forall>\<^sub>F x::\<bbbP> utp_prob_rel_prog.state in finite_subsets_at_top UNIV.
          (\<Sum>v\<^sub>0::utp_prob_rel_prog.state\<in>x. (if \<lparr>x\<^sub>v = 1::\<int>\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) / (2::\<real>)) \<in> S"
      apply (simp add: eventually_finite_subsets_at_top)
      apply (rule_tac x = "{\<lparr>x\<^sub>v = 1::\<int>\<rparr>}" in exI)
      apply (auto)
      proof -
        fix Y::"\<bbbP> utp_prob_rel_prog.state"
        assume a11: "finite Y"
        assume a12: "\<lparr>x\<^sub>v = 1::\<int>\<rparr> \<in> Y"
        have f1: "(\<Sum>v\<^sub>0::utp_prob_rel_prog.state\<in>{\<lparr>x\<^sub>v = 1::\<int>\<rparr>}. (if \<lparr>x\<^sub>v = 1::\<int>\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) / (2::\<real>)) = 1/2"
          by (simp add: sum.remove)
        have f2: "(\<Sum>v\<^sub>0::utp_prob_rel_prog.state\<in>Y-{\<lparr>x\<^sub>v = 1::\<int>\<rparr>}. (if \<lparr>x\<^sub>v = 1::\<int>\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) / (2::\<real>)) = 0"
          apply (subst sum_nonneg_eq_0_iff)
          by (auto simp add: a11)
        have f3: "(\<Sum>v\<^sub>0::utp_prob_rel_prog.state\<in>Y. (if \<lparr>x\<^sub>v = 1::\<int>\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) / (2::\<real>)) = 1/2"
          apply (insert sum_Un[where A="Y-{\<lparr>x\<^sub>v = 1::\<int>\<rparr>}" and B="{\<lparr>x\<^sub>v = 1::\<int>\<rparr>}" and 
                f="\<lambda>v\<^sub>0. (if \<lparr>x\<^sub>v = 1::\<int>\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) / (2::\<real>)"])
          apply auto
          by (simp add: a11 a12 f2 sum.insert_if)
        show "(\<Sum>v\<^sub>0::utp_prob_rel_prog.state\<in>Y. (if \<lparr>x\<^sub>v = 1::\<int>\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) / (2::\<real>)) \<in> S"
          using a2 f3 by presburger
      qed
    qed
          

  have "?x11 abs_summable_on UNIV"                                                                                    
    apply (simp, simp add: summable_on_def has_sum_def)
    apply (subst  topological_tendstoI)
    apply (auto)
  proof -
    fix x::"\<real>" and S::"\<bbbP> \<real>"
    assume "open S"
    assume "x \<in> S"

    show "\<forall>\<^sub>F xx::\<bbbP> utp_prob_rel_prog.state in finite_subsets_at_top UNIV.
          (\<Sum>x::utp_prob_rel_prog.state\<in>xx. (if \<lparr>x\<^sub>v = 1::\<int>\<rparr> = x then 1::\<real> else (0::\<real>)) / (2::\<real>)) \<in> S"
      apply (simp add: eventually_finite_subsets_at_top)
      apply (rule_tac x = "{\<lparr>x\<^sub>v = 1::\<int>\<rparr>}" in exI)
      apply (auto)
      proof -
        
      
    apply (subst abs_summable_iff_bdd_above)
  have "?f abs_summable_on UNIV"
    apply (subst abs_summable_iff_bdd_above)
    sledgehammer
  show " (\<Sum>\<^sub>\<infinity> v\<^sub>0::utp_prob_rel_prog.state. ?f v\<^sub>0) \<le> (1::\<real>)"
    apply (subst infsum_nonneg_is_SUPREMUM_real)
    apply (simp add: summable_on_def)
    unfolding has_sum_def
    apply (simp add: tendsto_def)
    apply (subst tendsto_cong[where g=\<open>\<lambda>_. 0\<close>])
   apply (rule eventually_finite_subsets_at_top_weakI)
next




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
