section \<open> Probabilistic relation programming example 1 \<close>

theory utp_prob_rel_ex1
  imports 
    "../utp_prob_rel_laws" 
begin 

unbundle UTP_Syntax

declare [[show_types]]

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
term "{r, a}\<^sub>v := {C, S}"

lemma passign_simp: "((r := C)::(DWTA_state, DWTA_state) prel) = prel_of_set (\<lbrakk> $r\<^sup>> = C \<and> $a\<^sup>> = $a\<^sup>< \<rbrakk>\<^sub>\<I>\<^sub>e)"
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
term "(x := x + 1)::'s rel"
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
