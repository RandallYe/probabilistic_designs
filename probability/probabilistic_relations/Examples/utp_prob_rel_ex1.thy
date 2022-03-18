section \<open> Probabilistic relation programming example 1 \<close>

theory utp_prob_rel_ex1
  imports 
    "../utp_prob_rel_laws" 
begin 

unbundle UTP_Syntax

declare [[show_types]]

subsection \<open> Doctor Who's Tardis Attacker \<close>
text \<open> Example 13 from Jim's draft report. 
Two robots, the Cyberman C and the Dalek D, attack Doctor Who’s Tardis once a day between them. 
C has a probability 1/2 of a successful attack, 
while D has a probability 3/10 of a successful attack. 
C attacks more often than D, with a probability of 3/5 on a particular day 
(and so D attacks with a probability of 2/5 on that day). 
What is the probability that there is a successful attack today?\<close>

subsubsection \<open> State space \<close>
datatype Attacker = C | D
find_theorems name: "Attacker.induct"

datatype Status = S | F

alphabet DWTA_state = 
  r:: Attacker
  a:: Status

find_theorems name: "DWTA_state.induct"
find_theorems name: "DWTA_state.select_convs"

subsubsection \<open> Finite \<close>

lemma attacker_finite: "finite (UNIV::Attacker set)"
  by (metis Attacker.induct Collect_empty_eq Collect_mem_eq DiffD2 Diff_infinite_finite finite.emptyI 
      finite_insert insertCI)

lemma status_finite: "finite (UNIV::Status set)"
by (metis Status.induct Collect_empty_eq Collect_mem_eq DiffD2 Diff_infinite_finite finite.emptyI 
      finite_insert insertCI)

lemma dwta_state_univ_rewrite: "(UNIV::DWTA_state set) = {\<lparr>r\<^sub>v = rr, a\<^sub>v = aa\<rparr> | (rr::Attacker) (aa::Status). True }"
  by (metis (mono_tags, lifting) CollectI DWTA_state.cases UNIV_eq_I)

lemma dwta_state_subset_finite: "finite {\<lparr>r\<^sub>v = rr, a\<^sub>v = aa\<rparr> | (rr::Attacker) (aa::Status). True \<and> True }"
  apply (rule finite_image_set2[where P="\<lambda>x. True" and Q="\<lambda>x. True" and f = "\<lambda>x y. \<lparr>r\<^sub>v = x, a\<^sub>v = y\<rparr>"])
  using attacker_finite status_finite by force+

lemma dwta_state_finite: "finite (UNIV::DWTA_state set)"
  apply (simp add: dwta_state_univ_rewrite)
  using dwta_state_subset_finite by presburger

lemma dwta_infsum_sum: "(\<Sum>\<^sub>\<infinity>s::DWTA_state. f s) = sum f (UNIV::DWTA_state set)"
  using dwta_state_finite by (simp)

subsubsection \<open> Laws \<close>
term "(r := C)::DWTA_state phrel"

term "(r := C) ; (if\<^sub>p (1/2) then (a := S) else (a := F))"

definition dwta :: "(DWTA_state, DWTA_state) prel" where
"dwta = 
  (if\<^sub>p (3/5) 
    then ((r := C) ; (if\<^sub>p ( 1/2) then (a := S) else (a := F))) 
    else ((r := D) ; (if\<^sub>p (3/10) then (a := S) else (a := F)))
  )
"

term "C"
term "(r\<^sup>> = C)\<^sub>e"
term "($r\<^sup>> = C)\<^sub>e"
term "\<lbrakk>(r\<^sup>> = C)\<^sub>e\<rbrakk>\<^sub>\<I>"
term "\<lbrakk> r\<^sup>> = C \<and> a\<^sup>> = S \<rbrakk>\<^sub>\<I>\<^sub>e"
term "(r := C)::DWTA_state phrel"

(*
lemma passign_simp: "((r := C)::(DWTA_state, DWTA_state) prel) = prel_of_rfrel (\<lbrakk> $r\<^sup>> = C \<and> $a\<^sup>> = $a\<^sup>< \<rbrakk>\<^sub>\<I>\<^sub>e)"
  apply (simp add: prel_defs expr_defs)
  apply (rel_auto)
  apply (subst prel_of_rfrel_inject)
    apply (simp add: dist_defs expr_defs)
    apply (simp add: infsum_singleton)
   apply (simp add: dist_defs expr_defs)
   apply (auto)
*)

lemma dwta_scomp_simp: 
  "(((r := C)::(DWTA_state, DWTA_state) prel); (a := S)) = prel_of_rfrel (\<lbrakk> $r\<^sup>> = C \<and> $a\<^sup>> = S \<rbrakk>\<^sub>\<I>\<^sub>e)"
  apply (simp add: passign_comp)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  by (rel_auto)

lemma dwta_infsum_two_instances: "(\<Sum>\<^sub>\<infinity>s::DWTA_state.
          p * (if \<lparr>r\<^sub>v = rr, a\<^sub>v = S\<rparr> = s then 1::\<real> else (0::\<real>)) +
          q * (if \<lparr>r\<^sub>v = rr, a\<^sub>v = F\<rparr> = s then 1::\<real> else (0::\<real>))) = (p + q)"
  apply (simp add: dwta_infsum_sum)
  apply (subst sum.subset_diff[where A="UNIV" and B="{\<lparr>r\<^sub>v = rr, a\<^sub>v = S\<rparr>, \<lparr>r\<^sub>v = rr, a\<^sub>v = F\<rparr>}"])
  apply (simp add: dwta_state_finite)+
  apply (subst sum_nonneg_eq_0_iff)
  using dwta_state_finite apply blast
  apply auto[1]
  by auto

lemma dwta_infsum_two_instances': "(\<Sum>\<^sub>\<infinity>s::DWTA_state.
          p* (if r\<^sub>v s = rr \<and> a\<^sub>v s = S then 1::\<real> else (0::\<real>)) +
          q* (if r\<^sub>v s = rr \<and> a\<^sub>v s = F then 1::\<real> else (0::\<real>))) = (p + q)"
  apply (simp add: dwta_infsum_sum)
  apply (subst sum.subset_diff[where A="UNIV" and B="{\<lparr>r\<^sub>v = rr, a\<^sub>v = S\<rparr>, \<lparr>r\<^sub>v = rr, a\<^sub>v = F\<rparr>}"])
  apply (simp add: dwta_state_finite)+
  apply (subst sum_nonneg_eq_0_iff)
  using dwta_state_finite apply blast
  apply auto[1]
  by auto

lemma dwta_attack_status:
  assumes "0 \<le> p \<and> p \<le> (1::\<real>)"
  shows "((r := \<guillemotleft>attacker\<guillemotright>)::(DWTA_state, DWTA_state) prel) ; (if\<^sub>p ( \<guillemotleft>p\<guillemotright>) then (a := S) else (a := F))
    = prel_of_rfrel (       \<guillemotleft>p\<guillemotright> * \<lbrakk> $r\<^sup>> = \<guillemotleft>attacker\<guillemotright> \<and> $a\<^sup>> = S \<rbrakk>\<^sub>\<I>\<^sub>e + 
                     (1 - \<guillemotleft>p\<guillemotright>)* \<lbrakk> $r\<^sup>> = \<guillemotleft>attacker\<guillemotright> \<and> $a\<^sup>> = F \<rbrakk>\<^sub>\<I>\<^sub>e
                  )\<^sub>e"
  apply (simp add: prel_seqcomp_left_one_point)
  apply (simp add: pchoice_def)
  apply (simp add: passigns_def pchoice_def)
  apply (simp add: prel_set_conv_assign)
  apply (subst prel_set_conv_pchoice_c)
  apply (simp add: assms)
  apply (metis prel_is_dist prel_set_conv_assign)
  apply (metis prel_is_dist prel_set_conv_assign)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  by (rel_auto)

lemma dwta_simp: "dwta = prel_of_rfrel (
     3/10 * \<lbrakk> $r\<^sup>> = C \<and> $a\<^sup>> = S \<rbrakk>\<^sub>\<I>\<^sub>e + 
     3/10 * \<lbrakk> $r\<^sup>> = C \<and> $a\<^sup>> = F \<rbrakk>\<^sub>\<I>\<^sub>e + 
     6/50 * \<lbrakk> $r\<^sup>> = D \<and> $a\<^sup>> = S \<rbrakk>\<^sub>\<I>\<^sub>e + 
    14/50 * \<lbrakk> $r\<^sup>> = D \<and> $a\<^sup>> = F \<rbrakk>\<^sub>\<I>\<^sub>e
  )\<^sub>e"
  apply (simp add: dwta_def)
  apply (subst dwta_attack_status[where p = "((1/2)::\<real>)" and attacker = C])
  apply (simp)
  apply (subst dwta_attack_status[where p = "((3/10)::\<real>)" and attacker = D])
  apply (simp)
  apply (simp add: prel_defs)
  apply (subst prel_of_rfrel_inverse)
  apply (simp add: dist_defs expr_defs lens_defs)
  apply (subgoal_tac "(\<Sum>\<^sub>\<infinity>s::DWTA_state.
   (1/2) * (if r\<^sub>v s = C \<and> a\<^sub>v s = S then 1::\<real> else (0::\<real>)) +
   (1/2) * (if r\<^sub>v s = C \<and> a\<^sub>v s = F then 1::\<real> else (0::\<real>))) = (1::\<real>)")
  apply (simp)
  apply (subst dwta_infsum_two_instances'[where rr=C and p="1/2" and q="1/2"])
  apply (simp)
  apply (subst prel_of_rfrel_inverse)
  apply (simp add: dist_defs expr_defs lens_defs)
  apply (subgoal_tac "(\<Sum>\<^sub>\<infinity>s::DWTA_state.
   (3/10) * (if r\<^sub>v s = D \<and> a\<^sub>v s = S then 1::\<real> else (0::\<real>)) +
   (7/10) * (if r\<^sub>v s = D \<and> a\<^sub>v s = F then 1::\<real> else (0::\<real>))) = (1::\<real>)")
  apply (simp)
  apply (subst dwta_infsum_two_instances'[where rr=D and p="3/10" and q="7/10"])
  apply (simp)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  by (rel_auto)

lemma "rfrel_of_prel dwta ;\<^sub>f (\<lbrakk>r\<^sup>< = C\<rbrakk>\<^sub>\<I>\<^sub>e) = (6/10)\<^sub>e"
  apply (simp add: dwta_simp)
  apply (subst prel_of_rfrel_inverse)
  apply (simp add: dist_defs expr_defs lens_defs)
   apply (simp add: dwta_infsum_sum)
   apply (subst sum.subset_diff[where A="UNIV" and B="{\<lparr>r\<^sub>v = C, a\<^sub>v = S\<rparr>, \<lparr>r\<^sub>v = C, a\<^sub>v = F\<rparr>, 
      \<lparr>r\<^sub>v = D, a\<^sub>v = S\<rparr>, \<lparr>r\<^sub>v = D, a\<^sub>v = F\<rparr>}"])
  apply (simp add: dwta_state_finite)+
  apply (subst sum_nonneg_eq_0_iff)
  using dwta_state_finite apply blast
  apply auto[1]
   apply (smt (z3) Attacker.exhaust DWTA_state.surjective DiffD2 Status.exhaust insertCI old.unit.exhaust)
  apply (rel_auto)
  apply (simp add: dwta_infsum_sum)
  apply (subst sum.subset_diff[where A="UNIV" and B="{\<lparr>r\<^sub>v = C, a\<^sub>v = S\<rparr>, \<lparr>r\<^sub>v = C, a\<^sub>v = F\<rparr>}"])
  apply (simp add: dwta_state_finite)+
  apply (subst sum_nonneg_eq_0_iff)
  using dwta_state_finite apply blast
   apply auto[1]
  by auto

subsubsection \<open> x \<close>
alphabet state =
  x :: int

term "x"
term "x\<^sup><"
term "x\<^sup>>"
term "$x"
term "$x\<^sup><"
find_theorems name: "state."

end
