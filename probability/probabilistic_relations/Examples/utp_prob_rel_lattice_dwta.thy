section \<open> Doctor Who's Tardis Attacker  \<close>

theory utp_prob_rel_lattice_dwta
  imports 
    "UTP_prob_relations.utp_prob_rel"
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
term "(r := C)::DWTA_state prhfun"

term "(r := C) ; (if\<^sub>p (1/2) then (a := S) else (a := F))"

definition dwta :: "(DWTA_state, DWTA_state) prfun" where
"dwta = 
  (if\<^sub>p (3/5) 
    then ((r := C) ; (if\<^sub>p ( 1/2) then (a := S) else (a := F))) 
    else ((r := D) ; (if\<^sub>p (3/10) then (a := S) else (a := F)))
  )
"

thm "dwta_def"

term "C"
term "(r\<^sup>> = C)\<^sub>e"
term "($r\<^sup>> = C)\<^sub>e"
term "\<lbrakk>(r\<^sup>> = C)\<^sub>e\<rbrakk>\<^sub>\<I>"
term "\<lbrakk> r\<^sup>> = C \<and> a\<^sup>> = S \<rbrakk>\<^sub>\<I>\<^sub>e"
term "(r := C)::DWTA_state prhfun"

lemma dwta_scomp_simp: 
  "(((r := C)::DWTA_state prhfun); (a := S)) = prfun_of_rvfun (\<lbrakk> $r\<^sup>> = C \<and> $a\<^sup>> = S \<rbrakk>\<^sub>\<I>\<^sub>e)"
  apply (simp add: prfun_passign_comp)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  by (pred_auto)

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
  shows "((r := \<guillemotleft>attacker\<guillemotright>)::(DWTA_state, DWTA_state) prfun) ; (if\<^sub>p (\<guillemotleft>p\<guillemotright>) then (a := S) else (a := F))
    = prfun_of_rvfun (    ureal2real \<guillemotleft>p\<guillemotright> * \<lbrakk> $r\<^sup>> = \<guillemotleft>attacker\<guillemotright> \<and> $a\<^sup>> = S \<rbrakk>\<^sub>\<I>\<^sub>e + 
                     (1 - ureal2real \<guillemotleft>p\<guillemotright>)* \<lbrakk> $r\<^sup>> = \<guillemotleft>attacker\<guillemotright> \<and> $a\<^sup>> = F \<rbrakk>\<^sub>\<I>\<^sub>e
                  )\<^sub>e"
proof -
  have f1: "rvfun_of_prfun [\<lambda>\<s>::DWTA_state \<times> DWTA_state. p]\<^sub>e = (\<lambda>s. ureal2real p)"
    by (simp add: SEXP_def rvfun_of_prfun_def)

  show ?thesis
  apply (simp add: prfun_seqcomp_left_one_point)
  apply (simp add: pchoice_def)
  apply (simp add: passigns_def pchoice_def)
  apply (simp add: rvfun_assignment_inverse)
  apply (simp only: f1)
  apply (subst rvfun_pchoice_inverse_c)
  using rvfun_assignment_is_prob apply blast+
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  by (pred_auto)
qed

lemma dwta_simp: "dwta = prfun_of_rvfun (
     3/10 * \<lbrakk> $r\<^sup>> = C \<and> $a\<^sup>> = S \<rbrakk>\<^sub>\<I>\<^sub>e + 
     3/10 * \<lbrakk> $r\<^sup>> = C \<and> $a\<^sup>> = F \<rbrakk>\<^sub>\<I>\<^sub>e + 
     6/50 * \<lbrakk> $r\<^sup>> = D \<and> $a\<^sup>> = S \<rbrakk>\<^sub>\<I>\<^sub>e + 
    14/50 * \<lbrakk> $r\<^sup>> = D \<and> $a\<^sup>> = F \<rbrakk>\<^sub>\<I>\<^sub>e
  )\<^sub>e"
  apply (simp add: dwta_def)
  apply (subst dwta_attack_status[where p = "ereal2ureal ((1::ereal) / ereal (2::\<real>))" and attacker = C])
  apply (subst dwta_attack_status[where p = "ereal2ureal (ereal ((3::\<real>) / (10::\<real>)))" and attacker = D])
  apply (simp add: pfun_defs)
  apply (subst rvfun_inverse)
  apply (simp add: is_prob_def iverson_bracket_def ureal_lower_bound ureal_upper_bound)
  apply (subst rvfun_inverse)
  apply (simp add: is_prob_def iverson_bracket_def ureal_lower_bound ureal_upper_bound)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (simp add: dist_defs expr_defs lens_defs ureal_defs)
  apply (subst fun_eq_iff)
  apply (auto)
  apply (simp add: real2uereal_inverse)
  apply (simp add: ereal_1_div)
  apply (simp add: real2uereal_inverse')
  apply (simp add: real2uereal_inverse')+
  by (simp add: ereal_1_div real2uereal_inverse')+

lemma dwta_attack_by_C: "rvfun_of_prfun dwta ;\<^sub>f (\<lbrakk>r\<^sup>< = C\<rbrakk>\<^sub>\<I>\<^sub>e) = (6/10)\<^sub>e"
  apply (simp add: dwta_simp)
  apply (subst rvfun_inverse)
  apply (simp add: dist_defs expr_defs)
  apply (simp add: dwta_infsum_sum)
  apply (subst sum.subset_diff[where A="UNIV" and B="{\<lparr>r\<^sub>v = C, a\<^sub>v = S\<rparr>, \<lparr>r\<^sub>v = C, a\<^sub>v = F\<rparr>, 
      \<lparr>r\<^sub>v = D, a\<^sub>v = S\<rparr>, \<lparr>r\<^sub>v = D, a\<^sub>v = F\<rparr>}"])
  apply (simp add: dwta_state_finite)+
  apply (expr_auto)
  apply (subst sum_nonneg_eq_0_iff)
  using dwta_state_finite apply blast
  apply auto[1]
  by (smt (z3) Attacker.exhaust DWTA_state.surjective DiffD2 Status.exhaust insertCI old.unit.exhaust)

lemma dwta_successful_attack: "rvfun_of_prfun dwta ;\<^sub>f (\<lbrakk>a\<^sup>< = S\<rbrakk>\<^sub>\<I>\<^sub>e) = (21/50)\<^sub>e"
  apply (simp add: dwta_simp)
  apply (subst rvfun_inverse)
  apply (simp add: dist_defs expr_defs)
  apply (simp add: dwta_infsum_sum)
  apply (subst sum.subset_diff[where A="UNIV" and B="{\<lparr>r\<^sub>v = C, a\<^sub>v = S\<rparr>, \<lparr>r\<^sub>v = C, a\<^sub>v = F\<rparr>, 
      \<lparr>r\<^sub>v = D, a\<^sub>v = S\<rparr>, \<lparr>r\<^sub>v = D, a\<^sub>v = F\<rparr>}"])
  apply (simp add: dwta_state_finite)+
  apply (expr_auto)
  apply (subst sum_nonneg_eq_0_iff)
  using dwta_state_finite apply blast
  apply auto[1]
  by (smt (z3) Attacker.exhaust DWTA_state.surjective DiffD2 Status.exhaust insertCI old.unit.exhaust)

lemma dwta_successful_attack_by_D: "rvfun_of_prfun dwta ;\<^sub>f (\<lbrakk>r\<^sup>< = D \<and> a\<^sup>< = S\<rbrakk>\<^sub>\<I>\<^sub>e) = (3/25)\<^sub>e"
  apply (simp add: dwta_simp)
  apply (subst rvfun_inverse)
  apply (simp add: dist_defs expr_defs)
  apply (simp add: dwta_infsum_sum)
  apply (subst sum.subset_diff[where A="UNIV" and B="{\<lparr>r\<^sub>v = C, a\<^sub>v = S\<rparr>, \<lparr>r\<^sub>v = C, a\<^sub>v = F\<rparr>, 
      \<lparr>r\<^sub>v = D, a\<^sub>v = S\<rparr>, \<lparr>r\<^sub>v = D, a\<^sub>v = F\<rparr>}"])
  apply (simp add: dwta_state_finite)+
  apply (expr_auto)
  apply (subst sum_nonneg_eq_0_iff)
  using dwta_state_finite apply blast
  apply auto[1]
  by (smt (z3) Attacker.exhaust DWTA_state.surjective DiffD2 Status.exhaust insertCI old.unit.exhaust)

end
