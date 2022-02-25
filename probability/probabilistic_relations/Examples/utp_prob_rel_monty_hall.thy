section \<open> Probabilistic relation programming example 1 \<close>

theory utp_prob_rel_monty_hall
  imports 
    "../utp_prob_rel_laws" 
begin 

unbundle UTP_Syntax

declare [[show_types]]

named_theorems dwta_defs

alphabet DWTA_state = 
  p :: nat
  c :: nat
  m :: nat

term "p"
term "p\<^sup>>"
term "p\<^sup><"
term "$p\<^sup>>"
term "$p"

term "\<^bold>N \<lbrakk>p\<^sup>> \<in> {0..2} \<and> c\<^sup>> = c\<^sup>< \<and> m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e"
term "\<^bold>N\<^sub>\<alpha> x (\<lbrakk>p\<^sup>> \<in> {0..2} \<and> c\<^sup>> = c\<^sup>< \<and> m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e)"
term "((\<^bold>N\<^sub>\<alpha> p (\<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e)) * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"

term "(prel_of_rfrel (p \<^bold>\<U> {0..2}))"

subsection \<open> Definitions \<close>
definition INIT_p :: "DWTA_state phrel" where 
[dwta_defs]: "INIT_p = prel_of_rfrel (p \<^bold>\<U> {0..2})"

definition INIT_c :: "DWTA_state phrel" where 
[dwta_defs]: "INIT_c = prel_of_rfrel (c \<^bold>\<U> {0..2})"

definition INIT:: "DWTA_state phrel" where 
[dwta_defs]: "INIT = INIT_p ; INIT_c"

term "(x)\<lparr>c\<^sub>v := Suc (0::\<nat>)\<rparr>"
find_theorems name:"DWTA_state"
record x = i :: nat

thm "DWTA_state.select_convs"
thm "DWTA_state.surjective"
thm "DWTA_state.update_convs"

term "($c\<^sup>< = $p\<^sup><)\<^sub>e"
term " (if c\<^sup>< = p\<^sup>< then II\<^sub>p else II)"
term "m := ((c + 1) mod 3) :: DWTA_state phrel"
term "(if\<^sub>p 1/2 then m := (($c + 1) mod 3) else m := (($c + 2) mod 3))"
term "(m := ($c + 1) mod 3) :: DWTA_state phrel "

(*
definition MHA:: "DWTA_state phrel" where
"MHA = pcond (c\<^sup>< = p\<^sup><)\<^sub>e (if\<^sub>p 1/2 then (m := ($c + 1) mod 3) else (m := ($c + 2) mod 3)) (m := 3 - $c - $p)"
*)

definition MHA:: "DWTA_state phrel" where
[dwta_defs]: "MHA = (if\<^sub>c c\<^sup>< = p\<^sup>< then 
          (if\<^sub>p 1/2 then (m := ($c + 1) mod 3) else (m := ($c + 2) mod 3)) 
        else 
          (m := 3 - $c - $p)
      )"

definition MHA_NC:: "DWTA_state phrel" where
[dwta_defs]: "MHA_NC = (if\<^sub>c c\<^sup>< = p\<^sup>< then 
          (if\<^sub>p 1/2 then (m := ($c + 1) mod 3) else (m := ($c + 2) mod 3)) 
        else 
          (m := 3 - $c - $p)
      ) ; II" (* No Change Strategy *)

definition MHA_C:: "DWTA_state phrel" where
[dwta_defs]: "MHA_C = (if\<^sub>c c\<^sup>< = p\<^sup>< then 
          (if\<^sub>p 1/2 then (m := ($c + 1) mod 3) else (m := ($c + 2) mod 3)) 
        else 
          (m := 3 - $c - $p)
      ) ; c := 3 - c - m" (* Change Strategy *)

thm "MHA_def"

definition IMHA_NC where 
[dwta_defs]: "IMHA_NC = INIT ; MHA_NC"

definition IMHA_C where 
[dwta_defs]: "IMHA_C = INIT ; MHA_C"

subsection \<open> @{text "INIT"} \<close>

lemma zero_to_two: "{0..2::\<nat>} = {0, 1, 2}"
  by force

lemma infsum_alt_3: 
  "(\<Sum>\<^sub>\<infinity>v::\<nat>. if v = (0::\<nat>) \<or> Suc (0::\<nat>) = v \<or> v = (2::\<nat>) then 1::\<real> else (0::\<real>)) = (3::\<real>)"
  apply (simp add: infsum_constant_finite_states)
  apply (subgoal_tac "{s::\<nat>. s = (0::\<nat>) \<or> Suc (0::\<nat>) = s \<or> s = (2::\<nat>)} = {0, Suc 0, 2}")
  apply simp
  apply (simp add: set_eq_iff)
  by meson

lemma INIT_p_altdef: 
  "INIT_p = prel_of_rfrel ((\<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e) / 3)\<^sub>e"
  apply (simp add: zero_to_two INIT_p_def)
  apply (simp add: dist_defs)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (rel_auto)
  by (simp_all add: infsum_alt_3)

lemma INIT_c_altdef: 
  "INIT_c = prel_of_rfrel ((\<lbrakk>p\<^sup>> = p\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e) / 3)\<^sub>e"
  apply (simp add: zero_to_two INIT_c_def)
  apply (simp add: dist_defs)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (rel_auto)
  by (simp_all add: infsum_alt_3)


(*
lemma "\<lbrakk>r1\<lparr>c\<^sub>v := a\<rparr> = r2\<lparr>c\<^sub>v := b\<rparr>\<rbrakk> \<Longrightarrow> (a = b)"
  by (metis DWTA_state.select_convs(2) DWTA_state.surjective DWTA_state.update_convs(2))

lemma "\<lbrakk>(a \<noteq> b)\<rbrakk> \<Longrightarrow> r1\<lparr>c\<^sub>v := a\<rparr> \<noteq> r2\<lparr>c\<^sub>v := b\<rparr>"
  by (metis DWTA_state.ext_inject DWTA_state.surjective DWTA_state.update_convs(2))
*)

lemma record_update_simp:
  assumes "m\<^sub>v (r\<^sub>1::DWTA_state) = m\<^sub>v r\<^sub>2"
  shows "(r\<^sub>1\<lparr>p\<^sub>v := p\<^sub>v (r\<^sub>2), c\<^sub>v := x\<rparr> = r\<^sub>2) \<longleftrightarrow> c\<^sub>v r\<^sub>2 = x"
  apply (auto)
  apply (metis DWTA_state.select_convs(2) DWTA_state.surjective DWTA_state.update_convs(2))
  by (simp add: assms)

lemma record_neq_p_c:
  assumes "a\<^sub>1 \<noteq> a\<^sub>2 \<or> b\<^sub>1 \<noteq> b\<^sub>2"
  assumes "r\<^sub>1\<lparr>p\<^sub>v := a\<^sub>1, c\<^sub>v := b\<^sub>1\<rparr> = r\<^sub>1\<lparr>p\<^sub>v := a\<^sub>2, c\<^sub>v := b\<^sub>2\<rparr>"
  shows "False"
  by (metis DWTA_state.ext_inject DWTA_state.surjective DWTA_state.update_convs(1) DWTA_state.update_convs(2) assms(1) assms(2))

text \<open> Below we illustrate the simplification of INIT using two ways: 
\begin{itemize}
  \item @{text "INIT_altdef"}: without @{thm "prel_uniform_dist_left"}. 
        We need to deal with infinite summation and cardinality.
  \item @{text "INIT_altdef'"}: with @{thm "prel_uniform_dist_left"}.
        We mainly deal with conditional and propositional logic.
\end{itemize}
1) 
\<close>
lemma INIT_altdef: "INIT = prel_of_rfrel ((\<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e) / 9)\<^sub>e"
  apply (simp add: INIT_def INIT_p_def INIT_c_def zero_to_two)
  apply (simp add: prel_defs)
  apply (simp add: uniform_dist_altdef')
  apply (expr_auto add: rel)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (simp only: fun_eq_iff)
  apply (rule allI)
proof -
  fix x :: "DWTA_state \<times> DWTA_state"
  let ?rhs = "(if p\<^sub>v (snd x) = (0::\<nat>) \<or> p\<^sub>v (snd x) = Suc (0::\<nat>) \<or> p\<^sub>v (snd x) = (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if c\<^sub>v (snd x) = (0::\<nat>) \<or> c\<^sub>v (snd x) = Suc (0::\<nat>) \<or> c\<^sub>v (snd x) = (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v (snd x) = m\<^sub>v (fst x) then 1::\<real> else (0::\<real>))"
  let ?rhs_1 = "(if (p\<^sub>v (snd x) = (0::\<nat>) \<or> p\<^sub>v (snd x) = Suc (0::\<nat>) \<or> p\<^sub>v (snd x) = (2::\<nat>)) \<and>
       (c\<^sub>v (snd x) = (0::\<nat>) \<or> c\<^sub>v (snd x) = Suc (0::\<nat>) \<or> c\<^sub>v (snd x) = (2::\<nat>)) \<and>
       (m\<^sub>v (snd x) = m\<^sub>v (fst x)) then 1::\<real> else (0::\<real>))"

  let ?lhs_1 = "\<lambda>v\<^sub>0. (if fst x\<lparr>p\<^sub>v := 0::\<nat>\<rparr> = v\<^sub>0 \<or> fst x\<lparr>p\<^sub>v := Suc (0::\<nat>)\<rparr> = v\<^sub>0 \<or> fst x\<lparr>p\<^sub>v := 2::\<nat>\<rparr> = v\<^sub>0 then 1::\<real>
           else (0::\<real>)) *
     (if v\<^sub>0\<lparr>c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> v\<^sub>0\<lparr>c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> v\<^sub>0\<lparr>c\<^sub>v := 2::\<nat>\<rparr> = snd x then 1::\<real> else (0::\<real>))"
  let ?lhs_2 = "\<lambda>v\<^sub>0. (if (fst x\<lparr>p\<^sub>v := 0::\<nat>\<rparr> = v\<^sub>0 \<or> fst x\<lparr>p\<^sub>v := Suc (0::\<nat>)\<rparr> = v\<^sub>0 \<or> fst x\<lparr>p\<^sub>v := 2::\<nat>\<rparr> = v\<^sub>0) \<and>
          (v\<^sub>0\<lparr>c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> v\<^sub>0\<lparr>c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> v\<^sub>0\<lparr>c\<^sub>v := 2::\<nat>\<rparr> = snd x) then 1::\<real>
           else (0::\<real>))"

  have fr: "?rhs / (9::\<real>) = ?rhs_1 / (9::\<real>)"
    by simp

  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state. ?lhs_1 v\<^sub>0 / (9::\<real>)) = (\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state. ?lhs_2 v\<^sub>0 / (9::\<real>))"
    by (simp add: infsum_cong)
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state. ?lhs_2 v\<^sub>0 * ( 1 / (9::\<real>)))"
    by auto
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state. ?lhs_2 v\<^sub>0) * ( 1 / (9::\<real>))"
    apply (subst infsum_cmult_left[where c = "1 / (9::real)"])
    apply (simp add: infsum_constant_finite_states_summable)
    by simp

  also have fl: "... = 
    (1 * card {v\<^sub>0. (fst x\<lparr>p\<^sub>v := 0::\<nat>\<rparr> = v\<^sub>0 \<or> fst x\<lparr>p\<^sub>v := Suc (0::\<nat>)\<rparr> = v\<^sub>0 \<or> fst x\<lparr>p\<^sub>v := 2::\<nat>\<rparr> = v\<^sub>0) \<and>
          (v\<^sub>0\<lparr>c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> v\<^sub>0\<lparr>c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> v\<^sub>0\<lparr>c\<^sub>v := 2::\<nat>\<rparr> = snd x)}
    ) * ( 1 / (9::\<real>))"
    by (simp add: infsum_constant_finite_states)

  have ff1: "card {v\<^sub>0. (fst x\<lparr>p\<^sub>v := 0::\<nat>\<rparr> = v\<^sub>0 \<or> fst x\<lparr>p\<^sub>v := Suc (0::\<nat>)\<rparr> = v\<^sub>0 \<or> fst x\<lparr>p\<^sub>v := 2::\<nat>\<rparr> = v\<^sub>0) \<and>
        (v\<^sub>0\<lparr>c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> v\<^sub>0\<lparr>c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> v\<^sub>0\<lparr>c\<^sub>v := 2::\<nat>\<rparr> = snd x)}
    = ?rhs_1"
    apply (simp add: if_bool_eq_conj)
    apply (rule conjI)
    apply (rule impI)
    apply (rule card_1_singleton)
    apply (rule ex_ex1I)
    apply (rule_tac x = "fst x\<lparr>p\<^sub>v := p\<^sub>v (snd x)\<rparr>" in exI)
    apply (erule conjE)+
    apply (rule conjI)
    apply presburger
    apply (simp add: record_update_simp)
    apply (erule conjE)+
    apply (smt (z3) DWTA_state.ext_inject DWTA_state.surjective DWTA_state.update_convs(1) DWTA_state.update_convs(2))
    apply (rule conjI)
    apply (rule impI)
    apply (smt (verit, ccfv_threshold) DWTA_state.ext_inject DWTA_state.surjective 
          DWTA_state.update_convs(1) DWTA_state.update_convs(2) less_nat_zero_code)
    apply (rule conjI)
    apply (rule impI)
    apply (smt (verit, ccfv_threshold) DWTA_state.ext_inject DWTA_state.surjective 
          DWTA_state.update_convs(1) DWTA_state.update_convs(2) less_nat_zero_code)
    apply (rule impI)
    by (smt (verit, ccfv_threshold) DWTA_state.ext_inject DWTA_state.surjective 
          DWTA_state.update_convs(1) DWTA_state.update_convs(2) less_nat_zero_code)

  show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state. ?lhs_1 v\<^sub>0 / (9::\<real>)) = ?rhs / (9::\<real>) "
    apply (simp only: fr fl)
    using ff1 calculation fl by linarith
qed

lemma conditionals_combined:
  assumes "b\<^sub>1 \<and> b\<^sub>2 = False"
  shows "(if b\<^sub>1 then aa else 0::\<real>) + (if b\<^sub>2 then aa else 0) = (if b\<^sub>1 \<or> b\<^sub>2 then aa else 0)"
  by (simp add: assms)

lemma INIT_altdef': "INIT = prel_of_rfrel ((\<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e) / 9)\<^sub>e"
  apply (simp add: INIT_def INIT_p_def INIT_c_def zero_to_two)
  apply (simp add: prel_uniform_dist_left)
  apply (simp add: uniform_dist_altdef')
  apply (expr_auto add: rel)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (simp only: fun_eq_iff)
  apply (rule allI)
proof -
  fix x :: "DWTA_state \<times> DWTA_state"
  let ?lhs = "((if fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> 
            fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 2::\<nat>\<rparr> = snd x then 1::\<real> else (0::\<real>)) /
        (3::\<real>) +
        ((if fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or>
             fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 2::\<nat>\<rparr> = snd x
          then 1::\<real> else (0::\<real>)) /
         (3::\<real>) +
         (if fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> 
            fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 2::\<nat>\<rparr> = snd x then 1::\<real> else (0::\<real>)) /
         (3::\<real>))) /
       (3::\<real>)"
  let ?rhs = "(if p\<^sub>v (snd x) = (0::\<nat>) \<or> p\<^sub>v (snd x) = Suc (0::\<nat>) \<or> p\<^sub>v (snd x) = (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if c\<^sub>v (snd x) = (0::\<nat>) \<or> c\<^sub>v (snd x) = Suc (0::\<nat>) \<or> c\<^sub>v (snd x) = (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v (snd x) = m\<^sub>v (fst x) then 1::\<real> else (0::\<real>)) /
       (9::\<real>)"
  let ?rhs_1 = "(if (p\<^sub>v (snd x) = (0::\<nat>) \<or> p\<^sub>v (snd x) = Suc (0::\<nat>) \<or> p\<^sub>v (snd x) = (2::\<nat>)) \<and>
       (c\<^sub>v (snd x) = (0::\<nat>) \<or> c\<^sub>v (snd x) = Suc (0::\<nat>) \<or> c\<^sub>v (snd x) = (2::\<nat>)) \<and>
       (m\<^sub>v (snd x) = m\<^sub>v (fst x)) then 1::\<real> else (0::\<real>)) / (9::\<real>)"
  have rhs_1: "?rhs = ?rhs_1"
    by force
  have lhs_1: "?lhs = ((if fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 2::\<nat>\<rparr> = snd x
         then 1::\<real> else (0::\<real>)) +
        (if fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or>
             fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 2::\<nat>\<rparr> = snd x
          then 1::\<real> else (0::\<real>)) +
         (if fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 2::\<nat>\<rparr> = snd x
          then 1::\<real> else (0::\<real>))) / (9::\<real>)"
    by force
  have "((if fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 2::\<nat>\<rparr> = snd x
         then 1::\<real> else (0::\<real>)) +
        (if fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or>
             fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 2::\<nat>\<rparr> = snd x
          then 1::\<real> else (0::\<real>)) +
         (if fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 2::\<nat>\<rparr> = snd x
          then 1::\<real> else (0::\<real>))) = 
      (if fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 2::\<nat>\<rparr> = snd x \<or>
          fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 2::\<nat>\<rparr> = snd x 
          then 1::\<real> else (0::\<real>)) + (if fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 2::\<nat>\<rparr> = snd x
          then 1::\<real> else (0::\<real>))"
    apply (simp add: conditionals_combined)
    apply auto
    by (metis DWTA_state.ext_inject DWTA_state.surjective DWTA_state.update_convs(1) DWTA_state.update_convs(2) One_nat_def one_neq_zero)+
  also have lhs_2: "... =  
      (if fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 2::\<nat>\<rparr> = snd x \<or>
          fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 2::\<nat>\<rparr> = snd x \<or>
          fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 2::\<nat>\<rparr> = snd x
          then 1::\<real> else (0::\<real>))"
    apply (simp add: conditionals_combined)
    apply auto
    using record_neq_p_c apply (metis zero_neq_numeral)+
    using record_neq_p_c by (metis n_not_Suc_n numeral_2_eq_2)+

  have lhs_rhs: "(if fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 2::\<nat>\<rparr> = snd x \<or>
          fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 2::\<nat>\<rparr> = snd x \<or>
          fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 2::\<nat>\<rparr> = snd x
          then 1::\<real> else (0::\<real>)) = (if (p\<^sub>v (snd x) = (0::\<nat>) \<or> p\<^sub>v (snd x) = Suc (0::\<nat>) \<or> p\<^sub>v (snd x) = (2::\<nat>)) \<and>
       (c\<^sub>v (snd x) = (0::\<nat>) \<or> c\<^sub>v (snd x) = Suc (0::\<nat>) \<or> c\<^sub>v (snd x) = (2::\<nat>)) \<and>
       (m\<^sub>v (snd x) = m\<^sub>v (fst x)) then 1::\<real> else (0::\<real>))"
    apply (rule if_cong)
    apply (rule iffI)
    apply (rule conjI)+
    apply (smt (z3) DWTA_state.ext_inject DWTA_state.surjective DWTA_state.update_convs(1) DWTA_state.update_convs(2))
    apply (smt (z3) DWTA_state.ext_inject DWTA_state.surjective DWTA_state.update_convs(1) DWTA_state.update_convs(2))
    apply (metis record_update_simp)
    by simp+
  show "?lhs = ?rhs "
    apply (simp only: lhs_1 rhs_1)
    using calculation lhs_2 lhs_rhs by presburger
qed

subsection \<open> @{text "MHA_NC"} \<close>
lemma card_states_9: "card {s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 0::\<nat>\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 2::\<nat>\<rparr>,
  s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 0::\<nat>\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := Suc (0::\<nat>)\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 2::\<nat>\<rparr>,
  s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 0::\<nat>\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 2::\<nat>\<rparr>} 
  = 9"
  apply (subst card_Suc_Diff1 [where x = "s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 0::\<nat>\<rparr>", symmetric], simp_all)
  apply (subst card_Suc_Diff1 [where x = "s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr>", symmetric], simp_all)
  apply (metis One_nat_def one_neq_zero record_neq_p_c)
  apply (subst card_Suc_Diff1 [where x = "s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 2\<rparr>", symmetric], simp_all)
  apply (metis One_nat_def Suc_1 n_not_Suc_n nat.distinct(1) record_neq_p_c)
  apply (subst card_Suc_Diff1 [where x = "s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 0::\<nat>\<rparr>", symmetric], simp_all)
  apply (metis One_nat_def Suc_1 n_not_Suc_n nat.distinct(1) record_neq_p_c)
  apply (subst card_Suc_Diff1 [where x = "s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := Suc (0::\<nat>)\<rparr>", symmetric], simp_all)
  apply (metis One_nat_def one_neq_zero record_neq_p_c)
  apply (subst card_Suc_Diff1 [where x = "s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 2\<rparr>", symmetric], simp_all)
  apply (metis One_nat_def Suc_1 n_not_Suc_n nat.distinct(1) record_neq_p_c)
  apply (subst card_Suc_Diff1 [where x = "s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 0::\<nat>\<rparr>", symmetric], simp_all)
  apply (metis One_nat_def Suc_1 n_not_Suc_n nat.distinct(1) record_neq_p_c)
  apply (subst card_Suc_Diff1 [where x = "s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr>", symmetric], simp_all)
  using record_neq_p_c apply fastforce
  apply (subst card_Suc_Diff1 [where x = "s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 2\<rparr>", symmetric], simp_all)
  apply (metis One_nat_def Suc_1 n_not_Suc_n nat.distinct(1) record_neq_p_c)
  by fastforce

lemma MHA_NC_altdef: "MHA_NC = 
    prel_of_rfrel (
      (\<lbrakk>c\<^sup>< = p\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> \<lbrakk>m := (c + 1) mod 3\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>\<^sub>e / 2) + 
      (\<lbrakk>c\<^sup>< = p\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> \<lbrakk>m := (c + 2) mod 3\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>\<^sub>e / 2) + 
      (\<lbrakk>c\<^sup>< \<noteq> p\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> \<lbrakk>m := 3 - c - p\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>\<^sub>e)
    )\<^sub>e"
  apply (simp only: dwta_defs)
  apply (simp add: prel_seqcomp_right_unit)
  apply (simp add: prel_pcond_altdef)
  apply (simp only: pchoice_def passigns_def)
  apply (simp only: prel_set_conv_assign)
  apply (subst prel_set_conv_pchoice_c')
  apply (simp)
  apply (meson prel_is_dist_assign)+
  apply (expr_auto add: rel)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  by fastforce

lemma IMHA_altdef: "IMHA_NC = prel_of_rfrel (
      (\<lbrakk>c\<^sup>> = p\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> m\<^sup>> = (c\<^sup>> + 1) mod 3 \<rbrakk>\<^sub>\<I>\<^sub>e / 18) + 
      (\<lbrakk>c\<^sup>> = p\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> m\<^sup>> = (c\<^sup>> + 2) mod 3 \<rbrakk>\<^sub>\<I>\<^sub>e / 18) + 
      (\<lbrakk>c\<^sup>> \<noteq> p\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> m\<^sup>> = 3 - c\<^sup>> - p\<^sup>> \<rbrakk>\<^sub>\<I>\<^sub>e / 9)
    )\<^sub>e"
  apply (simp add: IMHA_NC_def zero_to_two)
  apply (simp add: INIT_altdef MHA_NC_altdef)
  apply (simp add: prel_defs)
  apply (subst prel_of_rfrel_inverse)
  apply (simp add: expr_defs dist_defs)
  apply (rule allI)
  defer
  apply (subst prel_of_rfrel_inverse)
  apply (simp add: expr_defs dist_defs)
  apply (rule allI, rule conjI)
  apply (rel_auto)
  apply (rule infsum_singleton)
  apply (rel_auto)
  apply (subst infsum_add)
  apply (rule summable_on_cdiv_left)
  apply (rule infsum_singleton_summable, simp)
  apply (rule summable_on_cdiv_left)
  apply (rule infsum_singleton_summable, simp)
  apply (subst infsum_cdiv_left)
  apply (rule infsum_singleton_summable, simp)
  apply (subst infsum_cdiv_left)
  apply (rule infsum_singleton_summable, simp)
  apply (subst infsum_singleton)
  apply (subst infsum_singleton)
  apply (simp)
  apply (rel_auto)
   apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (subst fun_eq_iff, rule allI)
  defer
proof -
  fix s\<^sub>1::"DWTA_state"
  have set_states: "{s::DWTA_state. get\<^bsub>p\<^esub> s \<le> (2::\<nat>) \<and> get\<^bsub>c\<^esub> s \<le> (2::\<nat>) \<and> get\<^bsub>m\<^esub> s = get\<^bsub>m\<^esub> s\<^sub>1}
    = {s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 0::\<nat>\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 2::\<nat>\<rparr>,
          s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 0::\<nat>\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := Suc (0::\<nat>)\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 2::\<nat>\<rparr>,
          s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 0::\<nat>\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 2::\<nat>\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
    apply (smt (z3) DWTA_state.surjective DWTA_state.update_convs(1) DWTA_state.update_convs(2) 
          One_nat_def Suc_1 bot_nat_0.extremum_unique c_def le_Suc_eq lens.simps(1) m_def old.unit.exhaust p_def)
    by (smt (verit, best) DWTA_state.ext_inject DWTA_state.surjective DWTA_state.update_convs(1) 
          DWTA_state.update_convs(2) One_nat_def bot_nat_0.extremum c_def lens.simps(1) less_one 
          linorder_not_le m_def order_le_less p_def zero_neq_numeral)
  have "(\<Sum>\<^sub>\<infinity>s::DWTA_state.
          (if get\<^bsub>p\<^esub> s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * (if get\<^bsub>c\<^esub> s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
          (if get\<^bsub>m\<^esub> s = get\<^bsub>m\<^esub> s\<^sub>1 then 1::\<real> else (0::\<real>)) /
          (9::\<real>)) = 
    (\<Sum>\<^sub>\<infinity>s::DWTA_state.
          (if get\<^bsub>p\<^esub> s \<le> (2::\<nat>) \<and> get\<^bsub>c\<^esub> s \<le> (2::\<nat>) \<and> get\<^bsub>m\<^esub> s = get\<^bsub>m\<^esub> s\<^sub>1 then 1::\<real> else (0::\<real>)) /
          (9::\<real>))"
    by (smt (verit) infsum_cong mult_cancel_left1 mult_not_zero)
  also have "... = (\<Sum>\<^sub>\<infinity>s::DWTA_state.
    (if get\<^bsub>p\<^esub> s \<le> (2::\<nat>) \<and> get\<^bsub>c\<^esub> s \<le> (2::\<nat>) \<and> get\<^bsub>m\<^esub> s = get\<^bsub>m\<^esub> s\<^sub>1 then 1::\<real> else (0::\<real>))) /
    (9::\<real>)"
    apply (rule infsum_cdiv_left)
    apply (rule infsum_constant_finite_states_summable)
    by (simp add: set_states)
  also have "... = (card {s::DWTA_state. get\<^bsub>p\<^esub> s \<le> (2::\<nat>) \<and> get\<^bsub>c\<^esub> s \<le> (2::\<nat>) \<and> get\<^bsub>m\<^esub> s = get\<^bsub>m\<^esub> s\<^sub>1}) / 9"
    apply (subst infsum_constant_finite_states)
    apply (simp add: set_states)
    by linarith
    (*by (smt (z3) DWTA_state.ext_inject DWTA_state.surjective DWTA_state.update_convs(2) card.empty 
        card.insert finite.intros(1) finite_insert insert_iff numeral_1_eq_Suc_0 numeral_2_eq_2 
        numeral_3_eq_3 numeral_eq_iff semiring_norm(84) singletonD)*)
  also have "... = 1"
    apply (simp add: set_states)
    by (simp add: card_states_9)
    
  then show "(\<Sum>\<^sub>\<infinity>s::DWTA_state.
          (if get\<^bsub>p\<^esub> s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * (if get\<^bsub>c\<^esub> s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
          (if get\<^bsub>m\<^esub> s = get\<^bsub>m\<^esub> s\<^sub>1 then 1::\<real> else (0::\<real>)) /
          (9::\<real>)) = (1::\<real>)"
    using calculation by presburger
next
  fix x :: "DWTA_state \<times> DWTA_state"
  let ?lhs_p = "\<lambda>v\<^sub>0. (if p\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>))"
  let ?lhs_c = "\<lambda>v\<^sub>0. (if c\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>))"
  let ?lhs_m = "\<lambda>v\<^sub>0. (if m\<^sub>v v\<^sub>0 = m\<^sub>v (fst x) then 1::\<real> else (0::\<real>))"
  let ?lhs_c_p = "\<lambda>v\<^sub>0. (if c\<^sub>v v\<^sub>0 = p\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>))"
  let ?lhs_c_n_p = "\<lambda>v\<^sub>0. (if \<not> c\<^sub>v v\<^sub>0 = p\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>))"
  let ?m_1_mod = "\<lambda>v\<^sub>0. (if v\<^sub>0\<lparr>m\<^sub>v := Suc (c\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = snd x then 1::\<real> else (0::\<real>))"
  let ?m_2_mod = "\<lambda>v\<^sub>0. (if v\<^sub>0\<lparr>m\<^sub>v := Suc (Suc (c\<^sub>v v\<^sub>0)) mod (3::\<nat>)\<rparr> = snd x then 1::\<real> else (0::\<real>))"
  let ?m_3_c_p = "\<lambda>v\<^sub>0. (if v\<^sub>0\<lparr>m\<^sub>v := (3::\<nat>) - (c\<^sub>v v\<^sub>0 + p\<^sub>v v\<^sub>0)\<rparr> = snd x then 1::\<real> else (0::\<real>))"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state.
          ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 *
          (?lhs_c_p v\<^sub>0 * ?m_1_mod v\<^sub>0 / (2::\<real>) +
           ?lhs_c_p v\<^sub>0 * ?m_2_mod v\<^sub>0 / (2::\<real>) +
           ?lhs_c_n_p v\<^sub>0 * ?m_3_c_p v\<^sub>0) / (9::\<real>))"
  let ?rhs_1 = "(if c\<^sub>v (snd x) = p\<^sub>v (snd x) then 1::\<real> else (0::\<real>)) *
       (if p\<^sub>v (snd x) = (0::\<nat>) \<or> p\<^sub>v (snd x) = Suc (0::\<nat>) \<or> p\<^sub>v (snd x) = (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if c\<^sub>v (snd x) = (0::\<nat>) \<or> c\<^sub>v (snd x) = Suc (0::\<nat>) \<or> c\<^sub>v (snd x) = (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v (snd x) = Suc (c\<^sub>v (snd x)) mod (3::\<nat>) then 1::\<real> else (0::\<real>))"
  let ?rhs_2 = "(if c\<^sub>v (snd x) = p\<^sub>v (snd x) then 1::\<real> else (0::\<real>)) *
       (if p\<^sub>v (snd x) = (0::\<nat>) \<or> p\<^sub>v (snd x) = Suc (0::\<nat>) \<or> p\<^sub>v (snd x) = (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if c\<^sub>v (snd x) = (0::\<nat>) \<or> c\<^sub>v (snd x) = Suc (0::\<nat>) \<or> c\<^sub>v (snd x) = (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v (snd x) = Suc (Suc (c\<^sub>v (snd x))) mod (3::\<nat>) then 1::\<real> else (0::\<real>))"
  let ?rhs_3 = "(if \<not> c\<^sub>v (snd x) = p\<^sub>v (snd x) then 1::\<real> else (0::\<real>)) *
       (if p\<^sub>v (snd x) = (0::\<nat>) \<or> p\<^sub>v (snd x) = Suc (0::\<nat>) \<or> p\<^sub>v (snd x) = (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if c\<^sub>v (snd x) = (0::\<nat>) \<or> c\<^sub>v (snd x) = Suc (0::\<nat>) \<or> c\<^sub>v (snd x) = (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v (snd x) = (3::\<nat>) - (c\<^sub>v (snd x) + p\<^sub>v (snd x)) then 1::\<real> else (0::\<real>))"
  let ?rhs = "?rhs_1 / (18::\<real>) + ?rhs_2 / (18::\<real>) + ?rhs_3 / (9::\<real>) "

  let ?rhs_1_1 = "(if (c\<^sub>v (snd x) = p\<^sub>v (snd x) \<and> 
      (p\<^sub>v (snd x) = (0::\<nat>) \<or> p\<^sub>v (snd x) = Suc (0::\<nat>) \<or> p\<^sub>v (snd x) = (2::\<nat>)) \<and>
      (c\<^sub>v (snd x) = (0::\<nat>) \<or> c\<^sub>v (snd x) = Suc (0::\<nat>) \<or> c\<^sub>v (snd x) = (2::\<nat>)) \<and>
      (m\<^sub>v (snd x) = Suc (c\<^sub>v (snd x)) mod (3::\<nat>))) then 1::\<real> else (0::\<real>))"
  let ?rhs_1_2 = "(if (c\<^sub>v (snd x) = p\<^sub>v (snd x) \<and> 
      (p\<^sub>v (snd x) = (0::\<nat>) \<or> p\<^sub>v (snd x) = Suc (0::\<nat>) \<or> p\<^sub>v (snd x) = (2::\<nat>)) \<and>
      (c\<^sub>v (snd x) = (0::\<nat>) \<or> c\<^sub>v (snd x) = Suc (0::\<nat>) \<or> c\<^sub>v (snd x) = (2::\<nat>)) \<and>
      (m\<^sub>v (snd x) = Suc (Suc (c\<^sub>v (snd x))) mod (3::\<nat>))) then 1::\<real> else (0::\<real>))"
  let ?rhs_1_3 = "(if (\<not>c\<^sub>v (snd x) = p\<^sub>v (snd x) \<and> 
      (p\<^sub>v (snd x) = (0::\<nat>) \<or> p\<^sub>v (snd x) = Suc (0::\<nat>) \<or> p\<^sub>v (snd x) = (2::\<nat>)) \<and>
      (c\<^sub>v (snd x) = (0::\<nat>) \<or> c\<^sub>v (snd x) = Suc (0::\<nat>) \<or> c\<^sub>v (snd x) = (2::\<nat>)) \<and>
      (m\<^sub>v (snd x) = (3::\<nat>) - (c\<^sub>v (snd x) + p\<^sub>v (snd x)))) then 1::\<real> else (0::\<real>))"
  have rhs_1_1: "?rhs_1 = ?rhs_1_1"
    by simp
  have rhs_1_2: "?rhs_2 = ?rhs_1_2"
    by simp
  have rhs_1_3: "?rhs_3 = ?rhs_1_3"
    by simp
(* lhs_1 *)
  have lhs_1_f0: "(\<lambda>v\<^sub>0. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_1_mod v\<^sub>0) = 
      (\<lambda>v\<^sub>0. (if p\<^sub>v v\<^sub>0 \<le> (2::\<nat>) \<and>  c\<^sub>v v\<^sub>0 \<le> (2::\<nat>) \<and> m\<^sub>v v\<^sub>0 = m\<^sub>v (fst x) \<and> c\<^sub>v v\<^sub>0 = p\<^sub>v v\<^sub>0 \<and> 
            v\<^sub>0\<lparr>m\<^sub>v := Suc (c\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = snd x then 1::\<real> else (0::\<real>)))"
      by auto
  have lhs_1_set_simp: "{s::DWTA_state. p\<^sub>v s \<le> (2::\<nat>) \<and>
    c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v (fst x) \<and> c\<^sub>v s = p\<^sub>v s}
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = m\<^sub>v (fst x)\<rparr>,\<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>, 
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = m\<^sub>v (fst x)\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
    apply (metis (mono_tags, opaque_lifting) DWTA_state.surjective bot_nat_0.extremum le_SucE 
          le_antisym numeral_2_eq_2 old.unit.exhaust)
    by fastforce
  have lhs_1_set_A_finite: "finite {s::DWTA_state. p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v (fst x) \<and> c\<^sub>v s = p\<^sub>v s}"
    by (simp add: lhs_1_set_simp)

  have lhs_1_summable: "(\<lambda>v\<^sub>0. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_1_mod v\<^sub>0) summable_on UNIV"
    apply (simp add: lhs_1_f0)
    apply (rule infsum_constant_finite_states_summable)
    apply (rule rev_finite_subset[where B=
          "{s::DWTA_state. p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v (fst x) \<and> c\<^sub>v s = p\<^sub>v s}"])
    apply (simp add: lhs_1_set_A_finite)
    by blast

  have lhs_1_infsum: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_1_mod v\<^sub>0)
    = ?rhs_1_1"
    apply (simp only: lhs_1_f0)
    apply (subst infsum_constant_finite_states)
    apply (rule rev_finite_subset[where B=
          "{s::DWTA_state. p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v (fst x) \<and> c\<^sub>v s = p\<^sub>v s}"])
    apply (simp add: lhs_1_set_A_finite)
    apply (blast)
    apply (simp add: if_bool_eq_conj)
    apply (rule conjI)
    apply (rule impI)
    apply (rule card_1_singleton)
    apply (rule ex_ex1I)
    apply (rule_tac x = "\<lparr>p\<^sub>v = Suc (Suc (m\<^sub>v (snd x))) mod (3::\<nat>), 
      c\<^sub>v = Suc (Suc (m\<^sub>v (snd x))) mod (3::\<nat>), m\<^sub>v = m\<^sub>v (fst x) \<rparr>" in exI)
    apply (erule conjE)+
    apply (rule conjI)
    apply (metis DWTA_state.select_convs(1) mod_Suc_le_divisor numeral_2_eq_2 numeral_3_eq_3)
    apply (rule conjI)
    apply (metis DWTA_state.select_convs(2) mod_Suc_le_divisor numeral_2_eq_2 numeral_3_eq_3)
    apply (rule conjI)
    apply (metis DWTA_state.select_convs(3))
    apply (rule conjI)
    apply (metis DWTA_state.select_convs(1) DWTA_state.select_convs(2))
    defer
    apply (metis DWTA_state.surjective DWTA_state.update_convs(3))
    apply (smt (verit, best) Collect_empty_eq DWTA_state.select_convs(1) DWTA_state.select_convs(2) 
        DWTA_state.select_convs(3) DWTA_state.surjective DWTA_state.update_convs(3) card_eq_0_iff 
        less_2_cases less_numeral_extra(3) order_le_less)
  proof -
    assume a1: "m\<^sub>v (snd x) = Suc (c\<^sub>v (snd x)) mod (3::\<nat>)"
    assume a2: "c\<^sub>v (snd x) = (0::\<nat>) \<or> c\<^sub>v (snd x) = Suc (0::\<nat>) \<or> c\<^sub>v (snd x) = (2::\<nat>)"
    assume a3: "p\<^sub>v (snd x) = (0::\<nat>) \<or> p\<^sub>v (snd x) = Suc (0::\<nat>) \<or> p\<^sub>v (snd x) = (2::\<nat>)"
    assume a4: "c\<^sub>v (snd x) = p\<^sub>v (snd x)"
    (* have "Suc (Suc (Suc (c\<^sub>v (snd x)) mod (3::\<nat>))) mod (3::\<nat>) = c\<^sub>v (snd x)"
      apply (simp add: mod_Suc_Suc_eq)
      using a2 by fastforce
    *)
    have "\<lparr>p\<^sub>v = Suc (Suc (m\<^sub>v (snd x))) mod (3::\<nat>), c\<^sub>v = Suc (Suc (m\<^sub>v (snd x))) mod (3::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>
        \<lparr>m\<^sub>v := Suc (c\<^sub>v \<lparr>p\<^sub>v = Suc (Suc (m\<^sub>v (snd x))) mod (3::\<nat>), c\<^sub>v = Suc (Suc (m\<^sub>v (snd x))) mod (3::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>) mod (3::\<nat>)\<rparr>
      = \<lparr>p\<^sub>v = Suc (Suc (m\<^sub>v (snd x))) mod (3::\<nat>), c\<^sub>v = Suc (Suc (m\<^sub>v (snd x))) mod (3::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>
        \<lparr>m\<^sub>v := Suc (Suc (Suc (m\<^sub>v (snd x))) mod (3::\<nat>)) mod (3::\<nat>)\<rparr>"
      by (metis DWTA_state.select_convs(2))
    also have "... = \<lparr>p\<^sub>v = Suc (Suc (m\<^sub>v (snd x))) mod (3::\<nat>), c\<^sub>v = Suc (Suc (m\<^sub>v (snd x))) mod (3::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>
        \<lparr>m\<^sub>v := m\<^sub>v (snd x)\<rparr>"
      by (simp add: a1 mod_Suc_eq)
    also have "... = \<lparr>p\<^sub>v = Suc (Suc (Suc (c\<^sub>v (snd x)) mod (3::\<nat>))) mod (3::\<nat>), 
        c\<^sub>v = Suc (Suc (Suc (c\<^sub>v (snd x)) mod (3::\<nat>))) mod (3::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>\<lparr>m\<^sub>v := m\<^sub>v (snd x)\<rparr>"
      by (simp add: a1)
    also have "... = \<lparr>p\<^sub>v = c\<^sub>v (snd x), c\<^sub>v = c\<^sub>v (snd x), m\<^sub>v = m\<^sub>v (fst x)\<rparr>\<lparr>m\<^sub>v := m\<^sub>v (snd x)\<rparr>"
      using a2 by fastforce
    also have "... = \<lparr>p\<^sub>v = c\<^sub>v (snd x), c\<^sub>v = c\<^sub>v (snd x), m\<^sub>v = m\<^sub>v (snd x)\<rparr>"
      by auto
    also have "... = snd x"
      by (simp add: a4)
    then show "\<lparr>p\<^sub>v = Suc (Suc (m\<^sub>v (snd x))) mod (3::\<nat>), c\<^sub>v = Suc (Suc (m\<^sub>v (snd x))) mod (3::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>
        \<lparr>m\<^sub>v := Suc (c\<^sub>v \<lparr>p\<^sub>v = Suc (Suc (m\<^sub>v (snd x))) mod (3::\<nat>), c\<^sub>v = Suc (Suc (m\<^sub>v (snd x))) mod (3::\<nat>), 
        m\<^sub>v = m\<^sub>v (fst x)\<rparr>) mod (3::\<nat>)\<rparr> = snd x"
      using calculation by presburger
  qed

(* lhs_2 *)
  have lhs_2_f0: "(\<lambda>v\<^sub>0. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_2_mod v\<^sub>0) = 
      (\<lambda>v\<^sub>0. (if p\<^sub>v v\<^sub>0 \<le> (2::\<nat>) \<and>  c\<^sub>v v\<^sub>0 \<le> (2::\<nat>) \<and> m\<^sub>v v\<^sub>0 = m\<^sub>v (fst x) \<and> c\<^sub>v v\<^sub>0 = p\<^sub>v v\<^sub>0 \<and> 
            v\<^sub>0\<lparr>m\<^sub>v := Suc (Suc (c\<^sub>v v\<^sub>0)) mod (3::\<nat>)\<rparr> = snd x then 1::\<real> else (0::\<real>)))"
      by auto
  have lhs_2_summable: "(\<lambda>v\<^sub>0. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_2_mod v\<^sub>0) summable_on UNIV"
    apply (simp add: lhs_2_f0)
    apply (rule infsum_constant_finite_states_summable)
    apply (rule rev_finite_subset[where B=
          "{s::DWTA_state. p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v (fst x) \<and> c\<^sub>v s = p\<^sub>v s}"])
    apply (simp add: lhs_1_set_A_finite)
    by blast

  have lhs_2_infsum: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_2_mod v\<^sub>0)
    = ?rhs_1_2"
    apply (simp only: lhs_2_f0)
    apply (subst infsum_constant_finite_states)
    apply (rule rev_finite_subset[where B=
          "{s::DWTA_state. p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v (fst x) \<and> c\<^sub>v s = p\<^sub>v s}"])
    apply (simp add: lhs_1_set_A_finite)
    apply (blast)
    apply (simp add: if_bool_eq_conj)
    apply (rule conjI)
    apply (rule impI)
    apply (rule card_1_singleton)
    apply (rule ex_ex1I)
    apply (rule_tac x = "\<lparr>p\<^sub>v = Suc (m\<^sub>v (snd x)) mod (3::\<nat>), 
      c\<^sub>v = Suc (m\<^sub>v (snd x)) mod (3::\<nat>), m\<^sub>v = m\<^sub>v (fst x) \<rparr>" in exI)
    apply (erule conjE)+
    apply (rule conjI)
    apply (metis DWTA_state.select_convs(1) mod_Suc_le_divisor numeral_2_eq_2 numeral_3_eq_3)
    apply (rule conjI)
    apply (metis DWTA_state.select_convs(2) mod_Suc_le_divisor numeral_2_eq_2 numeral_3_eq_3)
    apply (rule conjI)
    apply (metis DWTA_state.select_convs(3))
    apply (rule conjI)
    apply (metis DWTA_state.select_convs(1) DWTA_state.select_convs(2))
    defer
    apply (metis DWTA_state.surjective DWTA_state.update_convs(3))
    apply (smt (verit, best) Collect_empty_eq DWTA_state.select_convs(1) DWTA_state.select_convs(2) 
        DWTA_state.select_convs(3) DWTA_state.surjective DWTA_state.update_convs(3) card_eq_0_iff 
        less_2_cases less_numeral_extra(3) order_le_less)
  proof -
    assume a1: "m\<^sub>v (snd x) = Suc (Suc (c\<^sub>v (snd x))) mod (3::\<nat>)"
    assume a2: "c\<^sub>v (snd x) = (0::\<nat>) \<or> c\<^sub>v (snd x) = Suc (0::\<nat>) \<or> c\<^sub>v (snd x) = (2::\<nat>)"
    assume a3: "p\<^sub>v (snd x) = (0::\<nat>) \<or> p\<^sub>v (snd x) = Suc (0::\<nat>) \<or> p\<^sub>v (snd x) = (2::\<nat>)"
    assume a4: "c\<^sub>v (snd x) = p\<^sub>v (snd x)"

    have "\<lparr>p\<^sub>v = Suc (m\<^sub>v (snd x)) mod (3::\<nat>), c\<^sub>v = Suc (m\<^sub>v (snd x)) mod (3::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>
        \<lparr>m\<^sub>v := Suc (Suc (c\<^sub>v \<lparr>p\<^sub>v = Suc (m\<^sub>v (snd x)) mod (3::\<nat>), c\<^sub>v = Suc (m\<^sub>v (snd x)) mod (3::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>)) mod (3::\<nat>)\<rparr>
      = \<lparr>p\<^sub>v = Suc (m\<^sub>v (snd x)) mod (3::\<nat>), c\<^sub>v = Suc (m\<^sub>v (snd x)) mod (3::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>
        \<lparr>m\<^sub>v := Suc (Suc (Suc (m\<^sub>v (snd x)) mod (3::\<nat>)) mod (3::\<nat>)) mod (3::\<nat>)\<rparr>"
      by (metis DWTA_state.select_convs(2) DWTA_state.unfold_congs(3) mod_Suc_eq)
    also have "... = \<lparr>p\<^sub>v = Suc (m\<^sub>v (snd x)) mod (3::\<nat>), c\<^sub>v = Suc (m\<^sub>v (snd x)) mod (3::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>
        \<lparr>m\<^sub>v := (m\<^sub>v (snd x))\<rparr>"
      by (simp add: a1 mod_Suc_eq)
    also have "... = \<lparr>p\<^sub>v = c\<^sub>v (snd x), c\<^sub>v = c\<^sub>v (snd x), m\<^sub>v = (m\<^sub>v (snd x))\<rparr>"
      by (smt (z3) DWTA_state.update_convs(3) Suc_mod_eq_add3_mod_numeral a1 a3 a4 
          add_cancel_left_left divmod_algorithm_code(3) divmod_algorithm_code(4) mod_Suc mod_add_self1 
          numeral_1_eq_Suc_0 numeral_2_eq_2 one_mod_two_eq_one plus_1_eq_Suc snd_divmod)
    also have "... = snd x"
      by (simp add: a4)
    then show "\<lparr>p\<^sub>v = Suc (m\<^sub>v (snd x)) mod (3::\<nat>), c\<^sub>v = Suc (m\<^sub>v (snd x)) mod (3::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>
        \<lparr>m\<^sub>v := Suc (Suc (c\<^sub>v \<lparr>p\<^sub>v = Suc (m\<^sub>v (snd x)) mod (3::\<nat>), c\<^sub>v = Suc (m\<^sub>v (snd x)) mod (3::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>)) mod (3::\<nat>)\<rparr> = snd x"
      using calculation by presburger
  qed

(* lhs_3 *)
  have lhs_3_f0: "(\<lambda>v\<^sub>0. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_n_p v\<^sub>0 * ?m_3_c_p v\<^sub>0) = 
      (\<lambda>v\<^sub>0. (if p\<^sub>v v\<^sub>0 \<le> (2::\<nat>) \<and>  c\<^sub>v v\<^sub>0 \<le> (2::\<nat>) \<and> m\<^sub>v v\<^sub>0 = m\<^sub>v (fst x) \<and> \<not> c\<^sub>v v\<^sub>0 = p\<^sub>v v\<^sub>0 \<and> 
            v\<^sub>0\<lparr>m\<^sub>v := (3::\<nat>) - (c\<^sub>v v\<^sub>0 + p\<^sub>v v\<^sub>0)\<rparr> = snd x then 1::\<real> else (0::\<real>)))"
      by auto
  have lhs_3_set_simp: "{s::DWTA_state. p\<^sub>v s \<le> (2::\<nat>) \<and>
    c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v (fst x) \<and>  \<not>c\<^sub>v s = p\<^sub>v s}
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 1::\<nat>, m\<^sub>v = m\<^sub>v (fst x)\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = m\<^sub>v (fst x)\<rparr>, 
       \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = (0::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = (2::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>, 
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = m\<^sub>v (fst x)\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
    apply (metis (mono_tags, opaque_lifting) DWTA_state.surjective bot_nat_0.extremum le_SucE 
          le_antisym numeral_2_eq_2 old.unit.exhaust)
    by fastforce
  have lhs_3_set_A_finite: "finite {s::DWTA_state. p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v (fst x) \<and> \<not>c\<^sub>v s = p\<^sub>v s}"
    by (simp add: lhs_3_set_simp)
  have lhs_3_summable: "(\<lambda>v\<^sub>0. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_n_p v\<^sub>0 * ?m_3_c_p v\<^sub>0) summable_on UNIV"
    apply (simp add: lhs_3_f0)
    apply (rule infsum_constant_finite_states_summable)
    apply (rule rev_finite_subset[where B=
          "{s::DWTA_state. p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v (fst x) \<and> \<not>c\<^sub>v s = p\<^sub>v s}"])
    apply (simp add: lhs_3_set_A_finite)
    by blast

  have lhs_3_infsum: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_n_p v\<^sub>0 * ?m_3_c_p v\<^sub>0)
    = ?rhs_1_3"
    apply (simp only: lhs_3_f0)
    apply (subst infsum_constant_finite_states)
    apply (rule rev_finite_subset[where B=
          "{s::DWTA_state. p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v (fst x) \<and> \<not>c\<^sub>v s = p\<^sub>v s}"])
    apply (simp add: lhs_3_set_A_finite)
    apply (blast)
    apply (simp add: if_bool_eq_conj)
    apply (rule conjI)
    apply (rule impI)
    apply (rule card_1_singleton)
    apply (rule ex_ex1I)
    apply (rule_tac x = "\<lparr>p\<^sub>v = (3::\<nat>) - (m\<^sub>v (snd x)) - c\<^sub>v (snd x), 
      c\<^sub>v = (3::\<nat>) - (m\<^sub>v (snd x)) - p\<^sub>v (snd x), m\<^sub>v = m\<^sub>v (fst x) \<rparr>" in exI)
    apply (erule conjE)+
    apply (rule conjI)
    apply fastforce
    apply (rule conjI)
    apply fastforce
    apply (rule conjI)
    apply (simp)
    apply (rule conjI)
    apply fastforce
    defer
    apply (metis DWTA_state.surjective DWTA_state.update_convs(3))
    apply (smt (verit, best) Collect_empty_eq DWTA_state.select_convs(1) DWTA_state.select_convs(2) 
        DWTA_state.select_convs(3) DWTA_state.surjective DWTA_state.update_convs(3) card_eq_0_iff 
        less_2_cases less_numeral_extra(3) order_le_less)
  proof -
    assume a1: "m\<^sub>v (snd x) = (3::\<nat>) - (c\<^sub>v (snd x) + p\<^sub>v (snd x))"
    assume a2: "c\<^sub>v (snd x) = (0::\<nat>) \<or> c\<^sub>v (snd x) = Suc (0::\<nat>) \<or> c\<^sub>v (snd x) = (2::\<nat>)"
    assume a3: "p\<^sub>v (snd x) = (0::\<nat>) \<or> p\<^sub>v (snd x) = Suc (0::\<nat>) \<or> p\<^sub>v (snd x) = (2::\<nat>)"
    assume a4: "\<not> c\<^sub>v (snd x) = p\<^sub>v (snd x)"

    have f0: "(3::\<nat>) - (((3::\<nat>) - m\<^sub>v (snd x) - p\<^sub>v (snd x)) + ((3::\<nat>) - m\<^sub>v (snd x) - c\<^sub>v (snd x)))
        = (2 * m\<^sub>v (snd x)) + p\<^sub>v (snd x) + c\<^sub>v (snd x) - 3"
      using a1 a2 a3 diff_zero by fastforce
    also have f1: "... = 3 - p\<^sub>v (snd x) - c\<^sub>v (snd x)"
      using a1 a2 a3 a4 by auto
    have lhs_0: "\<lparr>p\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - c\<^sub>v (snd x), c\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - p\<^sub>v (snd x), m\<^sub>v = m\<^sub>v (fst x)\<rparr>
      \<lparr>m\<^sub>v := (3::\<nat>) - (c\<^sub>v \<lparr>p\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - c\<^sub>v (snd x), c\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - p\<^sub>v (snd x), m\<^sub>v = m\<^sub>v (fst x)\<rparr> +
        p\<^sub>v \<lparr>p\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - c\<^sub>v (snd x), c\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - p\<^sub>v (snd x), m\<^sub>v = m\<^sub>v (fst x)\<rparr>)\<rparr>
      = \<lparr>p\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - c\<^sub>v (snd x), c\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - p\<^sub>v (snd x), m\<^sub>v = m\<^sub>v (fst x)\<rparr>
      \<lparr>m\<^sub>v := (3::\<nat>) - (((3::\<nat>) - m\<^sub>v (snd x) - p\<^sub>v (snd x)) + ((3::\<nat>) - m\<^sub>v (snd x) - c\<^sub>v (snd x)))\<rparr>"
      by force
    have lhs_1: "... = \<lparr>p\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - c\<^sub>v (snd x), c\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - p\<^sub>v (snd x), m\<^sub>v = m\<^sub>v (fst x)\<rparr>
        \<lparr>m\<^sub>v := 3 - p\<^sub>v (snd x) - c\<^sub>v (snd x)\<rparr>"
      using f0 f1 by presburger
    have lhs_2: "... = \<lparr>p\<^sub>v = p\<^sub>v (snd x), c\<^sub>v = c\<^sub>v (snd x), m\<^sub>v = m\<^sub>v (snd x)\<rparr>"
      using DWTA_state.update_convs(3) a1 a2 a3 a4 add.commute add.right_neutral by fastforce
    have lhs_3: "... = snd x"
      by (simp add: a4)
    show "\<lparr>p\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - c\<^sub>v (snd x), c\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - p\<^sub>v (snd x), m\<^sub>v = m\<^sub>v (fst x)\<rparr>
      \<lparr>m\<^sub>v := (3::\<nat>) - (c\<^sub>v \<lparr>p\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - c\<^sub>v (snd x), c\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - p\<^sub>v (snd x), m\<^sub>v = m\<^sub>v (fst x)\<rparr> +
        p\<^sub>v \<lparr>p\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - c\<^sub>v (snd x), c\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - p\<^sub>v (snd x), m\<^sub>v = m\<^sub>v (fst x)\<rparr>)\<rparr> = snd x"
      using lhs_0 lhs_1 lhs_2 lhs_3 by presburger
  qed

  have lhs_1: "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state.
          ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 *
          (?lhs_c_p v\<^sub>0 * ?m_1_mod v\<^sub>0 / (18::\<real>) +
           ?lhs_c_p v\<^sub>0 * ?m_2_mod v\<^sub>0 / (18::\<real>) +
           ?lhs_c_n_p v\<^sub>0 * ?m_3_c_p v\<^sub>0 / (9::\<real>)))"
    apply (rule infsum_cong)
    by (simp add: add_divide_distrib)
  also have lhs_2: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state.
          ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_1_mod v\<^sub>0 / (18::\<real>) +
          ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_2_mod v\<^sub>0 / (18::\<real>) +
          ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_n_p v\<^sub>0 * ?m_3_c_p v\<^sub>0 / (9::\<real>))"
    apply (rule infsum_cong)
    by simp
  also have lhs_3: "... = 
    (\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_1_mod v\<^sub>0 / (18::\<real>)) +
    (\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_2_mod v\<^sub>0 / (18::\<real>)) +
    (\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_n_p v\<^sub>0 * ?m_3_c_p v\<^sub>0 / (9::\<real>))"
    apply (subst infsum_add)
    apply (rule summable_on_add)
    apply (rule summable_on_cdiv_left)
    using lhs_1_summable apply blast
    apply (rule summable_on_cdiv_left)
    using lhs_2_summable apply blast
    apply (rule summable_on_cdiv_left)
    using lhs_3_summable apply blast
    apply (subst infsum_add)
    apply (rule summable_on_cdiv_left)
    using lhs_1_summable apply blast
    apply (rule summable_on_cdiv_left)
    using lhs_2_summable apply blast
    by meson
  also have lhs_4: "... = 
    (\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_1_mod v\<^sub>0) / (18::\<real>) +
    (\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_2_mod v\<^sub>0) / (18::\<real>) +
    (\<Sum>\<^sub>\<infinity>v\<^sub>0::DWTA_state. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_n_p v\<^sub>0 * ?m_3_c_p v\<^sub>0) / (9::\<real>)"
    apply (subst infsum_cdiv_left)
    using lhs_1_summable apply blast
    apply (subst infsum_cdiv_left)
    using lhs_2_summable apply blast
    apply (subst infsum_cdiv_left)
    using lhs_3_summable apply blast
    by simp
  then show "?lhs = ?rhs"
    using calculation lhs_1_infsum lhs_2_infsum lhs_3_infsum rhs_1_1 rhs_1_2 rhs_1_3 by presburger
qed

end
