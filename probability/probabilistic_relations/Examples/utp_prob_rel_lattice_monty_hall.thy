section \<open> Example of probabilistic relation programming: Monty Hall \<close>

theory utp_prob_rel_lattice_monty_hall
  imports 
    "../utp_prob_rel_lattice_laws" 
begin 

unbundle UTP_Syntax

declare [[show_types]]

named_theorems dwta_defs

alphabet mh_state = 
  p :: nat
  c :: nat
  m :: nat

subsection \<open> Definitions \<close>
definition INIT_p :: "mh_state prhfun" where 
[dwta_defs]: "INIT_p = prfun_of_rvfun (p \<^bold>\<U> {0..2})"

definition INIT_c :: "mh_state prhfun" where 
[dwta_defs]: "INIT_c = prfun_of_rvfun (c \<^bold>\<U> {0..2})"

definition INIT:: "mh_state prhfun" where 
[dwta_defs]: "INIT = INIT_p ; INIT_c"

term "(x)\<lparr>c\<^sub>v := Suc (0::\<nat>)\<rparr>"
find_theorems name:"mh_state"
record x = i :: nat

thm "mh_state.select_convs"
thm "mh_state.surjective"
thm "mh_state.update_convs"

abbreviation MHA_1 :: "mh_state prhfun" where 
"MHA_1 \<equiv> (if\<^sub>p 1/2 then (m := ($c + 1) mod 3) else (m := ($c + 2) mod 3))"

definition MHA:: "mh_state prhfun" where
[dwta_defs]: "MHA = (if\<^sub>c c\<^sup>< = p\<^sup>< then 
          MHA_1 
        else 
          (m := 3 - $c - $p)
      )"

definition MHA_NC:: "mh_state prhfun" where
[dwta_defs]: "MHA_NC = MHA ; II" (* No Change Strategy *)

definition MHA_C:: "mh_state prhfun" where
[dwta_defs]: "MHA_C = MHA ; c := 3 - c - m" (* Change Strategy *)

thm "MHA_def"

definition IMHA_NC where 
[dwta_defs]: "IMHA_NC = INIT ; MHA_NC"

definition IMHA_C where 
[dwta_defs]: "IMHA_C = INIT ; MHA_C"

subsection \<open> @{text "INIT"} \<close>

lemma zero_to_two: "{0..2::\<nat>} = {0, 1, 2}"
  by force

lemma infsum_alt_3: 
  "(\<Sum>\<^sub>\<infinity>v::\<nat>. if v = (0::\<nat>) \<or> v = Suc (0::\<nat>) \<or> v = (2::\<nat>) then 1::\<real> else (0::\<real>)) = (3::\<real>)"
  apply (simp add: infsum_constant_finite_states)
  apply (subgoal_tac "{v::\<nat>. v = (0::\<nat>) \<or> v = Suc (0::\<nat>) \<or> v = (2::\<nat>)} = {0, Suc 0, 2}")
  apply simp
  by (simp add: set_eq_iff)

lemma INIT_p_altdef: 
  "INIT_p = prfun_of_rvfun ((\<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e) / 3)\<^sub>e"
  apply (simp add: zero_to_two INIT_p_def)
  apply (simp add: dist_defs)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (pred_auto)
  by (simp_all add: infsum_alt_3)

lemma INIT_p_is_dist: 
  "is_final_distribution (rvfun_of_prfun INIT_p)"
  apply (simp add: INIT_p_def)
  apply (subst rvfun_uniform_dist_inverse)
  apply simp+
  by (simp add: rvfun_uniform_dist_is_dist)

lemma INIT_c_altdef: 
  "INIT_c = prfun_of_rvfun ((\<lbrakk>p\<^sup>> = p\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e) / 3)\<^sub>e"
  apply (simp add: zero_to_two INIT_c_def)
  apply (simp add: dist_defs)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (pred_auto)
  by (simp_all add: infsum_alt_3)

lemma INIT_c_is_dist: 
  "is_final_distribution (rvfun_of_prfun INIT_c)"
  apply (simp add: INIT_c_def)
  apply (subst rvfun_uniform_dist_inverse)
  apply simp+
  by (simp add: rvfun_uniform_dist_is_dist)

lemma record_update_simp:
  assumes "m\<^sub>v (r\<^sub>1::mh_state) = m\<^sub>v r\<^sub>2"
  shows "(r\<^sub>1\<lparr>p\<^sub>v := p\<^sub>v (r\<^sub>2), c\<^sub>v := x\<rparr> = r\<^sub>2) \<longleftrightarrow> c\<^sub>v r\<^sub>2 = x"
  apply (auto)
  apply (metis mh_state.select_convs(2) mh_state.surjective mh_state.update_convs(2))
  by (simp add: assms)

lemma record_update_simp':
  assumes "m\<^sub>v r\<^sub>2 = m\<^sub>v (r\<^sub>1::mh_state)"
  shows "(r\<^sub>1\<lparr>p\<^sub>v := p\<^sub>v (r\<^sub>2), c\<^sub>v := x\<rparr> = r\<^sub>2) \<longleftrightarrow> c\<^sub>v r\<^sub>2 = x"
  apply (auto)
  apply (metis mh_state.select_convs(2) mh_state.surjective mh_state.update_convs(2))
  by (simp add: assms)

lemma record_neq_p_c:
  assumes "p\<^sub>1 \<noteq> p\<^sub>2 \<or> c\<^sub>1 \<noteq> c\<^sub>2"
  assumes "r\<^sub>1\<lparr>p\<^sub>v := p\<^sub>1, c\<^sub>v := c\<^sub>1\<rparr> = r\<^sub>1\<lparr>p\<^sub>v := p\<^sub>2, c\<^sub>v := c\<^sub>2\<rparr>"
  shows "False"
  by (metis mh_state.ext_inject mh_state.surjective mh_state.update_convs(1) mh_state.update_convs(2) assms(1) assms(2))

lemma record_neq_p_c':
  assumes "p\<^sub>1 \<noteq> p\<^sub>2 \<or> c\<^sub>1 \<noteq> c\<^sub>2"
  shows "\<not> r\<^sub>1\<lparr>p\<^sub>v := p\<^sub>1, c\<^sub>v := c\<^sub>1\<rparr> = r\<^sub>2\<lparr>p\<^sub>v := p\<^sub>2, c\<^sub>v := c\<^sub>2\<rparr>"
  using assms record_neq_p_c 
  by (smt (verit, ccfv_SIG) mh_state.cases_scheme mh_state.update_convs(1) mh_state.update_convs(2))

lemma record_neq:
  assumes "p\<^sub>1 \<noteq> p\<^sub>2 \<or> c\<^sub>1 \<noteq> c\<^sub>2 \<or> m\<^sub>1 \<noteq> m\<^sub>2"
  shows "\<not> \<lparr>p\<^sub>v = p\<^sub>1, c\<^sub>v = c\<^sub>1, m\<^sub>v = m\<^sub>1\<rparr> = \<lparr>p\<^sub>v = p\<^sub>2, c\<^sub>v = c\<^sub>2, m\<^sub>v = m\<^sub>2\<rparr>"
  using assms by blast

text \<open> Below we illustrate the simplification of INIT using two ways: 
\begin{itemize}
  \item @{text "INIT_altdef"}: without @{thm "prfun_uniform_dist_left"}. 
        We need to deal with infinite summation and cardinality.
  \item @{text "INIT_altdef'"}: with @{thm "prfun_uniform_dist_left"}.
        We mainly deal with conditional and propositional logic.
\end{itemize}
1) 
\<close>                    
lemma INIT_altdef: "INIT = prfun_of_rvfun ((\<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e) / 9)\<^sub>e"
  apply (simp add: INIT_def INIT_p_def INIT_c_def zero_to_two)
  apply (simp add: pfun_defs)
  apply (simp add: prfun_uniform_dist_altdef')
  apply (expr_simp_1 add: assigns_r_def)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (simp only: fun_eq_iff)
  apply (rule allI)
proof -
  fix x :: "mh_state \<times> mh_state"
  let ?rhs = "(if p\<^sub>v (snd x) = (0::\<nat>) \<or> p\<^sub>v (snd x) = Suc (0::\<nat>) \<or> p\<^sub>v (snd x) = (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if c\<^sub>v (snd x) = (0::\<nat>) \<or> c\<^sub>v (snd x) = Suc (0::\<nat>) \<or> c\<^sub>v (snd x) = (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v (snd x) = m\<^sub>v (fst x) then 1::\<real> else (0::\<real>))"
  let ?rhs_1 = "(if (p\<^sub>v (snd x) = (0::\<nat>) \<or> p\<^sub>v (snd x) = Suc (0::\<nat>) \<or> p\<^sub>v (snd x) = (2::\<nat>)) \<and>
       (c\<^sub>v (snd x) = (0::\<nat>) \<or> c\<^sub>v (snd x) = Suc (0::\<nat>) \<or> c\<^sub>v (snd x) = (2::\<nat>)) \<and>
       (m\<^sub>v (snd x) = m\<^sub>v (fst x)) then 1::\<real> else (0::\<real>))"

  let ?lhs_1 = "\<lambda>v\<^sub>0. (if v\<^sub>0 = fst x\<lparr>p\<^sub>v := 0::\<nat>\<rparr> \<or> v\<^sub>0 = fst x\<lparr>p\<^sub>v := Suc (0::\<nat>)\<rparr> \<or> v\<^sub>0 = fst x\<lparr>p\<^sub>v := 2::\<nat>\<rparr> then 1::\<real>
           else (0::\<real>)) *
     (if snd x = v\<^sub>0\<lparr>c\<^sub>v := 0::\<nat>\<rparr> \<or> snd x = v\<^sub>0\<lparr>c\<^sub>v := Suc (0::\<nat>)\<rparr> \<or> snd x = v\<^sub>0\<lparr>c\<^sub>v := 2::\<nat>\<rparr> then 1::\<real> else (0::\<real>))"
  let ?lhs_2 = "\<lambda>v\<^sub>0. (if (v\<^sub>0 = fst x\<lparr>p\<^sub>v := 0::\<nat>\<rparr> \<or> v\<^sub>0 = fst x\<lparr>p\<^sub>v := Suc (0::\<nat>)\<rparr> \<or> v\<^sub>0 = fst x\<lparr>p\<^sub>v := 2::\<nat>\<rparr>) \<and>
          (snd x = v\<^sub>0\<lparr>c\<^sub>v := 0::\<nat>\<rparr> \<or> snd x = v\<^sub>0\<lparr>c\<^sub>v := Suc (0::\<nat>)\<rparr> \<or> snd x = v\<^sub>0\<lparr>c\<^sub>v := 2::\<nat>\<rparr>) then 1::\<real>
           else (0::\<real>))"

  have fr: "?rhs / (9::\<real>) = ?rhs_1 / (9::\<real>)"
    by simp

  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state. ?lhs_1 v\<^sub>0 / (9::\<real>)) = (\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state. ?lhs_2 v\<^sub>0 / (9::\<real>))"
    by (simp add: infsum_cong)
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state. ?lhs_2 v\<^sub>0 * ( 1 / (9::\<real>)))"
    by auto
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state. ?lhs_2 v\<^sub>0) * ( 1 / (9::\<real>))"
    apply (subst infsum_cmult_left[where c = "1 / (9::real)"])
    apply (simp add: infsum_constant_finite_states_summable)
    by simp

  also have fl: "... = 
    (1 * card {v\<^sub>0. (v\<^sub>0 = fst x\<lparr>p\<^sub>v := 0::\<nat>\<rparr> \<or> v\<^sub>0 = fst x\<lparr>p\<^sub>v := Suc (0::\<nat>)\<rparr> \<or> v\<^sub>0 = fst x\<lparr>p\<^sub>v := 2::\<nat>\<rparr>) \<and>
          (snd x = v\<^sub>0\<lparr>c\<^sub>v := 0::\<nat>\<rparr> \<or> snd x = v\<^sub>0\<lparr>c\<^sub>v := Suc (0::\<nat>)\<rparr> \<or> snd x = v\<^sub>0\<lparr>c\<^sub>v := 2::\<nat>\<rparr>)}
    ) * ( 1 / (9::\<real>))"
    by (simp add: infsum_constant_finite_states)

  have ff1: "card {v\<^sub>0. (v\<^sub>0 = fst x\<lparr>p\<^sub>v := 0::\<nat>\<rparr> \<or> v\<^sub>0 = fst x\<lparr>p\<^sub>v := Suc (0::\<nat>)\<rparr> \<or> v\<^sub>0 = fst x\<lparr>p\<^sub>v := 2::\<nat>\<rparr>) \<and>
        (snd x = v\<^sub>0\<lparr>c\<^sub>v := 0::\<nat>\<rparr> \<or> snd x = v\<^sub>0\<lparr>c\<^sub>v := Suc (0::\<nat>)\<rparr> \<or> snd x = v\<^sub>0\<lparr>c\<^sub>v := 2::\<nat>\<rparr>)}
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
    using record_update_simp apply metis
    apply (erule conjE)+
    apply (smt (z3) mh_state.ext_inject mh_state.surjective mh_state.update_convs(1) mh_state.update_convs(2))
    apply (rule conjI)
    apply (rule impI)
    apply (smt (verit, ccfv_threshold) mh_state.ext_inject mh_state.surjective 
          mh_state.update_convs(1) mh_state.update_convs(2) less_nat_zero_code)
    apply (rule conjI)
    apply (rule impI)
    apply (smt (verit, ccfv_threshold) mh_state.ext_inject mh_state.surjective 
          mh_state.update_convs(1) mh_state.update_convs(2) less_nat_zero_code)
    apply (rule impI)
    by (smt (verit, ccfv_threshold) mh_state.ext_inject mh_state.surjective 
          mh_state.update_convs(1) mh_state.update_convs(2) less_nat_zero_code)

  show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state. ?lhs_1 v\<^sub>0 / (9::\<real>)) = ?rhs / (9::\<real>) "
    apply (simp only: fr fl)
    using ff1 calculation fl by linarith
qed

lemma conditionals_combined:
  assumes "b\<^sub>1 \<and> b\<^sub>2 = False"
  shows "(if b\<^sub>1 then aa else 0::\<real>) + (if b\<^sub>2 then aa else 0) = (if b\<^sub>1 \<or> b\<^sub>2 then aa else 0)"
  by (simp add: assms)

lemma INIT_altdef': "INIT = prfun_of_rvfun ((\<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e) / 9)\<^sub>e"
  apply (simp add: INIT_def INIT_p_def INIT_c_def zero_to_two)
  apply (simp add: prfun_uniform_dist_left)
  apply (simp add: prfun_uniform_dist_altdef')
  apply (expr_simp_1 add: assigns_r_def)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (simp only: fun_eq_iff)
  apply (rule allI)
proof -
  fix x :: "mh_state \<times> mh_state"
  let ?lhs_1b = "snd x = fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 0::\<nat>\<rparr> \<or> 
            snd x = fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr> \<or> 
            snd x = fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 2::\<nat>\<rparr>"
  let ?lhs_2b = "snd x = fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 0::\<nat>\<rparr> \<or>
             snd x = fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := Suc (0::\<nat>)\<rparr> \<or> 
             snd x = fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 2::\<nat>\<rparr>"
  let ?lhs_3b = "snd x = fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 0::\<nat>\<rparr> \<or> 
             snd x = fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr> \<or> 
             snd x = fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 2::\<nat>\<rparr>"
  let ?lhs_1 = "(if ?lhs_1b then 1::\<real> else (0::\<real>))"
  let ?lhs_2 = "(if ?lhs_2b then 1::\<real> else (0::\<real>))"
  let ?lhs_3 = "(if ?lhs_3b then 1::\<real> else (0::\<real>))"
  let ?lhs = "(?lhs_1 / (3::\<real>) + (?lhs_2 / (3::\<real>) + ?lhs_3 / (3::\<real>))) / (3::\<real>)"
  let ?rhs_1b = "p\<^sub>v (snd x) = (0::\<nat>) \<or> p\<^sub>v (snd x) = Suc (0::\<nat>) \<or> p\<^sub>v (snd x) = (2::\<nat>)"
  let ?rhs_2b = "c\<^sub>v (snd x) = (0::\<nat>) \<or> c\<^sub>v (snd x) = Suc (0::\<nat>) \<or> c\<^sub>v (snd x) = (2::\<nat>)"
  let ?rhs_3b = "m\<^sub>v (snd x) = m\<^sub>v (fst x)"
  let ?rhs = "(if ?rhs_1b then 1::\<real> else (0::\<real>)) * (if ?rhs_2b then 1::\<real> else (0::\<real>)) *
       (if ?rhs_3b then 1::\<real> else (0::\<real>)) / (9::\<real>)"
  let ?rhs_1 = "(if ?rhs_1b \<and> ?rhs_2b \<and> ?rhs_3b then 1::\<real> else (0::\<real>)) / (9::\<real>)"
  have rhs_1: "?rhs = ?rhs_1"
    by force
  have lhs_1: "?lhs = (?lhs_1 + ?lhs_2 + ?lhs_3) / (9::\<real>)"
    by force

  let ?lhs_1b' = "fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> 
                  fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> 
                  fst x\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 2::\<nat>\<rparr> = snd x"
  let ?lhs_2b' = "fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> 
                  fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> 
                  fst x\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 2::\<nat>\<rparr> = snd x"
  let ?lhs_3b' = "fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 0::\<nat>\<rparr> = snd x \<or> 
                  fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr> = snd x \<or> 
                  fst x\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 2::\<nat>\<rparr> = snd x"
  have "((if ?lhs_1b' then 1::\<real> else (0::\<real>)) +
        (if ?lhs_2b' then 1::\<real> else (0::\<real>)) + (if ?lhs_3b' then 1::\<real> else (0::\<real>))) 
    =   (if ?lhs_1b' \<or> ?lhs_2b' then 1::\<real> else (0::\<real>)) + (if ?lhs_3b' then 1::\<real> else (0::\<real>))"
    (* auto can be applied here very usefully, but not to lhs_2 "(?lhs_1 + ?lhs_2 + ?lhs_3)" below. Why?
    That's why I use this formula *)
    apply auto
    by (metis mh_state.ext_inject mh_state.surjective mh_state.update_convs(1) mh_state.update_convs(2) One_nat_def one_neq_zero)+
  also have lhs_2': "... =  (if ?lhs_1b' \<or> ?lhs_2b' \<or> ?lhs_3b' then 1::\<real> else (0::\<real>))"
    apply auto
    using record_neq_p_c apply (metis zero_neq_numeral)+
    using record_neq_p_c by (metis n_not_Suc_n numeral_2_eq_2)+

  have lhs_2: "(?lhs_1 + ?lhs_2 + ?lhs_3) = (if ?lhs_1b \<or>?lhs_2b \<or> ?lhs_3b then 1::\<real> else (0::\<real>))"
    using lhs_2' by (smt (verit, best) calculation)

  have lhs_rhs: "(if ?lhs_1b \<or>?lhs_2b \<or> ?lhs_3b then 1::\<real> else (0::\<real>)) 
    = (if (p\<^sub>v (snd x) = (0::\<nat>) \<or> p\<^sub>v (snd x) = Suc (0::\<nat>) \<or> p\<^sub>v (snd x) = (2::\<nat>)) \<and>
       (c\<^sub>v (snd x) = (0::\<nat>) \<or> c\<^sub>v (snd x) = Suc (0::\<nat>) \<or> c\<^sub>v (snd x) = (2::\<nat>)) \<and>
       (m\<^sub>v (snd x) = m\<^sub>v (fst x)) then 1::\<real> else (0::\<real>))"
    apply (rule if_cong)
    apply (rule iffI)
    apply (rule conjI)+
    apply (smt (z3) mh_state.ext_inject mh_state.surjective mh_state.update_convs(1) mh_state.update_convs(2))
    apply (smt (z3) mh_state.ext_inject mh_state.surjective mh_state.update_convs(1) mh_state.update_convs(2))
    apply (metis record_update_simp)
    by simp+
  show "?lhs = ?rhs "
    apply (simp only: lhs_1 rhs_1)
    using calculation lhs_2 lhs_rhs by presburger
qed

lemma INIT_is_dist: 
  "is_final_distribution (rvfun_of_prfun INIT)"
  apply (simp add: INIT_def)
  apply (simp add: pseqcomp_def)
  apply (subst rvfun_seqcomp_inverse)
  apply (simp add: INIT_p_is_dist)
  using INIT_c_is_dist apply (simp add: ureal_is_prob)
  using INIT_c_is_dist INIT_p_is_dist rvfun_seqcomp_is_dist by blast

subsection \<open> @{text "MHA_NC"} \<close>
lemma suc_card_minus:
  assumes "x > 0"
  shows "(Suc (card A) = x) \<longleftrightarrow> (card A = x - 1)"
  using assms by fastforce

lemma nine_minus_nine_zero: 
  "(9::\<nat>) - (1::\<nat>) - (1::\<nat>) - (1::\<nat>) - (1::\<nat>) - (1::\<nat>) - (1::\<nat>) - (1::\<nat>) - (1::\<nat>) - (1::\<nat>) = 0"
  by simp
  
lemma card_states_9: 
"card {s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 0::\<nat>\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 2::\<nat>\<rparr>,
  s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 0::\<nat>\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := Suc (0::\<nat>)\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 2::\<nat>\<rparr>,
  s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 0::\<nat>\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 2::\<nat>\<rparr>
} = 9"
  apply (subst card_Suc_Diff1 [where x = "s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 0::\<nat>\<rparr>", symmetric])
  apply (meson finite.simps finite_Diff)
  apply (simp)
  apply (simp only: suc_card_minus)
  apply (subst card_Suc_Diff1 [where x = "s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr>", symmetric])
  apply (meson finite.simps finite_Diff)
  apply (simp)
  apply (metis One_nat_def one_neq_zero record_neq_p_c)
  apply (simp only: suc_card_minus)
  apply (subst card_Suc_Diff1 [where x = "s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 2\<rparr>", symmetric])
  apply (meson finite.simps finite_Diff)
  apply (simp)
  apply (metis One_nat_def Suc_1 n_not_Suc_n nat.distinct(1) record_neq_p_c)
  apply (simp only: suc_card_minus)
  apply (subst card_Suc_Diff1 [where x = "s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 0::\<nat>\<rparr>", symmetric])
  apply (meson finite.simps finite_Diff)
  apply (simp)
  apply (metis n_not_Suc_n record_neq_p_c)
  apply (simp only: suc_card_minus)
  apply (subst card_Suc_Diff1 [where x = "s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := Suc (0::\<nat>)\<rparr>", symmetric])
  apply (meson finite.simps finite_Diff)
  apply (simp)
  apply (metis One_nat_def one_neq_zero record_neq_p_c)
  apply (simp only: suc_card_minus)
  apply (subst card_Suc_Diff1 [where x = "s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 2\<rparr>", symmetric])
  apply (meson finite.simps finite_Diff)
  apply (simp)
  apply (metis One_nat_def Suc_1 n_not_Suc_n nat.distinct(1) record_neq_p_c)
  apply (simp only: suc_card_minus)
  apply (subst card_Suc_Diff1 [where x = "s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 0::\<nat>\<rparr>", symmetric])
  apply (meson finite.simps finite_Diff)
  apply (simp)
  apply (metis One_nat_def Suc_1 n_not_Suc_n nat.distinct(1) record_neq_p_c)
  apply (simp only: suc_card_minus)
  apply (subst card_Suc_Diff1 [where x = "s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr>", symmetric])
  apply (meson finite.simps finite_Diff)
  apply (simp)
  using record_neq_p_c apply fastforce
  apply (simp only: suc_card_minus)
  apply (subst card_Suc_Diff1 [where x = "s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 2\<rparr>", symmetric])
  apply (meson finite.simps finite_Diff)
  apply (simp)
  apply (metis One_nat_def Suc_1 n_not_Suc_n nat.distinct(1) record_neq_p_c)
  apply (simp only: suc_card_minus)
  apply (subst nine_minus_nine_zero)
  by (smt (z3) Diff_cancel Diff_insert card.empty insert_commute)

lemma set_states: "\<forall>s\<^sub>1::mh_state. {s::mh_state. get\<^bsub>p\<^esub> s \<le> (2::\<nat>) \<and> get\<^bsub>c\<^esub> s \<le> (2::\<nat>) \<and> get\<^bsub>m\<^esub> s = get\<^bsub>m\<^esub> s\<^sub>1}
    = {s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 0::\<nat>\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 2::\<nat>\<rparr>,
          s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 0::\<nat>\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := Suc (0::\<nat>)\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 2::\<nat>\<rparr>,
          s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 0::\<nat>\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 2::\<nat>\<rparr>}"
  apply (simp add: lens_defs)
  apply (simp add: set_eq_iff)
  apply (rule allI)+
  apply (rule iffI)
  apply (smt (z3) mh_state.surjective mh_state.update_convs(1) mh_state.update_convs(2) 
        One_nat_def Suc_1 bot_nat_0.extremum_unique c_def le_Suc_eq lens.simps(1) m_def old.unit.exhaust p_def)
  by (smt (verit, best) mh_state.ext_inject mh_state.surjective mh_state.update_convs(1) 
        mh_state.update_convs(2) One_nat_def bot_nat_0.extremum c_def lens.simps(1) less_one 
        linorder_not_le m_def order_le_less p_def zero_neq_numeral)
(*
lemma set_states': "\<forall>s\<^sub>1::mh_state. {s::mh_state. p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v s\<^sub>1}
    = {s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 0::\<nat>\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := 0::\<nat>, c\<^sub>v := 2::\<nat>\<rparr>,
          s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 0::\<nat>\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := Suc (0::\<nat>)\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := Suc (0::\<nat>), c\<^sub>v := 2::\<nat>\<rparr>,
          s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 0::\<nat>\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := Suc (0::\<nat>)\<rparr>, s\<^sub>1\<lparr>p\<^sub>v := 2::\<nat>, c\<^sub>v := 2::\<nat>\<rparr>}"
  by (smt (verit) Collect_cong c_def lens.simps(1) m_def p_def set_states)
*)


lemma ereal2real_1_2: "rvfun_of_prfun [\<lambda>x::mh_state \<times> mh_state.
    ereal2ureal ((1::ereal) / ereal (2::\<real>))]\<^sub>e = (1/2)\<^sub>e"
  apply (simp add: rvfun_of_prfun_simp)
  apply (simp add: ureal_defs)
  using SEXP_def ereal_1_div ereal_less_eq(6) mult_cancel_left1 real2uereal_min_inverse' zero_ereal_def by auto

lemma MHA_altdef: "MHA = 
    prfun_of_rvfun (
      (\<lbrakk>c\<^sup>< = p\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> m := (c + 1) mod 3 \<rbrakk>\<^sub>\<I>\<^sub>e / 2) + 
      (\<lbrakk>c\<^sup>< = p\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> m := (c + 2) mod 3 \<rbrakk>\<^sub>\<I>\<^sub>e / 2) + 
      (\<lbrakk>c\<^sup>< \<noteq> p\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> m := 3 - c - p \<rbrakk>\<^sub>\<I>\<^sub>e)
    )\<^sub>e"
proof -
  show ?thesis
  apply (simp only: dwta_defs)
  apply (simp add: prfun_seqcomp_right_unit)
  apply (simp add: prfun_pcond_altdef)
  apply (simp only: pchoice_def passigns_def)
  apply (simp only: rvfun_assignment_inverse)
  apply (simp only: ereal2real_1_2)
  apply (subst rvfun_pchoice_inverse_c'')
  using rvfun_assignment_is_prob apply blast+
  apply (simp)
  apply (simp add: expr_defs rel lens_defs prod.case_eq_if alpha_splits)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  by fastforce
qed

lemma MHA_is_dist: "is_final_distribution (rvfun_of_prfun MHA)"
proof -
  have f0: "is_final_distribution (rvfun_of_prfun MHA_1)"
    apply (simp add: pchoice_def)
    apply (subst rvfun_pchoice_inverse)
    apply (simp add: ureal_is_prob)+
    apply (simp only: ereal2real_1_2)
    apply (rule rvfun_pchoice_is_dist_c')
    by (simp add: passigns_def rvfun_assignment_inverse rvfun_assignment_is_dist)+
  show ?thesis
    apply (simp only: MHA_def)
    apply (simp only: pcond_def)
    apply (subst rvfun_pcond_inverse)
    using ureal_is_prob apply blast+
    apply (subst rvfun_pcond_is_dist')
    using f0 apply meson
    apply (simp add: passigns_def rvfun_assignment_inverse rvfun_assignment_is_dist)
    apply (pred_auto)
    by simp
qed

lemma MHA_NC_MHA_eq: "MHA_NC = MHA"
  apply (simp only: MHA_NC_def)
  by (simp add: prfun_seqcomp_right_unit)

subsection \<open> @{text "IMHA_NC"}\<close>
definition IMHA_NC_altdef :: "mh_state \<times> mh_state \<Rightarrow> \<real>" where 
"IMHA_NC_altdef = (
      (\<lbrakk>c\<^sup>> = p\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> m\<^sup>> = (c\<^sup>> + 1) mod 3 \<rbrakk>\<^sub>\<I>\<^sub>e / 18) + 
      (\<lbrakk>c\<^sup>> = p\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> m\<^sup>> = (c\<^sup>> + 2) mod 3 \<rbrakk>\<^sub>\<I>\<^sub>e / 18) + 
      (\<lbrakk>c\<^sup>> \<noteq> p\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> m\<^sup>> = 3 - c\<^sup>> - p\<^sup>> \<rbrakk>\<^sub>\<I>\<^sub>e / 9)
    )\<^sub>e"

lemma IMHA_NC_altdef_dist: "is_final_distribution IMHA_NC_altdef"
  apply (simp add: IMHA_NC_altdef_def)
  apply (simp add: dist_defs expr_defs lens_defs)
proof -
  let ?lhs_1 = "\<lambda>s::mh_state. (if c\<^sub>v s = p\<^sub>v s then 1::\<real> else (0::\<real>)) * (if p\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * 
        (if c\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>) then 1::\<real> else (0::\<real>))"
  let ?lhs_2 = "\<lambda>s::mh_state. (if c\<^sub>v s = p\<^sub>v s then 1::\<real> else (0::\<real>)) * (if p\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * 
        (if c\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>) then 1::\<real> else (0::\<real>))"
  let ?lhs_3 = "\<lambda>s::mh_state. (if \<not> c\<^sub>v s = p\<^sub>v s then 1::\<real> else (0::\<real>)) * (if p\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * 
        (if c\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v s = (3::\<nat>) - (c\<^sub>v s + p\<^sub>v s) then 1::\<real> else (0::\<real>))"
  let ?lhs = "\<lambda>s::mh_state. ?lhs_1 s / (18::\<real>) + ?lhs_2 s / (18::\<real>) + ?lhs_3 s / (9::\<real>) "
  
  have states_1_eq:"{s::mh_state. ((c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>)) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>)}
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>,\<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (2::\<nat>)\<rparr>, 
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = 0::\<nat>\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
    apply (smt (z3) mh_state.surjective Orderings.order_eq_iff Suc_eq_numeral add.assoc 
        cong_exp_iff_simps(2) diff_add_zero diff_is_0_eq le_SucE mod_Suc mod_self numeral_1_eq_Suc_0 
        numeral_2_eq_2 numeral_3_eq_3 old.unit.exhaust one_eq_numeral_iff plus_1_eq_Suc)
    by force

  have states_2_eq:"{s::mh_state. ((c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>)) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>)}
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (0::\<nat>)\<rparr>, 
       \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
    apply (smt (verit, best) mh_state.surjective lessI less_2_cases mod_Suc mod_less numeral_2_eq_2 
        numeral_3_eq_3 old.unit.exhaust order_le_less) 
    by force

  have states_3_eq: "{s::mh_state. ((\<not> c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>)) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> m\<^sub>v s = (3::\<nat>) - (c\<^sub>v s + p\<^sub>v s)}
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = (2::\<nat>), m\<^sub>v = Suc (0::\<nat>)\<rparr>,
       \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = (0::\<nat>), m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = (2::\<nat>), m\<^sub>v = (0::\<nat>)\<rparr>, 
       \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (0::\<nat>)\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
    apply (smt (verit, ccfv_SIG) mh_state.surjective One_nat_def diff_add_inverse diff_diff_eq 
        less_2_cases numeral_2_eq_2 numeral_3_eq_3 old.unit.exhaust order_le_less plus_1_eq_Suc)
    by force

  have lhs_1_summable: "?lhs_1 summable_on UNIV"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states_summable)
    using states_1_eq by (simp_all)

  have lhs_2_summable: "?lhs_2 summable_on UNIV"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states_summable)
    using states_2_eq by (simp_all)

  have lhs_3_summable: "?lhs_3 summable_on UNIV"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states_summable)
    using states_3_eq by (simp_all)

  have lhs_1_infsum: "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs_1 s) = 3"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states)
    using states_1_eq by (simp_all)

  have lhs_2_infsum: "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs_2 s) = 3"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states)
    using states_2_eq by (simp_all)

  have lhs_3_infsum: "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs_3 s) = 6"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states)
    using states_3_eq by (simp_all)

  show "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs s) = (1::\<real>)"
    apply (subst infsum_add)
    apply (subst summable_on_add)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_1_summable)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_2_summable)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_3_summable)
    apply (subst infsum_add)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_1_summable)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_2_summable)
    apply (subst infsum_cdiv_left)
    apply (simp_all add: lhs_1_summable)
    apply (subst infsum_cdiv_left)
    apply (simp_all add: lhs_2_summable)
    apply (subst infsum_cdiv_left)
    apply (simp_all add: lhs_3_summable)
    using lhs_1_infsum lhs_2_infsum lhs_3_infsum by (simp)
qed

lemma IMHA_NC_altdef: "IMHA_NC = prfun_of_rvfun IMHA_NC_altdef"
  apply (simp add: IMHA_NC_def zero_to_two IMHA_NC_altdef_def)
  apply (simp add: INIT_altdef MHA_NC_MHA_eq MHA_altdef)
  apply (simp add: pfun_defs)
  apply (subst rvfun_inverse)
  apply (simp add: expr_defs dist_defs)
  apply (subst rvfun_inverse)
  apply (simp add: expr_defs dist_defs)
  apply (expr_simp_1 add: assigns_r_def)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (subst fun_eq_iff, rule allI)
proof -
  fix x :: "mh_state \<times> mh_state"
  let ?lhs_p = "\<lambda>v\<^sub>0. (if p\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>))"
  let ?lhs_c = "\<lambda>v\<^sub>0. (if c\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>))"
  let ?lhs_m = "\<lambda>v\<^sub>0. (if m\<^sub>v v\<^sub>0 = m\<^sub>v (fst x) then 1::\<real> else (0::\<real>))"
  let ?lhs_c_p = "\<lambda>v\<^sub>0. (if c\<^sub>v v\<^sub>0 = p\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>))"
  let ?lhs_c_n_p = "\<lambda>v\<^sub>0. (if \<not> c\<^sub>v v\<^sub>0 = p\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>))"
  let ?m_1_mod = "\<lambda>v\<^sub>0. (if snd x = v\<^sub>0\<lparr>m\<^sub>v := Suc (c\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> then 1::\<real> else (0::\<real>))"
  let ?m_2_mod = "\<lambda>v\<^sub>0. (if snd x = v\<^sub>0\<lparr>m\<^sub>v := Suc (Suc (c\<^sub>v v\<^sub>0)) mod (3::\<nat>)\<rparr> then 1::\<real> else (0::\<real>))"
  let ?m_3_c_p = "\<lambda>v\<^sub>0. (if snd x = v\<^sub>0\<lparr>m\<^sub>v := (3::\<nat>) - (c\<^sub>v v\<^sub>0 + p\<^sub>v v\<^sub>0)\<rparr> then 1::\<real> else (0::\<real>))"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state.
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
  have lhs_1_set_simp: "{s::mh_state. p\<^sub>v s \<le> (2::\<nat>) \<and>
    c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v (fst x) \<and> c\<^sub>v s = p\<^sub>v s}
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = m\<^sub>v (fst x)\<rparr>,\<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>, 
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = m\<^sub>v (fst x)\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
    apply (metis (mono_tags, opaque_lifting) mh_state.surjective bot_nat_0.extremum le_SucE 
          le_antisym numeral_2_eq_2 old.unit.exhaust)
    by fastforce
  have lhs_1_set_A_finite: "finite {s::mh_state. p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v (fst x) \<and> c\<^sub>v s = p\<^sub>v s}"
    by (simp add: lhs_1_set_simp)

  have lhs_1_summable: "(\<lambda>v\<^sub>0. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_1_mod v\<^sub>0) summable_on UNIV"
    apply (simp add: lhs_1_f0)
    apply (rule infsum_constant_finite_states_summable)
    apply (rule rev_finite_subset[where B=
          "{s::mh_state. p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v (fst x) \<and> c\<^sub>v s = p\<^sub>v s}"])
    apply (simp add: lhs_1_set_A_finite)
    by blast

  have lhs_1_infsum: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_1_mod v\<^sub>0)
    = ?rhs_1_1"
    apply (simp only: lhs_1_f0)
    apply (subst infsum_constant_finite_states)
    apply (rule rev_finite_subset[where B=
          "{s::mh_state. p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v (fst x) \<and> c\<^sub>v s = p\<^sub>v s}"])
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
    apply (metis mh_state.select_convs(1) mod_Suc_le_divisor numeral_2_eq_2 numeral_3_eq_3)
    apply (rule conjI)
    apply (metis mh_state.select_convs(2) mod_Suc_le_divisor numeral_2_eq_2 numeral_3_eq_3)
    apply (rule conjI)
    apply (metis mh_state.select_convs(3))
    apply (rule conjI)
    apply (metis mh_state.select_convs(1) mh_state.select_convs(2))
    defer
    apply (metis mh_state.surjective mh_state.update_convs(3))
    apply (smt (verit, best) Collect_empty_eq mh_state.select_convs(1) mh_state.select_convs(2) 
        mh_state.select_convs(3) mh_state.surjective mh_state.update_convs(3) card_eq_0_iff 
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
      by (metis mh_state.select_convs(2))
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
          "{s::mh_state. p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v (fst x) \<and> c\<^sub>v s = p\<^sub>v s}"])
    apply (simp add: lhs_1_set_A_finite)
    by blast

  have lhs_2_infsum: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_2_mod v\<^sub>0)
    = ?rhs_1_2"
    apply (simp only: lhs_2_f0)
    apply (subst infsum_constant_finite_states)
    apply (rule rev_finite_subset[where B=
          "{s::mh_state. p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v (fst x) \<and> c\<^sub>v s = p\<^sub>v s}"])
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
    apply (metis mh_state.select_convs(1) mod_Suc_le_divisor numeral_2_eq_2 numeral_3_eq_3)
    apply (rule conjI)
    apply (metis mh_state.select_convs(2) mod_Suc_le_divisor numeral_2_eq_2 numeral_3_eq_3)
    apply (rule conjI)
    apply (metis mh_state.select_convs(3))
    apply (rule conjI)
    apply (metis mh_state.select_convs(1) mh_state.select_convs(2))
    defer
    apply (metis mh_state.surjective mh_state.update_convs(3))
    apply (smt (verit, best) Collect_empty_eq mh_state.select_convs(1) mh_state.select_convs(2) 
        mh_state.select_convs(3) mh_state.surjective mh_state.update_convs(3) card_eq_0_iff 
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
      by (metis mh_state.select_convs(2) mh_state.unfold_congs(3) mod_Suc_eq)
    also have "... = \<lparr>p\<^sub>v = Suc (m\<^sub>v (snd x)) mod (3::\<nat>), c\<^sub>v = Suc (m\<^sub>v (snd x)) mod (3::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>
        \<lparr>m\<^sub>v := (m\<^sub>v (snd x))\<rparr>"
      by (simp add: a1 mod_Suc_eq)
    also have "... = \<lparr>p\<^sub>v = c\<^sub>v (snd x), c\<^sub>v = c\<^sub>v (snd x), m\<^sub>v = (m\<^sub>v (snd x))\<rparr>"
      by (smt (z3) mh_state.update_convs(3) Suc_mod_eq_add3_mod_numeral a1 a3 a4 
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
  have lhs_3_set_simp: "{s::mh_state. p\<^sub>v s \<le> (2::\<nat>) \<and>
    c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v (fst x) \<and>  \<not>c\<^sub>v s = p\<^sub>v s}
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 1::\<nat>, m\<^sub>v = m\<^sub>v (fst x)\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = m\<^sub>v (fst x)\<rparr>, 
       \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = (0::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = (2::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>, 
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = m\<^sub>v (fst x)\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = m\<^sub>v (fst x)\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
    apply (metis (mono_tags, opaque_lifting) mh_state.surjective bot_nat_0.extremum le_SucE 
          le_antisym numeral_2_eq_2 old.unit.exhaust)
    by fastforce
  have lhs_3_set_A_finite: "finite {s::mh_state. p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v (fst x) \<and> \<not>c\<^sub>v s = p\<^sub>v s}"
    by (simp add: lhs_3_set_simp)
  have lhs_3_summable: "(\<lambda>v\<^sub>0. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_n_p v\<^sub>0 * ?m_3_c_p v\<^sub>0) summable_on UNIV"
    apply (simp add: lhs_3_f0)
    apply (rule infsum_constant_finite_states_summable)
    apply (rule rev_finite_subset[where B=
          "{s::mh_state. p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v (fst x) \<and> \<not>c\<^sub>v s = p\<^sub>v s}"])
    apply (simp add: lhs_3_set_A_finite)
    by blast

  have lhs_3_infsum: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_n_p v\<^sub>0 * ?m_3_c_p v\<^sub>0)
    = ?rhs_1_3"
    apply (simp only: lhs_3_f0)
    apply (subst infsum_constant_finite_states)
    apply (rule rev_finite_subset[where B=
          "{s::mh_state. p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v (fst x) \<and> \<not>c\<^sub>v s = p\<^sub>v s}"])
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
    apply (metis mh_state.surjective mh_state.update_convs(3))
    apply (smt (verit, best) Collect_empty_eq mh_state.select_convs(1) mh_state.select_convs(2) 
        mh_state.select_convs(3) mh_state.surjective mh_state.update_convs(3) card_eq_0_iff 
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
      using mh_state.update_convs(3) a1 a2 a3 a4 add.commute add.right_neutral by fastforce
    have lhs_3: "... = snd x"
      by (simp add: a4)
    show "\<lparr>p\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - c\<^sub>v (snd x), c\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - p\<^sub>v (snd x), m\<^sub>v = m\<^sub>v (fst x)\<rparr>
      \<lparr>m\<^sub>v := (3::\<nat>) - (c\<^sub>v \<lparr>p\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - c\<^sub>v (snd x), c\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - p\<^sub>v (snd x), m\<^sub>v = m\<^sub>v (fst x)\<rparr> +
        p\<^sub>v \<lparr>p\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - c\<^sub>v (snd x), c\<^sub>v = (3::\<nat>) - m\<^sub>v (snd x) - p\<^sub>v (snd x), m\<^sub>v = m\<^sub>v (fst x)\<rparr>)\<rparr> = snd x"
      using lhs_0 lhs_1 lhs_2 lhs_3 by presburger
  qed

  have lhs_1: "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state.
          ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 *
          (?lhs_c_p v\<^sub>0 * ?m_1_mod v\<^sub>0 / (18::\<real>) +
           ?lhs_c_p v\<^sub>0 * ?m_2_mod v\<^sub>0 / (18::\<real>) +
           ?lhs_c_n_p v\<^sub>0 * ?m_3_c_p v\<^sub>0 / (9::\<real>)))"
    apply (rule infsum_cong)
    by (simp add: add_divide_distrib)
  also have lhs_2: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state.
          ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_1_mod v\<^sub>0 / (18::\<real>) +
          ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_2_mod v\<^sub>0 / (18::\<real>) +
          ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_n_p v\<^sub>0 * ?m_3_c_p v\<^sub>0 / (9::\<real>))"
    apply (rule infsum_cong)
    by simp
  also have lhs_3: "... = 
    (\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_1_mod v\<^sub>0 / (18::\<real>)) +
    (\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_2_mod v\<^sub>0 / (18::\<real>)) +
    (\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_n_p v\<^sub>0 * ?m_3_c_p v\<^sub>0 / (9::\<real>))"
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
    (\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_1_mod v\<^sub>0) / (18::\<real>) +
    (\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_p v\<^sub>0 * ?m_2_mod v\<^sub>0) / (18::\<real>) +
    (\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state. ?lhs_p v\<^sub>0 * ?lhs_c v\<^sub>0 * ?lhs_m v\<^sub>0 * ?lhs_c_n_p v\<^sub>0 * ?m_3_c_p v\<^sub>0) / (9::\<real>)"
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

lemma IMHA_NC_altdef_states_1_eq:
  "{s::mh_state. ((c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>)) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>)}
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>,\<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (2::\<nat>)\<rparr>, 
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = 0::\<nat>\<rparr>}"
  apply (simp add: set_eq_iff)
  apply (rule allI)
  apply (rule iffI)
  apply (smt (z3) mh_state.surjective Orderings.order_eq_iff Suc_eq_numeral add.assoc 
      cong_exp_iff_simps(2) diff_add_zero diff_is_0_eq le_SucE mod_Suc mod_self numeral_1_eq_Suc_0 
      numeral_2_eq_2 numeral_3_eq_3 old.unit.exhaust one_eq_numeral_iff plus_1_eq_Suc)
  by force

lemma IMHA_NC_altdef_states_2_eq:
  "{s::mh_state. ((c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>)) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>)}
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (0::\<nat>)\<rparr>, 
       \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>}"
  apply (simp add: set_eq_iff)
  apply (rule allI)
  apply (rule iffI)
  apply (smt (verit, best) mh_state.surjective lessI less_2_cases mod_Suc mod_less numeral_2_eq_2 
      numeral_3_eq_3 old.unit.exhaust order_le_less) 
  by force

lemma IMHA_NC_altdef_states_3_eq: 
  "{s::mh_state. ((\<not> c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>)) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> m\<^sub>v s = (3::\<nat>) - (c\<^sub>v s + p\<^sub>v s)}
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = (2::\<nat>), m\<^sub>v = Suc (0::\<nat>)\<rparr>,
       \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = (0::\<nat>), m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = (2::\<nat>), m\<^sub>v = (0::\<nat>)\<rparr>, 
       \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (0::\<nat>)\<rparr>}"
  apply (simp add: set_eq_iff)
  apply (rule allI)
  apply (rule iffI)
  apply (smt (verit, ccfv_SIG) mh_state.surjective One_nat_def diff_add_inverse diff_diff_eq 
      less_2_cases numeral_2_eq_2 numeral_3_eq_3 old.unit.exhaust order_le_less plus_1_eq_Suc)
  by force

lemma IMHA__NC_win: "rvfun_of_prfun (IMHA_NC) ; \<lbrakk>c\<^sup>< = p\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e = (1/3)\<^sub>e"
  apply (simp add: IMHA_NC_altdef)
  apply (subst rvfun_inverse)
  using IMHA_NC_altdef_dist apply (simp add: is_dist_def is_final_prob_prob)
  apply (simp add: IMHA_NC_altdef_def)
  apply (expr_auto)
  apply (simp add: ring_distribs(2))
proof -
  let ?lhs_1 = "\<lambda>s::mh_state. (if c\<^sub>v s = p\<^sub>v s then 1::\<real> else (0::\<real>)) * (if p\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * 
        (if c\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>) then 1::\<real> else (0::\<real>)) * 
       (if c\<^sub>v s = p\<^sub>v s then 1::\<real> else (0::\<real>))"
  let ?lhs_2 = "\<lambda>s::mh_state. (if c\<^sub>v s = p\<^sub>v s then 1::\<real> else (0::\<real>)) * (if p\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * 
       (if c\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>) then 1::\<real> else (0::\<real>)) * 
       (if c\<^sub>v s = p\<^sub>v s then 1::\<real> else (0::\<real>))"
  let ?lhs_3 = "\<lambda>s::mh_state. (if \<not> c\<^sub>v s = p\<^sub>v s then 1::\<real> else (0::\<real>)) * (if p\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * 
        (if c\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v s = (3::\<nat>) - (c\<^sub>v s + p\<^sub>v s) then 1::\<real> else (0::\<real>)) * 
        (if c\<^sub>v s = p\<^sub>v s then 1::\<real> else (0::\<real>))"
  let ?lhs = "\<lambda>s::mh_state. ?lhs_1 s / (18::\<real>) + ?lhs_2 s / (18::\<real>) + ?lhs_3 s / (9::\<real>) "

  let ?lhs_1' = "\<lambda>s::mh_state. (if c\<^sub>v s = p\<^sub>v s then 1::\<real> else (0::\<real>)) * (if p\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * 
        (if c\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>) then 1::\<real> else (0::\<real>))"

  let ?lhs_2' = "\<lambda>s::mh_state. (if c\<^sub>v s = p\<^sub>v s then 1::\<real> else (0::\<real>)) * (if p\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * 
       (if c\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>) then 1::\<real> else (0::\<real>))"

  have lhs_1_eq: "?lhs_1 = ?lhs_1'"
    by auto
  have lhs_2_eq: "?lhs_2 = ?lhs_2'"
    by auto

  have lhs_3_zero: "?lhs_3 = (\<lambda>s::mh_state. 0)"
    by auto

  have lhs_1_summable: "?lhs_1 summable_on UNIV"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states_summable)
    using IMHA_NC_altdef_states_1_eq apply (metis (mono_tags, lifting) Collect_mono finite.emptyI 
        finite.insertI finite_subset)
    by simp

  have lhs_2_summable: "?lhs_2 summable_on UNIV"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states_summable)
    using IMHA_NC_altdef_states_2_eq apply (metis (mono_tags, lifting) Collect_mono finite.emptyI 
        finite.insertI finite_subset)
    by simp

  have lhs_3_summable: "?lhs_3 summable_on UNIV"
    by (meson lhs_3_zero summable_on_0)

  have lhs_1_infsum: "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs_1 s) = 3"
    apply (simp add: lhs_1_eq)
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states)
    using IMHA_NC_altdef_states_1_eq apply (metis (no_types, lifting) finite.emptyI finite.insertI)
    apply (subst IMHA_NC_altdef_states_1_eq)
    by auto

  have lhs_2_infsum: "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs_2 s) = 3"
    apply (simp add: lhs_2_eq)
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states)
    using IMHA_NC_altdef_states_2_eq apply (metis (no_types, lifting) finite.emptyI finite.insertI)
    apply (subst IMHA_NC_altdef_states_2_eq)
    by auto

  have lhs_3_infsum: "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs_3 s) = 0"
    by (simp add: lhs_3_zero)

  show "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs s) * 3 = 1"
    apply (subst infsum_add)
    apply (subst summable_on_add)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_1_summable)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_2_summable)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_3_summable)
    apply (subst infsum_add)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_1_summable)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_2_summable)
    apply (subst infsum_cdiv_left)
    apply (simp_all add: lhs_1_summable)
    apply (subst infsum_cdiv_left)
    apply (simp_all add: lhs_2_summable)
    apply (subst infsum_cdiv_left)
    apply (simp_all add: lhs_3_summable)
    using lhs_1_infsum lhs_2_infsum lhs_3_infsum by (simp)
qed

subsubsection \<open> Average values \<close>
text \<open>Average value of @{term "p"} after the execution of @{term "IMHA_C"}, a No Change Strategy. \<close>
lemma IMHA_NC_average_p: "rvfun_of_prfun IMHA_NC ; ($p\<^sup><)\<^sub>e = (1)\<^sub>e"
  apply (simp add: IMHA_NC_altdef)
  apply (subst rvfun_inverse)
  using IMHA_NC_altdef_dist 
  apply (simp add: is_final_distribution_prob is_final_prob_prob)
  apply (simp add: IMHA_NC_altdef_def)
  apply (expr_auto)
  apply (simp add: ring_distribs(2))
  apply (subst conditional_conds_conj)+
  apply (subst times_divide_eq_right[symmetric])+
  apply (subst conditional_cmult_1)+
  apply (subst infsum_add)
  apply (rule summable_on_add)
  apply (subst infsum_cond_finite_states_summable)
  apply (subst IMHA_NC_altdef_states_1_eq)
  apply blast+
  apply (subst infsum_cond_finite_states_summable)
  apply (subst IMHA_NC_altdef_states_2_eq)
  apply blast+
  apply (subst infsum_cond_finite_states_summable)
  apply (subst IMHA_NC_altdef_states_3_eq)
  apply blast+
  apply (subst infsum_add)
  apply (subst infsum_cond_finite_states_summable)
  apply (subst IMHA_NC_altdef_states_1_eq)
  apply blast+
  apply (subst infsum_cond_finite_states_summable)
  apply (subst IMHA_NC_altdef_states_2_eq)
  apply blast+
  apply (subst infsum_cond_finite_states)
  apply (subst IMHA_NC_altdef_states_1_eq)
  apply blast+
  apply (subst infsum_cond_finite_states)
  apply (subst IMHA_NC_altdef_states_2_eq)
  apply blast+
  apply (subst infsum_cond_finite_states)
  apply (subst IMHA_NC_altdef_states_3_eq)
  apply blast+
  apply (subst IMHA_NC_altdef_states_1_eq)
  apply (subst IMHA_NC_altdef_states_2_eq)
  apply (subst IMHA_NC_altdef_states_3_eq)
  apply (subst sum_divide_distrib[symmetric])+
  by (simp)

subsection \<open> @{text "IMHA_C"}\<close>
definition IMHA_C_altdef :: "mh_state \<times> mh_state \<Rightarrow> \<real>" where 
"IMHA_C_altdef = (
      (\<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = 3 - p\<^sup>> - m\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> m\<^sup>> = (p\<^sup>> + 1) mod 3 \<rbrakk>\<^sub>\<I>\<^sub>e / 18) + 
      (\<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> = 3 - p\<^sup>> - m\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> m\<^sup>> = (p\<^sup>> + 2) mod 3 \<rbrakk>\<^sub>\<I>\<^sub>e / 18) + 
      (\<lbrakk>3 - m\<^sup>> - p\<^sup>> \<noteq> p\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>3 - m\<^sup>> - p\<^sup>> \<le> 2\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>3 - m\<^sup>> \<ge> p\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> c\<^sup>> = p\<^sup>> \<rbrakk>\<^sub>\<I>\<^sub>e / 9)
    )\<^sub>e"
(* It is necessary to add an extra "\<lbrakk>3 - m\<^sup>> \<ge> p\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e" because a - b is always larger or than 0 for 
natural numbers in Isabelle/HOL. (a - b + b) is not necessary to be equal to a, but (max a b) *)
(* (\<lbrakk>3 - m\<^sup>> - p\<^sup>> \<noteq> p\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>3 - m\<^sup>> - p\<^sup>> \<le> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> c\<^sup>> = p\<^sup>> \<rbrakk>\<^sub>\<I>\<^sub>e / 9)*)

lemma IMHA_C_altdef_dist: "is_final_distribution IMHA_C_altdef"
proof -
  let ?lhs_1 = "\<lambda>(s\<^sub>1::mh_state) s::mh_state. 
    (if get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
          (if get\<^bsub>c\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) =
              (3::\<nat>) - (get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) + get\<^bsub>m\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)))
           then 1::\<real> else (0::\<real>)) *
          (if get\<^bsub>m\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) = Suc (get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s))) mod (3::\<nat>) then 1::\<real>
           else (0::\<real>))"
  let ?lhs_2 = "\<lambda>(s\<^sub>1::mh_state) s::mh_state. 
          (if get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
          (if get\<^bsub>c\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) =
              (3::\<nat>) - (get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) + get\<^bsub>m\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)))
           then 1::\<real> else (0::\<real>)) *
          (if get\<^bsub>m\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) = Suc (Suc (get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)))) mod (3::\<nat>) then 1::\<real>
           else (0::\<real>))"
  let ?lhs_3 = " \<lambda>(s\<^sub>1::mh_state) s::mh_state.
              (if \<not> (3::\<nat>) - (get\<^bsub>m\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) + get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s))) =
                 get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) then 1::\<real> else (0::\<real>)) *
          (if get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
          (if (3::\<nat>) - (get\<^bsub>m\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) + get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s))) \<le> (2::\<nat>) then 1::\<real>
           else (0::\<real>)) *
          (if get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) \<le> (3::\<nat>) - get\<^bsub>m\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) then 1::\<real> else (0::\<real>)) *
          (if get\<^bsub>c\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) = get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) then 1::\<real> else (0::\<real>))"
  let ?lhs = "\<lambda>(s\<^sub>1::mh_state) s::mh_state. ?lhs_1 s\<^sub>1 s / 18 + ?lhs_2 s\<^sub>1 s / 18 + ?lhs_3 s\<^sub>1 s / 9"

  let ?lhs_1' = "\<lambda>s::mh_state.
       (if p\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if c\<^sub>v s = (3::\<nat>) - (p\<^sub>v s + m\<^sub>v s) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v s = Suc (p\<^sub>v s) mod (3::\<nat>) then 1::\<real> else (0::\<real>))"
  let ?lhs_2' = "\<lambda>s::mh_state. (if p\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if c\<^sub>v s = (3::\<nat>) - (p\<^sub>v s + m\<^sub>v s) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v s = Suc (Suc (p\<^sub>v s)) mod (3::\<nat>) then 1::\<real> else (0::\<real>))"
  let ?lhs_3' = "\<lambda>s::mh_state. (if \<not> (3::\<nat>) - (m\<^sub>v s + p\<^sub>v s) = p\<^sub>v s then 1::\<real> else (0::\<real>)) *
       (if p\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if (3::\<nat>) - (m\<^sub>v s + p\<^sub>v s) \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if p\<^sub>v s \<le> (3::\<nat>) - m\<^sub>v s then 1::\<real> else (0::\<real>)) *
       (if c\<^sub>v s = p\<^sub>v s then 1::\<real> else (0::\<real>))"
  let ?lhs' = "\<lambda>s::mh_state. ?lhs_1' s / 18 + ?lhs_2' s / 18 + ?lhs_3' s / 9"

  have lhs_1_eq: "\<forall>(s\<^sub>1::mh_state) s::mh_state. ?lhs_1 s\<^sub>1 s = ?lhs_1' s"
    by (expr_simp)

  have lhs_2_eq: "\<forall>(s\<^sub>1::mh_state) s::mh_state. ?lhs_2 s\<^sub>1 s = ?lhs_2' s"
    by (expr_simp)

  have lhs_3_eq: "\<forall>(s\<^sub>1::mh_state) s::mh_state. ?lhs_3 s\<^sub>1 s = ?lhs_3' s"
    by (pred_simp)

  have lhs_lhs'_eq: "\<forall>(s\<^sub>1::mh_state) s::mh_state. ?lhs s\<^sub>1 s = ?lhs' s"
    by (simp add: c_def m_def p_def)

  have states_1_eq: 
    "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s = (3::\<nat>) - (p\<^sub>v s + m\<^sub>v s)) \<and> m\<^sub>v s = Suc (p\<^sub>v s) mod (3::\<nat>)} 
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>,\<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = (0::\<nat>), m\<^sub>v = (2::\<nat>)\<rparr>, 
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 1::\<nat>, m\<^sub>v = 0::\<nat>\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
    apply (smt (verit, best) mh_state.surjective Nat.add_0_right Nat.add_diff_assoc One_nat_def 
        Suc_1 Suc_le_mono add.commute add_2_eq_Suc' add_cancel_left_left bot_nat_0.extremum 
        diff_Suc_Suc diff_Suc_diff_eq2 diff_diff_left diff_is_0_eq diff_self_eq_0 
        eval_nat_numeral(3) le0 le_SucE le_antisym lessI less_2_cases mod_Suc mod_Suc_eq_mod_add3 
        mod_by_Suc_0 mod_less mod_mod_trivial mod_self nat.inject not_mod2_eq_Suc_0_eq_0 
        numeral_1_eq_Suc_0 numeral_3_eq_3 numeral_plus_numeral old.unit.exhaust order_le_less plus_1_eq_Suc)
    by force

  have infsum_lhs_1: "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs_1' s) = 3"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states)
    using states_1_eq apply auto[1]
    using states_1_eq by force

  have states_2_eq: 
    "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s = (3::\<nat>) - (p\<^sub>v s + m\<^sub>v s)) \<and> m\<^sub>v s = Suc (Suc (p\<^sub>v s)) mod (3::\<nat>)} 
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = (2::\<nat>), m\<^sub>v = (0::\<nat>)\<rparr>, 
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = 1::\<nat>\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
     apply (smt (verit, best) mh_state.surjective Nat.add_0_right Nat.add_diff_assoc One_nat_def 
        Suc_1 Suc_le_mono add.commute add_2_eq_Suc' add_cancel_left_left bot_nat_0.extremum 
        diff_Suc_Suc diff_Suc_diff_eq2 diff_diff_left diff_is_0_eq diff_self_eq_0 
        eval_nat_numeral(3) le0 le_SucE le_antisym lessI less_2_cases mod_Suc mod_Suc_eq_mod_add3 
        mod_by_Suc_0 mod_less mod_mod_trivial mod_self nat.inject not_mod2_eq_Suc_0_eq_0 
        numeral_1_eq_Suc_0 numeral_3_eq_3 numeral_plus_numeral old.unit.exhaust order_le_less plus_1_eq_Suc)
    by force

  have infsum_lhs_2: "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs_2' s) = 3"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states)
    using states_2_eq apply auto[1]
    using states_2_eq by force

  have states_3_eq: 
    "{s::mh_state. (((\<not> (3::\<nat>) - (m\<^sub>v s + p\<^sub>v s) = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>)) \<and> 
      (3::\<nat>) - (m\<^sub>v s + p\<^sub>v s) \<le> (2::\<nat>)) \<and> p\<^sub>v s \<le> (3::\<nat>) - m\<^sub>v s) \<and> c\<^sub>v s = p\<^sub>v s} 
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = (2::\<nat>)\<rparr>,
       \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (0::\<nat>)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (2::\<nat>)\<rparr>, 
       \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = 0::\<nat>\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
    apply (smt (verit, ccfv_SIG) mh_state.ext_inject mh_state.select_convs(1) 
        mh_state.select_convs(2) mh_state.select_convs(3) mh_state.surjective 
        Nat.add_0_right One_nat_def Suc_1 Suc_eq_numeral bot_nat_0.extremum diff_add_inverse 
        diff_commute diff_diff_cancel diff_diff_left diff_is_0_eq diff_is_0_eq' diff_le_self 
        diff_self_eq_0 eval_nat_numeral(3) le_Suc_eq le_antisym less_2_cases nat.distinct(1) 
        nle_le not_less_eq_eq old.nat.exhaust old.unit.exhaust order_le_less plus_1_eq_Suc)
    by force

  have infsum_lhs_3: "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs_3' s) = 6"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states)
    using states_3_eq apply auto[1]
    using states_3_eq by force

  have lhs_1_summable: "?lhs_1' summable_on UNIV"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states_summable)
    using states_1_eq by (simp_all)

  have lhs_2_summable: "?lhs_2' summable_on UNIV"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states_summable)
    using states_2_eq by (simp_all)

  have lhs_3_summable: "?lhs_3' summable_on UNIV"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states_summable)
    using states_3_eq by (simp_all)

  have infsum_lhs_lhs'_eq: "\<forall>s\<^sub>1::mh_state. (\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs s\<^sub>1 s) = (\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs' s)"
    apply (rule allI)
    by (metis (full_types) lhs_lhs'_eq)

  have infsum_lhs'_1: "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs' s) = 1"
    apply (subst infsum_add)
    apply (subst summable_on_add)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_1_summable)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_2_summable)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_3_summable)
    apply (subst infsum_add)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_1_summable)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_2_summable)
    apply (subst infsum_cdiv_left)
    apply (simp_all add: lhs_1_summable)
    apply (subst infsum_cdiv_left)
    apply (simp_all add: lhs_2_summable)
    apply (subst infsum_cdiv_left)
    apply (simp_all add: lhs_3_summable)
    using infsum_lhs_1 infsum_lhs_2 infsum_lhs_3 by (simp)

  have infsum_lhs_1: "\<forall>s\<^sub>1::mh_state. (\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs s\<^sub>1 s) = 1"
    using infsum_lhs'_1 infsum_lhs_lhs'_eq by presburger

  have lhs'_leq_1: "\<forall>s::mh_state. ?lhs' s \<le> infsum ?lhs' UNIV"
    apply (rule allI)
    apply (rule infsum_geq_element)
    apply fastforce
    apply (subst summable_on_add)
    apply (subst summable_on_add)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_1_summable)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_2_summable)
    apply (subst summable_on_cdiv_left)
    by (simp_all add: lhs_3_summable)
  have lhs'_leq_1': "\<forall>s::mh_state. ?lhs' s \<le> 1"
    using infsum_lhs'_1 lhs'_leq_1 by presburger
  have lhs_leq_1: "\<forall>s\<^sub>1::mh_state. (\<forall>s::mh_state. ?lhs s\<^sub>1 s \<le> 1)"
    by (simp add: c_def lhs'_leq_1' m_def p_def )

  show ?thesis
  apply (simp add: IMHA_C_altdef_def)
  apply (simp add: dist_defs)
  apply (simp only: expr_defs)
  apply (rule allI)
  apply (rule conjI)
  apply (rule allI)
  apply (rule conjI)
  using add_divide_distrib div_by_1 divide_divide_eq_right divide_le_0_1_iff mult_not_zero apply auto[1]
  using lhs_leq_1 apply blast
  using infsum_lhs_1 by blast
qed

lemma IMHA_C_altdef: "IMHA_C = prfun_of_rvfun IMHA_C_altdef"
  apply (simp only: IMHA_C_def MHA_C_def)
  apply (subst prfun_seqcomp_assoc)
  apply (rule INIT_is_dist)
    apply (rule MHA_is_dist)
  apply (simp add: passigns_def rvfun_assignment_inverse rvfun_assignment_is_dist)
  apply (simp add: MHA_NC_MHA_eq[symmetric])
  apply (simp add: IMHA_NC_def[symmetric])
  apply (simp add: IMHA_NC_altdef)
  apply (simp add: pfun_defs)
  apply (subst rvfun_inverse)
  using IMHA_NC_altdef_dist apply (simp add: is_final_distribution_prob is_final_prob_prob)
  apply (simp add: rvfun_assignment_inverse)
  apply (simp add: IMHA_NC_altdef_def IMHA_C_altdef_def)
  apply (expr_simp_1 add: assigns_r_def)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (simp only: fun_eq_iff)
  apply (rule allI)
  apply (subst ring_distribs(2))
  apply (subst ring_distribs(2))
  apply (subst times_divide_eq_left)+
proof -
  fix x::"mh_state \<times> mh_state"
  let ?lhs_1 = "\<lambda>v\<^sub>0::mh_state. (if c\<^sub>v v\<^sub>0 = p\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if p\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
          (if c\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
          (if m\<^sub>v v\<^sub>0 = Suc (c\<^sub>v v\<^sub>0) mod (3::\<nat>) then 1::\<real> else (0::\<real>)) *
          (if snd x = v\<^sub>0\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v v\<^sub>0 + m\<^sub>v v\<^sub>0)\<rparr> then 1::\<real> else (0::\<real>))"
  let ?lhs_2 = "\<lambda>v\<^sub>0::mh_state. (if c\<^sub>v v\<^sub>0 = p\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if p\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
          (if c\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
          (if m\<^sub>v v\<^sub>0 = Suc (Suc (c\<^sub>v v\<^sub>0)) mod (3::\<nat>) then 1::\<real> else (0::\<real>)) *
          (if snd x = v\<^sub>0\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v v\<^sub>0 + m\<^sub>v v\<^sub>0)\<rparr> then 1::\<real> else (0::\<real>))"
  let ?lhs_3 = "\<lambda>v\<^sub>0::mh_state. (if \<not> c\<^sub>v v\<^sub>0 = p\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if p\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
          (if c\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
          (if m\<^sub>v v\<^sub>0 = (3::\<nat>) - (c\<^sub>v v\<^sub>0 + p\<^sub>v v\<^sub>0) then 1::\<real> else (0::\<real>)) *
          (if snd x = v\<^sub>0\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v v\<^sub>0 + m\<^sub>v v\<^sub>0)\<rparr> then 1::\<real> else (0::\<real>))"
  let ?lhs = "\<lambda>s::mh_state. ?lhs_1 s / (18::\<real>) + ?lhs_2 s / (18::\<real>) + ?lhs_3 s / (9::\<real>) "

  let ?rhs_1 = "(if p\<^sub>v (snd x) \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * 
        (if c\<^sub>v (snd x) = (3::\<nat>) - (p\<^sub>v (snd x) + m\<^sub>v (snd x)) then 1::\<real> else (0::\<real>)) *
        (if m\<^sub>v (snd x) = Suc (p\<^sub>v (snd x)) mod (3::\<nat>) then 1::\<real> else (0::\<real>))"
  let ?rhs_2 = "(if p\<^sub>v (snd x) \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * 
        (if c\<^sub>v (snd x) = (3::\<nat>) - (p\<^sub>v (snd x) + m\<^sub>v (snd x)) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v (snd x) = Suc (Suc (p\<^sub>v (snd x))) mod (3::\<nat>) then 1::\<real> else (0::\<real>))"
  let ?rhs_3 = "(if \<not> (3::\<nat>) - (m\<^sub>v (snd x) + p\<^sub>v (snd x)) = p\<^sub>v (snd x) then 1::\<real> else (0::\<real>)) *
        (if p\<^sub>v (snd x) \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if (3::\<nat>) - (m\<^sub>v (snd x) + p\<^sub>v (snd x)) \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if p\<^sub>v (snd x) \<le> (3::\<nat>) - m\<^sub>v (snd x) then 1::\<real> else (0::\<real>)) *
       (if c\<^sub>v (snd x) = p\<^sub>v (snd x) then 1::\<real> else (0::\<real>))"
  let ?rhs = "?rhs_1 / (18::\<real>) + ?rhs_2 / (18::\<real>) + ?rhs_3 / (9::\<real>)"

  have states_1_eq:"{s::mh_state. ((c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>)) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> 
      m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>)}
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>,\<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (2::\<nat>)\<rparr>, 
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = 0::\<nat>\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
     apply (smt (z3) mh_state.surjective Orderings.order_eq_iff Suc_eq_numeral add.assoc 
        cong_exp_iff_simps(2) diff_add_zero diff_is_0_eq le_SucE mod_Suc mod_self numeral_1_eq_Suc_0 
        numeral_2_eq_2 numeral_3_eq_3 old.unit.exhaust one_eq_numeral_iff plus_1_eq_Suc)
    by force

  have states_2_eq:"{s::mh_state. ((c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>)) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> 
      m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>)}
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (0::\<nat>)\<rparr>, 
       \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
    apply (smt (verit, best) mh_state.surjective lessI less_2_cases mod_Suc mod_less numeral_2_eq_2 
        numeral_3_eq_3 old.unit.exhaust order_le_less) 
    by force

  have states_3_eq: "{s::mh_state. ((\<not> c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>)) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> 
      m\<^sub>v s = (3::\<nat>) - (c\<^sub>v s + p\<^sub>v s)}
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = (2::\<nat>), m\<^sub>v = Suc (0::\<nat>)\<rparr>,
       \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = (0::\<nat>), m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = (2::\<nat>), m\<^sub>v = (0::\<nat>)\<rparr>, 
       \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (0::\<nat>)\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
    apply (smt (verit, ccfv_SIG) mh_state.surjective One_nat_def diff_add_inverse diff_diff_eq 
        less_2_cases numeral_2_eq_2 numeral_3_eq_3 old.unit.exhaust order_le_less plus_1_eq_Suc)
    by force

  have lhs_1_summable: "?lhs_1 summable_on UNIV"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states_summable)
    apply (rule rev_finite_subset[where B="{s::mh_state. 
        ((c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>)) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>)}"])
    using states_1_eq apply simp
    apply blast
    by simp

  have lhs_2_summable: "?lhs_2 summable_on UNIV"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states_summable)
     apply (rule rev_finite_subset[where B= "{s::mh_state. 
        ((c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>)) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>)}"])
    using states_2_eq apply simp
    apply blast
    by simp

  have lhs_3_summable: "?lhs_3 summable_on UNIV"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states_summable)
    apply (rule rev_finite_subset[where B= "{s::mh_state. ((\<not> c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>)) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> 
      m\<^sub>v s = (3::\<nat>) - (c\<^sub>v s + p\<^sub>v s)}"])
    using states_3_eq apply simp
    apply blast
    by simp

  have lhs_1_infsum: "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs_1 s) = ?rhs_1"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states)
    apply (rule rev_finite_subset[where B="{s::mh_state. 
        ((c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>)) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>)}"])
    using states_1_eq apply simp
    apply fastforce
    apply (simp add: if_bool_eq_conj)
    apply (rule conjI)
    apply (rule impI)
    apply (rule card_1_singleton)
    apply (rule ex_ex1I)
    apply (rule_tac x = "\<lparr>p\<^sub>v = p\<^sub>v (snd x), c\<^sub>v = p\<^sub>v (snd x), m\<^sub>v = m\<^sub>v (snd x) \<rparr>" in exI)
    apply (erule conjE)+
    apply (rule conjI)
    apply (simp)
    apply (simp)
    apply (metis (no_types, lifting) mh_state.ext_inject mh_state.surjective mh_state.update_convs(2))
    apply (auto)
    proof -
      assume a1: "\<not> c\<^sub>v (snd x) = (3::\<nat>) - (p\<^sub>v (snd x) + m\<^sub>v (snd x))"
      have "\<not>(\<exists>s::mh_state. c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> 
              m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>) \<and> snd x = s\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v s + m\<^sub>v s)\<rparr>)"
        using a1 by (metis mh_state.select_convs(1) mh_state.select_convs(2) mh_state.select_convs(3) 
            mh_state.surjective mh_state.update_convs(2))
      then show "card {s::mh_state. c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> 
        m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>) \<and> snd x = s\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v s + m\<^sub>v s)\<rparr>} = (0::\<nat>)"
        using card_0_singleton by blast
    next
      assume a1: "\<not> p\<^sub>v (snd x) \<le> (2::\<nat>)"
      have "\<not>(\<exists>s::mh_state. c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> 
              m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>) \<and> snd x = s\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v s + m\<^sub>v s)\<rparr>)"
        using a1 by (metis mh_state.select_convs(1) mh_state.select_convs(2) mh_state.select_convs(3) 
            mh_state.surjective mh_state.update_convs(2))
      then show "card {s::mh_state. c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> 
        m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>) \<and> snd x = s\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v s + m\<^sub>v s)\<rparr>} = (0::\<nat>)"
        using card_0_singleton by blast
    next
      assume a1: "\<not> m\<^sub>v (snd x) = Suc (p\<^sub>v (snd x)) mod (3::\<nat>)"
      have "\<not>(\<exists>s::mh_state. c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> 
              m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>) \<and> snd x = s\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v s + m\<^sub>v s)\<rparr>)"
        using a1 by (metis mh_state.select_convs(1) mh_state.select_convs(2) mh_state.select_convs(3) 
            mh_state.surjective mh_state.update_convs(2))
      then show "card {s::mh_state. c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> 
        m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>) \<and> snd x = s\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v s + m\<^sub>v s)\<rparr>} = (0::\<nat>)"
        using card_0_singleton by blast
    qed

  have lhs_2_infsum: "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs_2 s) = ?rhs_2"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states)
    apply (rule rev_finite_subset[where B="{s::mh_state. 
        ((c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>)) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> m\<^sub>v s =  Suc (Suc (c\<^sub>v s)) mod (3::\<nat>)}"])
    using states_2_eq apply simp
    apply fastforce
    apply (simp add: if_bool_eq_conj)
    apply (rule conjI)
    apply (rule impI)
    apply (rule card_1_singleton)
    apply (rule ex_ex1I)
    apply (rule_tac x = "\<lparr>p\<^sub>v = p\<^sub>v (snd x), c\<^sub>v = p\<^sub>v (snd x), m\<^sub>v = m\<^sub>v (snd x) \<rparr>" in exI)
    apply (erule conjE)+
    apply (rule conjI)
    apply (simp)
    apply (simp)
    apply (metis mh_state.select_convs(1) mh_state.surjective mh_state.update_convs(2))
    apply (auto)
    proof -
      assume a1: "\<not> c\<^sub>v (snd x) = (3::\<nat>) - (p\<^sub>v (snd x) + m\<^sub>v (snd x))"
      have "\<not>(\<exists>s::mh_state. c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> 
              m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>) \<and> snd x = s\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v s + m\<^sub>v s)\<rparr>)"
        using a1 by (metis mh_state.select_convs(1) mh_state.select_convs(2) mh_state.select_convs(3) 
            mh_state.surjective mh_state.update_convs(2))
      then show "card {s::mh_state. c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> 
        m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>) \<and> snd x = s\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v s + m\<^sub>v s)\<rparr>} = (0::\<nat>)"
        using card_0_singleton by blast
    next
      assume a1: "\<not> p\<^sub>v (snd x) \<le> (2::\<nat>)"
      have "\<not>(\<exists>s::mh_state. c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> 
              m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>) \<and> snd x = s\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v s + m\<^sub>v s)\<rparr>)"
        using a1 by (metis mh_state.select_convs(1) mh_state.select_convs(2) mh_state.select_convs(3) 
            mh_state.surjective mh_state.update_convs(2))
      then show "card {s::mh_state. c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> 
        m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>) \<and> snd x = s\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v s + m\<^sub>v s)\<rparr>} = (0::\<nat>)"
        using card_0_singleton by blast
    next
      assume a1: "\<not> m\<^sub>v (snd x) = Suc (Suc (p\<^sub>v (snd x))) mod (3::\<nat>)"
      have "\<not>(\<exists>s::mh_state. c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> 
              m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>) \<and> snd x = s\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v s + m\<^sub>v s)\<rparr>)"
        using a1 by (metis mh_state.select_convs(1) mh_state.select_convs(2) mh_state.select_convs(3) 
            mh_state.surjective mh_state.update_convs(2))
      then show "card {s::mh_state. c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> 
        m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>) \<and> snd x = s\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v s + m\<^sub>v s)\<rparr>} = (0::\<nat>)"
        using card_0_singleton by blast
    qed

  have lhs_3_infsum: "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs_3 s) = ?rhs_3"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states)
    apply (rule rev_finite_subset[where B= "{s::mh_state. ((\<not> c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>)) \<and> 
      c\<^sub>v s \<le> (2::\<nat>)) \<and>  m\<^sub>v s = (3::\<nat>) - (c\<^sub>v s + p\<^sub>v s)}"])
    using states_3_eq apply simp
    apply fastforce
    apply (simp add: if_bool_eq_conj)
    apply (rule conjI)
    apply (rule impI)
    apply (rule card_1_singleton)
    apply (rule ex_ex1I)
    apply (rule_tac x = "\<lparr>p\<^sub>v = p\<^sub>v (snd x), c\<^sub>v = 3 - (p\<^sub>v (snd x) + m\<^sub>v (snd x)), m\<^sub>v = m\<^sub>v (snd x) \<rparr>" in exI)
    apply (erule conjE)+
    apply (rule conjI, simp)
    apply (rule conjI, simp)
    apply (rule conjI, simp)
    apply (rule conjI, simp)
    apply simp
    apply (erule conjE)+
    proof -
      fix s::"mh_state" and y::"mh_state"
      assume s1: "snd x = s\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v s + m\<^sub>v s)\<rparr>"
      assume y1: "snd x =  y\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v y + m\<^sub>v y)\<rparr>"
      assume s2: "m\<^sub>v s = (3::\<nat>) - (c\<^sub>v s + p\<^sub>v s)"
      assume y2: "m\<^sub>v y = (3::\<nat>) - (c\<^sub>v y + p\<^sub>v y)"
      assume s3: "p\<^sub>v s \<le> (2::\<nat>)"
      assume y3: "p\<^sub>v y \<le> (2::\<nat>)"
      assume s4: "p\<^sub>v (snd x) \<le> (2::\<nat>)"
      assume "(3::\<nat>) - (m\<^sub>v (snd x) + p\<^sub>v (snd x)) \<le> (2::\<nat>)"
      assume "p\<^sub>v (snd x) \<le> (3::\<nat>) - m\<^sub>v (snd x)"
      assume "c\<^sub>v (snd x) = p\<^sub>v (snd x)"
      assume "\<not> (3::\<nat>) - (m\<^sub>v (snd x) + p\<^sub>v (snd x)) = p\<^sub>v (snd x)"
      assume s4: "\<not> c\<^sub>v s = p\<^sub>v s"
      assume y4: "\<not> c\<^sub>v y = p\<^sub>v y"
      assume s5: "c\<^sub>v s \<le> (2::\<nat>)"
      assume y5: "c\<^sub>v y \<le> (2::\<nat>)"
  
      have psy: "p\<^sub>v s = p\<^sub>v y"
        using s1 y1 by (metis mh_state.ext_inject mh_state.surjective mh_state.update_convs(2))
      have msy: "m\<^sub>v s = m\<^sub>v y"
        using s1 y1 by (metis mh_state.ext_inject mh_state.surjective mh_state.update_convs(2))
      have csy: "c\<^sub>v s = c\<^sub>v y"
        using psy msy s2 y2 
        by (metis One_nat_def s4 y4 s5 y5 add.commute add_le_mono add_right_cancel diff_diff_cancel 
              le_Suc_eq numeral_2_eq_2 numeral_3_eq_3 plus_1_eq_Suc s3)
      show "s = y"
        using psy msy csy by simp
    next
      have pm_equal_snd_x: 
        "\<forall>s::mh_state. snd x = s\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v s + m\<^sub>v s)\<rparr> \<longrightarrow> p\<^sub>v s = p\<^sub>v (snd x) \<and> m\<^sub>v s = m\<^sub>v (snd x)"
        by (metis mh_state.select_convs(1) mh_state.select_convs(3) mh_state.surjective mh_state.update_convs(2))
      show "(p\<^sub>v (snd x) \<le> (3::\<nat>) - m\<^sub>v (snd x) \<longrightarrow> (3::\<nat>) - (m\<^sub>v (snd x) + p\<^sub>v (snd x)) \<le> (2::\<nat>) \<longrightarrow>
        p\<^sub>v (snd x) \<le> (2::\<nat>) \<longrightarrow> (3::\<nat>) - (m\<^sub>v (snd x) + p\<^sub>v (snd x)) = p\<^sub>v (snd x) \<or> \<not> c\<^sub>v (snd x) = p\<^sub>v (snd x)) \<longrightarrow>
        card {s::mh_state. \<not> c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = (3::\<nat>) - (c\<^sub>v s + p\<^sub>v s) \<and> 
        snd x = s\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v s + m\<^sub>v s)\<rparr>} =  (0::\<nat>)"
        apply (auto)
        apply (subgoal_tac "\<not>(\<exists>s::mh_state. \<not> c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> 
              m\<^sub>v s = (3::\<nat>) - (c\<^sub>v s + p\<^sub>v s) \<and> snd x = s\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v s + m\<^sub>v s)\<rparr>)")
        using card_0_singleton apply blast
        apply (metis mh_state.select_convs(1) mh_state.select_convs(3) mh_state.surjective 
            mh_state.update_convs(2) Nat.le_diff_conv2 One_nat_def Suc_1 add.commute diff_le_mono2 
            diff_le_self le_SucI le_add2 numeral_3_eq_3)
        apply (subgoal_tac "\<not>(\<exists>s::mh_state. \<not> c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> 
              m\<^sub>v s = (3::\<nat>) - (c\<^sub>v s + p\<^sub>v s) \<and> snd x = s\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v s + m\<^sub>v s)\<rparr>)")
        using card_0_singleton apply blast
        apply (smt (verit, ccfv_SIG) add.assoc add.commute le_cases3 le_diff_conv le_trans pm_equal_snd_x)
        apply (subgoal_tac "\<not>(\<exists>s::mh_state. \<not> c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> 
              m\<^sub>v s = (3::\<nat>) - (c\<^sub>v s + p\<^sub>v s) \<and> snd x = s\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v s + m\<^sub>v s)\<rparr>)")
        using card_0_singleton apply blast
        apply (metis pm_equal_snd_x)
        apply (subgoal_tac "\<not>(\<exists>s::mh_state. \<not> c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> 
              m\<^sub>v s = (3::\<nat>) - (c\<^sub>v s + p\<^sub>v s) \<and> snd x = s\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v s + m\<^sub>v s)\<rparr>)")
        using card_0_singleton apply blast
        apply (smt (z3) ab_semigroup_add_class.add_ac(1) add.right_neutral diff_add_inverse2 
           diff_is_0_eq' le_SucE le_add_diff nle_le numeral_3_eq_3 one_neq_zero plus_1_eq_Suc pm_equal_snd_x)
        apply (subgoal_tac "\<not>(\<exists>s::mh_state. \<not> c\<^sub>v s = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> 
              m\<^sub>v s = (3::\<nat>) - (c\<^sub>v s + p\<^sub>v s) \<and> snd x = s\<lparr>c\<^sub>v := (3::\<nat>) - (c\<^sub>v s + m\<^sub>v s)\<rparr>)")
        using card_0_singleton apply blast
        by (auto)
    qed

  show "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs s) = ?rhs"
    apply (subst infsum_add)
    apply (subst summable_on_add)
    apply (subst summable_on_cdiv_left)
    using lhs_1_summable apply blast+
    apply (subst summable_on_cdiv_left)
    using lhs_2_summable apply blast+
    apply (subst summable_on_cdiv_left)
    using lhs_3_summable apply blast+
    apply (subst infsum_add)
    apply (subst summable_on_cdiv_left)
    using lhs_1_summable apply blast+
    apply (subst summable_on_cdiv_left)
    using lhs_2_summable apply blast+
    apply (subst infsum_cdiv_left)
    using lhs_1_summable apply blast+
    apply (subst infsum_cdiv_left)
    using lhs_2_summable apply blast+
    apply (subst infsum_cdiv_left)
    using lhs_3_summable apply blast+
    using lhs_1_infsum lhs_2_infsum lhs_3_infsum by presburger
qed  

lemma IMHA_C_altdef_states_1_eq: 
    "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s = (3::\<nat>) - (p\<^sub>v s + m\<^sub>v s)) \<and> m\<^sub>v s = Suc (p\<^sub>v s) mod (3::\<nat>)} 
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>,\<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = (0::\<nat>), m\<^sub>v = (2::\<nat>)\<rparr>, 
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 1::\<nat>, m\<^sub>v = 0::\<nat>\<rparr>}"
  apply (simp add: set_eq_iff)
  apply (rule allI)
  apply (rule iffI)
  apply (smt (verit, best) mh_state.surjective Nat.add_0_right Nat.add_diff_assoc One_nat_def 
        Suc_1 Suc_le_mono add.commute add_2_eq_Suc' add_cancel_left_left bot_nat_0.extremum 
        diff_Suc_Suc diff_Suc_diff_eq2 diff_diff_left diff_is_0_eq diff_self_eq_0 
        eval_nat_numeral(3) le0 le_SucE le_antisym lessI less_2_cases mod_Suc mod_Suc_eq_mod_add3 
        mod_by_Suc_0 mod_less mod_mod_trivial mod_self nat.inject not_mod2_eq_Suc_0_eq_0 
        numeral_1_eq_Suc_0 numeral_3_eq_3 numeral_plus_numeral old.unit.exhaust order_le_less plus_1_eq_Suc)
  by (auto)

lemma IMHA_C_altdef_states_2_eq: 
    "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s = (3::\<nat>) - (p\<^sub>v s + m\<^sub>v s)) \<and> m\<^sub>v s = Suc (Suc (p\<^sub>v s)) mod (3::\<nat>)} 
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = (2::\<nat>), m\<^sub>v = (0::\<nat>)\<rparr>, 
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = 1::\<nat>\<rparr>}"
  apply (simp add: set_eq_iff)
  apply (rule allI)
  apply (rule iffI)
  apply (smt (verit, best) mh_state.surjective Nat.add_0_right Nat.add_diff_assoc One_nat_def 
      Suc_1 Suc_le_mono add.commute add_2_eq_Suc' add_cancel_left_left bot_nat_0.extremum 
      diff_Suc_Suc diff_Suc_diff_eq2 diff_diff_left diff_is_0_eq diff_self_eq_0 
      eval_nat_numeral(3) le0 le_SucE le_antisym lessI less_2_cases mod_Suc mod_Suc_eq_mod_add3 
      mod_by_Suc_0 mod_less mod_mod_trivial mod_self nat.inject not_mod2_eq_Suc_0_eq_0 
      numeral_1_eq_Suc_0 numeral_3_eq_3 numeral_plus_numeral old.unit.exhaust order_le_less plus_1_eq_Suc)
  by force

lemma IMHA_C_altdef_states_3_eq: 
  "{s::mh_state. (((\<not> (3::\<nat>) - (m\<^sub>v s + p\<^sub>v s) = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>)) \<and> 
      (3::\<nat>) - (m\<^sub>v s + p\<^sub>v s) \<le> (2::\<nat>)) \<and> p\<^sub>v s \<le> (3::\<nat>) - m\<^sub>v s) \<and> c\<^sub>v s = p\<^sub>v s} 
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = (2::\<nat>)\<rparr>,
       \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (0::\<nat>)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (2::\<nat>)\<rparr>, 
       \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = 0::\<nat>\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
    apply (smt (verit, ccfv_SIG) mh_state.ext_inject mh_state.select_convs(1) 
        mh_state.select_convs(2) mh_state.select_convs(3) mh_state.surjective 
        Nat.add_0_right One_nat_def Suc_1 Suc_eq_numeral bot_nat_0.extremum diff_add_inverse 
        diff_commute diff_diff_cancel diff_diff_left diff_is_0_eq diff_is_0_eq' diff_le_self 
        diff_self_eq_0 eval_nat_numeral(3) le_Suc_eq le_antisym less_2_cases nat.distinct(1) 
        nle_le not_less_eq_eq old.nat.exhaust old.unit.exhaust order_le_less plus_1_eq_Suc)
  by force

lemma IMHA_C_win: "rvfun_of_prfun (IMHA_C) ; \<lbrakk>c\<^sup>< = p\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e = (2/3)\<^sub>e"
proof -
  let ?lhs_1 = "\<lambda>(s\<^sub>1::mh_state) s::mh_state. 
    (if get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
          (if get\<^bsub>c\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) =
              (3::\<nat>) - (get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) + get\<^bsub>m\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)))
           then 1::\<real> else (0::\<real>)) *
          (if get\<^bsub>m\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) = Suc (get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s))) mod (3::\<nat>) then 1::\<real>
           else (0::\<real>))"
  let ?lhs_2 = "\<lambda>(s\<^sub>1::mh_state) s::mh_state. 
          (if get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
          (if get\<^bsub>c\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) =
              (3::\<nat>) - (get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) + get\<^bsub>m\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)))
           then 1::\<real> else (0::\<real>)) *
          (if get\<^bsub>m\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) = Suc (Suc (get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)))) mod (3::\<nat>) then 1::\<real>
           else (0::\<real>))"
  let ?lhs_3 = " \<lambda>(s\<^sub>1::mh_state) s::mh_state.
              (if \<not> (3::\<nat>) - (get\<^bsub>m\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) + get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s))) =
                 get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) then 1::\<real> else (0::\<real>)) *
          (if get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
          (if (3::\<nat>) - (get\<^bsub>m\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) + get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s))) \<le> (2::\<nat>) then 1::\<real>
           else (0::\<real>)) *
          (if get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) \<le> (3::\<nat>) - get\<^bsub>m\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) then 1::\<real> else (0::\<real>)) *
          (if get\<^bsub>c\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) = get\<^bsub>p\<^esub> (get\<^bsub>snd\<^sub>L\<^esub> (s\<^sub>1, s)) then 1::\<real> else (0::\<real>))"
  let ?lhs = "\<lambda>(s\<^sub>1::mh_state) s::mh_state. ?lhs_1 s\<^sub>1 s / 18 + ?lhs_2 s\<^sub>1 s / 18 + ?lhs_3 s\<^sub>1 s / 9"

  let ?lhs_1' = "\<lambda>s::mh_state.
       (if p\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if c\<^sub>v s = (3::\<nat>) - (p\<^sub>v s + m\<^sub>v s) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v s = Suc (p\<^sub>v s) mod (3::\<nat>) then 1::\<real> else (0::\<real>))"
  let ?lhs_2' = "\<lambda>s::mh_state. (if p\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if c\<^sub>v s = (3::\<nat>) - (p\<^sub>v s + m\<^sub>v s) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v s = Suc (Suc (p\<^sub>v s)) mod (3::\<nat>) then 1::\<real> else (0::\<real>))"
  let ?lhs_3' = "\<lambda>s::mh_state. (if \<not> (3::\<nat>) - (m\<^sub>v s + p\<^sub>v s) = p\<^sub>v s then 1::\<real> else (0::\<real>)) *
       (if p\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if (3::\<nat>) - (m\<^sub>v s + p\<^sub>v s) \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if p\<^sub>v s \<le> (3::\<nat>) - m\<^sub>v s then 1::\<real> else (0::\<real>)) *
       (if c\<^sub>v s = p\<^sub>v s then 1::\<real> else (0::\<real>))"
  let ?lhs' = "\<lambda>s::mh_state. ?lhs_1' s / 18 + ?lhs_2' s / 18 + ?lhs_3' s / 9"

  have lhs_1_eq: "\<forall>(s\<^sub>1::mh_state) s::mh_state. ?lhs_1 s\<^sub>1 s = ?lhs_1' s"
    by (expr_simp)

  have lhs_2_eq: "\<forall>(s\<^sub>1::mh_state) s::mh_state. ?lhs_2 s\<^sub>1 s = ?lhs_2' s"
    by (expr_simp)

  have lhs_3_eq: "\<forall>(s\<^sub>1::mh_state) s::mh_state. ?lhs_3 s\<^sub>1 s = ?lhs_3' s"
    by (expr_simp_1)

  have lhs_lhs'_eq: "\<forall>(s\<^sub>1::mh_state) s::mh_state. ?lhs s\<^sub>1 s = ?lhs' s"
    by (simp add: c_def m_def p_def)
(*
  have states_1_eq: 
    "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s = (3::\<nat>) - (p\<^sub>v s + m\<^sub>v s)) \<and> m\<^sub>v s = Suc (p\<^sub>v s) mod (3::\<nat>)} 
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>,\<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = (0::\<nat>), m\<^sub>v = (2::\<nat>)\<rparr>, 
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 1::\<nat>, m\<^sub>v = 0::\<nat>\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
    apply (smt (z3) mh_state.surjective Nat.add_0_right Nat.diff_add_assoc Nat.diff_cancel 
        add_diff_cancel_left' add_diff_cancel_right add_le_cancel_left bot_nat_0.extremum_uniqueI 
        diff_Suc_diff_eq2 diff_add_zero le_Suc_eq less_Suc_eq mod_less mod_self numeral_2_eq_2 
        numeral_3_eq_3 old.unit.exhaust)
    by force
*)
  have infsum_lhs_1: "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs_1' s) = 3"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states)
    using IMHA_C_altdef_states_1_eq apply auto[1]
    using IMHA_C_altdef_states_1_eq by force
(*
  have states_2_eq: 
    "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s = (3::\<nat>) - (p\<^sub>v s + m\<^sub>v s)) \<and> m\<^sub>v s = Suc (Suc (p\<^sub>v s)) mod (3::\<nat>)} 
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = (2::\<nat>), m\<^sub>v = (0::\<nat>)\<rparr>, 
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = 1::\<nat>\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
     apply (smt (verit, best) mh_state.surjective Nat.add_0_right Nat.add_diff_assoc One_nat_def 
        Suc_1 Suc_le_mono add.commute add_2_eq_Suc' add_cancel_left_left bot_nat_0.extremum 
        diff_Suc_Suc diff_Suc_diff_eq2 diff_diff_left diff_is_0_eq diff_self_eq_0 
        eval_nat_numeral(3) le0 le_SucE le_antisym lessI less_2_cases mod_Suc mod_Suc_eq_mod_add3 
        mod_by_Suc_0 mod_less mod_mod_trivial mod_self nat.inject not_mod2_eq_Suc_0_eq_0 
        numeral_1_eq_Suc_0 numeral_3_eq_3 numeral_plus_numeral old.unit.exhaust order_le_less plus_1_eq_Suc)
    by force
*)
  have infsum_lhs_2: "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs_2' s) = 3"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states)
    using IMHA_C_altdef_states_2_eq apply auto[1]
    using IMHA_C_altdef_states_2_eq by force
(*
  have states_3_eq: 
    "{s::mh_state. (((\<not> (3::\<nat>) - (m\<^sub>v s + p\<^sub>v s) = p\<^sub>v s \<and> p\<^sub>v s \<le> (2::\<nat>)) \<and> 
      (3::\<nat>) - (m\<^sub>v s + p\<^sub>v s) \<le> (2::\<nat>)) \<and> p\<^sub>v s \<le> (3::\<nat>) - m\<^sub>v s) \<and> c\<^sub>v s = p\<^sub>v s} 
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = (2::\<nat>)\<rparr>,
       \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (0::\<nat>)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = (2::\<nat>)\<rparr>, 
       \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = 0::\<nat>\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>}"
    apply (simp add: set_eq_iff)
    apply (rule allI)
    apply (rule iffI)
    apply (smt (verit, ccfv_SIG) mh_state.ext_inject mh_state.select_convs(1) 
        mh_state.select_convs(2) mh_state.select_convs(3) mh_state.surjective 
        Nat.add_0_right One_nat_def Suc_1 Suc_eq_numeral bot_nat_0.extremum diff_add_inverse 
        diff_commute diff_diff_cancel diff_diff_left diff_is_0_eq diff_is_0_eq' diff_le_self 
        diff_self_eq_0 eval_nat_numeral(3) le_Suc_eq le_antisym less_2_cases nat.distinct(1) 
        nle_le not_less_eq_eq old.nat.exhaust old.unit.exhaust order_le_less plus_1_eq_Suc)
    by force
*)
  have infsum_lhs_3: "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs_3' s) = 6"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states)
    using IMHA_C_altdef_states_3_eq apply auto[1]
    using IMHA_C_altdef_states_3_eq by force

  have lhs_1_summable: "?lhs_1' summable_on UNIV"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states_summable)
    using IMHA_C_altdef_states_1_eq by (simp_all)

  let ?lhs_cp = "\<lambda>s. (if c\<^sub>v s = p\<^sub>v s then 1::\<real> else (0::\<real>))"

  have lhs_1'_summable: "(\<lambda>s. ?lhs_1' s * ?lhs_cp s) summable_on UNIV"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states_summable)
    apply (rule finite_subset[where B="{s::mh_state. ((p\<^sub>v s \<le> (2::\<nat>) \<and> 
      c\<^sub>v s = (3::\<nat>) - (p\<^sub>v s + m\<^sub>v s)) \<and> m\<^sub>v s = Suc (p\<^sub>v s) mod (3::\<nat>))}"])
    apply force
    using IMHA_C_altdef_states_1_eq by (simp_all)

  have lhs_1'_infsum: "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs_1' s * ?lhs_cp s) = 0"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states)
    apply (metis (mono_tags, lifting) Collect_mono finite.emptyI finite_insert finite_subset IMHA_C_altdef_states_1_eq)
    apply (subgoal_tac "\<not>(\<exists>s::mh_state. ((p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s = (3::\<nat>) - (p\<^sub>v s + m\<^sub>v s)) \<and> 
      m\<^sub>v s = Suc (p\<^sub>v s) mod (3::\<nat>)) \<and> c\<^sub>v s = p\<^sub>v s)")
    apply (simp add: card_0_singleton)
    by (metis (no_types, lifting) add_cancel_left_right add_diff_cancel_left add_diff_cancel_left' 
        diff_is_0_eq le_SucE lessI mod_less mod_less_eq_dividend mod_self nat.distinct(1) 
        numeral_2_eq_2 numeral_3_eq_3 plus_1_eq_Suc)

  have lhs_2_summable: "?lhs_2' summable_on UNIV"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states_summable)
    using IMHA_C_altdef_states_2_eq by (simp_all)

  have lhs_2'_summable: "(\<lambda>s. ?lhs_2' s * ?lhs_cp s) summable_on UNIV"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states_summable)
    apply (rule finite_subset[where B="{s::mh_state. ((p\<^sub>v s \<le> (2::\<nat>) \<and> 
      c\<^sub>v s = (3::\<nat>) - (p\<^sub>v s + m\<^sub>v s)) \<and> m\<^sub>v s = Suc (Suc (p\<^sub>v s)) mod (3::\<nat>))}"])
    apply force
    using IMHA_C_altdef_states_2_eq by (simp_all)

  have lhs_2'_infsum: "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs_2' s * ?lhs_cp s) = 0"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states)
    apply (metis (mono_tags, lifting) Collect_mono finite.emptyI finite_insert finite_subset IMHA_C_altdef_states_2_eq)
    apply (subgoal_tac "\<not>(\<exists>s::mh_state. ((p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s = (3::\<nat>) - (p\<^sub>v s + m\<^sub>v s)) \<and> 
      m\<^sub>v s = Suc (Suc (p\<^sub>v s)) mod (3::\<nat>)) \<and> c\<^sub>v s = p\<^sub>v s)")
    apply (simp add: card_0_singleton)
    by (smt (z3) Suc_diff_le Suc_n_not_le_n diff_add_zero diff_le_self le_SucE le_add_diff_inverse2 
        mod_less mod_self numeral_2_eq_2 numeral_3_eq_3 order_le_less zero_less_diff)

  have lhs_3_summable: "?lhs_3' summable_on UNIV"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states_summable)
    using IMHA_C_altdef_states_3_eq by (simp_all)

  have lhs_3'_summable: "(\<lambda>s. ?lhs_3' s * ?lhs_cp s) summable_on UNIV"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_constant_finite_states_summable)
    using IMHA_C_altdef_states_3_eq by (simp_all)

  have lhs_3'_infsum: "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs_3' s * ?lhs_cp s) = 6"
    apply (subst infsum_lhs_3[symmetric])
    by (smt (verit) infsum_cong mult_cancel_left2 mult_cancel_right)

  have infsum_lhs_lhs'_eq: "\<forall>s\<^sub>1::mh_state. (\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs s\<^sub>1 s) = (\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs' s)"
    apply (rule allI)
    by (metis (full_types) lhs_lhs'_eq)

  have infsum_lhs'_1: "(\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs' s) = 1"
    apply (subst infsum_add)
    apply (subst summable_on_add)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_1_summable)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_2_summable)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_3_summable)
    apply (subst infsum_add)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_1_summable)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_2_summable)
    apply (subst infsum_cdiv_left)
    apply (simp_all add: lhs_1_summable)
    apply (subst infsum_cdiv_left)
    apply (simp_all add: lhs_2_summable)
    apply (subst infsum_cdiv_left)
    apply (simp_all add: lhs_3_summable)
    using infsum_lhs_1 infsum_lhs_2 infsum_lhs_3 by (simp)

  have infsum_lhs_1: "\<forall>s\<^sub>1::mh_state. (\<Sum>\<^sub>\<infinity>s::mh_state. ?lhs s\<^sub>1 s) = 1"
    using infsum_lhs'_1 infsum_lhs_lhs'_eq by presburger

  have lhs'_leq_1: "\<forall>s::mh_state. ?lhs' s \<le> infsum ?lhs' UNIV"
    apply (rule allI)
    apply (rule infsum_geq_element)
    apply fastforce
    apply (subst summable_on_add)
    apply (subst summable_on_add)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_1_summable)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_2_summable)
    apply (subst summable_on_cdiv_left)
    by (simp_all add: lhs_3_summable)
  have lhs'_leq_1': "\<forall>s::mh_state. ?lhs' s \<le> 1"
    using infsum_lhs'_1 lhs'_leq_1 by presburger
  have lhs_leq_1: "\<forall>s\<^sub>1::mh_state. (\<forall>s::mh_state. ?lhs s\<^sub>1 s \<le> 1)"
    by (simp add: c_def lhs'_leq_1' m_def p_def )

  have IMHA_C_altdef_dist: "is_final_distribution IMHA_C_altdef"
      apply (simp add: IMHA_C_altdef_def)
      apply (simp add: dist_defs)
      apply (simp only: expr_defs)
      apply (rule allI)
      apply (rule conjI)
      apply (rule allI)
      apply (rule conjI)
      using add_divide_distrib div_by_1 divide_divide_eq_right divide_le_0_1_iff mult_not_zero apply auto[1]
      using lhs_leq_1 apply blast
      using infsum_lhs_1 by blast

  show ?thesis
    apply (simp add: IMHA_C_altdef)
    apply (subst rvfun_inverse)
    using IMHA_C_altdef_dist apply (simp add: is_dist_def is_final_prob_prob)
    apply (simp add: IMHA_C_altdef_def)
    apply (expr_auto)
    apply (simp add: ring_distribs(2))
    apply (subst infsum_add)
    apply (subst summable_on_add)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_1'_summable)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_2'_summable)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_3'_summable)
    apply (subst infsum_add)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_1'_summable)
    apply (subst summable_on_cdiv_left)
    apply (simp_all add: lhs_2'_summable)
    apply (subst infsum_cdiv_left)
    apply (simp_all add: lhs_1'_summable)
    apply (subst infsum_cdiv_left)
    apply (simp_all add: lhs_2'_summable)
    apply (subst infsum_cdiv_left)
    apply (simp_all add: lhs_3'_summable)
    using lhs_1'_infsum lhs_2'_infsum lhs_3'_infsum by linarith
qed

subsubsection \<open> Average values \<close>
text \<open>Average value of @{term "p"} after the execution of @{term "IMHA_C"}, a Change Strategy. \<close>

term "(p\<^sup><)\<^sub>e"
term "($p\<^sup><)\<^sub>e"
term "rvfun_of_prfun IMHA_C ; ($p\<^sup><)\<^sub>e"
lemma IMHA_C_average_p: "rvfun_of_prfun IMHA_C ; ($p\<^sup><)\<^sub>e = (1)\<^sub>e"
  apply (simp add: IMHA_C_altdef)
  apply (subst rvfun_inverse)
  using IMHA_C_altdef_dist apply (simp add: is_final_distribution_prob is_final_prob_prob)
  apply (simp add: IMHA_C_altdef_def)
  apply (expr_auto)
  apply (simp add: ring_distribs(2))
  apply (subst conditional_conds_conj)+
  apply (subst times_divide_eq_right[symmetric])+
  apply (subst conditional_cmult_1)+
  apply (subst infsum_add)
  apply (rule summable_on_add)
  apply (subst infsum_cond_finite_states_summable)
  apply (subst IMHA_C_altdef_states_1_eq)
  apply blast+
  apply (subst infsum_cond_finite_states_summable)
  apply (subst IMHA_C_altdef_states_2_eq)
  apply blast+
  apply (subst infsum_cond_finite_states_summable)
  apply (subst IMHA_C_altdef_states_3_eq)
  apply blast+
  apply (subst infsum_add)
  apply (subst infsum_cond_finite_states_summable)
  apply (subst IMHA_C_altdef_states_1_eq)
  apply blast+
  apply (subst infsum_cond_finite_states_summable)
  apply (subst IMHA_C_altdef_states_2_eq)
  apply blast+
  apply (subst infsum_cond_finite_states)
  apply (subst IMHA_C_altdef_states_1_eq)
  apply blast+
  apply (subst infsum_cond_finite_states)
  apply (subst IMHA_C_altdef_states_2_eq)
  apply blast+
  apply (subst infsum_cond_finite_states)
  apply (subst IMHA_C_altdef_states_3_eq)
  apply blast+
  apply (subst IMHA_C_altdef_states_1_eq)
  apply (subst IMHA_C_altdef_states_2_eq)
  apply (subst IMHA_C_altdef_states_3_eq)
  apply (subst sum_divide_distrib[symmetric])+
  by (simp)

lemma IMHA_C_average_c: "rvfun_of_prfun IMHA_C ; ($c\<^sup><)\<^sub>e = (1)\<^sub>e"
  apply (simp add: IMHA_C_altdef)
  apply (subst rvfun_inverse)
  using IMHA_C_altdef_dist apply (simp add: is_final_distribution_prob is_final_prob_prob)
  apply (simp add: IMHA_C_altdef_def)
  apply (expr_auto)
  apply (simp add: ring_distribs(2))
  apply (subst conditional_conds_conj)+
  apply (subst times_divide_eq_right[symmetric])+
  apply (subst conditional_cmult_1)+
  apply (subst infsum_add)
  apply (rule summable_on_add)
  apply (subst infsum_cond_finite_states_summable)
  apply (subst IMHA_C_altdef_states_1_eq)
  apply blast+
  apply (subst infsum_cond_finite_states_summable)
  apply (subst IMHA_C_altdef_states_2_eq)
  apply blast+
  apply (subst infsum_cond_finite_states_summable)
  apply (subst IMHA_C_altdef_states_3_eq)
  apply blast+
  apply (subst infsum_add)
  apply (subst infsum_cond_finite_states_summable)
  apply (subst IMHA_C_altdef_states_1_eq)
  apply blast+
  apply (subst infsum_cond_finite_states_summable)
  apply (subst IMHA_C_altdef_states_2_eq)
  apply blast+
  apply (subst infsum_cond_finite_states)
  apply (subst IMHA_C_altdef_states_1_eq)
  apply blast+
  apply (subst infsum_cond_finite_states)
  apply (subst IMHA_C_altdef_states_2_eq)
  apply blast+
  apply (subst infsum_cond_finite_states)
  apply (subst IMHA_C_altdef_states_3_eq)
  apply blast+
  apply (subst IMHA_C_altdef_states_1_eq)
  apply (subst IMHA_C_altdef_states_2_eq)
  apply (subst IMHA_C_altdef_states_3_eq)
  apply (subst sum_divide_distrib[symmetric])+
  by (simp)

subsection \<open> Learn the fact (forgetful Monty) \<close>

text \<open> Suppose now that Monty forgets which door has the prize behind it. He just opens either of the 
doors not chosen by the contestant. 
If the prize is revealed ($m'=p'$), then obviously the contestant switches their choice to that door. 
So the contestant will surely win. 

However, if the prize is not revealed ($m' \neq p'$), should the contestant switch?
\<close>

definition Forgetful_Monty where 
"Forgetful_Monty = INIT ; (if\<^sub>p 1/2 then (m := ($c + 1) mod 3) else (m := ($c + 2) mod 3))"

(*
definition Learn_fact where
"Learn_fact = Forgetful_Monty \<parallel> (if\<^sub>p 1/2 then (m := ($p + 1) mod 3) else (m := ($p + 2) mod 3))"
*)

definition Learn_fact :: "(mh_state, mh_state) prfun" 
  where "Learn_fact = prfun_of_rvfun ((rvfun_of_prfun Forgetful_Monty) \<parallel>\<^sub>f \<lbrakk>m\<^sup>> \<noteq> p\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e)"

definition Forgetful_Monty' :: "(mh_state, mh_state) rvfun" where 
"Forgetful_Monty' = ((\<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> = ((c\<^sup>> + 1) mod 3)\<rbrakk>\<^sub>\<I>\<^sub>e) / 18 + 
               (\<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> = ((c\<^sup>> + 2) mod 3)\<rbrakk>\<^sub>\<I>\<^sub>e) / 18)\<^sub>e"

lemma Forgetful_Monty_altdef: "Forgetful_Monty = prfun_of_rvfun Forgetful_Monty'"
proof -
  (* have "\<forall>mm. card {s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> m\<^sub>v s = mm} = 9" *)
  have set_states: "\<forall>m. {s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> m\<^sub>v s = m}
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = m\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = m\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = m\<rparr>,
      \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = 0::\<nat>, m\<^sub>v = m\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = m\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = 2::\<nat>, m\<^sub>v = m\<rparr>,
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = m\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = m\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = m\<rparr> 
      }"
  apply (simp add: set_eq_iff)
  apply (rule allI)+
  apply (rule iffI)
  apply (smt (z3) mh_state.surjective mh_state.update_convs(1) mh_state.update_convs(2) 
        One_nat_def Suc_1 bot_nat_0.extremum_unique c_def le_Suc_eq lens.simps(1) m_def old.unit.exhaust p_def)
  by (smt (verit, best) mh_state.ext_inject mh_state.surjective mh_state.update_convs(1) 
        mh_state.update_convs(2) One_nat_def bot_nat_0.extremum c_def lens.simps(1) less_one 
        linorder_not_le m_def order_le_less p_def zero_neq_numeral)

  have card_states: "\<forall>mm. card {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = mm\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = mm\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = mm\<rparr>,
      \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = 0::\<nat>, m\<^sub>v = mm\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = mm\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = 2::\<nat>, m\<^sub>v = mm\<rparr>,
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = mm\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = mm\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = mm\<rparr> 
    } = 9"
    apply (rule allI)
    using record_neq_p_c by fastforce

  have finite_states: "\<forall>m. finite {s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> m\<^sub>v s = m}"
    using local.set_states by auto

  have summable_on: "\<forall>(m\<^sub>v'::\<nat>) (p\<^sub>v'::\<nat>) c\<^sub>v'::\<nat>. (\<lambda>v\<^sub>0::mh_state.
           (if p\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
           (if m\<^sub>v v\<^sub>0 = m\<^sub>v' then 1::\<real> else (0::\<real>)) *
           ((if \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = Suc c\<^sub>v' mod (3::\<nat>)\<rparr> = v\<^sub>0\<lparr>m\<^sub>v := Suc (c\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> then 1::\<real>
             else (0::\<real>)) / (2::\<real>) +
            (if \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = Suc c\<^sub>v' mod (3::\<nat>)\<rparr> = v\<^sub>0\<lparr>m\<^sub>v := Suc (Suc (c\<^sub>v v\<^sub>0)) mod (3::\<nat>)\<rparr> then 1::\<real>
             else (0::\<real>)) / (2::\<real>))) summable_on UNIV"
  proof (rule allI)+
    fix m\<^sub>v'::"\<nat>" and p\<^sub>v'::"\<nat>" and c\<^sub>v'::"\<nat>"
    show "(\<lambda>v\<^sub>0::mh_state.
           (if p\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
           (if m\<^sub>v v\<^sub>0 = m\<^sub>v' then 1::\<real> else (0::\<real>)) *
           ((if \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = Suc c\<^sub>v' mod (3::\<nat>)\<rparr> = v\<^sub>0\<lparr>m\<^sub>v := Suc (c\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> then 1::\<real> else (0::\<real>)) / (2::\<real>) +
            (if \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = Suc c\<^sub>v' mod (3::\<nat>)\<rparr> = v\<^sub>0\<lparr>m\<^sub>v := Suc (Suc (c\<^sub>v v\<^sub>0)) mod (3::\<nat>)\<rparr> then 1::\<real> else (0::\<real>)) /
            (2::\<real>))) summable_on
       UNIV "
    apply (subst conditional_conds_conj)+
    apply (simp add: ring_distribs(1))
    apply (subst conditional_conds_conj)+
    apply (subst summable_on_add)
    apply (subst summable_on_cdiv_left)
    apply (subst infsum_constant_finite_states_summable)
    apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
    using finite_states apply presburger
    apply fastforce+
    apply (subst summable_on_cdiv_left)
    apply (subst infsum_constant_finite_states_summable)
    apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
    using finite_states apply presburger
    by fastforce+
  qed

  show ?thesis
  apply (simp add: Forgetful_Monty_def Forgetful_Monty'_def)
  apply (simp add: INIT_altdef)
  apply (simp only: pseqcomp_def passigns_def pchoice_def)
  apply (simp only: rvfun_assignment_inverse)
  apply (simp only: ereal2real_1_2)
  apply (subst rvfun_pchoice_inverse_c'')
  apply (simp) 
  using rvfun_assignment_is_prob apply blast
  using rvfun_assignment_is_prob apply blast
  apply (simp)
  apply (subst rvfun_inverse)
  apply (simp add: is_prob_def iverson_bracket_def)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (pred_auto)
  apply (subst infsum_cdiv_left)
  using summable_on apply blast
  using mod_Suc apply force
  using mod_Suc apply force
  using mod_Suc apply force
  proof -
    fix m\<^sub>v'::"\<nat>" and p\<^sub>v'::"\<nat>" and c\<^sub>v'::"\<nat>"
    assume a1: "p\<^sub>v' \<le> (2::\<nat>)"
    assume a2: "c\<^sub>v' \<le> (2::\<nat>)"
    have set_1_eq: "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v') \<and>
           \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = Suc c\<^sub>v' mod (3::\<nat>)\<rparr> = s\<lparr>m\<^sub>v := Suc (c\<^sub>v s) mod (3::\<nat>)\<rparr>} 
        = {\<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = m\<^sub>v'\<rparr>}"
      apply (auto)
      apply (metis mh_state.ext_inject mh_state.surjective mh_state.update_convs(3))
      by (simp add: a1 a2)+
  
    have set_2_eq: "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v') \<and>
           \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = Suc c\<^sub>v' mod (3::\<nat>)\<rparr> = s\<lparr>m\<^sub>v := Suc (Suc (c\<^sub>v s)) mod (3::\<nat>)\<rparr>} = {}"
      apply (auto)
      by (smt (verit, best) mh_state.ext_inject mh_state.surjective mh_state.update_convs(3) 
          lessI less_2_cases mod_Suc_eq mod_less mod_self nat.simps(3) numeral_2_eq_2 numeral_3_eq_3 
          order_le_less)
  
    show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state.
            (if p\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
            (if m\<^sub>v v\<^sub>0 = m\<^sub>v' then 1::\<real> else (0::\<real>)) *
            ((if \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = Suc c\<^sub>v' mod (3::\<nat>)\<rparr> = v\<^sub>0\<lparr>m\<^sub>v := Suc (c\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> then 1::\<real> else (0::\<real>)) / (2::\<real>) +
             (if \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = Suc c\<^sub>v' mod (3::\<nat>)\<rparr> = v\<^sub>0\<lparr>m\<^sub>v := Suc (Suc (c\<^sub>v v\<^sub>0)) mod (3::\<nat>)\<rparr> then 1::\<real> else (0::\<real>)) /
             (2::\<real>)) / (9::\<real>)) * (18::\<real>) = (1::\<real>)"
      apply (subst conditional_conds_conj)+
      apply (simp add: ring_distribs(1))
      apply (subst conditional_conds_conj)+
      apply (subst infsum_cdiv_left)
       apply (rule summable_on_add)
      apply (subst summable_on_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
          apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
          apply fastforce+
      apply (subst summable_on_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
          apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst infsum_add)
      apply (subst summable_on_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst summable_on_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst infsum_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst infsum_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst infsum_constant_finite_states)
      apply (metis (no_types, lifting) Collect_mono finite_states finite_subset)
      apply (subst infsum_constant_finite_states)
      apply (metis (no_types, lifting) Collect_mono finite_states finite_subset)
      apply (subst set_1_eq, subst set_2_eq)
      by simp
  next
    fix m\<^sub>v'::"\<nat>" and p\<^sub>v'::"\<nat>" and c\<^sub>v'::"\<nat>"
    assume a1: "p\<^sub>v' \<le> (2::\<nat>)"
    assume a2: "c\<^sub>v' \<le> (2::\<nat>)"
    have set_1_eq: "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v') \<and>
           \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = Suc (Suc c\<^sub>v') mod (3::\<nat>)\<rparr> = s\<lparr>m\<^sub>v := Suc (c\<^sub>v s) mod (3::\<nat>)\<rparr>} 
        = {}"
      apply (auto)
      by (smt (verit, best) mh_state.ext_inject mh_state.surjective mh_state.update_convs(3) 
          lessI less_2_cases mod_Suc_eq mod_less mod_self nat.simps(3) numeral_2_eq_2 numeral_3_eq_3 
          order_le_less)
      
    have set_2_eq: "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v') \<and>
           \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = Suc (Suc c\<^sub>v') mod (3::\<nat>)\<rparr> = s\<lparr>m\<^sub>v := Suc (Suc (c\<^sub>v s)) mod (3::\<nat>)\<rparr>} 
      = {\<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = m\<^sub>v'\<rparr>}"
      apply (auto)
      apply (metis mh_state.ext_inject mh_state.surjective mh_state.update_convs(3))
      by (simp add: a1 a2)+
  
    show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state.
            (if p\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
            (if m\<^sub>v v\<^sub>0 = m\<^sub>v' then 1::\<real> else (0::\<real>)) *
            ((if \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = Suc (Suc c\<^sub>v') mod (3::\<nat>)\<rparr> = v\<^sub>0\<lparr>m\<^sub>v := Suc (c\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> then 1::\<real> else (0::\<real>)) /
             (2::\<real>) +
             (if \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = Suc (Suc c\<^sub>v') mod (3::\<nat>)\<rparr> = v\<^sub>0\<lparr>m\<^sub>v := Suc (Suc (c\<^sub>v v\<^sub>0)) mod (3::\<nat>)\<rparr> then 1::\<real> else (0::\<real>)) /
             (2::\<real>)) /  (9::\<real>)) * (18::\<real>) =  (1::\<real>)"
      apply (subst conditional_conds_conj)+
      apply (simp add: ring_distribs(1))
      apply (subst conditional_conds_conj)+
      apply (subst infsum_cdiv_left)
       apply (rule summable_on_add)
      apply (subst summable_on_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
          apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
          apply fastforce+
      apply (subst summable_on_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
          apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst infsum_add)
      apply (subst summable_on_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst summable_on_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst infsum_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst infsum_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst infsum_constant_finite_states)
      apply (metis (no_types, lifting) Collect_mono finite_states finite_subset)
      apply (subst infsum_constant_finite_states)
       apply (metis (no_types, lifting) Collect_mono finite_states finite_subset)
      apply (subst set_1_eq, subst set_2_eq)
      by simp
  next
    fix m\<^sub>v'::"\<nat>" and p\<^sub>v'::"\<nat>" and c\<^sub>v'::"\<nat>" and m\<^sub>v''::"\<nat>"
    assume a1: "p\<^sub>v' \<le> (2::\<nat>)"
    assume a2: "c\<^sub>v' \<le> (2::\<nat>)"
    assume a3: "\<not> m\<^sub>v'' = Suc c\<^sub>v' mod (3::\<nat>)"
    assume a4: "\<not> m\<^sub>v'' = Suc (Suc c\<^sub>v') mod (3::\<nat>)"
    have set_1_eq: "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v') \<and>
           \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = m\<^sub>v''\<rparr> = s\<lparr>m\<^sub>v := Suc (c\<^sub>v s) mod (3::\<nat>)\<rparr>} = {}"
      apply (auto)
      by (metis mh_state.ext_inject mh_state.surjective mh_state.update_convs(3) a3)
      
    have set_2_eq: "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v') \<and>
           \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = m\<^sub>v''\<rparr> = s\<lparr>m\<^sub>v := Suc (Suc (c\<^sub>v s)) mod (3::\<nat>)\<rparr>} = {}"
      apply (auto)
      by (metis mh_state.ext_inject mh_state.surjective mh_state.update_convs(3) a4)
  
    show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state.
            (if p\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
            (if m\<^sub>v v\<^sub>0 = m\<^sub>v' then 1::\<real> else (0::\<real>)) *
            ((if \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = m\<^sub>v''\<rparr> = v\<^sub>0\<lparr>m\<^sub>v := Suc (c\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> then 1::\<real> else (0::\<real>)) / (2::\<real>) +
             (if \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = m\<^sub>v''\<rparr> = v\<^sub>0\<lparr>m\<^sub>v := Suc (Suc (c\<^sub>v v\<^sub>0)) mod (3::\<nat>)\<rparr> then 1::\<real> else (0::\<real>)) / (2::\<real>)) /
            (9::\<real>)) =
         (0::\<real>)"
      apply (subst conditional_conds_conj)+
      apply (simp add: ring_distribs(1))
      apply (subst conditional_conds_conj)+
      apply (subst infsum_cdiv_left)
       apply (rule summable_on_add)
      apply (subst summable_on_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst summable_on_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst infsum_add)
      apply (subst summable_on_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst summable_on_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst infsum_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst infsum_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst infsum_constant_finite_states)
      apply (metis (no_types, lifting) Collect_mono finite_states finite_subset)
      apply (subst infsum_constant_finite_states)
       apply (metis (no_types, lifting) Collect_mono finite_states finite_subset)
      apply (subst set_1_eq, subst set_2_eq)
      by simp
  next
    fix m\<^sub>v'::"\<nat>" and p\<^sub>v'::"\<nat>" and c\<^sub>v'::"\<nat>" and m\<^sub>v''::"\<nat>"
    assume a1: "p\<^sub>v' \<le> (2::\<nat>)"
    assume a2: "\<not> c\<^sub>v' \<le> (2::\<nat>)"
    have set_1_eq: "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v') \<and>
           \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = m\<^sub>v''\<rparr> = s\<lparr>m\<^sub>v := Suc (c\<^sub>v s) mod (3::\<nat>)\<rparr>} = {}"
      apply (auto)
      by (metis mh_state.ext_inject mh_state.surjective mh_state.update_convs(3) a2)
      
    have set_2_eq: "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v') \<and>
           \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = m\<^sub>v''\<rparr> = s\<lparr>m\<^sub>v := Suc (Suc (c\<^sub>v s)) mod (3::\<nat>)\<rparr>} = {}"
      apply (auto)
      by (metis mh_state.ext_inject mh_state.surjective mh_state.update_convs(3) a2)
  
    show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state.
            (if p\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
            (if m\<^sub>v v\<^sub>0 = m\<^sub>v' then 1::\<real> else (0::\<real>)) *
            ((if \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = m\<^sub>v''\<rparr> = v\<^sub>0\<lparr>m\<^sub>v := Suc (c\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> then 1::\<real> else (0::\<real>)) / (2::\<real>) +
             (if \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = m\<^sub>v''\<rparr> = v\<^sub>0\<lparr>m\<^sub>v := Suc (Suc (c\<^sub>v v\<^sub>0)) mod (3::\<nat>)\<rparr> then 1::\<real> else (0::\<real>)) / (2::\<real>)) /
            (9::\<real>)) = (0::\<real>)"
      apply (subst conditional_conds_conj)+
      apply (simp add: ring_distribs(1))
      apply (subst conditional_conds_conj)+
      apply (subst infsum_cdiv_left)
       apply (rule summable_on_add)
      apply (subst summable_on_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst summable_on_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst infsum_add)
      apply (subst summable_on_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst summable_on_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst infsum_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst infsum_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst infsum_constant_finite_states)
      apply (metis (no_types, lifting) Collect_mono finite_states finite_subset)
      apply (subst infsum_constant_finite_states)
       apply (metis (no_types, lifting) Collect_mono finite_states finite_subset)
      apply (subst set_1_eq, subst set_2_eq)
      by simp
  next
    fix m\<^sub>v'::"\<nat>" and p\<^sub>v'::"\<nat>" and c\<^sub>v'::"\<nat>" and m\<^sub>v''::"\<nat>"
    assume a1: "\<not> p\<^sub>v' \<le> (2::\<nat>)"
    have set_1_eq: "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v') \<and>
           \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = m\<^sub>v''\<rparr> = s\<lparr>m\<^sub>v := Suc (c\<^sub>v s) mod (3::\<nat>)\<rparr>} = {}"
      apply (auto)
      by (metis mh_state.ext_inject mh_state.surjective mh_state.update_convs(3) a1)
      
    have set_2_eq: "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v') \<and>
           \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = m\<^sub>v''\<rparr> = s\<lparr>m\<^sub>v := Suc (Suc (c\<^sub>v s)) mod (3::\<nat>)\<rparr>} = {}"
      apply (auto)
      by (metis mh_state.ext_inject mh_state.surjective mh_state.update_convs(3) a1)
  
    show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state.
            (if p\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
            (if m\<^sub>v v\<^sub>0 = m\<^sub>v' then 1::\<real> else (0::\<real>)) *
            ((if \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = m\<^sub>v''\<rparr> = v\<^sub>0\<lparr>m\<^sub>v := Suc (c\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> then 1::\<real> else (0::\<real>)) / (2::\<real>) +
             (if \<lparr>p\<^sub>v = p\<^sub>v', c\<^sub>v = c\<^sub>v', m\<^sub>v = m\<^sub>v''\<rparr> = v\<^sub>0\<lparr>m\<^sub>v := Suc (Suc (c\<^sub>v v\<^sub>0)) mod (3::\<nat>)\<rparr> then 1::\<real> else (0::\<real>)) / (2::\<real>)) /
            (9::\<real>)) =
         (0::\<real>)"
      apply (subst conditional_conds_conj)+
      apply (simp add: ring_distribs(1))
      apply (subst conditional_conds_conj)+
      apply (subst infsum_cdiv_left)
       apply (rule summable_on_add)
      apply (subst summable_on_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst summable_on_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst infsum_add)
      apply (subst summable_on_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst summable_on_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst infsum_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst infsum_cdiv_left)
      apply (subst infsum_constant_finite_states_summable)
      apply (rule rev_finite_subset[where B = "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = m\<^sub>v')}"])
      using finite_states apply presburger
      apply fastforce+
      apply (subst infsum_constant_finite_states)
      apply (metis (no_types, lifting) Collect_mono finite_states finite_subset)
      apply (subst infsum_constant_finite_states)
       apply (metis (no_types, lifting) Collect_mono finite_states finite_subset)
      apply (subst set_1_eq, subst set_2_eq)
      by simp
  qed
qed

definition Forgetful_Monty'_learned :: "(mh_state, mh_state) rvfun" where 
"Forgetful_Monty'_learned = ((\<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> = ((c\<^sup>> + 1) mod 3)\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> \<noteq> p\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e) / 12 + 
               (\<lbrakk>p\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>c\<^sup>> \<in> {0..2}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> = ((c\<^sup>> + 2) mod 3)\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> \<noteq> p\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e) / 12)\<^sub>e"

lemma Forgetful_Monty_win: "rvfun_of_prfun Learn_fact ; \<lbrakk>c\<^sup>< = p\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e = (1/2)\<^sub>e"
proof -
  \<comment> \<open>Forgetful Monty\<close>
  have set_states_1: "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>)}
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 2::\<nat>\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = 0::\<nat>\<rparr>,
      \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 2::\<nat>\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = 2::\<nat>, m\<^sub>v = 0::\<nat>\<rparr>,
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 2::\<nat>\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = 0::\<nat>\<rparr> 
      }"
  apply (simp add: set_eq_iff)
  apply (rule allI)+
  apply (rule iffI)
  apply (smt (verit) mh_state.select_convs(1) mh_state.select_convs(3) mh_state.surjective 
      One_nat_def Suc_1 Suc_eq_numeral Suc_eq_plus1 Suc_le_mono add_Suc_right eval_nat_numeral(3) 
      le_0_eq le_Suc_eq le_add2 lessI less_Suc_eq mod_Suc mod_Suc_le_divisor mod_less 
      mod_less_eq_dividend mod_self n_not_Suc_n nat.distinct(1) nle_le not_less_eq_eq 
      numeral_One numeral_eq_one_iff old.unit.exhaust one_add_one one_le_numeral 
      pred_numeral_simps(2) trans_le_add2)
    by fastforce

  have card_states_1: "card {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 2::\<nat>\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = 0::\<nat>\<rparr>,
      \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 2::\<nat>\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = 2::\<nat>, m\<^sub>v = 0::\<nat>\<rparr>,
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 2::\<nat>\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = 0::\<nat>\<rparr> 
      } = 9"
    using record_neq_p_c by fastforce

  have finite_states_1: "finite {s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>)}"
    using local.set_states_1 by auto

  have set_states_2: "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>)}
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 0::\<nat>\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>,
      \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = 0::\<nat>, m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 0::\<nat>\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>,
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 0::\<nat>\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr> 
      }"
  apply (simp add: set_eq_iff)
  apply (rule allI)+
  apply (rule iffI)
  apply (smt (verit) mh_state.select_convs(1) mh_state.select_convs(3) mh_state.surjective 
      One_nat_def Suc_1 Suc_eq_numeral Suc_eq_plus1 Suc_le_mono add_Suc_right eval_nat_numeral(3) 
      le_0_eq le_Suc_eq le_add2 lessI less_Suc_eq mod_Suc mod_Suc_le_divisor mod_less 
      mod_less_eq_dividend mod_self n_not_Suc_n nat.distinct(1) nle_le not_less_eq_eq 
      numeral_One numeral_eq_one_iff old.unit.exhaust one_add_one one_le_numeral 
      pred_numeral_simps(2) trans_le_add2)
    by fastforce

  have card_states_2: "card {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 0::\<nat>\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>,
      \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = 0::\<nat>, m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 0::\<nat>\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>,
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 0::\<nat>\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr> 
      } = 9"
    using record_neq_p_c by fastforce

  have finite_states_2: "finite {s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>)}"
    using local.set_states_2 by auto

  have infsum_1: "(\<Sum>\<^sub>\<infinity>s::mh_state.
       (if p\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * (if c\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>) then 1::\<real> else (0::\<real>)) / (18::\<real>) +
       (if p\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * (if c\<^sub>v s \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
       (if m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>) then 1::\<real> else (0::\<real>)) / (18::\<real>)) = (1::\<real>)"
    apply (subst conditional_conds_conj)+
    apply (subst infsum_add)
    apply (subst summable_on_cdiv_left)
    apply (subst infsum_constant_finite_states_summable)
    using finite_states_1 apply blast+
    apply (subst summable_on_cdiv_left)
    apply (subst infsum_constant_finite_states_summable)
    using finite_states_2 apply blast+
    apply (subst infsum_cdiv_left)
    apply (subst infsum_constant_finite_states_summable)
    using finite_states_1 apply blast+
    apply (subst infsum_cdiv_left)
    apply (subst infsum_constant_finite_states_summable)
    using finite_states_2 apply blast+
    apply (subst infsum_constant_finite_states)
    using finite_states_1 apply blast+
    apply (subst infsum_constant_finite_states)
    using finite_states_2 apply blast+
    apply (subst set_states_1, subst card_states_1)
    apply (subst set_states_2, subst card_states_2)
    by (simp)

  \<comment> \<open>The final statesuf of Forgetful Monty is a distribution\<close>
  have Forgetful_Monty'_dist: "is_final_distribution (Forgetful_Monty')"
    apply (simp add: dist_defs Forgetful_Monty'_def)
    apply (expr_auto)
    using infsum_1 by blast

  \<comment> \<open>And so conversion is still itself.\<close>
  have Forgetful_Monty'': "rvfun_of_prfun (prfun_of_rvfun Forgetful_Monty') = Forgetful_Monty'"
    apply (subst rvfun_inverse)
    apply (simp add: Forgetful_Monty'_dist is_final_distribution_prob is_final_prob_prob)
    by (simp add: Forgetful_Monty'_dist)+

  \<comment> \<open> Learn a new fact \<close>
  have set_states_1': "{s::mh_state. ((p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>)) 
      \<and> m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>)) \<and> \<not> m\<^sub>v s = p\<^sub>v s}
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 2::\<nat>\<rparr>, 
       \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 2::\<nat>\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = 2::\<nat>, m\<^sub>v = 0::\<nat>\<rparr>,
       \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>,  \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = 0::\<nat>\<rparr> 
      }"
  apply (simp add: set_eq_iff)
  apply (rule allI)+
  apply (rule iffI)
  apply (smt (verit) mh_state.select_convs(1) mh_state.select_convs(3) mh_state.surjective 
      One_nat_def Suc_1 Suc_eq_numeral Suc_eq_plus1 Suc_le_mono add_Suc_right eval_nat_numeral(3) 
      le_0_eq le_Suc_eq le_add2 lessI less_Suc_eq mod_Suc mod_Suc_le_divisor mod_less 
      mod_less_eq_dividend mod_self n_not_Suc_n nat.distinct(1) nle_le not_less_eq_eq 
      numeral_One numeral_eq_one_iff old.unit.exhaust one_add_one one_le_numeral 
      pred_numeral_simps(2) trans_le_add2)
  by fastforce

  have card_states_1': "card {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 2::\<nat>\<rparr>, 
       \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 2::\<nat>\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = 2::\<nat>, m\<^sub>v = 0::\<nat>\<rparr>,
       \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>,  \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = 0::\<nat>\<rparr> 
      } = 6"
    using record_neq_p_c by fastforce

  have finite_state_1': "finite {s::mh_state. ((p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> 
    m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>)) \<and> \<not> m\<^sub>v s = p\<^sub>v s}"
    apply (rule rev_finite_subset[where B = 
        "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>))}"])
    using finite_states_1 apply presburger
    by fastforce

  have set_states_2': "{s::mh_state.  ((p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> 
      m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>)) \<and> \<not> m\<^sub>v s = p\<^sub>v s}
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>,
      \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = 0::\<nat>, m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 0::\<nat>\<rparr>, 
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 0::\<nat>\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr> 
      }"
  apply (simp add: set_eq_iff)
  apply (rule allI)+
  apply (rule iffI)
  apply (smt (verit) mh_state.select_convs(1) mh_state.select_convs(3) mh_state.surjective 
      One_nat_def Suc_1 Suc_eq_numeral Suc_eq_plus1 Suc_le_mono add_Suc_right eval_nat_numeral(3) 
      le_0_eq le_Suc_eq le_add2 lessI less_Suc_eq mod_Suc mod_Suc_le_divisor mod_less 
      mod_less_eq_dividend mod_self n_not_Suc_n nat.distinct(1) nle_le not_less_eq_eq 
      numeral_One numeral_eq_one_iff old.unit.exhaust one_add_one one_le_numeral 
      pred_numeral_simps(2) trans_le_add2)
    by fastforce

  have card_states_2': "card {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>,
      \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = 0::\<nat>, m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 0::\<nat>\<rparr>, 
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 0::\<nat>\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr> 
      } = 6"
    using record_neq_p_c by fastforce

  have finite_state_2': "finite {s::mh_state. ((p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> 
    m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>)) \<and> \<not> m\<^sub>v s = p\<^sub>v s}"
    apply (rule rev_finite_subset[where B = 
        "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>))}"])
    using finite_states_2 apply presburger
    by fastforce

  \<comment> \<open> After a new fact is learned, 1/3 states are excluded because these states have its 
    @{text "m\<^sub>v v\<^sub>0"} equal to @{text  "p\<^sub>v v\<^sub>0"}. \<close>
  let ?infsum = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state.
        ((if p\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
         (if m\<^sub>v v\<^sub>0 = Suc (c\<^sub>v v\<^sub>0) mod (3::\<nat>) then 1::\<real> else (0::\<real>)) /
         (18::\<real>) +
         (if p\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
         (if m\<^sub>v v\<^sub>0 = Suc (Suc (c\<^sub>v v\<^sub>0)) mod (3::\<nat>) then 1::\<real> else (0::\<real>)) /
         (18::\<real>)) * (if \<not> m\<^sub>v v\<^sub>0 = p\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)))"

  have infsum_2_3: "?infsum = 2/3"
    apply (simp add: ring_distribs(2))
    apply (subst conditional_conds_conj)+
    apply (subst infsum_add)
    apply (subst summable_on_cdiv_left)
    apply (subst infsum_constant_finite_states_summable)
    using finite_state_1' apply blast
    apply fastforce+
    apply (subst summable_on_cdiv_left)
    apply (subst infsum_constant_finite_states_summable)
    using finite_state_2' apply blast
    apply fastforce+
    apply (subst infsum_cdiv_left)
    apply (subst infsum_constant_finite_states_summable)
    using finite_state_1' apply blast
    apply fastforce+
    apply (subst infsum_cdiv_left)
    apply (subst infsum_constant_finite_states_summable)
    using finite_state_2' apply blast
    apply fastforce+
    apply (subst infsum_constant_finite_states)
    using finite_state_1' apply blast
    apply (subst infsum_constant_finite_states)
    using finite_state_2' apply blast
    apply (subst set_states_1', subst card_states_1')
    apply (subst set_states_2', subst card_states_2')
    by (simp)

  have Forgetful_Monty''': "(Forgetful_Monty' \<parallel>\<^sub>f \<lbrakk>m\<^sup>> \<noteq> p\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e) = Forgetful_Monty'_learned"
    apply (simp add: dist_defs Forgetful_Monty'_def Forgetful_Monty'_learned_def)
    apply (expr_auto)
    apply (metis One_nat_def Suc_n_not_n mod_Suc one_eq_numeral_iff semiring_norm(86))
    using mod_Suc apply auto[1]
    using infsum_2_3 by linarith+

  \<comment> \<open>The final states of the learned program is also a distribution. \<close>
  have Forgetful_Monty'_learned_dist: "is_final_distribution Forgetful_Monty'_learned"
    apply (simp add: dist_defs Forgetful_Monty'_learned_def)
    apply (expr_auto)
    apply (subst conditional_conds_conj)+
    apply (subst infsum_add)
    apply (subst summable_on_cdiv_left)
    apply (subst infsum_constant_finite_states_summable)
    using finite_state_1' apply blast
    apply fastforce+
    apply (subst summable_on_cdiv_left)
    apply (subst infsum_constant_finite_states_summable)
    using finite_state_2' apply blast
    apply fastforce+
    apply (subst infsum_cdiv_left)
    apply (subst infsum_constant_finite_states_summable)
    using finite_state_1' apply blast
    apply fastforce+
    apply (subst infsum_cdiv_left)
    apply (subst infsum_constant_finite_states_summable)
    using finite_state_2' apply blast
    apply fastforce+
    apply (subst infsum_constant_finite_states)
    using finite_state_1' apply blast
    apply (subst infsum_constant_finite_states)
    using finite_state_2' apply blast
    apply (subst set_states_1', subst card_states_1')
    apply (subst set_states_2', subst card_states_2')
    by (simp)

  \<comment> \<open> Win when @{text "c\<^sub>v s = p\<^sub>v s"}  \<close>
  have set_states_1'': "{s::mh_state. (((p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>)) 
    \<and> m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>)) \<and> \<not> m\<^sub>v s = p\<^sub>v s) \<and> c\<^sub>v s = p\<^sub>v s}
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 2::\<nat>\<rparr>, 
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = 0::\<nat>\<rparr>}"
  apply (simp add: set_eq_iff)
  apply (rule allI)+
  apply (rule iffI)
  apply (smt (verit) mh_state.select_convs(1) mh_state.select_convs(3) mh_state.surjective 
      One_nat_def Suc_1 Suc_eq_numeral Suc_eq_plus1 Suc_le_mono add_Suc_right eval_nat_numeral(3) 
      le_0_eq le_Suc_eq le_add2 lessI less_Suc_eq mod_Suc mod_Suc_le_divisor mod_less 
      mod_less_eq_dividend mod_self n_not_Suc_n nat.distinct(1) nle_le not_less_eq_eq 
      numeral_One numeral_eq_one_iff old.unit.exhaust one_add_one one_le_numeral 
      pred_numeral_simps(2) trans_le_add2)
  by fastforce

  have card_states_1'': "card {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr>, 
    \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 2::\<nat>\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = 0::\<nat>\<rparr>} = 3"
    using record_neq_p_c by fastforce

  have finite_state_1'': "finite {s::mh_state. (((p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> 
    m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>)) \<and> \<not> m\<^sub>v s = p\<^sub>v s) \<and> c\<^sub>v s = p\<^sub>v s}"
    apply (rule rev_finite_subset[where B = 
        "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = Suc (c\<^sub>v s) mod (3::\<nat>))}"])
    using finite_states_1 apply presburger
    by fastforce

  have set_states_2'': "{s::mh_state.  (((p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> 
      m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>)) \<and> \<not> m\<^sub>v s = p\<^sub>v s)  \<and> c\<^sub>v s = p\<^sub>v s}
    = {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = (2::\<nat>)\<rparr>, \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 0::\<nat>\<rparr>, 
      \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr> }"
  apply (simp add: set_eq_iff)
  apply (rule allI)+
  apply (rule iffI)
  apply (smt (verit) mh_state.select_convs(1) mh_state.select_convs(3) mh_state.surjective 
      One_nat_def Suc_1 Suc_eq_numeral Suc_eq_plus1 Suc_le_mono add_Suc_right eval_nat_numeral(3) 
      le_0_eq le_Suc_eq le_add2 lessI less_Suc_eq mod_Suc mod_Suc_le_divisor mod_less 
      mod_less_eq_dividend mod_self n_not_Suc_n nat.distinct(1) nle_le not_less_eq_eq 
      numeral_One numeral_eq_one_iff old.unit.exhaust one_add_one one_le_numeral 
      pred_numeral_simps(2) trans_le_add2)
    by fastforce

  have card_states_2'': "card {\<lparr>p\<^sub>v = 0::\<nat>, c\<^sub>v = 0::\<nat>, m\<^sub>v = (2::\<nat>)\<rparr>,
      \<lparr>p\<^sub>v = Suc (0::\<nat>), c\<^sub>v = Suc (0::\<nat>), m\<^sub>v = 0::\<nat>\<rparr>, \<lparr>p\<^sub>v = 2::\<nat>, c\<^sub>v = 2::\<nat>, m\<^sub>v = Suc (0::\<nat>)\<rparr> } = 3"
    using record_neq_p_c by fastforce

  have finite_state_2'': "finite {s::mh_state. (((p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>)) \<and> 
    m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>)) \<and> \<not> m\<^sub>v s = p\<^sub>v s) \<and> c\<^sub>v s = p\<^sub>v s}"
    apply (rule rev_finite_subset[where B = 
        "{s::mh_state. (p\<^sub>v s \<le> (2::\<nat>) \<and> c\<^sub>v s \<le> (2::\<nat>) \<and> m\<^sub>v s = Suc (Suc (c\<^sub>v s)) mod (3::\<nat>))}"])
    using finite_states_2 apply presburger
    by fastforce

  \<comment> \<open> After learning a new fact, the probability to win is 1/2, and so it doesn't matter if the 
  contestant chooses to switch or not. \<close>
  have infsum_1_2: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::mh_state.
       ((if p\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
        (if m\<^sub>v v\<^sub>0 = Suc (c\<^sub>v v\<^sub>0) mod (3::\<nat>) then 1::\<real> else (0::\<real>)) *
        (if \<not> m\<^sub>v v\<^sub>0 = p\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) /
        (12::\<real>) +
        (if p\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) * (if c\<^sub>v v\<^sub>0 \<le> (2::\<nat>) then 1::\<real> else (0::\<real>)) *
        (if m\<^sub>v v\<^sub>0 = Suc (Suc (c\<^sub>v v\<^sub>0)) mod (3::\<nat>) then 1::\<real> else (0::\<real>)) *
        (if \<not> m\<^sub>v v\<^sub>0 = p\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) /
        (12::\<real>)) *
       (if c\<^sub>v v\<^sub>0 = p\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>))) * (2::\<real>) = (1::\<real>)"
    apply (simp add: ring_distribs(2))
    apply (subst conditional_conds_conj)+
    apply (subst infsum_add)
    apply (subst summable_on_cdiv_left)
    apply (subst infsum_constant_finite_states_summable)
    using finite_state_1'' apply blast+
    apply (subst summable_on_cdiv_left)
    apply (subst infsum_constant_finite_states_summable)
    using finite_state_2'' apply blast+
    apply (subst infsum_cdiv_left)
    apply (subst infsum_constant_finite_states_summable)
    using finite_state_1'' apply blast+
    apply (subst infsum_cdiv_left)
    apply (subst infsum_constant_finite_states_summable)
    using finite_state_2'' apply blast+
    apply (subst infsum_constant_finite_states)
    using finite_state_1'' apply blast+
    apply (subst infsum_constant_finite_states)
    using finite_state_2'' apply blast+
    apply (subst set_states_1'', subst card_states_1'')
    apply (subst set_states_2'', subst card_states_2'')
    by (simp)
    
  show ?thesis
    apply (simp add: Learn_fact_def Forgetful_Monty_altdef)
    apply (subst Forgetful_Monty'')
    apply (subst Forgetful_Monty''')
    apply (subst rvfun_inverse)
    apply (simp add: Forgetful_Monty'_learned_dist is_final_distribution_prob is_final_prob_prob)
    apply (simp add: Forgetful_Monty'_learned_def dist_defs)
    apply (expr_auto)
    by (simp add: infsum_1_2)
qed

end
