section \<open> Uniform Selection Algorithms \<close>

text \<open> This example illustrates how to prove a tail-recursive probabilistic program that achieves a
uniform choice out of N based on a binary probabilistic choice operator @{text "\<oplus>\<^bsub>r\<^esub>"}. See 
@{url "https://robostar.cs.york.ac.uk/prob_case_studies/ransac_simp/index.html#-v2"} for its 
diagrammatic presentation in RoboChart.\<close>

theory utp_prob_ex1
  imports
  "../utp_prob_des_laws"
  "UTP.utp_hoare"
  "UTP.utp"
begin recall_syntax

alphabet unisel_vars = 
  i :: "nat"
  c :: "bool"

subsection \<open> unisel_rec_body \<close>
(* Use meta-subst operator for the weight of probabilistic choice *)
abbreviation unisel_rec_body_choice :: 
  "nat \<Rightarrow> (unisel_vars, unisel_vars) rel_pdes" where
"unisel_rec_body_choice N \<equiv> ((\<K>(c :=\<^sub>D false)) \<oplus>\<^bsub>r\<^esub> (\<K>(i :=\<^sub>D i+1))) \<lbrakk>r\<rightarrow>(\<lceil>\<lceil>U(1/real (\<guillemotleft>N\<guillemotright>-i))\<rceil>\<^sub><\<rceil>\<^sub>D)\<rbrakk>"

abbreviation unisel_rec_body :: "nat
     \<Rightarrow> (unisel_vars, unisel_vars) rel_pdes
     \<Rightarrow> (unisel_vars, unisel_vars) rel_pdes" where 
"unisel_rec_body N X \<equiv> (
        (unisel_rec_body_choice N ;; \<up>X)
          \<triangleleft> U(i < \<guillemotleft>N-1\<guillemotright> \<and> c) \<triangleright>\<^sub>D 
        \<K>(II\<^sub>D)
      )"

lemma unisel_rec_body_pchoice_simp:
  assumes "r \<in> {0..1} "
  shows "(\<K>(c :=\<^sub>D false)) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> (\<K>(i :=\<^sub>D i+1))
    = U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>r\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>r\<guillemotright>))"
  apply (simp add: pemp_assign)
  apply (ndes_simp cls: assms)
  apply (simp add: upred_defs)
  apply (rel_auto)
  using assms apply (simp add: pmf_wplus)
  apply (simp add: pmf_not_the_one_is_zero)
  using assms apply (simp add: pmf_wplus)
  apply (simp add: pmf_not_the_one_is_zero)
  proof -
    fix ok\<^sub>v::"bool" and i\<^sub>v::"nat" and c\<^sub>v::"bool" and nn\<^sub>v::"nat" and more::"'a" and ok\<^sub>v'::"bool" and
         prob\<^sub>v::"'a unisel_vars_scheme pmf"
    let ?s1 = "\<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False,  \<dots> = more\<rparr>"
    let ?s2 = "\<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = c\<^sub>v,  \<dots> = more\<rparr>"
    let ?prob' = "pmf_of_list [(?s1, (1::real))]"
    let ?prob'' = "pmf_of_list [(?s2, (1::real))]"
  
    assume a1: "pmf prob\<^sub>v ?s2 = (1::real) - pmf prob\<^sub>v ?s1"
    assume a2: "r = pmf prob\<^sub>v ?s1"
    have f1: "prob\<^sub>v = ?prob' +\<^bsub>r\<^esub> ?prob''"
      apply (subst pmf_instance_from_two_full_states'[of "prob\<^sub>v" "?s1" "?s2"])
      using a1 apply auto[1]
      apply simp
      by (simp add: a2)
    show "\<exists>(i\<^sub>v'::nat) (c\<^sub>v'::bool) (morea::'a) prob\<^sub>v'::'a unisel_vars_scheme pmf.
            pmf prob\<^sub>v' ?s1 = (1::real) \<and>
            (\<exists>prob\<^sub>v''::'a unisel_vars_scheme pmf.
                pmf prob\<^sub>v'' ?s2 = (1::real) \<and>
                i\<^sub>v' = i\<^sub>v \<and>
                c\<^sub>v' = c\<^sub>v \<and>
                morea = more \<and>
                prob\<^sub>v = prob\<^sub>v' +\<^bsub>pmf prob\<^sub>v ?s1\<^esub> prob\<^sub>v'')"
      apply (rule_tac x = "i\<^sub>v" in exI)
      apply (rule_tac x = "c\<^sub>v" in exI)
      apply (rule_tac x = "more" in exI)
      apply (rule_tac x = "?prob'" in exI)
      apply (rule conjI)
      apply (subst pmf_pmf_of_list, simp add: pmf_of_list_wf_def, simp)
      apply (rule_tac x = "?prob''" in exI)
      apply (rule conjI)
      apply (subst pmf_pmf_of_list, simp add: pmf_of_list_wf_def, simp, auto)
      using f1 a2 by force
  qed

lemma unisel_rec_body_pchoice_simp':
  shows "( ((\<K>(c :=\<^sub>D false)) \<oplus>\<^bsub>r\<^esub> (\<K>(i :=\<^sub>D i+1)))
    = U(true \<turnstile>\<^sub>n (($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>r\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>r\<guillemotright>) 
      \<triangleleft> \<guillemotleft>r\<guillemotright> \<in> {0..1} \<triangleright> false)))" (is "?LHS = ?RHS")
proof (cases "r \<in> {0..1}")
  case True
  then have T: "r \<in> {0..1}" by auto
  show ?thesis 
    proof (cases "r = 0")
      case True
      have lhs: "?LHS = (\<K>(i :=\<^sub>D i+1))"
        using True by (simp add: prob_choice_zero)
      have lhs': "... =  U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1))"
        apply (simp add: pemp_assign)
        by (rel_auto)
      have rhs: "?RHS = U(true \<turnstile>\<^sub>n (($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = 0 \<and> $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1)))"
        using True 
        by (smt cond_true_false conj_conds diff_zero le_pred_refl true_conj_zero(1) uset_laws(2) 
            utp_pred_laws.cond_idem utp_pred_laws.inf_top_right uzero_le_laws(3) zero_uexpr_def)
      have rhs': "... = U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1))"
        apply (rel_auto)
        by (simp add: pmf_not_the_one_is_zero)
      show ?thesis using lhs lhs' rhs rhs' by auto
    next
      case False
      have TF: "r \<in> {0..1} \<and> \<not> (r::real) = (0::real)"
        using T False by blast
      then show ?thesis 
        proof (cases "r = 1")
          case True
          have lhs: "?LHS = (\<K>(c :=\<^sub>D false))"
            using True by (simp add: prob_choice_one)
          have lhs': "... =  U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = 1))"
            by (simp add: pemp_assign)
          have rhs: "?RHS = U(true \<turnstile>\<^sub>n (($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = 1 \<and> $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 0)))"
            using True 
            by (smt cond_true_false conj_conds diff_numeral_special(9) le_pred_refl one_uexpr_def 
                true_conj_zero(1) uset_laws(2) utp_pred_laws.cond_idem utp_pred_laws.inf_top_right 
                uzero_le_laws(3))
          have rhs': "... = U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = 1))"
            apply (rel_auto)
            by (simp add: pmf_not_the_one_is_zero)
          show ?thesis using lhs lhs' rhs rhs' by auto
        next
          case False
          then have TFF: "r \<in> {0<..<1}"
            using TF by auto
          have lhs: "?LHS = (\<K>(c :=\<^sub>D false)) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> (\<K>(i :=\<^sub>D i+1))"
            using TFF by (simp add: prob_choice_r)
          have f0: "U(\<guillemotleft>r\<guillemotright> \<in> {0..1}) = U(true)"
            using True apply (rel_auto) 
            by (smt lit.rep_eq lit_fun_simps(3) true_inf(2) ulit_eq)
          have rhs: "?RHS = U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>r\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>r\<guillemotright>))"
            using TFF True f0 by (metis cond_unit_T)
          then show ?thesis using lhs rhs unisel_rec_body_pchoice_simp
            using True by auto
        qed
    qed
next
  case False
  have lhs: "?LHS = \<top>\<^sub>D"
    apply (subst prob_choice_def)
    using False by (auto)
  have f0: "U(\<guillemotleft>r\<guillemotright> \<in> {0..1}) = U(false)"
    using False apply (pred_auto)
    by (metis inf_bool_def inf_uexpr.rep_eq lit.rep_eq lit_fun_simps(3))+
  then have rhs: "?RHS = U(true \<turnstile>\<^sub>n (($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>r\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>r\<guillemotright>) 
      \<triangleleft> false \<triangleright> false))"
    by (metis)
  then have rhs': "... = U(true \<turnstile>\<^sub>n false)"
    by (simp)
  then have rhs'': "... = \<top>\<^sub>D"
    using ndesign_miracle by blast
  then show ?thesis
    using lhs rhs by auto
qed

lemma infsetsum_uni_c:
  assumes "finite A"
  assumes "\<forall>x \<in> A. P x = (cc::real)"
  shows "(\<Sum>\<^sub>aa \<in> A . P a) = (real (card A)) * cc"
proof (cases "A = {}")
  case True
  then show ?thesis
    by simp
next
  case False
  then show ?thesis 
    using assms 
    by (metis (full_types) assms(1) infsetsum_cong infsetsum_finite sum_constant)
qed

lemma card_set_comp_uniq:
  assumes "\<forall>x y. P x = P y \<longrightarrow> x = y"
  shows "card {P x | x . x < n} = n"
  apply (induct n)
  apply simp
proof -
  fix n::"nat"
  assume a1: "card {uu::'a. \<exists>x::nat. uu = P x \<and> x < n} = n"
  have f1: "{uu::'a. \<exists>x::nat. uu = P x \<and> x < Suc n} = {uu::'a. \<exists>x::nat. uu = P x \<and> (x < n \<or> x = n)}"
    by (simp add: less_Suc_eq)
  then have f2: "... = {uu::'a. \<exists>x::nat. uu = P x \<and> (x < n)} \<union> 
    {uu::'a. \<exists>x::nat. uu = P x \<and> (x = n)}"
    by auto
  have f3: "card {uu::'a. \<exists>x::nat. uu = P x \<and> x < Suc n}
    = card ({uu::'a. \<exists>x::nat. uu = P x \<and> (x < n)} \<union> 
    {uu::'a. \<exists>x::nat. uu = P x \<and> (x = n)})"
    using f1 f2 by auto
  have f4: "... = card {uu::'a. \<exists>x::nat. uu = P x \<and> (x < n)} 
    + card {uu::'a. \<exists>x::nat. uu = P x \<and> (x = n)}"
    apply (rule card_Un_disjoint)
    apply simp+
    using assms by auto
  have f5: "... = n + 1"
    using a1 by auto
  show "card {uu::'a. \<exists>x::nat. uu = P x \<and> x < Suc n} = Suc n"
    using a1 f1 f2 f4 by auto
qed

subsection \<open> Uniform selection (recursion) \<close>

definition unisel_rec :: "nat \<Rightarrow> (unisel_vars, unisel_vars) rel_pdes" where
"unisel_rec N =  (\<mu>\<^sub>N X \<bullet> (unisel_rec_body N X))"

lemma dcond_H1_H2_closed' [closure]:
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  shows "(P \<triangleleft> b \<triangleright>\<^sub>D Q) is \<^bold>H"
  proof -
    have "\<^bold>H (P \<triangleleft> b \<triangleright>\<^sub>D Q) = (pre\<^sub>D P \<triangleleft> b\<^sup>< \<triangleright> pre\<^sub>D Q) \<turnstile>\<^sub>r (post\<^sub>D P \<triangleleft> b\<^sup>< \<triangleright> post\<^sub>D Q)"
      by (simp add: H1_H2_eq_rdesign)
    then show ?thesis
      by (metis (no_types) H1_H2_eq_rdesign Healthy_def' aext_cond assms(1) assms(2) design_condr 
          rdesign_def)
  qed

lemma dcond_H1_H3_closed' [closure]:
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "(P \<triangleleft> b \<triangleright>\<^sub>D Q) is \<^bold>N"
  proof -
    have "\<^bold>N (P \<triangleleft> b \<triangleright>\<^sub>D Q) = (pre\<^sub>D P \<triangleleft> b\<^sup>< \<triangleright> pre\<^sub>D Q) \<turnstile>\<^sub>r (post\<^sub>D P \<triangleleft> b\<^sup>< \<triangleright> post\<^sub>D Q)"
      by (metis H1_H2_eq_rdesign H1_H3_right_unit H2_H3_absorb H3_def assms(1) assms(2) 
          dcond_H1_H2_closed design_post_condr design_pre_condr)
    then show ?thesis
      using assms(1) assms(2) dcond_H1_H2_closed by blast
  qed

subsubsection \<open> Invariant of recursion \<close>

lemma design_mu_N_refine_intro:
  assumes "$ok\<acute> \<sharp> C" "$ok\<acute> \<sharp> S" "(C \<turnstile> S) \<sqsubseteq> F(C \<turnstile> S)" "`C \<Rightarrow> (\<mu>\<^sub>N F \<Leftrightarrow> \<nu>\<^sub>N F)`" "(C \<turnstile> S) is \<^bold>N"
  shows "(C \<turnstile> S) \<sqsubseteq> \<mu>\<^sub>N F"
proof -
  from assms have "(C \<turnstile> S) \<sqsubseteq> \<nu>\<^sub>N F"
    by (simp add: assms design_is_H1_H2 ndes_theory.GFP_upperbound)
  with assms show ?thesis
    by (rel_auto, metis (no_types, lifting))
qed

definition unisel_inv ::
  "nat \<Rightarrow> (unisel_vars, unisel_vars) rel_pdes" where
"unisel_inv n = U(true \<turnstile>\<^sub>n 
    ((($c \<and> $i < (\<guillemotleft>n-1\<guillemotright>)) \<Rightarrow> 
      ((\<forall>j<\<guillemotleft>n\<guillemotright>-$i-1. $prob\<acute>($\<^bold>v\<lbrakk>\<guillemotleft>j\<guillemotright>+$i, false/$i, $c\<rbrakk>) = U(1/real (\<guillemotleft>n\<guillemotright>-$i))) \<and> 
      $prob\<acute>($\<^bold>v\<lbrakk>\<guillemotleft>n-1\<guillemotright>, true/$i, $c\<rbrakk>) = U(1/real (\<guillemotleft>n\<guillemotright>-$i)))
    ) \<and>
    (U(\<not>($c \<and> $i < (\<guillemotleft>n-1\<guillemotright>))) \<Rightarrow> ($prob\<acute>($\<^bold>v) = 1)))
  )"

lemma unisel_rec_inv:
  assumes "N \<ge> 1"
  shows "unisel_inv N \<sqsubseteq> unisel_rec N"
proof (cases "N=1")
  case True
  have f1: "\<forall>X. (unisel_rec_body N X) = II\<^sub>p"
    using True by (rel_auto)
  then have f2: "(\<mu>\<^sub>N X \<bullet> unisel_rec_body N X) = (\<mu>\<^sub>N X \<bullet> II\<^sub>p)"
    by simp
  have f3: "... = II\<^sub>p"
    by (metis ndes_theory.LFP_const ndesign_H1_H3 pemp_skip)
  then have f4: "unisel_rec N = II\<^sub>p"
    apply (simp add: unisel_rec_def)
    using f2 by auto
  have lhs: "unisel_inv N = II\<^sub>p"
    apply (simp add: unisel_inv_def pemp_skip)
    using True by (rel_auto)
  then show ?thesis
    by (simp add: f4)
next
  case False
  then have F: "N > 1"
    using assms by linarith
  then show ?thesis
    apply (simp add: unisel_rec_def unisel_inv_def)
    \<comment> \<open> Actually, (N - i) is not the variant as it is not always guaranteed to decrease. Sometime, 
    it just sets c to false and make i equal. \<close>
    apply (rule ndesign_mu_wf_refine_intro''[where e="U((\<guillemotleft>N\<guillemotright> - &i - (0 \<triangleleft> &c \<triangleright> 1)))" and R="{(x, y). x < y}"])
    apply (simp_all add: wf closure)
    apply (simp add: cond_mono kleisli_left_mono seqr_mono)
    apply (simp add: Pi_def)
    apply (clarify)
    apply (rule dcond_H1_H3_closed')
    apply (rule seq_r_H1_H3_closed)
    apply (simp add: unisel_rec_body_pchoice_simp')
    apply (rel_auto)
    using kleisli_left_N apply blast
    apply (simp add: ndesign_H1_H3 pemp_skip)
    apply (simp add: unisel_rec_body_pchoice_simp')
    apply (ndes_simp)
    apply (simp add: kleisli_lift_alt_def kleisli_lift2'_def)
    apply (simp add: upred_set_def)
    apply (rel_auto)
  proof -
    fix c\<^sub>v'::"bool" and ok\<^sub>v::"bool" and i\<^sub>v'::"nat" and ok\<^sub>v'::"bool" and 
      ok\<^sub>v''::"bool" and prob\<^sub>v'::"unisel_vars pmf"
    let ?sset = "{s::unisel_vars.
              (c\<^sub>v s \<longrightarrow> N - i\<^sub>v s < N - i\<^sub>v') \<and> (\<not> c\<^sub>v s \<longrightarrow> N - Suc (i\<^sub>v s) < N - i\<^sub>v')}"
    let ?s1 = "\<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = False\<rparr>"
    let ?s2 = "\<lparr>i\<^sub>v = Suc i\<^sub>v', c\<^sub>v = True\<rparr>"
    assume a1: "pmf prob\<^sub>v' \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = False\<rparr> = (1::real) / real (N - i\<^sub>v')"
    assume a2: "pmf prob\<^sub>v' \<lparr>i\<^sub>v = Suc i\<^sub>v', c\<^sub>v = True\<rparr> = (1::real) - (1::real) / real (N - i\<^sub>v')"
    assume a3: "i\<^sub>v' < N - Suc (0::nat)"
    assume a4: "(1::real) \<le> real (N - i\<^sub>v')"
    assume a5: "\<not>infsetsum (pmf prob\<^sub>v') ?sset = (1::real)"
    have f1: "?s1 \<in> ?sset"
      using a3 by auto
    have f2: "?s2 \<in> ?sset"
      using a3 by auto
    have f3: "infsetsum (pmf prob\<^sub>v') ?sset \<ge> infsetsum (pmf prob\<^sub>v') {?s1, ?s2}"
      apply (rule infsetsum_mono_neutral_left)
      apply simp
      apply blast
      apply simp
      using f1 f2 
      apply blast
      by simp
    have f4: "infsetsum (pmf prob\<^sub>v') {?s1, ?s2} = (pmf prob\<^sub>v' ?s1 + pmf prob\<^sub>v' ?s2)"
      by auto
    have f5: "infsetsum (pmf prob\<^sub>v') ?sset \<ge> 1"
      using f3 a1 a2 f4 by linarith
    have f6: "infsetsum (pmf prob\<^sub>v') ?sset = 1"
      using sum_pmf_eq_1 
      by (metis (mono_tags) UNIV_eq_I dual_order.antisym f5 mem_Collect_eq pmf_disj_leq)
    show "False"
      using f6 a4 a5 by blast
  next
    fix c\<^sub>v'::"bool" and ok\<^sub>v::"bool" and i\<^sub>v'::"nat" and prob\<^sub>v::"unisel_vars pmf" and
      ok\<^sub>v''::"bool" and prob\<^sub>v'::"unisel_vars pmf" and x::"nat"
    let ?sset = "{s::unisel_vars.
              (c\<^sub>v s \<longrightarrow> N - i\<^sub>v s < N - i\<^sub>v') \<and> (\<not> c\<^sub>v s \<longrightarrow> N - Suc (i\<^sub>v s) < N - i\<^sub>v')}"
    let ?s1 = "\<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = False\<rparr>"
    let ?s2 = "\<lparr>i\<^sub>v = Suc i\<^sub>v', c\<^sub>v = True\<rparr>"
    assume a1: "pmf prob\<^sub>v' \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = False\<rparr> = (1::real) / real (N - i\<^sub>v')"
    assume a2: "pmf prob\<^sub>v' \<lparr>i\<^sub>v = Suc i\<^sub>v', c\<^sub>v = True\<rparr> = (1::real) - (1::real) / real (N - i\<^sub>v')"
    assume a3: "i\<^sub>v' < N - Suc (0::nat)"
    assume a4: "\<not> infsetsum (pmf prob\<^sub>v') ?sset = (1::real)"
    have f1: "?s1 \<in> ?sset"
      using a3 by auto
    have f2: "?s2 \<in> ?sset"
      using a3 by auto
    have f3: "infsetsum (pmf prob\<^sub>v') ?sset \<ge> infsetsum (pmf prob\<^sub>v') {?s1, ?s2}"
      apply (rule infsetsum_mono_neutral_left)
      apply simp
      apply blast
      apply simp
      using f1 f2 
      apply blast
      by simp
    have f4: "infsetsum (pmf prob\<^sub>v') {?s1, ?s2} = (pmf prob\<^sub>v' ?s1 + pmf prob\<^sub>v' ?s2)"
      by auto
    have f5: "infsetsum (pmf prob\<^sub>v') ?sset \<ge> 1"
      using f3 a1 a2 f4 by linarith
    have f6: "infsetsum (pmf prob\<^sub>v') ?sset = 1"
      using sum_pmf_eq_1 
      by (metis (mono_tags) UNIV_eq_I dual_order.antisym f5 mem_Collect_eq pmf_disj_leq)
    show "False"
      using f6 a4 by blast
  next
    fix c\<^sub>v'::"bool" and ok\<^sub>v::"bool" and i\<^sub>v'::"nat" and prob\<^sub>v::"unisel_vars pmf" and
      ok\<^sub>v''::"bool" and prob\<^sub>v'::"unisel_vars pmf"
    let ?sset = "{s::unisel_vars.
              (c\<^sub>v s \<longrightarrow> N - i\<^sub>v s < N - i\<^sub>v') \<and> (\<not> c\<^sub>v s \<longrightarrow> N - Suc (i\<^sub>v s) < N - i\<^sub>v')}"
    let ?s1 = "\<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = False\<rparr>"
    let ?s2 = "\<lparr>i\<^sub>v = Suc i\<^sub>v', c\<^sub>v = True\<rparr>"
    assume a1: "pmf prob\<^sub>v' \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = False\<rparr> = (1::real) / real (N - i\<^sub>v')"
    assume a2: "pmf prob\<^sub>v' \<lparr>i\<^sub>v = Suc i\<^sub>v', c\<^sub>v = True\<rparr> = (1::real) - (1::real) / real (N - i\<^sub>v')"
    assume a3: "i\<^sub>v' < N - Suc 0"
    assume a4: "\<not> infsetsum (pmf prob\<^sub>v') ?sset = (1::real)"
    have f1: "?s1 \<in> ?sset"
      using a3 by auto
    have f2: "?s2 \<in> ?sset"
      using a3 by auto
    have f3: "infsetsum (pmf prob\<^sub>v') ?sset \<ge> infsetsum (pmf prob\<^sub>v') {?s1, ?s2}"
      apply (rule infsetsum_mono_neutral_left)
      apply simp
      apply blast
      apply simp
      using f1 f2 
      apply blast
      by simp
    have f4: "infsetsum (pmf prob\<^sub>v') {?s1, ?s2} = (pmf prob\<^sub>v' ?s1 + pmf prob\<^sub>v' ?s2)"
      by auto
    have f5: "infsetsum (pmf prob\<^sub>v') ?sset \<ge> 1"
      using f3 a1 a2 f4 by linarith
    have f6: "infsetsum (pmf prob\<^sub>v') ?sset = 1"
      using sum_pmf_eq_1 
      by (metis (mono_tags) UNIV_eq_I dual_order.antisym f5 mem_Collect_eq pmf_disj_leq)
    show "False"
      using f6 a4 by blast
  next
    fix c\<^sub>v::"bool" and ok\<^sub>v::"bool" and i\<^sub>v::"nat" and ok\<^sub>v'::"bool" and prob\<^sub>v::"unisel_vars pmf" and
      ok\<^sub>v''::"bool" and prob\<^sub>v'::"unisel_vars pmf" and x::"unisel_vars \<Rightarrow> unisel_vars pmf" and xa::"nat"
    let ?s1 = "\<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr>"
    let ?s2 = "\<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>"
    let ?p_s1 = "(1::real) / real (N - i\<^sub>v)"
    let ?p_s2 = "(1::real) - (1::real) / real (N - i\<^sub>v)"
    assume a1: "i\<^sub>v < N - Suc 0"
    assume a2: "(1::real) \<le> real (N - i\<^sub>v)"
    assume a3: "pmf prob\<^sub>v' \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr> = (1::real) / real (N - i\<^sub>v)"
    assume a4: "pmf prob\<^sub>v' \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr> = (1::real) - (1::real) / real (N - i\<^sub>v)"
    assume a5: "\<forall>(i\<^sub>v::nat) c\<^sub>v::bool.
            pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr> =
            (\<Sum>\<^sub>aa::unisel_vars. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr>)"
    assume a6: "\<forall>(i\<^sub>v'::nat) c\<^sub>v::bool.
            (0::real) < pmf prob\<^sub>v' \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = c\<^sub>v\<rparr> \<longrightarrow>
            (\<forall>prob\<^sub>v::unisel_vars pmf.
                c\<^sub>v \<and>
                N - i\<^sub>v' < N - i\<^sub>v \<and>
                (i\<^sub>v' < N - Suc (0::nat) \<longrightarrow>
                 (\<forall>x<N - Suc i\<^sub>v'. pmf prob\<^sub>v \<lparr>i\<^sub>v = x + i\<^sub>v', c\<^sub>v = False\<rparr> = (1::real) / real (N - i\<^sub>v')) \<and>
                 pmf prob\<^sub>v \<lparr>i\<^sub>v = N - Suc (0::nat), c\<^sub>v = True\<rparr> = (1::real) / real (N - i\<^sub>v')) \<and>
                (i\<^sub>v' < N - Suc (0::nat) \<or> pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = True\<rparr> = (1::real)) \<or>
                \<not> c\<^sub>v \<and> N - Suc i\<^sub>v' < N - i\<^sub>v \<and> pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = False\<rparr> = (1::real) \<or>
                (\<exists>(i\<^sub>v::nat) c\<^sub>v'::bool.
                    \<not> pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v'\<rparr> =
                       pmf (x \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = c\<^sub>v\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v'\<rparr>))"
    assume a7: "xa < N - Suc i\<^sub>v"
    assume a8: "\<not> (\<Sum>\<^sub>aa::unisel_vars. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = xa + i\<^sub>v, c\<^sub>v = False\<rparr>) =
            (1::real) / real (N - i\<^sub>v)"
  
    have f1: "(\<Sum>\<^sub>aa::unisel_vars. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = xa + i\<^sub>v, c\<^sub>v = False\<rparr>)
                 = (1::real) / real (N - i\<^sub>v)"
    proof -
      have a6': "\<forall>(i\<^sub>v'::nat) c\<^sub>v::bool.
          (0::real) < pmf prob\<^sub>v' \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = c\<^sub>v\<rparr> \<longrightarrow>
          (
              c\<^sub>v \<and>
              N - i\<^sub>v' < N - i\<^sub>v \<and>
              (i\<^sub>v' < N - Suc 0 \<longrightarrow>
               (\<forall>xx<N - Suc i\<^sub>v'. pmf (x \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = c\<^sub>v\<rparr>) \<lparr>i\<^sub>v = xx + i\<^sub>v', c\<^sub>v = False\<rparr> = 
                      (1::real) / (real (N - i\<^sub>v'))) \<and>
               pmf (x \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = c\<^sub>v\<rparr>) \<lparr>i\<^sub>v = N - Suc 0, c\<^sub>v = True\<rparr> = (1::real) / (real (N - i\<^sub>v'))) \<and>
              (i\<^sub>v' < N - Suc (0::nat) \<or> pmf (x \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = c\<^sub>v\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = True\<rparr> = (1::real)) \<or>
              \<not> c\<^sub>v \<and> N - Suc i\<^sub>v' < N - i\<^sub>v \<and> pmf (x \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = c\<^sub>v\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = False\<rparr> = (1::real)
          )"
        using a6 by blast
      (* *)
      have f10: "pmf (x ?s1) ?s1 = (1::real)"
        using a3 a6' a7 by force
      have f10': "xa > 0 \<longrightarrow> pmf (x ?s1) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr> = (0::real)"
        apply (auto)
        apply (rule pmf_not_the_one_is_zero[where xa="\<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr>"])
        using f10 apply simp by simp
       \<comment> \<open> From s1, terminate is 1 and others are 0 \<close>
      have f10'': "pmf (x ?s1) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr> = 
        (if xa = 0 then (1::real) else (0::real))"
        using f10 f10' by simp
  
      have Fi': "Suc i\<^sub>v < N"
        using a1 by simp
      have Fi'': "N - Suc i\<^sub>v < N - i\<^sub>v"
        using Fi' Suc_lessD diff_less_mono2 by blast
      have a6'': "(0::real) < pmf prob\<^sub>v' \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr> \<longrightarrow>
            (True \<and>
              N - Suc i\<^sub>v < N - i\<^sub>v \<and>
              (Suc i\<^sub>v < N - Suc 0 \<longrightarrow>
               (\<forall>xx<N - Suc (Suc i\<^sub>v). pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = xx + Suc i\<^sub>v, c\<^sub>v = False\<rparr> 
                = (1::real) / (real (N - Suc i\<^sub>v))) \<and>
               pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = N - Suc 0, c\<^sub>v = True\<rparr> 
                = (1::real) / (real (N - Suc i\<^sub>v))) \<and>
              (Suc i\<^sub>v < N - Suc (0::nat) \<or> pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr> = (1::real)))"
        using a6'
        by blast
      
      have a6''': "(Suc i\<^sub>v < N - Suc 0 \<longrightarrow> (
         (\<forall>xx<N - Suc (Suc i\<^sub>v). pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = xx + Suc i\<^sub>v, c\<^sub>v = False\<rparr> 
          = (1::real) / (real (N - Suc i\<^sub>v))) \<and>
         pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = N - Suc 0, c\<^sub>v = True\<rparr> 
          = (1::real) / (real (N - Suc i\<^sub>v)))) \<and>
       (Suc i\<^sub>v < N - Suc (0::nat) \<or> pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr> = (1::real))"
        using a6'' Fi' Fi'' a4 by auto
  
      have a6'''': "((
         (\<forall>xx<N - Suc (Suc i\<^sub>v). pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = xx + Suc i\<^sub>v, c\<^sub>v = False\<rparr> 
          = (1::real) / (real (N - Suc i\<^sub>v))) \<and>
         pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = N - Suc 0, c\<^sub>v = True\<rparr> 
          = (1::real) / (real (N - Suc i\<^sub>v))))"
        using a6''' Fi' Fi'' a4 
        by (metis One_nat_def Suc_lessI a1 assms diff_diff_cancel diff_self_eq_0 div_by_1 
            le_add_diff_inverse not_less0 of_nat_1 plus_1_eq_Suc)
  
      have f11: "(\<Sum>\<^sub>aa::unisel_vars\<in>
          {\<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> |xx. xx < N - Suc (Suc i\<^sub>v)} \<union> {\<lparr>i\<^sub>v = N - Suc 0, c\<^sub>v = True\<rparr>}. 
          pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) a) = 
        (\<Sum>\<^sub>aa::unisel_vars\<in> {\<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> |xx. xx < N - Suc (Suc i\<^sub>v)}. 
          pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) a)
      + (\<Sum>\<^sub>aa::unisel_vars\<in> {\<lparr>i\<^sub>v = N - Suc 0, c\<^sub>v = True\<rparr>}. pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) a)"
        unfolding infsetsum_altdef abs_summable_on_altdef
        apply (subst set_integral_Un, auto)
        using abs_summable_on_altdef apply fastforce
        using abs_summable_on_altdef by blast
      then have f12: "... = (\<Sum>\<^sub>aa::unisel_vars\<in> {\<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> |xx. xx < N - Suc (Suc i\<^sub>v)}. 
          pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) a) 
          + (1::real) / (real (N - Suc i\<^sub>v))"
        using a6'''' by (smt measure_pmf_conv_infsetsum pmf.rep_eq)
  
      (* Sum of (pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr>) *)
      have f13: "
        ((\<Sum>\<^sub>aa::unisel_vars\<in> {\<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> |xx. xx < N - Suc (Suc i\<^sub>v)}. 
          pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) a) 
        = ((1::real) / (real (N - Suc i\<^sub>v)))* (N - Suc (Suc i\<^sub>v)))"
        proof -
          have f1: "\<forall>a \<in> {\<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> |xx. xx <  N - Suc (Suc i\<^sub>v)}. 
              pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) a = ((1::real) / (real (N - Suc i\<^sub>v)))"
            using a6'''' by (smt add.commute mem_Collect_eq)
          have f2: "card {\<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> |xx. xx <  N - Suc (Suc i\<^sub>v)} =  N - Suc (Suc i\<^sub>v)"
            apply (rule card_set_comp_uniq)
            by auto
          show ?thesis
            apply (subst infsetsum_uni_c[where cc="((1::real) / (real (N - Suc i\<^sub>v)))"])
            apply simp
            using f1 apply blast
            using f2 by simp
        qed
      have f14: "(\<Sum>\<^sub>aa::unisel_vars\<in>
        {\<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> |xx. xx < N - Suc (Suc i\<^sub>v)} \<union> {\<lparr>i\<^sub>v = N - Suc 0, c\<^sub>v = True\<rparr>}. 
        pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) a) = 
        ((1::real) / (real (N - Suc i\<^sub>v)))* (N - Suc (Suc i\<^sub>v)) + 
        (1::real) / (real (N - Suc i\<^sub>v))"
        using f11 f12 f13 by simp
      have f15: "... = 1"
        by (metis Fi' Suc_diff_Suc add.commute add_divide_distrib diff_is_0_eq diff_zero divide_self 
            le_add1 mult.left_neutral n_not_Suc_n of_nat_Suc of_nat_eq_0_iff times_divide_eq_left)
      have f_not_in1: "\<not> \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr> \<in> 
        {\<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> |xx. xx < N - Suc (Suc i\<^sub>v)} \<union> {\<lparr>i\<^sub>v = N - Suc 0, c\<^sub>v = True\<rparr>}"
        by simp
      have f16: "pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr> = (0::real)"
        apply (rule pmf_not_in_the_one_is_zero[where 
              A="{\<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> |xx. xx < N - Suc (Suc i\<^sub>v)} \<union> {\<lparr>i\<^sub>v = N - Suc 0, c\<^sub>v = True\<rparr>}"])
        using f14 f15 apply simp
        using f_not_in1 by blast
      \<comment> \<open> Calculate pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr> \<close>
      have f17: "pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr> 
            = (if xa = 0 then 0 else (1::real) / (real (N - Suc i\<^sub>v)))"
        proof (cases "xa = 0")
          case True
          then show ?thesis
            apply (simp)
            using f16 by blast
        next
          case False
          have f111: "pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr> =
            pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = Suc i\<^sub>v + xa - 1, c\<^sub>v = False\<rparr>"
            using False by simp
          have f112: "xa - 1 < N - Suc (Suc i\<^sub>v)"
            using a7 False by linarith
          have "pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = Suc i\<^sub>v + xa - 1, c\<^sub>v = False\<rparr>
            = (1::real) / (real (N - Suc i\<^sub>v))"
            using a7 a6'''' False f112
            by (metis Nat.add_diff_assoc One_nat_def Suc_leI add.commute neq0_conv)
          then show ?thesis 
            using a5 a6'''' by (simp add: False)
        qed
      have prob\<^sub>v_1_1: "infsetsum (pmf prob\<^sub>v') {\<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr>, \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>} 
        = (pmf prob\<^sub>v' \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr>) + (pmf prob\<^sub>v' \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>)"
        by auto
      have prob\<^sub>v_1_2: "... = (1::real)"
        using a3 a4 by simp
      have not_s1_s2_is_0: "\<forall>a. a \<notin> {?s1, ?s2} \<longrightarrow> pmf prob\<^sub>v' a = 0"
        apply (auto)
        apply (rule pmf_not_in_the_one_is_zero[where A="{?s1, ?s2}"])
        apply (simp add: prob\<^sub>v_1_2)
        by simp
      have s1_s2_all: "{?s1,?s2}\<union>({x. x \<notin> {?s1,?s2}}) = UNIV"
        by blast
      have pmf_x_simp: "\<forall>a. (if a = ?s1 
             then ?p_s1 \<cdot> pmf (x ?s1) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>
             else (if a = ?s2 
                   then ?p_s2 \<cdot> pmf (x ?s2) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>
                   else pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>))
          = (if a = ?s1 
             then ?p_s1 \<cdot> pmf (x ?s1) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>
             else (if a = ?s2 
                   then ?p_s2 \<cdot> pmf (x ?s2) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>
                   else 0 \<cdot> pmf (x a) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>))"
        apply (auto)
        using not_s1_s2_is_0 by auto
      then have pmf_x_simp': "(\<lambda>a. (if a = ?s1 
             then ?p_s1 \<cdot> pmf (x ?s1) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>
             else (if a = ?s2 
                   then ?p_s2 \<cdot> pmf (x ?s2) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>
                   else pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>)))
        = (\<lambda>a. (if a = ?s1 
             then ?p_s1 \<cdot> pmf (x ?s1) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>
             else (if a = ?s2 
                   then ?p_s2 \<cdot> pmf (x ?s2) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>
                   else 0 \<cdot> pmf (x a) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>)))"
        by blast
      \<comment> \<open> Steps towards the goal: 
          Hard to deal with @{text "pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>"} directly,
          but we can split it into conditional expression.
         \<close>
      have f18: "(\<Sum>\<^sub>aa::unisel_vars. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>)
        = (\<Sum>\<^sub>aa::unisel_vars. 
            (if a = ?s1 
             then pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>
             else (if a = ?s2 
                   then pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>
                   else pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>)))"
        by presburger
      have f18': "... = (\<Sum>\<^sub>aa::unisel_vars. 
            (if a = ?s1 
             then ?p_s1 \<cdot> pmf (x ?s1) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>
             else (if a = ?s2 
                   then ?p_s2 \<cdot> pmf (x ?s2) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>
                   else pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>)))"
        using a3 a4
        by (metis (no_types, hide_lams))
      have f18'': "... = (\<Sum>\<^sub>aa::unisel_vars. 
            (if a = ?s1 
             then ?p_s1 \<cdot> pmf (x ?s1) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>
             else (if a = ?s2 
                   then ?p_s2 \<cdot> pmf (x ?s2) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>
                   else 0 \<cdot> pmf (x a) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>)))"
        using pmf_x_simp' by presburger
      have f18''': "... = (\<Sum>\<^sub>aa::unisel_vars. 
            (if a = ?s1 
             then ?p_s1 \<cdot> pmf (x ?s1) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>
             else (if a = ?s2 
                   then ?p_s2 \<cdot> pmf (x ?s2) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>
                   else 0)))"
        apply (subst mult_zero_left)
        by (simp)
      have f18'''': "... = (\<Sum>\<^sub>aa::unisel_vars\<in>{?s1,?s2}\<union>({x. x \<notin> {?s1,?s2}}). 
            (if a = ?s1 
             then ?p_s1 \<cdot> pmf (x ?s1) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>
             else (if a = ?s2 
                   then ?p_s2 \<cdot> pmf (x ?s2) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>
                   else 0)))"
        using s1_s2_all by simp
      \<comment> \<open> Substitute @{text "pmf (x ?s1) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>"} by f10'' and 
              @{text "pmf (x ?s2) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>"} by f17
         \<close>
      have f18''''': "... = (\<Sum>\<^sub>aa::unisel_vars\<in>{?s1,?s2}\<union>({x. x \<notin> {?s1,?s2}}). 
            (if a = ?s1 
             then ?p_s1 \<cdot> (if xa = 0 then (1::real) else (0::real))
             else (if a = ?s2 
                   then ?p_s2 \<cdot> (if xa = 0 then 0 else (1::real) /  (real (N - Suc i\<^sub>v)))
                   else 0)))"
        using f10'' f17 by presburger
      show ?thesis
        proof (cases "xa = 0")
          case True
          have f111: "(\<Sum>\<^sub>aa::unisel_vars. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>)
            = (\<Sum>\<^sub>aa::unisel_vars\<in>{?s1,?s2}\<union>({x. x \<notin> {?s1,?s2}}). 
            (if a = ?s1 
             then ?p_s1 \<cdot> (if xa = 0 then (1::real) else (0::real))
             else (if a = ?s2 
                   then ?p_s2 \<cdot> (if xa = 0 then 0 else (1::real) / (real (N - Suc i\<^sub>v)))
                   else 0)))"
            by (metis f18' f18'' f18''' f18''''' s1_s2_all)
          have f112: "... = (\<Sum>\<^sub>aa::unisel_vars\<in>{?s1,?s2}\<union>({x. x \<notin> {?s1,?s2}}). 
            (if a = ?s1 
             then ?p_s1 \<cdot> (1::real)
             else (if a = ?s2 then ?p_s2 \<cdot> (0::real) else 0)))"
            using True by simp
          have f113: "... = (\<Sum>\<^sub>aa::unisel_vars. 
            (if a = ?s1 then ?p_s1 else 0))"
            using s1_s2_all by (smt infsetsum_cong)
          have f114: "... = ?p_s1"
            apply (subst infsetsum_single)
            by simp
          then show ?thesis 
            proof -
              have "(\<Sum>\<^sub>au. pmf prob\<^sub>v' u \<cdot> pmf (x u) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>) = 1 / real (N - i\<^sub>v)"
                using f111 f112 f113 f114 by presburger
              then show ?thesis
                by (simp add: add.commute)
            qed
        next
          case False
          have p_s2': "?p_s2 = ((real (N - i\<^sub>v) - 1) / (real (N - i\<^sub>v)))"
            by (metis a2 diff_divide_distrib divide_self f10 not_le pmf_pos zero_neq_one)
          have f110: "(real (N - i\<^sub>v) - 1) = (real (N - Suc i\<^sub>v))"
            using a1 by linarith
          have f110': "(real (N - Suc i\<^sub>v)) > 0"
            using a1 by linarith
          have f111: "(\<Sum>\<^sub>aa::unisel_vars. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>)
            = (\<Sum>\<^sub>aa::unisel_vars\<in>{?s1,?s2}\<union>({x. x \<notin> {?s1,?s2}}). 
            (if a = ?s1 
             then ?p_s1 \<cdot> (if xa = 0 then (1::real) else (0::real))
             else (if a = ?s2 
                   then ?p_s2 \<cdot> (if xa = 0 then 0 else (1::real) / ((real (N - Suc i\<^sub>v))))
                   else 0)))"
            by (metis f18' f18'' f18''' f18''''' s1_s2_all)
          have f112: "... = (\<Sum>\<^sub>aa::unisel_vars\<in>{?s1,?s2}\<union>({x. x \<notin> {?s1,?s2}}). 
            (if a = ?s1 
             then ?p_s1 \<cdot> (0::real)
             else (if a = ?s2 then ?p_s2 \<cdot> ((1::real) / ((real (N - Suc i\<^sub>v)))) else 0)))"
            using False by simp
          have f113: "... = (\<Sum>\<^sub>aa::unisel_vars. 
            (if a = ?s2 then ?p_s2 \<cdot> ((1::real) / ((real (N - Suc i\<^sub>v)))) else 0))"
            using s1_s2_all
            by (smt infsetsum_cong unisel_vars.iffs)
          have f114: "... = ?p_s2 \<cdot> ((1::real) / ((real (N - Suc i\<^sub>v))))"
            apply (subst infsetsum_single)
            by simp
          have f115: "... = ((real (N - i\<^sub>v) - 1) / (real (N - i\<^sub>v))) \<cdot>
              ((1::real) / (((real (N - Suc i\<^sub>v)))))"
            by (simp add: p_s2')
          have f116: "(real (N - i\<^sub>v) - 1) = ((real (N - Suc i\<^sub>v)))"
            using f110 by blast
          then show ?thesis 
            using f110 f111 f112 f113 f114 f115 f110'
            by (simp add: add.commute)
        qed
      qed
    show "False"
      using a8 f1 by blast
  next
    fix c\<^sub>v::"bool" and ok\<^sub>v::"bool" and i\<^sub>v::"nat" and ok\<^sub>v'::"bool" and prob\<^sub>v::"unisel_vars pmf" and
      ok\<^sub>v''::"bool" and prob\<^sub>v'::"unisel_vars pmf" and x::"unisel_vars \<Rightarrow> unisel_vars pmf" and xa::"nat"
    let ?s1 = "\<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr>"
    let ?s2 = "\<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>"
    let ?p_s1 = "(1::real) / real (N - i\<^sub>v)"
    let ?p_s2 = "(1::real) - (1::real) / real (N - i\<^sub>v)"
    let ?s' = "\<lparr>i\<^sub>v = N - Suc 0, c\<^sub>v = True\<rparr>"
    assume a1: "i\<^sub>v < N - Suc 0"
    assume a2: "(1::real) \<le> real (N - i\<^sub>v)"
    assume a3: "pmf prob\<^sub>v' \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr> = (1::real) / real (N - i\<^sub>v)"
    assume a4: "pmf prob\<^sub>v' \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr> = (1::real) - (1::real) / real (N - i\<^sub>v)"
    assume a5: "\<forall>(i\<^sub>v::nat) c\<^sub>v::bool.
            pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr> =
            (\<Sum>\<^sub>aa::unisel_vars. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr>)"
    assume a6: "\<forall>(i\<^sub>v'::nat) c\<^sub>v::bool.
            (0::real) < pmf prob\<^sub>v' \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = c\<^sub>v\<rparr> \<longrightarrow>
            (\<forall>prob\<^sub>v::unisel_vars pmf.
                c\<^sub>v \<and>
                N - i\<^sub>v' < N - i\<^sub>v \<and>
                (i\<^sub>v' < N - Suc (0::nat) \<longrightarrow>
                 (\<forall>x<N - Suc i\<^sub>v'. pmf prob\<^sub>v \<lparr>i\<^sub>v = x + i\<^sub>v', c\<^sub>v = False\<rparr> = (1::real) / real (N - i\<^sub>v')) \<and>
                 pmf prob\<^sub>v \<lparr>i\<^sub>v = N - Suc (0::nat), c\<^sub>v = True\<rparr> = (1::real) / real (N - i\<^sub>v')) \<and>
                (i\<^sub>v' < N - Suc (0::nat) \<or> pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = True\<rparr> = (1::real)) \<or>
                \<not> c\<^sub>v \<and> N - Suc i\<^sub>v' < N - i\<^sub>v \<and> pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = False\<rparr> = (1::real) \<or>
                (\<exists>(i\<^sub>v::nat) c\<^sub>v'::bool.
                    \<not> pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v'\<rparr> = pmf (x \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = c\<^sub>v\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v'\<rparr>))"
    assume a7: "i\<^sub>v < N - Suc (0::nat)"
    assume a8: "\<not> (\<Sum>\<^sub>aa::unisel_vars. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = N - Suc (0::nat), c\<^sub>v = True\<rparr>) =
            (1::real) / real (N - i\<^sub>v)"
  
    have a6': "\<forall>(i\<^sub>v'::nat) c\<^sub>v::bool.
        (0::real) < pmf prob\<^sub>v' \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = c\<^sub>v\<rparr> \<longrightarrow>
        (
            c\<^sub>v \<and>
            N - i\<^sub>v' < N - i\<^sub>v \<and>
            (i\<^sub>v' < N - Suc 0 \<longrightarrow>
             (\<forall>xx<N - Suc i\<^sub>v'. pmf (x \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = c\<^sub>v\<rparr>) \<lparr>i\<^sub>v = xx + i\<^sub>v', c\<^sub>v = False\<rparr> = 
                    (1::real) / (real (N - i\<^sub>v'))) \<and>
             pmf (x \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = c\<^sub>v\<rparr>) \<lparr>i\<^sub>v = N - Suc 0, c\<^sub>v = True\<rparr> = (1::real) / (real (N - i\<^sub>v'))) \<and>
            (i\<^sub>v' < N - Suc (0::nat) \<or> pmf (x \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = c\<^sub>v\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = True\<rparr> = (1::real)) \<or>
            \<not> c\<^sub>v \<and> N - Suc i\<^sub>v' < N - i\<^sub>v \<and> pmf (x \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = c\<^sub>v\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = False\<rparr> = (1::real)
        )"
      using a6 by blast
    have a6'': "(0::real) < pmf prob\<^sub>v' \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr> \<longrightarrow>
          (True \<and>
            N - Suc i\<^sub>v < N - i\<^sub>v \<and>
            (Suc i\<^sub>v < N - Suc 0 \<longrightarrow>
             (\<forall>xx<N - Suc (Suc i\<^sub>v). pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = xx + Suc i\<^sub>v, c\<^sub>v = False\<rparr> 
              = (1::real) / (real (N - Suc i\<^sub>v))) \<and>
             pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = N - Suc 0, c\<^sub>v = True\<rparr> 
              = (1::real) / (real (N - Suc i\<^sub>v))) \<and>
            (Suc i\<^sub>v < N - Suc (0::nat) \<or> pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr> = (1::real)))"
      using a6'
      by blast
    
    have a6''': "(Suc i\<^sub>v < N - Suc 0 \<longrightarrow> (
       (\<forall>xx<N - Suc (Suc i\<^sub>v). pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = xx + Suc i\<^sub>v, c\<^sub>v = False\<rparr> 
        = (1::real) / (real (N - Suc i\<^sub>v))) \<and>
       pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = N - Suc 0, c\<^sub>v = True\<rparr> 
        = (1::real) / (real (N - Suc i\<^sub>v)))) \<and>
     (Suc i\<^sub>v < N - Suc (0::nat) \<or> pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr> = (1::real))"
      using a6'' a4 a7 by auto
  
    have a6'''': "((
       (\<forall>xx<N - Suc (Suc i\<^sub>v). pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = xx + Suc i\<^sub>v, c\<^sub>v = False\<rparr> 
        = (1::real) / (real (N - Suc i\<^sub>v))) \<and>
       pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = N - Suc 0, c\<^sub>v = True\<rparr> 
        = (1::real) / (real (N - Suc i\<^sub>v))))"
      using a6''' a4 
      by (metis One_nat_def Suc_lessI a7 assms diff_diff_cancel diff_self_eq_0 div_by_1 
          le_add_diff_inverse not_less0 of_nat_1 plus_1_eq_Suc)
  
    have f1: "(\<Sum>\<^sub>aa::unisel_vars. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v =  N - Suc (0::nat), c\<^sub>v = True\<rparr>) =
      (1::real) / real (N - i\<^sub>v)"
      proof -
        have f10: "(pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = N - Suc 0, c\<^sub>v = True\<rparr> 
                        = (1::real) / (real (N - Suc i\<^sub>v)))"
          using a6'''' by simp
  
        have f11: "pmf (x \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr> = (1::real)"
          using a6' a3 using a2 by force
          
        have f11': "pmf (x ?s1) ?s' = (0::real)"
          apply (rule pmf_not_the_one_is_zero[where xa="\<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr>"])
          using f11 apply simp
          by simp
  
        have f12: "pmf (x ?s2) ?s' = (1::real) / (real (N - Suc i\<^sub>v))"
          using a6'''' by simp
  
        have prob\<^sub>v_1_1: "infsetsum (pmf prob\<^sub>v') {\<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr>, \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>} 
          = (pmf prob\<^sub>v' \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr>) + (pmf prob\<^sub>v' \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>)"
          by auto
        have prob\<^sub>v_1_2: "... = (1::real)"
          using a3 a4 by simp
        have not_s1_s2_is_0: "\<forall>a. a \<notin> {?s1, ?s2} \<longrightarrow> pmf prob\<^sub>v' a = 0"
          apply (auto)
          apply (rule pmf_not_in_the_one_is_zero[where A="{?s1, ?s2}"])
          apply (simp add: prob\<^sub>v_1_2)
          by simp
  
        have pmf_x_simp: "\<forall>a. (if a = ?s1 
               then ?p_s1 \<cdot> pmf (x ?s1) ?s'
               else (if a = ?s2 
                     then ?p_s2 \<cdot> pmf (x ?s2) ?s'
                     else pmf prob\<^sub>v' a \<cdot> pmf (x a) ?s'))
            = (if a = ?s1 
               then ?p_s1 \<cdot> pmf (x ?s1) ?s'
               else (if a = ?s2 
                     then ?p_s2 \<cdot> pmf (x ?s2) ?s'
                     else 0 \<cdot> pmf (x a) ?s'))"
          apply (auto)
          using not_s1_s2_is_0 by auto
        then have pmf_x_simp': "(\<lambda>a. (if a = ?s1 
               then ?p_s1 \<cdot> pmf (x ?s1) ?s'
               else (if a = ?s2 
                     then ?p_s2 \<cdot> pmf (x ?s2) ?s'
                     else pmf prob\<^sub>v' a \<cdot> pmf (x a) ?s')))
          = (\<lambda>a. (if a = ?s1 
               then ?p_s1 \<cdot> pmf (x ?s1) ?s'
               else (if a = ?s2 
                     then ?p_s2 \<cdot> pmf (x ?s2) ?s'
                     else 0 \<cdot> pmf (x a) ?s')))"
          by blast
        have f13: "(\<Sum>\<^sub>aa::unisel_vars. pmf prob\<^sub>v' a \<cdot> pmf (x a) ?s')
          = (\<Sum>\<^sub>aa::unisel_vars. 
              (if a = ?s1 
               then pmf prob\<^sub>v' a \<cdot> pmf (x a) ?s'
               else (if a = ?s2 
                     then pmf prob\<^sub>v' a \<cdot> pmf (x a) ?s'
                     else pmf prob\<^sub>v' a \<cdot> pmf (x a) ?s')))"
          by presburger
        have f13': "... = (\<Sum>\<^sub>aa::unisel_vars. 
              (if a = ?s1 
               then ?p_s1 \<cdot> pmf (x ?s1) ?s'
               else (if a = ?s2 
                     then ?p_s2 \<cdot> pmf (x ?s2) ?s'
                     else pmf prob\<^sub>v' a \<cdot> pmf (x a) ?s')))"
          using a3 a4
          by (metis (no_types, hide_lams))
        have f13'': "... = (\<Sum>\<^sub>aa::unisel_vars. 
              (if a = ?s1 
               then ?p_s1 \<cdot> pmf (x ?s1) ?s'
               else (if a = ?s2 
                     then ?p_s2 \<cdot> pmf (x ?s2) ?s'
                     else 0 \<cdot> pmf (x a) ?s')))"
          using pmf_x_simp' by presburger
        have f13''': "... = (\<Sum>\<^sub>aa::unisel_vars. 
              (if a = ?s1 
               then ?p_s1 \<cdot> pmf (x ?s1) ?s'
               else (if a = ?s2 
                     then ?p_s2 \<cdot> pmf (x ?s2) ?s'
                     else 0)))"
          apply (subst mult_zero_left)
          by (simp)
        have f13'''': "... = (\<Sum>\<^sub>aa::unisel_vars. 
              (if a = ?s1 
               then ?p_s1 \<cdot> (0::real)
               else (if a = ?s2 
                     then ?p_s2 \<cdot> ((1::real) / (real (N - Suc i\<^sub>v)))
                     else 0)))"
          using f11' f12 by presburger
        have f13''''': "... = (\<Sum>\<^sub>aa::unisel_vars.
              (if a = ?s2 
               then ?p_s2 \<cdot> ((1::real) / (real (N - Suc i\<^sub>v)))
               else 0))"
          by (metis mult_zero_right unisel_vars.ext_inject)
        have f13'''''': "... = ?p_s2 \<cdot> ((1::real) / (real (N - Suc i\<^sub>v)))"
          apply (subst infsetsum_single)
          by simp
        have p_s2_simp: "?p_s2 = (real (N - i\<^sub>v) - 1) / (real (N - i\<^sub>v))"
           by (metis (no_types, hide_lams) a2 add_divide_distrib add_uminus_conv_diff 
               divide_minus_left divide_self linorder_neqE_linordered_idom not_le of_nat_1 
               of_nat_less_0_iff zero_neq_one)
        have p_s'_simp': "(real (N - i\<^sub>v) - 1) = (real (N - Suc i\<^sub>v))"
          using a1 by linarith
        have p_s2_s'_simp: "?p_s2 \<cdot> ((1::real) / (real (N - Suc i\<^sub>v)))
          = (1::real) / (real (N - i\<^sub>v))"
          using p_s'_simp' p_s2_simp a7 by force
        show ?thesis
          using f13 f13' f13'' f13''' f13'''' f13''''' f13'''''' p_s2_s'_simp by auto
      qed
    show "False"
      using f1 a8 by auto
  qed
qed

subsubsection \<open> Contract \<close>
lemma unisel'_contract:
  assumes "N \<ge> 1"
  shows "U(true \<turnstile>\<^sub>n 
    (
      ((\<forall>j<\<guillemotleft>N\<guillemotright>-1. $prob\<acute>($\<^bold>v\<lbrakk>\<guillemotleft>j\<guillemotright>, false/$i, $c\<rbrakk>) = U(1/real (\<guillemotleft>N\<guillemotright>))) \<and> 
      $prob\<acute>($\<^bold>v\<lbrakk>\<guillemotleft>N-1\<guillemotright>, true/$i, $c\<rbrakk>) = U(1/real (\<guillemotleft>N\<guillemotright>)))
    )) \<sqsubseteq> (i :=\<^sub>D 0 ;; c :=\<^sub>D true ;; unisel_rec N)"
proof -
  have f1: "i :=\<^sub>D 0 ;; c :=\<^sub>D true ;; unisel_inv N \<sqsubseteq> (i :=\<^sub>D 0 ;; c :=\<^sub>D true ;; unisel_rec N)"
    apply (rule seqr_mono, simp)
    apply (rule seqr_mono, simp)
    using assms unisel_rec_inv by auto
  have f2: "i :=\<^sub>D 0 ;; c :=\<^sub>D true ;; unisel_inv N = U(true \<turnstile>\<^sub>n 
    (
      ((\<forall>j<\<guillemotleft>N\<guillemotright>-1. $prob\<acute>($\<^bold>v\<lbrakk>\<guillemotleft>j\<guillemotright>, false/$i, $c\<rbrakk>) = U(1/real (\<guillemotleft>N\<guillemotright>))) \<and> 
      $prob\<acute>($\<^bold>v\<lbrakk>\<guillemotleft>N-1\<guillemotright>, true/$i, $c\<rbrakk>) = U(1/real (\<guillemotleft>N\<guillemotright>)))
    ))"
    apply (simp add: unisel_inv_def)
    apply (rel_auto)
    using assms apply linarith+
    apply blast
    by (metis (mono_tags, hide_lams) assms diff_is_0_eq' diff_zero div_by_1 
        less_Suc0 less_asym linorder_neqE_nat not_less_zero 
        of_nat_1_eq_iff zero_less_Suc zero_less_diff zero_neq_one)
  show ?thesis
    using f1 f2 by auto
qed

end
