section \<open> (pmf) Laws \<close>

text \<open> This section presents many proved laws regarding pmf to facilitate proof of algebraic laws of 
probabilistic designs.\<close>

theory utp_prob_pmf_laws
  imports "UTP-Designs.utp_designs" 
          "HOL-Probability.Probability_Mass_Function"
          utp_prob_des
begin recall_syntax

subsection \<open> Laws \<close>

lemma sum_pmf_eq_1:
  fixes M::"'a pmf"
  shows "(\<Sum>\<^sub>a i::'a. pmf M i) = 1"
  by (simp add: infsetsum_pmf_eq_1)

lemma pmf_not_the_one_is_zero:
  fixes M::"'a pmf"
  assumes "pmf M xa = 1"
  assumes "xa \<noteq> xb"
  shows "pmf M xb = 0"
proof (rule ccontr)
  assume a1: "\<not> pmf M xb = (0::real)"
  have f0: "pmf M xb > 0"
    using a1 by simp
  have f1: "(\<Sum>\<^sub>a i\<in>{xa,xb}. pmf M i) = (pmf M xa + pmf M xb)"
    apply (simp add: infsetsum_def)
    by (simp add: assms(2) lebesgue_integral_count_space_finite)
  have f2: "(\<Sum>\<^sub>a i::'a. pmf M i) \<ge> (\<Sum>\<^sub>a i\<in>{xa,xb}. pmf M i)"
    by (metis measure_pmf.prob_le_1 measure_pmf_conv_infsetsum sum_pmf_eq_1)
  from f1 f2 have "(\<Sum>\<^sub>a i::'a. pmf M i) > 1"
    using assms(1) f0 by linarith
  then show "False"
    using sum_pmf_eq_1
    by (simp add: sum_pmf_eq_1)
qed

lemma pmf_not_in_the_one_is_zero:
  fixes M::"'a pmf"
  assumes "(\<Sum>\<^sub>axb::'a \<in> A. pmf M xb) = 1"
  assumes "xa \<notin> A"
  shows "pmf M xa = 0"
proof (rule ccontr)
  assume a1: "\<not> pmf M xa = (0::real)"
  have f0: "pmf M xa > 0"
    using a1 by simp
  have f1: "(\<Sum>\<^sub>a i\<in>A \<union> {xa}. pmf M i) = ((\<Sum>\<^sub>axb::'a \<in> A. pmf M xb) + (\<Sum>\<^sub>axb::'a \<in> {xa}. pmf M xb))"
    unfolding infsetsum_altdef abs_summable_on_altdef
    apply (subst set_integral_Un, auto)
    using abs_summable_on_altdef assms(2) apply fastforce
    using abs_summable_on_altdef apply blast
    using abs_summable_on_altdef by blast
  then have f2: "... = 1 + pmf M xa"
    using assms(1) by auto
  then have f3: "... > 1"
    using f0 by linarith
  then show "False"
    by (metis f1 f2 measure_pmf.prob_le_1 measure_pmf_conv_infsetsum not_le)
qed

lemma pmf_not_in_the_two_is_zero:
  fixes M::"'a pmf"
  assumes "a \<in> {0..1}"
  assumes "sa \<noteq> sb"
  assumes "pmf M sa = a"
  assumes "pmf M sb = 1 - a"
  assumes "sc \<notin> {sa, sb}"
  shows "pmf M sc = 0"
proof -
  have f1: "infsetsum (pmf M) {sa, sb} = infsetsum (pmf M) {sa} + infsetsum (pmf M) {sb}"
    by (simp add: assms(2))
  then have f2: "... = pmf M sa + pmf M sb"
    by simp
  then have f3: "... = 1"
    using assms(3) assms(4) by auto
  show ?thesis
    apply (rule pmf_not_in_the_one_is_zero[where A = "{sa, sb}"])
    using f1 f2 f3 apply linarith
    using assms(5) by auto
qed
    

lemma infsetsum_single:
  fixes y::'a
  shows "(\<Sum>\<^sub>axb::'a. (if xb = y then xa else 0)) = xa"
  proof -
    have "(\<Sum>\<^sub>axb::'a. (if xb = y then (xa) else 0)) = 
          (\<Sum>\<^sub>axb\<in>({y} \<union> {t. \<not>t=y}). (if xb = y then (xa) else 0))"
      proof -
        have "UNIV = {y} \<union> {a. \<not> a = y}"
          by blast
        then show ?thesis
          by presburger
      qed
    also have "... = (\<Sum>\<^sub>axb\<in>({y}). (if xb = y then (xa) else 0)) +
       (\<Sum>\<^sub>axb\<in>({t. \<not>t=y}). (if xb = y then (xa) else 0))"
      unfolding infsetsum_altdef abs_summable_on_altdef
      apply (subst set_integral_Un, auto)
      using abs_summable_on_altdef apply fastforce
      using abs_summable_on_altdef by (smt abs_summable_on_0 abs_summable_on_cong mem_Collect_eq)
    also have "... = (xa) + (\<Sum>\<^sub>axb\<in>({t. \<not>t=y}). (if xb = y then (xa) else 0))"
      by simp
    also have "... = (xa)"
      by (smt add_cancel_left_right infsetsum_all_0 mem_Collect_eq)
    then show ?thesis
      by (simp add: calculation)
  qed

lemma infsetsum_single':
  fixes xa::'a and y::'a
  shows "(\<Sum>\<^sub>axb::'a. (if xb = y then P(xa) else 0)) = P(xa)"
  by (simp add: infsetsum_single)

lemma pmf_sum_single:
  fixes prob\<^sub>v::"'a pmf"
  shows "(\<Sum>\<^sub>axb::'a. (if xb = xa then pmf prob\<^sub>v xa else 0)) = pmf prob\<^sub>v xa"
  by (simp add: infsetsum_single)

lemma infsetsum_two:
  assumes "ya \<noteq> yb"
  shows "(\<Sum>\<^sub>axb::'a. (if xb = ya then va else (if xb = yb then vb else 0))) = va + vb"
  proof -
    have "(\<Sum>\<^sub>axb::'a. (if xb = ya then va else (if xb = yb then vb else 0))) = 
          (\<Sum>\<^sub>axb\<in>({ya,yb} \<union> {t. \<not>t=ya \<and> \<not>t=yb}). 
      (if xb = ya then va else (if xb = yb then vb else 0)))"
      proof -
        have "UNIV = ({ya, yb} \<union> {t. \<not>t=ya \<and> \<not>t=yb})"
          by blast
        then show ?thesis
          by presburger
      qed
    also have "... = (\<Sum>\<^sub>axb\<in>({ya,yb}). (if xb = ya then va else (if xb = yb then vb else 0))) +
       (\<Sum>\<^sub>axb\<in>({t. \<not>t=ya \<and> \<not>t=yb}). (if xb = ya then va else (if xb = yb then vb else 0)))"
      unfolding infsetsum_altdef abs_summable_on_altdef
      apply (subst set_integral_Un, auto)
      using abs_summable_on_altdef apply fastforce
      using abs_summable_on_altdef by (smt abs_summable_on_0 abs_summable_on_cong mem_Collect_eq)
    also have "... = (\<Sum>\<^sub>axb\<in>({ya,yb}). (if xb = ya then va else (if xb = yb then vb else 0))) +
       0"
      by (smt infsetsum_all_0 mem_Collect_eq)
    also have "... = (\<Sum>\<^sub>axb\<in>({ya}). (if xb = ya then va else (if xb = yb then vb else 0))) + 
      (\<Sum>\<^sub>axb\<in>({yb}). (if xb = ya then va else (if xb = yb then vb else 0)))"
      apply (simp add: infsetsum_Un_disjoint)
      using assms by auto
    also have "... = va + vb"
      using assms by auto
    then show ?thesis
      by (simp add: calculation)
  qed

lemma infsetsum_two':
  assumes "xa \<noteq> xb"
  assumes "pmf M xa + pmf M xb = (1::real)"
  shows "(\<Sum>\<^sub>ax::'a. (pmf M x) \<cdot> (Q x)) = pmf M xa \<cdot> (Q xa) + pmf M xb \<cdot> (Q xb)"
proof -
  have f1: "\<forall>xc. xc \<notin> {xa, xb} \<longrightarrow> pmf M xc = 0"
    apply (auto, rule pmf_not_in_the_two_is_zero[where sa="xa" and sb="xb" and a="pmf M xa"])
    apply auto+
      apply (simp add: pmf_le_1)
    using assms by auto+
  have f2: "(\<Sum>\<^sub>ax::'a. (pmf M x) \<cdot> (Q x)) = 
    (\<Sum>\<^sub>ax::'a. (if x = xa then (pmf M xa) \<cdot> (Q xa) else 
      (if x = xb then (pmf M xb) \<cdot> (Q xb) else (pmf M x) \<cdot> (Q x))))"
    by metis
  have f3: "... = (\<Sum>\<^sub>ax::'a. (if x = xa then (pmf M xa) \<cdot> (Q xa) else 
      (if x = xb then (pmf M xb) \<cdot> (Q xb) else 0)))"
    using f1
    by (smt infsetsum_cong insertE mult_not_zero singleton_iff)
  show ?thesis
    using f2 f3 
    by (simp add: assms(1) infsetsum_two)
qed

lemma pmf_sum_single':
  fixes prob\<^sub>v::"'a pmf"
  shows "(\<Sum>\<^sub>ax::'a. pmf prob\<^sub>v x \<cdot> pmf (pmf_of_list [(x, 1::real)]) xa) = pmf prob\<^sub>v xa"
  proof -
    have "pmf (pmf_of_list [(xb, 1::real)]) xa = (if xb = xa then 1 else 0)"
      by (simp add: filter.simps(2) pmf_of_list_wf_def pmf_pmf_of_list)
    then have "(pmf prob\<^sub>v xb \<cdot> pmf (pmf_of_list [(xb, 1::real)]) xa) = (if xb = xa then pmf prob\<^sub>v xa else 0)"
        by simp
    then show ?thesis
      using pmf_sum_single 
      by (smt filter.simps(1) filter.simps(2) infsetsum_cong list.set(1) list.set(2) list.simps(8) 
          list.simps(9) mult_cancel_left1 mult_cancel_right1 pmf_of_list_wf_def pmf_pmf_of_list 
          prod.sel(1) prod.sel(2) singletonD sum_list.Nil sum_list_simps(2))
  qed

lemma pmf_sum_single'':
  fixes prob\<^sub>v::"'a pmf"
  shows "(\<Sum>\<^sub>ax::'a. pmf prob\<^sub>v xa \<cdot> pmf (pmf_of_list [(y, 1::real)]) x) = pmf prob\<^sub>v xa"
  proof -
    have f1: "\<forall>x. pmf (pmf_of_list [(y, 1::real)]) x = (if y = x then 1 else 0)"
      by (simp add: filter.simps(2) pmf_of_list_wf_def pmf_pmf_of_list)
    then have f2: "\<forall>x. (pmf prob\<^sub>v xa \<cdot> pmf (pmf_of_list [(y, 1::real)]) x) = (if y = x then pmf prob\<^sub>v xa else 0)"
      by simp
    then have f3: "(\<Sum>\<^sub>ax::'a. pmf prob\<^sub>v xa \<cdot> pmf (pmf_of_list [(y, 1::real)]) x) = 
      (\<Sum>\<^sub>ax::'a. (if y = x then pmf prob\<^sub>v xa else 0))"
      by simp
    have f4: "(\<Sum>\<^sub>ax::'a. (if x = y then pmf prob\<^sub>v xa else 0)) = pmf prob\<^sub>v xa"
      by (simp add: infsetsum_single'[of y "\<lambda>x. pmf prob\<^sub>v x" xa])
    then show ?thesis
      by (smt f3 infsetsum_cong)
  qed

lemma infsum_singleton_is_single:
  assumes "\<forall>xb. xb \<noteq> xa \<longrightarrow> P xb = (0::real)"
  shows "(\<Sum>\<^sub>ax::'a. P x \<cdot> Q x) = P xa \<cdot> Q xa"
proof -
  have "\<forall>x. P x \<cdot> Q x = (if x = xa then P xa \<cdot> Q xa else 0)"
    apply (auto)
    using assms by blast
  then have f1: "(\<Sum>\<^sub>ax::'a. P x \<cdot> Q x) = (\<Sum>\<^sub>ax::'a.  (if x = xa then P xa \<cdot> Q xa else 0))"
    by auto
  show ?thesis
    apply (simp add: f1)
    by (rule infsetsum_single)
qed

lemma pmf_sum_singleton_is_single:
  fixes M::"'a pmf"
  assumes "pmf M xa = 1"
  shows "(\<Sum>\<^sub>ax::'a. pmf M x \<cdot> Q x) = Q xa"
proof -
  have "\<forall>x. pmf M x \<cdot> Q x = (if x = xa then Q xa else 0)"
    using assms pmf_not_the_one_is_zero by fastforce
  then have "(\<Sum>\<^sub>ax::'a. pmf M x \<cdot> Q x) = (\<Sum>\<^sub>ax::'a. (if x = xa then Q xa else 0))"
    by auto
  then show ?thesis
    by (simp add: infsetsum_single)
qed

lemma pmf_out_of_list_is_zero:
  assumes "r \<in> {0..1}" "\<not> xa = xb" "\<not> ii = xa" "\<not> ii = xb"
  shows "pmf (pmf_of_list [(xa, r), (xb, 1-r)]) ii = (0::real)"
  using assms
  by (smt atLeastAtMost_iff empty_iff filter.simps(1) filter.simps(2) fst_conv insert_iff 
      list.set(1) list.set(2) list.simps(8) list.simps(9) pmf_of_list_wf_def pmf_pmf_of_list snd_conv sum_list.Cons sum_list.Nil)

lemma pmf_instance_from_one_full_state:
  assumes "pmf M xa = 1"
  shows "M = (pmf_of_list [(xa, 1)])"
  proof -
    have f1: "\<forall>ii. pmf M ii = pmf (pmf_of_list [(xa, 1)]) ii"
      proof 
        fix ii::"'a"
        show "pmf M ii = pmf (pmf_of_list [(xa, 1)]) ii" (is "?LHS = ?RHS")
        proof (cases "ii = xa")
          case True
          have f1: "?LHS = 1.0"
            by (simp add: assms(1) True)
          have f2: "?RHS = 1.0"
            apply (subst pmf_pmf_of_list)
            using assms apply (simp add: pmf_of_list_wf_def)
            by (simp add: True)
          show ?thesis using f1 f2 by simp
        next
          case False
          have f1: "?LHS = 0"
            using False assms pmf_not_the_one_is_zero by fastforce
          have f2: "?RHS = 0"
            apply (subst pmf_pmf_of_list)
            using assms apply (simp add: pmf_of_list_wf_def)
            using False by auto
          show ?thesis using f1 f2 by simp
        qed
      qed
    show ?thesis
      using f1 pmf_eq_iff by auto
  qed

lemma pmf_instance_from_two_full_states:
  assumes "pmf M xa = 1 - pmf M xb"
  assumes "\<not> xa = xb"
  shows "M = (pmf_of_list [(xa, pmf M xa), (xb, pmf M xb)])"
  proof -
    let ?r = "pmf M xa"
    have f1: "\<forall>ii. pmf M ii = pmf (pmf_of_list [(xa, ?r), (xb, 1-?r)]) ii"
      proof 
        fix ii::"'a"
        show "pmf M ii = pmf (pmf_of_list [(xa, ?r), (xb, 1-?r)]) ii" (is "?LHS = ?RHS")
        proof (cases "ii = xa")
          case True
          have f1: "?LHS = ?r"
            by (simp add: True)
          have f2: "?RHS = ?r"
            apply (subst pmf_pmf_of_list)
            using assms apply (simp add: pmf_of_list_wf_def)
            apply (simp add: pmf_le_1)
            using True assms(2) by auto
          show ?thesis using f1 f2 by simp
        next
          case False
          then have F: "\<not> ii = xa"
            by blast
          show ?thesis 
            proof (cases "ii = xb")
              case True
              have f1: "?LHS = 1-?r"
                using True by (simp add: assms(1))
              have f2: "?RHS = 1-?r"
                apply (subst pmf_pmf_of_list)
                using assms apply (simp add: pmf_of_list_wf_def)
                apply (simp add: pmf_le_1)
                using True assms(2) by auto
              show ?thesis using f1 f2 by simp
            next
              case False
              have f1: "?LHS = 0"
                proof (rule ccontr)
                  assume aa1: "\<not> pmf M ii = (0::real)"
                  have f1: "(\<Sum>\<^sub>a i\<in>{xa,xb,ii}. pmf M i) = (pmf M xa + pmf M xb + pmf M ii)"
                    apply (simp add: infsetsum_def)
                    using F False lebesgue_integral_count_space_finite
                    by (smt assms(2) finite.emptyI finite.insertI insert_absorb insert_iff integral_pmf 
                        pmf.rep_eq singleton_insert_inj_eq' sum.insert)
                  have f2: "(\<Sum>\<^sub>a i. pmf M i) \<ge> (\<Sum>\<^sub>a i\<in>{xa,xb,ii}. pmf M i)"
                    by (metis measure_pmf.prob_le_1 measure_pmf_conv_infsetsum sum_pmf_eq_1)
                  from f1 f2 have "(\<Sum>\<^sub>a i. pmf M i) > 1"
                    using pmf_pos aa1 assms(1) by fastforce
                  then show "False"
                    by (simp add: sum_pmf_eq_1)
                qed
              have f2: "?RHS = 0"
                apply (subst pmf_pmf_of_list)
                using assms apply (simp add: pmf_of_list_wf_def)
                apply (simp add: pmf_le_1)
                using F False by auto
              show ?thesis using f1 f2 by simp
            qed
        qed
      qed
    show ?thesis
      using f1 pmf_eq_iff
      by (metis assms(1) cancel_ab_semigroup_add_class.diff_right_commute diff_eq_diff_eq)
  qed

lemma pmf_instance_from_two_full_states':
  assumes "pmf M xa = 1 - pmf M xb"
  assumes "\<not> xa = xb"
  shows "M = (pmf_of_list [(xa, (1::real))]) +\<^bsub>pmf M xa\<^esub> (pmf_of_list [(xb, (1::real))])"
  apply (subst pmf_instance_from_two_full_states[of "M" "xa" "xb"])
  using assms apply blast
  using assms(2) apply simp
  proof -
    have f0: "pmf M xa \<in> {0..1}"
      by (simp add: pmf_le_1)
    have f1: "\<forall>ii. pmf (pmf_of_list [(xa, pmf M xa), (xb, pmf M xb)]) ii =
      pmf (pmf_of_list [(xa, 1::real)] +\<^bsub>pmf M xa\<^esub> pmf_of_list [(xb, 1::real)]) ii"
      apply (auto)
      using f0 apply (simp add: pmf_wplus)
      proof -
        fix ii::"'a"
        show "pmf (pmf_of_list [(xa, pmf M xa), (xb, pmf M xb)]) ii =
         pmf (pmf_of_list [(xa, 1::real)]) ii \<cdot> pmf M xa +
         pmf (pmf_of_list [(xb, 1::real)]) ii \<cdot> ((1::real) - pmf M xa)" 
           (is "?LHS = ?RHS")
          proof (cases "ii = xa")
            case True
            have f1: "?LHS = pmf M xa"
              apply (subst pmf_pmf_of_list)
              apply (smt assms(1) insert_iff list.set(1) list.set(2) list.simps(8) list.simps(9) 
                  pmf_nonneg pmf_of_list_wf_def prod.sel(2) singletonD sum_list.Cons sum_list.Nil)
              using True assms(2) by auto
            have f2: "?RHS = pmf M xa"
              apply (subst pmf_pmf_of_list)
              using assms apply (simp add: pmf_of_list_wf_def)
              apply (subst pmf_pmf_of_list)
              using assms apply (simp add: pmf_of_list_wf_def)
              using True assms(2) by auto
            show ?thesis using f1 f2 by simp
          next
            case False
            then have F: "\<not> ii = xa"
              by blast
            show ?thesis 
              proof (cases "ii = xb")
                case True
                have f1: "?LHS = pmf M xb"
                  apply (subst pmf_pmf_of_list)
                  apply (smt assms(1) insert_iff list.set(1) list.set(2) list.simps(8) list.simps(9) 
                      pmf_nonneg pmf_of_list_wf_def prod.sel(2) singletonD sum_list.Cons sum_list.Nil)
                  using True assms(2) by auto
                have f2: "?RHS = pmf M xb"
                  apply (subst pmf_pmf_of_list)
                  using assms apply (simp add: pmf_of_list_wf_def)
                  apply (subst pmf_pmf_of_list)
                  using assms apply (simp add: pmf_of_list_wf_def)
                  using True assms by auto
                show ?thesis using f1 f2 by simp
              next
                case False
                have f1: "?LHS = 0"
                  using pmf_out_of_list_is_zero by (smt F False assms(1) assms(2) f0)
                have f2: "?RHS = 0"
                  by (smt F False filter.simps(1) filter.simps(2) fst_conv list.set(1) list.set(2) 
                      list.simps(8) list.simps(9) pmf_of_list_wf_def pmf_pmf_of_list singletonD snd_conv sum_list.Cons sum_list.Nil sum_list_mult_const)
                show ?thesis using f1 f2 by simp
              qed
          qed
      qed
    show "pmf_of_list [(xa, pmf M xa), (xb, pmf M xb)] =
      pmf_of_list [(xa, 1::real)] +\<^bsub>pmf M xa\<^esub> pmf_of_list [(xb, 1::real)]"
      using f1 pmf_eqI by blast
  qed

lemma pmf_comp_set:
  shows "((\<Sum>\<^sub>a i\<in>(X). pmf M i) = 1) = ((\<Sum>\<^sub>a i\<in> -X. pmf M i) = 0)"
  using pmf_disj_set[of X "-X"]
  by (simp add: sum_pmf_eq_1) 

lemma pmf_all_zero:
  assumes "((\<Sum>\<^sub>a i\<in>(X). pmf M i) = 0)"
  shows "\<forall>x\<in>X. pmf M x = 0"
proof
  fix x::'a
  assume a1: "x \<in> X"
  show "pmf M x = (0::real)"
  proof (rule ccontr)
    assume a2: "\<not> pmf M x = (0::real)"
    have f1: "pmf M x > (0::real)"
      using pmf_nonneg a2 by simp
    have f2: "(\<Sum>\<^sub>a i\<in>(X). pmf M i) \<ge> (\<Sum>\<^sub>a i\<in>{x}. pmf M i)"
      using a1
      by (meson empty_subsetI infsetsum_mono_neutral_left insert_subset order_refl pmf_abs_summable pmf_nonneg)
    have f3: "(\<Sum>\<^sub>a i\<in>{x}. pmf M i) = pmf M x"
      by simp
    have f4: "(\<Sum>\<^sub>a i\<in>(X). pmf M i) > 0"
      using f2 f3 f1 by linarith
    show "False"
      using f4 by (simp add: assms)
  qed
qed

lemma pmf_utp_univ:
  fixes prob\<^sub>v::"'a pmf"
  shows "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>\<not>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real)"
  by (simp add: infsetsum_pmf_eq_1 lit.rep_eq not_upred_def uexpr_appl.rep_eq uminus_uexpr_def)

lemma pmf_disj_set2:
  assumes "X \<inter> Y = {}"
  shows "(\<Sum>\<^sub>a i\<in>(X \<union> Y). pmf M i) = (\<Sum>\<^sub>a i\<in>X. pmf M i) + (\<Sum>\<^sub>a i\<in>Y. pmf M i)"
  by (metis assms infsetsum_Un_disjoint pmf_abs_summable)

lemma pmf_disj_set2':
  fixes prob\<^sub>v::"'a pmf"
  assumes "\<not> (\<exists>x. P x \<and> Q x)" 
  shows "(\<Sum>\<^sub>ax::'a | P x \<or> Q x. pmf prob\<^sub>v x) = 
        (\<Sum>\<^sub>ax::'a | P x. pmf prob\<^sub>v x) + (\<Sum>\<^sub>ax::'a | Q x. pmf prob\<^sub>v x)"
  apply (simp add: infsetsum_altdef)
proof -
  have 1: "{x::'a. P x \<or> Q x} = {x::'a. P x} \<union> {x::'a. Q x}"
    using assms by blast
  show "set_lebesgue_integral (count_space UNIV) {x::'a. P x \<or> Q x} (pmf prob\<^sub>v) =
    set_lebesgue_integral (count_space UNIV) (Collect P) (pmf prob\<^sub>v) +
    set_lebesgue_integral (count_space UNIV) (Collect Q) (pmf prob\<^sub>v)"
    apply (simp add: 1)
    unfolding infsetsum_altdef abs_summable_on_altdef
    apply (subst set_integral_Un, auto)
    using assms apply blast
    using abs_summable_on_altdef apply blast
    using abs_summable_on_altdef by blast
qed

lemma pmf_utp_disj_set2:
  fixes prob\<^sub>v::"'a pmf"
  assumes "\<not> (\<exists>x. \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x))"
  shows "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = 
        (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) + (\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x)"
  using assms by (rule pmf_disj_set2')
 
lemma pmf_disj_set3:
  fixes prob\<^sub>v::"'a pmf"
  assumes a1: "\<not> (\<exists>x. P x \<and> Q x)" 
  assumes a2: "\<not> (\<exists>x. P x \<and> R x)"
  assumes a3: "\<not> (\<exists>x. Q x \<and> R x)"
  shows "(\<Sum>\<^sub>ax::'a | P x \<or> Q x \<or> R x. pmf prob\<^sub>v x) = 
        (\<Sum>\<^sub>ax::'a | P x. pmf prob\<^sub>v x) + (\<Sum>\<^sub>ax::'a | Q x. pmf prob\<^sub>v x) + (\<Sum>\<^sub>ax::'a | R x. pmf prob\<^sub>v x)"
proof -
  have 1: "(\<Sum>\<^sub>ax::'a | P x \<or> Q x \<or> R x. pmf prob\<^sub>v x) = 
          (\<Sum>\<^sub>ax::'a | P x. pmf prob\<^sub>v x) + (\<Sum>\<^sub>ax::'a | Q x \<or> R x. pmf prob\<^sub>v x)"
    apply (rule pmf_disj_set2')
    using assms by blast
  have 2: "(\<Sum>\<^sub>ax::'a | Q x \<or> R x. pmf prob\<^sub>v x) = (\<Sum>\<^sub>ax::'a | Q x. pmf prob\<^sub>v x) + (\<Sum>\<^sub>ax::'a | R x. pmf prob\<^sub>v x)"
    apply (rule pmf_disj_set2')
    using assms by blast
  from 1 2 show ?thesis
    by auto
qed
  
lemma pmf_utp_comp0:
  fixes prob\<^sub>v::"'a pmf"
  assumes "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real)"
  shows "(\<Sum>\<^sub>ax::'a | \<lbrakk>\<not>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (0::real)"
  using pmf_utp_univ
  by (smt Collect_cong Compl_eq assms bool_Compl_def lit.rep_eq mem_Collect_eq not_upred_def 
      pmf_comp_set uexpr_appl.rep_eq uminus_uexpr_def)

lemma pmf_utp_comp0':
  fixes prob\<^sub>v::"'a pmf"
  assumes "(\<Sum>\<^sub>ax::'a | P x. pmf prob\<^sub>v x) = (1::real)"
  shows "(\<Sum>\<^sub>ax::'a | \<not> P x. pmf prob\<^sub>v x) = (0::real)"
  using pmf_utp_univ
  by (metis Collect_neg_eq assms pmf_comp_set)

lemma pmf_utp_comp1:
  fixes prob\<^sub>v::"'a pmf"
  assumes "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (0::real)"
  shows "(\<Sum>\<^sub>ax::'a | \<lbrakk>\<not>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real)"
  using pmf_utp_univ pmf_utp_comp0
  by (smt Collect_cong Compl_eq assms bool_Compl_def lit.rep_eq mem_Collect_eq not_upred_def 
      pmf_comp_set uexpr_appl.rep_eq uminus_uexpr_def)

lemma pmf_comp1:
  fixes prob\<^sub>v::"'a pmf"
  assumes "(\<Sum>\<^sub>ax::'a | P x. pmf prob\<^sub>v x) = (0::real)"
  shows "(\<Sum>\<^sub>ax::'a | \<not>(P x). pmf prob\<^sub>v x) = (1::real)"
  by (smt Collect_cong Compl_eq assms bool_Compl_def lit.rep_eq mem_Collect_eq not_upred_def
      pmf_comp_set uexpr_appl.rep_eq uminus_uexpr_def)

lemma pmf_utp_comp1':
  fixes prob\<^sub>v::"'a pmf"
  assumes "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (0::real)"
  shows "(\<Sum>\<^sub>ax::'a | \<not>\<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real)"
  by (smt Collect_cong Compl_eq assms bool_Compl_def lit.rep_eq mem_Collect_eq not_upred_def
      pmf_comp_set uexpr_appl.rep_eq uminus_uexpr_def)

lemma pmf_utp_comp_not0:
  fixes prob\<^sub>v::"'a pmf"
  assumes "\<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real)"
  shows "\<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>\<not>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (0::real)"
  using pmf_utp_univ pmf_utp_comp0 assms pmf_utp_comp1 by fastforce

lemma pmf_utp_comp_not1:
  fixes prob\<^sub>v::"'a pmf"
  assumes "\<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (0::real)"
  shows "\<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>\<not>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real)"
  using pmf_utp_univ pmf_utp_comp0 assms pmf_utp_comp1 by fastforce

(*
lemma pmf_utp_univ':
  fixes prob\<^sub>v::"'a pmf" and P::"'a \<Rightarrow> bool" and Q::"'a \<Rightarrow> bool"
  assumes "P(x) \<longrightarrow> Q(x)"
  shows "(\<Sum>\<^sub>ax::'a | P(x). pmf prob\<^sub>v x) \<le>
        (\<Sum>\<^sub>ax::'a | Q(x). pmf prob\<^sub>v x)"
  apply (simp add: infsetsum_def)
  apply (simp add: lebesgue_integral_def count_space_def)
  using assms sledgehammer
*)                     

term "count_space"
term "measure_space"
term "measure_of"
term "Abs_measure"
term "sigma_sets"
term "lebesgue_integral"
term "has_bochner_integral"

lemma pmf_disj_leq:
  fixes prob\<^sub>v::"'a pmf" and more::"'a"
  shows "(\<Sum>\<^sub>ax::'a | P x. pmf prob\<^sub>v x) \<le>
        (\<Sum>\<^sub>ax::'a | P x \<or> Q x. pmf prob\<^sub>v x)"
  by (metis (mono_tags, lifting) infsetsum_mono_neutral_left le_less 
      mem_Collect_eq pmf_abs_summable pmf_nonneg subsetI)

lemma pmf_disj_leq':
  fixes prob\<^sub>v::"'a pmf" and more::"'a"
  shows "(\<Sum>\<^sub>ax::'a | P x. pmf prob\<^sub>v x) \<le>
        (\<Sum>\<^sub>ax::'a | Q x \<or> P x. pmf prob\<^sub>v x)"
  by (metis (mono_tags, lifting) infsetsum_mono_neutral_left le_less 
      mem_Collect_eq pmf_abs_summable pmf_nonneg subsetI)

lemma pmf_utp_disj_leq:
  fixes prob\<^sub>v::"'a pmf" and P::"'a hrel" and Q::"'a hrel" and more::"'a"
  shows "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) \<le>
        (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x)"
  by (simp add: pmf_disj_leq)

lemma pmf_utp_disj_eq_1:
  fixes prob\<^sub>v::"'a pmf" and P::"'a hrel" and Q::"'a hrel" and more::"'a"
  assumes "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real)"
  shows "(\<Sum>\<^sub>ax::'a | \<exists>v::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> v = x \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x) \<and> v = x. pmf prob\<^sub>v x) = (1::real)"
proof -
  have f1: "(\<Sum>\<^sub>ax::'a | \<exists>v::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> v = x \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x) \<and> v = x. pmf prob\<^sub>v x)
    = (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x)"
    by (metis)
  have f2: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) \<le> 1"
    by (metis measure_pmf.prob_le_1 measure_pmf_conv_infsetsum)
  have f3: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) \<le> 
            (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x)"
    by (rule pmf_utp_disj_leq)
  then have "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) \<ge> 1"
    using assms by auto
  then show ?thesis
    using f2 f1 by linarith
qed

lemma pmf_utp_disj_eq_1':
  fixes prob\<^sub>v::"'a pmf" and P::"'a hrel" and Q::"'a hrel" and more::"'a"
  assumes "(\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real)"
  shows "(\<Sum>\<^sub>ax::'a | \<exists>v::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> v = x \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x) \<and> v = x. pmf prob\<^sub>v x) = (1::real)"
proof -
  have f1: "(\<Sum>\<^sub>ax::'a | \<exists>v::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, x) \<and> v = x \<or> \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> v = x. pmf prob\<^sub>v x) = (1::real)"
    by (simp add: assms pmf_utp_disj_eq_1)
  have "(\<Sum>\<^sub>ax::'a | \<exists>v::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, x) \<and> v = x \<or> \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> v = x. pmf prob\<^sub>v x) =
      (\<Sum>\<^sub>ax::'a | \<exists>v::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> v = x \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x) \<and> v = x. pmf prob\<^sub>v x)"
    by meson
  then show ?thesis
    using f1 by auto
qed

(*
lemma pmf_sum:
  fixes prob\<^sub>v'::"'a pmf" and prob\<^sub>v''::"'a pmf"
  shows "(\<Sum>\<^sub>ax::'a | P x. pmf prob\<^sub>v' x + pmf prob\<^sub>v'' x) = 
    (\<Sum>\<^sub>ax::'a | P x. pmf prob\<^sub>v' x) + (\<Sum>\<^sub>ax::'a | P x. pmf prob\<^sub>v'' x)"
  using infsetsum_add by blast

lemma pmf_sum_0:
  fixes prob\<^sub>v'::"'a pmf" and prob\<^sub>v''::"'a pmf"
  assumes "(\<Sum>\<^sub>ax::'a | P x. pmf prob\<^sub>v' x) = (0::real)"
  assumes "(\<Sum>\<^sub>ax::'a | P x. pmf prob\<^sub>v'' x) = (0::real)"
  assumes "r \<in> {0<..<1}"
  shows "(\<Sum>\<^sub>ax::'a | P x. pmf prob\<^sub>v' x + pmf prob\<^sub>v'' x) = (0::real)"
  using pmf_sum by (simp add: pmf_sum assms(1) assms(2))
*)
lemma pmf_conj_eq_0:
  fixes prob\<^sub>v'::"'a pmf" and prob\<^sub>v''::"'a pmf"
  assumes "(\<Sum>\<^sub>ax::'a | P x. pmf prob\<^sub>v' x) = (0::real)"
  assumes "(\<Sum>\<^sub>ax::'a | Q x. pmf prob\<^sub>v'' x) = (0::real)"
  assumes "r \<in> {0<..<1}"
  shows "(\<Sum>\<^sub>ax::'a | P x \<and> Q x. pmf (prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v'') x) = (0::real)"
  using assms(3) apply (simp add: pmf_wplus)
proof -
  have "(\<Sum>\<^sub>ax::'a | P x \<and> Q x. pmf prob\<^sub>v' x) = (0::real)"
    using assms infsetsum_nonneg
    by (smt Collect_cong  pmf_disj_leq pmf_nonneg)
  then have 1: "(\<Sum>\<^sub>ax::'a | P x \<and> Q x. pmf prob\<^sub>v' x \<cdot> r) = (0::real)"
    using assms(3) by (simp add: infsetsum_cmult_left pmf_abs_summable)
  have "(\<Sum>\<^sub>ax::'a | P x \<and> Q x. pmf prob\<^sub>v'' x) = (0::real)"
    using assms infsetsum_nonneg
    by (smt Collect_cong pmf_disj_leq pmf_nonneg)
  then have 2: "(\<Sum>\<^sub>ax::'a | P x \<and> Q x. pmf prob\<^sub>v'' x \<cdot> ((1::real) - r)) = (0::real)"
    using assms(3) by (simp add: infsetsum_cmult_left pmf_abs_summable)
  have "(\<Sum>\<^sub>ax::'a | P x \<and> Q x. pmf prob\<^sub>v' x \<cdot> r + pmf prob\<^sub>v'' x \<cdot> ((1::real) - r))
    = (\<Sum>\<^sub>ax::'a | P x \<and> Q x. pmf prob\<^sub>v' x \<cdot> r) + (\<Sum>\<^sub>ax::'a | P x \<and> Q x. pmf prob\<^sub>v'' x \<cdot> ((1::real) - r))"
    using infsetsum_add by (simp add: infsetsum_add abs_summable_on_cmult_left pmf_abs_summable)
  then show "(\<Sum>\<^sub>ax::'a | P x \<and> Q x. pmf prob\<^sub>v' x \<cdot> r + pmf prob\<^sub>v'' x \<cdot> ((1::real) - r)) = (0::real)"
    using 1 2 by linarith
qed

lemma pmf_utp_conj_eq_0:
  fixes prob\<^sub>v'::"'a pmf" and prob\<^sub>v''::"'a pmf" and P::"'a hrel" and Q::"'a hrel" and more::"'a"
  assumes "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v' x) = (0::real)"
  assumes "(\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v'' x) = (0::real)"
  assumes "r \<in> {0<..<1}"
  shows "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf (prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v'') x) = (0::real)"
  using pmf_conj_eq_0 assms(1) assms(2) assms(3) by blast

lemma pmf_utp_disj_comm:
  fixes prob\<^sub>v::"'a pmf" and P::"'a hrel" and Q::"'a hrel" and more::"'a"
  shows "(\<Sum>\<^sub>ax::'a | \<exists>v::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> v = x \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x) \<and> v = x. pmf prob\<^sub>v x) = 
    (\<Sum>\<^sub>ax::'a | \<exists>v::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, x) \<and> v = x \<or> \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> v = x. pmf prob\<^sub>v x)"
  by meson

lemma pmf_utp_disj_imp:
  fixes ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and prob\<^sub>v::"'a pmf"
  assumes a1: "(\<Sum>\<^sub>ax::'a | \<exists>v::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> v = x \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x) \<and> v = x. pmf prob\<^sub>v x) = (1::real)"
  assumes a2: "\<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real)"
  assumes a3: "\<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real)"
  shows "(0::real) < (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<not> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) \<and> 
     (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<not> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) < (1::real)"
  apply (rule conjI)
  proof -
    from a1 have f11: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real)"
      proof -
        have "{a. \<exists>aa. \<lbrakk>P\<rbrakk>\<^sub>e (more, a) \<and> aa = a \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, a) \<and> aa = a} = {a. \<lbrakk>P\<rbrakk>\<^sub>e (more, a) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, a)}"
          by auto
        then show ?thesis
          using a1 by presburger
      qed
    then have f12: "(\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)) \<or> (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<not>\<lbrakk>Q\<rbrakk>\<^sub>e (more, x)) \<or> 
              (\<not>\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x) = (1::real)"
      by (metis (no_types, lifting) Collect_cong)
    have f13: "(\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)) \<or> (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<not>\<lbrakk>Q\<rbrakk>\<^sub>e (more, x)) \<or> 
              (\<not>\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x)
          = (\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x) +
               (\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<not>\<lbrakk>Q\<rbrakk>\<^sub>e (more, x)) . pmf prob\<^sub>v x) + 
               (\<Sum>\<^sub>ax::'a | (\<not>\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x)"
      apply (rule pmf_disj_set3)
      by blast+
    then have f14: "(\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x) +
               (\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<not>\<lbrakk>Q\<rbrakk>\<^sub>e (more, x)) . pmf prob\<^sub>v x) + 
               (\<Sum>\<^sub>ax::'a | (\<not>\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x) = (1::real)"
      using f12 by auto

    show "(0::real) < (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<not> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x)"
    proof (rule ccontr)
      assume a11: "\<not> (0::real) < (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<not> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x)"
      from a11 f14 have f111: "(\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x) +
               (\<Sum>\<^sub>ax::'a | (\<not>\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x) = (1::real)"
        by (smt infsetsum_nonneg pmf_nonneg)
      have "(\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)) \<or> (\<not>\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x)
          = (\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x) +
               (\<Sum>\<^sub>ax::'a | (\<not>\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x)"
        apply (rule pmf_disj_set2')
        by blast
      then have "(\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)) \<or> (\<not>\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x)
          = (1::real)"
        using f111 by auto
      then have "(\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real)"
        by (metis (mono_tags, lifting) Collect_cong)
      then show "False"
        using a3 by auto
    qed
  next 
    from a1 have f11: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real)"
      proof -
        have "{a. \<exists>aa. \<lbrakk>P\<rbrakk>\<^sub>e (more, a) \<and> aa = a \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, a) \<and> aa = a} = {a. \<lbrakk>P\<rbrakk>\<^sub>e (more, a) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, a)}"
          by auto
        then show ?thesis
          using a1 by presburger
      qed
    then have f12: "(\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)) \<or> (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<not>\<lbrakk>Q\<rbrakk>\<^sub>e (more, x)) \<or> 
              (\<not>\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x) = (1::real)"
      by (metis (no_types, lifting) Collect_cong)
    have f13: "(\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)) \<or> (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<not>\<lbrakk>Q\<rbrakk>\<^sub>e (more, x)) \<or> 
              (\<not>\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x)
          = (\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x) +
               (\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<not>\<lbrakk>Q\<rbrakk>\<^sub>e (more, x)) . pmf prob\<^sub>v x) + 
               (\<Sum>\<^sub>ax::'a | (\<not>\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x)"
      apply (rule pmf_disj_set3)
      by blast+
    then have f14: "(\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x) +
               (\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<not>\<lbrakk>Q\<rbrakk>\<^sub>e (more, x)) . pmf prob\<^sub>v x) + 
               (\<Sum>\<^sub>ax::'a | (\<not>\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x) = (1::real)"
      using f12 by auto

    show "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<not> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) < (1::real)"
    proof (rule ccontr)
      assume a11: "\<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<not> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) < (1::real)"
      from a11 have f110: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<not> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real)"
        by (smt measure_pmf.prob_le_1 measure_pmf_conv_infsetsum)
      then have f111: "(\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x) +
               (\<Sum>\<^sub>ax::'a | (\<not>\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x) = (0::real)"
        using f14 by auto
      then have f112: "(\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x) = (0::real)"
        by (smt infsetsum_nonneg pmf_nonneg)
      have f113: "(\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)) \<or> (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<not>\<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x) = 
            (\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x) +
               (\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<not>\<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x)"
        apply (rule pmf_disj_set2')
        by blast
      have "(\<Sum>\<^sub>ax::'a | (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)) \<or> (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<not>\<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x) = 
        (1::real)"
        using f112 f110 by (simp add: f113)
      then have f114: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real)"
        by (metis (mono_tags, lifting) Collect_cong)
      then show "False"
        using a2 by auto
    qed
  qed

lemma pmf_utp_disj_imp':
  fixes ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and prob\<^sub>v::"'a pmf"
  assumes a1: "(\<Sum>\<^sub>ax::'a | \<exists>v::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> v = x \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x) \<and> v = x. pmf prob\<^sub>v x) = (1::real)"
  assumes a2: "\<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real)"
  assumes a3: "\<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real)"
  shows "(0::real) < (\<Sum>\<^sub>ax::'a | \<not>\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and>  \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) \<and> 
     (\<Sum>\<^sub>ax::'a | \<not>\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and>  \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) < (1::real)"
proof -
  have "(0::real) < (\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (more, x) \<and>  \<not>\<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) \<and> 
     (\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (more, x) \<and>  \<not>\<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) < (1::real)"
    using assms by (simp add: pmf_utp_disj_imp pmf_utp_disj_comm)
  then show ?thesis
    by (metis (mono_tags, lifting) Collect_cong)
qed

lemma pmf_sum_subset_imp_1:
  assumes "P \<subseteq> Q"
  assumes "(\<Sum>\<^sub>ai::'a\<in>P. pmf M i) = 1"
  shows "(\<Sum>\<^sub>ai::'a\<in>Q. pmf M i) = 1"
proof -
  have f1: "infsetsum (pmf M) P \<le> infsetsum (pmf M) Q"
    apply (rule infsetsum_mono_neutral_left)
    apply (simp add: pmf_abs_summable)+
    apply (simp add: assms)
    by simp
  show ?thesis
    using f1 assms
    by (metis measure_pmf.prob_le_1 measure_pmf_conv_infsetsum order_class.order.antisym)
qed

subsection \<open> Measures \<close>

text \<open> Construct 0.prob and 1.prob from a supplied pmf P, and two sets A and B.
We cannot modify the probability function in pmf since it has to satisfy a condition (@{text "prob_space M"}).
But we can modify the function in the measure space by dropping P to a measure, then modifying 
measure function, afterwards lifting back to the probability space. 

But when lifting, we need to prove additional laws
  @{text "prob_space M \<and> sets M = UNIV \<and> (AE x in M. measure M {x} \<noteq> 0)"}
to ensure modified measure is a probability measure.
\<close>

definition proj_f :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a pmf \<Rightarrow> 'a measure" ("\<F>") where
"proj_f A B P = measure_of (space P) (sets P)
  (\<lambda>AA. 
    (   emeasure P (AA \<inter> (A-B))*(((\<Sum>\<^sub>a i\<in>B-A. pmf P i) + (\<Sum>\<^sub>a i\<in>A-B. pmf P i))/(\<Sum>\<^sub>a i\<in>A-B. pmf P i))
      + emeasure P (AA \<inter> (A \<inter> B))
    )
  )
"

lemma emeasure_infsum_eq: "emeasure (P::'a pmf) A = (\<Sum>\<^sub>a i\<in>A. pmf P i)"
  by (simp add: measure_pmf.emeasure_eq_measure measure_pmf_conv_infsetsum)

lemma proj_f_sets: "sets (\<F> A B P) = UNIV"
   apply (simp add: proj_f_def)
  by auto

lemma proj_f_space: "space (\<F> A B P) = UNIV"
  by (simp add: proj_f_def)

lemma pmf_measure_zero:
  assumes "\<forall>i \<in> A. emeasure (measure_pmf P) {i} = (0::ennreal)" 
  shows "emeasure (measure_pmf P) A = (0::ennreal)"
  by (metis assms disjoint_iff_not_equal emeasure_Int_set_pmf emeasure_empty emeasure_pmf_single_eq_zero_iff)

lemma proj_f_emeasure: "emeasure (\<F> A B P) C = 
   (\<lambda>AA. emeasure P (AA \<inter> (A-B)) * (((\<Sum>\<^sub>a i\<in>B-A . pmf P i) + (\<Sum>\<^sub>a i\<in>A-B . pmf P i))/(\<Sum>\<^sub>a i\<in>A-B . pmf P i))
  + emeasure P (AA \<inter> (A \<inter> B))) C"
  apply (simp add: proj_f_def)
  apply (intro emeasure_measure_of_sigma)
  apply (metis sets.sigma_algebra_axioms sets_measure_pmf space_measure_pmf)
  apply (simp add: positive_def)
  defer
  apply simp
  proof (rule countably_additiveI)
    fix Aa :: "nat \<Rightarrow> 'a set"  
    let ?A_B = "infsetsum (pmf P) (A-B)"
    let ?B_A = "infsetsum (pmf P) (B-A)"
    let ?A_and_B = "infsetsum (pmf P) (A \<inter> B)"
    let ?em_A_and_B = "emeasure (measure_pmf P) (A \<inter> B)"
    let ?em_A_B = "emeasure (measure_pmf P) (A - B)"
    let ?em_B_A = "emeasure (measure_pmf P) (B - A)"
    assume *: "range Aa \<subseteq> UNIV" "disjoint_family Aa" "\<Union> (range Aa) \<in> UNIV"
    let ?f = "\<lambda>i::nat . emeasure (measure_pmf P) (Aa i \<inter> (A - B)) \<cdot>
         ennreal ((?B_A + ?A_B) / ?A_B) +
         emeasure (measure_pmf P) (Aa i \<inter> (A \<inter> B))"

    have f1: "(\<Sum>i::nat. ?f i) = (\<Sum>i::nat. emeasure (measure_pmf P) (Aa i \<inter> (A - B)) \<cdot>
         ennreal ((?B_A + ?A_B) / ?A_B)) + 
        (\<Sum>i::nat. emeasure (measure_pmf P) (Aa i \<inter> (A \<inter> B)))"
      apply (rule sym, rule suminf_add)
      apply blast
      by blast
    have f2: "(\<Sum>i::nat. emeasure (measure_pmf P) (Aa i \<inter> (A - B)) \<cdot>
         ennreal ((?B_A + ?A_B) / ?A_B))
        = (\<Sum>i::nat. emeasure (measure_pmf P) (Aa i \<inter> (A - B))) \<cdot>
         ennreal ((?B_A + ?A_B) / ?A_B)"
      by simp
    have f2: "(\<Union>i. Aa i) = \<Union> (range Aa)"
      by blast
    then have f3: "((\<Union>i. Aa i) \<inter> (A - B)) = (\<Union>i. Aa i \<inter> (A - B))"
      by blast
    then have f3': "((\<Union>i. Aa i) \<inter> (A  \<inter> B)) = (\<Union>i. Aa i \<inter> (A \<inter> B))"
      by blast
    have f4: "(\<Sum>i::nat. emeasure (measure_pmf P) (Aa i \<inter> (A - B)))
      = emeasure (measure_pmf P) (\<Union>i. Aa i \<inter> (A - B))"
      apply (rule suminf_emeasure)
      apply simp
      by (meson "*"(2) disjoint_family_subset semilattice_inf_class.inf.absorb_iff2 semilattice_inf_class.inf_left_idem)
    also have f4': "... = emeasure (measure_pmf P) (\<Union> (range Aa) \<inter> (A - B))"
      using f3 by simp
    have f5: "(\<Sum>i::nat. emeasure (measure_pmf P) (Aa i \<inter> (A \<inter> B)))
      = emeasure (measure_pmf P) (\<Union>i. Aa i \<inter> (A \<inter> B))"
      apply (rule suminf_emeasure)
      apply simp
      by (meson "*"(2) disjoint_family_subset semilattice_inf_class.inf.absorb_iff2 semilattice_inf_class.inf_left_idem)
    have f5': "... = emeasure (measure_pmf P) (\<Union> (range Aa) \<inter> (A \<inter> B))"
      using f3' by simp
    have f6: "(\<Sum>i::nat. ?f i) = (\<Sum>i::nat. emeasure (measure_pmf P) (Aa i \<inter> (A - B))) \<cdot>
         ennreal ((?B_A + ?A_B) / ?A_B)
        + (\<Sum>i::nat. emeasure (measure_pmf P) (Aa i \<inter> (A \<inter> B)))"
      using f1 f2 by simp
    have f6': "... = emeasure (measure_pmf P) (\<Union> (range Aa) \<inter> (A - B)) \<cdot>
         ennreal ((?B_A + ?A_B) / ?A_B)
        + emeasure (measure_pmf P) (\<Union> (range Aa) \<inter> (A \<inter> B))"
      using f4 f4' f5 f5' by simp
    then show "(\<Sum>i::nat. ?f i) = 
     emeasure (measure_pmf P) (\<Union> (range Aa) \<inter> (A - B)) \<cdot>
     ennreal ((?B_A + ?A_B) / ?A_B) +
     emeasure (measure_pmf P) (\<Union> (range Aa) \<inter> (A \<inter> B))"
      using f6 by simp
  qed

lemma prob_space_proj_f:
  fixes P::"'a pmf" and A::"'a set" and B::"'a set"
  assumes "(\<Sum>\<^sub>a i\<in>A \<union> B . pmf P i) = (1::real)"
  assumes "(\<Sum>\<^sub>a i\<in>A-B . pmf P i) > (0::real)"
  assumes "(\<Sum>\<^sub>a i\<in>B-A . pmf P i) > (0::real)"
  shows "prob_space (\<F> A B P)"
  apply (intro prob_spaceI)
  apply (simp add: prob_space_def proj_f_def)
  proof -
    let ?A_B = "infsetsum (pmf P) (A-B)"
    let ?B_A = "infsetsum (pmf P) (B-A)"
    let ?A_and_B = "infsetsum (pmf P) (A \<inter> B)"
    let ?em_A_and_B = "emeasure (measure_pmf P) (A \<inter> B)"
    let ?em_A_B = "emeasure (measure_pmf P) (A - B)"
    let ?em_B_A = "emeasure (measure_pmf P) (B - A)"
    have f0: "(\<Sum>\<^sub>a i\<in>A \<union> B . pmf P i) = (\<Sum>\<^sub>a i\<in>(A \<inter> B) \<union> (A-B) \<union> (B-A)  . pmf P i)"
      by (simp add: Int_Diff_Un)
    also have f0': "...=?A_B + ?B_A + ?A_and_B"
      by (smt Diff_Diff_Int Un_Diff_Int calculation infsetsum_Diff infsetsum_Un_Int 
            lattice_class.inf_sup_aci(1) pmf_abs_summable semilattice_sup_class.sup_ge1)
    have f1: "(space
            (measure_of UNIV UNIV
              (\<lambda>AA::'a set.
                  emeasure (measure_pmf P) (AA \<inter> (A - B)) \<cdot>
                  ennreal ((?B_A + ?A_B) / ?A_B) +
                  emeasure (measure_pmf P) (AA \<inter> (A \<inter> B))))) = UNIV"
      by (simp add: space_measure_of_conv)
    have f2: "emeasure
          (measure_of UNIV UNIV
            (\<lambda>AA::'a set.
                emeasure (measure_pmf P) (AA \<inter> (A - B)) \<cdot>
                ennreal ((?B_A + ?A_B) / ?A_B) +
                emeasure (measure_pmf P) (AA \<inter> (A \<inter> B)))) UNIV = 
          (\<lambda>AA::'a set.
                emeasure (measure_pmf P) (AA \<inter> (A - B)) \<cdot>
                ennreal ((?B_A + ?A_B) / ?A_B) +
                emeasure (measure_pmf P) (AA \<inter> (A \<inter> B))) UNIV"
      using proj_f_emeasure by (metis proj_f_def sets_measure_pmf space_measure_pmf)
    have f3: "?em_A_B = ?A_B"
      by (simp add: measure_pmf.emeasure_eq_measure measure_pmf_conv_infsetsum)
    have f4: "?em_A_B > 0"
      using assms(2) by (simp add: f3)
    have f5: "?B_A = ?em_B_A"
      by (simp add: measure_pmf.emeasure_eq_measure measure_pmf_conv_infsetsum)
    have f5': "?A_B + ?B_A
      = ?em_A_B + ?em_B_A"
      by (simp add: f3 f5 infsetsum_nonneg)
    have f5'': "(?A_B + ?B_A) / ?A_B
      = (?em_A_B + ?em_B_A) / ?em_A_B"
      by (smt assms(2) assms(3) divide_ennreal f3 f5')
    have f5''': "?A_B \<cdot> ((?B_A + ?A_B)/?A_B) = (?B_A + ?A_B)"
      using assms(2) by auto
    have f6: "(\<lambda>AA::'a set.
                emeasure (measure_pmf P) (AA \<inter> (A - B)) \<cdot>
                ennreal ((?B_A + ?A_B) / ?A_B) +
                emeasure (measure_pmf P) (AA \<inter> (A \<inter> B))) UNIV
      = (
          ?em_A_B \<cdot>
          ennreal ((?B_A + ?A_B) / ?A_B) +
          ?em_A_and_B)"
      by auto
    have f7: "... = (
          ennreal ?A_B \<cdot> ((?B_A + ?A_B) / ?A_B) +
          ?em_A_and_B)"
      using f3 f5 f5'' by (simp add: add.commute)
    have f8: "... = (ennreal ?A_B \<cdot> ((?B_A + ?A_B) / ?A_B) +
          ennreal ?A_and_B)"
      by (simp add: measure_pmf.emeasure_eq_measure measure_pmf_conv_infsetsum)
    have f9: "... = (ennreal (?B_A + ?A_B) + ennreal ?A_and_B)"
      using f5''' by (smt assms(2) ennreal_mult')
    have f10: "...= ennreal (?B_A + ?A_B + ?A_and_B)"
      by (simp add: infsetsum_nonneg)
    have f11: "... = ennreal (1)"
      using f0 f0' by (simp add: assms(1))
    then show "emeasure
     (measure_of UNIV UNIV
       (\<lambda>AA::'a set.
           emeasure (measure_pmf P) (AA \<inter> (A - B)) \<cdot>
           ennreal ((infsetsum (pmf P) (B - A) + infsetsum (pmf P) (A - B)) / infsetsum (pmf P) (A - B)) +
           emeasure (measure_pmf P) (AA \<inter> (A \<inter> B))))
     UNIV = (1::ennreal)"
      by (simp add: f10 f2 f7 f8 f9)
  qed

lemma proj_f_AE:
  fixes P::"'a pmf" and A::"'a set" and B::"'a set"
  assumes "(\<Sum>\<^sub>a i\<in>A \<union> B . pmf P i) = (1::real)"
  assumes "(\<Sum>\<^sub>a i\<in>A-B . pmf P i) > (0::real)"
  assumes "(\<Sum>\<^sub>a i\<in>B-A . pmf P i) > (0::real)"
  shows "AE x::'a in \<F> A B P. \<not> Sigma_Algebra.measure (\<F> A B P) {x} = (0::real)"
  apply (rule AE_I[where N="{x::'a. ((
         emeasure (measure_pmf P) ({x} \<inter> (A-B)) = 0) \<and>
        (emeasure (measure_pmf P) ({x} \<inter> A \<inter> B) = 0))}"])
proof -
  have "{x::'a. x \<in> space (\<F> A B P) \<and> \<not> \<not> Sigma_Algebra.measure (\<F> A B P) {x} = (0::real)}
    = {x::'a. Sigma_Algebra.measure (\<F> A B P) {x} = (0::real)}"
    by (simp add: proj_f_space)
  also have "... = 
    {x::'a. Sigma_Algebra.measure (measure_of UNIV UNIV
      (\<lambda>AA. emeasure P (AA \<inter> (A-B)) * (((\<Sum>\<^sub>a i\<in>B-A . pmf P i) + (\<Sum>\<^sub>a i\<in>A-B . pmf P i))/(\<Sum>\<^sub>a i\<in>A-B . pmf P i))
      + emeasure P (AA \<inter> (A \<inter> B)))) {x} = (0::real)}"
    by (simp add: proj_f_def)
  also have "... = {x::'a. enn2real ((\<lambda>AA::'a set.
         emeasure (measure_pmf P) (AA \<inter> (A-B)) \<cdot>
         ennreal ((infsetsum (pmf P) (A-B) + infsetsum (pmf P) (B-A)) / infsetsum (pmf P) (A-B)) +
         emeasure (measure_pmf P) (AA \<inter> (A \<inter> B))) {x}) = (0::real)}"
    apply (simp add: measure_def)
    by (smt Collect_cong Sigma_Algebra.measure_def UNIV_I calculation proj_f_emeasure proj_f_space)
  also have "... = {x::'a. ((\<lambda>AA::'a set.
         emeasure (measure_pmf P) (AA \<inter> (A-B)) \<cdot>
         ennreal ((infsetsum (pmf P) (A-B) + infsetsum (pmf P) (B-A)) / infsetsum (pmf P) (A-B)) +
         emeasure (measure_pmf P) (AA \<inter> (A \<inter> B))) {x}) = (0::real)}"
    apply (simp add: enn2real_eq_0_iff)
    using ennreal_mult_eq_top_iff by auto
  also have "... = {x::'a. ((\<lambda>AA::'a set.
         emeasure (measure_pmf P) (AA \<inter> (A-B)) \<cdot>
         ennreal ((infsetsum (pmf P) (A-B) + infsetsum (pmf P) (B-A)) / infsetsum (pmf P) (A-B))) {x} = 0) \<and>
         ((\<lambda>AA::'a set. emeasure (measure_pmf P) (AA \<inter> (A \<inter> B))) {x} = 0)}"
    by simp
  also have "... = {x::'a. ((\<lambda>AA::'a set.
         emeasure (measure_pmf P) (AA \<inter> (A-B))) {x} = 0) \<and>
         ((\<lambda>AA::'a set. emeasure (measure_pmf P) (AA \<inter> (A \<inter> B))) {x} = 0)}"
    using assms(2) assms(3) by force
  also have "... = {x::'a. (
         emeasure (measure_pmf P) ( {x} \<inter> (A-B)) = 0) \<and>
         (emeasure (measure_pmf P) ({x} \<inter> (A \<inter> B)) = 0)}"
    by blast
  then show "{x::'a. x \<in> space (\<F> A B P) \<and> \<not> \<not> Sigma_Algebra.measure (\<F> A B P) {x} = (0::real)}
    \<subseteq> {x::'a. emeasure (measure_pmf P) ({x} \<inter> (A - B)) = (0::ennreal) \<and> 
             emeasure (measure_pmf P) ({x} \<inter> A \<inter> B) = (0::ennreal)}"
    by (metis (no_types, lifting) Collect_mono_iff Int_assoc calculation)
next
  have f1: "emeasure (\<F> A B P)
     {x::'a. emeasure (measure_pmf P) ({x} \<inter> (A - B)) = (0::ennreal) \<and> 
            emeasure (measure_pmf P) ({x} \<inter> A \<inter> B) = (0::ennreal)}
      = (\<lambda>AA. emeasure P (AA \<inter> (A-B)) * 
        (((\<Sum>\<^sub>a i\<in>B-A . pmf P i) + (\<Sum>\<^sub>a i\<in>A-B . pmf P i))/(\<Sum>\<^sub>a i\<in>A-B . pmf P i))  
        + emeasure P (AA \<inter> (A \<inter> B)))
        {x::'a. emeasure (measure_pmf P) ({x} \<inter> (A - B)) = (0::ennreal) \<and> 
            emeasure (measure_pmf P) ({x} \<inter> A \<inter> B) = (0::ennreal)}"
    by (rule proj_f_emeasure)
  have f2: "\<forall>i \<in> {x::'a. emeasure (measure_pmf P) ({x} \<inter> (A - B)) = (0::ennreal) \<and> 
            emeasure (measure_pmf P) ({x} \<inter> A \<inter> B) = (0::ennreal)} . 
        emeasure (measure_pmf P) ({i} \<inter> (A - B)) = (0::ennreal)"
    by blast
  have f3: "\<forall>i \<in> {x::'a. emeasure (measure_pmf P) ({x} \<inter> (A - B)) = (0::ennreal) \<and> 
            emeasure (measure_pmf P) ({x} \<inter> A \<inter> B) = (0::ennreal)} . 
        emeasure (measure_pmf P) ({i} \<inter> A \<inter> B) = (0::ennreal)"
    by blast
  have f4: "emeasure P ({x::'a. emeasure (measure_pmf P) ({x} \<inter> (A - B)) = (0::ennreal) \<and> 
            emeasure (measure_pmf P) ({x} \<inter> A \<inter> B) = (0::ennreal)} \<inter> (A-B)) = 0"
    apply (rule pmf_measure_zero)
    by (simp add: Int_insert_right lattice_class.inf_sup_aci(1))
  have f5: "emeasure P ({x::'a. emeasure (measure_pmf P) ({x} \<inter> (A - B)) = (0::ennreal) \<and> 
            emeasure (measure_pmf P) ({x} \<inter> A \<inter> B) = (0::ennreal)} \<inter> (A \<inter> B)) = 0"
    apply (rule pmf_measure_zero)
    by (simp add: Int_insert_right lattice_class.inf_sup_aci(1))
  show "emeasure (\<F> A B P)
     {x::'a. emeasure (measure_pmf P) ({x} \<inter> (A - B)) = (0::ennreal) \<and> 
            emeasure (measure_pmf P) ({x} \<inter> A \<inter> B) = (0::ennreal)} = (0::ennreal)"
    using f1 f4 f5 by simp
next
  show "{x::'a.
     emeasure (measure_pmf P) ({x} \<inter> (A - B)) = (0::ennreal) \<and>
     emeasure (measure_pmf P) ({x} \<inter> A \<inter> B) = (0::ennreal)}
    \<in> sets (\<F> A B P)"
    by (simp add: proj_f_sets)
qed

(* declare [[ smt_timeout = 600 ]] *)

lemma proj_f_measure_pmf:
  fixes P::"'a pmf" and A::"'a set" and B::"'a set"
  assumes "(\<Sum>\<^sub>a i\<in>A \<union> B . pmf P i) = (1::real)"
  assumes "(\<Sum>\<^sub>a i\<in>A-B . pmf P i) > (0::real)"
  assumes "(\<Sum>\<^sub>a i\<in>B-A . pmf P i) > (0::real)"
  shows "(measure_pmf (Abs_pmf (\<F> A B P))) = \<F> A B P"
  apply (rule pmf.Abs_pmf_inverse)
  apply (auto)
  using assms(1) assms(2) assms(3) prob_space_proj_f apply blast
  apply (simp add: proj_f_sets)
  using assms(1) assms(2) assms(3) proj_f_AE by blast

lemma enn2real_distrib: "enn2real (A*c + A*d) = enn2real (A*(c+d))"
  by (simp add: distrib_left)

lemma proj_f_sum_eq_1:
  fixes P::"'a pmf" and A::"'a set" and B::"'a set"
  assumes "(\<Sum>\<^sub>a i\<in>A \<union> B . pmf P i) = (1::real)"
  assumes "(\<Sum>\<^sub>a i\<in>A-B . pmf P i) > (0::real)"
  assumes "(\<Sum>\<^sub>a i\<in>B-A . pmf P i) > (0::real)"
  shows "(\<Sum>\<^sub>a x::'a | x \<in> A . pmf (Abs_pmf (\<F> A B P)) x) = (1::real)"
proof -
  have f1: "(\<Sum>\<^sub>a x::'a | x \<in> A . pmf (Abs_pmf (\<F> A B P)) x) 
            = measure (measure_pmf (Abs_pmf (\<F> A B P))) A"
    by (simp add: measure_pmf_conv_infsetsum)
  then have f2: "... = measure (\<F> A B P) A"
    using assms by (simp add: proj_f_measure_pmf)
  then have f3: "... = enn2real (emeasure (measure_of (space P) (sets P)
    (\<lambda>AA. emeasure P (AA \<inter> (A-B)) * (
      ((\<Sum>\<^sub>a i\<in>B-A . pmf P i) + (\<Sum>\<^sub>a i\<in>A-B . pmf P i))/(\<Sum>\<^sub>a i\<in>A-B . pmf P i))
    + emeasure P (AA \<inter> (A \<inter> B)))) A)"
    by (simp add: proj_f_def measure_def)
  then have f4: "... = enn2real ((\<lambda>AA. emeasure P (AA \<inter> (A-B)) * 
      (((\<Sum>\<^sub>a i\<in>B-A . pmf P i) + (\<Sum>\<^sub>a i\<in>A-B . pmf P i))/(\<Sum>\<^sub>a i\<in>A-B . pmf P i))
    + emeasure P (AA \<inter> (A \<inter> B))) A)"
    by (simp add: Sigma_Algebra.measure_def proj_f_emeasure)
  then have f5: "... = enn2real (emeasure P ((A-B)) * 
      (((\<Sum>\<^sub>a i\<in>B-A . pmf P i) + (\<Sum>\<^sub>a i\<in>A-B . pmf P i))/(\<Sum>\<^sub>a i\<in>A-B . pmf P i))
    + emeasure P ((A \<inter> B)))"
    by (metis (no_types, lifting) Int_Diff semilattice_inf_class.inf.idem 
        semilattice_inf_class.inf_left_idem)
  then show ?thesis
    by (metis Int_commute Sigma_Algebra.measure_def assms(1) assms(2) assms(3) 
        bounded_semilattice_inf_top_class.inf_top.right_neutral emeasure_pmf_UNIV 
        enn2real_eq_1_iff f1 proj_f_emeasure proj_f_measure_pmf)
qed

end