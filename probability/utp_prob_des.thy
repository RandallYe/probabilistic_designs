section \<open> Probabilistic Designs \<close>

text \<open> This is the mechanisation of \emph{probabilistic designs}~\cite{Jifeng2004,Woodcock2019} in 
Isabelle/UTP.\<close>

theory utp_prob_des
  imports "UTP-Calculi.utp_wprespec" "UTP-Designs.utp_designs" "HOL-Probability.Probability_Mass_Function"
  "HOL-Probability.SPMF"
begin recall_syntax

purge_notation inner (infix "\<bullet>" 70)
(* Coercive: see section 12.4 in isar_ref 

  Register a new coercion function pmf:: "'a pmf \<Rightarrow> 'a \<Rightarrow> real", which allows 
  the user to omit explicit type conversions. Type inference will add them as 
  necessary when parsing a term.
  For example, users can write "$prob s" instead of explicit conversion "pmf $prob s" 
*)
declare [[coercion pmf]]

alphabet 's prss = 
  prob :: "'s pmf"

text \<open> If the probabilities of two disjoint sample sets sums up to 1, then the probability of the
  first set is equal to 1 minus the probability of the second set. \<close>

lemma pmf_disj_set:
  assumes "X \<inter> Y = {}"
  shows "((\<Sum>\<^sub>a i\<in>(X \<union> Y). pmf M i) = 1) = ((\<Sum>\<^sub>a i\<in>X. pmf M i) = 1 - (\<Sum>\<^sub>a i\<in>Y. pmf M i))"
  by (metis assms diff_eq_eq infsetsum_Un_disjoint pmf_abs_summable)

no_utp_lift ndesign wprespec uwp

text \<open>
  Probabilistic designs (@{text "('s, 's) rel_pdes"}), that map the standard state space to the 
probabilistic state space, are heterogeneous. 
\<close>

type_synonym ('a, 'b) rel_pdes = "('a, 'b prss) rel_des"
type_synonym 's hrel_pdes = "('s, 's) rel_pdes"
type_synonym 's hrel_hpdes = "('s prss, 's prss) rel_des"

translations
  (type) "('a, 'b) rel_pdes" <= (type) "('a, 'b prss) rel_des"

text \<open>
  @{term "forget_prob"} is a non-homogeneous design as a forgetful function that maps a discrete
probability distribution @{term "$prob"} at initial observation to a final state.
\<close>
definition forget_prob :: "('s prss, 's) rel_des" ("\<^bold>f\<^bold>p") where
[upred_defs]: "forget_prob = U(true \<turnstile>\<^sub>n ($prob($\<^bold>v\<acute>) > 0))"

text \<open>
  The weakest prespecification of a standard design @{text "D"} wrt @{text "\<^bold>f\<^bold>p"} is the weakest 
probabilistic design, as an embedding of @{text "D"} in the probabilistic world through @{text "\<K>"}.
\<close>
definition pemb :: "('a, 'b) rel_des \<Rightarrow> ('a, 'b) rel_pdes" ("\<K>")
  where [upred_defs]: "pemb D = \<^bold>f\<^bold>p \\ D"

lemma pemb_mono: "P \<sqsubseteq> Q \<Longrightarrow> \<K>(P) \<sqsubseteq> \<K>(Q)"
  by (metis (mono_tags, lifting) dual_order.trans order_refl pemb_def wprespec)

lemma wdprespec: "(true \<turnstile>\<^sub>n R) \\ (p \<turnstile>\<^sub>n Q) = (p \<turnstile>\<^sub>n (R \\ Q))"
  by (rel_auto)

(*
lemma "R wp (&\<^bold>v =\<^sub>u \<guillemotleft>s'\<guillemotright>) = Pre(R\<lbrakk>\<guillemotleft>s'\<guillemotright>/$\<^bold>v\<acute>\<rbrakk>)"
  apply (simp add: wp_upred_def)
  by (rel_auto)
*)
declare [[show_types]]
(*
term "U((\<Sum>\<^sub>a i\<in>\<lbrakk>p\<rbrakk>\<^sub>p. $prob i) = 1)"
term "\<^U>((\<Sum>\<^sub>a i\<in>{s'.(R wp (&\<^bold>v = s'))\<^sup><}. $prob\<acute> i) = 1)"
*)
lemma pemb_form:
  fixes R :: "('a, 'b) urel"
  shows "\<^U>(($prob($\<^bold>v\<acute>) > 0) \\ R) = \<^U>((\<Sum>\<^sub>a i\<in>{s'.(R wp (&\<^bold>v = s'))\<^sup><}. $prob\<acute> i) = 1)" (is "?lhs = ?rhs")
proof -
  have "?lhs = \<^U>((\<not> (\<not> R) ;; (0 < $prob\<acute>$\<^bold>v)))"
    by (rel_auto)
  also have "... = \<^U>((\<Sum>\<^sub>a i\<in>{s'.(R wp (&\<^bold>v = s'))\<^sup><}. $prob\<acute> i) = 1)"
    apply (rel_auto)
    apply (metis (no_types, lifting) infsetsum_pmf_eq_1 mem_Collect_eq pmf_positive subset_eq)
    apply (metis AE_measure_pmf_iff UNIV_I measure_pmf.prob_eq_1 measure_pmf_conv_infsetsum mem_Collect_eq set_pmf_eq' sets_measure_pmf)
    done
  finally show ?thesis .
qed

text \<open>
  Embedded standard designs are probabilistic designs~\cite[Theorem 1]{Woodcock2019} and
~\cite[Theorem 3.6]{Jifeng2004}.
\<close>
lemma prob_lift [ndes_simp]:
  fixes R :: "('a, 'b) urel" and p :: "'a upred"
  shows "\<K>(p \<turnstile>\<^sub>n R) = \<^U>(p \<turnstile>\<^sub>n ((\<Sum>\<^sub>a i\<in>{s'.(R wp (&\<^bold>v = s'))\<^sup><}. $prob\<acute> i) = 1))"
proof -
  have 1:"\<K>(p \<turnstile>\<^sub>n R) = \<^U>(p \<turnstile>\<^sub>n (($prob($\<^bold>v\<acute>) > 0) \\ R))"
    by (rel_auto)
  have 2:"\<^U>(($prob($\<^bold>v\<acute>) > 0) \\ R) = \<^U>((\<Sum>\<^sub>a i\<in>{s'.(R wp (&\<^bold>v = s'))\<^sup><}. $prob\<acute> i) = 1)"
    by (simp add: pemb_form)
  show ?thesis
    by (simp add: "1" "2")
qed

(*
text \<open>
  Inverse of @{text "\<K>"}~\cite[Corollary 3.7]{Jifeng2004}: 
embedding a standard design (P) in the probabilistic world then forgetting its probability 
distribution is equal to P itself.
\<close>
lemma pemb_inv:
  assumes "P is \<^bold>N"
  shows "\<K>(P) ;; \<^bold>f\<^bold>p = P"
proof -
  obtain pre\<^sub>p post\<^sub>p
    where p:"P = (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p)"
    using assms by (metis ndesign_form)
  have f1: "\<K>(pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) ;; \<^bold>f\<^bold>p = (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p)"
    apply (simp add: prob_lift forget_prob_def)
    apply (ndes_simp)
    apply (rel_auto)
    proof -
      fix ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and morea::"'b" and prob\<^sub>v::"'b pmf"
      assume a1: "(\<Sum>\<^sub>ax::'b | \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real)"
      assume a2: "(0::real) < pmf prob\<^sub>v morea"
      show "\<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, morea)"
      proof (rule ccontr)
        assume aa1: "\<not> \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, morea)"
        have f1: "(\<Sum>\<^sub>ax::'b \<in> {x. \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, x)} \<union> {morea}. pmf prob\<^sub>v x) = 
          (\<Sum>\<^sub>ax::'b \<in> {x. \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, x)}. pmf prob\<^sub>v x) + 
          (\<Sum>\<^sub>ax::'b \<in> {morea}. pmf prob\<^sub>v x)"
          unfolding infsetsum_altdef abs_summable_on_altdef
          apply (subst set_integral_Un, auto)
          using aa1 apply (simp)
          using abs_summable_on_altdef assms apply fastforce
          using abs_summable_on_altdef by blast
        then have f2: "... = 1 + pmf prob\<^sub>v morea"
          using a1 by auto
        then have f3: "... > 1"
          using a2 by linarith
        show "False"
          using f1 f2 f3
          by (metis f1 f2 measure_pmf.prob_le_1 measure_pmf_conv_infsetsum not_le)
      qed
    next
      fix ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and morea::"'b"
      assume a1: "\<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, morea)"
      have f1: "\<forall>x. (pmf (pmf_of_list [(morea, 1::real)]) x) = (if x = morea then (1::real) else 0)"
        by (simp add: pmf_of_list_wf_def pmf_pmf_of_list)
      have f2: "(\<Sum>\<^sub>ax::'b | \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, x). pmf (pmf_of_list [(morea, 1::real)]) x) = 
        (\<Sum>\<^sub>ax::'b | \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, x). (if x = morea then (1::real) else 0))"
        using f1 by simp
      have f3: "... = (1::real)"
        proof -
          have "(\<Sum>\<^sub>ax::'b | \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, x). if x = morea then 1::real else (0::real)) =
            (\<Sum>\<^sub>ax::'b \<in> {morea} \<union> {t. \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, t) \<and> t \<noteq> morea}. 
              if x = morea then 1::real else (0::real))"
            proof -
              have "{t. \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, t)} = {morea} \<union> {t. \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, t) \<and> t \<noteq> morea}"
                using a1 by blast
              then show ?thesis
                by presburger
            qed
          also have "... = (\<Sum>\<^sub>ax::'b \<in> {morea}. if x = morea then 1::real else (0::real)) +
             (\<Sum>\<^sub>ax::'b \<in> {t. \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, t) \<and> t \<noteq> morea}. if x = morea then 1::real else (0::real))"
            unfolding infsetsum_altdef abs_summable_on_altdef
            apply (subst set_integral_Un, auto)
            using abs_summable_on_altdef apply fastforce
            using abs_summable_on_altdef by (smt abs_summable_on_0 abs_summable_on_cong mem_Collect_eq)
          also have "... = (1::real) + 
            (\<Sum>\<^sub>ax::'b \<in> {t. \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, t) \<and> t \<noteq> morea}. if x = morea then 1::real else (0::real))"
            by simp
          also have "... = (1::real)"
            by (smt add_cancel_left_right infsetsum_all_0 mem_Collect_eq)
          then show ?thesis
            by (simp add: calculation)
        qed
      show "\<exists>prob\<^sub>v::'b pmf.
            (\<Sum>\<^sub>ax::'b | \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real) \<and> (0::real) < pmf prob\<^sub>v morea"
        apply (rule_tac x = "pmf_of_list [(morea, 1.0)]" in exI)
        apply (auto)
        apply (simp add: f1 f2 f3)
        by (simp add: pmf_of_list_wf_def pmf_pmf_of_list)
    qed
    show ?thesis
      using f1 by (simp add: p)
qed
*)
no_utp_lift usubst (0) subst (1)

subsection \<open> wplus \<close>
text \<open>
  Two pmfs can be joined into one by their corresponding weights via @{text "P +\<^bsub>w\<^esub> Q"} 
where @{text "w"} is the weight of P.
\<close>
definition wplus :: "'a pmf \<Rightarrow> real \<Rightarrow> 'a pmf \<Rightarrow> 'a pmf" ("(_ +\<^bsub>_\<^esub> _)" [64, 0, 65] 64) where
"wplus P w Q = join_pmf (pmf_of_list [(P, w), (Q, 1 - w)])"

text \<open>
  Query of the probability value of a state @{text "i"} in a joined probability distribution is just 
the summation of the query of @{text "i"} in P by its weight @{text "w"} and 
the query of @{text "i"} in Q by its weight @{text "(1 - w)"}.
\<close>
lemma pmf_wplus: 
  assumes "w \<in> {0..1}"
  shows "pmf (P +\<^bsub>w\<^esub> Q) i = pmf P i * w + pmf Q i * (1 - w)"
proof -
  from assms have pmf_wf_list: "pmf_of_list_wf [(P, w), (Q, 1 - w)]"
    by (auto intro!: pmf_of_list_wfI) 
  show ?thesis
  proof (cases "w \<in> {0<..<1}")
    case True
    hence set_pmf:"set_pmf (pmf_of_list [(P, w), (Q, 1 - w)]) = {P, Q}"
      by (subst set_pmf_of_list_eq, auto simp add: pmf_wf_list)
    thus ?thesis
    proof (cases "P = Q")
      case True
      from assms show ?thesis
        apply (auto simp add: wplus_def join_pmf_def pmf_bind)
        apply (subst integral_measure_pmf[of "{P, Q}"])
          apply (auto simp add: set_pmf_of_list pmf_wf_list set_pmf pmf_pmf_of_list)
        apply (simp add: True)
        apply (metis distrib_right eq_iff_diff_eq_0 le_add_diff_inverse mult.commute mult_cancel_left1)
        done
    next
      case False
      then show ?thesis
        apply (auto simp add: wplus_def join_pmf_def pmf_bind)
        apply (subst integral_measure_pmf[of "{P, Q}"])
          apply (auto simp add: set_pmf_of_list pmf_wf_list set_pmf pmf_pmf_of_list)
        done
    qed
  next
    case False
    thm disjE
    with assms have "w = 0 \<or> w = 1"
      by (auto)
    with assms show ?thesis 
    proof (erule_tac disjE, simp_all)
      assume w: "w = 0"
      with pmf_wf_list have "set_pmf (pmf_of_list [(P, w), (Q, 1 - w)]) = {Q}"
        apply (simp add: pmf_of_list_remove_zeros(2)[THEN sym])
        apply (subst set_pmf_of_list_eq, auto simp add: pmf_of_list_wf_def)
        done
      with w show "pmf (P +\<^bsub>0\<^esub> Q) i = pmf Q i"
        apply (auto simp add: wplus_def join_pmf_def pmf_bind pmf_wf_list pmf_of_list_remove_zeros(2)[THEN sym])
        apply (subst integral_measure_pmf[of "{Q}"])
          apply (simp_all add: set_pmf_of_list_eq pmf_pmf_of_list pmf_of_list_wf_def)
        done
    next
      assume w: "w = 1"
      with pmf_wf_list have "set_pmf (pmf_of_list [(P, w), (Q, 1 - w)]) = {P}"
        apply (simp add: pmf_of_list_remove_zeros(2)[THEN sym])
        apply (subst set_pmf_of_list_eq, auto simp add: pmf_of_list_wf_def)
        done
      with w show "pmf (P +\<^bsub>1\<^esub> Q) i = pmf P i"
        apply (auto simp add: wplus_def join_pmf_def pmf_bind pmf_wf_list pmf_of_list_remove_zeros(2)[THEN sym])
        apply (subst integral_measure_pmf[of "{P}"])
          apply (simp_all add: set_pmf_of_list_eq pmf_pmf_of_list pmf_of_list_wf_def)
        done
    qed
  qed
qed

lemma wplus_commute: 
  assumes "w \<in>{0..1}"
  shows "P +\<^bsub>w\<^esub> Q = Q +\<^bsub>(1 - w)\<^esub> P"
  using assms by (auto intro: pmf_eqI simp add: pmf_wplus)

lemma wplus_idem: 
  assumes "w \<in>{0..1}"
  shows "P +\<^bsub>w\<^esub> P = P"
  using assms
  apply (rule_tac pmf_eqI)
  apply (simp add: pmf_wplus)
  by (metis le_add_diff_inverse mult.commute mult_cancel_left2 ring_class.ring_distribs(2))

lemma wplus_zero: "P +\<^bsub>0\<^esub> Q = Q"
  by (auto intro: pmf_eqI simp add: pmf_wplus)

lemma wplus_one: "P +\<^bsub>1\<^esub> Q = P"
  by (auto intro: pmf_eqI simp add: pmf_wplus)

text \<open>
  This is used to prove the associativity of probabilistic choice: @{text "prob_choice_assoc"}.
\<close>
lemma wplus_assoc:
  assumes "w\<^sub>1 \<in> {0..1}" "w\<^sub>2 \<in> {0..1}"
  assumes "(1-w\<^sub>1)*(1-w\<^sub>2)=(1-r\<^sub>2)" "w\<^sub>1=r\<^sub>1*r\<^sub>2"
  shows "P +\<^bsub>w\<^sub>1\<^esub> (Q +\<^bsub>w\<^sub>2\<^esub> R) = (P +\<^bsub>r\<^sub>1\<^esub> Q) +\<^bsub>r\<^sub>2\<^esub> R"
proof (cases "w\<^sub>1 = 0 \<and> w\<^sub>2 = 0")
  case True
  then show ?thesis 
    proof -
      from assms(3-4) have t1: "r\<^sub>2=0"
        by (simp add: True)
      then show ?thesis
        by (simp add: wplus_zero True t1)
    qed
next
  case False
  from assms(3) have f1: "r\<^sub>2 = w\<^sub>1+w\<^sub>2-w\<^sub>1*w\<^sub>2"
    proof -
      have f1: "\<forall>r ra. (ra::real) + - r = 0 \<or> \<not> ra = r"
        by simp
      have f2: "\<forall>r ra rb rc. (rc::real) \<cdot> rb + - (ra \<cdot> r) = rc \<cdot> (rb + - r) + (rc + - ra) \<cdot> r"
        by (simp add: mult_diff_mult)
      have f3: "\<forall>r ra. (ra::real) + (r + - ra) = r + 0"
        by fastforce
      have f4: "\<forall>r ra. (ra::real) + ra \<cdot> r = ra \<cdot> (1 + r)"
        by (simp add: distrib_left)
      have f5: "\<forall>r ra. (ra::real) + - r + 0 = ra + - r"
        by linarith
      have f6: "\<forall>r ra. (0::real) + (ra + - r) = ra + - r"
        by simp
      have "1 + - w\<^sub>2 + - (w\<^sub>1 \<cdot> (1 + - w\<^sub>2)) = 1 + (0 + - r\<^sub>2)"
        using f2 f1 by (metis (no_types) add.left_commute add_uminus_conv_diff assms(3) mult.left_neutral)
      then have "1 + (w\<^sub>1 + w\<^sub>1 \<cdot> - w\<^sub>2 + - r\<^sub>2) = 1 + - w\<^sub>2"
        using f6 f5 f4 f3 by (metis (no_types) add.left_commute)
    then show ?thesis
    by linarith
    qed 
  then have f2: "r\<^sub>2 \<in> {0..1}"
    using assms(1-2) by (smt assms(3) atLeastAtMost_iff mult_le_one sum_le_prod1)
  from f1 have f2': "(w\<^sub>1+w\<^sub>2-w\<^sub>1*w\<^sub>2) \<ge> w\<^sub>1"
    using assms(1) assms(2) mult_left_le_one_le by auto
  from f1 have f3: "r\<^sub>1 = w\<^sub>1/(w\<^sub>1+w\<^sub>2-w\<^sub>1*w\<^sub>2)"
    by (metis False add.commute add_diff_eq assms(4) diff_add_cancel 
        mult_zero_left mult_zero_right nonzero_eq_divide_eq)
  show ?thesis 
  proof (cases "w\<^sub>1 = 0")
    case True
    from f3 have ft1: "r\<^sub>1 = 0" 
      by (simp add: True)
    from f1 have ft2: "r\<^sub>2 = w\<^sub>2"
      by (simp add: True)
    then show ?thesis 
      using ft1 ft2 assms(1-2)
      by (simp add: True wplus_zero)
  next
    case False
    from f3 f2' have ff1: "r\<^sub>1 \<le> 1"
      using False
      by (metis assms(4) atLeastAtMost_iff eq_iff f1 f2 le_cases le_numeral_extra(4) mult_cancel_right2 mult_right_mono)
    have ff2: "r\<^sub>1 \<ge> 0"
      by (smt False assms(1) assms(4) atLeastAtMost_iff f2 mult_not_zero zero_le_mult_iff)
    from ff1 and ff2 have ff3: "r\<^sub>1 \<in> {0..1}"
      by simp
    have ff4: "w\<^sub>2 * (1 - w\<^sub>1) = (1 - r\<^sub>1) * r\<^sub>2"
      using f1 f3 False assms
      by (metis (no_types, hide_lams) add_diff_eq diff_add_eq_diff_diff_swap diff_diff_add 
          diff_diff_eq2 eq_iff_diff_eq_0 mult.commute mult.right_neutral right_diff_distrib' right_minus_eq)
    then show ?thesis 
      using assms(1-2) f2 ff3 apply (rule_tac pmf_eqI)
      apply (simp add: assms(1-2) f2 ff3 pmf_wplus)
      using assms(3-4) ff4 
      by (metis (no_types, hide_lams) add.commute add.left_commute mult.assoc mult.commute)
  qed
qed

(*
typedef 'a ccpmf = "{p :: 'a pmf. \<forall>r \<in> {0..1}. p +\<^bsub>r\<^esub> p = p}"
  by (simp add: wplus_idem)
*)

(*
definition spmf_to_pmf:: "'a pmf \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a pmf" where
"spmf_to_pmf p A B = join_pmf (pmf_of_list [((pdres_spmf (A-B) P), 1), ((pdres_spmf (B-A) P), 1)])"

definition pdres1' :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a pmf \<Rightarrow> 'a pmf" where
"pdres1' A B P = (pdres_spmf (A-B) P) (pdres_spmf (B-A) P)"

term "nn_integral"
term "(SUP g \<in> {g. simple_function M g \<and> g \<le> f}. integral\<^sup>S M g)"

lemma 
  fixes P::"'a pmf"
  assumes "(\<Sum>\<^sub>a i\<in>A \<union> B . pmf P i) = (1::real)"
  assumes "(\<Sum>\<^sub>a i\<in>A . pmf P i) > (0::real)"
  assumes "(\<Sum>\<^sub>a i\<in>B . pmf P i) > (0::real)"
  shows "(\<Sum>\<^sub>a i\<in>A. pmf (pdres1 A B P) i) = (1::real)"
  apply (simp add: pdres1_def)
  apply (rule infsetsum_pmf_eq_1)
proof -
  from assms(2) have f1: "A \<noteq> {}"
    by auto
  have "pmf (embed_pmf (\<lambda>x. if x \<in> A \<and> x \<notin> B then pmf P x * 
          (1/((\<Sum>\<^sub>a i\<in>A . pmf P i) + (\<Sum>\<^sub>a i\<in>B . pmf P i)))
        else (0::real))) i = 
        (\<lambda>x. if x \<in> A \<and> x \<notin> B then pmf P x * 
          (1/((\<Sum>\<^sub>a i\<in>A . pmf P i) + (\<Sum>\<^sub>a i\<in>B . pmf P i)))
        else (0::real)) i"
    apply (rule pmf_embed_pmf)
    using assms(2) assms(3) apply auto[1]
    apply (simp add: nn_integral_def)
    sledgehammer
  proof -
    let ?f = "\<lambda>x. ennreal
          (if x \<in> A \<and> \<not> x \<in> B then pmf P x \<cdot> ((1::real) / (infsetsum (pmf P) A + infsetsum (pmf P) B))
           else (0::real))"

    show "\<integral>\<^sup>+ (x::'a).
         ennreal
          (if x \<in> A \<and> \<not> x \<in> B then pmf P x \<cdot> ((1::real) / (infsetsum (pmf P) A + infsetsum (pmf P) B))
           else (0::real))
       \<partial>count_space UNIV =
    (1::ennreal)"
      apply (simp add: nn_integral_count_space)
    sorry
  have "pmf (pdres1 A B P) i = 
      pmf (embed_pmf (\<lambda>x. if x \<in> A \<and> x \<notin> B then pmf P x * (1/((\<Sum>\<^sub>a i\<in>A . pmf P i) + (\<Sum>\<^sub>a i\<in>B . pmf P i)))
        else (0::real))) i"
    apply (simp add: pdres1_def)
*)

subsection \<open> Probabilistic Choice \<close>
text \<open> We use parallel-by-merge in UTP to define the probabilistic choice operator. 
The merge predicate is the join of two distributions by their weights.
\<close>

definition prob_merge :: "real \<Rightarrow> (('s, 's prss, 's prss) mrg, 's prss) urel" ("\<^bold>P\<^bold>M\<^bsub>_\<^esub>") where
[upred_defs]: "prob_merge r = \<^U>($prob\<acute> = $0:prob +\<^bsub>\<guillemotleft>r\<guillemotright>\<^esub> $1:prob)"

lemma swap_prob_merge:
  assumes "r \<in> {0..1}"
  shows "swap\<^sub>m ;; \<^bold>P\<^bold>M\<^bsub>r\<^esub> = \<^bold>P\<^bold>M\<^bsub>1 - r\<^esub>"
  by (rel_auto, (metis assms wplus_commute)+)

abbreviation prob_des_merge :: "real \<Rightarrow> (('s des, 's prss des, 's prss des) mrg, 's prss des) urel" ("\<^bold>P\<^bold>D\<^bold>M\<^bsub>_\<^esub>") where
"\<^bold>P\<^bold>D\<^bold>M\<^bsub>r\<^esub> \<equiv> \<^bold>D\<^bold>M(\<^bold>P\<^bold>M\<^bsub>r\<^esub>)"

lemma swap_prob_des_merge:
  assumes "r \<in> {0..1}"
  shows "swap\<^sub>m ;; \<^bold>P\<^bold>D\<^bold>M\<^bsub>r\<^esub> = \<^bold>P\<^bold>D\<^bold>M\<^bsub>1 - r\<^esub>"
  by (metis assms swap_des_merge swap_prob_merge)

text \<open> The probabilistic choice operator is defined conditionally in order to satisfy unit and zero 
laws (@{text "prob_choice_one"} and @{term "prob_choice_zero"}) below. The definition of the operator 
follows~\cite[Definition 3.14]{Jifeng2004}. Actually use of @{text "P \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> Q"} directly for (r = 0) 
or (r = 1) cannot get the desired result (P or Q) as the precondition of merged designs cannot be 
discharged to the precondition of P or Q simply.
\<close>
definition prob_choice :: "'s hrel_pdes \<Rightarrow> real \<Rightarrow> 's hrel_pdes \<Rightarrow> 's hrel_pdes" ("(_ \<oplus>\<^bsub>_\<^esub> _)" [164, 0, 165] 164) 
  where [upred_defs]:
"prob_choice P r Q \<equiv> 
  if r \<in> {0<..<1} 
  then P \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> Q
  else (if r = 0 
        then Q 
        else (if r = 1 
              then P 
              else \<top>\<^sub>D))"

(* Use Morgan's logical constant to construct a probabilistic choice of which the weight is a UTP 
expression *)
text \<open> The r in @{text "P \<oplus>\<^bsub>r\<^esub> Q"} is a real number (HOL terms). Sometimes, however, we want a 
similar operator of which the weight is a UTP expression (therefore it depends on the values of 
state variables). For example, @{text "P \<oplus>\<^bsub>U(1/real (\<guillemotleft>N\<guillemotright>-i))\<^esub> Q"} in a uniform selection algorithms 
where @{text "&i"} is a state variable. Hence, @{text "(P \<oplus>\<^sub>e\<^bsub>E\<^esub> Q)"} is defined below, which is 
inspired by Morgan's logical constant~\cite{Morgan1990a}.
\<close>
definition prob_choice_r :: "('a, 'a) rel_pdes \<Rightarrow> (real, 'a) uexpr \<Rightarrow> ('a, 'a) rel_pdes \<Rightarrow> ('a, 'a) rel_pdes"
  ("(_ \<oplus>\<^sub>e\<^bsub>_\<^esub> _)" [164, 0, 165] 164)
where [upred_defs]:
"prob_choice_r P E Q \<equiv> (con\<^sub>D R \<bullet> (II\<^sub>D \<triangleleft> U(\<guillemotleft>R\<guillemotright> = E) \<triangleright>\<^sub>D \<bottom>\<^sub>D) ;; (P \<oplus>\<^bsub>R\<^esub> Q))"

lemma prob_choice_commute: "r \<in> {0..1} \<Longrightarrow> P \<oplus>\<^bsub>r\<^esub> Q = Q \<oplus>\<^bsub>1 - r\<^esub> P"
  by (simp add: prob_choice_def swap_prob_des_merge[THEN sym], metis par_by_merge_commute_swap)

lemma prob_choice_one:
  "P \<oplus>\<^bsub>1\<^esub> Q = P"
  by (simp add: prob_choice_def)

lemma prob_choice_zero:
  "P \<oplus>\<^bsub>0\<^esub> Q = Q"
  by (simp add: prob_choice_def)

lemma prob_choice_r:
  "r \<in> {0<..<1} \<Longrightarrow> P \<oplus>\<^bsub>r\<^esub> Q = P \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> Q"
  by (simp add: prob_choice_def)

lemma prob_choice_inf_simp:
  "(\<Sqinter> r \<in> {0<..<1} \<bullet> (P \<oplus>\<^bsub>r\<^esub> Q)) = (\<Sqinter> r \<in> {0<..<1} \<bullet>  P \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> Q)"
  using prob_choice_r 
  apply (simp add: prob_choice_def)
  by (simp add: UINF_as_Sup_collect image_def)

text \<open> @{text "inf_is_exists"} helps to establish the fact that our theorem regarding nondeterminism
~\cite[Sect. 8]{Woodcock2019} is the same as He's~\cite[Theorem 3.10]{Jifeng2004}.
\<close>
lemma inf_is_exists:
  "(\<Sqinter> r \<in> {0<..<1} \<bullet>  (p \<turnstile>\<^sub>n P) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> (q \<turnstile>\<^sub>n Q)) 
 = (\<^bold>\<exists> r \<in> \<^U>({0<..<1}) \<bullet>  (p \<turnstile>\<^sub>n P) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> (q \<turnstile>\<^sub>n Q))"
  by (pred_auto)

subsection \<open> Kleisli Lifting and Sequential Composition \<close>
utp_lit_vars
text \<open> The Kleisli lifting operator maps a probabilistic design (@{text "p \<turnstile>\<^sub>n R"}) into a ``lifted'' 
design that maps from
@{text "prob"} to @{text "prob"}. Therefore, one probabilistic design can be composed sequentially with 
another lifted design. The precondition of the definition specifies that all states of the initial 
distribution satisfy the predicate @{text "p"}. The postcondition specifies that there exists a 
function @{text "Q"}, that maps states to distributions, such that 
\begin{itemize}
  \item for any state $s$, if its probability in the initial distribution is larger than 0, then 
R(s, Q(s)) must be held;
  \item any state $ss$ in final distribution @{text "$prob\<acute>"} is equal to summation of all paths 
from any state $t$ in its initial distribution to $ss$ via @{text "Q t"}.
\end{itemize}

\begin{figure*}\centering
    \includegraphics[width=.45\textwidth]{images/klift.pdf}
    \caption{\label{fig:klift}Illustration of Kleisli lifting}
\end{figure*}

Figure~\ref{fig:klift} illustrates the lifting operation, provided that there are four states in 
the state space. The blue states in @{text "$prob"} denotes their initial probabilities are larger 
than 0, and the red states in @{text "$prob\<acute>"} denotes their final probabilities are larger than 0.
Q is defined as 
  \[\{(s_1, Q(s_1)), (s_2, Q(s_2)), (s_4, Q(s_4))\}\]
and the relation between 
$s_i$ and $Q(s_i)$ is established by R. In addition, the probability of $s_1$ in $Q(s_1)$ is larger
than 0, that of $s_1$ and $s_3$ in $Q(s_2)$, and that of $s_3$ and $s_4$ in $Q(s_4)$. Finally, the
finally distribution is given below.
\begin{align*}
    & prob'(s_1) = prob(s_1) * Q(s_1)(s_1) + prob(s_2) * Q(s_2)(s_1) & \\
    & prob'(s_3) = prob(s_2) * Q(s_2)(s_3) + prob(s_4) * Q(s_4)(s_3) & \\
    & prob'(s_4) = prob(s_2) * Q(s_2)(s_4) + prob(s_4) * Q(s_4)(s_4) & 
\end{align*} 
\<close>
(*
\<up>(p\<turnstile>R) = ((prob(p) = 1) \<turnstile> 
  (\<exists>Q\<in>('s\<Rightarrow>'s pmf) . 
  (\<forall>s. prob(s) > 0 \<Rightarrow> R(s, Q s))  (* "prob(s) > 0" has different types as "R(s, Q s)", so \<Rightarrow> doesn't work *)
  \<and>
  (prob' =\<lambda>s. (\<Sum>t. prob(t)* (Q(t) s))))))
*)
definition kleisli_lift2:: "'a upred \<Rightarrow> ('a, 'a prss) urel \<Rightarrow> ('a prss, 'a prss) rel_des" 
  where "kleisli_lift2 p R = 
  ( \<^U>((\<Sum>\<^sub>a i\<in>\<lbrakk>p\<rbrakk>\<^sub>p. $prob i) = 1)
    \<turnstile>\<^sub>r
  (\<^bold>\<exists> Q \<bullet> (
      (\<^bold>\<forall>ss \<bullet> U(($prob\<acute> ss) = (\<Sum>\<^sub>a t. (($prob t) * (pmf (Q t) ss))))) \<and> 
      (\<^bold>\<forall>s \<bullet> (\<not>(U($prob $\<^bold>v\<acute> > 0 \<and> $\<^bold>v\<acute> = s) ;; 
            ((((\<not>R) ;; (\<^bold>\<forall>t \<bullet> U(($prob t) = (pmf (Q s) t)))))))
    ))
  )))"

named_theorems kleisli_lift

text \<open> Alternatively, we can define the lifting operator as a normal design, instead of a design in 
previous definition. \<close>
definition kleisli_lift2':: "'a upred \<Rightarrow> ('a, 'a prss) urel \<Rightarrow> ('a prss, 'a prss) rel_des" where 
[kleisli_lift]: "kleisli_lift2' p R = 
  ( \<^U>((\<Sum>\<^sub>a i\<in>\<lbrakk>p\<rbrakk>\<^sub>p. &prob i) = 1)
    \<turnstile>\<^sub>n
  (\<^bold>\<exists> Q \<bullet> (
      (\<^bold>\<forall>ss \<bullet> U(($prob\<acute> ss) = (\<Sum>\<^sub>a t. (($prob t) * (pmf (Q t) ss))))) \<and> 
      (\<^bold>\<forall>s \<bullet> (\<not>(U($prob $\<^bold>v\<acute> > 0 \<and> $\<^bold>v\<acute> = s) ;; 
            ((\<not>R) ;; (\<^bold>\<forall>t \<bullet> U(($prob t) = (pmf (Q s) t)))))
    ))
  )))"

(*
print_theorems
find_theorems "kleisli_lift2'"
*)

text \<open> Two definitions actually are equal. \<close>
lemma kleisli_lift2_eq: "kleisli_lift2' p R = kleisli_lift2 p R"
  apply (simp add: kleisli_lift2_def)
  apply (simp add: utp_prob_des.kleisli_lift2'_def)
  by (rel_auto)

utp_expr_vars

text \<open> Then the lifting operator @{text "\<up>"} is defined upon @{text "kleisli_lift2"}. 
\<close>
definition kleisli_lift ("\<up>") where
  "kleisli_lift P = kleisli_lift2 (\<lfloor>pre\<^sub>D(P)\<rfloor>\<^sub><) (pre\<^sub>D(P) \<and> post\<^sub>D(P))"

(* thm "kleisli_lift_def" *)

text \<open> The alternative definition of the lifting operator @{text "\<up>"} is based on 
@{text "kleisli_lift2'"}.
\<close>
lemma kleisli_lift_alt_def: 
  "kleisli_lift P = kleisli_lift2' (\<lfloor>pre\<^sub>D(P)\<rfloor>\<^sub><) (pre\<^sub>D(P) \<and> post\<^sub>D(P))"
  by (simp add: kleisli_lift_def kleisli_lift2_eq)

text \<open>
Sequential composition of two probabilistic designs (P and Q) is composition of P with the lifted Q 
through the Kleisli lifting operator.
\<close>
abbreviation pseqr :: "('b, 'b) rel_pdes \<Rightarrow> ('b, 'b) rel_pdes \<Rightarrow> ('b, 'b) rel_pdes" (infix ";;\<^sub>p" 60) where
  "pseqr P Q \<equiv> (P ;; (\<up> Q))"

text \<open>
@{text "II\<^sub>p"} is the identity of sequence of probabilistic designs.
\<close>
abbreviation skip_p ("II\<^sub>p") where
  "skip_p \<equiv> \<K>(II\<^sub>D)"

text \<open>
The top of probabilistic designs is still the top of designs.
\<close>
abbreviation falsep :: "('b, 'b) rel_pdes" ("false\<^sub>p") where
"falsep \<equiv> false"

end