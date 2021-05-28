section \<open> Probabilistic Designs Laws \<close>

theory utp_prob_des_laws
  imports "UTP-Calculi.utp_wprespec" 
          "UTP-Designs.utp_designs" 
          "HOL-Probability.Probability_Mass_Function"
          (* "HOL-Probability.PMF_Impl" *)
          utp_prob_des
          (* utp_prob_des_healthy *)
          utp_prob_pmf_laws
begin recall_syntax

(* declare [[show_types]]*)

subsection \<open> Probability Embedding \<close>

text \<open>
  Inverse of @{text "\<K>"}~\cite[Corollary 3.7]{Jifeng2004}: 
embedding a standard design (P) in the probabilistic world then forgetting its probability 
distribution is equal to P itself.
\<close>
lemma pemp_inv:
  assumes "P is \<^bold>N"
  shows "\<K>(P) ;; \<^bold>f\<^bold>p = P"
proof -
  have 1: "P \<sqsubseteq> \<K>(P) ;; \<^bold>f\<^bold>p"
    apply (simp add: pemb_def forget_prob_def)
    by (simp add: wprespec1)
  also have 2: "\<K>(P) ;; \<^bold>f\<^bold>p \<sqsubseteq> P"
  proof -
    obtain pre\<^sub>P post\<^sub>P
      where p:"P = (pre\<^sub>P \<turnstile>\<^sub>n post\<^sub>P)"   
      using assms by (metis ndesign_form)
    have "\<K>(P);;\<^bold>f\<^bold>p = \<K>(pre\<^sub>P \<turnstile>\<^sub>n post\<^sub>P);;\<^bold>f\<^bold>p"
      using p by auto
    also have "\<K>(pre\<^sub>P \<turnstile>\<^sub>n post\<^sub>P);;\<^bold>f\<^bold>p \<sqsubseteq> pre\<^sub>P \<turnstile>\<^sub>n post\<^sub>P"
    apply (simp add: pemb_def forget_prob_def wprespec_def)
    apply (rel_simp)
    proof -
      fix ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and morea::"'b"
      assume a1: "ok\<^sub>v \<and> \<lbrakk>pre\<^sub>P\<rbrakk>\<^sub>e more \<longrightarrow> ok\<^sub>v' \<and> \<lbrakk>post\<^sub>P\<rbrakk>\<^sub>e (more, morea)"
      show "\<exists>(ok\<^sub>v''::bool) prob\<^sub>v::'b pmf.
          (\<lbrakk>pre\<^sub>P\<rbrakk>\<^sub>e more \<longrightarrow>
           ok\<^sub>v \<longrightarrow>
           (\<forall>(ok\<^sub>v::bool) morea::'b.
               ok\<^sub>v \<and> \<lbrakk>post\<^sub>P\<rbrakk>\<^sub>e (more, morea) \<or> ok\<^sub>v'' \<and> (ok\<^sub>v \<longrightarrow> \<not> (0::real) < pmf prob\<^sub>v morea))) \<and>
          (ok\<^sub>v'' \<longrightarrow> ok\<^sub>v' \<and> (0::real) < pmf prob\<^sub>v morea)"
        apply (rule_tac x="ok\<^sub>v'" in exI)
        apply (rule_tac x="pmf_of_list [(morea, 1.0)]" in exI)
        apply (auto)          
        using a1 apply blast
        using a1 apply blast
        apply (rename_tac ok\<^sub>v'' moreaa)
        proof -
          fix ok\<^sub>v''::"bool" and moreaa::"'b"
          assume a21: "\<lbrakk>pre\<^sub>P\<rbrakk>\<^sub>e more"
          assume a22: "ok\<^sub>v"
          assume a23: "ok\<^sub>v''"
          assume a2: "(0::real) < pmf (pmf_of_list [(morea, (1::real))]) moreaa"
          have f1: "moreaa = morea"
            proof (rule ccontr)
              assume a3: "\<not> moreaa = morea"
              have f2: "pmf_of_list_wf [(morea, (1::real))]"
                by (simp add: pmf_of_list_wf_def)
              have f3: "pmf (pmf_of_list [(morea, (1::real))]) moreaa = 
                    sum_list (map snd (filter (\<lambda>z. fst z = moreaa) [(morea, (1::real))]))"
                by (simp add: f2 pmf_pmf_of_list)
              then have "... = 0"
                using a3 by auto
              then show "False"
                using a2 f3 by linarith
            qed
          show "\<lbrakk>post\<^sub>P\<rbrakk>\<^sub>e (more, moreaa)"
            using a1 a21 a22 a23 a2 f1 by blast
        next
          show "(0::real) < pmf (pmf_of_list [(morea, 1::real)]) morea"
            by (simp add: pmf_of_list_wf_def pmf_pmf_of_list)
        qed
    qed
    then show ?thesis
      by (simp add: p)
  qed
  show ?thesis
    using 1 2 by simp 
qed

lemma pemp_bot: " \<K>(\<bottom>\<^sub>D) = \<bottom>\<^sub>D"
  apply (simp add: upred_defs)
  by (rel_auto)

lemma pemp_bot': "\<K>(\<bottom>\<^sub>D) = true"
  apply (simp add: upred_defs)
  by (rel_auto)

lemma pemp_assigns: "\<K>(\<langle>\<sigma>\<rangle>\<^sub>D) = \<^U>(true \<turnstile>\<^sub>n ($prob\<acute>((\<sigma> \<dagger> &\<^bold>v)\<^sup><) = 1))"
  by (simp add: assigns_d_ndes_def prob_lift wp usubst, rel_auto)

lemma pemp_skip: "\<K>(II\<^sub>D) = \<^U>(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v) = 1))"
  by (simp only: assigns_d_id[THEN sym] pemp_assigns usubst, rel_auto)

lemma pemp_assign:
  fixes e :: "(_, _) uexpr" 
  shows "\<K>(x :=\<^sub>D e) = \<^U>(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>e\<^sup></$x\<rbrakk>) = 1))"
  by (simp add: pemp_assigns wp usubst, rel_auto)

lemma pemp_cond:
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "\<K>(P \<triangleleft> b \<triangleright>\<^sub>D Q) = \<K>(P) \<triangleleft> b \<triangleright>\<^sub>D \<K>(Q)"
  apply (ndes_simp cls: assms)
  by (rel_auto)

subsubsection \<open> Demonic choice \<close>
lemma pemb_intchoice:
  shows "\<K>((p \<turnstile>\<^sub>n P) \<sqinter> (q \<turnstile>\<^sub>n Q)) 
    = \<K>(p \<turnstile>\<^sub>n P) \<sqinter> \<K>(q \<turnstile>\<^sub>n Q) \<sqinter> (\<Sqinter> r \<in> {0<..<1} \<bullet> (\<K>(p \<turnstile>\<^sub>n P) \<oplus>\<^bsub>r\<^esub> \<K>(q \<turnstile>\<^sub>n Q)))"
    (is "?LHS = ?RHS")
  apply (simp add: prob_choice_inf_simp)
  apply (rule_tac eq_split)
  defer
  apply (simp add: prob_lift ndesign_choice)
  apply (simp add: upred_defs)
  apply (rel_auto)
  apply (simp add: pmf_utp_disj_eq_1)
proof -
  fix ok\<^sub>v :: bool and more :: 'a and ok\<^sub>v' :: bool and prob\<^sub>v :: "'a pmf"
  assume "(\<Sum>\<^sub>ax | \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = 1"
  then have "infsetsum (pmf prob\<^sub>v) {a. \<exists>aa. \<lbrakk>Q\<rbrakk>\<^sub>e (more, a) \<and> aa = a \<or> \<lbrakk>P\<rbrakk>\<^sub>e (more, a) \<and> aa = a} = 1"
    by (simp add: pmf_utp_disj_eq_1)
  then show "(\<Sum>\<^sub>aa | \<exists>aa. \<lbrakk>P\<rbrakk>\<^sub>e (more, a) \<and> aa = a \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, a) \<and> aa = a. pmf prob\<^sub>v a) = 1"
    by (simp add: pmf_utp_disj_comm)
next
  fix ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and r::"real" and ok\<^sub>v''::"bool" and ok\<^sub>v'''::"bool" 
      and prob\<^sub>v'::"'a pmf" and ok\<^sub>v''''::"bool" and prob\<^sub>v''::"'a pmf" and ok\<^sub>v'''''::"bool"
  assume a1: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v' x) = (1::real)"
  assume a2: "(\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v'' x) = (1::real)"
  assume a3: "(0::real) < r"
  assume a4: "r < (1::real)"
  show " (\<Sum>\<^sub>ax::'a | \<exists>v::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> v = x \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x) \<and> v = x. pmf (prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v'') x) =
       (1::real)"
    using a3 a4 apply (simp add: pmf_wplus)
  proof -
    have f1: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v' x) = (1::real)"
      using a1 by (metis measure_pmf.prob_le_1 measure_pmf_conv_infsetsum order_class.order.antisym pmf_disj_leq)
    have "(\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v'' x) = (1::real)"
      using a2 by (metis measure_pmf.prob_le_1 measure_pmf_conv_infsetsum order_class.order.antisym pmf_disj_leq)
    then have f2: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v'' x) = (1::real)"
      by (metis (no_types, lifting) Collect_cong)
    have "(\<Sum>\<^sub>ax::'a | \<exists>v::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> v = x \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x) \<and> v = x. 
          pmf prob\<^sub>v' x \<cdot> r + pmf prob\<^sub>v'' x \<cdot> ((1::real) - r))
        = (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v' x \<cdot> r + pmf prob\<^sub>v'' x \<cdot> ((1::real) - r))"
      by metis
    also have "... = (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v' x \<cdot> r)
        + (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v'' x \<cdot> ((1::real) - r))"
      by (simp add: abs_summable_on_cmult_left infsetsum_add pmf_abs_summable)
    also have "... = (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v' x) \<cdot> r
        + (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v'' x) \<cdot> ((1::real) - r)"
      by (simp add: infsetsum_cmult_left pmf_abs_summable)
    also have f3: "... = (1::real)"
      using f1 f2 a3 a4 by simp
    show "(\<Sum>\<^sub>ax::'a | \<exists>v::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> v = x \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x) \<and> v = x. 
          pmf prob\<^sub>v' x \<cdot> r + pmf prob\<^sub>v'' x \<cdot> ((1::real) - r)) = (1::real)"
      using f3 by (simp add: calculation)
  qed
next 
  let ?LHS = " \<^U>((p \<and> q) \<turnstile>\<^sub>n ( (\<exists> a \<in> {0<..<1} . \<exists> b \<in> {0<..<1} . 
        (\<Sum>\<^sub>a i\<in>{s'.((P \<or> Q) wp (&\<^bold>v = s'))\<^sup><}. $prob\<acute> i) = 1 \<and> 
        (\<Sum>\<^sub>a i\<in>{s'.((P \<and> \<not>Q) wp (&\<^bold>v = s'))\<^sup><}. $prob\<acute> i) = a \<and>
        (\<Sum>\<^sub>a i\<in>{s'.((\<not>P \<and> Q) wp (&\<^bold>v = s'))\<^sup><}. $prob\<acute> i) = b)))"
  let ?RHS = " \<^U>((p \<and> q) \<turnstile>\<^sub>n ( (\<exists> r \<in> {0<..<1} . \<exists> prob\<^sub>0 . \<exists> prob\<^sub>1 .
        ((\<Sum>\<^sub>a i\<in>{s'.((P) wp (&\<^bold>v = s'))\<^sup><}. (pmf prob\<^sub>0 i)) = (1::real)) \<and>
        ((\<Sum>\<^sub>a i\<in>{s'.((Q) wp (&\<^bold>v = s'))\<^sup><}. (pmf prob\<^sub>1 i)) = (1::real)) \<and>  
          $prob\<acute> = prob\<^sub>0 +\<^bsub>r\<^esub> prob\<^sub>1
        )))"
  let ?B = " \<^U>((p \<and> q) \<turnstile>\<^sub>n 
    (((\<Sum>\<^sub>a i\<in>{s'.((P) wp (&\<^bold>v = s'))\<^sup><}. $prob\<acute> i) = 1)
    \<or> (\<Sum>\<^sub>a i\<in>{s'.((Q) wp (&\<^bold>v = s'))\<^sup><}. $prob\<acute> i) = 1))"
  have f1: "\<K> ((p \<turnstile>\<^sub>n P) \<sqinter> (q \<turnstile>\<^sub>n Q)) = (?B \<sqinter> ?LHS)"
    apply (simp add: prob_lift ndesign_choice)
    apply (rel_auto)
    apply (simp add: pmf_utp_disj_imp)+
    apply (simp add: pmf_utp_disj_imp')+
    apply (simp add: pmf_utp_disj_eq_1)
    by (simp add: pmf_utp_disj_eq_1')

  have f2: "?RHS \<sqsubseteq> ?LHS"
    apply (rel_simp)
    proof -
      fix ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and prob\<^sub>v::"'a pmf"
      let ?a = "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<not> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x)"
      let ?b = "(\<Sum>\<^sub>ax::'a | \<not> \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x)"
      let ?b1 = "(infsetsum (pmf prob\<^sub>v) ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)}))"
      let ?a1 = "infsetsum (pmf prob\<^sub>v) ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})"
      let ?prob\<^sub>0 = "Abs_pmf (\<F> {s. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} {s. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} prob\<^sub>v)"
      let ?prob\<^sub>1 = "Abs_pmf (\<F> {s. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} {s. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} prob\<^sub>v)"
      assume a1: "(\<Sum>\<^sub>ax::'a | \<exists>v::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> v = x \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x) \<and> v = x. pmf prob\<^sub>v x) = (1::real)"
      assume a2: "(0::real) < ?a"
      assume a3: "?a < (1::real)"
      assume a4: "(0::real) < ?b"
      assume a5: "?b < (1::real)"

      from a1 have a1': "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real)"
        by (smt Collect_cong)
      from a1' have a1'': 
        "infsetsum (pmf prob\<^sub>v) ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} \<union> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)}) = (1::real)"
        by (simp add: Collect_disj_eq)
      have b_eq: "?b1 = ?b"
        by (smt Collect_cong mem_Collect_eq set_diff_eq)
      have a_eq: "?a1 = ?a"
        by (smt Collect_cong mem_Collect_eq set_diff_eq)
      from a2 have a2':
        "(0::real) < infsetsum (pmf prob\<^sub>v) ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})"
        by (smt Collect_cong mem_Collect_eq set_diff_eq)
      from a4 have a4':
        "(0::real) < infsetsum (pmf prob\<^sub>v) ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)})"
        by (smt Collect_cong mem_Collect_eq set_diff_eq)
      have f21: "?a/(?a+?b) \<in> {0::real<..<1::real}"
        using a2 a3 a4 a5 by auto
      have f211: "?b/(?a+?b) \<in> {0::real<..<1::real}"
        using a2 a3 a4 a5 by auto
      have f21': "1 - (?a/(?a+?b)) = ((?a+?b)/(?a+?b)) - (?a/(?a+?b))"
        using a2 a4 by auto
      then have f21'': "... = ?b/(?a+?b)"
        by (smt add_divide_distrib)
      have f222: "((?b1 + ?a1) / ?a1)*(?a/(?a+?b)) = ((?b + ?a)/?a)*(?a/(?a+?b))"
        using a_eq b_eq by simp
      then have f222': "... = 1"
        by (smt f21' f211 greaterThanLessThan_iff nonzero_mult_divide_mult_cancel_right2 times_divide_times_eq)
      have f223: "((?b1 + ?a1) / ?b1)*(?b/(?a+?b)) = ((?b + ?a)/?b)*(?b/(?a+?b))"
        using a_eq b_eq by simp
      then have f223': "... = 1"
        by (smt a4 f21' nonzero_mult_divide_mult_cancel_right2 times_divide_times_eq)
      
      have f22: "(\<Sum>\<^sub>a x::'a | x \<in> {x::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, x)} .
        (pmf (Abs_pmf (\<F> {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} prob\<^sub>v))) x) = (1::real)"
        apply (rule proj_f_sum_eq_1[of prob\<^sub>v "{s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)}" "{s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)}"])
        using a1'' apply blast
        using a2' apply blast
        using a4' by blast
      
      then have f23: "infsetsum (pmf (Abs_pmf (\<F> {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} prob\<^sub>v)))
            {x::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, x)} = (1::real)"
        by simp
      have f24: "\<forall>i::'a. pmf prob\<^sub>v i = pmf (?prob\<^sub>0 +\<^bsub>?a/(?a+?b)\<^esub> ?prob\<^sub>1) i"
        apply (auto)
        proof -
          fix i::'a
          have P_notQ: "{s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} = {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s) \<and> \<not> \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)}"
            by blast
          have Q_notP: "{s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} = {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s) \<and> \<not> \<lbrakk>P\<rbrakk>\<^sub>e (more, s)}"
            by blast
          have P_and_Q: "{s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} = {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)}"
            by blast
          have f240: "emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) * (?a/(?a+?b)) + 
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) * (?b/(?a+?b))
            = emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)}))* 
            ((?a/(?a+?b)) + (?b/(?a+?b)))"
            by (smt distrib_left ennreal_plus f21 f211 greaterThanLessThan_iff)
          then have f240': "... = emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)}))"
            by (smt ennreal_1 f21' f21'' mult.right_neutral)
          let ?P_Q = "emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)}))"
          let ?Q_P = "emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)}))"
          let ?PQ = "emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)}))"
          have f241: "pmf (Abs_pmf (\<F> {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} prob\<^sub>v)) i \<cdot> ?a/(?a+?b) +
            pmf (Abs_pmf (\<F> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} prob\<^sub>v)) i \<cdot>
            ((1::real) - ?a/(?a+?b))
            = measure (measure_pmf (Abs_pmf (\<F> {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} prob\<^sub>v))) {i} 
              \<cdot> ?a/(?a+?b) +
            measure (measure_pmf (Abs_pmf (\<F> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} prob\<^sub>v))) {i} \<cdot>
            ((1::real) - ?a/(?a+?b))"
            by (simp add: pmf.rep_eq)
          also have f242: "... = measure ((\<F> {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} prob\<^sub>v)) {i} 
              \<cdot> ?a/(?a+?b) +
            measure ((\<F> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} prob\<^sub>v)) {i} \<cdot>
            ((1::real) - ?a/(?a+?b))"
            by (simp add: Un_commute a1'' a2' a4' proj_f_measure_pmf)
          also have f243: "... = enn2real
             (emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) \<cdot>
              ennreal ((?b1 + ?a1) / ?a1) +
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)}))) \<cdot>
            (?a/(?a+?b)) +
            enn2real
             (emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)})) \<cdot>
              ennreal ((?a1 + ?b1) / ?b1) +
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)}))) \<cdot>
            ((1::real) - (?a/(?a+?b)))"
            apply (simp only: measure_def)
            by (simp add: proj_f_emeasure)
          also have f244: "... = enn2real
             (emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) \<cdot>
              ennreal ((?b1 + ?a1) / ?a1) +
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)}))) \<cdot>
            (?a/(?a+?b)) +
            enn2real
             (emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)})) \<cdot>
              ennreal ((?a1 + ?b1) / ?b1) +
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)}))) \<cdot>
            ((?b/(?a+?b)))"
            using f21' f21'' by simp
          also have f245: "... = enn2real
             (emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) \<cdot>
              ennreal ((?b1 + ?a1) / ?a1) *(?a/(?a+?b)) +
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) \<cdot>
            (?a/(?a+?b))) +
            enn2real
             (emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)})) \<cdot>
              ennreal ((?a1 + ?b1) / ?b1) +
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)}))) \<cdot>
            ((?b/(?a+?b)))"
            by (smt distrib_right' enn2real_ennreal enn2real_mult f21 greaterThanLessThan_iff)
          also have f246: "... = enn2real
             (emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) \<cdot>
              ennreal ((?b1 + ?a1) / ?a1) *(?a/(?a+?b)) +
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) \<cdot>
            (?a/(?a+?b))) +
            enn2real
             (emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)})) \<cdot>
              ennreal ((?a1 + ?b1) / ?b1) *(?b/(?a+?b)) +
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)})) \<cdot>
            (?b/(?a+?b)))"
            by (smt distrib_right' enn2real_ennreal enn2real_mult f211 greaterThanLessThan_iff)
          also have f247: "... = enn2real
             (emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) \<cdot> 1 +
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) \<cdot>
            (?a/(?a+?b))) +
            enn2real
             (emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)})) \<cdot> 1 +
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)})) \<cdot>
            (?b/(?a+?b)))"
            using f222 f222' f223 f223' by (smt ennreal_1 ennreal_mult'' f21 f211 greaterThanLessThan_iff mult.assoc)
           also have f248: "... = enn2real
             (emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) +
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) \<cdot>
            (?a/(?a+?b)) +
             emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)})) +
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)})) \<cdot>
            (?b/(?a+?b)))"
             by (smt enn2real_plus ennreal_add_eq_top ennreal_mult_eq_top_iff ennreal_neq_top 
                 measure_pmf.emeasure_subprob_space_less_top mult.right_neutral order_top_class.less_top)
          also have f249: "... = enn2real
             (emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) +
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) \<cdot>
            (?a/(?a+?b)) +
             emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)})) +
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) \<cdot>
            (?b/(?a+?b)))"
            by (simp add: Int_commute)
          also have f2410:"... = enn2real
             (emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) +
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)})) +
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) * (?a/(?a+?b)) + 
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) * (?b/(?a+?b)))
             "
            by (simp add: add.assoc add.left_commute)
          also have f2411: "... = enn2real
             (emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) +
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} - {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)})) +
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} \<inter> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)}))
             )"
            using f240 f240' by (simp add: add.assoc)
          also have f2412: "... = enn2real
             (emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s) \<and> \<not> \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) +
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s) \<and> \<not> \<lbrakk>P\<rbrakk>\<^sub>e (more, s)})) +
              emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)}))
             )"
            by (simp add: P_notQ P_and_Q Q_notP)
          have f2413: "emeasure (measure_pmf prob\<^sub>v) {i} = enn2real
               (emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s) \<and> \<not> \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)})) +
                emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s) \<and> \<not> \<lbrakk>P\<rbrakk>\<^sub>e (more, s)})) +
                emeasure (measure_pmf prob\<^sub>v) ({i} \<inter> ({s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)}))
               )"
            proof (cases "i \<in> {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s) \<and> \<not> \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)}")
              case True
              then show ?thesis 
                by (simp add: ennreal_enn2real_if)
            next
              case False
              then have Ff: "i \<notin> {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s) \<and> \<not> \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)}"
                by auto
              then show ?thesis 
                proof (cases "i \<in> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s) \<and> \<not>\<lbrakk>P\<rbrakk>\<^sub>e (more, s)}")
                  case True
                  then show ?thesis by (simp add: ennreal_enn2real_if)
                next
                  case False
                  then have Fff: "i \<notin> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s) \<and> \<not>\<lbrakk>P\<rbrakk>\<^sub>e (more, s)}"
                    by auto
                  then show ?thesis 
                    proof (cases "i \<in> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s) \<and> \<lbrakk>P\<rbrakk>\<^sub>e (more, s)}")
                      case True
                      then show ?thesis
                        by (metis (no_types, lifting) Int_insert_left_if0 Int_insert_left_if1 
                              Sigma_Algebra.measure_def add.left_neutral 
                              bounded_lattice_bot_class.inf_bot_left emeasure_empty 
                              measure_pmf.emeasure_eq_measure mem_Collect_eq)
                    next
                      case False
                      then have Ffff: "i \<in> {s::'a. \<not>(\<lbrakk>P\<rbrakk>\<^sub>e (more, s) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, s))}"
                        using Ff Fff by blast
                      from a1 have g1: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v x) = (1::real)"
                        using a1' by blast
                      then have g2: "(\<Sum>\<^sub>ax::'a | \<not>(\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x) = (0::real)"
                        by (rule pmf_utp_comp0'[of prob\<^sub>v "\<lambda>x. (\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x))"])
                      have g4: "(\<Sum>\<^sub>ax::'a | (\<lambda>x. x = i) x. pmf prob\<^sub>v x) \<le> 
                            (\<Sum>\<^sub>ax::'a | (\<lambda>x. x = i) x \<or> \<not>(\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x)"
                        by (rule pmf_disj_leq[of prob\<^sub>v "(\<lambda>x. x = i)" _])
                      then have g5: "(\<Sum>\<^sub>ax::'a | (\<lambda>x. x = i) x. pmf prob\<^sub>v x) \<le> 
                            (\<Sum>\<^sub>ax::'a | \<not>(\<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<or> \<lbrakk>Q\<rbrakk>\<^sub>e (more, x)). pmf prob\<^sub>v x)"
                        using Ffff by (smt Collect_cong mem_Collect_eq)
                      then have g6: "(\<Sum>\<^sub>ax::'a | (\<lambda>x. x = i) x. pmf prob\<^sub>v x) = 0"
                        using g2 by simp
                      have "(\<Sum>\<^sub>ax::'a | x = i. pmf prob\<^sub>v x) = pmf prob\<^sub>v i" 
                        by auto
                      then have g7: "(pmf prob\<^sub>v) i = 0"
                        using g6 by linarith
                      then show ?thesis using g7
                        by (simp add: emeasure_pmf_single pmf_measure_zero)
                    qed
                qed
            qed
          have f241: "pmf prob\<^sub>v i =
              pmf (Abs_pmf (\<F> {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} prob\<^sub>v)) i \<cdot> ?a/(?a+?b) +
              pmf (Abs_pmf (\<F> {s::'a. \<lbrakk>Q\<rbrakk>\<^sub>e (more, s)} {s::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, s)} prob\<^sub>v)) i \<cdot> ((1::real) - ?a/(?a+?b))"
            by (metis (no_types, lifting) P_and_Q P_notQ Q_notP Sigma_Algebra.measure_def calculation 
               ennreal_add_eq_top ennreal_enn2real f2413 measure_pmf.emeasure_subprob_space_less_top 
               order_top_class.less_top pmf.rep_eq)
          show "pmf prob\<^sub>v i = pmf (?prob\<^sub>0 +\<^bsub>?a/(?a+?b)\<^esub> ?prob\<^sub>1) i"
            using f21 apply (simp add: f21 pmf_wplus)
            using f241 by blast
        qed
      have f25: "prob\<^sub>v = (?prob\<^sub>0 +\<^bsub>?a/(?a+?b)\<^esub> ?prob\<^sub>1)"
        apply (rule pmf_eqI)
        using f24 by blast
      show "\<exists>x::real\<in>{0::real<..<1::real}.
            \<exists>xa::'a pmf.
               (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf xa x) = (1::real) \<and>
               (\<exists>xb::'a pmf. (\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (more, x). pmf xb x) = (1::real) \<and> prob\<^sub>v = xa +\<^bsub>x\<^esub> xb)"
        apply (simp add: Set.Bex_def)
        apply (rule_tac x = "?a/(?a+?b)" in exI)
        apply (rule conjI)
        using f21 apply simp
        apply (rule conjI)
        using f21 apply simp
        apply (rule_tac x = "?prob\<^sub>0" in exI)
        apply (rule_tac conjI)
        using f23 apply blast
        apply (rule_tac x = "?prob\<^sub>1" in exI)
        apply (rule_tac conjI)
        apply (metis Collect_mem_eq Un_commute a1'' a2' a4' proj_f_sum_eq_1)
        using f25 by blast
    qed
  then have f3: "(?B \<sqinter> ?RHS) \<sqsubseteq> (?B \<sqinter> ?LHS)"
    by (smt sup_bool_def sup_uexpr.rep_eq upred_ref_iff)

  have f4: "(?B \<sqinter> ?RHS) 
    = \<K> (p \<turnstile>\<^sub>n P) \<sqinter> \<K> (q \<turnstile>\<^sub>n Q) \<sqinter> (\<Sqinter> r::real \<in> {0::real<..<1::real} \<bullet> \<K> (p \<turnstile>\<^sub>n P) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> \<K> (q \<turnstile>\<^sub>n Q))"
    apply (simp add: prob_lift ndesign_choice)
    apply (simp add: upred_defs)
    apply (rel_auto)
    apply blast
    using greaterThanLessThan_iff by blast

  show "`\<K> ((p \<turnstile>\<^sub>n P) \<sqinter> (q \<turnstile>\<^sub>n Q)) \<Rightarrow>
     \<K> (p \<turnstile>\<^sub>n P) \<sqinter> \<K> (q \<turnstile>\<^sub>n Q) \<sqinter> (\<Sqinter> r::real \<in> {0::real<..<1::real} \<bullet> \<K> (p \<turnstile>\<^sub>n P) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> \<K> (q \<turnstile>\<^sub>n Q))`"
    using f1 f3 f4 refBy_order by (metis (mono_tags, lifting) )
qed

lemma pemb_intchoice':
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "\<K>(P \<sqinter> Q) 
    = \<K>(P) \<sqinter> \<K>(Q) \<sqinter> (\<Sqinter> r \<in> {0<..<1} \<bullet> (\<K>(P) \<oplus>\<^bsub>r\<^esub> \<K>(Q)))"
    (is "?LHS = ?RHS")
proof -
  obtain pre\<^sub>p post\<^sub>p pre\<^sub>q post\<^sub>q
    where p:"P = (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p)" and 
          q:"Q = (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)"
    using assms by (metis ndesign_form)
  have "\<K>((pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) \<sqinter> (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)) 
    = \<K>(pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) \<sqinter> \<K>(pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q) \<sqinter> (\<Sqinter> r \<in> {0<..<1} \<bullet> (\<K>(pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) \<oplus>\<^bsub>r\<^esub> \<K>(pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)))"
    by (simp add: pemb_intchoice)
  then show ?thesis
    using p q by auto
qed

lemma pemb_dem_choice_refinedby_prochoice:
  assumes "r \<in> {0..1}" "P is \<^bold>N" "Q is \<^bold>N"
  shows "\<K>(P \<sqinter> Q) \<sqsubseteq> (\<K>(P) \<oplus>\<^bsub>r\<^esub> \<K>(Q))"
proof (cases "r \<in> {0::real<..<1::real}")
  case True
  show ?thesis 
    using assms apply (simp add: pemb_intchoice')
    apply (simp add: UINF_as_Sup_collect)
    by (meson SUP_le_iff True semilattice_sup_class.sup_ge2)
next
  case False
  then show ?thesis
    by (metis assms(1) atLeastAtMost_iff greaterThanLessThan_iff less_le pemb_mono prob_choice_one 
        prob_choice_zero semilattice_sup_class.sup_ge1 semilattice_sup_class.sup_ge2)
qed

subsubsection \<open> Kleisli Lift and Sequential Composition \<close>
lemma kleisli_lift_skip_unit: "\<up> (\<K>(II\<^sub>D)) = kleisli_lift2 true (U($prob\<acute>($\<^bold>v) = 1))"
  by (simp add: kleisli_lift_def pemp_skip)

lemma kleisli_lift_skip: 
  "kleisli_lift2 true (U($prob\<acute>($\<^bold>v) = 1)) =  \<^U>(true \<turnstile>\<^sub>n ($prob\<acute> = $prob))"
  apply (simp add: kleisli_lift2_def ndesign_def)
  apply (rel_auto)
  apply (metis (full_types) equalityI lit.rep_eq mem_Collect_eq order_top_class.top_greatest subsetI 
      upred_ref_iff upred_set.rep_eq sum_pmf_eq_1)
  apply (metis (full_types) lit.rep_eq mem_Collect_eq order_top_class.top.extremum_unique subsetI 
      upred_ref_iff upred_set.rep_eq sum_pmf_eq_1)
  proof -
    fix ok\<^sub>v::"bool" and prob\<^sub>v::"'a pmf" and ok\<^sub>v'::"bool" and prob\<^sub>v'::"'a pmf" and x::"'a \<Rightarrow> 'a pmf"
    assume a1: " \<forall>xa::'a. pmf prob\<^sub>v' xa = (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v xb \<cdot> pmf (x xb) xa)"
    assume a2: "\<forall>xa::'a.
            (\<exists>prob\<^sub>v::'a pmf. \<not> pmf prob\<^sub>v xa = (1::real) \<and> (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb)) \<longrightarrow>
            \<not> (0::real) < pmf prob\<^sub>v xa"
    from a2 have f1: "\<forall>xa::'a. (pmf (x xa) xa = 1 ) \<or> \<not> (0::real) < pmf prob\<^sub>v xa"
      by blast
    then have f2: "\<forall>xa::'a. (pmf (x xa) xa = 1 ) \<or> (0::real) = pmf prob\<^sub>v xa"
      by auto
    have f3: "\<forall>xa. (pmf prob\<^sub>v xb \<cdot> pmf (x xb) xa) = (if xb = xa then pmf prob\<^sub>v xa else 0)"
      apply (rule allI)
      proof -
        fix xa::"'a"
        show "pmf prob\<^sub>v xb \<cdot> pmf (x xb) xa = (if xb = xa then pmf prob\<^sub>v xa else (0::real))"
        proof (cases "xb = xa")
          case True
          then show ?thesis
            using f2 by auto
        next
          case False
          then have f: "\<not>xb = xa"
            by simp
          then show ?thesis 
          proof (cases "pmf prob\<^sub>v xb = 0")
            case True
            then show ?thesis 
              by auto
          next
            case False
            then have "pmf (x xb) xb = 1"
              using f2 by auto
            then have "pmf (x xb) xa = 0"
              using f apply (simp add: pmf_def)
              by (simp add: measure_pmf_single pmf_not_the_one_is_zero)
            then show ?thesis 
              by (simp add: f)
          qed
        qed
      qed
    have f4: "\<forall>xa. (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v xb \<cdot> pmf (x xb) xa) = 
                     (\<Sum>\<^sub>axb::'a. (if xb = xa then pmf prob\<^sub>v xa else 0))"
      using f3
      by (smt f2 infsetsum_cong mult_cancel_left2 mult_not_zero pmf_not_the_one_is_zero)
    have f5: "\<forall>xa. (\<Sum>\<^sub>axb::'a. (if xb = xa then pmf prob\<^sub>v xa else 0)) =  pmf prob\<^sub>v xa"
      by (simp add: pmf_sum_single)
    have f6: "\<forall>xa. pmf prob\<^sub>v' xa = pmf prob\<^sub>v xa"
      using f4 f5 a1 by simp
    show "prob\<^sub>v' = prob\<^sub>v"
      using f6 by (simp add: pmf_eqI)
  next
    fix ok\<^sub>v::"bool" and prob\<^sub>v::"'a pmf" and ok\<^sub>v'::"bool"
    show "\<exists>x::'a \<Rightarrow> 'a pmf.
            (\<forall>xa::'a. pmf prob\<^sub>v xa = (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v xb \<cdot> pmf (x xb) xa)) \<and>
            (\<forall>xa::'a.
                (\<exists>prob\<^sub>v::'a pmf. \<not> pmf prob\<^sub>v xa = (1::real) \<and> (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb)) \<longrightarrow>
                \<not> (0::real) < pmf prob\<^sub>v xa)"
      apply (rule_tac x="\<lambda>s::'a. pmf_of_list([(s, 1.0)])" in exI)
      apply (rule conjI, auto)
      apply (simp add: pmf_sum_single')
      by (smt filter.simps(1) filter.simps(2) list.map(1) list.map(2) list.set(1) list.set(2) 
          pmf_of_list_wf_def pmf_pmf_of_list prod.sel(1) prod.sel(2) singletonD sum_list.Nil 
          sum_list_simps(2))
  qed

lemma kleisli_lift_skip':
  "\<up> (\<K>(II\<^sub>D))  =  \<^U>(true \<turnstile>\<^sub>n ($prob\<acute> = $prob))"
  by (simp add: kleisli_lift_skip kleisli_lift_skip_unit)

lemma kleisli_lift_skip_left_unit: 
  assumes "P is \<^bold>N" 
  shows "(\<K>(II\<^sub>D));; \<up> P = P"
  proof -
    obtain pre\<^sub>p post\<^sub>p where p:"P = (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p)" 
      using assms by (metis ndesign_form)
    have f1: "(\<K>(II\<^sub>D));; \<up> (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) = (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p)"
      apply (simp add: pemp_skip kleisli_lift_def kleisli_lift2_def upred_set_def)
      apply (rel_auto)
      apply (metis (full_types) Compl_iff infsetsum_all_0 mem_Collect_eq pmf_comp_set 
          pmf_not_the_one_is_zero upred_set.rep_eq)
      apply (metis Compl_iff infsetsum_all_0 mem_Collect_eq pmf_comp_set pmf_not_the_one_is_zero 
          upred_set.rep_eq)
      proof -
        fix ok\<^sub>v::"bool" and more::"'a" and prob\<^sub>v::"'a pmf" and ok\<^sub>v'::"bool" and ok\<^sub>v''::"bool" 
            and prob\<^sub>v'::"'a pmf" and x::"'a \<Rightarrow> 'a pmf"
        assume a1: "\<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>e more"
        assume a2: "pmf prob\<^sub>v' more = (1::real)"
        assume a3: "\<forall>xa::'a. pmf prob\<^sub>v xa = (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v' xb \<cdot> pmf (x xb) xa)"
        assume a4: "\<forall>xa::'a.
            (\<exists>prob\<^sub>v::'a pmf. (\<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>e xa \<longrightarrow> \<not> \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)) \<and> (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb)) \<longrightarrow>
            \<not> (0::real) < pmf prob\<^sub>v' xa"
        from a4 have f1: "
            (\<exists>prob\<^sub>v::'a pmf. \<not> \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>) \<and> (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x more) xb)) \<longrightarrow>
            \<not> (0::real) < pmf prob\<^sub>v' more"
          using a1 by blast
        then have f2: "\<not>(\<exists>prob\<^sub>v::'a pmf. \<not> \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>) \<and> (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x more) xb))"
          using a2 by simp
        then have f3: "(\<forall>prob\<^sub>v::'a pmf. \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>) \<or> \<not>(\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x more) xb))"
          by blast
        then have f4: "\<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>) \<or> \<not>(\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x more) xb)"
          by blast
        from a3 a2 have f5: "(\<forall>xa::'a. (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v' xb \<cdot> pmf (x xb) xa) = 
            (\<Sum>\<^sub>axb::'a. if xb = more then pmf (x more) xa else 0))"
          by (smt infsetsum_cong mult_cancel_left mult_cancel_right1 pmf_not_the_one_is_zero)
        have f6: "(\<forall>xa::'a. (\<Sum>\<^sub>axb::'a. if xb = more then pmf (x more) xa else 0) = pmf (x more) xa)"
          apply (rule allI)
        proof -
          fix xa::"'a"
          show "(\<Sum>\<^sub>axb::'a. if xb = more then pmf (x more) xa else (0::real)) = pmf (x more) xa"
            by (simp add: infsetsum_single'[of more "\<lambda>y. pmf (x y) xa" more])
        qed
        have f7: "(\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x more) xb)"
          using f6 f5 a3 by simp
        show "\<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)"
          using f7 f4 by blast
      next 
        fix ok\<^sub>v::"bool" and more::"'a" and prob\<^sub>v::"'a pmf" and ok\<^sub>v'::"bool"
        assume a1: "\<forall>(ok\<^sub>v''::bool) prob\<^sub>v'::'a pmf.
          ok\<^sub>v \<and> (ok\<^sub>v'' \<longrightarrow> \<not> pmf prob\<^sub>v' more = (1::real)) \<or>
          ok\<^sub>v'' \<and>
          infsetsum (pmf prob\<^sub>v') (Collect \<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>e) = (1::real) \<and>
          (ok\<^sub>v' \<longrightarrow>
           (\<forall>x::'a \<Rightarrow> 'a pmf.
               (\<exists>xa::'a. \<not> pmf prob\<^sub>v xa = (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v' xb \<cdot> pmf (x xb) xa)) \<or>
               (\<exists>xa::'a.
                   (\<exists>prob\<^sub>v::'a pmf. (\<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>e xa \<longrightarrow> \<not> \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)) \<and> (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb)) \<and>
                   (0::real) < pmf prob\<^sub>v' xa)))"
        let ?prob\<^sub>v' = "(pmf_of_list [(more,1.0)])"
        have f1: "\<not>pmf ?prob\<^sub>v' more = (1::real) \<or> infsetsum (pmf ?prob\<^sub>v') (Collect \<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>e) = (1::real)"
          using a1 by blast
        have f2: "pmf ?prob\<^sub>v' more = (1::real)"
          by (smt divide_self_if filter.simps(1) filter.simps(2) infsetsum_cong list.map(1) 
              list.map(2) list.set(1) list.set(2) pmf_of_list_wf_def pmf_pmf_of_list prod.sel(1) 
              prod.sel(2) singletonD sum_list_simps(1) sum_list_simps(2))
        have f3: "infsetsum (pmf ?prob\<^sub>v') (Collect \<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>e) = (1::real)"
          using f1 f2 by blast
        then have f4: "infsetsum (\<lambda>x. if x = more then 1 else 0) (Collect \<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>e) = (1::real)"
          by (smt div_self filter.simps(1) filter.simps(2) infsetsum_cong list.map(1) list.map(2) 
              list.set(1) list.set(2) pmf_of_list_wf_def pmf_pmf_of_list prod.sel(1) prod.sel(2) 
              singletonD sum_list_simps(1) sum_list_simps(2))
        then have f8: "more \<in> (Collect \<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>e)"
          by (smt infsetsum_all_0)
        show "\<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>e more"
          using f8 by blast
      next
        fix ok\<^sub>v::"bool" and more::"'a" and prob\<^sub>v::"'a pmf" and ok\<^sub>v'::"bool"
        assume a1: "\<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)"
        let ?prob\<^sub>v = "(pmf_of_list [(more,1.0)])"
        have f0: "\<forall>xa::'a. pmf prob\<^sub>v xa = (\<Sum>\<^sub>axb::'a. pmf ?prob\<^sub>v xb \<cdot> pmf prob\<^sub>v xa)"
          apply (auto)
          proof -
            fix xa::"'a"
            have f1: "(\<Sum>\<^sub>axb::'a. pmf (pmf_of_list [(more, 1::real)]) xb \<cdot> pmf prob\<^sub>v xa) = 
                  (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v xa \<cdot> pmf (pmf_of_list [(more, 1::real)]) xb)"
              by (meson mult.commute)
            have f2: "(\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v xa \<cdot> pmf (pmf_of_list [(more, 1::real)]) xb) = pmf prob\<^sub>v xa"
              by (simp add: pmf_sum_single'')
            show "pmf prob\<^sub>v xa = (\<Sum>\<^sub>axb::'a. pmf (pmf_of_list [(more, 1::real)]) xb \<cdot> pmf prob\<^sub>v xa)"  
              apply (rule sym)
              using pmf_sum_single' f1 by (simp add: f2)
          qed
        show "\<exists>(ok\<^sub>v'::bool) prob\<^sub>v'::'a pmf.
          (ok\<^sub>v \<longrightarrow> ok\<^sub>v' \<and> pmf prob\<^sub>v' more = (1::real)) \<and>
          (ok\<^sub>v' \<and> infsetsum (pmf prob\<^sub>v') (Collect \<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>e) = (1::real) \<longrightarrow>
           (\<exists>x::'a \<Rightarrow> 'a pmf.
               (\<forall>xa::'a. pmf prob\<^sub>v xa = (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v' xb \<cdot> pmf (x xb) xa)) \<and>
               (\<forall>xa::'a.
                   (\<exists>prob\<^sub>v::'a pmf.
                       (\<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>e xa \<longrightarrow> \<not> \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)) \<and>
                       (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb)) \<longrightarrow>
                   \<not> (0::real) < pmf prob\<^sub>v' xa)))"
          apply (rule_tac x = "True" in exI)
          apply (rule_tac x = "(pmf_of_list [(more,1.0)])" in exI)
          apply (rule conjI)
          apply (smt div_self filter.simps(1) filter.simps(2) infsetsum_cong list.map(1) list.map(2) 
              list.set(1) list.set(2) pmf_of_list_wf_def pmf_pmf_of_list prod.sel(1) prod.sel(2) 
              singletonD sum_list_simps(1) sum_list_simps(2))
          apply (auto)
          proof -
            assume a11: "infsetsum (pmf (pmf_of_list [(more, 1::real)])) (Collect \<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>e) = (1::real)"
            show "\<exists>x::'a \<Rightarrow> 'a pmf.
             (\<forall>xa::'a. pmf prob\<^sub>v xa = (\<Sum>\<^sub>axb::'a. pmf (pmf_of_list [(more, 1::real)]) xb \<cdot> pmf (x xb) xa)) \<and>
             (\<forall>xa::'a.
                 (\<exists>prob\<^sub>v::'a pmf.
                     (\<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>e xa \<longrightarrow> \<not> \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)) \<and>
                     (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb)) \<longrightarrow>
                 \<not> (0::real) < pmf (pmf_of_list [(more, 1::real)]) xa)"
              apply (rule_tac x = "\<lambda>x. prob\<^sub>v" in exI)
              apply (rule conjI)
              using f0 apply auto[1]
              apply auto
              proof -
                fix xa::"'a" and prob\<^sub>v'::"'a pmf"
                assume a111: "\<forall>xb::'a. pmf prob\<^sub>v' xb = pmf prob\<^sub>v xb"
                assume a112: "(0::real) < pmf (pmf_of_list [(more, 1::real)]) xa"
                assume a113: "\<not> \<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>e xa"
                from a112 have f111: "xa = more"
                  by (smt filter.simps(1) filter.simps(2) list.map(1) list.map(2) list.set(1) 
                      list.set(2) pmf_of_list_wf_def pmf_pmf_of_list prod.sel(1) prod.sel(2) 
                      singletonD sum_list.Nil sum_list_simps(2))
                from a11 have f112: "\<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>e more"
                  by (smt a112 a113 filter.simps(1) filter.simps(2) infsetsum_all_0 list.set(1) 
                      list.set(2) list.simps(8) list.simps(9) mem_Collect_eq pmf_of_list_wf_def 
                      pmf_pmf_of_list singletonD snd_conv sum_list.Cons sum_list.Nil)
                show "False"
                  using a113 f111 f112 by blast
              next
                fix xa::"'a" and prob\<^sub>v'::"'a pmf"
                assume a111: "\<forall>xb::'a. pmf prob\<^sub>v' xb = pmf prob\<^sub>v xb"
                assume a112: "(0::real) < pmf (pmf_of_list [(more, 1::real)]) xa"
                assume a113: "\<not> \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>)"
                from a112 have f111: "xa = more"
                  by (smt filter.simps(1) filter.simps(2) list.map(1) list.map(2) list.set(1) 
                      list.set(2) pmf_of_list_wf_def pmf_pmf_of_list prod.sel(1) prod.sel(2) 
                      singletonD sum_list.Nil sum_list_simps(2))
                from a111 have f112: "prob\<^sub>v' = prob\<^sub>v"
                  by (simp add: pmf_eqI)
                then show "False"
                  using a113 a1 f111 by blast
              qed
          qed
        qed
    show ?thesis
      using f1 by (simp add: p)
  qed

lemma kleisli_lift_skip_right_unit:
  assumes "P is \<^bold>N"
  shows "P ;;\<^sub>p (II\<^sub>p) = P"
  proof -
    obtain pre\<^sub>p post\<^sub>p where p:"P = (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p)" 
      using assms by (metis ndesign_form)
    have f1: "(pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) ;;\<^sub>p (II\<^sub>p) = (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p)"
      apply (simp add: kleisli_lift_skip')
      by (rel_auto)
    show ?thesis
      using p f1 by simp
  qed

(*
lemma 
  fixes f::"'a \<Rightarrow> real" and g::"'a \<Rightarrow> real"
  assumes "(\<lambda>x. f x) abs_summable_on A"
  assumes "(\<lambda>x. g x) abs_summable_on A"
  shows "(\<lambda>x. f x * g x) abs_summable_on A"
  using assms sledgehammer
*)

term "x abs_summable_on A"
term "integrable"
term "has_bochner_integral M f x"
term "integral\<^sup>L M f = (if \<exists>x. has_bochner_integral M f x then THE x. has_bochner_integral M f x else 0)"
term "infsetsum f A = lebesgue_integral (count_space A) f"
term "measure_of"

term "infsetsum (\<lambda>x. 
            (infsetsum 
              (\<lambda>xa. if pmf prob\<^sub>v' xa > 0 then pmf prob\<^sub>v' xa \<cdot> pmf (xx xa) x else 0) 
              UNIV)) 
            ({t. \<exists>y::'b. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, t)})"
term "simple_bochner_integrable x a"
term "sum"
thm "sum.If_cases"
thm "sum.Sigma"
thm "sum.swap"
term "ennreal"
term "ereal"

lemma sum_ennreal_extract:
  assumes "\<forall>x. P x \<ge> 0"
  shows "sum (\<lambda>x. ennreal (P x)) A = (ennreal (sum (\<lambda>x. P x) A))"
  using assms by auto

lemma sum_uniform_value:
  assumes "A \<noteq> {}" "finite A"
  shows "sum (\<lambda>x. C/(card A)) A = C"
  using assms by simp

lemma sum_uniform_value':
  assumes "\<forall>y. finite (A y)" "\<forall>y \<in> B. (A y \<noteq> {})"
  shows "sum (\<lambda>y. sum (\<lambda>x. C y/(card (A y))) (A y)) B = (sum (\<lambda>y. C y) B)"
  using assms by (simp add: sum_uniform_value)

lemma sum_uniform_value_zero:
  assumes "A = {}" "finite A"
  shows "sum (\<lambda>x. C/(card A)) A = 0"
  using assms by simp

(*
Jim mentioned to simplify sequential composition laws by only considering deterministic programs, 
no demonic choice, which might simplify sequential composition. May need more algebraic laws.
*)

lemma pemb_seq_comp:
  fixes D1::"('a, 'a) rel_des" and D2::"('a, 'a) rel_des"
  \<comment> \<open>He Jifeng's original paper doesn't explicitly mention the finiteness condition, but implicitly 
    in the construction of f(u,v) where a @{term "card"} function is used. Without this condition, 
    we are not able to prove this lemmas now because of subgoals 2 and 5 below which needs this 
    condition to transform infsetsum to sum. More importantly, swap summation operators like
       @{text "sum x. (sum y. (f x y))"} to @{text "sum y. (sum x. (f x y))"}
    in order to expand some expressions.
    \<close>
  assumes "finite (UNIV::'a set)"
  assumes "D1 is \<^bold>N" "D2 is \<^bold>N"
  shows "\<K>(D1 ;; D2) = \<K>(D1) ;; (\<up> (\<K>(D2)))"
  proof -
    obtain p P q Q
    where p:"D1 = (p \<turnstile>\<^sub>n P)" and 
          q:"D2 = (q \<turnstile>\<^sub>n Q)" 
      using assms by (metis ndesign_form)
    have seq_comp_ndesign: "\<K>((p \<turnstile>\<^sub>n P) ;; (q \<turnstile>\<^sub>n Q)) = \<K>((p \<turnstile>\<^sub>n P)) ;; (\<up> (\<K>((q \<turnstile>\<^sub>n Q))))"
      apply (simp add: ndesign_composition_wp prob_lift)
      apply (simp add: kleisli_lift2_def kleisli_lift_def upred_set_def)
      apply (rel_auto)
      \<comment> \<open>Five subgoals to prove: 1, 3, 4 regarding preconditions and 2,5 for postconditions.
        Subgoal 2 and 5 are nontrivial. \<close>
      proof -
        fix ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and prob\<^sub>v::"'a pmf" and y::"'a"
        assume a1: "\<forall>(ok\<^sub>v''::bool) prob\<^sub>v'::'a pmf.
          ok\<^sub>v \<and> \<lbrakk>p\<rbrakk>\<^sub>e more \<and> (ok\<^sub>v'' \<longrightarrow> \<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v' x) = (1::real)) \<or>
          ok\<^sub>v'' \<and>
          infsetsum (pmf prob\<^sub>v') (Collect \<lbrakk>q\<rbrakk>\<^sub>e) = (1::real) \<and>
          (ok\<^sub>v' \<longrightarrow>
           (\<forall>x::'a \<Rightarrow> 'a pmf.
               (\<exists>xa::'a. \<not> pmf prob\<^sub>v xa = (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v' xb \<cdot> pmf (x xb) xa)) \<or>
               (\<exists>xa::'a.
                   (\<exists>prob\<^sub>v::'a pmf.
                       (\<lbrakk>q\<rbrakk>\<^sub>e xa \<longrightarrow> \<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (xa, x). pmf prob\<^sub>v x) = (1::real)) \<and>
                       (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb)) \<and>
                   (0::real) < pmf prob\<^sub>v' xa)))"
        assume a2: "\<lbrakk>P\<rbrakk>\<^sub>e (more, y)"
        \<comment> \<open> Since a1 holds for every @{text "prob\<^sub>v'"}, we choose a simple distribution @{text "?prob\<^sub>v'"},
          a point distribution. \<close>
        let ?ok\<^sub>v'' = "True"
        let ?prob\<^sub>v' = "(pmf_of_list [(y,1.0)])"
        have f1: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf (?prob\<^sub>v') x) = 
            (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). if x = y then 1 else 0)"
          by (smt divide_self_if filter.simps(1) filter.simps(2) infsetsum_cong list.map(1) 
              list.map(2) list.set(1) list.set(2) pmf_of_list_wf_def pmf_pmf_of_list prod.sel(1) 
              prod.sel(2) singletonD sum_list_simps(1) sum_list_simps(2))
        also have f2: "... = (\<Sum>\<^sub>ax \<in> {y} \<union> {t. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> t \<noteq> y}. if x = y then 1 else 0)"
          using a2 by (smt Collect_cong Un_insert_left 
              bounded_semilattice_sup_bot_class.sup_bot.left_neutral insert_compr mem_Collect_eq)
        also have f3: "... = (\<Sum>\<^sub>ax \<in> {y}. if x = y then 1 else 0) + 
          (\<Sum>\<^sub>ax \<in> {t. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> t \<noteq> y}. if x = y then 1 else 0)"
          unfolding infsetsum_altdef abs_summable_on_altdef
          apply (subst set_integral_Un, auto)
          apply (meson abs_summable_on_altdef abs_summable_on_empty abs_summable_on_insert_iff)
          using abs_summable_on_altdef by (smt abs_summable_on_0 abs_summable_on_cong mem_Collect_eq)
        also have f4: "... = (1::real)"
          by (smt finite.emptyI finite.insertI infsetsum_all_0 infsetsum_finite insert_absorb 
              insert_not_empty mem_Collect_eq sum.insert)
        have f5: "(ok\<^sub>v \<and> \<lbrakk>p\<rbrakk>\<^sub>e more \<and> 
          (True \<longrightarrow> \<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf (?prob\<^sub>v') x) = (1::real))) = False"
          using calculation f4 by auto
        from f5 have f6: "infsetsum (pmf ?prob\<^sub>v') (Collect \<lbrakk>q\<rbrakk>\<^sub>e) = (1::real)"
          using a1 by blast
        then have f7: "infsetsum (\<lambda>x. if x = y then 1 else 0) (Collect \<lbrakk>q\<rbrakk>\<^sub>e) = (1::real)"
          by (smt div_self filter.simps(1) filter.simps(2) infsetsum_cong list.map(1) list.map(2) 
              list.set(1) list.set(2) pmf_of_list_wf_def pmf_pmf_of_list prod.sel(1) prod.sel(2) 
              singletonD sum_list_simps(1) sum_list_simps(2))
        then have f8: "y \<in> (Collect \<lbrakk>q\<rbrakk>\<^sub>e)"
          by (smt infsetsum_all_0)
        show "\<lbrakk>q\<rbrakk>\<^sub>e y"
          using f8 by auto
      next
        \<comment> \<open> Subgoal 2: postcondition implied from LHS to RHS:
            @{text "prob'(P;Q)=1"} implies there exists an intermediate distribution @{text "\<rho>"} and 
            a function (@{text "Q"} in He's paper) from intermediate states to the distribution on 
            final states.
          \<close>
        fix ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and prob\<^sub>v::"'a pmf"
        assume a1: "(\<Sum>\<^sub>ax::'a | \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x). pmf prob\<^sub>v x) = (1::real)"

        \<comment> \<open> @{text "?f(s', s\<^sub>0)"}, @{text "?p"} and @{text "?Q"} are corresponding functions to 
          construct f, p and Q in He's paper. \<close>
        let ?f = "\<lambda> s' s\<^sub>0. (if \<lbrakk>P\<rbrakk>\<^sub>e (more, s\<^sub>0) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (s\<^sub>0, s') then 
              (pmf prob\<^sub>v s'/(card {t. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, s')})) 
            else 0)"
        let ?p = "\<lambda>s\<^sub>0 . (\<Sum>\<^sub>a s'::'a . ?f s' s\<^sub>0)"
        \<comment> \<open> The else branch is not defined in He's paper. It couldn't be zero here as @{text "?Q"} is
            used to give a witness (@{text "\<lambda>s. embed_pmf (?Q s)"}) for @{text "\<exists>x::'a \<Rightarrow> 'a pmf"}.
            The type of @{text "x"} is from states to a pmf distribution. If the else branch gives
            zero, it couldn't be able to construct a pmf distribution (sum is equal to 1). Therefore,
            we choose a uniform distribution upon whole state space if @{text "?p s\<^sub>0"} is equal to 0. \<close>
        let ?Q = "\<lambda>s\<^sub>0 s'. (if ?p s\<^sub>0 > 0 then (?f s' s\<^sub>0 / ?p s\<^sub>0) else (1/card (UNIV::'a set)))"

        (* Used to prove "mf (embed_pmf ?p) x = ?p x" *)
        \<comment> \<open> We construct a witness for @{text "prob\<^sub>v'"} by embeding @{text "?p"} function using
           @{term "embed_pmf"}. After that, we also need to expand @{text "pmf (embed_pmf ?p) x"} to
           @{text "?p x"} by @{text "pmf_embed_pmf"} which also needs to prove @{text "nonneg"} and 
           @{text "prob"} assumptions. @{text "p_prob"} is for the @{text "prob"} condition.
          \<close>
        have p_prob: "(\<Sum>a::'a\<in>UNIV.  ennreal (\<Sum>x::'a\<in>UNIV.
          if \<lbrakk>P\<rbrakk>\<^sub>e (more, a) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (a, x) then pmf prob\<^sub>v x / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, x)})
          else (0::real))) = (1::ennreal)"
          proof - 
            from a1 have f11: "(\<Sum>\<^sub>ax::'a | \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x). pmf prob\<^sub>v x) = 
              (\<Sum>x \<in> {t. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, t)}. pmf prob\<^sub>v x)"
              using assms(1) apply (simp)
              by (metis (no_types, lifting) finite_subset infsetsum_finite subset_UNIV)
            then have f12: "(\<Sum>x \<in> {t. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, t)}. pmf prob\<^sub>v x) = (1::real)"
              using a1 by linarith
            have prob_ennreal_extract: "(\<Sum>a::'a\<in>UNIV.  ennreal
                (\<Sum>x::'a\<in>UNIV.
                   if \<lbrakk>P\<rbrakk>\<^sub>e (more, a) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (a, x)
                   then pmf prob\<^sub>v x / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, x)}) else (0::real)))
                = (ennreal (\<Sum>a::'a\<in>UNIV.  
                (\<Sum>x::'a\<in>UNIV. ( (
                   if \<lbrakk>P\<rbrakk>\<^sub>e (more, a) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (a, x)
                   then pmf prob\<^sub>v x / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, x)}) else (0::real))))))"
              apply (rule sum_ennreal_extract)
              by (simp add: sum_nonneg)
            have prob_swap: "(\<Sum>a::'a\<in>UNIV.  
              (\<Sum>x::'a\<in>UNIV. ((
                 if \<lbrakk>P\<rbrakk>\<^sub>e (more, a) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (a, x)
                 then pmf prob\<^sub>v x / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, x)}) else (0::real)))))
              = (\<Sum>x::'a\<in>UNIV.  
              (\<Sum>a::'a\<in>UNIV. (
                 if \<lbrakk>P\<rbrakk>\<^sub>e (more, a) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (a, x)
                 then pmf prob\<^sub>v x / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, x)}) else (0::real))))"
              by (rule sum.swap)
            have prob_if_cases: "... = (\<Sum>x::'a\<in>UNIV. 
                    ((sum (\<lambda>a. pmf prob\<^sub>v x / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, x)})) 
                    ({a. \<lbrakk>P\<rbrakk>\<^sub>e (more, a) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (a, x)}))))"
              using assms(1) by (simp add: sum.If_cases)
            have prob_set_split: "... = (\<Sum>x::'a\<in>({x. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x)} \<union> 
                      -{x. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x)}). 
                    ((sum (\<lambda>a. pmf prob\<^sub>v x / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, x)})) 
                    ({a. \<lbrakk>P\<rbrakk>\<^sub>e (more, a) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (a, x)}))))"
              by simp
            have prob_disjoint_union: "... = (\<Sum>x::'a\<in>({x. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x)}). 
                    ((sum (\<lambda>a. pmf prob\<^sub>v x / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, x)})) 
                    ({a. \<lbrakk>P\<rbrakk>\<^sub>e (more, a) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (a, x)})))) +
              (\<Sum>x::'a\<in>(-{x. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x)}). 
                    ((sum (\<lambda>a. pmf prob\<^sub>v x / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, x)})) 
                    ({a. \<lbrakk>P\<rbrakk>\<^sub>e (more, a) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (a, x)}))))"
              by (metis (mono_tags, lifting) Compl_iff IntE assms(1) 
                    boolean_algebra_class.sup_compl_top finite_Un sum.union_inter_neutral)
            have prob_elim_zero: "... = (\<Sum>x::'a\<in>({x. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x)}). 
                    ((sum (\<lambda>a. pmf prob\<^sub>v x / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, x)})) 
                    ({a. \<lbrakk>P\<rbrakk>\<^sub>e (more, a) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (a, x)}))))"
              apply (simp add: sum_uniform_value_zero)
              by (smt Compl_eq card_eq_sum mem_Collect_eq sum.not_neutral_contains_not_neutral)
            have prob_uniform_value: "... = (\<Sum>x::'a\<in>({x. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x)}). 
                    (pmf prob\<^sub>v x ))"
              apply (rule sum_uniform_value')
              using assms(1) rev_finite_subset apply auto[1]
              by blast
            have prob_eq_1: "... = (1::real)"
              using f12 by auto
            show "(\<Sum>a::'a\<in>UNIV.  ennreal
                (\<Sum>x::'a\<in>UNIV.
                   if \<lbrakk>P\<rbrakk>\<^sub>e (more, a) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (a, x) then pmf prob\<^sub>v x / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, x)})
                   else (0::real))) = (1::ennreal)"
              using ennreal_1 prob_disjoint_union prob_elim_zero prob_ennreal_extract prob_eq_1 
                prob_if_cases prob_set_split prob_swap prob_uniform_value by presburger
          qed

        \<comment> \<open> This is the subgoal 2. We need @{text "?p"} and @{text "?Q"} to construct witnesses for 
           @{text "prob\<^sub>v'"} and @{text "x"} respectively. \<close>
        show "\<exists>(ok\<^sub>v'::bool) prob\<^sub>v'::'a pmf.
          (ok\<^sub>v \<and> \<lbrakk>p\<rbrakk>\<^sub>e more \<longrightarrow> ok\<^sub>v' \<and> (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v' x) = (1::real)) \<and>
          (ok\<^sub>v' \<and> infsetsum (pmf prob\<^sub>v') (Collect \<lbrakk>q\<rbrakk>\<^sub>e) = (1::real) \<longrightarrow>
           (\<exists>x::'a \<Rightarrow> 'a pmf.
               (\<forall>xa::'a. pmf prob\<^sub>v xa = (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v' xb \<cdot> pmf (x xb) xa)) \<and>
               (\<forall>xa::'a.
                   (\<exists>prob\<^sub>v::'a pmf.
                       (\<lbrakk>q\<rbrakk>\<^sub>e xa \<longrightarrow> \<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (xa, x). pmf prob\<^sub>v x) = (1::real)) \<and>
                       (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb)) \<longrightarrow>
                   \<not> (0::real) < pmf prob\<^sub>v' xa)))"
          apply (rule_tac x = "True" in exI)
          \<comment> \<open> Construct a witness for @{text "prob\<^sub>v'"} by @{text "?p"} \<close>
          apply (rule_tac x = "embed_pmf (?p)" in exI)
          apply (auto)
          proof -
            have f1: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x).
               pmf (embed_pmf
                     (\<lambda>s\<^sub>0::'a.
                         \<Sum>\<^sub>as'::'a.
                           if \<lbrakk>P\<rbrakk>\<^sub>e (more, s\<^sub>0) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (s\<^sub>0, s')
                           then pmf prob\<^sub>v s' / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, s')})
                           else (0::real))) x)
              = (\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). ?p x)"
              apply (subst pmf_embed_pmf)
              apply (simp add: infsetsum_nonneg)
              apply (simp add: assms(1) nn_integral_count_space_finite)
              defer
              apply (simp)
              using p_prob by blast
            have f2: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). ?p x) = (1::real)"
              proof -
                have P_infset_to_fset: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). ?p x) = 
                      (\<Sum>x::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). (\<Sum>s'::'a\<in>UNIV. ?f s' x))"
                  using assms(1)
                  by (smt boolean_algebra_class.sup_compl_top finite_Un infsetsum_finite sum_mono)
                have P_swap: "... = (\<Sum>s'::'a\<in>UNIV. \<Sum>x::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). ?f s' x)"
                  by (rule sum.swap)
                have P_if_cases: "... = (\<Sum>s'::'a\<in>UNIV.
                  ((sum (\<lambda>x. pmf prob\<^sub>v s' / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, s')})) 
                        ({x. \<lbrakk>P\<rbrakk>\<^sub>e (more, x)} \<inter> {x. \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (x, s')}))))"
                  using assms(1) apply (subst sum.If_cases)
                  using rev_finite_subset apply blast
                  by simp
                have P_if_cases': "... = (\<Sum>s'::'a\<in>UNIV.
                  ((sum (\<lambda>x. pmf prob\<^sub>v s' / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, s')})) 
                        ({x. \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (x, s')}))))"
                  by (simp add: Collect_conj_eq)
                have P_split: "... = (\<Sum>s'::'a\<in>({x. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x)} \<union> 
                     -{x. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x)}).
                    ((sum (\<lambda>x. pmf prob\<^sub>v s' / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, s')})) 
                        ({x. \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (x, s')}))))"
                  by simp
                have P_disjoint_union: "... = (\<Sum>s'::'a\<in>({x. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x)}).
                    ((sum (\<lambda>x. pmf prob\<^sub>v s' / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, s')})) 
                        ({x. \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (x, s')})))) + 
                    (\<Sum>s'::'a\<in>(-{x. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x)}).
                    ((sum (\<lambda>x. pmf prob\<^sub>v s' / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, s')})) 
                        ({x. \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (x, s')}))))"
                  by (meson Compl_iff Int_iff assms(1) finite_subset subset_UNIV sum.union_inter_neutral)
                have P_elim_zero: "... = (\<Sum>s'::'a\<in>({x. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x)}).
                    ((sum (\<lambda>x. pmf prob\<^sub>v s' / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, s')})) 
                        ({x. \<lbrakk>P\<rbrakk>\<^sub>e (more, x) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (x, s')}))))"
                  apply (simp add: sum_uniform_value_zero)
                  by (smt Compl_eq card_eq_sum mem_Collect_eq sum.not_neutral_contains_not_neutral)
                have P_sum_elim: "... = (\<Sum>s'::'a\<in>({x. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x)}). pmf prob\<^sub>v s')"
                  apply (rule sum_uniform_value')
                  using assms(1) rev_finite_subset apply auto[1]
                  by blast
                have prob_eq_1: "... = (1::real)"
                  by (metis (no_types, lifting) Compl_partition a1 assms(1) finite_Un infsetsum_finite)
                show ?thesis
                  using P_disjoint_union P_elim_zero P_if_cases P_if_cases' P_infset_to_fset 
                        P_split P_sum_elim P_swap prob_eq_1 by linarith
              qed
            show "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x).
               pmf (embed_pmf
                     (\<lambda>s\<^sub>0::'a.
                         \<Sum>\<^sub>as'::'a.
                           if \<lbrakk>P\<rbrakk>\<^sub>e (more, s\<^sub>0) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (s\<^sub>0, s')
                           then pmf prob\<^sub>v s' / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, s')})
                           else (0::real)))
                x) = (1::real)"
              by (simp add: f1 f2)
          next
            assume a_sum_q: "infsetsum (pmf (embed_pmf (?p))) (Collect \<lbrakk>q\<rbrakk>\<^sub>e) = (1::real)"
            have f01: "\<forall>s. (\<Sum>a::'a\<in>UNIV. (?Q s) a) = (1::real)"
              proof -
                have Q_cond_ext: "\<forall>s. (\<Sum>a::'a\<in>UNIV. (?Q s) a) = 
                  (if (0::real) < ?p s
                  then \<Sum>a::'a\<in>UNIV. ?f a s / ?p s
                  else \<Sum>a::'a\<in>UNIV. (1::real) / real CARD('a))"
                  by auto
                have Q_uniform_dis: "(\<Sum>a::'a\<in>UNIV. (1::real) / real CARD('a)) = 1"
                  by (simp add: assms(1))
                have Q_sum_div_ext: "\<forall>s. (if (0::real) < ?p s
                  then \<Sum>a::'a\<in>UNIV. ?f a s / ?p s
                  else \<Sum>a::'a\<in>UNIV. (1::real) / real CARD('a)) = 
                  (if (0::real) < ?p s
                  then (\<Sum>a::'a\<in>UNIV. ?f a s) / ?p s
                  else \<Sum>a::'a\<in>UNIV. (1::real) / real CARD('a))"
                  by (simp add: sum_divide_distrib)
                have Q_eq_1: "\<forall>s. (if (0::real) < ?p s
                  then (\<Sum>a::'a\<in>UNIV. ?f a s) / ?p s
                  else \<Sum>a::'a\<in>UNIV. (1::real) / real CARD('a)) = 1"
                  by (simp add: assms(1))
                show ?thesis
                  by (simp add: Q_cond_ext Q_eq_1 Q_sum_div_ext)
              qed
            have P_simp: "\<forall>x. pmf (embed_pmf (?p)) x = ?p x"
              apply (subst pmf_embed_pmf)
              apply (simp add: infsetsum_nonneg)
              apply (simp add: assms(1) nn_integral_count_space_finite)
              defer
              apply (simp)
              using p_prob by blast
            from a_sum_q have a_sum_q': "infsetsum ?p (Collect \<lbrakk>q\<rbrakk>\<^sub>e) = (1::real)"
              using P_simp by auto
            have Q_simp: "\<forall>x. \<forall>s. pmf (embed_pmf (?Q s)) x = (?Q s) x"
              apply (subst pmf_embed_pmf)
              apply (simp add: infsetsum_nonneg)
              apply (simp add: assms(1) nn_integral_count_space_finite)
              defer
              apply (simp)
              using f01 by (simp add: assms(1))
            have f02: "(\<forall>xa::'a.
                 pmf prob\<^sub>v xa = (\<Sum>\<^sub>axb::'a. pmf (embed_pmf (?p)) xb \<cdot> pmf (embed_pmf (?Q xb)) xa))"
              proof -
                have f021: "\<forall>xa::'a. (\<Sum>\<^sub>axb::'a. pmf (embed_pmf (?p)) xb \<cdot> pmf (embed_pmf (?Q xb)) xa)
                  = (\<Sum>\<^sub>axb::'a. (?p xb) \<cdot> pmf (embed_pmf (?Q xb)) xa)"
                  using P_simp by auto
                have f022: "\<forall>xa::'a. (\<Sum>\<^sub>axb::'a. (?p xb) \<cdot> pmf (embed_pmf (?Q xb)) xa) = 
                  (\<Sum>\<^sub>axb::'a. (?p xb) \<cdot> (?Q xb) xa)"
                  using Q_simp by auto
                have f023: "\<forall>xa::'a. (\<Sum>\<^sub>axb::'a. (?p xb) \<cdot> (?Q xb) xa) = 
                  (\<Sum>\<^sub>axb::'a. 
                  (if (0::real) < (?p xb)
                   then ((?p xb) \<cdot> (?f xa xb / ?p xb))
                   else ((?p xb) \<cdot> ((1::real) / real CARD('a)))))"
                  using assms(1)
                  by (smt div_by_1 infsetsum_cong nonzero_eq_divide_eq times_divide_eq_right)
                have p_leq_zero: "\<forall>xb. (?p xb)\<ge> 0"
                  by (simp add: infsetsum_nonneg)
                have f024: "\<forall>xa::'a. (\<Sum>\<^sub>axb::'a. 
                  (if (0::real) < (?p xb)
                   then ((?p xb) \<cdot> (?f xa xb / ?p xb))
                   else ((?p xb) \<cdot> ((1::real) / real CARD('a))))) = 
                  (\<Sum>\<^sub>axb::'a. (if (0::real) < (?p xb) then (?f xa xb) else 0))"
                  using p_leq_zero
                  by (smt divide_cancel_right infsetsum_cong mult_not_zero nonzero_mult_div_cancel_left)
                have f025: "\<forall>xa::'a. (\<Sum>\<^sub>axb::'a. (if (0::real) < (?p xb) then (?f xa xb) else 0)) = 
                  (\<Sum>xb::'a\<in>{xb. (0::real) < (?p xb)}. (?f xa xb))"
                  using assms(1) by (simp add: sum.If_cases)
                have f026: "\<forall>xa::'a. (\<Sum>xb::'a\<in>{xb. (0::real) < (?p xb)}. (?f xa xb))
                  = (\<Sum>xb::'a\<in>({xb. (0::real) < (?p xb)} \<inter> {xb. \<lbrakk>P\<rbrakk>\<^sub>e (more, xb) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (xb, xa)}). 
                    (pmf prob\<^sub>v xa / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, xa)})))"
                  using assms(1) apply (subst sum.If_cases)
                  using rev_finite_subset apply blast
                  by simp 
                have f028: "\<forall>xa::'a. (\<Sum>xb::'a\<in>({xb. (0::real) < (?p xb)} \<inter> 
                      {xb. \<lbrakk>P\<rbrakk>\<^sub>e (more, xb) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (xb, xa)}). 
                    (pmf prob\<^sub>v xa / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, xa)}))) = pmf prob\<^sub>v xa"
                  apply (rule allI)
                  proof -
                    fix xa::"'a"
                    show "(\<Sum>xb::'a\<in>({xb. (0::real) < (?p xb)} \<inter> 
                        {xb. \<lbrakk>P\<rbrakk>\<^sub>e (more, xb) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (xb, xa)}). 
                      (pmf prob\<^sub>v xa / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, xa)}))) = pmf prob\<^sub>v xa"
                      proof (cases "pmf prob\<^sub>v xa = 0")
                        case True
                        then show ?thesis
                          by simp
                      next
                        case False
                        then have notneg: "pmf prob\<^sub>v xa > 0"
                          by simp
                        from a1 have comp_set: 
                          "(\<Sum>\<^sub>ax::'a \<in> -{x. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x)}. pmf prob\<^sub>v x) = (0::real)"
                          using pmf_comp_set by blast
                        then have all_zero: "\<forall>x \<in> -{x. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x)}. pmf prob\<^sub>v x = 0"
                          using pmf_all_zero by blast
                        have not_in: "xa \<notin> -{x. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x)}"
                          using notneg all_zero False by blast
                        then have is_in: "xa \<in> {x. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x)}"
                          by blast
                        then have exist: "\<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, xa)"
                          by blast
                        then have card_not_zero: "real (card {xb. \<lbrakk>P\<rbrakk>\<^sub>e (more, xb) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (xb, xa)}) \<noteq> 0"
                          by (metis (no_types, lifting) Collect_empty_eq assms(1) card_0_eq 
                              finite_subset of_nat_0_eq_iff order_top_class.top_greatest)
                        have ff: "{xb. \<lbrakk>P\<rbrakk>\<^sub>e (more, xb) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (xb, xa)} \<subseteq> {xb. (0::real) < (?p xb)}"
                          apply auto
                          proof -
                            fix x::"'a"
                            assume a11: "\<lbrakk>P\<rbrakk>\<^sub>e (more, x)"
                            assume a12: "\<lbrakk>Q\<rbrakk>\<^sub>e (x, xa)"
                            let ?fx = "\<lambda>xb. if \<lbrakk>Q\<rbrakk>\<^sub>e (x, xb) then pmf prob\<^sub>v xb / 
                              real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, xb)}) else (0::real)"
                            have ff0: "\<forall>xb. ?fx xb \<ge> 0"
                              by simp
                            then have ff1:"(\<Sum>xb::'a\<in>{xa}. ?fx xb) \<le> (\<Sum>xa::'a\<in>UNIV. ?fx xa)"
                              using assms(1) apply (subst sum_mono2)
                              apply blast
                              apply blast
                              apply blast
                              by auto
                            then have ff2:"(\<Sum>\<^sub>axb::'a\<in>{xa}. ?fx xb) \<le> (\<Sum>\<^sub>a xa::'a. ?fx xa)"
                              using assms(1) by simp
                            have card_no_zero: "(card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, xa)}) > 0"
                              using a11 a12
                              by (metis (mono_tags, lifting) Collect_empty_eq assms(1) card_gt_0_iff 
                                 finite_subset order_top_class.top_greatest)
                            have ff3:"(\<Sum>\<^sub>axb::'a\<in>{xa}. ?fx xb) = pmf prob\<^sub>v xa / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, xa)})"
                              using a12 by auto
                            have ff4:"... > 0"
                              using notneg card_no_zero
                              by simp
                            show "(0::real) < (\<Sum>\<^sub>axa::'a. if \<lbrakk>Q\<rbrakk>\<^sub>e (x, xa) then pmf prob\<^sub>v xa / 
                              real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, xa)}) else (0::real))"
                              using ff2 ff3 ff4 by linarith
                          qed
  
                        have ff1: "(\<Sum>xb::'a\<in>({xb. (0::real) < (?p xb)} \<inter> 
                          {xb. \<lbrakk>P\<rbrakk>\<^sub>e (more, xb) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (xb, xa)}). 
                          (pmf prob\<^sub>v xa / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, xa)}))) =
                          (\<Sum>xb::'a\<in>({xb. \<lbrakk>P\<rbrakk>\<^sub>e (more, xb) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (xb, xa)}). 
                          (pmf prob\<^sub>v xa / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, xa)})))"
                          using ff
                          by (simp add: semilattice_inf_class.inf.absorb_iff2)
                        have ff2: "... = 
                          (real (card {xb. \<lbrakk>P\<rbrakk>\<^sub>e (more, xb) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (xb, xa)}) *
                          (pmf prob\<^sub>v xa / real (card {t::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, t) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (t, xa)})))"
                          by simp
                        have ff3: "... = pmf prob\<^sub>v xa"
                          using card_not_zero by simp
                        show ?thesis
                          using ff1 ff2 ff3 by linarith
                      qed
                  qed
                  show ?thesis
                    using f021 f022 f023 f024 f025 f026 f028 by auto
              qed
            show "\<exists>x::'a \<Rightarrow> 'a pmf. 
              (\<forall>xa::'a.
                 pmf prob\<^sub>v xa = (\<Sum>\<^sub>axb::'a. pmf (embed_pmf (?p)) xb \<cdot> pmf (x xb) xa)) \<and>
              (\<forall>xa::'a.
                 (\<exists>prob\<^sub>v::'a pmf.
                     (\<lbrakk>q\<rbrakk>\<^sub>e xa \<longrightarrow> \<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (xa, x). pmf prob\<^sub>v x) = (1::real)) \<and>
                     (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb)) \<longrightarrow>
                 \<not> (0::real) < pmf (embed_pmf (?p)) xa)"
              apply (rule_tac x = "\<lambda>s. embed_pmf (?Q s)" in exI)
              apply (rule conjI)
              using f02 apply blast
              proof
                fix xa::"'a"
                have f10: "(\<exists>prob\<^sub>v::'a pmf.
                     (\<lbrakk>q\<rbrakk>\<^sub>e xa \<longrightarrow> \<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (xa, x). pmf prob\<^sub>v x) = (1::real)) \<and>
                     (\<forall>xb::'a. pmf prob\<^sub>v xb = (?Q xa) xb)) \<longrightarrow>
                  \<not> (0::real) < ?p xa"
                  apply (rule impI)
                  proof - 
                    assume aa: "(\<exists>prob\<^sub>v::'a pmf.
                       (\<lbrakk>q\<rbrakk>\<^sub>e xa \<longrightarrow> \<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (xa, x). pmf prob\<^sub>v x) = (1::real)) \<and>
                       (\<forall>xb::'a. pmf prob\<^sub>v xb = (?Q xa) xb))"
                    have "((\<lbrakk>q\<rbrakk>\<^sub>e xa \<longrightarrow> \<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (xa, x). (?Q xa) x) = (1::real)))"
                      using aa by auto
                    then have "\<not>\<lbrakk>q\<rbrakk>\<^sub>e xa \<or> (\<lbrakk>q\<rbrakk>\<^sub>e xa \<and> \<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (xa, x). (?Q xa) x) = (1::real))"
                      by (simp add: disjCI)
                    then show "\<not> (0::real) < ?p xa"
                      proof
                        assume aa: "\<not>\<lbrakk>q\<rbrakk>\<^sub>e xa"
                        from a_sum_q' have "infsetsum ?p (-Collect \<lbrakk>q\<rbrakk>\<^sub>e) = (0::real)"
                          by (metis (no_types, lifting) P_simp infsetsum_cong pmf_comp_set)
                        then show "\<not> (0::real) < ?p xa"
                          using a_sum_q' pmf_all_zero aa 
                          by (smt Compl_iff P_simp infsetsum_cong mem_Collect_eq) 
                      next
                        assume aa1: "(\<lbrakk>q\<rbrakk>\<^sub>e xa \<and> \<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (xa, x). (?Q xa) x) = (1::real))"
                        show "\<not> (0::real) < ?p xa"
                          proof (rule ccontr)
                            assume ac: "\<not>\<not>(0::real) < ?p xa"
                            from ac have "\<lbrakk>P\<rbrakk>\<^sub>e (more, xa)"
                              by force
                            have fc: "(\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (xa, x). (?Q xa) x) = 
                              (\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (xa, x). (?f x xa / ?p xa))"
                              using ac by auto
                            have fc1: "... = (\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (xa, x). (?f x xa))/?p xa"
                              proof -
                                have "\<forall>r A f. infsetsum f A / (r::real) = (\<Sum>\<^sub>aa\<in>A. f (a::'a) / r)"
                                  by (metis assms(1) finite_subset infsetsum_finite subset_UNIV 
                                     sum_divide_distrib)
                                then show ?thesis
                                  by presburger
                              qed
                            have fc2: "... = (\<Sum>\<^sub>ax::'a \<in> (UNIV-(-{x. \<lbrakk>Q\<rbrakk>\<^sub>e (xa, x)})). (?f x xa))/?p xa"
                              by simp
                            have fc3: "... = ((\<Sum>\<^sub>ax::'a \<in> (UNIV). (?f x xa)) - 
                              (\<Sum>\<^sub>ax::'a \<in> (-{x. \<lbrakk>Q\<rbrakk>\<^sub>e (xa, x)}). (?f x xa)))/?p xa"
                              using assms(1)
                              by (smt Compl_eq_Diff_UNIV DiffE IntE boolean_algebra_class.sup_compl_top 
                                  finite_Un infsetsum_finite sum.not_neutral_contains_not_neutral 
                                  sum.union_inter)
                            have fc4: "... = ((\<Sum>\<^sub>ax::'a \<in> (UNIV). (?f x xa))/?p xa) - 
                              (\<Sum>\<^sub>ax::'a \<in> (-{x. \<lbrakk>Q\<rbrakk>\<^sub>e (xa, x)}). (?f x xa))/?p xa"
                              using diff_divide_distrib by blast
                            have fc5: "... = 1"
                              by (smt ComplD aa1 ac div_self fc fc1 fc2 fc3 infsetsum_all_0 mem_Collect_eq)
                            show "False"
                                using aa1 fc5 fc fc1 fc2 fc3 fc4 by linarith
                          qed
                      qed
                  qed
                    
                show "(\<exists>prob\<^sub>v::'a pmf.
                     (\<lbrakk>q\<rbrakk>\<^sub>e xa \<longrightarrow> \<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (xa, x). pmf prob\<^sub>v x) = (1::real)) \<and>
                     (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (embed_pmf (?Q xa)) xb)) \<longrightarrow>
                  \<not> (0::real) < pmf (embed_pmf (?p)) xa"
                  using P_simp Q_simp f10 by auto
              qed
          qed
      next
        fix ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and ok\<^sub>v''::"bool" and prob\<^sub>v'::"'a pmf"
        assume a1: "\<forall>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<longrightarrow> \<lbrakk>q\<rbrakk>\<^sub>e y"
        assume a2: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v' x) = (1::real)"
        assume a3: "\<not> infsetsum (pmf prob\<^sub>v') (Collect \<lbrakk>q\<rbrakk>\<^sub>e) = (1::real)"
        from a1 have f1: "{t. \<lbrakk>P\<rbrakk>\<^sub>e (more, t)} \<subseteq> {t. \<lbrakk>q\<rbrakk>\<^sub>e t}"
          by blast
        have f2: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v' x) = (\<Sum>\<^sub>ax \<in> {t. \<lbrakk>P\<rbrakk>\<^sub>e (more, t)}. pmf prob\<^sub>v' x)"
          by blast
        have f3: "(\<Sum>\<^sub>ax::'a | \<lbrakk>q\<rbrakk>\<^sub>e x. pmf prob\<^sub>v' x) = (\<Sum>\<^sub>ax \<in> {t. \<lbrakk>q\<rbrakk>\<^sub>e t}. pmf prob\<^sub>v' x)"
          by blast
        have f4: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v' x) \<le> (\<Sum>\<^sub>ax::'a | \<lbrakk>q\<rbrakk>\<^sub>e x. pmf prob\<^sub>v' x)"
          using f2 f3 f1
          by (meson infsetsum_mono_neutral_left order_refl pmf_abs_summable pmf_nonneg)
        have f5: "(\<Sum>\<^sub>ax::'a | \<lbrakk>q\<rbrakk>\<^sub>e x. pmf prob\<^sub>v' x) = 1"
          using a2 f4 
          by (smt measure_pmf.prob_le_1 measure_pmf_conv_infsetsum)
        from f5 have f1: "infsetsum (pmf prob\<^sub>v') (Collect \<lbrakk>q\<rbrakk>\<^sub>e) = (1::real)"
          by blast
        show "ok\<^sub>v'"
          using f1 a3 by blast
      next
        fix ok\<^sub>v::"bool" and more::"'a" and prob\<^sub>v::"'a pmf" and ok\<^sub>v''::"bool" and prob\<^sub>v'::"'a pmf"
        assume a1: "\<forall>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<longrightarrow> \<lbrakk>q\<rbrakk>\<^sub>e y"
        assume a2: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v' x) = (1::real)"
        assume a3: "\<not> infsetsum (pmf prob\<^sub>v') (Collect \<lbrakk>q\<rbrakk>\<^sub>e) = (1::real)"
        from a1 have f1: "{t. \<lbrakk>P\<rbrakk>\<^sub>e (more, t)} \<subseteq> {t. \<lbrakk>q\<rbrakk>\<^sub>e t}"
          by blast
        have f2: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v' x) = (\<Sum>\<^sub>ax \<in> {t. \<lbrakk>P\<rbrakk>\<^sub>e (more, t)}. pmf prob\<^sub>v' x)"
          by blast
        have f3: "(\<Sum>\<^sub>ax::'a | \<lbrakk>q\<rbrakk>\<^sub>e x. pmf prob\<^sub>v' x) = (\<Sum>\<^sub>ax \<in> {t. \<lbrakk>q\<rbrakk>\<^sub>e t}. pmf prob\<^sub>v' x)"
          by blast
        have f4: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v' x) \<le> (\<Sum>\<^sub>ax::'a | \<lbrakk>q\<rbrakk>\<^sub>e x. pmf prob\<^sub>v' x)"
          using f2 f3 f1
          by (meson infsetsum_mono_neutral_left order_refl pmf_abs_summable pmf_nonneg)
        have f5: "(\<Sum>\<^sub>ax::'a | \<lbrakk>q\<rbrakk>\<^sub>e x. pmf prob\<^sub>v' x) = 1"
          using a2 f4 
          by (smt measure_pmf.prob_le_1 measure_pmf_conv_infsetsum)
        from f5 have f1: "infsetsum (pmf prob\<^sub>v') (Collect \<lbrakk>q\<rbrakk>\<^sub>e) = (1::real)"
          by blast
        show "(\<Sum>\<^sub>ax::'a | \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x). pmf prob\<^sub>v x) = (1::real)"
          using f1 a3 by blast
      next
        \<comment> \<open> Subgoal 5: postcondition implied from RHS to LHS:
            An intermediate distribution @{text "prob\<^sub>v'"} and a function @{text "xx"} from 
            intermediate states to the distribution on final states implies @{text "prob'(P;Q)=1"}.
          \<close>
        fix ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and prob\<^sub>v::"'a pmf" and ok\<^sub>v''::"bool" and 
            prob\<^sub>v'::"'a pmf" and xx::"'a \<Rightarrow>'a pmf"
        assume a1: "\<lbrakk>p\<rbrakk>\<^sub>e more"
        assume a2: "\<forall>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<longrightarrow> \<lbrakk>q\<rbrakk>\<^sub>e y"
        assume a3: "(\<Sum>\<^sub>ax::'a | \<lbrakk>P\<rbrakk>\<^sub>e (more, x). pmf prob\<^sub>v' x) = (1::real)"
        assume a4: "\<forall>xa::'a. pmf prob\<^sub>v xa = (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v' xb \<cdot> pmf (xx xb) xa)"
        assume a5: "\<forall>xa::'a.
          (\<exists>prob\<^sub>v::'a pmf.
              (\<lbrakk>q\<rbrakk>\<^sub>e xa \<longrightarrow> \<not> (\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (xa, x). pmf prob\<^sub>v x) = (1::real)) \<and>
              (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (xx xa) xb)) \<longrightarrow>
          \<not> (0::real) < pmf prob\<^sub>v' xa"
        let ?A = "{s'. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, s')}"
        let ?f = "\<lambda>x xa. pmf prob\<^sub>v' xa \<cdot> pmf (xx xa) x"
        from a5 have f1_0: "\<forall>xa::'a. (0::real) < pmf prob\<^sub>v' xa \<longrightarrow> 
            (\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (xa, x). pmf (xx xa) x) = (1::real)"
          by blast
        from a3 have f1_1: "\<forall>xa::'a. (0::real) < pmf prob\<^sub>v' xa \<longrightarrow> \<lbrakk>P\<rbrakk>\<^sub>e (more, xa)"
          using pmf_all_zero pmf_utp_comp0' by fastforce
        have f1_2: "\<forall>xa::'a. (0::real) < pmf prob\<^sub>v' xa \<longrightarrow> 
          {x. \<lbrakk>Q\<rbrakk>\<^sub>e (xa, x)} \<subseteq> ?A"
          using f1_1 by blast
        then have f1_3: "\<forall>xa::'a. (0::real) < pmf prob\<^sub>v' xa \<longrightarrow> 
            (\<Sum>x \<in> ?A. pmf (xx xa) x) \<ge> 
              (\<Sum>\<^sub>ax::'a | \<lbrakk>Q\<rbrakk>\<^sub>e (xa, x). pmf (xx xa) x)"
          by (metis (no_types, lifting) assms(1) boolean_algebra_class.sup_compl_top finite_Un 
                infsetsum_finite pmf_nonneg sum_mono2)
        then have f2: "\<forall>xa::'a. (0::real) < pmf prob\<^sub>v' xa \<longrightarrow> 
            (\<Sum>x \<in> ?A. pmf (xx xa) x) = 1"
          using f1_0
          by (smt assms(1) infsetsum_finite pmf_nonneg subset_UNIV sum_mono2 sum_pmf_eq_1)

        have f3: "(\<Sum>\<^sub>ax::'a | \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x). \<Sum>\<^sub>axa::'a. ?f x xa) = 
            (\<Sum>\<^sub>ax::'a | \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x). 
              \<Sum>\<^sub>axa::'a. if pmf prob\<^sub>v' xa > 0 then ?f x xa else 0)"
          by (smt infsetsum_cong mult_not_zero pmf_nonneg)
        also have f4: "... = 
            (\<Sum>\<^sub>ax \<in> {s'. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, s')}. 
            \<Sum>\<^sub>axa \<in> UNIV. if pmf prob\<^sub>v' xa > 0 then pmf prob\<^sub>v' xa \<cdot> pmf (xx xa) x else 0)"
          by blast
        also have f5: "... = 
            (\<Sum>x \<in> {s'. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, s')}. 
            \<Sum>xa \<in> UNIV. if pmf prob\<^sub>v' xa > 0 then pmf prob\<^sub>v' xa \<cdot> pmf (xx xa) x else 0)"
          using assms(1)
          by (metis (no_types, lifting) finite_subset infsetsum_finite subset_UNIV sum.cong)
        have f6: "... = (\<Sum>xa \<in> UNIV. \<Sum>x \<in> {s'. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, s')}. 
            if pmf prob\<^sub>v' xa > 0 then pmf prob\<^sub>v' xa \<cdot> pmf (xx xa) x else 0)"
          using assms(1) apply (subst sum.swap)
          by blast
        have f7: "... = (\<Sum>xa \<in> UNIV. if pmf prob\<^sub>v' xa > 0 then 
            (\<Sum>x \<in> {s'. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, s')}. pmf prob\<^sub>v' xa \<cdot> pmf (xx xa) x) else 0)"
          by (smt sum.cong sum.not_neutral_contains_not_neutral)
        have f8: "... = (\<Sum>xa \<in> UNIV. if pmf prob\<^sub>v' xa > 0 then 
            pmf prob\<^sub>v' xa \<cdot> (\<Sum>x \<in> {s'. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, s')}. pmf (xx xa) x) else 0)"
          by (metis (no_types) sum_distrib_left)
        have f9: "... = (\<Sum>xa \<in> UNIV. if pmf prob\<^sub>v' xa > 0 then pmf prob\<^sub>v' xa else 0)"
          using f2 by (metis (no_types, lifting) mult_cancel_left2)
        have f10: "... = (\<Sum>xa \<in> UNIV. pmf prob\<^sub>v' xa)"
          by (meson less_linear pmf_not_neg)
        then show "(\<Sum>\<^sub>ax::'a | \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x). 
            \<Sum>\<^sub>axa::'a. pmf prob\<^sub>v' xa \<cdot> pmf (xx xa) x) = (1::real)"
          by (smt assms(1) f3 f5 f6 f7 f8 f9 infsetsum_finite pmf_pos sum.cong sum_pmf_eq_1)
        (*
        have "has_bochner_integral (count_space UNIV) (\<lambda>x. pmf prob\<^sub>v' x \<cdot> pmf (xx x) xa) (pmf prob\<^sub>v xa)"
          apply (rule has_bochner_integral.intros[where s="\<lambda>_. (\<lambda>x. pmf prob\<^sub>v' x \<cdot> pmf (xx x) xa)"])
          apply simp
          apply (rule simple_bochner_integrable.intros)
        have "(\<Sum>\<^sub>ax::'a | \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x). 
            \<Sum>\<^sub>axa::'a. if pmf prob\<^sub>v' xa > 0 then pmf prob\<^sub>v' xa \<cdot> pmf (xx xa) x else 0) = 
          infsetsum (\<lambda>x. 
              (infsetsum 
                (\<lambda>xa. if pmf prob\<^sub>v' xa > 0 then pmf prob\<^sub>v' xa \<cdot> pmf (xx xa) x else 0) 
                UNIV)) 
              ({t. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, t)})"
          by (auto)
        from a4 have "\<forall>xa::'a. pmf prob\<^sub>v xa = infsetsum (?f xa) UNIV"
          by blast
        then have "\<forall>xa::'a. pmf prob\<^sub>v xa = lebesgue_integral (count_space UNIV) (?f xa)"
          by (simp add: infsetsum_def)
        then have "\<forall>xa. has_bochner_integral (count_space UNIV) (\<lambda>x. pmf prob\<^sub>v' x \<cdot> pmf (xx x) xa)
            (pmf prob\<^sub>v xa)" 
          apply (auto)
          apply (rule has_bochner_integral_integrable)
          sledgehammer*)
        (*have "\<And>x. x \<in> ?A \<Longrightarrow> ?f x abs_summable_on ?B"
          apply (smt abs_summable_on_cong not_summable_infsetsum_eq pmf_pos sum_pmf_eq_1) 
        proof -
          fix x::"'a"
          show "?f x abs_summable_on ?B"
            unfolding abs_summable_on_def integrable.simps has_bochner_integral.simps
            sledgehammer
          apply (simp add: Bochner_Integration.integrable_diff integrable.simps)*)
        (*
        have "(\<Sum>\<^sub>ax::'a | \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x). 
            \<Sum>\<^sub>axa::'a. pmf prob\<^sub>v' xa \<cdot> pmf (xx xa) x) = 
            (\<Sum>\<^sub>ax::'a | \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x). 
            \<Sum>\<^sub>axa::'a. if pmf prob\<^sub>v' xa > 0 then pmf prob\<^sub>v' xa \<cdot> pmf (xx xa) x else 0)
            "
          by (smt infsetsum_cong mult_not_zero pmf_nonneg)
        also have "... = 
            (\<Sum>\<^sub>ax \<in> {s'. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, s')}. 
            \<Sum>\<^sub>axa \<in> UNIV. if pmf prob\<^sub>v' xa > 0 then pmf prob\<^sub>v' xa \<cdot> pmf (xx xa) x else 0)"
          by blast
        also have "... = (\<Sum>\<^sub>axa \<in> UNIV. \<Sum>\<^sub>ax \<in> {s'. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, s')}. 
            if pmf prob\<^sub>v' xa > 0 then pmf prob\<^sub>v' xa \<cdot> pmf (xx xa) x else 0)"
          apply (rule sum_infsetsum[of "{s'. \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, s')}" 
                 "\<lambda>x xa. if pmf prob\<^sub>v' xa > 0 then pmf prob\<^sub>v' xa \<cdot> pmf (xx xa) x else 0" "UNIV"])
        *)
        (*
        have "(\<Sum>\<^sub>ax::'a | \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x). 
            \<Sum>\<^sub>axa::'a. pmf prob\<^sub>v' xa \<cdot> pmf (xx xa) x) = 
            (\<Sum>\<^sub>ax::'a | \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x). 
            \<Sum>\<^sub>axa \<in> ({t. (pmf prob\<^sub>v' t)=0}\<union>{t. (pmf prob\<^sub>v' t)>0}). pmf prob\<^sub>v' xa \<cdot> pmf (xx xa) x)
            "
          proof -
            { fix bb :: 'a
              have "\<forall>b. pmf prob\<^sub>v' b = 0 \<or> b \<in> {b. 0 < pmf prob\<^sub>v' b}"
                by force
              then have "(\<Sum>\<^sub>ab | \<exists>ba. \<lbrakk>P\<rbrakk>\<^sub>e (more, ba) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (ba, b). \<Sum>\<^sub>aba. pmf prob\<^sub>v' ba \<cdot> pmf (xx ba) b) = (\<Sum>\<^sub>ab | \<exists>ba. \<lbrakk>P\<rbrakk>\<^sub>e (more, ba) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (ba, b). \<Sum>\<^sub>aba\<in>{b. pmf prob\<^sub>v' b = 0} \<union> {b. 0 < pmf prob\<^sub>v' b}. pmf prob\<^sub>v' ba \<cdot> pmf (xx ba) b) \<or> (\<Sum>\<^sub>ab. pmf prob\<^sub>v' b \<cdot> pmf (xx b) bb) = (\<Sum>\<^sub>ab\<in>{b. pmf prob\<^sub>v' b = 0} \<union> {b. 0 < pmf prob\<^sub>v' b}. pmf prob\<^sub>v' b \<cdot> pmf (xx b) bb)"
                by (simp add: Un_def) }
            then show ?thesis
              by presburger
          qed
        also have "... = (\<Sum>\<^sub>ax::'a | \<exists>y::'a. \<lbrakk>P\<rbrakk>\<^sub>e (more, y) \<and> \<lbrakk>Q\<rbrakk>\<^sub>e (y, x). 
          ((\<Sum>\<^sub>axa \<in> ({t. (pmf prob\<^sub>v' t)=0}). pmf prob\<^sub>v' xa \<cdot> pmf (xx xa) x)
          + (\<Sum>\<^sub>axa \<in> ({t. (pmf prob\<^sub>v' t)>0}). pmf prob\<^sub>v' xa \<cdot> pmf (xx xa) x)))"
          unfolding infsetsum_altdef abs_summable_on_altdef
          apply (subst set_integral_Un, auto)
          proof -
            fix x :: 'a
            have "\<forall>B f fa Ba. (f abs_summable_on B \<or> \<not> fa abs_summable_on Ba) \<and> 
                  (fa abs_summable_on Ba \<or> \<not> f abs_summable_on B) \<or> \<not> B = Ba \<or> 
                  (\<exists>b. \<not> (f (b::'a)::real) = fa b \<and> b \<in> B)"
              by (metis (full_types) abs_summable_on_cong)
            then show "set_integrable (count_space UNIV) {b. pmf prob\<^sub>v' b = 0} (\<lambda>b. pmf prob\<^sub>v' b \<cdot> pmf (xx b) x)"
              using abs_summable_on_altdef by fastforce
          next
            fix x :: 'a
            have "\<forall>B f fa Ba. (f abs_summable_on B \<or> \<not> fa abs_summable_on Ba) \<and> 
                  (fa abs_summable_on Ba \<or> \<not> f abs_summable_on B) \<or> \<not> B = Ba \<or> 
                  (\<exists>b. \<not> (f (b::'a)::real) = fa b \<and> b \<in> B)"
              by (metis (full_types) abs_summable_on_cong)
            have "(\<lambda>b. pmf prob\<^sub>v' b \<cdot> pmf (xx b) x) abs_summable_on 
                  {t::'a. (0::real) < pmf prob\<^sub>v' t}"
              unfolding abs_summable_on_def sorry
            then show "set_integrable (count_space UNIV) {t::'a. (0::real) < pmf prob\<^sub>v' t} 
                      (\<lambda>b. pmf prob\<^sub>v' b \<cdot> pmf (xx b) x)"
              unfolding abs_summable_on_altdef by fastforce
          qed
        *)
      qed
    show ?thesis
        using p q seq_comp_ndesign by blast
  qed

(* It's not true
lemma pemb_kleisli_intchoice:
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "\<up> (P \<sqinter> Q) = (\<up> P) \<sqinter> (\<up> Q)" (is "?LHS = ?RHS")
proof -
  obtain pre\<^sub>p post\<^sub>p pre\<^sub>q post\<^sub>q
    where p:"P = (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p)" and 
          q:"Q = (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)"
    using assms by (metis ndesign_form)
  hence lhs: "?LHS = \<up> ((pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) \<sqinter> (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q))"
    by auto
  have rhs: "?RHS = ((\<up> (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) \<sqinter> \<up>(pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)))"
    by (simp add: p q)
  show ?thesis
    apply (simp add: lhs rhs)
    apply (ndes_simp)
    apply (simp add: kleisli_lift_alt_def kleisli_lift2'_def)
    apply (ndes_simp)
    apply (rule ndesign_eq_intro)
    apply (rel_auto)
*)

(*
(* For H, we haven't proved it yet *)
lemma kleisli_left_mono:
  assumes "P \<sqsubseteq> Q"
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  shows "\<up>P \<sqsubseteq> \<up>Q"
proof -
  obtain pre\<^sub>p post\<^sub>p pre\<^sub>q post\<^sub>q
    where p:"P = (pre\<^sub>p \<turnstile>\<^sub>r post\<^sub>p)" and 
          q:"Q = (pre\<^sub>q \<turnstile>\<^sub>r post\<^sub>q)" 
    using assms by (metis H1_H2_eq_rdesign Healthy_if)
  have f1: "\<lbrakk>\<lfloor>pre\<^sub>D P\<rfloor>\<^sub><\<rbrakk>\<^sub>p \<subseteq> \<lbrakk>\<lfloor>pre\<^sub>D Q\<rfloor>\<^sub><\<rbrakk>\<^sub>p"
    apply (simp add: upred_set.rep_eq)
    using assms
    by (smt Collect_mono arestr.rep_eq rdesign_ref_monos(1) upred_ref_iff)
  have f2: "`pre\<^sub>p \<Rightarrow> pre\<^sub>q`"
    using p q assms by (simp add: rdesign_refinement)
  have f2': "`pre\<^sub>p \<and> post\<^sub>q \<Rightarrow> post\<^sub>p`"
    using p q assms by (simp add: rdesign_refinement)
  have f4: "\<up>(pre\<^sub>p \<turnstile>\<^sub>r post\<^sub>p) \<sqsubseteq> \<up>(pre\<^sub>q \<turnstile>\<^sub>r post\<^sub>q)"
    apply (simp add: kleisli_lift_alt_def kleisli_lift2'_def)
    apply (simp add: ndesign_refinement)
    apply (auto)
    apply (pred_simp)
    using pmf_sum_subset_imp_1 apply (metis f1 fst_lens_def p q rdesign_pre)
    apply (rel_simp)
    proof -
      fix prob\<^sub>v::"'a pmf" and prob\<^sub>v'::"'a pmf" and x::"'a \<Rightarrow> 'a pmf"
      assume a1: "infsetsum (pmf prob\<^sub>v) \<lbrakk>pre\<^sub>p \<restriction>\<^sub>e \<lparr>lens_get = fst, lens_put = \<lambda>(\<sigma>::'a, \<rho>::'a prss) u::'a. (u, \<rho>)\<rparr>\<rbrakk>\<^sub>p = (1::real)"
      assume a2: "\<forall>xa::'a. pmf prob\<^sub>v' xa = (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v xb \<cdot> pmf (x xb) xa)"
      assume a3: " \<forall>xa::'a.
          (\<exists>prob\<^sub>v::'a pmf.
              (\<lbrakk>pre\<^sub>q\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>) \<longrightarrow> \<not> \<lbrakk>post\<^sub>q\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)) \<and>
              (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb)) \<longrightarrow>
          \<not> (0::real) < pmf prob\<^sub>v xa"
      show "\<exists>xa::'a \<Rightarrow> 'a pmf.
          (\<forall>xb::'a. (\<Sum>\<^sub>axa::'a. pmf prob\<^sub>v xa \<cdot> pmf (x xa) xb) = (\<Sum>\<^sub>ax::'a. pmf prob\<^sub>v x \<cdot> pmf (xa x) xb)) \<and>
          (\<forall>x::'a.
              (\<exists>prob\<^sub>v::'a pmf.
                  (\<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>e (x, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>) \<longrightarrow> \<not> \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (x, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)) \<and>
                  (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (xa x) xb)) \<longrightarrow>
              \<not> (0::real) < pmf prob\<^sub>v x)"
        apply (rule_tac x = "x" in exI, rule conjI)
        apply (metis a1 mem_Collect_eq order_less_irrefl pmf_all_zero pmf_utp_comp0' upred_set.rep_eq)
        apply (auto)
      proof -
        fix xa::"'a" and prob\<^sub>v'::"'a pmf"
        assume a11: "\<forall>xb::'a. pmf prob\<^sub>v' xb = pmf (x xa) xb"
        assume a12: "(0::real) < pmf prob\<^sub>v xa"
        assume a13: "\<not> \<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>)"
        have f11: "xa \<in> \<lbrakk>\<lfloor>pre\<^sub>p\<rfloor>\<^sub><\<rbrakk>\<^sub>p"
          using a1 a12 ComplI pmf_all_zero pmf_comp_set
          by (smt fst_lens_def p rdesign_pre)
        then have f12: "\<lbrakk>\<lfloor>pre\<^sub>p\<rfloor>\<^sub><\<rbrakk>\<^sub>e xa"
          by (simp add: upred_set_def)
        have f13: "\<not> \<lbrakk>\<lfloor>pre\<^sub>p\<rfloor>\<^sub><\<rbrakk>\<^sub>e xa"
          using a13 sledgehammer
        show "False"
          using f12 a13 apply (rel_auto)
          sledgehammer
        
        using a1 pmf_all_zero pmf_comp_set upred_set.rep_eq fst_lens_def alpha 
        proof -
          fix xa::"'a" and prob\<^sub>v'::"'a pmf"
          assume a11: "\<forall>xb::'a. pmf prob\<^sub>v' xb = pmf (x xa) xb"
          assume a12: "(0::real) < pmf prob\<^sub>v xa"
          assume a13: "\<not> \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>)"
          from a11 have f11: "prob\<^sub>v' = x xa"
            by (simp add: pmf_eqI)
          from a12 have f12: "\<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>e xa"
            using a3 by (smt Compl_iff a1 mem_Collect_eq pmf_all_zero pmf_comp_set upred_set.rep_eq)
          from f12 f2 have f13: "\<lbrakk>pre\<^sub>q\<rbrakk>\<^sub>e xa"
            using a12 a3 by blast
          have f14: "\<lbrakk>post\<^sub>q\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = x xa\<rparr>)"
            using a3 a12 by blast
          have f15: "\<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = x xa\<rparr>)"
            using f2' apply (rel_auto)
            by (simp add: f12 f14)
          show "False"
            using a13 f11 f15 by auto
        qed
      qed
  show ?thesis
      using f4 by (simp add: p q)
  qed
*)

(* \<up> is monotonic for normal designs *)
lemma kleisli_left_mono:
  assumes "P \<sqsubseteq> Q"
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "\<up>P \<sqsubseteq> \<up>Q"
proof -
  obtain pre\<^sub>p post\<^sub>p pre\<^sub>q post\<^sub>q
    where p:"P = (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p)" and 
          q:"Q = (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)" 
    using assms by (metis ndesign_form)
  have f1: "\<lbrakk>\<lfloor>pre\<^sub>D P\<rfloor>\<^sub><\<rbrakk>\<^sub>p \<subseteq> \<lbrakk>\<lfloor>pre\<^sub>D Q\<rfloor>\<^sub><\<rbrakk>\<^sub>p"
    apply (simp add: upred_set.rep_eq)
    using assms
    by (smt Collect_mono H1_H3_impl_H2 arestr.rep_eq rdesign_ref_monos(1) upred_ref_iff)
  have f2: "`pre\<^sub>p \<Rightarrow> pre\<^sub>q`"
    using p q assms by (simp add: ndesign_refinement')
  have f2': "post\<^sub>p \<sqsubseteq> ?[pre\<^sub>p] ;; post\<^sub>q"
    using p q assms by (simp add: ndesign_refinement')
  have f3: "\<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>p \<subseteq> \<lbrakk>pre\<^sub>q\<rbrakk>\<^sub>p"
    apply (simp add: upred_set.rep_eq)
    apply (rule Collect_mono)
    using assms by (meson f2 impl.rep_eq taut.rep_eq)
  have f4: "\<up>(pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) \<sqsubseteq> \<up>(pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)"
    apply (simp add: kleisli_lift_alt_def kleisli_lift2'_def)
    apply (simp add: ndesign_refinement)
    apply (auto)
    apply (pred_simp)
    using f3 pmf_sum_subset_imp_1 apply blast
    apply (rel_simp)
    proof -
      fix prob\<^sub>v::"'a pmf" and prob\<^sub>v'::"'a pmf" and x::"'a \<Rightarrow> 'a pmf"
      assume a1: "infsetsum (pmf prob\<^sub>v) \<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>p = (1::real)"
      assume a2: "\<forall>xa::'a. pmf prob\<^sub>v' xa = (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v xb \<cdot> pmf (x xb) xa)"
      assume a3: "\<forall>xa::'a.
            (\<exists>prob\<^sub>v::'a pmf.
                (\<lbrakk>pre\<^sub>q\<rbrakk>\<^sub>e xa \<longrightarrow> \<not> \<lbrakk>post\<^sub>q\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)) \<and>
                (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb)) \<longrightarrow>
            \<not> (0::real) < pmf prob\<^sub>v xa"
      show "\<exists>xa::'a \<Rightarrow> 'a pmf.
            (\<forall>xb::'a. (\<Sum>\<^sub>axa::'a. pmf prob\<^sub>v xa \<cdot> pmf (x xa) xb) = (\<Sum>\<^sub>ax::'a. pmf prob\<^sub>v x \<cdot> pmf (xa x) xb)) \<and>
            (\<forall>x::'a.
                (\<exists>prob\<^sub>v::'a pmf.
                    (\<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>e x \<longrightarrow> \<not> \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (x, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)) \<and>
                    (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (xa x) xb)) \<longrightarrow>
                \<not> (0::real) < pmf prob\<^sub>v x)"
        apply (rule_tac x = "x" in exI, rule conjI)
        apply (metis a1 mem_Collect_eq order_less_irrefl pmf_all_zero pmf_utp_comp0' upred_set.rep_eq)
        apply (auto)
        using a1 pmf_all_zero pmf_comp_set upred_set.rep_eq apply fastforce
        proof -
          fix xa::"'a" and prob\<^sub>v'::"'a pmf"
          assume a11: "\<forall>xb::'a. pmf prob\<^sub>v' xb = pmf (x xa) xb"
          assume a12: "(0::real) < pmf prob\<^sub>v xa"
          assume a13: "\<not> \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>)"
          from a11 have f11: "prob\<^sub>v' = x xa"
            by (simp add: pmf_eqI)
          from a12 have f12: "\<lbrakk>pre\<^sub>p\<rbrakk>\<^sub>e xa"
            using a3 by (smt Compl_iff a1 mem_Collect_eq pmf_all_zero pmf_comp_set upred_set.rep_eq)
          from f12 f2 have f13: "\<lbrakk>pre\<^sub>q\<rbrakk>\<^sub>e xa"
            using a12 a3 by blast
          have f14: "\<lbrakk>post\<^sub>q\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = x xa\<rparr>)"
            using a3 a12 by blast
          have f15: "\<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = x xa\<rparr>)"
            using f2' apply (rel_auto)
            by (simp add: f12 f14)
          show "False"
            using a13 f11 f15 by auto
        qed
      qed
  show ?thesis
      using f4 by (simp add: p q)
qed

(*
lemma kleisli_left_mono':
  assumes "P \<sqsubseteq> Q"
  shows "\<up>P \<sqsubseteq> \<up>Q"
proof -
  have f1: "`pre\<^sub>D(P) \<Rightarrow> pre\<^sub>D(Q)`"
    using assms by (simp add: design_refine_thms)
  have f2: "`pre\<^sub>D(P) \<and> post\<^sub>D(Q) \<Rightarrow> post\<^sub>D(P)`"
    using assms by (simp add: design_refine_thms)
  have f3: "\<up>P \<sqsubseteq> \<up>Q"
    apply (simp add: kleisli_lift_alt_def kleisli_lift2'_def)
    apply (simp add: ndesign_refinement)
    apply (auto)
    apply (pred_simp)
    using assms 
    apply (smt Collect_mono arestr.rep_eq lit.rep_eq pmf_sum_subset_imp_1 subst.rep_eq 
      uexpr_appl.rep_eq upred_ref_iff upred_set.rep_eq)
    apply (simp add: upred_set_def )
    apply (pred_simp)
    proof -
      fix prob\<^sub>v'::"'a pmf" and prob\<^sub>v''::"'a pmf" and x::"'a \<Rightarrow> 'a pmf"
      assume a1: "infsetsum (pmf prob\<^sub>v')
        {b::'a.
         \<not> \<lbrakk>P\<rbrakk>\<^sub>e (fst src\<^bsub>\<lparr>lens_get = map_prod des_vars.more des_vars.more, lens_put = \<lambda>(u::'a des, v::'a prss des) (x::'a, y::'a prss). (u\<lparr>des_vars.more := x\<rparr>, v\<lparr>des_vars.more := y\<rparr>)\<rparr>\<^esub>
                  \<lparr>des_vars.more := b, ok\<^sub>v := True\<rparr>,
                  snd src\<^bsub>\<lparr>lens_get = map_prod des_vars.more des_vars.more, lens_put = \<lambda>(u::'a des, v::'a prss des) (x::'a, y::'a prss). (u\<lparr>des_vars.more := x\<rparr>, v\<lparr>des_vars.more := y\<rparr>)\<rparr>\<^esub>
                  \<lparr>des_vars.more := snd src\<^bsub>\<lparr>lens_get = fst, lens_put = \<lambda>(\<sigma>::'a, \<rho>::'a prss) u::'a. (u, \<rho>)\<rparr>\<^esub>,
                     ok\<^sub>v := False\<rparr>)} =
       (1::real)"
      assume a2: "\<forall>xa::'a. pmf prob\<^sub>v'' xa = (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v' xb \<cdot> pmf (x xb) xa)"
      assume a3: "\<forall>xa::'a.
          \<not> (\<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>, \<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>)
             \<in> {p::'a prss \<times> 'a. (0::real) < pmf (prob\<^sub>v (fst p)) (snd p) \<and> snd p = xa} O
                {p::'a \<times> 'a prss.
                 \<lbrakk>Q\<rbrakk>\<^sub>e
                  (fst src\<^bsub>\<lparr>lens_get = map_prod des_vars.more des_vars.more, lens_put = \<lambda>(u::'a des, v::'a prss des) (x::'a, y::'a prss). (u\<lparr>des_vars.more := x\<rparr>, v\<lparr>des_vars.more := y\<rparr>)\<rparr>\<^esub>
                   \<lparr>des_vars.more := fst p, ok\<^sub>v := True\<rparr>,
                   snd src\<^bsub>\<lparr>lens_get = map_prod des_vars.more des_vars.more, lens_put = \<lambda>(u::'a des, v::'a prss des) (x::'a, y::'a prss). (u\<lparr>des_vars.more := x\<rparr>, v\<lparr>des_vars.more := y\<rparr>)\<rparr>\<^esub>
                   \<lparr>des_vars.more := snd p, ok\<^sub>v := False\<rparr>) \<or>
                 \<not> \<lbrakk>Q\<rbrakk>\<^sub>e (fst src\<^bsub>\<lparr>lens_get = map_prod des_vars.more des_vars.more, lens_put = \<lambda>(u::'a des, v::'a prss des) (x::'a, y::'a prss). (u\<lparr>des_vars.more := x\<rparr>, v\<lparr>des_vars.more := y\<rparr>)\<rparr>\<^esub>
                          \<lparr>des_vars.more := fst p, ok\<^sub>v := True\<rparr>,
                          snd src\<^bsub>\<lparr>lens_get = map_prod des_vars.more des_vars.more, lens_put = \<lambda>(u::'a des, v::'a prss des) (x::'a, y::'a prss). (u\<lparr>des_vars.more := x\<rparr>, v\<lparr>des_vars.more := y\<rparr>)\<rparr>\<^esub>
                          \<lparr>des_vars.more := snd p, ok\<^sub>v := True\<rparr>)} O
                {q::'a prss \<times> 'a prss. \<forall>xb::'a. pmf (prob\<^sub>v (fst q)) xb = pmf (x xa) xb}"
      show "\<exists>xa::'a \<Rightarrow> 'a pmf.
          (\<forall>xb::'a.
              (\<Sum>\<^sub>axa::'a. pmf prob\<^sub>v' xa \<cdot> pmf (x xa) xb) = (\<Sum>\<^sub>ax::'a. pmf prob\<^sub>v' x \<cdot> pmf (xa x) xb)) \<and>
          (\<forall>x::'a.
              \<not> (\<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>, \<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>)
                 \<in> {p::'a prss \<times> 'a. (0::real) < pmf (prob\<^sub>v (fst p)) (snd p) \<and> snd p = x} O
                    {p::'a \<times> 'a prss.
                     \<lbrakk>P\<rbrakk>\<^sub>e
                      (fst src\<^bsub>\<lparr>lens_get = map_prod des_vars.more des_vars.more, lens_put = \<lambda>(u::'a des, v::'a prss des) (x::'a, y::'a prss). (u\<lparr>des_vars.more := x\<rparr>, v\<lparr>des_vars.more := y\<rparr>)\<rparr>\<^esub>
                       \<lparr>des_vars.more := fst p, ok\<^sub>v := True\<rparr>,
                       snd src\<^bsub>\<lparr>lens_get = map_prod des_vars.more des_vars.more, lens_put = \<lambda>(u::'a des, v::'a prss des) (x::'a, y::'a prss). (u\<lparr>des_vars.more := x\<rparr>, v\<lparr>des_vars.more := y\<rparr>)\<rparr>\<^esub>
                       \<lparr>des_vars.more := snd p, ok\<^sub>v := False\<rparr>) \<or>
                     \<not> \<lbrakk>P\<rbrakk>\<^sub>e (fst src\<^bsub>\<lparr>lens_get = map_prod des_vars.more des_vars.more, lens_put = \<lambda>(u::'a des, v::'a prss des) (x::'a, y::'a prss). (u\<lparr>des_vars.more := x\<rparr>, v\<lparr>des_vars.more := y\<rparr>)\<rparr>\<^esub>
                              \<lparr>des_vars.more := fst p, ok\<^sub>v := True\<rparr>,
                              snd src\<^bsub>\<lparr>lens_get = map_prod des_vars.more des_vars.more, lens_put = \<lambda>(u::'a des, v::'a prss des) (x::'a, y::'a prss). (u\<lparr>des_vars.more := x\<rparr>, v\<lparr>des_vars.more := y\<rparr>)\<rparr>\<^esub>
                              \<lparr>des_vars.more := snd p, ok\<^sub>v := True\<rparr>)} O
                    {q::'a prss \<times> 'a prss. \<forall>xb::'a. pmf (prob\<^sub>v (fst q)) xb = pmf (xa x) xb})"
        apply (rule_tac x = "x" in exI, rule conjI)
        apply (metis a1 mem_Collect_eq order_less_irrefl pmf_all_zero pmf_utp_comp0' upred_set.rep_eq)
        apply (clarsimp)
        apply (auto)
        proof -
          fix xb::"'a" and ya::"'a prss"
          assume a11: "\<forall>xba::'a. pmf (prob\<^sub>v ya) xba = pmf (x xb) xba"
          assume a12: "(0::real) < pmf prob\<^sub>v' xb"
          assume a13: "\<lbrakk>P\<rbrakk>\<^sub>e
            (fst src\<^bsub>\<lparr>lens_get = map_prod des_vars.more des_vars.more, lens_put = \<lambda>(u::'a des, v::'a prss des) (x::'a, y::'a prss). (u\<lparr>des_vars.more := x\<rparr>, v\<lparr>des_vars.more := y\<rparr>)\<rparr>\<^esub>
             \<lparr>des_vars.more := xb, ok\<^sub>v := True\<rparr>,
             snd src\<^bsub>\<lparr>lens_get = map_prod des_vars.more des_vars.more, lens_put = \<lambda>(u::'a des, v::'a prss des) (x::'a, y::'a prss). (u\<lparr>des_vars.more := x\<rparr>, v\<lparr>des_vars.more := y\<rparr>)\<rparr>\<^esub>
             \<lparr>des_vars.more := ya, ok\<^sub>v := False\<rparr>)"
          from a12 have f11: "xb \<in> {b::'a.
            \<not> \<lbrakk>P\<rbrakk>\<^sub>e (fst src\<^bsub>\<lparr>lens_get = map_prod des_vars.more des_vars.more, lens_put = \<lambda>(u::'a des, v::'a prss des) (x::'a, y::'a prss). (u\<lparr>des_vars.more := x\<rparr>, v\<lparr>des_vars.more := y\<rparr>)\<rparr>\<^esub>
                  \<lparr>des_vars.more := b, ok\<^sub>v := True\<rparr>,
                  snd src\<^bsub>\<lparr>lens_get = map_prod des_vars.more des_vars.more, lens_put = \<lambda>(u::'a des, v::'a prss des) (x::'a, y::'a prss). (u\<lparr>des_vars.more := x\<rparr>, v\<lparr>des_vars.more := y\<rparr>)\<rparr>\<^esub>
                  \<lparr>des_vars.more := snd src\<^bsub>\<lparr>lens_get = fst, lens_put = \<lambda>(\<sigma>::'a, \<rho>::'a prss) u::'a. (u, \<rho>)\<rparr>\<^esub>,
                     ok\<^sub>v := False\<rparr>)}"
            using a1 pmf_all_zero pmf_utp_comp0' by fastforce
          have f12: "\<not> \<lbrakk>P\<rbrakk>\<^sub>e (fst src\<^bsub>\<lparr>lens_get = map_prod des_vars.more des_vars.more, lens_put = \<lambda>(u::'a des, v::'a prss des) (x::'a, y::'a prss). (u\<lparr>des_vars.more := x\<rparr>, v\<lparr>des_vars.more := y\<rparr>)\<rparr>\<^esub>
                  \<lparr>des_vars.more := xb, ok\<^sub>v := True\<rparr>,
                  snd src\<^bsub>\<lparr>lens_get = map_prod des_vars.more des_vars.more, lens_put = \<lambda>(u::'a des, v::'a prss des) (x::'a, y::'a prss). (u\<lparr>des_vars.more := x\<rparr>, v\<lparr>des_vars.more := y\<rparr>)\<rparr>\<^esub>
                  \<lparr>des_vars.more := snd src\<^bsub>\<lparr>lens_get = fst, lens_put = \<lambda>(\<sigma>::'a, \<rho>::'a prss) u::'a. (u, \<rho>)\<rparr>\<^esub>,
                     ok\<^sub>v := False\<rparr>)"
            using f11 by blast
          show "False"
            using f12 a13 sorry
        next
          fix xb::"'a" and ya::"'a prss"
          assume a11: "\<forall>xba::'a. pmf (prob\<^sub>v ya) xba = pmf (x xb) xba"
          assume a12: "(0::real) < pmf prob\<^sub>v' xb"
          assume a13: "\<not> \<lbrakk>P\<rbrakk>\<^sub>e (fst src\<^bsub>\<lparr>lens_get = map_prod des_vars.more des_vars.more, lens_put = \<lambda>(u::'a des, v::'a prss des) (x::'a, y::'a prss). (u\<lparr>des_vars.more := x\<rparr>, v\<lparr>des_vars.more := y\<rparr>)\<rparr>\<^esub>
                \<lparr>des_vars.more := xb, ok\<^sub>v := True\<rparr>,
                snd src\<^bsub>\<lparr>lens_get = map_prod des_vars.more des_vars.more, lens_put = \<lambda>(u::'a des, v::'a prss des) (x::'a, y::'a prss). (u\<lparr>des_vars.more := x\<rparr>, v\<lparr>des_vars.more := y\<rparr>)\<rparr>\<^esub>
                \<lparr>des_vars.more := ya, ok\<^sub>v := True\<rparr>)"
          show "False"
            sorry
        qed
      qed
  show ?thesis
      using f3 by (simp)
qed
*)

(* For all normal designs, it is monotonic *)
lemma kleisli_left_monotonic:
  assumes "\<forall>x. P x is \<^bold>N"
  assumes "mono P"
  shows "mono (\<lambda>X. \<up>(P X))"
  apply (simp add: mono_def, auto)
  proof -
    fix x::"'a" and y::"'a"
    assume a1: "x \<le> y"
    show "\<up> (P y) \<sqsubseteq> \<up> (P x)"
      apply (subst kleisli_left_mono)
      using a1 assms(2) apply (simp add: monoD)
      using assms(1) by blast+
  qed

lemma kleisli_left_H:
  assumes "P is \<^bold>H"
  shows "\<up>P is \<^bold>H"
  by (simp add: kleisli_lift2'_def kleisli_lift_alt_def ndesign_def rdesign_is_H1_H2)

lemma kleisli_left_N:
  assumes "P is \<^bold>N"
  shows "\<up>P is \<^bold>N"
  apply (simp add: kleisli_lift2'_def kleisli_lift_alt_def)
  using ndesign_H1_H3 by blast

subsubsection \<open> Recursion\<close>
  (* Recursion is the weakest fix point *)
(*
(* \<H> is a healthiness condition *)
term "utp_lfp \<equiv> LEAST_FP (utp_order \<H>)"

lemma mu_id: "(\<mu>\<^sub>D X \<bullet> X) = true\<^sub>D"
  apply (simp add: lfp_def gfp_upperbound lfp_lowerbound)
*)

subsection \<open> Conditional Choice \<close>

declare [[show_types]]

lemma cond_idem:
  fixes P::"'s hrel_pdes"
  shows "P \<triangleleft> b \<triangleright>\<^sub>D P = P"
  by auto

lemma cond_inf_distr:
  fixes P::"'s hrel_pdes" and Q::"'s hrel_pdes" and R::"'s hrel_pdes"
  shows "P \<sqinter> (Q \<triangleleft> b \<triangleright>\<^sub>D R) = (P \<sqinter> Q) \<triangleleft> b \<triangleright>\<^sub>D (P \<sqinter> R)"
  by (rel_auto)
  
subsection \<open> Probabilistic Choice \<close>
(*
lemma prob_choice_idem':
  assumes "r \<in> {0..1}"
  shows "p \<turnstile>\<^sub>n R is \<^bold>C\<^bold>C \<Longrightarrow> ((p \<turnstile>\<^sub>n R) \<oplus>\<^bsub>r\<^esub> (p \<turnstile>\<^sub>n R) = p \<turnstile>\<^sub>n R)"
  apply (simp add: Healthy_def Convex_Closed_eq)
  (*apply (ndes_simp cls: assms)
  apply (simp add: upred_defs)*)
proof (cases "r \<in> {0<..<1}")
  case True
  have t1: "((p \<turnstile>\<^sub>n R) \<oplus>\<^bsub>r\<^esub> (p \<turnstile>\<^sub>n R) = (p \<turnstile>\<^sub>n R) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> (p \<turnstile>\<^sub>n R))"
    using True prob_choice_r prob_choice_def 
    by blast
  show "(\<Sqinter> r::real \<in> {0::real<..<1::real} \<bullet> (p \<turnstile>\<^sub>n R) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> (p \<turnstile>\<^sub>n R)) \<sqinter> (p \<turnstile>\<^sub>n R) = p \<turnstile>\<^sub>n R \<Longrightarrow>
    (p \<turnstile>\<^sub>n R) \<oplus>\<^bsub>r\<^esub> (p \<turnstile>\<^sub>n R) = p \<turnstile>\<^sub>n R" 
    apply (simp add: t1)
    apply (ndes_simp cls: assms)
    apply (simp add: upred_defs)
    apply (rel_auto)
    proof -
      fix ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and prob\<^sub>v'::"'a pmf" and prob\<^sub>v''::"'a pmf"
      assume a1: "\<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>)"
      assume a2: "\<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>)"
      assume a3: "ok\<^sub>v"
      assume a4: "ok\<^sub>v'"
      assume a5: "\<lbrakk>p\<rbrakk>\<^sub>e more"
      assume a0: "\<forall>(ok\<^sub>v::bool) (more::'a) (ok\<^sub>v'::bool) prob\<^sub>v::'a pmf.
          (ok\<^sub>v \<and> (\<lbrakk>p\<rbrakk>\<^sub>e more \<or> (\<forall>x>0::real. \<not> x < (1::real))) \<and> \<lbrakk>p\<rbrakk>\<^sub>e more \<longrightarrow>
           ok\<^sub>v' \<and>
           ((\<exists>x::real.
                (\<exists>(mrg_prior\<^sub>v::'a) prob\<^sub>v'::'a pmf.
                    \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>) \<and>
                    (\<exists>prob\<^sub>v''::'a pmf.
                        \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>) \<and>
                        mrg_prior\<^sub>v = more \<and> prob\<^sub>v = prob\<^sub>v' +\<^bsub>x\<^esub> prob\<^sub>v'')) \<and>
                (0::real) < x \<and> x < (1::real)) \<or>
            \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>))) =
          (ok\<^sub>v \<and> \<lbrakk>p\<rbrakk>\<^sub>e more \<longrightarrow> ok\<^sub>v' \<and> \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>))"
      from a0 have t11: "\<forall> (more::'a) (ok\<^sub>v'::bool) prob\<^sub>v::'a pmf.
          (ok\<^sub>v \<and> (\<lbrakk>p\<rbrakk>\<^sub>e more \<or> (\<forall>x>0::real. \<not> x < (1::real))) \<and> \<lbrakk>p\<rbrakk>\<^sub>e more \<longrightarrow>
           ok\<^sub>v' \<and>
           ((\<exists>x::real.
                (\<exists>(mrg_prior\<^sub>v::'a) prob\<^sub>v'::'a pmf.
                    \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>) \<and>
                    (\<exists>prob\<^sub>v''::'a pmf.
                        \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>) \<and>
                        mrg_prior\<^sub>v = more \<and> prob\<^sub>v = prob\<^sub>v' +\<^bsub>x\<^esub> prob\<^sub>v'')) \<and>
                (0::real) < x \<and> x < (1::real)) \<or>
            \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>))) =
          (ok\<^sub>v \<and> \<lbrakk>p\<rbrakk>\<^sub>e more \<longrightarrow> ok\<^sub>v' \<and> \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>))"
        by (rule spec)
      then have t12: "\<forall>(ok\<^sub>v'::bool) prob\<^sub>v::'a pmf.
          (ok\<^sub>v \<and> (\<lbrakk>p\<rbrakk>\<^sub>e more \<or> (\<forall>x>0::real. \<not> x < (1::real))) \<and> \<lbrakk>p\<rbrakk>\<^sub>e more \<longrightarrow>
           ok\<^sub>v' \<and>
           ((\<exists>x::real.
                (\<exists>(mrg_prior\<^sub>v::'a) prob\<^sub>v'::'a pmf.
                    \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>) \<and>
                    (\<exists>prob\<^sub>v''::'a pmf.
                        \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>) \<and>
                        mrg_prior\<^sub>v = more \<and> prob\<^sub>v = prob\<^sub>v' +\<^bsub>x\<^esub> prob\<^sub>v'')) \<and>
                (0::real) < x \<and> x < (1::real)) \<or>
            \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>))) =
          (ok\<^sub>v \<and> \<lbrakk>p\<rbrakk>\<^sub>e more \<longrightarrow> ok\<^sub>v' \<and> \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>))"
        by (rule spec)
      then have t13: "\<forall> prob\<^sub>v::'a pmf.
          (ok\<^sub>v \<and> (\<lbrakk>p\<rbrakk>\<^sub>e more \<or> (\<forall>x>0::real. \<not> x < (1::real))) \<and> \<lbrakk>p\<rbrakk>\<^sub>e more \<longrightarrow>
           ok\<^sub>v' \<and>
           ((\<exists>x::real.
                (\<exists>(mrg_prior\<^sub>v::'a) prob\<^sub>v'::'a pmf.
                    \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>) \<and>
                    (\<exists>prob\<^sub>v''::'a pmf.
                        \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>) \<and>
                        mrg_prior\<^sub>v = more \<and> prob\<^sub>v = prob\<^sub>v' +\<^bsub>x\<^esub> prob\<^sub>v'')) \<and>
                (0::real) < x \<and> x < (1::real)) \<or>
            \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>))) =
          (ok\<^sub>v \<and> \<lbrakk>p\<rbrakk>\<^sub>e more \<longrightarrow> ok\<^sub>v' \<and> \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>))"
        by (rule spec)
      then have t14: "
          (ok\<^sub>v \<and> (\<lbrakk>p\<rbrakk>\<^sub>e more \<or> (\<forall>x>0::real. \<not> x < (1::real))) \<and> \<lbrakk>p\<rbrakk>\<^sub>e more \<longrightarrow>
           ok\<^sub>v' \<and>
           ((\<exists>x::real.
                (\<exists>(mrg_prior\<^sub>v::'a) prob\<^sub>v'''::'a pmf.
                    \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v'''\<rparr>) \<and>
                    (\<exists>prob\<^sub>v''''::'a pmf.
                        \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v''''\<rparr>) \<and>
                        mrg_prior\<^sub>v = more \<and> prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v'' = prob\<^sub>v''' +\<^bsub>x\<^esub> prob\<^sub>v'''')) \<and>
                (0::real) < x \<and> x < (1::real)) \<or>
            \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v''\<rparr>))) =
          (ok\<^sub>v \<and> \<lbrakk>p\<rbrakk>\<^sub>e more \<longrightarrow> ok\<^sub>v' \<and> \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v''\<rparr>))"
        apply (drule_tac x = "prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v''" in spec)
        by blast
      then have t15: "((\<exists>x::real.
                (\<exists>(mrg_prior\<^sub>v::'a) prob\<^sub>v'''::'a pmf.
                    \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v'''\<rparr>) \<and>
                    (\<exists>prob\<^sub>v''''::'a pmf.
                        \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v''''\<rparr>) \<and>
                        mrg_prior\<^sub>v = more \<and> prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v'' = prob\<^sub>v''' +\<^bsub>x\<^esub> prob\<^sub>v'''')) \<and>
                (0::real) < x \<and> x < (1::real)) \<or>
            \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v''\<rparr>))
        = \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v''\<rparr>)"
        using a3 a4 a5 by blast
      show "\<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v''\<rparr>)"
        using True a1 a2 greaterThanLessThan_iff t15 by blast
    next
      fix ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and prob\<^sub>v::"'a pmf"
      assume a0: "\<forall>(ok\<^sub>v::bool) (more::'a) (ok\<^sub>v'::bool) prob\<^sub>v::'a pmf.
          (ok\<^sub>v \<and> (\<lbrakk>p\<rbrakk>\<^sub>e more \<or> (\<forall>x>0::real. \<not> x < (1::real))) \<and> \<lbrakk>p\<rbrakk>\<^sub>e more \<longrightarrow>
           ok\<^sub>v' \<and>
           ((\<exists>x::real.
                (\<exists>(mrg_prior\<^sub>v::'a) prob\<^sub>v'::'a pmf.
                    \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>) \<and>
                    (\<exists>prob\<^sub>v''::'a pmf.
                        \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>) \<and>
                        mrg_prior\<^sub>v = more \<and> prob\<^sub>v = prob\<^sub>v' +\<^bsub>x\<^esub> prob\<^sub>v'')) \<and>
                (0::real) < x \<and> x < (1::real)) \<or>
            \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>))) =
          (ok\<^sub>v \<and> \<lbrakk>p\<rbrakk>\<^sub>e more \<longrightarrow> ok\<^sub>v' \<and> \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>))"
      assume a1: "\<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)"
      assume a2: "ok\<^sub>v"
      assume a3: "ok\<^sub>v'"
      assume a4: "\<lbrakk>p\<rbrakk>\<^sub>e more"
      show "\<exists>mrg_prior\<^sub>v prob\<^sub>v'.
            \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>) \<and>
            (\<exists>prob\<^sub>v''. \<lbrakk>R\<rbrakk>\<^sub>e (more, \<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>) \<and> mrg_prior\<^sub>v = more \<and> prob\<^sub>v = prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v'')"
        apply (rule_tac x = "more" in exI)
        apply (rule_tac x = "prob\<^sub>v" in exI)
        apply (rule_tac conjI)
        using a1 apply (simp)
        apply (rule_tac x = "prob\<^sub>v" in exI)
        apply (rule_tac conjI)
        using a1 apply (simp)
        apply (simp)
        by (metis assms(1) wplus_idem)
    qed
next
  case False
  have f1: "r = 0 \<or> r = 1"
    using False assms by auto
  then show ?thesis 
    using f1 prob_choice_one prob_choice_zero by auto 
qed

lemma prob_choice_idem: 
  assumes "r \<in> {0..1}" "P is \<^bold>N" "P is \<^bold>C\<^bold>C"
  shows "(P \<oplus>\<^bsub>r\<^esub> P = P)"
  proof -
    have 1: "P = (\<lfloor>pre\<^sub>D(P)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P))"
      using assms(2) by (simp add: ndesign_form)
    then have 2: " (\<lfloor>pre\<^sub>D(P)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P)) is \<^bold>C\<^bold>C"
      using assms(3) by (simp)
    then have 3: "((\<lfloor>pre\<^sub>D(P)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P)) \<oplus>\<^bsub>r\<^esub> (\<lfloor>pre\<^sub>D(P)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P)) = (\<lfloor>pre\<^sub>D(P)\<rfloor>\<^sub>< \<turnstile>\<^sub>n post\<^sub>D(P)))"
      using assms(1) by (simp add: prob_choice_idem')
    show ?thesis
      using "1" "3" by auto
  qed
*)
lemma prob_choice_inf_distr:
  assumes "r \<in> {0..1}" "P is \<^bold>N"  "Q is \<^bold>N" "R is \<^bold>N" 
  shows "(P \<sqinter> Q) \<oplus>\<^bsub>r\<^esub> R = ((P \<oplus>\<^bsub>r\<^esub> R) \<sqinter> (Q \<oplus>\<^bsub>r\<^esub> R))" (is "?LHS = ?RHS")
proof -
  obtain pre\<^sub>p post\<^sub>p pre\<^sub>q post\<^sub>q pre\<^sub>r post\<^sub>r
    where p:"P = (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p)" and 
          q:"Q = (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)" and 
          r:"R = (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)"
    using assms by (metis ndesign_form)
  hence lhs: "?LHS = ((pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) \<sqinter> (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)) \<oplus>\<^bsub>r\<^esub> (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)"
    by auto
  have rhs: "?RHS = (((pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) \<oplus>\<^bsub>r\<^esub> (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)) \<sqinter> ((pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q) \<oplus>\<^bsub>r\<^esub> (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)))"
    by (simp add: p q r)
  show ?thesis
    apply (simp add: p q r lhs rhs prob_choice_def)
    apply (ndes_simp cls: assms)
    apply (rel_auto)
    apply auto[1]
    by auto
qed
  
lemma prob_choice_inf_distl:
  assumes "r \<in> {0..1}" "P is \<^bold>N" "Q is \<^bold>N" "R is \<^bold>N"
  shows "P \<oplus>\<^bsub>r\<^esub> (Q \<sqinter> R)  = ((P \<oplus>\<^bsub>r\<^esub> Q) \<sqinter> (P \<oplus>\<^bsub>r\<^esub> R))" (is "?LHS = ?RHS")
proof -
  obtain pre\<^sub>p post\<^sub>p pre\<^sub>q post\<^sub>q pre\<^sub>r post\<^sub>r
    where p:"P = (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p)" and 
          q:"Q = (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)" and 
          r:"R = (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)"
    using assms by (metis ndesign_form)
  hence lhs: "?LHS = ((pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p)) \<oplus>\<^bsub>r\<^esub> ( (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q) \<sqinter> (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r))"
    by auto
  have rhs: "?RHS = (((pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) \<oplus>\<^bsub>r\<^esub> (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)) \<sqinter> ((pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) \<oplus>\<^bsub>r\<^esub> (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)))"
    by (simp add: p q r)
  show ?thesis
    apply (simp add: p q r lhs rhs prob_choice_def)
    apply (ndes_simp cls: assms)
    apply (rel_auto)
    apply auto[1]
    by auto
qed

lemma prob_choice_assoc:
  assumes "w\<^sub>1 \<in> {0..1}" "w\<^sub>2 \<in> {0..1}"
          "(1-w\<^sub>1)*(1-w\<^sub>2)=(1-r\<^sub>2)" "w\<^sub>1=r\<^sub>1*r\<^sub>2"
          "P is \<^bold>N" "Q is \<^bold>N" "R is \<^bold>N"
  shows  "(P \<oplus>\<^bsub>w\<^sub>1\<^esub> (Q \<oplus>\<^bsub>w\<^sub>2\<^esub> R)) = ((P \<oplus>\<^bsub>r\<^sub>1\<^esub> Q) \<oplus>\<^bsub>r\<^sub>2\<^esub> R)" (is "?LHS = ?RHS")
proof -
  obtain pre\<^sub>p post\<^sub>p pre\<^sub>q post\<^sub>q pre\<^sub>r post\<^sub>r
    where p:"P = (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p)" and 
          q:"Q = (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)" and 
          r:"R = (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)"
    using assms by (metis ndesign_form)
  hence rhs: "?RHS = ((pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) \<oplus>\<^bsub>r\<^sub>1\<^esub> (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)) \<oplus>\<^bsub>r\<^sub>2\<^esub> (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)"
    by auto
  have lhs: "?LHS = (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) \<oplus>\<^bsub>w\<^sub>1\<^esub> ((pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q) \<oplus>\<^bsub>w\<^sub>2\<^esub> (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r))"
    by (simp add: p q r)
  show ?thesis
    proof (cases "w\<^sub>1 = 0 \<or> w\<^sub>1 = 1 \<or> w\<^sub>2 = 0 \<or> w\<^sub>2 = 1")
      case True
      then show ?thesis 
      proof (cases "w\<^sub>1 = 0 \<or> w\<^sub>1 = 1")
        case True
        then show ?thesis 
          using True prob_choice_one prob_choice_zero assms(3-4)
          by (smt mult_cancel_left1 mult_cancel_right1 no_zero_divisors)
      next
        case False
        then show ?thesis 
          using False prob_choice_one prob_choice_zero assms(3-4) 
          by (smt True mult_cancel_left1 mult_cancel_right1)
      qed
    next
      case False
      have f1: "w\<^sub>1 \<in> {0<..<1}"
        using False assms(1) by auto
      have f2: "w\<^sub>2 \<in> {0<..<1}"
        using False assms(2) by auto
      have f3: "(P \<oplus>\<^bsub>w\<^sub>1\<^esub> (Q \<oplus>\<^bsub>w\<^sub>2\<^esub> R)) = P \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>w\<^sub>1\<^esub>\<^esub> (Q \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>w\<^sub>2\<^esub>\<^esub> R)"
        using f1 f2 by (simp add: prob_choice_r)
      from assms(3) have f4: "r\<^sub>2 = w\<^sub>1+w\<^sub>2-w\<^sub>1*w\<^sub>2"
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
      then have f5: "r\<^sub>2 \<in> {0<..<1}"
        using f1 f2 assms(1-2) assms(3) f4
        by (smt greaterThanLessThan_iff mult_left_le mult_nonneg_nonneg no_zero_divisors)
      from f4 have f6: "(w\<^sub>1+w\<^sub>2-w\<^sub>1*w\<^sub>2) > w\<^sub>1"
        using assms(1) assms(2) mult_left_le_one_le False by auto
      from f4 have f7: "r\<^sub>1 = w\<^sub>1/(w\<^sub>1+w\<^sub>2-w\<^sub>1*w\<^sub>2)"
        by (metis False assms(4) mult_zero_right nonzero_eq_divide_eq)
      from f6 f7 have f8: "r\<^sub>1 \<in> {0<..<1}"
        using False f1 f2 assms(1-4) 
        by (metis divide_less_eq_1_pos f5 greaterThanLessThan_iff 
            less_asym mult_zero_left nonzero_mult_div_cancel_left zero_less_divide_iff)
      have f9: "((P \<oplus>\<^bsub>r\<^sub>1\<^esub> Q) \<oplus>\<^bsub>r\<^sub>2\<^esub> R) = (P \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^sub>1\<^esub>\<^esub> Q) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^sub>2\<^esub>\<^esub> R"
        using f5 f8 f2 by (simp add: prob_choice_r)
      show ?thesis 
        apply (simp add: f3 f9)
        apply (simp add: p q r lhs rhs)
        apply (ndes_simp cls: assms)
        apply (rel_auto)
        apply (metis assms(1) assms(2) assms(4) wplus_assoc)
        apply blast
        apply (metis assms(1) assms(2) assms(4) wplus_assoc)
        by blast
    qed
qed

(* In He's paper, 0 and 1 are defined as special cases for probabilistic choice. Maybe the reason behind
is because if the probabilistic choice is defined as parallel-by-merge for inclusive {0..1}, its 
preconditions (p and q) cannot be discharged into one precondition (p or q) for 0 and 1. 
Actually, by parallel-by-merge, its precondition is 
  (pre\<^sub>p \<or> pre\<^sub>q \<and> \<not> Pre post\<^sub>q) \<and> (pre\<^sub>q \<or> pre\<^sub>p \<and> \<not> Pre post\<^sub>p))

No r appears in the precondition, so as it is no matter what the value that r takes.

Jim: this is a very interesting finding. We need to mention it in future papers.
*)
lemma prob_choice_one': 
  assumes "P is \<^bold>N" "Q is \<^bold>N"
  shows "(P \<oplus>\<^bsub>1\<^esub> Q) = P"
  by (simp add: prob_choice_one)
(*
proof -
  obtain pre\<^sub>p post\<^sub>p pre\<^sub>q post\<^sub>q
    where p:"P = (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p)" and 
          q:"Q = (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)"
    using assms by (metis ndesign_form)
  hence "(P \<oplus>\<^bsub>1\<^esub> Q) = (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) \<oplus>\<^bsub>1\<^esub> (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)"
    by simp
  also have "... = (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p)"
    apply (ndes_simp cls: assms)
    apply (simp add: Healthy_def Convex_Closed_def upred_defs)
    apply (rel_auto)
    sorry
  then show ?thesis
    by (simp add: p q)
qed
*)

(* declare [[show_types]] *)

lemma prob_choice_cond_distl:
  assumes "r \<in> {0..1}" "P is \<^bold>N" "Q is \<^bold>N" "R is \<^bold>N"
  shows "P \<oplus>\<^bsub>r\<^esub> (Q \<triangleleft> b \<triangleright>\<^sub>D R)  = ((P \<oplus>\<^bsub>r\<^esub> Q) \<triangleleft> b \<triangleright>\<^sub>D (P \<oplus>\<^bsub>r\<^esub> R))" (is "?LHS = ?RHS")
proof -
  obtain pre\<^sub>p post\<^sub>p pre\<^sub>q post\<^sub>q pre\<^sub>r post\<^sub>r
    where p:"P = (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p)" and 
          q:"Q = (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)" and 
          r:"R = (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)"
    using assms by (metis ndesign_form)
  hence lhs: "?LHS = ((pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p)) \<oplus>\<^bsub>r\<^esub> ( (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q) \<triangleleft> b \<triangleright>\<^sub>D (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r))"
    by auto
  also have lhs': "... = (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) \<oplus>\<^bsub>r\<^esub> (((pre\<^sub>q \<triangleleft> b \<triangleright> pre\<^sub>r) \<turnstile>\<^sub>n (post\<^sub>q \<triangleleft> b \<triangleright>\<^sub>r post\<^sub>r)))"
    by (ndes_simp)
  have rhs: "?RHS = (((pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) \<oplus>\<^bsub>r\<^esub> (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)) \<triangleleft> b \<triangleright>\<^sub>D ((pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) \<oplus>\<^bsub>r\<^esub> (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)))"
    by (simp add: p q r)
  show ?thesis
    apply (simp add: p q r lhs' rhs)
    apply (ndes_simp cls: assms)
    by (rel_auto)
qed

subsubsection \<open> UTP expression as weight \<close>
lemma log_const_metasubt_eq:
  assumes "\<forall>x. P x is \<^bold>N"
  shows "(P r)\<lbrakk>r\<rightarrow>\<lceil>\<lceil>E\<rceil>\<^sub><\<rceil>\<^sub>D\<rbrakk> = (con\<^sub>D R \<bullet> (II\<^sub>D \<triangleleft> U(\<guillemotleft>R\<guillemotright> = E) \<triangleright>\<^sub>D \<bottom>\<^sub>D) ;; P R)"
proof -
  have p: "P r = (pre\<^sub>D(P r) \<turnstile>\<^sub>r post\<^sub>D(P r))"
    using assms by (metis H1_H3_commute H1_H3_is_rdesign H3_idem Healthy_def)
  have f1: "(pre\<^sub>D(P r) \<turnstile>\<^sub>r post\<^sub>D(P r))\<lbrakk>r\<rightarrow>\<lceil>\<lceil>E\<rceil>\<^sub><\<rceil>\<^sub>D\<rbrakk> = msubst (\<lambda>r. (pre\<^sub>D(P r) \<turnstile>\<^sub>r post\<^sub>D(P r))) \<lceil>\<lceil>E\<rceil>\<^sub><\<rceil>\<^sub>D"
    by simp
  then have f2: "... =  msubst (\<lambda>r. P r) \<lceil>\<lceil>E\<rceil>\<^sub><\<rceil>\<^sub>D"
    using p apply (simp add: ext)
    by (metis (no_types) H1_H2_eq_rdesign H2_H3_absorb Healthy_def assms ndesign_form ndesign_is_H3)
  have f3: "(pre\<^sub>D(P r) \<turnstile>\<^sub>r post\<^sub>D(P r))\<lbrakk>r\<rightarrow>\<lceil>\<lceil>E\<rceil>\<^sub><\<rceil>\<^sub>D\<rbrakk> = 
    (con\<^sub>D R \<bullet> (II\<^sub>D \<triangleleft> U(\<guillemotleft>R\<guillemotright> = E) \<triangleright>\<^sub>D \<bottom>\<^sub>D) ;; (pre\<^sub>D(P R) \<turnstile>\<^sub>r post\<^sub>D(P R)))"
    by (rel_auto)
  show ?thesis
    using f1 f2 f3
    by (smt USUP_all_cong assms ndesign_def ndesign_form ndesign_pre)
qed

lemma log_const_metasubt_eq':
  shows "(P0 \<turnstile>\<^sub>n (P1 r))\<lbrakk>r\<rightarrow>\<lceil>\<lceil>E\<rceil>\<^sub><\<rceil>\<^sub>D\<rbrakk> = (con\<^sub>D R \<bullet> (II\<^sub>D \<triangleleft> U(\<guillemotleft>R\<guillemotright> = E) \<triangleright>\<^sub>D \<bottom>\<^sub>D) ;; (P0 \<turnstile>\<^sub>n (P1 R)))"
  apply (ndes_simp)
  by (rel_auto)

subsubsection \<open> Assignment \<close>
(*
lemma 
  fixes x :: "'a \<Longrightarrow> 'b prss"
  assumes "r \<in> {0..1}" "a \<noteq> b" "weak_lens x"
  shows "(\<K>(x :=\<^sub>D \<guillemotleft>a\<guillemotright>) \<oplus>\<^bsub>(r)\<^esub> \<K>(x :=\<^sub>D \<guillemotleft>b\<guillemotright>)) = 
         (\<^U>(true) \<turnstile>\<^sub>n U($prob\<acute>($\<^bold>v\<lbrakk>\<guillemotleft>a\<guillemotright>/$x\<rbrakk>) = \<guillemotleft>r\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>\<guillemotleft>b\<guillemotright>/$x\<rbrakk>) = \<guillemotleft>(1-r)\<guillemotright>))"
proof (cases "r = 0")
  case True
  show ?thesis 
    apply (simp add: True prob_choice_zero)
    apply (simp add: pemp_assign)
    apply (rel_auto)
  proof -
    fix ok\<^sub>v::"bool" and more::"'b" and ok\<^sub>v'::"bool" and prob\<^sub>v::"'b pmf"
    assume a1: "pmf prob\<^sub>v (put\<^bsub>x\<^esub> more b) = (1::real)"
    show "pmf prob\<^sub>v (put\<^bsub>x\<^esub> more a) = (0::real)"
      apply (rule pmf_not_the_one_is_zero[where xa="(put\<^bsub>x\<^esub> more b)"])
      using a1 apply blast
      using assms(2) apply (simp add: view_determination)
  qed
next
  case False
  then show ?thesis sorry
qed
  apply (simp add: pemp_assign prob_choice_r)
  apply (simp add: ndes_par)
  apply (rule ndesign_eq_intro)
  apply (simp)
  apply (rel_auto)
  apply (simp add: pmf_wplus pmf_not_the_one_is_zero)+
  apply (rule_tac ?x = "x\<^sub>v" in exI)
  apply (rule_tac ?x = "y\<^sub>v" in exI)
  apply (rule_tac x = "pmf_of_set {\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>}" in exI)
  apply (simp)
  apply (rule_tac x = "pmf_of_set {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}" in exI)
  apply (simp)
  apply (subgoal_tac "\<forall>s. (pmf prob\<^sub>v s) =
       pmf (pmf_of_set {\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>} +\<^bsub>(1::real) / (3::real)\<^esub> 
            pmf_of_set {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}) s")
  using pmf_eqI apply blast
  apply (auto)
  apply (simp add: pmf_wplus)
  apply (case_tac "s = \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>")
  apply auto[1]
  apply (case_tac "s = \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>")
  apply auto[1]
  apply (subst pmf_not_in_the_two_is_zero[where a = "(1::real)/(3::real)" and 
        sa="\<lparr>x\<^sub>v = (0::int), y\<^sub>v = y\<^sub>v\<rparr>" and 
        sb="\<lparr>x\<^sub>v = (1::int), y\<^sub>v = y\<^sub>v\<rparr>"])
*)

subsection \<open> Sequence \<close>
lemma sequence_cond_distr:
  assumes "P is \<^bold>N" "Q is \<^bold>N" "R is \<^bold>N"
  shows "(P \<triangleleft> b \<triangleright>\<^sub>D Q) ;; R  = ((P ;; R) \<triangleleft> b \<triangleright>\<^sub>D (Q ;; R))" (is "?LHS = ?RHS")
  by (rel_auto)

lemma sequence_inf_distr:
  assumes "P is \<^bold>N" "Q is \<^bold>N" "R is \<^bold>N"
  shows "(P \<sqinter> Q) ;; R  = ((P ;; R) \<sqinter> (Q ;; R))" (is "?LHS = ?RHS")
  by (rel_auto)

find_theorems "Rep_uexpr"
term "Rep_uexpr"
term "Abs_uexpr"
find_theorems "uexpr_defs"
(* \<lbrakk>(P::'a prss hrel)\<rbrakk>\<^sub>e is Rep_uexpr that injects from the type (uexpr) to the set (UNIV :: ('\<alpha> \<Rightarrow> 't) set) *)
(* 'a prss hrel = ('a prss \<times> 'a prss) upred = (bool, ('a prss \<times> 'a prss)) uexpr *)
term "\<lbrakk>(P::'a prss hrel)\<rbrakk>\<^sub>e ::('a prss \<times> 'a prss \<Rightarrow> bool)"

lemma weight_sum_is_both_1:
  assumes "r \<in> {0<..<1}" "x \<in> {0..1}" "y \<in> {0..1}"
  assumes "x*r + y*(1-r) = (1::real)"
  shows "x = 1 \<and> y = 1"
proof (rule ccontr)
  assume a1: "\<not> (x = (1::real) \<and> y = (1::real))"
  have "(\<not> x = (1::real)) \<or> (\<not> y = (1::real))"
    using a1 by blast
  then show False
  proof
    assume a11: "\<not> x = (1::real)"
    have f1: "x < 1"
      using assms(2) a11 by auto
    have f2: "x*r = (1::real) - y + y*r"
      by (metis add_diff_cancel assms(4) diff_add_eq diff_diff_eq2 mult_cancel_left1 
          vector_space_over_itself.scale_right_diff_distrib)
    have f3: "(1::real) - y + y*r < r"
      using f1 f2
      by (smt assms(1) assms(2) atLeastAtMost_iff greaterThanLessThan_iff mult.commute 
          mult_cancel_left1 mult_left_le_one_le)
    then have f4: "(1-y) < (1-y)*r"
      by (simp add: mult.commute vector_space_over_itself.scale_right_diff_distrib)
    then have f5: "r > 1"
      by (smt assms(3) atLeastAtMost_iff f3 sum_le_prod1)
    then show False
      using assms(1) by auto
  next
    assume a11: "\<not> y = (1::real)"
    have f1: "y < 1"
      using assms(3) a11 by auto
    have f2: "y*(1-r) = (1::real)-x*r"
      using assms(4) by linarith
    have f3: "(1::real)-x*r < 1-r"
      using f1 f2
      by (smt assms(1) assms(3) atLeastAtMost_iff greaterThanLessThan_iff mult_cancel_right1 
          mult_left_le_one_le)
    then have f4: "x > 1"
      using assms(1) by auto
    then show False
      using assms(2) by auto
  qed
qed

(*
term "
(\<^bold>\<forall>s \<bullet> 
  (\<^bold>\<exists> p1 \<bullet> 
    (\<^bold>\<exists> p2 \<bullet> 
      ((U($\<^bold>v\<acute> = s) ;; p ;; U(($prob = p1) \<and> ($prob\<acute>=$prob))) \<and> 
      (U($\<^bold>v\<acute> = s) ;; p ;; U($prob = p2 \<and> $prob\<acute>=$prob))) \<Rightarrow> U(p1 = p2))))"

abbreviation determinate_prob_des::"('a, 'a) rel_pdes \<Rightarrow> ('a, 'a) rel_pdes" where
"determinate_prob_des P \<equiv> 
  P \<and> (\<^bold>\<forall>s \<bullet> 
  (\<^bold>\<exists> p1 \<bullet> 
    (\<^bold>\<exists> p2 \<bullet> 
      ((U($\<^bold>v = s \<and> $\<^bold>v\<acute> = s) ;; P ;; U($prob = p1 \<and> $prob\<acute>=$prob)) \<and> 
      (U($\<^bold>v = s \<and> $\<^bold>v\<acute> = s) ;; P ;; U($prob = p2 \<and> $prob\<acute>=$prob))) \<Rightarrow> U(p1 = p2))))"
*)

(*
text \<open> @{term "deterministic_prob_rel"} checks if a probabilistic relation is deterministic or not. 
This is a very strong condition. \<close>

abbreviation deterministic_prob_rel:: "('a, 'b prss) urel \<Rightarrow> bool" where
"deterministic_prob_rel post\<^sub>r \<equiv> 
(\<forall>xa. \<forall>prob1. \<forall>prob2. 
  (\<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob1\<rparr>) \<and> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob2\<rparr>))
  \<longrightarrow> prob1 = prob2)"

abbreviation deterministic_prob_des:: "('a, 'a) rel_pdes \<Rightarrow> bool" where
"deterministic_prob_des P \<equiv> deterministic_prob_rel (pre\<^sub>D(P) \<and> post\<^sub>D(P))"

lemma sequence_prob_distr:
  fixes P::"('a, 'a) rel_pdes" and Q::"('a, 'a) rel_pdes" and R::"('a, 'a) rel_pdes"
  assumes "r \<in> {0..1}" "P is \<^bold>N" "Q is \<^bold>N" "R is \<^bold>N"
  \<comment> \<open> We need it to be finite in order to extract r from 
  @{text "(\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v'' xb) \<cdot> pmf (x xb) xa *r)"} according to @{thm "infsetsum_cmult_left"}.
  Alternatively, if not restricted to finite, we have to prove 
  @{text "\<lambda>xb. (pmf prob\<^sub>v'' xb) \<cdot> pmf (x xb) xa"} is @{thm "abs_summable_on_def"} \<close>
  assumes "finite (UNIV::'a set)"
  assumes "Pre(pre\<^sub>D(P) \<and> post\<^sub>D(P)) = true"
  assumes "Pre(pre\<^sub>D(Q) \<and> post\<^sub>D(Q)) = true"
  \<comment> \<open> This states R is deterministic. \<close>
  assumes "deterministic_prob_des R"
  shows "(P \<oplus>\<^bsub>r\<^esub> Q) ;; \<up> R  = ((P ;; \<up> R) \<oplus>\<^bsub>r\<^esub> (Q ;; \<up> R))" (is "?LHS = ?RHS")
proof (cases "r \<in> {0<..<1}")
  case True
  obtain pre\<^sub>p post\<^sub>p pre\<^sub>q post\<^sub>q pre\<^sub>r post\<^sub>r
    where p:"P = (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p)" and 
          q:"Q = (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)" and 
          r:"R = (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)"
    using assms by (metis ndesign_form)
  have lhs0: "?LHS = (P \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> Q) ;; \<up> R"
    using True prob_choice_r by (simp add: prob_choice_r)
  have rhs0: "?RHS = ((P ;; \<up> R)  \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> (Q ;; \<up> R))"
    using True prob_choice_r by (simp add: prob_choice_r)
  hence lhs: "?LHS = ((pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)) ;; \<up> (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)"
    using lhs0 p q r by blast
  have rhs: "?RHS = (((pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) ;; \<up> (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> ((pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q) ;; \<up> (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)))"
    using rhs0 p q r by blast
  have pre_p: "Pre(post\<^sub>p) = true"
    using assms(6) p apply (simp add: upred_defs)
    by (rel_auto)
  have pre_q: "Pre(post\<^sub>q) = true"
    using assms(7) q apply (simp add: upred_defs)
    by (rel_auto)
  have lhs_rhs: "((pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)) ;; \<up> (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r) = 
    (((pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) ;; \<up> (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> ((pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q) ;; \<up> (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)))"
    apply (simp add: kleisli_lift_alt_def kleisli_lift2'_def upred_set_def)
    apply (simp add: ndes_simp)
    apply (rule ndesign_eq_intro)
    apply (simp add: pre_p pre_q)
    apply (rel_auto)
    prefer 11
    apply (rel_auto)
    proof -
      fix a::"'a" and prob\<^sub>v::"'a pmf" and x::"'a \<Rightarrow> 'a pmf" and prob\<^sub>v''::"'a pmf" and prob\<^sub>v'''::"'a pmf"
      assume a1: "\<forall>xa::'a. pmf prob\<^sub>v xa = (\<Sum>\<^sub>axb::'a. pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') xb \<cdot> pmf (x xb) xa)"
      assume a2: "\<forall>xa::'a.
          (\<exists>prob\<^sub>v::'a pmf.
              (\<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e xa \<longrightarrow> \<not> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)) \<and>
              (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb)) \<longrightarrow>
          \<not> (0::real) < pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') xa"
      assume a3: "\<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (a, \<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>)"
      assume a4: "\<lbrakk>post\<^sub>q\<rbrakk>\<^sub>e (a, \<lparr>prob\<^sub>v = prob\<^sub>v'''\<rparr>)"
      have f0: "\<forall>xa::'a. pmf prob\<^sub>v xa = 
        (\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v'' xb) \<cdot> pmf (x xb) xa)*r + 
        (\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v''' xb) \<cdot> pmf (x xb) xa) * (1 - r)"
        apply (auto)
        proof -
          fix xa::"'a"
          have f00:"(\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v'' xb) \<cdot> pmf (x xb) xa *r) = 
            (\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v'' xb) \<cdot> pmf (x xb) xa) *r"
            apply (rule infsetsum_cmult_left)
            by (simp add: assms(5))
          have f00': "(\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v''' xb) \<cdot> pmf (x xb) xa * (1 - r)) = 
            (\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v''' xb) \<cdot> pmf (x xb) xa) * (1 - r)"
            apply (rule infsetsum_cmult_left)
            by (simp add: assms(5))
          have f01: "pmf prob\<^sub>v xa = 
            (\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v'' xb * r + pmf prob\<^sub>v''' xb * (1 - r)) \<cdot> pmf (x xb) xa)"
            using a1
            by (metis (no_types, lifting) assms(1) infsetsum_cong pmf_wplus)
          then have f02: "... = (\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v'' xb * r) \<cdot> pmf (x xb) xa + 
           (pmf prob\<^sub>v''' xb * (1 - r)) \<cdot> pmf (x xb) xa)"
            by auto
          then have f03: "... = (\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v'' xb * r) \<cdot> pmf (x xb) xa) + 
            (\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v''' xb * (1 - r)) \<cdot> pmf (x xb) xa)"
            apply (auto)
            apply (rule infsetsum_add)
            by (simp add: assms(5))+
          then have f04: "... = (\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v'' xb) \<cdot> pmf (x xb) xa *r) + 
            (\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v''' xb) \<cdot> pmf (x xb) xa * (1 - r))"
            by (smt infsetsum_cong mult.assoc mult.commute)
          then have f05: "... = (\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v'' xb) \<cdot> pmf (x xb) xa) * r + 
            (\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v''' xb) \<cdot> pmf (x xb) xa) * (1 - r)"
            using f00 f00' by auto
  
          show "pmf prob\<^sub>v xa =
            (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v'' xb \<cdot> pmf (x xb) xa) \<cdot> r +
            (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v''' xb \<cdot> pmf (x xb) xa) \<cdot> ((1::real) - r)"
            apply (simp add: a1)
            using a1 f00 f00' f01 f03 f04 by auto
        qed
      from a2 have f1: "\<forall>xa::'a. (0::real) < pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') xa 
            \<longrightarrow> (\<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = (x xa)\<rparr>))"
        by blast

      \<comment> \<open> In order to show ?prob\<^sub>1 is a probability distribution, we need to prov 
        @{text "(\<Sum>\<^sub>axa::'a. (\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v'' xb) \<cdot> pmf (x xb) xa)) = 1"}. \<close>
        
      (* Construct two witnesses using @{text "embed_pmf"}. In order to prove it is probability space, we 
      need to prove three conditions for each witness. *)
      let ?prob\<^sub>1_f = "(\<lambda>xa. (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v'' xb \<cdot> pmf (x xb) xa))"
      let ?prob\<^sub>1 = "embed_pmf ?prob\<^sub>1_f"
      let ?prob\<^sub>2_f = "(\<lambda>xa. (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v''' xb \<cdot> pmf (x xb) xa))"
      let ?prob\<^sub>2 = "embed_pmf ?prob\<^sub>2_f"
      have prob\<^sub>1_1: "(\<Sum>a::'a\<in>UNIV. ennreal (\<Sum>xa::'a\<in>UNIV. pmf prob\<^sub>v'' xa \<cdot> pmf (x xa) a)) = (1::ennreal)"
        apply (subst sum_ennreal_extract)
        apply (simp add: sum_nonneg)
        apply (subst sum.swap)
        proof -
          have prob\<^sub>1_1': "(\<Sum>j::'a\<in>UNIV. (\<Sum>i::'a\<in>UNIV. pmf prob\<^sub>v'' j \<cdot> pmf (x j) i)) = 
                (\<Sum>j::'a\<in>UNIV . pmf prob\<^sub>v'' j)"
            by (metis assms(5) infsetsum_finite mult.right_neutral sum_distrib_left 
                sum_pmf_eq_1)
          then have prob\<^sub>1_1'': "... = 1"
            by (metis assms(5) infsetsum_finite sum_pmf_eq_1)
          then show "ennreal (\<Sum>j::'a\<in>UNIV. \<Sum>i::'a\<in>UNIV. pmf prob\<^sub>v'' j \<cdot> pmf (x j) i) = (1::ennreal)"
            by (simp add: prob\<^sub>1_1')
        qed
      have prob1_pmf_embed_pmf: "\<forall>x::'a. pmf (?prob\<^sub>1) x = ?prob\<^sub>1_f x"
        apply (subst pmf_embed_pmf)
        apply (simp add: infsetsum_nonneg)
        apply (simp add: assms(5) nn_integral_count_space_finite)
        defer
        apply (simp)
        using prob\<^sub>1_1 by auto
      have prob\<^sub>2_1: "(\<Sum>a::'a\<in>UNIV. ennreal (\<Sum>xa::'a\<in>UNIV. pmf prob\<^sub>v''' xa \<cdot> pmf (x xa) a)) = (1::ennreal)"
        apply (subst sum_ennreal_extract)
        apply (simp add: sum_nonneg)
        apply (subst sum.swap)
        proof -
          have prob\<^sub>1_1': "(\<Sum>j::'a\<in>UNIV. (\<Sum>i::'a\<in>UNIV. pmf prob\<^sub>v''' j \<cdot> pmf (x j) i)) = 
                (\<Sum>j::'a\<in>UNIV . pmf prob\<^sub>v''' j)"
            by (metis assms(5) infsetsum_finite mult.right_neutral sum_distrib_left 
                sum_pmf_eq_1)
          then have prob\<^sub>1_1'': "... = 1"
            by (metis assms(5) infsetsum_finite sum_pmf_eq_1)
          then show "ennreal (\<Sum>j::'a\<in>UNIV. \<Sum>i::'a\<in>UNIV. pmf prob\<^sub>v''' j \<cdot> pmf (x j) i) = (1::ennreal)"
            by (simp add: prob\<^sub>1_1')
        qed
      have prob2_pmf_embed_pmf: "\<forall>x::'a. pmf (?prob\<^sub>2) x = ?prob\<^sub>2_f x"
        apply (subst pmf_embed_pmf)
        apply (simp add: infsetsum_nonneg)
        apply (simp add: assms(5) nn_integral_count_space_finite)
        defer
        apply (simp)
        using prob\<^sub>2_1 by auto
      have f2: "\<And>(xa::'a) prob\<^sub>v::'a pmf.
       \<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb \<Longrightarrow> (0::real) < pmf prob\<^sub>v'' xa \<Longrightarrow> \<not> \<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e xa \<Longrightarrow> False"
        proof -
          fix xa::"'a" and prob1\<^sub>v::"'a pmf"
          assume a11: "\<forall>xb::'a. pmf prob1\<^sub>v xb = pmf (x xa) xb"
          assume a12: "(0::real) < pmf prob\<^sub>v'' xa"
          assume a13: "\<not> \<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e xa"
          from a12 have gt0: "(0::real) < pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') xa"
            by (smt True atLeastAtMost_iff greaterThanLessThan_iff mult_nonneg_nonneg 
                mult_pos_pos pmf_not_neg pmf_wplus)
          then have "\<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e xa"
            using a2 gt0 by blast
          then show "False"
            using a13 by blast
        qed
      have f2': "\<And>(xa::'a) prob\<^sub>v::'a pmf.
       \<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb \<Longrightarrow> (0::real) < pmf prob\<^sub>v''' xa \<Longrightarrow> \<not> \<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e xa \<Longrightarrow> False"
        proof -
          fix xa::"'a" and prob1\<^sub>v::"'a pmf"
          assume a11: "\<forall>xb::'a. pmf prob1\<^sub>v xb = pmf (x xa) xb"
          assume a12: "(0::real) < pmf prob\<^sub>v''' xa"
          assume a13: "\<not> \<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e xa"
          from a12 have gt0: "(0::real) < pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') xa"
            by (smt True atLeastAtMost_iff greaterThanLessThan_iff mult_nonneg_nonneg 
                mult_pos_pos pmf_not_neg pmf_wplus)
          then have "\<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e xa"
            using a2 gt0 by blast
          then show "False"
            using a13 by blast
        qed
      have f3: "\<And>(xa::'a) prob\<^sub>v::'a pmf.
       \<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb \<Longrightarrow>
       (0::real) < pmf prob\<^sub>v'' xa \<Longrightarrow> \<not> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>) \<Longrightarrow> False"
        proof -
          fix xa::"'a" and prob1\<^sub>v::"'a pmf"
          assume a11: "\<forall>xb::'a. pmf prob1\<^sub>v xb = pmf (x xa) xb"
          assume a12: "(0::real) < pmf prob\<^sub>v'' xa"
          assume a13: "\<not> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob1\<^sub>v\<rparr>)"
          from a12 have gt0: "(0::real) < pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') xa"
            by (smt True atLeastAtMost_iff greaterThanLessThan_iff mult_nonneg_nonneg 
                mult_pos_pos pmf_not_neg pmf_wplus)
          then have "\<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = (x xa)\<rparr>)"
            using f1 by blast
          then show "False"
            using a11 a13 a2 gt0 by blast
        qed
      have f3': "\<And>(xa::'a) prob\<^sub>v::'a pmf.
       \<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb \<Longrightarrow>
       (0::real) < pmf prob\<^sub>v''' xa \<Longrightarrow> \<not> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>) \<Longrightarrow> False"
        proof -
          fix xa::"'a" and prob1\<^sub>v::"'a pmf"
          assume a11: "\<forall>xb::'a. pmf prob1\<^sub>v xb = pmf (x xa) xb"
          assume a12: "(0::real) < pmf prob\<^sub>v''' xa"
          assume a13: "\<not> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob1\<^sub>v\<rparr>)"
          from a12 have gt0: "(0::real) < pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') xa"
            by (smt True atLeastAtMost_iff greaterThanLessThan_iff mult_nonneg_nonneg 
                mult_pos_pos pmf_not_neg pmf_wplus)
          then have "\<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = (x xa)\<rparr>)"
            using f1 by blast
          then show "False"
            using a11 a13 a2 gt0 by blast
        qed
      have prob_choice_eq: "\<forall>xa::'a. pmf prob\<^sub>v xa = pmf (?prob\<^sub>1 +\<^bsub>r\<^esub> ?prob\<^sub>2) xa"
        apply (subst pmf_wplus)
        using assms(1) apply blast
        apply (simp add: prob1_pmf_embed_pmf prob2_pmf_embed_pmf)
        using a1 f0 by blast
      show "\<exists>(mrg_prior\<^sub>v::'a) prob\<^sub>v'::'a pmf.
          (\<exists>prob\<^sub>v::'a pmf.
              \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (a, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>) \<and>
              (\<exists>x::'a \<Rightarrow> 'a pmf.
                  (\<forall>xa::'a. pmf prob\<^sub>v' xa = (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v xb \<cdot> pmf (x xb) xa)) \<and>
                  (\<forall>xa::'a.
                      (\<exists>prob\<^sub>v::'a pmf.
                          (\<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e xa \<longrightarrow> \<not> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)) \<and>
                          (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb)) \<longrightarrow>
                      \<not> (0::real) < pmf prob\<^sub>v xa))) \<and>
          (\<exists>prob\<^sub>v''::'a pmf.
              (\<exists>prob\<^sub>v::'a pmf.
                  \<lbrakk>post\<^sub>q\<rbrakk>\<^sub>e (a, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>) \<and>
                  (\<exists>x::'a \<Rightarrow> 'a pmf.
                      (\<forall>xa::'a. pmf prob\<^sub>v'' xa = (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v xb \<cdot> pmf (x xb) xa)) \<and>
                      (\<forall>xa::'a.
                          (\<exists>prob\<^sub>v::'a pmf.
                              (\<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e xa \<longrightarrow> \<not> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)) \<and>
                              (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb)) \<longrightarrow>
                          \<not> (0::real) < pmf prob\<^sub>v xa))) \<and>
              mrg_prior\<^sub>v = a \<and> prob\<^sub>v = prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v'')"
        apply (rule_tac x = "a" in exI)
        apply (rule_tac x = "?prob\<^sub>1" in exI)
        apply (rule conjI)
        apply (rule_tac x = "prob\<^sub>v''" in exI)
        apply (rule conjI, simp add: a3)
        apply (rule_tac x = "x" in exI)
        apply (rule conjI)
        using prob1_pmf_embed_pmf apply blast
        apply (auto)
        using f2 apply blast
        using f3 apply blast
        apply (rule_tac x = "?prob\<^sub>2" in exI)
        apply (rule conjI)
        apply (rule_tac x = "prob\<^sub>v'''" in exI)
        apply (rule conjI, simp add: a4)
        apply (rule_tac x = "x" in exI)
        apply (rule conjI)
        using prob2_pmf_embed_pmf apply blast
        apply (auto)
        using f2' apply blast
        using f3' apply blast
        using prob_choice_eq pmf_eqI by blast
    next
      fix a::"'a" and prob\<^sub>v'::"'a pmf" and prob\<^sub>v''::"'a pmf" and prob\<^sub>v'''::"'a pmf" 
          and x::"'a \<Rightarrow> 'a pmf" and prob\<^sub>v''''::"'a pmf" and xa::"'a \<Rightarrow> 'a pmf"
      assume a1: " \<forall>xa::'a. pmf prob\<^sub>v' xa = (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v'' xb \<cdot> pmf (x xb) xa)"
      assume a2: "\<forall>xa::'a.
          (\<exists>prob\<^sub>v::'a pmf.
              (\<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e xa \<longrightarrow> \<not> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)) \<and>
              (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb)) \<longrightarrow>
          \<not> (0::real) < pmf prob\<^sub>v'' xa"
      assume a3: "\<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (a, \<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>)"
      assume a4: "\<lbrakk>post\<^sub>q\<rbrakk>\<^sub>e (a, \<lparr>prob\<^sub>v = prob\<^sub>v''''\<rparr>)"
      assume a5: "\<forall>x::'a. pmf prob\<^sub>v''' x = (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v'''' xb \<cdot> pmf (xa xb) x)"
      assume a6: "\<forall>x::'a.
          (\<exists>prob\<^sub>v::'a pmf.
              (\<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e x \<longrightarrow> \<not> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (x, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)) \<and> 
              (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (xa x) xb)) \<longrightarrow>
          \<not> (0::real) < pmf prob\<^sub>v'''' x"
      from a2 have f1: "\<forall>xa::'a. 0 < pmf prob\<^sub>v'' xa \<longrightarrow> \<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e xa \<and> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = x xa\<rparr>)"
        by blast
      from a6 have f2: "\<forall>xb::'a. 0 < pmf prob\<^sub>v'''' xb \<longrightarrow> \<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e xb \<and> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xb, \<lparr>prob\<^sub>v = xa xb\<rparr>)"
        by blast
      have f3: "\<forall>xb::'a. 0 < pmf prob\<^sub>v'' xb \<and> 0 < pmf prob\<^sub>v'''' xb \<longrightarrow> x xb = xa xb"
        proof (auto)
          fix xb::"'a"
          assume a11: "(0::real) < pmf prob\<^sub>v'' xb"
          assume a12: "(0::real) < pmf prob\<^sub>v'''' xb"
          have f11: "\<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xb, \<lparr>prob\<^sub>v = x xb\<rparr>) \<and> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xb, \<lparr>prob\<^sub>v = xa xb\<rparr>)"
            using a11 a12 f1 f2 by blast
          show "x xb = xa xb"
            using assms(6) f11 ndesign_pre ndesign_post
            by (smt a12 aext.rep_eq conj_upred_def f2 get_fst_lens impl.rep_eq 
                inf_uexpr.rep_eq r utp_pred_laws.inf.idem)
        qed
    \<comment> \<open> We need to prove 
      @{text 
      "(\<exists>x::'a \<Rightarrow> 'a pmf.
            (\<forall>xa::'a. pmf (prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v''') xa = (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v xb \<cdot> pmf (x xb) xa)) \<and>
            (\<forall>xa::'a.
                (\<exists>prob\<^sub>v::'a pmf.
                    (\<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e xa \<longrightarrow> \<not> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)) \<and>
                    (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb)) \<longrightarrow>
                \<not> (0::real) < pmf prob\<^sub>v xa))"}.
    Obviously, @{text "prob\<^sub>v"} must be equal to @{text "prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''''"}. Therefore,
      one subgoal is
      @{text
        "(\<exists>x::'a \<Rightarrow> 'a pmf.
            (\<forall>xa::'a. pmf (prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v''') xa = (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v xb \<cdot> pmf (x xb) xa)))"}. 
      According to a1 and a5, it is simplified to @{text 
      "\<exists>Q::'a \<Rightarrow> 'a pmf. \<forall>xxa::'a.
        (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v'' xb \<cdot> pmf (x xb) xxa) \<cdot> r +
        (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v'''' xb \<cdot> pmf (xa xb) xxa) \<cdot> ((1::real) - r) =
        (\<Sum>\<^sub>ax::'a. pmf prob\<^sub>v'' x \<cdot> r \<cdot> pmf (Q x) xxa + pmf prob\<^sub>v'''' x \<cdot> ((1::real) - r) \<cdot> pmf (Q x) xxa)"}.
      But how can we construct a Q that satisfies this when @{text "pmf prob\<^sub>v'' xb > 0 \<and> pmf prob\<^sub>v'''' xb > 0"}
      if @{text "\<exists>xxa. pmf (x xb) xxa \<noteq> pmf (xa xb) xxa"}. So we need extra condition that establishes
      that @{text "\<forall>xb. x xb = xa xb"}. In other words, there exists one unique Q that satisfies ...
      in the Kleisli lift of R.
    \<close>
      (* 
      have "\<exists>Q::'a \<Rightarrow> 'a pmf. \<forall>xxa::'a. pmf (prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v''') xxa = 
            (\<Sum>\<^sub>axb::'a. pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v'''') xb \<cdot> pmf (Q xb) xxa)"
        using assms(1) apply (simp add: pmf_wplus) 
        apply (simp add: a1 a5)
      *)
      let ?Q = "\<lambda>xb. (if pmf prob\<^sub>v'' xb > 0 \<and> pmf prob\<^sub>v'''' xb > 0 
                                  then (x xb)
                                  else (if pmf prob\<^sub>v'' xb > 0 then x xb else xa xb))"
      have f4: "\<forall>xaa::'a.
       pmf (prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v''') xaa =
       (\<Sum>\<^sub>axb::'a.
          pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v'''') xb \<cdot>
          pmf (?Q xb) xaa)"
        (* using assms(1) apply (simp add: pmf_wplus)
        apply (simp add: a1 a5) *)
        proof (auto)
          fix xaa::"'a"
          have f11: "(\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v'' xb \<cdot> pmf (?Q xb) xaa)) = 
              (\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v'' xb \<cdot> pmf (x xb) xaa))"
            proof -
              { fix aa :: 'a
                { assume "\<not> pmf prob\<^sub>v'' aa = 0"
                  then have "(\<Sum>\<^sub>aa. pmf prob\<^sub>v'' a \<cdot> pmf (?Q a) xaa) = (\<Sum>\<^sub>aa. pmf prob\<^sub>v'' a \<cdot> pmf (x a) xaa) 
                    \<or> pmf prob\<^sub>v'' aa \<cdot> pmf (?Q aa) xaa = pmf prob\<^sub>v'' aa \<cdot> pmf (x aa) xaa"
                  by simp }
              then have "(\<Sum>\<^sub>aa. pmf prob\<^sub>v'' a \<cdot> pmf (?Q a) xaa) = 
                    (\<Sum>\<^sub>aa. pmf prob\<^sub>v'' a \<cdot> pmf (x a) xaa) \<or> pmf prob\<^sub>v'' aa \<cdot> pmf (?Q aa) xaa 
                        = pmf prob\<^sub>v'' aa \<cdot> pmf (x aa) xaa"
                    by fastforce }
              then show ?thesis
                by meson
            qed
          have f12: "(\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v'''' xb \<cdot> pmf (?Q xb) xaa)) = 
              (\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v'''' xb \<cdot> pmf (xa xb) xaa))"
            proof -
              have f121: "(\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v'''' xb \<cdot> pmf (?Q xb) xaa)) = 
                (\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v'''' xb \<cdot> pmf (if (0::real) < pmf prob\<^sub>v'' xb then x xb else xa xb) xaa))"
                proof -
                  have "(\<Sum>\<^sub>aa. pmf prob\<^sub>v'''' a \<cdot> pmf (?Q a) xaa) = 
                    (\<Sum>\<^sub>aa. pmf prob\<^sub>v'''' a \<cdot> pmf (if 0 < pmf prob\<^sub>v'' a then x a else xa a) xaa) 
                  \<or> (\<forall>a. pmf prob\<^sub>v'''' a \<cdot> pmf (?Q a) xaa = 
                    pmf prob\<^sub>v'''' a \<cdot> pmf (if 0 < pmf prob\<^sub>v'' a then x a else xa a) xaa)"
                    by presburger
                  then show ?thesis
                    by presburger
                qed
              then have f122: "... = (\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v'''' xb \<cdot> pmf (xa xb) xaa))"
                using f3 by (metis (full_types, hide_lams) mult_zero_left pmf_pos)
              then show ?thesis
                by (simp add: f121)
            qed
          have f13: "(\<Sum>\<^sub>axb::'a. pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v'''') xb \<cdot> pmf (?Q xb) xaa) = (\<Sum>\<^sub>axb::'a.
            (pmf prob\<^sub>v'' xb * r + pmf prob\<^sub>v'''' xb * (1-r)) \<cdot>  pmf (?Q xb) xaa)"
            using assms(1) by (simp add: pmf_wplus)
          have f14: "... = (\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v'' xb \<cdot> pmf (?Q xb) xaa * r 
                                 + pmf prob\<^sub>v'''' xb \<cdot> pmf (?Q xb) xaa * (1-r)))"
            by (simp add: mult.assoc mult.commute)
          have f15: "... = (\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v'' xb \<cdot> pmf (?Q xb) xaa)) * r 
                    + (\<Sum>\<^sub>axb::'a . pmf prob\<^sub>v'''' xb \<cdot> pmf (?Q xb) xaa) * (1-r)"
            apply (subst infsetsum_add)
            apply (simp add: assms(5))+
            by (simp add: sum_distrib_right)
          have f16: "... = (\<Sum>\<^sub>axb::'a. (pmf prob\<^sub>v'' xb \<cdot> pmf (x xb) xaa)) * r 
                    + (\<Sum>\<^sub>axb::'a . pmf prob\<^sub>v'''' xb \<cdot> pmf (xa xb) xaa) * (1-r)"
            using f3 f11 f12 by simp
          have f17: "... = pmf (prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v''') xaa"
            using a1 a5 by (metis assms(1) pmf_wplus)
          show "pmf (prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v''') xaa =
          (\<Sum>\<^sub>axb::'a.
            pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v'''') xb \<cdot>
            pmf (if (0::real) < pmf prob\<^sub>v'' xb \<and> (0::real) < pmf prob\<^sub>v'''' xb then x xb
                 else if (0::real) < pmf prob\<^sub>v'' xb then x xb else xa xb)
             xaa)"
            using f17 f13 f14 f15 f16 by linarith
        qed
      have f5: "\<forall>xaa::'a.
        (0::real) < pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v'''') xaa \<longrightarrow> 
           (\<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e xaa \<and> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xaa, \<lparr>prob\<^sub>v = ?Q xaa\<rparr>))"
        using assms(1) apply (simp add: pmf_wplus)
        apply (auto)
        apply (simp add: f1)
        using f1 apply blast
        apply (metis (full_types) add.left_neutral f2 mult.commute mult_zero_right pmf_pos)
        by (metis add.left_neutral f2 mult.commute mult_zero_right pmf_pos)
      show "\<exists>prob\<^sub>v::'a pmf.
          (\<exists>(mrg_prior\<^sub>v::'a) prob\<^sub>v'::'a pmf.
              \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (a, \<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>) \<and>
              (\<exists>prob\<^sub>v''::'a pmf.
                  \<lbrakk>post\<^sub>q\<rbrakk>\<^sub>e (a, \<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>) \<and> mrg_prior\<^sub>v = a \<and> prob\<^sub>v = prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v'')) \<and>
          (\<exists>x::'a \<Rightarrow> 'a pmf.
              (\<forall>xa::'a. pmf (prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v''') xa = (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v xb \<cdot> pmf (x xb) xa)) \<and>
              (\<forall>xa::'a.
                  (\<exists>prob\<^sub>v::'a pmf.
                      (\<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e xa \<longrightarrow> \<not> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)) \<and>
                      (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb)) \<longrightarrow>
                  \<not> (0::real) < pmf prob\<^sub>v xa))"
        apply (rule_tac x = "prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''''" in exI)
        apply (rule conjI)
        apply (rule_tac x = "a" in exI)
        apply (rule_tac x = "prob\<^sub>v''" in exI, simp add: a3)
        apply (rule_tac x = "prob\<^sub>v''''" in exI, simp add: a4)
        apply (rule_tac x = "?Q" in exI)
        apply (rule conjI)
        using f4 apply blast
        using f5 pmf_eqI by blast
    next
      fix b::"'a" and prob\<^sub>v::"'a pmf" and prob\<^sub>v'::"'a pmf"
      assume a1: "\<forall>prob\<^sub>v::'a pmf.
          (\<forall>prob\<^sub>v'::'a pmf.
              \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (b, \<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>) \<longrightarrow>
              (\<forall>prob\<^sub>v''::'a pmf. \<lbrakk>post\<^sub>q\<rbrakk>\<^sub>e (b, \<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>) \<longrightarrow> \<not> prob\<^sub>v = prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v'')) \<or>
          infsetsum (pmf prob\<^sub>v) (Collect \<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e) = (1::real)"
      assume a2: "\<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (b, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)"
      assume a3: "\<lbrakk>post\<^sub>q\<rbrakk>\<^sub>e (b, \<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>)"
      assume a4: "\<not> infsetsum (pmf prob\<^sub>v) (Collect \<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e) = (1::real)"
      have "False"
        by (smt True a1 a2 a3 a4 atLeastAtMost_iff greaterThanLessThan_iff infsetsum_all_0 
               mult_nonneg_nonneg mult_pos_pos pmf_all_zero pmf_comp_set pmf_pos pmf_wplus)
      then show "infsetsum (pmf prob\<^sub>v') (Collect \<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e) = (1::real)"
        by blast
    next
      fix b::"'a" and prob\<^sub>v::"'a pmf" and prob\<^sub>v'::"'a pmf" and prob\<^sub>v''::"'a pmf" and x::"'a \<Rightarrow> 'a pmf"
      assume a1: "\<forall>prob\<^sub>v::'a pmf.
          (\<forall>prob\<^sub>v'::'a pmf.
              \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (b, \<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>) \<longrightarrow>
              (\<forall>prob\<^sub>v''::'a pmf. \<lbrakk>post\<^sub>q\<rbrakk>\<^sub>e (b, \<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>) \<longrightarrow> \<not> prob\<^sub>v = prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v'')) \<or>
          infsetsum (pmf prob\<^sub>v) (Collect \<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e) = (1::real)"
      assume a2: "\<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (b, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)"
      assume a3: "\<lbrakk>post\<^sub>q\<rbrakk>\<^sub>e (b, \<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>)"
      assume a4: "\<not> infsetsum (pmf prob\<^sub>v) (Collect \<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e) = (1::real)"
      assume a5: "\<forall>xa::'a.
          (\<exists>prob\<^sub>v::'a pmf.
              (\<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e xa \<longrightarrow> \<not> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)) \<and> (\<forall>xb::'a. pmf prob\<^sub>v xb = pmf (x xa) xb)) \<and>
          \<not> (0::real) < pmf prob\<^sub>v'' xa \<or>
          (\<forall>prob\<^sub>v::'a pmf.
              \<lbrakk>pre\<^sub>r\<rbrakk>\<^sub>e xa \<and> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (xa, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>) \<or> (\<exists>xb::'a. \<not> pmf prob\<^sub>v xb = pmf (x xa) xb))"
      have "False"
        by (smt True a1 a2 a3 a4 atLeastAtMost_iff greaterThanLessThan_iff infsetsum_all_0 
               mult_nonneg_nonneg mult_pos_pos pmf_all_zero pmf_comp_set pmf_pos pmf_wplus)
      then show "\<exists>xa::'a. \<not> pmf prob\<^sub>v' xa = (\<Sum>\<^sub>axb::'a. pmf prob\<^sub>v'' xb \<cdot> pmf (x xb) xa)"
        by blast
next
  case False
  have f1: "r = 0 \<or> r = 1"
    using False assms by auto
  then show ?thesis
    using f1 prob_choice_one prob_choice_zero by metis
qed
*)
(*
lemma sequence_prob_distr:
  assumes "r \<in> {0..1}" "P is \<^bold>N" "Q is \<^bold>N" "R is \<^bold>N"
  shows "(P \<oplus>\<^bsub>r\<^esub> Q) ;; R  = ((P ;; R) \<oplus>\<^bsub>r\<^esub> (Q ;; R))" (is "?LHS = ?RHS")
proof (cases "r \<in> {0<..<1}")
  case True
  obtain pre\<^sub>p post\<^sub>p pre\<^sub>q post\<^sub>q pre\<^sub>r post\<^sub>r
    where p:"P = (pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p)" and 
          q:"Q = (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)" and 
          r:"R = (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)"
    using assms by (metis ndesign_form)
  have lhs0: "?LHS = (P \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> Q) ;; R"
    using True prob_choice_r by (simp add: prob_choice_r)
  have rhs0: "?RHS = ((P ;; R)  \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> (Q ;; R))"
    using True prob_choice_r by (simp add: prob_choice_r)
  hence lhs: "?LHS = ((pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)) ;; (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)"
    using lhs0 p q r by blast
  have rhs: "?RHS = (((pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) ;; (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> ((pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q) ;; (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)))"
    using rhs0 p q r by blast
  have lhs_rhs: "((pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> (pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q)) ;; (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r) = 
    (((pre\<^sub>p \<turnstile>\<^sub>n post\<^sub>p) ;; (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> ((pre\<^sub>q \<turnstile>\<^sub>n post\<^sub>q) ;; (pre\<^sub>r \<turnstile>\<^sub>n post\<^sub>r)))"
    apply (simp add: ndes_simp)
    apply (rule ndesign_eq_intro)
    defer
    apply (rel_auto)
    proof -
      fix a::"'a" and prob\<^sub>v::"'a pmf" and prob\<^sub>v''::"'a pmf" and prob\<^sub>v'''::"'a pmf"
      assume a1: "\<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (\<lparr>prob\<^sub>v = prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v'''\<rparr>, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>)"
      assume a2: "\<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (a, \<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>)"
      assume a3: "\<lbrakk>post\<^sub>q\<rbrakk>\<^sub>e (a, \<lparr>prob\<^sub>v = prob\<^sub>v'''\<rparr>)"
      show "\<exists>(mrg_prior\<^sub>v::'a) prob\<^sub>v'::'a pmf.
            (\<exists>prob\<^sub>v::'a pmf.
                \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (a, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>) \<and> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (\<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>, \<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>)) \<and>
            (\<exists>prob\<^sub>v''::'a pmf.
                (\<exists>prob\<^sub>v::'a pmf.
                    \<lbrakk>post\<^sub>q\<rbrakk>\<^sub>e (a, \<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>) \<and> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (\<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>, \<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>)) \<and>
                mrg_prior\<^sub>v = a \<and> prob\<^sub>v = prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v'')"
        apply (rule_tac x="a" in exI)
        apply (rule_tac x="prob\<^sub>v" in exI)
        apply (rule_tac conjI)
        apply (rule_tac x="prob\<^sub>v''" in exI)
        apply (rule_tac conjI)
        using a2 apply blast
        sorry
    next
      fix a::"'a" and prob\<^sub>v'::"'a pmf" and prob\<^sub>v''::"'a pmf" and prob\<^sub>v'''::"'a pmf" and prob\<^sub>v''''::"'a pmf"
      assume a1: "\<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (a, \<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>)"
      assume a2: "\<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (\<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>, \<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>)"
      assume a3: "\<lbrakk>post\<^sub>q\<rbrakk>\<^sub>e (a, \<lparr>prob\<^sub>v = prob\<^sub>v''''\<rparr>)"
      assume a4: "\<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (\<lparr>prob\<^sub>v = prob\<^sub>v''''\<rparr>, \<lparr>prob\<^sub>v = prob\<^sub>v'''\<rparr>)"
      (* How can we prove it since post\<^sub>r is a homogeneous relation on probability distributions. *)
      have f1: "r \<in> {0<..<1} 
        \<longrightarrow> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (\<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>, \<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>)
        \<longrightarrow> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (\<lparr>prob\<^sub>v = prob\<^sub>v''''\<rparr>, \<lparr>prob\<^sub>v = prob\<^sub>v'''\<rparr>)
        \<longrightarrow> \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (\<lparr>prob\<^sub>v = prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''''\<rparr>, \<lparr>prob\<^sub>v = prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v'''\<rparr>)"
        apply (transfer, auto)
        proof -
          fix post\<^sub>r::"'a prss \<times> 'a prss \<Rightarrow> bool" and 
              prob\<^sub>v''::"'a pmf" and r::"real" and 
              prob\<^sub>v''''::"'a pmf" and prob\<^sub>v'::"'a pmf" and prob\<^sub>v'''::"'a pmf"
          assume r0: "(0::real) < r"
          assume r1: "r < (1::real)"
          assume a21: "post\<^sub>r (\<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>, \<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>)"
          assume a41: "post\<^sub>r (\<lparr>prob\<^sub>v = prob\<^sub>v''''\<rparr>, \<lparr>prob\<^sub>v = prob\<^sub>v'''\<rparr>)"
          show "post\<^sub>r (\<lparr>prob\<^sub>v = prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''''\<rparr>, \<lparr>prob\<^sub>v = prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v'''\<rparr>)"
            using r0 r1 a21 a41 apply 
        qed
      show "\<exists>prob\<^sub>v::'a pmf.
          (\<exists>(mrg_prior\<^sub>v::'a) prob\<^sub>v'::'a pmf.
              \<lbrakk>post\<^sub>p\<rbrakk>\<^sub>e (a, \<lparr>prob\<^sub>v = prob\<^sub>v'\<rparr>) \<and>
              (\<exists>prob\<^sub>v''::'a pmf.
                  \<lbrakk>post\<^sub>q\<rbrakk>\<^sub>e (a, \<lparr>prob\<^sub>v = prob\<^sub>v''\<rparr>) \<and> mrg_prior\<^sub>v = a \<and> prob\<^sub>v = prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v'')) \<and>
          \<lbrakk>post\<^sub>r\<rbrakk>\<^sub>e (\<lparr>prob\<^sub>v = prob\<^sub>v\<rparr>, \<lparr>prob\<^sub>v = prob\<^sub>v' +\<^bsub>r\<^esub> prob\<^sub>v'''\<rparr>)"
        apply (rule_tac x = "prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''''" in exI)
        apply (rule_tac conjI)
        apply (rule_tac x = "a" in exI)
        apply (rule_tac x = "prob\<^sub>v''" in exI)
        apply (rule_tac conjI)
        using a1 apply (simp)
        apply (rule_tac x = "prob\<^sub>v''''" in exI)
        apply (rule_tac conjI)
        using a3 apply (simp)+
        using f1 a2 a4 by blast
    next
  then show ?thesis
    using lhs rhs by auto
next
  case False
  have f1: "r = 0 \<or> r = 1"
    using False assms by auto
  then show ?thesis
    using f1 prob_choice_one prob_choice_zero by metis
qed
*)

subsection \<open> Kleene Algebra \<close>

interpretation pdes_semiring: semiring_1
  where times = pseqr and one = II\<^sub>p and zero = false\<^sub>p and plus = Lattices.sup
  apply (unfold_locales)
  apply (rel_auto)+
  apply (simp add: kleisli_lift_alt_def kleisli_lift2'_def)
  apply (rel_simp)
  oops
(*
declare upred_semiring.power_Suc [simp del]

text \<open> We introduce the power syntax derived from semirings \<close>

abbreviation upower :: "'\<alpha> hrel \<Rightarrow> nat \<Rightarrow> '\<alpha> hrel" (infixr "\<^bold>^" 80) where
"upower P n \<equiv> upred_semiring.power P n"

translations
  "P \<^bold>^ i" <= "CONST power.power II op ;; P i"
  "P \<^bold>^ i" <= "(CONST power.power II op ;; P) i"
*)

subsection \<open> Iteration \<close>
text \<open> Overloadable Syntax \<close>
  
consts
  uiterate       :: "'a set \<Rightarrow> ('a \<Rightarrow> 'p) \<Rightarrow> ('a \<Rightarrow> 'r) \<Rightarrow> 'r"
  uiterate_list  :: "('a \<times> 'r) list \<Rightarrow> 'r"

syntax
  "_iterind"       :: "pttrn \<Rightarrow> uexp \<Rightarrow> uexp \<Rightarrow> logic \<Rightarrow> logic" ("do _\<in>_ \<bullet> _ \<rightarrow> _ od")
  "_itergcomm"     :: "gcomms \<Rightarrow> logic" ("do _ od")
  
translations
  "_iterind x A g P" => "CONST uiterate A (\<lambda> x. g) (\<lambda> x. P)"
  "_iterind x A g P" <= "CONST uiterate A (\<lambda> x. g) (\<lambda> x'. P)"
  "_itergcomm cs" => "CONST uiterate_list cs"
  "_itergcomm (_gcomm_show cs)" <= "CONST uiterate_list cs"
 
definition IteratePD :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a upred) \<Rightarrow> ('b \<Rightarrow> ('a, 'a) rel_pdes) \<Rightarrow> ('a, 'a) rel_pdes" where
[upred_defs, ndes_simp]:
"IteratePD A g P = (\<mu>\<^sub>N X \<bullet> if i\<in>A \<bullet> g(i) \<rightarrow> P(i) ;; \<up>X else \<K>(II\<^sub>D) fi)"

definition IteratePD_list :: "('a upred \<times> ('a, 'a) rel_pdes) list \<Rightarrow> ('a, 'a) rel_pdes" where 
[upred_defs, ndes_simp]:
"IteratePD_list xs = IteratePD {0..<length xs} (\<lambda> i. fst (nth xs i)) (\<lambda> i. snd (nth xs i))"

adhoc_overloading
  uiterate IteratePD and
  uiterate_list IteratePD_list

term "do U(i < \<guillemotleft>N\<guillemotright> \<and> c) \<rightarrow> unisel_rec_bd_choice N od"

lemma IteratePD_empty:
  "do i\<in>{} \<bullet> g(i) \<rightarrow> P(i) od = \<K>(II\<^sub>D)"
  apply (simp add: IteratePD_def AlternateD_empty ndes_theory.LFP_const)
  apply (simp add: pemp_skip)
  apply (rule utp_des_theory.ndes_theory.LFP_const)
  by (simp add: ndesign_H1_H3)

lemma IteratePD_singleton:
  assumes "P is \<^bold>N"
  shows "do b \<rightarrow> P od = do i\<in>{0} \<bullet> b \<rightarrow> P od"
  apply (simp add: IteratePD_list_def IteratePD_def AlernateD_singleton assms)
  apply (subst AlernateD_singleton)
  apply (simp)
  apply (simp add: assms kleisli_lift2'_def kleisli_lift_alt_def ndesign_H1_H3 seq_r_H1_H3_closed)
  apply (simp add: ndesign_H1_H3 pemp_skip)
  apply (subst AlernateD_singleton)
  apply (simp add: assms kleisli_lift2'_def kleisli_lift_alt_def ndesign_H1_H3 seq_r_H1_H3_closed)
  apply (simp add: ndesign_H1_H3 pemp_skip)
  by simp

(*
lemma IteratePD_mono_refine:
  assumes 
    "\<And> i. P i is \<^bold>N" "\<And> i. Q i is \<^bold>N"
    "\<And> i. P i \<sqsubseteq> Q i"
  shows "(do i\<in>A \<bullet> g(i) \<rightarrow> P(i) od) \<sqsubseteq> (do i\<in>A \<bullet> g(i) \<rightarrow> Q(i) od)"
  apply (simp add: IteratePD_def ndes_theory.utp_lfp_def)
  apply (subst ndes_theory.utp_lfp_def)
  apply (simp_all add: closure assms)
  apply (subst ndes_theory.utp_lfp_def)
  apply (simp_all add: closure assms)
  apply (rule gfp_mono)
  apply (rule AlternateD_mono_refine)
  apply (simp_all add: closure seqr_mono assms)
done

lemma IterateD_single_refine:
  assumes 
    "P is \<^bold>N" "Q is \<^bold>N" "P \<sqsubseteq> Q"
  shows "(do g \<rightarrow> P od) \<sqsubseteq> (do g \<rightarrow> Q od)"
oops
*)
(*
lemma IteratePD_refine_intro:
  fixes V :: "(nat, 'a) uexpr"
  assumes "vwb_lens w"
  shows
  "I \<turnstile>\<^sub>n (w:[\<lceil>I \<and> \<not> (\<Or> i\<in>A \<bullet> g(i))\<rceil>\<^sub>>]) \<sqsubseteq> 
   do i\<in>A \<bullet> g(i) \<rightarrow> (I \<and> g(i)) \<turnstile>\<^sub>n (w:[\<lceil>I\<rceil>\<^sub>> \<and> \<lceil>V\<rceil>\<^sub>> <\<^sub>u \<lceil>V\<rceil>\<^sub><]) od"
proof (cases "A = {}")
  case True
  with assms show ?thesis
    by (simp add: IterateD_empty, rel_auto)
next
  case False
  then show ?thesis
  using assms
    apply (simp add: IterateD_def)
    apply (rule ndesign_mu_wf_refine_intro[where e=V and R="{(x, y). x < y}"])
    apply (simp_all add: wf closure)
    apply (simp add: ndes_simp unrest)
    apply (rule ndesign_refine_intro)
    apply (rel_auto)
    apply (rel_auto)
    apply (metis mwb_lens.put_put vwb_lens_mwb)
  done
qed
  
lemma IterateD_single_refine_intro:
  fixes V :: "(nat, 'a) uexpr"
  assumes "vwb_lens w"
  shows
  "I \<turnstile>\<^sub>n (w:[\<lceil>I \<and> \<not> g\<rceil>\<^sub>>]) \<sqsubseteq> 
   do g \<rightarrow> ((I \<and> g) \<turnstile>\<^sub>n (w:[\<lceil>I\<rceil>\<^sub>> \<and> \<lceil>V\<rceil>\<^sub>> <\<^sub>u \<lceil>V\<rceil>\<^sub><])) od"
  apply (rule order_trans)
  defer
   apply (rule IterateD_refine_intro[of w "{0}" "\<lambda> i. g" I V, simplified, OF assms(1)])
  oops
*)

subsection \<open> Recursion \<close>

end
