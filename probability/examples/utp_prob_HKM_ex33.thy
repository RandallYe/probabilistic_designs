section \<open> Example 3.3 in He's paper "Probabilistic models for the Guarded Command Language" \<close>

theory utp_prob_HKM_ex33
  imports
  "../utp_prob_des_laws"
begin recall_syntax

subsection \<open> State space \<close>
alphabet state = 
  x :: "int"
  y :: "int"

subsection \<open> P \<close>
abbreviation P' :: "(state, state) rel_pdes" where
  "P' \<equiv> (\<K>(x :=\<^sub>D 0) \<sqinter> \<K>(x :=\<^sub>D 1))"

abbreviation P :: "(state, state) rel_pdes" where
  "P \<equiv> \<K>((x :=\<^sub>D 0) \<sqinter> (x :=\<^sub>D 1))"

lemma P_alt:
  "P = P' \<sqinter> 
      (\<Sqinter> r \<in> {0<..<1} \<bullet> 
        (U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>0/$x\<rbrakk>) = 1)) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>1/$x\<rbrakk>) = 1))))"
  apply (subst pemb_intchoice')
  apply (simp add: assigns_d_H1_H3)+
  by (simp add: prob_choice_inf_simp pemp_assign)

lemma P_alt':
  "P = P' \<sqinter> 
      (\<^bold>\<exists> r \<in> U({0<..<1}) \<bullet> 
        (U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>0/$x\<rbrakk>) = 1)) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>1/$x\<rbrakk>) = 1))))"
  apply (simp add: P_alt)  
  by (simp add: inf_is_exists)

subsection \<open> Q \<close>
abbreviation Q :: "(state, state) rel_pdes" where
  "Q \<equiv> (\<K>(y :=\<^sub>D 0) \<oplus>\<^bsub>(0.5)\<^esub> \<K>(y :=\<^sub>D 1))"

lemma Q_alt:
  "Q = (\<^U>(true) \<turnstile>\<^sub>n U($prob\<acute>($\<^bold>v\<lbrakk>0/$y\<rbrakk>) = 0.5 \<and> $prob\<acute>($\<^bold>v\<lbrakk>1/$y\<rbrakk>) = 0.5))"
  apply (simp add: pemp_assign prob_choice_r)
  apply (simp add: ndes_par)
  apply (rule ndesign_eq_intro)
  apply (simp)
  apply (rel_auto)
proof -
  fix x\<^sub>v:: "int" and prob\<^sub>v':: "state pmf"
      and prob\<^sub>v''::"state pmf"
  assume a1: "pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> = (1::real)"
  assume a2: "pmf prob\<^sub>v'' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> = (1::real)"
  have "pmf prob\<^sub>v'' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> = (0::real)"
    apply (rule pmf_not_the_one_is_zero[of _ "\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>"])
    apply (simp add: a2)
    by simp
  then show "pmf (prob\<^sub>v' +\<^bsub>(1::real) / (2::real)\<^esub> prob\<^sub>v'') 
        \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real)"
    apply (simp add: pmf_wplus)
    using a1 by blast
next
  fix x\<^sub>v:: "int" and prob\<^sub>v':: "state pmf"
      and prob\<^sub>v''::"state pmf"
  assume a1: "pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> = (1::real)"
  assume a2: "pmf prob\<^sub>v'' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> = (1::real)"
  have "pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> = (0::real)"
    apply (rule pmf_not_the_one_is_zero[of _ "\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>"])
    apply (simp add: a1)
    by simp
  then show "pmf (prob\<^sub>v' +\<^bsub>(1::real) / (2::real)\<^esub> prob\<^sub>v'') 
        \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real)"
    apply (simp add: pmf_wplus)
    using a2 by blast
next
  fix x\<^sub>v::"int" and y\<^sub>v::"int" and prob\<^sub>v::"state pmf"
  assume a1: "pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real)"
  assume a2: "pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real)"
  have f0: "\<forall>s. s \<noteq> \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> \<and> s \<noteq> \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> \<longrightarrow>
          pmf prob\<^sub>v s = 0"
    apply (auto)
    proof -
      fix s::"state"
      assume a11: "\<not> s = \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>"
      assume a12: "\<not> s = \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>"
      show "pmf prob\<^sub>v s = (0::real)"
      proof (rule ccontr)
        assume a111: "\<not> pmf prob\<^sub>v s = (0::real)"
        then have f11: "pmf prob\<^sub>v s > 0"
          by simp
        have "(\<Sum>\<^sub>a a. pmf prob\<^sub>v a) \<ge> (\<Sum>\<^sub>a a \<in> {s, \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, 
            \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>}. pmf prob\<^sub>v a)"
          by (metis measure_pmf.prob_le_1 measure_pmf_conv_infsetsum sum_pmf_eq_1)
        then have "(\<Sum>\<^sub>a a. pmf prob\<^sub>v a) > 1"
          using f11 a1 a2 a11 a12 by auto
        then show "False"
          by (simp add: sum_pmf_eq_1)
      qed
    qed
  have f1: "\<forall>s. pmf prob\<^sub>v s =
    pmf ( pmf_of_set
     {\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>} +\<^bsub>(1::real) / (2::real)\<^esub> pmf_of_set {\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>}) s"
    apply (auto)
    apply (simp add: pmf_wplus)
    using a1 a2 f0 
    by (smt field_sum_of_halves indicator_simps(1) indicator_simps(2) singletonD singletonI state.ext_inject)
  show "\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int) prob\<^sub>v'::state pmf.
          pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> = (1::real) \<and>
          (\<exists>prob\<^sub>v''::state pmf.
              pmf prob\<^sub>v'' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> = (1::real) \<and>
              x\<^sub>v' = x\<^sub>v \<and> y\<^sub>v' = y\<^sub>v \<and> prob\<^sub>v = prob\<^sub>v' +\<^bsub>(1::real) / (2::real)\<^esub> prob\<^sub>v'')"
    apply (rule_tac x = "x\<^sub>v" in exI)
    apply (rule_tac x = "y\<^sub>v" in exI)
    apply (rule_tac x = "pmf_of_set {\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>}" in exI)
    apply (simp)
    apply (rule_tac x = "pmf_of_set {\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>}" in exI)
    apply (simp)
    using f1 pmf_eqI by blast
qed

lemma Q_refines:
  "U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>0/$y\<rbrakk>) = 0.5 \<and> $prob\<acute>($\<^bold>v\<lbrakk>1/$y\<rbrakk>) = 0.5)) \<sqsubseteq> Q"
  apply (subst Q_alt)
  by (simp)

subsection \<open> P ;; Q \<close>
lemma PQ_simp_1: "(P ;; \<up> Q) = (\<K>(x :=\<^sub>D 0) ;; \<up> Q)  \<sqinter> ((\<K>(x :=\<^sub>D 1)) ;; \<up> Q) \<sqinter> 
      (\<Sqinter> r \<in> {0<..<1} \<bullet> 
        ((U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>0/$x\<rbrakk>) = 1)) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>1/$x\<rbrakk>) = 1))) ;; \<up> Q))"
  apply (simp add: P_alt)
  apply (simp add: seqr_inf_distl)
  by (simp add: seq_UINF_distr)

lemma shEx_lift_seq_real:
  "((\<^bold>\<exists> r::real \<in> U({0<..<1}) \<bullet> PP r) ;; QQ) = (\<^bold>\<exists> r::real \<in> U({0<..<1}) \<bullet> (PP r ;; QQ))"
  by (rel_auto)

lemma PQ_simp_1': "(P ;; \<up> Q) = (\<K>(x :=\<^sub>D 0) ;; \<up> Q)  \<sqinter> ((\<K>(x :=\<^sub>D 1)) ;; \<up> Q) \<sqinter> 
      (\<^bold>\<exists> r \<in> U({0<..<1}) \<bullet> 
        ((U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>0/$x\<rbrakk>) = 1)) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>1/$x\<rbrakk>) = 1))) ;; \<up> Q))"
  apply (simp add: P_alt')
  apply (simp add: seqr_inf_distl)
  by (simp add: shEx_lift_seq_real)

lemma PQ_x0_simp: 
  "(\<K>(x :=\<^sub>D 0) ;; \<up> Q) = U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>0,0/$x,$y\<rbrakk>) = 0.5 \<and> $prob\<acute>($\<^bold>v\<lbrakk>0,1/$x,$y\<rbrakk>) = 0.5))"
  apply (subst Q_alt)
  apply (simp add: kleisli_lift_alt_def kleisli_lift2'_def pemp_assign)
  apply (ndes_simp)
  apply (rule ndesign_eq_intro)
  apply (rel_simp)
  apply (metis (full_types) Collect_cong lit.rep_eq order_top_class.top.extremum_unique top1I 
      top_set_def upred_ref_iff upred_set.rep_eq sum_pmf_eq_1)
  apply (rel_auto)
  proof -
    fix y\<^sub>v::"int" and prob\<^sub>v::"state pmf" and
       prob\<^sub>v'::"state pmf" and x::"state \<Rightarrow> state pmf"
    assume a1: "pmf prob\<^sub>v' \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real)"
    assume a2: "\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
          pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> =
          (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>)" 
    assume a3: "\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
          (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
          (\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
    have f1: "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>)
      = (pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>)"
      apply (rule pmf_sum_singleton_is_single)
      using a1 by blast
    from a3 have "(\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v =0::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
      using a1 by simp
    then have 
      "pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
       pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v =0::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real)"
      by blast
    then show "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>) \<cdot> (2::real) =
       (1::real)"
      using f1 by simp
  next
    fix y\<^sub>v::"int" and prob\<^sub>v::"state pmf" and
       prob\<^sub>v'::"state pmf" and x::"state \<Rightarrow> state pmf"
    assume a1: "pmf prob\<^sub>v' \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real)"
    assume a2: "\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
          pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> =
          (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>)" 
    assume a3: "\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
          (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
          (\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
    have f1: "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>)
      = (pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>)"
      apply (rule pmf_sum_singleton_is_single)
      using a1 by blast
    from a3 have "(\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v =0::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
      using a1 by simp
    then have 
      "pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
       pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v =0::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real)"
      by blast
    then show "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>) \<cdot> (2::real) =
       (1::real)"
      using f1 by simp
  next
    fix y\<^sub>v::"int" and prob\<^sub>v::"state pmf"
    assume a1: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real)"
    assume a2: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real)"
    show "\<exists>prob\<^sub>v'::state pmf.
          pmf prob\<^sub>v' \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<and>
          (\<exists>x::state \<Rightarrow> state pmf.
              (\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
                  pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> =
                  (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>)) \<and>
              (\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
                  (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
                  (\<forall>prob\<^sub>v::state pmf.
                      pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
                      pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
                      (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                          \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                             pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))))"
      apply (rule_tac x = "pmf_of_set {\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>}" in exI)
      apply (auto)
      apply (rule_tac x = "\<lambda>s. if s = \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> 
        then pmf_of_list [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>, 0.5), 
                          (\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>, 0.5)] 
        else pmf_of_set {\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>}" in exI) (* This can be any pmf *)
      apply (auto)
      defer
      apply (subst pmf_pmf_of_list)
      apply (simp add: pmf_of_list_wf_def)
      apply simp
      apply (subst pmf_pmf_of_list)
      apply (simp add: pmf_of_list_wf_def)
      apply simp
      proof -
        fix x\<^sub>v::"int" and y\<^sub>v'::"int"
        have f1: "(\<Sum>\<^sub>ax::state.
          indicat_real {\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>} x \<cdot>
          pmf (if x = \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>
               then pmf_of_list
                     [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>, (5::real) / (10::real)),
                      (\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>, (5::real) / (10::real))]
               else pmf_of_set {\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>})
           \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>) 
          = (pmf (pmf_of_list
                     [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>, (5::real) / (10::real)),
                      (\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>, (5::real) / (10::real))])
           \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>)"
          apply (subst infsum_singleton_is_single[where xa="\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>"])
          apply auto[1]
          by simp
        show "pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> =
         (\<Sum>\<^sub>ax::state.
            indicat_real {\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>} x \<cdot>
            pmf (if x = \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>
                 then pmf_of_list
                       [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>, (5::real) / (10::real)),
                        (\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>, (5::real) / (10::real))]
                 else pmf_of_set {\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>})
             \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>)"
            proof (cases "x\<^sub>v = (0::int) \<and> y\<^sub>v' = (0::int)")
              case True
              show ?thesis
                apply (simp add: f1)
                using True apply (subst pmf_pmf_of_list)
                apply (simp add: pmf_of_list_wf_def)
                using a1 by simp
            next
              case False
              then have f: "\<not>(x\<^sub>v = (0::int) \<and> y\<^sub>v' = (0::int))"
                by auto
              then show ?thesis 
                proof (cases "x\<^sub>v = (0::int) \<and> y\<^sub>v' = (1::int)")
                  case True
                  show ?thesis
                    apply (simp add: f1)
                    apply (subst pmf_pmf_of_list)
                    apply (simp add: pmf_of_list_wf_def)
                    using a2 True by simp
                next
                  case False
                  then have ff: "\<not>(x\<^sub>v = (0::int) \<and> y\<^sub>v' = (1::int))"
                    by auto
                  then have ff1: "\<not>(x\<^sub>v = (0::int)) \<or> \<not>(y\<^sub>v' = (1::int) \<or> y\<^sub>v' = (0::int))"
                    using f by blast
                  have ff2: "pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> = 0"
                    proof (rule ccontr)
                      assume ff2_a: "\<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> = 0"
                      have ff2_1: "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v a) \<ge> 
                        (\<Sum>\<^sub>aa::state\<in>{\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>,
                          \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>, \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>}. 
                          pmf prob\<^sub>v a)"
                        by (metis measure_pmf.prob_le_1 measure_pmf_conv_infsetsum 
                                  sum_pmf_eq_1)
                      have ff2_2: "(\<Sum>\<^sub>aa::state\<in>{\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>,
                          \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>, \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>}. 
                          pmf prob\<^sub>v a) = 
                          pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> + 
                          pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> + 
                          pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>"
                        using f ff finite.insertI finite.intros(1) infsetsum_finite insert_absorb insert_iff by force
                      have ff2_3: "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v a) > 1"
                        using ff2_1 ff2_2 ff2_a a1 a2 pmf_pos by fastforce
                      show False
                        using ff2_3 by (simp add: sum_pmf_eq_1)
                    qed
                  show ?thesis
                    apply (simp add: f1)
                    apply (subst pmf_pmf_of_list)
                    apply (simp add: pmf_of_list_wf_def)
                    using ff2 ff1 by auto
                qed
            qed
      qed
  qed

declare [[ smt_timeout = 1200 ]]

lemma PQ_x1_simp:
  "(\<K>(x :=\<^sub>D 1) ;; \<up> Q) = U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>1,0/$x,$y\<rbrakk>) = 0.5 \<and> $prob\<acute>($\<^bold>v\<lbrakk>1,1/$x,$y\<rbrakk>) = 0.5))"
  apply (subst Q_alt)
  apply (simp add: kleisli_lift_alt_def kleisli_lift2'_def pemp_assign)
  apply (ndes_simp)
  apply (rule ndesign_eq_intro)
  apply (rel_simp)
  apply (metis (full_types) Collect_cong lit.rep_eq order_top_class.top.extremum_unique top1I 
      top_set_def upred_ref_iff upred_set.rep_eq sum_pmf_eq_1)
  apply (rel_auto)
  proof -
    fix y\<^sub>v::"int" and prob\<^sub>v::"state pmf" and
       prob\<^sub>v'::"state pmf" and x::"state \<Rightarrow> state pmf"
    assume a1: "pmf prob\<^sub>v' \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real)"
    assume a2: "\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
          pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> =
          (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>)" 
    assume a3: "\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
          (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
          (\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
    have f1: "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>)
      = (pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>)"
      apply (rule pmf_sum_singleton_is_single)
      using a1 by blast
    from a3 have "(\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
      using a1 by simp
    then have 
      "pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
       pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real)"
      by blast
    then show "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>) \<cdot> (2::real) =
       (1::real)"
      using f1 by simp
  next
    fix y\<^sub>v::"int" and prob\<^sub>v::"state pmf" and
       prob\<^sub>v'::"state pmf" and x::"state \<Rightarrow> state pmf"
    assume a1: "pmf prob\<^sub>v' \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real)"
    assume a2: "\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
          pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> =
          (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>)" 
    assume a3: "\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
          (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
          (\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
    have f1: "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>)
      = (pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>)"
      apply (rule pmf_sum_singleton_is_single)
      using a1 by blast
    from a3 have "(\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
      using a1 by simp
    then have 
      "pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
       pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real)"
      by blast
    then show "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>) \<cdot> (2::real) =
       (1::real)"
      using f1 by simp
  next
    fix y\<^sub>v::"int" and prob\<^sub>v::"state pmf"
    assume a1: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real)"
    assume a2: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real)"
    show "\<exists>prob\<^sub>v'::state pmf.
          pmf prob\<^sub>v' \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<and>
          (\<exists>x::state \<Rightarrow> state pmf.
              (\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
                  pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> =
                  (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>)) \<and>
              (\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
                  (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
                  (\<forall>prob\<^sub>v::state pmf.
                      pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
                      pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
                      (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                          \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                             pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))))"
      apply (rule_tac x = "pmf_of_set {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}" in exI)
      apply (auto)
      apply (rule_tac x = "\<lambda>s. if s = \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> 
        then pmf_of_list [(\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>, 0.5), 
                          (\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>, 0.5)] 
        else pmf_of_set {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>}" in exI) (* This can be any pmf *)
      apply (auto)
      defer
      apply (subst pmf_pmf_of_list)
      apply (simp add: pmf_of_list_wf_def)
      apply simp
      apply (subst pmf_pmf_of_list)
      apply (simp add: pmf_of_list_wf_def)
      apply simp
      proof -
        fix x\<^sub>v::"int" and y\<^sub>v'::"int"
        have f1: "(\<Sum>\<^sub>ax::state.
          indicat_real {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>} x \<cdot>
          pmf (if x = \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>
               then pmf_of_list
                     [(\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>, (5::real) / (10::real)),
                      (\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>, (5::real) / (10::real))]
               else pmf_of_set {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>})
           \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>) 
          = (pmf (pmf_of_list
                     [(\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>, (5::real) / (10::real)),
                      (\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>, (5::real) / (10::real))])
           \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>)"
          apply (subst infsum_singleton_is_single[where xa="\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>"])
          apply auto[1]
          by simp
        show "pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> =
         (\<Sum>\<^sub>ax::state.
            indicat_real {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>} x \<cdot>
            pmf (if x = \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>
                 then pmf_of_list
                       [(\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>, (5::real) / (10::real)),
                        (\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>, (5::real) / (10::real))]
                 else pmf_of_set {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>})
             \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>)"
            proof (cases "x\<^sub>v = (1::int) \<and> y\<^sub>v' = (0::int)")
              case True
              show ?thesis
                apply (simp add: f1)
                using True apply (subst pmf_pmf_of_list)
                apply (simp add: pmf_of_list_wf_def)
                using a1 by simp
            next
              case False
              then have f: "\<not>(x\<^sub>v = (1::int) \<and> y\<^sub>v' = (0::int))"
                by auto
              then show ?thesis 
                proof (cases "x\<^sub>v = (1::int) \<and> y\<^sub>v' = (1::int)")
                  case True
                  show ?thesis
                    apply (simp add: f1)
                    apply (subst pmf_pmf_of_list)
                    apply (simp add: pmf_of_list_wf_def)
                    using a2 True by simp
                next
                  case False
                  then have ff: "\<not>(x\<^sub>v = (1::int) \<and> y\<^sub>v' = (1::int))"
                    by auto
                  then have ff1: "\<not>(x\<^sub>v = (1::int)) \<or> \<not>(y\<^sub>v' = (1::int) \<or> y\<^sub>v' = (0::int))"
                    using f by blast
                  have ff2: "pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> = 0"
                    proof (rule ccontr)
                      assume ff2_a: "\<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> = 0"
                      have ff2_1: "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v a) \<ge> 
                        (\<Sum>\<^sub>aa::state\<in>{\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>,
                          \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>, \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>}. 
                          pmf prob\<^sub>v a)"
                        by (metis measure_pmf.prob_le_1 measure_pmf_conv_infsetsum 
                                  sum_pmf_eq_1)
                      have ff2_2: "(\<Sum>\<^sub>aa::state\<in>{\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>,
                          \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>, \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>}. 
                          pmf prob\<^sub>v a) = 
                          pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> + 
                          pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> + 
                          pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>"
                        using f ff finite.insertI finite.intros(1) infsetsum_finite insert_absorb insert_iff by force
                      have ff2_3: "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v a) > 1"
                        using ff2_1 ff2_2 ff2_a a1 a2 pmf_pos by fastforce
                      show False
                        using ff2_3 by (simp add: sum_pmf_eq_1)
                    qed
                  show ?thesis
                    apply (simp add: f1)
                    apply (subst pmf_pmf_of_list)
                    apply (simp add: pmf_of_list_wf_def)
                    using ff2 ff1 by auto
                qed
            qed
      qed
  qed

lemma P'Q_x_r_simp:
  assumes "r \<in> {0<..<1}"
  shows "((U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>0/$x\<rbrakk>) = 1)) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>1/$x\<rbrakk>) = 1))) ;; \<up> Q)
  = U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>0,0/$x,$y\<rbrakk>) = 0.5*\<guillemotleft>r\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>0,1/$x,$y\<rbrakk>) = 0.5*\<guillemotleft>r\<guillemotright> \<and>
      $prob\<acute>($\<^bold>v\<lbrakk>1,0/$x,$y\<rbrakk>) = 0.5*\<guillemotleft>1-r\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>1,1/$x,$y\<rbrakk>) = 0.5*\<guillemotleft>1-r\<guillemotright>))"
  apply (subst Q_alt)
  apply (simp add: kleisli_lift_alt_def kleisli_lift2'_def pemp_assign)
  apply (ndes_simp)
  apply (rule ndesign_eq_intro)
  apply (rel_simp)
  apply (metis (full_types) Collect_cong lit.rep_eq order_top_class.top.extremum_unique top1I 
      top_set_def upred_ref_iff upred_set.rep_eq sum_pmf_eq_1)
  apply (rel_auto)
  proof -
    fix y\<^sub>v::"int" and prob\<^sub>v::"state pmf" and
       x::"state \<Rightarrow> state pmf" and
       prob\<^sub>v''::"state pmf" and prob\<^sub>v'''::"state pmf"
    assume a1: "\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
          pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> =
          (\<Sum>\<^sub>aa::state. pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') a \<cdot> pmf (x a) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>)" 
    assume a2: "\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
          (0::real) < pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
          (\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
    assume a3: "pmf prob\<^sub>v'' \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real)"
    assume a4: "pmf prob\<^sub>v''' \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real)"
    let ?f = "\<lambda>a. (if a = \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> 
             then pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> * r
             else (if a = \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> 
                then pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> *(1-r)
                else 0))"
    have f0: "\<forall>a. (pmf prob\<^sub>v'' a * pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> * r 
                + pmf prob\<^sub>v''' a * pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> *(1-r))
          = ?f a"
      using a3 a4 pmf_not_the_one_is_zero by fastforce

    have f1: "(\<Sum>\<^sub>aa::state. pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') a \<cdot> 
                    pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>) =
      (\<Sum>\<^sub>aa::state. (pmf prob\<^sub>v'' a * pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> * r 
                + pmf prob\<^sub>v''' a * pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> *(1-r)))"
      using assms apply (simp add: pmf_wplus)
      by (simp add: mult.assoc mult.commute)
  
    have f2: "... = (\<Sum>\<^sub>aa::state. ?f a)"
      using f0 by auto
    have f3: "... = (\<Sum>\<^sub>aa::state\<in>
          ({\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>} \<union> {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>} \<union>
          {t. t \<noteq> \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> \<and> t \<noteq> \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}). 
            ?f a)"
      apply (subgoal_tac "({\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>} \<union> {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>} \<union>
          {t. t \<noteq> \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> \<and> t \<noteq> \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}) = UNIV")
      apply auto[1]
      by blast
    have f4: "... = (\<Sum>\<^sub>aa::state\<in> 
          ({\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}). ?f a) + 
                    (\<Sum>\<^sub>aa::state\<in> ({t. t \<noteq> \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> \<and> 
                    t \<noteq> \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}). ?f a)"
      unfolding infsetsum_altdef abs_summable_on_altdef
      apply (subst set_integral_Un, auto)
      using abs_summable_on_altdef apply fastforce
      using abs_summable_on_altdef abs_summable_on_0 abs_summable_on_cong mem_Collect_eq
      apply smt
      by (simp add: insert_commute)
    have f5: "... = (\<Sum>\<^sub>aa::state\<in> 
          ({\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}). ?f a)"
      by (smt infsetsum_all_0 mem_Collect_eq)
    have f6: "... = (\<Sum>\<^sub>aa::state\<in> ({\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>}). ?f a) + 
                    (\<Sum>\<^sub>aa::state\<in> ({\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}). ?f a)"
      unfolding infsetsum_altdef abs_summable_on_altdef
      by (smt finite.insertI finite.intros(1) infsetsum_altdef' infsetsum_finite insert_absorb 
          insert_commute order_top_class.top_greatest singletonD state.ext_inject sum.empty sum.insert)
    have f7: "... = 
         pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> * r +
         pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> *(1-r)"
      by simp

    have f8: "(0::real) < pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>"
      using assms apply (simp add: pmf_wplus)
      using a3 a4 
      using pmf_not_the_one_is_zero by force
    have f9: "(0::real) < pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>"
      using assms apply (simp add: pmf_wplus)
      using a3 a4 
      using pmf_not_the_one_is_zero by force
    have f10: "(\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
      using a2 f8 by blast
    then have f11: "
      pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
      pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real)"
      by blast

    have f12: "(\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
      using a2 f9 by blast
    then have f13: "
      pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
      pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real)"
      by blast

    have f14: "pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> = 0"
      proof (rule ccontr)
        assume a11: "\<not> pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> = (0::real)"
        have "(\<Sum>\<^sub>aa::state. pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) a) \<ge> 
          (\<Sum>\<^sub>aa::state\<in>{\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>, 
           \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>, \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>}. 
            pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) a)"
          by (metis measure_pmf.prob_le_1 measure_pmf_conv_infsetsum sum_pmf_eq_1)
        then have "(\<Sum>\<^sub>aa::state. pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) a) > 1"
          using f13 a11 pmf_pos by fastforce
        then show "False"
          by (simp add: sum_pmf_eq_1)
      qed
    have f15: "pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> * r +
         pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> *(1-r) = 0.5*r"
      using f11 f14 by auto
    show "(\<Sum>\<^sub>aa::state. pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') a \<cdot> 
        pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>) \<cdot> (2::real) = r"
      using f1 f2 f3 f4 f5 f6 f7 f15 by linarith
  next
    fix y\<^sub>v::"int" and more::"'a" and prob\<^sub>v::"state pmf" and
       x::"state \<Rightarrow> state pmf" and
       prob\<^sub>v''::"state pmf" and prob\<^sub>v'''::"state pmf"
    assume a1: "\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
          pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> =
          (\<Sum>\<^sub>aa::state. pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') a \<cdot> pmf (x a) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>)" 
    assume a2: "\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
          (0::real) < pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
          (\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
    assume a3: "pmf prob\<^sub>v'' \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real)"
    assume a4: "pmf prob\<^sub>v''' \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real)"
    let ?f = "\<lambda>a. (if a = \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> 
             then pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> * r
             else (if a = \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> 
                then pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> *(1-r)
                else 0))"
    have f0: "\<forall>a. (pmf prob\<^sub>v'' a * pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> * r 
                + pmf prob\<^sub>v''' a * pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> *(1-r))
          = ?f a"
      using a3 a4 pmf_not_the_one_is_zero by fastforce

    have f1: "(\<Sum>\<^sub>aa::state. pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') a \<cdot> 
                    pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>) =
      (\<Sum>\<^sub>aa::state. (pmf prob\<^sub>v'' a * pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> * r 
                + pmf prob\<^sub>v''' a * pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> *(1-r)))"
      using assms apply (simp add: pmf_wplus)
      by (simp add: mult.assoc mult.commute)
  
    have f2: "... = (\<Sum>\<^sub>aa::state. ?f a)"
      using f0 by auto
    have f3: "... = (\<Sum>\<^sub>aa::state\<in>
          ({\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>} \<union> {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>} \<union>
          {t. t \<noteq> \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> \<and> t \<noteq> \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}). 
            ?f a)"
      apply (subgoal_tac "({\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>} \<union> {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>} \<union>
          {t. t \<noteq> \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> \<and> t \<noteq> \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}) = UNIV")
      apply auto[1]
      by blast
    have f4: "... = (\<Sum>\<^sub>aa::state\<in> 
          ({\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}). ?f a) + 
                    (\<Sum>\<^sub>aa::state\<in> ({t. t \<noteq> \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> \<and> 
                    t \<noteq> \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}). ?f a)"
      unfolding infsetsum_altdef abs_summable_on_altdef
      apply (subst set_integral_Un, auto)
      using abs_summable_on_altdef apply fastforce
      using abs_summable_on_altdef abs_summable_on_0 abs_summable_on_cong mem_Collect_eq
      apply smt
      by (simp add: insert_commute)
    have f5: "... = (\<Sum>\<^sub>aa::state\<in> 
          ({\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}). ?f a)"
      by (smt infsetsum_all_0 mem_Collect_eq)
    have f6: "... = (\<Sum>\<^sub>aa::state\<in> ({\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>}). ?f a) + 
                    (\<Sum>\<^sub>aa::state\<in> ({\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}). ?f a)"
      unfolding infsetsum_altdef abs_summable_on_altdef
      by (smt finite.insertI finite.intros(1) infsetsum_altdef' infsetsum_finite insert_absorb 
          insert_commute order_top_class.top_greatest singletonD state.ext_inject sum.empty sum.insert)
    have f7: "... = 
         pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> * r +
         pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> *(1-r)"
      by simp

    have f8: "(0::real) < pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>"
      using assms apply (simp add: pmf_wplus)
      using a3 a4 
      using pmf_not_the_one_is_zero by force
    have f9: "(0::real) < pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>"
      using assms apply (simp add: pmf_wplus)
      using a3 a4 
      using pmf_not_the_one_is_zero by force
    have f10: "(\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
      using a2 f8 by blast
    then have f11: "
      pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
      pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real)"
      by blast

    have f12: "(\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
      using a2 f9 by blast
    then have f13: "
      pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
      pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real)"
      by blast

    have f14: "pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> = 0"
      proof (rule ccontr)
        assume a11: "\<not> pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> = (0::real)"
        have "(\<Sum>\<^sub>aa::state. pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) a) \<ge> 
          (\<Sum>\<^sub>aa::state\<in>{\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>, 
           \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>, \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>}. 
            pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) a)"
          by (metis measure_pmf.prob_le_1 measure_pmf_conv_infsetsum sum_pmf_eq_1)
        then have "(\<Sum>\<^sub>aa::state. pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) a) > 1"
          using f13 a11 pmf_pos by fastforce
        then show "False"
          by (simp add: sum_pmf_eq_1)
      qed
    have f15: "pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> * r +
         pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> *(1-r) = 0.5*r"
      using f11 f14 by auto
    show "(\<Sum>\<^sub>aa::state. pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') a \<cdot> 
        pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>) \<cdot> (2::real) = r"
      using f1 f2 f3 f4 f5 f6 f7 f15 by linarith
  next
    fix y\<^sub>v::"int" and more::"'a" and prob\<^sub>v::"state pmf" and
       x::"state \<Rightarrow> state pmf" and
       prob\<^sub>v''::"state pmf" and prob\<^sub>v'''::"state pmf"
    assume a1: "\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
          pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> =
          (\<Sum>\<^sub>aa::state. pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') a \<cdot> pmf (x a) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>)" 
    assume a2: "\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
          (0::real) < pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
          (\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
    assume a3: "pmf prob\<^sub>v'' \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real)"
    assume a4: "pmf prob\<^sub>v''' \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real)"
    let ?f = "\<lambda>a. (if a = \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> 
             then pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> * r
             else (if a = \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> 
                then pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> *(1-r)
                else 0))"
    have f0: "\<forall>a. (pmf prob\<^sub>v'' a * pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> * r 
                + pmf prob\<^sub>v''' a * pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> *(1-r))
          = ?f a"
      using a3 a4 pmf_not_the_one_is_zero by fastforce

    have f1: "(\<Sum>\<^sub>aa::state. pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') a \<cdot> 
                    pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>) =
      (\<Sum>\<^sub>aa::state. (pmf prob\<^sub>v'' a * pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> * r 
                + pmf prob\<^sub>v''' a * pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> *(1-r)))"
      using assms apply (simp add: pmf_wplus)
      by (simp add: mult.assoc mult.commute)
  
    have f2: "... = (\<Sum>\<^sub>aa::state. ?f a)"
      using f0 by auto
    have f3: "... = (\<Sum>\<^sub>aa::state\<in>
          ({\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>} \<union> {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>} \<union>
          {t. t \<noteq> \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> \<and> t \<noteq> \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}). 
            ?f a)"
      apply (subgoal_tac "({\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>} \<union> {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>} \<union>
          {t. t \<noteq> \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> \<and> t \<noteq> \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}) = UNIV")
      apply auto[1]
      by blast
    have f4: "... = (\<Sum>\<^sub>aa::state\<in> 
          ({\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}). ?f a) + 
                    (\<Sum>\<^sub>aa::state\<in> ({t. t \<noteq> \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> \<and> 
                    t \<noteq> \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}). ?f a)"
      unfolding infsetsum_altdef abs_summable_on_altdef
      apply (subst set_integral_Un, auto)
      using abs_summable_on_altdef apply fastforce
      using abs_summable_on_altdef abs_summable_on_0 abs_summable_on_cong mem_Collect_eq
      apply smt
      by (simp add: insert_commute)
    have f5: "... = (\<Sum>\<^sub>aa::state\<in> 
          ({\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}). ?f a)"
      by (smt infsetsum_all_0 mem_Collect_eq)
    have f6: "... = (\<Sum>\<^sub>aa::state\<in> ({\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>}). ?f a) + 
                    (\<Sum>\<^sub>aa::state\<in> ({\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}). ?f a)"
      unfolding infsetsum_altdef abs_summable_on_altdef
      by (smt finite.insertI finite.intros(1) infsetsum_altdef' infsetsum_finite insert_absorb 
          insert_commute order_top_class.top_greatest singletonD state.ext_inject sum.empty sum.insert)
    have f7: "... = 
         pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> * r +
         pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> *(1-r)"
      by simp

    have f8: "(0::real) < pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>"
      using assms apply (simp add: pmf_wplus)
      using a3 a4 
      using pmf_not_the_one_is_zero by force
    have f9: "(0::real) < pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>"
      using assms apply (simp add: pmf_wplus)
      using a3 a4 
      using pmf_not_the_one_is_zero by force
    have f10: "(\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
      using a2 f8 by blast
    then have f11: "
      pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
      pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real)"
      by blast

    have f12: "(\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
      using a2 f9 by blast
    then have f13: "
      pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
      pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real)"
      by blast

    have f14: "pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> = 0"
      proof (rule ccontr)
        assume a11: "\<not> pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> = (0::real)"
        have "(\<Sum>\<^sub>aa::state. pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) a) \<ge> 
          (\<Sum>\<^sub>aa::state\<in>{\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>, 
           \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>, \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>}. 
            pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) a)"
          by (metis measure_pmf.prob_le_1 measure_pmf_conv_infsetsum sum_pmf_eq_1)
        then have "(\<Sum>\<^sub>aa::state. pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) a) > 1"
          using f11 a11 pmf_pos by fastforce
        then show "False"
          by (simp add: sum_pmf_eq_1)
      qed
    have f15: "(pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> * r +
         pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> *(1-r))
        \<cdot> (2::real) = (1::real) - r"
      using f13 f14 by auto
    show "(\<Sum>\<^sub>aa::state. pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>) \<cdot>
       (2::real) = (1::real) - r"
      using f1 f2 f3 f4 f5 f6 f7 f13 f14 f15 by (metis (no_types, lifting))
  next
    fix y\<^sub>v::"int" and more::"'a" and prob\<^sub>v::"state pmf" and
       x::"state \<Rightarrow> state pmf" and
       prob\<^sub>v''::"state pmf" and prob\<^sub>v'''::"state pmf"
    assume a1: "\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
          pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> =
          (\<Sum>\<^sub>aa::state. pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') a \<cdot> pmf (x a) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>)" 
    assume a2: "\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
          (0::real) < pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
          (\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
    assume a3: "pmf prob\<^sub>v'' \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real)"
    assume a4: "pmf prob\<^sub>v''' \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real)"
    let ?f = "\<lambda>a. (if a = \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> 
             then pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> * r
             else (if a = \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> 
                then pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> *(1-r)
                else 0))"
    have f0: "\<forall>a. (pmf prob\<^sub>v'' a * pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> * r 
                + pmf prob\<^sub>v''' a * pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> *(1-r))
          = ?f a"
      using a3 a4 pmf_not_the_one_is_zero by fastforce

    have f1: "(\<Sum>\<^sub>aa::state. pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') a \<cdot> 
                    pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>) =
      (\<Sum>\<^sub>aa::state. (pmf prob\<^sub>v'' a * pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> * r 
                + pmf prob\<^sub>v''' a * pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> *(1-r)))"
      using assms apply (simp add: pmf_wplus)
      by (simp add: mult.assoc mult.commute)
  
    have f2: "... = (\<Sum>\<^sub>aa::state. ?f a)"
      using f0 by auto
    have f3: "... = (\<Sum>\<^sub>aa::state\<in>
          ({\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>} \<union> {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>} \<union>
          {t. t \<noteq> \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> \<and> t \<noteq> \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}). 
            ?f a)"
      apply (subgoal_tac "({\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>} \<union> {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>} \<union>
          {t. t \<noteq> \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> \<and> t \<noteq> \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}) = UNIV")
      apply auto[1]
      by blast
    have f4: "... = (\<Sum>\<^sub>aa::state\<in> 
          ({\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}). ?f a) + 
                    (\<Sum>\<^sub>aa::state\<in> ({t. t \<noteq> \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> \<and> 
                    t \<noteq> \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}). ?f a)"
      unfolding infsetsum_altdef abs_summable_on_altdef
      apply (subst set_integral_Un, auto)
      using abs_summable_on_altdef apply fastforce
      using abs_summable_on_altdef abs_summable_on_0 abs_summable_on_cong mem_Collect_eq
      apply smt
      by (simp add: insert_commute)
    have f5: "... = (\<Sum>\<^sub>aa::state\<in> 
          ({\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}). ?f a)"
      by (smt infsetsum_all_0 mem_Collect_eq)
    have f6: "... = (\<Sum>\<^sub>aa::state\<in> ({\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>}). ?f a) + 
                    (\<Sum>\<^sub>aa::state\<in> ({\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}). ?f a)"
      unfolding infsetsum_altdef abs_summable_on_altdef
      by (smt finite.insertI finite.intros(1) infsetsum_altdef' infsetsum_finite insert_absorb 
          insert_commute order_top_class.top_greatest singletonD state.ext_inject sum.empty sum.insert)
    have f7: "... = 
         pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> * r +
         pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> *(1-r)"
      by simp

    have f8: "(0::real) < pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>"
      using assms apply (simp add: pmf_wplus)
      using a3 a4 
      using pmf_not_the_one_is_zero by force
    have f9: "(0::real) < pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>"
      using assms apply (simp add: pmf_wplus)
      using a3 a4 
      using pmf_not_the_one_is_zero by force
    have f10: "(\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
      using a2 f8 by blast
    then have f11: "
      pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
      pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real)"
      by blast

    have f12: "(\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
      using a2 f9 by blast
    then have f13: "
      pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
      pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real)"
      by blast

    have f14: "pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> = 0"
      proof (rule ccontr)
        assume a11: "\<not> pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> = (0::real)"
        have "(\<Sum>\<^sub>aa::state. pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) a) \<ge> 
          (\<Sum>\<^sub>aa::state\<in>{\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>, 
           \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>, \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>}. 
            pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) a)"
          by (metis measure_pmf.prob_le_1 measure_pmf_conv_infsetsum sum_pmf_eq_1)
        then have "(\<Sum>\<^sub>aa::state. pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) a) > 1"
          using f11 a11 pmf_pos by fastforce
        then show "False"
          by (simp add: sum_pmf_eq_1)
      qed
    have f15: "(pmf (x \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> * r +
         pmf (x \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> *(1-r))
        \<cdot> (2::real) = (1::real) - r"
      using f13 f14 by auto
    show "(\<Sum>\<^sub>aa::state. pmf (prob\<^sub>v'' +\<^bsub>r\<^esub> prob\<^sub>v''') a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>) \<cdot>
       (2::real) = (1::real) - r"
      using f1 f2 f3 f4 f5 f6 f7 f13 f14 f15 by (metis (no_types, lifting))
  next
    fix x\<^sub>v::"int" and y\<^sub>v::"int" and more::"'a" and prob\<^sub>v::"state pmf"
    let ?s00 = "\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>"
    let ?s01 = "\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>"
    let ?s10 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>"
    let ?s11 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>"
    assume a1: "r = pmf prob\<^sub>v ?s00 \<cdot> (2::real)"
    assume a2: "pmf prob\<^sub>v ?s01 = pmf prob\<^sub>v ?s00"
    assume a3: "pmf prob\<^sub>v ?s10 \<cdot> (2::real) = (1::real) - pmf prob\<^sub>v ?s00 \<cdot> (2::real)"
    assume a4: "pmf prob\<^sub>v ?s11 \<cdot> (2::real) = (1::real) - pmf prob\<^sub>v ?s00 \<cdot> (2::real)"
    have prob_is_1: "(\<Sum>\<^sub>aa::state\<in>{?s00, ?s01, ?s10, ?s11}. pmf prob\<^sub>v a) = 
      (\<Sum>\<^sub>aa::state\<in>{?s00}. pmf prob\<^sub>v a) + (\<Sum>\<^sub>aa::state\<in>{?s01}. pmf prob\<^sub>v a) + 
      (\<Sum>\<^sub>aa::state\<in>{?s10}. pmf prob\<^sub>v a) + (\<Sum>\<^sub>aa::state\<in>{?s11}. pmf prob\<^sub>v a)"
      by auto
    have prob_is_1': "... = 1"
      using a1 a2 a3 a4 by auto
    let ?prob\<^sub>v'' = "pmf_of_set {\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>}"
    let ?prob\<^sub>v''' = "pmf_of_set {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}"
    (* [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>, r), (\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>, 1-r)] *)
    let ?prob\<^sub>v' = "?prob\<^sub>v'' +\<^bsub>r\<^esub> ?prob\<^sub>v'''"
    (* [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>, 
          [(?s00, 0.25),
           (?s01, 0.25),
           (?s10, 0.25),
           (?s11, 0.25)]),
        (\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>, 
          [(?s00, 0.25),
           (?s01, 0.25),
           (?s10, 0.25),
           (?s11, 0.25)]] *)
    let ?pmf1 = "pmf_of_list [(?s00, 0.5), (?s01, 0.5)]"
    let ?pmf2 = "pmf_of_list [(?s10, 0.5), (?s11, 0.5)]"
    let ?x = "\<lambda>s. (if s = \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> 
                   then ?pmf1
                   else (if s = \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> 
                         then ?pmf2  
                         else pmf_of_set {?s11}))" (* not important *)
    show "\<exists>prob\<^sub>v'::state pmf.
          (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int) prob\<^sub>v''::state pmf.
              pmf prob\<^sub>v'' \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<and>
              (\<exists>prob\<^sub>v'''::state pmf.
                  pmf prob\<^sub>v''' \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<and>
                  x\<^sub>v' = x\<^sub>v \<and>
                  y\<^sub>v' = y\<^sub>v \<and>
                  prob\<^sub>v' = prob\<^sub>v'' +\<^bsub>pmf prob\<^sub>v ?s00 \<cdot> (2::real)\<^esub> prob\<^sub>v''')) \<and>
          (\<exists>x::state \<Rightarrow> state pmf.
              (\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
                  pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> =
                  (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>)) \<and>
              (\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
                  (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
                  (\<forall>prob\<^sub>v::state pmf.
                      pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
                      pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
                      (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                          \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                             pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))))"
      apply (rule_tac x = "?prob\<^sub>v'" in exI)
      apply (rule_tac conjI)
      apply (rule_tac x = "x\<^sub>v" in exI)
      apply (rule_tac x = "y\<^sub>v" in exI)
      apply (rule_tac x = "?prob\<^sub>v''" in exI, rule_tac conjI, simp)
      apply (rule_tac x = "?prob\<^sub>v'''" in exI, rule_tac conjI, simp, auto)
      using a1 apply blast
      apply (rule_tac x = "?x" in exI, rule_tac conjI)
      apply (rule allI)+
      proof -
        fix x\<^sub>v::"int" and y\<^sub>v'::"int"
        have f1: "\<forall>a. 
          pmf (?prob\<^sub>v'' +\<^bsub>r\<^esub> ?prob\<^sub>v''') a = 
          (if a = \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> 
           then r
           else if a = \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>
                then (1-r)
                else 0)"
          apply (subst pmf_wplus)
          using assms apply auto[1]
          by (auto)
        have f2: "\<forall>a. pmf (if a = \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>
                 then ?pmf1
                 else if a = \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>
                      then ?pmf2
                      else pmf_of_set {?s11})
             \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>
          = (if a = \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>
                 then pmf ?pmf1 \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>
                 else if a = \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>
                      then pmf ?pmf2 \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>
                      else pmf (pmf_of_set {?s11}) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>)"
          by simp
        have f3: "(\<Sum>\<^sub>aa::state.
            pmf (pmf_of_set
                  {\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>} +\<^bsub>r\<^esub> pmf_of_set {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>})
             a \<cdot>
            pmf (if a = \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>
                 then ?pmf1
                 else if a = \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>
                      then ?pmf2
                      else pmf_of_set {?s11})
             \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>) 
        = (\<Sum>\<^sub>aa::state.
            (if a = \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> 
             then r \<cdot> (pmf ?pmf1 \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>)
             else if a = \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>
                  then (1-r) \<cdot> (pmf ?pmf2 \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>)
                  else 0))"
          apply (simp add: f1 f2)
          by (smt distrib_right' infsetsum_cong)
        have f4: "... = r \<cdot> (pmf ?pmf1 \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>) + 
          (1-r) \<cdot> (pmf ?pmf2 \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>)"
          by (simp add: infsetsum_two)
        have f5: "pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> = 
          r \<cdot> (pmf ?pmf1 \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>) + (1-r) \<cdot> (pmf ?pmf2 \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>)" 
          proof (cases "x\<^sub>v = 0 \<and> y\<^sub>v' = 0")
            case True
            then show ?thesis
              apply (subst pmf_pmf_of_list)+
              apply (simp add: pmf_of_list_wf_def)+
              apply (subst pmf_pmf_of_list)+
              apply (simp add: pmf_of_list_wf_def)+
              using a2 a3 a4 a1 by blast
          next
            case False
            then have F: "\<not> (x\<^sub>v = 0 \<and> y\<^sub>v' = 0)"
              using False by simp
            show ?thesis 
              proof (cases "x\<^sub>v = 0 \<and> y\<^sub>v' = 1")
                case True
                then show ?thesis 
                  apply (subst pmf_pmf_of_list)+
                  apply (simp add: pmf_of_list_wf_def)+
                  apply (subst pmf_pmf_of_list)+
                  apply (simp add: pmf_of_list_wf_def)+
                  using a2 a3 a4 a1 by linarith
              next
                case False
                then have FF: "\<not> (x\<^sub>v = 0 \<and> y\<^sub>v' = 1)"
                  using False by simp
                then show ?thesis 
                  proof (cases "x\<^sub>v = 1 \<and> y\<^sub>v' = 0")
                    case True
                    then show ?thesis 
                      apply (subst pmf_pmf_of_list)+
                      apply (simp add: pmf_of_list_wf_def)+
                      apply (subst pmf_pmf_of_list)+
                      apply (simp add: pmf_of_list_wf_def)+
                      using a2 a3 a4 a1 by linarith
                  next
                    case False
                    then have FFF: "\<not> (x\<^sub>v = 1 \<and> y\<^sub>v' = 0)"
                      using False by simp
                    then show ?thesis 
                      proof (cases "x\<^sub>v = 1 \<and> y\<^sub>v' = 1")
                        case True
                        then show ?thesis 
                          apply (subst pmf_pmf_of_list)+
                          apply (simp add: pmf_of_list_wf_def)+
                          apply (subst pmf_pmf_of_list)+
                          apply (simp add: pmf_of_list_wf_def)+
                          using a2 a3 a4 a1 by linarith
                      next
                        case False
                        have f1: "pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> = 0"
                          apply (subst pmf_not_in_the_one_is_zero[where A="{?s00, ?s01, ?s10, ?s11}"])
                          using prob_is_1 prob_is_1' apply linarith
                          using False F FF FFF by auto
                        show ?thesis 
                          apply (subst pmf_pmf_of_list)+
                          apply (simp add: pmf_of_list_wf_def)+
                          apply (subst pmf_pmf_of_list)+
                          apply (simp add: pmf_of_list_wf_def)+
                          apply (subst pmf_pmf_of_list)+
                          apply (simp add: pmf_of_list_wf_def)+
                          apply (subst pmf_pmf_of_list)+
                          apply (simp add: pmf_of_list_wf_def)+
                          using FF FFF False a1 f1 by blast
                      qed
                  qed
              qed
          qed
        show "pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> =
         (\<Sum>\<^sub>aa::state.
            pmf (pmf_of_set
                  {\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>} +\<^bsub>r\<^esub> pmf_of_set {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>}) a \<cdot>
            pmf (if a = \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>
                 then ?pmf1
                 else if a = \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>
                      then ?pmf2
                      else pmf_of_set {?s11})
             \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>)"
        proof -
          have "r \<cdot> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> + pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> \<cdot> (1 - r) 
            = pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>"
            by (metis (no_types) add.commute diff_add_cancel distrib_left mult.commute 
                mult.right_neutral)
          then show ?thesis
            by (simp add: f3 f4 f5 mult.commute)
        qed
      next
        have f1: "\<forall>(x\<^sub>v::int) (y\<^sub>v'::int). 
          (0::real) < pmf (pmf_of_set {\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>} +\<^bsub>r\<^esub> pmf_of_set {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>})
          \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> \<longrightarrow> ((x\<^sub>v = (0::int) \<or> x\<^sub>v = (1::int)) \<and> y\<^sub>v' = y\<^sub>v)"
          apply (subst pmf_wplus)
          using assms apply auto[1]
          using less_le by fastforce
        show "\<forall>(x\<^sub>v::int) (y\<^sub>v'::int).
          (0::real) < pmf (pmf_of_set {\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>} +\<^bsub>r\<^esub> pmf_of_set {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>})
          \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> \<longrightarrow>
         (\<forall>prob\<^sub>v::state pmf.
             pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
             pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<or>
             (\<exists>(x\<^sub>v'::int) (y\<^sub>v''::int).
                 \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v''\<rparr> =
                    pmf (if \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> = \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>
                         then ?pmf1
                         else if \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> = \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>
                              then ?pmf2
                              else pmf_of_set {?s11})
                     \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v''\<rparr>))"
          apply (rule allI)+
          apply (auto)+
          apply (subst pmf_pmf_of_list)+
          apply (simp add: pmf_of_list_wf_def)+
          apply (subst pmf_pmf_of_list)+
          apply (simp add: pmf_of_list_wf_def)+
          apply (subst pmf_pmf_of_list)+
          apply (simp add: pmf_of_list_wf_def)+
          apply (subst pmf_pmf_of_list)+
          apply (simp add: pmf_of_list_wf_def)+
          using f1 by blast+
      qed
qed

lemma bounded_ex_eq:
  assumes "\<forall>r \<in> s. PP r = QQ \<guillemotleft>r\<guillemotright>"
  shows "(\<^bold>\<exists> r \<in> \<guillemotleft>s\<guillemotright> \<bullet> PP r) = (\<^bold>\<exists> r \<in> \<guillemotleft>s\<guillemotright> \<bullet> QQ \<guillemotleft>r\<guillemotright>)"
  using assms by(rel_auto)

lemma bounded_ex_eq':
  assumes "\<forall>r \<in> {0<..<1}. PP r = QQ r"
  shows "(\<^bold>\<exists> r \<in> U({0<..<1}) \<bullet> PP r) = (\<^bold>\<exists> r \<in> U({0<..<1}) \<bullet> QQ r)"
  using assms by(rel_auto)

lemma P'Q_x_r_simp':
  "(\<^bold>\<exists> r \<in> U({0<..<1}) \<bullet> 
        ((U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>0/$x\<rbrakk>) = 1)) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>1/$x\<rbrakk>) = 1))) ;; \<up> Q))
  = (\<^bold>\<exists> r \<in> U({0<..<1}) \<bullet> 
  U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>0,0/$x,$y\<rbrakk>) = 0.5*\<guillemotleft>r\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>0,1/$x,$y\<rbrakk>) = 0.5*\<guillemotleft>r\<guillemotright> \<and>
      $prob\<acute>($\<^bold>v\<lbrakk>1,0/$x,$y\<rbrakk>) = 0.5*\<guillemotleft>1-r\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>1,1/$x,$y\<rbrakk>) = 0.5*\<guillemotleft>1-r\<guillemotright>)))"
  apply (subst bounded_ex_eq'[where 
    QQ = "\<lambda>r. U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>0,0/$x,$y\<rbrakk>) = 0.5*\<guillemotleft>r\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>0,1/$x,$y\<rbrakk>) = 0.5*\<guillemotleft>r\<guillemotright> \<and>
      $prob\<acute>($\<^bold>v\<lbrakk>1,0/$x,$y\<rbrakk>) = 0.5*\<guillemotleft>1-r\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>1,1/$x,$y\<rbrakk>) = 0.5*\<guillemotleft>1-r\<guillemotright>))"])
  using P'Q_x_r_simp apply blast
  by auto

lemma P'Q_simp:
  "(P' ;; \<up> Q) = 
  U(true \<turnstile>\<^sub>n (($prob\<acute>($\<^bold>v\<lbrakk>0,0/$x,$y\<rbrakk>) = 0.5 \<and> $prob\<acute>($\<^bold>v\<lbrakk>0,1/$x,$y\<rbrakk>) = 0.5) 
          \<or> ($prob\<acute>($\<^bold>v\<lbrakk>1,0/$x,$y\<rbrakk>) = 0.5 \<and> $prob\<acute>($\<^bold>v\<lbrakk>1,1/$x,$y\<rbrakk>) = 0.5)))"
  using PQ_x0_simp PQ_x1_simp seqr_inf_distl ndesign_choice
  by (metis utp_pred_laws.inf_top_right)

lemma P'Q_prob_xy_equal:
  "U(true \<turnstile>\<^sub>n (($prob\<acute>($\<^bold>v\<lbrakk>0,0/$x,$y\<rbrakk>) = 0.5) \<or> ($prob\<acute>($\<^bold>v\<lbrakk>1,1/$x,$y\<rbrakk>) = 0.5))) \<sqsubseteq> (P' ;; \<up> Q)"
  apply (subst P'Q_simp)
  by (rel_auto)

lemma P'Q_prob_xy_equal':
  "U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>0,0/$x,$y\<rbrakk>) + $prob\<acute>($\<^bold>v\<lbrakk>1,1/$x,$y\<rbrakk>) = 0.5)) \<sqsubseteq> (P' ;; \<up> Q)"
  apply (subst P'Q_simp)
  apply (rel_auto)
proof -
  fix ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and prob\<^sub>v::"state pmf"
  assume a1: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real)"
  assume a2: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real)"
  show "pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> = (0::real)"
  proof (rule ccontr)
    assume a11: "\<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> = (0::real)"
    then have f11: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> > 0"
          by simp
    have f12: "(\<Sum>\<^sub>a a. pmf prob\<^sub>v a) \<ge> 
          (\<Sum>\<^sub>a a \<in> {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>, 
                    \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>, 
                    \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>}. pmf prob\<^sub>v a)"
      by (metis measure_pmf.prob_le_1 measure_pmf_conv_infsetsum sum_pmf_eq_1)
    have f13: "(\<Sum>\<^sub>a a \<in> {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>, 
                    \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>, 
                    \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>}. pmf prob\<^sub>v a) > 1"
      using a1 a2 f11 by auto
    then have "(\<Sum>\<^sub>a a. pmf prob\<^sub>v a) > 1"
      using f12 by auto
    then show "False"
      by (simp add: sum_pmf_eq_1)
  qed
next
  fix ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and prob\<^sub>v::"state pmf"
  assume a1: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real)"
  assume a2: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real)"
  show "pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> = (0::real)"
  proof (rule ccontr)
    assume a11: "\<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> = (0::real)"
    then have f11: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> > 0"
          by simp
    have f12: "(\<Sum>\<^sub>a a. pmf prob\<^sub>v a) \<ge> 
          (\<Sum>\<^sub>a a \<in> {\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>, 
                    \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>, 
                    \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>}. pmf prob\<^sub>v a)"
      by (metis measure_pmf.prob_le_1 measure_pmf_conv_infsetsum sum_pmf_eq_1)
    have f13: "(\<Sum>\<^sub>a a \<in> {\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>, 
                    \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>, 
                    \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>}. pmf prob\<^sub>v a) > 1"
      using a1 a2 f11 by auto
    then have "(\<Sum>\<^sub>a a. pmf prob\<^sub>v a) > 1"
      using f12 by auto
    then show "False"
      by (simp add: sum_pmf_eq_1)
  qed
qed

thm "pmf_not_in_the_two_is_zero"

lemma PQ_simp:
  "(P ;; \<up> Q) = 
  U(true \<turnstile>\<^sub>n (\<exists>r\<in>{0..1}. 
    ($prob\<acute>($\<^bold>v\<lbrakk>0,0/$x,$y\<rbrakk>) = 0.5*\<guillemotleft>r\<guillemotright> \<and> 
     $prob\<acute>($\<^bold>v\<lbrakk>0,1/$x,$y\<rbrakk>) = 0.5*\<guillemotleft>r\<guillemotright> \<and>
     $prob\<acute>($\<^bold>v\<lbrakk>1,0/$x,$y\<rbrakk>) = 0.5*\<guillemotleft>1-r\<guillemotright> \<and> 
     $prob\<acute>($\<^bold>v\<lbrakk>1,1/$x,$y\<rbrakk>) = 0.5*\<guillemotleft>1-r\<guillemotright>)))"
  apply (subst PQ_simp_1')
  apply (subst PQ_x0_simp)
  apply (subst PQ_x1_simp)
  apply (subst P'Q_x_r_simp')
  apply (ndes_simp)
  apply (rel_auto)
proof -
  fix ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and prob\<^sub>v::"state pmf"
  let ?s1 = "\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>"
  let ?s2 = "\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>"
  assume a1: "pmf prob\<^sub>v ?s1 \<cdot> (2::real) = (1::real)"
  assume a2: "pmf prob\<^sub>v ?s2 \<cdot> (2::real) = (1::real)"
  show "pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> = (0::real)"
    apply (rule pmf_not_in_the_two_is_zero[
          where a="1/2" and sa="?s1" and sb="?s2"])
    using a1 a2 by auto+
next
  fix ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and prob\<^sub>v::"state pmf"
  let ?s1 = "\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>"
  let ?s2 = "\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>"
  assume a1: "pmf prob\<^sub>v ?s1 \<cdot> (2::real) = (1::real)"
  assume a2: "pmf prob\<^sub>v ?s2 \<cdot> (2::real) = (1::real)"
  show "pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> = (0::real)"
    apply (rule pmf_not_in_the_two_is_zero[
          where a="1/2" and sa="?s1" and sb="?s2"])
    using a1 a2 by auto+
next
  fix ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and prob\<^sub>v::"state pmf"
  let ?s1 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>"
  let ?s2 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>"
  assume a1: "pmf prob\<^sub>v ?s1 \<cdot> (2::real) = (1::real)"
  assume a2: "pmf prob\<^sub>v ?s2 \<cdot> (2::real) = (1::real)"
  have f1: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> = (0::real)"
    apply (rule pmf_not_in_the_two_is_zero[
          where a="1/2" and sa="?s1" and sb="?s2"])
    using a1 a2 by auto+
  show "pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) \<le> (1::real)"
    using f1 by auto
next
  fix ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and prob\<^sub>v::"state pmf"
  let ?s1 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>"
  let ?s2 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>"
  assume a1: "pmf prob\<^sub>v ?s1 \<cdot> (2::real) = (1::real)"
  assume a2: "pmf prob\<^sub>v ?s2 \<cdot> (2::real) = (1::real)"
  have f1: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> = (0::real)"
    apply (rule pmf_not_in_the_two_is_zero[
          where a="1/2" and sa="?s1" and sb="?s2"])
    using a1 a2 by auto+
  have f2: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> = (0::real)"
    apply (rule pmf_not_in_the_two_is_zero[
          where a="1/2" and sa="?s1" and sb="?s2"])
    using a1 a2 by auto+
  show "pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> = pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>"
    using f1 f2 by auto
next
  fix ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and prob\<^sub>v::"state pmf"
  let ?s1 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>"
  let ?s2 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>"
  assume a1: "pmf prob\<^sub>v ?s1 \<cdot> (2::real) = (1::real)"
  assume a2: "pmf prob\<^sub>v ?s2 \<cdot> (2::real) = (1::real)"
  show "pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> = (0::real)"
    apply (rule pmf_not_in_the_two_is_zero[
          where a="1/2" and sa="?s1" and sb="?s2"])
    using a1 a2 by auto+
next
  fix ok\<^sub>v::"bool" and more::"'a" and ok\<^sub>v'::"bool" and prob\<^sub>v::"state pmf"
  let ?s1 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>"
  let ?s2 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>"
  assume a1: "pmf prob\<^sub>v ?s1 \<cdot> (2::real) = (1::real)"
  assume a2: "pmf prob\<^sub>v ?s2 \<cdot> (2::real) = (1::real)"
  show "pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> = (0::real)"
    apply (rule pmf_not_in_the_two_is_zero[
          where a="1/2" and sa="?s1" and sb="?s2"])
    using a1 a2 by auto+
qed

lemma PQ_prob_xy_equal_max:
  "U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>0,0/$x,$y\<rbrakk>) + $prob\<acute>($\<^bold>v\<lbrakk>1,1/$x,$y\<rbrakk>) = 0.5)) \<sqsubseteq> (P ;; \<up> Q)"
  apply (subst PQ_simp)
  by (rel_auto)

subsection \<open> Q ;; P \<close>
(* (\<^U>(true) \<turnstile>\<^sub>n U($prob\<acute>($\<^bold>v\<lbrakk>0/$y\<rbrakk>) = 0.5 \<and> $prob\<acute>($\<^bold>v\<lbrakk>1/$y\<rbrakk>) = 0.5)) ;; \<up> (\<K>(x :=\<^sub>D 0) \<sqinter> \<K>(x :=\<^sub>D 1)) *)
\<comment> \<open> The minimum probability of x=y is 0, see the second alternatives. \<close>
lemma QP'_simp: "(Q ;; \<up> P') = 
  U(true \<turnstile>\<^sub>n (
    ($prob\<acute>($\<^bold>v\<lbrakk>0,0/$x,$y\<rbrakk>) = 0.5 \<and> $prob\<acute>($\<^bold>v\<lbrakk>0,1/$x,$y\<rbrakk>) = 0.5 \<and> 
     $prob\<acute>($\<^bold>v\<lbrakk>1,0/$x,$y\<rbrakk>) = 0 \<and> $prob\<acute>($\<^bold>v\<lbrakk>1,1/$x,$y\<rbrakk>) = 0)
 
\<or>   ($prob\<acute>($\<^bold>v\<lbrakk>0,0/$x,$y\<rbrakk>) = 0 \<and> $prob\<acute>($\<^bold>v\<lbrakk>0,1/$x,$y\<rbrakk>) = 0.5 \<and> 
     $prob\<acute>($\<^bold>v\<lbrakk>1,0/$x,$y\<rbrakk>) = 0.5 \<and> $prob\<acute>($\<^bold>v\<lbrakk>1,1/$x,$y\<rbrakk>) = 0)

\<or>   ($prob\<acute>($\<^bold>v\<lbrakk>0,0/$x,$y\<rbrakk>) = 0.5 \<and> $prob\<acute>($\<^bold>v\<lbrakk>0,1/$x,$y\<rbrakk>) = 0 \<and> 
     $prob\<acute>($\<^bold>v\<lbrakk>1,0/$x,$y\<rbrakk>) = 0 \<and> $prob\<acute>($\<^bold>v\<lbrakk>1,1/$x,$y\<rbrakk>) = 0.5) 

\<or>   ($prob\<acute>($\<^bold>v\<lbrakk>0,0/$x,$y\<rbrakk>) = 0 \<and> $prob\<acute>($\<^bold>v\<lbrakk>0,1/$x,$y\<rbrakk>) = 0 \<and> 
     $prob\<acute>($\<^bold>v\<lbrakk>1,0/$x,$y\<rbrakk>) = 0.5 \<and> $prob\<acute>($\<^bold>v\<lbrakk>1,1/$x,$y\<rbrakk>) = 0.5)
  ))"
  apply (subst Q_alt)
  apply (simp add: pemp_assign, ndes_simp)
  apply (simp add: kleisli_lift_alt_def kleisli_lift2'_def)
  apply (ndes_simp)
  apply (rule ndesign_eq_intro)
  apply (rel_simp)
  apply (metis (full_types) Collect_cong UNIV_I lit.rep_eq mem_Collect_eq 
        order_top_class.top.extremum_unique top_set_def upred_ref_iff upred_set.rep_eq 
        sum_pmf_eq_1)
  apply (rule eq_split)
  defer
  apply (rel_simp, auto)
  defer defer defer defer
  apply (rel_simp)
proof -
  fix x\<^sub>v::"int" and more::"'a" and prob\<^sub>v::"state pmf" and prob\<^sub>v'::"state pmf"
    and x::"state \<Rightarrow> state pmf"
  let ?s0x = "\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>"
  let ?s1x = "\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>"
  let ?s00 = "\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>"
  let ?s01 = "\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>"
  let ?s10 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>"
  let ?s11 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>"
  assume a1: "pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real)"
  assume a2: "pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real)"
  assume a3: "\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
          pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> =
          (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>)"
  assume a4: "\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
          (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
          (\<forall>prob\<^sub>v::state pmf.
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<or>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<or>
              (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
  from a4 have a4': "\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
          (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
          (pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<or>
           pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real))"
    by blast
  from a4' have a4'': 
    "(pmf (x ?s0x) ?s00 = (1::real) \<or>
      pmf (x ?s0x) ?s10 = (1::real)) \<and> 
    (pmf (x ?s1x) ?s01 = (1::real) \<or>
      pmf (x ?s1x) ?s11 = (1::real))"
    using a1 a2 by auto
  have f1: "\<forall>s. (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) s) = 
            (pmf prob\<^sub>v' ?s0x \<cdot> pmf (x ?s0x) s) + (pmf prob\<^sub>v' ?s1x \<cdot> pmf (x ?s1x) s)"
    apply (auto)
    apply (subst infsetsum_two'[where xa="?s0x" and xb="?s1x"])
    apply simp
    using a1 a2 by auto
  have f1': "\<forall>s. (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) s) = 
    (0.5 \<cdot> pmf (x ?s0x) s) + (0.5 \<cdot> pmf (x ?s1x) s)"
    using f1 a1 a2
    proof -
      { fix ss :: state
      have ff1: "\<forall>r. (r::real) / r = 1 \<or> r = 0"
        by simp
      have ff2: "1 / 2 = pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0\<rparr>"
      by (simp add: a1)
    have ff3: "\<forall>n r. 2 / ((r::real) / numeral n) = numeral (num.Bit0 n) / r"
        by simp
      have ff4: "pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1\<rparr> = pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0\<rparr>"
        using ff2 a2 by linarith
      have "\<forall>n. numeral n / numeral (num.Bit0 n) = pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0\<rparr>"
        using ff3 ff2 ff1 by (metis divide_divide_eq_right nonzero_mult_div_cancel_left zero_neq_numeral)
      then have "(\<Sum>\<^sub>as. pmf prob\<^sub>v' s \<cdot> pmf (x s) ss) = 5 / 10 \<cdot> pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0\<rparr>) ss + 5 / 10 \<cdot> pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1\<rparr>) ss"
        using ff4 f1 by presburger }
    then show ?thesis
      by blast
    qed
  assume a5: 
    "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>) = (0::real) \<longrightarrow>
     (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>) \<cdot> (2::real) = (1::real) \<longrightarrow>
     (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>) \<cdot> (2::real) = (1::real) \<longrightarrow>
       \<not> (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>) = (0::real)"
  assume a6: 
    "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>) \<cdot> (2::real) = (1::real) \<longrightarrow>
     (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>) \<cdot> (2::real) = (1::real) \<longrightarrow>
     (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>) = (0::real) \<longrightarrow>
       \<not> (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>) = (0::real)"
  assume a7: "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>) \<cdot> (2::real) =
       (1::real) \<longrightarrow>
       (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>) = (0::real) \<longrightarrow>
       (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>) = (0::real) \<longrightarrow>
       \<not> (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>) \<cdot> (2::real) =
          (1::real)"
  have a5': 
     "(0.5 \<cdot> pmf (x ?s0x) ?s10) + (0.5 \<cdot> pmf (x ?s1x) ?s10) = 0 \<longrightarrow>
      (0.5 \<cdot> pmf (x ?s0x) ?s01) + (0.5 \<cdot> pmf (x ?s1x) ?s01) = 0.5 \<longrightarrow>
      (0.5 \<cdot> pmf (x ?s0x) ?s00) + (0.5 \<cdot> pmf (x ?s1x) ?s00) = 0.5 \<longrightarrow>
      \<not> (0.5 \<cdot> pmf (x ?s0x) ?s11) + (0.5 \<cdot> pmf (x ?s1x) ?s11) = 0
    "
    using a5 f1' by auto
  from a5' have a5'': "\<not>((pmf (x ?s0x) ?s00 = (1::real)) \<and> (pmf (x ?s1x) ?s01 = (1::real)))"
    apply (auto)
    by (simp add: pmf_not_the_one_is_zero)+
  have a6': 
     "(0.5 \<cdot> pmf (x ?s0x) ?s10) + (0.5 \<cdot> pmf (x ?s1x) ?s10) = 0.5 \<longrightarrow>
      (0.5 \<cdot> pmf (x ?s0x) ?s01) + (0.5 \<cdot> pmf (x ?s1x) ?s01) = 0.5 \<longrightarrow>
      (0.5 \<cdot> pmf (x ?s0x) ?s00) + (0.5 \<cdot> pmf (x ?s1x) ?s00) = 0 \<longrightarrow>
      \<not> (0.5 \<cdot> pmf (x ?s0x) ?s11) + (0.5 \<cdot> pmf (x ?s1x) ?s11) = 0
    "
    using a6 f1' by auto
  from a6' have a6'': "\<not>((pmf (x ?s0x) ?s10 = (1::real)) \<and> (pmf (x ?s1x) ?s01 = (1::real)))"
    apply (auto)
    by (simp add: pmf_not_the_one_is_zero)+
  have a7': 
     "(0.5 \<cdot> pmf (x ?s0x) ?s10) + (0.5 \<cdot> pmf (x ?s1x) ?s10) = 0.5 \<longrightarrow>
      (0.5 \<cdot> pmf (x ?s0x) ?s01) + (0.5 \<cdot> pmf (x ?s1x) ?s01) = 0 \<longrightarrow>
      (0.5 \<cdot> pmf (x ?s0x) ?s00) + (0.5 \<cdot> pmf (x ?s1x) ?s00) = 0 \<longrightarrow>
      \<not> (0.5 \<cdot> pmf (x ?s0x) ?s11) + (0.5 \<cdot> pmf (x ?s1x) ?s11) = 0.5
    "
    using a7 f1' by auto
  from a7' have a7'': "\<not>((pmf (x ?s0x) ?s10 = (1::real)) \<and> (pmf (x ?s1x) ?s11 = (1::real)))"
    apply (auto)
    by (simp add: pmf_not_the_one_is_zero)+
  have f2: "(pmf (x ?s0x) ?s00 = (1::real)) \<and> 
    (pmf (x ?s1x) ?s11 = (1::real))"
    using a5'' a4'' a6'' a7'' by blast
  show "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>) \<cdot> (2::real) =
       (1::real) \<and>
       (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>) = (0::real) \<and>
       (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>) = (0::real) \<and>
       (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>) \<cdot> (2::real) =
       (1::real)"
    apply (simp add: f1')
    using f2 pmf_not_the_one_is_zero by force
next
  fix x\<^sub>v::"int" and more::"'a" and prob\<^sub>v::"state pmf"
  let ?s00 = "\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>"
  let ?s01 = "\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>"
  let ?s10 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>"
  let ?s11 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>"
  assume a1: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real)"
  assume a2: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real)"
  assume a3: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> = (0::real)"
  assume a4: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> = (0::real)"
  have p1: "\<forall>vx::int. \<forall>vy::int. (vx \<noteq> (0::int)) \<longrightarrow> pmf prob\<^sub>v \<lparr>x\<^sub>v = vx, y\<^sub>v = vy\<rparr> = 0"
    apply (auto)
    apply (subst pmf_not_in_the_two_is_zero[where sa="?s00" and sb="?s01" and a="0.5"])
    apply (auto)+
    using a1 a2 by (auto)+
  have p2: "\<forall>vx::int. \<forall>vy::int. (vy \<noteq> (0::int) \<and> vy \<noteq> (1::int)) \<longrightarrow> pmf prob\<^sub>v \<lparr>x\<^sub>v = vx, y\<^sub>v = vy\<rparr> = 0"
    apply (auto)
    apply (subst pmf_not_in_the_two_is_zero[where sa="?s00" and sb="?s01" and a="0.5"])
    apply (auto)+
    using a1 a2 by (auto)+
  let ?x = "\<lambda>s. (if s = \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> 
     then pmf_of_list [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>, 1)]
     else (if s = \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> 
     then pmf_of_list [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>, 1)]
     else pmf_of_set {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>}))"
  show "\<exists>prob\<^sub>v'::state pmf.
          pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
          pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
          (\<exists>x::state \<Rightarrow> state pmf.
              (\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
                  pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> =
                  (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>)) \<and>
              (\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
                  (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
                  (\<forall>prob\<^sub>v::state pmf.
                      pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<or>
                      pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<or>
                      (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                          \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                             pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))))"
    apply (rule_tac x = "pmf_of_list [(\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, 0.5), 
            (\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>, 0.5)]" in exI)
    apply (rule conjI, subst pmf_pmf_of_list, simp add: pmf_of_list_wf_def, simp)
    apply (rule conjI, subst pmf_pmf_of_list, simp add: pmf_of_list_wf_def, simp)
    apply (rule_tac x = "?x" in exI)
    apply (rule conjI)
    apply (rule allI)+
    proof -
      fix x\<^sub>v'::"int" and y\<^sub>v::"int"
      have f1: "(\<Sum>\<^sub>aa::state.
            pmf (pmf_of_list
                  [(\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, (5::real) / (10::real)),
                   (\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>, (5::real) / (10::real))]) a
           \<cdot> pmf (?x a) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>)
          = (0.5* pmf (?x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>) + 
            (0.5* pmf (?x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>)"
        apply (subst infsetsum_two'[where xa="\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>" and xb="\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>"])
        apply simp
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        by (simp add: pmf_of_list_wf_def)+
      have f2: "... = (0.5* pmf (pmf_of_list [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>, 1)]) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>) + 
            (0.5* pmf (pmf_of_list [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>, 1)]) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>)"
        by simp
      have f3: "... = pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>"
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (auto)
        using a2 apply blast
        using a1 apply (simp add: p1)+
        by (simp add: p2)
      show "pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr> =
         (\<Sum>\<^sub>aa::state.
            pmf (pmf_of_list
                  [(\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, (5::real) / (10::real)),
                   (\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>, (5::real) / (10::real))]) a
           \<cdot> pmf (?x a) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>)"
        using f1 f3 by auto
    next
      have f1: "\<forall>(x\<^sub>v'::int) y\<^sub>v::int. (0::real)
        < pmf (pmf_of_list
               [(\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, (1::real) / (2::real)), (\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>, (1::real) / (2::real))])
          \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow> (x\<^sub>v' = x\<^sub>v \<and> ((y\<^sub>v = (0::int)) \<or> (y\<^sub>v = (1::int))))"
        apply (subst pmf_pmf_of_list)+
        by (simp add: pmf_of_list_wf_def)+
      have f2: "pmf (pmf_of_list [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>, 1::real)]) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> = (1::real)"
        apply (subst pmf_pmf_of_list)+
        by (simp add: pmf_of_list_wf_def)+
      show "\<forall>(x\<^sub>v'::int) y\<^sub>v::int.
         (0::real)
         < pmf (pmf_of_list
                 [(\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, (5::real) / (10::real)),
                  (\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>, (5::real) / (10::real))])
            \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
         (\<forall>prob\<^sub>v::state pmf.
             pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<or>
             pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<or>
             (\<exists>(x\<^sub>v''::int) y\<^sub>v'::int.
                 \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v'', y\<^sub>v = y\<^sub>v'\<rparr> =
                    pmf (if \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr> = \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>
                         then pmf_of_list [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>, 1::real)]
                         else if \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr> = \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>
                              then pmf_of_list [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>, 1::real)]
                              else pmf_of_set {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>})
                     \<lparr>x\<^sub>v = x\<^sub>v'', y\<^sub>v = y\<^sub>v'\<rparr>))"
      apply (auto)
      apply (metis indicator_eq_1_iff insert_iff pmf_instance_from_one_full_state pmf_return)
      using f1 f2 by blast+
    qed
next
  fix x\<^sub>v::"int" and prob\<^sub>v::"state pmf"
  let ?s00 = "\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>"
  let ?s01 = "\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>"
  let ?s10 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>"
  let ?s11 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>"
  assume a1: "pmf prob\<^sub>v ?s00  =  (0::real)"
  assume a2: "pmf prob\<^sub>v ?s01 \<cdot> (2::real) = (1::real)"
  assume a3: "pmf prob\<^sub>v ?s10\<cdot> (2::real) = (1::real)"
  assume a4: "pmf prob\<^sub>v ?s11 = (0::real)"
  have p1: "\<forall>vx::int. \<forall>vy::int. (vx \<noteq> (0::int) \<and> vx \<noteq> (1::int)) \<longrightarrow> pmf prob\<^sub>v \<lparr>x\<^sub>v = vx, y\<^sub>v = vy\<rparr> = 0"
    apply (auto)
    apply (subst pmf_not_in_the_two_is_zero[where sa="?s01" and sb="?s10" and a="0.5"])
    apply (auto)+
    using a2 apply blast
    using a3 by blast
  have p2: "\<forall>vx::int. \<forall>vy::int. (vx \<noteq> (1::int) \<and> vy \<noteq> (1::int)) \<longrightarrow> pmf prob\<^sub>v \<lparr>x\<^sub>v = vx, y\<^sub>v = vy\<rparr> = 0"
    apply (auto)
    apply (subst pmf_not_in_the_two_is_zero[where sa="?s01" and sb="?s10" and a="0.5"])
    apply (auto)+
    using a2 a3 by blast+
  have p3: "\<forall>vx::int. \<forall>vy::int. (vx \<noteq> (0::int) \<and> vy \<noteq> (0::int)) \<longrightarrow> pmf prob\<^sub>v \<lparr>x\<^sub>v = vx, y\<^sub>v = vy\<rparr> = 0"
    apply (auto)
    apply (subst pmf_not_in_the_two_is_zero[where sa="?s01" and sb="?s10" and a="0.5"])
    apply (auto)+
    using a2 a3 by blast+
  have p4: "\<forall>vx::int. \<forall>vy::int. (vy \<noteq> (0::int) \<and> vy \<noteq> (1::int)) \<longrightarrow> pmf prob\<^sub>v \<lparr>x\<^sub>v = vx, y\<^sub>v = vy\<rparr> = 0"
    apply (auto)
    apply (subst pmf_not_in_the_two_is_zero[where sa="?s01" and sb="?s10" and a="0.5"])
    apply (auto)+
    using a2 a3 by blast+
  let ?x = "\<lambda>s. (if s = \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> 
     then pmf_of_list [(\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>, 1)]
     else (if s = \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> 
     then pmf_of_list [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>, 1)]
     else pmf_of_set {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>}))"
  show "\<exists>prob\<^sub>v'::state pmf.
          pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
          pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
          (\<exists>x::state \<Rightarrow> state pmf.
              (\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
                  pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> =
                  (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>)) \<and>
              (\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
                  (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
                  (\<forall>prob\<^sub>v::state pmf.
                      pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<or>
                      pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<or>
                      (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                          \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                             pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))))"
    apply (rule_tac x = "pmf_of_list [(\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, 0.5), 
            (\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>, 0.5)]" in exI)
    apply (rule conjI, subst pmf_pmf_of_list, simp add: pmf_of_list_wf_def, simp)
    apply (rule conjI, subst pmf_pmf_of_list, simp add: pmf_of_list_wf_def, simp)
    apply (rule_tac x = "?x" in exI)
    apply (rule conjI)
    apply (rule allI)+
    proof -
      fix x\<^sub>v'::"int" and y\<^sub>v::"int"
      have f1: "(\<Sum>\<^sub>aa::state.
            pmf (pmf_of_list
                  [(\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, (5::real) / (10::real)),
                   (\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>, (5::real) / (10::real))]) a
           \<cdot> pmf (?x a) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>)
          = (0.5* pmf (?x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>) + 
            (0.5* pmf (?x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>)"
        apply (subst infsetsum_two'[where xa="\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>" and xb="\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>"])
        apply simp
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        by (simp add: pmf_of_list_wf_def)+
      have f2: "... = (0.5* pmf (pmf_of_list [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>, 1)]) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>) + 
            (0.5* pmf (pmf_of_list [(\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>, 1)]) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>)"
        by simp
      have f3: "... = pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>"
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (auto)
        using a3 apply blast
        using a2 apply blast
        using a1 apply (simp add: p1)+
        apply (simp add: p2)
        using a2 apply blast
        apply (simp add: p3)
        by (simp add: p4)
      show "pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr> =
         (\<Sum>\<^sub>aa::state.
            pmf (pmf_of_list
                  [(\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, (5::real) / (10::real)),
                   (\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>, (5::real) / (10::real))]) a
           \<cdot> pmf (?x a) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>)"
        using f1 f3 by auto
    next
      have f1: "\<forall>(x\<^sub>v'::int) y\<^sub>v::int. (0::real)
        < pmf (pmf_of_list
               [(\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, (1::real) / (2::real)), (\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>, (1::real) / (2::real))])
          \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow> (x\<^sub>v' = x\<^sub>v \<and> ((y\<^sub>v = (0::int)) \<or> (y\<^sub>v = (1::int))))"
        apply (subst pmf_pmf_of_list)+
        by (simp add: pmf_of_list_wf_def)+
      have f2: "pmf (pmf_of_list [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>, 1::real)]) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr> = (1::real)"
        apply (subst pmf_pmf_of_list)+
        by (simp add: pmf_of_list_wf_def)+
      have f3: "pmf (pmf_of_list [(\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>, 1::real)]) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> = (1::real)"
        apply (subst pmf_pmf_of_list)+
        by (simp add: pmf_of_list_wf_def)+
      show "\<forall>(x\<^sub>v'::int) y\<^sub>v::int.
         (0::real)
         < pmf (pmf_of_list
                 [(\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, (5::real) / (10::real)),
                  (\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>, (5::real) / (10::real))])
            \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
         (\<forall>prob\<^sub>v::state pmf.
             pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<or>
             pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<or>
             (\<exists>(x\<^sub>v''::int) y\<^sub>v'::int.
                 \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v'', y\<^sub>v = y\<^sub>v'\<rparr> =
                    pmf (?x \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>)
                     \<lparr>x\<^sub>v = x\<^sub>v'', y\<^sub>v = y\<^sub>v'\<rparr>))"
      apply (auto)
      using f2 apply blast
      using f1 f2 apply blast+
      using f3 apply blast
      using f1 by blast+
  qed
next
  fix x\<^sub>v::"int" and prob\<^sub>v::"state pmf"
  let ?s00 = "\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>"
  let ?s01 = "\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>"
  let ?s10 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>"
  let ?s11 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>"
  assume a1: "pmf prob\<^sub>v ?s00 \<cdot> (2::real) = (1::real)"
  assume a2: "pmf prob\<^sub>v ?s01  = (0::real)"
  assume a3: "pmf prob\<^sub>v ?s10  = (0::real)"
  assume a4: "pmf prob\<^sub>v ?s11\<cdot> (2::real) = (1::real)"
  have p1: "\<forall>vx::int. \<forall>vy::int. (vx \<noteq> (0::int) \<and> vx \<noteq> (1::int)) \<longrightarrow> pmf prob\<^sub>v \<lparr>x\<^sub>v = vx, y\<^sub>v = vy\<rparr> = 0"
    apply (auto)
    apply (subst pmf_not_in_the_two_is_zero[where sa="?s00" and sb="?s11" and a="0.5"])
    apply (auto)+
    using a1 apply blast
    using a4 by blast
  have p2: "\<forall>vx::int. \<forall>vy::int. (vx \<noteq> (1::int) \<and> vy \<noteq> (0::int)) \<longrightarrow> pmf prob\<^sub>v \<lparr>x\<^sub>v = vx, y\<^sub>v = vy\<rparr> = 0"
    apply (auto)
    apply (subst pmf_not_in_the_two_is_zero[where sa="?s00" and sb="?s11" and a="0.5"])
    apply (auto)+
    using a1 a4 by blast+
  have p3: "\<forall>vx::int. \<forall>vy::int. (vx \<noteq> (0::int) \<and> vy \<noteq> (1::int)) \<longrightarrow> pmf prob\<^sub>v \<lparr>x\<^sub>v = vx, y\<^sub>v = vy\<rparr> = 0"
    apply (auto)
    apply (subst pmf_not_in_the_two_is_zero[where sa="?s00" and sb="?s11" and a="0.5"])
    apply (auto)+
    using a1 a4 by blast+
  have p4: "\<forall>vx::int. \<forall>vy::int. (vy \<noteq> (0::int) \<and> vy \<noteq> (1::int)) \<longrightarrow> pmf prob\<^sub>v \<lparr>x\<^sub>v = vx, y\<^sub>v = vy\<rparr> = 0"
    apply (auto)
    apply (subst pmf_not_in_the_two_is_zero[where sa="?s00" and sb="?s11" and a="0.5"])
    apply (auto)+
    using a1 a4 by blast+
  let ?x = "\<lambda>s. (if s = \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> 
     then pmf_of_list [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>, 1)]
     else (if s = \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> 
     then pmf_of_list [(\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>, 1)]
     else pmf_of_set {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>}))"
  show "\<exists>prob\<^sub>v'::state pmf.
          pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
          pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
          (\<exists>x::state \<Rightarrow> state pmf.
              (\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
                  pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> =
                  (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>)) \<and>
              (\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
                  (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
                  (\<forall>prob\<^sub>v::state pmf.
                      pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<or>
                      pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<or>
                      (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                          \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                             pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))))"
    apply (rule_tac x = "pmf_of_list [(\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, 0.5), 
            (\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>, 0.5)]" in exI)
    apply (rule conjI, subst pmf_pmf_of_list, simp add: pmf_of_list_wf_def, simp)
    apply (rule conjI, subst pmf_pmf_of_list, simp add: pmf_of_list_wf_def, simp)
    apply (rule_tac x = "?x" in exI)
    apply (rule conjI)
    apply (rule allI)+
    proof -
      fix x\<^sub>v'::"int" and y\<^sub>v::"int"
      have f1: "(\<Sum>\<^sub>aa::state.
            pmf (pmf_of_list
                  [(\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, (5::real) / (10::real)),
                   (\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>, (5::real) / (10::real))]) a
           \<cdot> pmf (?x a) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>)
          = (0.5* pmf (?x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>) + 
            (0.5* pmf (?x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>)"
        apply (subst infsetsum_two'[where xa="\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>" and xb="\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>"])
        apply simp
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        by (simp add: pmf_of_list_wf_def)+
      have f2: "... = (0.5* pmf (pmf_of_list [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>, 1)]) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>) + 
            (0.5* pmf (pmf_of_list [(\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>, 1)]) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>)"
        by simp
      have f3: "... = pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>"
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (auto)
        using a4 apply blast
        using a1 apply blast
        using a1 apply (simp add: p1)+
        apply (simp add: p2)
        using a1 apply blast
        apply (simp add: p3)
        by (simp add: p4)
      show "pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr> =
         (\<Sum>\<^sub>aa::state.
            pmf (pmf_of_list
                  [(\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, (5::real) / (10::real)),
                   (\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>, (5::real) / (10::real))]) a
           \<cdot> pmf (?x a) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>)"
        using f1 f3 by auto
    next
      have f1: "\<forall>(x\<^sub>v'::int) y\<^sub>v::int. (0::real)
        < pmf (pmf_of_list
               [(\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, (1::real) / (2::real)), (\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>, (1::real) / (2::real))])
          \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow> (x\<^sub>v' = x\<^sub>v \<and> ((y\<^sub>v = (0::int)) \<or> (y\<^sub>v = (1::int))))"
        apply (subst pmf_pmf_of_list)+
        by (simp add: pmf_of_list_wf_def)+
      have f2: "pmf (pmf_of_list [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>, 1::real)]) \<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr> = (1::real)"
        apply (subst pmf_pmf_of_list)+
        by (simp add: pmf_of_list_wf_def)+
      have f3: "pmf (pmf_of_list [(\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>, 1::real)]) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> = (1::real)"
        apply (subst pmf_pmf_of_list)+
        by (simp add: pmf_of_list_wf_def)+
      show "\<forall>(x\<^sub>v'::int) y\<^sub>v::int.
         (0::real)
         < pmf (pmf_of_list
                 [(\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, (5::real) / (10::real)),
                  (\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>, (5::real) / (10::real))])
            \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
         (\<forall>prob\<^sub>v::state pmf.
             pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<or>
             pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<or>
             (\<exists>(x\<^sub>v''::int) y\<^sub>v'::int.
                 \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v'', y\<^sub>v = y\<^sub>v'\<rparr> =
                    pmf (?x \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>)
                     \<lparr>x\<^sub>v = x\<^sub>v'', y\<^sub>v = y\<^sub>v'\<rparr>))"
        apply (auto)
        apply (metis indicator_simps(1) insert_iff pmf_instance_from_one_full_state pmf_return)
        using f1 apply blast
        using f1 apply blast+
        using f2 apply blast
        using f1 by blast+
  qed
next
  fix x\<^sub>v::"int" and prob\<^sub>v::"state pmf"
  let ?s00 = "\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 0::int\<rparr>"
  let ?s01 = "\<lparr>x\<^sub>v = 0::int, y\<^sub>v = 1::int\<rparr>"
  let ?s10 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>"
  let ?s11 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>"
  assume a1: "pmf prob\<^sub>v ?s00 = (0::real)"
  assume a2: "pmf prob\<^sub>v ?s01 = (0::real)"
  assume a3: "pmf prob\<^sub>v ?s10 \<cdot> (2::real) = (1::real)"
  assume a4: "pmf prob\<^sub>v ?s11 \<cdot> (2::real) = (1::real)"
  have p1: "\<forall>vx::int. \<forall>vy::int. (vx \<noteq> (1::int)) \<longrightarrow> pmf prob\<^sub>v \<lparr>x\<^sub>v = vx, y\<^sub>v = vy\<rparr> = 0"
    apply (auto)
    apply (subst pmf_not_in_the_two_is_zero[where sa="?s10" and sb="?s11" and a="0.5"])
    apply (auto)+
    using a3 apply blast
    using a4 by blast
  have p2: "\<forall>vx::int. \<forall>vy::int. (vx \<noteq> (1::int) \<and> vy \<noteq> (1::int)) \<longrightarrow> pmf prob\<^sub>v \<lparr>x\<^sub>v = vx, y\<^sub>v = vy\<rparr> = 0"
    apply (auto)
    apply (subst pmf_not_in_the_two_is_zero[where sa="?s10" and sb="?s11" and a="0.5"])
    apply (auto)+
    using a3 a4 by blast+
  have p3: "\<forall>vx::int. \<forall>vy::int. (vy \<noteq> (0::int) \<and> vy \<noteq> (1::int)) \<longrightarrow> pmf prob\<^sub>v \<lparr>x\<^sub>v = vx, y\<^sub>v = vy\<rparr> = 0"
    apply (auto)
    apply (subst pmf_not_in_the_two_is_zero[where sa="?s10" and sb="?s11" and a="0.5"])
    apply (auto)+
    using a3 a4 by blast+
  let ?x = "\<lambda>s. (if s = \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> 
     then pmf_of_list [(\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>, 1)]
     else (if s = \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> 
     then pmf_of_list [(\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>, 1)]
     else pmf_of_set {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>}))"
  show "\<exists>prob\<^sub>v'::state pmf.
          pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
          pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr> \<cdot> (2::real) = (1::real) \<and>
          (\<exists>x::state \<Rightarrow> state pmf.
              (\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
                  pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> =
                  (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>)) \<and>
              (\<forall>(x\<^sub>v::int) (y\<^sub>v::int).
                  (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
                  (\<forall>prob\<^sub>v::state pmf.
                      pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<or>
                      pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<or>
                      (\<exists>(x\<^sub>v'::int) (y\<^sub>v'::int).
                          \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                             pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))))"
    apply (rule_tac x = "pmf_of_list [(\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, 0.5), 
            (\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>, 0.5)]" in exI)
    apply (rule conjI, subst pmf_pmf_of_list, simp add: pmf_of_list_wf_def, simp)
    apply (rule conjI, subst pmf_pmf_of_list, simp add: pmf_of_list_wf_def, simp)
    apply (rule_tac x = "?x" in exI)
    apply (rule conjI)
    apply (rule allI)+
    proof -
      fix x\<^sub>v'::"int" and y\<^sub>v::"int"
      have f1: "(\<Sum>\<^sub>aa::state.
            pmf (pmf_of_list
                  [(\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, (5::real) / (10::real)),
                   (\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>, (5::real) / (10::real))]) a
           \<cdot> pmf (?x a) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>)
          = (0.5* pmf (?x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>) + 
            (0.5* pmf (?x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>)"
        apply (subst infsetsum_two'[where xa="\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>" and xb="\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>"])
        apply simp
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        by (simp add: pmf_of_list_wf_def)+
      have f2: "... = (0.5* pmf (pmf_of_list [(\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>, 1)]) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>) + 
            (0.5* pmf (pmf_of_list [(\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>, 1)]) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>)"
        by simp
      have f3: "... = pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>"
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (subst pmf_pmf_of_list)+
        apply (simp add: pmf_of_list_wf_def)+
        apply (auto)
        using a4 apply blast
        apply (simp add: p1)+
        using a3 apply blast
        apply (simp add: p2)+
        by (simp add: p3)
      show "pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr> =
         (\<Sum>\<^sub>aa::state.
            pmf (pmf_of_list
                  [(\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, (5::real) / (10::real)),
                   (\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>, (5::real) / (10::real))]) a
           \<cdot> pmf (?x a) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>)"
        using f1 f3 by auto
    next
      have f1: "\<forall>(x\<^sub>v'::int) y\<^sub>v::int. (0::real)
        < pmf (pmf_of_list
               [(\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, (1::real) / (2::real)), (\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>, (1::real) / (2::real))])
          \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow> (x\<^sub>v' = x\<^sub>v \<and> ((y\<^sub>v = (0::int)) \<or> (y\<^sub>v = (1::int))))"
        apply (subst pmf_pmf_of_list)+
        by (simp add: pmf_of_list_wf_def)+
      have f2: "pmf (pmf_of_list [(\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr>, 1::real)]) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 0::int\<rparr> = (1::real)"
        apply (subst pmf_pmf_of_list)+
        by (simp add: pmf_of_list_wf_def)+
      have f3: "pmf (pmf_of_list [(\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>, 1::real)]) \<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr> = (1::real)"
        apply (subst pmf_pmf_of_list)+
        by (simp add: pmf_of_list_wf_def)+
      show "\<forall>(x\<^sub>v'::int) y\<^sub>v::int.
         (0::real)
         < pmf (pmf_of_list
                 [(\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 0::int\<rparr>, (5::real) / (10::real)),
                  (\<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = 1::int\<rparr>, (5::real) / (10::real))])
            \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
         (\<forall>prob\<^sub>v::state pmf.
             pmf prob\<^sub>v \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<or>
             pmf prob\<^sub>v \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) \<or>
             (\<exists>(x\<^sub>v''::int) y\<^sub>v'::int.
                 \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v'', y\<^sub>v = y\<^sub>v'\<rparr> =
                    pmf (?x \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v\<rparr>)
                     \<lparr>x\<^sub>v = x\<^sub>v'', y\<^sub>v = y\<^sub>v'\<rparr>))"
        apply (auto)
        apply (metis indicator_simps(1) insert_iff pmf_instance_from_one_full_state pmf_return)
        using f1 apply blast
        using f1 apply blast+
        using f2 apply blast
        using f1 by blast+
  qed
qed

lemma QP'_prob_xy_equal:
  "(Q ;; \<up> P')  \<sqsubseteq>  U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>0,0/$x,$y\<rbrakk>) = 0.5 \<and> $prob\<acute>($\<^bold>v\<lbrakk>0,1/$x,$y\<rbrakk>) = 0.5 \<and> 
     $prob\<acute>($\<^bold>v\<lbrakk>1,0/$x,$y\<rbrakk>) = 0 \<and> $prob\<acute>($\<^bold>v\<lbrakk>1,1/$x,$y\<rbrakk>) = 0))"
  apply (subst QP'_simp)
  by (rel_auto)

(*
lemma QP_simp: "(Q ;; \<up> P) = 
  U(true \<turnstile>\<^sub>n (
    ($prob\<acute>($\<^bold>v\<lbrakk>0,0/$x,$y\<rbrakk>) = 0.5 \<and> $prob\<acute>($\<^bold>v\<lbrakk>0,1/$x,$y\<rbrakk>) = 0.5 \<and> 
     $prob\<acute>($\<^bold>v\<lbrakk>1,0/$x,$y\<rbrakk>) = 0 \<and> $prob\<acute>($\<^bold>v\<lbrakk>1,1/$x,$y\<rbrakk>) = 0)
 
\<or>   ($prob\<acute>($\<^bold>v\<lbrakk>0,0/$x,$y\<rbrakk>) = 0 \<and> $prob\<acute>($\<^bold>v\<lbrakk>0,1/$x,$y\<rbrakk>) = 0.5 \<and> 
     $prob\<acute>($\<^bold>v\<lbrakk>1,0/$x,$y\<rbrakk>) = 0.5 \<and> $prob\<acute>($\<^bold>v\<lbrakk>1,1/$x,$y\<rbrakk>) = 0)

\<or>   ($prob\<acute>($\<^bold>v\<lbrakk>0,0/$x,$y\<rbrakk>) = 0.5 \<and> $prob\<acute>($\<^bold>v\<lbrakk>0,1/$x,$y\<rbrakk>) = 0 \<and> 
     $prob\<acute>($\<^bold>v\<lbrakk>1,0/$x,$y\<rbrakk>) = 0 \<and> $prob\<acute>($\<^bold>v\<lbrakk>1,1/$x,$y\<rbrakk>) = 0.5) 

\<or>   ($prob\<acute>($\<^bold>v\<lbrakk>0,0/$x,$y\<rbrakk>) = 0 \<and> $prob\<acute>($\<^bold>v\<lbrakk>0,1/$x,$y\<rbrakk>) = 0 \<and> 
     $prob\<acute>($\<^bold>v\<lbrakk>1,0/$x,$y\<rbrakk>) = 0.5 \<and> $prob\<acute>($\<^bold>v\<lbrakk>1,1/$x,$y\<rbrakk>) = 0.5)
\<or>
(\<exists>r\<in>{0..1}. 
    ($prob\<acute>($\<^bold>v\<lbrakk>0,0/$x,$y\<rbrakk>) = 0.5*\<guillemotleft>r\<guillemotright> \<and> 
     $prob\<acute>($\<^bold>v\<lbrakk>0,1/$x,$y\<rbrakk>) = 0.5*\<guillemotleft>r\<guillemotright> \<and>
     $prob\<acute>($\<^bold>v\<lbrakk>1,0/$x,$y\<rbrakk>) = 0.5*\<guillemotleft>1-r\<guillemotright> \<and> 
     $prob\<acute>($\<^bold>v\<lbrakk>1,1/$x,$y\<rbrakk>) = 0.5*\<guillemotleft>1-r\<guillemotright>))
  ))"
  apply (subst Q_alt)
  apply (simp add: P_alt')
*)
end
