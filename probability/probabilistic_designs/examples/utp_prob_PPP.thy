section \<open> Eric C.R. Hehner: "Probabilistic Predicative Programming" (PPP) \<close>

theory utp_prob_PPP
  imports
  "../utp_prob_des_laws"
begin recall_syntax

subsection \<open> State space \<close>
alphabet state = 
  x :: "int"
  y :: "int"

subsection \<open> Definitions \<close>

abbreviation pchoice ("(pif (_)/ pthen (_)/ pelse (_)/ pfi)") 
  where "pchoice b P Q \<equiv> P \<oplus>\<^bsub>b\<^esub> Q"

abbreviation pchoice_assign::"real \<Rightarrow> int \<Rightarrow> int \<Rightarrow> (state, state) rel_pdes" 
where
"pchoice_assign r a b \<equiv> (\<K>(x :=\<^sub>D \<guillemotleft>a\<guillemotright>) \<oplus>\<^bsub>(r)\<^esub> \<K>(x :=\<^sub>D \<guillemotleft>b\<guillemotright>))"

abbreviation pchoice_assign' ::
    "real \<Rightarrow> (int, state) uexpr  \<Rightarrow> (int, state) uexpr \<Rightarrow> (state, state) rel_pdes"
where
"pchoice_assign' r a b \<equiv> (\<K>(x :=\<^sub>D a) \<oplus>\<^bsub>(r)\<^esub> \<K>(x :=\<^sub>D b))"

lemma pchoice_assign_simp:
  assumes "r \<in> {0..1}" "a \<noteq> b"
  shows "pchoice_assign r a b = 
         (\<^U>(true) \<turnstile>\<^sub>n U($prob\<acute>($\<^bold>v\<lbrakk>\<guillemotleft>a\<guillemotright>/$x\<rbrakk>) = \<guillemotleft>r\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>\<guillemotleft>b\<guillemotright>/$x\<rbrakk>) = \<guillemotleft>(1-r)\<guillemotright>))"
proof (cases "r = 0")
  case True
  have T: "r = 0"
    using True by simp
  show ?thesis 
    apply (simp add: True prob_choice_zero)
    apply (simp add: pemp_assign)
    apply (rel_auto)
    using assms(2) pmf_not_the_one_is_zero by fastforce
next
  case False
  have F: "\<not> r = 0"
    using False by simp
  then show ?thesis 
    proof (cases "r = 1")
      case True
      then show ?thesis 
        apply (simp add: True prob_choice_zero)
        apply (simp add: pemp_assign)
        apply (rel_auto)
        using assms(2) pmf_not_the_one_is_zero by fastforce
    next
      case False
      then have "r \<in> {0<..<1}"
        using F assms(1) by auto
      then show ?thesis 
        apply (simp add: pemp_assign prob_choice_r)
        apply (simp add: ndes_par)
        apply (rule ndesign_eq_intro)
        apply (simp)
        apply (rel_auto)
        apply (simp add: pmf_wplus pmf_not_the_one_is_zero)
        using assms(2) pmf_not_the_one_is_zero apply fastforce
        apply (simp add: pmf_wplus pmf_not_the_one_is_zero)
        using assms(2) pmf_not_the_one_is_zero apply fastforce
        apply (rule_tac ?x = "x\<^sub>v" in exI)
        apply (rule_tac ?x = "y\<^sub>v" in exI)
        apply (rule_tac x = "pmf_of_set {\<lparr>x\<^sub>v = a, y\<^sub>v = y\<^sub>v\<rparr>}" in exI)
        apply (simp)
        apply (rule_tac x = "pmf_of_set {\<lparr>x\<^sub>v = b, y\<^sub>v = y\<^sub>v\<rparr>}" in exI)
        apply (simp)
        apply (subgoal_tac "\<forall>s. (pmf prob\<^sub>v s) =
             pmf (pmf_of_set {\<lparr>x\<^sub>v = a, y\<^sub>v = y\<^sub>v\<rparr>} +\<^bsub>r\<^esub> 
                  pmf_of_set {\<lparr>x\<^sub>v = b, y\<^sub>v = y\<^sub>v\<rparr>}) s")
        using pmf_eqI apply blast
        apply (auto)
        apply (simp add: pmf_wplus)
        apply (case_tac "s = \<lparr>x\<^sub>v = a, y\<^sub>v = y\<^sub>v\<rparr>")
        using assms(2) apply auto[1]
        apply (case_tac "s = \<lparr>x\<^sub>v = b, y\<^sub>v = y\<^sub>v\<rparr>")
        using assms(2) apply auto[1]
        proof -
          fix y\<^sub>v::"int" and prob\<^sub>v::"state pmf" and s::"state"
          assume a1: "pmf prob\<^sub>v \<lparr>x\<^sub>v = b, y\<^sub>v = y\<^sub>v\<rparr> = (1::real) - pmf prob\<^sub>v \<lparr>x\<^sub>v = a, y\<^sub>v = y\<^sub>v\<rparr>"
          assume a2: "r = pmf prob\<^sub>v \<lparr>x\<^sub>v = a, y\<^sub>v = y\<^sub>v\<rparr>"
          assume a3: "\<not> s = \<lparr>x\<^sub>v = a, y\<^sub>v = y\<^sub>v\<rparr>"
          assume a4: "\<not> s = \<lparr>x\<^sub>v = b, y\<^sub>v = y\<^sub>v\<rparr>"
          show "pmf prob\<^sub>v s =
           indicat_real {\<lparr>x\<^sub>v = a, y\<^sub>v = y\<^sub>v\<rparr>} s \<cdot> pmf prob\<^sub>v \<lparr>x\<^sub>v = a, y\<^sub>v = y\<^sub>v\<rparr> +
           indicat_real {\<lparr>x\<^sub>v = b, y\<^sub>v = y\<^sub>v\<rparr>} s \<cdot> ((1::real) - pmf prob\<^sub>v \<lparr>x\<^sub>v = a, y\<^sub>v = y\<^sub>v\<rparr>)"
            apply (subst pmf_not_in_the_two_is_zero[where a = "r" and 
                sa="\<lparr>x\<^sub>v = (a), y\<^sub>v = y\<^sub>v\<rparr>" and 
                sb="\<lparr>x\<^sub>v = (b), y\<^sub>v = y\<^sub>v\<rparr>"])
            using assms(1) apply simp
                apply simp
            using assms(2) apply simp
            using a2 apply simp
            using a1 apply simp
            using a2 apply simp
            apply (simp add: a3 a4)
            by (simp add: a3 a4)
        qed
    qed
qed

subsection \<open> Section 4 \<close>

lemma "U((x := x + 1) ;; ($x > 5)) = U($x > 4)"
  by (rel_auto)

lemma "U((x := x + 1) wp (&x > 5)) = U(&x > 4)"
  by (rel_auto)

subsection \<open> Section 6 \<close>
abbreviation P1 :: "(state, state) rel_pdes" where
  "P1 \<equiv> (pif 1/3 pthen \<K>(x :=\<^sub>D 0) pelse \<K>(x :=\<^sub>D 1) pfi)"

abbreviation P2 :: "(state, state) rel_pdes" where
  "P2 \<equiv> (pif 1/2 pthen \<K>(x :=\<^sub>D x + 2) pelse \<K>(x :=\<^sub>D x + 3) pfi)"

abbreviation P3 :: "(state, state) rel_pdes" where
  "P3 \<equiv> (pif 1/4 pthen \<K>(x :=\<^sub>D x + 4) pelse \<K>(x :=\<^sub>D x + 5) pfi)"

term "(pif 1/3 pthen \<K>(x :=\<^sub>D 0) pelse \<K>(x :=\<^sub>D 1) pfi)"

lemma P1_alt:
  "P1 = (\<^U>(true) \<turnstile>\<^sub>n U($prob\<acute>($\<^bold>v\<lbrakk>0/$x\<rbrakk>) = 1/3 \<and> $prob\<acute>($\<^bold>v\<lbrakk>1/$x\<rbrakk>) = 2/3))"
  apply (subgoal_tac "pchoice_assign (1/3) 0 1 
    = (\<^U>(true) \<turnstile>\<^sub>n U($prob\<acute>($\<^bold>v\<lbrakk>0/$x\<rbrakk>) = 1/3 \<and> $prob\<acute>($\<^bold>v\<lbrakk>1/$x\<rbrakk>) = 2/3))")
  apply (subgoal_tac "P1 = pchoice_assign (1/3) 0 1")
  apply auto[1] 
  apply (simp add: one_uexpr_def zero_uexpr_def)
  apply (subst pchoice_assign_simp[where r="1/3"])
  apply simp+
  by (rel_auto)

lemma P2_alt:
  "P2 = (\<^U>(true) \<turnstile>\<^sub>n U($prob\<acute>($\<^bold>v\<lbrakk>$x+2/$x\<rbrakk>) = 1/2 \<and> $prob\<acute>($\<^bold>v\<lbrakk>$x+3/$x\<rbrakk>) = 1/2))"
  apply (subgoal_tac "pchoice_assign' (1/2) (&x+2) (&x+3) 
    = (\<^U>(true) \<turnstile>\<^sub>n U($prob\<acute>($\<^bold>v\<lbrakk>$x+2/$x\<rbrakk>) = 1/2 \<and> $prob\<acute>($\<^bold>v\<lbrakk>$x+3/$x\<rbrakk>) = 1/2))")
  apply (subgoal_tac "P2 = pchoice_assign' (1/2) (&x+2) (&x+3)")
  apply auto[1] 
  apply (simp)
  apply (simp add: pemp_assign prob_choice_r)
  apply (simp add: ndes_par)
  apply (rule ndesign_eq_intro)
  apply (simp)
  apply (rel_auto)
  apply (simp add: pmf_wplus pmf_not_the_one_is_zero)+
  apply (rule_tac ?x = "x\<^sub>v" in exI)
  apply (rule_tac ?x = "y\<^sub>v" in exI)
  apply (rule_tac x = "pmf_of_set {\<lparr>x\<^sub>v = x\<^sub>v + (2::int), y\<^sub>v = y\<^sub>v\<rparr>}" in exI)
  apply (simp)
  apply (rule_tac x = "pmf_of_set {\<lparr>x\<^sub>v = x\<^sub>v + (3::int), y\<^sub>v = y\<^sub>v\<rparr>}" in exI)
  apply (simp)
  apply (rule pmf_eqI)
  apply (simp add: pmf_wplus)
  apply (case_tac "i = \<lparr>x\<^sub>v = x\<^sub>v + (2::int), y\<^sub>v = y\<^sub>v\<rparr>")
  apply auto[1]
  apply (case_tac "i = \<lparr>x\<^sub>v = x\<^sub>v + (3::int), y\<^sub>v = y\<^sub>v\<rparr>")
  apply auto[1]
  proof -
    fix x\<^sub>v::"int" and y\<^sub>v::"int" and prob\<^sub>v::"state pmf" and i::"state"
    assume a1: "pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v + (2::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real)"
    assume a2: "pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v + (3::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real)"
    assume a3: "\<not> i = \<lparr>x\<^sub>v = x\<^sub>v + (2::int), y\<^sub>v = y\<^sub>v\<rparr>"
    assume a4: "\<not> i = \<lparr>x\<^sub>v = x\<^sub>v + (3::int), y\<^sub>v = y\<^sub>v\<rparr>"
    show "pmf prob\<^sub>v i =
       indicat_real {\<lparr>x\<^sub>v = x\<^sub>v + (2::int), y\<^sub>v = y\<^sub>v\<rparr>} i / (2::real) +
       indicat_real {\<lparr>x\<^sub>v = x\<^sub>v + (3::int), y\<^sub>v = y\<^sub>v\<rparr>} i / (2::real)"
      apply (subst pmf_not_in_the_two_is_zero[where a = "1/2" and 
          sa="\<lparr>x\<^sub>v = x\<^sub>v + (2::int), y\<^sub>v = y\<^sub>v\<rparr>" and 
          sb="\<lparr>x\<^sub>v = x\<^sub>v + (3::int), y\<^sub>v = y\<^sub>v\<rparr>"])
      apply simp+
      using a1 apply simp
      using a2 apply simp
      apply (simp add: a3 a4)
      by (simp add: a3 a4)
  qed

lemma P3_alt:
  "P3 = (\<^U>(true) \<turnstile>\<^sub>n U($prob\<acute>($\<^bold>v\<lbrakk>$x+4/$x\<rbrakk>) = 1/4 \<and> $prob\<acute>($\<^bold>v\<lbrakk>$x+5/$x\<rbrakk>) = 3/4))"
  apply (subgoal_tac "pchoice_assign' (1/4) (&x+4) (&x+5) 
    = (\<^U>(true) \<turnstile>\<^sub>n U($prob\<acute>($\<^bold>v\<lbrakk>$x+4/$x\<rbrakk>) = 1/4 \<and> $prob\<acute>($\<^bold>v\<lbrakk>$x+5/$x\<rbrakk>) = 3/4))")
  apply (subgoal_tac "P3 = pchoice_assign' (1/4) (&x+4) (&x+5)")
  apply auto[1] 
  apply (simp)
  apply (simp add: pemp_assign prob_choice_r)
  apply (simp add: ndes_par)
  apply (rule ndesign_eq_intro)
  apply (simp)
  apply (rel_auto)
  apply (simp add: pmf_wplus pmf_not_the_one_is_zero)+
  apply (rule_tac ?x = "x\<^sub>v" in exI)
  apply (rule_tac ?x = "y\<^sub>v" in exI)
  apply (rule_tac x = "pmf_of_set {\<lparr>x\<^sub>v = x\<^sub>v + (4::int), y\<^sub>v = y\<^sub>v\<rparr>}" in exI)
  apply (simp)
  apply (rule_tac x = "pmf_of_set {\<lparr>x\<^sub>v = x\<^sub>v + (5::int), y\<^sub>v = y\<^sub>v\<rparr>}" in exI)
  apply (simp)
  apply (rule pmf_eqI)
  apply (simp add: pmf_wplus)
  apply (case_tac "i = \<lparr>x\<^sub>v = x\<^sub>v + (4::int), y\<^sub>v = y\<^sub>v\<rparr>")
  apply auto[1]
  apply (case_tac "i = \<lparr>x\<^sub>v = x\<^sub>v + (5::int), y\<^sub>v = y\<^sub>v\<rparr>")
  apply auto[1]
  proof -
    fix x\<^sub>v::"int" and y\<^sub>v::"int" and prob\<^sub>v::"state pmf" and i::"state"
    assume a1: "pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v + (4::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (1::real)"
    assume a2: "pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v + (5::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (3::real)"
    assume a3: "\<not> i = \<lparr>x\<^sub>v = x\<^sub>v + (4::int), y\<^sub>v = y\<^sub>v\<rparr>"
    assume a4: "\<not> i = \<lparr>x\<^sub>v = x\<^sub>v + (5::int), y\<^sub>v = y\<^sub>v\<rparr>"
    show "pmf prob\<^sub>v i =
       indicat_real {\<lparr>x\<^sub>v = x\<^sub>v + (4::int), y\<^sub>v = y\<^sub>v\<rparr>} i / (4::real) +
       indicat_real {\<lparr>x\<^sub>v = x\<^sub>v + (5::int), y\<^sub>v = y\<^sub>v\<rparr>} i \<cdot> (3::real) / (4::real)"
      apply (subst pmf_not_in_the_two_is_zero[where a = "1/4" and 
          sa="\<lparr>x\<^sub>v = x\<^sub>v + (4::int), y\<^sub>v = y\<^sub>v\<rparr>" and 
          sb="\<lparr>x\<^sub>v = x\<^sub>v + (5::int), y\<^sub>v = y\<^sub>v\<rparr>"])
      apply simp+
      using a1 apply simp
      using a2 apply simp
      apply (simp add: a3 a4)
      by (simp add: a3 a4)
  qed

lemma ex6_1: "
  (P1 ;;\<^sub>p (P2 \<triangleleft> U(x = 0) \<triangleright>\<^sub>D P3))
  = U(true \<turnstile>\<^sub>n ( 
    ($prob\<acute>($\<^bold>v\<lbrakk>2/$x\<rbrakk>) = 1/6 \<and> 
     $prob\<acute>($\<^bold>v\<lbrakk>3/$x\<rbrakk>) = 1/6 \<and>
     $prob\<acute>($\<^bold>v\<lbrakk>5/$x\<rbrakk>) = 1/6 \<and> 
     $prob\<acute>($\<^bold>v\<lbrakk>6/$x\<rbrakk>) = 1/2)))"
  apply (simp add: P1_alt P2_alt P3_alt)
  apply (simp add: kleisli_lift_alt_def kleisli_lift2'_def)
  apply (ndes_simp)
  apply (rule ndesign_eq_intro)
  apply (rel_simp)
  apply (metis (full_types) Collect_cong lit.rep_eq order_top_class.top.extremum_unique top1I 
      top_set_def upred_ref_iff upred_set.rep_eq sum_pmf_eq_1)
  apply (rel_auto)
proof -
  fix y\<^sub>v::"int" and prob\<^sub>v::"state pmf" and prob\<^sub>v'::"state pmf" and x::"state \<Rightarrow> state pmf"
  let ?s1 = "\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>"
  let ?s2 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>"
  assume a1: "pmf prob\<^sub>v' \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (3::real) = (1::real)"
  assume a2: "pmf prob\<^sub>v' \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (3::real) = (2::real)"
  assume a3: " \<forall>(x\<^sub>v::int) y\<^sub>v::int.
          (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
          (\<forall>prob\<^sub>v::state pmf.
              x\<^sub>v = (0::int) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<or>
              \<not> x\<^sub>v = (0::int) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v + (4::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v + (5::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (3::real) \<or>
              (\<exists>(x\<^sub>v'::int) y\<^sub>v'::int.
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
  from a3 have a3': "\<forall>(x\<^sub>v::int) y\<^sub>v::int.
          (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
          (
              x\<^sub>v = (0::int) \<and>
              pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<or>
              \<not> x\<^sub>v = (0::int) \<and>
              pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v + (4::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (1::real) \<and>
              pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v + (5::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (3::real))"
    by blast
  have a3'': "pmf (x ?s1) \<lparr>x\<^sub>v = (2::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf (x ?s1) \<lparr>x\<^sub>v = (3::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real)"
    using a3' a1 by force
  have a3''': "pmf (x ?s2) \<lparr>x\<^sub>v = (5::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (1::real) \<and>
              pmf (x ?s2) \<lparr>x\<^sub>v = (6::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (3::real)"
    using a3' a2 by smt 
  have f1: "pmf (x ?s2) \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr> = 0"
    apply (subst pmf_not_in_the_two_is_zero[where a = "1/4" and 
          sa="\<lparr>x\<^sub>v = (5::int), y\<^sub>v = y\<^sub>v\<rparr>" and 
          sb="\<lparr>x\<^sub>v = (6::int), y\<^sub>v = y\<^sub>v\<rparr>"])
         apply (simp)+
    using a3''' by simp+
  have f2: "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr>) = 
    pmf prob\<^sub>v' ?s1 \<cdot> pmf (x ?s1) \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr> + 
    pmf prob\<^sub>v' ?s2 \<cdot> pmf (x ?s2) \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr>"
    apply (subst infsetsum_two'[where xa="?s1" and xb="?s2"])
    apply simp
    using a1 a2 apply simp
    by (simp)
  have f3: "pmf prob\<^sub>v' ?s1 \<cdot> pmf (x ?s1) \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr> = 1/3 * 1/2"
    using a1 a3'' apply auto
    by (smt distrib_left mult_cancel_left1)
  have f4: "pmf prob\<^sub>v' ?s2 \<cdot> pmf (x ?s2) \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr> = pmf prob\<^sub>v' ?s2 \<cdot> 0"
    by (simp add: f1)
  show "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr>) \<cdot> (6::real) = (1::real)"
    using f3 f4 f2 by simp
next
  fix y\<^sub>v::"int" and prob\<^sub>v::"state pmf" and prob\<^sub>v'::"state pmf" and x::"state \<Rightarrow> state pmf"
  let ?s1 = "\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>"
  let ?s2 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>"
  assume a1: "pmf prob\<^sub>v' \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (3::real) = (1::real)"
  assume a2: "pmf prob\<^sub>v' \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (3::real) = (2::real)"
  assume a3: " \<forall>(x\<^sub>v::int) y\<^sub>v::int.
          (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
          (\<forall>prob\<^sub>v::state pmf.
              x\<^sub>v = (0::int) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<or>
              \<not> x\<^sub>v = (0::int) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v + (4::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v + (5::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (3::real) \<or>
              (\<exists>(x\<^sub>v'::int) y\<^sub>v'::int.
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
  from a3 have a3': "\<forall>(x\<^sub>v::int) y\<^sub>v::int.
          (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
          (
              x\<^sub>v = (0::int) \<and>
              pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<or>
              \<not> x\<^sub>v = (0::int) \<and>
              pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v + (4::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (1::real) \<and>
              pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v + (5::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (3::real))"
    by blast
  have a3'': "pmf (x ?s1) \<lparr>x\<^sub>v = (2::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf (x ?s1) \<lparr>x\<^sub>v = (3::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real)"
    using a3' a1 by force
  have a3''': "pmf (x ?s2) \<lparr>x\<^sub>v = (5::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (1::real) \<and>
              pmf (x ?s2) \<lparr>x\<^sub>v = (6::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (3::real)"
    using a3' a2 by smt 
  have f1: "pmf (x ?s2) \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr> = 0"
    apply (subst pmf_not_in_the_two_is_zero[where a = "1/4" and 
          sa="\<lparr>x\<^sub>v = (5::int), y\<^sub>v = y\<^sub>v\<rparr>" and 
          sb="\<lparr>x\<^sub>v = (6::int), y\<^sub>v = y\<^sub>v\<rparr>"])
         apply (simp)+
    using a3''' by simp+
  have f2: "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr>) = 
    pmf prob\<^sub>v' ?s1 \<cdot> pmf (x ?s1) \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr> + 
    pmf prob\<^sub>v' ?s2 \<cdot> pmf (x ?s2) \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr>"
    apply (subst infsetsum_two'[where xa="?s1" and xb="?s2"])
    apply simp
    using a1 a2 apply simp
    by (simp)
  have f3: "pmf prob\<^sub>v' ?s1 \<cdot> pmf (x ?s1) \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr> = 1/3 * 1/2"
    using a1 a3'' apply auto
    by (smt distrib_left mult_cancel_left1)
  have f4: "pmf prob\<^sub>v' ?s2 \<cdot> pmf (x ?s2) \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr> = pmf prob\<^sub>v' ?s2 \<cdot> 0"
    by (simp add: f1)
  show "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr>) \<cdot> (6::real) = (1::real)"
    using f3 f4 f2 by simp
next
  fix y\<^sub>v::"int" and prob\<^sub>v::"state pmf" and prob\<^sub>v'::"state pmf" and x::"state \<Rightarrow> state pmf"
  let ?s1 = "\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>"
  let ?s2 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>"
  assume a1: "pmf prob\<^sub>v' \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (3::real) = (1::real)"
  assume a2: "pmf prob\<^sub>v' \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (3::real) = (2::real)"
  assume a3: " \<forall>(x\<^sub>v::int) y\<^sub>v::int.
          (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
          (\<forall>prob\<^sub>v::state pmf.
              x\<^sub>v = (0::int) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<or>
              \<not> x\<^sub>v = (0::int) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v + (4::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v + (5::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (3::real) \<or>
              (\<exists>(x\<^sub>v'::int) y\<^sub>v'::int.
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
  from a3 have a3': "\<forall>(x\<^sub>v::int) y\<^sub>v::int.
          (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
          (
              x\<^sub>v = (0::int) \<and>
              pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<or>
              \<not> x\<^sub>v = (0::int) \<and>
              pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v + (4::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (1::real) \<and>
              pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v + (5::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (3::real))"
    by blast
  have a3'': "pmf (x ?s1) \<lparr>x\<^sub>v = (2::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf (x ?s1) \<lparr>x\<^sub>v = (3::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real)"
    using a3' a1 by force
  have a3''': "pmf (x ?s2) \<lparr>x\<^sub>v = (5::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (1::real) \<and>
              pmf (x ?s2) \<lparr>x\<^sub>v = (6::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (3::real)"
    using a3' a2 by smt 
  have f1: "pmf (x ?s1) \<lparr>x\<^sub>v = 5::int, y\<^sub>v = y\<^sub>v\<rparr> = 0"
    apply (subst pmf_not_in_the_two_is_zero[where a = "1/2" and 
          sa="\<lparr>x\<^sub>v = (2::int), y\<^sub>v = y\<^sub>v\<rparr>" and 
          sb="\<lparr>x\<^sub>v = (3::int), y\<^sub>v = y\<^sub>v\<rparr>"])
         apply (simp)+
    using a3'' by simp+
  have f2: "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 5::int, y\<^sub>v = y\<^sub>v\<rparr>) = 
    pmf prob\<^sub>v' ?s1 \<cdot> pmf (x ?s1) \<lparr>x\<^sub>v = 5::int, y\<^sub>v = y\<^sub>v\<rparr> + 
    pmf prob\<^sub>v' ?s2 \<cdot> pmf (x ?s2) \<lparr>x\<^sub>v = 5::int, y\<^sub>v = y\<^sub>v\<rparr>"
    apply (subst infsetsum_two'[where xa="?s1" and xb="?s2"])
    apply simp
    using a1 a2 apply simp
    by (simp)
  have f3: "pmf prob\<^sub>v' ?s1 \<cdot> pmf (x ?s1) \<lparr>x\<^sub>v = 5::int, y\<^sub>v = y\<^sub>v\<rparr> = 1/3 * 0"
    by (simp add: f1)
  have f4: "pmf prob\<^sub>v' ?s2 \<cdot> pmf (x ?s2) \<lparr>x\<^sub>v = 5::int, y\<^sub>v = y\<^sub>v\<rparr> = 2/3 \<cdot> 1/4"
    using a2 a3''' apply auto
    by (metis a2 mult.assoc mult.commute mult_2 numeral_Bit0)
  show "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 5::int, y\<^sub>v = y\<^sub>v\<rparr>) \<cdot> (6::real) = (1::real)"
    using f3 f4 f2 by simp
next
  fix y\<^sub>v::"int" and prob\<^sub>v::"state pmf" and prob\<^sub>v'::"state pmf" and x::"state \<Rightarrow> state pmf"
  let ?s1 = "\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>"
  let ?s2 = "\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>"
  assume a1: "pmf prob\<^sub>v' \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (3::real) = (1::real)"
  assume a2: "pmf prob\<^sub>v' \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (3::real) = (2::real)"
  assume a3: " \<forall>(x\<^sub>v::int) y\<^sub>v::int.
          (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
          (\<forall>prob\<^sub>v::state pmf.
              x\<^sub>v = (0::int) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<or>
              \<not> x\<^sub>v = (0::int) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v + (4::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (1::real) \<and>
              pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v + (5::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (3::real) \<or>
              (\<exists>(x\<^sub>v'::int) y\<^sub>v'::int.
                  \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                     pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))"
  from a3 have a3': "\<forall>(x\<^sub>v::int) y\<^sub>v::int.
          (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
          (
              x\<^sub>v = (0::int) \<and>
              pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<or>
              \<not> x\<^sub>v = (0::int) \<and>
              pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v + (4::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (1::real) \<and>
              pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v + (5::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (3::real))"
    by blast
  have a3'': "pmf (x ?s1) \<lparr>x\<^sub>v = (2::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<and>
              pmf (x ?s1) \<lparr>x\<^sub>v = (3::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real)"
    using a3' a1 by force
  have a3''': "pmf (x ?s2) \<lparr>x\<^sub>v = (5::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (1::real) \<and>
              pmf (x ?s2) \<lparr>x\<^sub>v = (6::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (3::real)"
    using a3' a2 by smt 
  have f1: "pmf (x ?s1) \<lparr>x\<^sub>v = 6::int, y\<^sub>v = y\<^sub>v\<rparr> = 0"
    apply (subst pmf_not_in_the_two_is_zero[where a = "1/2" and 
          sa="\<lparr>x\<^sub>v = (2::int), y\<^sub>v = y\<^sub>v\<rparr>" and 
          sb="\<lparr>x\<^sub>v = (3::int), y\<^sub>v = y\<^sub>v\<rparr>"])
         apply (simp)+
    using a3'' by simp+
  have f2: "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 6::int, y\<^sub>v = y\<^sub>v\<rparr>) = 
    pmf prob\<^sub>v' ?s1 \<cdot> pmf (x ?s1) \<lparr>x\<^sub>v = 6::int, y\<^sub>v = y\<^sub>v\<rparr> + 
    pmf prob\<^sub>v' ?s2 \<cdot> pmf (x ?s2) \<lparr>x\<^sub>v = 6::int, y\<^sub>v = y\<^sub>v\<rparr>"
    apply (subst infsetsum_two'[where xa="?s1" and xb="?s2"])
    apply simp
    using a1 a2 apply simp
    by (simp)
  have f3: "pmf prob\<^sub>v' ?s1 \<cdot> pmf (x ?s1) \<lparr>x\<^sub>v = 6::int, y\<^sub>v = y\<^sub>v\<rparr> = 1/3 * 0"
    by (simp add: f1)
  have f4: "pmf prob\<^sub>v' ?s2 \<cdot> pmf (x ?s2) \<lparr>x\<^sub>v = 6::int, y\<^sub>v = y\<^sub>v\<rparr> = 2/3 \<cdot> 3/4"
    using a2 a3''' apply auto
    proof -
      assume a1: "pmf (x \<lparr>x\<^sub>v = 1, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 5, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> 4 = 1"
      assume a2: "pmf (x \<lparr>x\<^sub>v = 1, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 6, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> 4 = 3"
      assume a3: "pmf prob\<^sub>v' \<lparr>x\<^sub>v = 1, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> 3 = 2"
      have f4: "\<forall>n r. 2 \<cdot> ((r::real) \<cdot> numeral n) = r \<cdot> numeral (num.Bit0 n)"
        by simp
        have f5: "\<forall>r ra. 2 \<cdot> ((ra::real) \<cdot> (r \<cdot> 1)) = ra \<cdot> (r \<cdot> 2)"
          by linarith
        have "\<forall>r. (Numeral1::real) \<cdot> r = r"
          by simp
        then have "pmf prob\<^sub>v' \<lparr>x\<^sub>v = 1, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (pmf (x \<lparr>x\<^sub>v = 1, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 6, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> 2) = 1"
        using f5 f4 a3 a2 a1 by (metis (full_types) mult.left_commute)
        then show "pmf prob\<^sub>v' \<lparr>x\<^sub>v = 1, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> pmf (x \<lparr>x\<^sub>v = 1, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = 6, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> 2 = 1"
          by linarith
      qed
  show "(\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = 6::int, y\<^sub>v = y\<^sub>v\<rparr>) \<cdot> (2::real) = (1::real)"
    using f3 f4 f2 by simp
next
  fix y\<^sub>v::"int" and prob\<^sub>v::"state pmf"
  assume a1: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (6::real) = (1::real)"
  assume a2: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (6::real) = (1::real)"
  assume a3: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 5::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (6::real) = (1::real)"
  assume a4: "pmf prob\<^sub>v \<lparr>x\<^sub>v = 6::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real)"
  let ?prob' = "pmf_of_list [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>, 1/3), 
            (\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>, 2/3)]"
  let ?x1 = "pmf_of_list [(\<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr>, 1/2), 
            (\<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr>, 1/2)]"
  let ?x2 = "pmf_of_list [(\<lparr>x\<^sub>v = (5::int), y\<^sub>v = y\<^sub>v\<rparr>, 1/4), 
            (\<lparr>x\<^sub>v = (6::int), y\<^sub>v = y\<^sub>v\<rparr>, 3/4)] "
  let ?x = "\<lambda>s. (if s = \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> then
      ?x1
      else (if s = \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> then 
      ?x2
      else pmf_of_set {\<lparr>x\<^sub>v = 1::int, y\<^sub>v = 1::int\<rparr>}))"
  show "\<exists>prob\<^sub>v'::state pmf.
          pmf prob\<^sub>v' \<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (3::real) = (1::real) \<and>
          pmf prob\<^sub>v' \<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (3::real) = (2::real) \<and>
          (\<exists>x::state \<Rightarrow> state pmf.
              (\<forall>(x\<^sub>v::int) y\<^sub>v::int.
                  pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> =
                  (\<Sum>\<^sub>aa::state. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>)) \<and>
              (\<forall>(x\<^sub>v::int) y\<^sub>v::int.
                  (0::real) < pmf prob\<^sub>v' \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr> \<longrightarrow>
                  (\<forall>prob\<^sub>v::state pmf.
                      x\<^sub>v = (0::int) \<and>
                      pmf prob\<^sub>v \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<and>
                      pmf prob\<^sub>v \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (2::real) = (1::real) \<or>
                      \<not> x\<^sub>v = (0::int) \<and>
                      pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v + (4::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (1::real) \<and>
                      pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v + (5::int), y\<^sub>v = y\<^sub>v\<rparr> \<cdot> (4::real) = (3::real) \<or>
                      (\<exists>(x\<^sub>v'::int) y\<^sub>v'::int.
                          \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr> =
                             pmf (x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v'\<rparr>))))"
    apply (rule_tac x = "?prob'" in exI)
    apply auto
    apply (subst pmf_pmf_of_list, simp add: pmf_of_list_wf_def, simp)
    apply (subst pmf_pmf_of_list, simp add: pmf_of_list_wf_def, simp)
    apply (rule_tac x = "?x" in exI)
    apply (rule conjI)
    apply (rule allI)+
  proof -
    fix x\<^sub>v::"int" and y\<^sub>v'::"int"
    have f1: "(\<Sum>\<^sub>aa::state.
          pmf (pmf_of_list
                [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>, (1::real) / (3::real)),
                 (\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>, (2::real) / (3::real))])
           a \<cdot>
          pmf (?x a) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>) = 
      (1/3) * pmf (?x1) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> + 
      (2/3) * pmf (?x2) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>"
      apply (subst infsetsum_two'[where xa="\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>" and xb="\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>"])
      apply simp
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      apply (auto)
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      apply (subst pmf_pmf_of_list)+
      by (simp add: pmf_of_list_wf_def)+
    have f2: "... = pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>"
      apply (case_tac "x\<^sub>v = (2::int) \<and> y\<^sub>v' = y\<^sub>v")
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      using a1 apply simp
      apply (case_tac "x\<^sub>v = (3::int) \<and> y\<^sub>v' = y\<^sub>v")
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      using a2 apply simp
      apply (case_tac "x\<^sub>v = (5::int) \<and> y\<^sub>v' = y\<^sub>v")
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      using a3 apply simp
      apply (case_tac "x\<^sub>v = (6::int) \<and> y\<^sub>v' = y\<^sub>v")
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      using a4 apply simp
      apply (subgoal_tac "pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> = 0")
      apply (subgoal_tac "pmf ?x1 \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> = 0")
      apply (subgoal_tac "pmf ?x2 \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> = 0")
      apply simp
      apply (rule pmf_not_in_the_two_is_zero[where a="1/4" and 
              sa="\<lparr>x\<^sub>v = 5::int, y\<^sub>v = y\<^sub>v\<rparr>" and 
              sb="\<lparr>x\<^sub>v = 6::int, y\<^sub>v = y\<^sub>v\<rparr>"])
      apply simp+
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      apply (rule pmf_not_in_the_two_is_zero[where a="1/2" and 
              sa="\<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr>" and 
              sb="\<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr>"])
      apply simp+
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      apply (rule pmf_not_in_the_one_is_zero[where 
            A = "{\<lparr>x\<^sub>v = 2, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 3, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 5, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 6, y\<^sub>v = y\<^sub>v\<rparr>}"])
      apply (subgoal_tac "infsetsum (pmf prob\<^sub>v)
        {\<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 5::int, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 6::int, y\<^sub>v = y\<^sub>v\<rparr>}
        = infsetsum (pmf prob\<^sub>v) {\<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr>} + infsetsum (pmf prob\<^sub>v) {\<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr>}
        + infsetsum (pmf prob\<^sub>v) {\<lparr>x\<^sub>v = 5::int, y\<^sub>v = y\<^sub>v\<rparr>} + infsetsum (pmf prob\<^sub>v) {\<lparr>x\<^sub>v = 6::int, y\<^sub>v = y\<^sub>v\<rparr>}")
      using a1 a2 a3 a4 apply auto[1]
      apply (subgoal_tac "(infsetsum (pmf prob\<^sub>v)
        {\<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 5::int, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 6::int, y\<^sub>v = y\<^sub>v\<rparr>}) = 
        infsetsum (pmf prob\<^sub>v) {\<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr>} + 
        infsetsum (pmf prob\<^sub>v) {\<lparr>x\<^sub>v = 5::int, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 6::int, y\<^sub>v = y\<^sub>v\<rparr>}")
      apply (subgoal_tac "infsetsum (pmf prob\<^sub>v) {\<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr>} = 
        infsetsum (pmf prob\<^sub>v) {\<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v\<rparr>} + infsetsum (pmf prob\<^sub>v) {\<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v\<rparr>}")
      apply (subgoal_tac "infsetsum (pmf prob\<^sub>v) {\<lparr>x\<^sub>v = 5::int, y\<^sub>v = y\<^sub>v\<rparr>, \<lparr>x\<^sub>v = 6::int, y\<^sub>v = y\<^sub>v\<rparr>} = 
        infsetsum (pmf prob\<^sub>v) {\<lparr>x\<^sub>v = 5::int, y\<^sub>v = y\<^sub>v\<rparr>} + infsetsum (pmf prob\<^sub>v) {\<lparr>x\<^sub>v = 6::int, y\<^sub>v = y\<^sub>v\<rparr>}")
      apply simp
      apply auto[1]
      apply auto[1]
      apply auto[1]
      by simp

    show "pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> =
       (\<Sum>\<^sub>aa::state.
          pmf (pmf_of_list
                [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>, (1::real) / (3::real)),
                 (\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>, (2::real) / (3::real))])
           a \<cdot>
          pmf (?x a) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>)"
      using f1 f2 by linarith
  next
    have f0: "\<forall>x\<^sub>v.\<forall>y\<^sub>v'.(0::real) < pmf (pmf_of_list
               [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>, (1::real) / (3::real)),
                (\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>, (2::real) / (3::real))]) \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> \<longrightarrow>
      ((x\<^sub>v = (0::int) \<or> x\<^sub>v = (1::int)) \<and> y\<^sub>v'= y\<^sub>v)"
      apply (subst pmf_pmf_of_list)+
      by (simp add: pmf_of_list_wf_def)+ 
    have f1: "(\<forall>(x\<^sub>v::int) y\<^sub>v'::int.
       (0::real)
       < pmf (pmf_of_list
               [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>, (1::real) / (3::real)),
                (\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>, (2::real) / (3::real))])
          \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> \<longrightarrow>
       (
           x\<^sub>v = (0::int) \<and>
           pmf (?x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>) \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v'\<rparr> \<cdot> (2::real) = (1::real) \<and>
           pmf (?x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>) \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v'\<rparr> \<cdot> (2::real) = (1::real) \<or>
           \<not> x\<^sub>v = (0::int) \<and>
           pmf (?x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v + (4::int), y\<^sub>v = y\<^sub>v'\<rparr> \<cdot> (4::real) = (1::real) \<and>
           pmf (?x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v + (5::int), y\<^sub>v = y\<^sub>v'\<rparr> \<cdot> (4::real) = (3::real))) 
      \<longrightarrow> (\<forall>(x\<^sub>v::int) y\<^sub>v'::int.
       (0::real)
       < pmf (pmf_of_list
               [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>, (1::real) / (3::real)),
                (\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>, (2::real) / (3::real))])
          \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> \<longrightarrow>
       (\<forall>prob\<^sub>v::state pmf.
           x\<^sub>v = (0::int) \<and>
           pmf prob\<^sub>v \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v'\<rparr> \<cdot> (2::real) = (1::real) \<and>
           pmf prob\<^sub>v \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v'\<rparr> \<cdot> (2::real) = (1::real) \<or>
           \<not> x\<^sub>v = (0::int) \<and>
           pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v + (4::int), y\<^sub>v = y\<^sub>v'\<rparr> \<cdot> (4::real) = (1::real) \<and>
           pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v + (5::int), y\<^sub>v = y\<^sub>v'\<rparr> \<cdot> (4::real) = (3::real) \<or>
           (\<exists>(x\<^sub>v'::int) y\<^sub>v''::int.
               \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v''\<rparr> =
                  pmf (?x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v''\<rparr>)))
      "
      by metis
    have f2: "(\<forall>(x\<^sub>v::int) y\<^sub>v'::int.
       (0::real)
       < pmf (pmf_of_list
               [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>, (1::real) / (3::real)),
                (\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>, (2::real) / (3::real))])
          \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> \<longrightarrow>
       (
           x\<^sub>v = (0::int) \<and>
           pmf (?x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>) \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v'\<rparr> \<cdot> (2::real) = (1::real) \<and>
           pmf (?x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>) \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v'\<rparr> \<cdot> (2::real) = (1::real) \<or>
           \<not> x\<^sub>v = (0::int) \<and>
           pmf (?x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v + (4::int), y\<^sub>v = y\<^sub>v'\<rparr> \<cdot> (4::real) = (1::real) \<and>
           pmf (?x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v + (5::int), y\<^sub>v = y\<^sub>v'\<rparr> \<cdot> (4::real) = (3::real)))"
      apply (rule allI)+
      apply (auto)
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      apply (subst pmf_pmf_of_list)+
      apply (simp add: pmf_of_list_wf_def)+
      using f0 by blast+
    show "\<forall>(x\<^sub>v::int) y\<^sub>v'::int.
       (0::real)
       < pmf (pmf_of_list
               [(\<lparr>x\<^sub>v = 0::int, y\<^sub>v = y\<^sub>v\<rparr>, (1::real) / (3::real)),
                (\<lparr>x\<^sub>v = 1::int, y\<^sub>v = y\<^sub>v\<rparr>, (2::real) / (3::real))])
          \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr> \<longrightarrow>
       (\<forall>prob\<^sub>v::state pmf.
           x\<^sub>v = (0::int) \<and>
           pmf prob\<^sub>v \<lparr>x\<^sub>v = 2::int, y\<^sub>v = y\<^sub>v'\<rparr> \<cdot> (2::real) = (1::real) \<and>
           pmf prob\<^sub>v \<lparr>x\<^sub>v = 3::int, y\<^sub>v = y\<^sub>v'\<rparr> \<cdot> (2::real) = (1::real) \<or>
           \<not> x\<^sub>v = (0::int) \<and>
           pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v + (4::int), y\<^sub>v = y\<^sub>v'\<rparr> \<cdot> (4::real) = (1::real) \<and>
           pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v + (5::int), y\<^sub>v = y\<^sub>v'\<rparr> \<cdot> (4::real) = (3::real) \<or>
           (\<exists>(x\<^sub>v'::int) y\<^sub>v''::int.
               \<not> pmf prob\<^sub>v \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v''\<rparr> =
                  pmf (?x \<lparr>x\<^sub>v = x\<^sub>v, y\<^sub>v = y\<^sub>v'\<rparr>) \<lparr>x\<^sub>v = x\<^sub>v', y\<^sub>v = y\<^sub>v''\<rparr>))"
      by (metis f2)
  qed
qed

end
