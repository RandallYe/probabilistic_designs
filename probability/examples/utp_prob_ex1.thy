section \<open> Uniform Selection Algorithms \<close>

theory utp_prob_ex1
  imports
  "../utp_prob_des_laws"
  "UTP.utp_hoare"
  "UTP.utp"
begin recall_syntax

alphabet unisel_vars = 
  i :: "nat"
  c :: "bool"


term "U(real_of_nat) |> (divide 1 U(N-i+1))"
term "U(N-i+1)"
term "get\<^bsub>i\<^esub>"
term "\<Sigma>"
term "i"
term "$i"
term "&i"
term "\<lbrakk>U(i)\<rbrakk>\<^sub>e"
term "Rep_uexpr"
term "mk\<^sub>e"
term "P\<lbrakk>x\<rightarrow>v\<rbrakk>"
term "(\<lambda>r. P \<oplus>\<^bsub>r\<^esub> Q)(r)\<lbrakk>r\<rightarrow>U(v)\<rbrakk>"
term "U(real (N-i+1))"
term "\<lceil>U(real (N-i+1))\<rceil>\<^sub><"
term "\<lceil>\<lceil>U(real (N-i+1))\<rceil>\<^sub><\<rceil>\<^sub>D"
term "\<lceil>U(real (N-i+1))\<rceil>\<^sub>D\<^sub>>"
term "(prob_choice (\<K>(c :=\<^sub>D false)) r (\<K>(i :=\<^sub>D i+1))) \<lbrakk>r\<rightarrow>(\<lceil>\<lceil>U(real (N-i+1))\<rceil>\<^sub><\<rceil>\<^sub>D)\<rbrakk>"

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

(* Use Morgan's logical constant for the weight of probabilistic choice *)
abbreviation unisel_rec_bd_choice :: 
  "nat \<Rightarrow> (unisel_vars, unisel_vars) rel_pdes" where
"unisel_rec_bd_choice N \<equiv> ((\<K>(c :=\<^sub>D false)) \<oplus>\<^sub>e\<^bsub>U(1/real (\<guillemotleft>N\<guillemotright>-i))\<^esub> (\<K>(i :=\<^sub>D i+1)))"

definition unisel_rec_bd :: "nat
     \<Rightarrow> (unisel_vars, unisel_vars) rel_pdes
     \<Rightarrow> (unisel_vars, unisel_vars) rel_pdes" where 
"unisel_rec_bd N X \<equiv> (
        (unisel_rec_bd_choice N ;; \<up>X)
          \<triangleleft> U(i < \<guillemotleft>N\<guillemotright> \<and> c) \<triangleright>\<^sub>D 
        \<K>(II\<^sub>D)
      )"

(* ================ Explain meta-subst operator a bit further ==========================

(\<lambda>y.P)(x)\<lbrakk>x\<rightarrow>v\<rbrakk> (where v is a UTP expression) is a meta-subst operator that represents
    @{text "CONST msubst (\<lambda> x. P) v"}.
 v may refer to variables used in P, and therefore we need to make sure v is evaluated before P

lift_definition msubst :: "('b \<Rightarrow> ('a, '\<alpha>) uexpr) \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr"
is "\<lambda> F v b. F (v b) b"

msubst \<equiv>
    map_fun (map_fun id Rep_uexpr) (map_fun Rep_uexpr mk\<^sub>e)
     (\<lambda>(F::?'b \<Rightarrow> ?'\<alpha> \<Rightarrow> ?'a) (v::?'\<alpha> \<Rightarrow> ?'b) b::?'\<alpha>. F (v b) b)
*)

term "(((c :=\<^sub>D \<guillemotleft>r\<guillemotright>)))\<lbrakk>r\<rightarrow>(\<lceil>\<lceil>U(c)\<rceil>\<^sub><\<rceil>\<^sub>D)\<rbrakk>"

(* To test if v will be evaluated before P. Actually, it is true from the lemma below. *)
lemma "(i :=\<^sub>D 0 ;; c :=\<^sub>D False) ;; ((\<lambda>x. (i :=\<^sub>D 1 ;; c :=\<^sub>D \<guillemotleft>x\<guillemotright>))(r))\<lbrakk>r\<rightarrow>(\<lceil>\<lceil>U(i=0)\<rceil>\<^sub><\<rceil>\<^sub>D)\<rbrakk> 
     = (i :=\<^sub>D 1 ;; c :=\<^sub>D True)"
  apply (ndes_simp)
  by (rel_auto)

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

lemma msubst_logconst_eq:
  "((\<K>(c :=\<^sub>D false)) \<oplus>\<^bsub>r\<^esub> (\<K>(i :=\<^sub>D i+1))) \<lbrakk>r\<rightarrow>(\<lceil>\<lceil>U(e)\<rceil>\<^sub><\<rceil>\<^sub>D)\<rbrakk> = 
  ((\<K>(c :=\<^sub>D false)) \<oplus>\<^sub>e\<^bsub>U(e)\<^esub> (\<K>(i :=\<^sub>D i+1)))"
  apply (simp add: prob_choice_r_def)
  apply (simp add: unisel_rec_body_pchoice_simp')
  apply (ndes_simp)
  by (rel_auto)

lemma msubst_logconst_eq'':
  "((\<K>(c :=\<^sub>D false)) \<oplus>\<^bsub>r\<^esub> (\<K>(i :=\<^sub>D i+1))) \<lbrakk>r\<rightarrow>(\<lceil>\<lceil>U(1/real (\<guillemotleft>N\<guillemotright>-i))\<rceil>\<^sub><\<rceil>\<^sub>D)\<rbrakk> = 
  ((\<K>(c :=\<^sub>D false)) \<oplus>\<^sub>e\<^bsub>U(1/real (\<guillemotleft>N\<guillemotright>-i))\<^esub> (\<K>(i :=\<^sub>D i+1)))"
  by (simp add: msubst_logconst_eq)

lemma unisel_rec_bd_choice_simp:
  "unisel_rec_bd_choice N = 
    (con\<^sub>D R \<bullet> (II\<^sub>D \<triangleleft> U(\<guillemotleft>R\<guillemotright> = (1/real (\<guillemotleft>N\<guillemotright>-i))) \<triangleright>\<^sub>D \<bottom>\<^sub>D) ;; 
        U(true \<turnstile>\<^sub>n (
            ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>R\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>R\<guillemotright>) 
              \<triangleleft> \<guillemotleft>R\<guillemotright> \<in> {0..1} \<triangleright> false)
          )
    )"
  by (simp add: prob_choice_r_def unisel_rec_body_pchoice_simp')

lemma unisel_rec_bd_simp: 
  "unisel_rec_bd N X = (
    (
      (con\<^sub>D R \<bullet> (II\<^sub>D \<triangleleft> U(\<guillemotleft>R\<guillemotright> = (1/real (\<guillemotleft>N\<guillemotright>-i))) \<triangleright>\<^sub>D \<bottom>\<^sub>D) ;; 
        U(true \<turnstile>\<^sub>n (
            ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>R\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>R\<guillemotright>) 
              \<triangleleft> \<guillemotleft>R\<guillemotright> \<in> {0..1} \<triangleright> false)
          )
      ) ;; \<up>X)
    \<triangleleft> U(i < \<guillemotleft>N\<guillemotright> \<and> c) \<triangleright>\<^sub>D 
    U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v) = 1))
)"
  by (simp add: unisel_rec_bd_choice_simp pemp_skip unisel_rec_bd_def)

subsection \<open> unisel_rec_bd_n \<close>
fun unisel_rec_bd_n :: "nat \<Rightarrow> nat \<Rightarrow> (unisel_vars, unisel_vars) rel_pdes"  where
"unisel_rec_bd_n 0 N = (\<K>(II\<^sub>D))" |
"unisel_rec_bd_n (Suc k) N = (
    (unisel_rec_bd_choice N ;; \<up> (unisel_rec_bd_n (k) N))
      \<triangleleft> U(i < \<guillemotleft>N\<guillemotright> \<and> c) \<triangleright>\<^sub>D 
    \<K>(II\<^sub>D)
  )"

\<comment> \<open> The first parameter: the current index.
    The second parameter: the number of samples. 
    Initial call:  @{text "unisel_rec_bd_n' (m-1) m"} means 'select m elements indexed from 0 to (m-1)'
   \<close>
fun unisel_rec_bd_n' :: "nat \<Rightarrow> nat \<Rightarrow> (unisel_vars, unisel_vars) rel_pdes"  where
"unisel_rec_bd_n' 0 N = (\<K>(II\<^sub>D))" |
"unisel_rec_bd_n' (Suc k) N = (
    (unisel_rec_body_choice N ;; \<up> (unisel_rec_bd_n' (k) N))
      \<triangleleft> U(i < \<guillemotleft>N\<guillemotright> \<and> c) \<triangleright>\<^sub>D 
    \<K>(II\<^sub>D)
  )"

lemma "unisel_rec_bd_n 1 1 = 
  (((con\<^sub>D R \<bullet> (II\<^sub>D \<triangleleft> U(\<guillemotleft>R\<guillemotright> = (1/real (1-i))) \<triangleright>\<^sub>D \<bottom>\<^sub>D) ;; 
        U(true \<turnstile>\<^sub>n (
            ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>R\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>R\<guillemotright>) 
              \<triangleleft> \<guillemotleft>R\<guillemotright> \<in> {0..1} \<triangleright> false)
          )
      ))
    \<triangleleft> U(i < 1 \<and> c) \<triangleright>\<^sub>D 
    U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v) = 1)))"
  apply (simp add: unisel_rec_bd_choice_simp)
  apply (subst kleisli_lift_skip_right_unit)
  apply (simp add: ndesign_H1_H3 USUP_ind_H1_H3_closed dcond_H1_H2_closed ndes_theory.bottom_closed 
      ndes_unital.Healthy_Unit seq_r_H1_H3_closed)
  using pemp_skip
  by (smt One_nat_def USUP_all_cong one_uexpr_def)

subsection \<open> Uniform selection (recursive funs) \<close>
abbreviation unisel_bd:: "nat \<Rightarrow> (unisel_vars, unisel_vars) rel_pdes" 
  where "unisel_bd n \<equiv> (unisel_rec_bd_n (n) (Suc n))"

abbreviation unisel:: "nat \<Rightarrow> (unisel_vars, unisel_vars) rel_pdes" 
  where "unisel n \<equiv> (i :=\<^sub>D 1 ;; c :=\<^sub>D true ;; unisel_rec_bd_n (n) (Suc n))"

abbreviation unisel'_bd:: "nat \<Rightarrow> (unisel_vars, unisel_vars) rel_pdes" 
  where "unisel'_bd n \<equiv> (unisel_rec_bd_n' (n) (Suc n))"

abbreviation unisel':: "nat \<Rightarrow> (unisel_vars, unisel_vars) rel_pdes" 
where "unisel' n \<equiv> (i :=\<^sub>D 0 ;; c :=\<^sub>D true ;; unisel_rec_bd_n' (n) (Suc n))"

lemma unisel_1_simp: "unisel 0 = U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>1,true/$i,$c\<rbrakk>) = 1))"
  apply (simp add: pemp_skip)
  apply (ndes_simp)
  by (rel_auto)

lemma unisel_2_simp: "unisel_rec_bd_n 1 2 = 
  (((con\<^sub>D R \<bullet> (II\<^sub>D \<triangleleft> U(\<guillemotleft>R\<guillemotright> = (1/real (2-i))) \<triangleright>\<^sub>D \<bottom>\<^sub>D) ;; 
        U(true \<turnstile>\<^sub>n (
            ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>R\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>R\<guillemotright>) 
              \<triangleleft> \<guillemotleft>R\<guillemotright> \<in> {0..1} \<triangleright> false)
          )
      ))
    \<triangleleft> U(i < 2 \<and> c) \<triangleright>\<^sub>D 
    U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v) = 1)))"
  apply (simp add: unisel_rec_bd_choice_simp)
  apply (subst kleisli_lift_skip_right_unit)
  apply (simp add: ndesign_H1_H3 USUP_ind_H1_H3_closed dcond_H1_H2_closed ndes_theory.bottom_closed 
      ndes_unital.Healthy_Unit seq_r_H1_H3_closed)
  using pemp_skip USUP_all_cong one_uexpr_def
  by (smt lit_numeral)

(*
lemma unisel_2_simp: "unisel' (Suc 0) = 
  U(true \<turnstile>\<^sub>n (
    $prob\<acute>($\<^bold>v\<lbrakk>0, false/$i, $c\<rbrakk>) = U(1/real (Suc 1)) \<and> 
    $prob\<acute>($\<^bold>v\<lbrakk>1, true/$i, $c\<rbrakk>) = U(1/real (Suc 1)))
  )"
  apply (simp add: unisel_rec_bd_choice_simp)
  apply (subst kleisli_lift_skip_right_unit)
  apply (simp add: unisel_rec_body_pchoice_simp')
  apply (rel_auto)
  apply (simp add: unisel_rec_body_pchoice_simp')
  apply (ndes_simp)
  apply (rel_auto)
  apply (simp add: numeral_2_eq_2)+
  apply blast
  oops
*)

lemma "U((c \<and> i = 0) \<turnstile>\<^sub>n (
    $prob\<acute>($\<^bold>v\<lbrakk>0, false/$i, $c\<rbrakk>) = U(1/real (Suc 1)) \<and> 
    $prob\<acute>($\<^bold>v\<lbrakk>1, true/$i, $c\<rbrakk>) = U(1/real (Suc 1)))
  ) \<sqsubseteq> unisel'_bd (Suc 0)"
  apply (simp add: unisel_rec_bd_choice_simp)
  apply (subst kleisli_lift_skip_right_unit)
  apply (simp add: unisel_rec_body_pchoice_simp')
  apply (rel_auto)
  apply (simp add: unisel_rec_body_pchoice_simp')
  by (rel_auto)

lemma "U((c \<and> i = 0) \<turnstile>\<^sub>n (
    $prob\<acute>($\<^bold>v\<lbrakk>0, false/$i, $c\<rbrakk>) = U(1/real (Suc 1)) \<and> 
    $prob\<acute>($\<^bold>v\<lbrakk>1, true/$i, $c\<rbrakk>) = U(1/real (Suc 1)))
  ) \<sqsubseteq> unisel_rec_bd_n' (1) (2)"
  apply (simp add: unisel_rec_bd_choice_simp)
  apply (subst kleisli_lift_skip_right_unit)
  apply (simp add: unisel_rec_body_pchoice_simp')
  apply (rel_auto)
  apply (simp add: unisel_rec_body_pchoice_simp')
  by (rel_auto)

find_theorems "unisel_rec_bd_n'"

lemma "U((c \<and> i = 0) \<turnstile>\<^sub>n (
    $prob\<acute>($\<^bold>v\<lbrakk>0, false/$i, $c\<rbrakk>) = U(1/real (3)) \<and> 
    $prob\<acute>($\<^bold>v\<lbrakk>1, true/$i, $c\<rbrakk>) = U(1 - 1/real (3)))
  ) \<sqsubseteq> unisel_rec_bd_n' (1) (3)"
  apply (simp add: unisel_rec_bd_choice_simp)
  apply (subst kleisli_lift_skip_right_unit)
  apply (simp add: unisel_rec_body_pchoice_simp')
  apply (rel_auto)
  apply (simp add: unisel_rec_body_pchoice_simp')
  by (rel_auto)

(*
lemma dcond_mono:
  "\<lbrakk> P\<^sub>1 \<sqsubseteq> P\<^sub>2; Q\<^sub>1 \<sqsubseteq> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (P\<^sub>1 \<triangleleft> b \<triangleright>\<^sub>D Q\<^sub>1) \<sqsubseteq> (P\<^sub>2 \<triangleleft> b \<triangleright>\<^sub>D Q\<^sub>2)"
  by (rel_auto)
*)

definition unisel_inv ::
  "nat \<Rightarrow> nat \<Rightarrow> (unisel_vars, unisel_vars) rel_pdes" where
"unisel_inv n m = U(true \<turnstile>\<^sub>n 
    ((($c \<and> $i < (\<guillemotleft>m-n\<guillemotright>)) \<Rightarrow> 
      ((\<forall>j<\<guillemotleft>n\<guillemotright>. $prob\<acute>($\<^bold>v\<lbrakk>$i+\<guillemotleft>j\<guillemotright>, false/$i, $c\<rbrakk>) = U(1/real (\<guillemotleft>m\<guillemotright>-$i))) \<and> 
      $prob\<acute>($\<^bold>v\<lbrakk>$i+\<guillemotleft>n\<guillemotright>, true/$i, $c\<rbrakk>) = U(1- real \<guillemotleft>n\<guillemotright>/real (\<guillemotleft>m\<guillemotright>-$i)))
    ) \<and>
    (U(\<not>$c) \<Rightarrow> ($prob\<acute>($\<^bold>v) = 1)))
  )"

(*
definition unisel_rec_bd_n'' :: 
  "nat \<Rightarrow> nat \<Rightarrow> (unisel_vars, unisel_vars) rel_pdes" where
"unisel_rec_bd_n'' n m = unisel_rec_bd_n' n m"
*)

find_theorems "upred_set"
lemma top_is_univ: "\<lbrakk>\<bottom>\<rbrakk>\<^sub>p = UNIV"
  apply (simp add: upred_set.rep_eq)
  by auto

(* 
  1 - 1/m 
  2 - (m-1)/m * 1/(m-1)
*)
lemma unisel_rec_bd_n'_is_N:
  shows "unisel_rec_bd_n' n m is \<^bold>N"
  apply (induction n)
  apply (simp add: pemp_skip)
   apply (simp add: ndesign_H1_H3)
  apply (simp)
  by (simp add: USUP_ind_H1_H3_closed dcond_H1_H2_closed kleisli_left_N msubst_logconst_eq'' 
      ndes_theory.bottom_closed ndes_unital.Healthy_Unit ndesign_H1_H3 pemp_skip seq_r_H1_H3_closed 
      unisel_rec_bd_choice_simp)

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

lemma unisel_rec_bd_n'_inv:
  assumes "m > n"
  shows "(unisel_inv n m) \<sqsubseteq> (unisel_rec_bd_n' (n) (m))"                                           
proof (induction n)
  case 0
  then show ?case 
    apply (simp add: pemp_skip unisel_inv_def)
    by (rel_auto)
next
  case (Suc n)
  then show ?case 
  proof -
    assume a1: "unisel_inv n m \<sqsubseteq> unisel_rec_bd_n' n m"
    have f1: "(\<K> (c :=\<^sub>D \<^U>(false)) \<oplus>\<^bsub>r\<^esub> \<K> (i :=\<^sub>D \<^U>(&i + 1)))\<lbrakk>r::real\<rightarrow>\<lceil>\<^U>(1 / real (\<guillemotleft>m\<guillemotright> - &i))\<rceil>\<^sub>D\<^sub><\<rbrakk> ;;
      \<up> (unisel_inv n m) \<triangleleft> \<^U>(&i < \<guillemotleft>m\<guillemotright> \<and> &c) \<triangleright>\<^sub>D II\<^sub>p
      \<sqsubseteq> (\<K> (c :=\<^sub>D \<^U>(false)) \<oplus>\<^bsub>r\<^esub> \<K> (i :=\<^sub>D \<^U>(&i + 1)))\<lbrakk>r::real\<rightarrow>\<lceil>\<^U>(1 / real (\<guillemotleft>m\<guillemotright> - &i))\<rceil>\<^sub>D\<^sub><\<rbrakk> ;;
      \<up> (unisel_rec_bd_n' n m) \<triangleleft> \<^U>(&i < \<guillemotleft>m\<guillemotright> \<and> &c) \<triangleright>\<^sub>D II\<^sub>p"
      apply (rule dcond_mono)
      apply (rule seqr_mono, simp)
       apply (rule kleisli_left_mono)
      using a1 apply blast
      apply (simp add: unisel_inv_def)
      apply (rel_auto)
      apply (simp add: unisel_rec_bd_n'_is_N)
      by (simp)
    have f2: "unisel_inv (Suc n) m \<sqsubseteq> 
      (\<K> (c :=\<^sub>D \<^U>(false)) \<oplus>\<^bsub>r\<^esub> \<K> (i :=\<^sub>D \<^U>(&i + 1)))\<lbrakk>r::real\<rightarrow>\<lceil>\<^U>(1 / real (\<guillemotleft>m\<guillemotright> - &i))\<rceil>\<^sub>D\<^sub><\<rbrakk> ;;
        \<up> (unisel_inv n m) \<triangleleft> \<^U>(&i < \<guillemotleft>m\<guillemotright> \<and> &c) \<triangleright>\<^sub>D II\<^sub>p"
      apply (simp add: unisel_rec_body_pchoice_simp' unisel_inv_def)
      apply (ndes_simp)
      apply (simp add: kleisli_lift_alt_def kleisli_lift2'_def)
      apply (rel_auto)
      apply (simp add: top_is_univ sum_pmf_eq_1)+
      proof -
        fix ok\<^sub>v::"bool" and i\<^sub>v::"nat" and c\<^sub>v::"bool" and ok\<^sub>v'::"bool" and prob\<^sub>v::"unisel_vars pmf" 
           and ok\<^sub>v''::"bool" and prob\<^sub>v'::"unisel_vars pmf" 
           and x::"unisel_vars \<Rightarrow> unisel_vars pmf" and xa::"nat"
        let ?s1 = "\<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr>"
        let ?s2 = "\<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>"
        let ?p_s1 = "(1::real) / (real (m - i\<^sub>v))"
        let ?p_s2 = "(1::real) - (1::real) / (real (m - i\<^sub>v))"
        assume a1: "i\<^sub>v < m"
        assume a2: "c\<^sub>v"
        assume a3: "pmf prob\<^sub>v' \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr> = ?p_s1"
        assume a4: "pmf prob\<^sub>v' \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr> = ?p_s2"
        assume a5: "\<forall>(i\<^sub>v::nat) c\<^sub>v::bool.
          pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr> =
          (\<Sum>\<^sub>aa::unisel_vars. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr>)"
        assume a6: "\<forall>(i\<^sub>v::nat) c\<^sub>v::bool.
          (0::real) < pmf prob\<^sub>v' \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr> \<longrightarrow>
          (\<forall>prob\<^sub>v::unisel_vars pmf.
              (i\<^sub>v < m - n \<longrightarrow>
               c\<^sub>v \<longrightarrow>
               (\<forall>x<n. pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v + x, c\<^sub>v = False\<rparr> = (1::real) / (real (m - i\<^sub>v))) \<and>
               (pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v + n, c\<^sub>v = True\<rparr> = (1::real) - real n / (real (m - i\<^sub>v)))) \<and>
              (c\<^sub>v \<or> pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr> = (1::real)) \<or>
              (\<exists>(i\<^sub>v'::nat) c\<^sub>v'::bool.
                  \<not> pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = c\<^sub>v'\<rparr> =
                     pmf (x \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = c\<^sub>v'\<rparr>))"
        assume a7: "i\<^sub>v < m - Suc n"
        assume a8: "xa < Suc n"

        \<comment> \<open> Depending on the value of xa (either 0 or > 0) \<close>
        show "(\<Sum>\<^sub>aa::unisel_vars. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>) =
                    (1::real) / (real (m - i\<^sub>v))"
          proof (cases "i\<^sub>v = m-1")
            case True
            then show ?thesis 
              using a7 by auto
          next
            case False
            have Fi: "i\<^sub>v < m - 1"
              using False a1 by auto
            have a6': "\<forall>(i\<^sub>v::nat) c\<^sub>v::bool.
              (0::real) < pmf prob\<^sub>v' \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr> \<longrightarrow>
              ((
                (i\<^sub>v < m - n \<longrightarrow> c\<^sub>v \<longrightarrow>
                  (\<forall>xx<n. pmf (x \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v + xx, c\<^sub>v = False\<rparr> 
                            = (1::real) / (real (m - i\<^sub>v))) \<and>
                   (pmf (x \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v + n, c\<^sub>v = True\<rparr> 
                            = (1::real) - real n / (real (m - i\<^sub>v)))
                ) \<and>
                (c\<^sub>v \<or> pmf (x \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr> = (1::real))))"
              using a6 by blast
            \<comment> \<open> From s1, it will terminate with prob 100% since c is False \<close>
            have f10: "pmf (x \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr> = (1::real)"
              using a6' a3
              by (metis a1 neq0_conv of_nat_eq_0_iff pmf_pos zero_eq_1_divide_iff zero_less_diff)
            have f10': "xa > 0 \<longrightarrow> pmf (x \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr> = (0::real)"
              apply (auto)
              apply (rule pmf_not_the_one_is_zero[where xa="\<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr>"])
              using f10 apply simp
              by simp
            \<comment> \<open> From s1, terminate is 1 and others are 0 \<close>
            have f10'': "pmf (x \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr> = 
              (if xa = 0 then (1::real) else (0::real))"
              using f10 f10' by simp
            \<comment> \<open> a6 can be further simplified \<close>
            have a6'': "(0::real) < pmf prob\<^sub>v' \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr> \<longrightarrow>
              ((
                (
                  ((\<forall>xx<n. pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> 
                            = (1::real) / (real (m - Suc i\<^sub>v))) \<and>
                  (pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = Suc i\<^sub>v + n, c\<^sub>v = True\<rparr> 
                            = (1::real) - real n / (real (m - Suc i\<^sub>v))))
                )))"
              using a6' a7
              by fastforce
            have a6''': "((\<forall>xx<n. pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> 
                            = (1::real) / (real (m - Suc i\<^sub>v))) \<and>
                  (pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = Suc i\<^sub>v + n, c\<^sub>v = True\<rparr> 
                            = (1::real) - real n / (real (m - Suc i\<^sub>v))))"
              using a4 a1 a6'' using False by auto
            \<comment> \<open> Proofs from f11 to f15 are going to show after s2, i\<^sub>v must be increased. So for i\<^sub>v, 
                the prob is 0
              f16: "pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr> = 0"   \<close>
            have f11: "(\<Sum>\<^sub>aa::unisel_vars\<in>
                {\<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> |xx. xx < n} \<union> {\<lparr>i\<^sub>v = Suc i\<^sub>v + n, c\<^sub>v = True\<rparr>}. 
                pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) a) = 
              (\<Sum>\<^sub>aa::unisel_vars\<in> {\<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> |xx. xx < n}. 
                pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) a)
            + (\<Sum>\<^sub>aa::unisel_vars\<in> {\<lparr>i\<^sub>v = Suc i\<^sub>v + n, c\<^sub>v = True\<rparr>}. pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) a)"
              unfolding infsetsum_altdef abs_summable_on_altdef
              apply (subst set_integral_Un, auto)
              using abs_summable_on_altdef apply fastforce
              using abs_summable_on_altdef by blast
            then have f12: "... = (\<Sum>\<^sub>aa::unisel_vars\<in> {\<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> |xx. xx < n}. 
                pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) a) 
                + ((1::real) - real n / (real (m - Suc i\<^sub>v)))"
              using a6''' by (smt measure_pmf_conv_infsetsum pmf.rep_eq)
    
            (* Sum of (pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr>) *)
            have f13: "
              ((\<Sum>\<^sub>aa::unisel_vars\<in> {\<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> |xx. xx < n}. 
                pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) a) 
              = ((1::real) / (real (m - Suc i\<^sub>v)))*n)"
              proof -
                have f1: "\<forall>a \<in> {\<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> |xx. xx < n}. 
                    pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) a 
                  = ((1::real) / (real (m - Suc i\<^sub>v)))"
                  using a6''' by blast
                have f2: "card {\<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> |xx. xx < n} = n"
                  apply (rule card_set_comp_uniq)
                  by auto
                show ?thesis
                  apply (subst infsetsum_uni_c[where cc="((1::real) / (real (m - Suc i\<^sub>v)))"])
                  apply simp
                  using f1 apply blast
                  using f2 by auto
              qed
            have f14: "(\<Sum>\<^sub>aa::unisel_vars\<in>
              {\<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> |xx. xx < n} \<union> {\<lparr>i\<^sub>v = Suc i\<^sub>v + n, c\<^sub>v = True\<rparr>}. 
              pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) a) = 
              ((1::real) / (real (m - Suc i\<^sub>v)))*n + 
              ((1::real) - real n / (real (m - Suc i\<^sub>v)))"
              using f11 f12 f13 by simp
            have f15: "... = 1"
              by simp
            have f_not_in1: "\<not> \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr> \<in> 
              {uu::unisel_vars. \<exists>xx::nat. uu = \<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> \<and> xx < n}"
              by simp
            have f15': "\<not> \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr>
             \<in> {uu::unisel_vars. \<exists>xx::nat. uu = \<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> \<and> xx < n} \<union>
                {\<lparr>i\<^sub>v = Suc i\<^sub>v + n, c\<^sub>v = True\<rparr>}"
              using f_not_in1 by blast
            have f16: "pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr> = (0::real)"
              apply (rule pmf_not_in_the_one_is_zero[where 
                    A="{\<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> |xx. xx < n} \<union> {\<lparr>i\<^sub>v = Suc i\<^sub>v + n, c\<^sub>v = True\<rparr>}"])
              using f14 f15 apply simp
              using f15' by blast
            \<comment> \<open> Calculate pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr> \<close>
            have f17: "pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr> 
                  = (if xa = 0 then 0 else (1::real) / (real (m - Suc i\<^sub>v)))"
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
                have f112: "xa - 1 < n"
                  using a8 False by linarith
                have "pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = Suc i\<^sub>v + xa - 1, c\<^sub>v = False\<rparr>
                  = (1::real) / (real (m - Suc i\<^sub>v))"
                  using a8 a6''' False f112 by auto
                then show ?thesis 
                  using a8 a6''' by (simp add: False)
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
            (*
            have a5': "pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr> = 
                 (\<Sum>\<^sub>aa::unisel_vars. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>)"
              using a5 by blast
            *)
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
                         then ?p_s2 \<cdot> (if xa = 0 then 0 else (1::real) / (real (m - Suc i\<^sub>v)))
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
                         then ?p_s2 \<cdot> (if xa = 0 then 0 else (1::real) / (real (m - Suc i\<^sub>v)))
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
                  using f111 f112 f113 f114 by simp
              next
                case False
                have p_s2': "?p_s2 = ((real (m - i\<^sub>v) - 1) / (real (m - i\<^sub>v)))"
                  by (smt a1 add_divide_distrib divide_less_eq_1_pos less_divide_eq_1_pos 
                      of_nat_0_less_iff zero_less_diff)
                have f110: "(real (m - i\<^sub>v) - 1) = (real (m - Suc i\<^sub>v))"
                  using a1 by linarith
                have f110': "(real (m - Suc i\<^sub>v)) > 0"
                  using Fi by linarith
                have f111: "(\<Sum>\<^sub>aa::unisel_vars. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = i\<^sub>v + xa, c\<^sub>v = False\<rparr>)
                  = (\<Sum>\<^sub>aa::unisel_vars\<in>{?s1,?s2}\<union>({x. x \<notin> {?s1,?s2}}). 
                  (if a = ?s1 
                   then ?p_s1 \<cdot> (if xa = 0 then (1::real) else (0::real))
                   else (if a = ?s2 
                         then ?p_s2 \<cdot> (if xa = 0 then 0 else (1::real) / (real (m - Suc i\<^sub>v)))
                         else 0)))"
                  by (metis f18' f18'' f18''' f18''''' s1_s2_all)
                have f112: "... = (\<Sum>\<^sub>aa::unisel_vars\<in>{?s1,?s2}\<union>({x. x \<notin> {?s1,?s2}}). 
                  (if a = ?s1 
                   then ?p_s1 \<cdot> (0::real)
                   else (if a = ?s2 then ?p_s2 \<cdot> ((1::real) / (real (m - Suc i\<^sub>v))) else 0)))"
                  using False by simp
                have f113: "... = (\<Sum>\<^sub>aa::unisel_vars. 
                  (if a = ?s2 then ?p_s2 \<cdot> ((1::real) / (real (m - Suc i\<^sub>v))) else 0))"
                  using s1_s2_all
                  by (smt infsetsum_cong unisel_vars.iffs)
                have f114: "... = ?p_s2 \<cdot> ((1::real) / (real (m - Suc i\<^sub>v)))"
                  apply (subst infsetsum_single)
                  by simp
                have f115: "... = ((real (m - i\<^sub>v) - 1) / (real (m - i\<^sub>v))) \<cdot>
                    ((1::real) / (real (m - Suc i\<^sub>v)))"
                  by (simp add: p_s2')
                then show ?thesis 
                  using f110 f111 f112 f113 f114 f115 Fi f110'
                  by (simp)
              qed
          qed
      next
        fix ok\<^sub>v::"bool" and i\<^sub>v::"nat" and c\<^sub>v::"bool" and ok\<^sub>v'::"bool" and prob\<^sub>v::"unisel_vars pmf" 
           and ok\<^sub>v''::"bool" and prob\<^sub>v'::"unisel_vars pmf" 
           and x::"unisel_vars \<Rightarrow> unisel_vars pmf"
        let ?s1 = "\<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr>"
        let ?s2 = "\<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>"
        let ?s' = "\<lparr>i\<^sub>v = Suc (i\<^sub>v + n), c\<^sub>v = True\<rparr>"
        let ?p_s1 = "(1::real) / (real (m - i\<^sub>v))"
        let ?p_s2 = "(1::real) - (1::real) / ( real (m - i\<^sub>v))"
        assume a1: "i\<^sub>v < m"
        assume a2: "c\<^sub>v"
        assume a3: "pmf prob\<^sub>v' \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr> = (1::real) / (real (m - i\<^sub>v))"
        assume a4: "pmf prob\<^sub>v' \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr> = (1::real) - (1::real) / (real (m - i\<^sub>v))"
        assume a5: "\<forall>(i\<^sub>v::nat) c\<^sub>v::bool.
          pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr> =
          (\<Sum>\<^sub>aa::unisel_vars. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr>)"
        assume a6: "\<forall>(i\<^sub>v::nat) c\<^sub>v::bool.
          (0::real) < pmf prob\<^sub>v' \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr> \<longrightarrow>
          (\<forall>prob\<^sub>v::unisel_vars pmf.
              (i\<^sub>v < m - n \<longrightarrow>
               c\<^sub>v \<longrightarrow>
               (\<forall>x<n. pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v + x, c\<^sub>v = False\<rparr> = (1::real) / (real (m - i\<^sub>v))) \<and>
               (pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v + n, c\<^sub>v = True\<rparr> = (1::real) - real n / (real (m - i\<^sub>v)))) \<and>
              (c\<^sub>v \<or> pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr> = (1::real)) \<or>
              (\<exists>(i\<^sub>v'::nat) c\<^sub>v'::bool.
                  \<not> pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = c\<^sub>v'\<rparr> =
                     pmf (x \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = c\<^sub>v'\<rparr>))"
        assume a7: "i\<^sub>v < m - Suc n"
        show "(\<Sum>\<^sub>aa::unisel_vars. pmf prob\<^sub>v' a \<cdot> pmf (x a) \<lparr>i\<^sub>v = Suc (i\<^sub>v + n), c\<^sub>v = True\<rparr>) =
          (1::real) - ((1::real) + real n) / (real (m - i\<^sub>v))"
          proof (cases "i\<^sub>v = m-1")
            case True
            then show ?thesis 
              using a7 by auto
          next
            case False
            have Fi: "i\<^sub>v < m - 1"
              using False a1 by auto
            have a6': "\<forall>(i\<^sub>v::nat) c\<^sub>v::bool.
              (0::real) < pmf prob\<^sub>v' \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr> \<longrightarrow>
              ((
                (i\<^sub>v < m - n \<longrightarrow> c\<^sub>v \<longrightarrow>
                  (\<forall>xx<n. pmf (x \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v + xx, c\<^sub>v = False\<rparr> 
                            = (1::real) / (real (m - i\<^sub>v))) \<and>
                   (pmf (x \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v + n, c\<^sub>v = True\<rparr> 
                            = (1::real) - real n / (real (m - i\<^sub>v)))
                ) \<and>
                (c\<^sub>v \<or> pmf (x \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = c\<^sub>v\<rparr> = (1::real))))"
              using a6 by blast
            \<comment> \<open> a6 can be further simplified \<close>
            have a6'': "(0::real) < pmf prob\<^sub>v' \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr> \<longrightarrow>
              ((
                (
                  ((\<forall>xx<n. pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> 
                            = (1::real) / (real (m - Suc i\<^sub>v))) \<and>
                  (pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = Suc i\<^sub>v + n, c\<^sub>v = True\<rparr> 
                            = (1::real) - real n / (real (m - Suc i\<^sub>v))))
                )))"
              using a6' a7
              by fastforce
            have a6''': "((\<forall>xx<n. pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = Suc i\<^sub>v + xx, c\<^sub>v = False\<rparr> 
                            = (1::real) / (real (m - Suc i\<^sub>v))) \<and>
                  (pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = Suc i\<^sub>v + n, c\<^sub>v = True\<rparr> 
                            = (1::real) - real n / (real (m - Suc i\<^sub>v))))"
              using a4 a1 a6'' Fi by auto
            have f10: "(pmf (x \<lparr>i\<^sub>v = Suc i\<^sub>v, c\<^sub>v = True\<rparr>) \<lparr>i\<^sub>v = Suc i\<^sub>v + n, c\<^sub>v = True\<rparr> 
                            = (1::real) - real n / (real (m - Suc i\<^sub>v)))"
              using a6''' by simp
    
            \<comment> \<open> From s1, it will terminate with prob 100% since c is False. \<close>
            have f11: "pmf (x \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr>) \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr> = (1::real)"
              using a6' a3 Fi 
              by (metis a1 linorder_neqE_linordered_idom of_nat_eq_0_iff of_nat_less_0_iff 
                  zero_less_diff zero_less_divide_1_iff zero_less_iff_neq_zero)
            \<comment> \<open> From s1, elsewhere it is zero. \<close>
            have f11': "pmf (x ?s1) ?s' = (0::real)"
              apply (rule pmf_not_the_one_is_zero[where xa="\<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr>"])
              using f11 apply simp
              by simp
    
            have f12: "pmf (x ?s2) ?s' = 
              (1::real) - real n / (real (m - Suc i\<^sub>v))"
              using a6''' by simp
    
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
                         then ?p_s2 \<cdot> ((1::real) - real n / (real (m - Suc i\<^sub>v)))
                         else 0)))"
              using f11' f12 by presburger
            have f13''''': "... = (\<Sum>\<^sub>aa::unisel_vars.
                  (if a = ?s2 
                   then ?p_s2 \<cdot> ((1::real) - real n / (real (m - Suc i\<^sub>v)))
                   else 0))"
              by (metis mult_zero_right unisel_vars.ext_inject)
            \<comment> \<open> @{text "pmf (x ?s1) \<lparr>i\<^sub>v = Suc (i\<^sub>v + n), c\<^sub>v = True\<rparr> = 0"}
                 @{text "pmf prob\<^sub>v' ?s1 = (1::real) - (1::real) / ((1::real) + real (m - i\<^sub>v))
                    = real (m - i\<^sub>v) / ((1::real) + real (m - i\<^sub>v))"}
                 @{text "pmf (x ?s2) \<lparr>i\<^sub>v = Suc (i\<^sub>v + n), c\<^sub>v = True\<rparr> 
                    = (1::real) - real n / ((1::real) + real (m - Suc i\<^sub>v))
                    = (((1::real) + real (m - Suc i\<^sub>v)) - real n) / (real (m - i\<^sub>v))"}
               \<close>
            have f13'''''': "... = ?p_s2 \<cdot> ((1::real) - real n / (real (m - Suc i\<^sub>v)))"
              apply (subst infsetsum_single)
              by simp
            have p_s2_simp: "?p_s2 = (real (m - i\<^sub>v) - 1) / (real (m - i\<^sub>v))"
              by (metis (no_types) Suc_diff_Suc a1 add_divide_distrib add_uminus_conv_diff 
                  divide_minus_left divide_self nat.distinct(1) of_nat_eq_0_iff)
            have p_s'_simp': "(real (m - i\<^sub>v) - 1) = (real (m - Suc i\<^sub>v))"
              using a1 by linarith
            have p_s'_simp: "((1::real) - real n / (real (m - Suc i\<^sub>v)))
              = ((real (m - Suc i\<^sub>v) - real n) / (real (m - Suc i\<^sub>v)))"
              by (metis (no_types, hide_lams) Fi add_divide_distrib add_uminus_conv_diff 
                  diff_Suc_eq_diff_pred diff_is_0_eq divide_minus_left divide_self not_le of_nat_eq_0_iff)
            have p_s'_simp'': "... = (((real (m - i\<^sub>v) - 1) - real n) / (real (m - i\<^sub>v) - 1))"
              using p_s'_simp' by simp
            have p_s2_s'_simp: "?p_s2 \<cdot> ((1::real) - real n / (real (m - Suc i\<^sub>v)))
              = (real (m - i\<^sub>v) - 1) / (real (m - i\<^sub>v)) \<cdot> (((real (m - i\<^sub>v) - 1) - real n) / (real (m - i\<^sub>v) - 1))"
              by (simp add: p_s'_simp p_s'_simp'' p_s2_simp)
            have p_s2_s'_simp': "... = ((real (m - i\<^sub>v) - 1) - real n) / (real (m - i\<^sub>v))"
              using Fi by simp
            have ret_simp: "(1::real) - ((1::real) + real n) / (real (m - i\<^sub>v))
                = ((real (m - i\<^sub>v) - (1 + real n)) / (real (m - i\<^sub>v)))"
              by (smt diff_divide_distrib p_s2_simp)
            show ?thesis
              using f13 f13' f13'' f13''' f13'''' f13''''' f13'''''' p_s2_s'_simp p_s2_s'_simp' ret_simp by auto
          qed
        qed
    show "unisel_inv (Suc n) m \<sqsubseteq> unisel_rec_bd_n' (Suc n) m"
      using f1 f2 by auto
  qed
qed

lemma unisel_inv_contr:
  assumes "m > n"
  shows "(i :=\<^sub>D 0 ;; c :=\<^sub>D true ;; (unisel_inv n m)) \<sqsubseteq> (i :=\<^sub>D 0 ;; c :=\<^sub>D true ;; (unisel_rec_bd_n' (n) (m)))"
  apply (rule seqr_mono, simp)
  apply (rule seqr_mono, simp)
  by (simp add: assms unisel_rec_bd_n'_inv)

lemma unisel_inv_simp:
  assumes "m > 1"
  shows "(i :=\<^sub>D 0 ;; c :=\<^sub>D true ;; (unisel_inv (m-1) m)) = 
    U(true \<turnstile>\<^sub>n 
    ((
      ((\<forall>j<\<guillemotleft>m-1\<guillemotright>. $prob\<acute>($\<^bold>v\<lbrakk>\<guillemotleft>j\<guillemotright>, false/$i, $c\<rbrakk>) = U(1/real (\<guillemotleft>m\<guillemotright>))) \<and> 
      $prob\<acute>($\<^bold>v\<lbrakk>\<guillemotleft>m-1\<guillemotright>, true/$i, $c\<rbrakk>) = U(1- real \<guillemotleft>m-1\<guillemotright>/real (\<guillemotleft>m\<guillemotright>)))
    ))
  )"
  apply (simp add: unisel_inv_def)
  apply (ndes_simp)
  apply (rel_auto)
  using assms by simp

lemma unisel_contract:
  assumes "m > 1"
  shows "U(true \<turnstile>\<^sub>n 
    ((
      ((\<forall>j<\<guillemotleft>m-1\<guillemotright>. $prob\<acute>($\<^bold>v\<lbrakk>\<guillemotleft>j\<guillemotright>, false/$i, $c\<rbrakk>) = U(1/real (\<guillemotleft>m\<guillemotright>))) \<and> 
      $prob\<acute>($\<^bold>v\<lbrakk>\<guillemotleft>m-1\<guillemotright>, true/$i, $c\<rbrakk>) = U(1- real \<guillemotleft>m-1\<guillemotright>/real (\<guillemotleft>m\<guillemotright>)))
    ))
  ) \<sqsubseteq> (i :=\<^sub>D 0 ;; c :=\<^sub>D true ;; (unisel_rec_bd_n' (m-1) (m)))"
  using unisel_inv_contr unisel_inv_simp 
proof -
  have "(i :=\<^sub>D (\<^U>(0)::(nat, unisel_vars) uexpr) ;; 
        (c :=\<^sub>D (\<^U>(true)::unisel_vars upred) ;; 
        unisel_inv (m - 1) m::(unisel_vars, unisel_vars) rel_pdes)::(unisel_vars, unisel_vars) rel_pdes) 
      \<sqsubseteq> i :=\<^sub>D (\<^U>(0)::(nat, unisel_vars) uexpr) ;; (c :=\<^sub>D (\<^U>(true)::unisel_vars upred) ;; 
        unisel_rec_bd_n' (m - 1) m::(unisel_vars, unisel_vars) rel_pdes)"
    by (metis (no_types) One_nat_def assms diff_Suc_less le_less_trans unisel_inv_contr zero_le_one)
  then show ?thesis
    using assms unisel_inv_simp by force
qed

(*
  Considering a two-step example where

U(true \<turnstile>\<^sub>n 
    ((i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-$i+1))\<guillemotright> \<and> 
        $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-$i+1))\<guillemotright>)) \<and>
    (\<not>(i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v) = 1))
) ;; 
\<up> (
  U(true \<turnstile>\<^sub>n 
    ((i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-$i+1))\<guillemotright> \<and> 
        $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-$i+1))\<guillemotright>)) \<and>
    (\<not>(i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v) = 1))
  )
)
= 
U(true \<turnstile>\<^sub>n 
    ((i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-$i+1))\<guillemotright> \<and> 
        $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-$i+1))\<guillemotright>)) \<and>
    (\<not>(i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v) = 1))
) ;; 
U($prob(true) = 1 \<turnstile>\<^sub>n 
  \<exists>Q \<in> (S \<longrightarrow> PROB) \<bullet> 
    (\<forall>s \<bullet> $prob(s) > 0 \<Rightarrow> 
      (((i < N \<and> c) \<Rightarrow> (Q(s)($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-$i+1))\<guillemotright> \<and> 
        Q(s)($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-$i+1))\<guillemotright>))\<and> 
      (\<not>(i < N \<and> c) \<Rightarrow> (Q(s)($\<^bold>v) = 1)))
    ) \<and>
    (\<forall>ss \<bullet> $prob\<acute>(ss) = infsetsum (\<lambda> t. $prob(t) * (Q(t) ss)) UNIV) 
)
= 
U(true \<turnstile>\<^sub>n 
    (((i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-$i+1))\<guillemotright> \<and> 
        $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-$i+1))\<guillemotright>)) \<and>
    (\<not>(i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v) = 1))) ;; (
  \<exists>Q \<in> (S \<longrightarrow> PROB) \<bullet> 
    (\<forall>s \<bullet> $prob(s) > 0 \<Rightarrow> 
      (((i < N \<and> c) \<Rightarrow> (Q(s)($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-$i+1))\<guillemotright> \<and> 
        Q(s)($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-$i+1))\<guillemotright>))\<and> 
      (\<not>(i < N \<and> c) \<Rightarrow> (Q(s)($\<^bold>v) = 1)))
    ) \<and>
    (\<forall>ss \<bullet> $prob\<acute>(ss) = infsetsum (\<lambda> t. $prob(t) * (Q(t) ss)) UNIV) )
)
= (Q \<equiv> \<lambda>s \<bullet> if s = ($\<^bold>v\<lbrakk>false/$c\<rbrakk>) then pmf_list [(s, 1)] else 
        (if s = ($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) then pmf_list [(s, 1)] else ))
U(true \<turnstile>\<^sub>n 
    (((i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-$i+1))\<guillemotright> \<and> 
        ((i+1 < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v\<lbrakk>false,$i+1/$c,$i\<rbrakk>) = (1-\<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-$i+1))\<guillemotright>)*\<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-$i))\<guillemotright> \<and>
                           $prob\<acute>($\<^bold>v\<lbrakk>true,$i+2/$c,$i\<rbrakk>) = (1-\<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-$i+1))\<guillemotright>)*\<guillemotleft>(1-1/real (\<guillemotleft>N\<guillemotright>-$i))\<guillemotright>)
         (i+1 = N) \<Rightarrow> $prob\<acute>($\<^bold>v\<lbrakk>true,$i+1/$c,$i\<rbrakk>) = (1-\<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-$i+1))\<guillemotright>)))
    ) \<and>
    (\<not>(i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v) = 1)))
)
= {1} (N = 2 \<and> i = 1 \<and> c = true)
U(true \<turnstile>\<^sub>n 
    (((i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = 1/2 \<and> 
          (i+1 = N) \<Rightarrow> $prob\<acute>($\<^bold>v\<lbrakk>true,2/$c,$i\<rbrakk>) = 0.5))
    )
)
= {2} (c = false)
U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v) = 1)))
= {3} (N = 3 \<and> i = 1 \<and> c = true)
U(true \<turnstile>\<^sub>n 
    (((i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = 1/3 \<and> 
        ((i+1 < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v\<lbrakk>false,2/$c,$i\<rbrakk>) = 2/3*1/2 = 1/3 \<and>
                           $prob\<acute>($\<^bold>v\<lbrakk>true,3/$c,$i\<rbrakk>) = 1/3*1/2 = 1/3)
    )
)

1) N = 2 and i = 1

U(true \<turnstile>\<^sub>n 
    ((i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>R\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>R\<guillemotright>))
  \<and> (\<not>(i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v) = 1))
) ;; \<up> U(true \<turnstile>\<^sub>n 
    ((i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>R\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>R\<guillemotright>))
  \<and> (\<not>(i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v) = 1))
)
= 
U(true \<turnstile>\<^sub>n
    (($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = 1/2 \<and> $prob\<acute>($\<^bold>v\<lbrakk>2/$i\<rbrakk>) = 1/2))
) ;; \<up> U(true \<turnstile>\<^sub>n 
    ((i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>R\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>R\<guillemotright>))
  \<and> (\<not>(i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v) = 1))
)
= 
U(true \<turnstile>\<^sub>n 
    (($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = 1/2 \<and> $prob\<acute>($\<^bold>v\<lbrakk>2/$i\<rbrakk>) = 1/2))
) ;; U($prob(true) = 1 \<turnstile>\<^sub>n 
  \<exists>Q \<in> (S \<longrightarrow> PROB) \<bullet> 
    (\<forall>s \<bullet> $prob(s) > 0 \<Rightarrow> 
      (((i < N \<and> c) \<Rightarrow> (Q(s)($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>R\<guillemotright> \<and> Q(s)($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>R\<guillemotright>))\<and> 
      (\<not>(i < N \<and> c) \<Rightarrow> (Q(s)($\<^bold>v) = 1)))
    ) \<and>
    (\<forall>ss \<bullet> $prob\<acute>(ss) = infsetsum (\<lambda> t. $prob(t) * (Q(t) ss)) UNIV) 
)
= 
U(true \<and> \<not> ((($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = 1/2 \<and> $prob\<acute>($\<^bold>v\<lbrakk>2/$i\<rbrakk>) = 1/2)) ;; \<not> ($prob(true) = 1)) 
\<turnstile>\<^sub>n 
  (($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = 1/2 \<and> $prob\<acute>($\<^bold>v\<lbrakk>2/$i\<rbrakk>) = 1/2)) ;; 
  (\<exists>Q \<in> (S \<longrightarrow> PROB) \<bullet> 
    (\<forall>s \<bullet> $prob(s) > 0 \<Rightarrow> 
      (((i < N \<and> c) \<Rightarrow> (Q(s)($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>R\<guillemotright> \<and> Q(s)($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>R\<guillemotright>))\<and> 
      (\<not>(i < N \<and> c) \<Rightarrow> (Q(s)($\<^bold>v) = 1)))
    ) \<and>
    (\<forall>ss \<bullet> $prob\<acute>(ss) = infsetsum (\<lambda> t. $prob(t) * (Q(t) ss)) UNIV)) 
)
= (Q \<equiv> \<lambda> s \<bullet> (pmf_of_list [(s, 1::real)]))

U(true
\<turnstile>\<^sub>n 
  prob\<acute> ($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = 1/2 \<and> $prob\<acute>($\<^bold>v\<lbrakk>2/$i\<rbrakk>) = 1/2
)

2) N = 3 and i = 1

U(true \<turnstile>\<^sub>n 
    ((i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>R\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>R\<guillemotright>))
  \<and> (\<not>(i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v) = 1))
) ;; 
\<up> (
  U(true \<turnstile>\<^sub>n 
    ((i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>R\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>R\<guillemotright>)) \<and>
    (\<not>(i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v) = 1))
   ) ;; 
   \<up> (
      U(true \<turnstile>\<^sub>n 
        ((i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>R\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>R\<guillemotright>)) \<and>
        (\<not>(i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v) = 1))
      )
   )
)
= 
U(true \<turnstile>\<^sub>n (($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = 1/2 \<and> $prob\<acute>($\<^bold>v\<lbrakk>2/$i\<rbrakk>) = 1/2))) ;; 
\<up> (
  U(true \<turnstile>\<^sub>n 
    ((i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>R\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>R\<guillemotright>)) \<and>
    (\<not>(i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v) = 1))
   ) ;; 
   \<up> (
      U(true \<turnstile>\<^sub>n 
        ((i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>R\<guillemotright> \<and> $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>R\<guillemotright>)) \<and>
        (\<not>(i < N \<and> c) \<Rightarrow> ($prob\<acute>($\<^bold>v) = 1))
      )
   )
)
= 
U(true \<turnstile>\<^sub>n 
    (($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = 1/2 \<and> $prob\<acute>($\<^bold>v\<lbrakk>2/$i\<rbrakk>) = 1/2))
) ;; U($prob(true) = 1 \<turnstile>\<^sub>n 
  \<exists>Q \<in> (S \<longrightarrow> PROB) \<bullet> 
    (\<forall>s \<bullet> $prob(s) > 0 \<Rightarrow> 
      (((i < N \<and> c) \<Rightarrow> (Q(s)($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>R\<guillemotright> \<and> Q(s)($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>R\<guillemotright>))\<and> 
      (\<not>(i < N \<and> c) \<Rightarrow> (Q(s)($\<^bold>v) = 1)))
    ) \<and>
    (\<forall>ss \<bullet> $prob\<acute>(ss) = infsetsum (\<lambda> t. $prob(t) * (Q(t) ss)) UNIV) 
)
= 
U(true \<and> \<not> ((($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = 1/2 \<and> $prob\<acute>($\<^bold>v\<lbrakk>2/$i\<rbrakk>) = 1/2)) ;; \<not> ($prob(true) = 1)) 
\<turnstile>\<^sub>n 
  (($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = 1/2 \<and> $prob\<acute>($\<^bold>v\<lbrakk>2/$i\<rbrakk>) = 1/2)) ;; 
  (\<exists>Q \<in> (S \<longrightarrow> PROB) \<bullet> 
    (\<forall>s \<bullet> $prob(s) > 0 \<Rightarrow> 
      (((i < N \<and> c) \<Rightarrow> (Q(s)($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>R\<guillemotright> \<and> Q(s)($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>R\<guillemotright>))\<and> 
      (\<not>(i < N \<and> c) \<Rightarrow> (Q(s)($\<^bold>v) = 1)))
    ) \<and>
    (\<forall>ss \<bullet> $prob\<acute>(ss) = infsetsum (\<lambda> t. $prob(t) * (Q(t) ss)) UNIV)) 
)
= (Q \<equiv> \<lambda> s \<bullet> (pmf_of_list [(s, 1::real)]))

U(true
\<turnstile>\<^sub>n 
  prob\<acute> ($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = 1/2 \<and> $prob\<acute>($\<^bold>v\<lbrakk>2/$i\<rbrakk>) = 1/2
)

*)

subsection \<open> Uniform selection (recursion) \<close>

definition unisel_rec :: "nat \<Rightarrow> (unisel_vars, unisel_vars) rel_pdes" where
"unisel_rec N =  (\<mu>\<^sub>N X \<bullet> (unisel_rec_bd N X))"

definition unisel_rec' :: "nat \<Rightarrow> (unisel_vars, unisel_vars) rel_pdes" where
"unisel_rec' N =  (\<mu>\<^sub>N X \<bullet> (unisel_rec_body N X))"

definition unisel_1 :: "nat \<Rightarrow> (unisel_vars, unisel_vars) rel_pdes" where
"unisel_1 N = (i :=\<^sub>D 0 ;; c :=\<^sub>D true ;; unisel_rec N)"

lemma unisel_rec_eq:
  "unisel_rec N = do U(i < \<guillemotleft>N\<guillemotright> \<and> c) \<rightarrow> unisel_rec_bd_choice N od"
  apply (simp add: unisel_rec_def unisel_rec_bd_def)
  apply (subst IteratePD_singleton)
  apply (simp add: USUP_ind_H1_H3_closed dcond_H1_H2_closed ndes_theory.bottom_closed 
      ndes_unital.Healthy_Unit ndesign_H1_H3 prob_choice_r_def seq_r_H1_H3_closed 
      unisel_rec_body_pchoice_simp')
  apply (simp add: IteratePD_def)
  apply (subst AlernateD_no_ind)
  apply (simp)
  apply (simp add: USUP_ind_H1_H3_closed dcond_H1_H2_closed kleisli_lift2'_def kleisli_lift_alt_def 
      ndes_theory.bottom_closed ndes_unital.Healthy_Unit ndesign_H1_H3 prob_choice_r_def 
      seq_r_H1_H3_closed unisel_rec_body_pchoice_simp')
  apply (simp add: ndesign_H1_H3 pemp_skip)
  apply (subst AlternateD_dcond)
  apply (simp add: USUP_ind_H1_H3_closed dcond_H1_H2_closed kleisli_lift2'_def kleisli_lift_alt_def 
      ndes_theory.bottom_closed ndes_unital.Healthy_Unit ndesign_H1_H3 prob_choice_r_def 
      seq_r_H1_H3_closed unisel_rec_body_pchoice_simp')
  apply (simp add: ndesign_H1_H3 pemp_skip)
  by (simp)

(*
- Discussed with Jim about six-side die. He suggested to consider 3-sided die using a fair coin, then
combine two 3-sided die together into a 6-sided die.
- For the RANSAC algorithm, he suggested to calculate a contract for non-probabilistic part in normal 
design, then lift to probabilistic designs, afterwards compose with probabilistic parts (uniform 
selection) to get full contract.
*)

lemma des_assgns_to_simu_assgns: 
  "(i :=\<^sub>D 1 ;; c :=\<^sub>D true) = (i,c :=\<^sub>D 1,true)"
  by (rel_auto)

lemma des_assgns_to_subst: 
  "(i :=\<^sub>D 1 ;; c :=\<^sub>D true) = \<langle> (id\<^sub>s)(i \<mapsto>\<^sub>s 1, c \<mapsto>\<^sub>s true)\<rangle>\<^sub>D"
  apply (simp add: des_assgns_to_simu_assgns)
  by (simp add: pr_var_def)

find_theorems "\<mu>\<^sub>D"
thm "cond_mono"

(* Cannot prove kleisli_left_monotonic' yet. Have to restrict it to normal designs. *)
(*lemma unisel_rec_bd_mono: "Monotonic (\<lambda>X. unisel_rec_bd N X)"
  apply (simp add: unisel_rec_bd_simp)
  apply (rule cond_monotonic)
  defer
  apply (simp add: Monotonic_const)
  apply (rule seqr_monotonic)
  apply (auto intro: monoI seqr_mono cond_mono)
  using kleisli_left_monotonic' by blast
*)

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

thm "utp_des_theory.des_theory.utp_lfp_def"
thm "utp_des_theory.des_theory.LFP_unfold"
thm "mono_Monotone_utp_order"

lemma unisel_rec_bd_HH: "(\<lambda>X. unisel_rec_bd N X) \<in> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H"
  apply (simp add: Pi_def)
  apply (clarify)
  apply (simp add: unisel_rec_bd_simp)
  apply (rule dcond_H1_H2_closed')
  apply (rule seq_r_H1_H2_closed)
  apply (simp_all add: closure)
  by (simp add: kleisli_left_H)

lemma unisel_rec_bd_NN: "(\<lambda>X. unisel_rec_bd N X) \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
  apply (simp add: Pi_def)
  apply (clarify)
  apply (simp add: unisel_rec_bd_simp)
  apply (rule dcond_H1_H3_closed')
  apply (simp_all add: closure)
  by (simp add: USUP_ind_H1_H3_closed dcond_H1_H2_closed kleisli_left_N ndes_theory.bottom_closed 
      ndes_unital.Healthy_Unit ndesign_H1_H3 seq_r_H1_H3_closed)

lemma unisel_rec_bd_NN': "(\<lambda>X. (
        (unisel_rec_bd_choice N ;; \<up>X)
          \<triangleleft> U(i < \<guillemotleft>N\<guillemotright> \<and> c) \<triangleright>\<^sub>D 
        \<K>(II\<^sub>D)
      )) \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
  using unisel_rec_bd_NN 
  by (simp add: USUP_ind_H1_H3_closed dcond_H1_H2_closed kleisli_left_N ndes_theory.bottom_closed 
      ndes_unital.Healthy_Unit ndesign_H1_H3 pemp_skip prob_choice_r_def seq_r_H1_H3_closed 
      unisel_rec_body_pchoice_simp')

lemma unisel_rec_unfold:
  shows "unisel_rec N = 
    ((unisel_rec_bd_choice N ;; \<up> (unisel_rec N))
          \<triangleleft> U(i < \<guillemotleft>N\<guillemotright> \<and> c) \<triangleright>\<^sub>D 
        \<K>(II\<^sub>D))"
  \<comment> \<open> mono \<close>
  apply (simp add: unisel_rec_def unisel_rec_bd_def)
  apply (subst utp_des_theory.ndes_theory.LFP_unfold)
  apply (rule Mono_utp_orderI)
  apply (simp add: cond_mono kleisli_left_mono seqr_mono)
  \<comment> \<open> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>H\<rbrakk>\<^sub>H \<close>
  using unisel_rec_bd_NN 
   apply (simp add: USUP_ind_H1_H3_closed dcond_H1_H2_closed kleisli_left_N ndes_theory.bottom_closed 
      ndes_unital.Healthy_Unit ndesign_H1_H3 pemp_skip prob_choice_r_def seq_r_H1_H3_closed 
      unisel_rec_body_pchoice_simp')
  by (simp add: unisel_rec_bd_simp)

lemma dcond_ref_not:
  shows "(p1 \<turnstile>\<^sub>n Q) \<sqsubseteq> (P \<triangleleft> (\<not> p1) \<triangleright>\<^sub>D (true \<turnstile>\<^sub>n Q))"
  by (rel_simp)

lemma dcond_ref_not':
  shows "(\<lceil>p1\<rceil>\<^sub>< \<turnstile>\<^sub>r Q) \<sqsubseteq> (P \<triangleleft> (\<not> p1) \<triangleright>\<^sub>D (true \<turnstile>\<^sub>n Q))"
  by (metis dcond_ref_not ndesign_def)

lemma dcond_ref_not'':
  shows "`(\<lceil>p1\<rceil>\<^sub>D\<^sub>< \<Rightarrow> ((P \<triangleleft> (\<not> p1) \<triangleright>\<^sub>D Q) \<Leftrightarrow> Q))`"
  by (rel_auto)

lemma dcond_ref_not''':
  shows "`(\<lceil>p1\<rceil>\<^sub>D\<^sub>< \<Rightarrow> ((P \<triangleleft> (p1) \<triangleright>\<^sub>D Q) \<Leftrightarrow> P))`"
  by (rel_auto)

lemma assign_dcond:
  fixes x :: "'a \<Longrightarrow> 'b"
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  (* assumes "out\<alpha> \<sharp> b" *)
  shows "(x :=\<^sub>D e ;; (P \<triangleleft> b \<triangleright>\<^sub>D Q)) = (((x :=\<^sub>D e) ;; P) \<triangleleft> \<lfloor>(\<lceil>b\<rceil>\<^sub><\<lbrakk>\<lceil>e\<rceil>\<^sub></$x\<rbrakk>)\<rfloor>\<^sub>< \<triangleright>\<^sub>D ((x :=\<^sub>D e) ;; Q))"
proof -
  obtain pre\<^sub>p post\<^sub>p pre\<^sub>q post\<^sub>q
    where p:"P = (pre\<^sub>p \<turnstile>\<^sub>r post\<^sub>p)" and 
          q:"Q = (pre\<^sub>q \<turnstile>\<^sub>r post\<^sub>q)" 
    using assms by (metis H1_H2_eq_rdesign Healthy_if)
  show ?thesis
    apply (simp add: p q)
    apply (simp add: cond_def)
    apply (simp add: assigns_d_def)
    by (rel_auto)
qed

(*
lemma assign_dcond':
  fixes x :: "'a \<Longrightarrow> 'b"
  assumes "P is \<^bold>H" "Q is \<^bold>H"
  assumes "out\<alpha> \<sharp> \<lceil>b\<rceil>\<^sub>>"
  shows "(x :=\<^sub>D e ;; (P \<triangleleft> b \<triangleright>\<^sub>D Q)) = (((x :=\<^sub>D e) ;; P) \<triangleleft> \<lfloor>(\<lceil>b\<rceil>\<^sub>>\<lbrakk>\<lceil>e\<rceil>\<^sub></$x\<rbrakk>)\<rfloor>\<^sub>< \<triangleright>\<^sub>D ((x :=\<^sub>D e) ;; Q))"
  proof -
  obtain pre\<^sub>p post\<^sub>p pre\<^sub>q post\<^sub>q
    where p:"P = (pre\<^sub>p \<turnstile>\<^sub>r post\<^sub>p)" and 
          q:"Q = (pre\<^sub>q \<turnstile>\<^sub>r post\<^sub>q)" 
    using assms by (metis H1_H2_eq_rdesign Healthy_if)
  show ?thesis
    apply (simp add: p q)
    apply (simp add: cond_def)
    apply (simp add: assigns_d_def)
    apply (rel_simp)
    sorry
qed
*)

(*
lemma assign_cond:
  fixes x :: "nat \<Longrightarrow> 'c unisel_vars"
  shows "(x :=\<^sub>D e ;; (P \<triangleleft> b \<triangleright>\<^sub>D Q)) = (((x :=\<^sub>D e) ;; P) \<triangleleft> b\<lbrakk>\<lceil>f\<rceil>\<^sub></$x\<rbrakk> \<triangleright>\<^sub>D ((x :=\<^sub>D e) ;; Q))"
*)
(*
lemma "unisel 1 = \<K> II\<^sub>D"
  apply (simp add: unisel_def)
  apply (subst unisel_rec_unfold)
  apply (simp add: cond_def)
proof -
  have f1: "\<langle>\<^U>([c \<mapsto>\<^sub>s true, i \<mapsto>\<^sub>s 1])\<rangle>\<^sub>D ;; (\<not> \<lceil>\<^U>(&i < Suc 0 \<and> &c)\<rceil>\<^sub>D\<^sub>< \<and> \<K> II\<^sub>D) = 
      \<langle>U([c \<mapsto>\<^sub>s true, i \<mapsto>\<^sub>s 1])\<rangle>\<^sub>D ;; \<K> II\<^sub>D"
    by (rel_auto)
  have f2: "(\<langle>\<^U>([c \<mapsto>\<^sub>s true, i \<mapsto>\<^sub>s 1])\<rangle>\<^sub>D ;; (\<lceil>\<^U>(&i < Suc 0 \<and> &c)\<rceil>\<^sub>D\<^sub>< \<and>
      (\<K> (c :=\<^sub>D \<^U>(false)) \<oplus>\<^sub>e\<^bsub>\<^U>(1 / real (Suc 0 - &i + 1))\<^esub> \<K> (i :=\<^sub>D \<^U>(&i + 1)) ;;
      \<up> (unisel_rec (Suc (0::nat)))))) = 
    \<lceil>false\<rceil>\<^sub>D\<^sub><"
    apply (ndes_simp)
    apply (simp add: upred_defs)
    sorry
  have "unisel 1 = (i :=\<^sub>D \<^U>(1) ;;
    c :=\<^sub>D \<^U>(true) ;;
    (\<K> (c :=\<^sub>D \<^U>(false)) \<oplus>\<^sub>e\<^bsub>\<^U>(1 / real (Suc (0::nat) - &i + 1))\<^esub> \<K> (i :=\<^sub>D \<^U>(&i + 1)) ;;
     \<up> (unisel_rec (Suc (0::nat))) 
    \<triangleleft> \<^U>(&i < Suc (0::nat) \<and> &c) \<triangleright>\<^sub>D \<K> II\<^sub>D))"
    apply (simp add: unisel_def)
    apply (subst unisel_rec_unfold)
    by (rel_auto)
  have "... = ((i :=\<^sub>D \<^U>(1) ;;
    c :=\<^sub>D \<^U>(true)) ;;
    (\<K> (c :=\<^sub>D \<^U>(false)) \<oplus>\<^sub>e\<^bsub>\<^U>(1 / real (Suc (0::nat) - &i + 1))\<^esub> \<K> (i :=\<^sub>D \<^U>(&i + 1)) ;;
     \<up> (unisel_rec (Suc (0::nat))) 
    \<triangleleft> \<^U>(&i < Suc (0::nat) \<and> &c) \<triangleright>\<^sub>D \<K> II\<^sub>D))"
    by (simp add: seqr_assoc)
  have "... = \<langle> (id\<^sub>s)(i \<mapsto>\<^sub>s 1, c \<mapsto>\<^sub>s true)\<rangle>\<^sub>D ;; 
    (\<K> (c :=\<^sub>D \<^U>(false)) \<oplus>\<^sub>e\<^bsub>\<^U>(1 / real (Suc (0::nat) - &i + 1))\<^esub> \<K> (i :=\<^sub>D \<^U>(&i + 1)) ;;
     \<up> (unisel_rec (Suc (0::nat))) 
    \<triangleleft> \<^U>(&i < Suc (0::nat) \<and> &c) \<triangleright>\<^sub>D \<K> II\<^sub>D)"
    by (simp add: des_assgns_to_subst)
  have "... = \<langle>U([c \<mapsto>\<^sub>s true, i \<mapsto>\<^sub>s 1])\<rangle>\<^sub>D ;; \<K> II\<^sub>D"
    apply (simp add: cond_def)
    apply (subst seqr_or_distr)
    using f1 f2 by (metis aext_false utp_pred_laws.sup_bot_left)
qed
*)

lemma unisel_rec_bd_is_H: "unisel_rec_bd N X is \<^bold>H"
  apply (simp add: unisel_rec_bd_def)
  apply (rule dcond_H1_H2_closed')
  apply (rule seq_r_H1_H2_closed)
  apply (simp add: prob_choice_r_def)
  apply (simp add: H1_H3_impl_H2 USUP_ind_H1_H2_closed dcond_H1_H2_closed ndes_theory.bottom_closed 
      ndes_unital.Healthy_Unit ndesign_H1_H3 seq_r_H1_H3_closed unisel_rec_body_pchoice_simp')
  apply (simp add: kleisli_lift2'_def kleisli_lift_alt_def ndesign_def rdesign_is_H1_H2)
  by (simp add: H1_H3_impl_H2 assigns_d_is_H1_H2 ndesign_H1_H3 pemp_skip seq_r_H1_H2_closed)

lemma unisel_rec_unfold_is_H: 
  "\<K> (c :=\<^sub>D \<^U>(false)) \<oplus>\<^sub>e\<^bsub>\<^U>(1 / real (Suc 0 - &i))\<^esub> \<K> (i :=\<^sub>D \<^U>(&i + 1)) ;; \<up> (unisel_rec N) is \<^bold>H"
  apply (rule seq_r_H1_H2_closed)
  apply (simp add: prob_choice_r_def)
  apply (simp add: H1_H3_impl_H2 USUP_ind_H1_H2_closed dcond_H1_H2_closed ndes_theory.bottom_closed 
      ndes_unital.Healthy_Unit ndesign_H1_H3 seq_r_H1_H3_closed unisel_rec_body_pchoice_simp')
  by (simp add: kleisli_lift2'_def kleisli_lift_alt_def ndesign_def rdesign_is_H1_H2)
  
(* Unfold one step *)
(*
lemma "U(true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v\<lbrakk>0,true/$i,$c\<rbrakk>) = 1)) \<sqsubseteq> unisel_1 1"
proof -
  let ?P = "(\<K> (c :=\<^sub>D \<^U>(false)) \<oplus>\<^sub>e\<^bsub>\<^U>(1 / real (Suc (0::nat) - &i))\<^esub> \<K> (i :=\<^sub>D \<^U>(&i + 1)) ;;
     \<up> (unisel_rec (Suc (0::nat))))"
  have f1: "(c :=\<^sub>D \<^U>(true) ;; (?P \<triangleleft> \<^U>(&i < Suc (0::nat) \<and> &c) \<triangleright>\<^sub>D \<K> II\<^sub>D)) = 
      ((c :=\<^sub>D \<^U>(true) ;; ?P) \<triangleleft> U(&i < Suc (0::nat)) \<triangleright>\<^sub>D (c :=\<^sub>D \<^U>(true) ;; \<K> II\<^sub>D))"
    apply (subst assign_dcond)
    apply (rule seq_r_H1_H2_closed)
    apply (simp add: prob_choice_r_def)
    apply (simp add: H1_H3_impl_H2 USUP_ind_H1_H2_closed dcond_H1_H2_closed ndes_theory.bottom_closed 
        ndes_unital.Healthy_Unit ndesign_H1_H3 seq_r_H1_H3_closed unisel_rec_body_pchoice_simp')
    apply (simp add: kleisli_lift2'_def kleisli_lift_alt_def ndesign_def rdesign_is_H1_H2)
    apply (simp add: H1_H3_impl_H2 ndesign_H1_H3 pemp_skip)
    by (rel_auto)
  have f2: "i :=\<^sub>D \<^U>(0) ;; (c :=\<^sub>D \<^U>(true) ;; (?P \<triangleleft> \<^U>(&i < Suc (0::nat) \<and> &c) \<triangleright>\<^sub>D \<K> II\<^sub>D)) = 
      i :=\<^sub>D \<^U>(0) ;; ((c :=\<^sub>D \<^U>(true) ;; ?P) \<triangleleft> U(&i < Suc (0::nat)) \<triangleright>\<^sub>D (c :=\<^sub>D \<^U>(true) ;; \<K> II\<^sub>D))"
    by (simp add: f1)
  have f3: "... = (i :=\<^sub>D \<^U>(0) ;; c :=\<^sub>D \<^U>(true) ;; \<K> II\<^sub>D)"
    apply (subst assign_dcond)
    apply (rule seq_r_H1_H2_closed)
    using assigns_d_is_H1_H2 apply blast
    apply (rule unisel_rec_unfold_is_H)
    apply (simp add: H1_H3_impl_H2 assigns_d_is_H1_H2 ndesign_H1_H3 pemp_skip seq_r_H1_H2_closed)
    by (rel_auto)
  have f4: "unisel_1 (Suc (0::nat)) = 
    (i :=\<^sub>D \<^U>(0) ;; (c :=\<^sub>D \<^U>(true) ;; (?P \<triangleleft> \<^U>(&i < Suc (0::nat) \<and> &c) \<triangleright>\<^sub>D \<K> II\<^sub>D)))"
    apply (simp add: unisel_1_def)
    apply (subst unisel_rec_unfold)
    apply (rel_auto)
  have f5: "... = (i :=\<^sub>D \<^U>(0) ;; c :=\<^sub>D \<^U>(true) ;; \<K> II\<^sub>D)"
    using f1 f2 by (simp add: f3)
  show ?thesis
    apply (simp add: f4 f5)
    apply (simp add: pemp_skip)
    apply (ndes_simp)
    by (rel_auto)
qed
*)

(* Unfold one step *)
lemma "U((c = false) \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v) = 1)) \<sqsubseteq> unisel_rec N"
proof -
  have f1: "unisel_rec N = 
    ((unisel_rec_bd_choice N ;; \<up> (unisel_rec N))
          \<triangleleft> U(i < \<guillemotleft>N\<guillemotright> \<and> c) \<triangleright>\<^sub>D 
        \<K>(II\<^sub>D))"
    using unisel_rec_unfold by blast
  show ?thesis
    apply (subst f1)
    apply (rel_auto)
    proof -
      fix ok\<^sub>v::"bool" and i\<^sub>v::"nat" and c\<^sub>v::"bool" and ok\<^sub>v'::"bool" and 
          prob\<^sub>v::"unisel_vars pmf"
      let ?s = "\<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr>"
      assume a1: "\<forall>(ok\<^sub>v::bool) (i\<^sub>v'::nat) (c\<^sub>v::bool).
            ok\<^sub>v \<and> i\<^sub>v' = i\<^sub>v \<and> \<not> c\<^sub>v  \<or>
            ok\<^sub>v' \<and> (ok\<^sub>v \<longrightarrow> \<not> (0::real) < pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = c\<^sub>v\<rparr>)"
      from a1 have f1: "\<forall>s. s \<noteq> \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr> \<longrightarrow> 
          (0::real) = pmf prob\<^sub>v s"
        by (metis (full_types) old.unit.exhaust pmf_pos unisel_vars.cases_scheme)
      have f2: "(\<Sum>\<^sub>axb\<in>({?s} \<union> {t. \<not>t=?s}). pmf prob\<^sub>v xb) = (1::real)"
        by (simp add: Compl_eq pmf_comp_set)
      have f3: "(\<Sum>\<^sub>axb\<in>({?s} \<union> {t. \<not>t=?s}). pmf prob\<^sub>v xb) = (\<Sum>\<^sub>axb\<in>({?s}). pmf prob\<^sub>v xb) +
        (\<Sum>\<^sub>axb\<in>({t. \<not>t=?s}). pmf prob\<^sub>v xb)"
        unfolding infsetsum_altdef abs_summable_on_altdef
        apply (subst set_integral_Un, auto)
        using abs_summable_on_altdef apply fastforce
        using abs_summable_on_altdef by blast
      have f4: "(\<Sum>\<^sub>axb\<in>({t. \<not>t=?s}). pmf prob\<^sub>v xb) = (0::real)"
        using f1 by (smt infsetsum_all_0 mem_Collect_eq)
      show "pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr> = (1::real)"
        using f4 f2 f3 by auto
    qed
  qed

subsubsection \<open> Invariant of recursion \<close>

thm "ndes_theory.GFP_upperbound"

lemma design_mu_N_refine_intro:
  assumes "$ok\<acute> \<sharp> C" "$ok\<acute> \<sharp> S" "(C \<turnstile> S) \<sqsubseteq> F(C \<turnstile> S)" "`C \<Rightarrow> (\<mu>\<^sub>N F \<Leftrightarrow> \<nu>\<^sub>N F)`" "(C \<turnstile> S) is \<^bold>N"
  shows "(C \<turnstile> S) \<sqsubseteq> \<mu>\<^sub>N F"
proof -
  from assms have "(C \<turnstile> S) \<sqsubseteq> \<nu>\<^sub>N F"
    by (simp add: assms design_is_H1_H2 ndes_theory.GFP_upperbound)
  with assms show ?thesis
    by (rel_auto, metis (no_types, lifting))
qed

(* See UTP book Lemma 2.7.2 *)
thm "des_theory.utp_lfp_def"
find_theorems "des_theory.utp_gfp"
find_theorems "Monotonic"
term "GREATEST_FP"
thm "isotone_def"
thm "mono_def"
find_theorems "mono "
find_theorems "des_theory"
term "Monotone"
thm "ndes_theory.LFP_lemma3"
thm "Mono_utp_orderI"
thm "isotone_def"
thm "use_iso1"

(* This theorem modifies the assumption "M" of ndesign_mu_wf_refine_intro since M is too general
and not possible to prove in this context. So specialise it using "Mono_utp_orderI" *)
(*
theorem ndesign_mu_wf_refine_intro'': 
  assumes   WF: "wf R"
    and      M: "\<And> P Q. \<lbrakk> P \<sqsubseteq> Q; P is \<^bold>N; Q is \<^bold>N \<rbrakk> \<Longrightarrow> F(P) \<sqsubseteq> F(Q)"
    and      H: "F \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
    and  induct_step:
    "\<And>st. ((p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n Q) \<sqsubseteq> F ((p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Q)"
  shows "(p \<turnstile>\<^sub>n Q) \<sqsubseteq> \<mu>\<^sub>N F"
proof -          
  {
  fix st
  have "(p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n Q \<sqsubseteq> \<mu>\<^sub>N F" 
  using WF proof (induction rule: wf_induct_rule)
    case (less st)
    hence 0: "(p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Q \<sqsubseteq> \<mu>\<^sub>N F"
      by rel_blast
    have M': "Mono\<^bsub>ndes_theory.thy_order\<^esub> F"
      using M by (simp add: Mono_utp_orderI)
    have 1: "\<mu>\<^sub>N F \<sqsubseteq>  F (\<mu>\<^sub>N F)"
      by (subst ndes_theory.LFP_lemma3, simp_all add: M' H)
    from 0 1 have 2:"(p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u\<in>\<^sub>u\<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Q \<sqsubseteq> F (\<mu>\<^sub>N F)"
      by simp
    have 3: "F ((p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Q) \<sqsubseteq> F (\<mu>\<^sub>N F)"
      using 0 M by (simp add: ndesign_H1_H3)
    have 4:"(p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n Q \<sqsubseteq> \<dots>" 
      by (rule induct_step)
    show ?case
      using order_trans[OF 3 4] H M' ndes_theory.LFP_lemma2 dual_order.trans 
      by (smt)
  qed
  }
  thus ?thesis
    by (pred_simp)
qed  
*)

(*
theorem ndesign_mu_wf_refine_intro'': 
  assumes   WF: "wf R"
    and      M: "\<And> P Q. \<lbrakk> P \<sqsubseteq> Q; P is \<^bold>N; Q is \<^bold>N \<rbrakk> \<Longrightarrow> F(P) \<sqsubseteq> F(Q)"
    and      H: "F \<in> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>\<^bold>N\<rbrakk>\<^sub>H"
    and induct_step:
      "\<And>st.
       (p \<and> (p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>)) \<turnstile>\<^sub>n P \<sqsubseteq>
       (Q ;; \<up> (((p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>)) \<turnstile>\<^sub>n P) \<triangleleft> g \<triangleright>\<^sub>D \<^U>(\<not> $ok)) \<sqinter>
       (\<K> II\<^sub>D \<triangleleft> (\<not> g) \<triangleright>\<^sub>D \<^U>(\<not> $ok))"
  shows "(p \<turnstile>\<^sub>n P) \<sqsubseteq> do g \<rightarrow> Q od"
  apply (simp add: IteratePD_list_def IteratePD_def AlternateD_def GrdCommD_def)
  apply (rule ndesign_mu_wf_refine_intro''[where e=V and R="R"])
  apply (simp_all add: wf WF)
  apply (rel_auto)
  apply (simp add: cond_mono kleisli_left_mono seqr_mono)
  apply (simp add: Pi_def)
  apply (clarify)
  apply (rule dcond_H1_H3_closed')
  apply (rule seq_r_H1_H3_closed)
  apply (simp add: unisel_rec_body_pchoice_simp')
  apply (rel_auto)
*)

lemma "U((\<not> c) \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v) = 1)) \<sqsubseteq> unisel_rec N"
  apply (simp add: unisel_rec_def unisel_rec_bd_def)
  apply (rule ndesign_mu_wf_refine_intro''[where e="&i" and R="{(x, y). x < y}"])
  apply (simp_all add: wf closure)
  apply (simp add: cond_mono kleisli_left_mono seqr_mono)
  apply (simp add: unisel_rec_bd_NN')
  apply (rel_auto)
  proof -
    fix ok\<^sub>v::"bool" and i\<^sub>v::"nat" and c\<^sub>v::"bool" and ok\<^sub>v'::"bool" and 
        prob\<^sub>v::"unisel_vars pmf"
    let ?s = "\<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr>"
    assume a1: "\<forall>(ok\<^sub>v::bool) (i\<^sub>v'::nat) (c\<^sub>v::bool).
          ok\<^sub>v \<and> i\<^sub>v' = i\<^sub>v \<and> \<not> c\<^sub>v  \<or>
          ok\<^sub>v' \<and> (ok\<^sub>v \<longrightarrow> \<not> (0::real) < pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v', c\<^sub>v = c\<^sub>v\<rparr>)"
    from a1 have f1: "\<forall>s. s \<noteq> \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr> \<longrightarrow> 
        (0::real) = pmf prob\<^sub>v s"
      by (metis (full_types) old.unit.exhaust pmf_pos unisel_vars.cases_scheme)
    have f2: "(\<Sum>\<^sub>axb\<in>({?s} \<union> {t. \<not>t=?s}). pmf prob\<^sub>v xb) = (1::real)"
      by (simp add: Compl_eq pmf_comp_set)
    have f3: "(\<Sum>\<^sub>axb\<in>({?s} \<union> {t. \<not>t=?s}). pmf prob\<^sub>v xb) = (\<Sum>\<^sub>axb\<in>({?s}). pmf prob\<^sub>v xb) +
      (\<Sum>\<^sub>axb\<in>({t. \<not>t=?s}). pmf prob\<^sub>v xb)"
      unfolding infsetsum_altdef abs_summable_on_altdef
      apply (subst set_integral_Un, auto)
      using abs_summable_on_altdef apply fastforce
      using abs_summable_on_altdef by blast
    have f4: "(\<Sum>\<^sub>axb\<in>({t. \<not>t=?s}). pmf prob\<^sub>v xb) = (0::real)"
      using f1 by (smt infsetsum_all_0 mem_Collect_eq)
    show "pmf prob\<^sub>v \<lparr>i\<^sub>v = i\<^sub>v, c\<^sub>v = False\<rparr> = (1::real)"
      using f4 f2 f3 by auto
  qed

lemma "U((c \<and> \<guillemotleft>N\<guillemotright> > i) \<turnstile>\<^sub>n 
      ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = (1/(real (\<guillemotleft>N\<guillemotright>-$i))) \<and> 
       $prob\<acute>($\<^bold>v\<lbrakk>true,$i+1/$c,$i\<rbrakk>) = (1 - 1/(real (\<guillemotleft>N\<guillemotright>-$i)))))
  \<sqsubseteq> unisel_rec_bd_choice N"
  apply (simp add: unisel_rec_bd_choice_simp)
  apply (ndes_simp)
  apply (rel_simp)
  by fastforce

lemma "U((\<guillemotleft>N\<guillemotright> > i) \<turnstile>\<^sub>n 
      ((($c \<and> \<guillemotleft>N\<guillemotright> > $i) \<Rightarrow> 
          ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = (1/(real (\<guillemotleft>N\<guillemotright>-$i+1))) \<and> 
           $prob\<acute>($\<^bold>v\<lbrakk>true,$i+1/$c,$i\<rbrakk>) = (1 - 1/(real (\<guillemotleft>N\<guillemotright>-$i+1))))
      ) \<and>
      ((\<not> ($c \<and> \<guillemotleft>N\<guillemotright> > $i)) \<Rightarrow> ($prob\<acute>($\<^bold>v) = (1::real))))
  ) 
  \<sqsubseteq> unisel_rec_bd N X"
  apply (simp add: unisel_rec_bd_simp)
  apply (ndes_simp)
  apply (rel_simp)
  oops

      (*(\<forall> k \<in> {1..\<guillemotleft>N\<guillemotright>} .
          (k < \<guillemotleft>N\<guillemotright> \<Rightarrow> $prob\<acute>($\<^bold>v\<lbrakk>false,\<guillemotleft>k\<guillemotright>/$c,$i\<rbrakk>) = (1/(real (\<guillemotleft>N\<guillemotright>)))) \<and> 
          (k = \<guillemotleft>N\<guillemotright> \<Rightarrow> $prob\<acute>($\<^bold>v\<lbrakk>true,\<guillemotleft>k\<guillemotright>/$c,$i\<rbrakk>) = (1/(real (\<guillemotleft>N\<guillemotright>))))
      )*)

(* How to find out its contract:
According to @{text "ndesign_mu_wf_refine_intro''"}:
  1) "\<And>st. ((p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n Q) \<sqsubseteq> F ((p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Q)"
where
  e="\<guillemotleft>N\<guillemotright> - &i" and 
  R="{(x, y). x < y}" and
  F (X) = ((((\<K>(c :=\<^sub>D false)) \<oplus>\<^sub>e\<^bsub>U(1/real (\<guillemotleft>N\<guillemotright>-i+1))\<^esub> (\<K>(i :=\<^sub>D i+1))) ;; \<up>X)
          \<triangleleft> U(i < \<guillemotleft>N\<guillemotright> \<and> c) \<triangleright>\<^sub>D \<K>(II\<^sub>D))
Question: find out p and Q in order to make the formula 1) hold.

Let's start with @{text "\<up> (((p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Q))"} in RHS

------------(1)------------
\<up> (((p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Q))
= 
(U((\<Sum>\<^sub>ai::'a\<in>\<lbrakk>p \<and> bop (\<in>) (e, \<^U>(st))\<^sub>u \<^U>(R)\<rbrakk>\<^sub>p. pmf (&prob) i) = 1) \<turnstile>\<^sub>n
(\<^bold>\<exists> Qa::'a \<Rightarrow> 'a pmf \<bullet> 
  (\<^bold>\<forall> ss::'a \<bullet> \<^U>(pmf ($prob\<acute>) ss = (\<Sum>\<^sub>at::'a. pmf ($prob) t \<cdot> pmf (Qa t) ss))) \<and>
  (\<^bold>\<forall> s::'a \<bullet> \<not> \<^U>((\<lambda>(x::real) y::real. y < x) (pmf ($prob) ($\<^bold>v\<acute>)) 0 \<and> $\<^bold>v\<acute> = s) ;;
            (\<not> (p \<and> bop (\<in>) (e, \<^U>(st))\<^sub>u \<^U>(R))\<^sup>< \<or> \<not> Q) ;;
            (\<^bold>\<forall> t::'a \<bullet> \<^U>(pmf ($prob) t = pmf (Qa s) t)))))

------------(2)------------
F ((p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Q)
=
((((\<K>(c :=\<^sub>D false)) \<oplus>\<^sub>e\<^bsub>U(1/real (\<guillemotleft>N\<guillemotright>-i+1))\<^esub> (\<K>(i :=\<^sub>D i+1))) ;; \<up> (((p \<and> (e, \<guillemotleft>st\<guillemotright>)\<^sub>u \<in>\<^sub>u \<guillemotleft>R\<guillemotright>) \<turnstile>\<^sub>n Q)))
\<triangleleft> U(i < \<guillemotleft>N\<guillemotright> \<and> c) \<triangleright>\<^sub>D \<K>(II\<^sub>D))
= (1) and unisel_rec_bd_simp
( (U(true \<turnstile>\<^sub>n (
      ($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-i+1))\<guillemotright> \<and> 
      $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-i+1))\<guillemotright>))
  ) ;; 
  (U((\<Sum>\<^sub>ai::'a\<in>\<lbrakk>p \<and> bop (\<in>) (e, \<^U>(st))\<^sub>u \<^U>(R)\<rbrakk>\<^sub>p. pmf (&prob) i) = 1) \<turnstile>\<^sub>n
  (\<^bold>\<exists> Qa::'a \<Rightarrow> 'a pmf \<bullet> 
    (\<^bold>\<forall> ss::'a \<bullet> \<^U>(pmf ($prob\<acute>) ss = (\<Sum>\<^sub>at::'a. pmf ($prob) t \<cdot> pmf (Qa t) ss))) \<and>
    (\<^bold>\<forall> s::'a \<bullet> \<not> \<^U>((\<lambda>(x::real) y::real. y < x) (pmf ($prob) ($\<^bold>v\<acute>)) 0 \<and> $\<^bold>v\<acute> = s) ;;
              (\<not> (p \<and> bop (\<in>) (e, \<^U>(st))\<^sub>u \<^U>(R))\<^sup>< \<or> \<not> Q) ;;
              (\<^bold>\<forall> t::'a \<bullet> \<^U>(pmf ($prob) t = pmf (Qa s) t))))
  ))
\<triangleleft> U(i < \<guillemotleft>N\<guillemotright> \<and> c) \<triangleright>\<^sub>D 
  \<K>(II\<^sub>D))
= ndesign_composition_wp
(  (((($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-i+1))\<guillemotright> \<and> 
     $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-i+1))\<guillemotright>)) 
    wlp ((\<Sum>\<^sub>ai::'a\<in>\<lbrakk>p \<and> bop (\<in>) (e, \<^U>(st))\<^sub>u \<^U>(R)\<rbrakk>\<^sub>p. pmf (&prob) i) = 1)) 
    \<turnstile>\<^sub>n 
    ((($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-i+1))\<guillemotright> \<and> 
     $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-i+1))\<guillemotright>)) ;; 
    (\<^bold>\<exists> Qa::'a \<Rightarrow> 'a pmf \<bullet> 
      (\<^bold>\<forall> ss::'a \<bullet> \<^U>(pmf ($prob\<acute>) ss = (\<Sum>\<^sub>at::'a. pmf ($prob) t \<cdot> pmf (Qa t) ss))) \<and>
      (\<^bold>\<forall> s::'a \<bullet> \<not> \<^U>((\<lambda>(x::real) y::real. y < x) (pmf ($prob) ($\<^bold>v\<acute>)) 0 \<and> $\<^bold>v\<acute> = s) ;;
                (\<not> (p \<and> bop (\<in>) (e, \<^U>(st))\<^sub>u \<^U>(R))\<^sup>< \<or> \<not> Q) ;;
                (\<^bold>\<forall> t::'a \<bullet> \<^U>(pmf ($prob) t = pmf (Qa s) t)))))
  )
\<triangleleft> U(i < \<guillemotleft>N\<guillemotright> \<and> c) \<triangleright>\<^sub>D 
  \<K>(II\<^sub>D))
= 
(  ((\<forall>prob0 . ((($prob0($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-i+1))\<guillemotright> \<and> 
     $prob0($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-i+1))\<guillemotright>)) \<Rightarrow> 
    ((\<Sum>\<^sub>ai::'a\<in>\<lbrakk>p \<and> bop (\<in>) (e, \<^U>(st))\<^sub>u \<^U>(R)\<rbrakk>\<^sub>p. pmf (&prob0) i) = 1))) 
    \<turnstile>\<^sub>n 
    ((($prob\<acute>($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-i+1))\<guillemotright> \<and> 
     $prob\<acute>($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-i+1))\<guillemotright>)) ;; 
    (\<^bold>\<exists> Qa::'a \<Rightarrow> 'a pmf \<bullet> 
      (\<^bold>\<forall> ss::'a \<bullet> U(pmf ($prob\<acute>) ss = (\<Sum>\<^sub>at::'a. pmf ($prob) t \<cdot> pmf (Qa t) ss))) \<and>
      (\<^bold>\<forall> s::'a \<bullet> (pmf $prob s > 0) \<Rightarrow> (Q(s, Qa s))))) (* Simplification *)
  )
\<triangleleft> U(i < \<guillemotleft>N\<guillemotright> \<and> c) \<triangleright>\<^sub>D 
  (true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v) = 1)))
= 
(  ((\<forall>prob0 . ((($prob0($\<^bold>v\<lbrakk>false/$c\<rbrakk>) = \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-i+1))\<guillemotright> \<and> 
     $prob0($\<^bold>v\<lbrakk>$i+1/$i\<rbrakk>) = 1 - \<guillemotleft>(1/real (\<guillemotleft>N\<guillemotright>-i+1))\<guillemotright>)) \<Rightarrow> 
    ((\<Sum>\<^sub>ai::'a\<in>\<lbrakk>p \<and> bop (\<in>) (e, \<^U>(st))\<^sub>u \<^U>(R)\<rbrakk>\<^sub>p. pmf (&prob0) i) = 1))) 
    \<turnstile>\<^sub>n 
    (\<^bold>\<exists> Qa::'a \<Rightarrow> 'a pmf \<bullet> 
      (\<^bold>\<forall> ss::'a \<bullet> U(pmf ($prob\<acute>) ss = r1*(pmf (Qa s1) ss) + (1-r1)*(pmf (Qa s2) ss))) \<and>
      Q(s1, Qa s1) \<and> Q(s2, Qa s2)) (* Simplification *)
  )
\<triangleleft> U(i < \<guillemotleft>N\<guillemotright> \<and> c) \<triangleright>\<^sub>D 
  (true \<turnstile>\<^sub>n ($prob\<acute>($\<^bold>v) = 1)))

------------(3)------------
((p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<turnstile>\<^sub>n Q) \<sqsubseteq> (2)
= ndesign_refinement  (`p1 \<Rightarrow> p2` \<and> `\<lceil>p1\<rceil>\<^sub>< \<and> Q2 \<Rightarrow> Q1`)
(3.1) (p \<and> e =\<^sub>u \<guillemotleft>st\<guillemotright>) \<Rightarrow> () \<triangleleft> (i < \<guillemotleft>N\<guillemotright> \<and> c) \<triangleright> true

(3.2) Q \<sqsubseteq> 
((\<^bold>\<exists> Qa::'a \<Rightarrow> 'a pmf \<bullet> 
      (\<^bold>\<forall> ss::'a \<bullet> U(pmf ($prob\<acute>) ss = r1*(pmf (Qa s1) ss) + (1-r1)*(pmf (Qa s2) ss))) \<and>
      Q(s1, Qa s1) \<and> Q(s2, Qa s2)) 
  \<triangleleft> (i < \<guillemotleft>N\<guillemotright> \<and> c) \<triangleright> 
  ($prob\<acute>($\<^bold>v) = 1)
)

if Q=(\<forall>cc. (\<forall>ii \<ge> $i. $prob\<acute>($\<^bold>v\<lbrakk>ii,cc/$i,$c\<rbrakk>) = (calc_prob' \<guillemotleft>N\<guillemotright> ($i) ii cc)))

prob' = r1 * (\<forall>cc. (\<forall>ii \<ge> $i. (Qa s1)($\<^bold>v\<lbrakk>ii,cc/$i,$c\<rbrakk>) = (calc_prob' \<guillemotleft>N\<guillemotright> ($i) ii cc)))
*)

(*
Variant: N-i is not enough as (p \<turnstile> P) is a probability design, so out\<alpha> is $prob\<acute>, not state any
more. To state $i\<acute> is no sense. We have to recover $i from $prob\<acute>.
*)

(*
fun calc_prob :: "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> real" where
"calc_prob NN ii False = (1/(NN-ii+1))" | 
"calc_prob NN ii True = ((NN-(ii-1))/(NN-(ii-1)+1))"

value "calc_prob 5 3 False"
value "calc_prob 5 3 True"

function calc_prob' :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> real" where
"calc_prob' NN i0 ii False = 
  (if ii = i0 then calc_prob NN i0 False 
  else (calc_prob NN ii False) * (calc_prob' NN i0 (ii) True))" | 
"calc_prob' NN i0 ii True = 
  (if ii = (i0+1) then calc_prob NN (i0+1) True 
  else (calc_prob NN ii True) * (calc_prob' NN i0 (ii-1) True))"
  by fastforce+
termination
  sorry

value "calc_prob' 5 1 1 False"
value "calc_prob' 5 1 2 False"
value "calc_prob' 5 1 3 False"
value "calc_prob' 5 1 3 True"
value "calc_prob' 5 1 5 True"
term "U(calc_prob' \<guillemotleft>N\<guillemotright> &i &i &c)"
*)

definition unisel_inv' ::
  "nat \<Rightarrow> (unisel_vars, unisel_vars) rel_pdes" where
"unisel_inv' n = U(true \<turnstile>\<^sub>n 
    ((($c \<and> $i < (\<guillemotleft>n-1\<guillemotright>)) \<Rightarrow> 
      ((\<forall>j<\<guillemotleft>n\<guillemotright>-$i-1. $prob\<acute>($\<^bold>v\<lbrakk>\<guillemotleft>j\<guillemotright>+$i, false/$i, $c\<rbrakk>) = U(1/real (\<guillemotleft>n\<guillemotright>-$i))) \<and> 
      $prob\<acute>($\<^bold>v\<lbrakk>\<guillemotleft>n-1\<guillemotright>, true/$i, $c\<rbrakk>) = U(1/real (\<guillemotleft>n\<guillemotright>-$i)))
    ) \<and>
    (U(\<not>($c \<and> $i < (\<guillemotleft>n-1\<guillemotright>))) \<Rightarrow> ($prob\<acute>($\<^bold>v) = 1)))
  )"

find_theorems "Rep_uexpr"

lemma unisel_rec'_inv:
  assumes "N \<ge> 1"
  shows "unisel_inv' N \<sqsubseteq> unisel_rec' N"
proof (cases "N=1")
  case True
  have f1: "\<forall>X. (unisel_rec_body N X) = II\<^sub>p"
    using True by (rel_auto)
  then have f2: "(\<mu>\<^sub>N X \<bullet> unisel_rec_body N X) = (\<mu>\<^sub>N X \<bullet> II\<^sub>p)"
    by simp
  have f3: "... = II\<^sub>p"
    by (metis ndes_theory.LFP_const ndesign_H1_H3 pemp_skip)
  then have f4: "unisel_rec' N = II\<^sub>p"
    apply (simp add: unisel_rec'_def)
    using f2 by auto
  have lhs: "unisel_inv' N = II\<^sub>p"
    apply (simp add: unisel_inv'_def pemp_skip)
    using True by (rel_auto)
  then show ?thesis
    by (simp add: f4)
next
  case False
  then have F: "N > 1"
    using assms by linarith
  then show ?thesis
    apply (simp add: unisel_rec'_def unisel_inv'_def)
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
    )) \<sqsubseteq> (i :=\<^sub>D 0 ;; c :=\<^sub>D true ;; unisel_rec' N)"
proof -
  have f1: "i :=\<^sub>D 0 ;; c :=\<^sub>D true ;; unisel_inv' N \<sqsubseteq> (i :=\<^sub>D 0 ;; c :=\<^sub>D true ;; unisel_rec' N)"
    apply (rule seqr_mono, simp)
    apply (rule seqr_mono, simp)
    using assms unisel_rec'_inv by auto
  have f2: "i :=\<^sub>D 0 ;; c :=\<^sub>D true ;; unisel_inv' N = U(true \<turnstile>\<^sub>n 
    (
      ((\<forall>j<\<guillemotleft>N\<guillemotright>-1. $prob\<acute>($\<^bold>v\<lbrakk>\<guillemotleft>j\<guillemotright>, false/$i, $c\<rbrakk>) = U(1/real (\<guillemotleft>N\<guillemotright>))) \<and> 
      $prob\<acute>($\<^bold>v\<lbrakk>\<guillemotleft>N-1\<guillemotright>, true/$i, $c\<rbrakk>) = U(1/real (\<guillemotleft>N\<guillemotright>)))
    ))"
    apply (simp add: unisel_inv'_def)
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
