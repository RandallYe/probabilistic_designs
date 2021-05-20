section \<open> Healthiness conditions \<close>

theory utp_prob_des_healthy
  imports "UTP-Calculi.utp_wprespec" "UTP-Designs.utp_designs" "HOL-Probability.Probability_Mass_Function"
  utp_prob_des
begin recall_syntax

subsection \<open> Definition of Convex Closure \<close>

definition Convex_Closed :: "'s hrel_pdes \<Rightarrow> 's hrel_pdes" ("\<^bold>C\<^bold>C") 
  where [upred_defs]: "Convex_Closed p \<equiv>  \<Sqinter> r \<in> {0..1} \<bullet> (p \<oplus>\<^bsub>r\<^esub> p)"

(* declare [[show_types]] *)

subsection \<open> Laws of Convex Closure \<close>

lemma Convex_Closed_eq:
  "Convex_Closed p = ((\<Sqinter> r \<in> {0<..<1} \<bullet> (p \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> p)) \<sqinter> p)"
  apply (simp add: Convex_Closed_def prob_choice_def)
  apply (simp add: UINF_as_Sup_collect image_def)
proof -
  have f1: " {y::('a, 'a) rel_pdes.
        y = \<top>\<^sub>D \<and>
        (\<exists>x::real.
            (0::real) \<le> x \<and>
            x \<le> (1::real) \<and> ((0::real) < x \<longrightarrow> \<not> x < (1::real)) \<and> \<not> x = (0::real) \<and> \<not> x = (1::real))}
    = {}"
    by (rel_auto)
  then have f2: "\<Or>({y::('a, 'a) rel_pdes.
        \<exists>x::real\<in>{0::real..1::real} \<inter> {x::real. (0::real) < x \<and> x < (1::real)}. y = p \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>x\<^esub>\<^esub> p} \<union>
       {y::('a, 'a) rel_pdes.
        y = \<top>\<^sub>D \<and>
        (\<exists>x::real.
            (0::real) \<le> x \<and>
            x \<le> (1::real) \<and> ((0::real) < x \<longrightarrow> \<not> x < (1::real)) \<and> \<not> x = (0::real) \<and> \<not> x = (1::real))})
    = \<Or>({y::('a, 'a) rel_pdes.
        \<exists>x::real\<in>{0::real..1::real} \<inter> {x::real. (0::real) < x \<and> x < (1::real)}. y = p \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>x\<^esub>\<^esub> p})"
    by (simp add: f1)
  also have f3: "... = \<Or>({y::('a, 'a) rel_pdes. \<exists>x::real\<in>{0::real<..<1::real}. y = p \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>x\<^esub>\<^esub> p})"
    by (metis (no_types, lifting) Int_Collect atLeastAtMost_iff greaterThanLessThan_iff less_le)
  then show "p \<sqinter>
    \<Or>({y::('a, 'a) rel_pdes.
        \<exists>x::real\<in>{0::real..1::real} \<inter> {x::real. (0::real) < x \<and> x < (1::real)}. y = p \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>x\<^esub>\<^esub> p} \<union>
       {y::('a, 'a) rel_pdes.
        y = \<top>\<^sub>D \<and>
        (\<exists>x::real.
            (0::real) \<le> x \<and>
            x \<le> (1::real) \<and> ((0::real) < x \<longrightarrow> \<not> x < (1::real)) \<and> \<not> x = (0::real) \<and> \<not> x = (1::real))}) =
    \<Or>{y::('a, 'a) rel_pdes. \<exists>x::real\<in>{0::real<..<1::real}. y = p \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>x\<^esub>\<^esub> p} \<sqinter> p"
    apply (simp add: f2 f3)
    using semilattice_sup_class.sup_commute by blast
qed

declare [[show_types]]

lemma K_skip_idem:
  assumes "r \<in> {0<..<1}"
  shows "(\<K>(II\<^sub>D) \<oplus>\<^bsub>r\<^esub> \<K>(II\<^sub>D)) = \<K>(II\<^sub>D)"
proof -
  have f1: "(\<K>(II\<^sub>D) \<oplus>\<^bsub>r\<^esub> \<K>(II\<^sub>D)) =  \<K>(II\<^sub>D) \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>r\<^esub>\<^esub> \<K>(II\<^sub>D)"
    using assms by (simp add: prob_choice_def)
  also have f2: "... = \<K>(II\<^sub>D)"
    apply (simp add: upred_defs)
    apply (rel_auto)
    apply (metis assms atLeastAtMost_iff greaterThanLessThan_iff less_le not_less_iff_gr_or_eq 
      pmf_neq_exists_less pmf_not_neg wplus_idem)
    apply blast
    apply blast
    proof -
      fix ok\<^sub>v::"bool" and more::"'b" and ok\<^sub>v'::"bool" and prob\<^sub>v::"'b pmf"
      assume a1: "\<forall>ok\<^sub>v morea. ok\<^sub>v \<and> morea = more \<or> ok\<^sub>v' \<and> (ok\<^sub>v \<longrightarrow> \<not> 0 < pmf prob\<^sub>v morea)"
      show "\<exists>ok\<^sub>v'' morea ok\<^sub>v''' prob\<^sub>v'.
          (ok\<^sub>v \<longrightarrow> (\<forall>ok\<^sub>v morea. ok\<^sub>v \<and> morea = more \<or> ok\<^sub>v''' \<and> (ok\<^sub>v \<longrightarrow> \<not> 0 < pmf prob\<^sub>v' morea))) \<and>
          (\<exists>ok\<^sub>v'''' prob\<^sub>v''.
              (ok\<^sub>v \<longrightarrow> (\<forall>ok\<^sub>v morea. ok\<^sub>v \<and> morea = more \<or> ok\<^sub>v'''' \<and> (ok\<^sub>v \<longrightarrow> \<not> 0 < pmf prob\<^sub>v'' morea))) \<and>
              ok\<^sub>v'' = ok\<^sub>v \<and>
              morea = more \<and>
              (\<exists>ok\<^sub>v mrg_prior\<^sub>v prob\<^sub>v''' prob\<^sub>v''''.
                  (ok\<^sub>v''' \<and> ok\<^sub>v'''' \<longrightarrow>
                   ok\<^sub>v \<and> prob\<^sub>v''' = prob\<^sub>v' \<and> prob\<^sub>v'''' = prob\<^sub>v'' \<and> mrg_prior\<^sub>v = morea) \<and>
                  (ok\<^sub>v \<longrightarrow> ok\<^sub>v' \<and> prob\<^sub>v = prob\<^sub>v''' +\<^bsub>r\<^esub> prob\<^sub>v'''')))"
        apply (rule_tac x = "ok\<^sub>v" in exI)
        apply (rule_tac x = "more" in exI)
        apply (rule_tac x = "ok\<^sub>v'" in exI)
        apply (rule_tac x = "prob\<^sub>v" in exI)
        apply (rule_tac conjI)
        using a1 apply blast
        apply (rule_tac x = "ok\<^sub>v'" in exI)
        apply (rule_tac x = "prob\<^sub>v" in exI)
        apply (rule_tac conjI)
        using a1 apply blast
        apply (auto)
        apply (rule_tac x = "ok\<^sub>v'" in exI)
        apply (rule_tac x = "more" in exI)
        apply (rule_tac x = "prob\<^sub>v" in exI)
        apply (rule_tac x = "prob\<^sub>v" in exI)
        apply (auto)
        by (metis assms atLeastAtMost_iff greaterThanLessThan_iff less_eq_real_def wplus_idem)
    qed
    show ?thesis
      using f1 assms
      by (simp add: f2)
  qed

lemma CC_skip: "\<K>(II\<^sub>D) is \<^bold>C\<^bold>C"
  apply (simp add: Healthy_def Convex_Closed_def)
  apply (simp add: UINF_as_Sup_collect image_def)
  apply (simp add: prob_choice_def)
  proof -
    have f1: "(\<Or>{y::('a, 'a) rel_pdes.
         \<exists>x::real\<in>{0::real..1::real}.
            (x = (0::real) \<longrightarrow> y = \<K> II\<^sub>D) \<and>
            (\<not> x = (0::real) \<longrightarrow>
             (x < (1::real) \<longrightarrow> y = \<K> II\<^sub>D \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>x\<^esub>\<^esub> \<K> II\<^sub>D) \<and> (\<not> x < (1::real) \<longrightarrow> y = \<K> II\<^sub>D))})
      = (\<Or>{y::('a, 'a) rel_pdes. y = \<K> II\<^sub>D \<and> (\<exists>x::real. (0::real) \<le> x \<and> x \<le> (1::real))})"
      by (metis (no_types, hide_lams) K_skip_idem atLeastAtMost_iff greaterThanLessThan_iff 
          le_numeral_extra(1) less_le order_refl prob_choice_def)
    also have f2: "... = \<K> II\<^sub>D"
      proof -
        have "\<exists>r. (0::real) \<le> r \<and> r \<le> 1"
          using le_numeral_extra(1) by blast
        then show ?thesis
          by simp
      qed
    show "\<Or>{y::('a, 'a) rel_pdes.
         \<exists>x::real\<in>{0::real..1::real}.
            (x = (0::real) \<longrightarrow> y = \<K> II\<^sub>D) \<and>
            (\<not> x = (0::real) \<longrightarrow>
             (x < (1::real) \<longrightarrow> y = \<K> II\<^sub>D \<parallel>\<^sup>D\<^bsub>\<^bold>P\<^bold>M\<^bsub>x\<^esub>\<^esub> \<K> II\<^sub>D) \<and> (\<not> x < (1::real) \<longrightarrow> y = \<K> II\<^sub>D))} =
        \<K> II\<^sub>D"
      by (simp add: f1 f2)
  qed

end
