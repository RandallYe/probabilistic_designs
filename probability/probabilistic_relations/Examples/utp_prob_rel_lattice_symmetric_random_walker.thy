section \<open> Example of probabilistic relation programming: parallel composition \<close>

theory utp_prob_rel_lattice_symmetric_random_walker
  imports 
    "UTP_prob_relations.utp_prob_rel_lattice_laws" 
    "HOL-Analysis.Infinite_Set_Sum"
begin 

unbundle UTP_Syntax

declare [[show_types]]

subsection \<open> Definitions \<close>
alphabet srwstate = time + 
  x :: nat

definition move:: "srwstate prhfun" where
"move = if\<^sub>p 0.5 then (x := x - 1) else (x := x + 1)"

definition sym_random_walker where
"sym_random_walker = while\<^sub>p\<^sub>t (x\<^sup>< > 0)\<^sub>e do move od"

definition Ht:: "srwstate rvhfun" where 
"Ht = ((\<lbrakk>\<not>x\<^sup>< > 0\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>x\<^sup>> = x\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e) + 
        \<lbrakk>x\<^sup>< > 0\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>x\<^sup>> = 0\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> \<ge> t\<^sup>< + x\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> - (t\<^sup>< + x\<^sup><) mod 2 = 0\<rbrakk>\<^sub>\<I>\<^sub>e * (1/2)^(t\<^sup>> - t\<^sup><))\<^sub>e"

definition move_t_alt :: "srwstate rvhfun" where
"move_t_alt \<equiv> (\<lbrakk>x\<^sup>> = x\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>$t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 2 + \<lbrakk>x\<^sup>> = x\<^sup>< - 1\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>$t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 2)\<^sub>e"

subsection \<open> Distributions \<close>
thm "fact_prod"
term "fact 2"
term "even"

context semiring_char_0
begin
text \<open> @{text "fact2 (n-1)"} \<close>
(* fact2 0 = (-1)!! = 1 
   fact2 1 = (0)!! = 1 
   fact2 n = (n-1)!! 
*)
definition fact2 :: "nat \<Rightarrow> 'a"
  where fact2_prod: "fact2 n = (
    if n = 0 \<or> n = 1 then 1 else 
      (if even (n-1) 
      then (of_nat (\<Prod>i\<in>{1..((n-1) div 2)}. 2*i)) 
      else (of_nat (\<Prod>i\<in>{1..(n div 2)}. 2*i-1))
      )
    )"
end

lemma "(fact2 0::\<nat>) = 1"
  by (simp add: fact2_prod)

lemma "(fact2 1::\<nat>) = 1"
  by (simp add: fact2_prod)

lemma "(fact2 2::\<nat>) = 1"
  by (simp add: fact2_prod)

lemma "(fact2 3::\<nat>) = 2"
  by (simp add: fact2_prod)

lemma "(fact2 4::\<nat>) = 3"
  apply (simp add: fact2_prod)
  by (metis (no_types, lifting) One_nat_def add_Suc diff_Suc_1 le_add_same_cancel1 mult_2 
      mult_numeral_1_right numeral_1_eq_Suc_0 numeral_3_eq_3 plus_1_eq_Suc prod.nat_ivl_Suc' 
      prod_neutral_const zero_less_one_class.zero_le_one)

definition p_n :: "nat \<Rightarrow> \<real>" where
"p_n n = (-1)^(n-1) * ((1/2::\<real>) gchoose n)"

subsection \<open> Theorems \<close>
lemma rvfun_of_prfun_1_2: "rvfun_of_prfun (\<lambda>x::srwstate \<times> srwstate. ereal2ureal (ereal ((1::\<real>) / (2::\<real>))))
  = ((1::\<real>) / (2::\<real>))\<^sub>e"
  apply (simp add: ureal_defs)
  by (simp add: real2uereal_inverse)

lemma rvfun_of_prfun_1_2': 
  "rvfun_of_prfun [\<lambda>x::srwstate \<times> srwstate. ereal2ureal (ereal ((1::\<real>) / (2::\<real>)))]\<^sub>e
  = (\<lambda>s. ureal2real (1/2))"
  apply (simp add: ureal_defs)
  by (simp add: SEXP_def ereal_1_div)

lemma rvfun_of_prfun_1_2'': 
  "rvfun_of_prfun [\<lambda>x::srwstate \<times> srwstate. ereal2ureal (ereal ((1::\<real>) / (2::\<real>)))]\<^sub>e
  = ((1::\<real>) / (2::\<real>))\<^sub>e"
  apply (simp add: ureal_defs)
  by (simp add: real2uereal_inverse)

lemma srw_move_t: "(Pt move) = prfun_of_rvfun move_t_alt"
  apply (simp add: move_def Pt_def move_t_alt_def)
  apply (simp add: pseqcomp_def)
  apply (simp add: pchoice_def)
  apply (subst rvfun_inverse)
  apply (simp add: rvfun_of_prfun_1_2')
  apply (rule rvfun_pchoice_is_prob')
  using ureal_is_prob apply blast
  using ureal_is_prob apply blast
  apply (simp only: rvfun_of_prfun_1_2'')
  apply (simp add: pfun_defs)
  apply (simp add: rvfun_assignment_inverse)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (simp add: fun_eq_iff)
  apply (rule allI)+
  apply (pred_auto)
  defer
  apply (simp add: infsum_0)
  defer
  apply (simp add: infsum_0)+
proof -
  fix t::\<nat> and x::\<nat>
  assume a1: "\<not> Suc x = x - Suc (0::\<nat>)"
  let ?f1 = "\<lambda>v\<^sub>0. ((if v\<^sub>0 = \<lparr>t\<^sub>v = t, x\<^sub>v = x - Suc (0::\<nat>)\<rparr> then 1::\<real> else (0::\<real>)))"
  let ?f2 = "\<lambda>v\<^sub>0. (if v\<^sub>0 = \<lparr>t\<^sub>v = t, x\<^sub>v = Suc x\<rparr> then 1::\<real> else (0::\<real>))"
  let ?f3 = "\<lambda>v\<^sub>0. (if \<lparr>t\<^sub>v = Suc t, x\<^sub>v = Suc x\<rparr> = v\<^sub>0\<lparr>t\<^sub>v := Suc (t\<^sub>v v\<^sub>0)\<rparr> then 1::\<real> else (0::\<real>))"

  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::srwstate. (?f1 v\<^sub>0 / (2::\<real>) +  ?f2 v\<^sub>0 / (2::\<real>)) * ?f3 v\<^sub>0) = 
        (\<Sum>\<^sub>\<infinity>v\<^sub>0::srwstate. (if v\<^sub>0 = \<lparr>t\<^sub>v = t, x\<^sub>v = Suc x\<rparr> \<and> \<lparr>t\<^sub>v = Suc t, x\<^sub>v = Suc x\<rparr> = v\<^sub>0\<lparr>t\<^sub>v := Suc (t\<^sub>v v\<^sub>0)\<rparr> 
            then (1/2) else (0::\<real>)))"
    apply (rule infsum_cong)
    by (smt (verit, best) a1 div_0 mult_cancel_left2 mult_cancel_right2 srwstate.simps(1) time.update_convs(1))
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::srwstate. (if v\<^sub>0 = \<lparr>t\<^sub>v = t, x\<^sub>v = Suc x\<rparr> then (1/2) else (0::\<real>)))"
    apply (rule infsum_cong)
    by simp
  also have "... = 1/2"
    by (simp add: infsum_singleton_1)
  finally show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::srwstate. (?f1 v\<^sub>0 / (2::\<real>) +  ?f2 v\<^sub>0 / (2::\<real>)) * ?f3 v\<^sub>0) * (2::\<real>) = (1::\<real>)"
    by linarith
next
  fix t::\<nat> and x::\<nat>
  assume a1: "\<not> x - Suc (0::\<nat>) = Suc x"
  let ?f1 = "\<lambda>v\<^sub>0. ((if v\<^sub>0 = \<lparr>t\<^sub>v = t, x\<^sub>v = x - Suc (0::\<nat>)\<rparr> then 1::\<real> else (0::\<real>)))"
  let ?f2 = "\<lambda>v\<^sub>0. (if v\<^sub>0 = \<lparr>t\<^sub>v = t, x\<^sub>v = Suc x\<rparr> then 1::\<real> else (0::\<real>))"
  let ?f3 = "\<lambda>v\<^sub>0. (if \<lparr>t\<^sub>v = Suc t, x\<^sub>v = x - Suc (0::\<nat>)\<rparr> = v\<^sub>0\<lparr>t\<^sub>v := Suc (t\<^sub>v v\<^sub>0)\<rparr> then 1::\<real> else (0::\<real>))"

  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::srwstate. (?f1 v\<^sub>0 / (2::\<real>) +  ?f2 v\<^sub>0 / (2::\<real>)) * ?f3 v\<^sub>0) = 
        (\<Sum>\<^sub>\<infinity>v\<^sub>0::srwstate. (if v\<^sub>0 = \<lparr>t\<^sub>v = t, x\<^sub>v = x - Suc (0::\<nat>)\<rparr> \<and> \<lparr>t\<^sub>v = Suc t, x\<^sub>v = x - Suc (0::\<nat>)\<rparr> = v\<^sub>0\<lparr>t\<^sub>v := Suc (t\<^sub>v v\<^sub>0)\<rparr> 
            then (1/2) else (0::\<real>)))"
    apply (rule infsum_cong)
    by (smt (verit, best) a1 div_0 mult_cancel_left2 mult_cancel_right2 srwstate.simps(1) time.update_convs(1))
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::srwstate. (if v\<^sub>0 = \<lparr>t\<^sub>v = t, x\<^sub>v = x - Suc (0::\<nat>)\<rparr> then (1/2) else (0::\<real>)))"
    apply (rule infsum_cong)
    by simp
  also have "... = 1/2"
    by (simp add: infsum_singleton_1)
  finally show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::srwstate. (?f1 v\<^sub>0 / (2::\<real>) +  ?f2 v\<^sub>0 / (2::\<real>)) * ?f3 v\<^sub>0) * (2::\<real>) = (1::\<real>)"
    by linarith
qed

lemma move_t_alt_is_dist: "is_final_distribution move_t_alt"
  apply (simp add: dist_defs move_t_alt_def)
  apply (expr_auto)
proof -
  fix t::\<nat> and x::\<nat>
  assume a1: " \<not> x - Suc (0::\<nat>) = Suc x"
  let ?f = "\<lambda>s. (if x\<^sub>v s = Suc x then 1::\<real> else (0::\<real>)) * (if t\<^sub>v s = Suc t then 1::\<real> else (0::\<real>)) / (2::\<real>) +
          (if x\<^sub>v s = x - Suc (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if t\<^sub>v s = Suc t then 1::\<real> else (0::\<real>)) / (2::\<real>)"
  have "(\<Sum>\<^sub>\<infinity>s::srwstate. ?f s) = 
    (\<Sum>\<^sub>\<infinity>s::srwstate. (if x\<^sub>v s = Suc x \<and> t\<^sub>v s = Suc t then 1/2 else 0) + 
                     (if x\<^sub>v s = x - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc t then 1/2 else 0))"
    apply (rule infsum_cong)
    by simp
  also have "... = 1"
    apply (subst infsum_add)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (z3) Collect_mono finite.emptyI finite_insert old.unit.exhaust rev_finite_subset singleton_conv srwstate.surjective)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (z3) Collect_mono finite.emptyI finite_insert old.unit.exhaust rev_finite_subset singleton_conv srwstate.surjective)
    apply (subst infsum_singleton_cond_unique)
    apply (metis (mono_tags, opaque_lifting) old.unit.exhaust srwstate.select_convs(1) srwstate.surjective time.select_convs(1))
    apply (subst infsum_singleton_cond_unique)
    apply (metis (mono_tags, opaque_lifting) old.unit.exhaust srwstate.select_convs(1) srwstate.surjective time.select_convs(1))
    by simp
  finally show "(\<Sum>\<^sub>\<infinity>s::srwstate. ?f s) = 1"
    by meson
qed

lemma srw_iterdiff_simp:
  shows "(iterdiff 0 (x\<^sup>< > 0)\<^sub>e (Pt move) 1\<^sub>p) = 1\<^sub>p"
        "(iterdiff (n+1) (x\<^sup>< > 0)\<^sub>e (Pt move) 1\<^sub>p) = 
            prfun_of_rvfun ((\<lbrakk>x\<^sup>< > 0\<rbrakk>\<^sub>\<I>\<^sub>e * (5/6)^\<guillemotleft>n\<guillemotright>)\<^sub>e)"
  apply force
proof -
  show "(iterdiff (n+1) (x\<^sup>< > 0)\<^sub>e (Pt move) 1\<^sub>p) = 
            prfun_of_rvfun ((\<lbrakk>x\<^sup>< > 0\<rbrakk>\<^sub>\<I>\<^sub>e * (5/6)^\<guillemotleft>n\<guillemotright>)\<^sub>e)"
    sorry
qed
  
lemma srw_iter_seq_tendsto_0:
  "\<forall>s::srwstate \<times> srwstate. (\<lambda>n::\<nat>. ureal2real (iterdiff n (x\<^sup>< > 0)\<^sub>e (Pt move) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
proof 
  fix s
  have "(\<lambda>n::\<nat>. ureal2real (iterdiff (n+1) (x\<^sup>< > 0)\<^sub>e (Pt move) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    sorry
  then show "(\<lambda>n::\<nat>. ureal2real (iterdiff n (x\<^sup>< > 0)\<^sub>e (Pt move) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    by (rule LIMSEQ_offset[where k = 1])
qed

lemma Ht_is_dist: "is_final_distribution Ht"
  apply (simp add: dist_defs Ht_def)
  apply (simp add: expr_defs)
  apply (pred_auto)
  defer
  apply (smt (verit, best) divide_nonneg_nonneg le_divide_eq_1_pos power_le_one_iff)
  defer
proof -
  fix t
  let ?f = "\<lambda>s. (if t\<^sub>v s = t then 1::\<real> else (0::\<real>)) * (if x\<^sub>v s = (0::\<nat>) then 1::\<real> else (0::\<real>))"
  have "(\<Sum>\<^sub>\<infinity>s::srwstate. ?f s) 
      = (\<Sum>\<^sub>\<infinity>s::srwstate. (if t\<^sub>v s = t \<and> x\<^sub>v s = (0::\<nat>) then 1::\<real> else (0::\<real>)))"
    apply (rule infsum_cong)
    by force
  also have "... = 1"
    apply (rule infsum_singleton_cond_unique)
    apply (auto)
    by (meson srwstate.select_convs(1) time.select_convs(1))
  finally show "(\<Sum>\<^sub>\<infinity>s::srwstate. ?f s) = (1::\<real>)"
    by blast
next
  fix t::\<nat> and x::\<nat>
  assume a1: "(0::\<nat>) < x"
  let ?f1 = "\<lambda>s. (if x\<^sub>v s = (0::\<nat>) then 1::\<real> else (0::\<real>))"
  let ?f2 = "\<lambda>s. (if t + x \<le> t\<^sub>v s then 1::\<real> else (0::\<real>))"

  have set_eq: "{s. x\<^sub>v s = (0::\<nat>) \<and> t + x \<le> t\<^sub>v s} = {y::srwstate. \<exists>xa::\<nat>. y = \<lparr>t\<^sub>v = t + x + xa, x\<^sub>v = 0::\<nat>\<rparr>}"
    apply (subst set_eq_iff)
    apply (auto)
    apply (rule_tac x = "t\<^sub>v xa - (t + x)" in exI)
    by simp
  have "(\<Sum>\<^sub>\<infinity>s::srwstate. ?f1 s * ?f2 s * ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - (t + x)) / (2::\<real>)) = 
        (\<Sum>\<^sub>\<infinity>s::srwstate. (if x\<^sub>v s = (0::\<nat>) \<and> t + x \<le> t\<^sub>v s then 
          ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - (t + x)) / (2::\<real>) else (0::\<real>)))"
    apply (rule infsum_cong)
    by force
  also have "... = (\<Sum>\<^sub>\<infinity>s::srwstate \<in> {s. x\<^sub>v s = (0::\<nat>) \<and> t + x \<le> t\<^sub>v s}. 
                      ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - (t + x)) / (2::\<real>))"
    by (smt (verit, ccfv_SIG) DiffD2 Diff_UNIV IntE empty_iff infsum_cong_neutral mem_Collect_eq)
  also have "... = infsum (\<lambda>s. ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - (t + x)) / (2::\<real>)) ((\<lambda>n::\<nat>. \<lparr>t\<^sub>v = t + x + n, x\<^sub>v = 0\<rparr>) ` UNIV)"
    apply (simp add: image_def)
    using set_eq by presburger
  (* \<open>infsum g (h ` A) = infsum (g \<circ> h) A\<close> *)
  also have "...  = (\<Sum>\<^sub>\<infinity>n::\<nat>. ((1::\<real>) / (2::\<real>)) ^ n / 2 )"
    apply (subst infsum_reindex)
    apply (simp add: inj_def)
    apply (rule infsum_cong)
    by (auto)
  also have "... = 1"
    apply (subst infsetsum_infsum[symmetric])
    apply (simp add: abs_summable_on_nat_iff')
    apply (subst infsetsum_nat)
    apply (simp add: abs_summable_on_nat_iff')
    apply auto
    using power_half_series sums_unique by fastforce
  finally show "(\<Sum>\<^sub>\<infinity>s::srwstate. ?f1 s * ?f2 s * ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - (t + x)) / (2::\<real>)) = (1::\<real>)"
    by meson
qed

lemma Ht_is_fp: "\<F> (x\<^sup>< > 0)\<^sub>e (Pt move) (prfun_of_rvfun (Ht)) = prfun_of_rvfun (Ht)"
  apply (simp add: Ht_def loopfunc_def)
  apply (simp add: pfun_defs srw_move_t)
  apply (subst rvfun_skip_inverse)
  apply (subst rvfun_skip\<^sub>_f_simp)
  apply (subst rvfun_seqcomp_inverse)
  apply (simp add: move_t_alt_is_dist rvfun_inverse rvfun_prob_sum1_summable'(1))
  using ureal_is_prob apply blast
  apply (subst rvfun_inverse)
  apply (simp add: move_t_alt_is_dist rvfun_prob_sum1_summable'(1))
  apply (subst rvfun_inverse)
  apply (expr_auto add: dist_defs)
  apply (subgoal_tac "((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - (t + x))  \<le> 1")
  apply (smt (verit, ccfv_threshold) divide_le_eq_1_pos divide_nonneg_nonneg power_le_one)
  apply (simp add: power_le_one_iff)
  apply (simp only: move_t_alt_def)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (expr_simp_1)
  apply (pred_auto)
  defer
  apply (simp add: infsum_0)+
proof -
  fix t and x and t\<^sub>v'::\<nat>
  assume a1: "(0::\<nat>) < x"
  assume a2: "t + x \<le> t\<^sub>v'"
  let ?f = "\<lambda>v\<^sub>0::srwstate.
          ((if x\<^sub>v v\<^sub>0 = Suc x then 1::\<real> else (0::\<real>)) * (if t\<^sub>v v\<^sub>0 = Suc t then 1::\<real> else (0::\<real>)) / (2::\<real>) +
           (if x\<^sub>v v\<^sub>0 = x - Suc (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if t\<^sub>v v\<^sub>0 = Suc t then 1::\<real> else (0::\<real>)) / (2::\<real>)) *
          ((if x\<^sub>v v\<^sub>0 = (0::\<nat>) then 1::\<real> else (0::\<real>)) * (if t\<^sub>v' = t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) *
           (if x\<^sub>v v\<^sub>0 = (0::\<nat>) then 1::\<real> else (0::\<real>)) +
           (if (0::\<nat>) < x\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0 \<le> t\<^sub>v' then 1::\<real> else (0::\<real>)) *
           ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v' - (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0)) / (2::\<real>))"

  have set_eq_0: "{s::srwstate. x\<^sub>v s = x - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc t \<and> x\<^sub>v s = (0::\<nat>) \<and> t\<^sub>v' = t\<^sub>v s} = 
        (if x = Suc 0 \<and> t\<^sub>v' = Suc t then {s::srwstate. x\<^sub>v s = x - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc t} else {})"
    apply (auto)
    using a1 by linarith
  have card_set_0: "card {s::srwstate. x\<^sub>v s = x - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc t \<and> x\<^sub>v s = (0::\<nat>) \<and> t\<^sub>v' = t\<^sub>v s} = 
    (if x = Suc 0 \<and> t\<^sub>v' = Suc t then 1 else 0)"
    apply (simp add: set_eq_0)
    apply (auto)
    by (smt (verit, best) card_1_singleton old.unit.exhaust srwstate.select_convs(1) srwstate.surjective time.select_convs(1))

  have set_eq_1: "{s::srwstate. x\<^sub>v s = Suc x \<and> t\<^sub>v s = Suc t \<and> (0::\<nat>) < x\<^sub>v s \<and> Suc t + Suc x \<le> t\<^sub>v'} = 
    (if Suc t + Suc x \<le> t\<^sub>v' then {s::srwstate. x\<^sub>v s = Suc x \<and> t\<^sub>v s = Suc t} else {})"
    by auto
  have card_set_1: "card {s::srwstate. x\<^sub>v s = Suc x \<and> t\<^sub>v s = Suc t \<and> (0::\<nat>) < x\<^sub>v s \<and> Suc t + Suc x \<le> t\<^sub>v'} 
    = (if Suc t + Suc x \<le> t\<^sub>v' then 1 else 0)"
    apply (simp only: set_eq_1)
    apply auto
    by (smt (verit, best) card_1_singleton old.unit.exhaust srwstate.select_convs(1) srwstate.surjective time.select_convs(1))

  have set_eq_2: "{s::srwstate. x\<^sub>v s = x - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc t \<and> (0::\<nat>) < x\<^sub>v s \<and> Suc t + x - Suc (0::\<nat>) \<le> t\<^sub>v'}
     = (if x > Suc 0 \<and> Suc t + x - Suc (0::\<nat>) \<le> t\<^sub>v' then {s::srwstate. x\<^sub>v s = x - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc t} else {})"
    by (auto)
  have card_set_2: "card {s::srwstate. x\<^sub>v s = x - Suc (0::\<nat>) \<and> t\<^sub>v s = Suc t \<and> (0::\<nat>) < x\<^sub>v s \<and> Suc t + x - Suc (0::\<nat>) \<le> t\<^sub>v'} 
    = (if x > Suc 0 \<and> Suc t + x - Suc (0::\<nat>) \<le> t\<^sub>v' then 1 else 0)"
    apply (simp only: set_eq_2)
    apply (auto)
    by (smt (verit, best) card_1_singleton old.unit.exhaust srwstate.select_convs(1) srwstate.surjective time.select_convs(1))

  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::srwstate. ?f v\<^sub>0) = (\<Sum>\<^sub>\<infinity>v\<^sub>0::srwstate. 
          ((if x\<^sub>v v\<^sub>0 = Suc x \<and> t\<^sub>v v\<^sub>0 = Suc t then 1/2 else (0::\<real>)) +
           (if x\<^sub>v v\<^sub>0 = x - Suc (0::\<nat>) \<and> t\<^sub>v v\<^sub>0 = Suc t then 1/2 else (0::\<real>))) *
          ((if x\<^sub>v v\<^sub>0 = (0::\<nat>) \<and> t\<^sub>v' = t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) +
           (if (0::\<nat>) < x\<^sub>v v\<^sub>0 \<and> t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0 \<le> t\<^sub>v' then ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v' - (t\<^sub>v v\<^sub>0 + x\<^sub>v v\<^sub>0)) / (2::\<real>) else (0::\<real>))
           ))"
    apply (rule infsum_cong)
    by simp
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::srwstate. 
          (if x\<^sub>v v\<^sub>0 = x - Suc (0::\<nat>) \<and> t\<^sub>v v\<^sub>0 = Suc t \<and> x\<^sub>v v\<^sub>0 = (0::\<nat>) \<and> t\<^sub>v' = t\<^sub>v v\<^sub>0 then 1/2 else 0) + 
          (if x\<^sub>v v\<^sub>0 = Suc x \<and> t\<^sub>v v\<^sub>0 = Suc t \<and> (0::\<nat>) < x\<^sub>v v\<^sub>0 \<and> Suc t + Suc x \<le> t\<^sub>v' then 
            ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v' - (Suc t + Suc x)) / (2::\<real>) / 2 else 0) + 
          (if x\<^sub>v v\<^sub>0 = x - Suc (0::\<nat>) \<and> t\<^sub>v v\<^sub>0 = Suc t \<and> (0::\<nat>) < x\<^sub>v v\<^sub>0 \<and> Suc t + x - Suc (0::\<nat>) \<le> t\<^sub>v' then 
            ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v' - (Suc t + x - Suc (0::\<nat>))) / (2::\<real>) / 2 else 0))"
    apply (rule infsum_cong)
    by (auto)
  also have "... = ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v' - (t + x)) / 2"
    apply (subst infsum_add)
    apply (subst summable_on_add)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_threshold) Collect_mem_eq Collect_mono_iff Zero_not_Suc card.infinite card_1_singleton finite.simps old.unit.exhaust rev_finite_subset srwstate.surjective)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_threshold) Collect_mem_eq Collect_mono_iff Zero_not_Suc card.infinite card_1_singleton finite.simps old.unit.exhaust rev_finite_subset srwstate.surjective)
    apply (simp)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_threshold) Collect_mem_eq Collect_mono_iff Zero_not_Suc card.infinite card_1_singleton finite.simps old.unit.exhaust rev_finite_subset srwstate.surjective)
    apply (subst infsum_add)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_threshold) Collect_mem_eq Collect_mono_iff Zero_not_Suc card.infinite card_1_singleton finite.simps old.unit.exhaust rev_finite_subset srwstate.surjective)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_threshold) Collect_mem_eq Collect_mono_iff Zero_not_Suc card.infinite card_1_singleton finite.simps old.unit.exhaust rev_finite_subset srwstate.surjective)
    apply (subst infsum_constant_finite_states)
    apply (smt (verit, del_insts) Collect_mem_eq Collect_mono card.infinite card_1_singleton finite.simps nat.distinct(1) old.unit.exhaust rev_finite_subset srwstate.surjective)
    apply (subst infsum_constant_finite_states)
    apply (smt (verit, del_insts) Collect_mem_eq Collect_mono card.infinite card_1_singleton finite.simps nat.distinct(1) old.unit.exhaust rev_finite_subset srwstate.surjective)
    apply (subst infsum_constant_finite_states)
    apply (smt (verit, del_insts) Collect_mem_eq Collect_mono card.infinite card_1_singleton finite.simps nat.distinct(1) old.unit.exhaust rev_finite_subset srwstate.surjective)
    apply (simp only: card_set_0 card_set_1 card_set_2)
    apply (auto)
    sledgehammer
    by simp

    show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::srwstate. ?f v\<^sub>0) * (2::\<real>) = ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v' - (t + x))"
  qed

end
