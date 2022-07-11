section \<open> Probabilistic relation programming example: six-sided dice \<close>

theory utp_prob_rel_lattice_dices
  imports 
    "../utp_prob_rel_lattice_laws" 
begin 

unbundle UTP_Syntax

declare [[show_types]]

subsection \<open> Throw Two dice\<close>
text \<open>This example is from Section 15 of the Hehner's paper ``A probability perspective''.

The invariant of the program for an equal result is 
@{text "\<lbrakk>u' = v'\<rbrakk>\<^sub>\<I> * \<lbrakk>t' \<ge> t+1\<rbrakk>\<^sub>\<I> * (5/6)^(t'-t-1) * (1/6)"}.

This program cannot guarantee absolute termination (see Section 2.3 of ``
2005_Book_Abstraction Refinement and Proof for Probabilistic Systems''), but it is almost-certain 
termination.

The probability for non-termination is @{text "\<lbrakk>u' \<noteq> v'\<rbrakk>\<^sub>\<I> * \<lbrakk>t' \<ge> t+1\<rbrakk>\<^sub>\<I> * (5/6)^(t'-t)"}. When 
@{text "t'"} tends to @{text "\<infinity>"}, then the probability tends to 0.
\<close>

subsubsection \<open> State space \<close>
paragraph \<open> \<close>
(*
typedef  Tdice = "{v::nat. v \<le> 6 \<and> v \<ge> 1}"
morphisms td2nat nat2td
  apply (rule_tac x = "1" in exI)
  by auto
*)
alphabet dstate = 
  d1 :: nat
  d2 :: nat

abbreviation "outcomes \<equiv> {1..(6::nat)}"

definition dice_throw:: "dstate prhfun" where
"dice_throw = prfun_of_rvfun (d1 \<^bold>\<U> outcomes) ; prfun_of_rvfun (d2 \<^bold>\<U> outcomes)"

definition dice_throw_loop where
"dice_throw_loop = while\<^sub>p (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e do dice_throw od"

definition H:: "dstate rvhfun" where 
"H = (\<lbrakk>d1\<^sup>> = d2\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"

term "(\<lambda>n. iterate\<^sub>p n (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p)"

definition f :: "\<nat> \<Rightarrow> dstate prhfun" where
"f = (\<lambda>n. iterate\<^sub>p n (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p)"

lemma r_simp: "rvfun_of_prfun [\<lambda>\<s>::dstate \<times> dstate. p]\<^sub>e = (\<lambda>s. ureal2real p)"
  by (simp add: SEXP_def rvfun_of_prfun_def)

lemma d1_uni_is_dist: "is_final_distribution (rvfun_of_prfun (prfun_of_rvfun (d1 \<^bold>\<U> outcomes)))"
  apply (subst rvfun_uniform_dist_is_dist')
  apply blast
  by simp+

lemma d2_uni_is_dist: "is_final_distribution (rvfun_of_prfun (prfun_of_rvfun (d2 \<^bold>\<U> outcomes)))"
  apply (subst rvfun_uniform_dist_is_dist')
  apply blast
  by simp+
  
lemma dice_throw_is_dist: "is_final_distribution (rvfun_of_prfun dice_throw)"
  apply (simp only: dice_throw_def pseqcomp_def)
  apply (subst rvfun_seqcomp_inverse)
  using d1_uni_is_dist apply blast
  using ureal_is_prob apply blast
  apply (subst rvfun_seqcomp_is_dist)
  using d1_uni_is_dist apply blast
  using d2_uni_is_dist by blast+

lemma dice_throw_altdef: "rvfun_of_prfun dice_throw = (\<lbrakk>d1\<^sup>> \<in> outcomes\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>d2\<^sup>> \<in> outcomes\<rbrakk>\<^sub>\<I>\<^sub>e / 36)\<^sub>e"
  apply (simp add: dice_throw_def pseqcomp_def)
  apply (subst rvfun_uniform_dist_inverse)
  apply (simp)+
  apply (subst rvfun_uniform_dist_inverse)
  apply (simp)+
  apply (subst rvfun_seqcomp_inverse)
  apply (simp add: rvfun_uniform_dist_is_dist)
  using d2_vwb_lens rvfun_uniform_dist_is_prob apply blast
  apply (subst rvfun_uniform_dist_altdef)
  apply (simp)+
  apply (subst rvfun_uniform_dist_altdef)
  apply (simp)+
  apply (rel_auto)
  defer
  apply (smt (verit, ccfv_SIG) atLeastAtMost_iff divide_eq_0_iff dstate.ext_inject 
        dstate.update_convs(2) infsum_0 mult_eq_0_iff)
  apply (smt (verit, ccfv_SIG) atLeastAtMost_iff divide_eq_0_iff dstate.ext_inject 
        dstate.update_convs(2) infsum_0 mult_eq_0_iff)
  apply (smt (verit, ccfv_SIG) atLeastAtMost_iff divide_eq_0_iff dstate.ext_inject 
        dstate.update_convs(2) infsum_0 mult_eq_0_iff)
  apply (smt (verit, ccfv_SIG) atLeastAtMost_iff divide_eq_0_iff dstate.ext_inject 
        dstate.update_convs(2) infsum_0 mult_eq_0_iff)
proof -
  fix d2\<^sub>v d1\<^sub>v d2\<^sub>v'
  assume a1: "Suc (0::\<nat>) \<le> d1\<^sub>v"
  assume a2: "d1\<^sub>v \<le> (6::\<nat>)"
  assume a3: "Suc (0::\<nat>) \<le> d2\<^sub>v'"
  assume a4: "d2\<^sub>v' \<le> (6::\<nat>)"
  let ?f1 = "\<lambda>v\<^sub>0. (if \<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. \<lparr>d1\<^sub>v = x, d2\<^sub>v = d2\<^sub>v\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) *
          (if \<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. v\<^sub>0\<lparr>d2\<^sub>v := x\<rparr> = \<lparr>d1\<^sub>v = d1\<^sub>v, d2\<^sub>v = d2\<^sub>v'\<rparr> then 1::\<real> else (0::\<real>))"
  let ?f2 = "\<lambda>v\<^sub>0. (if (\<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. \<lparr>d1\<^sub>v = x, d2\<^sub>v = d2\<^sub>v\<rparr> = v\<^sub>0 \<and> 
              (\<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. v\<^sub>0\<lparr>d2\<^sub>v := x\<rparr> = \<lparr>d1\<^sub>v = d1\<^sub>v, d2\<^sub>v = d2\<^sub>v'\<rparr>)) 
              then 1::\<real> else (0::\<real>))"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::dstate. ?f1 v\<^sub>0 / (36::\<real>))"
  have f1_f2_eq: "\<forall>v\<^sub>0. ?f1 v\<^sub>0 = ?f2 v\<^sub>0"
    by simp

  have finite_d1: "finite {s::dstate. (\<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. \<lparr>d1\<^sub>v = x, d2\<^sub>v = d2\<^sub>v'\<rparr> = s)}"
    apply (subst finite_Collect_bex)
    by (simp)+

  have set_eq: "{v\<^sub>0::dstate. \<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. \<lparr>d1\<^sub>v = x, d2\<^sub>v = d2\<^sub>v\<rparr> = v\<^sub>0 \<and> 
                    (\<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. v\<^sub>0\<lparr>d2\<^sub>v := x\<rparr> = \<lparr>d1\<^sub>v = d1\<^sub>v, d2\<^sub>v = d2\<^sub>v'\<rparr>)}
    = {v\<^sub>0::dstate. \<lparr>d1\<^sub>v = d1\<^sub>v, d2\<^sub>v = d2\<^sub>v\<rparr> = v\<^sub>0}"
    using a1 a2 a3 a4 by fastforce

  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::dstate. ?f1 v\<^sub>0) = (\<Sum>\<^sub>\<infinity>v\<^sub>0::dstate. ?f2 v\<^sub>0)"
    using f1_f2_eq infsum_cong by presburger
  also have "... = card {v\<^sub>0. \<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}.
             \<lparr>d1\<^sub>v = x, d2\<^sub>v = d2\<^sub>v\<rparr> = v\<^sub>0 \<and>
             (\<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. v\<^sub>0\<lparr>d2\<^sub>v := x\<rparr> = \<lparr>d1\<^sub>v = d1\<^sub>v, d2\<^sub>v = d2\<^sub>v'\<rparr>)}"
    apply (subst infsum_constant_finite_states)
    apply (subst finite_subset[where B = "{s::dstate. (\<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. \<lparr>d1\<^sub>v = x, d2\<^sub>v = d2\<^sub>v\<rparr> = s)}"])
    apply blast
    by (simp add: finite_d1)+
  also have lhs_1: "... = 1"
    using set_eq by simp
  show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::dstate.
          (if \<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. \<lparr>d1\<^sub>v = x, d2\<^sub>v = d2\<^sub>v\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) *
          (if \<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. v\<^sub>0\<lparr>d2\<^sub>v := x\<rparr> = \<lparr>d1\<^sub>v = d1\<^sub>v, d2\<^sub>v = d2\<^sub>v'\<rparr> then 1::\<real> else (0::\<real>)) /
          (36::\<real>)) * (36::\<real>) = (1::\<real>)"
    apply (subst infsum_cdiv_left)
    apply (simp add: f1_f2_eq)
    apply (subst infsum_constant_finite_states_summable)
    apply (subst finite_subset[where B = "{s::dstate. (\<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. \<lparr>d1\<^sub>v = x, d2\<^sub>v = d2\<^sub>v\<rparr> = s)}"])
    apply blast
    apply (simp add: finite_d1)+
    using lhs_1 calculation by presburger
qed

(*
lemma dstate_UNIV_set: "(UNIV::\<bbbP> dstate) = {\<lparr>c\<^sub>v = chead\<rparr>, \<lparr>c\<^sub>v = ctail\<rparr>}"
  apply (auto)
  by (metis Tcoin.exhaust dstate.cases)

lemma dstate_rel_UNIV_set:
  "{s::dstate \<times> dstate. True} = {(\<lparr>c\<^sub>v = chead\<rparr>, \<lparr>c\<^sub>v = chead\<rparr>), 
  (\<lparr>c\<^sub>v = chead\<rparr>, \<lparr>c\<^sub>v = ctail\<rparr>),  (\<lparr>c\<^sub>v = ctail\<rparr>, \<lparr>c\<^sub>v = ctail\<rparr>), (\<lparr>c\<^sub>v = ctail\<rparr>, \<lparr>c\<^sub>v = chead\<rparr>)}"
  apply (simp)
  apply (subst set_eq_iff)
  apply (rule allI)
  apply (rule iffI)
  apply (clarify)
  using dstate_UNIV_set apply blast
  apply (clarify)
  by blast

lemma ureal2real_1_2: "ureal2real (ereal2ureal (ereal (1::\<real>))) / (2::\<real>) = (1::\<real>) / (2::\<real>)"
  apply (simp add: ureal_defs)
  using real_1 by presburger

lemma sum_1_2: "(sum ((^) ((1::\<real>) / (2::\<real>))) {Suc (0::\<nat>)..n} +
               ((1::\<real>) / (2::\<real>)) ^ n / (2::\<real>)) = 
  (sum ((^) ((1::\<real>) / (2::\<real>))) {Suc (0::\<nat>)..n+1})"
  by (metis (no_types, lifting) One_nat_def Suc_1 Suc_eq_plus1 add_is_0 less_Suc0 one_neq_zero 
      one_power2 power_Suc power_add power_one_over sum.cl_ivl_Suc times_divide_eq_left times_divide_eq_right)

lemma sum_geometric_series: 
  (* "(sum ((^) ((1::\<real>) / (2::\<real>))) {Suc (0::\<nat>)..n + (1::\<nat>)}) = (1 - 1 / 2 ^ (n+2)) / (1 - 1/2) - 1" *)
  "(sum ((^) ((1::\<real>) / (2::\<real>))) {Suc (0::\<nat>)..n + (1::\<nat>)}) = 1 - 1 / 2 ^ (n+1)"
  apply (induction n)
  apply (simp)
  by (simp add: power_one_over sum_gp)

lemma sum_geometric_series_1: 
  "(sum ((^) ((1::\<real>) / (2::\<real>))) {1..n + (1::\<nat>)}) = 1 - 1 / 2 ^ (n+1)"
  apply (induction n)
   apply (simp)
  using One_nat_def sum_geometric_series by presburger

lemma sum_geometric_series': 
  "(sum ((^) ((1::\<real>) / (2::\<real>))) {Suc (0::\<nat>)..n}) = 1 - 1 / 2 ^ (n)"
  apply (induction n)
  apply (simp)
  by (simp add: power_one_over sum_gp)

lemma sum_geometric_series_ureal:
  "ureal2real (ereal2ureal (ereal (sum ((^) ((1::\<real>) / (2::\<real>))) {Suc (0::\<nat>)..n + (1::\<nat>)}))) / (2::\<real>)
  = (1 - 1 / 2 ^ (n+1))/2"
  apply (subst sum_geometric_series)
  apply (simp add: ureal_defs)
  apply (subst real2uereal_inverse)
  using max.cobounded1 apply blast
   apply simp
  apply (simp add: max_def)
  by (smt (z3) one_le_power)

lemma iterate_dice_throw_bottom_simp:
  shows "iterate\<^sub>p 0 (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p = 0\<^sub>p"
        "iterate\<^sub>p (Suc 0) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p = (\<lbrakk>$c\<^sup>< = chead \<and> $c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)"
        "iterate\<^sub>p (n+2) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p = 
              (\<lbrakk>$c\<^sup>< = chead \<and> $c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e + 
               \<lbrakk>$c\<^sup>< = ctail \<and> $c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e * (\<Sum>i\<in>{1..\<guillemotleft>n+1\<guillemotright>}. (1/2)^i))\<^sub>e"
  apply (auto)
  apply (simp add: Fwhile_def)
  apply (simp add: prfun_zero_right')
  apply (simp add: pfun_defs)
  apply (subst rvfun_skip_inverse)
  apply (subst ureal_zero)
  apply (simp add: ureal_defs)
  apply (subst fun_eq_iff)
  apply (expr_auto)
  apply (meson Tcoin.exhaust)
  apply (induct_tac n)
  apply (simp)
  apply (simp add: Fwhile_def)
  apply (simp add: prfun_zero_right')
  apply (simp add: pfun_defs)
  apply (subst rvfun_skip_inverse)+
  apply (subst ureal_zero)
  apply (subst rvfun_pcond_inverse)
  apply (metis ureal_is_prob ureal_zero)
  apply (simp add: rvfun_skip_f_is_prob)
  apply (subst dice_throw_altdef)
  apply (subst rvfun_inverse)
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: infsum_nonneg iverson_bracket_def)
  apply (rel_auto)
  apply (simp add: dstate_UNIV_set)
  apply (smt (verit, ccfv_SIG) prfun_in_0_1' rvfun_skip_inverse)
  apply (simp add: prfun_of_rvfun_def)
  apply (expr_auto)
  apply (simp add: real2ureal_def)
  apply (simp add: infsum_0 iverson_bracket_def real2ureal_def rel_skip)
  apply (meson Tcoin.exhaust)
  apply (simp add: dstate_UNIV_set)
  apply (rel_auto)
  apply (simp add: real2ureal_def)
  using real2ureal_def apply blast+
  apply (simp add: dstate_UNIV_set)
  apply (rel_auto)
  using real2ureal_def apply blast+
  apply (simp add: dstate_UNIV_set)
  apply (rel_auto)
  using real2ureal_def apply blast+
  (* *)
  apply (simp)
  apply (subst Fwhile_def)
  apply (subst pseqcomp_def)
  apply (subst pcond_def)
  apply (subst dice_throw_altdef)
  apply (subst rvfun_inverse)
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: infsum_nonneg  prfun_in_0_1')
  apply (rel_auto)
  apply (simp add: dstate_UNIV_set)
  apply (simp add: rvfun_of_prfun_def)
  apply (auto)
  apply (smt (verit, best) field_sum_of_halves ureal_upper_bound)
  using ureal_upper_bound apply blast
  apply (subst prfun_of_rvfun_def)
  apply (subst rvfun_of_prfun_def)+
  apply (expr_auto)
  apply (simp add: dstate_UNIV_set)
  apply (rel_auto)
  defer
  apply (subst prfun_skip_id)
  apply (simp add: one_ureal.rep_eq real2ureal_def ureal2real_def)
  using Tcoin.exhaust apply blast
  apply (metis (full_types) Tcoin.exhaust dstate.select_convs(1) ereal_real o_def prfun_skip_not_id real2ureal_def ureal2real_def zero_ereal_def zero_ureal.rep_eq)
  apply (subst infsum_0)
  apply (subst ureal_defs)
  apply (smt (verit, best) divide_eq_0_iff ereal_max min.absorb2 min.commute mult_eq_0_iff o_apply real_of_ereal_0 ureal2ereal_inverse ureal2real_def zero_ereal_def zero_less_one_ereal zero_ureal.rep_eq)
  using real2ureal_def apply presburger
  using Tcoin.exhaust apply blast
  apply (subst infsum_0)
  apply (subst ureal_defs)
  apply (smt (verit, best) divide_eq_0_iff ereal_max min.absorb2 min.commute mult_eq_0_iff o_apply real_of_ereal_0 ureal2ereal_inverse ureal2real_def zero_ereal_def zero_less_one_ereal zero_ureal.rep_eq)
  using real2ureal_def apply blast
  apply (metis (full_types) Tcoin.exhaust dstate.ext_inject o_def prfun_skip_not_id real2ureal_def real_of_ereal_0 ureal2real_def zero_ureal.rep_eq)
  apply (subst ureal2real_1_2)
  apply (subst sum_1_2)
  apply (subst sum_geometric_series_ureal)
  apply (subst sum_geometric_series')
  apply (subst ureal_defs)+
proof -
  fix n
  have f1: "((1::\<real>) / (2::\<real>) + ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ (n + (1::\<nat>))) / (2::\<real>)) = 
        ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ (n + 2))"
    by (simp add: add.assoc diff_divide_distrib)
  have f2: "((3::\<real>) * ((1::\<real>) / (2::\<real>)) ^ n / (4::\<real>) + ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ n)) =  
          ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ (n+2))"
    apply (auto)
    by (simp add: power_one_over)
  show "ereal2ureal' (min (max (0::ereal) (ereal ((1::\<real>) / (2::\<real>) + ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ (n + (1::\<nat>))) / (2::\<real>)))) (1::ereal)) =
       ereal2ureal' (min (max (0::ereal) (ereal ((3::\<real>) * ((1::\<real>) / (2::\<real>)) ^ n / (4::\<real>) + ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ n)))) (1::ereal))"
    using f1 f2 by presburger
qed

lemma dice_throw_drop_initial_segments_eq: 
  "(\<Squnion>n::\<nat>. iterate\<^sub>p (n+2) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p) = (\<Squnion>n::\<nat>. iterate\<^sub>p (n) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p)"
  apply (rule increasing_chain_sup_subset_eq)
  apply (rule iterate_increasing_chain)
  by (simp add: dice_throw_is_dist)

lemma dice_throw_iterate_limit_sup:
  assumes "f = (\<lambda>n. (iterate\<^sub>p (n+2) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p))"
  shows "(\<lambda>n. ureal2real (f n s)) \<longlonglongrightarrow> (ureal2real (\<Squnion>n::\<nat>. f n s))"
  apply (simp only: assms)
  apply (subst LIMSEQ_ignore_initial_segment[where k = "2"])
  apply (subst increasing_chain_sup_subset_eq[where m = "2"])
  apply (rule increasing_chain_fun)
  apply (rule iterate_increasing_chain)
  apply (simp add: dice_throw_is_dist)
  apply (subst increasing_chain_limit_is_lub')
  apply (simp add: increasing_chain_def)
  apply (auto)
  apply (rule le_funI)
  by (smt (verit, ccfv_threshold) dice_throw_is_dist iterate_increasing2 le_fun_def)

lemma fa: "(\<lambda>n::\<nat>. ureal2real (ereal2ureal (ereal ((1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ n)))))
  = (\<lambda>n::\<nat>. ((1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ n)))"
  apply (subst fun_eq_iff)
  apply (auto)
  apply (simp add: ureal_defs)
  apply (subst real2uereal_inverse)
   apply (meson max.cobounded1)
   apply simp
proof -
  fix x
  have f1: "(max (0::ereal) (ereal ((1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ x)))) = 
    (ereal ((1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ x)))"
    apply (simp add: max_def)
    by (smt (z3) one_le_power)
  show "real_of_ereal (max (0::ereal) (ereal ((1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ x)))) =
       (1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ x)"
    by (simp add: f1)
qed

lemma fb: 
  " (\<lambda>n::\<nat>. (1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ n)) \<longlonglongrightarrow> (1::\<real>)"
proof -
  have f0: "(\<lambda>n::\<nat>. ((1::\<real>) - ((1::\<real>) / (2::\<real>)) ^ (n+1))) = (\<lambda>n::\<nat>. (1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ n))"
    apply (subst fun_eq_iff)
    apply (auto)
    using power_one_over by blast
  have f1: "(\<lambda>n::\<nat>. ((1::\<real>) - ((1::\<real>) / (2::\<real>)) ^ (n+1))) \<longlonglongrightarrow> (1 - 0)"
    apply (rule tendsto_diff)
    apply (auto)
    apply (rule LIMSEQ_power_zero)
    by simp
  show ?thesis
    using f0 f1 by auto
qed

lemma dice_throw_iterate_limit_cH:
  assumes "f = (\<lambda>n. (iterate\<^sub>p (n+2) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p))"
  shows "(\<lambda>n. ureal2real (f n s)) \<longlonglongrightarrow> ((\<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e s)"
  apply (simp only: assms)
  apply (subst iterate_dice_throw_bottom_simp(3))
  apply (subst sum_geometric_series_1)
  apply (rel_auto)
  apply (simp add: fa)
  apply (simp add: fb)
  apply (metis LIMSEQ_const_iff nle_le real2ureal_def ureal_lower_bound ureal_real2ureal_smaller)
  apply (metis comp_def one_ereal_def one_ureal.rep_eq one_ureal_def real_ereal_1 tendsto_const ureal2real_def)
  apply (metis LIMSEQ_const_iff nle_le real2ureal_def ureal_lower_bound ureal_real2ureal_smaller)
  by (meson Tcoin.exhaust)+

lemma fh:
  assumes "f = (\<lambda>n. (iterate\<^sub>p (n+2) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p))"
  shows "((\<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e s) = (ureal2real (\<Squnion>n::\<nat>. f n s))"
  apply (subst LIMSEQ_unique[where X = "(\<lambda>n. ureal2real (f n s))" and a = "((\<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e s)" and 
          b = "(ureal2real (\<Squnion>n::\<nat>. f n s))"])
  using dice_throw_iterate_limit_cH apply (simp add: assms)
  using dice_throw_iterate_limit_sup apply (simp add: assms)
  by auto

lemma fi: "(\<Squnion>n::\<nat>. iterate\<^sub>p (n+2) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p) = 
  (\<lambda>x::dstate \<times> dstate. ereal2ureal (ereal ((\<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e x)))"
  apply (simp only: fh)
  apply (simp add: ureal2rereal_inverse)
  using SUP_apply by fastforce
*)

lemma iterate_dice_throw_bottom_simp:
  shows "f 0 = 0\<^sub>p"
        "f (Suc 0) = (\<lbrakk>$d1\<^sup>< = $d2\<^sup>< \<and> $d1\<^sup>> = $d1\<^sup>< \<and> $d2\<^sup>> = $d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e)"
        "iterate\<^sub>p (n+2) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p = 
              (\<lbrakk>d1\<^sup>> = d2\<^sup>> \<and> $d1\<^sup>> = $d1\<^sup>< \<and> $d2\<^sup>> = $d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e + 
               \<lbrakk>d1\<^sup>> = d2\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * (\<Sum>i\<in>{1..\<guillemotleft>n+1\<guillemotright>}. (1/2)^i))\<^sub>e"
  apply (simp add: f_def)+
  apply (simp add: Fwhile_def)
  apply (simp add: prfun_zero_right')
  apply (simp add: pfun_defs)
  apply (subst rvfun_skip_inverse)
  apply (subst ureal_zero)
  apply (simp add: ureal_defs)
  apply (subst fun_eq_iff)
  apply (expr_auto)

  apply (meson Tcoin.exhaust)
  apply (induct_tac n)
  apply (simp)
  apply (simp add: Fwhile_def)
  apply (simp add: prfun_zero_right')
  apply (simp add: pfun_defs)
  apply (subst rvfun_skip_inverse)+
  apply (subst ureal_zero)
  apply (subst rvfun_pcond_inverse)
  apply (metis ureal_is_prob ureal_zero)
  apply (simp add: rvfun_skip_f_is_prob)
  apply (subst dice_throw_altdef)
  apply (subst rvfun_inverse)
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: infsum_nonneg iverson_bracket_def)
  apply (rel_auto)
  apply (simp add: dstate_UNIV_set)
  apply (smt (verit, ccfv_SIG) prfun_in_0_1' rvfun_skip_inverse)
  apply (simp add: prfun_of_rvfun_def)
  apply (expr_auto)
  apply (simp add: real2ureal_def)
  apply (simp add: infsum_0 iverson_bracket_def real2ureal_def rel_skip)
  apply (meson Tcoin.exhaust)
  apply (simp add: dstate_UNIV_set)
  apply (rel_auto)
  apply (simp add: real2ureal_def)
  using real2ureal_def apply blast+
  apply (simp add: dstate_UNIV_set)
  apply (rel_auto)
  using real2ureal_def apply blast+
  apply (simp add: dstate_UNIV_set)
  apply (rel_auto)
  using real2ureal_def apply blast+
  (* *)
  apply (simp)
  apply (subst Fwhile_def)
  apply (subst pseqcomp_def)
  apply (subst pcond_def)
  apply (subst dice_throw_altdef)
  apply (subst rvfun_inverse)
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: infsum_nonneg  prfun_in_0_1')
  apply (rel_auto)
  apply (simp add: dstate_UNIV_set)
  apply (simp add: rvfun_of_prfun_def)
  apply (auto)
  apply (smt (verit, best) field_sum_of_halves ureal_upper_bound)
  using ureal_upper_bound apply blast
  apply (subst prfun_of_rvfun_def)
  apply (subst rvfun_of_prfun_def)+
  apply (expr_auto)
  apply (simp add: dstate_UNIV_set)
  apply (rel_auto)
  defer
  apply (subst prfun_skip_id)
  apply (simp add: one_ureal.rep_eq real2ureal_def ureal2real_def)
  using Tcoin.exhaust apply blast
  apply (metis (full_types) Tcoin.exhaust dstate.select_convs(1) ereal_real o_def prfun_skip_not_id real2ureal_def ureal2real_def zero_ereal_def zero_ureal.rep_eq)
  apply (subst infsum_0)
  apply (subst ureal_defs)
  apply (smt (verit, best) divide_eq_0_iff ereal_max min.absorb2 min.commute mult_eq_0_iff o_apply real_of_ereal_0 ureal2ereal_inverse ureal2real_def zero_ereal_def zero_less_one_ereal zero_ureal.rep_eq)
  using real2ureal_def apply presburger
  using Tcoin.exhaust apply blast
  apply (subst infsum_0)
  apply (subst ureal_defs)
  apply (smt (verit, best) divide_eq_0_iff ereal_max min.absorb2 min.commute mult_eq_0_iff o_apply real_of_ereal_0 ureal2ereal_inverse ureal2real_def zero_ereal_def zero_less_one_ereal zero_ureal.rep_eq)
  using real2ureal_def apply blast
  apply (metis (full_types) Tcoin.exhaust dstate.ext_inject o_def prfun_skip_not_id real2ureal_def real_of_ereal_0 ureal2real_def zero_ureal.rep_eq)
  apply (subst ureal2real_1_2)
  apply (subst sum_1_2)
  apply (subst sum_geometric_series_ureal)
  apply (subst sum_geometric_series')
  apply (subst ureal_defs)+
proof -
  fix n
  have f1: "((1::\<real>) / (2::\<real>) + ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ (n + (1::\<nat>))) / (2::\<real>)) = 
        ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ (n + 2))"
    by (simp add: add.assoc diff_divide_distrib)
  have f2: "((3::\<real>) * ((1::\<real>) / (2::\<real>)) ^ n / (4::\<real>) + ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ n)) =  
          ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ (n+2))"
    apply (auto)
    by (simp add: power_one_over)
  show "ereal2ureal' (min (max (0::ereal) (ereal ((1::\<real>) / (2::\<real>) + ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ (n + (1::\<nat>))) / (2::\<real>)))) (1::ereal)) =
       ereal2ureal' (min (max (0::ereal) (ereal ((3::\<real>) * ((1::\<real>) / (2::\<real>)) ^ n / (4::\<real>) + ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ n)))) (1::ereal))"
    using f1 f2 by presburger
qed

lemma coin_flip_loop: "dice_throw_loop = H"
  apply (simp add: dice_throw_loop_def H_def)
  apply (subst sup_continuous_lfp_iteration)
  apply (simp add: dice_throw_is_dist)
  apply (rule finite_subset[where B = "{s::dstate \<times> dstate. True}"])
  apply force
  apply (metis dstate_rel_UNIV_set finite.emptyI finite.insertI)
  apply (simp only: dice_throw_drop_initial_segments_eq[symmetric])
  apply (simp only: fi)
  by auto

end