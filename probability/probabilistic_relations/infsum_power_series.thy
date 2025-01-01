section \<open> Laws related to @{text "infsum"} for power series \<close>

theory infsum_power_series
  imports 
    "HOL-Analysis.Infinite_Set_Sum"
begin 
subsection \<open> Series \<close>

lemma summable_n_2_power_n: 
  "summable (\<lambda>n::nat. (n / (2::real)^n))" (is "summable ?f")
  (* n:                             0, 1,   2,   3,   4 *)
  (* a(n)   = n/2^n                 0, 1/2, 2/4, 3/8, 4/16 *)
  (* a(n+1) = (n+1)/(2^(n+1)):    1/2, 2/4, 3/8, 4/6, 5/8, ... *)
  (* ratio a(n+1)/a(n) = (n+1)/2n:  x, 1,   3/4, 4/6, 5/8, ... *)
  apply (subst summable_ratio_test[where c="3/4" and N="3"])
  apply auto
proof -
  fix n::nat
  assume a1: "3 \<le> n"
  have f1: "((1::real) + real n) / ((2::real) * (2::real) ^ n) = ((n+1) / (2* n)) * (?f n)"
    using a1 by auto
  have f2: "((1::real) + real n) / 1 \<le> (3::real) * real n / ((2::real))"
    using a1 by force
  have f3: "((1::real) + real n) / ((2::real) * (2::real) ^ n) \<le> (3::real) * real n / (2) / ((2::real) * (2::real) ^ n)"
    apply (subst divide_right_mono[where c="((2::real) * (2::real) ^ n)"])
    using f2 apply force
    apply force
    by simp
  show "((1::real) + real n) / ((2::real) * (2::real) ^ n) \<le> (3::real) * real n / ((4::real) * (2::real) ^ n)"
    apply (simp only: f1)
    apply (auto)
    using f3 by force
qed

lemma summable_2_power_n: "summable (\<lambda>n::nat. ((1::real) / (2::real)) ^ n / (2::real))"
  apply (rule summable_divide)
  apply (rule summable_geometric)
  by simp

(*
lemma summable_n_a_power_n: 
  assumes "a \<ge> 2"
  shows "summable (\<lambda>n::nat. (n / (a::real)^n))" (is "summable ?f")
  (* n:           0, 1,   2,      3,    4 *)
  (*              0, 1/a, 2/a^2, 3/a^3, 4/a^4 *)
  (* (n+1)/(a*n): x, 2/a, 3/a*2, 4/a*3, 5/a*4, ... *)
  apply (subst summable_ratio_test[where c="3/4" and N="3"])
  apply auto
proof -
  fix n::nat
  assume a1: "3 \<le> n"
  have f0: "\<bar>a * a ^ n\<bar> = a * a ^ n"
    using assms by auto
  have f1: "\<bar>a ^ n\<bar> = a ^ n"
    using assms by auto
  have f1: "((1::real) + real n) / ((a::real) * (a::real) ^ n) = ((n+1) / (a* n)) * (?f n)"
    using a1 by auto
  have f2: "((1::real) + real n) / 1 \<le> (3::real) * real n / (4/a)"
    apply auto
  have f3: "((1::real) + real n) / ((2::real) * (2::real) ^ n) \<le> (3::real) * real n / (2) / ((2::real) * (2::real) ^ n)"
    apply (subst divide_right_mono[where c="((2::real) * (2::real) ^ n)"])
    using f2 apply force
    apply force
    by simp
  show "((1::real) + real n) / \<bar>a * a ^ n\<bar> \<le> (3::real) * real n / ((4::real) * \<bar>a ^ n\<bar>)"
    apply (simp only: f0)
    apply (simp only: f1)
    apply (auto)
    using f3 by force
qed
*)

lemma summable_1_2_power_n_t_n: 
  "summable (\<lambda>n::nat. ((1::real) / (2::real)) ^ (n) * ((real (t::nat) + real n)))" (is "summable ?f")
proof -
  have f1: "(\<lambda>n::nat. ((1::real) / (2::real)) ^ n * ((real t + real n))) = 
        (\<lambda>n::nat. ((1::real) / (2::real)) ^ n * (real t)  + ((1::real) / (2::real)) ^ n * (real n))"
    by (metis (mono_tags, opaque_lifting) mult_of_nat_commute of_nat_add ring_class.ring_distribs(2))

  have f2: "(\<lambda>n::nat. ((1::real) / (2::real)) ^ n * real n) = (\<lambda>n::nat. ((1::real) / (2::real)) ^ n * n)"
    by simp
  show "summable ?f"
    apply (simp add: f1)
     apply (subst summable_add)
    apply (rule summable_mult2)
    apply (rule summable_geometric)
    apply simp
    apply (subst summable_cong[where g = "(\<lambda>n::nat. (n / (2::real)^n))"])
    apply (simp add: power_divide)
    using summable_n_2_power_n apply blast
    by simp
qed

lemma summable_n_r_power_n: 
  (* n:                                0, 1,    2,   3,   4 *)
  (* a(n)   = n/r^n                    0, 1/r, 2/r^2, 3/r^3, 4/16 *)
  (* a(n+1) = (n+1)/r^(n+1):              1/r, 2/r^2, 3/r^3, 4/r^4, 5/8, ... *)
  (* ratio r(n) = a(n+1)/a(n) = (n+1)/rn:   -,  2/r,    3/2r, 4/3r, 5/8, ... *)
  fixes r :: real
  assumes "r > 1"
  shows "summable (\<lambda>n::nat. ((real n) / (r)^n))" (is "summable ?f")
  apply (subst summable_ratio_test[where c = "((nat \<lfloor>(2.0 * r - 1)/(r - 1)\<rfloor>) + 1) / (r * (nat \<lfloor>(2 * r - 1)/(r - 1)\<rfloor>)) " 
         and N="nat \<lfloor>(2*r-1)/(r-1)\<rfloor>"])
  apply auto
proof -
  have N_lg_0: "(nat \<lfloor>(2 * r - 1) / (r - 1)\<rfloor>) > 0"
    using assms by force
  have N_1: "(2 * r - 1) / (r - 1) = 1 + r / (r - 1)"
    by (smt (verit, best) assms diff_divide_distrib right_inverse_eq)
  have N_2: "(nat \<lfloor>(2 * r - 1) / (r - 1)\<rfloor>) > r / (r - 1)"
    using N_1 by linarith
  have c_1: "(1 + real (nat \<lfloor>(2 * r - 1) / (r - 1)\<rfloor>)) - (r * real (nat \<lfloor>(2 * r - 1) / (r - 1)\<rfloor>))
    = (1 - (r - 1) * real (nat \<lfloor>(2 * r - 1) / (r - 1)\<rfloor>))"
    by (simp add: left_diff_distrib)
  have c_2: "... < 0"
    by (smt (verit, ccfv_SIG) N_2 assms diff_divide_distrib divide_less_eq_1_pos nonzero_mult_div_cancel_left)
  show "(1 + real (nat \<lfloor>(2 * r - 1) / (r - 1)\<rfloor>)) / (r * real (nat \<lfloor>(2 * r - 1) / (r - 1)\<rfloor>)) < 1"
    using c_1 c_2 by force
next
  fix n::nat
  let ?n = "nat \<lfloor>(2 * r - 1) / (r - 1)\<rfloor>"
  assume a1: "?n \<le> n"
  (* (1 + real n) / \<bar>r * r ^ n\<bar> \<le> (1 + real ?n) * real n / (r * real (?n) * \<bar>r ^ n\<bar>) 
  = (1 + real n) * (r * real (?n) * r ^ n)  \<le> (1 + real ?n) * real n * (r * r ^ n)
  = (1 + real n) * r * real ?n * r ^n \<le> (1+real ?n) * real n * r * r ^ n
  = (1 + real n) * real ?n \<le> (1+real ?n) * real n
  *)
  have f0: "?n \<ge> 1"
    using assms le_nat_floor by fastforce
  then have f0': "(r * real (?n) * r ^ n) \<ge> 1"
    by (smt (verit, ccfv_SIG) assms divide_less_eq_1 nonzero_mult_div_cancel_left of_nat_1 of_nat_mono one_le_power)
  from a1 have f1: "real ?n \<le> real n"
    using of_nat_le_iff by blast
  then have f2: "real ?n + real n * real ?n \<le> real n +real ?n * real n"
    by auto
  then have f3: "(1 + real n) * real ?n \<le> (1+real ?n) * real n"
    by (metis (mono_tags, opaque_lifting) of_nat_Suc of_nat_add of_nat_mult times_nat.simps(2))
  then have f4: "(1 + real n) * real ?n * r *  r ^n \<le> (1+real ?n) * real n * r * r ^ n"
    using assms by auto
  then have f5: "(1 + real n) * (r * real (?n) * r ^ n)  \<le> (1 + real ?n) * real n * (r * r ^ n)"
    by (simp add: mult.assoc mult.left_commute)
  then have f6: "(1 + real n) * (r * real (?n) * r ^ n) / (r * r ^ n) \<le> (1 + real ?n) * real n"
    using assms by force
  then have f7: "((1 + real n) * (r * real (?n) * r ^ n) / (r * r ^ n)) / (r * real (?n) * r ^ n) 
               \<le> (1 + real ?n) * real n / (r * real (?n) * r ^ n) "
    using f0 f0' assms by (smt (verit, best) divide_less_cancel)
  then have f8: "((1 + real n) / (r * r ^ n)) \<le> (1 + real ?n) * real n / (r * real (?n) * r ^ n) "
    by (smt (verit) f0' mult.commute nonzero_mult_div_cancel_left times_divide_eq_right)
  show "(1 + real n) / \<bar>r * r ^ n\<bar> \<le> (1 + real ?n) * real n / (r * real (?n) * \<bar>r ^ n\<bar>)"
    apply (subst abs_of_nonneg)
    using assms apply force
    apply (subst abs_of_nonneg)
    using assms apply force
    using f8 by blast
qed

lemma summable_n_r_power_n_mult: 
  fixes r :: real
  assumes "r \<ge> 0" "r < 1" 
  shows "summable (\<lambda>n::nat. ((real n) * r^n))" (is "summable ?f")
proof (cases "r = 0")
  case True
  then show ?thesis by simp
next
  case False
  then show ?thesis
    apply (subgoal_tac "summable (\<lambda>n::nat. ((real n) / (1/r)^n))")
    apply (subst summable_cong[where g="(\<lambda>n::nat. ((real n) / (1/r)^n))"])
    apply (simp add: power_one_over)
    apply simp
    apply (rule summable_n_r_power_n)
    using assms by simp
qed

lemma summable_on_n_r_power_n_mult: 
  fixes r :: real
  assumes "r \<ge> 0" "r < 1" 
  shows "(\<lambda>n::nat. ((real n) * r^n)) summable_on UNIV"
  (*
  apply (subst summable_on_UNIV_nonneg_real_iff)
  using assms(1) apply force
  by (simp add: assms(1) assms(2) summable_n_r_power_n_mult)
  *)
  apply (rule norm_summable_imp_summable_on)
  apply (simp add: assms)
  by (simp add: assms(1) assms(2) summable_n_r_power_n_mult)

lemma summable_n_r_power_n_add_c: 
  fixes r :: real
  assumes "r > 1"
  shows "summable (\<lambda>n::nat. ((real n + c) / (r)^n))" (is "summable ?f")
  apply (subgoal_tac "summable (\<lambda>n::nat. ((real n) / (r)^n) + c / (r ^ n))")
  apply (subst summable_cong[where g="(\<lambda>n::nat. ((real n) / (r)^n) + c / (r ^ n))"])
  apply (simp add: add_divide_distrib)
  apply simp
  apply (rule summable_add)
  apply (simp add: assms summable_n_r_power_n)
  apply (subgoal_tac "summable (\<lambda>n. c * (1/r) ^ n)")
  apply (subst summable_cong[where g="(\<lambda>n. c * (1/r) ^ n)"])
  apply (metis (mono_tags, lifting) divide_inverse eventually_at_top_dense mult_1 power_one_over)
  apply simp
  apply (subst summable_mult)
  using assms summable_geometric by auto

lemma summable_n_r_power_n_add_c_mult: 
  fixes r :: real
  assumes "r > 1"
  shows "summable (\<lambda>n::nat. ((real n + c) * (1/r)^n))" (is "summable ?f")
  apply (subgoal_tac "summable (\<lambda>n::nat. ((real n + c) / (r)^n))")
  apply (subst summable_cong[where g="(\<lambda>n::nat. ((real n + c) / (r)^n))"])
  apply (simp add: power_one_over)
  apply simp
  by (simp add: assms summable_n_r_power_n_add_c)

lemma summable_n_r_power_n_add_c_mult': 
  fixes r :: real
  assumes "r \<ge> 0" "r < 1"
  shows "summable (\<lambda>n::nat. ((real n + c) * r^n))" (is "summable ?f")
proof (cases "r = 0")
  case True
  then show ?thesis by simp
next
  case False
  then show ?thesis 
    apply (subgoal_tac "summable (\<lambda>n::nat. ((real n + c) / (1/r)^n))")
    apply (subst summable_cong[where g="(\<lambda>n::nat. ((real n + c) / (1/r)^n))"])
    apply (simp add: power_one_over)
    apply simp
    apply (subst summable_n_r_power_n_add_c)
    using assms by simp+
qed

(*
lemma choose_2_eq: "real (n * (n-1) div 2) = real (n*(n-1)) / 2"
  apply (induction n)
  apply simp
  by (simp add: real_of_nat_div)

lemma filterlim_at_top_div_const_nat':
  assumes "c > 0"
  shows   "filterlim (\<lambda>x::nat. real (x-b) / c) at_top at_top"
  unfolding filterlim_at_top
proof
  fix C :: nat
  have *: "n div c \<ge> C" if "n \<ge> C * c" for n
    using assms that by (metis div_le_mono div_mult_self_is_m)
  have "eventually (\<lambda>n. n \<ge> C * c) at_top"
    by (rule eventually_ge_at_top)
  thus "eventually (\<lambda>n. real (n-b) / c \<ge> real C) at_top"
    by eventually_elim (use * in auto)
qed

lemma Arithmetico_geometric_sequence_tendsto_0:
  assumes "(p::real) > 0"
  shows "(\<lambda>n. real n / (1+p) ^ (n)) \<longlonglongrightarrow> 0"
proof - 
  (* (1+p)^n \<ge> n * p + 1 *)
  (* (1+p)^n \<ge> 1 + n*(n-1)*p^2 + ... *)
  have f1: "(1+p) ^ n = (\<Sum>k\<le>n. (of_nat (n choose k)) * 1^k * p^(n-k))"
    by (rule Binomial.binomial_ring)
  also have f2: "n \<ge> 2 \<longrightarrow> (1+p) ^ n \<ge> 1 + (real (n*(n-1)) / 2)*p^2"
    apply auto
    apply (simp add: f1)
    proof -
      assume a1: "2 \<le> n"
      have f1: "(\<Sum>k\<le>n. real (n choose k) * p ^ (n - k)) \<ge> (\<Sum>k\<in>{n-2,n}. real (n choose k) * p ^ (n - k))"
        apply (rule sum_mono2)
        apply simp+
        by (meson assms less_eq_real_def mult_nonneg_nonneg of_nat_0_le_iff zero_le_power)
      also have f2: "(\<Sum>k\<in>{n-2,n}. real (n choose k) * p ^ (n - k)) = real (n choose (n-2))*p^2 + real (n choose (n-n))*p^0"
        by (smt (verit, ccfv_threshold) a1 binomial_symmetric diff_diff_cancel diff_is_0_eq diff_self_eq_0 empty_iff finite.intros(1) finite_insert singletonD sum.empty sum.insert zero_neq_numeral)
      also have f3: "... =  (real (n*(n-1)) / 2)*p^2 + 1"
        apply (simp add: a1 binomial_symmetric choose_two)
        using choose_2_eq by simp
      then show "1 + real n * real (n - Suc 0) * p\<^sup>2 / 2 \<le> (\<Sum>k\<le>n. real (n choose k) * p ^ (n - k))"
        using calculation by (smt (verit, best) One_nat_def of_nat_mult times_divide_eq_left)
    qed
  have f_inf0: "LIM n sequentially. (real n) :> at_infinity"
    using tendsto_of_nat by blast
  then have f_inf1: "LIM n sequentially. (real (n-1)) :> at_infinity"
    using filterlim_compose filterlim_minus_const_nat_at_top by blast
  then have f_inf2: "LIM n sequentially. (real (n div 2)) :> at_infinity"
    using filterlim_at_top_div_const_nat filterlim_at_top_imp_at_infinity filterlim_sequentially_iff_filterlim_real pos2 by blast

  have ff: "\<forall>n > 0. ((real (n * (n - 1)) / 2) * p\<^sup>2) / real n = ((real (n - 1) / 2) * p\<^sup>2)"
    by auto
  have "\<forall>n > 0. ((real (n - 1) / 2) * p\<^sup>2) = ((real (n - 1)) * (p\<^sup>2 / 2))"
    by simp
  have "\<forall>n > 0. ((real (n - 1)) * (p\<^sup>2 / 2)) = (real n) * (p\<^sup>2 / 2) - (p\<^sup>2 / 2)"
    apply auto
    by (smt (verit) Suc_pred left_diff_distrib mult_cancel_right1 of_nat_1 of_nat_add plus_1_eq_Suc)

  have "LIM n sequentially. ((real (n - 1)) * (p\<^sup>2 / 2)) :> at_infinity"
    using f_inf0 f_inf1 

  have f3: "(\<lambda>n. 1 / ((1 + real ((n)*(n-1) div 2)*p^2) / real n)) \<longlonglongrightarrow> 0 "
    apply (rule tendsto_divide_0[where c="1"])
    apply auto[1]
    sledgehammer
  show ?thesis
    sorry
qed

text \<open> Arithmetico-geometric sequence or Gabriel's staircase \<close>
(* I tried to prove this based on the usual strategy to calculate 
  S1(n) = n * r^n
  S2(n) =( n * r^n) * r
Then define a new sequence by S1(n) - Sn(1). 
*)
lemma  
  fixes r :: real
  assumes "r \<ge> 0" "r < 1" 
  shows "(\<Sum>\<^sub>\<infinity>n::nat. (real n) * r^n) = r / (1-r)^2"
proof -
  let ?f = "(\<lambda>n::nat. (real n) * r^n)"
  let ?f_r = "(\<lambda>n::nat. ((real n) * r^n) * r)"
  let ?f_1_r = "(\<lambda>n::nat. ((real n) * r^n) * (1-r))"
  have summable_f: "summable ?f"
    by (simp add: assms(1) assms(2) summable_n_r_power_n_mult)
  obtain l where P_l: "?f sums l"
    using summable_f by blast

  have f1: "(?f_r) sums (l * r)"
    apply (subst sums_mult2)
    by (simp add: P_l)+

  have f2: "(?f_1_r) sums (l * (1-r))"
    apply (subst sums_mult2)
    by (simp add: P_l)+

  (* n: ?f 0 - ?f_r 0 + ?f 1 - ?f_r 1 + ... + ?f (n-1) - ?f_r (n-1) *)
  (* n: ?f 0 - ?f_r 0 + r^1 - 1*r^2 + 2*r^2 - 2*r^3 ... + ?f (n-1) - ?f_r (n-1) *)
  (* n: r^1 + r^2 + r^3 + ... + r^n - (n)*r^(n+1) *)
  have f3: "\<forall>n. (\<Sum>i\<le>n. (?f i - ?f_r i)) = (\<Sum>i\<le>n. r^i) - 1 - (real n) * r ^ (n+1)"
    apply (auto)
    apply (induct_tac "n")
    apply simp
    proof -
      fix n na::"nat"
      assume a1: "(\<Sum>i\<le>na. ?f i - ?f_r i) = sum ((^) r) {..na} - 1 - real na * (r * r ^ na)"

      have f1: "(\<Sum>i \<in> ({0..na}). ?f i - ?f_r i) = (\<Sum>i \<in> ({0..Suc na} - {Suc na}). ?f i - ?f_r i)"
        by (simp add: atLeast0_atMost_Suc)

      have f2: "(\<Sum>i \<in> ({0..na}). ?f i - ?f_r i) = (\<Sum>i \<le> na. ?f i - ?f_r i)"
        using atLeast0AtMost by presburger

      have f3: "(\<Sum>i \<in> ({0..Suc na} - {Suc na}). ?f i - ?f_r i) = 
            (\<Sum>i\<le>Suc na. ?f i - ?f_r i) - (real (na+1) * r ^ (na+1) - real (na+1) * r ^ (na+1) * r)"
        apply (subst sum_diff1)
        apply blast
        apply auto
        using atLeast0AtMost by presburger

      from f1 have f4: "(\<Sum>i\<le>Suc na. ?f i - ?f_r i) = 
          (\<Sum>i \<le> na. ?f i - ?f_r i) + (real (na+1) * r ^ (na+1) - real (na+1) * r ^ (na+1) * r)"
        using f3 f1 f2 by linarith

      have f5: "... = sum ((^) r) {..na} - 1 - real na * (r * r ^ na) + (real (na+1) * r ^ (na+1) - real (na+1) * r ^ (na+1) * r)"
        using f4 a1 by presburger 

      have f6: "... = sum ((^) r) {..na} - 1 - (real na * (r ^ (na+1)) - real (na+1) * r ^ (na+1)) - real (na+1) * r ^ (na+1) * r"
        using f5 by simp

      have f7: "... = sum ((^) r) {..na} - 1 + (real (na+1) * r ^ (na+1) - real na * (r ^ (na+1)) ) - real (na+1) * r ^ (na+1) * r"
        by linarith
      
      have f8: "... = sum ((^) r) {..na} - 1 + r ^ (na+1) - real (na+1) * r ^ (na+1) * r"
      proof -
        have "\<forall>n. 1 = real (Suc n) - real n"
          by simp
        then show ?thesis
          by (metis (no_types) Rings.ring_distribs(3) Suc_eq_plus1 mult.left_neutral)
      qed

      have f9: "... = sum ((^) r) {..na+1} - 1 - real (na+1) * r ^ (na+1) * r"
        by force

      show "(\<Sum>i\<le>Suc na. ?f i - ?f_r i) = sum ((^) r) {..Suc na} - 1 - real (Suc na) * (r * r ^ Suc na)"
        using f5 f8 by auto
    qed

  have f3': "\<forall>l. ((\<lambda>n. \<Sum>i\<le>n. (?f i - ?f_r i)) \<longlonglongrightarrow> l) = ((\<lambda>n. ((\<Sum>i\<le>n. r^i) - 1 - (real n) * r ^ (n+1))) \<longlonglongrightarrow> l)"
      apply (rule allI)
      by (simp add: f3)

  have f4: "\<forall>l. (\<lambda>n. (?f n - ?f_r n)) sums l = (\<lambda>n. \<Sum>i\<le>n. (?f i - ?f_r i)) \<longlonglongrightarrow> l"
    apply (rule allI)
    by (rule sums_def_le)

  have f5: "\<forall>l. (\<lambda>n. (?f n - ?f_r n)) sums l = (\<lambda>n. (\<Sum>i\<le>n. r^i) - 1 - (real n) * r ^ (n+1)) \<longlonglongrightarrow> l"
    apply (rule allI)
    by (simp add: f4 f3')

  have "(\<lambda>n. (\<Sum>i\<le>n. r^i) + (-1) + (-(real n) * r ^ (n+1))) \<longlonglongrightarrow> (1/(1-r)) + (-1) + 0"
    apply (rule tendsto_add)
    apply (rule tendsto_add)
    apply (metis abs_of_nonneg assms(1) assms(2) geometric_sums real_norm_def sums_def_le)
    apply simp
    using Arithmetico_geometric_sequence_tendsto_0 sledgehammer
    (* "let r = 1 + p" 
       (1+p)^n \<ge> 1 + C(n, 2)*p^2
    *)
    term "n / (1+p)^n \<le> n / (1 + C(n,2)*p^2)"

  have "suminf (\<lambda>n. (?f n - ?f_r n)) = suminf (\<lambda>n. (\<Sum>i\<le>n. r^i) - 1 - n * r ^ (n+1))"
    using f5 sums_unique sledgehammer

    apply (simp add: suminf_eq_lim)
    apply (simp add: sums_def_le)
  have "(\<lambda>n. (?f n - ?f_r n)) sums l"
  show ?thesis
    sorry
*)

lemma infsum_Suc_iff:
  fixes r :: "real" and f::"nat \<Rightarrow> real"
  assumes r_0_1: "r \<ge> 0" "r < 1"
  assumes f_nonneg: "\<forall>n. f n \<ge> 0"
  assumes f_summable: "summable f"
  shows "(\<Sum>\<^sub>\<infinity>n::nat. f (n)) = (\<Sum>\<^sub>\<infinity>n::nat. f (Suc n)) + f 0" (is "infsum ?f UNIV = ?g")
  apply (subst infsetsum_infsum[symmetric])
  apply (simp add: abs_summable_on_nat_iff' f_nonneg f_summable summable_Suc_iff)
  apply (subst infsetsum_infsum[symmetric])
  apply (simp add: abs_summable_on_nat_iff' f_nonneg f_summable summable_Suc_iff)
  apply (subst infsetsum_nat)
  apply (simp add: abs_summable_on_nat_iff' f_nonneg f_summable summable_Suc_iff)
  apply (subst infsetsum_nat)
  apply (simp add: abs_summable_on_nat_iff' f_nonneg f_summable summable_Suc_iff)
  apply (simp add: suminf_def)
  apply (simp add: sums_Suc_iff)
  by (smt (z3) f_summable summable_sums_iff sums_unique theI_unique)

lemma infsum_geometric:
  assumes "r > 0" "(r::real) < 1"
  shows "(\<Sum>\<^sub>\<infinity>n. r ^ n) = 1 / (1 - r)"
  apply (subst infsumI[where x = "1/(1-r)"])
  apply (rule norm_summable_imp_has_sum)
  using assms(1) assms(2) apply force
  apply (simp add: assms(1) assms(2) geometric_sums less_eq_real_def)
  by auto

lemma infsum_geometric_cmult_right:
  assumes "r > 0" "(r::real) < 1"
  shows "(\<Sum>\<^sub>\<infinity>n. c * r ^ n) = c / (1 - r)"
  apply (subst infsum_cmult_right)
  using assms(1) assms(2) summable_on_UNIV_nonneg_real_iff apply auto[1]
  by (simp add: assms infsum_geometric) 

lemma infsum_geometric_cmult_left:
  assumes "r > 0" "(r::real) < 1"
  shows "(\<Sum>\<^sub>\<infinity>n. r ^ n * c) = c / (1 - r)"
  apply (subst infsum_cmult_left)
  using assms(1) assms(2) summable_on_UNIV_nonneg_real_iff apply auto[1]
  by (simp add: assms infsum_geometric) 

lemma arithmetico_geometric_seq_sum:
  fixes r :: real
  assumes "r \<ge> 0" "r < 1" 
  shows "(\<Sum>\<^sub>\<infinity>n::nat. (real n) * r^n) = r / (1-r)^2" (is "infsum ?f UNIV = _")
proof -
  (* have f_summable_on: "?f summable_on UNIV"
    apply (rule norm_summable_imp_summable_on)
    apply (simp add: assms)
    by (simp add: assms(1) assms(2) summable_n_r_power_n_mult)
  *)
  obtain l where P_l: "infsum ?f UNIV = l"
    using summable_on_n_r_power_n_mult by blast

  have f_suc_n_by_Suc_iff: "infsum (\<lambda>n. ?f (Suc n)) UNIV = infsum ?f UNIV - ?f 0"
    apply (subst infsum_Suc_iff[where r = "r" and f = "?f"])
    apply (simp add: assms)+
    apply (simp add: assms(1) assms(2) summable_n_r_power_n_mult)
    by linarith

  then have f_suc_n_eq_l: "infsum (\<lambda>n. ?f (Suc n)) UNIV = l"
    using P_l by simp

  have f_suc_n_by_expand: "infsum (\<lambda>n. ?f (Suc n)) UNIV = infsum (\<lambda>n. r * (real n * r ^ n) + (r * r^n)) UNIV"
    by (metis (no_types, opaque_lifting) add.commute distrib_left mult.assoc mult.commute mult.right_neutral of_nat_Suc power_Suc)
  also have f_suc_n_by_expand': "... = r*l + r/(1-r)"
    apply (subst infsum_add)
    apply (rule summable_on_cmult_right)
    apply (simp add: assms summable_on_n_r_power_n_mult)
    apply (rule summable_on_cmult_right)
    apply (simp add: assms(1) assms(2) summable_on_UNIV_nonneg_real_iff)
    apply (subst infsum_cmult_right)
    using assms(1) assms(2) summable_on_n_r_power_n_mult apply blast
    apply (subst infsum_cmult_right)
    apply (simp add: assms(1) assms(2) summable_on_UNIV_nonneg_real_iff)
    apply (simp add: P_l)
    apply (subst infsumI[where x = "1/(1-r)"])
    apply (rule norm_summable_imp_has_sum)
    using assms(1) assms(2) apply force
    apply (simp add: assms(1) assms(2) geometric_sums)
    by auto

  from f_suc_n_by_expand' and f_suc_n_eq_l have f_suc_eq: "l = r*l + r/(1-r)"
    using f_suc_n_by_expand by presburger
  then have "(1-r)*l = r/(1-r)"
    by (simp add: vector_space_over_itself.scale_left_diff_distrib)
  ultimately have "l = r/(1-r)^2"
    by (smt (verit, del_insts) Suc_1 assms(2) divide_divide_eq_left' nonzero_mult_div_cancel_left power_Suc power_one_right)

  then show ?thesis
    using P_l by blast
qed

lemma arithmetico_geometric_seq_sum_offset_const:
  fixes r :: real
  assumes "r > 0" "r < 1" 
  shows "(\<Sum>\<^sub>\<infinity>n::nat. (real n + c) * r^n) = r / (1-r)^2 + c/(1-r)" (is "infsum ?f UNIV = _")
  apply (simp add: Rings.ring_class.ring_distribs(2))
  apply (subst infsum_add)
  apply (simp add: assms(1) assms(2) less_eq_real_def summable_on_n_r_power_n_mult)
  apply (simp add: assms(1) assms(2) less_eq_real_def summable_on_UNIV_nonneg_real_iff summable_on_cmult_right)
  apply (simp add: assms less_eq_real_def arithmetico_geometric_seq_sum)
  apply (subst infsum_cmult_right)
  apply (simp add: assms(1) assms(2) less_eq_real_def summable_on_UNIV_nonneg_real_iff)
  by (simp add: assms(1) assms(2) infsum_geometric)

end
