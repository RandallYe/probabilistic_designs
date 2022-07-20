section \<open> Probabilistic relation programming example 1 \<close>

theory utp_prob_rel_loop
  imports 
    (* "HOL-Analysis.Infinite_Set_Sum" *)
    "../utp_prob_rel_laws" 
begin 

unbundle UTP_Syntax

declare [[show_types]]

subsection \<open> Single coin \<close>

datatype Tcoin = chead | ctail
alphabet coin_state = time +
  coin :: Tcoin

thm "coin_state.simps"
definition flip:: "coin_state phrel" where
"flip = (prel_of_rfrel (coin \<^bold>\<U> {chead, ctail}))"

definition flip_loop where
"flip_loop = repeat flip until (coin\<^sup>< = chead)\<^sub>e"

(*
definition H:: "coin_state \<times> coin_state \<Rightarrow> \<real>" where 
"H = (\<lbrakk>coin\<^sup>> = chead \<and> $t\<^sup>> \<ge> $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1/2)^(the_enat ($t\<^sup>> - $t\<^sup>< - 1)) * (1/2))\<^sub>e"
*)

definition H:: "coin_state \<times> coin_state \<Rightarrow> \<real>" where 
"H = (\<lbrakk>coin\<^sup>> = chead \<and> $t\<^sup>> \<ge> $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1/2)^(($t\<^sup>> - $t\<^sup>< - 1)) * (1/2))\<^sub>e"

(* 
\<lbrakk>coin\<^sup>> \<in> {chead, ctail}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>$t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 2 ; (if\<^sub>c \<lbrakk>($coin\<^sup>< = chead)\<^sub>e\<rbrakk> then II else (prel_of_rfrel H))
= 
\<lbrakk>coin\<^sup>> \<in> {chead, ctail}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>$t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 2 ; (\<lbrakk>$coin\<^sup>< = chead\<rbrakk>\<^sub>\<I>\<^sub>e * II + \<lbrakk>$coin\<^sup>< \<noteq> chead\<rbrakk>\<^sub>\<I>\<^sub>e * H)
= 
\<Sum>\<^sub>\<infinity> v\<^sub>0. (\<lbrakk>coin\<^sub>0 \<in> {chead, ctail}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sub>0 = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 2) * 
          (\<lbrakk>coin\<^sub>0 = chead\<rbrakk>\<^sub>\<I>\<^sub>e*\<lbrakk>v' = v\<^sub>0\<rbrakk>\<^sub>\<I>\<^sub>e + \<lbrakk>coin\<^sub>0 \<noteq> chead\<rbrakk>\<^sub>\<I>\<^sub>e * H) 
=
\<Sum>\<^sub>\<infinity> v\<^sub>0. (\<lbrakk>coin\<^sub>0 \<in> {chead, ctail}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sub>0 = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 2) * \<lbrakk>coin\<^sub>0 = chead\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>v' = v\<^sub>0\<rbrakk>\<^sub>\<I>\<^sub>e + 
\<Sum>\<^sub>\<infinity> v\<^sub>0. (\<lbrakk>coin\<^sub>0 \<in> {chead, ctail}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sub>0 = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 2) * \<lbrakk>coin\<^sub>0 \<noteq> chead\<rbrakk>\<^sub>\<I>\<^sub>e * H 
= 
\<Sum>\<^sub>\<infinity> v\<^sub>0. (\<lbrakk>coin\<^sub>0 = chead\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sub>0 = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 2) * \<lbrakk>coin' = chead\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t' = t\<^sub>0\<rbrakk>\<^sub>\<I>\<^sub>e + 
\<Sum>\<^sub>\<infinity> v\<^sub>0. (\<lbrakk>coin\<^sub>0 = ctail\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sub>0 = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 2) * H
=
\<lbrakk>t' = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>coin' = chead\<rbrakk>\<^sub>\<I>\<^sub>e / 2 +
\<Sum>\<^sub>\<infinity> v\<^sub>0. \<lbrakk>t\<^sub>0 = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>coin\<^sub>0 = ctail\<rbrakk>\<^sub>\<I>\<^sub>e / 2 * \<lbrakk>coin' = chead \<and> t' \<ge> t\<^sub>0 + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1/2)^(t' - t\<^sub>0 - 1) * (1/2)
=
\<lbrakk>t' = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>coin' = chead\<rbrakk>\<^sub>\<I>\<^sub>e / 2 +
\<lbrakk>coin' = chead\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t' \<ge> t + 1 + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1/2)^(t' - (t+1) - 1) * (1/2) / 2
=
\<lbrakk>t' = t + 1\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>coin' = chead\<rbrakk>\<^sub>\<I>\<^sub>e / 2 +
\<lbrakk>coin' = chead\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t' \<ge> t + 2\<rbrakk>\<^sub>\<I>\<^sub>e * (1/2)^(t' - t - 2) * (1/2) / 2
= 
\<lbrakk>coin' = chead\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t' \<ge> t + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1/2)^(t'- t - 1) * (1/2)
*)
definition f :: "\<nat> \<Rightarrow> coin_state"
  where "f = (\<lambda>t. \<lparr>t\<^sub>v = t, coin\<^sub>v = chead\<rparr>)"

lemma H_simp: "H = (\<lambda>\<s>::coin_state \<times> coin_state.
        (if coin\<^sub>v (snd \<s>) = chead \<and> Suc (t\<^sub>v (fst \<s>)) \<le> t\<^sub>v (snd \<s>) then 1::\<real> else (0::\<real>)) *
        ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v (snd \<s>) - Suc (t\<^sub>v (fst \<s>))) /
        (2::\<real>))"
  apply (simp add: H_def)
  by (simp add: expr_defs rel lens_defs)
  
lemma H_is_dist: "is_final_distribution H"
  apply (simp add: dist_defs H_def)
  apply (simp add: expr_defs)
  apply (auto)
  apply (smt (verit, best) field_sum_of_halves power_le_one)
  apply (simp add: lens_defs)
proof -
  fix s\<^sub>1::"coin_state"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>s::coin_state.
          (if coin\<^sub>v s = chead \<and> Suc (t\<^sub>v s\<^sub>1) \<le> t\<^sub>v s then 1::\<real> else (0::\<real>)) *
          ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - Suc (t\<^sub>v s\<^sub>1)) / (2::\<real>))"
  let ?set = "{s::coin_state. coin\<^sub>v s = chead \<and> Suc (t\<^sub>v s\<^sub>1) \<le> t\<^sub>v s}"

  (*
  thm "infsum_reindex"
  have "(\<Sum>\<^sub>\<infinity>t::nat \<in> {t. t \<ge> Suc (t\<^sub>v s\<^sub>1)}. ((1::\<real>) / (2::\<real>)) ^ (t - Suc (t\<^sub>v s\<^sub>1) + 1)) = 1"
    apply (subst infsum_reindex[where h = "\<lambda>s::coin_state. t\<^sub>v s" and A = "?set"])
*)
  have f1: "?lhs = (\<Sum>\<^sub>\<infinity>s::coin_state \<in> ?set \<union> -?set.
          (if coin\<^sub>v s = chead \<and> Suc (t\<^sub>v s\<^sub>1) \<le> t\<^sub>v s then 1::\<real> else (0::\<real>)) *
          ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - Suc (t\<^sub>v s\<^sub>1)) / (2::\<real>))"
    by auto
  moreover have "... = (\<Sum>\<^sub>\<infinity>s::coin_state \<in> ?set.
          (if coin\<^sub>v s = chead \<and> Suc (t\<^sub>v s\<^sub>1) \<le> t\<^sub>v s then 1::\<real> else (0::\<real>)) *
          ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - Suc (t\<^sub>v s\<^sub>1)) / (2::\<real>))"
    apply (rule infsum_cong_neutral)
    apply force
    apply simp
    by blast
  moreover have "... = (\<Sum>\<^sub>\<infinity>s::coin_state \<in> ?set. ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - Suc (t\<^sub>v s\<^sub>1)) / (2::\<real>))"
    by (smt (verit) infsum_cong mem_Collect_eq mult_cancel_right2)
  moreover have "... = (\<Sum>\<^sub>\<infinity>s::coin_state \<in> ?set. ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v s - Suc (t\<^sub>v s\<^sub>1) + 1))"
    by auto
  moreover have "... = (\<Sum>\<^sub>\<infinity>t::nat \<in> {t. t \<ge> Suc (t\<^sub>v s\<^sub>1)}. ((1::\<real>) / (2::\<real>)) ^ (t - Suc (t\<^sub>v s\<^sub>1) + 1))"
    apply (subst infsum_reindex_bij_betw[symmetric, where g = "\<lambda>s::coin_state. t\<^sub>v s" and A = "?set"])
    apply (simp add: bij_betw_def)
    apply (rule conjI)
    apply (simp add: inj_on_def)
    apply auto
    apply (simp add: image_def)
    apply (rule_tac x = "\<lparr>t\<^sub>v = x, coin\<^sub>v = chead\<rparr>" in exI)
    by simp
  moreover have "... = (\<Sum>\<^sub>\<infinity>t::nat. ((1::\<real>) / (2::\<real>)) ^ (t + 1))"
    apply (subst infsum_reindex_bij_betw[symmetric, where g = "\<lambda>n. n + Suc (t\<^sub>v s\<^sub>1)" and A = "UNIV"])
    apply auto
    apply (simp add: bij_betw_def)
    apply (rule conjI)
    apply (simp add: inj_on_def)
    apply (simp add: image_def)
    apply (auto)
    by (simp add: add.commute le_iff_add)
  moreover have "... = 1"
    (* Intend to prove it as follows.
      Use "HOL-Analysis.Infinite_Set_Sum.infsetsum_infsum" 
          to turn infsum to infsetsum
      also use HOL-Analysis.Infinite_Set_Sum.abs_summable_equivalent
          to establish HOL-Analysis.Infinite_Set_Sum.abs_summable_on = abs_summable_on
      Use "HOL-Analysis.Infinite_Set_Sum.infsetsum_nat"
          to turn infsetsum to sums over series suminf
      Use "HOL.Series.suminf_geometric"
          to calculate geometric progression
    *)
    sorry
  ultimately show "?lhs = (1::\<real>)"
    by presburger
qed

definition flip_body_alt :: "coin_state \<times> coin_state \<Rightarrow> \<real>" where
"flip_body_alt \<equiv> (\<lbrakk>coin\<^sup>> \<in> {chead, ctail} \<and> $t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 2)\<^sub>e"

lemma flip_body: 
  "flip ; (t := $t + 1) = prel_of_rfrel flip_body_alt"
  apply (simp add: flip_def flip_body_alt_def)
  apply (simp add: prel_uniform_dist_left)
  apply (simp add: prel_defs)
  apply (simp add: prel_set_conv_assign)
  apply (expr_auto add: rel)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (simp add: fun_eq_iff)
  apply (rule allI)+
  apply (auto)
  by (metis Tcoin.distinct(2) coin_state.ext_inject coin_state.surjective coin_state.update_convs(1) 
      time.ext_inject time.update_convs(1))

lemma flip_body_set_eq: 
  "\<forall>s\<^sub>1. {s::coin_state. (coin\<^sub>v s = chead \<or> coin\<^sub>v s = ctail) \<and> t\<^sub>v s = Suc (t\<^sub>v s\<^sub>1)} = 
  {\<lparr>t\<^sub>v = Suc (t\<^sub>v s\<^sub>1), coin\<^sub>v = chead\<rparr>, \<lparr>t\<^sub>v = Suc (t\<^sub>v s\<^sub>1), coin\<^sub>v = ctail\<rparr>}"
  by (auto)

lemma flip_body_is_dist: "is_final_distribution flip_body_alt"
  apply (simp add: dist_defs flip_body_alt_def)
  apply (simp add: expr_defs)
  apply (auto)
  apply (simp add: lens_defs)
  apply (subst infsum_cdiv_left)
  apply (rule infsum_constant_finite_states_summable)
  using flip_body_set_eq apply (metis finite.simps)
  apply (subst infsum_constant_finite_states)
  using flip_body_set_eq apply (metis finite.simps)
  using flip_body_set_eq 
  by (smt (verit, best) Collect_cong One_nat_def Suc_1 Tcoin.distinct(1) card.empty card.insert 
      coin_state.ext_inject field_sum_of_halves finite.emptyI finite.insertI insert_absorb 
      insert_not_empty of_nat_1 of_nat_add one_add_one singletonD time.ext_inject)

(* Fixed-point X: 
    repeat_body flip ((pre \<lbrakk>($coin\<^sup>< = chead)\<^sub>e\<rbrakk>\<^sub>u)\<^sup>\<Up>) X = X
needs to establish below. 

  repeat_body flip ((pre \<lbrakk>($coin\<^sup>< = chead)\<^sub>e\<rbrakk>\<^sub>u)\<^sup>\<Up>) X = X
=   (repeat_body_defs)
  flip ; (t := $t + 1) ; (if\<^sub>c ((pre \<lbrakk>($coin\<^sup>< = chead)\<^sub>e\<rbrakk>\<^sub>u)\<^sup>\<Up>) then II else X) = X
=   (flip_body)
  \<lbrakk>coin' \<in> {chead, ctail} \<and> $t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 2 ; (if\<^sub>c ((pre \<lbrakk>($coin\<^sup>< = chead)\<^sub>e\<rbrakk>\<^sub>u)\<^sup>\<Up>) then II else X) = X
=   (pcond_pchoice_eq and pchoice definition)
  \<lbrakk>coin' \<in> {chead, ctail} \<and> $t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 2 ; (\<lbrakk>coin = chead\<rbrakk>\<^sub>\<I> * \<lbrakk>v'=v\<rbrakk>\<^sub>\<I> + \<lbrakk>coin = ctail\<rbrakk>\<^sub>\<I> * X) = X
=   (Iverson bracket disjunction)
  (\<lbrakk>coin' = chead\<rbrakk>\<^sub>\<I> * \<lbrakk>t' = t + 1\<rbrakk>\<^sub>\<I> / 2 + \<lbrakk>coin' = ctail\<rbrakk>\<^sub>\<I> * \<lbrakk>t' = t + 1\<rbrakk>\<^sub>\<I> / 2) ; 
    (\<lbrakk>coin = chead\<rbrakk>\<^sub>\<I> * \<lbrakk>v'=v\<rbrakk>\<^sub>\<I> + \<lbrakk>coin = ctail\<rbrakk>\<^sub>\<I> * X) = X
=   (sequential composition)
  (\<Sum>\<^sub>\<infinity> v\<^sub>0. (\<lbrakk>coin\<^sub>0 = chead\<rbrakk>\<^sub>\<I> * \<lbrakk>t\<^sub>0 = t + 1\<rbrakk>\<^sub>\<I> / 2 + \<lbrakk>coin\<^sub>0 = ctail\<rbrakk>\<^sub>\<I> * \<lbrakk>t\<^sub>0 = t + 1\<rbrakk>\<^sub>\<I> / 2) *
          (\<lbrakk>coin\<^sub>0 = chead\<rbrakk>\<^sub>\<I> * \<lbrakk>v' = v\<^sub>0\<rbrakk>\<^sub>\<I> + \<lbrakk>coin\<^sub>0 = ctail\<rbrakk>\<^sub>\<I> * X[v\<^sub>0/v]))
    = X
=   (times distribution)
  (\<Sum>\<^sub>\<infinity> v\<^sub>0. (\<lbrakk>coin\<^sub>0 = chead\<rbrakk>\<^sub>\<I> * \<lbrakk>t\<^sub>0 = t + 1\<rbrakk>\<^sub>\<I> * \<lbrakk>coin' = chead\<rbrakk>\<^sub>\<I> * \<lbrakk>t' = t + 1\<rbrakk>\<^sub>\<I> / 2 + 
           \<lbrakk>coin\<^sub>0 = ctail\<rbrakk>\<^sub>\<I> * \<lbrakk>t\<^sub>0 = t + 1\<rbrakk>\<^sub>\<I> * X[ctail/coin,t+1/t] / 2)) = X
=
  (\<Sum>\<^sub>\<infinity> v\<^sub>0. \<lbrakk>coin\<^sub>0 = chead\<rbrakk>\<^sub>\<I> * \<lbrakk>t\<^sub>0 = t + 1\<rbrakk>\<^sub>\<I> * \<lbrakk>coin' = chead\<rbrakk>\<^sub>\<I> * \<lbrakk>t' = t + 1\<rbrakk>\<^sub>\<I> / 2) + 
  (\<Sum>\<^sub>\<infinity> v\<^sub>0. \<lbrakk>coin\<^sub>0 = ctail\<rbrakk>\<^sub>\<I> * \<lbrakk>t\<^sub>0 = t + 1\<rbrakk>\<^sub>\<I> * X[ctail/coin,t+1/t] / 2) = X
=
  \<lbrakk>coin' = chead\<rbrakk>\<^sub>\<I> * \<lbrakk>t' = t + 1\<rbrakk>\<^sub>\<I> / 2 + X[ctail/coin,t+1/t] / 2 = X
=
  \<lbrakk>coin' = chead\<rbrakk>\<^sub>\<I> * \<lbrakk>t' = t + 1\<rbrakk>\<^sub>\<I> + X[ctail/coin,t+1/t] = X * 2
=
  X * 2 - X[ctail/coin,t+1/t]  =  \<lbrakk>coin' = chead\<rbrakk>\<^sub>\<I> * \<lbrakk>t' = t + 1\<rbrakk>\<^sub>\<I>

As a fixed point, X shall satisfy the equation above.
*)

(*
H: Satisfy this invariant
  
  H * 2 - H[ctail/coin,t+1/t]
=   (H = \<lbrakk>coin' = chead\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t' \<ge> t + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1/2)^(t'- t - 1) * (1/2))
  \<lbrakk>coin' = chead \<and> t' \<ge> t + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1/2)^(t' - t - 1) * (1/2) * 2 - \<lbrakk>coin' = chead \<and> t' \<ge> t + 1 + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1/2)^(t' - t - 2) * (1/2)
=
  \<lbrakk>coin' = chead \<and> t' \<ge> t + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1/2)^(t' - t - 1) - \<lbrakk>coin' = chead \<and> t' \<ge> t + 1 + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1/2)^(t' - t - 1)
=
  \<lbrakk>coin' = chead\<rbrakk>\<^sub>\<I> * ( \<lbrakk>t' \<ge> t + 1\<rbrakk>\<^sub>\<I> - \<lbrakk>t' \<ge> t + 2\<rbrakk>\<^sub>\<I>) * (1/2)^(t' - t - 1)
=
  \<lbrakk>coin' = chead\<rbrakk>\<^sub>\<I> * (\<lbrakk>t' \<ge> t + 2 \<or> t' = t + 1\<rbrakk>\<^sub>\<I> - \<lbrakk>t' \<ge> t + 2\<rbrakk>\<^sub>\<I>) * (1/2)^(t' - t - 1)
=   (disjunction of Iverson bracket)
  \<lbrakk>coin' = chead\<rbrakk>\<^sub>\<I> * (\<lbrakk>t' = t + 1\<rbrakk>\<^sub>\<I>) * (1/2)^(t' - t - 1)
=   (t' = t + 1)
  \<lbrakk>coin' = chead\<rbrakk>\<^sub>\<I> * (\<lbrakk>t' = t + 1\<rbrakk>\<^sub>\<I>)
*)

(* Actually, H is the unique solution?
 
  " X * 2 - X[ctail/coin,t+1/t]  =  \<lbrakk>coin' = chead\<rbrakk>\<^sub>\<I> * \<lbrakk>t' = t + 1\<rbrakk>\<^sub>\<I> " \<Longrightarrow> X = H

\<forall>s. 
X(s, s')*2 - X(s[coin := ctail, t := t+1], s') = s(coin := chead, t := t+1)
= 
X(s, s')*2 - X(s[coin := ctail, t := t+1], s')  = H(s, s')*2 - H(s[coin := ctail, t := t+1], s')
= 
(X(s, s') - H(s, s')) * 2 = X(s[coin := ctail, t := t+1], s') - H(s[coin := ctail, t := t+1], s')


\<forall>t. 
X(t, t')*2 - X(s[coin := ctail, t := t+1], s') = s[coin := chead, t := t+1]

t' = t+1
X(t, t+1)*2 - X([ctail, t+1], t+1) = [c' = h]

t' > t + 1
X(t, > t+1)*2 = X([ctail, t+1], > t+1)
*)
print_locale "complete_lattice"

(*
interpretation unit_interval_lattice: 
  complete_lattice "Min" "Max" "(min)" "(\<le>)" "(<)" "(max)" "1::\<real>" "0::\<real>"
  apply unfold_locales
  apply simp+
  apply (simp add: Min_def)
  sorry
*)

thm "le_fun_def"
term "(\<nu> X \<bullet> ((P \<Zcomp> X) \<^bold>\<lhd> b \<^bold>\<rhd> II))"
term "while b do P od"
thm "while_top_def"
term "lfp (\<lambda>X. ((P \<Zcomp> X) \<^bold>\<lhd> b \<^bold>\<rhd> II))"
term "complete_lattice.lfp"
term "lfp"
term "complete_lattice.lfp (\<lambda>X. (if b then P;X else II))"
term "lfp (\<lambda>X. (if b then P;X else II))"
term "complete_lattice.lfp (\<lambda>X. (if\<^sub>c b then (P ; (t := $t + 1) ; X) else II))"
(*
definition pmin:: "('a, 'b) rfrel \<Rightarrow> ('a, 'b) rfrel \<Rightarrow> ('a, 'b) rfrel" where
"pmin P Q = (if (\<forall>s. P s \<le> Q s) then P else Q)"

definition pmax:: "('a, 'b) rfrel \<Rightarrow> ('a, 'b) rfrel \<Rightarrow> ('a, 'b) rfrel" where
"pmax P Q = (if (\<forall>s. P s \<le> Q s) then Q else P)"

interpretation prob_unit_interval_lattice: 
  complete_lattice "Min" "Max" "(pmin)" "(\<le>)" "(<)" "(pmax)" "(\<lambda>s. 0::\<real>)" "(\<lambda>s. 1::\<real>)"
  apply unfold_locales
  apply simp+
  apply (simp add: Min_def)
  sorry
*)

text \<open>So @{term "H"} is an invariant or fix-point of the loop body function over flip and a condition
if the outcome of flip is head. \<close>
lemma H_is_inv: "repeat_body flip ((pre \<lbrakk>($coin\<^sup>< = chead)\<^sub>e\<rbrakk>\<^sub>u)\<^sup>\<Up>) (prel_of_rfrel H) = (prel_of_rfrel H)"
  apply (simp only: repeat_body_def)
  apply (subst flip_body)
  apply (simp add: pcond_def)
  apply (subst prel_of_rfrel_inverse)
  using H_is_dist apply fastforce
  apply (simp add: pseqcomp_def)
  apply (subst prel_of_rfrel_inverse)
  using flip_body_is_dist apply fastforce
  apply (subst prel_of_rfrel_inverse)
  apply (simp add: H_is_dist prel_is_dist prel_is_dist_pcond)
  apply (simp add: flip_body_alt_def)
  apply (simp only: H_simp)
  apply (simp only: pskip_def)
  apply (simp only: prel_set_conv_skip pred_pre)
  apply (simp only: pskip\<^sub>_f_simp)
  apply (expr_auto add: rel)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (subst fun_eq_iff, rule allI)
proof -
  fix x::"coin_state \<times> coin_state"
  let ?f = "\<lambda>v\<^sub>0::coin_state. 
      ((if (coin\<^sub>v v\<^sub>0 = chead \<or> coin\<^sub>v v\<^sub>0 = ctail) \<and> t\<^sub>v v\<^sub>0 = Suc (t\<^sub>v (fst x)) then 1::\<real> else (0::\<real>)) *
      (if coin\<^sub>v v\<^sub>0 = chead then 
            if v\<^sub>0 = snd x then 1::\<real> else (0::\<real>)
       else 
            (if coin\<^sub>v (snd (v\<^sub>0, snd x)) = chead \<and> Suc (t\<^sub>v (fst (v\<^sub>0, snd x))) \<le> t\<^sub>v (snd (v\<^sub>0, snd x))
                 then 1::\<real> else (0::\<real>)) *
                ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v (snd (v\<^sub>0, snd x)) - Suc (t\<^sub>v (fst (v\<^sub>0, snd x)))) / (2::\<real>)
      ) / (2::\<real>))"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_state. ?f v\<^sub>0)"
  let ?rhs = "(if coin\<^sub>v (snd x) = chead \<and> Suc (t\<^sub>v (fst x)) \<le> t\<^sub>v (snd x) then 1::\<real> else (0::\<real>)) *
       ((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v (snd x) - Suc (t\<^sub>v (fst x))) / (2::\<real>)"
  have set_eq: "{v\<^sub>0::coin_state. t\<^sub>v v\<^sub>0 = Suc (t\<^sub>v (fst x))} = 
        {\<lparr>t\<^sub>v = Suc (t\<^sub>v (fst x)), coin\<^sub>v = chead\<rparr>, \<lparr>t\<^sub>v = Suc (t\<^sub>v (fst x)), coin\<^sub>v = ctail\<rparr>}"
    by (smt (verit, best) Collect_cong Tcoin.exhaust flip_body_set_eq)
  have f1: "\<forall>v\<^sub>0::coin_state. (?f v\<^sub>0) 
    = ((if (coin\<^sub>v v\<^sub>0 = chead \<or> coin\<^sub>v v\<^sub>0 = ctail) \<and> t\<^sub>v v\<^sub>0 = Suc (t\<^sub>v (fst x)) then 1::\<real> else (0::\<real>)) *
      (if coin\<^sub>v v\<^sub>0 = chead then 
            if v\<^sub>0 = snd x then 1::\<real> else (0::\<real>)
       else 
            ((if coin\<^sub>v (snd x) = chead \<and> Suc (t\<^sub>v v\<^sub>0) \<le> t\<^sub>v (snd x) then 
              (((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) / (2::\<real>)) else (0::\<real>)))
      ) / (2::\<real>))
      "
    using divide_eq_0_iff fst_conv by auto
  then have f2: "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_state. 
      ((if (coin\<^sub>v v\<^sub>0 = chead \<or> coin\<^sub>v v\<^sub>0 = ctail) \<and> t\<^sub>v v\<^sub>0 = Suc (t\<^sub>v (fst x)) then 1::\<real> else (0::\<real>)) *
      (if coin\<^sub>v v\<^sub>0 = chead then 
            if v\<^sub>0 = snd x then 1::\<real> else (0::\<real>)
       else 
            ((if coin\<^sub>v (snd x) = chead \<and> Suc (t\<^sub>v v\<^sub>0) \<le> t\<^sub>v (snd x) then 
              (((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) / (2::\<real>)) else (0::\<real>)))
      ) / (2::\<real>)))"
    by presburger
  moreover have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_state \<in> 
      {v\<^sub>0::coin_state. t\<^sub>v v\<^sub>0 = Suc (t\<^sub>v (fst x))} \<union> (-{v\<^sub>0::coin_state. t\<^sub>v v\<^sub>0 = Suc (t\<^sub>v (fst x))}). 
      ((if (coin\<^sub>v v\<^sub>0 = chead \<or> coin\<^sub>v v\<^sub>0 = ctail) \<and> t\<^sub>v v\<^sub>0 = Suc (t\<^sub>v (fst x)) then 1::\<real> else (0::\<real>)) *
      (if coin\<^sub>v v\<^sub>0 = chead then 
            if v\<^sub>0 = snd x then 1::\<real> else (0::\<real>)
       else 
            ((if coin\<^sub>v (snd x) = chead \<and> Suc (t\<^sub>v v\<^sub>0) \<le> t\<^sub>v (snd x) then 
              (((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) / (2::\<real>)) else (0::\<real>)))
      ) / (2::\<real>)))"
    by auto
  moreover have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_state \<in> {v\<^sub>0::coin_state. t\<^sub>v v\<^sub>0 = Suc (t\<^sub>v (fst x))}. 
      ((if (coin\<^sub>v v\<^sub>0 = chead \<or> coin\<^sub>v v\<^sub>0 = ctail) \<and> t\<^sub>v v\<^sub>0 = Suc (t\<^sub>v (fst x)) then 1::\<real> else (0::\<real>)) *
      (if coin\<^sub>v v\<^sub>0 = chead then 
            if v\<^sub>0 = snd x then 1::\<real> else (0::\<real>)
       else 
            ((if coin\<^sub>v (snd x) = chead \<and> Suc (t\<^sub>v v\<^sub>0) \<le> t\<^sub>v (snd x) then 
              (((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) / (2::\<real>)) else (0::\<real>)))
      ) / (2::\<real>)))"
    apply (rule infsum_cong_neutral)
    apply force
    apply simp
    by blast
  moreover have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::coin_state \<in> {v\<^sub>0::coin_state. t\<^sub>v v\<^sub>0 = Suc (t\<^sub>v (fst x))}. 
      ((if coin\<^sub>v v\<^sub>0 = chead then 
            if v\<^sub>0 = snd x then 1::\<real> else (0::\<real>)
       else 
            ((if coin\<^sub>v (snd x) = chead \<and> Suc (t\<^sub>v v\<^sub>0) \<le> t\<^sub>v (snd x) then 
              (((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) / (2::\<real>)) else (0::\<real>)))
      ) / (2::\<real>)))"
    by (smt (verit, best) Tcoin.exhaust infsum_cong mem_Collect_eq mult_cancel_right2)
  moreover have "... = (\<Sum>v\<^sub>0::coin_state \<in> 
      {\<lparr>t\<^sub>v = Suc (t\<^sub>v (fst x)), coin\<^sub>v = chead\<rparr>, \<lparr>t\<^sub>v = Suc (t\<^sub>v (fst x)), coin\<^sub>v = ctail\<rparr>}. 
      ((if coin\<^sub>v v\<^sub>0 = chead then 
            if v\<^sub>0 = snd x then 1::\<real> else (0::\<real>)
       else 
            ((if coin\<^sub>v (snd x) = chead \<and> Suc (t\<^sub>v v\<^sub>0) \<le> t\<^sub>v (snd x) then 
              (((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v (snd x) - Suc (t\<^sub>v v\<^sub>0)) / (2::\<real>)) else (0::\<real>)))
      ) / (2::\<real>)))"
    by (simp add: set_eq)
  moreover have "... = (if \<lparr>t\<^sub>v = Suc (t\<^sub>v (fst x)), coin\<^sub>v = chead\<rparr> = snd x then 1 else 0) / 2 + 
    (if coin\<^sub>v (snd x) = chead \<and> Suc (Suc (t\<^sub>v (fst x))) \<le> t\<^sub>v (snd x) then 
      (((1::\<real>) / (2::\<real>)) ^ (t\<^sub>v (snd x) - Suc (Suc (t\<^sub>v (fst x)))) / (2::\<real>)) else 0) / 2"
    using coin_state.simps(1) by force
  moreover have "... = ?rhs"
    apply auto
    apply (metis Suc_n_not_le_n time.select_convs(1))
    apply (metis coin_state.select_convs(1))
    apply (metis coin_state.select_convs(1))
    apply (metis coin_state.select_convs(1))
    apply (metis order_refl time.select_convs(1))
    using Suc_diff_le power_Suc2 power_commutes times_divide_eq_left by fastforce
  ultimately show "?lhs = ?rhs"
    by presburger
qed

abbreviation "ff P b \<equiv> (repeat_body P b (prel_of_rfrel H) = (prel_of_rfrel H))"
text \<open> What's the probability of this program having an outcome head? \<close>
thm "prepeat.pinduct"
lemma 
  assumes "prepeat_dom (P, b)"
  shows "rfrel_of_prel (repeat P until b) = (1)\<^sub>e"
  using assms prepeat.pinduct by blast
  apply (induct P b rule: prepeat.pinduct)

subsection \<open> Double dices \<close>
text \<open>This example is from Section 15 of the Hehner's paper ``A probability perspective''.

The invariant of the program for an equal result is 
@{text "\<lbrakk>u' = v'\<rbrakk>\<^sub>\<I> * \<lbrakk>t' \<ge> t+1\<rbrakk>\<^sub>\<I> * (5/6)^(t'-t-1) * (1/6)"}.

This program cannot guarantee absolute termination (see Section 2.3 of ``
2005_Book_Abstraction Refinement and Proof for Probabilistic Systems''), but it is almost-certain 
termination.

The probability for non-termination is @{text "\<lbrakk>u' \<noteq> v'\<rbrakk>\<^sub>\<I> * \<lbrakk>t' \<ge> t+1\<rbrakk>\<^sub>\<I> * (5/6)^(t'-t)"}. When 
@{text "t'"} tends to @{text "\<infinity>"}, then the probability tends to 0.
\<close>
alphabet dice = time +
  u :: nat
  v :: nat

definition throw_dice :: "(dice, dice) prel" where
"throw_dice = ((prel_of_rfrel (u \<^bold>\<U> {1..6})) ; (prel_of_rfrel (v \<^bold>\<U> {1..6})))"

lemma "throw_dice = prel_of_rfrel ((\<lbrakk>u\<^sup>> \<in> {1..6}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>v\<^sup>> \<in> {1..6}\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e) / 36)\<^sub>e"
  sorry

definition equal_dices :: "(dice, dice) prel" where 
"equal_dices = repeat 0 throw_dice until (u\<^sup>> = v\<^sup>>)\<^sub>e"

find_theorems name:"prepeat"
term "nat (1)"
term "(a ^ (the_enat ($t\<^sup>> - $t\<^sup>< - 1)))\<^sub>e"
thm "prepeat.cases"
thm "prepeat.pinduct"
find_theorems "prepeat_dom"

lemma 
  shows "prepeat' n throw_dice (u\<^sup>> = v\<^sup>>)\<^sub>e = 
    prel_of_rfrel (\<lbrakk>u\<^sup>> = v\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * (5/6)^\<guillemotleft>n\<guillemotright> * (1/6) + \<lbrakk>\<not>u\<^sup>> = v\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * (1 - (5/6)^\<guillemotleft>n\<guillemotright> * (1/6)) )\<^sub>e"
  apply (induct_tac n)
  apply (simp add: throw_dice_def)
  apply (simp add: prel_uniform_dist_left)
  apply (simp add: prel_pcond_id prel_seqcomp_right_unit uniform_dist_altdef')
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (rel_auto)
  oops
(*
lemma
  assumes "prepeat_dom (P, b)"
  (* assumes "Inv = P ; (t := $t + 1) ; (if\<^sub>c b then II else Inv)" *)
  shows "(repeat P until b) = Inv"
  apply (subst utp_prob_rel_prog.prepeat.psimps)
  apply (simp add: assms(1))
  using assms(1) prepeat.pinduct by blast

lemma 
  shows "equal_dices = prel_of_rfrel (\<lbrakk>u\<^sup>> = v\<^sup>> \<and> $t\<^sup>> \<ge> $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (5/6)^(the_enat ($t\<^sup>> - $t\<^sup>< - 1)) * (1/6))\<^sub>e"
  apply (simp add: A_def)
*)

end