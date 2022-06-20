section \<open> Probabilistic relation programming example 1 \<close>

theory utp_prob_rel_loop_coin
  imports 
    "../utp_prob_rel_lattice_laws" 
begin 

unbundle UTP_Syntax

declare [[show_types]]

subsection \<open> Single coin \<close>

datatype Tcoin = chead | ctail
alphabet coin_state = time +
  coin :: Tcoin

thm "coin_state.simps"
definition flip:: "coin_state prhfun" where
"flip = (prfun_of_rvfun (coin \<^bold>\<U> {chead, ctail}))"

definition flip_loop where
"flip_loop = while\<^sub>p\<^sub>t (coin\<^sup>< = ctail)\<^sub>e do flip od"

definition H:: "coin_state \<times> coin_state \<Rightarrow> \<real>" where 
"H = (\<lbrakk>coin\<^sup>> = chead \<and> $t\<^sup>> \<ge> $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * (1/2)^(($t\<^sup>> - $t\<^sup>< - 1)) * (1/2))\<^sub>e"

lemma flip_is_dist: "is_final_distribution (rvfun_of_prfun flip)"
  apply (simp add: flip_def)
  apply (subst rvfun_uniform_dist_inverse)
  apply (simp)+
  using rvfun_uniform_dist_is_dist
  by (metis coin_vwb_lens finite.emptyI finite.insertI insert_not_empty)

lemma flip_altdef: "rvfun_of_prfun flip = (\<lbrakk>\<lbrakk>\<Union> v \<in> {ctail, chead}. coin := \<guillemotleft>v\<guillemotright>\<rbrakk>\<^sub>P\<rbrakk>\<^sub>\<I>\<^sub>e / 2)\<^sub>e"
  apply (simp add: flip_def)
  apply (subst prfun_uniform_dist_altdef')
  apply simp+
  by (rel_auto)

lemma flip_t: "(flip ; t := $t + 1) = prfun_of_rvfun (\<lbrakk>coin\<^sup>> \<in> {chead, ctail} \<and> $t\<^sup>> = $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 2)\<^sub>e"
  apply (simp add: flip_def)
  apply (simp add: prfun_uniform_dist_left)
  apply (simp add: pfun_defs)
  apply (simp add: rvfun_assignment_inverse)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (simp add: fun_eq_iff)
  apply (rule allI)+
  apply (expr_auto add: rel)
  apply (metis Tcoin.distinct(2) coin_state.ext_inject coin_state.surjective coin_state.update_convs(1) time.ext_inject time.update_convs(1))
  apply (metis Tcoin.distinct(2) coin_state.ext_inject coin_state.surjective coin_state.update_convs(1) time.select_convs(2) time.update_convs(1))
  apply (meson Tcoin.exhaust)
  using Tcoin.exhaust apply blast
  apply (metis time.select_convs(1) time.surjective time.update_convs(1))
  using Tcoin.exhaust apply blast
  by (metis time.select_convs(1) time.surjective time.update_convs(1))

lemma "flip_loop = H"
  apply (simp add: flip_loop_def H_def)
  apply (simp add: ptwhile_def)
  apply (subst flip_t)
  apply (subst sup_continuous_lfp_iteration)
  apply (simp add: pseqcomp_def)
  apply (subst rvfun_seqcomp_inverse)
  apply (simp add: flip_is_dist)
  using ureal_is_prob apply blast
    apply (subst rvfun_seqcomp_is_dist)
      apply (simp add: flip_is_dist)
  apply (expr_auto)
     apply (simp add: passigns_def rvfun_assignment_inverse rvfun_assignment_is_dist)
    apply (simp)
   apply (simp add: pfun_defs)
  apply (simp add: flip_altdef)
   apply (expr_auto)
   apply (subst rvfun_inverse)
    apply (simp add: is_prob_def)
   apply (rel_simp)
end