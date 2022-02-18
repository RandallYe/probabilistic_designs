section \<open> Probabilistic relation programming example 1 \<close>

theory utp_prob_rel_monty_hall
  imports 
    "../utp_prob_rel_laws" 
begin 

unbundle UTP_Syntax

declare [[show_types]]

subsection \<open> No Change \<close>

alphabet DWTA_state = 
  p :: nat
  c :: nat
  m :: nat

term "\<^bold>N \<lbrakk>p\<^sup>> \<in> {0, 1, 2} \<and> c\<^sup>> = c\<^sup>< \<and> m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e"
term "\<^bold>N\<^sub>\<alpha> x (\<lbrakk>p\<^sup>> \<in> {0, 1, 2} \<and> c\<^sup>> = c\<^sup>< \<and> m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e)"
term "((\<^bold>N\<^sub>\<alpha> p (\<lbrakk>p\<^sup>> \<in> {0, 1, 2}\<rbrakk>\<^sub>\<I>\<^sub>e)) * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"

term "(prel_of_rfrel (\<^bold>N\<^sub>\<alpha> p (\<lbrakk>p\<^sup>> \<in> {0, 1, 2} \<and> c\<^sup>> = c\<^sup>< \<and> m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e)))"

definition INIT_p :: "DWTA_state phrel" where 
"INIT_p \<equiv> prel_of_rfrel (\<^bold>N\<^sub>\<alpha> p (\<lbrakk>p\<^sup>> \<in> {0, 1, 2} \<and> c\<^sup>> = c\<^sup>< \<and> m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e))"

definition INIT_c :: "DWTA_state phrel" where 
"INIT_c \<equiv> prel_of_rfrel (\<^bold>N\<^sub>\<alpha> c (\<lbrakk>c\<^sup>> \<in> {0, 1, 2} \<and> p\<^sup>> = p\<^sup>< \<and> m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e))"

definition INIT:: "DWTA_state phrel" where 
"INIT = INIT_p ; INIT_c"

lemma "INIT_p = prel_of_rfrel ((\<^bold>N\<^sub>\<alpha> p (\<lbrakk>p\<^sup>> \<in> {0, 1, 2}\<rbrakk>\<^sub>\<I>\<^sub>e)) * \<lbrakk>c\<^sup>> = c\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"
  apply (simp add: INIT_p_def dist_defs)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  by (expr_auto)

lemma "rfrel_of_prel INIT_p = \<^bold>N\<^sub>\<alpha> p (\<lbrakk>p\<^sup>> \<in> {0, 1, 2} \<and> c\<^sup>> = c\<^sup>< \<and> m\<^sup>> = m\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e)"
   apply (simp add: INIT_p_def dist_defs)

lemma "\<forall>x \<in> {0..2}. (rfrel_of_prel INIT_p ;\<^sub>f (\<lbrakk>p\<^sup>< = \<guillemotleft>x\<guillemotright>\<rbrakk>\<^sub>\<I>\<^sub>e) = (1/3)\<^sub>e)"
  apply (simp add: INIT_p_def dist_defs)
  apply (expr_auto)
  apply (subst prel_of_rfrel_inverse)
  apply (simp)
  apply (subst prel_is_dist_pparallel)
proof
qed

end
