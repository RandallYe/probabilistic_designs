section \<open> Example of probabilistic relation programming: parallel composition \<close>

theory utp_prob_rel_lattice_symmetric_random_walker
  imports 
    "UTP_prob_relations.utp_prob_rel_lattice_laws" 
begin 

unbundle UTP_Syntax

declare [[show_types]]

alphabet srwstate = 
  x :: nat

definition f:: "srwstate prhfun" where
"f = if\<^sub>p 0.5 then (x := x - 1) else (x := x + 1)"

definition sym_random_walker where
"sym_random_walker = while\<^sub>p (x\<^sup>< > 0)\<^sub>e do f od"

lemma cflip_iter_seq_tendsto_0:
  "\<forall>s::srwstate \<times> srwstate. (\<lambda>n::\<nat>. ureal2real (iter_seq n (x\<^sup>< > 0)\<^sub>e f 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
proof 
  fix s
  have "(\<lambda>n::\<nat>. ureal2real (iter_seq (n+1) (x\<^sup>< > 0)\<^sub>e f 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    sorry
  then show "(\<lambda>n::\<nat>. ureal2real (iter_seq n (x\<^sup>< > 0)\<^sub>e f 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    by (rule LIMSEQ_offset[where k = 1])
qed

end
