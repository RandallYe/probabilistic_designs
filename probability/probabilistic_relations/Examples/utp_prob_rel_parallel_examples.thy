section \<open> Example of probabilistic relation programming: parallel composition \<close>

theory utp_prob_rel_parallel_examples
  imports 
    "../utp_prob_rel_laws" 
begin 

unbundle UTP_Syntax

declare [[show_types]]

named_theorems robot_local_defs

alphabet state1 = 
  b :: \<bool>

lemma if_div_distrib: "(if a then (bb::\<real>) else c) / d = (if a then (bb / d) else (c /d))"
  by presburger

lemma if_div_distrib': "n * (if a then (bb::\<real>) else c) / d = (if a then (n * bb / d) else (n * c /d))"
  by presburger

find_theorems "?x / ?y"
lemma "x / y = x * ((1::\<real>) / y)"
  by (simp add: Fields.field_class.field_divide_inverse)

text \<open>This example is from Hehner's paper "a Probability Perspective" 
\cite[Sect.~Probabilistic programming]{Hehner2011} \<close>
term "\<lbrakk>(b := e) :: state1 rel\<rbrakk>\<^sub>P"
term "(b\<^sup>> = f)\<^sub>e"
lemma b_assign_rel: "\<lbrakk>(b := \<guillemotleft>e\<guillemotright>) :: state1 rel\<rbrakk>\<^sub>P = (b\<^sup>> = \<guillemotleft>e\<guillemotright>)\<^sub>e"
  by (rel_auto)

lemma b_assign_rel': "\<lbrakk>(b := e) :: state1 rel\<rbrakk>\<^sub>P = (b\<^sup>> = e\<^sup><)\<^sub>e"
  apply (simp add: expr_defs)
  by (rel_auto)

lemma "(((if\<^sub>p 1/3 then b := False else b := True) \<parallel> (if\<^sub>p 1/3 then b := (\<not> b) else II))::state1 phrel) = 
  prel_of_rfrel ((5 - 3 * \<lbrakk>b\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e + 6 * \<lbrakk>b\<^sup>< \<and> b\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e) / 10)\<^sub>e "
  apply (simp add: pparallel'_def)
  apply (simp add: prel_skip[where x = "b"])
  apply (subst prel_set_conv_pchoice_assigns_c')
  apply (simp)
  apply (subst prel_set_conv_pchoice_assigns_c')
   apply (simp)
  apply (simp add: b_assign_rel')
  apply (simp add: pparallel_def)
  apply (expr_auto add: dist_defs)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (subst fun_eq_iff, rule allI)
proof -
  fix x::"state1 \<times> state1"
  let ?sum = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state1.
          ((if \<not> b\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) / (3::\<real>) +
           (2::\<real>) * (if b\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) / (3::\<real>)) *
          ((if b\<^sub>v v\<^sub>0 = (\<not> b\<^sub>v (fst x)) then 1::\<real> else (0::\<real>)) / (3::\<real>) +
           (2::\<real>) * (if b\<^sub>v v\<^sub>0 = b\<^sub>v (fst x) then 1::\<real> else (0::\<real>)) / (3::\<real>)))"
  have card_1: "(card {s::state1. \<not> b\<^sub>v s \<and> b\<^sub>v s = (\<not> b\<^sub>v (fst x))}) 
    = (if b\<^sub>v (fst x) then 1 else 0)"
    apply (simp)
    by (smt (verit, ccfv_threshold) card_1_singleton state1.cases state1.select_convs(1))
  have card_2: "(card {s::state1. \<not> b\<^sub>v s \<and> b\<^sub>v s = b\<^sub>v (fst x)}) 
    = (if \<not>b\<^sub>v (fst x) then 1 else 0)"
    apply (auto)
    by (smt (verit) card_1_singleton state1.cases state1.select_convs(1) state1.update_convs(1))

  have card_3: "(card {s::state1. b\<^sub>v s \<and> b\<^sub>v s = (\<not> b\<^sub>v (fst x))}) 
    = (if \<not>b\<^sub>v (fst x) then 1 else 0)"
    apply (auto)
    by (smt (verit) card_1_singleton state1.cases state1.select_convs(1) state1.update_convs(1))

  have card_4: "(card {s::state1. b\<^sub>v s \<and> b\<^sub>v s = b\<^sub>v (fst x)}) 
    = (if b\<^sub>v (fst x) then 1 else 0)"
    apply (auto)
    by (smt (verit) card_1_singleton state1.cases state1.select_convs(1) state1.update_convs(1))

  have sum_1: "?sum = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state1.
       (if \<not> b\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) / (3::\<real>) *
       ((if b\<^sub>v v\<^sub>0 = (\<not> b\<^sub>v (fst x)) then 1::\<real> else (0::\<real>)) / (3::\<real>)) +
       (if \<not> b\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) / (3::\<real>) *
       ((2::\<real>) * (if b\<^sub>v v\<^sub>0 = b\<^sub>v (fst x) then 1::\<real> else (0::\<real>)) / (3::\<real>)) +
       ((2::\<real>) * (if b\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) / (3::\<real>) *
        ((if b\<^sub>v v\<^sub>0 = (\<not> b\<^sub>v (fst x)) then 1::\<real> else (0::\<real>)) / (3::\<real>)) +
        (2::\<real>) * (if b\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) / (3::\<real>) *
        ((2::\<real>) * (if b\<^sub>v v\<^sub>0 = b\<^sub>v (fst x) then 1::\<real> else (0::\<real>)) / (3::\<real>))))"
    apply (simp only: ring_distribs(2))
    by (simp only: ring_distribs(1))
   also have sum_2: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state1.
          (if \<not> b\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) *
             (if b\<^sub>v v\<^sub>0 = (\<not> b\<^sub>v (fst x)) then 1::\<real> else (0::\<real>)) / (9::\<real>) +
       (if \<not> b\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) *
         (if b\<^sub>v v\<^sub>0 = b\<^sub>v (fst x) then 1::\<real> else (0::\<real>)) * ((2::\<real>) / (9::\<real>)) +
       ((if b\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) *
         (if b\<^sub>v v\<^sub>0 = (\<not> b\<^sub>v (fst x)) then 1::\<real> else (0::\<real>)) * ((2::\<real>) / (9::\<real>))) +
       ((if b\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) *
         (if b\<^sub>v v\<^sub>0 = b\<^sub>v (fst x) then 1::\<real> else (0::\<real>)) * (4 / (9::\<real>))))"
    apply (rule infsum_cong)
     by (simp)
   also have sum_3: "... = (if b\<^sub>v (fst x) then 5 else 4) / 9"
     apply (subst conditional_conds_conj)+
     apply (simp only: divide_inverse)
     apply (subst infsum_constant_finite_states_4)
     using card_1 not_finite_existsD apply force
     using card_2 not_finite_existsD apply force
     using card_3 not_finite_existsD apply force
     using card_4 not_finite_existsD apply force
     by (simp add: card_1 card_2 card_3 card_4)
  
  show "((if \<not> b\<^sub>v (snd x) then 1::\<real> else (0::\<real>)) / (3::\<real>) +
        (2::\<real>) * (if b\<^sub>v (snd x) then 1::\<real> else (0::\<real>)) / (3::\<real>)) *
       ((if b\<^sub>v (snd x) = (\<not> b\<^sub>v (fst x)) then 1::\<real> else (0::\<real>)) / (3::\<real>) +
        (2::\<real>) * (if b\<^sub>v (snd x) = b\<^sub>v (fst x) then 1::\<real> else (0::\<real>)) / (3::\<real>)) /
       ?sum =
       ((5::\<real>) - (3::\<real>) * (if b\<^sub>v (fst x) then 1::\<real> else (0::\<real>)) +
        (6::\<real>) * (if b\<^sub>v (fst x) \<and> b\<^sub>v (snd x) then 1::\<real> else (0::\<real>))) /
       (10::\<real>)"
    apply (simp only: sum_1 sum_2 sum_3)
    by (auto)
qed

end
