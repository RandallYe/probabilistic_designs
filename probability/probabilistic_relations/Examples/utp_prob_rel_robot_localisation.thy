section \<open> Example of probabilistic relation programming: Monty Hall \<close>

theory utp_prob_rel_robot_localisation
  imports 
    "../utp_prob_rel_laws" 
begin 

unbundle UTP_Syntax

declare [[show_types]]

named_theorems robot_local_defs

alphabet robot_local_state = 
  bel :: nat

definition "door p = ((p = (0::\<nat>)) \<or> (p = 2))"

definition init :: "robot_local_state rfhrel" where
"init = bel \<^bold>\<U> {(0::\<nat>), 1, 2}"

text \<open> A noisy sensor is more likely to get a right reading than a wrong reading: 4 vs. 1.\<close>
definition scale_door :: "robot_local_state rfhrel"  where
"scale_door = (3 * \<lbrakk>\<guillemotleft>door\<guillemotright> (bel\<^sup>>)\<rbrakk>\<^sub>\<I>\<^sub>e + 1)\<^sub>e"

definition scale_wall :: "robot_local_state rfhrel"  where
"scale_wall = (3 * \<lbrakk>\<not>\<guillemotleft>door\<guillemotright> (bel\<^sup>>)\<rbrakk>\<^sub>\<I>\<^sub>e + 1)\<^sub>e"

definition move_right :: "robot_local_state phrel"  where
"move_right = (bel := (bel + 1) mod 3)"

definition robot_localisation where 
"robot_localisation = ((((init \<parallel> scale_door) ; move_right) \<parallel> scale_door) ; move_right) \<parallel> scale_wall"

definition believe_1::"robot_local_state rfhrel" where 
"believe_1 \<equiv> (4/9 * \<lbrakk>bel\<^sup>> = 0\<rbrakk>\<^sub>\<I>\<^sub>e + 1/9 * \<lbrakk>bel\<^sup>> = 1\<rbrakk>\<^sub>\<I>\<^sub>e + 4/9 * \<lbrakk>bel\<^sup>> = 2\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"

definition move_right_1::"robot_local_state rfhrel" where 
"move_right_1 \<equiv> (4/9 * \<lbrakk>bel\<^sup>> = 0\<rbrakk>\<^sub>\<I>\<^sub>e + 4/9 * \<lbrakk>bel\<^sup>> = 1\<rbrakk>\<^sub>\<I>\<^sub>e + 1/9 * \<lbrakk>bel\<^sup>> = 2\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"

lemma init_knowledge_sum: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state.
       (if \<lparr>bel\<^sub>v = 0::\<nat>\<rparr> = v\<^sub>0 \<or> \<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr> = v\<^sub>0 \<or> \<lparr>bel\<^sub>v = 2::\<nat>\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) *
       ((3::\<real>) * (if bel\<^sub>v v\<^sub>0 = (0::\<nat>) \<or> bel\<^sub>v v\<^sub>0 = (2::\<nat>) then 1::\<real> else (0::\<real>)) + (1::\<real>)) /
       (3::\<real>)) = 3"
proof -
  let ?bel_set = "{\<lparr>bel\<^sub>v = 0::\<nat>\<rparr>, \<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr>, \<lparr>bel\<^sub>v = 2::\<nat>\<rparr>}"
  let ?sum = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state.
       (if \<lparr>bel\<^sub>v = 0::\<nat>\<rparr> = v\<^sub>0 \<or> \<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr> = v\<^sub>0 \<or> \<lparr>bel\<^sub>v = 2::\<nat>\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) *
       ((3::\<real>) * (if bel\<^sub>v v\<^sub>0 = (0::\<nat>) \<or> bel\<^sub>v v\<^sub>0 = (2::\<nat>) then 1::\<real> else (0::\<real>)) + (1::\<real>)) /
       (3::\<real>))"
  let ?fun = "\<lambda>v\<^sub>0. (if \<lparr>bel\<^sub>v = 0::\<nat>\<rparr> = v\<^sub>0 \<or> \<lparr>bel\<^sub>v = 2\<rparr> = v\<^sub>0 then 4::\<real> else 
        (if \<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>))) / 3"
  have "?sum = 
    (\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state. ?fun v\<^sub>0)"
    apply (subst infsum_cong[where g="\<lambda>v\<^sub>0. (if \<lparr>bel\<^sub>v = 0::\<nat>\<rparr> = v\<^sub>0 \<or> \<lparr>bel\<^sub>v = 2\<rparr> = v\<^sub>0 then 4::\<real> else 
        (if \<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>))) / 3"])
    by (auto)
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state \<in> ?bel_set \<union> (UNIV - ?bel_set). ?fun v\<^sub>0)"
    by auto
  also have "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state \<in> ?bel_set. ?fun v\<^sub>0)"
    apply (rule infsum_cong_neutral)
    apply fastforce
     apply fastforce
    by blast
  also have "... = (\<Sum>v\<^sub>0::robot_local_state \<in> {\<lparr>bel\<^sub>v = 0::\<nat>\<rparr>}. ?fun v\<^sub>0) + 
      (\<Sum>v\<^sub>0::robot_local_state \<in> {\<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr>, \<lparr>bel\<^sub>v = (2::\<nat>)\<rparr>}. ?fun v\<^sub>0)"
    apply (subst infsum_finite)
    apply (simp)
    by force
  also have "... = (\<Sum>v\<^sub>0::robot_local_state \<in> {\<lparr>bel\<^sub>v = 0::\<nat>\<rparr>}. ?fun v\<^sub>0) + 
      (\<Sum>v\<^sub>0::robot_local_state \<in> {\<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr>}. ?fun v\<^sub>0) +
      (\<Sum>v\<^sub>0::robot_local_state \<in> {\<lparr>bel\<^sub>v = (2::\<nat>)\<rparr>}. ?fun v\<^sub>0)"
    by force
  also have "... = 3"
    by simp
  then show ?thesis
    using calculation by presburger
qed

lemma believe_1_simp: 
  "(init \<parallel> scale_door) = prel_of_rfrel believe_1"
  apply (simp add: pparallel_def init_def scale_door_def believe_1_def)
  apply (simp add: dist_norm_def)
  apply (simp add: uniform_dist_altdef)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (simp add: door_def)
  apply (simp add: expr_defs)
  apply (rel_auto)
  using init_knowledge_sum apply auto[1]
  using init_knowledge_sum apply linarith
  apply (simp add: init_knowledge_sum)
  using init_knowledge_sum by auto[1]

(* Use algebraic laws *)
lemma believe_1_simp': 
  "(init \<parallel> scale_door) = prel_of_rfrel believe_1"
  apply (simp add: init_def believe_1_def)
  apply (subst prel_parallel_uniform_dist)
  apply (simp)+
  apply (simp add: scale_door_def)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (simp add: door_def)
  apply (simp add: expr_defs)
  by (rel_auto)

lemma move_right_1_simp: "(init \<parallel> scale_door) ; move_right = prel_of_rfrel move_right_1"
  apply (simp add: pcomp_def move_right_1_def)
  (* apply (simp add: pparallel_def dist_norm_def) *)
  apply (simp add: init_def)
  apply (subst prel_parallel_uniform_dist')
  apply (simp)+
  apply (simp add: scale_door_def door_def)
  apply (expr_auto)
  apply (simp add: scale_door_def door_def)
   apply (expr_auto)
  apply (simp add: prel_defs dist_norm_def move_right_def scale_door_def door_def )
  apply (subst prel_set_conv_assign)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (expr_auto add: rel)
proof -
  let ?lhs_f = "\<lambda>v\<^sub>0::robot_local_state. ((if \<lparr>bel\<^sub>v = 0::\<nat>\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) * (4::\<real>) +
        ((if \<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) +
         (if \<lparr>bel\<^sub>v = 2::\<nat>\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) * (4::\<real>))) *
       (if v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = 0::\<nat>\<rparr> then 1::\<real> else (0::\<real>)) / 9"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state. ?lhs_f v\<^sub>0)"

  have f1: "\<forall>v\<^sub>0. \<not>(\<lparr>bel\<^sub>v = 0::\<nat>\<rparr> = v\<^sub>0 \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = 0::\<nat>\<rparr>)"
    by (auto)
  have f2: "\<forall>v\<^sub>0. \<not>(\<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr> = v\<^sub>0 \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = 0::\<nat>\<rparr>)"
    by (auto)
  have f3: "\<forall>v\<^sub>0. (\<lparr>bel\<^sub>v = 2::\<nat>\<rparr> = v\<^sub>0 \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = 0::\<nat>\<rparr>) = 
          (\<lparr>bel\<^sub>v = 2::\<nat>\<rparr> = v\<^sub>0)"
    by (auto)
  have "?lhs = (4 / 9)"
    apply (subst ring_distribs(2))+
    apply (simp add: mult.commute[where b = "(4::\<real>)"])+
    apply (simp add: mult.assoc)+
    apply (subst conditional_conds_conj)+
    apply (simp add: f1 f2 f3)
    apply (subst infsum_cdiv_left)
    apply (rule summable_on_cmult_right)
    apply (simp add: infsum_singleton_summable)
    apply (subst infsum_cmult_right)
    apply (simp add: infsum_singleton_summable)
    apply (subst infsum_constant_finite_states)
    by (simp)+
    
  then show "?lhs * (9::\<real>) =  (4::\<real>)"
    by linarith
next
  let ?lhs_f = "\<lambda>v\<^sub>0::robot_local_state. ((if \<lparr>bel\<^sub>v = 0::\<nat>\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) * (4::\<real>) +
        ((if \<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) +
         (if \<lparr>bel\<^sub>v = 2::\<nat>\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) * (4::\<real>))) *
       (if v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr> then 1::\<real> else (0::\<real>)) / 9"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state. ?lhs_f v\<^sub>0)"

  have f1: "\<forall>v\<^sub>0. (\<lparr>bel\<^sub>v = 0::\<nat>\<rparr> = v\<^sub>0 \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr>) = 
      (\<lparr>bel\<^sub>v = 0::\<nat>\<rparr> = v\<^sub>0)"
    by (auto)
  have f2: "\<forall>v\<^sub>0. \<not>(\<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr> = v\<^sub>0 \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr>)"
    by (auto)
  have f3: "\<forall>v\<^sub>0. \<not>(\<lparr>bel\<^sub>v = 2::\<nat>\<rparr> = v\<^sub>0 \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr>)"
    by (auto)
  have "?lhs = (4 / 9)"
    apply (subst ring_distribs(2))+
    apply (simp add: mult.commute[where b = "(4::\<real>)"])+
    apply (simp add: mult.assoc)+
    apply (subst conditional_conds_conj)+
    apply (simp add: f1 f2 f3)
    apply (subst infsum_cdiv_left)
    apply (rule summable_on_cmult_right)
    apply (simp add: infsum_singleton_summable)
    apply (subst infsum_cmult_right)
    apply (simp add: infsum_singleton_summable)
    apply (subst infsum_constant_finite_states)
    by (simp)+
    
  then show "?lhs * (9::\<real>) =  (4::\<real>)"
    by linarith
next
  let ?lhs_f = "\<lambda>v\<^sub>0::robot_local_state. ((if \<lparr>bel\<^sub>v = 0::\<nat>\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) * (4::\<real>) +
        ((if \<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) +
         (if \<lparr>bel\<^sub>v = 2::\<nat>\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) * (4::\<real>))) *
       (if v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = (2::\<nat>)\<rparr> then 1::\<real> else (0::\<real>)) / 9"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state. ?lhs_f v\<^sub>0)"

  have f1: "\<forall>v\<^sub>0. \<not>(\<lparr>bel\<^sub>v = 0::\<nat>\<rparr> = v\<^sub>0 \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = (2::\<nat>)\<rparr>)"
    by (auto)
  have f2: "\<forall>v\<^sub>0. (\<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr> = v\<^sub>0 \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = (2::\<nat>)\<rparr>) 
     = (\<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr> = v\<^sub>0)"
    by (auto)
  have f3: "\<forall>v\<^sub>0. \<not>(\<lparr>bel\<^sub>v = 2::\<nat>\<rparr> = v\<^sub>0 \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = (2::\<nat>)\<rparr>)"
    by (auto)
  have "?lhs = (1 / 9)"
    apply (subst ring_distribs(2))+
    apply (simp add: mult.commute[where b = "(4::\<real>)"])+
    apply (simp add: mult.assoc)+
    apply (subst conditional_conds_conj)+
    apply (simp add: f1 f2 f3)
    apply (subst infsum_cdiv_left)
    apply (simp add: infsum_singleton_summable)
    apply (simp add: infsum_singleton_summable)
    apply (subst infsum_constant_finite_states)
    by (simp)+
    
  then show "?lhs * (9::\<real>) =  (1::\<real>)"
    by linarith
next
  fix bel
  assume a1: "(0::\<nat>) < bel"
  assume a2: "\<not> bel = Suc (0::\<nat>)"
  assume a3: "\<not> bel = (2::\<nat>)"
  let ?lhs_f = "\<lambda>v\<^sub>0::robot_local_state. ((if \<lparr>bel\<^sub>v = 0::\<nat>\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) * (4::\<real>) +
        ((if \<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) +
         (if \<lparr>bel\<^sub>v = 2::\<nat>\<rparr> = v\<^sub>0 then 1::\<real> else (0::\<real>)) * (4::\<real>))) *
       (if v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = bel\<rparr> then 1::\<real> else (0::\<real>)) / 9"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state. ?lhs_f v\<^sub>0)"

  have f1: "\<forall>v\<^sub>0. \<not>(\<lparr>bel\<^sub>v = 0::\<nat>\<rparr> = v\<^sub>0 \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = bel\<rparr>)"
    using a2 by force
  have f2: "\<forall>v\<^sub>0. \<not>(\<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr> = v\<^sub>0 \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = bel\<rparr>)"
    using a3 by force
  have f3: "\<forall>v\<^sub>0. \<not>(\<lparr>bel\<^sub>v = 2::\<nat>\<rparr> = v\<^sub>0 \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = bel\<rparr>)"
    using a1 by force
  have "?lhs = 0"
    apply (subst ring_distribs(2))+
    apply (simp add: mult.commute[where b = "(4::\<real>)"])+
    apply (simp add: mult.assoc)+
    apply (subst conditional_conds_conj)+
    by (simp add: f1 f2 f3)
    
  then show "?lhs =  0"
    by linarith
qed

lemma "rfrel_of_prel (prel_of_rfrel move_right_1) = move_right_1"
  ap

lemma "(((init \<parallel> scale_door) ; move_right) \<parallel> scale_door) = 
  prel_of_rfrel (2/3 * \<lbrakk>bel\<^sup>> = 0\<rbrakk>\<^sub>\<I>\<^sub>e + 1/6 * \<lbrakk>bel\<^sup>> = 1\<rbrakk>\<^sub>\<I>\<^sub>e + 1/6 * \<lbrakk>bel\<^sup>> = 2\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"
  apply (simp add: move_right_1_simp)
  apply (simp add: scale_door_def door_def prel_defs)

end
