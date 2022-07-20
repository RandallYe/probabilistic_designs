section \<open> Example of probabilistic relation programming: Robot localisation \<close>

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

definition believe_2::"robot_local_state rfhrel" where 
"believe_2 \<equiv> (2/3 * \<lbrakk>bel\<^sup>> = 0\<rbrakk>\<^sub>\<I>\<^sub>e + 1/6 * \<lbrakk>bel\<^sup>> = 1\<rbrakk>\<^sub>\<I>\<^sub>e + 1/6 * \<lbrakk>bel\<^sup>> = 2\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"

definition move_right_2::"robot_local_state rfhrel" where 
"move_right_2 \<equiv> (1/6 * \<lbrakk>bel\<^sup>> = 0\<rbrakk>\<^sub>\<I>\<^sub>e + 2/3 * \<lbrakk>bel\<^sup>> = 1\<rbrakk>\<^sub>\<I>\<^sub>e + 1/6 * \<lbrakk>bel\<^sup>> = 2\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"

definition believe_3::"robot_local_state rfhrel" where 
"believe_3 \<equiv> (1/18 * \<lbrakk>bel\<^sup>> = 0\<rbrakk>\<^sub>\<I>\<^sub>e + 8/9 * \<lbrakk>bel\<^sup>> = 1\<rbrakk>\<^sub>\<I>\<^sub>e + 1/18 * \<lbrakk>bel\<^sup>> = 2\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"

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

lemma believe_1_simp: "(init \<parallel> scale_door) = prel_of_rfrel believe_1"
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
lemma believe_1_simp': "(init \<parallel> scale_door) = prel_of_rfrel believe_1"
  apply (simp add: init_def believe_1_def)
  apply (subst prel_parallel_uniform_dist)
  apply (simp)+
  apply (simp add: scale_door_def)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (simp add: door_def)
  apply (simp add: expr_defs)
  by (rel_auto)

lemma move_right_1_simp: "(init \<parallel> scale_door) ; move_right = prel_of_rfrel move_right_1"
  apply (simp add: pseqcomp_def move_right_1_def)
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

lemma move_right_1_dist: "rfrel_of_prel (prel_of_rfrel move_right_1) = move_right_1"
proof -
  have summable_1: "(\<lambda>s::robot_local_state. (4::\<real>) * (if bel\<^sub>v s = (0::\<nat>) then 1::\<real> else (0::\<real>)) / (9::\<real>)) 
        summable_on UNIV"
    apply (rule summable_on_cdiv_left)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    by (smt (z3) Collect_mono card_0_eq finite.insertI infinite_arbitrarily_large rev_finite_subset 
      robot_local_state.surjective singleton_conv unit.exhaust)

  have summable_2: "(\<lambda>s::robot_local_state. (4::\<real>) * (if bel\<^sub>v s = Suc (0::\<nat>) then 1::\<real> else (0::\<real>)) / (9::\<real>)) 
      summable_on UNIV"
    apply (rule summable_on_cdiv_left)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    by (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)

  have summable_3: "(\<lambda>s::robot_local_state. (if bel\<^sub>v s = (2::\<nat>) then 1::\<real> else (0::\<real>)) / (9::\<real>)) 
      summable_on UNIV"
    apply (rule summable_on_cdiv_left)
    apply (rule infsum_constant_finite_states_summable)
    by (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)

  have sum_1: "(\<Sum>\<^sub>\<infinity>s::robot_local_state. (4::\<real>) * (if bel\<^sub>v s = (0::\<nat>) then 1::\<real> else (0::\<real>)) / (9::\<real>)) = 4/9"
    apply (subst infsum_cdiv_left)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (subst infsum_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (subst infsum_constant_finite_states)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (simp)
    apply (subst card_1_singleton_iff)
    apply (rule_tac x = "\<lparr>bel\<^sub>v = (0::\<nat>)\<rparr>" in exI)
    by force

have sum_2: "(\<Sum>\<^sub>\<infinity>s::robot_local_state. (4::\<real>) * (if bel\<^sub>v s = Suc (0::\<nat>) then 1::\<real> else (0::\<real>)) / (9::\<real>)) = 4/9"
    apply (subst infsum_cdiv_left)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (subst infsum_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (subst infsum_constant_finite_states)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (simp)
    apply (subst card_1_singleton_iff)
    apply (rule_tac x = "\<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr>" in exI)
    by force

  have sum_3: "(\<Sum>\<^sub>\<infinity>s::robot_local_state. (if bel\<^sub>v s = (2::\<nat>) then 1::\<real> else (0::\<real>)) / (9::\<real>)) = 1/9"
    apply (subst infsum_cdiv_left)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (subst infsum_constant_finite_states)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (simp)
    apply (subst card_1_singleton_iff)
    apply (rule_tac x = "\<lparr>bel\<^sub>v = (2::\<nat>)\<rparr>" in exI)
  by force

  show ?thesis
    apply (simp add: move_right_1_def)
    apply (subst prel_of_rfrel_inverse)
    apply (expr_auto add: dist_defs)
    apply (subst infsum_add)
    apply (subst summable_on_add)
    apply (simp add: summable_1)
    apply (simp add: summable_2)
    apply (simp)
    apply (simp add: summable_3)
    apply (subst infsum_add)
    apply (simp add: summable_1)
    apply (simp add: summable_2)
    by (simp add: sum_1 sum_2 sum_3)+
qed

lemma believe_2_sum: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state.
         (4::\<real>) * (if bel\<^sub>v v\<^sub>0 = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
         ((3::\<real>) * (if bel\<^sub>v v\<^sub>0 = (0::\<nat>) \<or> bel\<^sub>v v\<^sub>0 = (2::\<nat>) then 1::\<real> else (0::\<real>)) + (1::\<real>)) /
         (9::\<real>) +
         (4::\<real>) * (if bel\<^sub>v v\<^sub>0 = Suc (0::\<nat>) then 1::\<real> else (0::\<real>)) *
         ((3::\<real>) * (if bel\<^sub>v v\<^sub>0 = (0::\<nat>) \<or> bel\<^sub>v v\<^sub>0 = (2::\<nat>) then 1::\<real> else (0::\<real>)) + (1::\<real>)) /
         (9::\<real>) +
         (if bel\<^sub>v v\<^sub>0 = (2::\<nat>) then 1::\<real> else (0::\<real>)) *
         ((3::\<real>) * (if bel\<^sub>v v\<^sub>0 = (0::\<nat>) \<or> bel\<^sub>v v\<^sub>0 = (2::\<nat>) then 1::\<real> else (0::\<real>)) + (1::\<real>)) /
         (9::\<real>)) = 8 /3"
  apply (simp add: ring_distribs(1))
  apply (subst mult.assoc[symmetric,where b = "3"])
  apply (subst mult.commute[where b = "3"])
  apply (subst mult.assoc)
  apply (subst conditional_conds_conj)+
proof -
  let ?f1 = "(\<lambda>v\<^sub>0::robot_local_state. ((12::\<real>) *
        (if bel\<^sub>v v\<^sub>0 = (0::\<nat>) \<and> (bel\<^sub>v v\<^sub>0 = (0::\<nat>) \<or> bel\<^sub>v v\<^sub>0 = (2::\<nat>)) then 1::\<real> else (0::\<real>)) +
        (4::\<real>) * (if bel\<^sub>v v\<^sub>0 = (0::\<nat>) then 1::\<real> else (0::\<real>))) /
       (9::\<real>))"
  let ?f2 = "(\<lambda>v\<^sub>0::robot_local_state. ((12::\<real>) *
        (if bel\<^sub>v v\<^sub>0 = Suc (0::\<nat>) \<and> (bel\<^sub>v v\<^sub>0 = (0::\<nat>) \<or> bel\<^sub>v v\<^sub>0 = (2::\<nat>)) then 1::\<real> else (0::\<real>)) +
        (4::\<real>) * (if bel\<^sub>v v\<^sub>0 = Suc (0::\<nat>) then 1::\<real> else (0::\<real>))) /
       (9::\<real>))"
  let ?f3 = "(\<lambda>v\<^sub>0::robot_local_state. ((3::\<real>) * (if bel\<^sub>v v\<^sub>0 = (2::\<nat>) \<and> (bel\<^sub>v v\<^sub>0 = (0::\<nat>) \<or> bel\<^sub>v v\<^sub>0 = (2::\<nat>)) then 1::\<real> else (0::\<real>)) +
      (if bel\<^sub>v v\<^sub>0 = (2::\<nat>) then 1::\<real> else (0::\<real>))) /
     (9::\<real>))"
  have summable_1: "?f1 summable_on UNIV"
    apply (rule summable_on_cdiv_left)
    apply (rule summable_on_add)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_SIG) Collect_mono finite.emptyI finite.insertI not_finite_existsD 
        rev_finite_subset robot_local_state.equality singleton_conv unit.exhaust)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    by (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
  have summable_2: "?f2 summable_on UNIV"
    apply (rule summable_on_cdiv_left)
    apply (rule summable_on_add)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_SIG) Collect_mono finite.emptyI finite.insertI not_finite_existsD 
        rev_finite_subset robot_local_state.equality singleton_conv unit.exhaust)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    by (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
  have summable_3: "?f3 summable_on UNIV"
    apply (rule summable_on_cdiv_left)
    apply (rule summable_on_add)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_SIG) Collect_mono finite.emptyI finite.insertI not_finite_existsD 
        rev_finite_subset robot_local_state.equality singleton_conv unit.exhaust)
    apply (rule infsum_constant_finite_states_summable)
    by (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)

  have card_1: "card {s::robot_local_state. bel\<^sub>v s = 0} = Suc (0)"
    apply (subst card_1_singleton_iff)
    by (smt (verit, del_insts) Collect_cong robot_local_state.equality robot_local_state.select_convs(1) 
      singleton_conv unit.exhaust)
  have card_2: "card {s::robot_local_state. bel\<^sub>v s = Suc (0)} = Suc (0)"
    apply (subst card_1_singleton_iff)
    by (smt (verit, del_insts) Collect_cong robot_local_state.equality robot_local_state.select_convs(1) 
      singleton_conv unit.exhaust)
  have card_3: "card {s::robot_local_state. bel\<^sub>v s = 2} = Suc (0)"
    apply (subst card_1_singleton_iff)
    by (smt (verit, del_insts) Collect_cong robot_local_state.equality robot_local_state.select_convs(1) 
      singleton_conv unit.exhaust)

  have sum_1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state. ?f1 v\<^sub>0) = 16 / 9"
    apply (subst infsum_cdiv_left)
    apply (rule summable_on_add)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_SIG) Collect_mono finite.emptyI finite.insertI not_finite_existsD 
        rev_finite_subset robot_local_state.equality singleton_conv unit.exhaust)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_add)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_SIG) Collect_mono finite.emptyI finite.insertI not_finite_existsD 
        rev_finite_subset robot_local_state.equality singleton_conv unit.exhaust)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_constant_finite_states)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_constant_finite_states)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    using card_1 by (smt (verit, ccfv_SIG) Collect_cong One_nat_def of_nat_1)

  have sum_2: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state. ?f2 v\<^sub>0) = 4 / 9"
    apply (subst infsum_cdiv_left)
    apply (rule summable_on_add)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_SIG) Collect_mono finite.emptyI finite.insertI not_finite_existsD 
        rev_finite_subset robot_local_state.equality singleton_conv unit.exhaust)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_add)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_SIG) Collect_mono finite.emptyI finite.insertI not_finite_existsD 
        rev_finite_subset robot_local_state.equality singleton_conv unit.exhaust)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_constant_finite_states)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_constant_finite_states)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    using card_2 by (simp add: card_0_singleton)

  have sum_3: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state. ?f3 v\<^sub>0) = 4 / 9"
    apply (subst infsum_cdiv_left)
    apply (rule summable_on_add)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_SIG) Collect_mono finite.emptyI finite.insertI not_finite_existsD 
        rev_finite_subset robot_local_state.equality singleton_conv unit.exhaust)
    apply (rule infsum_constant_finite_states_summable)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_add)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_SIG) Collect_mono finite.emptyI finite.insertI not_finite_existsD 
        rev_finite_subset robot_local_state.equality singleton_conv unit.exhaust)
    apply (rule infsum_constant_finite_states_summable)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_constant_finite_states)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_constant_finite_states)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
  using card_3 by (smt (verit, ccfv_SIG) Collect_cong One_nat_def of_nat_1)

  show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state. ?f1 v\<^sub>0 + ?f2 v\<^sub>0 + ?f3 v\<^sub>0) * 3 = 8"
    apply (subst infsum_add)
    apply (rule summable_on_add)
    using summable_1 apply blast
    using summable_2 apply blast
    using summable_3 apply blast
    apply (subst infsum_add)
    using summable_1 apply blast
    using summable_2 apply blast
    by (simp add: sum_1 sum_2 sum_3)
qed
  
lemma believe_2_simp: "(((init \<parallel> scale_door) ; move_right) \<parallel> scale_door) = 
  prel_of_rfrel believe_2"
  apply (simp add: move_right_1_simp believe_2_def)
  apply (simp add: scale_door_def door_def prel_defs)
  apply (simp add: move_right_1_dist)
  apply (simp add: move_right_1_def dist_defs)
  apply (expr_auto add: rel)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (simp add: ring_distribs(2))
  apply (subst fun_eq_iff, rule allI)
  apply (auto)
  by (simp add: believe_2_sum)+

lemma believe_2_dist: "rfrel_of_prel (prel_of_rfrel believe_2) = believe_2"
proof -
  have summable_1: "(\<lambda>s::robot_local_state. (2::\<real>) * (if bel\<^sub>v s = (0::\<nat>) then 1::\<real> else (0::\<real>)) / (3::\<real>)) 
        summable_on UNIV"
    apply (rule summable_on_cdiv_left)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    by (smt (z3) Collect_mono card_0_eq finite.insertI infinite_arbitrarily_large rev_finite_subset 
      robot_local_state.surjective singleton_conv unit.exhaust)

  have summable_2: "(\<lambda>s::robot_local_state. (if bel\<^sub>v s = Suc (0::\<nat>) then 1::\<real> else (0::\<real>)) / (6::\<real>)) 
      summable_on UNIV"
    apply (rule summable_on_cdiv_left)
    apply (rule infsum_constant_finite_states_summable)
    by (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)

  have summable_3: "(\<lambda>s::robot_local_state. (if bel\<^sub>v s = (2::\<nat>) then 1::\<real> else (0::\<real>)) / (6::\<real>)) 
      summable_on UNIV"
    apply (rule summable_on_cdiv_left)
    apply (rule infsum_constant_finite_states_summable)
    by (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)

  have sum_1: "(\<Sum>\<^sub>\<infinity>s::robot_local_state. (2::\<real>) * (if bel\<^sub>v s = (0::\<nat>) then 1::\<real> else (0::\<real>)) / (3::\<real>)) = 2/3"
    apply (subst infsum_cdiv_left)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (subst infsum_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (subst infsum_constant_finite_states)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (simp)
    apply (subst card_1_singleton_iff)
    apply (rule_tac x = "\<lparr>bel\<^sub>v = (0::\<nat>)\<rparr>" in exI)
    by force

  have sum_2: "(\<Sum>\<^sub>\<infinity>s::robot_local_state. (if bel\<^sub>v s = Suc (0::\<nat>) then 1::\<real> else (0::\<real>)) / (6::\<real>)) = 1/6"
    apply (subst infsum_cdiv_left)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (subst infsum_constant_finite_states)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (simp)
    apply (subst card_1_singleton_iff)
    apply (rule_tac x = "\<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr>" in exI)
    by force

  have sum_3: "(\<Sum>\<^sub>\<infinity>s::robot_local_state. (if bel\<^sub>v s = (2::\<nat>) then 1::\<real> else (0::\<real>)) / (6::\<real>)) = 1/6"
    apply (subst infsum_cdiv_left)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (subst infsum_constant_finite_states)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (simp)
    apply (subst card_1_singleton_iff)
    apply (rule_tac x = "\<lparr>bel\<^sub>v = (2::\<nat>)\<rparr>" in exI)
  by force

  show ?thesis
    apply (simp add: believe_2_def)
    apply (subst prel_of_rfrel_inverse)
    apply (expr_auto add: dist_defs)
    apply (subst infsum_add)
    apply (subst summable_on_add)
    apply (simp add: summable_1)
    apply (simp add: summable_2)
    apply (simp)
    apply (simp add: summable_3)
    apply (subst infsum_add)
    apply (simp add: summable_1)
    apply (simp add: summable_2)
    by (simp add: sum_1 sum_2 sum_3)+
qed

lemma move_right_2_simp: 
  "((((init \<parallel> scale_door) ; move_right) \<parallel> scale_door) ; move_right) = prel_of_rfrel move_right_2"
  apply (simp add: believe_2_simp)
  apply (simp add: move_right_2_def move_right_def)
  apply (simp add: prel_defs)
  apply (simp add: believe_2_dist)
  apply (subst prel_set_conv_assign)
  apply (simp add: believe_2_def)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (expr_auto add: rel)
  apply (simp_all add: ring_distribs(2))
  apply (simp add: mult.assoc)+
  apply (subst conditional_conds_conj)+
  defer
  apply (simp add: mult.assoc)+
  apply (subst conditional_conds_conj)+
  defer
  apply (simp add: mult.assoc)+
  apply (subst conditional_conds_conj)+
  defer
  apply (simp add: mult.assoc)+
  apply (subst conditional_conds_conj)+
     defer 
proof -
  let ?lhs_f = "\<lambda>v\<^sub>0::robot_local_state. (2::\<real>) *
       (if bel\<^sub>v v\<^sub>0 = (0::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr> then 1::\<real>
        else (0::\<real>)) / (3::\<real>) +
       (if bel\<^sub>v v\<^sub>0 = Suc (0::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr> then 1::\<real>
        else (0::\<real>)) / (6::\<real>) +
       (if bel\<^sub>v v\<^sub>0 = (2::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr> then 1::\<real>
        else (0::\<real>)) / (6::\<real>)"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state. ?lhs_f v\<^sub>0)"

  have f1: "\<forall>v\<^sub>0. (bel\<^sub>v v\<^sub>0 = (0::\<nat>) \<and> (v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr>)) = 
      (\<lparr>bel\<^sub>v = 0::\<nat>\<rparr> = v\<^sub>0)"
    by auto
  have f2: "\<forall>v\<^sub>0. \<not>(bel\<^sub>v v\<^sub>0 = Suc (0::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr>)"
    apply (auto)
    by (metis n_not_Suc_n robot_local_state.select_convs(1) robot_local_state.surjective 
        robot_local_state.update_convs(1))
  have f3: "\<forall>v\<^sub>0. \<not>(bel\<^sub>v v\<^sub>0 = (2::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr>)"
    apply (auto)
    by (metis n_not_Suc_n robot_local_state.select_convs(1) robot_local_state.surjective 
        robot_local_state.update_convs(1))
  show "?lhs * (3::\<real>) = (2::\<real>)"
    apply (simp add: f1 f2 f3)
    apply (subst infsum_cdiv_left)
    apply (rule summable_on_cmult_right)
    apply (simp add: infsum_singleton_summable)
    apply (subst infsum_cmult_right)
    apply (simp add: infsum_singleton_summable)
    apply (subst infsum_constant_finite_states)
    by (simp)+
next
  let ?lhs_f = "\<lambda>v\<^sub>0::robot_local_state. (2::\<real>) *
       (if bel\<^sub>v v\<^sub>0 = (0::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v =  (0::\<nat>)\<rparr> then 1::\<real>
        else (0::\<real>)) / (3::\<real>) +
       (if bel\<^sub>v v\<^sub>0 = Suc (0::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v =  (0::\<nat>)\<rparr> then 1::\<real>
        else (0::\<real>)) / (6::\<real>) +
       (if bel\<^sub>v v\<^sub>0 = (2::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v =  (0::\<nat>)\<rparr> then 1::\<real>
        else (0::\<real>)) / (6::\<real>)"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state. ?lhs_f v\<^sub>0)"

  have f1: "\<forall>v\<^sub>0. \<not>(bel\<^sub>v v\<^sub>0 = (0::\<nat>) \<and> (v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = (0::\<nat>)\<rparr>))"
    apply (auto)
    by (metis n_not_Suc_n robot_local_state.select_convs(1) robot_local_state.surjective 
        robot_local_state.update_convs(1))
  have f2: "\<forall>v\<^sub>0. \<not>(bel\<^sub>v v\<^sub>0 = Suc (0::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = (0::\<nat>)\<rparr>)"
    apply (auto)
    by (metis nat.distinct(1) robot_local_state.select_convs(1) robot_local_state.surjective 
        robot_local_state.update_convs(1))
  have f3: "\<forall>v\<^sub>0. (bel\<^sub>v v\<^sub>0 = (2::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = (0::\<nat>)\<rparr>)  = 
      (\<lparr>bel\<^sub>v = 2::\<nat>\<rparr> = v\<^sub>0)"
    by (auto)
  show "?lhs * (6::\<real>) = (1::\<real>)"
    apply (simp add: f1 f2 f3)
    apply (subst infsum_cdiv_left)
    apply (simp add: infsum_singleton_summable)
    apply (subst infsum_constant_finite_states)
    by (simp)+
next
let ?lhs_f = "\<lambda>v\<^sub>0::robot_local_state. (2::\<real>) *
       (if bel\<^sub>v v\<^sub>0 = (0::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = (2::\<nat>)\<rparr> then 1::\<real>
        else (0::\<real>)) / (3::\<real>) +
       (if bel\<^sub>v v\<^sub>0 = Suc (0::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = (2::\<nat>)\<rparr> then 1::\<real>
        else (0::\<real>)) / (6::\<real>) +
       (if bel\<^sub>v v\<^sub>0 = (2::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = (2::\<nat>)\<rparr> then 1::\<real>
        else (0::\<real>)) / (6::\<real>)"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state. ?lhs_f v\<^sub>0)"

  have f1: "\<forall>v\<^sub>0. \<not>(bel\<^sub>v v\<^sub>0 = (0::\<nat>) \<and> (v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = (2::\<nat>)\<rparr>))"
    apply (auto)
    by (metis n_not_Suc_n numeral_2_eq_2 robot_local_state.select_convs(1) 
        robot_local_state.surjective robot_local_state.update_convs(1))
  have f2: "\<forall>v\<^sub>0. (bel\<^sub>v v\<^sub>0 = Suc (0::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = (2::\<nat>)\<rparr>) =  
      (\<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr> = v\<^sub>0)"
    by (auto)
  have f3: "\<forall>v\<^sub>0. \<not>(bel\<^sub>v v\<^sub>0 = (2::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = (2::\<nat>)\<rparr>)"
    apply (auto)
    by (metis robot_local_state.select_convs(1) robot_local_state.surjective 
        robot_local_state.update_convs(1) zero_neq_numeral)
  show "?lhs * (6::\<real>) = (1::\<real>)"
    apply (simp add: f1 f2 f3)
    apply (subst infsum_cdiv_left)
    apply (simp add: infsum_singleton_summable)
    apply (subst infsum_constant_finite_states)
    by (simp)+
next
  fix bel
  assume a1: "\<not> bel = Suc (0::\<nat>)"
  assume a2: "(0::\<nat>) < bel"
  assume a3: "\<not> bel = (2::\<nat>)"

  have f1: "\<forall>v\<^sub>0. \<not>(bel\<^sub>v v\<^sub>0 = (0::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = bel\<rparr>)"
    apply (auto)
    by (metis a1 robot_local_state.select_convs(1) robot_local_state.surjective 
        robot_local_state.update_convs(1))
  have f2: "\<forall>v\<^sub>0. \<not>(bel\<^sub>v v\<^sub>0 = Suc (0::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = bel\<rparr>)"
    apply (auto)
    by (metis a3 numeral_2_eq_2 robot_local_state.select_convs(1) robot_local_state.surjective 
        robot_local_state.update_convs(1))
  have f3: "\<forall>v\<^sub>0. \<not>(bel\<^sub>v v\<^sub>0 = (2::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = bel\<rparr>)"
    apply (auto)
    by (metis a2 nat_neq_iff robot_local_state.select_convs(1) robot_local_state.surjective 
        robot_local_state.update_convs(1))

  show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state.
          (2::\<real>) * (if bel\<^sub>v v\<^sub>0 = (0::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = bel\<rparr> then 1::\<real>
           else (0::\<real>)) /
          (3::\<real>) +
          (if bel\<^sub>v v\<^sub>0 = Suc (0::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = bel\<rparr> then 1::\<real>
           else (0::\<real>)) /
          (6::\<real>) +
          (if bel\<^sub>v v\<^sub>0 = (2::\<nat>) \<and> v\<^sub>0\<lparr>bel\<^sub>v := Suc (bel\<^sub>v v\<^sub>0) mod (3::\<nat>)\<rparr> = \<lparr>bel\<^sub>v = bel\<rparr> then 1::\<real>
           else (0::\<real>)) /
          (6::\<real>)) =
       (0::\<real>) "
    by (simp add: f1 f2 f3)
qed


lemma move_right_2_dist: "rfrel_of_prel (prel_of_rfrel move_right_2) = move_right_2"
proof -
  have summable_1: "(\<lambda>s::robot_local_state. (if bel\<^sub>v s = (0::\<nat>) then 1::\<real> else (0::\<real>)) / (6::\<real>)) 
        summable_on UNIV"
    apply (rule summable_on_cdiv_left)
    apply (rule infsum_constant_finite_states_summable)
    by (smt (z3) Collect_mono card_0_eq finite.insertI infinite_arbitrarily_large rev_finite_subset 
      robot_local_state.surjective singleton_conv unit.exhaust)

  have summable_2: "(\<lambda>s::robot_local_state. (2::\<real>) * (if bel\<^sub>v s = Suc (0::\<nat>) then 1::\<real> else (0::\<real>)) / (3::\<real>)) 
      summable_on UNIV"
    apply (rule summable_on_cdiv_left)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    by (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)

  have summable_3: "(\<lambda>s::robot_local_state. (if bel\<^sub>v s = (2::\<nat>) then 1::\<real> else (0::\<real>)) / (6::\<real>)) 
      summable_on UNIV"
    apply (rule summable_on_cdiv_left)
    apply (rule infsum_constant_finite_states_summable)
    by (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)

  have sum_1: "(\<Sum>\<^sub>\<infinity>s::robot_local_state. (if bel\<^sub>v s = (0::\<nat>) then 1::\<real> else (0::\<real>)) / (6::\<real>)) = 1/6"
    apply (subst infsum_cdiv_left)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (subst infsum_constant_finite_states)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (simp)
    apply (subst card_1_singleton_iff)
    apply (rule_tac x = "\<lparr>bel\<^sub>v = (0::\<nat>)\<rparr>" in exI)
    by force

  have sum_2: "(\<Sum>\<^sub>\<infinity>s::robot_local_state. (2::\<real>) * (if bel\<^sub>v s = Suc (0::\<nat>) then 1::\<real> else (0::\<real>)) / (3::\<real>)) = 2/3"
    apply (subst infsum_cdiv_left)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (subst infsum_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (subst infsum_constant_finite_states)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (simp)
    apply (subst card_1_singleton_iff)
    apply (rule_tac x = "\<lparr>bel\<^sub>v = Suc (0::\<nat>)\<rparr>" in exI)
    by force

  have sum_3: "(\<Sum>\<^sub>\<infinity>s::robot_local_state. (if bel\<^sub>v s = (2::\<nat>) then 1::\<real> else (0::\<real>)) / (6::\<real>)) = 1/6"
    apply (subst infsum_cdiv_left)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (subst infsum_constant_finite_states)
    apply (smt (z3) Collect_mono finite.emptyI finite.insertI rev_finite_subset 
      robot_local_state.equality singleton_conv unit.exhaust)
    apply (simp)
    apply (subst card_1_singleton_iff)
    apply (rule_tac x = "\<lparr>bel\<^sub>v = (2::\<nat>)\<rparr>" in exI)
  by force

  show ?thesis
    apply (simp add: move_right_2_def)
    apply (subst prel_of_rfrel_inverse)
    apply (expr_auto add: dist_defs)
    apply (subst infsum_add)
    apply (subst summable_on_add)
    apply (simp add: summable_1)
    apply (simp add: summable_2)
    apply (simp)
    apply (simp add: summable_3)
    apply (subst infsum_add)
    apply (simp add: summable_1)
    apply (simp add: summable_2)
    by (simp add: sum_1 sum_2 sum_3)+
qed

lemma believe_3_sum: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state.
          (if bel\<^sub>v v\<^sub>0 = (0::\<nat>) then 1::\<real> else (0::\<real>)) *
          ((3::\<real>) * (if (0::\<nat>) < bel\<^sub>v v\<^sub>0 \<and> \<not> bel\<^sub>v v\<^sub>0 = (2::\<nat>) then 1::\<real> else (0::\<real>)) + (1::\<real>)) / (6::\<real>) 
        +  (2::\<real>) * (if bel\<^sub>v v\<^sub>0 = Suc (0::\<nat>) then 1::\<real> else (0::\<real>)) *
          ((3::\<real>) * (if (0::\<nat>) < bel\<^sub>v v\<^sub>0 \<and> \<not> bel\<^sub>v v\<^sub>0 = (2::\<nat>) then 1::\<real> else (0::\<real>)) + (1::\<real>)) /
          (3::\<real>) +  (if bel\<^sub>v v\<^sub>0 = (2::\<nat>) then 1::\<real> else (0::\<real>)) *
          ((3::\<real>) * (if (0::\<nat>) < bel\<^sub>v v\<^sub>0 \<and> \<not> bel\<^sub>v v\<^sub>0 = (2::\<nat>) then 1::\<real> else (0::\<real>)) + (1::\<real>)) /
          (6::\<real>)) = 3"
  apply (simp add: ring_distribs(1))
  apply (subst mult.assoc[symmetric,where b = "3"])
  apply (subst mult.commute[where b = "3"])
  apply (subst mult.assoc)
  apply (subst mult.assoc[symmetric,where b = "3"])
  apply (subst mult.commute[where b = "3"])
  apply (subst mult.assoc)
  apply (subst conditional_conds_conj)+
proof -
  let ?f1 = "(\<lambda>v\<^sub>0::robot_local_state. 
    ((3::\<real>) * (if bel\<^sub>v v\<^sub>0 = (0::\<nat>) \<and> (0::\<nat>) < bel\<^sub>v v\<^sub>0 \<and> \<not> bel\<^sub>v v\<^sub>0 = (2::\<nat>) then 1::\<real> else (0::\<real>)) +
        (if bel\<^sub>v v\<^sub>0 = (0::\<nat>) then 1::\<real> else (0::\<real>))) / (6::\<real>))"
  let ?f2 = "(\<lambda>v\<^sub>0::robot_local_state. 
    ((6::\<real>) * (if bel\<^sub>v v\<^sub>0 = Suc (0::\<nat>) \<and> (0::\<nat>) < bel\<^sub>v v\<^sub>0 \<and> \<not> bel\<^sub>v v\<^sub>0 = (2::\<nat>) then 1::\<real> else (0::\<real>)) +
        (2::\<real>) * (if bel\<^sub>v v\<^sub>0 = Suc (0::\<nat>) then 1::\<real> else (0::\<real>))) /
       (3::\<real>))"
  let ?f3 = "(\<lambda>v\<^sub>0::robot_local_state. 
    ((3::\<real>) * (if bel\<^sub>v v\<^sub>0 = (2::\<nat>) \<and> (0::\<nat>) < bel\<^sub>v v\<^sub>0 \<and> \<not> bel\<^sub>v v\<^sub>0 = (2::\<nat>) then 1::\<real> else (0::\<real>)) +
        (if bel\<^sub>v v\<^sub>0 = (2::\<nat>) then 1::\<real> else (0::\<real>))) /
       (6::\<real>))"
  have summable_1: "?f1 summable_on UNIV"
    apply (rule summable_on_cdiv_left)
    apply (rule summable_on_add)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_SIG) Collect_mono finite.emptyI finite.insertI not_finite_existsD 
        rev_finite_subset robot_local_state.equality singleton_conv unit.exhaust)
    apply (rule infsum_constant_finite_states_summable)
    by (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
  have summable_2: "?f2 summable_on UNIV"
    apply (rule summable_on_cdiv_left)
    apply (rule summable_on_add)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_SIG) Collect_mono finite.emptyI finite.insertI not_finite_existsD 
        rev_finite_subset robot_local_state.equality singleton_conv unit.exhaust)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    by (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
  have summable_3: "?f3 summable_on UNIV"
    apply (rule summable_on_cdiv_left)
    apply (rule summable_on_add)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_SIG) Collect_mono finite.emptyI finite.insertI not_finite_existsD 
        rev_finite_subset robot_local_state.equality singleton_conv unit.exhaust)
    apply (rule infsum_constant_finite_states_summable)
    by (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)

  have card_1: "card {s::robot_local_state. bel\<^sub>v s = 0} = Suc (0)"
    apply (subst card_1_singleton_iff)
    by (smt (verit, del_insts) Collect_cong robot_local_state.equality robot_local_state.select_convs(1) 
      singleton_conv unit.exhaust)
  have card_2: "card {s::robot_local_state. bel\<^sub>v s = Suc (0)} = Suc (0)"
    apply (subst card_1_singleton_iff)
    by (smt (verit, del_insts) Collect_cong robot_local_state.equality robot_local_state.select_convs(1) 
      singleton_conv unit.exhaust)
  have card_2': "card {s::robot_local_state. bel\<^sub>v s = Suc (0::\<nat>) \<and> (0::\<nat>) < bel\<^sub>v s \<and> \<not> bel\<^sub>v s = (2::\<nat>)} = Suc 0"
    apply (subst card_1_singleton_iff)
    by (metis (mono_tags, lifting) Collect_cong card_1_singleton_iff card_2 less_Suc0 n_not_Suc_n numeral_2_eq_2)
  have card_3: "card {s::robot_local_state. bel\<^sub>v s = 2} = Suc (0)"
    apply (subst card_1_singleton_iff)
    by (smt (verit, del_insts) Collect_cong robot_local_state.equality robot_local_state.select_convs(1) 
      singleton_conv unit.exhaust)
  have card_3': "card {s::robot_local_state. bel\<^sub>v s = (2::\<nat>) \<and> (0::\<nat>) < bel\<^sub>v s \<and> \<not> bel\<^sub>v s = (2::\<nat>)} = 0"
    by (simp add: card_0_singleton)

  have f1: "\<forall>v\<^sub>0. \<not>(bel\<^sub>v v\<^sub>0 = (0::\<nat>) \<and> (0::\<nat>) < bel\<^sub>v v\<^sub>0 \<and> \<not> bel\<^sub>v v\<^sub>0 = (2::\<nat>))"
    by auto
  have sum_1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state. ?f1 v\<^sub>0) = 1 / 6"
    apply (subst infsum_cdiv_left)
    apply (rule summable_on_add)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_SIG) Collect_mono finite.emptyI finite.insertI not_finite_existsD 
        rev_finite_subset robot_local_state.equality singleton_conv unit.exhaust)
    apply (rule infsum_constant_finite_states_summable)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (simp add: f1)
    apply (subst infsum_constant_finite_states)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    using card_1 by (smt (verit, ccfv_SIG) Collect_cong One_nat_def of_nat_1)

  have sum_2: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state. ?f2 v\<^sub>0) = 8/3"
    apply (subst infsum_cdiv_left)
    apply (rule summable_on_add)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_SIG) Collect_mono finite.emptyI finite.insertI not_finite_existsD 
        rev_finite_subset robot_local_state.equality singleton_conv unit.exhaust)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_add)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_SIG) Collect_mono finite.emptyI finite.insertI not_finite_existsD 
        rev_finite_subset robot_local_state.equality singleton_conv unit.exhaust)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_constant_finite_states)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_constant_finite_states)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    by (simp add: card_2 card_2')

  have sum_3: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state. ?f3 v\<^sub>0) = 1 / 6"
    apply (subst infsum_cdiv_left)
    apply (rule summable_on_add)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_SIG) Collect_mono finite.emptyI finite.insertI not_finite_existsD 
        rev_finite_subset robot_local_state.equality singleton_conv unit.exhaust)
    apply (rule infsum_constant_finite_states_summable)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_add)
    apply (rule summable_on_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (smt (verit, ccfv_SIG) Collect_mono finite.emptyI finite.insertI not_finite_existsD 
        rev_finite_subset robot_local_state.equality singleton_conv unit.exhaust)
    apply (rule infsum_constant_finite_states_summable)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_cmult_right)
    apply (rule infsum_constant_finite_states_summable)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_constant_finite_states)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    apply (subst infsum_constant_finite_states)
    apply (metis (mono_tags, lifting) card.infinite card_1_singleton nat.simps(3) not_finite_existsD 
        robot_local_state.equality unit.exhaust)
    by (simp add: card_3 card_3')

  show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::robot_local_state. ?f1 v\<^sub>0 + ?f2 v\<^sub>0 + ?f3 v\<^sub>0) = 3"
    apply (subst infsum_add)
    apply (rule summable_on_add)
    using summable_1 apply blast
    using summable_2 apply blast
    using summable_3 apply blast
    apply (subst infsum_add)
    using summable_1 apply blast
    using summable_2 apply blast
    by (simp add: sum_1 sum_2 sum_3)
qed

lemma believe_3_simp: "robot_localisation = prel_of_rfrel believe_3"
  apply (simp add: robot_localisation_def)
  apply (simp add: move_right_2_simp believe_3_def)
  apply (simp add: scale_wall_def door_def prel_defs)
  apply (simp add: move_right_2_dist)
  apply (simp add: move_right_2_def dist_defs)
  apply (expr_auto add: rel)
  apply (rule HOL.arg_cong[where f="prel_of_rfrel"])
  apply (simp add: ring_distribs(2))
  apply (subst fun_eq_iff, rule allI)
  apply (auto)
  by (simp add: believe_3_sum)+

end
