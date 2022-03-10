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

end
