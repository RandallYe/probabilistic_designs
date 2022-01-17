section \<open> Iverson Bracket examples from Jim's ``Uncertainty and Probabilistic UTP''\<close>

theory utp_iverson_bracket_examples
  imports "HOL.Series" "HOL-Analysis.Infinite_Sum" "utp_iverson_bracket" 
begin 

(* This unbundle is necessary in order to make the term below correct. 
Otherwise, with the imported Series, the term below is not syntactically correct. *)
unbundle UTP_Syntax
term "(($r\<^sup>> = C) \<and> ($a\<^sup>> = $a\<^sup><))\<^sub>e"

declare [[show_types]]

lemma Example_2: "(\<Sum>i::int \<in> {1..4}. (2*i+1)) = 3 + 5 + 7 + 9"
  apply (subgoal_tac "(\<Sum>i::int \<in> {1..4}. (2*i+1)) = 
    (\<Sum>i::int \<in> ({1}). (2*i+1)) + (\<Sum>i::int \<in> ({2..4}). (2*i+1))")
  defer
  using simp_from_to apply auto[1]
  apply (subgoal_tac "(\<Sum>i::int \<in> ({2..4}). (2*i+1)) = 
    (\<Sum>i::int \<in> ({2}). (2*i+1)) + (\<Sum>i::int \<in> ({3..4}). (2*i+1))")
  defer
  using simp_from_to apply auto[1]
  apply (subgoal_tac "(\<Sum>i::int \<in> {3..4}. (2*i+1)) = 
    (\<Sum>i::int \<in> ({3}). (2*i+1)) + (\<Sum>i::int \<in> ({4}). (2*i+1))")
  defer
  using simp_from_to apply auto[1]
  by (auto)

term "(\<lbrakk>(\<lambda>i. (i \<in> {1..4}))\<rbrakk>\<^sub>\<I> i)"
(*
lemma Example_2_iverson_bracket: 
  (* shows "(\<Sum>\<^sub>\<infinity>i::int. ((2*i+1)*(\<lbrakk>(\<lambda>i. i \<in> {1::int..4})\<rbrakk>\<^sub>\<I> i))) = 3 + 5 + 7 + 9" *)
  shows "(\<Sum>i::int. ((2*i+1)*(\<lbrakk>(\<lambda>i. i \<in> {1::int..4})\<rbrakk>\<^sub>\<I> i))) = 3 + 5 + 7 + 9"
proof -
  have "(\<Sum>i::int. ((2*i+1)*(\<lbrakk>(\<lambda>i. i \<in> {1::int..4})\<rbrakk>\<^sub>\<I> i))) = 
    (\<Sum>i\<in> ({i. i \<in> {1..4}} \<union> {i. i \<notin> {1..4}}). ((2*i+1)*(\<lbrakk>(\<lambda>i. i \<in> {1::int..4})\<rbrakk>\<^sub>\<I> i)))"
qed
*)

(*
lemma Example_2_iverson_bracket': 
  assumes "finite (A::int set)" "{1..4} \<subseteq> A"
  shows "(\<Sum>i\<in>A. ((2*i+1)*(\<lbrakk>(\<lambda>i. ((1 \<le> i) \<and> (i \<le> 4)))\<rbrakk>\<^sub>\<I> i))) = 3 + 5 + 7 + 9"
  apply (simp add: expr_defs)
  sorry
 
*)
(*
lemma Example_3_double_counting_rule:
  "(\<Sum>i\<in>A. P i) = (\<Sum>i|True. \<lbrakk>P\<rbrakk>\<^sub>\<I>)\<^sub>e"
  oops
*)
term "f sums a"
term "(\<lambda>n. \<Sum>i<n. f i) \<longlonglongrightarrow> s"
term "suminf"
term "\<Sum> f"

term "(\<Sum>\<^sub>\<infinity> n|True. f n)"

datatype Attacker = C | D
datatype Status = S | F

alphabet RA = 
  r:: Attacker
  a:: Status

term "(($r\<^sup>> = C) \<and> ($a\<^sup>> = $a\<^sup><))\<^sub>e"
term "(($r\<^sup>> = C) \<and> ($a\<^sup>> = $a\<^sup><))\<^sub>u"
(* r := C *)
definition "r0 = \<lbrakk>(($r\<^sup>> = C) \<and> ($a\<^sup>> = $a\<^sup><))\<^sub>e\<rbrakk>\<^sub>\<I>"
(* r := D *)
definition "r1 = \<lbrakk>(($r\<^sup>> = D) \<and> ($a\<^sup>> = $a\<^sup><))\<^sub>e\<rbrakk>\<^sub>\<I>"
expr_ctr r0 r1
(* a := S *)
definition "a0 = \<lbrakk>(($r\<^sup>> = $r\<^sup><) \<and> ($a\<^sup>> = S))\<^sub>e\<rbrakk>\<^sub>\<I>"
expr_ctr a0
(* a := F *)
definition "a1 = \<lbrakk>(($r\<^sup>> = $r\<^sup><) \<and> ($a\<^sup>> = F))\<^sub>e\<rbrakk>\<^sub>\<I>"
(*expr_ctr a1*)
full_exprs
(* b01 = (if 1/2 then a := S else a := F) *)
term "(0.5*a0 + 0.5*@a1)\<^sub>e"
term "(0.5*a0 + 0.5*a1)\<^sub>e"
term "(0.5*@a0 + 0.5*@a1)\<^sub>e"
definition "b01 = (0.5*a0 + 0.5*@a1)\<^sub>e"
term "(f+0)\<^sub>e"
term "\<lambda>s. (f s + 0)"
expr_ctr b01
term "r' = C"
term "(c' = $a\<^sup><)"
term "(\<Sum>\<^sub>\<infinity> r'. (\<lbrakk>((r' = C) \<and> (c' = $a\<^sup><))\<^sub>e\<rbrakk>\<^sub>\<I>))\<^sub>e"
(* b0 = ( r := C ; if 1=2 then a := S else a := F ) *)
(* Manual substitution *)
term "
  (\<Sum>\<^sub>\<infinity> r'. \<Sum>\<^sub>\<infinity> a'. 
    (
      \<lbrakk>((r' = C) \<and> (a' = $a\<^sup><))\<^sub>e\<rbrakk>\<^sub>\<I> 
      * 
      ( 
        0.5 * \<lbrakk>(($r\<^sup>> = r') \<and> ($a\<^sup>> = S))\<^sub>e\<rbrakk>\<^sub>\<I> + 
        0.5 * \<lbrakk>(($r\<^sup>> = $r\<^sup><) \<and> ($a\<^sup>> = F))\<^sub>e\<rbrakk>\<^sub>\<I>
      )
    )
  )\<^sub>e"
term "((($r\<^sup>> = C) \<and> ($a\<^sup>> = $a\<^sup><))\<lbrakk>r'/r\<^sup>>\<rbrakk>)\<^sub>e"
term "(r0\<lbrakk>r'/r\<^sup>>\<rbrakk>)\<^sub>e"
term "(r0\<lbrakk>r',a'/r\<^sup>>,a\<^sup><\<rbrakk>)\<^sub>e"
term "(b01\<lbrakk>r',a'/r\<^sup>>,a\<^sup><\<rbrakk>)\<^sub>e"

definition "b0 = (\<Sum>\<^sub>\<infinity> r'. \<Sum>\<^sub>\<infinity> a'. ((r0\<lbrakk>r',a'/r\<^sup>>,a\<^sup><\<rbrakk>) * (b01\<lbrakk>r',a'/r\<^sup>>,a\<^sup><\<rbrakk>)))\<^sub>e"
expr_ctr b0

definition "b11 = (3/10*a0 + 7/10*@a1)\<^sub>e"
expr_ctr b11
definition "b1 = (\<Sum>\<^sub>\<infinity> r'. \<Sum>\<^sub>\<infinity> a'. ((r1\<lbrakk>r',a'/r\<^sup>>,a\<^sup><\<rbrakk>) * (b11\<lbrakk>r',a'/r\<^sup>>,a\<^sup><\<rbrakk>)))\<^sub>e"
expr_ctr b1

definition "DWTA = ((3/5)*b0+(2/5)*b1)\<^sub>e"

end
