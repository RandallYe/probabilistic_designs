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

subsection \<open> Example - Experiment with state space \<close>
datatype color = Red | Green | Yellow
alphabet StColor = 
  c :: color

term "{s. P s}"
term "{s. P s = (1::\<real>)}"
term "c\<^sub>v"
term "$\<^bold>v\<^sup>>"
term "$\<^bold>v\<^sup><"
term "get\<^bsub>c\<^esub>"
term "($c\<^sup>> = Red)\<^sub>e"
term "(($c\<^sup>> = Red) \<and> ($c\<^sup>< = Green))\<^sub>e"
term "(($c\<^sup>> = Red) \<and> ($c\<^sup>< = Green))\<^sub>u ::color\<leftrightarrow>color"

term "{(Green, Red)}"

(* {(Green, Red)} *)
definition red_green :: "StColor rel" where
"red_green = (($c\<^sup>> = Red) \<and> ($c\<^sup>< = Green))\<^sub>u"

(* {(Gree, Red), (Gree, Yellow)} *)
definition red_green2 :: "StColor rel" where
"red_green2 = ((($c\<^sup>> = Red) \<and> ($c\<^sup>< = Green)) \<or> (($c\<^sup>> = Yellow) \<and> ($c\<^sup>< = Green)))\<^sub>u"

term "get\<^bsub>c\<^esub> s"

lemma "{\<s>::StColor \<times> StColor. c\<^sub>v (snd \<s>) = Red \<and> c\<^sub>v (fst \<s>) = Green}
  = (insert (THE s::StColor \<times> StColor. c\<^sub>v (snd \<s>) = Red \<and> c\<^sub>v (fst \<s>) = Green) {})"
  sorry

lemma "card red_green = 1"
  apply (simp add: red_green_def)
  apply (simp add: expr_defs lens_defs)
  sorry

lemma "card red_green2 = 1"
  apply (simp add: red_green2_def)
  apply (simp add: expr_defs lens_defs)
  sorry 

term "red_green \<Zcomp> red_green2"

subsection \<open> Example \<close>

datatype Attacker = C | D
datatype Status = S | F

alphabet RA = 
  r:: Attacker
  a:: Status

subsubsection \<open> Nondeterminism \<close>
(* \<or> in a non-probabilistic program is a union of set-based programs (P \<or> Q) *)
(* {s:: RA \<times> RA. r\<^sub>v (snd s) = C \<or> r\<^sub>v (snd s) = D} *)
term "((r := \<guillemotleft>C\<guillemotright>) \<or> (r := \<guillemotleft>D\<guillemotright>))"

subsubsection \<open> Semantics \<close>
term "(r := \<guillemotleft>C\<guillemotright>)"
term "\<lbrakk> \<lbrakk>(r := \<guillemotleft>C\<guillemotright>)\<rbrakk>\<^sub>P \<rbrakk>\<^sub>\<I>"

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
term "((1/2)*a0 + (1/2)*@a1)\<^sub>e"
term "((1/2)*a0 + (1/2)*a1)\<^sub>e"
term "((1/2)*@a0 + (1/2)*@a1)\<^sub>e"
definition "b01 = ((1/2)*a0 + (1/2)*@a1)\<^sub>e" 

term "(f+0)\<^sub>e"
term "\<lambda>s. (f s + 0)"
expr_ctr b01
term "r' = C"
term "(c' = $a\<^sup><)"
term "(\<Sum>\<^sub>\<infinity> r'. (\<lbrakk>((r' = C) \<and> (c' = $a\<^sup><))\<^sub>e\<rbrakk>\<^sub>\<I>))\<^sub>e"
(* b0 = ( r := C ; if 1/2 then a := S else a := F ) *)
(* Manual substitution *)
term "
  (\<Sum>\<^sub>\<infinity> r'. \<Sum>\<^sub>\<infinity> a'. 
    (
      \<lbrakk>((r' = C) \<and> (a' = $a\<^sup><))\<^sub>e\<rbrakk>\<^sub>\<I> 
      * 
      ( 
        (1/2) * \<lbrakk>(($r\<^sup>> = r') \<and> ($a\<^sup>> = S))\<^sub>e\<rbrakk>\<^sub>\<I> + 
        (1/2) * \<lbrakk>(($r\<^sup>> = $r\<^sup><) \<and> ($a\<^sup>> = F))\<^sub>e\<rbrakk>\<^sub>\<I>
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
(* b1 = ( r := D ; if 3/10 then a := S else a := F ) *)
definition "b1 = (\<Sum>\<^sub>\<infinity> r'. \<Sum>\<^sub>\<infinity> a'. ((r1\<lbrakk>r',a'/r\<^sup>>,a\<^sup><\<rbrakk>) * (b11\<lbrakk>r',a'/r\<^sup>>,a\<^sup><\<rbrakk>)))\<^sub>e"
expr_ctr b1

term "b01\<or> b11"

definition "DWTA = ((3/5)*b0+(2/5)*b1)\<^sub>e"

end
