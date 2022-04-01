section \<open> Probabilistic relation programming laws \<close>

theory topological_space_study
  imports 
        "HOL-Analysis.Infinite_Sum"
begin 
declare [[show_types]]

term "inj_on"
term "Sigma"
thm "sum.cartesian_product"
term "open"
term "at_top"
term "finite_subsets_at_top"
term "a::('a::linorder)"
term "sequentially"
term "nhds"
term "at x within S"
term "at x"
term "at_bot"
term "principal"
term "finite_subsets_at_top"
term "at_left"
term "at_right"

(* The summation of f over possibly infinite sets A is x, *)
(* Definition: lim (A tendsto infinity) (sum f A tendsto x)
  Ordered by set inclusion. A1 \<subseteq> A2
*)
term "infsum f A = x" (* Lim (finite_subsets_at_top A) (sum f) *)
(* equal to the summation of f converges to x in a filter: (finite_subsets_at_top A) *)
term "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A)"

term "(\<forall>S. open S \<longrightarrow> x \<in> S \<longrightarrow> eventually (\<lambda>X. (sum f) X \<in> S) (finite_subsets_at_top A))"

term "(
\<forall>S. open S \<longrightarrow> 
    x \<in> S \<longrightarrow> 
      (\<exists>X. finite X \<and> X \<subseteq> A \<and> 
           (\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> A \<longrightarrow> 
              (sum f Y \<in> S))))"

(* tendsto definition: a function f converges to l on a filter F *)
term "(f \<longlongrightarrow> l) F"
(* *) 
term "filterlim f (nhds l) F"
(* equal to below: *)
term "(filtermap f F) \<le> (nhds l)"
term "filterlim"

thm "subsetI"
thm "mem_Collect_eq"

end