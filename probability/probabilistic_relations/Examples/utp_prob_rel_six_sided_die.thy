section \<open> Throw two six-sided dice \<close>
text \<open>This example is from Section 15 of the Hehner's paper ``A probability perspective''.
The invariant of the program for an equal result is 
@{text "\<lbrakk>u' = v'\<rbrakk>\<^sub>\<I> * \<lbrakk>t' \<ge> t+1\<rbrakk>\<^sub>\<I> * (5/6)^(t'-t-1) * (1/6)"}.
This program cannot guarantee absolute termination (see Section 2.3 of ``
Abstraction Refinement and Proof for Probabilistic Systems''), but it is almost-certain 
termination.
The probability for non-termination is @{text "\<lbrakk>u' \<noteq> v'\<rbrakk>\<^sub>\<I> * \<lbrakk>t' \<ge> t+1\<rbrakk>\<^sub>\<I> * (5/6)^(t'-t)"}. When 
@{text "t'"} tends to @{text "\<infinity>"}, then the probability tends to 0.
\<close>

theory utp_prob_rel_six_sided_die
  imports 
    "UTP_prob_relations.utp_prob_rel" 
    "HOL-Analysis.Infinite_Set_Sum"
begin 

unbundle UTP_Syntax

declare [[show_types]]
subsection \<open> Knuth and Yao's algorithm to simulate six-sided die using a fair coin \<close>

datatype S = s1 | s2 | s3 | s4
datatype O = o0 | o1 | o2 | o3

subsubsection \<open> State space \<close>
alphabet state = time +
  c   :: bool
  s   :: S
  d   :: O

term "if"

definition step1:: "ureal \<Rightarrow> state prhfun" where
"step1 p  = if\<^sub>p \<guillemotleft>p\<guillemotright> then (s := s2) else (s := s3) ; t := t + 1"

definition step2:: "state prhfun" where
"step2 = if\<^sub>p 0.5 then (s := s1) else (s := s4) ; t := t + 1"

definition step3:: "state prhfun" where
"step3 = if\<^sub>p 0.5 then (s := s5) else (s := s6) ; t := t + 1"

term "while\<^sub>p (s\<^sup>< = s0 \<or> s\<^sup>< = s1 \<or> s\<^sup>< = s2)\<^sub>e do 
      (step1 ; (if\<^sub>c s\<^sup>< = s2 then step2 else pskip))
    od"

abbreviation "state_t_set t\<^sub>0 \<equiv> {
  \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 1, d2\<^sub>v = nat2td 1\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 1, d2\<^sub>v = nat2td 2\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 1, d2\<^sub>v = nat2td 3\<rparr>,
  \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 1, d2\<^sub>v = nat2td 4\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 1, d2\<^sub>v = nat2td 5\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 1, d2\<^sub>v = nat2td 6\<rparr>,
  \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 2, d2\<^sub>v = nat2td 1\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 2, d2\<^sub>v = nat2td 2\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 2, d2\<^sub>v = nat2td 3\<rparr>,
  \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 2, d2\<^sub>v = nat2td 4\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 2, d2\<^sub>v = nat2td 5\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 2, d2\<^sub>v = nat2td 6\<rparr>,
  \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 3, d2\<^sub>v = nat2td 1\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 3, d2\<^sub>v = nat2td 2\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 3, d2\<^sub>v = nat2td 3\<rparr>,
  \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 3, d2\<^sub>v = nat2td 4\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 3, d2\<^sub>v = nat2td 5\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 3, d2\<^sub>v = nat2td 6\<rparr>,
  \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 4, d2\<^sub>v = nat2td 1\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 4, d2\<^sub>v = nat2td 2\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 4, d2\<^sub>v = nat2td 3\<rparr>,
  \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 4, d2\<^sub>v = nat2td 4\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 4, d2\<^sub>v = nat2td 5\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 4, d2\<^sub>v = nat2td 6\<rparr>,
  \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 5, d2\<^sub>v = nat2td 1\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 5, d2\<^sub>v = nat2td 2\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 5, d2\<^sub>v = nat2td 3\<rparr>,
  \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 5, d2\<^sub>v = nat2td 4\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 5, d2\<^sub>v = nat2td 5\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 5, d2\<^sub>v = nat2td 6\<rparr>,
  \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 6, d2\<^sub>v = nat2td 1\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 6, d2\<^sub>v = nat2td 2\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 6, d2\<^sub>v = nat2td 3\<rparr>,
  \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 6, d2\<^sub>v = nat2td 4\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 6, d2\<^sub>v = nat2td 5\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 6, d2\<^sub>v = nat2td 6\<rparr>
}"

abbreviation "state_t_set_d1d2_eq t\<^sub>0 \<equiv> {\<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 1, d2\<^sub>v = nat2td 1\<rparr>, 
  \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 2, d2\<^sub>v = nat2td 2\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 3, d2\<^sub>v = nat2td 3\<rparr>, 
  \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 4, d2\<^sub>v = nat2td 4\<rparr>, \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 5, d2\<^sub>v = nat2td 5\<rparr>, 
  \<lparr>t\<^sub>v = t\<^sub>0, d1\<^sub>v = nat2td 6, d2\<^sub>v = nat2td 6\<rparr>}"

lemma state_t_set_finite: "finite (state_t_set t\<^sub>0)"
  by force

(* {\<lparr>fd1\<^sub>v = x1, fd2\<^sub>v = x2\<rparr> | x1 x2. x1 \<in> outcomes1 \<and> x2 \<in> outcomes1} *)
lemma state_t_set_eq: "{x::state_t. t\<^sub>v x = t\<^sub>0} = state_t_set t\<^sub>0"
  apply (simp)
  apply (subst set_eq_iff)
  apply (auto)
  apply (rule ccontr)
proof -
  fix x::"state_t"
  assume a0  : "t\<^sub>0 = t\<^sub>v x"
  assume a1  : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (Suc (0::\<nat>)), d2\<^sub>v = nat2td (Suc (0::\<nat>))\<rparr>"
  assume a2  : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (Suc (0::\<nat>)), d2\<^sub>v = nat2td (2::\<nat>)\<rparr>"
  assume a3  : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (Suc (0::\<nat>)), d2\<^sub>v = nat2td (3::\<nat>)\<rparr>"
  assume a4  : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (Suc (0::\<nat>)), d2\<^sub>v = nat2td (4::\<nat>)\<rparr>"
  assume a5  : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (Suc (0::\<nat>)), d2\<^sub>v = nat2td (5::\<nat>)\<rparr>"
  assume a6  : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (Suc (0::\<nat>)), d2\<^sub>v = nat2td (6::\<nat>)\<rparr>"
  assume a7  : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (2::\<nat>), d2\<^sub>v = nat2td (Suc (0::\<nat>))\<rparr>"
  assume a8  : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (2::\<nat>), d2\<^sub>v = nat2td (2::\<nat>)\<rparr>"
  assume a9  : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (2::\<nat>), d2\<^sub>v = nat2td (3::\<nat>)\<rparr>"
  assume a10 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (2::\<nat>), d2\<^sub>v = nat2td (4::\<nat>)\<rparr>"
  assume a11 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (2::\<nat>), d2\<^sub>v = nat2td (5::\<nat>)\<rparr>"
  assume a12 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (2::\<nat>), d2\<^sub>v = nat2td (6::\<nat>)\<rparr>"
  assume a13 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (3::\<nat>), d2\<^sub>v = nat2td (Suc (0::\<nat>))\<rparr>"
  assume a14 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (3::\<nat>), d2\<^sub>v = nat2td (2::\<nat>)\<rparr>"
  assume a15 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (3::\<nat>), d2\<^sub>v = nat2td (3::\<nat>)\<rparr>"
  assume a16 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (3::\<nat>), d2\<^sub>v = nat2td (4::\<nat>)\<rparr>"
  assume a17 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (3::\<nat>), d2\<^sub>v = nat2td (5::\<nat>)\<rparr>"
  assume a18 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (3::\<nat>), d2\<^sub>v = nat2td (6::\<nat>)\<rparr>"
  assume a19 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (4::\<nat>), d2\<^sub>v = nat2td (Suc (0::\<nat>))\<rparr>"
  assume a20 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (4::\<nat>), d2\<^sub>v = nat2td (2::\<nat>)\<rparr>"
  assume a21 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (4::\<nat>), d2\<^sub>v = nat2td (3::\<nat>)\<rparr>"
  assume a22 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (4::\<nat>), d2\<^sub>v = nat2td (4::\<nat>)\<rparr>"
  assume a23 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (4::\<nat>), d2\<^sub>v = nat2td (5::\<nat>)\<rparr>"
  assume a24 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (4::\<nat>), d2\<^sub>v = nat2td (6::\<nat>)\<rparr>"
  assume a25 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (5::\<nat>), d2\<^sub>v = nat2td (Suc (0::\<nat>))\<rparr>"
  assume a26 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (5::\<nat>), d2\<^sub>v = nat2td (2::\<nat>)\<rparr>"
  assume a27 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (5::\<nat>), d2\<^sub>v = nat2td (3::\<nat>)\<rparr>"
  assume a28 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (5::\<nat>), d2\<^sub>v = nat2td (4::\<nat>)\<rparr>"
  assume a29 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (5::\<nat>), d2\<^sub>v = nat2td (5::\<nat>)\<rparr>"
  assume a30 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (5::\<nat>), d2\<^sub>v = nat2td (6::\<nat>)\<rparr>"
  assume a31 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (6::\<nat>), d2\<^sub>v = nat2td (Suc (0::\<nat>))\<rparr>"
  assume a32 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (6::\<nat>), d2\<^sub>v = nat2td (2::\<nat>)\<rparr>"
  assume a33 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (6::\<nat>), d2\<^sub>v = nat2td (3::\<nat>)\<rparr>"
  assume a34 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (6::\<nat>), d2\<^sub>v = nat2td (4::\<nat>)\<rparr>"
  assume a35 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (6::\<nat>), d2\<^sub>v = nat2td (6::\<nat>)\<rparr>"
  assume a36 : "\<not> x = \<lparr>t\<^sub>v = t\<^sub>v x, d1\<^sub>v = nat2td (6::\<nat>), d2\<^sub>v = nat2td (5::\<nat>)\<rparr>"

  have f1: "d1\<^sub>v x \<in> (UNIV)"
    by simp

  have f2: "d1\<^sub>v x \<notin> outcomes1"
    apply (auto)
    using Tdice_mem a1 a2 a3 a4 a5 a6 
    apply (metis (mono_tags, opaque_lifting) One_nat_def empty_iff insert_iff old.unit.exhaust state_t.surjective)
    using Tdice_mem a7 a8 a9 a10 a11 a12
    apply (metis (mono_tags, opaque_lifting) One_nat_def empty_iff insert_iff old.unit.exhaust state_t.surjective)
    using Tdice_mem a13 a14 a15 a16 a17 a18 
    apply (metis (mono_tags, opaque_lifting) One_nat_def empty_iff insert_iff old.unit.exhaust state_t.surjective)
    using Tdice_mem a19 a20 a21 a22 a23 a24 
    apply (metis (mono_tags, opaque_lifting) One_nat_def empty_iff insert_iff old.unit.exhaust state_t.surjective)
    using Tdice_mem a25 a26 a27 a28 a29 a30 
    apply (metis (mono_tags, opaque_lifting) One_nat_def empty_iff insert_iff old.unit.exhaust state_t.surjective)
    using Tdice_mem a31 a32 a33 a34 a35 a36 
    by (metis (mono_tags, opaque_lifting) One_nat_def empty_iff insert_iff old.unit.exhaust state_t.surjective)
  
  from f1 f2 show "False"
    using Tdice_UNIV_eq by blast
qed

lemma state_t_finite: "finite {x::state_t. t\<^sub>v x = t\<^sub>0}"
  using state_t_set_eq state_t_set_finite by presburger

lemma state_t_neq: "(x::state_t) \<noteq> y \<longleftrightarrow> (d1\<^sub>v x \<noteq> d1\<^sub>v y) \<or> (d2\<^sub>v x \<noteq> d2\<^sub>v y) \<or> (t\<^sub>v x \<noteq> t\<^sub>v y)"
  by (auto)

lemma card_state_t_set: "card (state_t_set t\<^sub>0) = 36"
proof -
  let ?f = "\<lambda>x::state_t. 6 * (td2nat (d1\<^sub>v x) - 1) +  td2nat (d2\<^sub>v x)"
  have f_inj_on: "inj_on ?f (state_t_set t\<^sub>0)"
    apply (subst inj_on_def)
    apply (clarify)
    apply (rule ccontr)
    proof -
      fix x y
      assume a1: "x \<in> state_t_set t\<^sub>0"
      assume a2: "y \<in> state_t_set t\<^sub>0"
      assume a3: "(6::\<nat>) * (td2nat (d1\<^sub>v x) - (1::\<nat>)) + td2nat (d2\<^sub>v x) = 
                  (6::\<nat>) * (td2nat (d1\<^sub>v y) - (1::\<nat>)) + td2nat (d2\<^sub>v y)"
      assume a4: "\<not> x = y"
      then have f1: "\<not>(d1\<^sub>v x) = (d1\<^sub>v y) \<or> \<not>(d2\<^sub>v x) = (d2\<^sub>v y) \<or> \<not>(t\<^sub>v x) = (t\<^sub>v y)"
        by (simp add: state_t_neq)
      have f2: "\<not>(d1\<^sub>v x) = (d1\<^sub>v y) \<Longrightarrow> \<not>(6::\<nat>) * (td2nat (d1\<^sub>v x) - (1::\<nat>)) + td2nat (d2\<^sub>v x) = 
                  (6::\<nat>) * (td2nat (d1\<^sub>v y) - (1::\<nat>)) + td2nat (d2\<^sub>v y)"
        proof (cases "td2nat (d1\<^sub>v x) > td2nat (d1\<^sub>v y)")
          case True
          then have f20: "(6::\<nat>) * (td2nat (d1\<^sub>v x) - (1::\<nat>)) + td2nat (d2\<^sub>v x) = 
              (6::\<nat>) * (td2nat (d1\<^sub>v y) + (td2nat (d1\<^sub>v x) - td2nat (d1\<^sub>v y)) - (1::\<nat>)) + td2nat (d2\<^sub>v x)"
            by simp
          have f21: "... = (6::\<nat>) * (td2nat (d1\<^sub>v y) - (1::\<nat>)) + 6 * (td2nat (d1\<^sub>v x) - td2nat (d1\<^sub>v y)) + td2nat (d2\<^sub>v x)"
            using diff_mult_distrib2 td2nat_in_1_6 by force
          have f22: "6 * (td2nat (d1\<^sub>v x) - td2nat (d1\<^sub>v y)) \<ge> 6"
            using True by simp
          then have f23: "6 * (td2nat (d1\<^sub>v x) - td2nat (d1\<^sub>v y)) + td2nat (d2\<^sub>v x) > 6"
            by (metis diff_add_inverse diff_is_0_eq le_eq_less_or_eq le_zero_eq td2nat_in_1_6 trans_le_add1 zero_neq_one)
          have f24: "6 * (td2nat (d1\<^sub>v x) - td2nat (d1\<^sub>v y)) + td2nat (d2\<^sub>v x) \<noteq> td2nat (d2\<^sub>v y)"
            using f23 td2nat_in_1_6 by (metis linorder_not_less)
          then show ?thesis
            using f21 f20 by linarith
        next
          case False
          assume a11: "\<not> d1\<^sub>v x = d1\<^sub>v y"
          assume a12: "\<not> td2nat (d1\<^sub>v y) < td2nat (d1\<^sub>v x)"
          from False have "td2nat (d1\<^sub>v y) \<ge> td2nat (d1\<^sub>v x)"
            by simp
          then have f0: "td2nat (d1\<^sub>v y) > td2nat (d1\<^sub>v x)"
            using a11 le_neq_implies_less td2nat_inject by presburger
          then have f20: "(6::\<nat>) * (td2nat (d1\<^sub>v y) - (1::\<nat>)) + td2nat (d2\<^sub>v y) = 
              (6::\<nat>) * (td2nat (d1\<^sub>v x) + (td2nat (d1\<^sub>v y) - td2nat (d1\<^sub>v x)) - (1::\<nat>)) + td2nat (d2\<^sub>v y)"
            by simp
          have f21: "... = (6::\<nat>) * (td2nat (d1\<^sub>v x) - (1::\<nat>)) + 6 * (td2nat (d1\<^sub>v y) - td2nat (d1\<^sub>v x)) + td2nat (d2\<^sub>v y)"
            using diff_mult_distrib2 td2nat_in_1_6 by force
          have f22: "6 * (td2nat (d1\<^sub>v y) - td2nat (d1\<^sub>v x)) \<ge> 6"
            using f0 by simp
          then have f23: "6 * (td2nat (d1\<^sub>v y) - td2nat (d1\<^sub>v x)) + td2nat (d2\<^sub>v y) > 6"
            by (metis diff_add_inverse diff_is_0_eq le_eq_less_or_eq le_zero_eq td2nat_in_1_6 trans_le_add1 zero_neq_one)
          have f24: "6 * (td2nat (d1\<^sub>v y) - td2nat (d1\<^sub>v x)) + td2nat (d2\<^sub>v y) \<noteq> td2nat (d2\<^sub>v x)"
            using f23 td2nat_in_1_6 by (metis linorder_not_less)
          then show ?thesis
            using f21 f20 by linarith
        qed
      have f3: "\<not>(d2\<^sub>v x) = (d2\<^sub>v y) \<Longrightarrow> \<not>(6::\<nat>) * (td2nat (d1\<^sub>v x) - (1::\<nat>)) + td2nat (d2\<^sub>v x) = 
                  (6::\<nat>) * (td2nat (d1\<^sub>v y) - (1::\<nat>)) + td2nat (d2\<^sub>v y)"
        proof (cases "(d1\<^sub>v x) = (d1\<^sub>v y)")
          case True
          then show ?thesis 
            using f1 td2nat_inject
            by (smt (verit, best) a1 a2 add.commute diff_add_inverse2 mem_Collect_eq state_t_set_eq)
        next
          case False
          then show ?thesis 
            using f2 by blast
        qed
      show "False"
        using f1 f2 f3 a3 by (smt (verit, best) a1 a2 mem_Collect_eq state_t_set_eq)
    qed

  have inj_set: "?f ` (state_t_set t\<^sub>0) = {(1::\<nat>)..36}"
    apply (simp add: image_def)
    apply (simp add: nat2td_inverse)
    apply (auto)
    by presburger
  have card_eq: "card (state_t_set t\<^sub>0) = card(?f ` (state_t_set t\<^sub>0))"
    using inj_on_iff_eq_card f_inj_on by (smt (verit, best) card_image)
  have card_inj_eq: "... = card ({(1::\<nat>)..36})"
    using inj_set by presburger
  have "... = 36"
    by simp
  then show ?thesis
    using card_eq inj_set by presburger
qed

lemma state_t_set_d1_d2_eq: "{x::state_t. t\<^sub>v x = t\<^sub>0 \<and> d1\<^sub>v x = d2\<^sub>v x} = state_t_set_d1d2_eq t\<^sub>0"
  apply (auto)
  by (smt (verit, ccfv_SIG) One_nat_def Tdice_mem empty_iff insert_iff old.unit.exhaust state_t.surjective)

lemma state_t_set_d1d2_eq_6: "card (state_t_set_d1d2_eq t\<^sub>0) = 6"
proof -
  let ?f = "\<lambda>x::state_t. (td2nat (d1\<^sub>v x))"
  have f_inj_on: "inj_on ?f (state_t_set_d1d2_eq t\<^sub>0)"
    apply (subst inj_on_def)
    apply (clarify)
    apply (rule ccontr)
    proof -
      fix x y
      assume a1: "x \<in> state_t_set_d1d2_eq t\<^sub>0"
      assume a2: "y \<in> state_t_set_d1d2_eq t\<^sub>0"
      assume a3: "td2nat (d1\<^sub>v x) = td2nat (d1\<^sub>v y)"
      assume a4: "\<not> x = y"
      then have f1: "\<not>(d1\<^sub>v x) = (d1\<^sub>v y) \<or> \<not>(d2\<^sub>v x) = (d2\<^sub>v y) \<or> \<not>(t\<^sub>v x) = (t\<^sub>v y)"
        by (simp add: state_t_neq)
      show "False"
        using f1 by (metis (mono_tags) a1 a2 a3 mem_Collect_eq state_t_set_d1_d2_eq td2nat_inverse)
    qed

  have inj_set: "?f ` (state_t_set_d1d2_eq t\<^sub>0) = {(1::\<nat>)..6}"
    apply (simp add: image_def)
    apply (simp add: nat2td_inverse)
    by (auto)
  have card_eq: "card (state_t_set_d1d2_eq t\<^sub>0) = card(?f ` (state_t_set_d1d2_eq t\<^sub>0))"
    using inj_on_iff_eq_card f_inj_on by (smt (verit, best) card_image)
  have card_inj_eq: "... = card ({(1::\<nat>)..6})"
    using inj_set by presburger
  have "... = 6"
    by simp
  then show ?thesis
    using card_eq card_inj_eq by presburger
qed

lemma state_t_set_d1d2_eq_card: "card {x::state_t. t\<^sub>v x = t\<^sub>0 \<and> d1\<^sub>v x = d2\<^sub>v x} = 6"
  using One_nat_def state_t_set_d1d2_eq_6 state_t_set_d1_d2_eq by presburger

lemma state_t_set_d1d2_neq: "{x::state_t. t\<^sub>v x = t\<^sub>0 \<and> \<not>d1\<^sub>v x = d2\<^sub>v x} = {x::state_t. t\<^sub>v x = t\<^sub>0} - {x::state_t. t\<^sub>v x = t\<^sub>0 \<and> d1\<^sub>v x = d2\<^sub>v x}"
  by auto

lemma state_set_d1d2_neq': "{x::state_t. t\<^sub>v x = t\<^sub>0 \<and> \<not>d1\<^sub>v x = d2\<^sub>v x} = state_t_set t\<^sub>0 - state_t_set_d1d2_eq  t\<^sub>0"
  apply (simp only: state_t_set_d1d2_neq)
  using state_t_set_d1_d2_eq state_t_set_eq by presburger

lemma state_t_set_d1d2_neq_card: "card {x::state_t. t\<^sub>v x = t\<^sub>0 \<and> \<not> d1\<^sub>v x = d2\<^sub>v x} = 30"
proof -
  have "card {x::state_t. t\<^sub>v x = t\<^sub>0 \<and> \<not> d1\<^sub>v x = d2\<^sub>v x} = card (state_t_set t\<^sub>0 - state_t_set_d1d2_eq  t\<^sub>0)"
    by (simp add: state_set_d1d2_neq')
  also have "... = card (state_t_set t\<^sub>0) - card ( state_t_set_d1d2_eq  t\<^sub>0)"
    using One_nat_def UNIV_def card_Diff_subset card_state_t_set state_t_set_d1_d2_eq 
        state_t_set_d1d2_neq state_t_set_eq state_t_set_finite finite_subset insert_commute 
        numeral_1_eq_Suc_0 top.extremum by (smt (verit, del_insts) finite.insertI mem_Collect_eq subsetI)
  also have "... = 30"
    apply (simp only: card_state_t_set state_t_set_d1_d2_eq[symmetric])
    by (simp only: state_t_set_d1d2_eq_card)
  then show ?thesis
    using calculation by presburger
qed

subsubsection \<open> Definitions \<close>
definition dice_throw:: "state_t prhfun" where
"dice_throw = prfun_of_rvfun (d1 \<^bold>\<U> outcomes1) ; prfun_of_rvfun (d2 \<^bold>\<U> outcomes1)"

definition dice_throw_t_loop where
"dice_throw_t_loop = while\<^sub>p\<^sub>t (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e do dice_throw od"

definition Ht:: "state_t rvhfun" where 
"Ht = ((\<lbrakk>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup>< \<and> d1\<^sup>> = d1\<^sup>< \<and> d2\<^sup>> = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e) + 
        \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>d1\<^sup>> = d2\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> $t\<^sup>> \<ge> $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e  * (5/6)^($t\<^sup>> - $t\<^sup>< - 1) * (1/36))\<^sub>e"

subsubsection \<open> Theorems \<close>
lemma d1_uni_is_dist: 
  "is_final_distribution (rvfun_of_prfun (prfun_of_rvfun (d1 \<^bold>\<U> outcomes1)))"
  apply (subst rvfun_uniform_dist_is_dist')
  apply blast
  by simp+

lemma d2_uni_is_dist: 
  "is_final_distribution (rvfun_of_prfun (prfun_of_rvfun (d2 \<^bold>\<U> outcomes1)))"
  apply (subst rvfun_uniform_dist_is_dist')
  apply blast
  by simp+

lemma dice_throw_is_dist: "is_final_distribution (rvfun_of_prfun dice_throw)"
  apply (simp only: dice_throw_def pseqcomp_def)
  apply (subst rvfun_seqcomp_inverse)
  using d1_uni_is_dist apply blast
  using ureal_is_prob apply blast
  apply (subst rvfun_seqcomp_is_dist)
  using d1_uni_is_dist apply blast
  using d2_uni_is_dist by blast+

lemma real_ab: "real (6::\<nat>) * real (6::\<nat>) = (36::\<real>)"
  by auto

lemma d1_if_simp: "(if d1\<^sub>v (x) = nat2td (Suc (0::\<nat>)) \<or> d1\<^sub>v (x) = nat2td (2::\<nat>) \<or>
        d1\<^sub>v (x) = nat2td (3::\<nat>) \<or> d1\<^sub>v (x) = nat2td (4::\<nat>) \<or> 
        d1\<^sub>v (x) = nat2td (5::\<nat>) \<or> d1\<^sub>v (x) = nat2td (6::\<nat>)
     then 1::\<real> else (0::\<real>)) = (1::\<real>)"
  using Tdice_mem by auto

lemma d2_if_simp: "(if d2\<^sub>v (x) = nat2td (Suc (0::\<nat>)) \<or> d2\<^sub>v (x) = nat2td (2::\<nat>) \<or>
        d2\<^sub>v (x) = nat2td (3::\<nat>) \<or> d2\<^sub>v (x) = nat2td (4::\<nat>) \<or> 
        d2\<^sub>v (x) = nat2td (5::\<nat>) \<or> d2\<^sub>v (x) = nat2td (6::\<nat>)
     then 1::\<real> else (0::\<real>)) = (1::\<real>)"
  using Tdice_mem by auto

lemma dice_throw_altdef: "rvfun_of_prfun dice_throw = 
  (\<lbrakk>d1\<^sup>> \<in> outcomes1\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>d2\<^sup>> \<in> outcomes1\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e / 36)\<^sub>e"
  apply (simp add: dice_throw_def pseqcomp_def)
  apply (subst rvfun_uniform_dist_inverse)
  apply (simp)+
  apply (subst rvfun_uniform_dist_inverse)
  apply (simp)+
  apply (subst rvfun_seqcomp_inverse)
  apply (simp add: rvfun_uniform_dist_is_dist)
  apply (simp add: rvfun_uniform_dist_is_prob)
  apply (subst rvfun_uniform_dist_altdef)
  apply (simp)+
  apply (subst rvfun_uniform_dist_altdef)
  apply (simp)+
  apply (expr_simp_1 add: rel assigns_r_def)
  apply (subst fun_eq_iff)
  apply (simp only: outcomes1'_card real_ab)
  apply (rule allI)
proof -
  fix x::"state_t \<times> state_t"
  let ?lhs1_b = "\<lambda>v\<^sub>0. v\<^sub>0 = fst x\<lparr>d1\<^sub>v := nat2td (Suc (0::\<nat>))\<rparr> \<or>
              v\<^sub>0 = fst x\<lparr>d1\<^sub>v := nat2td (2::\<nat>)\<rparr> \<or>
              v\<^sub>0 = fst x\<lparr>d1\<^sub>v := nat2td (3::\<nat>)\<rparr> \<or>
              v\<^sub>0 = fst x\<lparr>d1\<^sub>v := nat2td (4::\<nat>)\<rparr> \<or> 
              v\<^sub>0 = fst x\<lparr>d1\<^sub>v := nat2td (5::\<nat>)\<rparr> \<or> 
              v\<^sub>0 = fst x\<lparr>d1\<^sub>v := nat2td (6::\<nat>)\<rparr>"
  let ?lhs1_b' = "\<lambda>v\<^sub>0. ((fst x\<lparr>d1\<^sub>v := (nat2td (Suc (0::\<nat>)))\<rparr> = v\<^sub>0) \<or>
              (fst x\<lparr>d1\<^sub>v := nat2td (2::\<nat>)\<rparr> = v\<^sub>0) \<or>
              (fst x\<lparr>d1\<^sub>v := nat2td (3::\<nat>)\<rparr> = v\<^sub>0) \<or>
              (fst x\<lparr>d1\<^sub>v := nat2td (4::\<nat>)\<rparr> = v\<^sub>0) \<or>
              (fst x\<lparr>d1\<^sub>v := nat2td (5::\<nat>)\<rparr> = v\<^sub>0) \<or> 
              (fst x\<lparr>d1\<^sub>v := nat2td (6::\<nat>)\<rparr> = v\<^sub>0))"
  let ?lhs1 = "\<lambda>v\<^sub>0. (if ?lhs1_b v\<^sub>0 then 1::\<real> else (0::\<real>))"
  let ?lhs2_b = "\<lambda>v\<^sub>0. snd x = v\<^sub>0\<lparr>d2\<^sub>v := nat2td (Suc (0::\<nat>))\<rparr> \<or>
              snd x = v\<^sub>0\<lparr>d2\<^sub>v := nat2td (2::\<nat>)\<rparr> \<or>
              snd x = v\<^sub>0\<lparr>d2\<^sub>v := nat2td (3::\<nat>)\<rparr> \<or>
              snd x = v\<^sub>0\<lparr>d2\<^sub>v := nat2td (4::\<nat>)\<rparr> \<or> 
              snd x = v\<^sub>0\<lparr>d2\<^sub>v := nat2td (5::\<nat>)\<rparr> \<or> 
              snd x = v\<^sub>0\<lparr>d2\<^sub>v := nat2td (6::\<nat>)\<rparr>"
  let ?lhs2_b' = "\<lambda>v\<^sub>0. v\<^sub>0\<lparr>d2\<^sub>v := nat2td (Suc (0::\<nat>))\<rparr> = snd x \<or>
           v\<^sub>0\<lparr>d2\<^sub>v := nat2td (2::\<nat>)\<rparr> = snd x \<or>
           v\<^sub>0\<lparr>d2\<^sub>v := nat2td (3::\<nat>)\<rparr> = snd x \<or>
           v\<^sub>0\<lparr>d2\<^sub>v := nat2td (4::\<nat>)\<rparr> = snd x \<or>
           v\<^sub>0\<lparr>d2\<^sub>v := nat2td (5::\<nat>)\<rparr> = snd x \<or> v\<^sub>0\<lparr>d2\<^sub>v := nat2td (6::\<nat>)\<rparr> = snd x"
  let ?lhs2 = "\<lambda>v\<^sub>0. ((if ?lhs2_b v\<^sub>0 then 1::\<real> else (0::\<real>)))"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0. ?lhs1 v\<^sub>0 * ?lhs2 v\<^sub>0 / 36)"

  let ?rhs1 = "(if d1\<^sub>v (snd x) = nat2td (Suc (0::\<nat>)) \<or>
           d1\<^sub>v (snd x) = nat2td (2::\<nat>) \<or>
           d1\<^sub>v (snd x) = nat2td (3::\<nat>) \<or> 
           d1\<^sub>v (snd x) = nat2td (4::\<nat>) \<or> 
           d1\<^sub>v (snd x) = nat2td (5::\<nat>) \<or> 
           d1\<^sub>v (snd x) = nat2td (6::\<nat>)
      then 1::\<real> else (0::\<real>))"
  let ?rhs2 = "(if d2\<^sub>v (snd x) = nat2td (Suc (0::\<nat>)) \<or>
           d2\<^sub>v (snd x) = nat2td (2::\<nat>) \<or>
           d2\<^sub>v (snd x) = nat2td (3::\<nat>) \<or> 
           d2\<^sub>v (snd x) = nat2td (4::\<nat>) \<or> 
           d2\<^sub>v (snd x) = nat2td (5::\<nat>) \<or> 
           d2\<^sub>v (snd x) = nat2td (6::\<nat>)
      then 1::\<real> else (0::\<real>))"
  let ?rhs3 = "(if t\<^sub>v (snd x) = t\<^sub>v (fst x) then 1::\<real> else (0::\<real>))"
  let ?rhs = "?rhs1 * ?rhs2 * ?rhs3 / 36"
  have lhs1_lhs2_simp: "\<forall>v\<^sub>0. (?lhs1 v\<^sub>0 * ?lhs2 v\<^sub>0 = (if (?lhs1_b v\<^sub>0 \<and> ?lhs2_b v\<^sub>0) then 1 else 0))"
    by (auto)
  have lhs1b_lhs2b_simp: "\<forall>v\<^sub>0. (?lhs1_b v\<^sub>0 \<and> ?lhs2_b v\<^sub>0) = 
    (t\<^sub>v (fst x) = t\<^sub>v (snd x) \<and> (v\<^sub>0 = \<lparr> t\<^sub>v = t\<^sub>v (fst x), d1\<^sub>v = d1\<^sub>v (snd x), d2\<^sub>v = d2\<^sub>v (fst x) \<rparr>))"
    apply (rule allI)
    proof -
      fix v\<^sub>0::state_t
      have f1: "?lhs1_b v\<^sub>0 \<longrightarrow> d2\<^sub>v v\<^sub>0 = d2\<^sub>v (fst x)"
        by auto
      have f2: "?lhs2_b v\<^sub>0 \<longrightarrow> d1\<^sub>v v\<^sub>0 = d1\<^sub>v (snd x)"
        by auto
      show "(?lhs1_b v\<^sub>0 \<and> ?lhs2_b v\<^sub>0) = 
          (t\<^sub>v (fst x) = t\<^sub>v (snd x) \<and> (v\<^sub>0 = \<lparr>t\<^sub>v = t\<^sub>v (fst x), d1\<^sub>v = d1\<^sub>v (snd x), d2\<^sub>v = d2\<^sub>v (fst x)\<rparr>))"
        apply (rule iffI)
        using f1 f2 apply force
        apply (auto)
        proof -
          assume a0: "t\<^sub>v (fst x) = t\<^sub>v (snd x)"
          assume a0': "v\<^sub>0 = \<lparr>t\<^sub>v = t\<^sub>v (snd x), d1\<^sub>v = d1\<^sub>v (snd x), d2\<^sub>v = d2\<^sub>v (fst x)\<rparr>"
          assume a1: "\<not> \<lparr>t\<^sub>v = t\<^sub>v (snd x), d1\<^sub>v = d1\<^sub>v (snd x), d2\<^sub>v = d2\<^sub>v (fst x)\<rparr> = (fst x\<lparr>d1\<^sub>v := nat2td (Suc (0::\<nat>))\<rparr>)"
          assume a2: "\<not> \<lparr>t\<^sub>v = t\<^sub>v (snd x), d1\<^sub>v = d1\<^sub>v (snd x), d2\<^sub>v = d2\<^sub>v (fst x)\<rparr> = fst x\<lparr>d1\<^sub>v := nat2td (2::\<nat>)\<rparr>"
          assume a3: "\<not> \<lparr>t\<^sub>v = t\<^sub>v (snd x), d1\<^sub>v = d1\<^sub>v (snd x), d2\<^sub>v = d2\<^sub>v (fst x)\<rparr> = fst x\<lparr>d1\<^sub>v := nat2td (3::\<nat>)\<rparr>"
          assume a4: "\<not> \<lparr>t\<^sub>v = t\<^sub>v (snd x), d1\<^sub>v = d1\<^sub>v (snd x), d2\<^sub>v = d2\<^sub>v (fst x)\<rparr> = fst x\<lparr>d1\<^sub>v := nat2td (4::\<nat>)\<rparr>"
          assume a6: "\<not> \<lparr>t\<^sub>v = t\<^sub>v (snd x), d1\<^sub>v = d1\<^sub>v (snd x), d2\<^sub>v = d2\<^sub>v (fst x)\<rparr> = fst x\<lparr>d1\<^sub>v := nat2td (6::\<nat>)\<rparr>"
          from a1 have f11: "\<not>d1\<^sub>v (snd x) = nat2td (Suc (0::\<nat>))"
            using a0 by force
          from a2 have f12: "\<not>d1\<^sub>v (snd x) = nat2td (2::\<nat>)"
            using a0 by force
          from a3 have f13: "\<not>d1\<^sub>v (snd x) = nat2td (3::\<nat>)"
            using a0 by force
          from a4 have f14: "\<not>d1\<^sub>v (snd x) = nat2td (4::\<nat>)"
            using a0 by force
          from a6 have f16: "\<not>d1\<^sub>v (snd x) = nat2td (6::\<nat>)"
            using a0 by force
          have "d1\<^sub>v (snd x) = nat2td (5::\<nat>)"
            using f11 f12 f13 f14 f16 Tdice_mem by (metis One_nat_def empty_iff insert_iff)
          then show "\<lparr>t\<^sub>v = t\<^sub>v (snd x), d1\<^sub>v = d1\<^sub>v (snd x), d2\<^sub>v = d2\<^sub>v (fst x)\<rparr> = fst x\<lparr>d1\<^sub>v := nat2td (5::\<nat>)\<rparr>"
            using a0 by simp
        next
          assume a0: "t\<^sub>v (fst x) = t\<^sub>v (snd x)"
          assume a0': "v\<^sub>0 = \<lparr>t\<^sub>v = t\<^sub>v (snd x), d1\<^sub>v = d1\<^sub>v (snd x), d2\<^sub>v = d2\<^sub>v (fst x)\<rparr>"
          assume a1: "\<not> snd x = \<lparr>t\<^sub>v = t\<^sub>v (snd x), d1\<^sub>v = d1\<^sub>v (snd x), d2\<^sub>v = nat2td (Suc (0::\<nat>))\<rparr>"
          assume a2: "\<not> snd x = \<lparr>t\<^sub>v = t\<^sub>v (snd x), d1\<^sub>v = d1\<^sub>v (snd x), d2\<^sub>v = nat2td (2::\<nat>)\<rparr>"
          assume a3: "\<not> snd x = \<lparr>t\<^sub>v = t\<^sub>v (snd x), d1\<^sub>v = d1\<^sub>v (snd x), d2\<^sub>v = nat2td (3::\<nat>)\<rparr>"
          assume a4: "\<not> snd x = \<lparr>t\<^sub>v = t\<^sub>v (snd x), d1\<^sub>v = d1\<^sub>v (snd x), d2\<^sub>v = nat2td (4::\<nat>)\<rparr>"
          assume a6: "\<not> snd x = \<lparr>t\<^sub>v = t\<^sub>v (snd x), d1\<^sub>v = d1\<^sub>v (snd x), d2\<^sub>v = nat2td (6::\<nat>)\<rparr>"
          from a1 have f11: "\<not>d2\<^sub>v (snd x) = nat2td (Suc (0::\<nat>))"
            by force
          from a2 have f12: "\<not>d2\<^sub>v (snd x) = nat2td (2::\<nat>)"
            by force
          from a3 have f13: "\<not>d2\<^sub>v (snd x) = nat2td (3::\<nat>)"
            by force
          from a4 have f14: "\<not>d2\<^sub>v (snd x) = nat2td (4::\<nat>)"
            by force
          from a6 have f16: "\<not>d2\<^sub>v (snd x) = nat2td (6::\<nat>)"
            by force
          have "d2\<^sub>v (snd x) = nat2td (5::\<nat>)"
            using f11 f12 f13 f14 f16 Tdice_mem by (metis One_nat_def empty_iff insert_iff)
          then show "snd x = \<lparr>t\<^sub>v = t\<^sub>v (snd x), d1\<^sub>v = d1\<^sub>v (snd x), d2\<^sub>v = nat2td (5::\<nat>)\<rparr>"
            by simp
        qed
    qed

  have f1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0. ?lhs1 v\<^sub>0 * ?lhs2 v\<^sub>0) = 
            (\<Sum>\<^sub>\<infinity>v\<^sub>0. (if (?lhs1_b v\<^sub>0 \<and> ?lhs2_b v\<^sub>0) then 1 else 0))"
    using lhs1_lhs2_simp infsum_cong by auto
  also have f2: "... = card {v\<^sub>0. (?lhs1_b v\<^sub>0 \<and> ?lhs2_b v\<^sub>0)}"
    apply (subst infsum_constant_finite_states)
    apply (subst finite_subset[where B = "{s. t\<^sub>v s = t\<^sub>v (fst x)}"])
    apply (simp add: Collect_mono lhs1b_lhs2b_simp)
    using state_t_finite apply fastforce
    by (simp)+
  also have f3: "... = (if t\<^sub>v (fst x) = t\<^sub>v (snd x) then 1 else 0)"
    by (simp add: lhs1b_lhs2b_simp)

  have lhs': "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t. (if t\<^sub>v (fst x) = t\<^sub>v (snd x) \<and> v\<^sub>0 = \<lparr>t\<^sub>v = t\<^sub>v (fst x), d1\<^sub>v = d1\<^sub>v (snd x), 
        d2\<^sub>v = d2\<^sub>v (fst x)\<rparr> then 1::\<real> else (0::\<real>)) / (36::\<real>)) 
    = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t. (if t\<^sub>v (fst x) = t\<^sub>v (snd x) \<and> v\<^sub>0 = \<lparr>t\<^sub>v = t\<^sub>v (fst x), d1\<^sub>v = d1\<^sub>v (snd x), 
        d2\<^sub>v = d2\<^sub>v (fst x)\<rparr> then 1/36 else (0::\<real>)))"
    by (smt (verit, best) divide_eq_0_iff infsum_cong)

  show "?lhs = ?rhs"
    apply (simp only: lhs1_lhs2_simp lhs1b_lhs2b_simp)
    apply (simp only: d1_if_simp d2_if_simp)
    apply (simp only: lhs')
    apply (auto)
    apply (subst infsum_constant_finite_states)
    by simp+
qed

definition dice_throw_t_alt :: "state_t rvhfun" where
"dice_throw_t_alt \<equiv> (\<lbrakk>d1\<^sup>> \<in> outcomes1\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>d2\<^sup>> \<in> outcomes1\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 36)\<^sub>e"

lemma dice_throw_t_alt_eq: "dice_throw_t_alt = (\<lbrakk>t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 36)\<^sub>e"
  apply (simp add: dice_throw_t_alt_def)
  apply (pred_auto)
  using Tdice_mem apply auto[1]
  using Tdice_mem apply auto[1]
  using Tdice_mem apply auto[1]
  using Tdice_mem apply auto[1]
  using Tdice_mem apply auto[1]
  using Tdice_mem apply auto[1]
  using Tdice_mem by auto[1]

lemma state_t_add_1: "(rvfun_of_prfun ((t := $t + 1)::state_t prhfun)) = 
  (\<lbrakk>d1\<^sup>> = d1\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>d2\<^sup>> = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"
  apply (simp add: pfun_defs rvfun_assignment_inverse)
  by (pred_auto)

lemma state_t_set_eq_1: "{s::state_t. t\<^sub>v s = a \<and> d1\<^sub>v s = b \<and> d2\<^sub>v s = c} = {\<lparr>t\<^sub>v = a, d1\<^sub>v = b, d2\<^sub>v = c\<rparr>}"
  apply (simp add: set_eq_iff)
  by auto

lemma dice_throw_t: "(Pt dice_throw) = prfun_of_rvfun dice_throw_t_alt"
  apply (simp only: Pt_def)
  apply (simp only: pseqcomp_def)
  apply (simp only: state_t_add_1)
  apply (simp only: dice_throw_altdef)
  apply (simp only: dice_throw_t_alt_def)
  apply (expr_simp_1)
  apply (simp only: d1_if_simp d2_if_simp)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (simp add: fun_eq_iff)
  apply (auto)
proof -
  fix a b::"state_t"
  assume "t\<^sub>v b = Suc (t\<^sub>v a)"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t. (if t\<^sub>v v\<^sub>0 = t\<^sub>v a then 1::\<real> else (0::\<real>)) *
          ((if d1\<^sub>v b = d1\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if d2\<^sub>v b = d2\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) *
           (if t\<^sub>v a = t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>))) / (36::\<real>))"
  have "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t. (if t\<^sub>v v\<^sub>0 = t\<^sub>v a \<and> d1\<^sub>v b = d1\<^sub>v v\<^sub>0 \<and> d2\<^sub>v b = d2\<^sub>v v\<^sub>0 then 1/36 else (0::\<real>)))"
    by (smt (verit, best) infsum_cong mult_not_zero one_power2 power2_eq_square times_divide_eq_left)
  also have "... = 1/36"
    apply (subst infsum_constant_finite_states)
    apply (simp add: state_t_finite)
    apply (subgoal_tac "{s::state_t. t\<^sub>v s = t\<^sub>v a \<and> d1\<^sub>v b = d1\<^sub>v s \<and> d2\<^sub>v b = d2\<^sub>v s} = 
                        {s::state_t. t\<^sub>v s = t\<^sub>v a \<and> d1\<^sub>v s = d1\<^sub>v b \<and> d2\<^sub>v s = d2\<^sub>v b}")
    apply (simp add: state_t_set_eq_1)
    by auto
  then show "?lhs * 36 = 1"
    by (simp add: calculation)
next
  fix a b::"state_t"
  assume a1: "\<not> t\<^sub>v b = Suc (t\<^sub>v a)"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t. (if t\<^sub>v v\<^sub>0 = t\<^sub>v a then 1::\<real> else (0::\<real>)) *
          ((if d1\<^sub>v b = d1\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if d2\<^sub>v b = d2\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) *
           (if t\<^sub>v b = Suc (t\<^sub>v v\<^sub>0) then 1::\<real> else (0::\<real>))) / (36::\<real>))"
  show "?lhs = 0"
    by (simp add: a1 infsum_0)
qed

lemma dice_throw_t_is_dist: "is_final_distribution dice_throw_t_alt"
  apply (simp add: dist_defs dice_throw_t_alt_def)
  apply (expr_auto)
  apply (simp only: d1_if_simp d2_if_simp)
  apply (subst infsum_cdiv_left)
  apply (simp add: infsum_constant_finite_states_summable state_t_finite)
  apply (auto)
  apply (subst infsum_constant_finite_states)
  using state_t_finite apply blast
  by (metis card_state_t_set lambda_one of_nat_numeral state_t_set_eq)

lemma dice_throw_t_alt_inverse: "rvfun_of_prfun (prfun_of_rvfun dice_throw_t_alt) = dice_throw_t_alt"
  apply (subst rvfun_inverse)
  apply (simp add: dice_throw_t_is_dist rvfun_prob_sum1_summable'(1))
  by simp

lemma state_eq_set_Union: "{v\<^sub>0. d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0 \<and> t\<^sub>0 \<le> t\<^sub>v v\<^sub>0} = 
        (\<Union>i \<in> {1..6}. {v\<^sub>0. d1\<^sub>v v\<^sub>0 = nat2td i \<and> d2\<^sub>v v\<^sub>0 = nat2td i \<and> t\<^sub>0 \<le> t\<^sub>v v\<^sub>0})"
  apply (auto)
  by (metis One_nat_def nat2td_cases)

lemma geometry_series_sum: "(\<Sum>\<^sub>\<infinity>n::\<nat>. (((5::\<real>) / (6::\<real>)) ^ n /  (36::\<real>))) = 1 / 6"
  apply (subst infsetsum_infsum[symmetric])
  apply (simp add: abs_summable_on_nat_iff')
  apply (subst infsetsum_nat)
  apply (simp add: abs_summable_on_nat_iff')
  apply auto
  apply (subst suminf_divide)
  apply (simp add: summable_geometric)
  apply (subst suminf_geometric)
  apply simp
  by auto

lemma sum_d1_d2_eq_tt_1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t \<in> {v\<^sub>0. d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0 \<and> Suc tt \<le> t\<^sub>v v\<^sub>0}. 
          ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc tt) / (36::\<real>)) = 1" (is "?lhs = ?rhs")
proof -
  have reindex: "\<forall>i\<in>{1..6}. 
    (\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t \<in> {v\<^sub>0. d1\<^sub>v v\<^sub>0 = nat2td i \<and> d2\<^sub>v v\<^sub>0 = nat2td i \<and> Suc tt \<le> t\<^sub>v v\<^sub>0}.
       ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc tt) / (36::\<real>)) 
    = (\<Sum>\<^sub>\<infinity>n::\<nat>. (((5::\<real>) / (6::\<real>)) ^ n /  (36::\<real>)))"
  proof
    fix i::\<nat>
    have set_eq: "{v\<^sub>0. d1\<^sub>v v\<^sub>0 = nat2td i \<and> d2\<^sub>v v\<^sub>0 = nat2td i \<and> Suc tt \<le> t\<^sub>v v\<^sub>0} = 
                  range (\<lambda>n::\<nat>. \<lparr>t\<^sub>v = Suc tt + n, d1\<^sub>v = nat2td i, d2\<^sub>v = nat2td i\<rparr>)"
      apply (simp add: image_def, auto)
      by (metis add_Suc le_Suc_ex state_t.select_convs(1) state_t.select_convs(2) state_t_neq time.select_convs(1))
    have sum_eq: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t \<in> {v\<^sub>0. d1\<^sub>v v\<^sub>0 = nat2td i \<and> d2\<^sub>v v\<^sub>0 = nat2td i \<and> Suc tt \<le> t\<^sub>v v\<^sub>0}.
       ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc tt) /  (36::\<real>)) = 
      infsum (\<lambda>v\<^sub>0::state_t. ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc tt) /  (36::\<real>))
      ((\<lambda>n::\<nat>. \<lparr>t\<^sub>v = Suc tt + n, d1\<^sub>v = nat2td i, d2\<^sub>v = nat2td i\<rparr>) ` UNIV)"
      by (simp add: set_eq)
    have reindex: "infsum (\<lambda>v\<^sub>0::state_t. ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc tt) /  (36::\<real>))
      ((\<lambda>n::\<nat>. \<lparr>t\<^sub>v = Suc tt + n, d1\<^sub>v = nat2td i, d2\<^sub>v = nat2td i\<rparr>) ` UNIV)
      = infsum (\<lambda>n::\<nat>. ((5::\<real>) / (6::\<real>)) ^ n /  (36::\<real>)) UNIV"
      apply (subst infsum_reindex)
      apply (simp add: inj_def)
      by (simp add: infsum_cong)
    show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t \<in> {v\<^sub>0. d1\<^sub>v v\<^sub>0 = nat2td i \<and> d2\<^sub>v v\<^sub>0 = nat2td i \<and> Suc tt \<le> t\<^sub>v v\<^sub>0}.
       ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc tt) /  (36::\<real>)) 
      = (\<Sum>\<^sub>\<infinity>n::\<nat>. (((5::\<real>) / (6::\<real>)) ^ n /  (36::\<real>)))"
      by (simp only: sum_eq reindex)
  qed

  have "?lhs = sum (\<lambda>i. (\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t \<in> {v\<^sub>0. d1\<^sub>v v\<^sub>0 = nat2td i \<and> d2\<^sub>v v\<^sub>0 = nat2td i \<and> Suc tt \<le> t\<^sub>v v\<^sub>0}.
       ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc tt) /  (36::\<real>))) {1..6}"
    apply (simp add: state_eq_set_Union)
    apply (subst sum_infsum)
    apply blast
    apply (smt (verit, best) One_nat_def divide_eq_0_iff infsum_not_exists reindex geometry_series_sum zero_neq_numeral)
    apply (auto)
    by (simp add: nat2td_inject)
  moreover have "... = 1"
    by (simp add: reindex geometry_series_sum)
  then show "?lhs = (1::\<real>)"
    using calculation by presburger
qed

lemma Ht_is_dist: "is_final_distribution Ht"
  apply (simp add: dist_defs Ht_def)
  apply (simp add: expr_defs)
  apply (pred_auto)
  apply (subst infsum_constant_finite_states)
  apply (simp add: state_t_finite)
  apply (subst state_t_set_eq_1)
  apply (simp)
  apply (subgoal_tac "((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc t)  \<le> 1")
  apply linarith
  apply (simp add: power_le_one_iff)
proof -
  fix t::\<nat> and d1::Tdice and d2::Tdice
  let ?lhs = "(\<Sum>\<^sub>\<infinity>s::state_t. (if d1\<^sub>v s = d2\<^sub>v s then 1::\<real> else (0::\<real>)) * 
          (if Suc t \<le> t\<^sub>v s then 1::\<real> else (0::\<real>)) *
          ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v s - Suc t) / (36::\<real>))"
  let ?set = "{s::state_t. d1\<^sub>v s = d2\<^sub>v s \<and> Suc t \<le> t\<^sub>v s}"

  have f1: "?lhs = (\<Sum>\<^sub>\<infinity>s::state_t \<in> ?set \<union> -?set.
    (if d1\<^sub>v s = d2\<^sub>v s \<and> Suc t \<le> t\<^sub>v s then (((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v s - Suc t) / (36::\<real>)) else (0::\<real>)))"
    by (smt (verit, best) boolean_algebra.disj_cancel_right div_0 infsum_cong mult_cancel_right2 mult_eq_0_iff)
  moreover have "... = (\<Sum>\<^sub>\<infinity>s::state_t \<in> ?set. (if d1\<^sub>v s = d2\<^sub>v s \<and> Suc t \<le> t\<^sub>v s then 
            (((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v s - Suc t) / (36::\<real>)) else (0::\<real>)))"
    apply (rule infsum_cong_neutral)
    apply force
    apply simp
    by blast
  moreover have "... = (\<Sum>\<^sub>\<infinity>s::state_t \<in> ?set. (((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v s - Suc t) / (36::\<real>)))"
    by (smt (verit) infsum_cong mem_Collect_eq mult_cancel_right2)
  moreover have "... = 1"
    using sum_d1_d2_eq_tt_1 by presburger
  ultimately show "?lhs = (1::\<real>)"
    by presburger
qed

lemma Ht_is_fp: "\<F> (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e (Pt dice_throw) (prfun_of_rvfun (Ht)) = prfun_of_rvfun (Ht)"
  apply (simp add: Ht_def loopfunc_def)
  apply (simp add: pfun_defs dice_throw_t)
  (* apply (subst dice_throw_t_alt_def) *)
  apply (subst rvfun_skip_inverse)
  apply (subst rvfun_skip\<^sub>_f_simp)
  apply (subst rvfun_seqcomp_inverse)
  apply (simp add: dice_throw_t_is_dist rvfun_inverse rvfun_prob_sum1_summable'(1))
  using ureal_is_prob apply blast
  apply (subst rvfun_inverse)
   apply (simp add: dice_throw_t_is_dist rvfun_prob_sum1_summable'(1))
  apply (subst rvfun_inverse)
  apply (expr_auto add: dist_defs)
  apply (subgoal_tac "((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc t)  \<le> 1")
  apply linarith
  apply (simp add: power_le_one_iff)
  apply (simp only: dice_throw_t_alt_def)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (expr_simp_1)
  apply (pred_auto)
  apply (simp only: d1_if_simp d2_if_simp)
  defer
  apply (smt (verit, best) divide_eq_0_iff infsum_0 mult_not_zero)
  apply (smt (verit, best) Suc_leD divide_eq_0_iff infsum_0 mult_eq_0_iff not_less_eq_eq)
  apply (simp add: infsum_0)
  apply (auto)
proof -
  fix d1::Tdice and d2::Tdice and t::\<nat> and t\<^sub>v'::\<nat> and d2\<^sub>v'::Tdice
  assume a0: "\<not> d1 = d2"
  assume a1: "Suc t \<le> t\<^sub>v'"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t.
          (if t\<^sub>v v\<^sub>0 = Suc t then 1::\<real> else (0::\<real>)) *
          ((if d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if t\<^sub>v' = t\<^sub>v v\<^sub>0 \<and> d2\<^sub>v' = d1\<^sub>v v\<^sub>0 \<and> d2\<^sub>v' = d2\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) +
           (if \<not> d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if Suc (t\<^sub>v v\<^sub>0) \<le> t\<^sub>v' then 1::\<real> else (0::\<real>)) *
           ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc (t\<^sub>v v\<^sub>0)) / (36::\<real>)) / (36::\<real>))"
  have f0: "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t.
          ((if t\<^sub>v v\<^sub>0 = Suc t \<and> t\<^sub>v' = t\<^sub>v v\<^sub>0 \<and> d2\<^sub>v' = d1\<^sub>v v\<^sub>0 \<and> d2\<^sub>v' = d2\<^sub>v v\<^sub>0 then 1/36 else (0::\<real>)) +
           (if t\<^sub>v v\<^sub>0 = Suc t \<and> \<not> d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0 \<and> Suc (Suc t) \<le> t\<^sub>v' then (((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc (Suc t)) / (36::\<real>) / 36) else (0::\<real>))))"
    using infsum_cong divide_eq_0_iff mult_cancel_right1 mult_not_zero by (smt (verit, ccfv_SIG))
  moreover have f1: "... = (if Suc t = t\<^sub>v' then 1/36 else ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc (Suc t)) * 30 / (36::\<real>) / 36)"
    apply (subst infsum_add)
    apply (simp add: infsum_constant_finite_states_summable state_t_finite)
    apply (simp add: infsum_cond_finite_states_summable state_t_finite)
    apply (subst infsum_constant_finite_states_subset)
    apply (simp add: state_t_finite)
    apply (subst infsum_constant_finite_states_subset)
    using state_t_finite apply force
    apply (auto)
  proof -
    assume a: "t\<^sub>v' = Suc t"
    have f0: "{s::state_t. t\<^sub>v s = Suc t \<and> Suc t = t\<^sub>v s \<and> d2\<^sub>v' = d1\<^sub>v s \<and> d2\<^sub>v' = d2\<^sub>v s} = 
          {s::state_t. t\<^sub>v s = Suc t \<and> d2\<^sub>v' = d1\<^sub>v s \<and> d2\<^sub>v' = d2\<^sub>v s}"
      by fastforce
    show "card {s::state_t. t\<^sub>v s = Suc t \<and> Suc t = t\<^sub>v s \<and> d2\<^sub>v' = d1\<^sub>v s \<and> d2\<^sub>v' = d2\<^sub>v s} = Suc (0::\<nat>)"
      apply (simp add: f0)
      by (smt (verit, ccfv_threshold) card_1_singleton old.unit.exhaust state_t.select_convs(1) 
          state_t.select_convs(2) state_t.surjective time.select_convs(1))
  next
    assume a: "\<not> Suc t = t\<^sub>v'"
    have f1: "real (card {s::state_t. t\<^sub>v s = Suc t \<and> t\<^sub>v' = t\<^sub>v s \<and> d2\<^sub>v' = d1\<^sub>v s \<and> d2\<^sub>v' = d2\<^sub>v s}) = 0"
      using a by (simp add: card_0_singleton)
    have f2: "(card {s::state_t. t\<^sub>v s = Suc t \<and> \<not> d1\<^sub>v s = d2\<^sub>v s \<and> Suc (Suc t) \<le> t\<^sub>v'}) = 
      (card {s::state_t. t\<^sub>v s = Suc t \<and> \<not> d1\<^sub>v s = d2\<^sub>v s})"
      by (metis a a1 le_antisym not_less_eq_eq)
    also have "... = 30"
      using state_t_set_d1d2_neq_card by blast
    then show "(6::\<real>) * real (card {s::state_t. t\<^sub>v s = Suc t \<and> t\<^sub>v' = t\<^sub>v s \<and> d2\<^sub>v' = d1\<^sub>v s \<and> d2\<^sub>v' = d2\<^sub>v s}) +
      ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc (Suc t)) * real (card {s::state_t. t\<^sub>v s = Suc t \<and> \<not> d1\<^sub>v s = d2\<^sub>v s \<and> Suc (Suc t) \<le> t\<^sub>v'}) /
      (6::\<real>) = (5::\<real>) * ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc (Suc t))"
      apply (simp add: f1)
      using f2 by linarith
  qed
  show "?lhs * (36::\<real>) =  ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc t)"
    apply (simp only: f0 f1)
    apply (auto)
  proof -
    assume aa: "\<not> Suc t = t\<^sub>v'"
    have f0: "((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc t) * (6::\<real>) = ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc t - 1) * (5/6) * (6::\<real>)"
      by (metis One_nat_def Suc_pred a1 aa bot_nat_0.not_eq_extremum cancel_comm_monoid_add_class.diff_zero diff_diff_cancel power_Suc2)
    have f1: "(t\<^sub>v' - Suc (Suc t)) = (t\<^sub>v' - Suc t - 1)"
      using diff_Suc_eq_diff_pred diff_commute by presburger
    then show "(5::\<real>) * ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc (Suc t)) = ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc t) * (6::\<real>)"
      using f0 by auto
  qed
qed

(*
(Ht' = (\<lbrakk>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup>< \<and> d1\<^sup>> = d1\<^sup>< \<and> d2\<^sup>> = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e) +  (* Ht1 *)
  \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>d1\<^sup>> = d2\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> $t\<^sup>> \<ge> $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e  * (5/6)^($t\<^sup>> - $t\<^sup>< - 1) * (1/6))\<^sub>e" (* Ht2 *)

Now try to prove Ht is a fixed point and actually it is not.

if (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e then ((Pt dice_throw) ; Ht') else II = Ht'
= \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * ((Pt dice_throw) ; Ht') + \<lbrakk>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * II = Ht'
= \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * ((Pt dice_throw) ; Ht') + \<lbrakk>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * II = Ht1 + Ht2
= { Remove equal parts on LHS and RHS }
  \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * ((Pt dice_throw) ; (Ht1 + Ht2)) = Ht2
= { (Pt dice_throw) is simplified by dice_throw_t }
  \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e* ((\<lbrakk>t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 36)\<^sub>e ; (Ht1 + Ht2)) = Ht2
= { Sequential composition contributes through addition if summable }
  \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e* ((\<lbrakk>t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 36)\<^sub>e ; Ht1) + \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e* ((\<lbrakk>t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 36)\<^sub>e ; Ht2) = Ht2
= { Ht1 and Ht2 definitions }
  \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e* ((\<lbrakk>t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 36)\<^sub>e ; \<lbrakk>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>II\<rbrakk>\<^sub>\<I>\<^sub>e) + 
  \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e* ((\<lbrakk>t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 36)\<^sub>e ; (\<lbrakk>\<not>d1\<^sup><=d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e*\<lbrakk>d1\<^sup>>=d2\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> \<ge> t\<^sup><+1\<rbrakk>\<^sub>\<I>\<^sub>e * (5/6)^(t\<^sup>>-t\<^sup><-1) * (1/6))) 
  = \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>d1\<^sup>> = d2\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> $t\<^sup>> \<ge> $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e  * (5/6)^($t\<^sup>> - $t\<^sup>< - 1) * (1/6))\<^sub>e
= { Sequential composition }
  \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e* (\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t. \<lbrakk>t\<^sub>v v\<^sub>0 = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 36 * \<lbrakk>d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sub>v v\<^sub>0 \<and> d1\<^sup>< = d1\<^sub>v v\<^sub>0 \<and> d2\<^sup>> = d2\<^sub>v v\<^sub>0\<rbrakk>\<^sub>\<I>\<^sub>e) + 
  \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e* (\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t. \<lbrakk>t\<^sub>v v\<^sub>0 = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 36 * \<lbrakk>\<not>d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>d1\<^sup>>=d2\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> \<ge> t\<^sub>v v\<^sub>0+1\<rbrakk>\<^sub>\<I>\<^sub>e * (5/6)^(t\<^sup>>-t\<^sub>v v\<^sub>0-1) * (1/6))) 
  = \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>d1\<^sup>> = d2\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> $t\<^sup>> \<ge> $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e  * (5/6)^($t\<^sup>> - $t\<^sup>< - 1) * (1/6))\<^sub>e
= { Summation }
  (* Very easy to make a mistake where there is only one state v\<^sub>0 (not 6 states) satisfying 
      \<lbrakk>t\<^sub>v v\<^sub>0 = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e / 36 * \<lbrakk>d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sub>v v\<^sub>0 \<and> d1\<^sup>< = d1\<^sub>v v\<^sub>0 \<and> d2\<^sup>> = d2\<^sub>v v\<^sub>0\<rbrakk>\<^sub>\<I>\<^sub>e 
    The only state is: \<lparr>t\<^sub>v = t\<^sup>< + 1, d1\<^sub>v = d1\<^sup><, d2\<^sub>v = d1\<^sup><\<rparr>
  *)
  \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup>< + 1 \<and> d1\<^sup>< = d2\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * 1 / 36 +
  \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e*  \<lbrakk> d1\<^sup>> = d2\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> \<ge> t\<^sup><+2\<rbrakk>\<^sub>\<I>\<^sub>e * (5/6)^(t\<^sup>>-t\<^sup><-2) * (1/6) * 30 / 36 
  = \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>d1\<^sup>> = d2\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> $t\<^sup>> \<ge> $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e  * (5/6)^($t\<^sup>> - $t\<^sup>< - 1) * (1/6))\<^sub>e
= { ... }
  \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>d1\<^sup>> = d2\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e * 1 / 36 + 
  \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e*  \<lbrakk>d1\<^sup>> = d2\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> \<ge> t\<^sup>< + 2\<rbrakk>\<^sub>\<I>\<^sub>e * (5/6)^(t\<^sup>>-t\<^sup><-1) * (1/6)
  = \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>d1\<^sup>> = d2\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> $t\<^sup>> \<ge> $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e  * (5/6)^($t\<^sup>> - $t\<^sup>< - 1) * (1/6))\<^sub>e
= { Not able to combination }
    False

Indeed, Ht is a fixed point where 
  if (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e then ((Pt dice_throw) ; Ht) else II = Ht
*)

(*
definition Ht':: "state_t rvhfun" where 
"Ht' = ((\<lbrakk>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>t\<^sup>> = t\<^sup>< \<and> d1\<^sup>> = d1\<^sup>< \<and> d2\<^sup>> = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e) + 
        \<lbrakk>\<not>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>d1\<^sup>> = d2\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk> $t\<^sup>> \<ge> $t\<^sup>< + 1\<rbrakk>\<^sub>\<I>\<^sub>e  * (5/6)^($t\<^sup>> - $t\<^sup>< - 1) * (1/6))\<^sub>e"

lemma Ht_is_fp: "\<F> (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e (Pt dice_throw) (prfun_of_rvfun (Ht')) = prfun_of_rvfun (Ht')"
  apply (simp add: Ht'_def loopfunc_def)
  apply (simp add: pfun_defs dice_throw_t)
  (* apply (subst dice_throw_t_alt_def) *)
  apply (subst rvfun_skip_inverse)
  apply (subst rvfun_skip\<^sub>_f_simp)
  apply (subst rvfun_seqcomp_inverse)
  apply (simp add: dice_throw_t_is_dist rvfun_inverse rvfun_prob_sum1_summable'(1))
  using ureal_is_prob apply blast
  apply (subst rvfun_inverse)
   apply (simp add: dice_throw_t_is_dist rvfun_prob_sum1_summable'(1))
  apply (subst rvfun_inverse)
  apply (expr_auto add: dist_defs)
  apply (subgoal_tac "((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc t)  \<le> 1")
  apply linarith
  apply (simp add: power_le_one_iff)
  apply (simp only: dice_throw_t_alt_def)
  apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
  apply (expr_simp_1)
  apply (pred_auto)
  apply (simp only: d1_if_simp d2_if_simp)
  defer
  apply (smt (verit, best) divide_eq_0_iff infsum_0 mult_not_zero)
  apply (smt (verit, best) Suc_leD divide_eq_0_iff infsum_0 mult_eq_0_iff not_less_eq_eq)
  apply (simp add: infsum_0)
  apply (auto)
proof -
  fix d1::Tdice and d2::Tdice and t::\<nat> and t\<^sub>v'::\<nat> and d2\<^sub>v'::Tdice
  assume a0: "\<not> d1 = d2"
  assume a1: "Suc t \<le> t\<^sub>v'"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t.
          (if t\<^sub>v v\<^sub>0 = Suc t then 1::\<real> else (0::\<real>)) *
          ((if d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if t\<^sub>v' = t\<^sub>v v\<^sub>0 \<and> d2\<^sub>v' = d1\<^sub>v v\<^sub>0 \<and> d2\<^sub>v' = d2\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) +
           (if \<not> d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * (if Suc (t\<^sub>v v\<^sub>0) \<le> t\<^sub>v' then 1::\<real> else (0::\<real>)) *
           ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc (t\<^sub>v v\<^sub>0)) / (6::\<real>)) / (36::\<real>))"
  have f0: "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t.
          ((if t\<^sub>v v\<^sub>0 = Suc t \<and> t\<^sub>v' = t\<^sub>v v\<^sub>0 \<and> d2\<^sub>v' = d1\<^sub>v v\<^sub>0 \<and> d2\<^sub>v' = d2\<^sub>v v\<^sub>0 then 1/36 else (0::\<real>)) +
           (if t\<^sub>v v\<^sub>0 = Suc t \<and> \<not> d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0 \<and> Suc (Suc t) \<le> t\<^sub>v' then (((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc (Suc t)) / (6::\<real>) / 36) else (0::\<real>))))"
    using infsum_cong divide_eq_0_iff mult_cancel_right1 mult_not_zero by (smt (verit, ccfv_SIG))
  moreover have f1: "... = (if Suc t = t\<^sub>v' then 1/36 else ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc (Suc t)) * 30 / (6::\<real>) / 36)"
    apply (subst infsum_add)
    apply (simp add: infsum_constant_finite_states_summable state_t_finite)
    apply (simp add: infsum_cond_finite_states_summable state_t_finite)
    apply (subst infsum_constant_finite_states_subset)
    apply (simp add: state_t_finite)
    apply (subst infsum_constant_finite_states_subset)
    using state_t_finite apply force
    apply (auto)
  proof -
    assume a: "t\<^sub>v' = Suc t"
    have f0: "{s::state_t. t\<^sub>v s = Suc t \<and> Suc t = t\<^sub>v s \<and> d2\<^sub>v' = d1\<^sub>v s \<and> d2\<^sub>v' = d2\<^sub>v s} = 
          {s::state_t. t\<^sub>v s = Suc t \<and> d2\<^sub>v' = d1\<^sub>v s \<and> d2\<^sub>v' = d2\<^sub>v s}"
      by fastforce
    show "card {s::state_t. t\<^sub>v s = Suc t \<and> Suc t = t\<^sub>v s \<and> d2\<^sub>v' = d1\<^sub>v s \<and> d2\<^sub>v' = d2\<^sub>v s} = Suc (0::\<nat>)"
      apply (simp add: f0)
      by (smt (verit, ccfv_threshold) card_1_singleton old.unit.exhaust state_t.select_convs(1) 
          state_t.select_convs(2) state_t.surjective time.select_convs(1))
  next
    assume a: "\<not> Suc t = t\<^sub>v'"
    have f1: "real (card {s::state_t. t\<^sub>v s = Suc t \<and> t\<^sub>v' = t\<^sub>v s \<and> d2\<^sub>v' = d1\<^sub>v s \<and> d2\<^sub>v' = d2\<^sub>v s}) = 0"
      using a by (simp add: card_0_singleton)
    have f2: "(card {s::state_t. t\<^sub>v s = Suc t \<and> \<not> d1\<^sub>v s = d2\<^sub>v s \<and> Suc (Suc t) \<le> t\<^sub>v'}) = 
      (card {s::state_t. t\<^sub>v s = Suc t \<and> \<not> d1\<^sub>v s = d2\<^sub>v s})"
      by (metis a a1 le_antisym not_less_eq_eq)
    also have "... = 30"
      using state_t_set_d1d2_neq_card by blast
    then show "real (card {s::state_t. t\<^sub>v s = Suc t \<and> t\<^sub>v' = t\<^sub>v s \<and> d2\<^sub>v' = d1\<^sub>v s \<and> d2\<^sub>v' = d2\<^sub>v s}) +
      ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc (Suc t)) * real (card {s::state_t. t\<^sub>v s = Suc t \<and> \<not> d1\<^sub>v s = d2\<^sub>v s \<and> Suc (Suc t) \<le> t\<^sub>v'}) /
      (6::\<real>) = (5::\<real>) * ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc (Suc t))"
      apply (simp add: f1)
      using f2 by linarith
  qed
  show "?lhs * (6::\<real>) =  ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc t)"
    apply (simp only: f0 f1)
    apply (auto)
  proof -
    assume aa: "\<not> Suc t = t\<^sub>v'"
    have f0: "((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc t) * (6::\<real>) = ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc t - 1) * (5/6) * (6::\<real>)"
      by (metis One_nat_def Suc_pred a1 aa bot_nat_0.not_eq_extremum cancel_comm_monoid_add_class.diff_zero diff_diff_cancel power_Suc2)
    have f1: "(t\<^sub>v' - Suc (Suc t)) = (t\<^sub>v' - Suc t - 1)"
      using diff_Suc_eq_diff_pred diff_commute by presburger
    then show "(5::\<real>) * ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc (Suc t)) = ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v' - Suc t) * (6::\<real>)"
      using f0 by auto
  qed
qed
*)

lemma Pt_dice_throw_finite: "\<forall>s. finite {s'::state_t. (0::ureal) < Pt dice_throw (s, s')}"
proof
  fix s 
  show "finite {s'::state_t. (0::ureal) < Pt dice_throw (s, s')} "
    apply (simp add: dice_throw_t)
    apply (simp add: rvfun_ge_zero)
    apply (simp add: dice_throw_t_alt_eq)
    apply (pred_auto)
    by (simp add: state_t_finite)
qed

lemma dice_throw_iterdiff_simp:
  shows "(iterdiff 0 (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e (Pt dice_throw) 1\<^sub>p) = 1\<^sub>p"
        "(iterdiff (n+1) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e (Pt dice_throw) 1\<^sub>p) = 
            prfun_of_rvfun ((\<lbrakk>d1\<^sup>< \<noteq> d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * (5/6)^\<guillemotleft>n\<guillemotright>)\<^sub>e)"
proof -
  show "(iterdiff 0 (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e (Pt dice_throw) 1\<^sub>p) = 1\<^sub>p"
    by (auto)

  show "(iterdiff (n+1) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e (Pt dice_throw) 1\<^sub>p) = 
            prfun_of_rvfun ((\<lbrakk>d1\<^sup>< \<noteq> d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * (5/6)^\<guillemotleft>n\<guillemotright>)\<^sub>e)"
    apply (induction n)
    apply (simp add: pfun_defs dice_throw_t)
    apply (subst dice_throw_t_alt_eq)
    apply (subst ureal_zero)
    apply (subst ureal_one)
    apply (subst rvfun_seqcomp_inverse)
    using dice_throw_t_alt_eq dice_throw_t_alt_inverse dice_throw_t_is_dist apply presburger
    apply (metis ureal_is_prob ureal_one)
    apply (subst rvfun_inverse)
    using dice_throw_t_alt_eq dice_throw_t_is_dist rvfun_prob_sum1_summable'(1) apply auto[1]
    apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
    apply (simp add: fun_eq_iff)
    apply (pred_auto)
    apply (subst infsum_cdiv_left)
    apply (rule infsum_constant_finite_states_summable)
    using state_t_finite apply presburger
    apply (subst infsum_constant_finite_states)
    using state_t_finite apply presburger
    apply (metis One_nat_def card_state_t_set eval_nat_numeral(3) nonzero_mult_div_cancel_right 
        numeral_eq_one_iff of_nat_eq_0_iff of_nat_numeral semiring_norm(84) state_t_set_eq)
  proof -
    fix n
    assume a: "(iter\<^sub>d (n+1) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e (Pt dice_throw) 1\<^sub>p) = 
            prfun_of_rvfun ((\<lbrakk>d1\<^sup>< \<noteq> d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * (5/6)^\<guillemotleft>n\<guillemotright>)\<^sub>e)"
    have f0: "(iter\<^sub>d (Suc n + (1::\<nat>)) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e (Pt dice_throw) 1\<^sub>p) = 
      (pcond (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e ((Pt dice_throw) ; (iter\<^sub>d (Suc n) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e (Pt dice_throw) 1\<^sub>p)) 0\<^sub>p)"
      apply (simp only: add_Suc)
      apply (simp only: iterdiff.simps(2))
      by simp
    also have f1: "... = (pcond (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e ((Pt dice_throw) ; prfun_of_rvfun ((\<lbrakk>d1\<^sup>< \<noteq> d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * (5/6)^\<guillemotleft>n\<guillemotright>)\<^sub>e)) 0\<^sub>p)"
      using a by simp
    also have f2: "... = prfun_of_rvfun ((\<lbrakk>d1\<^sup>< \<noteq> d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * (5/6)^\<guillemotleft>Suc n\<guillemotright>)\<^sub>e)"
      apply (simp add: pfun_defs dice_throw_t) 
      apply (subst dice_throw_t_alt_eq)
      apply (subst ureal_zero)
      apply (subst rvfun_seqcomp_inverse)
      using dice_throw_t_alt_eq dice_throw_t_alt_inverse dice_throw_t_is_dist apply presburger
      apply (metis ureal_is_prob)
      apply (subst rvfun_inverse)
      using dice_throw_t_alt_eq dice_throw_t_is_dist rvfun_prob_sum1_summable'(1) apply auto[1]
      apply (subst rvfun_inverse)
      apply (pred_auto add: dist_defs)
      apply (simp add: power_le_one_iff)
      apply (rule HOL.arg_cong[where f="prfun_of_rvfun"])
      apply (simp add: fun_eq_iff)
      apply (pred_auto)
      proof -
        fix d1 d2::"Tdice" and t::"\<nat>"
        let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t. (if t\<^sub>v v\<^sub>0 = Suc t then 1::\<real> else (0::\<real>)) * 
                ((if \<not> d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((5::\<real>) / (6::\<real>)) ^ n) / (36::\<real>))"
        
        have f0: "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t. (if t\<^sub>v v\<^sub>0 = Suc t \<and> \<not> d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0 then ((((5::\<real>) / (6::\<real>)) ^ n) / (36::\<real>)) else (0::\<real>)))"
          apply (subst infsum_cong[where g = "\<lambda>v\<^sub>0::state_t. (if t\<^sub>v v\<^sub>0 = Suc t \<and> \<not> d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0 then ((((5::\<real>) / (6::\<real>)) ^ n) / (36::\<real>)) else (0::\<real>))"])
          by simp+
        also have f1: "... = 30 * ((((5::\<real>) / (6::\<real>)) ^ n) / (36::\<real>))"
          apply (subst infsum_constant_finite_states)
          apply (simp add: state_t_finite)
          by (simp add: state_t_set_d1d2_neq_card)
        show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t. (if t\<^sub>v v\<^sub>0 = Suc t then 1::\<real> else (0::\<real>)) * 
                ((if \<not> d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((5::\<real>) / (6::\<real>)) ^ n) / (36::\<real>)) 
          * (6::\<real>) = (5::\<real>) * ((5::\<real>) / (6::\<real>)) ^ n"
          by (simp add: f0 f1)
      qed
    show "iter\<^sub>d (Suc n + (1::\<nat>)) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e (Pt dice_throw) 1\<^sub>p =
            prfun_of_rvfun ((\<lbrakk>d1\<^sup>< \<noteq> d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * (5/6)^\<guillemotleft>Suc n\<guillemotright>)\<^sub>e)"
      by (simp only: f0 f1 f2)
  qed
qed

lemma dice_throw_iterdiff_tendsto_0:
  "\<forall>s. (\<lambda>n::\<nat>. ureal2real (iterdiff n (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e (Pt dice_throw) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
proof 
  fix s
  have "(\<lambda>n::\<nat>. ureal2real (iterdiff (n+1) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e (Pt dice_throw) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    apply (subst dice_throw_iterdiff_simp)
    apply (simp add: prfun_of_rvfun_def)
    apply (expr_auto)
    apply (subst real2ureal_inverse)
    apply (simp)
    apply (simp add: power_le_one)
    apply (simp add: LIMSEQ_realpow_zero)
    by (simp add: real2ureal_inverse)
  then show "(\<lambda>n::\<nat>. ureal2real (iterdiff n (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e (Pt dice_throw) 1\<^sub>p s)) \<longlonglongrightarrow> (0::\<real>)"
    by (rule LIMSEQ_offset[where k = 1])
qed

lemma dice_throw_t_loop: "dice_throw_t_loop = prfun_of_rvfun Ht"
  apply (simp add: dice_throw_t_loop_def ptwhile_def)
  apply (subst unique_fixed_point_lfp_gfp_finite_final'[where fp = "prfun_of_rvfun Ht"])
  apply (simp add: dice_throw_t dice_throw_t_is_dist rvfun_inverse rvfun_prob_sum1_summable'(1))
  using Pt_dice_throw_finite apply blast
  using dice_throw_iterdiff_tendsto_0 apply (simp)
  using Ht_is_fp apply blast
  by simp

subsubsection \<open> Termination and average termination time \<close>
lemma Ht_inverse: "rvfun_of_prfun (prfun_of_rvfun Ht) = Ht"
  apply (subst rvfun_inverse)
  using Ht_is_dist rvfun_prob_sum1_summable'(1) apply blast
  by simp

lemma dice_throw_t_termination_prob: "rvfun_of_prfun dice_throw_t_loop ; \<lbrakk>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e = (1)\<^sub>e"
  apply (simp add: dice_throw_t_loop)
  apply (simp add: Ht_inverse)
  apply (simp add: Ht_def)
  apply (expr_auto)
proof -
  fix t::\<nat> and d2::Tdice
  let ?lhs_f = "\<lambda>v\<^sub>0. (if t\<^sub>v v\<^sub>0 = t \<and> d1\<^sub>v v\<^sub>0 = d2 \<and> d2\<^sub>v v\<^sub>0 = d2 then 1::\<real> else (0::\<real>))"
  let ?lhs_f2 = "\<lambda>v\<^sub>0. (if d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>))"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t. ?lhs_f v\<^sub>0 * ?lhs_f2 v\<^sub>0 )"
  have "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t. if t\<^sub>v v\<^sub>0 = t \<and> d1\<^sub>v v\<^sub>0 = d2 \<and> d2\<^sub>v v\<^sub>0 = d2 then 1::\<real> else (0::\<real>))"
    apply (rule infsum_cong)
    by (auto)
  also have "... = 1"
    apply (subst infsum_constant_finite_states)
    by (simp add: state_t_set_eq_1)+
  then show "?lhs = (1::\<real>)"
    using calculation by presburger
next
  fix t::\<nat> and d1 and d2::Tdice
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t. (if d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * 
          (if Suc t \<le> t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc t) *
          (if d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) /  (36::\<real>))"

  have f0: "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t. (if d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0 \<and> Suc t \<le> t\<^sub>v v\<^sub>0 then ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc t) /  (36::\<real>) else (0::\<real>)))"
    by (smt (verit, ccfv_SIG) div_0 infsum_cong mult_cancel_left2 mult_cancel_right2)
  moreover have f1: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t \<in> {v\<^sub>0. d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0 \<and> Suc t \<le> t\<^sub>v v\<^sub>0}.
       ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc t) /  (36::\<real>))"
    apply (rule infsum_cong_neutral)
    by (auto)
  moreover have "... = 1"
    using sum_d1_d2_eq_tt_1 by blast
  then show "?lhs = (1::\<real>)"
    using calculation f0 f1 by presburger
qed

lemma dice_throw_t_expected_termination_time:
  "rvfun_of_prfun dice_throw_t_loop ; (\<guillemotleft>real\<guillemotright> (t\<^sup><))\<^sub>e = (\<lbrakk>d1\<^sup>< \<noteq> d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * (t\<^sup>< + 6)  + \<lbrakk>d1\<^sup>< = d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e * t\<^sup>< )\<^sub>e"
  apply (simp add: dice_throw_t_loop)
  apply (simp add: Ht_inverse)
  apply (pred_auto add: Ht_def)
proof -
  fix t::\<nat> and d2::Tdice
  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t. (if t\<^sub>v v\<^sub>0 = t \<and> d1\<^sub>v v\<^sub>0 = d2 \<and> d2\<^sub>v v\<^sub>0 = d2 then 1::\<real> else (0::\<real>)) * real (t\<^sub>v v\<^sub>0)) 
    = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t. (if t\<^sub>v v\<^sub>0 = t \<and> d1\<^sub>v v\<^sub>0 = d2 \<and> d2\<^sub>v v\<^sub>0 = d2 then real (t) else (0::\<real>)))"
    apply (rule infsum_cong)
    by (auto)
  also have "... = real t"
    apply (subst infsum_constant_finite_states)
    apply (simp add: state_t_set_eq_1)
    by (simp add: state_t_set_eq_1)
  also show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t. (if t\<^sub>v v\<^sub>0 = t \<and> d1\<^sub>v v\<^sub>0 = d2 \<and> d2\<^sub>v v\<^sub>0 = d2 then 1::\<real> else (0::\<real>)) * real (t\<^sub>v v\<^sub>0)) =
       real t"
    using calculation by blast
next
  fix t::\<nat> and d1 and d2::Tdice
  \<comment> \<open> Original functions over state space \<close>
  let ?fs1 = "(\<lambda>v\<^sub>0::state_t. ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc t) * real (t\<^sub>v v\<^sub>0))"
  let ?fs = "(\<lambda>v\<^sub>0::state_t. ?fs1 v\<^sub>0 / (36::\<real>))"
  \<comment> \<open> Reindexed functions over natural numbers \<close>
  let ?fn1 = "(\<lambda>n::\<nat>. (((5::\<real>) / (6::\<real>)) ^ n * real (Suc t + n)))"
  let ?fn = "(\<lambda>n::\<nat>. (?fn1 n / (36::\<real>)))"
  \<comment> \<open> The set of states in which the outcomes of the pair of dice are the same: @{text "d1 = d2"} \<close>
  let ?h_d1d2_eq_set = "\<lambda>i. {v\<^sub>0::state_t. d1\<^sub>v v\<^sub>0 = nat2td i \<and> d2\<^sub>v v\<^sub>0 = nat2td i \<and> Suc t \<le> t\<^sub>v v\<^sub>0}"
  
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t. (if d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * 
      (if Suc t \<le> t\<^sub>v v\<^sub>0 then 1::\<real> else (0::\<real>)) * 
      ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc t) * real (t\<^sub>v v\<^sub>0) / (36::\<real>))"

  \<comment> \<open> Reindex the function over state space to the function over @{text "\<nat>"}, and so we can 
  calculate the summation over geometric progression. \<close>
  have reindex: "\<forall>i\<in>{1..6}. (\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t \<in> ?h_d1d2_eq_set i. ?fs v\<^sub>0) = (\<Sum>\<^sub>\<infinity>n::\<nat>. ?fn n)"
  proof
    fix i::\<nat>
    have set_eq: "{v\<^sub>0. d1\<^sub>v v\<^sub>0 = nat2td i \<and> d2\<^sub>v v\<^sub>0 = nat2td i \<and> Suc t \<le> t\<^sub>v v\<^sub>0} = 
                  range (\<lambda>n::\<nat>. \<lparr>t\<^sub>v = Suc t + n, d1\<^sub>v = nat2td i, d2\<^sub>v = nat2td i\<rparr>)"
      apply (simp add: image_def, auto)
      by (metis add_Suc le_Suc_ex state_t.select_convs(1) state_t.select_convs(2) state_t_neq time.select_convs(1))
    have sum_eq: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t \<in> {v\<^sub>0. d1\<^sub>v v\<^sub>0 = nat2td i \<and> d2\<^sub>v v\<^sub>0 = nat2td i \<and> Suc t \<le> t\<^sub>v v\<^sub>0}.
       ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc t)* real (t\<^sub>v v\<^sub>0) /  (36::\<real>)) = 
      infsum (\<lambda>v\<^sub>0::state_t. ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc t)* real (t\<^sub>v v\<^sub>0) /  (36::\<real>))
      ((\<lambda>n::\<nat>. \<lparr>t\<^sub>v = Suc t + n, d1\<^sub>v = nat2td i, d2\<^sub>v = nat2td i\<rparr>) ` UNIV)"
      by (simp add: set_eq)
    have reindex: "infsum (\<lambda>v\<^sub>0::state_t. ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc t)* real (t\<^sub>v v\<^sub>0) /  (36::\<real>))
      ((\<lambda>n::\<nat>. \<lparr>t\<^sub>v = Suc t + n, d1\<^sub>v = nat2td i, d2\<^sub>v = nat2td i\<rparr>) ` UNIV)
      = infsum (\<lambda>n::\<nat>. ((5::\<real>) / (6::\<real>)) ^ n * real (Suc t + n) /  (36::\<real>)) UNIV"
      apply (subst infsum_reindex)
      apply (simp add: inj_def)
      by (simp add: infsum_cong)
    show "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t | d1\<^sub>v v\<^sub>0 = nat2td i \<and> d2\<^sub>v v\<^sub>0 = nat2td i \<and> Suc t \<le> t\<^sub>v v\<^sub>0.
          ((5::\<real>) / (6::\<real>)) ^ (t\<^sub>v v\<^sub>0 - Suc t) * real (t\<^sub>v v\<^sub>0) / (36::\<real>)) 
      = (\<Sum>\<^sub>\<infinity>n::\<nat>. ((5::\<real>) / (6::\<real>)) ^ n * real (Suc t + n) / (36::\<real>))"
      by (simp only: sum_eq reindex)
  qed

  \<comment> \<open> Prove the function is summable over @{text "\<nat>"} based on the ratio test, that is, 
  the sequence decreases at least a ratio (less than 1) after some n. \<close>
  have summable_n_6_5_power_n: "summable (\<lambda>n::\<nat>. (n / (6/5)^n))"
  (* n:                       0,       1,         2,         3,         4         5, 6*)
  (* n/(6/5)^n                0,       1/(6/5)^1, 2/(6/5)^2, 3/(6/5)^3, 4/(6/5)^4 *)
  (* (n+1)/((6/5)^(n+1)):     1/(6/5), 2/(6/5)^2, 3/(6/5)^3, 4/(6/5)^4, 5/(6/5)^4 *)
  (* ratio ((n+1)/(6/5)*n):   x,       5/3,       5/4,       10/9,      25/24,    1, 35/36 *)
    apply (subst summable_ratio_test[where c="35/36" and N="6"])
    apply auto
  proof -
    fix n::\<nat>
    assume a1: "6 \<le> n"
    have f1: "((5::\<real>) + real n * (5::\<real>)) / (6::\<real>) \<le> (35::\<real>) * real n / (36::\<real>)"
      using a1 by force
    have f2: "(((5::\<real>) + real n * (5::\<real>)) / (6::\<real>)) / (6/5)^n \<le> ((35::\<real>) * real n / (36::\<real>)) / (6/5)^n"
      apply (subst divide_right_mono)
      apply (simp add: f1 a1)
      by simp+
    show "((5::\<real>) + real n * (5::\<real>)) / ((6::\<real>) * ((6::\<real>) / (5::\<real>)) ^ n) \<le> (35::\<real>) * real n / ((36::\<real>) * ((6::\<real>) / (5::\<real>)) ^ n) "
      using f2 by simp
  qed

  have summable_fn1: "summable ?fn1"
  proof -
    have f1: "(\<lambda>n::\<nat>. ((5::\<real>) / (6::\<real>)) ^ n * ((1::\<real>) + (real t + real n))) = 
          (\<lambda>n::\<nat>. ((5::\<real>) / (6::\<real>)) ^ n * (1 + real t)  + ((5::\<real>) / (6::\<real>)) ^ n * (n))"
      by (simp add: add.assoc mult.commute ring_class.ring_distribs(2))
    show ?thesis
      apply (simp add: f1)
      apply (subst summable_add)
      apply (rule summable_mult2)
      apply (rule summable_geometric)
      apply simp
      apply (subst summable_cong[where g = "(\<lambda>n::\<nat>. (n / (6/5)^n))"])
      apply (simp add: power_divide)
      using summable_n_6_5_power_n apply blast
      by simp
  qed

  have summable_fn: "summable ?fn"
    apply (simp add: suminf_divide)
    using summable_fn1 by simp

  have summable_fn_suc_n: "summable (\<lambda>n. ?fn (Suc n))"
    apply (subst summable_Suc_iff)
    using summable_fn by auto

  \<comment> \<open>The general idea to find out what @{text "?fn"} sums to is to solve an equation.
  \begin{itemize}
    \item @{text "(\<lambda>n. ?fn (Suc n))"} is summable, then @{text "\<Sum>n. ?fn (Suc n)"} sums to a value, 
      say @{text "l"}.
    \item @{text "(\<lambda>n. ?fn (n))"} sums to @{text "(l + ?fn 0)"}
    \item Calculate @{text "suminf (\<lambda>n. ?fn (Suc n))"} by expressing it as @{text "(\<lambda>n. ?fn (n + 1))"}
      and then expand @{text "n+1"} to get the result in terms of @{text "suminf (\<lambda>n. ?fn (n))"}, say
      @{text "g(suminf (\<lambda>n. ?fn (n)))"}
    \item Now the equation is @{text "l = g(l + ?fn 0)"}, whose LHS and RHS only contain one variable 
      @{text "l"}. Solve the equation to get @{text "l"}
  \end{itemize} 
    \<close>
  obtain l where P_l: "(\<lambda>n. ?fn (Suc n)) sums l"
    using summable_fn_suc_n by blast

  have sum_f0: "(\<lambda>n. ?fn (Suc n)) sums l \<longleftrightarrow> ?fn sums (l + ?fn 0)"
    apply (subst sums_Suc_iff)
    by simp

  have suminf_f_l: "?fn sums (l + ?fn 0)"
    using P_l sum_f0 by blast

  have suminf_f_l': "suminf ?fn = l + real (Suc t) / 36"
    using suminf_f_l sums_unique by fastforce

  \<comment> \<open>@{text "?fn (Suc n)"} \<close>
  have suminf_fn_suc_n: "(\<Sum>n::\<nat>. ((5::\<real>) / (6::\<real>)) ^ n * (1 + (Suc t + n)) / (36::\<real>)) =  
        (\<Sum>n::\<nat>. ((5::\<real>) / (6::\<real>)) ^ n / 36 +  ((5::\<real>) / (6::\<real>)) ^ n * real ((Suc t) + n) / (36::\<real>))"
    apply (rule suminf_cong)
    by (simp add: ring_class.ring_distribs(1))
  also have suminf_fn_suc_n': 
    "... = (\<Sum>n::\<nat>. ((5::\<real>) / (6::\<real>)) ^ n / 36) +  (\<Sum>n::\<nat>. ((5::\<real>) / (6::\<real>)) ^ n * real ((Suc t) + n) / (36::\<real>))"
    apply (subst suminf_add)
    apply (rule summable_divide)
    apply (rule summable_geometric)
    apply simp
    apply (rule summable_comparison_test[where g = "(\<lambda>n::\<nat>. ((5::\<real>) / (6::\<real>)) ^ n * ((1::\<real>) + (real t + real n)) /36)"])
    apply (simp)
    using summable_fn by simp+
  also have suminf_fn_suc_n'': 
    "... = (\<Sum>n::\<nat>. ((5::\<real>) / (6::\<real>)) ^ n) / 36 +  l + real (Suc t) / 36"
    apply (subst suminf_divide)
    apply (simp add: summable_geometric)
    by (simp only: suminf_f_l')
  also have suminf_fn_suc_n''': "... = 1/6 +  l + real (Suc t) / 36"
    by (simp add: suminf_geometric)

  have suminf_f_suc_n: "(\<Sum>n::\<nat>. ((5::\<real>) / (6::\<real>)) ^ n * (1 + (Suc t + n)) / (36::\<real>)) = 
    (\<Sum>n::\<nat>. (((5::\<real>) / (6::\<real>)) ^ (Suc n) * ((Suc t + Suc n)) / (36::\<real>)) / (5/6))"
    by (simp add: suminf_cong)
  \<comment> \<open> Move @{text "(5/6)"} outside of the sum \<close>
  also have "... = (\<Sum>n::\<nat>. (((5::\<real>) / (6::\<real>)) ^ (Suc n) * ((Suc t + Suc n)) / (36::\<real>))) / (5/6)"
    apply (subst suminf_divide)
    using summable_fn_suc_n apply blast
    by simp
  also have "... = (suminf (\<lambda>n. ?fn (Suc n))) / (5/6)"
    by meson
  moreover have "... = l / (5/6)"
    using P_l sums_unique by blast
  \<comment> \<open> Calculate @{text "l"} by solving an equation \<close>
  then have "1/6 + l + real (Suc t) / 36 = l / (5/6)"
    using calculation(1) suminf_fn_suc_n''' by presburger
  then have "5/6 + 5*l + 5 * real (Suc t) / 36 = 6 * l"
    by auto
  then have suminf_f_suc_n_l: "5/6 + 5 * real (Suc t) / 36 = l"
    by auto

  have suc_t_n: "\<forall>n. 1 + (real t + real n) = real (Suc t + n)"
    by auto

  have geometry_sum: "(\<Sum>\<^sub>\<infinity>n::\<nat>. ?fn n) = 5/6 + 5 * real (Suc t) / 36 + real (Suc t) / (36::\<real>)"
    apply (subst infsetsum_infsum[symmetric])
    apply (simp add: abs_summable_on_nat_iff')
    using summable_fn1 apply simp
    apply (subst infsetsum_nat)
    apply (simp add: abs_summable_on_nat_iff')
    using summable_fn1 apply simp
    apply auto
    apply (simp only: suc_t_n)
    apply (simp only: suminf_f_l')
    using suminf_f_suc_n_l by auto
  then have geometry_sum': "... = 5/6 + real (Suc t) / 6"
    apply (auto) by (simp add: add_divide_distrib)

  have fs_summable: "\<forall>i\<in>{1..6}. (?fs) summable_on ?h_d1d2_eq_set i"
  proof
    fix i
    assume a: "i \<in> outcomes"
    show "(?fs) summable_on ?h_d1d2_eq_set i"
    proof (rule ccontr)
      assume "\<not> (?fs) summable_on ?h_d1d2_eq_set i"
      then have f1: "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t \<in> ?h_d1d2_eq_set i. ?fs v\<^sub>0) = 0"
        using infsum_not_exists by blast
      have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t \<in> ?h_d1d2_eq_set i. ?fs v\<^sub>0) \<noteq> 0"
        apply (subst reindex)
        apply (simp only: a)
        using geometry_sum by linarith
      then show "False"
        using f1 by blast
    qed
  qed

  have f0: "?lhs = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t. (if d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0 \<and> Suc t \<le> t\<^sub>v v\<^sub>0 then ?fs v\<^sub>0 else (0::\<real>)))"
    apply (rule infsum_cong)
    by (auto)
  moreover have f1: "... = (\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t \<in> {v\<^sub>0. d1\<^sub>v v\<^sub>0 = d2\<^sub>v v\<^sub>0 \<and> Suc t \<le> t\<^sub>v v\<^sub>0}. ?fs v\<^sub>0)"
    apply (rule infsum_cong_neutral)
    by (auto)
  \<comment> \<open> An important step to turn the summation over a set of states where @{text "d1=d2"} into a finite 
    sum of (the summation over a set of states @{text "d1=d2=i"}) over @{text "i \<in> {1..6}"}. \<close>
  moreover have "... = sum (\<lambda>i. (\<Sum>\<^sub>\<infinity>v\<^sub>0::state_t \<in> ?h_d1d2_eq_set i. ?fs v\<^sub>0)) {1..6}"
    apply (simp add: state_eq_set_Union)
    apply (subst sum_infsum)
    apply blast
    apply (simp add: fs_summable)
    apply (auto)
    by (simp add: nat2td_inject)
  moreover have "... = sum (\<lambda>i. (\<Sum>\<^sub>\<infinity>n::\<nat>. ?fn n)) {1::\<nat>..6}"
    using reindex by simp
  moreover have "... = sum (\<lambda>i. 5/6 + real (Suc t) / 6) {1::\<nat>..6}"
    using geometry_sum geometry_sum' nat2td_cases by metis
  moreover have "... = (5/6 + real (Suc t) / 6) * 6"
    apply (subst sum_constant)
    by force
  moreover have "... = 5 + real (Suc t)"
    by simp
     
  ultimately show "?lhs = real t + 6"
    using f0 f1 by linarith
qed


(* subsection \<open> Die program with time \<close> 
text \<open> We use @{typ "nat"} as the type for dice outcome, then restrict it to [1..6] when uniformly 
choosing the outcomes of two dice. By this way, the state space itself is not finite because natural 
numbers are infinite. \<close>

alphabet dstate = 
  d1 :: nat
  d2 :: nat

definition dice_throw:: "dstate prhfun" where
"dice_throw = prfun_of_rvfun (d1 \<^bold>\<U> outcomes) ; prfun_of_rvfun (d2 \<^bold>\<U> outcomes)"

definition dice_throw_loop where
"dice_throw_loop = while\<^sub>p (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e do dice_throw od"

definition H:: "dstate rvhfun" where 
"H = (\<lbrakk>d1\<^sup>> = d2\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e"

term "(\<lambda>n. iter\<^sub>p n (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p)"

definition dice_iterate_n :: "\<nat> \<Rightarrow> dstate prhfun" where
"dice_iterate_n = (\<lambda>n. iter\<^sub>p n (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p)"

lemma r_simp: "rvfun_of_prfun [\<lambda>\<s>::dstate \<times> dstate. p]\<^sub>e = (\<lambda>s. ureal2real p)"
  by (simp add: SEXP_def rvfun_of_prfun_def)

lemma d1_uni_is_dist: "is_final_distribution (rvfun_of_prfun (prfun_of_rvfun (d1 \<^bold>\<U> outcomes)))"
  apply (subst rvfun_uniform_dist_is_dist')
  apply blast
  by simp+

lemma d2_uni_is_dist: "is_final_distribution (rvfun_of_prfun (prfun_of_rvfun (d2 \<^bold>\<U> outcomes)))"
  apply (subst rvfun_uniform_dist_is_dist')
  apply blast
  by simp+
  
lemma dice_throw_is_dist: "is_final_distribution (rvfun_of_prfun dice_throw)"
  apply (simp only: dice_throw_def pseqcomp_def)
  apply (subst rvfun_seqcomp_inverse)
  using d1_uni_is_dist apply blast
  using ureal_is_prob apply blast
  apply (subst rvfun_seqcomp_is_dist)
  using d1_uni_is_dist apply blast
  using d2_uni_is_dist by blast+

lemma dice_throw_altdef: "rvfun_of_prfun dice_throw = (\<lbrakk>d1\<^sup>> \<in> outcomes\<rbrakk>\<^sub>\<I>\<^sub>e * \<lbrakk>d2\<^sup>> \<in> outcomes\<rbrakk>\<^sub>\<I>\<^sub>e / 36)\<^sub>e"
  apply (simp add: dice_throw_def pseqcomp_def)
  apply (subst rvfun_uniform_dist_inverse)
  apply (simp)+
  apply (subst rvfun_uniform_dist_inverse)
  apply (simp)+
  apply (subst rvfun_seqcomp_inverse)
  apply (simp add: rvfun_uniform_dist_is_dist)
  using d2_vwb_lens rvfun_uniform_dist_is_prob apply blast
  apply (subst rvfun_uniform_dist_altdef)
  apply (simp)+
  apply (subst rvfun_uniform_dist_altdef)
  apply (simp)+
  apply (pred_auto)
  defer
  apply (smt (verit, ccfv_SIG) atLeastAtMost_iff divide_eq_0_iff dstate.ext_inject 
        dstate.update_convs(2) infsum_0 mult_eq_0_iff)
  apply (smt (verit, ccfv_SIG) atLeastAtMost_iff divide_eq_0_iff dstate.ext_inject 
        dstate.update_convs(2) infsum_0 mult_eq_0_iff)
  apply (smt (verit, ccfv_SIG) atLeastAtMost_iff divide_eq_0_iff dstate.ext_inject 
        dstate.update_convs(2) infsum_0 mult_eq_0_iff)
  apply (smt (verit, ccfv_SIG) atLeastAtMost_iff divide_eq_0_iff dstate.ext_inject 
        dstate.update_convs(2) infsum_0 mult_eq_0_iff)
proof -
  fix d2\<^sub>v d1\<^sub>v d2\<^sub>v'
  assume a1: "Suc (0::\<nat>) \<le> d1\<^sub>v"
  assume a2: "d1\<^sub>v \<le> (6::\<nat>)"
  assume a3: "Suc (0::\<nat>) \<le> d2\<^sub>v'"
  assume a4: "d2\<^sub>v' \<le> (6::\<nat>)"
  let ?f1 = "\<lambda>v\<^sub>0. (if \<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. v\<^sub>0 = \<lparr>d1\<^sub>v = x, d2\<^sub>v = d2\<^sub>v\<rparr> then 1::\<real> else (0::\<real>)) *
          (if \<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. \<lparr>d1\<^sub>v = d1\<^sub>v, d2\<^sub>v = d2\<^sub>v'\<rparr> =v\<^sub>0\<lparr>d2\<^sub>v := x\<rparr> then 1::\<real> else (0::\<real>))"
  let ?f2 = "\<lambda>v\<^sub>0. (if (\<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. v\<^sub>0 = \<lparr>d1\<^sub>v = x, d2\<^sub>v = d2\<^sub>v\<rparr> \<and> 
              (\<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. \<lparr>d1\<^sub>v = d1\<^sub>v, d2\<^sub>v = d2\<^sub>v'\<rparr> =v\<^sub>0\<lparr>d2\<^sub>v := x\<rparr>)) 
              then 1::\<real> else (0::\<real>))"
  let ?lhs = "(\<Sum>\<^sub>\<infinity>v\<^sub>0::dstate. ?f1 v\<^sub>0 / (36::\<real>))"
  have f1_f2_eq: "\<forall>v\<^sub>0. ?f1 v\<^sub>0 = ?f2 v\<^sub>0"
    by simp

  have finite_d1: "finite {s::dstate. (\<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. \<lparr>d1\<^sub>v = x, d2\<^sub>v = d2\<^sub>v'\<rparr> = s)}"
    apply (subst finite_Collect_bex)
    by (simp)+

  have set_eq: "{v\<^sub>0::dstate. \<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. v\<^sub>0 = \<lparr>d1\<^sub>v = x, d2\<^sub>v = d2\<^sub>v\<rparr> \<and> 
                    (\<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. \<lparr>d1\<^sub>v = d1\<^sub>v, d2\<^sub>v = d2\<^sub>v'\<rparr> = v\<^sub>0\<lparr>d2\<^sub>v := x\<rparr>)}
    = {v\<^sub>0::dstate. \<lparr>d1\<^sub>v = d1\<^sub>v, d2\<^sub>v = d2\<^sub>v\<rparr> = v\<^sub>0}"
    using a1 a2 a3 a4 by fastforce

  have "(\<Sum>\<^sub>\<infinity>v\<^sub>0::dstate. ?f1 v\<^sub>0) = (\<Sum>\<^sub>\<infinity>v\<^sub>0::dstate. ?f2 v\<^sub>0)"
    using f1_f2_eq infsum_cong by presburger
  also have "... = card {v\<^sub>0. \<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}.
       v\<^sub>0 = \<lparr>d1\<^sub>v = x, d2\<^sub>v = d2\<^sub>v\<rparr> \<and> (\<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. \<lparr>d1\<^sub>v = d1\<^sub>v, d2\<^sub>v = d2\<^sub>v'\<rparr> = v\<^sub>0\<lparr>d2\<^sub>v := x\<rparr>)}"
    apply (subst infsum_constant_finite_states)
    apply (subst finite_subset[where B = "{s::dstate. (\<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. s= \<lparr>d1\<^sub>v = x, d2\<^sub>v = d2\<^sub>v\<rparr>)}"])
    apply blast
    by (simp add: finite_d1)+
  also have lhs_1: "... = 1"
    using set_eq by simp
  show "?lhs * (36::\<real>) = (1::\<real>)"
    apply (subst infsum_cdiv_left)
    apply (simp add: f1_f2_eq)
    apply (subst infsum_constant_finite_states_summable)
    apply (subst finite_subset[where B = "{s::dstate. (\<exists>x::\<nat>\<in>{Suc (0::\<nat>)..6::\<nat>}. \<lparr>d1\<^sub>v = x, d2\<^sub>v = d2\<^sub>v\<rparr> = s)}"])
    apply blast
    apply (simp add: finite_d1)+
    using lhs_1 calculation by presburger
qed
*)
(*
lemma dstate_UNIV_set: "(UNIV::\<bbbP> dstate) = {\<lparr>c\<^sub>v = chead\<rparr>, \<lparr>c\<^sub>v = ctail\<rparr>}"
  apply (auto)
  by (metis Tcoin.exhaust dstate.cases)

lemma dstate_rel_UNIV_set:
  "{s::dstate \<times> dstate. True} = {(\<lparr>c\<^sub>v = chead\<rparr>, \<lparr>c\<^sub>v = chead\<rparr>), 
  (\<lparr>c\<^sub>v = chead\<rparr>, \<lparr>c\<^sub>v = ctail\<rparr>),  (\<lparr>c\<^sub>v = ctail\<rparr>, \<lparr>c\<^sub>v = ctail\<rparr>), (\<lparr>c\<^sub>v = ctail\<rparr>, \<lparr>c\<^sub>v = chead\<rparr>)}"
  apply (simp)
  apply (subst set_eq_iff)
  apply (rule allI)
  apply (rule iffI)
  apply (clarify)
  using dstate_UNIV_set apply blast
  apply (clarify)
  by blast

lemma ureal2real_1_2: "ureal2real (ereal2ureal (ereal (1::\<real>))) / (2::\<real>) = (1::\<real>) / (2::\<real>)"
  apply (simp add: ureal_defs)
  using real_1 by presburger

lemma sum_1_2: "(sum ((^) ((1::\<real>) / (2::\<real>))) {Suc (0::\<nat>)..n} +
               ((1::\<real>) / (2::\<real>)) ^ n / (2::\<real>)) = 
  (sum ((^) ((1::\<real>) / (2::\<real>))) {Suc (0::\<nat>)..n+1})"
  by (metis (no_types, lifting) One_nat_def Suc_1 Suc_eq_plus1 add_is_0 less_Suc0 one_neq_zero 
      one_power2 power_Suc power_add power_one_over sum.cl_ivl_Suc times_divide_eq_left times_divide_eq_right)

lemma sum_geometric_series: 
  (* "(sum ((^) ((1::\<real>) / (2::\<real>))) {Suc (0::\<nat>)..n + (1::\<nat>)}) = (1 - 1 / 2 ^ (n+2)) / (1 - 1/2) - 1" *)
  "(sum ((^) ((1::\<real>) / (2::\<real>))) {Suc (0::\<nat>)..n + (1::\<nat>)}) = 1 - 1 / 2 ^ (n+1)"
  apply (induction n)
  apply (simp)
  by (simp add: power_one_over sum_gp)

lemma sum_geometric_series_1: 
  "(sum ((^) ((1::\<real>) / (2::\<real>))) {1..n + (1::\<nat>)}) = 1 - 1 / 2 ^ (n+1)"
  apply (induction n)
   apply (simp)
  using One_nat_def sum_geometric_series by presburger

lemma sum_geometric_series': 
  "(sum ((^) ((1::\<real>) / (2::\<real>))) {Suc (0::\<nat>)..n}) = 1 - 1 / 2 ^ (n)"
  apply (induction n)
  apply (simp)
  by (simp add: power_one_over sum_gp)

lemma sum_geometric_series_ureal:
  "ureal2real (ereal2ureal (ereal (sum ((^) ((1::\<real>) / (2::\<real>))) {Suc (0::\<nat>)..n + (1::\<nat>)}))) / (2::\<real>)
  = (1 - 1 / 2 ^ (n+1))/2"
  apply (subst sum_geometric_series)
  apply (simp add: ureal_defs)
  apply (subst real2uereal_inverse)
  using max.cobounded1 apply blast
   apply simp
  apply (simp add: max_def)
  by (smt (z3) one_le_power)

lemma iterate_dice_throw_bottom_simp:
  shows "iter\<^sub>p 0 (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p = 0\<^sub>p"
        "iter\<^sub>p (Suc 0) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p = (\<lbrakk>$c\<^sup>< = chead \<and> $c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)"
        "iter\<^sub>p (n+2) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p = 
              (\<lbrakk>$c\<^sup>< = chead \<and> $c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e + 
               \<lbrakk>$c\<^sup>< = ctail \<and> $c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e * (\<Sum>i\<in>{1..\<guillemotleft>n+1\<guillemotright>}. (1/2)^i))\<^sub>e"
  apply (auto)
  apply (simp add: loopfunc_def)
  apply (simp add: prfun_zero_right')
  apply (simp add: pfun_defs)
  apply (subst rvfun_skip_inverse)
  apply (subst ureal_zero)
  apply (simp add: ureal_defs)
  apply (subst fun_eq_iff)
  apply (expr_auto)
  apply (meson Tcoin.exhaust)
  apply (induct_tac n)
  apply (simp)
  apply (simp add: loopfunc_def)
  apply (simp add: prfun_zero_right')
  apply (simp add: pfun_defs)
  apply (subst rvfun_skip_inverse)+
  apply (subst ureal_zero)
  apply (subst rvfun_pcond_inverse)
  apply (metis ureal_is_prob ureal_zero)
  apply (simp add: rvfun_skip_f_is_prob)
  apply (subst dice_throw_altdef)
  apply (subst rvfun_inverse)
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: infsum_nonneg iverson_bracket_def)
  apply (pred_auto)
  apply (simp add: dstate_UNIV_set)
  apply (smt (verit, ccfv_SIG) prfun_in_0_1' rvfun_skip_inverse)
  apply (simp add: prfun_of_rvfun_def)
  apply (expr_auto)
  apply (simp add: real2ureal_def)
  apply (simp add: infsum_0 iverson_bracket_def real2ureal_def rel_skip)
  apply (meson Tcoin.exhaust)
  apply (simp add: dstate_UNIV_set)
  apply (pred_auto)
  apply (simp add: real2ureal_def)
  using real2ureal_def apply blast+
  apply (simp add: dstate_UNIV_set)
  apply (pred_auto)
  using real2ureal_def apply blast+
  apply (simp add: dstate_UNIV_set)
  apply (pred_auto)
  using real2ureal_def apply blast+
  (* *)
  apply (simp)
  apply (subst loopfunc_def)
  apply (subst pseqcomp_def)
  apply (subst pcond_def)
  apply (subst dice_throw_altdef)
  apply (subst rvfun_inverse)
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: infsum_nonneg  prfun_in_0_1')
  apply (pred_auto)
  apply (simp add: dstate_UNIV_set)
  apply (simp add: rvfun_of_prfun_def)
  apply (auto)
  apply (smt (verit, best) field_sum_of_halves ureal_upper_bound)
  using ureal_upper_bound apply blast
  apply (subst prfun_of_rvfun_def)
  apply (subst rvfun_of_prfun_def)+
  apply (expr_auto)
  apply (simp add: dstate_UNIV_set)
  apply (pred_auto)
  defer
  apply (subst prfun_skip_id)
  apply (simp add: one_ureal.rep_eq real2ureal_def ureal2real_def)
  using Tcoin.exhaust apply blast
  apply (metis (full_types) Tcoin.exhaust dstate.select_convs(1) ereal_real o_def prfun_skip_not_id real2ureal_def ureal2real_def zero_ereal_def zero_ureal.rep_eq)
  apply (subst infsum_0)
  apply (subst ureal_defs)
  apply (smt (verit, best) divide_eq_0_iff ereal_max min.absorb2 min.commute mult_eq_0_iff o_apply real_of_ereal_0 ureal2ereal_inverse ureal2real_def zero_ereal_def zero_less_one_ereal zero_ureal.rep_eq)
  using real2ureal_def apply presburger
  using Tcoin.exhaust apply blast
  apply (subst infsum_0)
  apply (subst ureal_defs)
  apply (smt (verit, best) divide_eq_0_iff ereal_max min.absorb2 min.commute mult_eq_0_iff o_apply real_of_ereal_0 ureal2ereal_inverse ureal2real_def zero_ereal_def zero_less_one_ereal zero_ureal.rep_eq)
  using real2ureal_def apply blast
  apply (metis (full_types) Tcoin.exhaust dstate.ext_inject o_def prfun_skip_not_id real2ureal_def real_of_ereal_0 ureal2real_def zero_ureal.rep_eq)
  apply (subst ureal2real_1_2)
  apply (subst sum_1_2)
  apply (subst sum_geometric_series_ureal)
  apply (subst sum_geometric_series')
  apply (subst ureal_defs)+
proof -
  fix n
  have f1: "((1::\<real>) / (2::\<real>) + ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ (n + (1::\<nat>))) / (2::\<real>)) = 
        ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ (n + 2))"
    by (simp add: add.assoc diff_divide_distrib)
  have f2: "((3::\<real>) * ((1::\<real>) / (2::\<real>)) ^ n / (4::\<real>) + ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ n)) =  
          ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ (n+2))"
    apply (auto)
    by (simp add: power_one_over)
  show "ereal2ureal' (min (max (0::ereal) (ereal ((1::\<real>) / (2::\<real>) + ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ (n + (1::\<nat>))) / (2::\<real>)))) (1::ereal)) =
       ereal2ureal' (min (max (0::ereal) (ereal ((3::\<real>) * ((1::\<real>) / (2::\<real>)) ^ n / (4::\<real>) + ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ n)))) (1::ereal))"
    using f1 f2 by presburger
qed

lemma dice_throw_drop_initial_segments_eq: 
  "(\<Squnion>n::\<nat>. iter\<^sub>p (n+2) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p) = (\<Squnion>n::\<nat>. iter\<^sub>p (n) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p)"
  apply (rule increasing_chain_sup_subset_eq)
  apply (rule iterate_increasing_chain)
  by (simp add: dice_throw_is_dist)

lemma dice_throw_iterate_limit_sup:
  assumes "f = (\<lambda>n. (iter\<^sub>p (n+2) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p))"
  shows "(\<lambda>n. ureal2real (f n s)) \<longlonglongrightarrow> (ureal2real (\<Squnion>n::\<nat>. f n s))"
  apply (simp only: assms)
  apply (subst LIMSEQ_ignore_initial_segment[where k = "2"])
  apply (subst increasing_chain_sup_subset_eq[where m = "2"])
  apply (rule increasing_chain_fun)
  apply (rule iterate_increasing_chain)
  apply (simp add: dice_throw_is_dist)
  apply (subst increasing_chain_limit_is_lub')
  apply (simp add: increasing_chain_def)
  apply (auto)
  apply (rule le_funI)
  by (smt (verit, ccfv_threshold) dice_throw_is_dist iterate_increasing2 le_fun_def)

lemma fa: "(\<lambda>n::\<nat>. ureal2real (ereal2ureal (ereal ((1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ n)))))
  = (\<lambda>n::\<nat>. ((1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ n)))"
  apply (subst fun_eq_iff)
  apply (auto)
  apply (simp add: ureal_defs)
  apply (subst real2uereal_inverse)
   apply (meson max.cobounded1)
   apply simp
proof -
  fix x
  have f1: "(max (0::ereal) (ereal ((1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ x)))) = 
    (ereal ((1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ x)))"
    apply (simp add: max_def)
    by (smt (z3) one_le_power)
  show "real_of_ereal (max (0::ereal) (ereal ((1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ x)))) =
       (1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ x)"
    by (simp add: f1)
qed

lemma fb: 
  " (\<lambda>n::\<nat>. (1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ n)) \<longlonglongrightarrow> (1::\<real>)"
proof -
  have f0: "(\<lambda>n::\<nat>. ((1::\<real>) - ((1::\<real>) / (2::\<real>)) ^ (n+1))) = (\<lambda>n::\<nat>. (1::\<real>) - (1::\<real>) / ((2::\<real>) * (2::\<real>) ^ n))"
    apply (subst fun_eq_iff)
    apply (auto)
    using power_one_over by blast
  have f1: "(\<lambda>n::\<nat>. ((1::\<real>) - ((1::\<real>) / (2::\<real>)) ^ (n+1))) \<longlonglongrightarrow> (1 - 0)"
    apply (rule tendsto_diff)
    apply (auto)
    apply (rule LIMSEQ_power_zero)
    by simp
  show ?thesis
    using f0 f1 by auto
qed

lemma dice_throw_iterate_limit_cH:
  assumes "f = (\<lambda>n. (iter\<^sub>p (n+2) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p))"
  shows "(\<lambda>n. ureal2real (f n s)) \<longlonglongrightarrow> ((\<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e s)"
  apply (simp only: assms)
  apply (subst iterate_dice_throw_bottom_simp(3))
  apply (subst sum_geometric_series_1)
  apply (pred_auto)
  apply (simp add: fa)
  apply (simp add: fb)
  apply (metis LIMSEQ_const_iff nle_le real2ureal_def ureal_lower_bound ureal_real2ureal_smaller)
  apply (metis comp_def one_ereal_def one_ureal.rep_eq one_ureal_def real_ereal_1 tendsto_const ureal2real_def)
  apply (metis LIMSEQ_const_iff nle_le real2ureal_def ureal_lower_bound ureal_real2ureal_smaller)
  by (meson Tcoin.exhaust)+

lemma fh:
  assumes "f = (\<lambda>n. (iter\<^sub>p (n+2) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p))"
  shows "((\<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e s) = (ureal2real (\<Squnion>n::\<nat>. f n s))"
  apply (subst LIMSEQ_unique[where X = "(\<lambda>n. ureal2real (f n s))" and a = "((\<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e s)" and 
          b = "(ureal2real (\<Squnion>n::\<nat>. f n s))"])
  using dice_throw_iterate_limit_cH apply (simp add: assms)
  using dice_throw_iterate_limit_sup apply (simp add: assms)
  by auto

lemma fi: "(\<Squnion>n::\<nat>. iter\<^sub>p (n+2) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p) = 
  (\<lambda>x::dstate \<times> dstate. ereal2ureal (ereal ((\<lbrakk>c\<^sup>> = chead\<rbrakk>\<^sub>\<I>\<^sub>e)\<^sub>e x)))"
  apply (simp only: fh)
  apply (simp add: ureal2rereal_inverse)
  using SUP_apply by fastforce
*)
(*
lemma iterate_dice_throw_bottom_simp:
  shows "f 0 = 0\<^sub>p"
        "f (Suc 0) = (\<lbrakk>$d1\<^sup>< = $d2\<^sup>< \<and> $d1\<^sup>> = $d1\<^sup>< \<and> $d2\<^sup>> = $d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e)"
        "iter\<^sub>p (n+2) (d1\<^sup>< \<noteq> d2\<^sup><)\<^sub>e dice_throw 0\<^sub>p = 
              (\<lbrakk>d1\<^sup>> = d2\<^sup>> \<and> $d1\<^sup>> = $d1\<^sup>< \<and> $d2\<^sup>> = $d2\<^sup><\<rbrakk>\<^sub>\<I>\<^sub>e + 
               \<lbrakk>d1\<^sup>> = d2\<^sup>>\<rbrakk>\<^sub>\<I>\<^sub>e * (\<Sum>i\<in>{1..\<guillemotleft>n+1\<guillemotright>}. (1/2)^i))\<^sub>e"
  apply (simp add: f_def)+
  apply (simp add: loopfunc_def)
  apply (simp add: prfun_zero_right')
  apply (simp add: pfun_defs)
  apply (subst rvfun_skip_inverse)
  apply (subst ureal_zero)
  apply (simp add: ureal_defs)
  apply (subst fun_eq_iff)
  apply (expr_auto)

  apply (meson Tcoin.exhaust)
  apply (induct_tac n)
  apply (simp)
  apply (simp add: loopfunc_def)
  apply (simp add: prfun_zero_right')
  apply (simp add: pfun_defs)
  apply (subst rvfun_skip_inverse)+
  apply (subst ureal_zero)
  apply (subst rvfun_pcond_inverse)
  apply (metis ureal_is_prob ureal_zero)
  apply (simp add: rvfun_skip_f_is_prob)
  apply (subst dice_throw_altdef)
  apply (subst rvfun_inverse)
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: infsum_nonneg iverson_bracket_def)
  apply (pred_auto)
  apply (simp add: dstate_UNIV_set)
  apply (smt (verit, ccfv_SIG) prfun_in_0_1' rvfun_skip_inverse)
  apply (simp add: prfun_of_rvfun_def)
  apply (expr_auto)
  apply (simp add: real2ureal_def)
  apply (simp add: infsum_0 iverson_bracket_def real2ureal_def rel_skip)
  apply (meson Tcoin.exhaust)
  apply (simp add: dstate_UNIV_set)
  apply (pred_auto)
  apply (simp add: real2ureal_def)
  using real2ureal_def apply blast+
  apply (simp add: dstate_UNIV_set)
  apply (pred_auto)
  using real2ureal_def apply blast+
  apply (simp add: dstate_UNIV_set)
  apply (pred_auto)
  using real2ureal_def apply blast+
  (* *)
  apply (simp)
  apply (subst loopfunc_def)
  apply (subst pseqcomp_def)
  apply (subst pcond_def)
  apply (subst dice_throw_altdef)
  apply (subst rvfun_inverse)
  apply (simp add: dist_defs)
  apply (expr_auto)
  apply (simp add: infsum_nonneg  prfun_in_0_1')
  apply (pred_auto)
  apply (simp add: dstate_UNIV_set)
  apply (simp add: rvfun_of_prfun_def)
  apply (auto)
  apply (smt (verit, best) field_sum_of_halves ureal_upper_bound)
  using ureal_upper_bound apply blast
  apply (subst prfun_of_rvfun_def)
  apply (subst rvfun_of_prfun_def)+
  apply (expr_auto)
  apply (simp add: dstate_UNIV_set)
  apply (pred_auto)
  defer
  apply (subst prfun_skip_id)
  apply (simp add: one_ureal.rep_eq real2ureal_def ureal2real_def)
  using Tcoin.exhaust apply blast
  apply (metis (full_types) Tcoin.exhaust dstate.select_convs(1) ereal_real o_def prfun_skip_not_id real2ureal_def ureal2real_def zero_ereal_def zero_ureal.rep_eq)
  apply (subst infsum_0)
  apply (subst ureal_defs)
  apply (smt (verit, best) divide_eq_0_iff ereal_max min.absorb2 min.commute mult_eq_0_iff o_apply real_of_ereal_0 ureal2ereal_inverse ureal2real_def zero_ereal_def zero_less_one_ereal zero_ureal.rep_eq)
  using real2ureal_def apply presburger
  using Tcoin.exhaust apply blast
  apply (subst infsum_0)
  apply (subst ureal_defs)
  apply (smt (verit, best) divide_eq_0_iff ereal_max min.absorb2 min.commute mult_eq_0_iff o_apply real_of_ereal_0 ureal2ereal_inverse ureal2real_def zero_ereal_def zero_less_one_ereal zero_ureal.rep_eq)
  using real2ureal_def apply blast
  apply (metis (full_types) Tcoin.exhaust dstate.ext_inject o_def prfun_skip_not_id real2ureal_def real_of_ereal_0 ureal2real_def zero_ureal.rep_eq)
  apply (subst ureal2real_1_2)
  apply (subst sum_1_2)
  apply (subst sum_geometric_series_ureal)
  apply (subst sum_geometric_series')
  apply (subst ureal_defs)+
proof -
  fix n
  have f1: "((1::\<real>) / (2::\<real>) + ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ (n + (1::\<nat>))) / (2::\<real>)) = 
        ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ (n + 2))"
    by (simp add: add.assoc diff_divide_distrib)
  have f2: "((3::\<real>) * ((1::\<real>) / (2::\<real>)) ^ n / (4::\<real>) + ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ n)) =  
          ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ (n+2))"
    apply (auto)
    by (simp add: power_one_over)
  show "ereal2ureal' (min (max (0::ereal) (ereal ((1::\<real>) / (2::\<real>) + ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ (n + (1::\<nat>))) / (2::\<real>)))) (1::ereal)) =
       ereal2ureal' (min (max (0::ereal) (ereal ((3::\<real>) * ((1::\<real>) / (2::\<real>)) ^ n / (4::\<real>) + ((1::\<real>) - (1::\<real>) / (2::\<real>) ^ n)))) (1::ereal))"
    using f1 f2 by presburger
qed

lemma coin_flip_loop: "dice_throw_loop = H"
  apply (simp add: dice_throw_loop_def H_def)
  apply (subst sup_continuous_lfp_iteration)
  apply (simp add: dice_throw_is_dist)
  apply (rule finite_subset[where B = "{s::dstate \<times> dstate. True}"])
  apply force
  apply (metis dstate_rel_UNIV_set finite.emptyI finite.insertI)
  apply (simp only: dice_throw_drop_initial_segments_eq[symmetric])
  apply (simp only: fi)
  by auto
*)

end