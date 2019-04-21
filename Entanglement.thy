(* Authors: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk,
 
            Yijun He, University of Cambridge, yh403@cam.ac.uk
*)

theory Entanglement
imports
  Main
  Jordan_Normal_Form.Matrix
  Quantum
  Tensor
  MoreTensor
begin


section\<open>Quantum Entanglement\<close>

subsection\<open>The Product States and Entangled States of a 2-qubits System\<close>

(* Below we add the condition that v and w are two-dimensional states , otherwise u can always be 
represented by the tensor product of the 1-dimensional vector (1) and u itself *)

definition prod_state2 ::"complex Matrix.mat \<Rightarrow> bool" where
"prod_state2 u \<equiv> if state 2 u then \<exists>v w. state 1 v \<and> state 1 w \<and> u = v \<Otimes> w else undefined"

definition entangled2 ::"complex Matrix.mat \<Rightarrow> bool" where
"entangled2 u \<equiv> \<not> prod_state2 u"

text\<open>The Bell states are entangled states\<close>

lemma bell_00_is_entangled2:
  shows "entangled2 |\<beta>\<^sub>0\<^sub>0\<rangle>" 
proof-
  have "\<forall>v w. state 1 v \<longrightarrow> state 1 w \<longrightarrow> |\<beta>\<^sub>0\<^sub>0\<rangle> \<noteq> v \<Otimes> w"
  proof-
    have "(\<exists>v w. state 1 v \<and> state 1 w \<and> |\<beta>\<^sub>0\<^sub>0\<rangle> = v \<Otimes> w) \<longrightarrow> False"
    proof
      assume asm:"\<exists>v  w. state 1 v \<and> state 1 w \<and> |\<beta>\<^sub>0\<^sub>0\<rangle> = v \<Otimes> w"
      obtain v and w where a0:"state 1 v" and a1:"state 1 w" and a2:"|\<beta>\<^sub>0\<^sub>0\<rangle> = v \<Otimes> w"
        using asm
        by auto
      have "|\<beta>\<^sub>0\<^sub>0\<rangle> $$ (0,0) = (v \<Otimes> w) $$ (0,0)"
        using a2
        by simp
      then have f1:"v $$ (0,0) * w $$ (0,0) = 1/sqrt 2"
        using a0 a1
        by(auto simp add: mat_tensor_prod_2 bell_00_index(1))
      have "|\<beta>\<^sub>0\<^sub>0\<rangle> $$ (1,0) = (v \<Otimes> w) $$ (1,0)"
        using a2
        by simp
      then have f2:"v $$ (0,0) * w $$ (1,0) = 0"
        using a0 a1
        apply (auto simp: mat_tensor_prod_2)
        by (metis One_nat_def bell_00_index(2) divisors_zero)
      have "|\<beta>\<^sub>0\<^sub>0\<rangle> $$ (2,0) = (v \<Otimes> w) $$ (2,0)"
        using a2
        by simp
      then have f3:"v $$ (1,0) * w $$ (0,0) = 0"
        using a0 a1
        apply (auto simp: mat_tensor_prod_2)
        using bell_00_index(3) numeral_2_eq_2 
        by auto
      have "|\<beta>\<^sub>0\<^sub>0\<rangle> $$ (3,0) = (v \<Otimes> w) $$ (3,0)"
        using a2
        by simp
      then have f4:"v $$ (1,0) * w $$ (1,0) = 1 /sqrt 2"
        using a0 a1
        apply (auto simp: mat_tensor_prod_2)
        using bell_00_index(4) numeral_3_eq_3 
        by auto
      have "1 /sqrt 2 * 1 /sqrt 2 = 0"
        using f1 f2 f3 f4
        by auto
      then show False
        by simp
    qed
    then show ?thesis
      by blast
  qed
  thus ?thesis 
    by(simp add: entangled2_def prod_state2_def bell_is_state)
qed

lemma bell_01_is_entangled2:
  shows "entangled2 |\<beta>\<^sub>0\<^sub>1\<rangle>" 
proof-
  have "\<forall>v w. state 1 v \<longrightarrow> state 1 w \<longrightarrow> |\<beta>\<^sub>0\<^sub>1\<rangle> \<noteq> v \<Otimes> w"
  proof-
    have "(\<exists>v w. state 1 v \<and> state 1 w \<and> |\<beta>\<^sub>0\<^sub>1\<rangle> = v \<Otimes> w) \<longrightarrow> False"
    proof
      assume asm:"\<exists>v w. state 1 v \<and> state 1 w \<and> |\<beta>\<^sub>0\<^sub>1\<rangle> = v \<Otimes> w"
      obtain v and w where a0:"state 1 v" and a1:"state 1 w" and a2:"|\<beta>\<^sub>0\<^sub>1\<rangle> = v \<Otimes> w"
        using asm
        by blast
      have "|\<beta>\<^sub>0\<^sub>1\<rangle> $$ (0,0) = (v \<Otimes> w) $$ (0,0)"
        using a2
        by simp
      then have f1:"v $$ (0,0) * w $$ (0,0) = 0"
        using a0 a1
        by(auto simp add: mat_tensor_prod_2 bell_01_index)
      have "|\<beta>\<^sub>0\<^sub>1\<rangle> $$ (1,0) = (v \<Otimes> w) $$ (1,0)"
        using a2
        by simp
      then have f2:"v $$ (0,0) * w $$ (1,0) = 1 /sqrt 2"
        using a0 a1
        apply (auto simp: mat_tensor_prod_2)
        using bell_01_index(2) 
        by auto
      have "|\<beta>\<^sub>0\<^sub>1\<rangle> $$ (2,0) = (v \<Otimes> w) $$ (2,0)"
        using a2
        by simp
      then have f3:"v $$ (1,0) * w $$ (0,0) = 1 /sqrt 2"
        using a0 a1
        apply (auto simp: mat_tensor_prod_2)
        using bell_01_index(3) numeral_2_eq_2 
        by auto
      have "|\<beta>\<^sub>0\<^sub>1\<rangle> $$ (3,0) = (v \<Otimes> w) $$ (3,0)"
        using a2
        by simp
      then have f4:"v $$ (1,0) * w $$ (1,0) = 0"
        using a0 a1
        apply (auto simp: mat_tensor_prod_2 numeral_3_eq_3)
        by (simp add: Suc3_eq_add_3 bell_01_index(4))
      have "1 / sqrt 2 * 1 / sqrt 2 = 0"
        using f1 f2 f3 f4
        by auto
      then show False
        by simp
    qed
    then show "\<forall>v w. state 1 v \<longrightarrow> state 1 w \<longrightarrow> |\<beta>\<^sub>0\<^sub>1\<rangle> \<noteq> v \<Otimes> w"
      by blast
  qed
  then show ?thesis 
    by(simp add: entangled2_def prod_state2_def bell_is_state)
qed

lemma bell_10_is_entangled2:
  shows "entangled2 |\<beta>\<^sub>1\<^sub>0\<rangle>" 
proof-
  have "\<forall>v w. state 1 v \<longrightarrow> state 1 w \<longrightarrow> |\<beta>\<^sub>1\<^sub>0\<rangle> \<noteq> v \<Otimes> w"
  proof-
    have "(\<exists>v w. state 1 v \<and> state 1 w \<and> |\<beta>\<^sub>1\<^sub>0\<rangle> = v \<Otimes> w) \<longrightarrow> False"
    proof
      assume asm:"\<exists>v w. state 1 v \<and> state 1 w \<and> |\<beta>\<^sub>1\<^sub>0\<rangle> = v \<Otimes> w"
      obtain v and w where a0:"state 1 v" and a1:"state 1 w" and a2:"|\<beta>\<^sub>1\<^sub>0\<rangle> = v \<Otimes> w"
        using asm
        by blast
      have "|\<beta>\<^sub>1\<^sub>0\<rangle> $$ (0,0) = (v \<Otimes> w) $$ (0,0)"
        using a2
        by simp
      then have f1:"v $$ (0,0) * w $$ (0,0) = 1 /sqrt 2"
        using a0 a1
        apply (auto simp: mat_tensor_prod_2 mult.times.simps bell_10_index).
      have "|\<beta>\<^sub>1\<^sub>0\<rangle> $$ (1,0) = (v \<Otimes> w) $$ (1,0)"
        using a2
        by simp
      then have f2:"v $$ (0,0) * w $$ (1,0) = 0"
        using a0 a1
        apply (auto simp: mat_tensor_prod_2)
        by (metis One_nat_def bell_10_index(2) no_zero_divisors)
      have "|\<beta>\<^sub>1\<^sub>0\<rangle> $$ (2,0) = (v \<Otimes> w) $$ (2,0)"
        using a2
        by simp
      then have f3:"v $$ (1,0) * w $$ (0,0) = 0"
        using a0 a1
        apply (auto simp: mat_tensor_prod_2)
        using bell_10_index(3) numeral_2_eq_2 
        by auto
      have "|\<beta>\<^sub>1\<^sub>0\<rangle> $$ (3,0) = (v \<Otimes> w) $$ (3,0)"
        using a2
        by simp
      then have f4:"v $$ (1,0) * w $$ (1,0) = -1 /sqrt 2"
        using a0 a1
        apply (auto simp: mat_tensor_prod_2)
        using bell_10_index(4) numeral_3_eq_3 
        by auto
      have "1 /sqrt 2 * 1 /sqrt 2 = 0"
        using f1 f2 f3 f4
        by auto
      then show False
        by simp
    qed
    then show "\<forall>v w. state 1 v \<longrightarrow> state 1 w \<longrightarrow> |\<beta>\<^sub>1\<^sub>0\<rangle> \<noteq> v \<Otimes> w"
      by blast
  qed
  then show ?thesis 
    by(simp add: entangled2_def prod_state2_def bell_is_state)
qed

lemma bell_11_is_entangled2:
  shows "entangled2 |\<beta>\<^sub>1\<^sub>1\<rangle>"
proof-
  have "\<forall>v w. state 1 v \<longrightarrow> state 1 w \<longrightarrow> |\<beta>\<^sub>1\<^sub>1\<rangle> \<noteq> v \<Otimes> w"
  proof-
    have "(\<exists>v w. state 1 v \<and> state 1 w \<and> |\<beta>\<^sub>1\<^sub>1\<rangle> = v \<Otimes> w) \<longrightarrow> False"
    proof
      assume asm:"\<exists>v w. state 1 v \<and> state 1 w \<and> |\<beta>\<^sub>1\<^sub>1\<rangle> = v \<Otimes> w"
      obtain v and w where a0:"state 1 v" and a1:"state 1 w" and a2:"|\<beta>\<^sub>1\<^sub>1\<rangle> = v \<Otimes> w"
        using asm
        by blast
      have "|\<beta>\<^sub>1\<^sub>1\<rangle> $$ (0,0) = (v \<Otimes> w) $$ (0,0)"
        using a2
        by simp
      then have f1:"v $$ (0,0) * w $$ (0,0) = 0"
        using a0 a1
        apply (auto simp: mat_tensor_prod_2 bell_11_index).
      have "|\<beta>\<^sub>1\<^sub>1\<rangle> $$ (1,0) = (v \<Otimes> w) $$ (1,0)"
        using a2
        by simp
      then have f2:"v $$ (0,0) * w $$ (1,0) = 1 /sqrt 2"
        using a0 a1
        apply (auto simp: mat_tensor_prod_2)
        using bell_11_index(2) 
        by auto
      have "|\<beta>\<^sub>1\<^sub>1\<rangle> $$ (2,0) = (v \<Otimes> w) $$ (2,0)"
        using a2
        by simp
      then have f3:"v $$ (1,0) * w $$ (0,0) = -1 /sqrt 2"
        using a0 a1
        apply (auto simp: mat_tensor_prod_2)
        using bell_11_index(3) numeral_2_eq_2 
        by auto
      have "|\<beta>\<^sub>1\<^sub>1\<rangle> $$ (3,0) = (v \<Otimes> w) $$ (3,0)"
        using a2
        by simp
      then have f4:"v $$ (1,0) * w $$ (1,0) = 0"
        using a0 a1
        apply (auto simp: mat_tensor_prod_2)
        using bell_11_index(4) numeral_3_eq_3 
        by auto
      have "1 /sqrt 2 * 1 /sqrt 2 = 0"
        using f1 f2 f3 f4
        by auto
      then show False
        by simp
    qed
    then show "\<forall>v w. state 1 v \<longrightarrow> state 1 w \<longrightarrow> |\<beta>\<^sub>1\<^sub>1\<rangle> \<noteq> v \<Otimes> w"
      by blast
  qed
  then show ?thesis 
    by(simp add: entangled2_def prod_state2_def bell_is_state)
qed


text \<open>An entangled state is a state that cannot be broken down as the tensor product of smaller states\<close>

definition prod_state ::"nat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
"prod_state m u \<equiv> if state m u then \<exists>n p::nat.\<exists>v w. state n v \<and> state p w \<and> 
  n < m \<and> p < m \<and>  u = v \<Otimes> w else undefined"

definition entangled ::"nat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
"entangled n v \<equiv> \<not> (prod_state n v)"

(* To do: as an exercise prove the equivalence between entangled2 and (entangled 2) *)

lemma sanity_check: 
  shows "\<not>(entangled 2 (mat_of_cols_list 2 [[1/sqrt(2), 1/sqrt(2)]] \<Otimes> mat_of_cols_list 2 [[1/sqrt(2), 1/sqrt(2)]]))"
proof-
  define u where "u = mat_of_cols_list 2 [[1/sqrt(2), 1/sqrt(2)]]"
  then have "state 1 u"
  proof-
    have f1:"dim_col u = 1"
      using u_def mat_of_cols_list_def 
      by simp
    have f2:"dim_row u = 2"
      using u_def mat_of_cols_list_def 
      by simp
    have "\<parallel>Matrix.col u 0\<parallel> = 1"
    proof-
      have f3:"(cmod (u $$ (0, 0)))\<^sup>2 = (1/sqrt 2)\<^sup>2"
        apply (auto simp: u_def mat_of_cols_list_def cmod_def).
      have "(cmod (u $$ (1, 0)))\<^sup>2 = (1/sqrt 2)\<^sup>2"
        apply (auto simp: u_def mat_of_cols_list_def cmod_def).
      then have "(\<Sum>i\<in>{0,1}.(cmod (u $$ (i, 0)))\<^sup>2) = (1/sqrt 2)\<^sup>2 + (1/sqrt 2)\<^sup>2"
        using f3
        by simp
      then have "(\<Sum>i<2.(cmod (u $$ (i, 0)))\<^sup>2) = (1/sqrt 2)\<^sup>2 + (1/sqrt 2)\<^sup>2"
        by (simp add: numeral_2_eq_2)
      then have "\<parallel>Matrix.col u 0\<parallel> = sqrt ((1/sqrt 2)\<^sup>2 + (1/sqrt 2)\<^sup>2)"
        using f2
        apply (auto simp: Matrix.col_def u_def cpx_vec_length_def).
      thus ?thesis
        by (simp add: power_divide)
    qed
    thus ?thesis
      using state_def
      by (simp add: f1 f2)
  qed
  then have "state 2 (u \<Otimes> u)"
    using tensor_state \<open>state 1 u\<close>
    by (metis one_add_one)
  thus ?thesis
    using entangled_def prod_state_def
    by (metis \<open>state 1 u\<close> one_less_numeral_iff semiring_norm(76) u_def)
qed



end