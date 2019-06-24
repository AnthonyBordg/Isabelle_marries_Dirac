(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk *)

theory Quantum_Teleportation
imports 
  Quantum 
  MoreTensor
begin


definition Alice:: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
"Alice \<phi> \<equiv> (H \<Otimes> id 2) * ((CNOT \<Otimes> id 1) * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>))"

lemma set_8 [simp]: "{0..<8::nat} = {0,1,2,3,4,5,6,7}" by auto

definition M1 :: "complex Matrix.mat" where
"M1 = mat_of_cols_list 8 [[1, 0, 0, 0, 0, 0, 0, 0],
                          [0, 1, 0, 0, 0, 0, 0, 0],
                          [0, 0, 1, 0, 0, 0, 0, 0],
                          [0, 0, 0, 1, 0, 0, 0, 0],
                          [0, 0, 0, 0, 0, 0, 1, 0],
                          [0, 0, 0, 0, 0, 0, 0, 1],
                          [0, 0, 0, 0, 1, 0, 0, 0],
                          [0, 0, 0, 0, 0, 1, 0, 0]]"

lemma tensor_prod_of_cnot_id_1: shows "(CNOT \<Otimes> id 1) = M1"
proof
  show "dim_col (CNOT \<Otimes> id 1) = dim_col M1"
    by(simp add: CNOT_def id_def M1_def mat_of_cols_list_def)
  show "dim_row (CNOT \<Otimes> id 1) = dim_row M1"
    by(simp add: CNOT_def id_def M1_def mat_of_cols_list_def)
  fix i j::nat assume a1:"i < dim_row M1" and a2:"j < dim_col M1"
  then have "i \<in> {0,1,2,3,4,5,6,7} \<and> j \<in> {0,1,2,3,4,5,6,7}"
    by (auto simp add: M1_def mat_of_cols_list_def)
  then show "(CNOT \<Otimes> id 1) $$ (i, j) = M1 $$ (i, j)"
    by (auto simp add: id_def M1_def CNOT_def mat_of_cols_list_def)
qed

definition M2 :: "complex Matrix.mat" where
"M2 = mat_of_cols_list 8 [[1/sqrt(2), 0, 0, 0, 1/sqrt(2), 0, 0, 0],
                          [0, 1/sqrt(2), 0, 0, 0, 1/sqrt(2), 0, 0],
                          [0, 0, 1/sqrt(2), 0, 0, 0, 1/sqrt(2), 0],
                          [0, 0, 0, 1/sqrt(2), 0, 0, 0, 1/sqrt(2)],
                          [1/sqrt(2), 0, 0, 0, -1/sqrt(2), 0, 0, 0],
                          [0, 1/sqrt(2), 0, 0, 0, -1/sqrt(2), 0, 0],
                          [0, 0, 1/sqrt(2), 0, 0, 0, -1/sqrt(2), 0],
                          [0, 0, 0, 1/sqrt(2), 0, 0, 0, -1/sqrt(2)]]"

lemma tensor_prod_of_h_id_2: shows "(H \<Otimes> id 2) = M2"
proof
  show "dim_col (H \<Otimes> id 2) = dim_col M2"
    by(simp add: H_def id_def M2_def mat_of_cols_list_def)
  show "dim_row (H \<Otimes> id 2) = dim_row M2"
    by(simp add: H_def id_def M2_def mat_of_cols_list_def)
  fix i j::nat assume a1:"i < dim_row M2" and a2:"j < dim_col M2"
  then have "i \<in> {0,1,2,3,4,5,6,7} \<and> j \<in> {0,1,2,3,4,5,6,7}"
    by (auto simp add: M2_def mat_of_cols_list_def)
  then show "(H \<Otimes> id 2) $$ (i, j) = M2 $$ (i, j)"
    by (auto simp add: id_def M2_def H_def mat_of_cols_list_def)
qed

lemma Alice_step_1_state [simp]:
  assumes "state 1 \<phi>"
  shows "state 3 (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>)"
  using assms bell00_is_state tensor_state by (metis One_nat_def Suc_1 numeral_3_eq_3 plus_1_eq_Suc)

lemma Alice_step_2_state [simp]:
  assumes "state 1 \<phi>"
  shows "state 3 ((CNOT \<Otimes> id 1) * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>))"
proof-
  have "gate 3 (CNOT \<Otimes> id 1)"
    using CNOT_is_gate id_is_gate tensor_gate by (metis numeral_plus_one semiring_norm(5))
  then show "state 3 ((CNOT \<Otimes> id 1) * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>))"
    using assms
    by simp
qed

lemma Alice_state [simp]:
  assumes "state 1 \<phi>"
  shows "state 3 (Alice \<phi>) "
proof-
  have "gate 3 (H \<Otimes> id 2)"
    using tensor_gate id_is_gate H_is_gate
    by (metis eval_nat_numeral(3) plus_1_eq_Suc)
  then show ?thesis 
    using assms Alice_step_2_state
    by(simp add: Alice_def)
qed

lemma square_of_sqrt_2 [simp]:"\<And>z::complex. z * 2 / (complex_of_real (sqrt 2) * complex_of_real (sqrt 2)) = z"
  by (metis nonzero_mult_div_cancel_right norm_numeral of_real_numeral of_real_power power2_eq_square 
real_norm_def real_sqrt_abs real_sqrt_power zero_neq_numeral)

lemma Alice_step_1:
  assumes "state 1 \<phi>" and "\<alpha> = \<phi> $$ (0,0)" and "\<beta> = \<phi> $$ (1,0)"
  shows "(\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>) = mat_of_cols_list 8 [[\<alpha>/sqrt(2), 0, 0, \<alpha>/sqrt(2), \<beta>/sqrt(2), 0, 0, \<beta>/sqrt(2)]]"
proof
  define v where asm:"v = mat_of_cols_list 8 [[\<alpha>/sqrt(2), 0, 0, \<alpha>/sqrt(2), \<beta>/sqrt(2), 0, 0, \<beta>/sqrt(2)]]"
  show "dim_row (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>) = dim_row v"
    using assms(1) Alice_step_1_state state.dim_row asm mat_of_cols_list_def by fastforce
  show "dim_col (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>) = dim_col v"
    using assms(1) Alice_step_1_state state.dim_col asm mat_of_cols_list_def by fastforce
  show "\<And>i j. i < dim_row v \<Longrightarrow> j < dim_col v \<Longrightarrow> (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>) $$ (i, j) = v $$ (i, j)"
  proof-
    fix i j assume "i < dim_row v" and " j < dim_col v"
    then have "i \<in> {0,1,2,3,4,5,6,7} \<and> j = 0"
      using asm
      by (auto simp add: mat_of_cols_list_def)
    moreover have "dim_row |\<beta>\<^sub>0\<^sub>0\<rangle> = 4"
      using bell00_is_state state_def by auto
    moreover have "dim_col |\<beta>\<^sub>0\<^sub>0\<rangle> = 1"
      using bell00_is_state state_def by auto
    ultimately show "(\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>) $$ (i, j) = v $$ (i, j)"
      using state_def assms asm
      by (auto simp add: bell00_def)
  qed
qed

lemma Alice_step_2:
  assumes "state 1 \<phi>" and "\<alpha> = \<phi> $$ (0,0)" and "\<beta> = \<phi> $$ (1,0)"
  shows "(CNOT \<Otimes> id 1) * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>) = mat_of_cols_list 8 [[\<alpha>/sqrt(2), 0, 0, \<alpha>/sqrt(2), 0, \<beta>/sqrt(2), \<beta>/sqrt(2), 0]]"
proof
  define v where asm:"v = mat_of_cols_list 8 [[\<alpha>/sqrt(2), 0, 0, \<alpha>/sqrt(2), 0, \<beta>/sqrt(2), \<beta>/sqrt(2), 0]]"
  have f0:"(\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>) = mat_of_cols_list 8 [[\<alpha>/sqrt(2), 0, 0, \<alpha>/sqrt(2), \<beta>/sqrt(2), 0, 0, \<beta>/sqrt(2)]]"
    using assms Alice_step_1
    by simp
  show "dim_row ((CNOT \<Otimes> id 1) * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>)) = dim_row v"
    using assms(1) Alice_step_2_state state.dim_row asm mat_of_cols_list_def by fastforce
  show "dim_col ((CNOT \<Otimes> id 1) * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>)) = dim_col v"
    using assms(1) Alice_step_2_state state.dim_col asm mat_of_cols_list_def by fastforce
  show "\<And>i j. i < dim_row v \<Longrightarrow> j < dim_col v \<Longrightarrow> ((CNOT \<Otimes> id 1) * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>)) $$ (i, j) = v $$ (i, j)"
  proof-
    fix i j assume "i < dim_row v" and " j < dim_col v"
    then have "i \<in> {0,1,2,3,4,5,6,7} \<and> j = 0"
      using asm
      by (auto simp add: mat_of_cols_list_def)
    then have "(M1 * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>)) $$ (i, j) = v $$ (i, j)"
      by (auto simp add: M1_def f0 asm mat_of_cols_list_def times_mat_def scalar_prod_def)
    then show "((CNOT \<Otimes> id 1) * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>)) $$ (i, j) = v $$ (i, j)"
      using tensor_prod_of_cnot_id_1
      by auto
  qed
qed

lemma Alice_result:
  assumes "state 1 \<phi>" and "\<alpha> = \<phi> $$ (0,0)" and "\<beta> = \<phi> $$ (1,0)"
  shows "Alice \<phi> = mat_of_cols_list 8 [[\<alpha>/2, \<beta>/2, \<beta>/2, \<alpha>/2, \<alpha>/2, -\<beta>/2, -\<beta>/2, \<alpha>/2]]"
proof
  define v where asm:"v = mat_of_cols_list 8 [[\<alpha>/2, \<beta>/2, \<beta>/2, \<alpha>/2, \<alpha>/2, -\<beta>/2, -\<beta>/2, \<alpha>/2]]"
  define w where asm1:"w = (CNOT \<Otimes> id 1) * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>)"
  have f0:"w = mat_of_cols_list 8 [[\<alpha>/sqrt(2), 0, 0, \<alpha>/sqrt(2), 0, \<beta>/sqrt(2), \<beta>/sqrt(2), 0]]"
    using assms Alice_step_2 asm1 by auto
  show "dim_row (Alice \<phi>) = dim_row v"
    using assms(1) Alice_state state_def asm
    by (simp add: mat_of_cols_list_def)
  show "dim_col (Alice \<phi>) = dim_col v"
    using assms(1) Alice_state state_def asm
    by (simp add: mat_of_cols_list_def)
  show "\<And>i j. i < dim_row v \<Longrightarrow> j < dim_col v \<Longrightarrow> Alice \<phi> $$ (i, j) = v $$ (i, j)"
  proof-
    fix i j assume "i < dim_row v" and " j < dim_col v"
    then have c1:"i \<in> {0,1,2,3,4,5,6,7} \<and> j = 0"
      using asm
      by (auto simp add: Tensor.mat_of_cols_list_def)
    then have "(M2 * w) $$ (i, j) = v $$ (i, j)"
      by (auto simp add: M2_def f0 asm mat_of_cols_list_def times_mat_def scalar_prod_def)
    then show "Alice \<phi> $$ (i, j) = v $$ (i, j)"
      by (auto simp add: tensor_prod_of_h_id_2 Alice_def asm1)
  qed
qed

text \<open>
An application of function Alice to a state \<phi> of a 1-qubit system results in the following cases.
\<close>

definition Alice_meas:: "complex Matrix.mat \<Rightarrow> _list" where
"Alice_meas \<phi> \<equiv> [
  ((prob0 3 (Alice \<phi>) 0) * (prob0 3 (post_meas0 3 (Alice \<phi>) 0) 1), post_meas0 3 (post_meas0 3 (Alice \<phi>) 0) 1)
, ((prob0 3 (Alice \<phi>) 0) * (prob1 3 (post_meas0 3 (Alice \<phi>) 0) 1), post_meas1 3 (post_meas0 3 (Alice \<phi>) 0) 1)
, ((prob1 3 (Alice \<phi>) 0) * (prob0 3 (post_meas1 3 (Alice \<phi>) 0) 1), post_meas0 3 (post_meas1 3 (Alice \<phi>) 0) 1)
, ((prob1 3 (Alice \<phi>) 0) * (prob1 3 (post_meas1 3 (Alice \<phi>) 0) 1), post_meas1 3 (post_meas1 3 (Alice \<phi>) 0) 1)
]"

definition Alice_pos:: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
"Alice_pos \<phi> q \<equiv>  q = mat_of_cols_list 8 [[\<phi> $$ (0,0), \<phi> $$ (1,0), 0, 0, 0, 0, 0, 0]] \<or>
                  q = mat_of_cols_list 8 [[0, 0, \<phi> $$ (1,0), \<phi> $$ (0,0), 0, 0, 0, 0]] \<or>
                  q = mat_of_cols_list 8 [[0, 0, 0, 0, \<phi> $$ (0,0), - \<phi> $$ (1,0), 0, 0]] \<or>
                  q = mat_of_cols_list 8 [[0, 0, 0, 0, 0, 0, - \<phi> $$ (1,0), \<phi> $$ (0,0)]]"

lemma Alice_case [simp]:
  assumes "state 1 \<phi>" and "state 3 q" and "List.member (Alice_meas \<phi>) (p, q)"
  shows "Alice_pos \<phi> q"
proof-
  define \<alpha> \<beta> where a0:"\<alpha> = \<phi> $$ (0,0)" and a1:"\<beta> = \<phi> $$ (1,0)"
  then have a2:"cmod(\<alpha>)^2 + cmod(\<beta>)^2 = 1"
    using set_2 assms(1) state_def a0 a1 Matrix.col_def cpx_vec_length_def
    by (auto simp add: atLeast0LessThan)
  have a3:"{j::nat. select_index 3 0 j} = {4,5,6,7}"
    by (auto simp add: select_index_def)
  have a4:"{j::nat. j < 8 \<and> \<not> select_index 3 0 j} = {0,1,2,3}"
  proof-
    have "\<And>j::nat. j < 8 \<and> j \<notin> {4,5,6,7} \<Longrightarrow> j \<in> {0,1,2,3}" 
      by auto
    then show ?thesis
      by (auto simp add: select_index_def)
  qed
  have a5:"{j::nat. select_index 3 (Suc 0) j} = {2,3,6,7}"
  proof
    show "{j. select_index 3 (Suc 0) j} \<subseteq> {2, 3, 6, 7}"
    proof
      fix j::nat assume "j \<in> {j. select_index 3 (Suc 0) j}"
      then have "j \<in> {0,1,2,3,4,5,6,7} \<and> j mod 4 \<in> {2,3}"
        by (auto simp add: select_index_def)
      then show "j \<in> {2,3,6,7}"
        by auto
    qed
    show "{2, 3, 6, 7} \<subseteq> {j. select_index 3 (Suc 0) j}"
      by (auto simp add: select_index_def)
  qed
  have a6:"{j::nat. j < 8 \<and> \<not> select_index 3 (Suc 0) j} = {0,1,4,5}"
  proof-
    have "{j::nat. j < 8 \<and> j \<notin> {2,3,6,7}} = {0,1,4,5}" 
      by auto
    then show ?thesis
      using a5
      by blast
  qed
  have a7:"select_index 3 0 0 = False \<and> select_index 3 0 1 = False \<and> 
           select_index 3 0 2 = False \<and> select_index 3 0 3 = False "
    using a4
    by auto
  have a8:"select_index 3 1 0 = False \<and> select_index 3 1 1 = False \<and> 
           select_index 3 1 4 = False \<and> select_index 3 1 5 = False "
    using a6
    by auto
  have m0:"2 * complex_of_real (sqrt (1/2)) = complex_of_real (sqrt 2)"
  proof -
    have f1: "\<And>r ra. r *\<^sub>R (1::complex) / ra *\<^sub>R 1 = (r / ra) *\<^sub>R 1"
      by (metis of_real_def of_real_divide)
    { assume "sqrt (1 / 2) *\<^sub>R (1::complex) \<noteq> 0"
      then have "sqrt 2 *\<^sub>R (1::complex) / sqrt (1 / 2) *\<^sub>R 1 = 2 \<and> sqrt (1 / 2) *\<^sub>R (1::complex) \<noteq> 0"
        using f1 by (metis div_by_1 divide_divide_eq_right numeral_times_numeral of_real_def of_real_numeral real_sqrt_divide real_sqrt_four semiring_norm(12) semiring_norm(13))
      then have "2 * sqrt (1 / 2) *\<^sub>R (1::complex) = sqrt 2 *\<^sub>R 1"
        by (metis (full_types) nonzero_eq_divide_eq) }
    then show ?thesis
      by (simp add: of_real_def)
  qed

  have c0:"prob0 3 (Alice \<phi>) 0 = 1/2"
    using Alice_result assms prob0_def Alice_state
    apply (auto simp add: a4)
    by (metis (no_types, hide_lams) One_nat_def a0 a1 a2 four_x_squared mult.commute 
nonzero_mult_div_cancel_right times_divide_eq_right zero_neq_numeral)
  have c1:"prob1 3 (Alice \<phi>) 0 = 1/2"
    using Alice_result assms prob1_def Alice_state
    apply (auto simp add: a3)
    by (metis (no_types, hide_lams) One_nat_def a0 a1 a2 four_x_squared mult.commute 
nonzero_mult_div_cancel_right times_divide_eq_right zero_neq_numeral)

  have c2:"post_meas0 3 (Alice \<phi>) 0 = mat_of_cols_list 8 [[\<alpha>/sqrt(2), \<beta>/sqrt(2), \<beta>/sqrt(2), \<alpha>/sqrt(2), 0, 0, 0, 0]]"
  proof
    define v where asm:"v = mat_of_cols_list 8 [[\<alpha>/sqrt(2), \<beta>/sqrt(2), \<beta>/sqrt(2), \<alpha>/sqrt(2), 0, 0, 0, 0]]"
    show "dim_row (post_meas0 3 (Alice \<phi>) 0) = dim_row v"
      using mat_of_cols_list_def post_meas0_def assms Alice_state ket_vec_def asm
      by auto
    show "dim_col (post_meas0 3 (Alice \<phi>) 0) = dim_col v"
      using mat_of_cols_list_def post_meas0_def assms Alice_state ket_vec_def asm
      by auto
    show "\<And>i j. i < dim_row v \<Longrightarrow> j < dim_col v \<Longrightarrow> post_meas0 3 (Alice \<phi>) 0 $$ (i, j) = v $$ (i, j)"
    proof-
      fix i j assume "i < dim_row v" and "j < dim_col v"
      then have "i \<in> {0,1,2,3,4,5,6,7} \<and> j = 0"
        using asm set_8 mat_of_cols_list_def
        by auto
      then show "post_meas0 3 (Alice \<phi>) 0 $$ (i, j) = v $$ (i, j)"
        using post_meas0_def assms asm mat_of_cols_list_def ket_vec_def a3
        apply (auto simp add: c0)
        using assms Alice_result a0 a1 m0 a4
        by (auto)
    qed
  qed
  have c3:"post_meas1 3 (Alice \<phi>) 0 = mat_of_cols_list 8 [[0, 0, 0, 0, \<alpha>/sqrt(2), -\<beta>/sqrt(2), -\<beta>/sqrt(2), \<alpha>/sqrt(2)]]"
  proof
    define v where asm:"v = mat_of_cols_list 8 [[0, 0, 0, 0, \<alpha>/sqrt(2), -\<beta>/sqrt(2), -\<beta>/sqrt(2), \<alpha>/sqrt(2)]]"
    show "dim_row (post_meas1 3 (Alice \<phi>) 0) = dim_row v"
      using mat_of_cols_list_def post_meas1_def assms Alice_state ket_vec_def asm
      by auto
    show "dim_col (post_meas1 3 (Alice \<phi>) 0) = dim_col v"
      using mat_of_cols_list_def post_meas1_def assms Alice_state ket_vec_def asm
      by auto
    show "\<And>i j. i < dim_row v \<Longrightarrow> j < dim_col v \<Longrightarrow> post_meas1 3 (Alice \<phi>) 0 $$ (i, j) = v $$ (i, j)"
    proof-
      fix i j assume "i < dim_row v" and "j < dim_col v"
      then have "i \<in> {0,1,2,3,4,5,6,7} \<and> j = 0"
        using asm set_8 mat_of_cols_list_def
        by auto
      then show "post_meas1 3 (Alice \<phi>) 0 $$ (i, j) = v $$ (i, j)"
        using post_meas1_def assms asm mat_of_cols_list_def ket_vec_def a7
        apply (auto simp add: c1)
        using assms Alice_result a0 a1 m0 a3
        by (auto)
    qed
  qed

  have c4:"state 3 (post_meas0 3 (Alice \<phi>) 0)"
    using assms c0
    by auto
  have c5:"state 3 (post_meas1 3 (Alice \<phi>) 0)"
    using assms c1
    by auto

  have c6:"prob0 3 (Matrix.mat 8 (Suc 0) 
          (\<lambda>(i, j). [[\<alpha>/sqrt 2, \<beta>/sqrt 2, \<beta>/sqrt 2, \<alpha>/sqrt 2, 0, 0, 0, 0]] ! j ! i)) (Suc 0) = 1/2"
    using c2 prob0_def mat_of_cols_list_def c4
    by (auto simp add: a6 norm_divide power_divide a2)
  have c7:"prob1 3 (Matrix.mat 8 (Suc 0) 
          (\<lambda>(i, j). [[\<alpha>/sqrt 2, \<beta>/sqrt 2, \<beta>/sqrt 2, \<alpha>/sqrt 2, 0, 0, 0, 0]] ! j ! i)) (Suc 0) = 1/2"
    using c2 prob1_def mat_of_cols_list_def c4
    by (auto simp add: a5 norm_divide power_divide a2 algebra_simps)
  have c8:"prob0 3 (Matrix.mat 8 (Suc 0) 
          (\<lambda>(i, j). [[0, 0, 0, 0, \<alpha>/complex_of_real (sqrt 2), -(\<beta>/complex_of_real (sqrt 2)), -(\<beta>/complex_of_real (sqrt 2)),
                      \<alpha>/complex_of_real (sqrt 2)]] ! j ! i)) (Suc 0) = 1/2"
    using c3 prob0_def mat_of_cols_list_def c5
    by (auto simp add: a6 norm_divide power_divide a2)
  have c9:"prob1 3 (Matrix.mat 8 (Suc 0) 
          (\<lambda>(i, j). [[0, 0, 0, 0, \<alpha>/complex_of_real (sqrt 2), -(\<beta>/complex_of_real (sqrt 2)), -(\<beta>/complex_of_real (sqrt 2)),
                      \<alpha>/complex_of_real (sqrt 2)]] ! j ! i)) (Suc 0) = 1/2"
    using c3 prob1_def mat_of_cols_list_def c5
    by (auto simp add: a5 norm_divide power_divide a2 algebra_simps)
  have "(p, q) = ((prob0 3 (Alice \<phi>) 0) * (prob0 3 (post_meas0 3 (Alice \<phi>) 0) 1), post_meas0 3 (post_meas0 3 (Alice \<phi>) 0) 1) \<or>
        (p, q) = ((prob0 3 (Alice \<phi>) 0) * (prob1 3 (post_meas0 3 (Alice \<phi>) 0) 1), post_meas1 3 (post_meas0 3 (Alice \<phi>) 0) 1) \<or>
        (p, q) = ((prob1 3 (Alice \<phi>) 0) * (prob0 3 (post_meas1 3 (Alice \<phi>) 0) 1), post_meas0 3 (post_meas1 3 (Alice \<phi>) 0) 1) \<or>
        (p, q) = ((prob1 3 (Alice \<phi>) 0) * (prob1 3 (post_meas1 3 (Alice \<phi>) 0) 1), post_meas1 3 (post_meas1 3 (Alice \<phi>) 0) 1)"
    using assms Alice_meas_def List.member_def
    by (smt list.distinct(1) list.exhaust list.inject member_rec(1) member_rec(2))
  then have "q = post_meas0 3 (post_meas0 3 (Alice \<phi>) 0) 1 \<or> q = post_meas1 3 (post_meas0 3 (Alice \<phi>) 0) 1 \<or>
             q = post_meas0 3 (post_meas1 3 (Alice \<phi>) 0) 1 \<or> q = post_meas1 3 (post_meas1 3 (Alice \<phi>) 0) 1"
    by auto
  moreover have "post_meas0 3 (post_meas0 3 (Alice \<phi>) 0) 1 = mat_of_cols_list 8 [[\<alpha>, \<beta>, 0, 0, 0, 0, 0, 0]]"
  proof
    define v where asm:"v = mat_of_cols_list 8 [[\<alpha>, \<beta>, 0, 0, 0, 0, 0, 0]]"
    show "dim_row (post_meas0 3 (post_meas0 3 (Alice \<phi>) 0) 1) = dim_row v"
      using mat_of_cols_list_def post_meas0_def assms Alice_state ket_vec_def asm
      by auto
    show "dim_col (post_meas0 3 (post_meas0 3 (Alice \<phi>) 0) 1) = dim_col v"
      using mat_of_cols_list_def post_meas0_def assms Alice_state ket_vec_def asm
      by auto
    show "\<And>i j. i < dim_row v \<Longrightarrow> j < dim_col v \<Longrightarrow> post_meas0 3 (post_meas0 3 (Alice \<phi>) 0) 1 $$ (i, j) = v $$ (i, j)"
    proof-
      fix i j assume "i < dim_row v" and "j < dim_col v"
      then have "i \<in> {0,1,2,3,4,5,6,7} \<and> j = 0"
        using asm set_8 mat_of_cols_list_def
        by auto
      then show "post_meas0 3 (post_meas0 3 (Alice \<phi>) 0) 1 $$ (i, j) = v $$ (i, j)"
        using c2
        apply (auto)
        using post_meas0_def assms asm mat_of_cols_list_def ket_vec_def a8 a5
        by (auto simp add: c6 real_sqrt_divide)
    qed
  qed
  moreover have "post_meas1 3 (post_meas0 3 (Alice \<phi>) 0) 1 = mat_of_cols_list 8 [[0, 0, \<beta>, \<alpha>, 0, 0, 0, 0]]"
  proof
    define v where asm:"v = mat_of_cols_list 8 [[0, 0, \<beta>, \<alpha>, 0, 0, 0, 0]]"
    show "dim_row (post_meas1 3 (post_meas0 3 (Alice \<phi>) 0) 1) = dim_row v"
      using mat_of_cols_list_def post_meas1_def assms Alice_state ket_vec_def asm
      by auto
    show "dim_col (post_meas1 3 (post_meas0 3 (Alice \<phi>) 0) 1) = dim_col v"
      using mat_of_cols_list_def post_meas1_def assms Alice_state ket_vec_def asm
      by auto
    show "\<And>i j. i < dim_row v \<Longrightarrow> j < dim_col v \<Longrightarrow> post_meas1 3 (post_meas0 3 (Alice \<phi>) 0) 1 $$ (i, j) = v $$ (i, j)"
    proof-
      fix i j assume "i < dim_row v" and "j < dim_col v"
      then have "i \<in> {0,1,2,3,4,5,6,7} \<and> j = 0"
        using asm set_8 mat_of_cols_list_def
        by auto
      then show "post_meas1 3 (post_meas0 3 (Alice \<phi>) 0) 1 $$ (i, j) = v $$ (i, j)"
        using c2
        apply (auto)
        using post_meas1_def assms asm mat_of_cols_list_def ket_vec_def a8 a5
        by (auto simp add: c7 real_sqrt_divide)
    qed
  qed
  moreover have "post_meas0 3 (post_meas1 3 (Alice \<phi>) 0) 1 = mat_of_cols_list 8 [[0, 0, 0, 0, \<alpha>, -\<beta>, 0, 0]]"
  proof
    define v where asm:"v = mat_of_cols_list 8 [[0, 0, 0, 0, \<alpha>, -\<beta>, 0, 0]]"
    show "dim_row (post_meas0 3 (post_meas1 3 (Alice \<phi>) 0) 1) = dim_row v"
      using mat_of_cols_list_def post_meas0_def assms Alice_state ket_vec_def asm
      by auto
    show "dim_col (post_meas0 3 (post_meas1 3 (Alice \<phi>) 0) 1) = dim_col v"
      using mat_of_cols_list_def post_meas0_def assms Alice_state ket_vec_def asm
      by auto
    show "\<And>i j. i < dim_row v \<Longrightarrow> j < dim_col v \<Longrightarrow> post_meas0 3 (post_meas1 3 (Alice \<phi>) 0) 1 $$ (i, j) = v $$ (i, j)"
    proof-
      fix i j assume "i < dim_row v" and "j < dim_col v"
      then have "i \<in> {0,1,2,3,4,5,6,7} \<and> j = 0"
        using asm set_8 mat_of_cols_list_def
        by auto
      then show "post_meas0 3 (post_meas1 3 (Alice \<phi>) 0) 1 $$ (i, j) = v $$ (i, j)"
        using c3
        apply (auto)
        using post_meas0_def assms asm mat_of_cols_list_def ket_vec_def a8 a5
        by (auto simp add: c8 real_sqrt_divide)
    qed
  qed
  moreover have "post_meas1 3 (post_meas1 3 (Alice \<phi>) 0) 1 = mat_of_cols_list 8 [[0, 0, 0, 0, 0, 0, -\<beta>, \<alpha>]]"
  proof
    define v where asm:"v = mat_of_cols_list 8 [[0, 0, 0, 0, 0, 0, -\<beta>, \<alpha>]]"
    show "dim_row (post_meas1 3 (post_meas1 3 (Alice \<phi>) 0) 1) = dim_row v"
      using mat_of_cols_list_def post_meas1_def assms Alice_state ket_vec_def asm
      by auto
    show "dim_col (post_meas1 3 (post_meas1 3 (Alice \<phi>) 0) 1) = dim_col v"
      using mat_of_cols_list_def post_meas1_def assms Alice_state ket_vec_def asm
      by auto
    show "\<And>i j. i < dim_row v \<Longrightarrow> j < dim_col v \<Longrightarrow> post_meas1 3 (post_meas1 3 (Alice \<phi>) 0) 1 $$ (i, j) = v $$ (i, j)"
    proof-
      fix i j assume "i < dim_row v" and "j < dim_col v"
      then have "i \<in> {0,1,2,3,4,5,6,7} \<and> j = 0"
        using asm set_8 mat_of_cols_list_def
        by auto
      then show "post_meas1 3 (post_meas1 3 (Alice \<phi>) 0) 1 $$ (i, j) = v $$ (i, j)"
        using c3
        apply (auto)
        using post_meas1_def assms asm mat_of_cols_list_def ket_vec_def a8 a5
        by (auto simp add: c9 real_sqrt_divide)
    qed
  qed
  ultimately show ?thesis
    using Alice_pos_def a0 a1
    by auto
qed


datatype bit = zero | one

definition Alice_out:: "complex Matrix.mat => complex Matrix.mat => bit \<times> bit" where
"Alice_out \<phi> q \<equiv> if q = mat_of_cols_list 8 [[\<phi> $$ (0,0), \<phi> $$ (1,0), 0, 0, 0, 0, 0, 0]] then (zero, zero) else
  if q = mat_of_cols_list 8 [[0, 0, \<phi> $$ (1,0), \<phi> $$ (0,0), 0, 0, 0, 0]] then (zero, one) else
    if q = mat_of_cols_list 8 [[0, 0, 0, 0, \<phi> $$ (0,0), - \<phi> $$ (1,0), 0, 0]] then (one, zero) else
      if q = mat_of_cols_list 8 [[0, 0, 0, 0, 0, 0, - \<phi> $$ (1,0), \<phi> $$ (0,0)]] then (one, one) else 
        undefined"

definition Bob:: "complex Matrix.mat => bit \<times> bit \<Rightarrow> complex Matrix.mat" where
"Bob q b \<equiv> if (fst b, snd b) = (zero, zero) then q else 
  if (fst b, snd b) = (zero, one) then (id 2 \<Otimes> X) * q else
    if (fst b, snd b) = (one, zero) then (id 2 \<Otimes> Z) * q else
      if (fst b, snd b) = (one, one) then (id 2 \<Otimes> Y) * q else 
        undefined"

lemma alice_out_unique [simp]:
  assumes "state 1 \<phi>"
  shows "Matrix.mat 8 (Suc 0) (\<lambda>(i, j). [[0, 0, \<phi> $$ (Suc 0, 0), \<phi> $$ (0, 0), 0, 0, 0, 0]] ! j ! i) \<noteq>
         Matrix.mat 8 (Suc 0) (\<lambda>(i, j). [[\<phi> $$ (0, 0), \<phi> $$ (Suc 0, 0), 0, 0, 0, 0, 0, 0]] ! j ! i) \<and> 
         Matrix.mat 8 (Suc 0) (\<lambda>(i, j). [[0, 0, 0, 0, \<phi> $$ (0, 0), -\<phi> $$ (Suc 0, 0), 0, 0]] ! j ! i) \<noteq>
         Matrix.mat 8 (Suc 0) (\<lambda>(i, j). [[\<phi> $$ (0, 0), \<phi> $$ (Suc 0, 0), 0, 0, 0, 0, 0, 0]] ! j ! i) \<and> 
         Matrix.mat 8 (Suc 0) (\<lambda>(i, j). [[0, 0, 0, 0, 0, 0, -\<phi> $$ (Suc 0, 0), \<phi> $$ (0, 0)]] ! j ! i) \<noteq>
         Matrix.mat 8 (Suc 0) (\<lambda>(i, j). [[\<phi> $$ (0, 0), \<phi> $$ (Suc 0, 0), 0, 0, 0, 0, 0, 0]] ! j ! i) \<and> 
         Matrix.mat 8 (Suc 0) (\<lambda>(i, j). [[0, 0, 0, 0, \<phi> $$ (0, 0), -\<phi> $$ (Suc 0, 0), 0, 0]] ! j ! i) \<noteq>
         Matrix.mat 8 (Suc 0) (\<lambda>(i, j). [[0, 0, \<phi> $$ (Suc 0, 0), \<phi> $$ (0, 0), 0, 0, 0, 0]] ! j ! i) \<and> 
         Matrix.mat 8 (Suc 0) (\<lambda>(i, j). [[0, 0, 0, 0, 0, 0, -\<phi> $$ (Suc 0, 0), \<phi> $$ (0, 0)]] ! j ! i) \<noteq>
         Matrix.mat 8 (Suc 0) (\<lambda>(i, j). [[0, 0, \<phi> $$ (Suc 0, 0), \<phi> $$ (0, 0), 0, 0, 0, 0]] ! j ! i) \<and> 
         Matrix.mat 8 (Suc 0) (\<lambda>(i, j). [[0, 0, 0, 0, 0, 0, -\<phi> $$ (Suc 0, 0), \<phi> $$ (0, 0)]] ! j ! i) \<noteq>
         Matrix.mat 8 (Suc 0) (\<lambda>(i, j). [[0, 0, 0, 0, \<phi> $$ (0, 0), -\<phi> $$ (Suc 0, 0), 0, 0]] ! j ! i)"
proof-
  define v1 v2 v3 v4 where a1:"v1 = Matrix.mat 8 1 (\<lambda>(i, j). [[\<phi> $$ (0, 0), \<phi> $$ (1, 0), 0, 0, 0, 0, 0, 0]] ! j ! i)"
                       and a2:"v2 = Matrix.mat 8 1 (\<lambda>(i, j). [[0, 0, \<phi> $$ (1, 0), \<phi> $$ (0, 0), 0, 0, 0, 0]] ! j ! i)"
                       and a3:"v3 = Matrix.mat 8 1 (\<lambda>(i, j). [[0, 0, 0, 0, \<phi> $$ (0, 0), -\<phi> $$ (1, 0), 0, 0]] ! j ! i)"
                       and a4:"v4 = Matrix.mat 8 1 (\<lambda>(i, j). [[0, 0, 0, 0, 0, 0, -\<phi> $$ (1, 0), \<phi> $$ (0, 0)]] ! j ! i)"
  have f0:"\<phi> $$ (0, 0) \<noteq> 0 \<or> \<phi> $$ (1, 0) \<noteq> 0"
    using assms state_def Matrix.col_def cpx_vec_length_def set_2
    by (auto simp add: atLeast0LessThan)
  then have "(v1 $$ (0,0) \<noteq> v2 $$ (0,0) \<or> v1 $$ (1,0) \<noteq> v2 $$ (1,0)) \<and> 
             (v1 $$ (0,0) \<noteq> v3 $$ (0,0) \<or> v1 $$ (1,0) \<noteq> v3 $$ (1,0)) \<and>  
             (v1 $$ (0,0) \<noteq> v4 $$ (0,0) \<or> v1 $$ (1,0) \<noteq> v4 $$ (1,0)) \<and>  
             (v2 $$ (2,0) \<noteq> v3 $$ (2,0) \<or> v2 $$ (3,0) \<noteq> v3 $$ (3,0)) \<and>  
             (v2 $$ (2,0) \<noteq> v4 $$ (2,0) \<or> v2 $$ (3,0) \<noteq> v4 $$ (3,0)) \<and>  
             (v3 $$ (4,0) \<noteq> v4 $$ (4,0) \<or> v3 $$ (5,0) \<noteq> v4 $$ (5,0))"
    using f0 a1 a2 a3 a4
    by auto
  then have "v1 \<noteq> v2 \<and> v1 \<noteq> v3 \<and> v1 \<noteq> v4 \<and> v2 \<noteq> v3 \<and> v2 \<noteq> v4 \<and> v3 \<noteq> v4"
    by force
  then show ?thesis
    using a1 a2 a3 a4
    by auto
qed

definition M3 :: "complex Matrix.mat" where 
"M3 = mat_of_cols_list 8 [[0, 1, 0, 0, 0, 0, 0, 0],
                          [1, 0, 0, 0, 0, 0, 0, 0],
                          [0, 0, 0, 1, 0, 0, 0, 0],
                          [0, 0, 1, 0, 0, 0, 0, 0],
                          [0, 0, 0, 0, 0, 1, 0, 0],
                          [0, 0, 0, 0, 1, 0, 0, 0],
                          [0, 0, 0, 0, 0, 0, 0, 1],
                          [0, 0, 0, 0, 0, 0, 1, 0]]"

lemma tensor_prod_of_id_2_x:
  shows "(id 2 \<Otimes> X) = M3"
proof
    have a0:"gate 3 (id 2 \<Otimes> X)"
      using X_is_gate tensor_gate[of "2" "id 2" "1" "X"]
      by auto
    show "dim_row (id 2 \<Otimes> X) = dim_row M3"
      using a0 gate_def
      by (auto simp add: M3_def mat_of_cols_list_def)
    show "dim_col (id 2 \<Otimes> X) = dim_col M3"
      using a0 gate_def
      by (auto simp add: M3_def mat_of_cols_list_def)
    show "\<And>i j. i < dim_row M3 \<Longrightarrow> j < dim_col M3 \<Longrightarrow> (id 2 \<Otimes> X) $$ (i, j) = M3 $$ (i, j)"
    proof-
      fix i j assume "i < dim_row M3" and "j < dim_col M3"
      then have "i \<in> {0,1,2,3,4,5,6,7} \<and> j \<in> {0,1,2,3,4,5,6,7}"
        by (auto simp add: M3_def mat_of_cols_list_def)
      then show "(id 2 \<Otimes> X) $$ (i, j) = M3 $$ (i, j)"
        using id_def X_def index_tensor_mat[of "id 2" "4" "4" "X" "2" "2" "i" "j"] gate_def X_is_gate id_is_gate id_def
        by (auto simp add: M3_def mat_of_cols_list_def X_def)
    qed
qed

definition M4 :: "complex Matrix.mat" where 
"M4 = mat_of_cols_list 8 [[0, \<i>, 0, 0, 0, 0, 0, 0],
                          [-\<i>, 0, 0, 0, 0, 0, 0, 0],
                          [0, 0, 0, \<i>, 0, 0, 0, 0],
                          [0, 0, -\<i>, 0, 0, 0, 0, 0],
                          [0, 0, 0, 0, 0, \<i>, 0, 0],
                          [0, 0, 0, 0, -\<i>, 0, 0, 0],
                          [0, 0, 0, 0, 0, 0, 0, \<i>],
                          [0, 0, 0, 0, 0, 0, -\<i>, 0]]"

lemma tensor_prod_of_id_2_y:
  shows "(id 2 \<Otimes> Y) = M4"
proof
    have a0:"gate 3 (id 2 \<Otimes> Y)"
      using Y_is_gate tensor_gate[of "2" "id 2" "1" "Y"]
      by auto
    show "dim_row (id 2 \<Otimes> Y) = dim_row M4"
      using a0 gate_def
      by (auto simp add: M4_def mat_of_cols_list_def)
    show "dim_col (id 2 \<Otimes> Y) = dim_col M4"
      using a0 gate_def
      by (auto simp add: M4_def mat_of_cols_list_def)
    show "\<And>i j. i < dim_row M4 \<Longrightarrow> j < dim_col M4 \<Longrightarrow> (id 2 \<Otimes> Y) $$ (i, j) = M4 $$ (i, j)"
    proof-
      fix i j assume "i < dim_row M4" and "j < dim_col M4"
      then have "i \<in> {0,1,2,3,4,5,6,7} \<and> j \<in> {0,1,2,3,4,5,6,7}"
        by (auto simp add: M4_def mat_of_cols_list_def)
      then show "(id 2 \<Otimes> Y) $$ (i, j) = M4 $$ (i, j)"
        using id_def Y_def index_tensor_mat[of "id 2" "4" "4" "Y" "2" "2" "i" "j"] gate_def Y_is_gate id_is_gate id_def
        by (auto simp add: M4_def mat_of_cols_list_def Y_def)
    qed
qed

definition M5 :: "complex Matrix.mat" where 
"M5 = mat_of_cols_list 8 [[1, 0, 0, 0, 0, 0, 0, 0],
                          [0, -1, 0, 0, 0, 0, 0, 0],
                          [0, 0, 1, 0, 0, 0, 0, 0],
                          [0, 0, 0, -1, 0, 0, 0, 0],
                          [0, 0, 0, 0, 1, 0, 0, 0],
                          [0, 0, 0, 0, 0, -1, 0, 0],
                          [0, 0, 0, 0, 0, 0, 1, 0],
                          [0, 0, 0, 0, 0, 0, 0, -1]]"

lemma tensor_prod_of_id_2_z:
  shows "(id 2 \<Otimes> Z) = M5"
proof
    have a0:"gate 3 (id 2 \<Otimes> Z)"
      using Z_is_gate tensor_gate[of "2" "id 2" "1" "Z"]
      by auto
    show "dim_row (id 2 \<Otimes> Z) = dim_row M5"
      using a0 gate_def
      by (auto simp add: M5_def mat_of_cols_list_def)
    show "dim_col (id 2 \<Otimes> Z) = dim_col M5"
      using a0 gate_def
      by (auto simp add: M5_def mat_of_cols_list_def)
    show "\<And>i j. i < dim_row M5 \<Longrightarrow> j < dim_col M5 \<Longrightarrow> (id 2 \<Otimes> Z) $$ (i, j) = M5 $$ (i, j)"
    proof-
      fix i j assume "i < dim_row M5" and "j < dim_col M5"
      then have "i \<in> {0,1,2,3,4,5,6,7} \<and> j \<in> {0,1,2,3,4,5,6,7}"
        by (auto simp add: M5_def mat_of_cols_list_def)
      then show "(id 2 \<Otimes> Z) $$ (i, j) = M5 $$ (i, j)"
        using id_def Z_def index_tensor_mat[of "id 2" "4" "4" "Z" "2" "2" "i" "j"] gate_def Z_is_gate id_is_gate id_def
        by (auto simp add: M5_def mat_of_cols_list_def Z_def)
    qed
qed

lemma teleportation:
  assumes "state 1 \<phi>" and "state 3 q" and "List.member (Alice_meas \<phi>) (p, q)"
  shows "\<exists>r. state 2 r \<and> Bob q (Alice_out \<phi> q) = r \<Otimes> \<phi>"
proof-
  define \<alpha> \<beta> where a0:"\<alpha> = \<phi> $$ (0,0)" and a1:"\<beta> = \<phi> $$ (1,0)"
  then have "q = mat_of_cols_list 8 [[\<alpha>, \<beta>, 0, 0, 0, 0, 0, 0]] \<or>
        q = mat_of_cols_list 8 [[0, 0, \<beta>, \<alpha>, 0, 0, 0, 0]] \<or>
        q = mat_of_cols_list 8 [[0, 0, 0, 0, \<alpha>, -\<beta>, 0, 0]] \<or>
        q = mat_of_cols_list 8 [[0, 0, 0, 0, 0, 0, -\<beta>, \<alpha>]]"
    using assms Alice_case Alice_pos_def
    by auto
  moreover have "q = mat_of_cols_list 8 [[\<alpha>, \<beta>, 0, 0, 0, 0, 0, 0]] \<Longrightarrow> Bob q (Alice_out \<phi> q) = 
mat_of_cols_list 4 [[1, 0, 0, 0]] \<Otimes> \<phi>"
  proof
    assume asm:"q = Tensor.mat_of_cols_list 8 [[\<alpha>, \<beta>, 0, 0, 0, 0, 0, 0]]"
    show "dim_row (Bob q (Alice_out \<phi> q)) = dim_row (Tensor.mat_of_cols_list 4 [[1, 0, 0, 0]] \<Otimes> \<phi>)"
      using mat_of_cols_list_def a0 a1 assms state_def Bob_def Alice_out_def asm
      by auto
    show "dim_col (Bob q (Alice_out \<phi> q)) = dim_col (Tensor.mat_of_cols_list 4 [[1, 0, 0, 0]] \<Otimes> \<phi>)"
      using mat_of_cols_list_def a0 a1 assms state_def Bob_def Alice_out_def asm
      by auto
    show "\<And>i j. i < dim_row (Tensor.mat_of_cols_list 4 [[1, 0, 0, 0]] \<Otimes> \<phi>) \<Longrightarrow> 
                j < dim_col (Tensor.mat_of_cols_list 4 [[1, 0, 0, 0]] \<Otimes> \<phi>) \<Longrightarrow>
           Bob q (Alice_out \<phi> q) $$ (i, j) = (Tensor.mat_of_cols_list 4 [[1, 0, 0, 0]] \<Otimes> \<phi>) $$ (i, j)"
    proof-
      fix i j assume "i < dim_row (Tensor.mat_of_cols_list 4 [[1, 0, 0, 0]] \<Otimes> \<phi>)" and
                     "j < dim_col (Tensor.mat_of_cols_list 4 [[1, 0, 0, 0]] \<Otimes> \<phi>)"
      then have "i \<in> {0,1,2,3,4,5,6,7} \<and> j = 0"
        using asm set_8 mat_of_cols_list_def assms state_def
        by auto
      then show "Bob q (Alice_out \<phi> q) $$ (i, j) = (Tensor.mat_of_cols_list 4 [[1, 0, 0, 0]] \<Otimes> \<phi>) $$ (i, j)"
        using Bob_def Alice_out_def asm mat_of_cols_list_def a0 a1 assms state_def
        by (auto)
    qed
  qed
  moreover have "q = mat_of_cols_list 8 [[0, 0, \<beta>, \<alpha>, 0, 0, 0, 0]] \<Longrightarrow> Bob q (Alice_out \<phi> q) = 
mat_of_cols_list 4 [[0, 1, 0, 0]] \<Otimes> \<phi>"
  proof
    assume asm:"q = Tensor.mat_of_cols_list 8 [[0, 0, \<beta>, \<alpha>, 0, 0, 0, 0]]"
    show "dim_row (Bob q (Alice_out \<phi> q)) = dim_row (Tensor.mat_of_cols_list 4 [[0, 1, 0, 0]] \<Otimes> \<phi>)"
      using mat_of_cols_list_def a0 a1 assms(1) state_def Bob_def Alice_out_def asm tensor_prod_of_id_2_x
      by (auto simp add: M3_def)
    show "dim_col (Bob q (Alice_out \<phi> q)) = dim_col (Tensor.mat_of_cols_list 4 [[0, 1, 0, 0]] \<Otimes> \<phi>)"
      using mat_of_cols_list_def a0 a1 assms(1) state_def Bob_def Alice_out_def asm
      by auto      
    show "\<And>i j. i < dim_row (Tensor.mat_of_cols_list 4 [[0, 1, 0, 0]] \<Otimes> \<phi>) \<Longrightarrow> 
                j < dim_col (Tensor.mat_of_cols_list 4 [[0, 1, 0, 0]] \<Otimes> \<phi>) \<Longrightarrow>
           Bob q (Alice_out \<phi> q) $$ (i, j) = (Tensor.mat_of_cols_list 4 [[0, 1, 0, 0]] \<Otimes> \<phi>) $$ (i, j)"
    proof-
      fix i j assume "i < dim_row (Tensor.mat_of_cols_list 4 [[0, 1, 0, 0]] \<Otimes> \<phi>)" and
                     "j < dim_col (Tensor.mat_of_cols_list 4 [[0, 1, 0, 0]] \<Otimes> \<phi>)"
      then have c1:"i \<in> {0,1,2,3,4,5,6,7} \<and> j = 0"
        using asm set_8 mat_of_cols_list_def assms(1) state_def
        by auto
      then have "(M3 * (Matrix.mat 8 (Suc 0) (\<lambda>(i, j). [[0, 0, \<phi> $$ (Suc 0, 0), \<phi> $$ (0, 0), 0, 0, 0, 0]] ! j ! i))) $$ (i, j) = 
(Tensor.mat_of_cols_list 4 [[0, 1, 0, 0]] \<Otimes> \<phi>) $$ (i, j)"
        using state_def assms(1)
        by (auto simp add: M3_def a0 a1 mat_of_cols_list_def times_mat_def scalar_prod_def)
      then show "Bob q (Alice_out \<phi> q) $$ (i, j) = (Tensor.mat_of_cols_list 4 [[0, 1, 0, 0]] \<Otimes> \<phi>) $$ (i, j)"
        using Bob_def Alice_out_def asm c1 a0 a1 mat_of_cols_list_def tensor_prod_of_id_2_x assms(1)
        by auto
    qed
  qed
  moreover have "q = mat_of_cols_list 8 [[0, 0, 0, 0, \<alpha>, -\<beta>, 0, 0]] \<Longrightarrow> Bob q (Alice_out \<phi> q) = 
mat_of_cols_list 4 [[0, 0, 1, 0]] \<Otimes> \<phi>"
  proof
    assume asm:"q = Tensor.mat_of_cols_list 8 [[0, 0, 0, 0, \<alpha>, -\<beta>, 0, 0]]"
    show "dim_row (Bob q (Alice_out \<phi> q)) = dim_row (Tensor.mat_of_cols_list 4 [[0, 0, 1, 0]] \<Otimes> \<phi>)"
      using mat_of_cols_list_def a0 a1 assms(1) state_def Bob_def Alice_out_def asm tensor_prod_of_id_2_z
      by (auto simp add: M5_def)
    show "dim_col (Bob q (Alice_out \<phi> q)) = dim_col (Tensor.mat_of_cols_list 4 [[0, 0, 1, 0]] \<Otimes> \<phi>)"
      using mat_of_cols_list_def a0 a1 assms(1) state_def Bob_def Alice_out_def asm
      by auto      
    show "\<And>i j. i < dim_row (Tensor.mat_of_cols_list 4 [[0, 0, 1, 0]] \<Otimes> \<phi>) \<Longrightarrow> 
                j < dim_col (Tensor.mat_of_cols_list 4 [[0, 0, 1, 0]] \<Otimes> \<phi>) \<Longrightarrow>
           Bob q (Alice_out \<phi> q) $$ (i, j) = (Tensor.mat_of_cols_list 4 [[0, 0, 1, 0]] \<Otimes> \<phi>) $$ (i, j)"
    proof-
      fix i j assume "i < dim_row (Tensor.mat_of_cols_list 4 [[0, 0, 1, 0]] \<Otimes> \<phi>)" and
                     "j < dim_col (Tensor.mat_of_cols_list 4 [[0, 0, 1, 0]] \<Otimes> \<phi>)"
      then have c1:"i \<in> {0,1,2,3,4,5,6,7} \<and> j = 0"
        using asm set_8 mat_of_cols_list_def assms state_def
        by auto
      then have "(M5 * (Matrix.mat 8 (Suc 0) (\<lambda>(i, j). [[0, 0, 0, 0, \<phi> $$ (0, 0), -\<phi> $$ (Suc 0, 0), 0, 0]] ! j ! i))) $$ (i, j) = 
(Tensor.mat_of_cols_list 4 [[0, 0, 1, 0]] \<Otimes> \<phi>) $$ (i, j)"
        using state_def assms(1)
        by (auto simp add: M5_def a0 a1 mat_of_cols_list_def times_mat_def scalar_prod_def)
      then show "Bob q (Alice_out \<phi> q) $$ (i, j) = (Tensor.mat_of_cols_list 4 [[0, 0, 1, 0]] \<Otimes> \<phi>) $$ (i, j)"
        using Bob_def Alice_out_def asm c1 a0 a1 mat_of_cols_list_def tensor_prod_of_id_2_z assms(1)
        by auto
    qed
  qed
  moreover have "q = mat_of_cols_list 8 [[0, 0, 0, 0, 0, 0, -\<beta>, \<alpha>]] \<Longrightarrow> Bob q (Alice_out \<phi> q) = 
mat_of_cols_list 4 [[0, 0, 0, -\<i>]] \<Otimes> \<phi>"
  proof
    assume asm:"q = Tensor.mat_of_cols_list 8 [[0, 0, 0, 0, 0, 0, -\<beta>, \<alpha>]]"
    show "dim_row (Bob q (Alice_out \<phi> q)) = dim_row (Tensor.mat_of_cols_list 4 [[0, 0, 0, -\<i>]] \<Otimes> \<phi>)"
      using mat_of_cols_list_def a0 a1 assms(1) state_def Bob_def Alice_out_def asm tensor_prod_of_id_2_y
      by (auto simp add: M4_def)
    show "dim_col (Bob q (Alice_out \<phi> q)) = dim_col (Tensor.mat_of_cols_list 4 [[0, 0, 0, -\<i>]] \<Otimes> \<phi>)"
      using mat_of_cols_list_def a0 a1 assms(1) state_def Bob_def Alice_out_def asm
      by auto      
    show "\<And>i j. i < dim_row (Tensor.mat_of_cols_list 4 [[0, 0, 0, -\<i>]] \<Otimes> \<phi>) \<Longrightarrow> 
                j < dim_col (Tensor.mat_of_cols_list 4 [[0, 0, 0, -\<i>]] \<Otimes> \<phi>) \<Longrightarrow>
           Bob q (Alice_out \<phi> q) $$ (i, j) = (Tensor.mat_of_cols_list 4 [[0, 0, 0, -\<i>]] \<Otimes> \<phi>) $$ (i, j)"
    proof-
      fix i j assume "i < dim_row (Tensor.mat_of_cols_list 4 [[0, 0, 0, -\<i>]] \<Otimes> \<phi>)" and
                     "j < dim_col (Tensor.mat_of_cols_list 4 [[0, 0, 0, -\<i>]] \<Otimes> \<phi>)"
      then have c1:"i \<in> {0,1,2,3,4,5,6,7} \<and> j = 0"
        using asm set_8 mat_of_cols_list_def assms state_def
        by auto
      then have "(M4 * (Matrix.mat 8 (Suc 0) (\<lambda>(i, j). [[0, 0, 0, 0, 0, 0, -\<phi> $$ (Suc 0, 0), \<phi> $$ (0, 0)]] ! j ! i))) $$ (i, j) = 
(Tensor.mat_of_cols_list 4 [[0, 0, 0, -\<i>]] \<Otimes> \<phi>) $$ (i, j)"
        using state_def assms(1)
        by (auto simp add: M4_def a0 a1 mat_of_cols_list_def times_mat_def scalar_prod_def)
      then show "Bob q (Alice_out \<phi> q) $$ (i, j) = (Tensor.mat_of_cols_list 4 [[0, 0, 0, -\<i>]] \<Otimes> \<phi>) $$ (i, j)"
        using Bob_def Alice_out_def asm c1 a0 a1 mat_of_cols_list_def tensor_prod_of_id_2_y assms(1)
        by auto
    qed
  qed
  moreover have "state 2 (mat_of_cols_list 4 [[1, 0, 0, 0]])"
    using state_def mat_of_cols_list_def cpx_vec_length_def lessThan_atLeast0
    by (auto)
  moreover have "state 2 (mat_of_cols_list 4 [[0, 1, 0, 0]])"
    using state_def mat_of_cols_list_def cpx_vec_length_def lessThan_atLeast0
    by (auto)
  moreover have "state 2 (mat_of_cols_list 4 [[0, 0, 1, 0]])"
    using state_def mat_of_cols_list_def cpx_vec_length_def lessThan_atLeast0
    by (auto)
  moreover have "state 2 (mat_of_cols_list 4 [[0, 0, 0, -\<i>]])"
    using state_def mat_of_cols_list_def cpx_vec_length_def lessThan_atLeast0
    by (auto)
  ultimately show ?thesis
    by auto
qed

(* 
Bibliography:

- Jaap Boender, Florian Kammüller, Rajagopal Nagarajan, Formalization of Quantum Protocols Using Coq, 
Proceedings QPL 2015, arXiv:1511.01181 
*)


end