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

lemma tensor_prod_2:"mult.vec_vec_Tensor ( * ) [x1::complex,x2] [x3,x4] = [x1*x3,x1*x4,x2*x3,x2*x4]"
proof-
  have f0:"Matrix_Tensor.mult (1::complex) ( * )" 
  proof
    fix a::complex and b::complex and c::complex and x::complex
    show "a * b = b * a" by simp
    show "a * b * c = a * (b * c)" by simp
    show "1 * x = x" by simp
    show "x * 1 = x" by simp
  qed
  show "mult.vec_vec_Tensor ( * ) [x1::complex,x2] [x3,x4] = [x1*x3,x1*x4,x2*x3,x2*x4]"
    using mult.vec_vec_Tensor_def[of "(1::complex)" "( * )"] mult.times_def[of "(1::complex)" "( * )"]
  by(simp add: f0)
qed

lemma list_vec: 
  assumes "v \<in> state_qbit 1"
  shows "list_of_vec v = [v $ 0, v $ 1]"
proof-
  have a1:"Rep_vec v = (fst(Rep_vec v), snd(Rep_vec v))" 
    by auto
  have a2:"fst(Rep_vec v) = 2" 
    using state_qbit_def assms
    by(auto simp add: dim_vec.rep_eq)
  have a3:"Rep_vec v = (2, vec_index v)"
    using a1 a2 vec_index.rep_eq
    by(auto simp add: vec_index.rep_eq)
  have a4:"[0..<2::nat] = [0,1]"
    by(simp add: upt_rec) 
  show ?thesis
    using a3 a4
    by(auto simp add: list_of_vec_def)
qed

lemma vec_tensor_prod_2:
  assumes "v \<in> state_qbit 1" and "w \<in> state_qbit 1"
  shows "v \<otimes> w = vec_of_list [v $ 0 * w $ 0, v $ 0 * w $ 1, v $ 1 * w $ 0, v $ 1 * w $ 1]"
proof-
  have f1:"list_of_vec v = [v $ 0, v $ 1]"
    using list_vec assms
    by simp
  have f2:"list_of_vec w = [w $ 0, w $ 1]"
    using list_vec assms
    by simp
  show "v \<otimes> w = vec_of_list [v $ 0 * w $ 0, v $ 0 * w $ 1, v $ 1 * w $ 0, v $ 1 * w $ 1]"
    by(simp add: tensor_vec_def f1 f2 tensor_prod_2)
qed

lemma vec_dim_of_vec_of_list:
  assumes "length l = n"
  shows "dim_vec (vec_of_list l) = n"
  using assms vec_of_list_def 
  by simp

lemma vec_tensor_prod_2_bis:
  assumes "v \<in> state_qbit 1" and "w \<in> state_qbit 1"
  shows "v \<otimes> w = Matrix.vec 4 (\<lambda>i. if i = 0 then v $ 0 * w $ 0 else 
                                      if i = 3 then v $ 1 * w $ 1 else
                                          if i = 1 then v $ 0 * w $ 1 else v $ 1 * w $ 0)"
proof-
  have f1:"\<forall>i::nat. i \<noteq> Suc 0 \<longrightarrow> i \<noteq> 3 \<longrightarrow> 0 < i \<longrightarrow> i < 4 \<longrightarrow> i = 2" 
    by simp
  define u where "u = Matrix.vec 4 (\<lambda>i. if i = 0 then v $ 0 * w $ 0 else 
                                          if i = 3 then v $ 1 * w $ 1 else
                                            if i = 1 then v $ 0 * w $ 1 else v $ 1 * w $ 0)"
  have f2:"dim_vec (v \<otimes> w) = 4"
    using assms vec_tensor_prod_2 vec_dim_of_vec_of_list 
    by simp
  have "\<forall>i < 4. (v \<otimes> w) $ i = u $ i"
    apply (auto simp: u_def vec_of_list_index)
    using assms vec_tensor_prod_2 apply auto[3]
    apply (simp add: numeral_3_eq_3)
    using f1 u_def vec_of_list_index vec_tensor_prod_2
    by (metis (no_types, lifting) One_nat_def assms nth_Cons_0 nth_Cons_Suc numeral_2_eq_2)
  thus ?thesis
    using vec_eq_iff f2 u_def 
    by auto
qed

lemma index_col_mat_of_cols_list:
  assumes "i < n" and "j < length l"
  shows "Matrix.col (mat_of_cols_list n l) j $ i = l ! j ! i"
  apply (auto simp: Matrix.col_def mat_of_cols_list_def)
  using assms less_le_trans 
  by fastforce

lemma multTensor2:
  assumes "A = Matrix.mat 2 1 (\<lambda>(i,j). if i = 0 then a0 else a1)" and 
"B = Matrix.mat 2 1 (\<lambda>(i,j). if i = 0 then b0 else b1)"
  shows "mult.Tensor ( * ) (mat_to_cols_list A) (mat_to_cols_list B) =  
[[a0 * b0, a0 * b1, a1 * b0, a1 * b1]]"
proof-
  have f1:"mat_to_cols_list A = [[a0, a1]]"
    apply (auto simp: assms(1) mat_to_cols_list_def)
    by (simp add: numeral_2_eq_2)
  have f2:"mat_to_cols_list B = [[b0, b1]]"
    apply (auto simp: assms(2) mat_to_cols_list_def)
    by (simp add: numeral_2_eq_2)
  then have "mult.Tensor ( * ) (mat_to_cols_list A) (mat_to_cols_list B) =
mult.Tensor ( * ) [[a0, a1]] [[b0, b1]]"
    using f1 
    by simp
  thus ?thesis
    using mult.Tensor_def[of "(1::complex)" "( * )"] mult.times_def[of "(1::complex)" "( * )"]
    by (smt append_self_conv list.simps(6) mult.Tensor.simps(2) mult.commute mult.intro mult.right_neutral 
mult.vec_mat_Tensor.simps(1) mult.vec_mat_Tensor.simps(2) semiring_normalization_rules(18) tensor_prod_2)
qed

lemma multTensor2_bis:
  assumes "dim_row A = 2" and "dim_col A = 1" and "dim_row B = 2" and "dim_col B = 1"
  shows "mult.Tensor ( * ) (mat_to_cols_list A) (mat_to_cols_list B) =  
[[A $$ (0,0) * B $$ (0,0), A $$ (0,0) *  B $$ (1,0), A $$ (1,0) * B $$ (0,0), A $$ (1,0) * B $$ (1,0)]]" 
proof-
  have f1:"mat_to_cols_list A = [[A $$ (0,0), A $$ (1,0)]]"
    apply (auto simp: assms(1) assms(2) mat_to_cols_list_def)
    by (simp add: numeral_2_eq_2)
  have f2:"mat_to_cols_list B = [[B $$ (0,0), B $$ (1,0)]]"
    apply (auto simp: assms(3) assms(4) mat_to_cols_list_def)
    by (simp add: numeral_2_eq_2)
  then have "mult.Tensor ( * ) (mat_to_cols_list A) (mat_to_cols_list B) =
mult.Tensor ( * ) [[A $$ (0,0), A $$ (1,0)]] [[B $$ (0,0), B $$ (1,0)]]"
    using f1 
    by simp
  thus ?thesis
    using mult.Tensor_def[of "(1::complex)" "( * )"] mult.times_def[of "(1::complex)" "( * )"]
    by (smt append_self_conv list.simps(6) mult.Tensor.simps(2) mult.commute mult.intro mult.right_neutral 
mult.vec_mat_Tensor.simps(1) mult.vec_mat_Tensor.simps(2) semiring_normalization_rules(18) tensor_prod_2)
qed

lemma mat_tensor_prod_2_prelim:
  assumes "state 1 v" and "state 1 w"
  shows "v \<Otimes> w = 
mat_of_cols_list 4 
[[v $$ (0,0) * w $$ (0,0), v $$ (0,0) * w $$ (1,0), v $$ (1,0) * w $$ (0,0), v $$ (1,0) * w $$ (1,0)]]"
proof-
  define u where "u = mat_of_cols_list 4 
[[v $$ (0,0) * w $$ (0,0), v $$ (0,0) * w $$ (1,0), v $$ (1,0) * w $$ (0,0), v $$ (1,0) * w $$ (1,0)]]"
  then have f1:"dim_row (v \<Otimes> w) = dim_row u"
    using assms state_def mat_of_cols_list_def tensor_mat_def 
    by simp
  have f2:"dim_col (v \<Otimes> w) = dim_col u"
    using assms state_def mat_of_cols_list_def tensor_mat_def u_def
    by (smt One_nat_def Suc_eq_plus1 dim_col_mat(1) dim_col_tensor_mat list.size(3) list.size(4) 
mult.right_neutral)
  have "\<forall>i j. i < 4 \<longrightarrow> j < 1 \<longrightarrow>  (v \<Otimes> w) $$ (i, j) = u $$ (i, j)"
      using u_def tensor_mat_def assms state_def multTensor2_bis
      by simp 
  thus ?thesis
    using f1 f2 mat_eq_iff
    by (metis One_nat_def Suc_eq_plus1 Tensor.mat_of_cols_list_def dim_col_mat(1) dim_row_mat(1) 
list.size(3) list.size(4) u_def)
qed

lemma mat_tensor_prod_2_col:
  assumes "state 1 v" and "state 1 w"
  shows "Matrix.col (v \<Otimes> w) 0 = Matrix.col v 0 \<otimes> Matrix.col w 0"
proof-
  have f1:"dim_vec (Matrix.col (v \<Otimes> w) 0) = dim_vec (Matrix.col v 0 \<otimes> Matrix.col w 0)"
    using assms dim_row_tensor_mat state_def state_to_state_qbit vec_tensor_prod_2_bis
    by simp
  then have "\<forall>(i::nat)< 4. Matrix.col (v \<Otimes> w) 0 $ i = (Matrix.col v 0 \<otimes> Matrix.col w 0) $ i"
  proof-
    have "(Matrix.col v 0 \<otimes> Matrix.col w 0) $ 0 = v $$ (0,0) * w $$ (0,0)"
      using assms vec_tensor_prod_2 state_to_state_qbit col_index_of_mat_col
      by (simp add: state_def)
    then have f1:"Matrix.col (v \<Otimes> w) 0 $ 0 = (Matrix.col v 0 \<otimes> Matrix.col w 0) $ 0"
      using assms mat_tensor_prod_2_prelim index_col_mat_of_cols_list 
      by simp
    have "(Matrix.col v 0 \<otimes> Matrix.col w 0) $ 1 = v $$ (0,0) * w $$ (1,0)"
      using assms vec_tensor_prod_2 state_to_state_qbit col_index_of_mat_col
      by (simp add: state_def)
    then have f2:"Matrix.col (v \<Otimes> w) 0 $ 1 = (Matrix.col v 0 \<otimes> Matrix.col w 0) $ 1"
      using assms mat_tensor_prod_2_prelim index_col_mat_of_cols_list 
      by simp
    have "(Matrix.col v 0 \<otimes> Matrix.col w 0) $ 2 = v $$ (1,0) * w $$ (0,0)"
      using assms vec_tensor_prod_2 state_to_state_qbit col_index_of_mat_col
      by (simp add: numeral_Bit0 state_def)
    then have f3:"Matrix.col (v \<Otimes> w) 0 $ 2 = (Matrix.col v 0 \<otimes> Matrix.col w 0) $ 2"
      using assms mat_tensor_prod_2_prelim index_col_mat_of_cols_list 
      by simp
    have "(Matrix.col v 0 \<otimes> Matrix.col w 0) $ 3 = v $$ (1,0) * w $$ (1,0)"
      using assms vec_tensor_prod_2 state_to_state_qbit col_index_of_mat_col
      by (simp add: numeral_3_eq_3 state_def)
    then have f4:"Matrix.col (v \<Otimes> w) 0 $ 3 = (Matrix.col v 0 \<otimes> Matrix.col w 0) $ 3"
      using assms mat_tensor_prod_2_prelim index_col_mat_of_cols_list 
      by simp
    have "\<forall>i::nat. i < 4 \<longrightarrow> i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3" 
      by auto
    thus ?thesis
      using f1 f2 f3 f4 
      by auto
  qed
  thus ?thesis
    using vec_eq_iff f1 assms state_def
    by (simp add: vec_eq_iff state_to_state_qbit vec_tensor_prod_2_bis)
qed

lemma mat_tensor_prod_2:
  assumes "state 1 v" and "state 1 w"
  shows "v \<Otimes> w = Matrix.mat 4 1 (\<lambda>(i,j). if i = 0 then v $$ (0,0) * w $$ (0,0) else 
                                            if i = 3 then v $$ (1,0) * w $$ (1,0) else
                                              if i = 1 then v $$ (0,0) * w $$ (1,0) else 
                                                v $$ (1,0) * w $$ (0,0))"
proof-
  define u where "u = Matrix.mat 4 1 (\<lambda>(i,j). if i = 0 then v $$ (0,0) * w $$ (0,0) else 
                                            if i = 3 then v $$ (1,0) * w $$ (1,0) else
                                              if i = 1 then v $$ (0,0) * w $$ (1,0) else 
                                                v $$ (1,0) * w $$ (0,0))"
  have "dim_row (v \<Otimes> w) = dim_row u"
    using assms tensor_mat_def state_def u_def
    by (simp add: Tensor.mat_of_cols_list_def)
  then have f1:"dim_row (v \<Otimes> w) = 4"
    using u_def
    by simp
  have "dim_col (v \<Otimes> w) = dim_col u"
    using u_def assms tensor_mat_def state_def Tensor.mat_of_cols_list_def dim_col_tensor_mat 
    by simp
  then have "dim_col (v \<Otimes> w) = 1"
    using u_def
    by simp
  then have "\<And>i j. i < 4 \<Longrightarrow> j < 1 \<Longrightarrow>
           (v \<Otimes> w) $$ (i, j) = u $$ (i,j)"
  proof-
    fix i j::nat
    assume a1:"i < 4" and a2:"j < 1"
    then have "(v \<Otimes> w) $$ (i, j) = Matrix.col (v \<Otimes> w) 0 $ i"
      using Matrix.col_def
      by (simp add: \<open>dim_col (v \<Otimes> w) = 1\<close> f1)
    then have f1:"(v \<Otimes> w) $$ (i, j) = (Matrix.col v 0 \<otimes> Matrix.col w 0) $ i"
      using assms mat_tensor_prod_2_col 
      by simp
    have "(Matrix.col v 0 \<otimes> Matrix.col w 0) $ i = 
 Matrix.vec 4 (\<lambda>i. if i = 0 then Matrix.col v 0 $ 0 * Matrix.col w 0 $ 0 else 
                                      if i = 3 then Matrix.col v 0 $ 1 * Matrix.col w 0 $ 1 else
                                          if i = 1 then Matrix.col v 0 $ 0 * Matrix.col w 0 $ 1 else 
                                            Matrix.col v 0 $ 1 * Matrix.col w 0 $ 0) $ i"
      using vec_tensor_prod_2_bis assms state_to_state_qbit 
      by simp
    thus "(v \<Otimes> w) $$ (i, j) = u $$ (i,j)"
      using u_def a1 a2 col_index_of_mat_col assms state_def f1 
      by auto
  qed
  thus ?thesis
    using mat_eq_iff
    by (simp add: mat_eq_iff \<open>dim_col (v \<Otimes> w) = dim_col u\<close> f1 u_def)
qed
                         

lemma mat_tensor_prod_2_bis:
  assumes "state 1 v" and "state 1 w"
  shows "v \<Otimes> w = |Matrix.vec 4 (\<lambda>i. if i = 0 then v $$ (0,0) * w $$ (0,0) else 
                                          if i = 3 then v $$ (1,0) * w $$ (1,0) else
                                            if i = 1 then v $$ (0,0) * w $$ (1,0) else 
                                              v $$ (1,0) * w $$ (0,0))\<rangle>"
proof-
  define u where "u = |Matrix.vec 4 (\<lambda>i. if i = 0 then v $$ (0,0) * w $$ (0,0) else 
                                          if i = 3 then v $$ (1,0) * w $$ (1,0) else
                                            if i = 1 then v $$ (0,0) * w $$ (1,0) else 
                                              v $$ (1,0) * w $$ (0,0))\<rangle>"
  have "dim_row (v \<Otimes> w) = dim_row u"
    using assms u_def ket_vec_def mat_tensor_prod_2 
    by simp
  thus ?thesis
    using assms ket_vec_def mat_tensor_prod_2
    by (simp add: mat_eq_iff u_def dim_vec_of_col index_mat(1))
qed

lemma mat_tensor_ket_vec:
  assumes "state 1 v" and "state 1 w"
  shows "v \<Otimes> w = |(Matrix.col v 0) \<otimes> (Matrix.col w 0)\<rangle>"
proof-
  define u where "u = |(Matrix.col v 0) \<otimes> (Matrix.col w 0)\<rangle>"
  have f1:"v \<Otimes> w = |Matrix.col v 0\<rangle> \<Otimes> |Matrix.col w 0\<rangle>"
    using assms state_def col_ket_vec 
    by simp
  have f2:"dim_col (v \<Otimes> w) = dim_col u"
    using ket_vec_def assms state_def
    by (simp add: dim_col_tensor_mat u_def)
  have f3:"dim_row (v \<Otimes> w) = dim_row u"
    using ket_vec_def assms state_def u_def
    by (simp add: dim_row_tensor_mat state_qbit_def vec_tensor_prod_2_bis)
  have f4:"|Matrix.col v 0\<rangle> \<Otimes> |Matrix.col w 0\<rangle> = 
|Matrix.vec 4 (\<lambda>i. if i = 0 then |Matrix.col v 0\<rangle> $$ (0,0) * |Matrix.col w 0\<rangle> $$ (0,0) else 
                                          if i = 3 then |Matrix.col v 0\<rangle> $$ (1,0) * |Matrix.col w 0\<rangle> $$ (1,0) else
                                            if i = 1 then |Matrix.col v 0\<rangle> $$ (0,0) * |Matrix.col w 0\<rangle> $$ (1,0) else 
                                              |Matrix.col v 0\<rangle> $$ (1,0) * |Matrix.col w 0\<rangle> $$ (0,0))\<rangle>"
    using assms mat_tensor_prod_2_bis state_col_ket_vec 
    by simp
  then have f5:"|Matrix.col v 0\<rangle> \<Otimes> |Matrix.col w 0\<rangle> = 
|Matrix.vec 4 (\<lambda>i. if i = 0 then v $$ (0,0) * w $$ (0,0) else 
                                          if i = 3 then v $$ (1,0) * w $$ (1,0) else
                                            if i = 1 then v $$ (0,0) * w $$ (1,0) else 
                                              v $$ (1,0) * w $$ (0,0))\<rangle>"
  proof-
    have "Matrix.vec 4 (\<lambda>i. if i = 0 then |Matrix.col v 0\<rangle> $$ (0,0) * |Matrix.col w 0\<rangle> $$ (0,0) else 
                                          if i = 3 then |Matrix.col v 0\<rangle> $$ (1,0) * |Matrix.col w 0\<rangle> $$ (1,0) else
                                            if i = 1 then |Matrix.col v 0\<rangle> $$ (0,0) * |Matrix.col w 0\<rangle> $$ (1,0) else 
                                              |Matrix.col v 0\<rangle> $$ (1,0) * |Matrix.col w 0\<rangle> $$ (0,0))
= Matrix.vec 4 (\<lambda>i. if i = 0 then v $$ (0,0) * w $$ (0,0) else 
                                          if i = 3 then v $$ (1,0) * w $$ (1,0) else
                                            if i = 1 then v $$ (0,0) * w $$ (1,0) else 
                                              v $$ (1,0) * w $$ (0,0))"
      using ket_vec_index assms state_def 
      by auto
    thus ?thesis
      using eq_ket_vec f4 
      by simp
  qed
  have "|(Matrix.col v 0) \<otimes> (Matrix.col w 0)\<rangle> = 
|Matrix.vec 4 (\<lambda>i. if i = 0 then Matrix.col v 0 $ 0 * Matrix.col w 0 $ 0 else 
                                      if i = 3 then Matrix.col v 0 $ 1 * Matrix.col w 0 $ 1 else
                                          if i = 1 then Matrix.col v 0 $ 0 * Matrix.col w 0 $ 1 else 
                                            Matrix.col v 0 $ 1 * Matrix.col w 0 $ 0)\<rangle>"
    using vec_tensor_prod_2_bis assms state_to_state_qbit 
    by simp
  then have "|(Matrix.col v 0) \<otimes> (Matrix.col w 0)\<rangle> = 
|Matrix.vec 4 (\<lambda>i. if i = 0 then v $$ (0,0) * w $$ (0,0) else 
                                          if i = 3 then v $$ (1,0) * w $$ (1,0) else
                                            if i = 1 then v $$ (0,0) * w $$ (1,0) else 
                                              v $$ (1,0) * w $$ (0,0))\<rangle>"
  proof-
    have "Matrix.vec 4 (\<lambda>i. if i = 0 then Matrix.col v 0 $ 0 * Matrix.col w 0 $ 0 else 
                                      if i = 3 then Matrix.col v 0 $ 1 * Matrix.col w 0 $ 1 else
                                          if i = 1 then Matrix.col v 0 $ 0 * Matrix.col w 0 $ 1 else 
                                            Matrix.col v 0 $ 1 * Matrix.col w 0 $ 0) 
= Matrix.vec 4 (\<lambda>i. if i = 0 then v $$ (0,0) * w $$ (0,0) else 
                                          if i = 3 then v $$ (1,0) * w $$ (1,0) else
                                            if i = 1 then v $$ (0,0) * w $$ (1,0) else 
                                              v $$ (1,0) * w $$ (0,0))"
      using col_index_of_mat_col assms state_def 
      by auto
    thus ?thesis
      using vec_tensor_prod_2_bis state_to_state_qbit assms 
      by simp
  qed
  thus ?thesis
    using f1 f5 
    by simp
qed

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