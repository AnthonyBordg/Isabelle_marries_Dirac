(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk *)

theory Tensor
imports
  Main
  Jordan_Normal_Form.Matrix
  Matrix_Tensor.Matrix_Tensor
  "HOL-Algebra.Ring"
  Rings
begin

text{* There is already a formalization of tensor products in the Archive of Formal Proofs, 
namely Matrix_Tensor.thy in Tensor Product of Matrices[1] by T.V.H. Prathamesh, but it does not build 
on top of the formalization of vectors and matrices given in Matrices, Jordan Normal Forms, and 
Spectral Radius Theory[2] by René Thiemann and Akihisa Yamada. 
In the present theory our purpose consists in giving such a formalization. Of course, we will reuse 
Prathamesh's code as much as possible.
*}

section \<open>Tensor Products\<close>

subsection \<open>The Kronecker Product of Complex Vectors\<close>

definition tensor_vec ::"complex Matrix.vec \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" (infixl "\<otimes>" 63) 
where "tensor_vec u v \<equiv> vec_of_list (mult.vec_vec_Tensor (op *) (list_of_vec u) (list_of_vec v))"

subsection \<open>The Tensor Product of Complex Matrices\<close>

text\<open>To see a matrix in the sense of [2] as a matrix in the sense of [1], we convert it into its list
of column vectors.\<close>

definition mat_to_cols_list :: "complex Matrix.mat \<Rightarrow> complex list list" where
  "mat_to_cols_list A = [ [A $$ (i,j) . i <- [0 ..< dim_row A]] . j <- [0 ..< dim_col A]]"

lemma length_mat_to_cols_list:
  shows "length (mat_to_cols_list A) = dim_col A"
  by (simp add: mat_to_cols_list_def)

lemma length_cols_mat_to_cols_list:
  assumes "j < dim_col A"
  shows "length [A $$ (i,j) . i <- [0 ..< dim_row A]] = dim_row A"
  using assms 
  by simp

lemma mat_to_cols_list_is_not_Nil:
  assumes "dim_col A > 0"
  shows "mat_to_cols_list A \<noteq> []"
  using assms
  by (simp add: mat_to_cols_list_def)

lemma row_length_mat_to_cols_list:
  assumes "dim_col A > 0"
  shows "mult.row_length (mat_to_cols_list A) = dim_row A"
proof-
  have "mat_to_cols_list A \<noteq> []"
    using assms mat_to_cols_list_is_not_Nil 
    by auto
  then have "mult.row_length (mat_to_cols_list A) = length (hd (mat_to_cols_list A))"
    using mult.row_length_def[of "1" "op *"]
    by (simp add: \<open>\<And>xs. Matrix_Tensor.mult 1 op * \<Longrightarrow> mult.row_length xs \<equiv> if xs = [] then 0 else length (hd xs)\<close> mult.intro)
  thus ?thesis
    using assms mat_to_cols_list_def length_cols_mat_to_cols_list[of 0]
    by (simp add: upt_conv_Cons)
qed

lemma mat_to_cols_list_is_mat:
  assumes "dim_col A > 0"
  shows "Matrix_Legacy.mat (mult.row_length (mat_to_cols_list A)) (length (mat_to_cols_list A)) (mat_to_cols_list A)"
  using Matrix_Legacy.mat_def
proof-
  have "Ball (set (mat_to_cols_list A)) (Matrix_Legacy.vec (mult.row_length (mat_to_cols_list A)))"
    using assms row_length_mat_to_cols_list mat_to_cols_list_def Ball_def set_def Matrix_Legacy.vec_def
    by fastforce
  thus ?thesis
    using Matrix_Legacy.mat_def 
    by auto
qed

definition mat_of_cols_list :: "nat \<Rightarrow> complex list list \<Rightarrow> complex Matrix.mat" where
  "mat_of_cols_list nr cs = Matrix.mat nr (length cs) (\<lambda> (i,j). cs ! j ! i)"

lemma index_mat_of_cols_list:
  assumes "i < nr" and "j < length cs"
  shows "mat_of_cols_list nr cs $$ (i,j) = cs ! j ! i"
  using assms mat_of_cols_list_def 
  by simp 

lemma mat_to_cols_list_to_mat:
  shows "mat_of_cols_list (dim_row A) (mat_to_cols_list A) = A"
proof-
  have f1:"dim_row (mat_of_cols_list (dim_row A) (mat_to_cols_list A)) = dim_row A"
    by (simp add: Tensor.mat_of_cols_list_def)
  have f2:"dim_col (mat_of_cols_list (dim_row A) (mat_to_cols_list A)) = dim_col A"
    by (simp add: Tensor.mat_of_cols_list_def length_mat_to_cols_list)
  have "\<And>i j. i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> 
    (mat_of_cols_list (dim_row A) (mat_to_cols_list A)) $$ (i, j) = A $$ (i, j)"
    by (simp add: Tensor.mat_of_cols_list_def mat_to_cols_list_def)
  thus ?thesis
    using f1 f2 eq_matI 
    by auto
qed

lemma list_to_mat_to_cols_list:
  fixes l::"complex list list"
  assumes "\<forall>i< length l. length (l ! i) = n"
  shows "mat_to_cols_list (mat_of_cols_list n l) = l"
proof-
  have f1:"length (mat_to_cols_list (mat_of_cols_list n l)) = length l"
    by (simp add: Tensor.mat_of_cols_list_def length_mat_to_cols_list)
  have f2:"\<forall>i<length l. mat_to_cols_list (mat_of_cols_list n l) ! i = l ! i"
    using mat_to_cols_list_def mat_of_cols_list_def
    by (smt assms atLeastLessThan_iff case_prod_conv dim_row_mat(1) f1 index_mat(1) 
        length_mat_to_cols_list map_eq_conv map_nth set_upt)
  thus ?thesis
    using f1 f2
    by (simp add: nth_equalityI)
qed

definition tensor_mat ::"complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" (infixl "\<Otimes>" 63)
  where 
"tensor_mat A B \<equiv> mat_of_cols_list (dim_row A * dim_row B) (mult.Tensor (op *) (mat_to_cols_list A) (mat_to_cols_list B))"
  
lemma dim_row_tensor_mat:
  shows "dim_row (A \<Otimes> B) = dim_row A * dim_row B"
  by (simp add: mat_of_cols_list_def tensor_mat_def)

lemma dim_col_tensor_mat:
  shows "dim_col (A \<Otimes> B) = dim_col A * dim_col B"
  using tensor_mat_def mat_of_cols_list_def Matrix_Tensor.mult.length_Tensor[of "1" "op *"] 
    length_mat_to_cols_list
  by (smt ab_semigroup_mult_class.mult_ac(1) comm_monoid_mult_class.mult_1 dim_col_mat(1) mult.commute mult.intro)

lemma index_tensor_mat:
  assumes "dim_row A = rA" and "dim_col A = cA" and "dim_row B = rB" and "dim_col B = cB"
    and "i < rA * rB" and "j < cA * cB" and "cA > 0" and "cB > 0"
  shows "(A \<Otimes> B) $$ (i,j) = A $$ (i div rB, j div cB) * B $$ (i mod rB, j mod cB)"
proof-
  have f1:"(A \<Otimes> B) $$ (i,j) = (mult.Tensor (op *) (mat_to_cols_list A) (mat_to_cols_list B)) ! j ! i"
    using assms tensor_mat_def mat_of_cols_list_def dim_col_tensor_mat 
    by auto
  have f2:"i < mult.row_length (mat_to_cols_list A) * mult.row_length (mat_to_cols_list B)"
    using assms(1) assms(2) assms(3) assms(4) assms(5) assms(7) assms(8) row_length_mat_to_cols_list
    by simp
  have f3:"j < length (mat_to_cols_list A) * length (mat_to_cols_list B)"
    using assms(2) assms(4) assms(6) length_mat_to_cols_list 
    by simp
  have f4:"Matrix_Legacy.mat (mult.row_length (mat_to_cols_list A)) (length (mat_to_cols_list A)) (mat_to_cols_list A)"
    using assms(2) assms(7) mat_to_cols_list_is_mat 
    by simp
  have f5:"Matrix_Legacy.mat (mult.row_length (mat_to_cols_list B)) (length (mat_to_cols_list B)) (mat_to_cols_list B)"
    using assms(4) assms(8) mat_to_cols_list_is_mat
    by simp
  then have "(A \<Otimes> B) $$ (i,j) = 
    (mat_to_cols_list A) ! (j div length (mat_to_cols_list B)) ! (i div mult.row_length (mat_to_cols_list B)) 
    * (mat_to_cols_list B) ! (j mod length (mat_to_cols_list B)) ! (i mod mult.row_length (mat_to_cols_list B))"
    using mult.matrix_Tensor_elements[of "1" "op *"] f1 f2 f3 f4 f5
    by (simp add: \<open>\<And>M2 M1. Matrix_Tensor.mult 1 op * \<Longrightarrow> \<forall>i j. (i < mult.row_length M1 * mult.row_length M2 
    \<and> j < length M1 * length M2) \<and> Matrix_Legacy.mat (mult.row_length M1) (length M1) M1 \<and> 
    Matrix_Legacy.mat (mult.row_length M2) (length M2) M2 \<longrightarrow> 
    mult.Tensor op * M1 M2 ! j ! i = M1 ! (j div length M2) ! (i div mult.row_length M2) * M2 ! (j mod length M2) ! (i mod mult.row_length M2)\<close> f1 f2 mult.intro)
  thus ?thesis
    using mat_to_cols_list_def
    by (smt Divides.div_mult2_eq assms(2) assms(3) assms(4) assms(6) div_eq_0_iff f2 index_mat_of_cols_list 
        length_mat_to_cols_list less_nat_zero_code mat_to_cols_list_to_mat mod_less_divisor mult.commute 
        mult_is_0 neq0_conv row_length_mat_to_cols_list)
qed
  
lemma mult_distr_tensor:
  assumes "dim_col A = dim_row B" and "dim_col C = dim_row D"
  shows "(A * B) \<Otimes> (C * D) = (A \<Otimes> C) * (B \<Otimes> D)"
proof-
  have f1:"dim_row ((A * B) \<Otimes> (C * D)) = dim_row ((A \<Otimes> C) * (B \<Otimes> D))"
    by (simp add: dim_row_tensor_mat)
  have f2:"dim_col ((A * B) \<Otimes> (C * D)) = dim_col ((A \<Otimes> C) * (B \<Otimes> D))"
    by (simp add: dim_col_tensor_mat)
  have "\<And>i j. i < dim_row ((A \<Otimes> C) * (B \<Otimes> D)) \<Longrightarrow>
           j < dim_col ((A \<Otimes> C) * (B \<Otimes> D)) \<Longrightarrow> (A * B \<Otimes> C * D) $$ (i, j) = ((A \<Otimes> C) * (B \<Otimes> D)) $$ (i, j)"
    using index_tensor_mat index_mult_mat


subsection \<open>The Tensor Product of Vector Spaces\<close>




end