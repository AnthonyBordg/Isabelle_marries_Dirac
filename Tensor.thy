(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk *)

theory Tensor
imports
  Main
  Jordan_Normal_Form.Matrix
  Matrix_Tensor.Matrix_Tensor
  "HOL-Algebra.Ring"
begin

text{* There is already a formalization of tensor products in the Archive of Formal Proofs, 
namely Matrix_Tensor.thy in Tensor Product of Matrices[1] by T.V.H. Prathamesh, but it does not build 
on top of the formalization of vectors and matrices given in Matrices, Jordan Normal Forms, and 
Spectral Radius Theory[2] by René Thiemann and Akihisa Yamada. 
In the present theory our purpose consists in giving such a formalization. Of course, we will reuse 
Prathamesh's code as much as possible.
*}

section \<open>Tensor Products\<close>

subsection \<open>The Kronecker Product of Vectors\<close>

definition tensor_vec ::"('a::comm_monoid_mult) Matrix.vec \<Rightarrow> 'a Matrix.vec \<Rightarrow> 'a Matrix.vec" (infixl "\<otimes>" 63) 
where "tensor_vec u v \<equiv> vec_of_list (mult.vec_vec_Tensor (op *) (list_of_vec u) (list_of_vec v))"

subsection \<open>The Tensor Product of Matrices\<close>

text\<open>To see a matrix in the sense of [2] as a matrix in the sense of [1], we convert it into its list
of column vectors.\<close>

definition mat_to_cols_list :: "'a Matrix.mat \<Rightarrow> 'a list list" where
  "mat_to_cols_list A = [ [A $$ (i,j) . i <- [0 ..< dim_row A]] . j <- [0 ..< dim_col A]]"

definition tensor_mat ::"('a::comm_monoid_mult) Matrix.mat \<Rightarrow> 'a Matrix.mat \<Rightarrow> 'a Matrix.mat" (infixl "\<Otimes>" 63)
  where 
"tensor_mat A B \<equiv> mat_of_cols_list (dim_row A * dim_row B) (mult.Tensor (op *) (mat_to_cols_list A) (mat_to_cols_list B))"

lemma length_mat_to_cols_list:
  shows "length (mat_to_cols_list A) = dim_col A"
  by (simp add: mat_to_cols_list_def)
  
lemma dim_row_tensor_mat:
  shows "dim_row (A \<Otimes> B) = dim_row A * dim_row B"
  by (simp add: mat_of_cols_list_def tensor_mat_def)

lemma dim_col_tensor_mat:
  shows "dim_col (A \<Otimes> B) = dim_col A * dim_col B"
  using tensor_mat_def mat_of_cols_list_def Matrix_Tensor.mult.length_Tensor[of "1" "op *"] 
    length_mat_to_cols_list
  by (smt ab_semigroup_mult_class.mult_ac(1) comm_monoid_mult_class.mult_1 dim_col_mat(1) mult.commute mult.intro)

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
  proof-


subsection \<open>The Tensor Product of Vector Spaces\<close>




end