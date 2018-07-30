(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk *)

theory Tensor
imports
  Main
  Jordan_Normal_Form.Matrix
  Matrix_Tensor.Matrix_Tensor
  "HOL-Algebra.Ring"
begin

text{* There are at least two formalizations of tensor products in the Archive of Formal Proofs, 
namely Matrix_Tensor.thy in Tensor Product of Matrices by T.V.H. Prathamesh and Tensor.thy in 
Expressiveness of Deep Learning by Alexander Bentkamp, but none of them build on top of the 
formalization of vectors and matrices given in Matrices, Jordan Normal Forms, and Spectral Radius 
Theory by René Thiemann and Akihisa Yamada. In the present theory our purpose consists in giving such 
a formalization. Of course, we will reuse their code as much as possible.
*}

section \<open>Tensor Products\<close>

subsection \<open>The Kronecker Product of Two Vectors\<close>

definition tensor_vec ::"('a::comm_monoid_mult) Matrix.vec \<Rightarrow> 'a Matrix.vec \<Rightarrow> 'a Matrix.vec" (infixl "\<otimes>" 63) 
where "tensor_vec u v \<equiv> vec_of_list (mult.vec_vec_Tensor (op *) (list_of_vec u) (list_of_vec v))"

subsection \<open>Tensor Products of Matrices\<close>

definition tensor_mat ::"('a::comm_monoid_mult) Matrix.mat \<Rightarrow> 'a Matrix.mat \<Rightarrow> 'a Matrix.mat" (infixl "\<Otimes>" 63)
where "tensor_mat A B \<equiv> mat_of_cols_list (dim_row A * dim_row B) (mult.Tensor (op *) (mat_to_list A) (mat_to_list B))"

subsection \<open>Tensor Products of Vector Spaces\<close>




end