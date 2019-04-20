(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk *)

theory MoreTensor
imports
  Main
  HOL.Complex
  Quantum
  Jordan_Normal_Form.Matrix
  Matrix_Tensor.Matrix_Tensor
  Tensor
begin

text \<open>The property of being a state (resp. a gate) is preserved by tensor product.\<close>

lemma tensor_state:
  assumes "state m u" and "state n v"
  shows "state (m + n) (u \<Otimes> v)"
proof-
  have f1:"dim_col (u \<Otimes> v) = 1"
    using assms 
    by (simp add: dim_col_tensor_mat state_def)
  have f2:"dim_row (u \<Otimes> v) = 2^(m + n)"
    using assms state_def dim_row_tensor_mat
    by (simp add: power_add)
  then have "\<parallel>Matrix.col (u \<Otimes> v) 0\<parallel> = 1" sorry
  thus ?thesis
    using f1 f2 state_def 
    by simp
qed


lemma tensor_gate:
  assumes "gate m G1" and "gate n G2"
  shows "gate  (m + n) (G1 \<Otimes> G2)" sorry

end