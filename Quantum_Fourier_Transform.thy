theory Quantum_Fourier_Transform
imports
  Quantum
  Tensor
  MoreTensor
  FFT.FFT
begin

lemma root_unit_length [simp]:
  fixes "n"::nat
  shows "root n * cnj(root n) = 1"
  by (auto simp add: root_def complex_eq_iff)

definition R::"nat \<Rightarrow> complex Matrix.mat" where
"R n \<equiv> Matrix.mat 2 2 (\<lambda>(i,j). if i=j then (if i=0 then 1 else root (2^n)) else 0)"

lemma R_is_gate [simp]:
  fixes "n"::nat
  shows "gate 1 (R n)"
proof
  show "dim_row (R n) = 2 ^ 1"
    using R_def by simp
  show "square_mat (R n)"
    using R_def by simp
  show "unitary (R n)"
    apply (auto simp add: one_mat_def R_def times_mat_def unitary_def)
    apply (rule cong_mat)
    by (auto simp: scalar_prod_def complex_eqI algebra_simps)
qed

definition Fourier::"nat \<Rightarrow> complex Matrix.mat" where
"Fourier n \<equiv> Matrix.mat (2^n) (2^n) (\<lambda>(i,j). root (2^n) ^ (i*j) / sqrt(2^n))"

lemma fourier_inv_0 [simp]:
  fixes "i" "j"::nat assumes "i < 2^n" and "j < 2^n" and "i \<noteq> j"
  shows "(\<Sum>k = 0..<2^n. root (2^n) ^ (i*k) * cnj (root (2^n)) ^ (j*k) /
         (complex_of_real (sqrt (2^n)) * complex_of_real (sqrt (2^n)))) = 0"
  sorry

lemma fourier_inv_1 [simp]:
  fixes "j"::nat assumes "j < 2^n"
  shows "(\<Sum>i = 0..<2^n. root (2^n) ^ (j*i) * cnj (root (2^n)) ^ (j*i) /
         (complex_of_real (sqrt (2^n)) * complex_of_real (sqrt (2^n)))) = 1"
  sorry

lemma Fourier_is_gate [simp]:
  "gate n (Fourier n)"
proof
  show c0:"dim_row (Fourier n) = 2^n"
    using Fourier_def by simp
  moreover show c1:"square_mat (Fourier n)"
    using Fourier_def by simp
  moreover have "(Fourier n) * ((Fourier n)\<^sup>\<dagger>) = 1\<^sub>m (2^n)"
    apply (auto simp add: one_mat_def Fourier_def times_mat_def unitary_def)
    apply (rule cong_mat)
    by (auto simp: scalar_prod_def complex_eqI algebra_simps)
  moreover have "((Fourier n)\<^sup>\<dagger>) * (Fourier n)= 1\<^sub>m (2^n)"
    apply (auto simp add: one_mat_def Fourier_def times_mat_def unitary_def)
    apply (rule cong_mat)
    by (auto simp: scalar_prod_def complex_eqI algebra_simps)
  ultimately show "unitary (Fourier n)"
    by (auto simp add: unitary_def)
qed

end