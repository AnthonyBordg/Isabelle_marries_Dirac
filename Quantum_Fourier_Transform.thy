theory Quantum_Fourier_Transform
imports
  Quantum
  Tensor
  MoreTensor
  FFT.FFT
begin

lemma root_unit_length [simp]:
  fixes "n":: nat
  shows "root n * cnj(root n) = 1"
  by (simp add: root_def complex_eq_iff)

text\<open>
This is the phase shift gate R_\<phi> on Wikipedia, but in the book it is denoted as R_k, with \<phi> = 2\<pi>/(2^k).
\<close>

definition R :: "nat \<Rightarrow> complex Matrix.mat" where
"R n \<equiv> Matrix.mat 2 2 (\<lambda>(i,j). if i = j then (if i = 0 then 1 else root (2^n)) else 0)"

lemma R_is_gate [simp]:
  fixes "n":: nat
  shows "gate 1 (R n)"
proof
  show "dim_row (R n) = 2^1" by (simp add: R_def)
  show "square_mat (R n)" by (simp add: R_def)
  show "unitary (R n)"
    apply (auto simp add: one_mat_def R_def times_mat_def unitary_def)
    apply (rule cong_mat)
    by (auto simp: scalar_prod_def complex_eqI algebra_simps)
qed

text\<open>
This is the controlled phase shift gate controlled-R_k. It is an n-gate using the b-th qubit to 
control an R_(b-a+1) gate on the a-th qubit. 
\<close>

definition CR :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
"CR n a b \<equiv> Matrix.mat (2^n) (2^n) (\<lambda>(i,j). if i = j then 
            (if (select_index n a i \<and> select_index n b i) then root (2^(b-a+1)) else 1) else 0)"

lemma CR_is_gate [simp]:
  fixes "n":: nat
  assumes "b>a"
  shows "gate n (CR n a b)"
proof
  show "dim_row (CR n a b) = 2^n" by (simp add: CR_def)
  moreover show "square_mat (CR n a b)" by (simp add: CR_def)
  moreover have "(CR n a b) * ((CR n a b)\<^sup>\<dagger>) = 1\<^sub>m (2^n)"
    apply (auto simp add: one_mat_def CR_def times_mat_def unitary_def)
    apply (rule cong_mat)
    apply (auto simp: scalar_prod_def complex_eqI algebra_simps)
    sorry
  moreover have "((CR n a b)\<^sup>\<dagger>) * (CR n a b)= 1\<^sub>m (2^n)"
    apply (auto simp add: one_mat_def CR_def times_mat_def unitary_def)
    apply (rule cong_mat)
    apply (auto simp: scalar_prod_def complex_eqI algebra_simps)
    sorry
  ultimately show "unitary (CR n a b)" by (simp add: unitary_def)
qed

text\<open>
This is the Fourier transform on n qubits, which can be represented by a 2^n*2^n unitary matrix, i.e.
an n-gate.
\<close>

definition Fourier:: "nat \<Rightarrow> complex Matrix.mat" where
"Fourier n \<equiv> Matrix.mat (2^n) (2^n) (\<lambda>(i,j). (root (2^n))^(i*j) / sqrt(2^n))"

lemma sqrt_power_of_2:
  fixes "n":: nat
  shows "2^n = sqrt (2^n) * sqrt (2^n)"
  by simp

lemma fourier_inv_0 [simp]:
  fixes "i" "j":: nat 
  assumes "i < 2^n" and "j < 2^n" and "i \<noteq> j"
  shows "(\<Sum>k = 0..<2^n. root (2^n)^(i*k) * cnj (root (2^n))^(j*k) /
         (complex_of_real (sqrt (2^n)) * complex_of_real (sqrt (2^n)))) = 0"
proof (cases "i>j")
  case c0:True
  then have f0:"i-j>0" by simp
  then have "\<And>k. root (2^n)^(i*k) / (root (2^n))^(j*k) = root (2^n)^((i-j)*k)"
    by (metis (no_types, lifting) linorder_not_le nat_diff_split order_less_irrefl power_diff 
power_divide power_mult root_nonzero)
  moreover have "\<And>k. cnj (root (2^n))^(j*k) = 1 / root (2^n)^(j*k)"
    by (metis nonzero_mult_div_cancel_left power_one_over root_nonzero root_unit_length)
  ultimately have "\<And>k. root (2^n)^(i*k) * cnj (root (2^n))^(j*k) = (root (2^n)^(i-j))^k"
    by (simp add: power_mult)
  moreover have "i-j<2^n" using assms(1,2) c0 by simp
  ultimately have "(\<Sum>k = 0..<2^n. root (2^n)^(i*k) * cnj (root (2^n))^(j*k)) = 0"
    using root_summation[of "i-j" "2^n"] f0 by auto
  then show ?thesis
    using sum_divide_distrib[of "\<lambda>k. (root (2^n)^(i*k) * cnj (root (2^n))^(j*k))" "{0..<2^n}"
 "(complex_of_real (sqrt (2^n)) * complex_of_real (sqrt (2^n)))"]
    by simp
next
  case c1:False
  then have f1:"j-i>0" using assms(3) by simp
  then have "\<And>k. root (2^n)^(i*k) / (root (2^n))^(j*k) * (root (2^n)^((j-i)*k)) = 1"
    by (simp add: diff_mult_distrib power_diff root_nonzero)
  then have "\<And>k. root (2^n)^(i*k) / (root (2^n))^(j*k) = 1 / (root (2^n)^((j-i)*k))"
    by (metis nonzero_mult_div_cancel_right power_not_zero root_nonzero)
  moreover have "\<And>k. cnj (root (2^n))^(j*k) = 1 / root (2^n)^(j*k)"
    by (metis nonzero_mult_div_cancel_left power_one_over root_nonzero root_unit_length)
  ultimately have "\<And>k. root (2^n)^(i*k) * cnj (root (2^n))^(j*k) = ((1 / root (2^n))^(j-i))^k"
    by (simp add: power_mult power_one_over)
  moreover have "j-i<2^n" using assms(1,2) c1 by simp
  ultimately have "(\<Sum>k = 0..<2^n. root (2^n)^(i*k) * cnj (root (2^n))^(j*k)) = 0"
    using root_summation_inv[of "j-i" "2^n"] f1 by auto
  then show ?thesis
    using sum_divide_distrib[of "\<lambda>k. (root (2^n)^(i*k) * cnj (root (2^n))^(j*k))" "{0..<2^n}"
 "(complex_of_real (sqrt (2^n)) * complex_of_real (sqrt (2^n)))"]
    by simp
qed

lemma fourier_inv_1 [simp]:
  fixes "j"::nat assumes "j < 2^n"
  shows "(\<Sum>i = 0..<2^n. root (2^n) ^ (j*i) * cnj (root (2^n)) ^ (j*i) /
         (complex_of_real (sqrt (2^n)) * complex_of_real (sqrt (2^n)))) = 1"
proof-
  have "\<And>i. root (2^n) ^ (j*i) * cnj (root (2^n)) ^ (j*i) = 1"
    by (metis power_mult_distrib power_one root_unit_length)
  then have "(\<Sum>i = 0..<2^n. root (2^n) ^ (j*i) * cnj (root (2^n)) ^ (j*i) /
             (complex_of_real (sqrt (2^n)) * complex_of_real (sqrt (2^n)))) = 2^n /
             (complex_of_real (sqrt (2^n)) * complex_of_real (sqrt (2^n)))"
    by simp
  then show ?thesis
    apply simp
    by (metis sqrt_power_of_2 of_real_mult of_real_numeral of_real_power)
qed

lemma Fourier_is_gate [simp]:
  "gate n (Fourier n)"
proof
  show "dim_row (Fourier n) = 2^n" by (simp add: Fourier_def)
  moreover show "square_mat (Fourier n)" by (simp add: Fourier_def)
  moreover have "(Fourier n) * ((Fourier n)\<^sup>\<dagger>) = 1\<^sub>m (2^n)"
    apply (auto simp add: one_mat_def Fourier_def times_mat_def unitary_def)
    apply (rule cong_mat)
    by (auto simp: scalar_prod_def complex_eqI algebra_simps)
  moreover have "((Fourier n)\<^sup>\<dagger>) * (Fourier n)= 1\<^sub>m (2^n)"
    apply (auto simp add: one_mat_def Fourier_def times_mat_def unitary_def)
    apply (rule cong_mat)
    by (auto simp: scalar_prod_def complex_eqI algebra_simps)
  ultimately show "unitary (Fourier n)" by (simp add: unitary_def)
qed

primrec qft :: "nat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "qft 0 v = v"
| "qft (Suc n) v = |v\<rangle>" (* Still trying to find a nice way to formalize the composition of gates *)

end