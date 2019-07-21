theory Quantum_Fourier_Transform
imports
  Quantum
  Tensor
  MoreTensor
  Binary_Nat
  FFT.FFT
begin

lemma root_unit_length [simp]:
  fixes "n":: nat
  shows "root n * cnj(root n) = 1"
  by (simp add: root_def complex_eq_iff)

text\<open>
This is the phase shift gate $R_\<phi>$ on Wikipedia, but in the book it is denoted as $R_k$, with 
$\<phi> = 2\pi/(2^k)$. 
\<close>

definition phase_shift:: "nat \<Rightarrow> complex Matrix.mat" ("R _") where
"R n \<equiv> Matrix.mat 2 2 (\<lambda>(i,j). if i = j then (if i = 0 then 1 else root (2^n)) else 0)"

lemma phase_shift_is_gate [simp]:
  fixes "n":: nat
  shows "gate 1 (R n)"
proof
  show "dim_row (R n) = 2^1" by (simp add: phase_shift_def)
  show "square_mat (R n)" by (simp add: phase_shift_def)
  show "unitary (R n)"
    apply (auto simp add: one_mat_def phase_shift_def times_mat_def unitary_def)
    apply (rule cong_mat)
    by (auto simp: scalar_prod_def complex_eqI algebra_simps)
qed

text\<open>
This is the controlled phase shift gate controlled-$R_k$. It is an n-gate using the b-th qubit to 
control an $R_(b-a+1)$ gate on the a-th qubit. It is assumed that $b > a$.
\<close>

definition ctld_phase_shift:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("CR _ _ _") where
"CR n a b \<equiv> Matrix.mat (2^n) (2^n) (\<lambda>(i,j). if i = j then 
            (if (select_index n a i \<and> select_index n b i) then root (2^(b-a+1)) else 1) else 0)"

lemma transpose_of_ctld_phase_shift: 
  fixes n a b:: nat
  shows "(CR n a b)\<^sup>t = CR n a b"
  by (auto simp add: ctld_phase_shift_def)

lemma hermite_cnj_of_ctld_phase_shift [simp]:
  fixes n a b:: nat
  shows "(CR n a b)\<^sup>\<dagger> = Matrix.mat (2^n) (2^n) (\<lambda>(i,j). if i = j then 
            (if (select_index n a i \<and> select_index n b i) then cnj(root (2^(b-a+1))) else 1) else 0)"
  by (auto simp add: ctld_phase_shift_def hermite_cnj_def)

lemma empty_sum_but_one:
  fixes j n:: nat and z:: complex
  assumes "j < n"
  shows "(\<Sum>i = 0..<n. if j = i then z else 0) = z" 
  by (simp add: assms)

lemma empty_sum_but_one_mult:
  fixes j n:: nat and z:: complex
  assumes "j < n"
  shows "(\<Sum>i = 0..<n. (if j = i then z else 0) * cnj(if j = i then z else 0)) = z * cnj z"
proof-
  have "(\<Sum>i = 0..<n. (if j = i then z else 0) * cnj(if j = i then z else 0)) =
(\<Sum>i \<in> ({0..<n}-{j}). (if j = i then z else 0) * cnj(if j = i then z else 0)) + (z * cnj z)"
    using assms by (simp add: sum.remove)
  thus ?thesis by simp
qed

lemma empty_sum_in_disguise:
  fixes i j n:: nat and z1 z2:: complex
  assumes "i \<noteq> j" and "i < n" and "j < n"
  shows "(\<Sum>k = 0..<n. (if i = k then z1 else 0) * (if j = k then z2 else 0)) = 0"
  by (simp add: assms sum.neutral)

lemma empty_sum_in_disguise_cnj:
  fixes i j n:: nat and z1 z2:: complex
  assumes "i \<noteq> j" and "i < n" and "j < n"
  shows "(\<Sum>k = 0..<n. (if i = k then z1 else 0) * cnj(if j = k then z2 else 0)) = 0"
  by (simp add: assms sum.neutral)

lemma ctld_phase_shift_is_gate [simp]:
  fixes n:: nat
  assumes "b > a"
  shows "gate n (CR n a b)"
proof
  show "dim_row (CR n a b) = 2^n" by (simp add: ctld_phase_shift_def)
  moreover show "square_mat (CR n a b)" by (simp add: ctld_phase_shift_def)
  moreover have "(CR n a b) * ((CR n a b)\<^sup>\<dagger>) = 1\<^sub>m (2^n)"
    apply (auto simp add: one_mat_def ctld_phase_shift_def times_mat_def)
    apply (rule cong_mat)
    apply (auto simp: scalar_prod_def complex_eqI algebra_simps)
    apply (auto simp: empty_sum_but_one_mult sum.neutral).
  moreover have "((CR n a b)\<^sup>\<dagger>) * (CR n a b)= 1\<^sub>m (2^n)"
    apply (auto simp add: one_mat_def ctld_phase_shift_def times_mat_def)
    apply (rule cong_mat)
    apply (auto simp: scalar_prod_def complex_eqI algebra_simps)
    apply (auto simp: empty_sum_but_one_mult sum.neutral sum.remove).
  ultimately show "unitary (CR n a b)" by (simp add: unitary_def)
qed

text\<open>
This is the fourier transform on n qubits, which can be represented by a @{text "2^n * 2^n"} 
unitary matrix, i.e. an n-gate.
\<close>

definition fourier:: "nat \<Rightarrow> complex Matrix.mat" where
"fourier n \<equiv> Matrix.mat (2^n) (2^n) (\<lambda>(i,j). (root (2^n))^(i*j) / sqrt(2^n))"

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
  fixes "j":: nat 
  assumes "j < 2^n"
  shows "(\<Sum>i = 0..<2^n. root (2^n) ^ (j*i) * cnj (root (2^n)) ^ (j*i) /
         (complex_of_real (sqrt (2^n)) * complex_of_real (sqrt (2^n)))) = 1"
proof-
  have "(complex_of_real(sqrt(2^n)) * complex_of_real (sqrt(2^n))) = complex_of_real(sqrt(2^n) * sqrt(2^n))"
    by (metis of_real_mult)
  moreover have "\<dots> = complex_of_real (2^n)" by simp
  ultimately have "(\<Sum>i = 0..<2^n. (root (2^n))^(j*i) * (cnj(root(2^n)))^(j*i) /
         (complex_of_real (sqrt(2^n)) * complex_of_real (sqrt(2^n)))) =
(\<Sum>i = 0..<2^n. (1/complex_of_real (2^n)) * (root(2^n))^(j*i) * (cnj(root(2^n)))^(j*i))" by simp
  moreover have "\<dots> = (1/complex_of_real (2^n)) * (\<Sum>i = 0..<2^n.(root(2^n))^(j*i) * (cnj(root(2^n)))^(j*i))"
    using sum_distrib_left[of "1/complex_of_real (2^n)"] by (smt sum.cong algebra_simps)
  moreover have "\<forall>i::nat. root (2^n) ^ (j*i) * cnj (root (2^n)) ^ (j*i) = 1"
    by (metis power_mult_distrib power_one root_unit_length)
  ultimately show ?thesis by (simp add: power_divide)
qed

lemma fourier_is_gate [simp]:
  "gate n (fourier n)"
proof
  show "dim_row (fourier n) = 2^n" by (simp add: fourier_def)
  moreover show "square_mat (fourier n)" by (simp add: fourier_def)
  moreover have "(fourier n) * ((fourier n)\<^sup>\<dagger>) = 1\<^sub>m (2^n)"
    apply (auto simp add: one_mat_def fourier_def times_mat_def unitary_def)
    apply (rule cong_mat)
    by (auto simp: scalar_prod_def complex_eqI algebra_simps)
  moreover have "((fourier n)\<^sup>\<dagger>) * (fourier n)= 1\<^sub>m (2^n)"
    apply (auto simp add: one_mat_def fourier_def times_mat_def unitary_def)
    apply (rule cong_mat)
    by (auto simp: scalar_prod_def complex_eqI algebra_simps)
  ultimately show "unitary (fourier n)" by (simp add: unitary_def)
qed

definition SWAP :: "nat \<Rightarrow> complex Matrix.mat" where
"SWAP n \<equiv> Matrix.mat (2^n) (2^n) (\<lambda>(i,j). if (\<forall>k\<in>{0..<n}. (select_index n k i) = (select_index n (n-1-k) j)) 
                                            then 1 else 0)"

primrec qft_single_qbit :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "qft_single_qbit n i 0 v = (Id i \<Otimes> H \<Otimes> Id (n-i-1)) * |v\<rangle>"
| "qft_single_qbit n i (Suc m) v = (CR n i (i+m+1)) * |qft_single_qbit n i m v\<rangle>"

primrec qft_no_swap :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
  "qft_no_swap n 0 v = v"
| "qft_no_swap n (Suc m) v = qft_single_qbit n m (n-m-1) (qft_no_swap n m v)"

definition qft :: "nat \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
"qft n v = (SWAP n) * |qft_no_swap n n v\<rangle>"

lemma mod_pow_2_eq:
  fixes i k:: nat
  shows "i mod (2^(k+1)) = i mod 2^k \<or> i mod (2^(k+1)) = i mod 2^k + 2^k"
proof-
  have "(i mod 2^(k+1) < 2^k) \<or> (i mod 2^(k+1) \<ge> 2^k)" by auto
  moreover have "(i mod 2^(k+1)) mod 2^k = i mod 2^(k+1) \<or>
             (i mod 2^(k+1)) mod 2^k = i mod 2^(k+1) - 2^k"
    by (metis (no_types, lifting) add.commute divmod_digit_1(2) less_nat_zero_code mod_less mod_mod_trivial 
not_less plus_1_eq_Suc pos2 semiring_normalization_rules(27) zero_less_power)
  moreover have "i mod 2^(k+1) + i div 2^(k+1) * 2*(2^k) = i"
    using div_mult_mod_eq[of "i" "2^(k+1)"] by simp
  then have "(i mod 2^(k+1)) mod 2^k = i mod 2^k" by (metis mod_mult_self1)
  ultimately show ?thesis by (metis le_add_diff_inverse2 mod_less)
qed

lemma select_index_eq_to_mod_eq:
  fixes n i j k:: nat
  assumes "i < 2^n" and "j < 2^n" and "\<And>k. (k\<in>{..<n} \<Longrightarrow> select_index n k i = select_index n k j)"
  shows "k\<in>{..<n+1} \<Longrightarrow> i mod (2^k) = j mod (2^k)"
proof (induction k)
  case 0
  then show ?case by simp
next
  case c1:(Suc k)
  then have "(i mod 2^(k+1) = i mod 2^k \<and> j mod 2^(k+1) = j mod 2^k) \<or> 
             (i mod 2^(k+1) = i mod 2^k + 2^k \<and> j mod 2^(k+1) = j mod 2^k + 2^k)"
  proof-
    have "n - (k+1) < n" using c1 by simp
    moreover have "select_index n (n - (k+1)) i = (2^k \<le> i mod 2^(k+1))"
      using select_index_def assms(1) c1 by auto
    moreover have "select_index n (n - (k+1)) j = (2^k \<le> j mod 2^(k+1))"
      using select_index_def assms(2) c1 by auto
    ultimately have "(2^k \<le> i mod 2^(k+1)) = (2^k \<le> j mod 2^(k+1))"
      using assms(3) by simp
    moreover have "i mod (2^(k+1)) = i mod 2^k \<or> i mod (2^(k+1)) = i mod 2^k + 2^k"
      using mod_pow_2_eq by simp
    moreover have "j mod (2^(k+1)) = j mod 2^k \<or> j mod (2^(k+1)) = j mod 2^k + 2^k"
      using mod_pow_2_eq by simp
    moreover have "\<forall>l::nat. ((l mod 2^k < 2^k) \<and> (l mod 2^k + 2^k \<ge> 2^k))" 
      using mod_less_divisor[of "2^k"] zero_less_power[of "2" "k"] by simp 
    ultimately show ?thesis by (metis linorder_not_less)
  qed
  then show "i mod 2^(Suc k) = j mod 2^(Suc k)" using c1 by auto
qed

lemma uniq_select_index: 
  fixes i j:: "nat"
  assumes "i < 2^n" and "j < 2^n" and "i \<noteq> j"
  shows " \<exists>a\<in>{..<n}. select_index n a i = (\<not> select_index n a j)"
proof-
  have "(\<And>a. (a\<in>{..<n} \<Longrightarrow> select_index n a i = select_index n a j)) \<Longrightarrow> i = j"
  proof-
    assume "\<And>a. (a\<in>{..<n} \<Longrightarrow> select_index n a i = select_index n a j)"
    then have "i mod 2^n = j mod 2^n" 
      using assms(1,2) select_index_eq_to_mod_eq by (meson lessThan_iff less_add_one)
    then show "i = j" 
      using assms(1,2) by simp
  qed
  then show ?thesis
    using assms(3) by blast
qed

primrec qubits :: "nat \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> (nat \<Rightarrow> complex) \<Rightarrow> complex Matrix.mat" where
  "qubits 0 f g = |Matrix.vec 1 (\<lambda>i. 1)\<rangle>"
| "qubits (Suc n) f g = qubits n f g \<Otimes> |Matrix.vec 2 (\<lambda>i. if i=0 then f(n) else g(n))\<rangle>"

lemma dim_row_qubits[simp]:
  fixes n::"nat" and f g::"nat \<Rightarrow> complex"
  shows "dim_row (qubits n f g) = 2^n"
proof (induction n)
  case 0
  then show ?case
    using qubits_def ket_vec_def by simp
next
  case (Suc n)
  then show ?case
    using qubits_def ket_vec_def by simp
qed

lemma dim_col_qubits[simp]:
  fixes n::"nat" and f g::"nat \<Rightarrow> complex"
  shows "dim_col (qubits n f g) = 1"
proof (induction n)
  case 0
  then show ?case
    using qubits_def ket_vec_def by simp
next
  case (Suc n)
  then show ?case
    using qubits_def ket_vec_def by simp
qed

lemma select_index_div_2:
  fixes n i j::"nat"
  assumes "i < 2^(n+1)" and "j<n"
  shows "select_index n j (i div 2) = select_index (n+1) j i"
proof-
  have "2^(n-Suc j) \<le> i div 2 mod 2^(n-j) \<Longrightarrow> 2^(n-j) \<le> i mod 2^(n+1-j)"
  proof-
    define a::nat where a0:"a = i div 2 mod 2^(n-j)"
    assume "2^(n-Suc j) \<le> a"
    then have "2*a + i mod 2 \<ge> 2^(n-(Suc j)+1)" by simp
    then have f0:"2*a + i mod 2 \<ge> 2^(n-j)"
      by (metis Suc_diff_Suc Suc_eq_plus1 assms(2))
    have "a < 2^(n-j)" using a0 by simp
    then have "2*a + i mod 2 < 2*2^(n-j)" by linarith
    then have "2*a + i mod 2 < 2^(n-j+1)" by simp
    then have f1:"2*a + i mod 2 < 2^(n+1-j)"
      by (metis Nat.add_diff_assoc2 Suc_leD Suc_leI assms(2))
    have "i = 2*(a + 2^(n-j)*(i div 2 div 2^(n-j))) + i mod 2" using a0 by simp
    then have "i = 2*a + i mod 2 + 2^(n-j+1)*(i div 2 div 2^(n-j))" by simp
    then have "i = 2*a + i mod 2 + 2^(n+1-j)*(i div 2 div 2^(n-j))"
      by (metis Nat.add_diff_assoc2 Suc_leD Suc_leI assms(2))
    then have "i mod 2^(n+1-j) = 2*a + i mod 2"
      using f1 by (metis mod_if mod_mult_self2)
    then show "2^(n-j) \<le> i mod 2^(n+1-j)"
      using f0 by simp
  qed
  moreover have "2^(n-j) \<le> i mod 2^(n+1-j) \<Longrightarrow> 2^(n-Suc j) \<le> i div 2 mod 2^(n-j)"
  proof-
    define a::nat where a0:"a = i div 2 mod 2^(n-j)"
    assume a1:"2^(n-j) \<le> i mod 2^(n+1-j)"
    have f0:"2^(n-j) = 2^(n-Suc j+1)"
      by (metis Suc_diff_Suc Suc_eq_plus1 assms(2))
    have "a < 2^(n-j)" using a0 by simp
    then have "2*a + i mod 2 < 2*2^(n-j)" by linarith
    then have "2*a + i mod 2 < 2^(n-j+1)" by simp
    then have f1:"2*a + i mod 2 < 2^(n+1-j)"
      by (metis Nat.add_diff_assoc2 Suc_leD Suc_leI assms(2))
    have "i = 2*(a + 2^(n-j)*(i div 2 div 2^(n-j))) + i mod 2" using a0 by simp
    then have "i = 2*a + i mod 2 + 2^(n-j+1)*(i div 2 div 2^(n-j))" by simp
    then have "i = 2*a + i mod 2 + 2^(n+1-j)*(i div 2 div 2^(n-j))"
      by (metis Nat.add_diff_assoc2 Suc_leD Suc_leI assms(2))
    then have "i mod 2^(n+1-j) = 2*a + i mod 2"
      using f1 by (metis mod_if mod_mult_self2)
    then have "2*a + i mod 2 \<ge> 2^(n-j)"
      using a1 by simp
    then have "(2*a + i mod 2) div 2 \<ge> (2^(n-j)) div 2"
      using div_le_mono by blast
    then show "2^(n-Suc j) \<le> a" by (simp add: f0)
  qed
  ultimately show ?thesis
    using select_index_def assms by auto
qed

lemma qubits_rep:
  fixes n::"nat" and f g::"nat \<Rightarrow> complex"
  shows "qubits n f g = |Matrix.vec (2^n) (\<lambda>j. \<Prod>i<n. if select_index n i j then g(i) else f(i))\<rangle>"
proof (induction n)
  case 0
  define v where d0:"v = |Matrix.vec (2^0) (\<lambda>j. \<Prod>i<0. if select_index 0 i j then g(i) else f(i))\<rangle>"
  show "qubits 0 f g = v"
  proof
    show "dim_row (qubits 0 f g) = dim_row v"
      using d0 ket_vec_def by simp
    show "dim_col (qubits 0 f g) = dim_col v"
      using d0 ket_vec_def by simp
    show "\<And>i j. i < dim_row v \<Longrightarrow> j < dim_col v \<Longrightarrow> qubits 0 f g $$ (i, j) = v $$ (i, j)"
    proof-
      fix i j assume "i < dim_row v" and "j < dim_col v"
      then have "i = 0 \<and> j = 0"
        using d0 ket_vec_def by simp
      then show "qubits 0 f g $$ (i, j) = v $$ (i, j)"
        using d0 by simp
    qed
  qed
next
  case c1:(Suc n)
  define v1 where d1:"v1 = |Matrix.vec (2^n) (\<lambda>j. \<Prod>i<n. if select_index n i j then g(i) else f(i))\<rangle>"
  define v2 where d2:"v2 = |Matrix.vec (2^(Suc n)) (\<lambda>j. \<Prod>i<(Suc n). if select_index (Suc n) i j then g(i) else f(i))\<rangle>"
  have "qubits n f g = v1" using c1 d1 by simp
  moreover have "v1 \<Otimes> |Matrix.vec 2 (\<lambda>i. if i=0 then f(n) else g(n))\<rangle> = v2"
  proof
    show "dim_row (v1 \<Otimes> |Matrix.vec 2 (\<lambda>i. if i = 0 then f n else g n)\<rangle>) = dim_row v2"
      using d1 d2 ket_vec_def by simp
    show "dim_col (v1 \<Otimes> |Matrix.vec 2 (\<lambda>i. if i = 0 then f n else g n)\<rangle>) = dim_col v2"
      using d1 d2 ket_vec_def by simp
    show "\<And>i j. i < dim_row v2 \<Longrightarrow> j < dim_col v2 \<Longrightarrow> 
          (v1 \<Otimes> |Matrix.vec 2 (\<lambda>i. if i = 0 then f n else g n)\<rangle>) $$ (i, j) = v2 $$ (i, j)"
    proof-
      fix i j assume "i < dim_row v2" and "j < dim_col v2"
      then have f0:"i < 2^(n+1) \<and> j = 0"
        using d2 ket_vec_def by simp
      then have "(v1 \<Otimes> |Matrix.vec 2 (\<lambda>i. if i = 0 then f n else g n)\<rangle>) $$ (i, j) = 
                 (\<Prod>j<n. if select_index n j (i div 2) then g(j) else f(j)) * (if i mod 2 = 0 then f n else g n)"
        using ket_vec_def d1 by auto
      then have "(v1 \<Otimes> |Matrix.vec 2 (\<lambda>i. if i = 0 then f n else g n)\<rangle>) $$ (i, j) = 
                 (\<Prod>j<n. if select_index (n+1) j i then g(j) else f(j)) * (if i mod 2 = 0 then f n else g n)"
        using f0 select_index_div_2 by simp
      moreover have "(i mod 2 = 0) = (\<not>select_index (n+1) n i)"
        using f0 select_index_def by auto
      ultimately show "(v1 \<Otimes> |Matrix.vec 2 (\<lambda>i. if i = 0 then f n else g n)\<rangle>) $$ (i, j) = v2 $$ (i, j)"
        using f0 d2 by simp
    qed
  qed
  ultimately show "qubits (Suc n) f g = v2"
    using qubits_def by simp
qed

lemma tensor_with_qubits_0:
  fixes f g:: "nat \<Rightarrow> complex" and M:: "complex Matrix.mat"
  shows "M \<Otimes> (qubits 0 f g) = M"
proof
  show c0:"dim_row (M \<Otimes> qubits 0 f g) = dim_row M" 
    using dim_row_tensor_mat dim_row_qubits[of 0 f g] power_0[of 2] by simp 
  show c1:"dim_col (M \<Otimes> qubits 0 f g) = dim_col M"
    using dim_row_tensor_mat dim_col_qubits[of 0 f g] by simp
  show "\<And>i j. i < dim_row M \<Longrightarrow> j < dim_col M \<Longrightarrow> (M \<Otimes> qubits 0 f g) $$ (i, j) = M $$ (i, j)"
    using qubits.simps(1) index_tensor_mat c0 c1 by simp
qed

lemma qubits_tensor_eq:
  fixes n:: nat and f1 f2 g1 g2:: "nat \<Rightarrow> complex"
  assumes "\<forall>j<2^n. \<forall>i<n. (select_index n i j \<longrightarrow> g1(i) = g2(i)) \<and> (\<not> select_index n i j \<longrightarrow> f1(i) = f2(i))"
  shows "qubits n f1 g1 = qubits n f2 g2"
proof
  show "dim_col (qubits n f1 g1) = dim_col (qubits n f2 g2)" 
    using dim_col_qubits by simp
  show "dim_row (qubits n f1 g1) = dim_row (qubits n f2 g2)"
    using dim_row_qubits by simp
  show "\<And>i j. i < dim_row (qubits n f2 g2) \<Longrightarrow>
           j < dim_col (qubits n f2 g2) \<Longrightarrow> qubits n f1 g1 $$ (i, j) = qubits n f2 g2 $$ (i, j)"
  proof-
    have f0:"\<And>i. i < dim_row (qubits n f2 g2) \<Longrightarrow> i < 2^n" 
      using dim_row_qubits by simp
    moreover have f1:"\<And>j. j < dim_col (qubits n f2 g2) \<Longrightarrow> j = 0"
      using dim_col_qubits by simp
    ultimately show "\<And>i j. i < dim_row (qubits n f2 g2) \<Longrightarrow>
           j < dim_col (qubits n f2 g2) \<Longrightarrow> qubits n f1 g1 $$ (i, j) = qubits n f2 g2 $$ (i, j)"
      using assms eq_vecI f0 prod.cong qubits_rep by (smt dim_vec index_vec lessThan_iff)
  qed
qed

lemma qubits_tensor_prod:
  fixes n1 n2 n3:: "nat" and f1 f2 f3 g1 g2 g3:: "nat \<Rightarrow> complex"
  assumes "n1 = n2 + n3" and "\<forall>i < n2. f2 i = f1 i \<and> g2 i = g1 i" and 
"\<forall>i < n3. f3 i = f1 (i + n2) \<and> g3 i = g1 (i + n2)"
  shows "qubits n1 f1 g1 = qubits n2 f2 g2 \<Otimes> qubits n3 f3 g3"
  using assms
proof(induction n3 arbitrary: n1 n2)
  case 0
  assume "n1 = n2 + 0" and "\<forall>i < n2. f2 i = f1 i \<and> g2 i = g1 i"
  then show "qubits n1 f1 g1 = qubits n2 f2 g2 \<Otimes> qubits 0 f3 g3"
    using qubits_tensor_eq tensor_with_qubits_0 by simp
next
  case (Suc n3)
  assume a0:"\<And>n1 n2.
           n1 = n2 + n3 \<Longrightarrow>
           \<forall>i<n2. f2 i = f1 i \<and> g2 i = g1 i \<Longrightarrow>
           \<forall>i<n3. f3 i = f1 (i + n2) \<and> g3 i = g1 (i + n2) \<Longrightarrow>
           qubits n1 f1 g1 = qubits n2 f2 g2 \<Otimes> qubits n3 f3 g3" and a1:"n1 = n2 + Suc n3" and
a2:"\<forall>i<n2. f2 i = f1 i \<and> g2 i = g1 i" and a3:"\<forall>i<Suc n3. f3 i = f1 (i + n2) \<and> g3 i = g1 (i + n2)"
  then show "qubits n1 f1 g1 = qubits n2 f2 g2 \<Otimes> qubits (Suc n3) f3 g3"
  proof-
    have f0:"n1 - 1 = n2 + n3" using a1 by simp
    moreover have "qubits n2 f2 g2 \<Otimes> qubits (Suc n3) f3 g3 = 
qubits n2 f2 g2 \<Otimes> (qubits n3 f3 g3 \<Otimes> |Matrix.vec 2 (\<lambda>i. if i=0 then f3(n3) else g3(n3))\<rangle>)"
      using qubits.simps(2) by simp
    moreover have "\<dots> = (qubits n2 f2 g2 \<Otimes> qubits n3 f3 g3) \<Otimes> |Matrix.vec 2 (\<lambda>i. if i=0 then f3(n3) else g3(n3))\<rangle>"
      using tensor_mat_is_assoc by simp
    moreover have "\<dots> = (qubits n2 f2 g2 \<Otimes> qubits n3 f3 g3) \<Otimes> |Matrix.vec 2 (\<lambda>i. if i=0 then f1(n1-1) else g1(n1-1))\<rangle>"
      using a3 f0 by (metis (full_types) add.commute lessI)
    moreover have "\<dots> = qubits (n1-1) f1 g1 \<Otimes> |Matrix.vec 2 (\<lambda>i. if i=0 then f1(n1-1) else g1(n1-1))\<rangle>"
      using a0[of "n1-1" "n2"] a2 a3 f0 by simp
    ultimately show ?thesis 
      using qubits.simps(2) by (metis a1 add.commute add_Suc)
  qed
qed

lemma qft_no_swap_of_unit_vec:
  fixes v::"complex Matrix.vec"
  assumes "v = unit_vec (2^n) i" and "i < 2^n"
  shows "m \<le> n \<Longrightarrow> qft_no_swap n m v = qubits n 
         (\<lambda>j. (if j<m then 1 else (if select_index n j i then 0 else 1))*(sqrt(1/2)^m))
         (\<lambda>j. (if j<m then root (2^(n-j))^(\<Sum>l<(n-j). (2^(n-j-l)) * (if select_index n (l+k) i then 1 else 0)) 
                      else (if select_index n j i then 1 else 0))*(sqrt(1/2)^m))"
proof (induction m)
  case 0
  define w where d0:"w = qubits n 
         (\<lambda>j. (if j<0 then 1 else (if select_index n j i then 0 else 1))*(sqrt(1/2)^0))
         (\<lambda>j. (if j<0 then root (2^(n-j))^(\<Sum>l<(n-j). (2^(n-j-l)) * (if select_index n (l+k) i then 1 else 0)) 
                      else (if select_index n j i then 1 else 0))*(sqrt(1/2)^0))"
  have "qft_no_swap n 0 v = w"
  proof
    show "dim_vec (qft_no_swap n 0 v) = dim_vec w"
      by (auto simp add: assms(1) d0)
    show " \<And>j. j < dim_vec w \<Longrightarrow> (qft_no_swap n 0 v) $ j = w $ j"
    proof-
      fix j assume "j < dim_vec w"
      moreover have "\<And>k l. k<n \<Longrightarrow> (if select_index n k l then if select_index n k i then 1 else 0 else complex_of_real (if select_index n k i then 0 else 1)) = 
            (if (select_index n k l = select_index n k i) then 1 else 0)"
        by simp
      ultimately show "(qft_no_swap n 0 v) $ j = w $ j"
        using qubits_rep
        by (auto simp add: assms(1,2) d0 uniq_select_index)
    qed
  qed
  then show "0 \<le> n \<Longrightarrow> qft_no_swap n 0 v = w" by simp
next
  case c0:(Suc m)
  then have c1:"qft_no_swap n m v = qubits n 
               (\<lambda>j. (if j<m then 1 else (if select_index n j i then 0 else 1))*(sqrt(1/2)^m))
               (\<lambda>j. (if j<m then root (2^(n-j))^(\<Sum>l<(n-j). (2^(n-j-l)) * (if select_index n (l+k) i then 1 else 0)) 
                            else (if select_index n j i then 1 else 0))*(sqrt(1/2)^m))"
    by simp
  have "t \<le> n-m-1 \<Longrightarrow> qft_single_qbit n m t (qft_no_swap n m v) = qubits n 
        (\<lambda>j. (if j\<le>m then 1 else (if select_index n j i then 0 else 1))*(sqrt(1/2)^m))
        (\<lambda>j. (if j<m then root (2^(n-j))^(\<Sum>l<(n-j). (2^(n-j-l))*(if select_index n (l+k) i then 1 else 0)) 
                     else (if j=m then (root (2^(n-m)))^(\<Sum>l<t+1. (2^(n-m-l))*(if select_index n (l+m) i then 1 else 0)) 
                                  else(if select_index n j i then 1 else 0)))*(sqrt(1/2)^m))"
    sorry
  moreover have "n-(Suc m)+1 = n-m" using c0 by auto
  ultimately show "qft_no_swap n (Suc m) v = qubits n 
                   (\<lambda>j. (if j<(Suc m) then 1 else (if select_index n j i then 0 else 1))*(sqrt(1/2)^(Suc m)))
                   (\<lambda>j. (if j<(Suc m) then root (2^(n-j))^(\<Sum>l<(n-j). (2^(n-j-l)) * (if select_index n (l+k) i then 1 else 0)) 
                                else (if select_index n j i then 1 else 0))*(sqrt(1/2)^(Suc m)))"
    using qft_no_swap_def qubits_def
    sorry
qed

lemma select_index_eq_bin_rep:
  fixes n m i:: nat
  assumes "n \<ge> 1" and "m < 2^n" and "i < n"
  shows "bin_rep n m ! i = (if (select_index n i (nat m)) then 1 else 0)"
proof-
  have "m mod 2^(n-i) < 2^(n-i)" by simp
  moreover have f0:"2*2^(n-1-i) = 2^(n-1-i+1)" using power_add by auto
  moreover have f1:"(n-1-i+1) = (n-i)" using assms(3) by linarith
  ultimately have "m mod 2^(n-i) < 2*2^(n-1-i)" by metis
  then have "m mod 2^(n-i) div 2^(n-1-i) < 2" using less_mult_imp_div_less by simp
  moreover have "2^(n-1-i) \<le> m mod 2^(n-i) \<Longrightarrow> m mod 2^(n-i) div 2^(n-1-i) \<ge> 1"
    by (metis (no_types) div_greater_zero_iff div_mult2_eq nat_mult_1 nat_zero_less_power_iff pos2 
semiring_normalization_rules(7))
  ultimately have "2^(n-1-i) \<le> m mod 2^(n-i) \<Longrightarrow> int(m mod 2^(n-i) div 2^(n-1-i)) = 1" by simp 
  thus ?thesis 
    using bin_rep_index select_index_def assms
    by (smt One_nat_def Suc_diff_1 Suc_leI Suc_le_mono div_greater_zero_iff int_nat_eq less_imp_of_nat_less 
nat_2 nat_int of_nat_0_less_iff of_nat_power one_add_one plus_1_eq_Suc zdiv_int zmod_int)
qed

lemma swap_of_qubits:
  fixes n::"nat" and f g::"nat \<Rightarrow> complex"
  shows "SWAP n * qubits n f g = qubits n (\<lambda>i. f(n-1-i)) (\<lambda>i. g(n-1-i))"
proof
  define v where d0:"v = qubits n (\<lambda>i. f (n-1-i)) (\<lambda>i. g (n-1-i))"
  show "dim_row (SWAP n * qubits n f g) = dim_row v"
    using SWAP_def qubits_def d0 by simp
  show "dim_col (SWAP n * qubits n f g) = dim_col v"
    using SWAP_def qubits_def d0 by simp
  show "\<And>i j. i < dim_row v \<Longrightarrow> j < dim_col v \<Longrightarrow> (SWAP n * qubits n f g) $$ (i, j) = v $$ (i, j)"
  proof-
    fix i j assume "i < dim_row v" and "j < dim_col v"
    then show "(SWAP n * qubits n f g) $$ (i, j) = v $$ (i, j)"
      using SWAP_def qubits_rep d0 ket_vec_def uniq_select_index
      apply (auto simp add: times_mat_def scalar_prod_def)
      sorry
  qed
qed

lemma qft_of_unit_vec:
  fixes v::"complex Matrix.vec"
  assumes "v = unit_vec (2^n) i" and "i < 2^n"
  shows "qft n v = fourier n * |v\<rangle>"
proof
  show "dim_vec (qft n v) = dim_vec (col_fst (fourier n * |v\<rangle>))"
    by (simp add: qft_def fourier_def SWAP_def)
  show "\<And>i. i < dim_vec (col_fst (fourier n * |v\<rangle>)) \<Longrightarrow> qft n v $ i = col_fst (fourier n * |v\<rangle>) $ i"
  proof-
    fix i assume "i < dim_vec (col_fst (fourier n * |v\<rangle>))"
    then have "i \<in> {0..<2^n}"
      by (simp add: fourier_def)
    show "qft n v $ i = col_fst (fourier n * |v\<rangle>) $ i"
      sorry
  qed
qed

lemma sum_of_unit_vec:
  fixes v::"complex Matrix.vec"
  assumes "dim_vec v = n"
  shows "v = finsum_vec TYPE(complex) n (\<lambda>k. v $ k \<cdot>\<^sub>v unit_vec n k) {0..<n}"
proof
  define w where d0:"w = finsum_vec TYPE(complex) n (\<lambda>k. v $ k \<cdot>\<^sub>v unit_vec n k) {0..<n}"
  show c0:"dim_vec v = dim_vec w"
    using finsum_vec_closed[of "(\<lambda>k. v $ k \<cdot>\<^sub>v unit_vec n k)" "{0..<n}" "n"] carrier_vec_def unit_vec_def assms d0
    by auto
  show "\<And>i. i < dim_vec w \<Longrightarrow> v $ i = w $ i"
  proof-
    fix i assume "i < dim_vec w"
    moreover have "(\<Sum>f = 0..<dim_vec v. v $ f * (if i = f then 1 else 0)) = 
                   (\<Sum>f = 0..<dim_vec v. (if i = f then v $ f else 0))"
      using sum.cong
      by (smt mult_cancel_left1 mult_cancel_right1)
    ultimately show "v $ i = w $ i"
      using index_finsum_vec[of "{0..<n}" "i" "n" "(\<lambda>k. v $ k \<cdot>\<^sub>v unit_vec n k)"] d0 c0 assms
      by simp
  qed
qed

theorem qft_fourier: 
  fixes v::"complex Matrix.vec"
  assumes "dim_vec v = 2^n"
  shows "qft n v = fourier n * |v\<rangle>"
proof
  show "dim_vec (qft n v) = dim_vec (col_fst (fourier n * |v\<rangle>))"
    by (simp add: qft_def fourier_def SWAP_def)
  show "\<And>i. i < dim_vec (col_fst (fourier n * |v\<rangle>)) \<Longrightarrow> qft n v $ i = col_fst (fourier n * |v\<rangle>) $ i"
  proof-
    fix i assume "i < dim_vec (col_fst (fourier n * |v\<rangle>))"
    then have "i \<in> {0..<2^n}"
      by (simp add: fourier_def)
    show "qft n v $ i = col_fst (fourier n * |v\<rangle>) $ i"
      apply (auto simp add: qft_def fourier_def SWAP_def qft_no_swap_def qft_single_qbit_def)
      sorry
  qed
qed

(*
Biblio:

- Quantum Computation and Quantum Information, Michael A. Nielsen & Isaac L. Chuang, 
10th Anniversary Edition, Cambridge University Press, 2010.
*)

end