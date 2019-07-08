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

lemma adding_term_to_prod:
  fixes f::"nat \<Rightarrow> complex" and m::"nat"
  shows "(\<Prod>k<m. f(k)) * f(m) = (\<Prod>k<(Suc m). f(k))"
  by auto

lemma qft_no_swap_of_unit_vec:
  fixes v::"complex Matrix.vec"
  assumes "v = unit_vec (2^n) i" and "i < 2^n"
  shows "m \<le> n \<Longrightarrow> qft_no_swap n m v = Matrix.vec (2^n) (\<lambda>j. (\<Prod>k<m. if select_index n k j then 
         root (2^(n-k))^(\<Sum>l<(n-k). (2^(n-k-l)) * (if select_index n (l+k) j then 1 else 0)) else 1) * 
         (\<Prod>k<n-m. if (select_index n (k+m) i = select_index n (k+m) j) then 1 else 0) / (sqrt(2)^m))"
proof (induction m)
  case 0
  define w where d0:"w = Matrix.vec (2^n) (\<lambda>j. (\<Prod>k<0. if select_index n k j then 
        root (2^(n-k))^(\<Sum>l<(n-k). (2^(n-k-l)) * (if select_index n (l+k) j then 1 else 0)) else 1) *
        (\<Prod>k<n-0. if select_index n (k+0) i = select_index n (k+0) j then 1 else 0) / (sqrt(2)^0))"
  have "qft_no_swap n 0 v = w"
  proof
    show "dim_vec (qft_no_swap n 0 v) = dim_vec w"
      by (auto simp add: assms(1) d0)
    show " \<And>j. j < dim_vec w \<Longrightarrow> (qft_no_swap n 0 v) $ j = w $ j"
    proof-
      fix j assume "j < dim_vec w"
      then show "(qft_no_swap n 0 v) $ j = w $ j"
        by (simp add: assms(1,2) d0 uniq_select_index)
    qed
  qed
  then show "0 \<le> n \<Longrightarrow> qft_no_swap n 0 v = w" by simp
next
  case c0:(Suc m)
  then have c1:"qft_no_swap n m v = Matrix.vec (2^n) (\<lambda>j. (\<Prod>k<m. if select_index n k j then 
             (root (2^(n-k)))^(\<Sum>l<(n-k). (2^(n-k-l)) * (if select_index n (l+k) j then 1 else 0)) else 1) * 
             (\<Prod>k<n-m. if (select_index n (k+m) i = select_index n (k+m) j) then 1 else 0) / (sqrt(2)^m))"
    by simp
  have "\<And>t. t \<le> n-m-1 \<Longrightarrow> qft_single_qbit n m t (qft_no_swap n m v) = Matrix.vec (2^n) (\<lambda>j. 
        (\<Prod>k<m. if select_index n k j then root (2^(n-k))^(\<Sum>l<(n-k). (2^(n-k-l)) * (if select_index n (l+k) j then 1 else 0)) else 1) * 
        (if select_index n m j then (root (2^(n-k)))^(\<Sum>l<t+1. (2^(n-m-l)) * (if select_index n (l+m) j then 1 else 0)) else 1) *
        (\<Prod>k<n-(Suc m). if (select_index n (k+(Suc m)) i = select_index n (k+(Suc m)) j) then 1 else 0) / (sqrt(2)^(Suc m)))"
  proof-
    fix t
    show "t \<le> n-m-1 \<Longrightarrow> qft_single_qbit n m t (qft_no_swap n m v) = Matrix.vec (2^n) (\<lambda>j. 
          (\<Prod>k<m. if select_index n k j then root (2^(n-k))^(\<Sum>l<(n-k). (2^(n-k-l)) * (if select_index n (l+k) j then 1 else 0)) else 1) * 
          (if select_index n m j then (root (2^(n-k)))^(\<Sum>l<t+1. (2^(n-m-l)) * (if select_index n (l+m) j then 1 else 0)) else 1) *
          (\<Prod>k<n-(Suc m). if (select_index n (k+(Suc m)) i = select_index n (k+(Suc m)) j) then 1 else 0) / (sqrt(2)^(Suc m)))"
    proof (induction t)
      case 0
      then show ?case
        using c1 qft_single_qbit_def
        apply auto
        sorry
    next
      case (Suc t)
      then show ?case
        using c1 qft_single_qbit_def
        apply auto
        sorry
    qed
  qed
  moreover have "n-(Suc m)+1 = n-m" using c0 by auto
  ultimately have "qft_no_swap n (Suc m) v = Matrix.vec (2^n) (\<lambda>j. 
             (\<Prod>k<m. if select_index n k j then root (2^(n-k))^(\<Sum>l<(n-k). (2^(n-k-l)) * (if select_index n (l+k) j then 1 else 0)) else 1) * 
             (if select_index n m j then (root (2^(n-k)))^(\<Sum>l<n-m. (2^(n-m-l)) * (if select_index n (l+m) j then 1 else 0)) else 1) *
             (\<Prod>k<n-(Suc m). if (select_index n (k+(Suc m)) i = select_index n (k+(Suc m)) j) then 1 else 0) / (sqrt(2)^(Suc m)))"
    using qft_no_swap_def
    by auto
  then show "qft_no_swap n (Suc m) v = Matrix.vec (2^n) (\<lambda>j. (\<Prod>k<(Suc m). if select_index n k j then 
        root (2^(n-k))^(\<Sum>l<(n-k). (2^(n-k-l)) * (if select_index n (l+k) j then 1 else 0)) else 1) * 
        (\<Prod>k<n-(Suc m). if (select_index n (k+(Suc m)) i = select_index n (k+(Suc m)) j) then 1 else 0) / (sqrt(2)^(Suc m)))"
    using adding_term_to_prod[of "\<lambda>k. if select_index n k j then root (2^(n-k))^(\<Sum>l<(n-k). (2^(n-k-l)) * (if select_index n (l+k) j then 1 else 0)) else 1" "m"]
    apply auto (* I don't know why auto can't automatically prove this; the goal is already reduced to a proposition of form X = X. *)
    sorry
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