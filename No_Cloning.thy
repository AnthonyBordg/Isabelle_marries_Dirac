(* author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk *)

theory No_Cloning
imports
  Quantum
  Tensor
begin

section \<open>The Cauchy-Schwarz Inequality\<close>

lemma Cauchy_Schwarz_ineq:
  assumes "dim_vec v = dim_vec w"
  shows "(cmod(\<langle>v|w\<rangle>))\<^sup>2 \<le> Re (\<langle>v|v\<rangle> * \<langle>w|w\<rangle>)" 
proof (cases "\<langle>v|v\<rangle> = 0")
  case c0:True
  then have "\<And>i. i < dim_vec v \<Longrightarrow> v $ i = 0"
    by (metis index_zero_vec(1) inner_prod_with_itself_nonneg_reals_non0)
  then have a1:"(cmod(\<langle>v|w\<rangle>))\<^sup>2 = 0"
    using assms inner_prod_def by simp
  moreover have a2:"Re (\<langle>v|v\<rangle> * \<langle>w|w\<rangle>) = 0"
    using c0 by simp
  then show ?thesis
    using a1 a2 by simp
next
  case False
  have "(\<Sum>i<dim_vec w. cmod(w $ i - (\<langle>v|w\<rangle>/\<langle>v|v\<rangle>) * v $ i)^2) \<ge> 0"
    by (simp add: sum_nonneg)
  have "cmod(w $ i - \<langle>v|w\<rangle>/\<langle>v|v\<rangle> * v $ i)^2 = cnj(w $ i - \<langle>v|w\<rangle>/\<langle>v|v\<rangle> * v $ i) * (w $ i - \<langle>v|w\<rangle>/\<langle>v|v\<rangle> * v $ i)"
    using complex_norm_square by simp
  then have "(cmod(w $ i - \<langle>v|w\<rangle>/\<langle>v|v\<rangle> * v $ i))^2 = cmod(w $ i)^2 - cnj(w $ i) * \<langle>v|w\<rangle>/\<langle>v|v\<rangle> * v $ i - 
w $ i * cnj(\<langle>v|w\<rangle>/\<langle>v|v\<rangle> * v $ i) + cmod(\<langle>v|w\<rangle>/\<langle>v|v\<rangle> * v $ i)^2"
    using complex_norm_square by (simp add: algebra_simps)
  then have "(\<Sum>i<dim_vec w. cmod(w $ i - (\<langle>v|w\<rangle>/\<langle>v|v\<rangle>) * v $ i)^2) = (\<Sum>i<dim_vec w. cmod(w $ i)^2 - 
cnj(w $ i) * \<langle>v|w\<rangle>/\<langle>v|v\<rangle> * v $ i -  w $ i * cnj(\<langle>v|w\<rangle>/\<langle>v|v\<rangle> * v $ i) + cmod(\<langle>v|w\<rangle>/\<langle>v|v\<rangle> * v $ i)^2)"
    using sum.cong assms complex_of_real_def
  then show ?thesis sorry
qed

lemma Cauchy_Schwarz_ineq_is_eq [simp]:
  assumes "v = (l \<cdot>\<^sub>v w)"
  shows "(cmod(\<langle>v|w\<rangle>))\<^sup>2 = Re (\<langle>v|v\<rangle> * \<langle>w|w\<rangle>)" 
  using assms
  apply(simp add: inner_prod_def)
  sorry

lemma Cauchy_Schwarz_col [simp]:
  assumes "dim_vec v = dim_vec w" and "(cmod(\<langle>v|w\<rangle>))\<^sup>2 = Re (\<langle>v|v\<rangle> * \<langle>w|w\<rangle>)"
  shows "v = (l \<cdot>\<^sub>v w)" sorry

section \<open>The No-Cloning Theorem\<close>

lemma inner_prod_is_eq [simp]:
  assumes "dim_vec v = dim_vec w" and "\<langle>v|w\<rangle> = 1"
  shows "v = w" sorry

locale quantum_machine =
  fixes n:: nat and s::"complex Matrix.vec" and U:: "complex Matrix.mat"
  assumes dim_vec [simp]: "dim_vec s = 2^n"
    and dim_col [simp]: "dim_col U = 2^n * 2^n"
    and square [simp]: "square_mat U" and unitary [simp]: "unitary U"

theorem (in quantum_machine) no_cloning:
  assumes [simp]: "dim_vec v = 2^n" and [simp]: "dim_vec w = 2^n" and 
    cloning1 [simp]: "U * ( |v\<rangle> \<Otimes> |s\<rangle>) = |v\<rangle> \<Otimes> |v\<rangle>" and
    cloning2 [simp]: "U * ( |w\<rangle> \<Otimes> |s\<rangle>) = |w\<rangle> \<Otimes> |w\<rangle>"
  shows "v = w \<or> \<langle>v|w\<rangle> = 0" sorry