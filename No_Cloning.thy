(* author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk *)

theory No_Cloning
imports
  Quantum
  Tensor
begin

section \<open>The Cauchy-Schwarz Inequality\<close>

lemma inner_prod_expand:
  assumes "dim_vec a = dim_vec b" and "dim_vec a = dim_vec c" and "dim_vec a = dim_vec d"
  shows "\<langle>a + b|c + d\<rangle> = \<langle>a|c\<rangle> + \<langle>a|d\<rangle> + \<langle>b|c\<rangle> + \<langle>b|d\<rangle>"
  using assms
  apply (simp add: inner_prod_def)
  by (smt add.assoc comm_semiring_class.distrib linordered_field_class.sign_simps(17) mult_hom.hom_add 
ring_class.ring_distribs(1) ring_class.ring_distribs(2) sum.cong sum.distrib)

lemma inner_prod_distr1:
  assumes "dim_vec a = dim_vec b"
  shows "\<langle>c \<cdot>\<^sub>v a|b\<rangle> = cnj(c) * \<langle>a|b\<rangle>"
  using assms inner_prod_def
  by (simp add: algebra_simps mult_hom.hom_sum)

lemma inner_prod_distr2:
  assumes "dim_vec a = dim_vec b"
  shows "\<langle>a|c \<cdot>\<^sub>v b\<rangle> = c * \<langle>a|b\<rangle>"
  using assms
  by (simp add: algebra_simps mult_hom.hom_sum)

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
  case c1:False
  then have c2:"Re(\<langle>v|v\<rangle>) > 0"
    using inner_prod_with_itself_Re_non0 inner_prod_with_itself_eq0
    by blast
  have f0:"Re(\<langle>w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle>) \<ge> 0"
    using inner_prod_with_itself_Re
    by blast
  have "dim_vec w = dim_vec (- \<langle>v|w\<rangle> / \<langle>v|v\<rangle> \<cdot>\<^sub>v v)" using assms by simp
  then have f1:"\<langle>w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> = \<langle>w|w\<rangle> + \<langle>w|-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> + \<langle>-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|w\<rangle> + 
\<langle>-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle>"
    using inner_prod_expand[of "w" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v" "w" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v"]
    by blast
  have f2:"\<langle>w|-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> = -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> * \<langle>w|v\<rangle>"
    using inner_prod_distr2[of "w" "v" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>"] assms
    by simp
  have f3:"\<langle>-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|w\<rangle> = cnj(-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>) * \<langle>v|w\<rangle>"
    using inner_prod_distr1[of "v" "w" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>"] assms
    by simp
  have f4:"\<langle>-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> = cnj(-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>) * (-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>) * \<langle>v|v\<rangle>"
    using inner_prod_distr1[of "v" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>"] inner_prod_distr2[of "v" "v" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>"]
    by simp
  have f5:"\<langle>w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> = \<langle>w|w\<rangle> -  cmod(\<langle>v|w\<rangle>)^2 / \<langle>v|v\<rangle>"
    using f1 f2 f3 f4 inner_prod_cnj[of "w" "v"] inner_prod_cnj[of "v" "v"] assms complex_norm_square
    by simp
  then have "Re(\<langle>w|w\<rangle>) \<ge> cmod(\<langle>v|w\<rangle>)^2/Re(\<langle>v|v\<rangle>)"
    using f0 inner_prod_with_itself_real
    by simp
  then have "Re(\<langle>w|w\<rangle>) * Re(\<langle>v|v\<rangle>) \<ge> cmod(\<langle>v|w\<rangle>)^2/Re(\<langle>v|v\<rangle>) * Re(\<langle>v|v\<rangle>)"
    using c2 real_mult_le_cancel_iff1
    by blast
  then show ?thesis
    using inner_prod_with_itself_Im c2
    by (simp add: mult.commute)
qed

lemma Cauchy_Schwarz_ineq_is_eq [simp]:
  assumes "v = (l \<cdot>\<^sub>v w)"
  shows "(cmod(\<langle>v|w\<rangle>))\<^sup>2 = Re (\<langle>v|v\<rangle> * \<langle>w|w\<rangle>)"
proof-
  have "cmod(\<langle>v|w\<rangle>) = cmod(cnj(l) * \<langle>w|w\<rangle>)"
    using assms inner_prod_distr1[of "w" "w" "l"]
    by simp
  then have f1:"cmod(\<langle>v|w\<rangle>)^2 = cmod(l)^2 * \<langle>w|w\<rangle> * \<langle>w|w\<rangle>"
    using complex_norm_square inner_prod_cnj[of "w" "w"]
    by simp
  have f2:"\<langle>v|v\<rangle> = cmod(l)^2 * \<langle>w|w\<rangle>"
    using assms complex_norm_square inner_prod_distr1[of "w" "v" "l"] inner_prod_distr2[of "w" "w" "l"]
    by simp
  show ?thesis
    using f1 f2
    by (metis Re_complex_of_real)
qed

lemma Cauchy_Schwarz_col [simp]:
  assumes "dim_vec v = dim_vec w" and "(cmod(\<langle>v|w\<rangle>))\<^sup>2 = Re (\<langle>v|v\<rangle> * \<langle>w|w\<rangle>)"
  shows "\<exists>l. v = (l \<cdot>\<^sub>v w) \<or> w = (l \<cdot>\<^sub>v v)"
proof (cases "\<langle>v|v\<rangle> = 0")
  case c0:True
  then have "\<And>i. i < dim_vec v \<Longrightarrow> v $ i = 0"
    by (metis index_zero_vec(1) inner_prod_with_itself_nonneg_reals_non0)
  then have "v = 0 \<cdot>\<^sub>v w"
    using assms
    by auto
  then show ?thesis
    by auto
next
  case c1:False
  then have c2:"Re(\<langle>v|v\<rangle>) > 0"
    using inner_prod_with_itself_Re_non0 inner_prod_with_itself_eq0
    by blast
  have f0:"dim_vec w = dim_vec (- \<langle>v|w\<rangle> / \<langle>v|v\<rangle> \<cdot>\<^sub>v v)" using assms by simp
  then have f1:"\<langle>w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> = \<langle>w|w\<rangle> + \<langle>w|-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> + \<langle>-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|w\<rangle> + 
\<langle>-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle>"
    using inner_prod_expand[of "w" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v" "w" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v"]
    by blast
  have f2:"\<langle>w|-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> = -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> * \<langle>w|v\<rangle>"
    using inner_prod_distr2[of "w" "v" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>"] assms
    by simp
  have f3:"\<langle>-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|w\<rangle> = cnj(-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>) * \<langle>v|w\<rangle>"
    using inner_prod_distr1[of "v" "w" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>"] assms
    by simp
  have f4:"\<langle>-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> = cnj(-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>) * (-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>) * \<langle>v|v\<rangle>"
    using inner_prod_distr1[of "v" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>"] inner_prod_distr2[of "v" "v" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>"]
    by simp
  have f5:"\<langle>w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> = \<langle>w|w\<rangle> -  cmod(\<langle>v|w\<rangle>)^2 / \<langle>v|v\<rangle>"
    using f1 f2 f3 f4 inner_prod_cnj[of "w" "v"] inner_prod_cnj[of "v" "v"] assms(1) complex_norm_square
    by simp
  have "\<langle>w|w\<rangle> = cmod(\<langle>v|w\<rangle>)^2 / \<langle>v|v\<rangle>"
    using assms inner_prod_with_itself_real
    by (metis Reals_mult c1 nonzero_mult_div_cancel_left of_real_Re)
  then have "\<langle>w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> = 0"
    using f5
    by simp
  then have "\<And>i. i<dim_vec w \<Longrightarrow> (w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v) $ i = 0"
    by (metis f0 index_add_vec(2) index_zero_vec(1) inner_prod_with_itself_nonneg_reals_non0)
  then have "\<And>i. i<dim_vec w \<Longrightarrow> w $ i + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> * v $ i = 0"
    by (metis assms(1) f0 index_add_vec(1) index_smult_vec(1))
  then have "\<And>i. i<dim_vec w \<Longrightarrow> w $ i = \<langle>v|w\<rangle>/\<langle>v|v\<rangle> * v $ i"
    by simp
  then have "w = \<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v"
    using assms(1)
    by auto
  then show ?thesis
    by blast
qed

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