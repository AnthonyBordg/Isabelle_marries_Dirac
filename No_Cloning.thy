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
  assumes "dim_vec v = dim_vec w" and "\<langle>v|w\<rangle> = 1" and "\<langle>v|v\<rangle> = 1" and "\<langle>w|w\<rangle> = 1"
  shows "v = w"
proof-
  have "(cmod(\<langle>v|w\<rangle>))\<^sup>2 = Re (\<langle>v|v\<rangle> * \<langle>w|w\<rangle>)"
    using assms
    by simp
  then have f1:"\<exists>l. v = (l \<cdot>\<^sub>v w) \<or> w = (l \<cdot>\<^sub>v v)"
    using assms
    by simp
  show ?thesis
  proof (cases "\<exists>l. v = (l \<cdot>\<^sub>v w)")
    case True
    then have "\<exists>l. v = (l \<cdot>\<^sub>v w) \<and> \<langle>v|w\<rangle> = cnj(l) * \<langle>w|w\<rangle>"
      using inner_prod_distr1
      by auto
    then show ?thesis
      using assms
      by simp
  next
    case False
    then have "\<exists>l. w = (l \<cdot>\<^sub>v v) \<and> \<langle>v|w\<rangle> = l * \<langle>v|v\<rangle>"
      using f1 inner_prod_distr2
      by auto
    then show ?thesis
      using assms
      by simp
  qed
qed

lemma tensor_conj:
  shows "(A \<Otimes> B)\<^sup>\<dagger>  = (A\<^sup>\<dagger>) \<Otimes> (B\<^sup>\<dagger>)"
proof
  show c1:"dim_row ((A \<Otimes> B)\<^sup>\<dagger>) = dim_row ((A\<^sup>\<dagger>) \<Otimes> (B\<^sup>\<dagger>))"
    by auto
  show c2:"dim_col ((A \<Otimes> B)\<^sup>\<dagger>) = dim_col ((A\<^sup>\<dagger>) \<Otimes> (B\<^sup>\<dagger>))"
    by auto
  show "\<And>i j. i < dim_row ((A\<^sup>\<dagger>) \<Otimes> (B\<^sup>\<dagger>)) \<Longrightarrow> j < dim_col ((A\<^sup>\<dagger>) \<Otimes> (B\<^sup>\<dagger>)) \<Longrightarrow> 
((A \<Otimes> B)\<^sup>\<dagger>) $$ (i, j) = ((A\<^sup>\<dagger>) \<Otimes> (B\<^sup>\<dagger>)) $$ (i, j)"
  proof-
    fix i j assume a1:"i < dim_row ((A\<^sup>\<dagger>) \<Otimes> (B\<^sup>\<dagger>))" and a2:"j < dim_col ((A\<^sup>\<dagger>) \<Otimes> (B\<^sup>\<dagger>))"
    have "(A \<Otimes> B)\<^sup>\<dagger> $$ (i, j) = cnj((A \<Otimes> B) $$ (j, i))"
      using c1 c2 a1 a2 hermite_cnj_def
      by auto
    then have f1:"(A \<Otimes> B)\<^sup>\<dagger> $$ (i, j) = cnj(A $$ (j div dim_row(B), i div dim_col(B)) * B $$ (j mod dim_row(B), i mod dim_col(B)))"
      by (metis (mono_tags, lifting) a1 a2 c2 dim_row_tensor_mat hermite_cnj_dim_col hermite_cnj_dim_row 
index_tensor_mat less_nat_zero_code mult_not_zero neq0_conv)
    have f2:"((A\<^sup>\<dagger>) \<Otimes> (B\<^sup>\<dagger>)) $$ (i, j) = (A\<^sup>\<dagger>) $$ (i div dim_col(B), j div dim_row(B)) * (B\<^sup>\<dagger>) $$ (i mod dim_col(B), j mod dim_row(B))"
      by (smt a1 a2 c2 dim_row_tensor_mat hermite_cnj_dim_col hermite_cnj_dim_row index_tensor_mat 
less_nat_zero_code mult_eq_0_iff neq0_conv)
    have f3:"i mod dim_col(B) < dim_col(B)"
      using a1 gr_implies_not_zero mod_div_trivial
      by fastforce
    have f4:"j mod dim_row(B) < dim_row(B)"
      using a2 gr_implies_not_zero mod_div_trivial
      by fastforce
    have f5:"(B\<^sup>\<dagger>) $$ (i mod dim_col(B), j mod dim_row(B)) = cnj(B $$ (j mod dim_row(B), i mod dim_col(B)))"
      using hermite_cnj_def f3 f4
      by auto
    have f6:"i div dim_col(B) < dim_col(A)"
      using a1 c1 hermite_cnj_def
      by (simp add: less_mult_imp_div_less)
    have f7:"j div dim_row(B) < dim_row(A)"
      using a2 c2 hermite_cnj_def
      by (simp add: less_mult_imp_div_less)
    have f8:"(A\<^sup>\<dagger>) $$ (i div dim_col(B), j div dim_row(B)) = cnj(A $$ (j div dim_row(B), i div dim_col(B)))"
      using hermite_cnj_def f6 f7
      by auto
    show "((A \<Otimes> B)\<^sup>\<dagger>) $$ (i, j) = ((A\<^sup>\<dagger>) \<Otimes> (B\<^sup>\<dagger>)) $$ (i, j)"
      using f1 f2 f5 f8
      by simp
  qed
qed

lemma hermite_prod:
  assumes "dim_col A = dim_row B"
  shows "(A * B)\<^sup>\<dagger>  = (B\<^sup>\<dagger>) * (A\<^sup>\<dagger>)"
  using assms
  by (metis carrier_mat_triv cpx_mat_cnj_cnj cpx_mat_cnj_prod hermite_cnj_dim_col hermite_cnj_dim_row transpose_cnj transpose_mult)

locale quantum_machine =
  fixes n:: nat and s::"complex Matrix.vec" and U:: "complex Matrix.mat"
  assumes dim_vec [simp]: "dim_vec s = 2^n"
    and dim_col [simp]: "dim_col U = 2^n * 2^n"
    and square [simp]: "square_mat U" and unitary [simp]: "unitary U"

theorem (in quantum_machine) no_cloning:
  assumes [simp]: "dim_vec v = 2^n" and [simp]: "dim_vec w = 2^n" and 
    cloning1: "U * ( |v\<rangle> \<Otimes> |s\<rangle>) = |v\<rangle> \<Otimes> |v\<rangle>" and
    cloning2: "U * ( |w\<rangle> \<Otimes> |s\<rangle>) = |w\<rangle> \<Otimes> |w\<rangle>" and 
    "\<langle>v|v\<rangle> = 1" and "\<langle>w|w\<rangle> = 1"
  shows "v = w \<or> \<langle>v|w\<rangle> = 0"
proof-
  have f1:"\<langle>|v\<rangle>| \<Otimes> \<langle>|s\<rangle>| = (( |v\<rangle> \<Otimes> |s\<rangle>)\<^sup>\<dagger>)"
    using tensor_conj[of "|v\<rangle>" "|s\<rangle>"] bra_def hermite_cnj_def ket_vec_def
    by simp
  have f2:"\<langle>|v\<rangle>| \<Otimes> \<langle>|v\<rangle>| = (( |v\<rangle> \<Otimes> |v\<rangle>)\<^sup>\<dagger>)"
    using tensor_conj[of "|v\<rangle>" "|v\<rangle>"] bra_def hermite_cnj_def ket_vec_def
    by simp
  have "(U * ( |v\<rangle> \<Otimes> |s\<rangle>))\<^sup>\<dagger> = (\<langle>|v\<rangle>| \<Otimes> \<langle>|s\<rangle>| ) * (U\<^sup>\<dagger>)"
    using hermite_prod[of "U" "|v\<rangle> \<Otimes> |s\<rangle>"] assms f1
    by (simp add: ket_vec_def)
  then have f3:"(U * ( |v\<rangle> \<Otimes> |s\<rangle>))\<^sup>\<dagger> * U * ( |w\<rangle> \<Otimes> |s\<rangle>) = (\<langle>|v\<rangle>| \<Otimes> \<langle>|s\<rangle>| ) * (U\<^sup>\<dagger>) * U * ( |w\<rangle> \<Otimes> |s\<rangle>)"
    by auto
  have f4:"(U * ( |v\<rangle> \<Otimes> |s\<rangle>))\<^sup>\<dagger> * U * ( |w\<rangle> \<Otimes> |s\<rangle>) = (( |v\<rangle> \<Otimes> |v\<rangle>)\<^sup>\<dagger>) * ( |w\<rangle> \<Otimes> |w\<rangle>)"
    using assms
    by (smt assoc_mult_mat carrier_mat_triv dim_row_mat(1) dim_row_tensor_mat hermite_cnj_dim_col 
index_mult_mat(2) ket_vec_def local.dim_vec square square_mat.elims(2))
  have f5:"(U\<^sup>\<dagger>) * U = 1\<^sub>m (2^n * 2^n)"
    using unitary_def dim_col unitary
    by auto
  have f6:"(\<langle>|v\<rangle>| \<Otimes> \<langle>|s\<rangle>| ) * (U\<^sup>\<dagger>) * U = (\<langle>|v\<rangle>| \<Otimes> \<langle>|s\<rangle>| ) * ((U\<^sup>\<dagger>) * U)"
    by (smt assms(1) assoc_mult_mat carrier_mat_triv dim_row_mat(1) dim_row_tensor_mat f1 
hermite_cnj_dim_col hermite_cnj_dim_row ket_vec_def local.dim_col local.dim_vec)
  have f7:"(\<langle>|v\<rangle>| \<Otimes> \<langle>|s\<rangle>| ) * 1\<^sub>m (2^n * 2^n) = (\<langle>|v\<rangle>| \<Otimes> \<langle>|s\<rangle>| )"
    using f1 ket_vec_def by auto
  have "( |v\<rangle> \<Otimes> |v\<rangle>)\<^sup>\<dagger> * ( |w\<rangle> \<Otimes> |w\<rangle>) = (\<langle>|v\<rangle>| \<Otimes> \<langle>|s\<rangle>| ) * ( |w\<rangle> \<Otimes> |s\<rangle>)"
    using f3 f4 f5 f6 f7
    by auto
  then have f8:"(\<langle>|v\<rangle>| * |w\<rangle>) \<Otimes> (\<langle>|v\<rangle>| * |w\<rangle>) = (\<langle>|v\<rangle>| * |w\<rangle>) \<Otimes> (\<langle>|s\<rangle>| * |s\<rangle>)"
    using f2
    by (simp add: bra_def mult_distr_tensor ket_vec_def)
  have f9:"((\<langle>|v\<rangle>| * |w\<rangle>) \<Otimes> (\<langle>|v\<rangle>| * |w\<rangle>)) $$ (0,0) = \<langle>v|w\<rangle> * \<langle>v|w\<rangle>"
    using assms inner_prod_with_times_mat[of "v" "w"]
    by (auto simp add: bra_def ket_vec_def)
  have f10:"((\<langle>|v\<rangle>| * |w\<rangle>) \<Otimes> (\<langle>|s\<rangle>| * |s\<rangle>)) $$ (0,0) = \<langle>v|w\<rangle> * \<langle>s|s\<rangle>"
    using assms inner_prod_with_times_mat[of "v" "w"] inner_prod_with_times_mat[of "s" "s"]
    by (auto simp add: bra_def ket_vec_def)
  have "\<langle>v|w\<rangle> * \<langle>v|w\<rangle> = \<langle>v|w\<rangle> * \<langle>s|s\<rangle>"
    using f8 f9 f10
    by simp
  then have "\<langle>v|w\<rangle> = 0 \<or> \<langle>v|w\<rangle> = \<langle>s|s\<rangle>"
    using mult_left_cancel by blast
  show ?thesis
    sorry
qed