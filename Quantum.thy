(*
Authors: 

  Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk
  Yijun He, University of Cambridge, yh403@cam.ac.uk
*)

theory Quantum
imports
  Jordan_Normal_Form.Matrix
  "HOL-Library.Nonpos_Ints"
  Basics
begin

section \<open>Qubits and Quantum Gates\<close>

subsection \<open>Qubits\<close>

text\<open>In this theory @{text cpx} stands for @{text complex}.\<close>

definition cpx_vec_length :: "complex vec \<Rightarrow> real" ("\<parallel>_\<parallel>") where
"cpx_vec_length v \<equiv> sqrt(\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2)"

lemma cpx_length_of_vec_of_list [simp]:
  "\<parallel>vec_of_list l\<parallel> = sqrt(\<Sum>i<length l. (cmod (l ! i))\<^sup>2)"
  apply (auto simp: cpx_vec_length_def vec_of_list_def vec_of_list_index)
  by (metis (no_types, lifting) dim_vec_of_list sum.cong vec_of_list.abs_eq vec_of_list_index)

lemma norm_vec_index_unit_vec_is_0 [simp]:
  assumes "j < n" and "j \<noteq> i"
  shows "cmod ((unit_vec n i) $ j) = 0"
  using assms by (simp add: unit_vec_def)

lemma norm_vec_index_unit_vec_is_1 [simp]:
  assumes "j < n" and "j = i"
  shows "cmod ((unit_vec n i) $ j) = 1"
proof -
  have f:"(unit_vec n i) $ j = 1"
    using assms by simp
  thus ?thesis
    by (simp add: f cmod_def) 
qed

lemma unit_cpx_vec_length [simp]:
  assumes "i < n"
  shows "\<parallel>unit_vec n i\<parallel> = 1"
proof -
  have "(\<Sum>j<n. (cmod((unit_vec n i) $ j))\<^sup>2) = (\<Sum>j<n. if j = i then 1 else 0)"
    using norm_vec_index_unit_vec_is_0 norm_vec_index_unit_vec_is_1
    by (smt lessThan_iff one_power2 sum.cong zero_power2) 
  also have "\<dots> = 1"
    using assms by simp
  finally have "sqrt (\<Sum>j<n. (cmod((unit_vec n i) $ j))\<^sup>2) = 1" 
    by simp
  thus ?thesis
    using cpx_vec_length_def by simp
qed

locale state =
  fixes n:: nat and v:: "complex mat"
  assumes dim_col [simp]: "dim_col v = 1"
    and dim_row [simp]: "dim_row v = 2^n"
    and length [simp]: "\<parallel>col v 0\<parallel> = 1"

text\<open> 
Below the natural number n codes for the dimension of the complex vector space whose elements of norm
1 we call states. 
\<close>

lemma unit_vec_of_right_length_is_state [simp]:
  assumes "i < 2^n"
  shows "unit_vec (2^n) i \<in> {v| n v::complex vec. dim_vec v = 2^n \<and> \<parallel>v\<parallel> = 1}"
proof-
  have "dim_vec (unit_vec (2^n) i) = 2^n" 
    by simp
  moreover have "\<parallel>unit_vec (2^n) i\<parallel> = 1"
    using assms by simp
  ultimately show ?thesis 
    by simp
qed

definition state_qbit :: "nat \<Rightarrow> complex vec set" where
"state_qbit n \<equiv> {v| v:: complex vec. dim_vec v = 2^n \<and> \<parallel>v\<parallel> = 1}"

lemma state_to_state_qbit [simp]:
  assumes "state n v"
  shows "col v 0 \<in> state_qbit n"
  using assms state_def state_qbit_def by simp

subsection "The Hermitian Conjugation"

text \<open>The Hermitian conjugate of a complex matrix is the complex conjugate of its transpose. \<close>

definition hermite_cnj :: "complex mat \<Rightarrow> complex mat" ("_\<^sup>\<dagger>") where
  "hermite_cnj M \<equiv> mat (dim_col M) (dim_row M) (\<lambda> (i,j). cnj(M $$ (j,i)))"

text \<open>We introduce the type of complex square matrices.\<close>

typedef cpx_sqr_mat = "{M | M::complex mat. square_mat M}"
proof-
  have "square_mat (1\<^sub>m n)" for n
    using one_mat_def by simp
  thus ?thesis by blast
qed

definition cpx_sqr_mat_to_cpx_mat :: "cpx_sqr_mat => complex mat" where
"cpx_sqr_mat_to_cpx_mat M \<equiv> Rep_cpx_sqr_mat M"

text \<open>
We introduce a coercion from the type of complex square matrices to the type of complex 
matrices.
\<close>

declare [[coercion cpx_sqr_mat_to_cpx_mat]]

lemma hermite_cnj_dim_row [simp]:
  "dim_row (M\<^sup>\<dagger>) = dim_col M"
  using hermite_cnj_def by simp

lemma hermite_cnj_dim_col [simp]:
  "dim_col (M\<^sup>\<dagger>) = dim_row M"
  using hermite_cnj_def by simp

lemma col_hermite_cnj [simp]:
  assumes "j < dim_row M"
  shows "col (M\<^sup>\<dagger>) j = vec (dim_col M) (\<lambda>i. cnj (M $$ (j,i)))"
  using assms col_def hermite_cnj_def by simp

lemma row_hermite_cnj [simp]:
  assumes "i < dim_col M"
  shows "row (M\<^sup>\<dagger>) i = vec (dim_row M) (\<lambda>j. cnj (M $$ (j,i)))"
  using assms row_def hermite_cnj_def by simp

lemma hermite_cnj_of_sqr_is_sqr [simp]:
  "square_mat ((M::cpx_sqr_mat)\<^sup>\<dagger>)"
proof-
  have "square_mat M"
    using cpx_sqr_mat_to_cpx_mat_def Rep_cpx_sqr_mat by simp
  then have "dim_row M = dim_col M" by simp
  then have "dim_col (M\<^sup>\<dagger>) = dim_row (M\<^sup>\<dagger>)" by simp
  thus "square_mat (M\<^sup>\<dagger>)" by simp
qed

lemma hermite_cnj_of_id_is_id [simp]:
  "(1\<^sub>m n)\<^sup>\<dagger> = 1\<^sub>m n"
  using hermite_cnj_def one_mat_def by auto

subsection "Unitary Matrices and Quantum Gates"

definition unitary :: "complex mat \<Rightarrow> bool" where
"unitary M \<equiv> (M\<^sup>\<dagger>) * M = 1\<^sub>m (dim_col M) \<and> M * (M\<^sup>\<dagger>) = 1\<^sub>m (dim_row M)"

lemma id_is_unitary [simp]:
  "unitary (1\<^sub>m n)"
  by (simp add: unitary_def)

locale gate =
  fixes n:: nat and A :: "complex mat"
  assumes dim_row [simp]: "dim_row A = 2^n"
    and square_mat [simp]: "square_mat A"
    and unitary [simp]: "unitary A"

text \<open>
We prove that a quantum gate is invertible and its inverse is given by its Hermitian conjugate.
\<close>

lemma mat_unitary_mat [intro]:
  assumes "unitary M"
  shows "inverts_mat M (M\<^sup>\<dagger>)"
  using assms by (simp add: unitary_def inverts_mat_def)

lemma unitary_mat_mat [intro]:
  assumes "unitary M"
  shows "inverts_mat (M\<^sup>\<dagger>) M"
  using assms by (simp add: unitary_def inverts_mat_def)

lemma (in gate) gate_is_inv:
  "invertible_mat A"
  using square_mat unitary invertible_mat_def by blast

subsection "Relations Between Complex Conjugation, Hermitian Conjugation, Transposition and Unitarity"

notation transpose_mat ("(_\<^sup>t)")

lemma col_tranpose [simp]:
  assumes "dim_row M = n" and "i < n"
  shows "col (M\<^sup>t) i = row M i"
proof
  show "dim_vec (col (M\<^sup>t) i) = dim_vec (row M i)"
    by (simp add: row_def col_def transpose_mat_def)
next
  show "\<And>j. j < dim_vec (row M i) \<Longrightarrow> col M\<^sup>t i $ j = row M i $ j"
    using assms by (simp add: transpose_mat_def)
qed

lemma row_transpose [simp]:
  assumes "dim_col M = n" and "i < n"
  shows "row (M\<^sup>t) i = col M i"
  using assms by simp

definition cpx_mat_cnj :: "complex mat \<Rightarrow> complex mat" ("(_\<^sup>\<star>)") where
"cpx_mat_cnj M \<equiv> mat (dim_row M) (dim_col M) (\<lambda>(i,j). cnj (M $$ (i,j)))"

lemma cpx_mat_cnj_id [simp]:
  "(1\<^sub>m n)\<^sup>\<star> = 1\<^sub>m n" 
  by (auto simp: cpx_mat_cnj_def)

lemma cpx_mat_cnj_cnj [simp]:
  "(M\<^sup>\<star>)\<^sup>\<star> = M"
  by (auto simp: cpx_mat_cnj_def)

lemma dim_row_of_cjn_prod [simp]: 
  "dim_row ((M\<^sup>\<star>) * (N\<^sup>\<star>)) = dim_row M"
  by (simp add: cpx_mat_cnj_def)

lemma dim_col_of_cjn_prod [simp]: 
  "dim_col ((M\<^sup>\<star>) * (N\<^sup>\<star>)) = dim_col N"
  by (simp add: cpx_mat_cnj_def)

lemma cpx_mat_cnj_prod:
  assumes "dim_col M = dim_row N"
  shows "(M * N)\<^sup>\<star> = (M\<^sup>\<star>) * (N\<^sup>\<star>)"
proof
  show "dim_row (M * N)\<^sup>\<star> = dim_row ((M\<^sup>\<star>) * (N\<^sup>\<star>))" 
    by (simp add: cpx_mat_cnj_def)
next
  show "dim_col ((M * N)\<^sup>\<star>) = dim_col ((M\<^sup>\<star>) * (N\<^sup>\<star>))" 
    by (simp add: cpx_mat_cnj_def)
next 
  fix i j::nat
  assume a1:"i < dim_row ((M\<^sup>\<star>) * (N\<^sup>\<star>))" and a2:"j < dim_col ((M\<^sup>\<star>) * (N\<^sup>\<star>))"
  then have "(M * N)\<^sup>\<star> $$ (i,j) = cnj (\<Sum>k<(dim_row N). M $$ (i,k) * N $$ (k,j))"
    using assms cpx_mat_cnj_def index_mat times_mat_def scalar_prod_def row_def col_def 
dim_row_of_cjn_prod dim_col_of_cjn_prod
    by (smt case_prod_conv dim_col index_mult_mat(2) index_mult_mat(3) index_vec lessThan_atLeast0 
        lessThan_iff sum.cong)
  also have "\<dots> = (\<Sum>k<(dim_row N). cnj(M $$ (i,k)) * cnj(N $$ (k,j)))" by simp
  also have "((M\<^sup>\<star>) * (N\<^sup>\<star>)) $$ (i,j) = 
    (\<Sum>k<(dim_row N). cnj(M $$ (i,k)) * cnj(N $$ (k,j)))"
    using assms a1 a2 cpx_mat_cnj_def index_mat times_mat_def scalar_prod_def row_def col_def
    by (smt case_prod_conv dim_col dim_col_mat(1) dim_row_mat(1) index_vec lessThan_atLeast0 
        lessThan_iff sum.cong)
  finally show "(M * N)\<^sup>\<star> $$ (i, j) = ((M\<^sup>\<star>) * (N\<^sup>\<star>)) $$ (i, j)" by simp
qed

lemma transpose_cnj [simp]:
  "(M\<^sup>t)\<^sup>\<star> = (M\<^sup>\<dagger>)"
proof
  show f1:"dim_row ((M\<^sup>t)\<^sup>\<star>) = dim_row (M\<^sup>\<dagger>)"
    by (simp add: cpx_mat_cnj_def transpose_mat_def hermite_cnj_def)
next
  show f2:"dim_col ((M\<^sup>t)\<^sup>\<star>) = dim_col (M\<^sup>\<dagger>)" 
    by (simp add: cpx_mat_cnj_def transpose_mat_def hermite_cnj_def)
next
  fix i j::nat
  assume "i < dim_row M\<^sup>\<dagger>" and "j < dim_col M\<^sup>\<dagger>"
  then show "M\<^sup>t\<^sup>\<star> $$ (i, j) = M\<^sup>\<dagger> $$ (i, j)" 
    by (simp add: cpx_mat_cnj_def transpose_mat_def hermite_cnj_def)
qed

lemma cnj_transpose [simp]:
  "(M\<^sup>\<star>)\<^sup>t = (M\<^sup>\<dagger>)"
proof
  show "dim_row ((M\<^sup>\<star>)\<^sup>t) = dim_row (M\<^sup>\<dagger>)" 
    by (simp add: transpose_mat_def cpx_mat_cnj_def hermite_cnj_def)
next
  show "dim_col ((M\<^sup>\<star>)\<^sup>t) = dim_col (M\<^sup>\<dagger>)" 
    by (simp add: transpose_mat_def cpx_mat_cnj_def hermite_cnj_def)
next
  fix i j::nat
  assume "i < dim_row M\<^sup>\<dagger>" and "j < dim_col M\<^sup>\<dagger>"
  then show "M\<^sup>\<star>\<^sup>t $$ (i, j) = M\<^sup>\<dagger> $$ (i, j)" 
    by (simp add: transpose_mat_def cpx_mat_cnj_def hermite_cnj_def)
qed

lemma transpose_hermite_cnj [simp]:
  "(M\<^sup>t)\<^sup>\<dagger> = (M\<^sup>\<star>)"
  by (metis transpose_transpose transpose_cnj)

lemma left_inv_of_unitary_transpose [simp]:
  assumes "unitary U"
  shows "(U\<^sup>t)\<^sup>\<dagger> * (U\<^sup>t) =  1\<^sub>m(dim_row U)"
proof -
  have "dim_col U = dim_row ((U\<^sup>t)\<^sup>\<star>)" by simp
  then have "(U * ((U\<^sup>t)\<^sup>\<star>))\<^sup>\<star> = (U\<^sup>\<star>) * (U\<^sup>t)"
    using cpx_mat_cnj_prod cpx_mat_cnj_cnj by presburger
  also have "\<dots> = (U\<^sup>t)\<^sup>\<dagger> * (U\<^sup>t)" by simp
  finally show ?thesis 
    using assms by (metis transpose_cnj cpx_mat_cnj_id unitary_def)
qed

lemma right_inv_of_unitary_transpose [simp]:
  assumes "unitary U"
  shows "U\<^sup>t * ((U\<^sup>t)\<^sup>\<dagger>) = 1\<^sub>m(dim_col U)"
proof -
  have "dim_col ((U\<^sup>t)\<^sup>\<star>) = dim_row U" by simp
  then have "U\<^sup>t * ((U\<^sup>t)\<^sup>\<dagger>) = (((U\<^sup>t)\<^sup>\<star> * U)\<^sup>\<star>)"
    using cpx_mat_cnj_cnj cpx_mat_cnj_prod transpose_hermite_cnj by presburger
  also have "\<dots> = (U\<^sup>\<dagger> * U)\<^sup>\<star>" by simp
  finally show ?thesis
    using assms by (metis cpx_mat_cnj_id unitary_def)
qed

lemma transpose_of_unitary_is_unitary [simp]:
  assumes "unitary U"
  shows "unitary (U\<^sup>t)" 
  using unitary_def assms left_inv_of_unitary_transpose right_inv_of_unitary_transpose by simp


subsection "The Inner Product"

text \<open>We introduce a coercion between complex vectors and (column) complex matrices.\<close>

definition ket_vec :: "complex vec \<Rightarrow> complex mat" ("|_\<rangle>") where
"ket_vec v \<equiv> mat (dim_vec v) 1 (\<lambda>(i,j). v $ i)"

lemma ket_vec_col [simp]:
  "col |v\<rangle> 0 = v"
  by (auto simp: col_def ket_vec_def)

lemma smult_ket_vec [simp]:
  "|x \<cdot>\<^sub>v v\<rangle> = x \<cdot>\<^sub>m |v\<rangle>"
  by (auto simp: ket_vec_def)

declare [[coercion ket_vec]]

definition row_vec :: "complex vec \<Rightarrow> complex mat" where
"row_vec v \<equiv> mat 1 (dim_vec v) (\<lambda>(i,j). v $ j)" 

definition bra_vec :: "complex vec \<Rightarrow> complex mat" where
"bra_vec v \<equiv> (row_vec v)\<^sup>\<star>"

lemma row_bra_vec [simp]:
  "row (bra_vec v) 0 = vec (dim_vec v) (\<lambda>i. cnj(v $ i))"
  by (auto simp: row_def bra_vec_def cpx_mat_cnj_def row_vec_def)

text \<open>We introduce a definition called @{term "bra"} to see a vector as a column matrix.\<close>

definition bra :: "complex mat \<Rightarrow> complex mat" ("\<langle>_|") where
"bra v \<equiv> mat 1 (dim_row v) (\<lambda>(i,j). cnj(v $$ (j,i)))"

text \<open>The relation between @{term "bra"}, @{term "bra_vec"} and @{term "ket_vec"} is given as follows.\<close>

lemma bra_bra_vec [simp]:
  "bra (ket_vec v) = bra_vec v"
  by (auto simp: bra_def ket_vec_def bra_vec_def cpx_mat_cnj_def row_vec_def)

lemma row_bra [simp]:
  fixes v::"complex vec"
  shows "row \<langle>v| 0 = vec (dim_vec v) (\<lambda>i. cnj (v $ i))" by simp

text \<open>We introduce the inner product of two complex vectors in @{text "\<complex>\<^sup>n"}.\<close>

definition inner_prod :: "complex vec \<Rightarrow> complex vec \<Rightarrow> complex" ("\<langle>_|_\<rangle>") where
"inner_prod u v \<equiv> \<Sum> i \<in> {0..< dim_vec v}. cnj(u $ i) * (v $ i)"

lemma inner_prod_with_row_bra_vec [simp]:
  assumes "dim_vec u = dim_vec v"
  shows "\<langle>u|v\<rangle> = row (bra_vec u) 0 \<bullet> v"
  using assms inner_prod_def scalar_prod_def row_bra_vec index_vec
  by (smt lessThan_atLeast0 lessThan_iff sum.cong)

lemma inner_prod_with_row_bra_vec_col_ket_vec [simp]:
  assumes "dim_vec u = dim_vec v"
  shows "\<langle>u|v\<rangle> = (row \<langle>u| 0) \<bullet> (col |v\<rangle> 0)"
  using assms by (simp add: inner_prod_def scalar_prod_def)

lemma inner_prod_with_times_mat [simp]:
  assumes "dim_vec u = dim_vec v"
  shows "\<langle>u|v\<rangle> = (\<langle>u| * |v\<rangle>) $$ (0,0)"
  using assms inner_prod_with_row_bra_vec_col_ket_vec 
  by (simp add: inner_prod_def times_mat_def ket_vec_def bra_def)

lemma orthogonal_unit_vec [simp]:
  assumes "i < n" and "j < n" and "i \<noteq> j"
  shows "\<langle>unit_vec n i|unit_vec n j\<rangle> = 0"
proof-
  have "\<langle>unit_vec n i|unit_vec n j\<rangle> = unit_vec n i \<bullet> unit_vec n j"
    using assms unit_vec_def inner_prod_def scalar_prod_def
    by (smt complex_cnj_zero index_unit_vec(3) index_vec inner_prod_with_row_bra_vec row_bra_vec 
        scalar_prod_right_unit)
  thus ?thesis
    using assms scalar_prod_def unit_vec_def by simp 
qed

text \<open>We prove that our inner product is linear in its second argument.\<close>

lemma vec_index_is_linear [simp]:
  assumes "dim_vec u = dim_vec v" and "j < dim_vec u"
  shows "(k \<cdot>\<^sub>v u + l \<cdot>\<^sub>v v) $ j = k * (u $ j) + l * (v $ j)"
  using assms vec_index_def smult_vec_def plus_vec_def by simp

lemma inner_prod_is_linear [simp]:
  fixes u::"complex vec" and v::"nat \<Rightarrow> complex vec" and l::"nat \<Rightarrow> complex"
  assumes "\<forall>i\<in>{0, 1}. dim_vec u = dim_vec (v i)"
  shows "\<langle>u|l 0 \<cdot>\<^sub>v v 0 + l 1 \<cdot>\<^sub>v v 1\<rangle> = (\<Sum>i\<le>1. l i * \<langle>u|v i\<rangle>)"
proof -
  have f1:"dim_vec (l 0 \<cdot>\<^sub>v v 0 + l 1 \<cdot>\<^sub>v v 1) = dim_vec u"
    using assms by simp
  then have "\<langle>u|l 0 \<cdot>\<^sub>v v 0 + l 1 \<cdot>\<^sub>v v 1\<rangle> = (\<Sum>i\<in>{0 ..< dim_vec u}. cnj (u $ i) * ((l 0 \<cdot>\<^sub>v v 0 + l 1 \<cdot>\<^sub>v v 1) $ i))"
    by (simp add: inner_prod_def)
  also have "\<dots> = (\<Sum>i\<in>{0 ..< dim_vec u}. cnj (u $ i) * (l 0 * v 0 $ i + l 1 * v 1 $ i))"
    using assms by simp
  also have "\<dots> = l 0 * (\<Sum>i\<in>{0 ..< dim_vec u}. cnj(u $ i) * (v 0 $ i)) + l 1 * (\<Sum>i\<in>{0 ..< dim_vec u}. cnj(u $ i) * (v 1 $ i))"
    apply (auto simp: algebra_simps)
    by (simp add: sum.distrib sum_distrib_left)
  also have "\<dots> = l 0 * \<langle>u|v 0\<rangle> + l 1 * \<langle>u|v 1\<rangle>"
    using assms inner_prod_def by auto
  finally show ?thesis by simp
qed

lemma inner_prod_cnj:
  assumes "dim_vec u = dim_vec v"
  shows "\<langle>v|u\<rangle> = cnj (\<langle>u|v\<rangle>)"
  by (simp add: assms inner_prod_def algebra_simps)

lemma inner_prod_with_itself_Im [simp]:
  "Im (\<langle>u|u\<rangle>) = 0"
  using inner_prod_cnj by (metis Reals_cnj_iff complex_is_Real_iff)

lemma inner_prod_with_itself_real [simp]:
  "\<langle>u|u\<rangle> \<in> \<real>"
  using inner_prod_with_itself_Im by (simp add: complex_is_Real_iff)

lemma inner_prod_with_itself_eq0 [simp]:
  assumes "u = 0\<^sub>v (dim_vec u)"
  shows "\<langle>u|u\<rangle> = 0"
  using assms inner_prod_def zero_vec_def
  by (smt atLeastLessThan_iff complex_cnj_zero index_zero_vec(1) mult_zero_left sum.neutral)

lemma inner_prod_with_itself_Re:
  "Re (\<langle>u|u\<rangle>) \<ge> 0"
proof -
  have "Re (\<langle>u|u\<rangle>) = (\<Sum>i<dim_vec u. Re (cnj(u $ i) * (u $ i)))"
    by (simp add: inner_prod_def lessThan_atLeast0)
  moreover have "\<dots> = (\<Sum>i<dim_vec u. (Re (u $ i))\<^sup>2 + (Im (u $ i))\<^sup>2)"
    using complex_mult_cnj
    by (metis (no_types, lifting) Re_complex_of_real semiring_normalization_rules(7))
  ultimately show "Re (\<langle>u|u\<rangle>) \<ge> 0" by (simp add: sum_nonneg)
qed

lemma inner_prod_with_itself_nonneg_reals:
  fixes u::"complex vec"
  shows "\<langle>u|u\<rangle> \<in> nonneg_Reals"
  using inner_prod_with_itself_real inner_prod_with_itself_Re complex_nonneg_Reals_iff 
inner_prod_with_itself_Im by auto

lemma inner_prod_with_itself_Re_non0:
  assumes "u \<noteq> 0\<^sub>v (dim_vec u)"
  shows "Re (\<langle>u|u\<rangle>) > 0"
proof -
  obtain i where a1:"i < dim_vec u" and "u $ i \<noteq> 0"
    using assms zero_vec_def by (metis dim_vec eq_vecI index_zero_vec(1))
  then have f1:"Re (cnj (u $ i) * (u $ i)) > 0"
    by (metis Re_complex_of_real complex_mult_cnj complex_neq_0 mult.commute)
  moreover have f2:"Re (\<langle>u|u\<rangle>) = (\<Sum>i<dim_vec u. Re (cnj(u $ i) * (u $ i)))"
    using inner_prod_def by (simp add: lessThan_atLeast0)
  moreover have f3:"\<forall>i<dim_vec u. Re (cnj(u $ i) * (u $ i)) \<ge> 0"
    using complex_mult_cnj by simp
  ultimately show ?thesis
    using a1 inner_prod_def lessThan_iff
    by (metis (no_types, lifting) finite_lessThan sum_pos2)
qed

lemma inner_prod_with_itself_nonneg_reals_non0:
  assumes "u \<noteq> 0\<^sub>v (dim_vec u)"
  shows "\<langle>u|u\<rangle> \<noteq> 0"
  using assms inner_prod_with_itself_Re_non0 by fastforce

lemma cpx_vec_length_inner_prod [simp]:
  "\<parallel>v\<parallel>\<^sup>2 = \<langle>v|v\<rangle>"
proof -
  have "\<parallel>v\<parallel>\<^sup>2 = (\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2)"
    using cpx_vec_length_def complex_of_real_def
    by (metis (no_types, lifting) real_sqrt_power real_sqrt_unique sum_nonneg zero_le_power2)
  also have "\<dots> = (\<Sum>i<dim_vec v. cnj (v $ i) * (v $ i))"
    using complex_norm_square mult.commute by (smt of_real_sum sum.cong)
  finally show ?thesis
    using inner_prod_def by (simp add: lessThan_atLeast0)
qed

lemma inner_prod_csqrt [simp]:
  "csqrt \<langle>v|v\<rangle> = \<parallel>v\<parallel>"
  using inner_prod_with_itself_Re inner_prod_with_itself_Im csqrt_of_real_nonneg cpx_vec_length_def
  by (metis (no_types, lifting) Re_complex_of_real cpx_vec_length_inner_prod real_sqrt_ge_0_iff 
      real_sqrt_unique sum_nonneg zero_le_power2)


subsection "Unitary Matrices and Length-preservation"

text \<open>The bra-vector @{text "\<langle>A * v|"} is given by @{text "\<langle>v| * A\<^sup>\<dagger>"}$\<close>


lemma bra_mat_on_vec:
  fixes v::"complex vec" and A::"complex mat"
  assumes "dim_col A = dim_vec v"
  shows "\<langle>A * v| = \<langle>v| * (A\<^sup>\<dagger>)"
proof
  show "dim_row \<langle>A * v| = dim_row (\<langle>v| * (A\<^sup>\<dagger>))"
    by (simp add: bra_def times_mat_def)
next
  show "dim_col \<langle>A * v| = dim_col (\<langle>v| * (A\<^sup>\<dagger>))"
    by (simp add: bra_def times_mat_def)
next
  fix i j::nat
  assume a1:"i < dim_row (\<langle>v| * (A\<^sup>\<dagger>))" and a2:"j < dim_col (\<langle>v| * (A\<^sup>\<dagger>))" 
  then have "cnj((A * v) $$ (j,0)) = cnj (row A j \<bullet> v)"
    using bra_def times_mat_def ket_vec_col ket_vec_def by simp
  also have f7:"\<dots>= (\<Sum>i\<in>{0 ..< dim_vec v}. cnj(v $ i) * cnj(A $$ (j,i)))"
    using row_def scalar_prod_def cnj_sum complex_cnj_mult mult.commute
    by (smt assms index_vec lessThan_atLeast0 lessThan_iff sum.cong)
  moreover have f8:"(row \<langle>v| 0) \<bullet> (col (A\<^sup>\<dagger>) j) = 
    vec (dim_vec v) (\<lambda>i. cnj (v $ i)) \<bullet> vec (dim_col A) (\<lambda>i. cnj (A $$ (j,i)))"
    using a2 by simp 
  ultimately have "cnj((A * v) $$ (j,0)) = (row \<langle>v| 0) \<bullet> (col (A\<^sup>\<dagger>) j)"
    using assms scalar_prod_def
    by (smt dim_vec index_vec lessThan_atLeast0 lessThan_iff sum.cong)
  then have "\<langle>A * v| $$ (0,j) = (\<langle>v| * (A\<^sup>\<dagger>)) $$ (0,j)"
    using bra_def times_mat_def a2 by simp
  thus "\<langle>A * |v\<rangle>| $$ (i, j) = (\<langle>v| * (A\<^sup>\<dagger>)) $$ (i, j)" 
    using a1 by (simp add: times_mat_def bra_def)
qed

definition col_fst :: "'a mat \<Rightarrow> 'a vec" where 
  "col_fst A = vec (dim_row A) (\<lambda> i. A $$ (i,0))"

lemma col_fst_is_col [simp]:
  "col_fst M = col M 0"
  by (simp add: col_def col_fst_def)

text \<open>
We need to declare @{term "col_fst"} as a coercion from matrices to vectors in order to see a column 
matrix as a vector. 
\<close>

declare 
  [[coercion_delete ket_vec]]
  [[coercion col_fst]]

lemma unit_vec_to_col:
  assumes "dim_col A = n" and "i < n"
  shows "col A i = A * |unit_vec n i\<rangle>"
proof
  show "dim_vec (col A i) = dim_vec (A * |unit_vec n i\<rangle>)"
    using col_def times_mat_def by simp
next
  fix j::nat
  assume "j < dim_vec (col_fst (A * |unit_vec n i\<rangle>))"
  then show "col A i $ j = (A * |unit_vec n i\<rangle>) $ j"
    using assms times_mat_def ket_vec_def
    by (smt col_fst_is_col dim_col dim_col_mat(1) index_col index_mult_mat(1) index_mult_mat(2) 
index_row(1) ket_vec_col less_numeral_extra(1) scalar_prod_right_unit)
qed

lemma mult_ket_vec_is_ket_vec_of_mult:
  fixes A::"complex mat" and v::"complex vec"
  assumes "dim_col A = dim_vec v"
  shows "|A * |v\<rangle> \<rangle> = A * |v\<rangle>"
  using assms ket_vec_def
  by (metis One_nat_def col_fst_is_col dim_col dim_col_mat(1) index_mult_mat(3) ket_vec_col less_Suc0 
mat_col_eqI)

lemma unitary_squared_length_bis [simp]:
  assumes "unitary U" and "dim_vec v = dim_col U"
  shows "\<parallel>U * |v\<rangle>\<parallel>\<^sup>2 = \<parallel>v\<parallel>\<^sup>2"
proof -
  have "\<langle>U * |v\<rangle>|U * |v\<rangle> \<rangle> = (\<langle>|v\<rangle>| * (U\<^sup>\<dagger>) * |U * |v\<rangle>\<rangle>) $$ (0,0)"
    using assms(2) bra_mat_on_vec
    by (metis inner_prod_with_times_mat mult_ket_vec_is_ket_vec_of_mult)
  then have "\<langle>U * |v\<rangle>|U * |v\<rangle> \<rangle> = (\<langle>|v\<rangle>| * (U\<^sup>\<dagger>) * (U * |v\<rangle>)) $$ (0,0)"
    using assms(2) mult_ket_vec_is_ket_vec_of_mult by simp
  moreover have f1:"dim_col \<langle>|v\<rangle>| = dim_vec v"
    using ket_vec_def bra_def by simp
  moreover have "dim_row (U\<^sup>\<dagger>) = dim_vec v"
    using assms(2) by simp
  ultimately have "\<langle>U * |v\<rangle>|U * |v\<rangle> \<rangle> = (\<langle>|v\<rangle>| * ((U\<^sup>\<dagger>) * U) * |v\<rangle>) $$ (0,0)"
    using assoc_mult_mat
    by (smt carrier_mat_triv dim_row_mat(1) hermite_cnj_def ket_vec_def mat_carrier times_mat_def)
  then have "\<langle>U * |v\<rangle>|U * |v\<rangle> \<rangle> = (\<langle>|v\<rangle>| * |v\<rangle>) $$ (0,0)"
    using assms(1) assms(2) f1 unitary_def by auto
  thus ?thesis
    using  cpx_vec_length_inner_prod
    by (metis Re_complex_of_real inner_prod_with_times_mat)
qed

lemma col_ket_vec [simp]:
  assumes "dim_col M = 1"
  shows "|col M 0\<rangle> = M"
  using eq_matI assms ket_vec_def by auto

lemma state_col_ket_vec:
  assumes "state 1 v"
  shows "state 1 |col v 0\<rangle>"
  using assms by (simp add: state_def)

lemma eq_ket_vec [intro]:
  assumes "u = v"
  shows "|u\<rangle> = |v\<rangle>"
  using assms by simp

lemma col_ket_vec_index [simp]:
  assumes "i < dim_row v"
  shows "|col v 0\<rangle> $$ (i,0) = v $$ (i,0)"
  using assms ket_vec_def by (simp add: col_def)

lemma col_index_of_mat_col [simp]:
  assumes "dim_col v = 1" and "i < dim_row v"
  shows "col v 0 $ i = v $$ (i,0)"
  using assms by simp

lemma unitary_squared_length [simp]:
  assumes "unitary U" and "dim_row v = dim_col U" and "dim_col v = 1"
  shows "\<parallel>col (U * v) 0\<parallel>\<^sup>2 = \<parallel>col v 0\<parallel>\<^sup>2"
proof -
  have "dim_vec (col v 0) = dim_col U"
    using assms(2) by simp
  then have "\<parallel>col_fst (U * |col v 0\<rangle>)\<parallel>\<^sup>2 = \<parallel>col v 0\<parallel>\<^sup>2"
    using unitary_squared_length_bis[of "U" "col v 0"] assms(1) by simp
  thus ?thesis
    using assms(3) by simp
qed

text \<open> 
A unitary matrix is length-preserving, i.e. it acts on a vector to produce another vector of the 
same length. 
\<close>

lemma unitary_length [simp]:
  fixes U::"complex mat" and v::"complex mat"
  assumes "unitary U" and "dim_row v = dim_col U" and "dim_col v = 1"
  shows "\<parallel>col (U * v) 0\<parallel> = \<parallel>col v 0\<parallel>"
  using assms unitary_squared_length
  by (metis cpx_vec_length_inner_prod inner_prod_csqrt of_real_hom.injectivity)

lemma unitary_length_bis [simp]:
  fixes U::"complex mat" and v::"complex vec"
  assumes "unitary U" and "dim_vec v = dim_col U"
  shows "\<parallel>U * |v\<rangle>\<parallel> = \<parallel>v\<parallel>"
  using assms unitary_squared_length_bis
  by (metis cpx_vec_length_inner_prod inner_prod_csqrt of_real_hom.injectivity)

lemma inner_prod_with_unitary_mat [simp]:
  assumes "unitary U" and "dim_vec u = dim_col U" and "dim_vec v = dim_col U"
  shows "\<langle>U * |u\<rangle>|U * |v\<rangle>\<rangle> = \<langle>u|v\<rangle>"
proof -
  have f1:"\<langle>U * |u\<rangle>|U * |v\<rangle>\<rangle> = (\<langle>|u\<rangle>| * (U\<^sup>\<dagger>) * U * |v\<rangle>) $$ (0,0)"
    using assms(2-3) bra_mat_on_vec mult_ket_vec_is_ket_vec_of_mult
    by (smt assoc_mult_mat carrier_mat_triv col_fst_def dim_vec hermite_cnj_dim_col index_mult_mat(2) 
        index_mult_mat(3) inner_prod_with_times_mat ket_vec_def mat_carrier)
  moreover have f2:"\<langle>|u\<rangle>| \<in> carrier_mat 1 (dim_vec v)"
    using bra_def ket_vec_def assms(2-3) by simp
  moreover have f3:"U\<^sup>\<dagger> \<in> carrier_mat (dim_col U) (dim_row U)"
    using hermite_cnj_def by simp
  ultimately have "\<langle>U * |u\<rangle>|U * |v\<rangle>\<rangle> = (\<langle>|u\<rangle>| * (U\<^sup>\<dagger> * U) * |v\<rangle>) $$ (0,0)"
    using assms(3) assoc_mult_mat by (metis carrier_mat_triv)
  also have "\<dots> = (\<langle>|u\<rangle>| * |v\<rangle>) $$ (0,0)"
    using assms(1) unitary_def
    by (simp add: assms(2) bra_def ket_vec_def)
  finally show ?thesis
    using assms(2-3) inner_prod_with_times_mat by presburger
qed

text \<open>As a consequence we prove that columns and rows of a unitary matrix are orthonormal vectors.\<close>

lemma unitary_unit_col [simp]:
  assumes "unitary U" and "dim_col U = n" and "i < n"
  shows "\<parallel>col U i\<parallel> = 1"
  using assms unit_vec_to_col unitary_length_bis by simp

lemma unitary_unit_row [simp]:
  assumes "unitary U" and "dim_row U = n" and "i < n"
  shows "\<parallel>row U i\<parallel> = 1"
proof -
  have "row U i = col (U\<^sup>t) i"
    using  assms(2-3) by simp
  thus ?thesis
    using assms transpose_of_unitary_is_unitary unitary_unit_col
    by (metis index_transpose_mat(3))
qed

lemma orthogonal_col_of_unitary [simp]:
  assumes "unitary U" and "dim_col U = n" and "i < n" and "j < n" and "i \<noteq> j"
  shows "\<langle>col U i|col U j\<rangle> = 0"
proof -
  have "\<langle>col U i|col U j\<rangle> = \<langle>U * |unit_vec n i\<rangle>| U * |unit_vec n j\<rangle>\<rangle>"
    using assms(2-4) unit_vec_to_col by simp
  also have "\<dots> = \<langle>unit_vec n i |unit_vec n j\<rangle>"
    using assms(1-2) inner_prod_with_unitary_mat index_unit_vec(3) by simp
  finally show ?thesis
    using assms(3-5) by simp
qed

lemma orthogonal_row_of_unitary [simp]:
  fixes U::"complex mat"
  assumes "unitary U" and "dim_row U = n" and "i < n" and "j < n" and "i \<noteq> j"
  shows "\<langle>row U i|row U j\<rangle> = 0"
  using assms orthogonal_col_of_unitary transpose_of_unitary_is_unitary col_transpose
  by (metis index_transpose_mat(3))


text\<open>
As a consequence, we prove that a quantum gate acting on a state of a system of n qubits give 
another state of that same system.
\<close>

lemma gate_on_state_is_state [intro, simp]:
  assumes a1:"gate n A" and a2:"state n v"
  shows "state n (A * v)"
proof
  show "dim_row (A * v) = 2^n"
    using gate_def state_def a1 by simp
next
  show "dim_col (A * v) = 1"
    using state_def a2 by simp
next
  have "square_mat A"
    using a1 gate_def by simp
  then have "dim_col A = 2^n"
    using a1 gate.dim_row by simp
  then have "dim_col A = dim_row v"
    using a2 state.dim_row by simp
  then have "\<parallel>col (A * v) 0\<parallel> = \<parallel>col v 0\<parallel>"
    using unitary_length assms gate_def state_def by simp
  thus"\<parallel>col (A * v) 0\<parallel> = 1"
    using a2 state.length by simp
qed


subsection \<open>A Few Well-known Quantum Gates\<close>

text \<open>
Any unitary operation on n qubits can be implemented exactly by composing single qubits and
CNOT-gates (controlled-NOT gates). However, no straightforward method is known to implement these 
gates in a fashion which is resistant to errors. But, the Hadamard gate, the phase gate, the 
CNOT-gate and the @{text "\<pi>/8"} gate are also universal for quantum computations, i.e. any quantum circuit on 
n qubits can be approximated to an arbitrary accuracy by using only these gates, and these gates can 
be implemented in a fault-tolerant way. 
\<close>

text \<open>We introduce a coercion from real matrices to complex matrices.\<close>

definition real_to_cpx_mat:: "real mat \<Rightarrow> complex mat" where
"real_to_cpx_mat A \<equiv> mat (dim_row A) (dim_col A) (\<lambda>(i,j). A $$ (i,j))"

text \<open>Our first quantum gate: the identity matrix! Arguably, not a very interesting one though!\<close>

definition Id :: "nat \<Rightarrow> complex mat" where
"Id n \<equiv> 1\<^sub>m (2^n)"

lemma id_is_gate [simp]:
  "gate n (Id n)"
proof
  show "dim_row (Id n) = 2^n"
    using Id_def by simp
next
  show "square_mat (Id n)"
    using Id_def by simp
next
  show "unitary (Id n)" 
    by (simp add: Id_def)
qed

text \<open>More interesting: the Pauli matrices.\<close>

definition X ::"complex mat" where
"X \<equiv> mat 2 2 (\<lambda>(i,j). if i=j then 0 else 1)"

text\<open> 
Be aware that @{text "gate n A"} means that the matrix A has dimension @{text "2^n * 2^n"}. 
For instance, with this convention a 2 X 2 matrix A which is unitary satisfies @{text "gate 1 A"}
 but not @{text "gate 2 A"} as one might have been expected.
\<close>

lemma hermite_cnj_of_X [simp]:
  "X\<^sup>\<dagger> = X"
  using hermite_cnj_def by (simp add: X_def cong_mat)

lemma X_inv [simp]:
  "X * X = 1\<^sub>m 2"
  apply(simp add: X_def times_mat_def one_mat_def)
  apply(rule cong_mat)
  by(auto simp: scalar_prod_def)

lemma X_is_gate [simp]:
  "gate 1 X"
  apply(simp add: gate_def unitary_def)
  apply(simp add: X_def)
  done

definition Y ::"complex mat" where
"Y \<equiv> mat 2 2 (\<lambda>(i,j). if i=j then 0 else (if i=0 then -\<i> else \<i>))"

lemma hermite_cnj_of_Y [simp]:
  "Y\<^sup>\<dagger> = Y"
  using hermite_cnj_def by (simp add: Y_def cong_mat)

lemma Y_inv [simp]:
  "Y * Y = 1\<^sub>m 2"
  apply(simp add: Y_def times_mat_def one_mat_def)
  apply(rule cong_mat)
  by(auto simp: scalar_prod_def)

lemma Y_is_gate [simp]:
  "gate 1 Y"
  apply(simp add: gate_def unitary_def)
  apply(simp add: Y_def)
  done

definition Z ::"complex mat" where
"Z \<equiv> mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 0 else (if i=0 then 1 else -1))"

lemma hermite_cnj_of_Z [simp]:
  "Z\<^sup>\<dagger> = Z"
  using hermite_cnj_def by (simp add: Z_def cong_mat)

lemma Z_inv [simp]:
  "Z * Z = 1\<^sub>m 2"
  apply(simp add: Z_def times_mat_def one_mat_def)
  apply(rule cong_mat)
  by(auto simp: scalar_prod_def)

lemma Z_is_gate [simp]:
  "gate 1 Z"
  apply(simp add: gate_def unitary_def)
  apply(simp add: Z_def)
  done

text \<open>The Hadamard gate\<close>

definition H ::"complex mat" where
"H \<equiv> 1/sqrt(2) \<cdot>\<^sub>m (mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i=0 then 1 else -1)))"

lemma H_without_scalar_prod:
  "H = mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1/sqrt(2) else (if i=0 then 1/sqrt(2) else -(1/sqrt(2))))"
  using cong_mat by (auto simp: H_def)

lemma hermite_cnj_of_H [simp]:
  "H\<^sup>\<dagger> = H"
  using hermite_cnj_def by (auto simp: H_def cong_mat)

lemma H_inv [simp]:
  "H * H = 1\<^sub>m 2"
  apply(simp add: H_def times_mat_def one_mat_def)
  apply(rule cong_mat)
  by(auto simp: scalar_prod_def complex_eqI)

lemma H_is_gate [simp]:
  "gate 1 H"
  apply(simp add: gate_def unitary_def)
  apply(simp add: H_def)
  done

lemma H_values:
  fixes i j:: nat
  assumes "i < dim_row H" and "j < dim_col H" and "i \<noteq> 1 \<or> j \<noteq> 1" 
  shows "H $$ (i,j) = 1/sqrt 2"
proof-
  have "i < 2"
    using assms(1) by (simp add: H_without_scalar_prod less_2_cases)
  moreover have "j < 2"
    using assms(2) by (simp add: H_without_scalar_prod less_2_cases)
  ultimately show ?thesis 
    using assms(3) H_without_scalar_prod by(smt One_nat_def index_mat(1) less_2_cases old.prod.case)
qed

text \<open>The controlled-NOT gate\<close>

definition CNOT ::"complex mat" where
"CNOT \<equiv> mat 4 4 
  (\<lambda>(i,j). if i=0 \<and> j=0 then 1 else 
    (if i=1 \<and> j=1 then 1 else 
      (if i=2 \<and> j=3 then 1 else 
        (if i=3 \<and> j=2 then 1 else 0))))"

lemma hermite_cnj_of_CNOT [simp]:
  "CNOT\<^sup>\<dagger> = CNOT"
  using hermite_cnj_def by (simp add: CNOT_def cong_mat)

lemma CNOT_inv [simp]:
  "CNOT * CNOT = 1\<^sub>m 4"
  apply(simp add: CNOT_def times_mat_def one_mat_def)
  apply(rule cong_mat)
  by(auto simp: scalar_prod_def)

lemma CNOT_is_gate [simp]:
  "gate 2 CNOT"
  apply(simp add: gate_def unitary_def)
  apply(simp add: CNOT_def)
  done

text \<open>The phase gate, also known as the S-gate\<close>

definition S ::"complex mat" where
"S \<equiv> mat 2 2 (\<lambda>(i,j). if i=0 \<and> j=0 then 1 else (if i=1 \<and> j=1 then \<i> else 0))"

text \<open>The @{text "\<pi>/8"} gate, also known as the T-gate\<close>

definition T ::"complex mat" where
"T \<equiv> mat 2 2 (\<lambda>(i,j). if i=0 \<and> j=0 then 1 else (if i=1 \<and> j=1 then exp(\<i>*(pi/4)) else 0))"

text \<open>A few relations between the Hadamard gate and the Pauli matrices\<close>

lemma HXH_is_Z [simp]:
  "H * X * H = Z" 
  apply(simp add: X_def Z_def H_def times_mat_def)
  apply(rule cong_mat)
  by(auto simp add: scalar_prod_def complex_eqI)

lemma HYH_is_minusY [simp]:
  "H * Y * H = - Y" 
  apply(simp add: Y_def H_def times_mat_def)
  apply(rule eq_matI)
  by(auto simp add: scalar_prod_def complex_eqI)

lemma HZH_is_X [simp]:
  shows "H * Z * H = X"  
  apply(simp add: X_def Z_def H_def times_mat_def)
  apply(rule cong_mat)
  by(auto simp add: scalar_prod_def complex_eqI)


subsection \<open>Measurement\<close>

text \<open>
Given an element v  such that @{text "state n v"}, its components @{text "v $ i"} (when v is seen as 
a vector, v being a matrix column) for @{text "0 \<le> i < n"} have to be understood as the coefficients 
of the representation of v in the basis given by the unit vectors of dimension $2^n$, unless stated otherwise. 
Such a vector v is a state for a quantum system of n qubits.
In the literature on quantum computing, for $n = 1$, i.e. for a quantum system of 1 qubit, the elements
of the so-called computational basis are denoted $|0\rangle$,$|1\rangle$, and these last elements might be understood
for instance as $(1,0)$,$(0,1)$, i.e. as the zeroth and the first elements of a given basis ; for $n = 2$, 
i.e. for a quantum system of 2 qubits, the elements of the computational basis are denoted $|00\rangle$,
$|01\rangle$, $|10\rangle$,$|11\rangle$, and they might be understood for instance as $(1,0,0,0)$,
$(0,1,0,0)$, $(0,0,1,0)$, $(0,0,0,1)$; and so on for higher values of $n$. 
The idea behind these standard notations is that the labels on the vectors of the 
computational basis are the binary expressions of the natural numbers indexing the elements
in a given ordered basis interpreting the computational basis in a specific context, another point of
view is that the order of the basis corresponds to the lexicographic order for the labels. 
Those labels also represent the possible outcomes of a measurement of the $n$ qubits of the system, 
while the squared modules of the corresponding coefficients represent the probabilities for those 
outcomes. The fact that the vector v has to be normalized expresses precisely the fact that the squared 
modules of the coefficients represent some probabilities and hence their sum should be $1$.
Note that in the case of a system with multiple qubits, i.e. $n \geq 2$, one can model the simultaneous 
measurement of multiple qubits by sequential measurements of single qubits. Indeed, this last process
leads to the same probabilities for the various possible outcomes.
Given a system with n-qubits and i the index of one qubit among the $n$ qubits of the system, where
$0 \leq i \leq n-1$ (i.e. we start the indexing from $0$), we want to find the indices of the states of the
computational basis whose labels have a $1$ at the ith spot (counting from $0$). For instance, 
if $n=3$ and $i=2$ then $1$,$3$,$5$,$7$ are the indices of the elements of the computational basis 
with a $1$ at the 2nd spot, namely $|001\rangle$,$|011\rangle$,$|101\rangle$,$|111\rangle$. To achieve that we define the 
predicate @{term "select_index"} below.
\<close>

definition select_index ::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"select_index n i j \<equiv> (i\<le>n-1) \<and> (j\<le>2^n - 1) \<and> (j mod 2^(n-i) \<ge> 2^(n-1-i))"

lemma select_index_union:
  "{k| k::nat. select_index n i k} \<union> {k| k::nat. (k<2^n) \<and> \<not> select_index n i k} = {0..<2^n::nat}"
proof
  have "{k |k. select_index n i k} \<subseteq> {0..<2 ^ n}"
  proof
    fix x::nat assume "x \<in> {k |k. select_index n i k}"
    then show "x \<in> {0..<2^n}" 
      using select_index_def
      by (metis (no_types, lifting) atLeastLessThan_iff diff_diff_cancel diff_is_0_eq' diff_le_mono2 
le_less_linear le_numeral_extra(2) mem_Collect_eq one_le_numeral one_le_power select_index_def zero_order(1))
  qed
  moreover have "{k |k. k<2 ^ n \<and> \<not> select_index n i k} \<subseteq> {0..<2 ^ n}" by auto
  ultimately show "{k |k. select_index n i k} \<union> {k |k. k<2 ^ n \<and> \<not> select_index n i k} \<subseteq> {0..<2 ^ n}" by simp
next
  show "{0..<2 ^ n} \<subseteq> {k |k. select_index n i k} \<union> {k |k. k<2 ^ n \<and> \<not> select_index n i k}" by auto
qed

lemma select_index_inter:
  "{k| k::nat. select_index n i k} \<inter> {k| k::nat. (k<2^n) \<and> \<not> select_index n i k} = {}" by auto

lemma outcomes_sum [simp]:
  fixes f :: "nat \<Rightarrow> real"
  shows
  "(\<Sum>j\<in>{k| k::nat. select_index n i k}. (f j)) + 
   (\<Sum>j\<in>{k| k::nat. (k<2^n) \<and> \<not> select_index n i k}. (f j)) = 
   (\<Sum>j\<in>{0..<2^n::nat}. (f j))"
proof -
  have "{k| k::nat. select_index n i k} \<subseteq> {0..<2^n::nat}"
    using select_index_union by blast
  then have "finite {k| k::nat. select_index n i k}"
    using rev_finite_subset by blast
  moreover have "{k| k::nat. (k<2^n) \<and> \<not> select_index n i k} \<subseteq> {0..<2^n::nat}"
    using select_index_union by blast
  then have "finite {k| k::nat. (k<2^n) \<and> \<not> select_index n i k}"
    using rev_finite_subset by blast
  ultimately have "(\<Sum>j\<in>{k| k::nat. select_index n i k}\<union>{k| k::nat. (k<2^n) \<and> \<not> select_index n i k}. (f j)) = 
           (\<Sum>j\<in>{k| k::nat. select_index n i k}. (f j)) + 
           (\<Sum>j\<in>{k| k::nat. (k<2^n) \<and> \<not> select_index n i k}. (f j)) -
           (\<Sum>j\<in>{k| k::nat. select_index n i k}\<inter>{k| k::nat. (k<2^n) \<and> \<not> select_index n i k}. (f j))"
    using sum_Un by blast
  then have "(\<Sum>j\<in>{0..<2^n::nat}. (f j)) = 
                (\<Sum>j\<in>{k| k::nat. select_index n i k}. (f j)) + 
                (\<Sum>j\<in>{k| k::nat. (k<2^n) \<and> \<not> select_index n i k}. (f j)) -
                (\<Sum>j\<in>{}. (f j))"
    using select_index_union select_index_inter by simp
  thus ?thesis by simp
qed

text \<open>
Given a state v of a n-qbit system, we compute the probability that a measure 
of qubit i has the outcome 1.
\<close>

definition prob1 ::"nat \<Rightarrow> complex mat \<Rightarrow> nat \<Rightarrow> real" where
"prob1 n v i \<equiv> \<Sum>j\<in>{k| k::nat. select_index n i k}. (cmod(v $$ (j,0)))\<^sup>2"

definition prob0 ::"nat \<Rightarrow> complex mat \<Rightarrow> nat \<Rightarrow> real" where
"prob0 n v i \<equiv> \<Sum>j\<in>{k| k::nat. (k<2^n) \<and> \<not> select_index n i k}. (cmod(v $$ (j,0)))\<^sup>2"

lemma
  shows prob1_geq_zero:"prob1 n v i \<ge> 0" and prob0_geq_zero:"prob0 n v i \<ge> 0" 
proof -
  have "(\<Sum>j\<in>{k| k::nat. select_index n i k}. (cmod(v $$ (j,0)))\<^sup>2) \<ge> 
           (\<Sum>j\<in>{k| k::nat. select_index n i k}. (0::real))"
    by (simp add: sum_nonneg)
  then have "(\<Sum>j\<in>{k| k::nat. select_index n i k}. (cmod(v $$ (j,0)))\<^sup>2) \<ge> 0" by simp
  thus "prob1 n v i \<ge> 0"
    using prob1_def by simp
next
  have "(\<Sum>j\<in>{k| k::nat. (k < 2 ^ n) \<and> \<not> select_index n i k}. (cmod(v $$ (j,0)))\<^sup>2) \<ge> 
           (\<Sum>j\<in>{k| k::nat. (k < 2 ^ n) \<and> \<not> select_index n i k}. (0::real))"
    by (simp add: sum_nonneg)
  then have "(\<Sum>j\<in>{k| k::nat. (k < 2 ^ n) \<and> \<not> select_index n i k}. (cmod(v $$ (j,0)))\<^sup>2) \<ge> 0" by simp
  thus "prob0 n v i \<ge> 0"
    using prob0_def by simp
qed

lemma prob_sum_is_one [simp]:
  assumes "state n v"
  shows "prob1 n v i + prob0 n v i = 1"
proof-
  have "prob1 n v i + prob0 n v i = (\<Sum>j\<in>{0..<2^n::nat}. (cmod(v $$ (j,0)))\<^sup>2)"
    using prob1_def prob0_def outcomes_sum by simp
  also have "\<dots> = \<parallel>col v 0\<parallel>\<^sup>2"
    using cpx_vec_length_def assms state_def atLeast0LessThan by fastforce
  finally show ?thesis 
    using assms state_def by simp
qed

lemma
  assumes "state n v"
  shows prob1_leq_one:"prob1 n v i \<le> 1" and prob0_leq_one:"prob0 n v i \<le> 1"
   apply(metis assms le_add_same_cancel1 prob0_geq_zero prob_sum_is_one)
  apply(metis assms le_add_same_cancel2 prob1_geq_zero prob_sum_is_one)
  done

lemma prob0_is_prob: 
  assumes "state n v"
  shows "prob0 n v i \<ge> 0 \<and> prob0 n v i \<le> 1"
  by (simp add: assms prob0_geq_zero prob0_leq_one)

lemma prob1_is_prob: 
  assumes "state n v"
  shows "prob1 n v i \<ge> 0 \<and> prob1 n v i \<le> 1"
  by (simp add: assms prob1_geq_zero prob1_leq_one)

text \<open>Below we give the new state of a n-qubits system after a measurement of the ith qubit gave 0.\<close>

definition post_meas0 ::"nat \<Rightarrow> complex mat \<Rightarrow> nat \<Rightarrow> complex mat" where
"post_meas0 n v i \<equiv> 
  of_real(1/sqrt(prob0 n v i)) \<cdot>\<^sub>m |vec (2^n) (\<lambda>j. if \<not> select_index n i j then v $$ (j,0) else 0)\<rangle>"
 
text \<open>
Note that a division by 0 never occurs. Indeed, if @{text "sqrt(prob0 n v i)"} would be 0 then 
@{text "prob0 n v i"} would be 0 and it would mean that the measurement of the ith qubit gave 1.
\<close>

lemma smult_vec_length [simp]:
  assumes "x \<ge> 0"
  shows "\<parallel>complex_of_real(x) \<cdot>\<^sub>v v\<parallel> = x * \<parallel>v\<parallel>"
proof-
  have "(\<lambda>i::nat.(cmod (complex_of_real x * v $ i))\<^sup>2) = (\<lambda>i::nat. (cmod (v $ i))\<^sup>2 * x\<^sup>2)" 
    by (auto simp: norm_mult power_mult_distrib)
  then have "(\<Sum>i<dim_vec v. (cmod (complex_of_real x * v $ i))\<^sup>2) = 
             (\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2 * x\<^sup>2)" by meson
  moreover have "(\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2 * x\<^sup>2) = x\<^sup>2 * (\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2)"
    by (metis (no_types) mult.commute sum_distrib_right)
  moreover have "sqrt(x\<^sup>2 * (\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2)) = 
                 sqrt(x\<^sup>2) * sqrt (\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2)" 
    using real_sqrt_mult by blast
  ultimately show ?thesis
    by(simp add: cpx_vec_length_def assms)
qed

lemma smult_vec_length_bis [simp]:
  assumes "x \<ge> 0"
  shows "\<parallel>col (complex_of_real(x) \<cdot>\<^sub>m |v\<rangle>) 0\<parallel> = x * \<parallel>v\<parallel>"
  using assms smult_ket_vec smult_vec_length ket_vec_col by metis

lemma post_meas0_is_state [simp]:
  assumes "state n v" and "prob0 n v i \<noteq> 0"
  shows "state n (post_meas0 n v i)" 
proof -
  have "(\<Sum>j\<in>{0..<2^n::nat}. (cmod (if \<not> select_index n i j then v $$ (j,0) else 0))\<^sup>2) = 
           (\<Sum>j\<in>{k| k::nat. select_index n i k}. (cmod (if \<not> select_index n i j then v $$ (j,0) else 0))\<^sup>2) +
           (\<Sum>j\<in>{k| k::nat. (k<2^n) \<and> \<not> select_index n i k}. (cmod (if \<not> select_index n i j then v $$ (j,0) else 0))\<^sup>2)"
    using outcomes_sum[of "\<lambda>j. (cmod (if \<not> select_index n i j then v $$ (j,0) else 0))\<^sup>2" n i] by simp
  moreover have "(\<Sum>j\<in>{k| k::nat. (k<2^n) \<and> \<not> select_index n i k}. (cmod (if \<not> select_index n i j then v $$ (j,0) else 0))\<^sup>2) = 
           prob0 n v i"
    by(simp add: prob0_def)
  ultimately have "\<parallel>vec (2 ^ n) (\<lambda>j. if \<not> select_index n i j then v $$ (j,0) else 0)\<parallel> = sqrt(prob0 n v i)"
    using lessThan_atLeast0 by (simp add: cpx_vec_length_def)
  moreover have "\<parallel>col (complex_of_real (1/sqrt (prob0 n v i)) \<cdot>\<^sub>m |vec (2^n) (\<lambda>j. if \<not> select_index n i j then v $$ (j,0) else 0)\<rangle>) 0\<parallel> = 
           (1/sqrt (prob0 n v i)) * \<parallel>vec (2^n) (\<lambda>j. if \<not> select_index n i j then v $$ (j,0) else 0)\<parallel>"
    using prob0_geq_zero smult_vec_length_bis by(metis (no_types, lifting) real_sqrt_ge_0_iff zero_le_divide_1_iff)
  ultimately show ?thesis
    using state_def post_meas0_def by (simp add: ket_vec_def post_meas0_def assms(2))
qed

text \<open>Below we give the new state of a n-qubits system after a measurement of the ith qubit gave 1.\<close>

definition post_meas1 ::"nat \<Rightarrow> complex mat \<Rightarrow> nat \<Rightarrow> complex mat" where
"post_meas1 n v i \<equiv> 
  of_real(1/sqrt(prob1 n v i)) \<cdot>\<^sub>m |vec (2^n) (\<lambda>j. if select_index n i j then v $$ (j,0) else 0)\<rangle>"
 
text \<open>
Note that a division by 0 never occurs. Indeed, if @{text "sqrt(prob1 n v i)"} would be 0 then 
@{text "prob1 n v i"} would be 0 and it would mean that the measurement of the ith qubit gave 0.
\<close> 

lemma post_meas_1_is_state [simp]:
  assumes "state n v" and "prob1 n v i \<noteq> 0"
  shows "state n (post_meas1 n v i)"
proof -
  have "(\<Sum>j\<in>{0..<2^n::nat}. (cmod (if select_index n i j then v $$ (j,0) else 0))\<^sup>2) = 
           (\<Sum>j\<in>{k| k::nat. select_index n i k}. (cmod (if select_index n i j then v $$ (j,0) else 0))\<^sup>2) +
           (\<Sum>j\<in>{k| k::nat. (k<2^n) \<and> \<not> select_index n i k}. (cmod (if select_index n i j then v $$ (j,0) else 0))\<^sup>2)"
    using outcomes_sum[of "\<lambda>j. (cmod (if select_index n i j then v $$ (j,0) else 0))\<^sup>2" n i] by simp
  then have "\<parallel>vec (2^n) (\<lambda>j. if select_index n i j then v $$ (j,0) else 0)\<parallel> = sqrt(prob1 n v i)"
    using lessThan_atLeast0 by (simp add: cpx_vec_length_def prob1_def)
  moreover have "\<parallel>col(complex_of_real (1/sqrt (prob1 n v i)) \<cdot>\<^sub>m |vec (2^n) (\<lambda>j. if select_index n i j then v $$ (j,0) else 0)\<rangle>) 0\<parallel> = 
           (1/sqrt(prob1 n v i)) * \<parallel>vec (2^n) (\<lambda>j. if select_index n i j then v $$ (j,0) else 0)\<parallel>"
    using prob1_geq_zero smult_vec_length_bis
    by (metis (no_types, lifting) real_sqrt_ge_0_iff zero_le_divide_1_iff)
  ultimately have "\<parallel>col(complex_of_real (1/sqrt (prob1 n v i)) \<cdot>\<^sub>m |vec (2^n) (\<lambda>j. if select_index n i j then v $$ (j,0) else 0)\<rangle>) 0\<parallel>
= (1/sqrt(prob1 n v i)) * sqrt(prob1 n v i)" by simp
  thus ?thesis
    using state_def post_meas1_def by (simp add: ket_vec_def post_meas1_def assms(2))
qed

text \<open>
The measurement operator below takes a number of qubits n, a state v of a n-qubits system, a number
i corresponding to the index (starting from 0) of one qubit among the n-qubits, and it computes a list 
whose first (resp. second) element is the pair made of the probability that the outcome of the measurement
of the ith qubit is 0 (resp. 1) and the corresponding post-measurement state of the system.
Of course, note that i should be strictly less than n and v should be a state of dimension n, i.e. 
state n v should hold".
\<close>

definition meas ::"nat \<Rightarrow> complex mat \<Rightarrow> nat \<Rightarrow> _list" where
"meas n v i \<equiv> [(prob0 n v i, post_meas0 n v i), (prob1 n v i, post_meas1 n v i)]"


subsection \<open>The Bell States\<close>

text \<open>
We introduce below the so-called Bell states, also known as EPR pairs (EPR stands for Einstein,
Podolsky and Rosen).
\<close>

definition bell00 ::"complex mat" ("|\<beta>\<^sub>0\<^sub>0\<rangle>") where
"bell00 \<equiv> 1/sqrt(2) \<cdot>\<^sub>m |vec 4 (\<lambda>i. if i=0 \<or> i=3 then 1 else 0)\<rangle>"

definition bell01 ::"complex mat" ("|\<beta>\<^sub>0\<^sub>1\<rangle>") where
"bell01 \<equiv> 1/sqrt(2) \<cdot>\<^sub>m |vec 4 (\<lambda>i. if i=1 \<or> i=2 then 1 else 0)\<rangle>"

definition bell10 ::"complex mat" ("|\<beta>\<^sub>1\<^sub>0\<rangle>") where
"bell10 \<equiv> 1/sqrt(2) \<cdot>\<^sub>m |vec 4 (\<lambda>i. if i=0 then 1 else if i=3 then -1 else 0)\<rangle>"

definition bell11 ::"complex mat" ("|\<beta>\<^sub>1\<^sub>1\<rangle>") where
"bell11 \<equiv> 1/sqrt(2) \<cdot>\<^sub>m |vec 4 (\<lambda>i. if i=1 then 1 else if i=2 then -1 else 0)\<rangle>"

lemma
  shows bell00_is_state [simp]:"state 2 |\<beta>\<^sub>0\<^sub>0\<rangle>" and bell01_is_state [simp]:"state 2 |\<beta>\<^sub>0\<^sub>1\<rangle>" and 
    bell10_is_state [simp]:"state 2 |\<beta>\<^sub>1\<^sub>0\<rangle>" and bell11_is_state [simp]:"state 2 |\<beta>\<^sub>1\<^sub>1\<rangle>"
     apply (auto simp: state_def bell00_def bell01_def bell10_def bell11_def ket_vec_def)
     apply (auto simp: cpx_vec_length_def Set_Interval.lessThan_atLeast0 cmod_def power2_eq_square) 
  done

lemma ket_vec_index [simp]:
  assumes "i < dim_vec v"
  shows "|v\<rangle> $$ (i,0) = v $ i"
  using assms ket_vec_def by simp

lemma bell00_index [simp]:
  shows "|\<beta>\<^sub>0\<^sub>0\<rangle> $$ (0,0) = 1/sqrt 2" and "|\<beta>\<^sub>0\<^sub>0\<rangle> $$ (1,0) = 0" and "|\<beta>\<^sub>0\<^sub>0\<rangle> $$ (2,0) = 0" and 
    "|\<beta>\<^sub>0\<^sub>0\<rangle> $$ (3,0) = 1/sqrt 2"
     apply (auto simp: bell00_def ket_vec_def)
  done

lemma bell01_index [simp]:
  shows "|\<beta>\<^sub>0\<^sub>1\<rangle> $$ (0,0) = 0" and "|\<beta>\<^sub>0\<^sub>1\<rangle> $$ (1,0) = 1/sqrt 2" and "|\<beta>\<^sub>0\<^sub>1\<rangle> $$ (2,0) = 1/sqrt 2" and 
    "|\<beta>\<^sub>0\<^sub>1\<rangle> $$ (3,0) = 0"
     apply (auto simp: bell01_def ket_vec_def)
  done

lemma bell10_index [simp]:
  shows "|\<beta>\<^sub>1\<^sub>0\<rangle> $$ (0,0) = 1/sqrt 2" and "|\<beta>\<^sub>1\<^sub>0\<rangle> $$ (1,0) = 0" and "|\<beta>\<^sub>1\<^sub>0\<rangle> $$ (2,0) = 0" and 
    "|\<beta>\<^sub>1\<^sub>0\<rangle> $$ (3,0) = - 1/sqrt 2"
     apply (auto simp: bell10_def ket_vec_def)
  done

lemma bell_11_index [simp]:
  shows "|\<beta>\<^sub>1\<^sub>1\<rangle> $$ (0,0) = 0" and "|\<beta>\<^sub>1\<^sub>1\<rangle> $$ (1,0) = 1/sqrt 2" and "|\<beta>\<^sub>1\<^sub>1\<rangle> $$ (2,0) = - 1/sqrt 2" and 
    "|\<beta>\<^sub>1\<^sub>1\<rangle> $$ (3,0) = 0"
     apply (auto simp: bell11_def ket_vec_def)
  done

text \<open>
A Bell state is a remarkable state. Indeed, if one makes one measure, either of the first or the second 
qubit, then one gets either $0$ with probability $1/2$ or $1$ with probability $1/2$. Moreover, in the case of 
two successive measurements of the first and second qubit, the outcomes are correlated. 
Indeed, in the case of @{text "|\<beta>\<^sub>0\<^sub>0\<rangle>"} or @{text "|\<beta>\<^sub>1\<^sub>0\<rangle>"} (resp. @{text "|\<beta>\<^sub>0\<^sub>1\<rangle>"} or @{text "|\<beta>\<^sub>1\<^sub>1\<rangle>"}) if 
one measures the second qubit after a measurement of the first qubit (or the other way around) then 
one gets the same outcomes (resp. opposite outcomes), i.e. for instance the probability of measuring 
$0$ for the second qubit after a measure with outcome $0$ for the first qubit is $1$ (resp. $0$).
\<close>

lemma prob0_bell_fst [simp]:
  assumes "v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
  shows "prob0 2 v 0 = 1/2" 
proof -
  have set_0 [simp]:"{k| k::nat. (k<4) \<and> \<not> select_index 2 0 k} = {0,1}"
    using select_index_def by auto
  have "v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<Longrightarrow> prob0 2 v 0 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>0\<rangle>"
    show "prob0 2 v 0 = 1/2"
    proof -
      have "prob0 2 v 0 = (\<Sum>j\<in>{k| k::nat. (k<4) \<and> \<not> select_index 2 0 k}. (cmod(bell00 $$ (j,0)))\<^sup>2)"
        apply (auto simp: prob0_def asm).
      also have "\<dots> = (\<Sum>j\<in>{0,1}. (cmod(bell00 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        apply (auto simp: bell00_def ket_vec_def).
      finally show  ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<Longrightarrow> prob0 2 v 0 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>1\<rangle>"
    show "prob0 2 v 0 = 1/2"
    proof -
      have "prob0 2 v 0 = (\<Sum>j\<in>{k| k::nat. (k<4) \<and> \<not> select_index 2 0 k}. (cmod(bell01 $$ (j,0)))\<^sup>2)"
        apply (auto simp: prob0_def asm).
      also have "\<dots> = (\<Sum>j\<in>{0,1}. (cmod(bell01 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        apply (auto simp: bell01_def ket_vec_def).
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<Longrightarrow> prob0 2 v 0 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>0\<rangle>"
    show "prob0 2 v 0 = 1/2"
    proof -
      have "prob0 2 v 0 = (\<Sum>j\<in>{k| k::nat. (k<4) \<and> \<not> select_index 2 0 k}. (cmod(bell10 $$ (j,0)))\<^sup>2)"
        apply (auto simp: prob0_def asm).
      also have "\<dots> = (\<Sum>j\<in>{0,1}. (cmod(bell10 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        apply (auto simp: bell10_def ket_vec_def).
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>1\<^sub>1\<rangle> \<Longrightarrow> prob0 2 v 0 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
    show "prob0 2 v 0 = 1/2"
    proof -
      have "prob0 2 v 0 = (\<Sum>j\<in>{k| k::nat. (k<4) \<and> \<not> select_index 2 0 k}. (cmod(bell11 $$ (j,0)))\<^sup>2)"
        apply (auto simp: prob0_def asm).
      also have "\<dots> = (\<Sum>j\<in>{0,1}. (cmod(bell11 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        apply (auto simp: bell11_def ket_vec_def).
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  ultimately show ?thesis using assms by auto
qed

lemma prob_1_bell_fst [simp]:
  assumes "v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
  shows "prob1 2 v 0 = 1/2" 
proof -
  have set_0 [simp]:"{k| k::nat. select_index 2 0 k} = {2,3}"
    using select_index_def by auto
  have "v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<Longrightarrow> prob1 2 v 0 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>0\<rangle>"
    show "prob1 2 v 0 = 1/2"
    proof -
      have "prob1 2 v 0 = (\<Sum>j\<in>{k| k::nat. select_index 2 0 k}. (cmod(bell00 $$ (j,0)))\<^sup>2)"
        apply (auto simp: prob1_def asm).
      also have "\<dots> = (\<Sum>j\<in>{2,3}. (cmod(bell00 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        apply (auto simp: bell00_def ket_vec_def).
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<Longrightarrow> prob1 2 v 0 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>1\<rangle>"
    show "prob1 2 v 0 = 1/2"
    proof -
      have "prob1 2 v 0 = (\<Sum>j\<in>{k| k::nat. select_index 2 0 k}. (cmod(bell01 $$ (j,0)))\<^sup>2)"
        apply (auto simp: prob1_def asm).
      also have "\<dots> = (\<Sum>j\<in>{2,3}. (cmod(bell01 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        apply (auto simp: bell01_def ket_vec_def).
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<Longrightarrow> prob1 2 v 0 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>0\<rangle>"
    show "prob1 2 v 0 = 1/2"
    proof -
      have "prob1 2 v 0 = (\<Sum>j\<in>{k| k::nat. select_index 2 0 k}. (cmod(bell10 $$ (j,0)))\<^sup>2)"
        apply (auto simp: prob1_def asm).
      also have "\<dots> = (\<Sum>j\<in>{2,3}. (cmod(bell10 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        apply (auto simp: bell10_def ket_vec_def).
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>1\<^sub>1\<rangle> \<Longrightarrow> prob1 2 v 0 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
    show "prob1 2 v 0 = 1/2"
    proof -
      have "prob1 2 v 0 = (\<Sum>j\<in>{k| k::nat. select_index 2 0 k}. (cmod(bell11 $$ (j,0)))\<^sup>2)"
        apply (auto simp: prob1_def asm).
      also have "\<dots> = (\<Sum>j\<in>{2,3}. (cmod(bell11 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        apply (auto simp: bell11_def ket_vec_def).
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  ultimately show ?thesis using assms by auto
qed

lemma prob0_bell_snd [simp]:
  assumes "v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
  shows "prob0 2 v 1 = 1/2" 
proof -
  have set_0 [simp]:"{k| k::nat. (k<4) \<and> \<not> select_index 2 1 k} = {0,2}"
    apply (auto simp: select_index_def)
    by (metis Suc_le_mono add_Suc add_Suc_right le_numeral_extra(3) less_antisym mod_Suc_eq mod_less 
neq0_conv not_mod2_eq_Suc_0_eq_0 numeral_2_eq_2 numeral_Bit0 one_add_one one_mod_two_eq_one one_neq_zero) 
  have "v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<Longrightarrow> prob0 2 v 1 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>0\<rangle>"
    show "prob0 2 v 1 = 1/2"
    proof -
      have "prob0 2 v 1 = (\<Sum>j\<in>{k| k::nat. (k<4) \<and> \<not> select_index 2 1 k}. (cmod(bell00 $$ (j,0)))\<^sup>2)"
        apply (auto simp: prob0_def asm).
      also have "\<dots> = (\<Sum>j\<in>{0,2}. (cmod(bell00 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        apply (auto simp: bell00_def ket_vec_def).
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<Longrightarrow> prob0 2 v 1 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>1\<rangle>"
    show "prob0 2 v 1 = 1/2"
    proof -
      have "prob0 2 v 1 = (\<Sum>j\<in>{k| k::nat. (k<4) \<and> \<not> select_index 2 1 k}. (cmod(bell01 $$ (j,0)))\<^sup>2)"
        apply (auto simp: prob0_def asm).
      also have "\<dots> = (\<Sum>j\<in>{0,2}. (cmod(bell01 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        apply (auto simp: bell01_def ket_vec_def).
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<Longrightarrow> prob0 2 v 1 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>0\<rangle>"
    show "prob0 2 v 1 = 1/2"
    proof -
      have "prob0 2 v 1 = (\<Sum>j\<in>{k| k::nat. (k<4) \<and> \<not> select_index 2 1 k}. (cmod(bell10 $$ (j,0)))\<^sup>2)"
        apply (auto simp: prob0_def asm).
      also have "\<dots> = (\<Sum>j\<in>{0,2}. (cmod(bell10 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        apply (auto simp: bell10_def ket_vec_def).
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>1\<^sub>1\<rangle> \<Longrightarrow> prob0 2 v 1 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
    show "prob0 2 v 1 = 1/2"
    proof -
      have "prob0 2 v 1 = (\<Sum>j\<in>{k| k::nat. (k<4) \<and> \<not> select_index 2 1 k}. (cmod(bell11 $$ (j,0)))\<^sup>2)"
        apply (auto simp: prob0_def asm).
      also have "\<dots> = (\<Sum>j\<in>{0,2}. (cmod(bell11 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        apply (auto simp: bell11_def ket_vec_def).
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  ultimately show ?thesis using assms by auto
qed

lemma prob_1_bell_snd [simp]:
  assumes "v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
  shows "prob1 2 v 1 = 1/2" 
proof -
  have set_0:"{k| k::nat. select_index 2 1 k} = {1,3}"
    apply (auto simp: select_index_def)
    by (metis Suc_le_lessD le_SucE le_less mod2_gr_0 mod_less mod_self numeral_2_eq_2 numeral_3_eq_3)
  have "v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<Longrightarrow> prob1 2 v 1 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>0\<rangle>"
    show "prob1 2 v 1 = 1/2"
    proof -
      have "prob1 2 v 1 = (\<Sum>j\<in>{k| k::nat. select_index 2 1 k}. (cmod(bell00 $$ (j,0)))\<^sup>2)"
        apply (auto simp: prob1_def asm).
      also have "\<dots> = (\<Sum>j\<in>{1,3}. (cmod(bell00 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        apply (auto simp: bell00_def ket_vec_def).
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<Longrightarrow> prob1 2 v 1 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>1\<rangle>"
    show "prob1 2 v 1 = 1/2"
    proof -
      have "prob1 2 v 1 = (\<Sum>j\<in>{k| k::nat. select_index 2 1 k}. (cmod(bell01 $$ (j,0)))\<^sup>2)"
        apply (auto simp: prob1_def asm).
      also have "\<dots> = (\<Sum>j\<in>{1,3}. (cmod(bell01 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        apply (auto simp: bell01_def ket_vec_def).
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<Longrightarrow> prob1 2 v 1 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>0\<rangle>"
    show "prob1 2 v 1 = 1/2"
    proof -
      have "prob1 2 v 1 = (\<Sum>j\<in>{k| k::nat. select_index 2 1 k}. (cmod(bell10 $$ (j,0)))\<^sup>2)"
        apply (auto simp: prob1_def asm).
      also have "\<dots> = (\<Sum>j\<in>{1,3}. (cmod(bell10 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        apply (auto simp: bell10_def ket_vec_def).
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>1\<^sub>1\<rangle> \<Longrightarrow> prob1 2 v 1 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
    show "prob1 2 v 1 = 1/2"
    proof -
      have "prob1 2 v 1 = (\<Sum>j\<in>{k| k::nat. select_index 2 1 k}. (cmod(bell11 $$ (j,0)))\<^sup>2)"
        apply (auto simp: prob1_def asm).
      also have "\<dots> = (\<Sum>j\<in>{1,3}. (cmod(bell11 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        apply (auto simp: bell11_def ket_vec_def).
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  ultimately show ?thesis using assms by auto
qed

lemma post_meas0_bell00_fst [simp]:
  "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 = |unit_vec 4 0\<rangle>"
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 0\<rangle>" and "j < dim_col |unit_vec 4 0\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0"
    by(auto simp add: ket_vec_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (0,0) = |unit_vec 4 0\<rangle> $$ (0,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (1,0) = |unit_vec 4 0\<rangle> $$ (1,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (2,0) = |unit_vec 4 0\<rangle> $$ (2,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (3,0) = |unit_vec 4 0\<rangle> $$ (3,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide) 
  ultimately show "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (i,j) = |unit_vec 4 0\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0) = dim_row |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
  show "dim_col (post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0) = dim_col |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
qed

lemma post_meas0_bell00_snd [simp]:
  "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 = |unit_vec 4 0\<rangle>"
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 0\<rangle>" and "j < dim_col |unit_vec 4 0\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (0,0) = |unit_vec 4 0\<rangle> $$ (0,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide del:One_nat_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (1,0) = |unit_vec 4 0\<rangle> $$ (1,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (2,0) = |unit_vec 4 0\<rangle> $$ (2,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (3,0) = |unit_vec 4 0\<rangle> $$ (3,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (i,j) = |unit_vec 4 0\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1) = dim_row |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
  show "dim_col (post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1) = dim_col |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
qed

lemma post_meas0_bell01_fst [simp]:
  "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 = |unit_vec 4 1\<rangle>"
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 1\<rangle>" and "j < dim_col |unit_vec 4 1\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (0,0) = |unit_vec 4 1\<rangle> $$ (0,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (1,0) = |unit_vec 4 1\<rangle> $$ (1,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (2,0) = |unit_vec 4 1\<rangle> $$ (2,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (3,0) = |unit_vec 4 1\<rangle> $$ (3,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (i,j) = |unit_vec 4 1\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0) = dim_row |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
  show "dim_col (post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0) = dim_col |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
qed

lemma post_meas0_bell01_snd [simp]:
  "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 = |unit_vec 4 2\<rangle>" 
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 2\<rangle>" and "j < dim_col |unit_vec 4 2\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (0,0) = |unit_vec 4 2\<rangle> $$ (0,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (1,0) = |unit_vec 4 2\<rangle> $$ (1,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (2,0) = |unit_vec 4 2\<rangle> $$ (2,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide del:One_nat_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (3,0) = |unit_vec 4 2\<rangle> $$ (3,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (i,j) = |unit_vec 4 2\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1) = dim_row |unit_vec 4 2\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
  show "dim_col (post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1) = dim_col |unit_vec 4 2\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
qed

lemma post_meas0_bell10_fst [simp]:
  "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 = |unit_vec 4 0\<rangle>" 
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 0\<rangle>" and "j < dim_col |unit_vec 4 0\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (0,0) = |unit_vec 4 0\<rangle> $$ (0,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (1,0) = |unit_vec 4 0\<rangle> $$ (1,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (2,0) = |unit_vec 4 0\<rangle> $$ (2,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (3,0) = |unit_vec 4 0\<rangle> $$ (3,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (i,j) = |unit_vec 4 0\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0) = dim_row |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
  show "dim_col (post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0) = dim_col |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
qed

lemma post_meas0_bell10_snd [simp]:
  "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 = |unit_vec 4 0\<rangle>" 
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 0\<rangle>" and "j < dim_col |unit_vec 4 0\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (0,0) = |unit_vec 4 0\<rangle> $$ (0,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide del:One_nat_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (1,0) = |unit_vec 4 0\<rangle> $$ (1,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (2,0) = |unit_vec 4 0\<rangle> $$ (2,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (3,0) = |unit_vec 4 0\<rangle> $$ (3,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (i,j) = |unit_vec 4 0\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1) = dim_row |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
  show "dim_col (post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1) = dim_col |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
qed

lemma post_meas0_bell11_fst [simp]:
  "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 = |unit_vec 4 1\<rangle>" 
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 1\<rangle>" and "j < dim_col |unit_vec 4 1\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0"  
    by(auto simp add: ket_vec_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (0,0) = |unit_vec 4 1\<rangle> $$ (0,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (1,0) = |unit_vec 4 1\<rangle> $$ (1,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (2,0) = |unit_vec 4 1\<rangle> $$ (2,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (3,0) = |unit_vec 4 1\<rangle> $$ (3,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (i,j) = |unit_vec 4 1\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0) = dim_row |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
  show "dim_col (post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0) = dim_col |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
qed

lemma post_meas0_bell11_snd [simp]:
  "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 = - |unit_vec 4 2\<rangle>" 
proof
  fix i j::nat assume "i < dim_row (- |unit_vec 4 2\<rangle>)" and "j < dim_col (- |unit_vec 4 2\<rangle>)"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (0,0) = (- |unit_vec 4 2\<rangle>) $$ (0,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (1,0) = (- |unit_vec 4 2\<rangle>) $$ (1,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (2,0) = (- |unit_vec 4 2\<rangle>) $$ (2,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide del:One_nat_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (3,0) = (- |unit_vec 4 2\<rangle>) $$ (3,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (i,j) = (- |unit_vec 4 2\<rangle>) $$ (i,j)" by auto
next
  show "dim_row (post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1) = dim_row (- |unit_vec 4 2\<rangle>)"
    by(auto simp add: post_meas0_def ket_vec_def)
  show "dim_col (post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1) = dim_col (- |unit_vec 4 2\<rangle>)"
    by(auto simp add: post_meas0_def ket_vec_def)
qed

lemma post_meas1_bell00_fst [simp]:
  "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 = |unit_vec 4 3\<rangle>" 
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 3\<rangle>" and "j < dim_col |unit_vec 4 3\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0"  
    by(auto simp add: ket_vec_def)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (0,0) = |unit_vec 4 3\<rangle> $$ (0,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (1,0) = |unit_vec 4 3\<rangle> $$ (1,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (2,0) = |unit_vec 4 3\<rangle> $$ (2,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (3,0) = |unit_vec 4 3\<rangle> $$ (3,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (i,j) = |unit_vec 4 3\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0) = dim_row |unit_vec 4 3\<rangle>"
    by(auto simp add: post_meas1_def ket_vec_def)
  show "dim_col (post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0) = dim_col |unit_vec 4 3\<rangle>"
    by(auto simp add: post_meas1_def ket_vec_def)
qed

lemma post_meas1_bell00_snd [simp]:
  "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 = |unit_vec 4 3\<rangle>" 
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 3\<rangle>" and "j < dim_col |unit_vec 4 3\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (0,0) = |unit_vec 4 3\<rangle> $$ (0,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (1,0) = |unit_vec 4 3\<rangle> $$ (1,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (2,0) = |unit_vec 4 3\<rangle> $$ (2,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (3,0) = |unit_vec 4 3\<rangle> $$ (3,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide del: One_nat_def)
  ultimately show "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (i,j) = |unit_vec 4 3\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1) = dim_row |unit_vec 4 3\<rangle>"
    by(auto simp add: post_meas1_def ket_vec_def)
  show "dim_col (post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1) = dim_col |unit_vec 4 3\<rangle>"
    by(auto simp add: post_meas1_def ket_vec_def)
qed

lemma post_meas1_bell01_fst [simp]:
  "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 = |unit_vec 4 2\<rangle>" 
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 2\<rangle>" and "j < dim_col |unit_vec 4 2\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (0,0) = |unit_vec 4 2\<rangle> $$ (0,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (1,0) = |unit_vec 4 2\<rangle> $$ (1,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (2,0) = |unit_vec 4 2\<rangle> $$ (2,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (3,0) = |unit_vec 4 2\<rangle> $$ (3,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (i,j) = |unit_vec 4 2\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0) = dim_row |unit_vec 4 2\<rangle>"
    by(auto simp add: post_meas1_def ket_vec_def)
  show "dim_col (post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0) = dim_col |unit_vec 4 2\<rangle>"
    by(auto simp add: post_meas1_def ket_vec_def)
qed

lemma post_meas1_bell01_snd [simp]:
  "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 = |unit_vec 4 1\<rangle>" 
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 1\<rangle>" and "j < dim_col |unit_vec 4 1\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (0,0) = |unit_vec 4 1\<rangle> $$ (0,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (1,0) = |unit_vec 4 1\<rangle> $$ (1,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide del: One_nat_def)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (2,0) = |unit_vec 4 1\<rangle> $$ (2,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (3,0) = |unit_vec 4 1\<rangle> $$ (3,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (i,j) = |unit_vec 4 1\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1) = dim_row |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas1_def ket_vec_def)
  show "dim_col (post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1) = dim_col |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas1_def ket_vec_def)
qed

lemma post_meas1_bell10_fst [simp]:
  "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 = - |unit_vec 4 3\<rangle>" 
proof
  fix i j::nat assume "i < dim_row (- |unit_vec 4 3\<rangle>)" and "j < dim_col (- |unit_vec 4 3\<rangle>)"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (0,0) = (- |unit_vec 4 3\<rangle>) $$ (0,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (1,0) = (- |unit_vec 4 3\<rangle>) $$ (1,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (2,0) = (- |unit_vec 4 3\<rangle>) $$ (2,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (3,0) = (- |unit_vec 4 3\<rangle>) $$ (3,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (i,j) = (- |unit_vec 4 3\<rangle>) $$ (i,j)" by auto
next
  show "dim_row (post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0) = dim_row (- |unit_vec 4 3\<rangle>)"
    by(auto simp add: post_meas1_def ket_vec_def)
  show "dim_col (post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0) = dim_col (- |unit_vec 4 3\<rangle>)"
    by(auto simp add: post_meas1_def ket_vec_def)
qed

lemma post_meas1_bell10_snd [simp]:
  "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 = - |unit_vec 4 3\<rangle>" 
proof
  fix i j::nat assume "i < dim_row (- |unit_vec 4 3\<rangle>)" and "j < dim_col (- |unit_vec 4 3\<rangle>)"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (0,0) = (- |unit_vec 4 3\<rangle>) $$ (0,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (1,0) = (- |unit_vec 4 3\<rangle>) $$ (1,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (2,0) = (- |unit_vec 4 3\<rangle>) $$ (2,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (3,0) = (- |unit_vec 4 3\<rangle>) $$ (3,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide del: One_nat_def)
  ultimately show "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (i,j) = (- |unit_vec 4 3\<rangle>) $$ (i,j)" by auto    
next
  show "dim_row (post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1) = dim_row (- |unit_vec 4 3\<rangle>)"
    by(auto simp add: post_meas1_def ket_vec_def)
  show "dim_col (post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1) = dim_col (- |unit_vec 4 3\<rangle>)"
    by(auto simp add: post_meas1_def ket_vec_def)
qed

lemma post_meas1_bell11_fst [simp]:
  "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 = - |unit_vec 4 2\<rangle>" 
proof
  fix i j::nat assume "i < dim_row (- |unit_vec 4 2\<rangle>)" and "j < dim_col (- |unit_vec 4 2\<rangle>)"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (0,0) = (- |unit_vec 4 2\<rangle>) $$ (0,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (1,0) = (- |unit_vec 4 2\<rangle>) $$ (1,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (2,0) = (- |unit_vec 4 2\<rangle>) $$ (2,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (3,0) = (- |unit_vec 4 2\<rangle>) $$ (3,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (i,j) = (- |unit_vec 4 2\<rangle>) $$ (i,j)" by auto    
next
  show "dim_row (post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0) = dim_row (- |unit_vec 4 2\<rangle>)"
    by(auto simp add: post_meas1_def ket_vec_def)
  show "dim_col (post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0) = dim_col (- |unit_vec 4 2\<rangle>)"
    by(auto simp add: post_meas1_def ket_vec_def)
qed

lemma post_meas1_bell11_snd [simp]:
  "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 = |unit_vec 4 1\<rangle>" 
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 1\<rangle>" and "j < dim_col |unit_vec 4 1\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0"  
    by(auto simp add: ket_vec_def)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (0,0) = |unit_vec 4 1\<rangle> $$ (0,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (1,0) = |unit_vec 4 1\<rangle> $$ (1,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide del: One_nat_def)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (2,0) = |unit_vec 4 1\<rangle> $$ (2,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (3,0) = |unit_vec 4 1\<rangle> $$ (3,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (i,j) = |unit_vec 4 1\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1) = dim_row |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas1_def ket_vec_def)
  show "dim_col (post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1) = dim_col |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas1_def ket_vec_def)
qed


(*
Biblio:

@book{MikeandIke,
  author = {Nielsen, Michael A. and Chuang, Isaac L.},
  publisher = {Cambridge University Press},
  title = {Quantum Computation and Quantum Information},
  year = 2010
}
*)

end
