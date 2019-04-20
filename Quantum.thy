(* Authors: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk, 
           
            Yijun He, University of Cambridge, yh403@cam.ac.uk
*)

theory Quantum
imports 
  Main 
  HOL.Power 
  HOL.Real 
  HOL.Complex 
  Jordan_Normal_Form.Matrix
  "HOL-Library.Nonpos_Ints"
  VectorSpace.VectorSpace
  "HOL-Algebra.Ring"
  VectorSpace.LinearCombinations
  HOL.Transcendental
begin

section \<open>Qubits and Quantum Gates\<close>

subsection \<open>Qubits\<close>

text\<open>In this theory "cpx" stands for "complex"\<close>

definition cpx_vec_length :: "complex vec \<Rightarrow> real" ("\<parallel>_\<parallel>") where
"cpx_vec_length v \<equiv> sqrt(\<Sum>i< dim_vec v.(cmod (vec_index v i))\<^sup>2)"

lemma norm_vec_index_unit_vec_is_0:
  assumes "j < n" and "j \<noteq> i"
  shows "cmod (vec_index (unit_vec n i) j) = 0"
  using assms
  by (simp add: unit_vec_def)

lemma norm_vec_index_unit_vec_is_1:
  assumes "j < n" and "j = i"
  shows "cmod (vec_index (unit_vec n i) j) = 1"
proof-
  have f1:"vec_index (unit_vec n i) j = 1"
    using assms 
    by simp
  thus ?thesis
    using cmod_def
    by (simp add: f1)
qed

lemma unit_cpx_vec_length:
  assumes "i < n"
  shows "\<parallel>unit_vec n i\<parallel> = 1"
proof-
  have f1:"(\<Sum>j<n. (cmod(vec_index (unit_vec n i) j))\<^sup>2) = (\<Sum>j<n. if j = i then 1 else 0)"
    using norm_vec_index_unit_vec_is_0 norm_vec_index_unit_vec_is_1
    by (smt lessThan_iff one_power2 sum.cong zero_power2) 
  also have "(\<Sum>j<n. if j = i then 1 else 0) = 1"
    using assms  
    by simp
  then have "(\<Sum>j<n. (cmod(vec_index (unit_vec n i) j))\<^sup>2) = 1"
    using f1 
    by simp
  then have "sqrt (\<Sum>j<n. (cmod(vec_index (unit_vec n i) j))\<^sup>2) = 1" 
    by simp
  thus ?thesis
    using cpx_vec_length_def 
    by simp
qed

locale state =
  fixes n:: nat and v:: "complex mat"
  assumes "dim_col v = 1"
    and "dim_row v = 2^n"
    and "\<parallel>col v 0\<parallel> = 1"

text\<open> 
Below the natural number n codes for the dimension of the complex vector space whose elements of norm
1 we call states 
\<close>

lemma unit_vec_of_right_length_is_state:
  assumes "i < 2^n"
  shows "unit_vec (2^n) i \<in> {v| n v::complex vec. dim_vec v = 2^n \<and> \<parallel>v\<parallel> = 1}"
proof-
  have f1:"dim_vec (unit_vec (2^n) i) = 2^n" 
    by simp
  have f2:"\<parallel>unit_vec (2^n) i\<parallel> = 1"
    using assms unit_cpx_vec_length
    by simp
  thus "unit_vec (2^n) i \<in> {v| n v::complex vec. dim_vec v = 2^n \<and> \<parallel>v\<parallel> = 1}"
    using f1 f2 
    by simp
qed


definition state_qbit:: "nat \<Rightarrow> complex vec set" where
"state_qbit n \<equiv> {v| v:: complex vec. dim_vec v = 2^n \<and> \<parallel>v\<parallel> = 1}"

lemma state_to_state_qbit:
  assumes "state n v"
  shows "col v 0 \<in> state_qbit n"
  using assms state_def state_qbit_def 
  by simp

subsection "The Hermitian Conjugation"

text\<open>The Hermitian conjugate of a complex matrix is the complex conjugate of its transpose\<close>

definition hermite_cnj :: "complex mat \<Rightarrow> complex mat" ("_\<^sup>\<dagger>") where
  "hermite_cnj M \<equiv> Matrix.mat (dim_col M) (dim_row M) (\<lambda> (i,j). cnj(M $$ (j,i)))"

text\<open>We introduce the type of complex square matrices\<close>

typedef cpx_sqr_mat = "{M | M::complex mat. square_mat M}"
proof-
  have "square_mat (1\<^sub>m n)" for n
    using one_mat_def 
    by simp
  thus ?thesis
    by blast
qed

definition cpx_sqr_mat_to_cpx_mat :: "cpx_sqr_mat \<Rightarrow> complex mat" where
"cpx_sqr_mat_to_cpx_mat M \<equiv> Rep_cpx_sqr_mat M"

text \<open>We introduce a coercion from the type of complex square matrices to the type of complex 
matrices\<close>

declare [[coercion cpx_sqr_mat_to_cpx_mat]]

lemma hermite_cnj_dim_row:
  shows "dim_row (M\<^sup>\<dagger>) = dim_col M"
  using hermite_cnj_def 
  by simp

lemma hermite_cnj_dim_col:
  shows "dim_col (M\<^sup>\<dagger>) = dim_row M"
  using hermite_cnj_def
  by simp

lemma col_hermite_cnj:
  fixes M::"complex mat"
  assumes "j < dim_row M"
  shows "col (M\<^sup>\<dagger>) j = vec (dim_col M) (\<lambda>i. cnj (M $$ (j,i)))"
  using assms col_def hermite_cnj_def 
  by simp

lemma row_hermite_cnj:
  fixes M::"complex mat"
  assumes "i < dim_col M"
  shows "row (M\<^sup>\<dagger>) i = vec (dim_row M) (\<lambda>j. cnj (M $$ (j,i)))"
  using assms row_def hermite_cnj_def 
  by simp

lemma hermite_cnj_of_sqr_is_sqr:
  shows "square_mat ((M::cpx_sqr_mat)\<^sup>\<dagger>)"
proof-
  have "square_mat M"
    using cpx_sqr_mat_to_cpx_mat_def Rep_cpx_sqr_mat 
    by auto
  then have "dim_row M = dim_col M" 
    by simp
  then have "dim_col (M\<^sup>\<dagger>) = dim_row (M\<^sup>\<dagger>)"
    using hermite_cnj_dim_col hermite_cnj_dim_row 
    by simp
  thus "square_mat (M\<^sup>\<dagger>)" 
    by simp
qed

lemma hermite_cnj_of_id_is_id:
  shows "(1\<^sub>m n)\<^sup>\<dagger> = 1\<^sub>m n"
  using hermite_cnj_def one_mat_def 
  by auto


subsection "Unitary Matrices and Quantum Gates"

definition unitary :: "complex mat \<Rightarrow> bool" where
"unitary M \<equiv> (M\<^sup>\<dagger>) * M = 1\<^sub>m (dim_col M) \<and> M * (M\<^sup>\<dagger>) = 1\<^sub>m (dim_row M)"

lemma id_is_unitary:
  shows "unitary (1\<^sub>m n)"
  using unitary_def hermite_cnj_of_id_is_id 
  by simp

locale gate =
  fixes n:: nat and A :: "complex mat"
  assumes "dim_row A = 2^n"
    and "square_mat A"
    and "unitary A"


text\<open>We prove that a quantum gate is invertible and its inverse is given by its Hermitian conjugate\<close>

lemma mat_unitary_mat:
  fixes M::"complex mat"
  assumes "unitary M"
  shows "inverts_mat M (M\<^sup>\<dagger>)"
  using assms inverts_mat_def unitary_def
  by auto

lemma unitary_mat_mat:
  fixes M::"complex mat"
  assumes "unitary M"
  shows "inverts_mat (M\<^sup>\<dagger>) M"
  using assms unitary_def
  by (simp add: inverts_mat_def hermite_cnj_dim_row)

lemma (in gate) gate_is_inv:
  shows "invertible_mat A"
  using gate_def gate_axioms invertible_mat_def mat_unitary_mat unitary_mat_mat 
  by blast

subsection 
"Relations Between Complex Conjugation, Hermitian Conjugation, Transposition and Unitarity"

syntax
  "transpose_mat" :: "'a mat => 'a mat"
      ("(_\<^sup>t)")

lemma col_tranpose:
  fixes M::"'a mat"
  assumes "dim_row M = n" and "i < n"
  shows "col (M\<^sup>t) i = row M i"
proof-
  have "dim_vec (col (M\<^sup>t) i) = dim_vec (row M i)"
    using row_def col_def transpose_mat_def 
    by simp
  thus ?thesis
    using assms eq_vecI col_def row_def transpose_mat_def 
    by auto
qed

lemma row_transpose:
  fixes M::"'a mat"
  assumes "dim_col M = n" and "i < n"
  shows "row (M\<^sup>t) i = col M i"
  using assms col_transpose transpose_transpose 
  by simp

definition cpx_mat_cnj :: "complex mat \<Rightarrow> complex mat" ("(_\<^sup>\<star>)") where
"cpx_mat_cnj M \<equiv> Matrix.mat (dim_row M) (dim_col M) (\<lambda>(i,j). cnj (M $$ (i,j)))"

lemma cpx_mat_cnj_id:
  fixes n::"nat"
  shows "(1\<^sub>m n)\<^sup>\<star> = 1\<^sub>m n"
  using cpx_mat_cnj_def one_mat_def 
  by auto

lemma cpx_mat_cnj_cnj:
  fixes M::"complex mat"
  shows "(M\<^sup>\<star>)\<^sup>\<star> = M"
  using eq_matI cpx_mat_cnj_def 
  by auto

lemma cpx_mat_cnj_prod:
  fixes M N::"complex mat"
  assumes "dim_col M = dim_row N"
  shows "(M * N)\<^sup>\<star> = (M\<^sup>\<star>) * (N\<^sup>\<star>)"
proof-
  have f1:"dim_row ((M * N)\<^sup>\<star>) = dim_row ((M\<^sup>\<star>) * (N\<^sup>\<star>))"
    using cpx_mat_cnj_def 
    by simp
  have f2:"dim_col ((M * N)\<^sup>\<star>) = dim_col ((M\<^sup>\<star>) * (N\<^sup>\<star>))"
    using cpx_mat_cnj_def
    by simp
  have "i < dim_row M \<longrightarrow> j < dim_col N \<longrightarrow> ((M * N)\<^sup>\<star>) $$ (i,j) = 
    cnj (\<Sum>k=0..<(dim_row N). M $$ (i,k) * N $$ (k,j))" for i j
    using cpx_mat_cnj_def index_mat times_mat_def scalar_prod_def row_def col_def
    by (smt assms case_prod_conv dim_col index_mult_mat(2) index_mult_mat(3) index_vec lessThan_atLeast0 
        lessThan_iff sum.cong)
  then have f3:"i < dim_row M \<longrightarrow> j < dim_col N \<longrightarrow> ((M * N)\<^sup>\<star>) $$ (i,j) = 
    (\<Sum>k=0..<(dim_row N). cnj(M $$ (i,k)) * cnj(N $$ (k,j)))" for i j
    using cnj_sum complex_cnj_mult 
    by simp
  have f4:"i < dim_row M \<longrightarrow> j < dim_col N \<longrightarrow> ((M\<^sup>\<star>) * (N\<^sup>\<star>)) $$ (i,j) = 
    (\<Sum>k=0..<(dim_row N). cnj(M $$ (i,k)) * cnj(N $$ (k,j)))" for i j
    using cpx_mat_cnj_def index_mat times_mat_def scalar_prod_def row_def col_def
    by (smt assms case_prod_conv dim_col dim_col_mat(1) dim_row_mat(1) index_vec lessThan_atLeast0 
        lessThan_iff sum.cong)
  thus ?thesis
    using assms eq_matI f1 f2 f3 f4 cpx_mat_cnj_def 
    by auto
qed

lemma transpose_cnj:
  fixes M::"complex mat"
  shows "(M\<^sup>t)\<^sup>\<star> = (M\<^sup>\<dagger>)"
proof-
  have f1:"dim_row ((M\<^sup>t)\<^sup>\<star>) = dim_row (M\<^sup>\<dagger>)"
    using cpx_mat_cnj_def transpose_mat_def hermite_cnj_def 
    by simp
  have f2:"dim_col ((M\<^sup>t)\<^sup>\<star>) = dim_col (M\<^sup>\<dagger>)"
    using cpx_mat_cnj_def transpose_mat_def hermite_cnj_def 
    by simp
  thus ?thesis
    using eq_matI f1 f2 cpx_mat_cnj_def transpose_mat_def hermite_cnj_def 
    by auto
qed

lemma cnj_transpose:
  fixes M::"complex mat"
  shows "(M\<^sup>\<star>)\<^sup>t = (M\<^sup>\<dagger>)"
proof-
  have f1:"dim_row ((M\<^sup>\<star>)\<^sup>t) = dim_row (M\<^sup>\<dagger>)"
    using transpose_mat_def cpx_mat_cnj_def hermite_cnj_def 
    by simp
  have f2:"dim_col ((M\<^sup>\<star>)\<^sup>t) = dim_col (M\<^sup>\<dagger>)"
    using transpose_mat_def cpx_mat_cnj_def hermite_cnj_def 
    by simp
  thus ?thesis
    using eq_matI f1 f2 transpose_mat_def cpx_mat_cnj_def hermite_cnj_def 
    by auto
qed

lemma transpose_hermite_cnj:
  fixes M::"complex mat"
  shows "(M\<^sup>t)\<^sup>\<dagger> = (M\<^sup>\<star>)"
  using transpose_transpose transpose_cnj
  by metis

lemma transpose_of_unitary_is_unitary:
  fixes U::"complex mat"
  assumes "unitary U"
  shows "unitary (U\<^sup>t)"
proof-
  have c1:"(U\<^sup>t)\<^sup>\<dagger> * (U\<^sup>t) =  1\<^sub>m(dim_row U)"
  proof-
    have f1:"(U\<^sup>t)\<^sup>\<dagger> * (U\<^sup>t) = (U\<^sup>\<star>) * (U\<^sup>t)"
      using transpose_hermite_cnj 
      by simp
    have "dim_col U = dim_row ((U\<^sup>t)\<^sup>\<star>)"
      using cpx_mat_cnj_def transpose_mat_def 
      by auto
    then have "(U\<^sup>t)\<^sup>\<dagger> * (U\<^sup>t) = ((U * ((U\<^sup>t)\<^sup>\<star>))\<^sup>\<star>)"
      using f1 cpx_mat_cnj_cnj cpx_mat_cnj_prod 
      by simp
    then have "(U\<^sup>t)\<^sup>\<dagger> * (U\<^sup>t) = ((U * (U\<^sup>\<dagger>))\<^sup>\<star>)"
      using transpose_cnj 
      by simp
    thus ?thesis
      using assms cpx_mat_cnj_id unitary_def 
      by auto
  qed
  have c2:"U\<^sup>t * ((U\<^sup>t)\<^sup>\<dagger>) = 1\<^sub>m(dim_col U)"
  proof-
    have f1:"U\<^sup>t * ((U\<^sup>t)\<^sup>\<dagger>) = (U\<^sup>t) * (U\<^sup>\<star>)"
      using transpose_hermite_cnj 
      by simp
    have "dim_col ((U\<^sup>t)\<^sup>\<star>) = dim_row U"
      using cpx_mat_cnj_def transpose_mat_def 
      by simp
    then have "U\<^sup>t * ((U\<^sup>t)\<^sup>\<dagger>) = (((U\<^sup>t)\<^sup>\<star> * U)\<^sup>\<star>)"
      using f1 cpx_mat_cnj_cnj cpx_mat_cnj_prod 
      by simp
    then have "U\<^sup>t * ((U\<^sup>t)\<^sup>\<dagger>) = ((U\<^sup>\<dagger> * U)\<^sup>\<star>)"
      using transpose_cnj 
      by simp
    thus ?thesis
      using assms unitary_def cpx_mat_cnj_id 
      by simp
  qed
  thus ?thesis
    using unitary_def c1 c2 
    by simp
qed


subsection "The Inner Product"

text\<open>Now, we introduce a coercion between complex vectors and (column) complex matrices\<close>

definition ket_vec :: "complex vec \<Rightarrow> complex mat" ("|_\<rangle>") where
"ket_vec v \<equiv> Matrix.mat (dim_vec v) 1 (\<lambda>(i,j). v $ i)"

lemma ket_vec_col:
  fixes v::"complex vec"
  shows "col |v\<rangle> 0 = v"
  using col_def ket_vec_def index_mat eq_vecI
  by auto

lemma smult_ket_vec:
  fixes v::"complex vec" and x::"complex"
  shows "|x \<cdot>\<^sub>v v\<rangle> = x \<cdot>\<^sub>m |v\<rangle>"
  using ket_vec_def 
  by auto

declare [[coercion ket_vec]]

definition row_vec :: "complex vec \<Rightarrow> complex mat" where
"row_vec v \<equiv> Matrix.mat 1 (dim_vec v) (\<lambda>(i,j). v $ j)" 

definition mat_cnj :: "complex mat \<Rightarrow> complex mat" where
"mat_cnj M \<equiv> Matrix.mat (dim_row M) (dim_col M) (\<lambda>(i,j). cnj (M $$ (i,j)))"

definition bra_vec :: "complex vec \<Rightarrow> complex mat" where
"bra_vec v \<equiv> mat_cnj (row_vec v)"

lemma row_bra_vec:
  fixes v::"complex vec"
  shows "row (bra_vec v) 0 = vec (dim_vec v) (\<lambda>i. cnj(v $ i))"
  using row_def bra_vec_def mat_cnj_def index_mat row_vec_def 
  by auto

text\<open> 
We introduce a definition called bra to take the corresponding bra of a vector when this last
vector is given under its matrix representation, i.e. as a column matrix 
\<close>

definition bra :: "complex mat \<Rightarrow> complex mat" ("\<langle>_|") where
"bra v \<equiv> Matrix.mat 1 (dim_row v) (\<lambda>(i,j). cnj(v $$ (j,i)))"

text\<open>The relation between bra, bra_vec and ket_vec is given as follows.\<close>

lemma bra_bra_vec:
  fixes v::"complex vec"
  shows "bra (ket_vec v) = bra_vec v"
  using cong_mat bra_def ket_vec_def bra_vec_def mat_cnj_def row_vec_def
  by auto

lemma row_bra:
  fixes v::"complex vec"
  shows "row \<langle>v| 0 = vec (dim_vec v) (\<lambda>i. cnj (v $ i))"
  using bra_bra_vec row_bra_vec 
  by simp

text\<open>We introduce the inner product of two complex vectors in C^n.\<close>

definition inner_prod :: "complex vec \<Rightarrow> complex vec \<Rightarrow> complex" ("\<langle>_|_\<rangle>") where
"inner_prod u v \<equiv> \<Sum> i \<in> {0 ..< dim_vec v}. cnj(u $ i) * (v $ i)"

lemma inner_prod_with_row_bra_vec:
  fixes u::"complex vec" and v::"complex vec"
  assumes "dim_vec u = dim_vec v"
  shows "\<langle>u|v\<rangle> = row (bra_vec u) 0 \<bullet> v"
  using assms inner_prod_def scalar_prod_def row_bra_vec index_vec
  by (smt lessThan_atLeast0 lessThan_iff sum.cong)

lemma inner_prod_with_row_bra_vec_col_ket_vec:
  fixes u::"complex vec" and v::"complex vec"
  assumes "dim_vec u = dim_vec v"
  shows "\<langle>u|v\<rangle> = (row \<langle>u| 0) \<bullet> (col |v\<rangle> 0)"
  using assms inner_prod_def index_vec row_bra_vec ket_vec_col
  by (simp add: scalar_prod_def bra_bra_vec)

lemma inner_prod_with_times_mat:
  fixes u::"complex vec" and v::"complex vec"
  assumes "dim_vec u = dim_vec v"
  shows "\<langle>u|v\<rangle> = (\<langle>u| * |v\<rangle>) $$ (0,0)"
  using assms inner_prod_def times_mat_def index_mat ket_vec_def bra_def 
    inner_prod_with_row_bra_vec_col_ket_vec 
  by auto

lemma orthogonal_unit_vec:
  assumes "i < n" and "j < n" and "i \<noteq> j"
  shows "\<langle>unit_vec n i|unit_vec n j\<rangle> = 0"
proof-
  have "\<langle>unit_vec n i|unit_vec n j\<rangle> = unit_vec n i \<bullet> unit_vec n j"
    using assms unit_vec_def inner_prod_def scalar_prod_def
    by (smt complex_cnj_zero index_unit_vec(3) index_vec inner_prod_with_row_bra_vec row_bra_vec 
        scalar_prod_right_unit)
  thus ?thesis
    using assms scalar_prod_def unit_vec_def 
    by simp
qed

text\<open>We prove that our inner product is linear in its second argument\<close>

lemma vec_index_is_linear:
  fixes u::"complex vec" and v::"complex vec" and k::"complex" and l::"complex"
  assumes "dim_vec u = dim_vec v" and "j < dim_vec u"
  shows "(k \<cdot>\<^sub>v u + l \<cdot>\<^sub>v v) $ j = k * (u $ j) + l * (v $ j)"
  using assms vec_index_def smult_vec_def plus_vec_def 
  by simp

lemma inner_prod_is_linear:
  fixes u::"complex vec" and v::"nat \<Rightarrow> complex vec" and l::"nat \<Rightarrow> complex"
  assumes "\<forall>i\<in>{0, 1}. dim_vec u = dim_vec (v i)"
  shows "\<langle>u|l 0 \<cdot>\<^sub>v v 0 + l 1 \<cdot>\<^sub>v v 1\<rangle> = (\<Sum>i\<le>1. l i * \<langle>u|v i\<rangle>)"
proof-
  have f1:"dim_vec (l 0 \<cdot>\<^sub>v v 0 + l 1 \<cdot>\<^sub>v v 1) = dim_vec u"
    using assms 
    by simp
  then have "\<langle>u|l 0 \<cdot>\<^sub>v v 0 + l 1 \<cdot>\<^sub>v v 1\<rangle> = (\<Sum> i \<in> {0 ..< dim_vec u}. cnj (u $ i) * ((l 0 \<cdot>\<^sub>v v 0 + l 1 \<cdot>\<^sub>v v 1) $ i))"
    using inner_prod_def 
    by simp
  then have "\<langle>u|l 0 \<cdot>\<^sub>v v 0 + l 1 \<cdot>\<^sub>v v 1\<rangle> = 
    (\<Sum> i \<in> {0 ..< dim_vec u}. cnj (u $ i) * (l 0 * v 0 $ i + l 1 * v 1 $ i))"
    using assms vec_index_is_linear
    by simp
  then have "\<langle>u|l 0 \<cdot>\<^sub>v v 0 + l 1 \<cdot>\<^sub>v v 1\<rangle> = 
    l 0 * (\<Sum> i \<in> {0 ..< dim_vec u}. cnj(u $ i) * (v 0 $ i)) + l 1 * (\<Sum> i \<in> {0 ..< dim_vec u}. cnj(u $ i) * (v 1 $ i))"
    using distrib_left ab_semigroup_mult.mult_commute
    by (smt mult_hom.hom_sum semiring_normalization_rules(19) sum.cong sum.distrib)
  then have "\<langle>u|l 0 \<cdot>\<^sub>v v 0 + l 1 \<cdot>\<^sub>v v 1\<rangle> = l 0 * \<langle>u|v 0\<rangle> + l 1 * \<langle>u|v 1\<rangle>"
    using assms inner_prod_def 
    by auto
  thus ?thesis 
    by simp
qed

lemma inner_prod_cnj:
  fixes u::"complex vec" and v::"complex vec"
  assumes "dim_vec u = dim_vec v"
  shows "\<langle>v|u\<rangle> = cnj (\<langle>u|v\<rangle>)"
  using assms inner_prod_def complex_cnj_cnj complex_cnj_mult cnj_sum
  by (smt semiring_normalization_rules(7) sum.cong)

lemma inner_prod_with_itself_Im:
  fixes u::"complex vec"
  shows "Im (\<langle>u|u\<rangle>) = 0"
  using inner_prod_cnj
  by (metis Reals_cnj_iff complex_is_Real_iff)

lemma inner_prod_with_itself_real:
  fixes u::"complex vec"
  shows "\<langle>u|u\<rangle> \<in> \<real>"
  using inner_prod_with_itself_Im
  by (simp add: complex_is_Real_iff)

lemma inner_prod_with_itself_eq0:
  fixes u::"complex vec"
  assumes "u = 0\<^sub>v (dim_vec u)"
  shows "\<langle>u|u\<rangle> = 0"
  using assms inner_prod_def zero_vec_def
  by (smt atLeastLessThan_iff complex_cnj_zero index_zero_vec(1) mult_zero_left sum.neutral)

lemma inner_prod_with_itself_Re:
  fixes u::"complex vec"
  shows "Re (\<langle>u|u\<rangle>) \<ge> 0"
proof-
  have "Re (\<langle>u|u\<rangle>) = (\<Sum>i<dim_vec u. Re (cnj(u $ i) * (u $ i)))"
    using inner_prod_def Re_sum
    by (simp add: lessThan_atLeast0)
  then have "Re (\<langle>u|u\<rangle>) = (\<Sum>i<dim_vec u. (Re (u $ i))\<^sup>2 + (Im (u $ i))\<^sup>2)"
    using complex_mult_cnj
    by (metis (no_types, lifting) Re_complex_of_real semiring_normalization_rules(7) sum.cong)
  thus "Re (\<langle>u|u\<rangle>) \<ge> 0"
    by (simp add: sum_nonneg)
qed

lemma inner_prod_with_itself_nonneg_reals:
  fixes u::"complex vec"
  shows "\<langle>u|u\<rangle> \<in> nonneg_Reals"
  using inner_prod_with_itself_real inner_prod_with_itself_Re nonneg_Reals_def
  by (simp add: complex_nonneg_Reals_iff inner_prod_with_itself_Im)

lemma inner_prod_with_itself_Re_non0:
  fixes u::"complex vec"
  assumes "u \<noteq> 0\<^sub>v (dim_vec u)"
  shows "Re (\<langle>u|u\<rangle>) > 0"
proof-
  obtain i where a1:"i < dim_vec u" and "u $ i \<noteq> 0"
    using assms zero_vec_def
    by (metis dim_vec eq_vecI index_zero_vec(1))
  then have f1:"Re (cnj (u $ i) * (u $ i)) > 0"
    by (metis Re_complex_of_real complex_mult_cnj complex_neq_0 mult.commute)
  have f2:"Re (\<langle>u|u\<rangle>) = (\<Sum>i<dim_vec u. Re (cnj(u $ i) * (u $ i)))"
    using inner_prod_def Re_sum
    by (simp add: lessThan_atLeast0)
  have f3:"\<forall>i < dim_vec u. Re (cnj(u $ i) * (u $ i)) \<ge> 0"
    using complex_mult_cnj
    by simp
  thus ?thesis
    using a1 f1 f2 f3 inner_prod_def lessThan_iff
    by (metis (no_types, lifting) finite_lessThan sum_pos2)
qed

lemma inner_prod_with_itself_nonneg_reals_non0:
  fixes u::"complex vec"
  assumes "u \<noteq> 0\<^sub>v (dim_vec u)"
  shows "\<langle>u|u\<rangle> \<in> nonneg_Reals" and "\<langle>u|u\<rangle> \<noteq> 0"
proof-
  show "\<langle>u|u\<rangle> \<in> nonneg_Reals"
    using inner_prod_with_itself_nonneg_reals 
    by simp
  show "\<langle>u|u\<rangle> \<noteq> 0"
    using assms inner_prod_with_itself_Re_non0
    by fastforce
qed

text\<open>We declare a coercion from real numbers to complex numbers\<close>

declare [[coercion complex_of_real]]

lemma cpx_vec_length_inner_prod:
  fixes v::"complex vec"
  shows "\<parallel>v\<parallel>\<^sup>2 = \<langle>v|v\<rangle>"
proof-
  have "\<parallel>v\<parallel>\<^sup>2 = (\<Sum>i < dim_vec v.(cmod (v $ i))\<^sup>2)"
    using cpx_vec_length_def complex_of_real_def
    by (metis (no_types, lifting) real_sqrt_power real_sqrt_unique sum_nonneg zero_le_power2)
  then have "\<parallel>v\<parallel>\<^sup>2 = (\<Sum>i < dim_vec v. cnj (v $ i) * (v $ i))"
    using complex_norm_square mult.commute
    by (smt of_real_sum sum.cong)
  thus ?thesis
    using inner_prod_def
    by (simp add: lessThan_atLeast0)
qed

lemma inner_prod_csqrt:
  fixes v::"complex vec"
  shows "csqrt \<langle>v|v\<rangle> = \<parallel>v\<parallel>"
  using inner_prod_with_itself_Re inner_prod_with_itself_Im csqrt_of_real_nonneg cpx_vec_length_def
  by (metis (no_types, lifting) Re_complex_of_real cpx_vec_length_inner_prod real_sqrt_ge_0_iff 
      real_sqrt_unique sum_nonneg zero_le_power2)


subsection "Unitary Matrices and Length-preservation"

(* The bra-vector \<langle>Av| is given by \<langle>v|A\<^sup>\<dagger> *)

lemma bra_mat_on_vec:
  fixes v::"complex vec" and A::"complex mat"
  assumes "dim_col A = dim_vec v"
  shows "\<langle>A * v| = \<langle>v| * (A\<^sup>\<dagger>)"
proof-
  have f1:"dim_row \<langle>A * v| = 1"
    using bra_def 
    by simp
  have f2:"dim_row (\<langle>v| * (A\<^sup>\<dagger>)) = 1"
    using times_mat_def bra_def 
    by simp
  from f1 and f2 have f3:"dim_row \<langle>A * v| = dim_row (\<langle>v| * (A\<^sup>\<dagger>))" 
    by simp
  have f4:"dim_col \<langle>A * v| = dim_row A"
    using bra_def times_mat_def 
    by simp
  have f5:"dim_col (\<langle>v| * (A\<^sup>\<dagger>)) = dim_row A"
    using times_mat_def hermite_cnj_dim_col 
    by simp
  from f4 and f5 have f6:"dim_col \<langle>A * v| = dim_col (\<langle>v| * (A\<^sup>\<dagger>))"
    by simp
  have "j < dim_row A \<Longrightarrow> cnj((A * v) $$ (j,0)) = cnj (row A j \<bullet> v)" for j
    using index_mat bra_def times_mat_def ket_vec_col eq_vecI ket_vec_def 
    by auto
  then have f7:"j < dim_row A \<Longrightarrow> cnj((A * v) $$ (j,0)) = 
    (\<Sum> i \<in> {0 ..< dim_vec v}. cnj(v $ i) * cnj(A $$ (j,i)))" for j
    using row_def scalar_prod_def index_mat cnj_sum complex_cnj_mult mult.commute
    by (smt assms index_vec lessThan_atLeast0 lessThan_iff sum.cong)
  have f8:"j < dim_row A \<Longrightarrow> (row \<langle>v| 0) \<bullet> (col (A\<^sup>\<dagger>) j) = 
    vec (dim_vec v) (\<lambda>i. cnj (v $ i)) \<bullet> vec (dim_col A) (\<lambda>i. cnj (A $$ (j,i)))" for j
    using row_bra col_hermite_cnj f1
    by simp 
  from f7 and f8 have "j < dim_row A \<Longrightarrow> cnj((A * v) $$ (j,0)) = (row \<langle>v| 0) \<bullet> (col (A\<^sup>\<dagger>) j)" for j
    using assms scalar_prod_def
    by (smt dim_vec index_vec lessThan_atLeast0 lessThan_iff sum.cong)
  then have "j < dim_col \<langle>A * v| \<Longrightarrow> \<langle>A * v| $$ (0,j) = (\<langle>v| * (A\<^sup>\<dagger>)) $$ (0,j)" for j
    using bra_def times_mat_def f5 
    by simp
  thus ?thesis
    using eq_matI f1 f3 f6 
    by auto
qed

definition col_fst :: "'a mat \<Rightarrow> 'a vec" where 
  "col_fst A = vec (dim_row A) (\<lambda> i. A $$ (i,0))"

lemma col_fst_is_col:
  fixes M::"complex mat"
  shows "col_fst M = col M 0"
  using eq_vecI
  by (simp add: col_def col_fst_def)

text\<open>
We need to declare col_fst as a coercion from matrices to vectors in order to see a column matrix
as a vector 
\<close>

declare 
  [[coercion_delete ket_vec]]
  [[coercion col_fst]]

lemma unit_vec_to_col:
  assumes "dim_col A = n" and "i < n"
  shows "col A i = A * |unit_vec n i\<rangle>"
proof-
  have "dim_vec (col A i) = dim_vec (A * |unit_vec n i\<rangle>)"
    using col_def times_mat_def
    by (simp add: col_fst_def)
  thus "col A i = A * |unit_vec n i\<rangle>"
    using assms col_def unit_vec_def times_mat_def col_fst_def ket_vec_def eq_vecI
    by (smt col_fst_is_col ket_vec_col dim_col dim_col_mat(1) index_col index_mult_mat(1) index_row(1) 
        less_numeral_extra(1) scalar_prod_right_unit)
qed

lemma mult_ket_vec_is_ket_vec_of_mult:
  fixes A::"complex mat" and v::"complex vec"
  assumes "dim_col A = dim_vec v"
  shows "|A * |v\<rangle> \<rangle> = A * |v\<rangle>"
  using assms ket_vec_def
  by (simp add: times_mat_def col_fst_def cong_mat)

lemma unitary_squared_length_bis:
  fixes U::"complex mat" and v::"complex vec"
  assumes "unitary U" and "dim_vec v = dim_col U"
  shows "\<parallel>U * |v\<rangle>\<parallel>\<^sup>2 = \<parallel>v\<parallel>\<^sup>2"
proof-
  have "\<langle>U * |v\<rangle>|U * |v\<rangle> \<rangle> = (\<langle>|v\<rangle>| * (U\<^sup>\<dagger>) * |U * |v\<rangle>\<rangle>) $$ (0,0)"
    using assms(2) inner_prod_with_row_bra_vec_col_ket_vec bra_mat_on_vec
    by (metis inner_prod_with_times_mat mult_ket_vec_is_ket_vec_of_mult)
  then have f2:"\<langle>U * |v\<rangle>|U * |v\<rangle> \<rangle> = (\<langle>|v\<rangle>| * (U\<^sup>\<dagger>) * (U * |v\<rangle>)) $$ (0,0)"
    using assms(2) mult_ket_vec_is_ket_vec_of_mult 
    by simp
  have f3:"dim_col \<langle>|v\<rangle>| = dim_vec v"
    using ket_vec_def bra_def
    by simp
  have f4:"dim_row (U\<^sup>\<dagger>) = dim_vec v"
    using assms(2)
    by (simp add: hermite_cnj_dim_row)
  have "dim_row (U * |v\<rangle>) = dim_row U"
    using times_mat_def 
    by simp
  then have "\<langle>U * |v\<rangle>|U * |v\<rangle> \<rangle> = (\<langle>|v\<rangle>| * ((U\<^sup>\<dagger>) * U) * |v\<rangle>) $$ (0,0)"
    using assoc_mult_mat f2 f3 f4
    by (smt carrier_mat_triv dim_row_mat(1) hermite_cnj_def ket_vec_def mat_carrier times_mat_def)
  then have "\<langle>U * |v\<rangle>|U * |v\<rangle> \<rangle> = (\<langle>|v\<rangle>| * |v\<rangle>) $$ (0,0)"
    using assms(1)
    by (simp add: assms(2) f3 unitary_def)
  thus ?thesis
    using inner_prod_with_row_bra_vec_col_ket_vec cpx_vec_length_inner_prod
    by (metis Re_complex_of_real inner_prod_with_times_mat)
qed

lemma col_ket_vec:
  fixes M::"complex mat"
  assumes "dim_col M = 1"
  shows "|col M 0\<rangle> = M"
  using eq_matI assms ket_vec_def col_def 
  by auto

lemma state_col_ket_vec:
  assumes "state 1 v"
  shows "state 1 |col v 0\<rangle>"
  using assms state_def col_ket_vec 
  by simp

lemma eq_ket_vec:
  assumes "u = v"
  shows "|u\<rangle> = |v\<rangle>"
  using assms 
  by simp

lemma dim_vec_of_col:
  fixes M::"complex mat"
  shows "dim_vec (col M 0) = dim_row M"
  using col_def 
  by simp

lemma col_ket_vec_index:
  assumes "i < dim_row v"
  shows "|Matrix.col v 0\<rangle> $$ (i,0) = v $$ (i,0)"
  using ket_vec_def
  by (simp add: Matrix.col_def assms)

lemma col_index_of_mat_col:
  assumes "dim_col v = 1" and "i < dim_row v"
  shows "Matrix.col v 0 $ i = v $$ (i,0)"
  using assms Matrix.col_def 
  by simp

lemma unitary_squared_length:
  fixes U::"complex mat" and v::"complex mat"
  assumes "unitary U" and "dim_row v = dim_col U" and "dim_col v = 1"
  shows "\<parallel>col (U * v) 0\<parallel>\<^sup>2 = \<parallel>col v 0\<parallel>\<^sup>2"
proof-
  have "dim_vec (col v 0) = dim_col U"
    using dim_vec_of_col assms(2) 
    by simp
  then have "\<parallel>col_fst (U * |col v 0\<rangle>)\<parallel>\<^sup>2 = \<parallel>col v 0\<parallel>\<^sup>2"
    using unitary_squared_length_bis[of "U" "col v 0"] assms(1) 
    by simp
  thus ?thesis
    using assms(3) col_fst_is_col col_ket_vec 
    by simp
qed

text\<open> 
A unitary matrix is length-preserving, i.e. it acts on a vector to produce another vector of the 
same length. 
\<close>

lemma unitary_length:
  fixes U::"complex mat" and v::"complex mat"
  assumes "unitary U" and "dim_row v = dim_col U" and "dim_col v = 1"
  shows "\<parallel>col (U * v) 0\<parallel> = \<parallel>col v 0\<parallel>"
  using assms unitary_squared_length
  by (metis cpx_vec_length_inner_prod inner_prod_csqrt of_real_hom.injectivity)

lemma unitary_length_bis:
  fixes U::"complex mat" and v::"complex vec"
  assumes "unitary U" and "dim_vec v = dim_col U"
  shows "\<parallel>U * |v\<rangle>\<parallel> = \<parallel>v\<parallel>"
  using assms unitary_squared_length_bis
  by (metis cpx_vec_length_inner_prod inner_prod_csqrt of_real_hom.injectivity)

lemma inner_prod_with_unitary_mat:
  fixes U::"complex mat" and u::"complex vec" and v::"complex vec"
  assumes "unitary U" and "dim_vec u = dim_col U" and "dim_vec v = dim_col U"
  shows "\<langle>U * |u\<rangle>|U * |v\<rangle>\<rangle> = \<langle>u|v\<rangle>"
proof-
  have f1:"\<langle>U * |u\<rangle>|U * |v\<rangle>\<rangle> = (\<langle>|u\<rangle>| * (U\<^sup>\<dagger>) * U * |v\<rangle>) $$ (0,0)"
    using assms(2) assms(3) bra_mat_on_vec mult_ket_vec_is_ket_vec_of_mult
    by (smt assoc_mult_mat carrier_mat_triv col_fst_def dim_vec hermite_cnj_dim_col index_mult_mat(2) 
        index_mult_mat(3) inner_prod_with_times_mat ket_vec_def mat_carrier)
  have f2:"\<langle>|u\<rangle>| \<in> carrier_mat 1 (dim_vec v)"
    using bra_def ket_vec_def assms(2) assms(3) 
    by auto
  have f3:"U\<^sup>\<dagger> \<in> carrier_mat (dim_col U) (dim_row U)"
    using hermite_cnj_def
    by simp
  then have "\<langle>U * |u\<rangle>|U * |v\<rangle>\<rangle> = (\<langle>|u\<rangle>| * (U\<^sup>\<dagger> * U) * |v\<rangle>) $$ (0,0)"
    using f1 f2 f3 assms(3) assoc_mult_mat
    by (metis carrier_mat_triv)
  then have "\<langle>U * |u\<rangle>|U * |v\<rangle>\<rangle> = (\<langle>|u\<rangle>| * |v\<rangle>) $$ (0,0)"
    using assms(1) unitary_def
    by (simp add: assms(2) bra_def ket_vec_def)
  thus ?thesis
    using assms(2) assms(3) inner_prod_with_times_mat 
    by simp
qed

text\<open>As a consequence we prove that columns and rows of a unitary matrix are orthonormal vectors\<close>

lemma unitary_unit_col:
  fixes U::"complex mat"
  assumes "unitary U" and "dim_col U = n" and "i < n"
  shows "\<parallel>col U i\<parallel> = 1"
proof-
  have "col U i = U * |unit_vec n i\<rangle>"
    using assms(2) assms(3) unit_vec_to_col 
    by simp
  thus ?thesis
    using assms unit_cpx_vec_length unitary_length_bis unit_vec_def 
    by simp
qed

lemma unitary_unit_row:
  fixes U::"complex mat"
  assumes "unitary U" and "dim_row U = n" and "i < n"
  shows "\<parallel>row U i\<parallel> = 1"
proof-
  have "row U i = col (U\<^sup>t) i"
    using col_transpose assms(2) assms(3) 
    by simp
  thus ?thesis
    using assms transpose_of_unitary_is_unitary unitary_unit_col
    by (metis index_transpose_mat(3))
qed

lemma orthogonal_col_of_unitary:
  fixes U::"complex mat"
  assumes "unitary U" and "dim_col U = n" and "i < n" and "j < n" and "i \<noteq> j"
  shows "\<langle>col U i|col U j\<rangle> = 0"
proof-
  have "\<langle>col U i|col U j\<rangle> = \<langle>U * |unit_vec n i\<rangle>| U * |unit_vec n j\<rangle>\<rangle>"
    using assms(2) assms(3) assms(4) unit_vec_to_col 
    by simp
  then have "\<langle>col U i|col U j\<rangle> = \<langle>unit_vec n i |unit_vec n j\<rangle>"
    using assms(1) assms(2) inner_prod_with_unitary_mat index_unit_vec(3) 
    by simp
  thus ?thesis
    using assms(3) assms(4) assms(5) orthogonal_unit_vec 
    by simp
qed

lemma orthogonal_row_of_unitary:
  fixes U::"complex mat"
  assumes "unitary U" and "dim_row U = n" and "i < n" and "j < n" and "i \<noteq> j"
  shows "\<langle>row U i|row U j\<rangle> = 0"
  using assms orthogonal_col_of_unitary transpose_of_unitary_is_unitary col_transpose
  by (metis index_transpose_mat(3))


text\<open>
As a consequence, we prove that a quantum gate acts on the states of a system of n qubits to give 
another state of this same system.
\<close>

definition app :: "complex mat \<Rightarrow> complex mat \<Rightarrow> complex mat" where
"app A v \<equiv> A * v"

lemma gate_on_state_is_state:
  assumes "gate n A" and "state n v"
  shows "state n (app A v)"
proof-
  have f1:"dim_row (app A v) = 2^n"
    using app_def times_mat_def gate_def state_def assms(1) 
    by simp
  have f2:"dim_col (app A v) = 1"
    using app_def times_mat_def state_def assms(2) 
    by simp
  have "square_mat A"
    using assms(1) gate_def 
    by simp
  then have "dim_col A = 2^n"
    using assms(1) gate_def 
    by simp
  then have "dim_col A = dim_row v"
    using assms(2) state_def 
    by simp
  then have "\<parallel>col (app A v) 0\<parallel> = \<parallel>col v 0\<parallel>"
    using unitary_length assms gate_def state_def app_def 
    by simp
  then have "\<parallel>col (app A v) 0\<parallel> = 1"
    using assms(2) state_def 
    by simp
  thus ?thesis
    using f1 f2 state_def 
    by simp
qed


subsection \<open>A Few Well-known Quantum Gates\<close>

text\<open>
Any unitary operation on n qubits can be implemented exactly by composing single qubits and
CNOT-gates (controlled-NOT gates). However, no straightforward method is known to implement these 
gates in a fashion which is resistant to errors. But, the Hadamard gate, the phase gate, the 
CNOT-gate and the \<pi>/8 gate are also universal for quantum computations, i.e. any quantum circuit on 
n qubits can be approximated to an arbitrary accuracy by using only these gates, and these gates can 
be implemented in a fault-tolerant way. 
\<close>

text\<open>We introduce a coercion from real matrices to complex matrices\<close>

definition real_to_cpx_mat:: "real mat \<Rightarrow> complex mat" where
"real_to_cpx_mat A \<equiv> mat (dim_row A) (dim_col A) (\<lambda>(i,j). A $$ (i,j))"

lemma set_2:"{0..<2::nat} = {0,1}" 
  by auto

text\<open>Our first quantum gate: the identity matrix ! Arguably, not a very interesting one though !\<close>

definition id :: "nat \<Rightarrow> complex mat" where
"id n \<equiv> 1\<^sub>m (2^n)"

text\<open>More interesting: the Pauli matrices.\<close>

definition X ::"complex mat" where
"X \<equiv> mat 2 2 (\<lambda>(i,j). if i=j then 0 else 1)"

text\<open> 
Be aware that "gate n A" means that the matrix A has dimension 2^n * 2^n. For instance, with this
convention a 2 X 2 matrix A which is unitary satisfies "gate 1 A" but not "gate 2 A" as
one might have been expected.
\<close>

lemma X_is_gate:
  shows "gate 1 X"
proof-
  define A::"complex mat" where "A = mat 2 2 (\<lambda>(i,j). if i=j then 0 else 1)"
  then have f1:"dim_row A = 2^1"
    by simp
  have f2:"dim_col A = 2^1"
    using A_def 
    by simp
  from f1 and f2 have f3:"square_mat A" 
    by simp
  have f4:"A\<^sup>\<dagger> = A"
    using hermite_cnj_def A_def 
    by auto
  have f5:"A\<^sup>\<dagger> * A = 1\<^sub>m (dim_col A)"
    apply(simp add: f4)
    apply(simp add: A_def times_mat_def one_mat_def)
    apply(rule cong_mat)
    by(auto simp add: scalar_prod_def set_2)
  have f6:"A * (A\<^sup>\<dagger>) = 1\<^sub>m (dim_row A)" 
    apply(simp add: f4)
    apply(simp add: A_def times_mat_def one_mat_def)
    apply(rule cong_mat)
    by(auto simp add: scalar_prod_def set_2)
  thus ?thesis
    using f1 f3 f5 f6 unitary_def gate_def A_def X_def
    by simp
qed

definition Y ::"complex mat" where
"Y \<equiv> mat 2 2 (\<lambda>(i,j). if i=j then 0 else (if i=0 then  -\<i> else \<i>))"

lemma Y_is_gate:
  shows "gate 1 Y"
proof-
  define A::"complex mat" where "A = mat 2 2 (\<lambda>(i,j). if i=j then 0 else (if i=0 then  -\<i> else \<i>))"
  then have f1:"dim_row A = 2^1"
    by simp
  have f2:"dim_col A = 2^1"
    using A_def 
    by simp
  from f1 and f2 have f3:"square_mat A" 
    by simp
  have f4:"A\<^sup>\<dagger> = A"
    using hermite_cnj_def A_def 
    by auto
  have f5:"A\<^sup>\<dagger> * A = 1\<^sub>m (dim_col A)"
    apply(simp add: f4)
    apply(simp add: A_def times_mat_def one_mat_def)
    apply(rule cong_mat)
    by(auto simp add: scalar_prod_def set_2)
  have f6:"A * (A\<^sup>\<dagger>) = 1\<^sub>m (dim_row A)"
    apply(simp add: f4)
    apply(simp add: A_def times_mat_def one_mat_def)
    apply(rule cong_mat)
    by(auto simp add: scalar_prod_def set_2)
  thus ?thesis
    using f1 f3 f5 f6 unitary_def gate_def A_def Y_def
    by simp
qed

definition Z ::"complex mat" where
"Z \<equiv> mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 0 else (if i = 0 then 1 else -1))"

lemma Z_is_gate:
  shows "gate 1 Z"
proof-
  define A::"complex mat" where "A = mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 0 else (if i = 0 then 1 else -1))"
  then have f1:"dim_row A = 2^1"
    by simp
  have f2:"dim_col A = 2^1"
    using A_def 
    by simp
  from f1 and f2 have f3:"square_mat A" 
    by simp
  have f4:"A\<^sup>\<dagger> = A"
    using hermite_cnj_def A_def 
    by auto
  have f5:"A\<^sup>\<dagger> * A = 1\<^sub>m (dim_col A)"
    apply(simp add: f4)
    apply(simp add: A_def times_mat_def one_mat_def)
    apply(rule cong_mat)
    by(auto simp add: scalar_prod_def set_2)
  have f6:"A * (A\<^sup>\<dagger>) = 1\<^sub>m (dim_row A)"
    apply(simp add: f4)
    apply(simp add: A_def times_mat_def one_mat_def)
    apply(rule cong_mat)
    by(auto simp add: scalar_prod_def set_2)
  thus ?thesis
    using f1 f3 f5 f6 unitary_def gate_def A_def Z_def 
    by simp
qed

text\<open>The Hadamard gate\<close>

definition H ::"complex mat" where
"H \<equiv> 1/sqrt(2) \<cdot>\<^sub>m (mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i = 0 then 1 else -1)))"

lemma H_without_scalar_prod:
  shows "H = mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1/sqrt(2) else (if i=0 then 1/sqrt(2) else -(1/sqrt(2))))"
proof-
  define A::"complex mat" where "A = 1/sqrt(2) \<cdot>\<^sub>m (mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i = 0 then 1 else -1)))"
  define B::"complex mat" where "B = mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1/sqrt(2) else (if i=0 then 1/sqrt(2) else -(1/sqrt(2))))"
  then have f1:"A = B" 
    using A_def 
    by auto
  thus ?thesis
    using H_def B_def A_def
    by simp
qed

lemma H_is_gate:
  shows "gate 1 H"
proof-
  define A::"complex mat" where "A = 1/sqrt(2) \<cdot>\<^sub>m (mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i = 0 then 1 else -1)))"
  then have f1:"dim_row A = 2^1"
    by simp
  have f2:"dim_col A = 2^1"
    using A_def 
    by simp
  from f1 and f2 have f3:"square_mat A" 
    by simp
  have f4:"A\<^sup>\<dagger> = A"
    using hermite_cnj_def A_def 
    by auto
  then have f5:"A\<^sup>\<dagger> * A = 1\<^sub>m (dim_col A)" 
    apply(simp add: f4)
    apply(simp add: A_def times_mat_def one_mat_def)
    apply(rule cong_mat)
    by(auto simp add: scalar_prod_def set_2 complex_of_real_def Complex_eq_0 complex_eqI)
  have f6:"A * (A\<^sup>\<dagger>) = 1\<^sub>m (dim_row A)"
    apply(simp add: f4)
    apply(simp add: A_def times_mat_def one_mat_def)
    apply(rule cong_mat)
    by(auto simp add: scalar_prod_def set_2 complex_of_real_def Complex_eq_0 complex_eqI)
  thus ?thesis
    using f1 f3 f5 f6 unitary_def gate_def A_def H_def
    by (simp add: H_def)
qed

text\<open>The Hadamard gate is its own inverse\<close>

lemma H_herm_cnj:
  shows "H\<^sup>\<dagger> = H"
proof-
  have f1:"dim_col H = dim_row H"
    using H_is_gate gate_def 
    by simp
  then have "\<forall>i<dim_row H.\<forall>j<dim_col H. cnj(H $$ (j,i)) = H $$ (i,j)"
    by (simp add: H_without_scalar_prod) 
  thus ?thesis
    using f1 hermite_cnj_def
    by (simp add: mat_eq_iff)
qed

lemma H_inv:
  shows "inverts_mat H H"
  using H_is_gate gate_def unitary_def H_herm_cnj
  by (simp add: inverts_mat_def)
 
lemma set_4:"{0..<4::nat} = {0,1,2,3}" 
  by auto

text\<open>The controlled-NOT gate\<close>

definition CNOT ::"complex mat" where
"CNOT \<equiv> mat 4 4 
  (\<lambda>(i,j). if i=0 \<and> j= 0 then 1 else 
    (if i=1 \<and> j=1 then 1 else 
      (if i = 2 \<and> j= 3 then 1 else 
        (if i = 3 \<and> j= 2 then 1 else 0))))"

lemma CNOT_is_gate:
  shows "gate 2 CNOT"
proof-
  define A::"complex mat" where "A = mat 4 4 
  (\<lambda>(i,j). if i=0 \<and> j= 0 then 1 else 
    (if i=1 \<and> j=1 then 1 else 
      (if i = 2 \<and> j= 3 then 1 else 
        (if i = 3 \<and> j= 2 then 1 else 0))))"
  then have f1:"dim_row A = 2^2"
    by simp
  have f2:"dim_col A = 2^2"
    using A_def 
    by simp
  from f1 and f2 have f3:"square_mat A" 
    by simp
  have f4:"A\<^sup>\<dagger> = A"
    using hermite_cnj_def A_def 
    by auto
  have f5:"A\<^sup>\<dagger> * A = 1\<^sub>m (dim_col A)" 
    apply(simp add: f4)
    apply(simp add: A_def times_mat_def one_mat_def)
    apply(rule cong_mat)
    by(auto simp add: scalar_prod_def set_4)
  have f6:"A * (A\<^sup>\<dagger>) = 1\<^sub>m (dim_row A)"
    apply(simp add: f4)
    apply(simp add: A_def times_mat_def one_mat_def)
    apply(rule cong_mat)
    by(auto simp add: scalar_prod_def set_4)
  thus ?thesis
    using f1 f3 f5 f6 unitary_def gate_def A_def CNOT_def 
    by simp
qed

lemma CNOT_herm_cnj:
  shows "CNOT\<^sup>\<dagger> = CNOT"
proof-
  have f1:"dim_col CNOT = dim_row CNOT"
    using CNOT_is_gate gate_def 
    by simp
  then have "\<forall>i<dim_row CNOT.\<forall>j<dim_col CNOT. cnj(CNOT $$ (j,i)) = CNOT $$ (i,j)"
    using CNOT_def complex_cnj_one complex_cnj_zero
    by (smt dim_col_mat(1) index_mat(1) prod.simps(2)) 
  thus ?thesis
    using f1 hermite_cnj_def
    by (simp add: mat_eq_iff)
qed

lemma CNOT_inv:
  shows "inverts_mat CNOT CNOT"
proof-
  have f1:"CNOT = mat 4 4 
  (\<lambda>(i,j). if i=0 \<and> j= 0 then 1 else 
    (if i=1 \<and> j=1 then 1 else 
      (if i = 2 \<and> j= 3 then 1 else 
        (if i = 3 \<and> j= 2 then 1 else 0))))"
    using CNOT_is_gate CNOT_def 
    by simp
  thus ?thesis
    using CNOT_is_gate gate_def unitary_def CNOT_herm_cnj
    by (simp add: inverts_mat_def)
qed

text\<open>The phase gate, also known as the S-gate\<close>

definition S ::"complex mat" where
"S \<equiv> mat 2 2 (\<lambda>(i,j). if i=0 \<and> j=0 then 1 else (if i=1 \<and> j=1 then \<i> else 0))"

text\<open>The \<pi>/8 gate, also known as the T-gate\<close>

definition T ::"complex mat" where
"T \<equiv> mat 2 2 (\<lambda>(i,j). if i=0 \<and> j=0 then 1 else (if i=1 \<and> j=1 then exp(\<i>*(pi/4)) else 0))"

text\<open>A few relations between the Hadamard gate and the Pauli matrices\<close>

lemma HXH_is_Z:
  shows "H * X * H = Z" 
    apply(simp add: X_def Z_def H_def times_mat_def)
    apply(rule cong_mat)
    by(auto simp add: set_2 scalar_prod_def complex_eqI)

lemma HYH_is_minusY:
  shows "H * Y * H = - Y" 
proof-
  have f3:"- mat 2 2 (\<lambda>(i, j). if i = j then 0 else if i = 0 then - \<i> else \<i>) =
             mat 2 2 (\<lambda>(i, j). if i = j then 0 else if i = 0 then  \<i> else -\<i>)" 
    by auto
  thus ?thesis 
    apply(simp add: Y_def H_def times_mat_def)
    apply(rule cong_mat)
    by(auto simp add: set_2 scalar_prod_def complex_eqI)
qed

lemma HZH_is_X:
  shows "H * Z * H = X"  
    apply(simp add: X_def Z_def H_def times_mat_def)
    apply(rule cong_mat)
    by(auto simp add: set_2 scalar_prod_def complex_eqI)


subsection \<open>Measurement\<close>

text \<open>Given an element v  such that "state n v", its components v $ i (when v is seen as a vector, v 
being a matrix column) for 0 <= i < n have to be understood as the coefficients of the representation 
of v in the basis given by the unit vectors of dimension 2^n, unless stated otherwise. 
Such a vector v is a state for a quantum system of n qubits.
In the literature on quantum computing, for n = 1, i.e. for a quantum system of 1 qubit, the elements
of the so-called computational basis are denoted |0\<rangle>,|1\<rangle>, and these last elements might be understood
for instance as (1,0),(0,1), i.e. as the zeroth and the first elements of a given basis ; for n = 2, 
i.e. for a quantum system of 2 qubits, the elements of the computational basis are denoted |00\<rangle>,|01\<rangle>, 
|10\<rangle>,|11\<rangle>, and they might be understood for instance as (1,0,0,0),(0,1,0,0),(0,0,1,0),(0,0,0,1); and 
so on for higher values of n. 
The idea behind these standard notations is that the labels on the vectors of the 
computational basis are the binary expressions of the natural numbers indexing the elements
in a given ordered basis interpreting the computational basis in a specific context, another point of
view is that the order of the basis corresponds to the lexicographic order for the labels. 
Those labels also represent the possible outcomes of a measurement of the n qubits of the system, 
while the squared modules of the corresponding coefficients represent the probabilities for those 
outcomes. The fact that the vector v has to be normalized expresses precisely the fact that the squared 
modules of the coefficients represent some probabilities and hence their sum should be 1.
Note that in the case of a system with multiple qubits, i.e. n>=2, one can model the simultaneous 
measurement of multiple qubits by sequential measurements of single qubits. Indeed, this last process
leads to the same probabilities for the various possible outcomes.\<close>


text \<open>Given a system with n-qubits and i the index of one qubit among the n qubits of the system, where
0 <= i <= n-1 (i.e. we start the indexing from 0), we want to find the indices of the states of the
computational basis whose labels have a 1 at the ith spot (counting from 0). For instance, if n=3 and 
i=2 then 1,3,5,7 are the indices of the elements of the computational basis with a 1 at the 2nd spot,
namely |001\<rangle>,|011\<rangle>,|101\<rangle>,|111\<rangle>. To achieve that we define the predicate select_index below.\<close>

definition select_index ::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"select_index n i j \<equiv> (i \<le> n-1) \<and> (j \<le> 2^n - 1) \<and> (j mod 2^(n-i) \<ge> 2^(n-1-i))"


lemma select_index_union:
  "{k| k::nat. select_index n i k} \<union> {k| k::nat. (k < 2^n) \<and> \<not> select_index n i k} = {0..<2^n::nat}"
proof
  have f1:"{k |k. select_index n i k} \<subseteq> {0..<2 ^ n}"
  proof
    fix x::nat assume "x \<in> {k |k. select_index n i k}"
    show "x \<in> {0..<2^n}" 
      using select_index_def
      by (metis (no_types, lifting) \<open>x \<in> {k |k. select_index n i k}\<close> atLeastLessThan_iff diff_diff_cancel diff_is_0_eq' diff_le_mono2 le_less_linear le_numeral_extra(2) mem_Collect_eq one_le_numeral one_le_power select_index_def zero_order(1))
  qed
  have f2:"{k |k. k < 2 ^ n \<and> \<not> select_index n i k} \<subseteq> {0..<2 ^ n}"
  proof
    fix x::nat assume "x \<in> {k |k. k < 2 ^ n \<and> \<not> select_index n i k}"
    show "x \<in> {0..<2^n}"
      using \<open>x \<in> {k |k. k < 2 ^ n \<and> \<not> select_index n i k}\<close> atLeast0LessThan
      by blast
  qed
  show "{k |k. select_index n i k} \<union> {k |k. k < 2 ^ n \<and> \<not> select_index n i k} \<subseteq> {0..<2 ^ n}"
    using f1 f2
    by auto
next
  show "{0..<2 ^ n} \<subseteq> {k |k. select_index n i k} \<union> {k |k. k < 2 ^ n \<and> \<not> select_index n i k}"
  proof
    fix x::nat assume "x \<in> {0..<2^n}"
    show "x \<in> {k |k. select_index n i k} \<union> {k |k. k < 2 ^ n \<and> \<not> select_index n i k}"
      using \<open>x \<in> {0..<2 ^ n}\<close>
      by auto
  qed
qed

lemma select_index_inter:
  "{k| k::nat. select_index n i k} \<inter> {k| k::nat. (k < 2^n) \<and> \<not> select_index n i k} = {}"
  by auto

lemma outcomes_sum:
  fixes f :: "nat \<Rightarrow> real"
  shows
  "(\<Sum>j\<in>{k| k::nat. select_index n i k}. (f j)) + 
   (\<Sum>j\<in>{k| k::nat. (k < 2^n) \<and> \<not> select_index n i k}. (f j)) = 
   (\<Sum>j\<in>{0..<2^n::nat}. (f j))"
proof-
  have f0:"finite {0..<2^n::nat}"
    using finite_Collect_less_nat
    by blast
  have f1:"{k| k::nat. select_index n i k} \<subseteq> {0..<2^n::nat}"
    using select_index_union
    by blast
  have f2:"{k| k::nat. (k < 2^n) \<and> \<not> select_index n i k} \<subseteq> {0..<2^n::nat}"
    using select_index_union
    by blast
  have f3:"finite {k| k::nat. select_index n i k}"
    using f1 rev_finite_subset
    by blast
  have f4:"finite {k| k::nat. (k < 2^n) \<and> \<not> select_index n i k}"
    using f2 rev_finite_subset
    by blast
  have f5:"(\<Sum>j\<in>{k| k::nat. select_index n i k}\<union>{k| k::nat. (k < 2^n) \<and> \<not> select_index n i k}. (f j)) = 
           (\<Sum>j\<in>{k| k::nat. select_index n i k}. (f j)) + 
           (\<Sum>j\<in>{k| k::nat. (k < 2^n) \<and> \<not> select_index n i k}. (f j)) -
           (\<Sum>j\<in>{k| k::nat. select_index n i k}\<inter>{k| k::nat. (k < 2^n) \<and> \<not> select_index n i k}. (f j))"
    using f3 f4 sum_Un
    by blast
  then have f6:"(\<Sum>j\<in>{0..<2^n::nat}. (f j)) = 
                (\<Sum>j\<in>{k| k::nat. select_index n i k}. (f j)) + 
                (\<Sum>j\<in>{k| k::nat. (k < 2^n) \<and> \<not> select_index n i k}. (f j)) -
                (\<Sum>j\<in>{}. (f j))"
    using select_index_union select_index_inter
    by auto
  thus ?thesis
    by simp
qed

text
\<open>
Given a state v of a n-qbit system, we compute the probability that a measure 
of qubit i has the outcome 1.
\<close>

definition prob_1 ::"nat \<Rightarrow> complex mat \<Rightarrow> nat \<Rightarrow> real" where
"prob_1 n v i \<equiv> 
  if state n v then \<Sum>j\<in>{k| k::nat. select_index n i k}. (cmod(v $$ (j,0)))\<^sup>2 else undefined"

definition prob_0 ::"nat \<Rightarrow> complex mat \<Rightarrow> nat \<Rightarrow> real" where
"prob_0 n v i \<equiv>
  if state n v then \<Sum>j\<in>{k| k::nat. (k < 2^n) \<and> \<not> select_index n i k}. (cmod(v $$ (j,0)))\<^sup>2
                      else undefined"

lemma prob_geq_zero:
  fixes n::"nat" and i::"nat" and v::"complex mat" 
  assumes "i \<le> n-1" and "state n v"
  shows "prob_1 n v i \<ge> 0 \<and> prob_0 n v i \<ge> 0" 
proof
  have f1:"(\<Sum>j\<in>{k| k::nat. select_index n i k}. (cmod(v $$ (j,0)))\<^sup>2) \<ge> 
           (\<Sum>j\<in>{k| k::nat. select_index n i k}. (0::real))"
    by (meson sum_mono zero_le_power2)
  then have f2:"(\<Sum>j\<in>{k| k::nat. select_index n i k}. (cmod(v $$ (j,0)))\<^sup>2) \<ge> 0"
    by simp
  thus "prob_1 n v i \<ge> 0"
    using assms prob_1_def
    by simp
next
  have f1:"(\<Sum>j\<in>{k| k::nat. (k < 2 ^ n) \<and> \<not> select_index n i k}. (cmod(v $$ (j,0)))\<^sup>2) \<ge> 
           (\<Sum>j\<in>{k| k::nat. (k < 2 ^ n) \<and> \<not> select_index n i k}. (0::real))"
    by (meson sum_mono zero_le_power2)
  then have f2:"(\<Sum>j\<in>{k| k::nat. (k < 2 ^ n) \<and> \<not> select_index n i k}. (cmod(v $$ (j,0)))\<^sup>2) \<ge> 0"
    by simp
  thus "prob_0 n v i \<ge> 0"
    using assms prob_0_def
    by simp
qed

lemma prob_sum_is_one:
  fixes n::"nat" and i::"nat" and v::"complex mat" 
  assumes "i \<le> n-1" and "state n v"
  shows "prob_1 n v i + prob_0 n v i = 1"
proof-
  have f0:"prob_1 n v i + prob_0 n v i = (\<Sum>j\<in>{0..<2^n::nat}. (cmod(v $$ (j,0)))\<^sup>2)"
    using prob_1_def prob_0_def assms outcomes_sum
    by simp
  have f1:"(\<Sum>j\<in>{0..<2^n::nat}. (cmod(v $$ (j,0)))\<^sup>2) = \<parallel>col v 0\<parallel>\<^sup>2"
    using cpx_vec_length_def assms state_def
    by (metis (no_types, lifting) One_nat_def atLeast0LessThan atLeastLessThan_iff dim_vec_of_col 
index_col lessI real_sqrt_power real_sqrt_unique sum.cong sum_nonneg zero_compare_simps(12))
  have f2:"\<parallel>col v 0\<parallel>\<^sup>2 = 1"
    using assms state_def
    by simp
  show ?thesis
    using f0 f1 f2
    by simp
qed

lemma prob_1_is_prob:
  fixes n::"nat" and i::"nat" and v::"complex mat" 
  assumes "i \<le> n-1" and "state n v"
  shows "prob_1 n v i \<ge> 0 \<and> prob_1 n v i \<le> 1" 
proof
  show "prob_1 n v i \<ge> 0"
    using prob_geq_zero assms
    by simp
next
  show "prob_1 n v i \<le> 1"
    using prob_geq_zero prob_sum_is_one assms
    by fastforce
qed

lemma prob_0_is_prob:
  fixes n::"nat" and i::"nat" and v::"complex mat" 
  assumes "i \<le> n-1" and "state n v"
  shows "prob_0 n v i \<ge> 0 \<and> prob_0 n v i \<le> 1"
proof
  show "prob_0 n v i \<ge> 0"
    using prob_geq_zero assms
    by simp
next
  show "prob_0 n v i \<le> 1"
    using prob_geq_zero prob_sum_is_one assms
    by fastforce
qed

text\<open>Below we give the new state of a n-qubits system after a measurement of the ith qubit gave 0.\<close>

definition post_meas_0 ::"nat \<Rightarrow> complex mat \<Rightarrow> nat \<Rightarrow> complex mat" where
"post_meas_0 n v i \<equiv> 
  of_real(1/sqrt(prob_0 n v i)) \<cdot>\<^sub>m |vec (2^n) (\<lambda>j. if \<not> select_index n i j then v $$ (j,0) else 0)\<rangle>"
 
text \<open>Note that a division by 0 never occurs. Indeed, if sqrt(prob_0 n v i) would be 0 then prob_0 n v i 
would be 0 and it would mean that the measurement of the ith qubit gave 1.\<close>

lemma smult_vec_length:
  fixes x::"real" and v :: "complex vec"
  assumes "x \<ge> 0"
  shows "\<parallel>complex_of_real(x) \<cdot>\<^sub>v v\<parallel> = x * \<parallel>v\<parallel>"
proof-
  have f0:"(\<lambda>i::nat.(cmod (complex_of_real x * v $ i))\<^sup>2) = (\<lambda>i::nat.(cmod (v $ i))\<^sup>2*x\<^sup>2)"
  proof
    fix i
    show "(cmod (complex_of_real x * v $ i))\<^sup>2 = (cmod (v $ i))\<^sup>2 * x\<^sup>2"
      by (simp add: norm_mult power_mult_distrib)
  qed
  then have f1:"(\<Sum>i<dim_vec v. (cmod (complex_of_real x * v $ i))\<^sup>2) = 
                (\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2*x\<^sup>2)"
    by meson
  have f2:"(\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2*x\<^sup>2) = 
           x\<^sup>2 * (\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2)"
    by (metis (no_types) mult.commute sum_distrib_right)
  have f3:"sqrt(x\<^sup>2 * (\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2)) = 
           sqrt(x\<^sup>2) * sqrt (\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2)"
    using real_sqrt_mult
    by blast
  show ?thesis
    by(simp add: cpx_vec_length_def f1 f2 f3 assms)
qed

lemma smult_vec_length_bis:
  fixes x::"real" and v :: "complex vec"
  assumes "x \<ge> 0"
  shows "\<parallel>col (complex_of_real(x) \<cdot>\<^sub>m |v\<rangle>) 0\<parallel> = x * \<parallel>v\<parallel>"
  using assms smult_ket_vec smult_vec_length ket_vec_col
  by metis

lemma post_meas_0_is_state:
  fixes n::"nat" and i::"nat" and v::"complex mat"
  assumes "i \<le> n-1" and "state n v" and "prob_0 n v i \<noteq> 0"
  shows "state n (post_meas_0 n v i)" 
proof-
  have f0:"\<parallel>vec (2 ^ n) (\<lambda>j. if \<not> select_index n i j then v $$ (j,0) else 0)\<parallel> = 
           sqrt(\<Sum>j<2^n. (cmod (if \<not> select_index n i j then v $$ (j,0) else 0))\<^sup>2)"
    using cpx_vec_length_def ket_vec_col 
    by auto
  have f1:"(\<Sum>j\<in>{0..<2^n::nat}. (cmod (if \<not> select_index n i j then v $$ (j,0) else 0))\<^sup>2) = 
           (\<Sum>j\<in>{k| k::nat. select_index n i k}. (cmod (if \<not> select_index n i j then v $$ (j,0) else 0))\<^sup>2) +
           (\<Sum>j\<in>{k| k::nat. (k < 2^n) \<and> \<not> select_index n i k}. (cmod (if \<not> select_index n i j then v $$ (j,0) else 0))\<^sup>2)"
    using outcomes_sum[of "\<lambda>j. (cmod (if \<not> select_index n i j then v $$ (j,0) else 0))\<^sup>2" n i]
    by simp
  have f2:"(\<Sum>j\<in>{k| k::nat. select_index n i k}. (cmod (if \<not> select_index n i j then v $$ (j,0) else 0))\<^sup>2) = 0"
    by simp
  have f3:"(\<Sum>j\<in>{k| k::nat. (k < 2^n) \<and> \<not> select_index n i k}. (cmod (if \<not> select_index n i j then v $$ (j,0) else 0))\<^sup>2) = 
           prob_0 n v i"
    by(simp add: prob_0_def assms)
  have f4:"\<parallel>vec (2 ^ n) (\<lambda>j. if \<not> select_index n i j then v $$ (j,0) else 0)\<parallel> = sqrt(prob_0 n v i)"
    using f0 f1 f2 f3 lessThan_atLeast0
    by simp
  have f5:"\<parallel>col (complex_of_real (1 / sqrt (prob_0 n v i)) \<cdot>\<^sub>m |vec (2 ^ n) (\<lambda>j. if \<not> select_index n i j then v $$ (j,0) else 0)\<rangle>) 0\<parallel> = 
           (1 / sqrt (prob_0 n v i)) * \<parallel>vec (2 ^ n) (\<lambda>j. if \<not> select_index n i j then v $$ (j,0) else 0)\<parallel>"
    using  assms(1) assms(2) prob_geq_zero smult_vec_length_bis
    by (metis (no_types, lifting) real_sqrt_ge_0_iff zero_le_divide_1_iff)
  then have "\<parallel>col (complex_of_real (1 / sqrt (prob_0 n v i)) \<cdot>\<^sub>m |vec (2 ^ n) (\<lambda>j. if \<not> select_index n i j then v $$ (j,0) else 0)\<rangle>) 0\<parallel>
= (1 / sqrt (prob_0 n v i)) * sqrt(prob_0 n v i)"
    using f4 
    by simp
  then have "\<parallel>col (post_meas_0 n v i) 0\<parallel> = 1"
    using post_meas_0_def assms(3) 
    by simp
  thus ?thesis
    using state_def post_meas_0_def
    by (simp add: ket_vec_def)
qed

text\<open>Below we give the new state of a n-qubits system after a measurement of the ith qubit gave 1.\<close>

definition post_meas_1 ::"nat \<Rightarrow> complex mat \<Rightarrow> nat \<Rightarrow> complex mat" where
"post_meas_1 n v i \<equiv> 
  of_real(1/sqrt(prob_1 n v i)) \<cdot>\<^sub>m |vec (2^n) (\<lambda>j. if select_index n i j then v $$ (j,0) else 0)\<rangle>"
 
text \<open>Note that a division by 0 never occurs. Indeed, if sqrt(prob_1 n v i) would be 0 then prob_1 n v i 
would be 0 and it would mean that the measurement of the ith qubit gave 0.\<close> 

lemma post_meas_1_is_state:
  fixes n::"nat" and i::"nat" and v::"complex mat"
  assumes "i \<le> n-1" and "state n v" and "prob_1 n v i \<noteq> 0"
  shows "state n (post_meas_1 n v i)"
proof-
  have f0:"\<parallel>vec (2 ^ n) (\<lambda>j. if select_index n i j then v $$ (j,0) else 0)\<parallel> = 
           sqrt(\<Sum>j<2^n. (cmod (if select_index n i j then v $$ (j,0) else 0))\<^sup>2)"
    by(simp add: cpx_vec_length_def)
  have f1:"(\<Sum>j\<in>{0..<2^n::nat}. (cmod (if select_index n i j then v $$ (j,0) else 0))\<^sup>2) = 
           (\<Sum>j\<in>{k| k::nat. select_index n i k}. (cmod (if select_index n i j then v $$ (j,0) else 0))\<^sup>2) +
           (\<Sum>j\<in>{k| k::nat. (k < 2^n) \<and> \<not> select_index n i k}. (cmod (if select_index n i j then v $$ (j,0) else 0))\<^sup>2)"
    using outcomes_sum[of "\<lambda>j. (cmod (if select_index n i j then v $$ (j,0) else 0))\<^sup>2" n i]
    by simp
  have f2:"(\<Sum>j\<in>{k| k::nat. select_index n i k}. (cmod (if select_index n i j then v $$ (j,0) else 0))\<^sup>2) = prob_1 n v i"
    by(simp add: prob_1_def assms)
  have f3:"(\<Sum>j\<in>{k| k::nat. (k < 2^n) \<and> \<not> select_index n i k}. (cmod (if select_index n i j then v $$ (j,0) else 0))\<^sup>2) = 0"
    by simp
  have f4:"\<parallel>vec (2 ^ n) (\<lambda>j. if  select_index n i j then v $$ (j,0) else 0)\<parallel> = sqrt(prob_1 n v i)"
    using f0 f1 f2 f3 lessThan_atLeast0
    by simp
  have f5:"\<parallel>col (complex_of_real (1 / sqrt (prob_1 n v i)) \<cdot>\<^sub>m |vec (2 ^ n) (\<lambda>j. if  select_index n i j then v $$ (j,0) else 0)\<rangle>) 0\<parallel> = 
           (1 / sqrt (prob_1 n v i)) * \<parallel>vec (2 ^ n) (\<lambda>j. if  select_index n i j then v $$ (j,0) else 0)\<parallel>"
    using  assms(1) assms(2) prob_geq_zero smult_vec_length_bis
    by (metis (no_types, lifting) real_sqrt_ge_0_iff zero_le_divide_1_iff)
  then have "\<parallel>col (complex_of_real (1 / sqrt (prob_1 n v i)) \<cdot>\<^sub>m |vec (2 ^ n) (\<lambda>j. if select_index n i j then v $$ (j,0) else 0)\<rangle>) 0\<parallel>
= (1 / sqrt (prob_1 n v i)) * sqrt(prob_1 n v i)"
    using f4 
    by simp
  then have "\<parallel>col (post_meas_1 n v i) 0\<parallel> = 1"
    using post_meas_1_def assms(3) 
    by simp
  thus ?thesis
    using state_def post_meas_1_def
    by (simp add: ket_vec_def)
qed

text
\<open>
The measurement operator below takes a number of qubits n, a state v of a n-qubits system, a number
i corresponding to the index (starting from 0) of one qubit among the n-qubits, and it computes a list 
whose first (resp. second) element is the pair made of the probability that the outcome of the measurement
of the ith qubit is 0 (resp. 1) and the corresponding post-measurement state of the system.
Of course, note that i should be strictly less than n and v should be a state of dimension n, i.e. 
state n v should hold".
\<close>

definition meas ::"nat \<Rightarrow> complex mat \<Rightarrow> nat \<Rightarrow> _list" where
"meas n v i \<equiv> [(prob_0 n v i, post_meas_0 n v i), (prob_1 n v i, post_meas_1 n v i)]"


subsection\<open>The Bell States\<close>

text \<open>We introduce below the so-called Bell states, also known as EPR pairs (EPR stands for Einstein,
Podolsky and Rosen).\<close>

definition bell_00 ::"complex mat" ("|\<beta>\<^sub>0\<^sub>0\<rangle>") where
"bell_00 \<equiv> 1/sqrt(2) \<cdot>\<^sub>m |vec 4 (\<lambda>i. if i=0 \<or> i=3 then 1 else 0)\<rangle>"

definition bell_01 ::"complex mat" ("|\<beta>\<^sub>0\<^sub>1\<rangle>") where
"bell_01 \<equiv> 1/sqrt(2) \<cdot>\<^sub>m |vec 4 (\<lambda>i. if i=1 \<or> i=2 then 1 else 0)\<rangle>"

definition bell_10 ::"complex mat" ("|\<beta>\<^sub>1\<^sub>0\<rangle>") where
"bell_10 \<equiv> 1/sqrt(2) \<cdot>\<^sub>m |vec 4 (\<lambda>i. if i=0 then 1 else if i=3 then -1 else 0)\<rangle>"

definition bell_11 ::"complex mat" ("|\<beta>\<^sub>1\<^sub>1\<rangle>") where
"bell_11 \<equiv> 1/sqrt(2) \<cdot>\<^sub>m |vec 4 (\<lambda>i. if i=1 then 1 else if i=2 then -1 else 0)\<rangle>"

lemma bell_is_state:
  shows "state 2 |\<beta>\<^sub>0\<^sub>0\<rangle>" and "state 2 |\<beta>\<^sub>0\<^sub>1\<rangle>" and "state 2 |\<beta>\<^sub>1\<^sub>0\<rangle>" and "state 2 |\<beta>\<^sub>1\<^sub>1\<rangle>"
proof-
  have "col |\<beta>\<^sub>0\<^sub>0\<rangle> 0 = 1/sqrt(2) \<cdot>\<^sub>v vec 4 (\<lambda>i. if i=0 \<or> i=3 then 1 else 0)" and 
"col |\<beta>\<^sub>0\<^sub>1\<rangle> 0 = 1/sqrt(2) \<cdot>\<^sub>v vec 4 (\<lambda>i. if i=1 \<or> i=2 then 1 else 0)" and
"col |\<beta>\<^sub>1\<^sub>0\<rangle> 0 = 1/sqrt(2) \<cdot>\<^sub>v vec 4 (\<lambda>i. if i=0 then 1 else if i=3 then -1 else 0)" and
"col |\<beta>\<^sub>1\<^sub>1\<rangle> 0 = 1/sqrt(2) \<cdot>\<^sub>v vec 4 (\<lambda>i. if i=1 then 1 else if i=2 then -1 else 0)"
       apply (auto simp: smult_ket_vec bell_00_def bell_01_def bell_10_def bell_11_def ket_vec_col 
ket_vec_def).
  then have "\<parallel>col |\<beta>\<^sub>0\<^sub>0\<rangle> 0\<parallel> = 1" and "\<parallel>col |\<beta>\<^sub>0\<^sub>1\<rangle> 0\<parallel> = 1" and "\<parallel>col |\<beta>\<^sub>1\<^sub>0\<rangle> 0\<parallel> = 1" and "\<parallel>col |\<beta>\<^sub>1\<^sub>1\<rangle> 0\<parallel> = 1"
       apply (auto simp: bell_00_def bell_01_def bell_10_def bell_11_def cpx_vec_length_def set_4 
Set_Interval.lessThan_atLeast0 cmod_def power2_eq_square).
  thus "state 2 |\<beta>\<^sub>0\<^sub>0\<rangle>" and "state 2 |\<beta>\<^sub>0\<^sub>1\<rangle>" and "state 2 |\<beta>\<^sub>1\<^sub>0\<rangle>" and "state 2 |\<beta>\<^sub>1\<^sub>1\<rangle>"
    apply (auto simp: state_def bell_00_def bell_01_def bell_10_def bell_11_def ket_vec_def).
qed

lemma ket_vec_index:
  assumes "i < dim_vec v"
  shows "|v\<rangle> $$ (i,0) = v $ i"
  using assms ket_vec_def 
  by simp

lemma bell_00_index:
  shows "|\<beta>\<^sub>0\<^sub>0\<rangle> $$ (0,0) = 1/sqrt 2" and "|\<beta>\<^sub>0\<^sub>0\<rangle> $$ (1,0) = 0" and "|\<beta>\<^sub>0\<^sub>0\<rangle> $$ (2,0) = 0" and 
"|\<beta>\<^sub>0\<^sub>0\<rangle> $$ (3,0) = 1/sqrt 2"
     apply (auto simp: bell_00_def ket_vec_def).

lemma bell_01_index:
  shows "|\<beta>\<^sub>0\<^sub>1\<rangle> $$ (0,0) = 0" and "|\<beta>\<^sub>0\<^sub>1\<rangle> $$ (1,0) = 1/sqrt 2" and "|\<beta>\<^sub>0\<^sub>1\<rangle> $$ (2,0) = 1/sqrt 2" and 
"|\<beta>\<^sub>0\<^sub>1\<rangle> $$ (3,0) = 0"
     apply (auto simp: bell_01_def ket_vec_def).

lemma bell_10_index:
  shows "|\<beta>\<^sub>1\<^sub>0\<rangle> $$ (0,0) = 1/sqrt 2" and "|\<beta>\<^sub>1\<^sub>0\<rangle> $$ (1,0) = 0" and "|\<beta>\<^sub>1\<^sub>0\<rangle> $$ (2,0) = 0" and 
"|\<beta>\<^sub>1\<^sub>0\<rangle> $$ (3,0) = - 1/sqrt 2"
     apply (auto simp: bell_10_def ket_vec_def).

lemma bell_11_index:
  shows "|\<beta>\<^sub>1\<^sub>1\<rangle> $$ (0,0) = 0" and "|\<beta>\<^sub>1\<^sub>1\<rangle> $$ (1,0) = 1/sqrt 2" and "|\<beta>\<^sub>1\<^sub>1\<rangle> $$ (2,0) = - 1/sqrt 2" and 
"|\<beta>\<^sub>1\<^sub>1\<rangle> $$ (3,0) = 0"
     apply (auto simp: bell_11_def ket_vec_def).

text
\<open>
A Bell state is a remarkable state. Indeed, if one makes one measure, either of the first or the second 
qubit, then one gets either 0 with probability 1/2 or 1 with probability 1/2. Moreover, in the case of 
two successive measurements of the first and second qubit, the outcomes are correlated. 
Indeed, in the case of |\<beta>00\<rangle> or |\<beta>10\<rangle> (resp. |\<beta>01\<rangle> or |\<beta>11\<rangle>) if one measures the second qubit after a 
measurement of the first qubit (or the other way around) then one gets the same outcomes (resp. opposite 
outcomes), i.e. for instance the probability of measuring 0 for the second qubit after a measure with 
outcome 0 for the first qubit is 1 (resp. 0).
\<close>

lemma prob_0_bell_fst:
  assumes "v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
  shows "prob_0 2 v 0 = 1/2" 
proof-
  have set_0:"{k| k::nat. (k < 4) \<and> \<not> select_index 2 0 k} = {0,1}"
    using select_index_def 
    by auto
  have f1:"v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<Longrightarrow> prob_0 2 v 0 = 1/2"
  proof-
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>0\<rangle>"
    show "prob_0 2 v 0 = 1/2"
    proof-
      have "prob_0 2 v 0 = (\<Sum>j\<in>{k| k::nat. (k < 4) \<and> \<not> select_index 2 0 k}. (cmod(bell_00 $$ (j,0)))\<^sup>2)"
        apply (auto simp: bell_is_state(1) prob_0_def asm).
      then have "prob_0 2 v 0 = (\<Sum>j\<in>{0,1}. (cmod(bell_00 $$ (j,0)))\<^sup>2)"
        using set_0 
        by simp
      then have "prob_0 2 v 0 = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        apply (auto simp: bell_00_def set_0 ket_vec_def).
      thus ?thesis
        by(simp add: cmod_def power_divide)
    qed
  qed
  have f2:"v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<Longrightarrow> prob_0 2 v 0 = 1/2"
  proof-
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>1\<rangle>"
    show "prob_0 2 v 0 = 1/2"
    proof-
      have "prob_0 2 v 0 = (\<Sum>j\<in>{k| k::nat. (k < 4) \<and> \<not> select_index 2 0 k}. (cmod(bell_01 $$ (j,0)))\<^sup>2)"
        apply (auto simp: bell_is_state(2) prob_0_def asm).
      then have "prob_0 2 v 0 = (\<Sum>j\<in>{0,1}. (cmod(bell_01 $$ (j,0)))\<^sup>2)"
        using set_0 
        by simp
      then have "prob_0 2 v 0 = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        apply (auto simp: bell_01_def set_0 ket_vec_def).
      thus ?thesis
        by(simp add: cmod_def power_divide)
    qed
  qed
  have f3:"v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<Longrightarrow> prob_0 2 v 0 = 1/2"
  proof-
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>0\<rangle>"
    show "prob_0 2 v 0 = 1/2"
    proof-
      have "prob_0 2 v 0 = (\<Sum>j\<in>{k| k::nat. (k < 4) \<and> \<not> select_index 2 0 k}. (cmod(bell_10 $$ (j,0)))\<^sup>2)"
        apply (auto simp: bell_is_state(3) prob_0_def asm).
      then have "prob_0 2 v 0 = (\<Sum>j\<in>{0,1}. (cmod(bell_10 $$ (j,0)))\<^sup>2)"
        using set_0 
        by simp
      then have "prob_0 2 v 0 = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        apply (auto simp: bell_10_def set_0 ket_vec_def).
      thus ?thesis
        by(simp add: cmod_def power_divide)
    qed
  qed
  have f4:"v = |\<beta>\<^sub>1\<^sub>1\<rangle> \<Longrightarrow> prob_0 2 v 0 = 1/2"
  proof-
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
    show "prob_0 2 v 0 = 1/2"
    proof-
      have "prob_0 2 v 0 = (\<Sum>j\<in>{k| k::nat. (k < 4) \<and> \<not> select_index 2 0 k}. (cmod(bell_11 $$ (j,0)))\<^sup>2)"
        apply (auto simp: bell_is_state(4) prob_0_def asm).
      then have "prob_0 2 v 0 = (\<Sum>j\<in>{0,1}. (cmod(bell_11 $$ (j,0)))\<^sup>2)"
        using set_0 
        by simp
      then have "prob_0 2 v 0 = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        apply (auto simp: bell_11_def set_0 ket_vec_def).
      thus ?thesis
        by(simp add: cmod_def power_divide)
    qed
  qed
  show ?thesis
    using f1 f2 f3 f4 assms
    by auto
qed

lemma prob_1_bell_fst:
  assumes "v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
  shows "prob_1 2 v 0 = 1/2" 
proof-
  have set_0:"{k| k::nat. select_index 2 0 k} = {2,3}"
    using select_index_def 
    by auto
  have f1:"v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<Longrightarrow> prob_1 2 v 0 = 1/2"
  proof-
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>0\<rangle>"
    show "prob_1 2 v 0 = 1/2"
    proof-
      have "prob_1 2 v 0 = (\<Sum>j\<in>{k| k::nat. select_index 2 0 k}. (cmod(bell_00 $$ (j,0)))\<^sup>2)"
        apply (auto simp: bell_is_state(1) prob_1_def asm).
      then have "prob_1 2 v 0 = (\<Sum>j\<in>{2,3}. (cmod(bell_00 $$ (j,0)))\<^sup>2)"
        using set_0 
        by simp
      then have "prob_1 2 v 0 = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        apply (auto simp: bell_00_def set_0 ket_vec_def).
      thus ?thesis
        by(simp add: cmod_def power_divide)
    qed
  qed
  have f2:"v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<Longrightarrow> prob_1 2 v 0 = 1/2"
  proof-
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>1\<rangle>"
    show "prob_1 2 v 0 = 1/2"
    proof-
      have "prob_1 2 v 0 = (\<Sum>j\<in>{k| k::nat. select_index 2 0 k}. (cmod(bell_01 $$ (j,0)))\<^sup>2)"
        apply (auto simp: bell_is_state(2) prob_1_def asm).
      then have "prob_1 2 v 0 = (\<Sum>j\<in>{2,3}. (cmod(bell_01 $$ (j,0)))\<^sup>2)"
        using set_0 
        by simp
      then have "prob_1 2 v 0 = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        apply (auto simp: bell_01_def set_0 ket_vec_def).
      thus ?thesis
        by(simp add: cmod_def power_divide)
    qed
  qed
  have f3:"v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<Longrightarrow> prob_1 2 v 0 = 1/2"
  proof-
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>0\<rangle>"
    show "prob_1 2 v 0 = 1/2"
    proof-
      have "prob_1 2 v 0 = (\<Sum>j\<in>{k| k::nat. select_index 2 0 k}. (cmod(bell_10 $$ (j,0)))\<^sup>2)"
        apply (auto simp: bell_is_state(3) prob_1_def asm).
      then have "prob_1 2 v 0 = (\<Sum>j\<in>{2,3}. (cmod(bell_10 $$ (j,0)))\<^sup>2)"
        using set_0 
        by simp
      then have "prob_1 2 v 0 = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        apply (auto simp: bell_10_def set_0 ket_vec_def).
      thus ?thesis
        by(simp add: cmod_def power_divide)
    qed
  qed
  have f4:"v = |\<beta>\<^sub>1\<^sub>1\<rangle> \<Longrightarrow> prob_1 2 v 0 = 1/2"
  proof-
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
    show "prob_1 2 v 0 = 1/2"
    proof-
      have "prob_1 2 v 0 = (\<Sum>j\<in>{k| k::nat. select_index 2 0 k}. (cmod(bell_11 $$ (j,0)))\<^sup>2)"
        apply (auto simp: bell_is_state(4) prob_1_def asm).
      then have "prob_1 2 v 0 = (\<Sum>j\<in>{2,3}. (cmod(bell_11 $$ (j,0)))\<^sup>2)"
        using set_0 
        by simp
      then have "prob_1 2 v 0 = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        apply (auto simp: bell_11_def set_0 ket_vec_def).
      thus ?thesis
        by(simp add: cmod_def power_divide)
    qed
  qed
  show ?thesis
    using f1 f2 f3 f4 assms
    by auto
qed

lemma prob_0_bell_snd:
  assumes "v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
  shows "prob_0 2 v 1 = 1/2" 
proof-
  have set_0:"{k| k::nat. (k < 4) \<and> \<not> select_index 2 1 k} = {0,2}"
    apply (auto simp: select_index_def)
    by (metis Suc_le_mono add_Suc add_Suc_right le_numeral_extra(3) less_antisym mod_Suc_eq mod_less 
neq0_conv not_mod2_eq_Suc_0_eq_0 numeral_2_eq_2 numeral_Bit0 one_add_one one_mod_two_eq_one one_neq_zero) 
  have f1:"v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<Longrightarrow> prob_0 2 v 1 = 1/2"
  proof-
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>0\<rangle>"
    show "prob_0 2 v 1 = 1/2"
    proof-
      have "prob_0 2 v 1 = (\<Sum>j\<in>{k| k::nat. (k < 4) \<and> \<not> select_index 2 1 k}. (cmod(bell_00 $$ (j,0)))\<^sup>2)"
        apply (auto simp: bell_is_state(1) prob_0_def asm).
      then have "prob_0 2 v 1 = (\<Sum>j\<in>{0,2}. (cmod(bell_00 $$ (j,0)))\<^sup>2)"
        using set_0 
        by simp
      then have "prob_0 2 v 1 = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        apply (auto simp: bell_00_def set_0 ket_vec_def).
      thus ?thesis
        by(simp add: cmod_def power_divide)
    qed
  qed
  have f2:"v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<Longrightarrow> prob_0 2 v 1 = 1/2"
  proof-
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>1\<rangle>"
    show "prob_0 2 v 1 = 1/2"
    proof-
      have "prob_0 2 v 1 = (\<Sum>j\<in>{k| k::nat. (k < 4) \<and> \<not> select_index 2 1 k}. (cmod(bell_01 $$ (j,0)))\<^sup>2)"
        apply (auto simp: bell_is_state(2) prob_0_def asm).
      then have "prob_0 2 v 1 = (\<Sum>j\<in>{0,2}. (cmod(bell_01 $$ (j,0)))\<^sup>2)"
        using set_0 
        by simp
      then have "prob_0 2 v 1 = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        apply (auto simp: bell_01_def set_0 ket_vec_def).
      thus ?thesis
        by(simp add: cmod_def power_divide)
    qed
  qed
  have f3:"v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<Longrightarrow> prob_0 2 v 1 = 1/2"
  proof-
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>0\<rangle>"
    show "prob_0 2 v 1 = 1/2"
    proof-
      have "prob_0 2 v 1 = (\<Sum>j\<in>{k| k::nat. (k < 4) \<and> \<not> select_index 2 1 k}. (cmod(bell_10 $$ (j,0)))\<^sup>2)"
        apply (auto simp: bell_is_state(3) prob_0_def asm).
      then have "prob_0 2 v 1 = (\<Sum>j\<in>{0,2}. (cmod(bell_10 $$ (j,0)))\<^sup>2)"
        using set_0 
        by simp
      then have "prob_0 2 v 1 = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        apply (auto simp: bell_10_def set_0 ket_vec_def).
      thus ?thesis
        by(simp add: cmod_def power_divide)
    qed
  qed
  have f4:"v = |\<beta>\<^sub>1\<^sub>1\<rangle> \<Longrightarrow> prob_0 2 v 1 = 1/2"
  proof-
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
    show "prob_0 2 v 1 = 1/2"
    proof-
      have "prob_0 2 v 1 = (\<Sum>j\<in>{k| k::nat. (k < 4) \<and> \<not> select_index 2 1 k}. (cmod(bell_11 $$ (j,0)))\<^sup>2)"
        apply (auto simp: bell_is_state(4) prob_0_def asm).
      then have "prob_0 2 v 1 = (\<Sum>j\<in>{0,2}. (cmod(bell_11 $$ (j,0)))\<^sup>2)"
        using set_0 
        by simp
      then have "prob_0 2 v 1 = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        apply (auto simp: bell_11_def set_0 ket_vec_def).
      thus ?thesis
        by(simp add: cmod_def power_divide)
    qed
  qed
  show ?thesis
    using f1 f2 f3 f4 assms
    by auto
qed

lemma prob_1_bell_snd:
  assumes "v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
  shows "prob_1 2 v 1 = 1/2" 
proof-
  have set_0:"{k| k::nat. select_index 2 1 k} = {1,3}"
    apply (auto simp: select_index_def)
    by (metis Suc_le_lessD le_SucE le_less mod2_gr_0 mod_less mod_self numeral_2_eq_2 numeral_3_eq_3)
  have f1:"v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<Longrightarrow> prob_1 2 v 1 = 1/2"
  proof-
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>0\<rangle>"
    show "prob_1 2 v 1 = 1/2"
    proof-
      have "prob_1 2 v 1 = (\<Sum>j\<in>{k| k::nat. select_index 2 1 k}. (cmod(bell_00 $$ (j,0)))\<^sup>2)"
        apply (auto simp: bell_is_state(1) prob_1_def asm).
      then have "prob_1 2 v 1 = (\<Sum>j\<in>{1,3}. (cmod(bell_00 $$ (j,0)))\<^sup>2)"
        using set_0 
        by simp
      then have "prob_1 2 v 1 = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        apply (auto simp: bell_00_def set_0 ket_vec_def).
      thus ?thesis
        by(simp add: cmod_def power_divide)
    qed
  qed
  have f2:"v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<Longrightarrow> prob_1 2 v 1 = 1/2"
  proof-
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>1\<rangle>"
    show "prob_1 2 v 1 = 1/2"
    proof-
      have "prob_1 2 v 1 = (\<Sum>j\<in>{k| k::nat. select_index 2 1 k}. (cmod(bell_01 $$ (j,0)))\<^sup>2)"
        apply (auto simp: bell_is_state(2) prob_1_def asm).
      then have "prob_1 2 v 1 = (\<Sum>j\<in>{1,3}. (cmod(bell_01 $$ (j,0)))\<^sup>2)"
        using set_0 
        by simp
      then have "prob_1 2 v 1 = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        apply (auto simp: bell_01_def set_0 ket_vec_def).
      thus ?thesis
        by(simp add: cmod_def power_divide)
    qed
  qed
  have f3:"v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<Longrightarrow> prob_1 2 v 1 = 1/2"
  proof-
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>0\<rangle>"
    show "prob_1 2 v 1 = 1/2"
    proof-
      have "prob_1 2 v 1 = (\<Sum>j\<in>{k| k::nat. select_index 2 1 k}. (cmod(bell_10 $$ (j,0)))\<^sup>2)"
        apply (auto simp: bell_is_state(3) prob_1_def asm).
      then have "prob_1 2 v 1 = (\<Sum>j\<in>{1,3}. (cmod(bell_10 $$ (j,0)))\<^sup>2)"
        using set_0 
        by simp
      then have "prob_1 2 v 1 = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        apply (auto simp: bell_10_def set_0 ket_vec_def).
      thus ?thesis
        by(simp add: cmod_def power_divide)
    qed
  qed
  have f4:"v = |\<beta>\<^sub>1\<^sub>1\<rangle> \<Longrightarrow> prob_1 2 v 1 = 1/2"
  proof-
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
    show "prob_1 2 v 1 = 1/2"
    proof-
      have "prob_1 2 v 1 = (\<Sum>j\<in>{k| k::nat. select_index 2 1 k}. (cmod(bell_11 $$ (j,0)))\<^sup>2)"
        apply (auto simp: bell_is_state(4) prob_1_def asm).
      then have "prob_1 2 v 1 = (\<Sum>j\<in>{1,3}. (cmod(bell_11 $$ (j,0)))\<^sup>2)"
        using set_0 
        by simp
      then have "prob_1 2 v 1 = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        apply (auto simp: bell_11_def set_0 ket_vec_def).
      thus ?thesis
        by(simp add: cmod_def power_divide)
    qed
  qed
  show ?thesis
    using f1 f2 f3 f4 assms
    by auto
qed

lemma post_meas_0_bell_00_fst:
  shows "post_meas_0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 = |unit_vec 4 0\<rangle>"
proof
  fix i::nat assume asm:"i < dim_row |unit_vec 4 0\<rangle>"
  have f0:"post_meas_0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (0,0) = |unit_vec 4 0\<rangle> $$ (0,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_fst bell_00_def 
ket_vec_def real_sqrt_divide)
  have f1:"post_meas_0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (1,0) = |unit_vec 4 0\<rangle> $$ (1,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_fst bell_00_def 
ket_vec_def real_sqrt_divide)
  have f2:"post_meas_0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (2,0) = |unit_vec 4 0\<rangle> $$ (2,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_fst bell_00_def 
ket_vec_def real_sqrt_divide)
  have f3:"post_meas_0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (3,0) = |unit_vec 4 0\<rangle> $$ (3,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_fst bell_00_def 
ket_vec_def real_sqrt_divide)
  have f4:"i \<in> {0,1,2,3}"
    using asm
    by(auto simp add: ket_vec_def)
  fix j assume "j < dim_col |unit_vec 4 0\<rangle>"
  then have "j = 0"
    by(auto simp add: ket_vec_def)  
  then show "post_meas_0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (i,j) = |unit_vec 4 0\<rangle> $$ (i,j)"
    using f0 f1 f2 f3 f4
    by blast
next
  show "dim_row (post_meas_0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0) = dim_row |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas_0_def ket_vec_def)
  show "dim_col (post_meas_0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0) = dim_col |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas_0_def ket_vec_def)
qed

lemma post_meas_0_bell_00_snd:
  shows "post_meas_0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 = |unit_vec 4 0\<rangle>"
proof
  fix i::nat assume asm:"i < dim_row |unit_vec 4 0\<rangle>"
  have f0:"post_meas_0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (0,0) = |unit_vec 4 0\<rangle> $$ (0,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_snd bell_00_def ket_vec_def 
real_sqrt_divide del:One_nat_def)
  have f1:"post_meas_0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (1,0) = |unit_vec 4 0\<rangle> $$ (1,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_snd bell_00_def ket_vec_def 
real_sqrt_divide)
  have f2:"post_meas_0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (2,0) = |unit_vec 4 0\<rangle> $$ (2,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_snd bell_00_def ket_vec_def 
real_sqrt_divide)
  have f3:"post_meas_0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (3,0) = |unit_vec 4 0\<rangle> $$ (3,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_snd bell_00_def ket_vec_def 
real_sqrt_divide)
  have f4:"i \<in> {0,1,2,3}"
    using asm
    by(auto simp add: ket_vec_def)
  fix j assume "j < dim_col |unit_vec 4 0\<rangle>"
  then have "j = 0"
    using ket_vec_def 
    by simp
  then show "post_meas_0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (i,j) = |unit_vec 4 0\<rangle> $$ (i,j)"
    using f0 f1 f2 f3 f4
    by blast
next
  show "dim_row (post_meas_0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1) = dim_row |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas_0_def ket_vec_def)
  show "dim_col (post_meas_0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1) = dim_col |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas_0_def ket_vec_def)
qed

lemma post_meas_0_bell_01_fst:
  shows "post_meas_0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 = |unit_vec 4 1\<rangle>"
proof
  fix i::nat assume asm:"i < dim_row |unit_vec 4 1\<rangle>"
  have f0:"post_meas_0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (0,0) = |unit_vec 4 1\<rangle> $$ (0,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_fst bell_01_def ket_vec_def
real_sqrt_divide)
  have f1:"post_meas_0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (1,0) = |unit_vec 4 1\<rangle> $$ (1,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_fst bell_01_def 
ket_vec_def real_sqrt_divide)
  have f2:"post_meas_0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (2,0) = |unit_vec 4 1\<rangle> $$ (2,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_fst bell_01_def 
ket_vec_def real_sqrt_divide)
  have f3:"post_meas_0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (3,0) = |unit_vec 4 1\<rangle> $$ (3,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_fst bell_01_def 
ket_vec_def real_sqrt_divide)
  have f4:"i \<in> {0,1,2,3}"
    using asm
    by(auto simp add: ket_vec_def)
  fix j assume "j < dim_col |unit_vec 4 1\<rangle>"
  then have "j = 0"
    using ket_vec_def 
    by simp
  then show "post_meas_0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (i,j) = |unit_vec 4 1\<rangle> $$ (i,j)"
    using f0 f1 f2 f3 f4
    by auto
next
  show "dim_row (post_meas_0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0) = dim_row |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas_0_def ket_vec_def)
  show "dim_col (post_meas_0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0) = dim_col |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas_0_def ket_vec_def)
qed

lemma post_meas_0_bell_01_snd:
  shows "post_meas_0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 = |unit_vec 4 2\<rangle>" 
proof
  fix i::nat assume asm:"i < dim_row |unit_vec 4 2\<rangle>"
  have f0:"post_meas_0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (0,0) = |unit_vec 4 2\<rangle> $$ (0,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_snd bell_01_def ket_vec_def 
real_sqrt_divide)
  have f1:"post_meas_0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (1,0) = |unit_vec 4 2\<rangle> $$ (1,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_snd bell_01_def ket_vec_def 
real_sqrt_divide)
  have f2:"post_meas_0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (2,0) = |unit_vec 4 2\<rangle> $$ (2,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_snd bell_01_def 
ket_vec_def real_sqrt_divide del:One_nat_def)
  have f3:"post_meas_0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (3,0) = |unit_vec 4 2\<rangle> $$ (3,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_snd bell_01_def 
ket_vec_def real_sqrt_divide)
  have f4:"i \<in> {0,1,2,3}"
    using asm
    by(auto simp add: ket_vec_def)
  fix j assume "j < dim_col |unit_vec 4 2\<rangle>"
  then have "j = 0"
    using ket_vec_def 
    by simp
  then show "post_meas_0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (i,j) = |unit_vec 4 2\<rangle> $$ (i,j)"
    using f0 f1 f2 f3 f4
    by auto
next
  show "dim_row (post_meas_0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1) = dim_row |unit_vec 4 2\<rangle>"
    by(auto simp add: post_meas_0_def ket_vec_def)
  show "dim_col (post_meas_0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1) = dim_col |unit_vec 4 2\<rangle>"
    by(auto simp add: post_meas_0_def ket_vec_def)
qed

lemma post_meas_0_bell_10_fst:
  shows "post_meas_0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 = |unit_vec 4 0\<rangle>" 
proof
  fix i::nat assume asm:"i < dim_row |unit_vec 4 0\<rangle>"
  have f0:"post_meas_0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (0,0) = |unit_vec 4 0\<rangle> $$ (0,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_fst bell_10_def 
ket_vec_def real_sqrt_divide)
  have f1:"post_meas_0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (1,0) = |unit_vec 4 0\<rangle> $$ (1,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_fst bell_10_def 
ket_vec_def real_sqrt_divide)
  have f2:"post_meas_0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (2,0) = |unit_vec 4 0\<rangle> $$ (2,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_fst bell_10_def 
ket_vec_def real_sqrt_divide)
  have f3:"post_meas_0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (3,0) = |unit_vec 4 0\<rangle> $$ (3,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_fst bell_10_def 
ket_vec_def real_sqrt_divide)
  have f4:"i \<in> {0,1,2,3}"
    using asm
    by(auto simp add: ket_vec_def)
  fix j assume "j < dim_col |unit_vec 4 0\<rangle>"
  hence "j = 0"
    using ket_vec_def 
    by simp
  then show "post_meas_0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (i,j) = |unit_vec 4 0\<rangle> $$ (i,j)"
    using f0 f1 f2 f3 f4
    by auto
next
  show "dim_row (post_meas_0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0) = dim_row |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas_0_def ket_vec_def)
  show "dim_col (post_meas_0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0) = dim_col |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas_0_def ket_vec_def)
qed

lemma post_meas_0_bell_10_snd:
  shows "post_meas_0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 = |unit_vec 4 0\<rangle>" 
proof
  fix i::nat assume asm:"i < dim_row |unit_vec 4 0\<rangle>"
  have f0:"post_meas_0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (0,0) = |unit_vec 4 0\<rangle> $$ (0,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_snd bell_10_def 
ket_vec_def real_sqrt_divide del:One_nat_def)
  have f1:"post_meas_0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (1,0) = |unit_vec 4 0\<rangle> $$ (1,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_snd bell_10_def 
ket_vec_def real_sqrt_divide)
  have f2:"post_meas_0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (2,0) = |unit_vec 4 0\<rangle> $$ (2,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_snd bell_10_def 
ket_vec_def real_sqrt_divide)
  have f3:"post_meas_0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (3,0) = |unit_vec 4 0\<rangle> $$ (3,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_snd bell_10_def 
ket_vec_def real_sqrt_divide)
  have f4:"i \<in> {0,1,2,3}"
    using asm
    by(auto simp add: ket_vec_def)
  fix j assume "j < dim_col |unit_vec 4 0\<rangle>"
  hence "j = 0"
    using ket_vec_def 
    by simp
  then show "post_meas_0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (i,j) = |unit_vec 4 0\<rangle> $$ (i,j)"
    using f0 f1 f2 f3 f4
    by blast
next
  show "dim_row (post_meas_0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1) = dim_row |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas_0_def ket_vec_def)
  show "dim_col (post_meas_0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1) = dim_col |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas_0_def ket_vec_def)
qed

lemma post_meas_0_bell_11_fst:
  shows "post_meas_0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 = |unit_vec 4 1\<rangle>" 
proof
  fix i::nat assume asm:"i < dim_row |unit_vec 4 1\<rangle>"
  have f0:"post_meas_0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (0,0) = |unit_vec 4 1\<rangle> $$ (0,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_fst bell_11_def 
ket_vec_def real_sqrt_divide)
  have f1:"post_meas_0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (1,0) = |unit_vec 4 1\<rangle> $$ (1,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_fst bell_11_def 
ket_vec_def real_sqrt_divide)
  have f2:"post_meas_0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (2,0) = |unit_vec 4 1\<rangle> $$ (2,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_fst bell_11_def 
ket_vec_def real_sqrt_divide)
  have f3:"post_meas_0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (3,0) = |unit_vec 4 1\<rangle> $$ (3,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_fst bell_11_def 
ket_vec_def real_sqrt_divide)
  have f4:"i \<in> {0,1,2,3}"
    using asm
    by(auto simp add: ket_vec_def)
  fix j assume "j < dim_col |unit_vec 4 1\<rangle>"
  hence "j = 0"
    using ket_vec_def 
    by simp
  then show "post_meas_0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (i,j) = |unit_vec 4 1\<rangle> $$ (i,j)"
    using f0 f1 f2 f3 f4
    by auto
next
  show "dim_row (post_meas_0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0) = dim_row |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas_0_def ket_vec_def)
  show "dim_col (post_meas_0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0) = dim_col |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas_0_def ket_vec_def)
qed

lemma post_meas_0_bell_11_snd:
  shows "post_meas_0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 = - |unit_vec 4 2\<rangle>" 
proof
  fix i::nat assume asm:"i < dim_row (- |unit_vec 4 2\<rangle>)"
  have f0:"post_meas_0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (0,0) = (- |unit_vec 4 2\<rangle>) $$ (0,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_snd bell_11_def 
ket_vec_def real_sqrt_divide)
  have f1:"post_meas_0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (1,0) = (- |unit_vec 4 2\<rangle>) $$ (1,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_snd bell_11_def 
ket_vec_def real_sqrt_divide)
  have f2:"post_meas_0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (2,0) = (- |unit_vec 4 2\<rangle>) $$ (2,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_snd bell_11_def 
ket_vec_def real_sqrt_divide del:One_nat_def)
  have f3:"post_meas_0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (3,0) = (- |unit_vec 4 2\<rangle>) $$ (3,0)"
    by(simp add: post_meas_0_def unit_vec_def select_index_def prob_0_bell_snd bell_11_def 
ket_vec_def real_sqrt_divide)
  have f4:"i \<in> {0,1,2,3}"
    using asm
    by(auto simp add: ket_vec_def)
  fix j assume "j < dim_col (- |unit_vec 4 2\<rangle>)"
  hence "j = 0"
    using ket_vec_def 
    by simp
  then show "post_meas_0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (i,j) = (- |unit_vec 4 2\<rangle>) $$ (i,j)"
    using f0 f1 f2 f3 f4
    by auto
next
  show "dim_row (post_meas_0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1) = dim_row (- |unit_vec 4 2\<rangle>)"
    by(auto simp add: post_meas_0_def ket_vec_def)
  show "dim_col (post_meas_0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1) = dim_col (- |unit_vec 4 2\<rangle>)"
    by(auto simp add: post_meas_0_def ket_vec_def)
qed

lemma post_meas_1_bell_00_fst:
  shows "post_meas_1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 = |unit_vec 4 3\<rangle>" 
proof
  fix i::nat assume asm:"i < dim_row |unit_vec 4 3\<rangle>"
  have f0:"post_meas_1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (0,0) = |unit_vec 4 3\<rangle> $$ (0,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_fst bell_00_def 
ket_vec_def real_sqrt_divide)
  have f1:"post_meas_1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (1,0) = |unit_vec 4 3\<rangle> $$ (1,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_fst bell_00_def 
ket_vec_def real_sqrt_divide)
  have f2:"post_meas_1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (2,0) = |unit_vec 4 3\<rangle> $$ (2,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_fst bell_00_def 
ket_vec_def real_sqrt_divide)
  have f3:"post_meas_1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (3,0) = |unit_vec 4 3\<rangle> $$ (3,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_fst bell_00_def 
ket_vec_def real_sqrt_divide)
  have f4:"i \<in> {0,1,2,3}"
    using asm
    by(auto simp add: ket_vec_def)
  fix j assume "j < dim_col |unit_vec 4 3\<rangle>"
  hence "j = 0"
    using ket_vec_def 
    by simp
  then show "post_meas_1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (i,j) = |unit_vec 4 3\<rangle> $$ (i,j)"
    using f0 f1 f2 f3 f4
    by auto
next
  show "dim_row (post_meas_1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0) = dim_row |unit_vec 4 3\<rangle>"
    by(auto simp add: post_meas_1_def ket_vec_def)
  show "dim_col (post_meas_1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0) = dim_col |unit_vec 4 3\<rangle>"
    by(auto simp add: post_meas_1_def ket_vec_def)
qed

lemma post_meas_1_bell_00_snd:
  shows "post_meas_1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 = |unit_vec 4 3\<rangle>" 
proof
  fix i::nat assume asm:"i < dim_row |unit_vec 4 3\<rangle>"
  have f0:"post_meas_1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (0,0) = |unit_vec 4 3\<rangle> $$ (0,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_snd bell_00_def 
ket_vec_def real_sqrt_divide)
  have f1:"post_meas_1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (1,0) = |unit_vec 4 3\<rangle> $$ (1,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_snd bell_00_def 
ket_vec_def real_sqrt_divide)
  have f2:"post_meas_1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (2,0) = |unit_vec 4 3\<rangle> $$ (2,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_snd bell_00_def 
ket_vec_def real_sqrt_divide)
  have f3:"post_meas_1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (3,0) = |unit_vec 4 3\<rangle> $$ (3,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_snd bell_00_def 
ket_vec_def real_sqrt_divide del: One_nat_def)
  have f4:"i \<in> {0,1,2,3}"
    using asm
    by(auto simp add: ket_vec_def)
  fix j assume "j < dim_col |unit_vec 4 3\<rangle>"
  hence "j = 0"
    using ket_vec_def 
    by simp
  then show "post_meas_1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (i,j) = |unit_vec 4 3\<rangle> $$ (i,j)"
    using f0 f1 f2 f3 f4
    by auto
next
  show "dim_row (post_meas_1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1) = dim_row |unit_vec 4 3\<rangle>"
    by(auto simp add: post_meas_1_def ket_vec_def)
  show "dim_col (post_meas_1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1) = dim_col |unit_vec 4 3\<rangle>"
    by(auto simp add: post_meas_1_def ket_vec_def)
qed

lemma post_meas_1_bell_01_fst:
  shows "post_meas_1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 = |unit_vec 4 2\<rangle>" 
proof
  fix i::nat assume asm:"i < dim_row |unit_vec 4 2\<rangle>"
  have f0:"post_meas_1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (0,0) = |unit_vec 4 2\<rangle> $$ (0,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_fst bell_01_def 
ket_vec_def real_sqrt_divide)
  have f1:"post_meas_1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (1,0) = |unit_vec 4 2\<rangle> $$ (1,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_fst bell_01_def 
ket_vec_def real_sqrt_divide)
  have f2:"post_meas_1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (2,0) = |unit_vec 4 2\<rangle> $$ (2,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_fst bell_01_def 
ket_vec_def real_sqrt_divide)
  have f3:"post_meas_1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (3,0) = |unit_vec 4 2\<rangle> $$ (3,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_fst bell_01_def 
ket_vec_def real_sqrt_divide)
  have f4:"i \<in> {0,1,2,3}"
    using asm
    by(auto simp add: ket_vec_def)
  fix j assume "j < dim_col |unit_vec 4 2\<rangle>"
  hence "j = 0"
    using ket_vec_def 
    by simp
  then show "post_meas_1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (i,j) = |unit_vec 4 2\<rangle> $$ (i,j)"
    using f0 f1 f2 f3 f4
    by auto
next
  show "dim_row (post_meas_1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0) = dim_row |unit_vec 4 2\<rangle>"
    by(auto simp add: post_meas_1_def ket_vec_def)
  show "dim_col (post_meas_1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0) = dim_col |unit_vec 4 2\<rangle>"
    by(auto simp add: post_meas_1_def ket_vec_def)
qed

lemma post_meas_1_bell_01_snd:
  shows "post_meas_1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 = |unit_vec 4 1\<rangle>" 
proof
  fix i::nat assume asm:"i < dim_row |unit_vec 4 1\<rangle>"
  have f0:"post_meas_1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (0,0) = |unit_vec 4 1\<rangle> $$ (0,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_snd bell_01_def 
ket_vec_def real_sqrt_divide)
  have f1:"post_meas_1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (1,0) = |unit_vec 4 1\<rangle> $$ (1,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_snd bell_01_def 
ket_vec_def real_sqrt_divide del: One_nat_def)
  have f2:"post_meas_1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (2,0) = |unit_vec 4 1\<rangle> $$ (2,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_snd bell_01_def 
ket_vec_def real_sqrt_divide)
  have f3:"post_meas_1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (3,0) = |unit_vec 4 1\<rangle> $$ (3,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_snd bell_01_def 
ket_vec_def real_sqrt_divide)
  have f4:"i \<in> {0,1,2,3}"
    using asm
    by(auto simp add: ket_vec_def)
  fix j assume "j < dim_col |unit_vec 4 1\<rangle>"
  hence "j = 0"
    using ket_vec_def 
    by simp
  then show "post_meas_1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (i,j) = |unit_vec 4 1\<rangle> $$ (i,j)"
    using f0 f1 f2 f3 f4
    by auto
next
  show "dim_row (post_meas_1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1) = dim_row |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas_1_def ket_vec_def)
  show "dim_col (post_meas_1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1) = dim_col |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas_1_def ket_vec_def)
qed

lemma post_meas_1_bell_10_fst:
  shows "post_meas_1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 = - |unit_vec 4 3\<rangle>" 
proof
  fix i::nat assume asm:"i < dim_row (- |unit_vec 4 3\<rangle>)"
  have f0:"post_meas_1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (0,0) = (- |unit_vec 4 3\<rangle>) $$ (0,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_fst bell_10_def 
ket_vec_def real_sqrt_divide)
  have f1:"post_meas_1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (1,0) = (- |unit_vec 4 3\<rangle>) $$ (1,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_fst bell_10_def 
ket_vec_def real_sqrt_divide)
  have f2:"post_meas_1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (2,0) = (- |unit_vec 4 3\<rangle>) $$ (2,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_fst bell_10_def 
ket_vec_def real_sqrt_divide)
  have f3:"post_meas_1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (3,0) = (- |unit_vec 4 3\<rangle>) $$ (3,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_fst bell_10_def 
ket_vec_def real_sqrt_divide)
  have f4:"i \<in> {0,1,2,3}"
    using asm
    by(auto simp add: ket_vec_def)
  fix j assume "j < dim_col (- |unit_vec 4 3\<rangle>)"
  hence "j = 0"
    using ket_vec_def 
    by simp
  then show "post_meas_1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (i,j) = (- |unit_vec 4 3\<rangle>) $$ (i,j)"
    using f0 f1 f2 f3 f4
    by auto
next
  show "dim_row (post_meas_1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0) = dim_row (- |unit_vec 4 3\<rangle>)"
    by(auto simp add: post_meas_1_def ket_vec_def)
  show "dim_col (post_meas_1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0) = dim_col (- |unit_vec 4 3\<rangle>)"
    by(auto simp add: post_meas_1_def ket_vec_def)
qed

lemma post_meas_1_bell_10_snd:
  shows "post_meas_1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 = - |unit_vec 4 3\<rangle>" 
proof
  fix i::nat assume asm:"i < dim_row (- |unit_vec 4 3\<rangle>)"
  have f0:"post_meas_1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (0,0) = (- |unit_vec 4 3\<rangle>) $$ (0,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_snd bell_10_def 
ket_vec_def real_sqrt_divide)
  have f1:"post_meas_1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (1,0) = (- |unit_vec 4 3\<rangle>) $$ (1,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_snd bell_10_def 
ket_vec_def real_sqrt_divide)
  have f2:"post_meas_1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (2,0) = (- |unit_vec 4 3\<rangle>) $$ (2,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_snd bell_10_def 
ket_vec_def real_sqrt_divide)
  have f3:"post_meas_1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (3,0) = (- |unit_vec 4 3\<rangle>) $$ (3,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_snd bell_10_def ket_vec_def real_sqrt_divide del: One_nat_def)
  have f4:"i \<in> {0,1,2,3}"
    using asm
    by(auto simp add: ket_vec_def)
  fix j assume "j < dim_col (- |unit_vec 4 3\<rangle>)"
  hence "j = 0"
    using ket_vec_def 
    by simp
  then show "post_meas_1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (i,j) = (- |unit_vec 4 3\<rangle>) $$ (i,j)"
    using f0 f1 f2 f3 f4
    by auto
next
  show "dim_row (post_meas_1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1) = dim_row (- |unit_vec 4 3\<rangle>)"
    by(auto simp add: post_meas_1_def ket_vec_def)
  show "dim_col (post_meas_1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1) = dim_col (- |unit_vec 4 3\<rangle>)"
    by(auto simp add: post_meas_1_def ket_vec_def)
qed

lemma post_meas_1_bell_11_fst:
  shows "post_meas_1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 = - |unit_vec 4 2\<rangle>" 
proof
  fix i::nat assume asm:"i < dim_row (- |unit_vec 4 2\<rangle>)"
  have f0:"post_meas_1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (0,0) = (- |unit_vec 4 2\<rangle>) $$ (0,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_fst bell_11_def 
ket_vec_def real_sqrt_divide)
  have f1:"post_meas_1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (1,0) = (- |unit_vec 4 2\<rangle>) $$ (1,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_fst bell_11_def 
ket_vec_def real_sqrt_divide)
  have f2:"post_meas_1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (2,0) = (- |unit_vec 4 2\<rangle>) $$ (2,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_fst bell_11_def 
ket_vec_def real_sqrt_divide)
  have f3:"post_meas_1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (3,0) = (- |unit_vec 4 2\<rangle>) $$ (3,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_fst bell_11_def 
ket_vec_def real_sqrt_divide)
  have f4:"i \<in> {0,1,2,3}"
    using asm
    by(auto simp add: ket_vec_def)
  fix j assume "j < dim_col (- |unit_vec 4 2\<rangle>)"
  hence "j = 0"
    using ket_vec_def 
    by simp
  then show "post_meas_1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (i,j) = (- |unit_vec 4 2\<rangle>) $$ (i,j)"
    using f0 f1 f2 f3 f4
    by auto
next
  show "dim_row (post_meas_1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0) = dim_row (- |unit_vec 4 2\<rangle>)"
    by(auto simp add: post_meas_1_def ket_vec_def)
  show "dim_col (post_meas_1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0) = dim_col (- |unit_vec 4 2\<rangle>)"
    by(auto simp add: post_meas_1_def ket_vec_def)
qed

lemma post_meas_1_bell_11_snd:
  shows "post_meas_1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 = |unit_vec 4 1\<rangle>" 
proof
  fix i::nat assume asm:"i < dim_row |unit_vec 4 1\<rangle>"
  have f0:"post_meas_1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (0,0) = |unit_vec 4 1\<rangle> $$ (0,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_snd bell_11_def 
ket_vec_def real_sqrt_divide)
  have f1:"post_meas_1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (1,0) = |unit_vec 4 1\<rangle> $$ (1,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_snd bell_11_def 
ket_vec_def real_sqrt_divide del: One_nat_def)
  have f2:"post_meas_1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (2,0) = |unit_vec 4 1\<rangle> $$ (2,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_snd bell_11_def 
ket_vec_def real_sqrt_divide)
  have f3:"post_meas_1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (3,0) = |unit_vec 4 1\<rangle> $$ (3,0)"
    by(simp add: post_meas_1_def unit_vec_def select_index_def prob_1_bell_snd bell_11_def 
ket_vec_def real_sqrt_divide)
  have f4:"i \<in> {0,1,2,3}"
    using asm
    by(auto simp add: ket_vec_def)
  fix j assume "j < dim_col |unit_vec 4 1\<rangle>"
  hence "j = 0"
    using ket_vec_def 
    by simp
  then show "post_meas_1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (i,j) = |unit_vec 4 1\<rangle> $$ (i,j)"
    using f0 f1 f2 f3 f4
    by auto
next
  show "dim_row (post_meas_1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1) = dim_row |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas_1_def ket_vec_def)
  show "dim_col (post_meas_1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1) = dim_col |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas_1_def ket_vec_def)
qed



end
