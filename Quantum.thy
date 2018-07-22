theory Quantum
imports 
  Main 
  Power 
  Real 
  Complex 
  Jordan_Normal_Form.Matrix
  "HOL-Library.Nonpos_Ints"
  VectorSpace.VectorSpace
  "HOL-Algebra.Ring"
  VectorSpace.LinearCombinations
begin

section \<open>Qubits and Quantum Gates\<close>

subsection \<open>Qubits\<close>

(* In this theory "cpx" stands for "complex" *)
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

typedef qubit = "{v| n v::complex vec. dim_vec v = 2^n \<and> \<parallel>v\<parallel> = 1}"
  using unit_cpx_vec_length[of 0 "2^n"]
  by (smt index_unit_vec(3) less_numeral_extra(1) mem_Collect_eq power_0 unit_cpx_vec_length)

definition qubit_to_cpx_vec:: "qubit \<Rightarrow> complex vec" where
"qubit_to_cpx_vec v \<equiv> Rep_qubit v"

(* We introduce a coercion from the type of qubits to the type of complex vectors *)

declare 
  [[coercion_enabled]]
  [[coercion qubit_to_cpx_vec]]

(* Below the natural number n codes for the dimension of the complex vector space where the qubits 
live *)
lemma unit_vec_of_right_length_is_qubit:
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

definition qubit_of_dim:: "nat \<Rightarrow> _ set" where
"qubit_of_dim n \<equiv> {v| v:: complex vec. dim_vec v = 2^n \<and> \<parallel>v\<parallel> = 1}"

lemma qubit_of_dim_is_qubit:
  assumes "v \<in> qubit_of_dim n"
  shows "v \<in> {v| n v::complex vec. dim_vec v = 2^n \<and> \<parallel>v\<parallel> = 1}"
  using assms qubit_of_dim_def
  by simp


subsection "The Hermitian Conjugation"

(* The Hermitian conjugate of a complex matrix is the complex conjugate of its transpose *)
definition hermite_cnj :: "complex mat \<Rightarrow> complex mat" ("_\<dagger>") where
  "hermite_cnj A \<equiv> mat (dim_col A) (dim_row A) (\<lambda> (i,j). cnj(A $$ (j,i)))"

(* We introduce the type of complex square matrices *)
typedef cpx_sqr_mat = "{A | A::complex mat. square_mat A}"
proof-
  have "square_mat (1\<^sub>m n)" for n
    using one_mat_def 
    by simp
  thus ?thesis
    by blast
qed

definition cpx_sqr_mat_to_cpx_mat :: "cpx_sqr_mat \<Rightarrow> complex mat" where
"cpx_sqr_mat_to_cpx_mat A \<equiv> Rep_cpx_sqr_mat A"

(* We introduce a coercion from the type of complex square matrices to the type of complex matrices 
*)
declare [[coercion cpx_sqr_mat_to_cpx_mat]]

lemma hermite_cnj_dim_row:
  shows "dim_row (A\<dagger>) = dim_col A"
  using hermite_cnj_def 
  by simp

lemma hermite_cnj_dim_col:
  shows "dim_col (A\<dagger>) = dim_row A"
  using hermite_cnj_def
  by simp

lemma col_hermite_cnj:
  fixes A::"complex mat"
  assumes "j < dim_row A"
  shows "col (A\<dagger>) j = vec (dim_col A) (\<lambda>i. cnj (A $$ (j,i)))"
  using assms col_def hermite_cnj_def 
  by simp

lemma row_hermite_cnj:
  fixes A::"complex mat"
  assumes "i < dim_col A"
  shows "row (A\<dagger>) i = vec (dim_row A) (\<lambda>j. cnj (A $$ (j,i)))"
  using assms row_def hermite_cnj_def 
  by simp

lemma hermite_cnj_of_sqr_is_sqr:
  shows "square_mat ((A::cpx_sqr_mat)\<dagger>)"
proof-
  have "square_mat A"
    using cpx_sqr_mat_to_cpx_mat_def Rep_cpx_sqr_mat 
    by auto
  then have "dim_row A = dim_col A" 
    by simp
  then have "dim_col (A\<dagger>) = dim_row (A\<dagger>)"
    using hermite_cnj_dim_col hermite_cnj_dim_row 
    by simp
  thus "square_mat (A\<dagger>)" 
    by simp
qed

lemma hermite_cnj_of_id_is_id:
  shows "(1\<^sub>m n)\<dagger> = 1\<^sub>m n"
  using hermite_cnj_def one_mat_def 
  by auto


subsection "Unitary Matrices and Quantum Gates"

definition unitary :: "complex mat \<Rightarrow> bool" where
"unitary A \<equiv> (A\<dagger>) * A = 1\<^sub>m (dim_col A) \<and> A * (A\<dagger>) = 1\<^sub>m (dim_row A)"

lemma id_is_unitary:
  shows "unitary (1\<^sub>m n)"
  using unitary_def hermite_cnj_of_id_is_id 
  by simp

typedef gate = "{A | n A::complex mat. square_mat A \<and> dim_row A = 2^n \<and> unitary A}"
proof-
  have f1:"dim_row (1\<^sub>m (2^n)) = 2^n" for n
    using one_mat_def 
    by simp
  have f2:"square_mat (1\<^sub>m (2^n))" for n
    using one_mat_def 
    by simp
  have f3:"unitary (1\<^sub>m (2^n))" for n
    using id_is_unitary 
    by simp
  thus ?thesis
    using f1 f2 f3 
    by blast
qed

definition gate_to_cpx_mat:: "gate \<Rightarrow> complex mat" where
"gate_to_cpx_mat A \<equiv> Rep_gate A"

definition gate_of_dim :: "nat \<Rightarrow> _ set" where
"gate_of_dim n \<equiv> {A | A::complex mat. square_mat A \<and> dim_row A = 2^n \<and> unitary A}"

lemma gate_of_dim_is_gate:
  assumes "A \<in> gate_of_dim n"
  shows "A \<in> {A | n A::complex mat. square_mat A \<and> dim_row A = 2^n \<and> unitary A}"
  using assms gate_of_dim_def 
  by simp

(* We introduce a coercion from the type of quantum gates to the type of complex matrices *)

declare [[coercion gate_to_cpx_mat]]

(* We prove that a quantum gate is invertible and its inverse is given by its Hermitian conjugate *)

lemma mat_unitary_mat:
  fixes A::"complex mat"
  assumes "unitary A"
  shows "inverts_mat A (A\<dagger>)"
  using assms inverts_mat_def unitary_def
  by auto

lemma unitary_mat_mat:
  fixes A::"complex mat"
  assumes "unitary A"
  shows "inverts_mat (A\<dagger>) A"
  using assms unitary_def
  by (simp add: inverts_mat_def hermite_cnj_dim_row)

lemma gate_is_inv:
  shows "invertible_mat (A::gate)"
proof-
  have f1:"square_mat A"
    using Rep_gate gate_to_cpx_mat_def 
    by simp
  have f2:"inverts_mat A (A\<dagger>)"
    using mat_unitary_mat Rep_gate gate_to_cpx_mat_def
    by simp
  have f3:"inverts_mat (A\<dagger>) A"
    using Rep_gate gate_to_cpx_mat_def unitary_mat_mat
    by simp
  thus ?thesis
    using f1 f2 f3 invertible_mat_def 
    by auto
qed


subsection "The Inner Product"

(* Now, we introduce a coercion between complex vectors and (column) complex matrices *)

definition ket_vec :: "complex vec \<Rightarrow> complex mat" ("|_\<rangle>") where
"ket_vec v \<equiv> mat (dim_vec v) 1 (\<lambda>(i,j). v $ i)"

lemma col_ket_vec:
  fixes v::"complex vec"
  shows "col |v\<rangle> 0 = v"
  using col_def ket_vec_def index_mat eq_vecI
  by auto

declare [[coercion ket_vec]]

definition row_vec :: "complex vec \<Rightarrow> complex mat" where
"row_vec v \<equiv> mat 1 (dim_vec v) (\<lambda>(i,j). v $ j)" 

definition mat_cnj :: "complex mat \<Rightarrow> complex mat" where
"mat_cnj A \<equiv> mat (dim_row A) (dim_col A) (\<lambda>(i,j). cnj (A $$ (i,j)))"

definition bra_vec :: "complex vec \<Rightarrow> complex mat" where
"bra_vec v \<equiv> mat_cnj (row_vec v)"

lemma row_bra_vec:
  fixes v::"complex vec"
  shows "row (bra_vec v) 0 = vec (dim_vec v) (\<lambda>i. cnj(v $ i))"
  using row_def bra_vec_def mat_cnj_def index_mat row_vec_def 
  by auto

(* We introduce a definition called bra to take the corresponding bra of a vector when this last
vector is given under its matrix representation, i.e. as a column matrix *)
definition bra :: "complex mat \<Rightarrow> complex mat" ("\<langle>_|") where
"bra v \<equiv> mat 1 (dim_row v) (\<lambda>(i,j). cnj(v $$ (j,i)))"

(* The relation between bra, bra_vec and ket_vec is given as follows. *)
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

(* We introduce the inner product of two complex vectors in C^n.
The result of an inner product is a (1,1)-matrix, i.e. a complex number. *)
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
  using assms inner_prod_def index_vec row_bra_vec col_ket_vec
  by (simp add: scalar_prod_def bra_bra_vec)

lemma inner_prod_with_times_mat:
  fixes u::"complex vec" and v::"complex vec"
  assumes "dim_vec u = dim_vec v"
  shows "\<langle>u|v\<rangle> = (\<langle>u| * |v\<rangle>) $$ (0,0)"
  using assms inner_prod_def times_mat_def index_mat ket_vec_def bra_def 
    inner_prod_with_row_bra_vec_col_ket_vec 
  by auto

(* We prove that our inner product is linear in its second argument *)

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

(* We declare a coercion from real numbers to complex numbers *)
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

(* The bra-vector \<langle>Av| is given by \<langle>v|A\<dagger> *)

lemma bra_mat_on_vec:
  fixes v::"complex vec" and A::"complex mat"
  assumes "dim_col A = dim_vec v"
  shows "\<langle>A * v| = \<langle>v| * (A\<dagger>)"
proof-
  have f1:"dim_row \<langle>A * v| = 1"
    using bra_def 
    by simp
  have f2:"dim_row (\<langle>v| * (A\<dagger>)) = 1"
    using times_mat_def bra_def 
    by simp
  from f1 and f2 have f3:"dim_row \<langle>A * v| = dim_row (\<langle>v| * (A\<dagger>))" 
    by simp
  have f4:"dim_col \<langle>A * v| = dim_row A"
    using bra_def times_mat_def 
    by simp
  have f5:"dim_col (\<langle>v| * (A\<dagger>)) = dim_row A"
    using times_mat_def hermite_cnj_dim_col 
    by simp
  from f4 and f5 have f6:"dim_col \<langle>A * v| = dim_col (\<langle>v| * (A\<dagger>))"
    by simp
  have "j < dim_row A \<Longrightarrow> cnj((A * v) $$ (j,0)) = cnj (row A j \<bullet> v)" for j
    using index_mat bra_def times_mat_def col_ket_vec eq_vecI ket_vec_def 
    by auto
  then have f7:"j < dim_row A \<Longrightarrow> cnj((A * v) $$ (j,0)) = 
    (\<Sum> i \<in> {0 ..< dim_vec v}. cnj(v $ i) * cnj(A $$ (j,i)))" for j
    using row_def scalar_prod_def index_mat cnj_sum complex_cnj_mult mult.commute
    by (smt assms index_vec lessThan_atLeast0 lessThan_iff sum.cong)
  have f8:"j < dim_row A \<Longrightarrow> (row \<langle>v| 0) \<bullet> (col (A\<dagger>) j) = 
    vec (dim_vec v) (\<lambda>i. cnj (v $ i)) \<bullet> vec (dim_col A) (\<lambda>i. cnj (A $$ (j,i)))" for j
    using row_bra col_hermite_cnj f1
    by simp 
  from f7 and f8 have "j < dim_row A \<Longrightarrow> cnj((A * v) $$ (j,0)) = (row \<langle>v| 0) \<bullet> (col (A\<dagger>) j)" for j
    using assms scalar_prod_def
    by (smt dim_vec index_vec lessThan_atLeast0 lessThan_iff sum.cong)
  then have "j < dim_col \<langle>A * v| \<Longrightarrow> \<langle>A * v| $$ (0,j) = (\<langle>v| * (A\<dagger>)) $$ (0,j)" for j
    using bra_def times_mat_def f5 
    by simp
  thus ?thesis
    using eq_matI f1 f3 f6 
    by auto
qed

(* A unitary matrix is length-preserving, i.e. it acts on a vector to produce another vector of the 
same length. *)

definition col_fst :: "'a mat \<Rightarrow> 'a vec" where 
  "col_fst A = vec (dim_row A) (\<lambda> i. A $$ (i,0))"

(* We need to declare col_fst as a coercion from matrices to vectors in order to see a column matrix
as a vector *)
declare 
  [[coercion_delete ket_vec]]
  [[coercion col_fst]]

lemma mult_ket_vec_is_ket_vec_of_mult:
  fixes A::"complex mat" and v::"complex vec"
  assumes "dim_col A = dim_vec v"
  shows "|A * |v\<rangle> \<rangle> = A * |v\<rangle>"
  using assms ket_vec_def
  by (simp add: times_mat_def col_fst_def cong_mat)

lemma unitary_squared_length:
  fixes U::"complex mat" and v::"complex vec"
  assumes "unitary U" and "dim_vec v = dim_col U"
  shows "\<parallel>U * |v\<rangle>\<parallel>\<^sup>2 = \<parallel>v\<parallel>\<^sup>2"
proof-
  have "\<langle>U * |v\<rangle>|U * |v\<rangle> \<rangle> = (\<langle>|v\<rangle>| * (U\<dagger>) * |U * |v\<rangle>\<rangle>) $$ (0,0)"
    using assms(2) inner_prod_with_row_bra_vec_col_ket_vec bra_mat_on_vec
    by (metis inner_prod_with_times_mat mult_ket_vec_is_ket_vec_of_mult)
  then have f2:"\<langle>U * |v\<rangle>|U * |v\<rangle> \<rangle> = (\<langle>|v\<rangle>| * (U\<dagger>) * (U * |v\<rangle>)) $$ (0,0)"
    using assms(2) mult_ket_vec_is_ket_vec_of_mult 
    by simp
  have f3:"dim_col \<langle>|v\<rangle>| = dim_vec v"
    using ket_vec_def bra_def
    by simp
  have f4:"dim_row (U\<dagger>) = dim_vec v"
    using assms(2)
    by (simp add: hermite_cnj_dim_row)
  have "dim_row (U * |v\<rangle>) = dim_row U"
    using times_mat_def 
    by simp
  then have "\<langle>U * |v\<rangle>|U * |v\<rangle> \<rangle> = (\<langle>|v\<rangle>| * ((U\<dagger>) * U) * |v\<rangle>) $$ (0,0)"
    using assoc_mult_mat f2 f3 f4
    by (smt carrier_mat_triv dim_row_mat(1) hermite_cnj_def ket_vec_def mat_carrier times_mat_def)
  then have "\<langle>U * |v\<rangle>|U * |v\<rangle> \<rangle> = (\<langle>|v\<rangle>| * |v\<rangle>) $$ (0,0)"
    using assms(1)
    by (simp add: assms(2) f3 unitary_def)
  thus ?thesis
    using inner_prod_with_row_bra_vec_col_ket_vec cpx_vec_length_inner_prod
    by (metis Re_complex_of_real inner_prod_with_times_mat)
qed

lemma unitary_length:
  fixes U::"complex mat" and v::"complex vec"
  assumes "unitary U" and "dim_vec v = dim_col U"
  shows "\<parallel>U * |v\<rangle>\<parallel> = \<parallel>v\<parallel>"
  using assms unitary_squared_length
  by (metis cpx_vec_length_inner_prod inner_prod_csqrt of_real_hom.injectivity)

lemma col_fst_col:
  fixes A::"complex mat" and v::"complex vec"
  shows "col_fst (U * |v\<rangle>) = col (U * |v\<rangle>) 0"
  using eq_vecI
  by (simp add: col_def col_fst_def)

declare 
  [[coercion_delete col_fst]]
  [[coercion ket_vec]]

(* As a consequence, we prove that a quantum gate acting on a qubit really gives a qubit of the
same dimension *)

definition app :: "gate \<Rightarrow> qubit \<Rightarrow> qubit" where
"app A v \<equiv> Abs_qubit (col (Rep_gate A * v) 0)"

lemma gate_on_qubit_is_qubit:
  fixes U::"complex mat" and v::"complex vec"
  assumes "U \<in> gate_of_dim n" and "v \<in> qubit_of_dim n"
  shows "col (U * v) 0 \<in> qubit_of_dim n"
proof-
  have f1:"dim_vec (col (U * v) 0) = 2^n"
    using col_def gate_of_dim_def assms(1) times_mat_def 
    by simp
  have "square_mat U"
    using assms(1) gate_of_dim_def 
    by simp
  then have "dim_col U = 2^n"
    using assms(1) gate_of_dim_def 
    by simp
  then have "\<parallel>col (U * v) 0\<parallel> = \<parallel>v\<parallel>"
    using unitary_length assms gate_of_dim_def qubit_of_dim_def col_fst_col
    by (metis (mono_tags, lifting) mem_Collect_eq)
  then have f2:"\<parallel>col (U * v) 0\<parallel> = 1"
    using assms(2) qubit_of_dim_def 
    by simp
  thus ?thesis
    using f1 f2 qubit_of_dim_def 
    by simp
qed

lemma gate_on_qubit_is_qubit_bis:
  fixes U::"gate" and v::"qubit"
  assumes "Rep_gate U \<in> gate_of_dim n" and "Rep_qubit v \<in> qubit_of_dim n"
  shows "Rep_qubit (app U v) \<in> qubit_of_dim n"
  using assms app_def gate_on_qubit_is_qubit Abs_qubit_inverse qubit_of_dim_def qubit_to_cpx_vec_def 
  by auto


subsection \<open>A Few Well-known Quantum Gates\<close>

(* We introduce a coercion from real matrices to complex matrices *)

definition real_to_cpx_mat:: "real mat \<Rightarrow> complex mat" where
"real_to_cpx_mat A \<equiv> mat (dim_row A) (dim_col A) (\<lambda>(i,j). A $$ (i,j))"

(* declare [[coercion real_to_cpx_mat]] prompts an error! *)

(* Our first quantum gate: the identity matrix ! Arguably, not a very interesting one though ! *)
definition id_gate :: "nat \<Rightarrow> gate" where
"id_gate n \<equiv> Abs_gate (1\<^sub>m (2^n))"

(* More interesting: the Pauli matrices. *)

definition X_gate ::"gate" where
"X_gate \<equiv> Abs_gate (mat 2 2 (\<lambda>(i,j). if i=j then 0 else 1))"

(* Below we use (momentarily, hopefully) "sorry", since Sledgehammer is not able to conveniently 
handle (matrix) computations, even very easy ones *)

(* Be aware that "gate_of_dim n" means that the matrix has dimension 2^n. For instance, with this
convention a 2 X 2 matrix which is unitary belongs to "gate_of_dim 1" but not to "gate_of_dim 2" as
one might have been expected *)
lemma X_gate_dim_prelim:
  shows "mat 2 2 (\<lambda>(i,j). if i=j then 0 else 1) \<in> gate_of_dim 1"
proof-
  define A::"complex mat" where "A = mat 2 2 (\<lambda>(i,j). if i=j then 0 else 1)"
  then have f1:"dim_row A = 2^1"
    by simp
  have f2:"dim_col A = 2^1"
    using A_def 
    by simp
  from f1 and f2 have f3:"square_mat A" 
    by simp
  have f4:"A\<dagger> = A"
    using hermite_cnj_def A_def 
    by auto
  then have f5:"A\<dagger> * A = 1\<^sub>m (dim_col A)" sorry
  have f6:"A * (A\<dagger>) = 1\<^sub>m (dim_row A)" sorry
  thus ?thesis
    using f1 f3 f5 f6 unitary_def gate_of_dim_def A_def 
    by simp
qed

lemma X_gate_dim:
  shows "Rep_gate X_gate \<in> gate_of_dim 1"
  using X_gate_dim_prelim X_gate_def Abs_gate_inverse gate_of_dim_is_gate 
  by fastforce

definition Y_gate ::"gate" where
"Y_gate \<equiv> Abs_gate (mat 2 2 (\<lambda>(i,j). if i=j then 0 else (if i=0 then  -\<i> else \<i>)))"

lemma Y_gate_dim_prelim:
  shows "mat 2 2 (\<lambda>(i,j). if i=j then 0 else (if i=0 then  -\<i> else \<i>)) \<in> gate_of_dim 1"
proof-
  define A::"complex mat" where "A = mat 2 2 (\<lambda>(i,j). if i=j then 0 else (if i=0 then  -\<i> else \<i>))"
  then have f1:"dim_row A = 2^1"
    by simp
  have f2:"dim_col A = 2^1"
    using A_def 
    by simp
  from f1 and f2 have f3:"square_mat A" 
    by simp
  have f4:"A\<dagger> = A"
    using hermite_cnj_def A_def 
    by auto
  then have f5:"A\<dagger> * A = 1\<^sub>m (dim_col A)" sorry
  have f6:"A * (A\<dagger>) = 1\<^sub>m (dim_row A)" sorry
  thus ?thesis
    using f1 f3 f5 f6 unitary_def gate_of_dim_def A_def 
    by simp
qed

lemma Y_gate_dim:
  shows "Rep_gate Y_gate \<in> gate_of_dim 1"
  using Y_gate_dim_prelim Y_gate_def Abs_gate_inverse gate_of_dim_is_gate 
  by fastforce

definition Z_gate ::"gate" where
"Z_gate \<equiv> Abs_gate (mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 0 else (if i = 0 then 1 else -1)))"

lemma Z_gate_dim_prelim:
  shows "mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 0 else (if i = 0 then 1 else -1)) \<in> gate_of_dim 1"
proof-
  define A::"complex mat" where "A = mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 0 else (if i = 0 then 1 else -1))"
  then have f1:"dim_row A = 2^1"
    by simp
  have f2:"dim_col A = 2^1"
    using A_def 
    by simp
  from f1 and f2 have f3:"square_mat A" 
    by simp
  have f4:"A\<dagger> = A"
    using hermite_cnj_def A_def 
    by auto
  then have f5:"A\<dagger> * A = 1\<^sub>m (dim_col A)" sorry
  have f6:"A * (A\<dagger>) = 1\<^sub>m (dim_row A)" sorry
  thus ?thesis
    using f1 f3 f5 f6 unitary_def gate_of_dim_def A_def 
    by simp
qed

lemma Z_gate_dim:
  shows "Rep_gate Z_gate \<in> gate_of_dim 1"
  using Z_gate_dim_prelim Z_gate_def Abs_gate_inverse gate_of_dim_is_gate 
  by fastforce

(* The Hadamard gate *)

definition H_gate ::"gate" where
"H_gate \<equiv> Abs_gate (1/sqrt(2) \<cdot>\<^sub>m (mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i = 0 then 1 else -1))))"

lemma H_gate_without_scalar_prod:
  shows "H_gate = Abs_gate (mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1/sqrt(2) else (if i=0 then 1/sqrt(2) else -(1/sqrt(2)))))"
proof-
  define A::"complex mat" where "A = 1/sqrt(2) \<cdot>\<^sub>m (mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i = 0 then 1 else -1)))"
  define B::"complex mat" where "B = mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1/sqrt(2) else (if i=0 then 1/sqrt(2) else -(1/sqrt(2))))"
  then have f1:"A = B" 
    using A_def 
    by auto
  then have f2:"Rep_gate H_gate = Rep_gate (Abs_gate B)"
    using H_gate_def A_def B_def
    by simp
  thus ?thesis
    using H_gate_def Rep_gate_inject B_def 
    by simp
qed

lemma H_gate_dim_prelim:
  shows "1/sqrt(2) \<cdot>\<^sub>m (mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i = 0 then 1 else -1))) \<in> gate_of_dim 1"
proof-
  define A::"complex mat" where "A = 1/sqrt(2) \<cdot>\<^sub>m (mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i = 0 then 1 else -1)))"
  then have f1:"dim_row A = 2^1"
    by simp
  have f2:"dim_col A = 2^1"
    using A_def 
    by simp
  from f1 and f2 have f3:"square_mat A" 
    by simp
  have f4:"A\<dagger> = A"
    using hermite_cnj_def A_def 
    by auto
  then have f5:"A\<dagger> * A = 1\<^sub>m (dim_col A)" sorry
  have f6:"A * (A\<dagger>) = 1\<^sub>m (dim_row A)" sorry
  thus ?thesis
    using f1 f3 f5 f6 unitary_def gate_of_dim_def A_def 
    by simp
qed

lemma H_gate_dim:
  shows "Rep_gate H_gate \<in> gate_of_dim 1"
  using H_gate_dim_prelim H_gate_def Abs_gate_inverse gate_of_dim_is_gate 
  by fastforce

(* The controlled-NOT gate *)

definition CN_gate ::"gate" where
"CN_gate \<equiv> Abs_gate (mat 4 4 
  (\<lambda>(i,j). if i=0 \<and> j= 0 then 1 else 
    (if i=1 \<and> j=1 then 1 else 
      (if i = 2 \<and> j= 3 then 1 else 
        (if i = 3 \<and> j= 2 then 1 else 0)))))"

lemma CN_gate_dim_prelim:
  shows "mat 4 4 
  (\<lambda>(i,j). if i=0 \<and> j= 0 then 1 else 
    (if i=1 \<and> j=1 then 1 else 
      (if i = 2 \<and> j= 3 then 1 else 
        (if i = 3 \<and> j= 2 then 1 else 0)))) \<in> gate_of_dim 2"
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
  have f4:"A\<dagger> = A"
    using hermite_cnj_def A_def 
    by auto
  then have f5:"A\<dagger> * A = 1\<^sub>m (dim_col A)" sorry
  have f6:"A * (A\<dagger>) = 1\<^sub>m (dim_row A)" sorry
  thus ?thesis
    using f1 f3 f5 f6 unitary_def gate_of_dim_def A_def 
    by simp
qed

lemma CN_gate_dim:
  shows "Rep_gate CN_gate \<in> gate_of_dim 2"
  using CN_gate_dim_prelim CN_gate_def Abs_gate_inverse gate_of_dim_is_gate 
  by fastforce

subsection \<open>The Vector Space of Complex Vectors of Dimension n\<close>

definition module_cpx_vec:: "nat \<Rightarrow> (complex, complex vec) module" where
"module_cpx_vec n \<equiv> module_vec TYPE(complex) n"

definition cpx_rng ::"complex ring" where
"cpx_rng \<equiv> \<lparr>carrier = UNIV, mult = op *, one = 1, zero = 0, add = op +\<rparr>"

lemma cpx_cring:
  shows "field cpx_rng"
  apply unfold_locales
  apply (auto intro: right_inverse simp: cpx_rng_def Units_def field_simps)
  by (metis add.right_neutral add_diff_cancel_left' add_uminus_conv_diff)

lemma cpx_abelian_monoid:
  shows "abelian_monoid cpx_rng"
  using cpx_cring field_def
  by (simp add: field_def abelian_group_def cring_def domain_def ring_def)

lemma vecspace_cpx_vec:
  fixes n::"nat"
  shows "vectorspace cpx_rng (module_cpx_vec n)"
  apply unfold_locales
  apply (auto simp: cpx_rng_def cpx_cring module_cpx_vec_def module_vec_def Units_def field_simps)
  apply (auto intro: right_inverse add_inv_exists_vec)
  by (metis add.right_neutral add_diff_cancel_left' add_uminus_conv_diff)

lemma module_cpx_vec:
  fixes n::"nat"
  shows "module cpx_rng (module_cpx_vec n)"
  using vecspace_cpx_vec vectorspace_def 
  by auto

definition qubit_of_basis :: "nat \<Rightarrow> nat \<Rightarrow> qubit" where
"qubit_of_basis n i \<equiv> Abs_qubit (unit_vec (2^n) i)"

definition unit_vectors :: "nat \<Rightarrow> (complex vec) set" where
"unit_vectors n \<equiv> {unit_vec n i| i::nat. 0 \<le> i \<and> i < n}"

lemma unit_vectors_carrier_vec:
  fixes n::"nat"
  shows "unit_vectors n \<subseteq> carrier_vec n"
  using unit_vectors_def 
  by auto

lemma (in module) finsum_over_singleton:
  assumes "f x \<in> carrier M"
  shows "finsum M f {x} = f x"
  using assms 
  by simp

lemma lincomb_over_singleton:
  fixes n::"nat"
  assumes "x \<in> carrier_vec n" and "f \<in> {x} \<rightarrow> UNIV"
  shows "module.lincomb (module_cpx_vec n) f {x} = f x \<cdot>\<^sub>v x"
  using assms module.lincomb_def module_cpx_vec_def module_vec_def module.finsum_over_singleton 
    module_cpx_vec
  by (smt carrier_vecD carrier_vecI index_smult_vec(2) module_vec_simps(3) module_vec_simps(4))

lemma dim_vec_lincomb:
  fixes n::"nat"
  assumes "finite F" and "f: F \<rightarrow> UNIV" and "F \<subseteq> carrier_vec n"
  shows "dim_vec (module.lincomb (module_cpx_vec n) f F) = n"
  using assms
proof(induct F)
  case empty
  show "dim_vec (module.lincomb (module_cpx_vec n) f {}) = n"
  proof-
    have "module.lincomb (module_cpx_vec n) f {} = 0\<^sub>v n"
      using module.lincomb_def abelian_monoid.finsum_empty module_cpx_vec_def module_vec_def
        vecspace_cpx_vec vectorspace_def
      by (smt abelian_group_def module_def module_vec_simps(2))
    thus ?thesis
      using index_zero_vec 
      by simp
  qed
next
  case (insert x F)
  hence "module.lincomb (module_cpx_vec n) f (insert x F) = 
    (f x \<cdot>\<^sub>v x) \<oplus>\<^bsub>module_cpx_vec n\<^esub> module.lincomb (module_cpx_vec n) f F"
    using module_cpx_vec_def module_vec_def module_cpx_vec module.lincomb_insert cpx_rng_def insert_subset
    by (smt Pi_I' UNIV_I Un_insert_right module_vec_simps(4) partial_object.select_convs(1) sup_bot.comm_neutral)
  hence "dim_vec (module.lincomb (module_cpx_vec n) f (insert x F)) = 
    dim_vec (module.lincomb (module_cpx_vec n) f F)"
    using index_add_vec
    by (simp add: module_cpx_vec_def module_vec_simps(1))
  thus "dim_vec (module.lincomb (module_cpx_vec n) f (insert x F)) = n"
    using insert.hyps(3) insert.prems(2) 
    by auto
qed

lemma lincomb_vec_index:
  fixes n::"nat"
  assumes "finite F" and "i < n" and "F \<subseteq> carrier_vec n" and "f: F \<rightarrow> UNIV"
  shows "module.lincomb (module_cpx_vec n) f F $ i = (\<Sum>v\<in>F. f v * (v $ i))"
  using assms
proof(induct F)
  case empty
  then show "module.lincomb (module_cpx_vec n) f {} $ i = (\<Sum>v\<in>{}. f v * v $ i)"
    apply auto
    using assms(2) module.lincomb_def abelian_monoid.finsum_empty module_cpx_vec_def
    by (metis (mono_tags) abelian_group_def index_zero_vec(1) module_cpx_vec module_def module_vec_simps(2))
next
  case(insert x F)
  then show "module.lincomb (module_cpx_vec n) f (insert x F) $ i = (\<Sum>v\<in>insert x F. f v * v $ i)"
    apply auto
  proof-
    have "module.lincomb (module_cpx_vec n) f (insert x F) = 
      f x \<cdot>\<^sub>v x \<oplus>\<^bsub>module_cpx_vec n\<^esub> module.lincomb (module_cpx_vec n) f F"
      using module.lincomb_insert module_cpx_vec insert.hyps(1) module_cpx_vec_def module_vec_def
        insert.prems(2) insert.hyps(2) insert.prems(3) insert_def
      by (smt Pi_I' UNIV_I Un_insert_right cpx_rng_def insert_subset module_vec_simps(4) 
          partial_object.select_convs(1) sup_bot.comm_neutral)
    then have "module.lincomb (module_cpx_vec n) f (insert x F) $ i = 
      (f x \<cdot>\<^sub>v x) $ i + module.lincomb (module_cpx_vec n) f F $ i"
      using index_add_vec assms(2) dim_vec_lincomb
      by (metis Pi_split_insert_domain insert.hyps(1) insert.prems(2) insert.prems(3) insert_subset 
          module_cpx_vec_def module_vec_simps(1))
    thus "module.lincomb (module_cpx_vec n) f (insert x F) $ i = f x * x $ i + (\<Sum>v\<in>F. f v * v $ i)"
      using index_smult_vec assms(2) insert.prems(2) insert_def insert.hyps(3) 
      by auto
  qed
qed

lemma unit_vectors_is_lin_indpt :
  fixes n::"nat"
  shows "module.lin_indpt cpx_rng (module_cpx_vec n) (unit_vectors n)"
proof
  assume a1:"module.lin_dep cpx_rng (module_cpx_vec n) (unit_vectors n)"
  then have "\<exists>A a v. (finite A \<and> A \<subseteq> (unit_vectors n) \<and> (a \<in> A \<rightarrow> UNIV) \<and> 
    (module.lincomb (module_cpx_vec n) a A = \<zero>\<^bsub>module_cpx_vec n\<^esub>) \<and> (v \<in> A) \<and> (a v \<noteq> \<zero>\<^bsub>cpx_rng\<^esub>))"
    using module.lin_dep_def cpx_rng_def module_cpx_vec 
    by fastforce
  then obtain A and a and v where f1:"finite A" and f2:"A \<subseteq> (unit_vectors n)" and f3:"a \<in> A \<rightarrow> UNIV" 
    and f4:"module.lincomb (module_cpx_vec n) a A = \<zero>\<^bsub>module_cpx_vec n\<^esub>" and f5:"v \<in> A" and 
    f6:"a v \<noteq> \<zero>\<^bsub>cpx_rng\<^esub>"
    by blast
  then obtain i where f7:"v = unit_vec n i" and f8:"i < n"
    using f5 f2 unit_vectors_def 
    by auto
  then have f9:"module.lincomb (module_cpx_vec n) a A $ i = (\<Sum>u\<in>A. a u * (u $ i))"
    using lincomb_vec_index f1 f2 f3 f8
    by (smt carrier_dim_vec index_unit_vec(3) mem_Collect_eq subset_iff sum.cong unit_vectors_def)
  have "\<forall>u\<in>A.\<forall>j<n. u = unit_vec n j \<longrightarrow> j \<noteq> i \<longrightarrow> a u * (u $ i) = 0"
    using f2 unit_vectors_def index_unit_vec
    by (simp add: f8)
  then have "(\<Sum>u\<in>A. a u * (u $ i)) = (\<Sum>u\<in>A. if u=v then a v * v $ i else 0)"
    using f2 unit_vectors_def f7
    by (smt mem_Collect_eq subsetCE sum.cong)
  then have "(\<Sum>u\<in>A. a u * (u $ i)) = a v * (v $ i)"
    using abelian_monoid.finsum_singleton[of cpx_rng v A "\<lambda>u\<in>A. a u * (u $ i)"] cpx_abelian_monoid
      f5 f1 cpx_rng_def 
    by simp
  then have "(\<Sum>u\<in>A. a u * (u $ i)) = a v"
    using f7 index_unit_vec f8
    by simp
  then have "(\<Sum>u\<in>A. a u * (u $ i)) \<noteq> 0"
    using f6
    by (simp add: cpx_rng_def)
  thus False
    using f4 module_cpx_vec_def module_vec_def index_zero_vec f8 f9
    by (simp add: module_vec_simps(2))
qed

lemma unit_vectors_is_genset:
  fixes n::"nat"
  shows "module.gen_set cpx_rng (module_cpx_vec n) (unit_vectors n)"
proof-
  have "module.span cpx_rng (module_cpx_vec n) (unit_vectors n) \<subseteq> carrier_vec n"
    using module.span_def dim_vec_lincomb carrier_vec_def cpx_rng_def
    by (smt Collect_mono index_unit_vec(3) module.span_is_subset2 module_cpx_vec module_cpx_vec_def 
        module_vec_simps(3) unit_vectors_def)
  have "carrier (module_cpx_vec n) \<subseteq> module.span cpx_rng (module_cpx_vec n) (unit_vectors n)"
  proof
    fix v
    assume a1:"v \<in> carrier (module_cpx_vec n)"
    define A a lc where "A = {unit_vec n i ::complex vec| i::nat. i < n \<and> v $ i \<noteq> 0}" and 
      "a = (\<lambda>u\<in>A. u \<bullet> v)" and "lc = module.lincomb (module_cpx_vec n) a A"
    then have f1:"finite A" 
      by simp
    have f2:"A \<subseteq> carrier_vec n"
      using carrier_vec_def A_def 
      by auto
    have f3:"a \<in> A \<rightarrow> UNIV"
      using a_def 
      by simp
    then have f4:"dim_vec v = dim_vec lc"
      using f1 f2 f3 a1 module_cpx_vec_def dim_vec_lincomb lc_def
      by (simp add: module_vec_simps(3))
    then have f5:"i < n \<Longrightarrow> lc $ i = (\<Sum>u\<in>A. u \<bullet> v * u $ i)" for i
      using lincomb_vec_index lc_def a_def f1 f2 f3 
      by simp
    then have "i < n \<Longrightarrow> j < n \<Longrightarrow> j \<noteq> i \<Longrightarrow> unit_vec n j \<bullet> v * unit_vec n j $ i = 0" for i j
      using index_unit_vec
      by simp
    then have "i < n \<Longrightarrow> lc $ i = (\<Sum>u\<in>A. if u = unit_vec n i then v $ i else 0)" for i
      using a1 A_def f5 scalar_prod_left_unit
      by (smt f4 carrier_vecI dim_vec_lincomb f1 f2 f3 index_unit_vec(2) lc_def 
          mem_Collect_eq mult.right_neutral sum.cong)
    then have "i < n \<Longrightarrow> lc $ i = v $ i" for i
      using abelian_monoid.finsum_singleton[of cpx_rng i] A_def cpx_rng_def 
      by auto
    then have f6:"v = lc"
      using eq_vecI f4 dim_vec_lincomb f1 f2 lc_def 
      by auto
    have "A \<subseteq> unit_vectors n"
      using A_def unit_vectors_def 
      by auto
    thus "v \<in> module.span cpx_rng (module_cpx_vec n) (unit_vectors n)"
      using f6 module.span_def[of cpx_rng "module_cpx_vec n"] lc_def f1 f2 cpx_rng_def module_cpx_vec
      by (smt Pi_I' UNIV_I mem_Collect_eq partial_object.select_convs(1))
  qed
  thus ?thesis
    using module_cpx_vec_def module_vec_def \<open>module.span cpx_rng (module_cpx_vec n) (unit_vectors n) \<subseteq> carrier_vec n\<close> 
      module_vec_simps(3) 
    by fastforce
qed
    
lemma unit_vectors_is_basis :
  fixes n::"nat"
  shows "vectorspace.basis cpx_rng (module_cpx_vec n) (unit_vectors n)"
proof-
  fix n
  have "unit_vectors n \<subseteq> carrier (module_cpx_vec n)"
    using unit_vectors_def module_cpx_vec_def module_vec_def carrier_vec_def index_unit_vec module_vec_simps(3) 
    by fastforce
  then show ?thesis
    using vectorspace.basis_def unit_vectors_is_lin_indpt unit_vectors_is_genset vecspace_cpx_vec
      cpx_cring
    by (smt carrier_dim_vec index_unit_vec(3) mem_Collect_eq module_cpx_vec_def module_vec_simps(3) 
        subsetI unit_vectors_def)
qed

lemma qubit_of_dim_is_lincomb:
  fixes n::"nat"
  shows "qubit_of_dim n = 
  {module.lincomb (module_cpx_vec (2^n)) a A|a A. 
    finite A \<and> A\<subseteq>(unit_vectors (2^n)) \<and> a\<in> A \<rightarrow> UNIV \<and> \<parallel>module.lincomb (module_cpx_vec (2^n)) a A\<parallel>=1}"
proof
  show "qubit_of_dim n
    \<subseteq> {module.lincomb (module_cpx_vec (2^n)) a A |a A.
        finite A \<and> A \<subseteq> unit_vectors (2^n) \<and> a \<in> A \<rightarrow> UNIV \<and> \<parallel>module.lincomb (module_cpx_vec (2^n)) a A\<parallel> = 1}"
  proof
    fix v
    assume a1:"v \<in> qubit_of_dim n"
    then show "v \<in> {module.lincomb (module_cpx_vec (2^n)) a A |a A.
               finite A \<and> A \<subseteq> unit_vectors (2^n) \<and> a \<in> A \<rightarrow> UNIV \<and> \<parallel>module.lincomb (module_cpx_vec (2^n)) a A\<parallel> = 1}"
    proof-
      obtain a and A where "finite A" and "a\<in> A \<rightarrow> UNIV" and "A \<subseteq> unit_vectors (2^n)" and 
        "v = module.lincomb (module_cpx_vec (2^n)) a A"
        using a1 qubit_of_dim_def unit_vectors_is_basis vectorspace.basis_def module.span_def 
        vecspace_cpx_vec module_cpx_vec module_cpx_vec_def module_vec_def carrier_vec_def
        by (smt Pi_UNIV UNIV_I mem_Collect_eq module_vec_simps(3))
      thus ?thesis
        using a1 qubit_of_dim_def 
        by auto
    qed
  qed
  show "{module.lincomb (module_cpx_vec (2 ^ n)) a A |a A.
     finite A \<and> A \<subseteq> unit_vectors (2 ^ n) \<and> a \<in> A \<rightarrow> UNIV \<and> \<parallel>module.lincomb (module_cpx_vec (2 ^ n)) a A\<parallel> = 1}
    \<subseteq> qubit_of_dim n"
  proof
    fix v
    assume "v \<in> {module.lincomb (module_cpx_vec (2 ^ n)) a A |a A.
              finite A \<and> A \<subseteq> unit_vectors (2 ^ n) \<and> a \<in> A \<rightarrow> UNIV \<and> \<parallel>module.lincomb (module_cpx_vec (2 ^ n)) a A\<parallel> = 1}"
    then show "v\<in> qubit_of_dim n"
      using qubit_of_dim_def dim_vec_lincomb unit_vectors_carrier_vec
      by (smt mem_Collect_eq order_trans)
  qed
qed



end
