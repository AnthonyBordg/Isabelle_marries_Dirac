theory Quantum
imports 
  Main 
  Power 
  Real 
  Complex 
  "Jordan_Normal_Form.Matrix"
  "HOL-Library.Nonpos_Ints"
begin

section \<open>Qubits and Quantum Gates\<close>

subsection \<open>Basics of Qubits and Quantum Gates\<close>

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

definition basis_qubit :: "nat \<Rightarrow> nat \<Rightarrow> qubit" where
"basis_qubit n i \<equiv> Abs_qubit (unit_vec (2^n) i)"

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

definition cpx_vec_to_cpx_mat :: "complex vec \<Rightarrow> complex mat" where
"cpx_vec_to_cpx_mat v \<equiv> mat (dim_vec v) 1 (\<lambda>(i,j). vec_index v i)"

(* Based on the definition above, we introduce a coercion from complex vectors to complex (column) 
matrices, then by composition the coercion algorithm will infer a coercion from qubits to complex
matrices  *)

declare [[coercion cpx_vec_to_cpx_mat]]

definition app :: "gate \<Rightarrow> qubit \<Rightarrow> qubit" where
"app A v \<equiv> Abs_qubit (col (Rep_gate A * v) 1)"

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

(* As a consequence, we prove that a quantum gate acting on a qubit gives a qubit *)

lemma gate_on_qubit_is_qubit:
  fixes U::"gate" and v::"qubit"
  assumes "Rep_gate U \<in> gate_of_dim n" and "Rep_qubit v \<in> qubit_of_dim n"
  shows "Rep_qubit (app U v) \<in> qubit_of_dim n"

subsection \<open>A Few Well-known Quantum Gates\<close>

(* Our first quantum gate: the identity matrix ! Arguably, not a very interesting one though ! *)
definition id_gate :: "nat \<Rightarrow> gate" where
"id_gate n \<equiv> Abs_gate (1\<^sub>m (2^n))"

end