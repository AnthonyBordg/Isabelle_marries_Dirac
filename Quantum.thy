theory Quantum
imports 
  Main 
  Power 
  Real 
  Complex 
  "Jordan_Normal_Form.Matrix"
begin

(* In this theory "cpx" stands for "complex" *)
definition cpx_vec_length :: "complex vec \<Rightarrow> real" where
"cpx_vec_length v \<equiv> sqrt(\<Sum>i< dim_vec v.(cmod (vec_index v i))^2)"

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
  shows "cpx_vec_length (unit_vec n i) = 1"
proof-
  have f1:"(\<Sum>j<n. cmod(vec_index (unit_vec n i) j)^2) = (\<Sum>j<n. if j = i then 1 else 0)"
    using norm_vec_index_unit_vec_is_0 norm_vec_index_unit_vec_is_1
    by (smt lessThan_iff one_power2 sum.cong zero_power2) 
  also have "(\<Sum>j<n. if j = i then 1 else 0) = 1"
    using assms  
    by simp
  then have "(\<Sum>j<n. cmod(vec_index (unit_vec n i) j)^2) = 1"
    using f1 
    by simp
  then have "sqrt (\<Sum>j<n. cmod(vec_index (unit_vec n i) j)^2) = 1" 
    by simp
  thus ?thesis
    using cpx_vec_length_def 
    by simp
qed

typedef qubit = "{v| n v::complex vec. dim_vec v = 2^n \<and> cpx_vec_length v = 1}"
  using unit_cpx_vec_length[of 0 "2^n"]
  by (smt index_unit_vec(3) less_numeral_extra(1) mem_Collect_eq power_0 unit_cpx_vec_length)

(* Below the natural number n codes for the dimension of the complex vector space where the qubits 
live *)
lemma unit_vec_of_right_length_is_qubit:
  assumes "i < 2^n"
  shows "unit_vec (2^n) i \<in> {v| n v::complex vec. dim_vec v = 2^n \<and> cpx_vec_length v = 1}"
proof-
  have f1:"dim_vec (unit_vec (2^n) i) = 2^n" 
    by simp
  have f2:"cpx_vec_length (unit_vec (2^n) i) = 1"
    using assms unit_cpx_vec_length
    by simp
  thus "unit_vec (2^n) i \<in> {v| n v::complex vec. dim_vec v = 2^n \<and> cpx_vec_length v = 1}"
    using f1 f2 
    by simp
qed

definition basis_qubit :: "nat \<Rightarrow> nat \<Rightarrow> qubit" where
"basis_qubit n i \<equiv> Abs_qubit (unit_vec (2^n) i)"

(* The Hermitian conjugate of a complex matrix is the complex conjugate of its transpose *)
definition hermite_cnj :: "complex mat \<Rightarrow> complex mat" where
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
declare 
  [[coercion_enabled]]
  [[coercion cpx_sqr_mat_to_cpx_mat]]


lemma hermite_cnj_dim_row:
  shows "dim_row (hermite_cnj A) = dim_col A"
  using hermite_cnj_def 
  by simp

lemma hermite_cnj_dim_col:
  shows "dim_col (hermite_cnj A) = dim_row A"
  using hermite_cnj_def
  by simp

lemma hermite_cnj_of_sqr_is_sqr:
  shows "square_mat (hermite_cnj (A::cpx_sqr_mat))"
proof-
  have "square_mat A"
    using cpx_sqr_mat_to_cpx_mat_def Rep_cpx_sqr_mat 
    by auto
  then have "dim_row A = dim_col A" 
    by simp
  then have "dim_col (hermite_cnj A) = dim_row (hermite_cnj A)"
    using hermite_cnj_dim_col hermite_cnj_dim_row 
    by simp
  thus "square_mat (hermite_cnj A)" 
    by simp
qed

lemma hermite_cnj_of_id_is_id:
  shows "hermite_cnj (1\<^sub>m n) = 1\<^sub>m n"
  using hermite_cnj_def one_mat_def 
  by auto

definition unitary :: "complex mat \<Rightarrow> bool" where
"unitary A \<equiv> hermite_cnj A * A = 1\<^sub>m (dim_col A) \<and> A * hermite_cnj A = 1\<^sub>m (dim_row A)"

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

(* Our first quantum gate: the identity matrix ! Arguably, not a very interesting one though ! *)

definition id_gate :: "nat \<Rightarrow> gate" where
"id_gate n \<equiv> Abs_gate (1\<^sub>m (2^n))"


end