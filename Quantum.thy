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

definition qubit_of_dim:: "nat \<Rightarrow> _ set" where
"qubit_of_dim n \<equiv> {v| v:: complex vec. dim_vec v = 2^n \<and> cpx_vec_length v = 1}"

lemma qubit_of_dim_is_qubit:
  assumes "v \<in> qubit_of_dim n"
  shows "v \<in> {v| n v::complex vec. dim_vec v = 2^n \<and> cpx_vec_length v = 1}"
  using assms qubit_of_dim_def
  by simp

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
declare [[coercion cpx_sqr_mat_to_cpx_mat]]

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

(* Our first quantum gate: the identity matrix ! Arguably, not a very interesting one though ! *)

definition id_gate :: "nat \<Rightarrow> gate" where
"id_gate n \<equiv> Abs_gate (1\<^sub>m (2^n))"

(* We prove that a quantum gate is invertible and its inverse is given by its Hermitian conjugate *)

lemma gate_is_inv:
  shows "invertible_mat (A::gate)"
proof-
  have f1:"square_mat A"
    using Rep_gate gate_to_cpx_mat_def 
    by simp
  have f2:"inverts_mat A (hermite_cnj A)"
    using inverts_mat_def Rep_gate gate_to_cpx_mat_def unitary_def 
    by auto
  have f3:"inverts_mat (hermite_cnj A) A"
    using Rep_gate gate_to_cpx_mat_def unitary_def hermite_cnj_dim_row
    by (simp add: inverts_mat_def)
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

(* A unitary matrix is length-preserving, i.e. it acts on a vector to produce another vector of the 
same length. As a consequence, we prove that a quantum gate acting on a qubit really produces a 
qubit *)

lemma gate_on_qubit_is_qubit:
  assumes ""



end