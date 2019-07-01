
theory Deutsch_Algorithm 
imports
  MoreTensor
  Jordan_Normal_Form.Matrix
  Quantum(* , Jordan_Normal_Form.Matrix
            Quantum , no need for those files since they are imported when you import MoreTensor 
            HL: just temp seems to finds relevant facts better*)
begin


(*sledgehammer_params [verbose=true]*)
  
section \<open>Deutsch's algorithm\<close>

subsection \<open>Black-box function\<close>

text \<open>
A constant function with values in {0,1} returns either always 0 or always 1. 
A balanced function is 0 for half of the inputs and 1 for the other half. 
\<close>

locale deutsch =
  fixes f:: "nat \<Rightarrow> nat" 
  assumes dom: "f \<in> ({0,1} \<rightarrow>\<^sub>E {0,1})"

locale is_swap = deutsch +
  assumes swapping: "\<forall>x. f x = 1 - x"

context is_swap
begin

lemma is_swap_values:
  shows "f 0 = 1" and "f 1 = 0" using swapping by auto

end (* context is_swap *)

sublocale is_swap \<subseteq> deutsch by (simp add: deutsch_axioms)

  
context deutsch
begin

definition const:: "nat \<Rightarrow> bool" where 

"const n = (\<forall>x.(f x = n))"

definition deutsch_const:: "bool" where (* AB: this definition might be useful later *)
"deutsch_const \<equiv> const 0 \<or> const 1"

definition balanced:: "bool" where
"balanced \<equiv> f = id \<or> is_swap f"

lemma f_values: "(f 0 = 0 \<or> f 0 = 1) \<and> (f 1 = 0 \<or> f 1 = 1)" using dom by auto 
end (* context deutsch *)


text \<open>Black box function @{text U\<^sub>f}. \<close>

definition (in deutsch) deutsch_transform:: "complex Matrix.mat" ("U\<^sub>f") where 

"U\<^sub>f \<equiv> mat_of_cols_list 4 [[1 - f(0), f(0), 0, 0],
                          [f(0), 1 - f(0), 0, 0],
                          [0, 0, 1 - f(1), f(1)],
                          [0, 0, f(1), 1 - f(1)]]"

lemma set_two [simp]:
  fixes i:: nat
  assumes "i < 2"
  shows "i = 0 \<or> i = Suc 0"
  using assms by auto

lemma set_four [simp]: 
  fixes i:: nat
  assumes "i < 4"
  shows "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
  by (auto simp add: assms)

lemma (in deutsch) deutsch_transform_dim [simp]: 
  shows "dim_row U\<^sub>f = 4" and "dim_col U\<^sub>f = 4" 
  by (auto simp add: deutsch_transform_def mat_of_cols_list_def)

lemma (in deutsch) deutsch_transform_coeff_is_zero [simp]: 
  shows "U\<^sub>f $$ (0,2) = 0" and "U\<^sub>f $$ (0,3) = 0"
    and "U\<^sub>f $$ (1,2) = 0" and "U\<^sub>f $$(1,3) = 0"
    and "U\<^sub>f $$ (2,0) = 0" and "U\<^sub>f $$(2,1) = 0"
    and "U\<^sub>f $$ (3,0) = 0" and "U\<^sub>f $$ (3,1) = 0"
  using deutsch_transform_def by auto

lemma (in deutsch) deutsch_transform_coeff [simp]: 
  shows "U\<^sub>f $$ (0,1) = f(0)" and "U\<^sub>f $$ (1,0) = f(0)"
    and "U\<^sub>f $$(2,3) = f(1)" and "U\<^sub>f $$ (3,2) = f(1)"
    and "U\<^sub>f $$ (0,0) = 1 - f(0)" and "U\<^sub>f $$(1,1) = 1 - f(0)"
    and "U\<^sub>f $$ (2,2) = 1 - f(1)" and "U\<^sub>f $$ (3,3) = 1 - f(1)"
  using deutsch_transform_def by auto

abbreviation (in deutsch) V\<^sub>f:: "complex Matrix.mat" where
"V\<^sub>f \<equiv> Matrix.mat 4 4 (\<lambda>(i,j). 
                if i=0 \<and> j=0 then 1 - f(0) else
                  (if i=0 \<and> j=1 then f(0) else
                    (if i=1 \<and> j=0 then f(0) else
                      (if i=1 \<and> j=1 then 1 - f(0) else
                        (if i=2 \<and> j=2 then 1 - f(1) else
                          (if i=2 \<and> j=3 then f(1) else
                            (if i=3 \<and> j=2 then f(1) else
                              (if i=3 \<and> j=3 then 1 - f(1) else 0))))))))"

lemma (in deutsch) deutsch_transform_alt_rep_coeff_is_zero [simp]:
  shows "V\<^sub>f $$ (0,2) = 0" and "V\<^sub>f $$ (0,3) = 0"
    and "V\<^sub>f $$ (1,2) = 0" and "V\<^sub>f $$(1,3) = 0"
    and "V\<^sub>f $$ (2,0) = 0" and "V\<^sub>f $$(2,1) = 0"
    and "V\<^sub>f $$ (3,0) = 0" and "V\<^sub>f $$ (3,1) = 0"
  by auto

lemma (in deutsch) deutsch_transform_alt_rep_coeff [simp]:
  shows "V\<^sub>f $$ (0,1) = f(0)" and "V\<^sub>f $$ (1,0) = f(0)"
    and "V\<^sub>f $$(2,3) = f(1)" and "V\<^sub>f $$ (3,2) = f(1)"
    and "V\<^sub>f $$ (0,0) = 1 - f(0)" and "V\<^sub>f $$(1,1) = 1 - f(0)"
    and "V\<^sub>f $$ (2,2) = 1 - f(1)" and "V\<^sub>f $$ (3,3) = 1 - f(1)"
  by auto

lemma (in deutsch) deutsch_transform_alt_rep:
  shows "U\<^sub>f = V\<^sub>f"
proof
  show c0:"dim_row U\<^sub>f = dim_row V\<^sub>f" by simp
  show c1:"dim_col U\<^sub>f = dim_col V\<^sub>f" by simp
  fix i j:: nat
  assume "i < dim_row V\<^sub>f" and "j < dim_col V\<^sub>f"
  then have "i < 4" and "j < 4" by auto
  then show "U\<^sub>f $$ (i,j) = V\<^sub>f $$ (i,j)"
    by (smt deutsch_transform_alt_rep_coeff deutsch_transform_alt_rep_coeff_is_zero deutsch_transform_coeff
 deutsch_transform_coeff_is_zero set_four)
qed


text \<open>@{text U\<^sub>f} is a gate.\<close>


lemma (in deutsch) transpose_of_deutsch_transform:
  shows "(U\<^sub>f)\<^sup>t = U\<^sub>f"
proof
  show "dim_row U\<^sub>f\<^sup>t = dim_row U\<^sub>f" by simp
  show "dim_col U\<^sub>f\<^sup>t = dim_col U\<^sub>f" by simp
  fix i j:: nat
  assume "i < dim_row U\<^sub>f" and "j < dim_col U\<^sub>f"
  then show "U\<^sub>f\<^sup>t $$ (i, j) = U\<^sub>f $$ (i, j)"
    apply (auto simp add: transpose_mat_def)
    by (metis deutsch_transform_coeff(1-4) deutsch_transform_coeff_is_zero set_four)
qed

lemma (in deutsch) adjoint_of_deutsch_transform: 
  shows "(U\<^sub>f)\<^sup>\<dagger> = U\<^sub>f"
proof
  show "dim_row U\<^sub>f\<^sup>\<dagger> = dim_row U\<^sub>f" by simp
  show "dim_col U\<^sub>f\<^sup>\<dagger> = dim_col U\<^sub>f" by simp
  fix i j:: nat
  assume "i < dim_row U\<^sub>f" and "j < dim_col U\<^sub>f"
  then show "U\<^sub>f\<^sup>\<dagger> $$ (i, j) = U\<^sub>f $$ (i, j)"
    apply (auto simp add: hermite_cnj_def)
    by (metis complex_cnj_of_nat complex_cnj_zero deutsch_transform_coeff 
deutsch_transform_coeff_is_zero set_four)
qed

lemma (in deutsch) deutsch_transform_is_gate: (* AB: I tidied up the proof a little bit *)
  shows "gate 2 U\<^sub>f"
proof
  show "dim_row U\<^sub>f = 2\<^sup>2" by simp
next
  show "square_mat U\<^sub>f" by simp
next
  show "unitary U\<^sub>f"
  proof-
    have "U\<^sub>f * U\<^sub>f = 1\<^sub>m (dim_col U\<^sub>f)"
    proof
      show "dim_row (U\<^sub>f * U\<^sub>f) = dim_row (1\<^sub>m (dim_col U\<^sub>f))" by simp
    next
      show "dim_col (U\<^sub>f * U\<^sub>f) = dim_col (1\<^sub>m (dim_col U\<^sub>f))" by simp
    next
      fix i j:: nat
      assume "i < dim_row (1\<^sub>m (dim_col U\<^sub>f))" and "j < dim_col (1\<^sub>m (dim_col U\<^sub>f))"
      then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)"
        apply (auto simp add: deutsch_transform_alt_rep one_mat_def times_mat_def)
         apply (auto simp: scalar_prod_def algebra_simps) 
        using f_values apply auto.
    qed
    thus ?thesis by (simp add: adjoint_of_deutsch_transform unitary_def)
  qed
qed
   
(* AB: in the comment below you have forgotten the antiquotations. *)
text \<open>Two qubits are prepared. The first one in the state |0\<rangle>, the second one in the state |1\<rangle>.\<close>

(*From here on under construction*)
(*HL Question: in text do I need to use @{text \<psi>\<^sub>0\<^sub>0} for objects from Isabelle?
Not done in Quantum for bell states *)
(* AB: here you may want to use @{text \<psi>\<^sub>0\<^sub>0} indeed. But it depends on what comes after the 
antiquotation, see 4.2 of the Isar reference manual 2019. Maybe you want to use @{term } or 
@{abbrev }.
Thanks, I will add the forgotten antiquotations in Quantum.thy. *)

(*HL: Already define these with mat_of_cols_list? *)
(* AB: I don't think it is necessary here, but see how it goes and then see if you need some changes.*)


abbreviation zero ("0") where "zero \<equiv> unit_vec 2 0"
abbreviation one ("1") where "one \<equiv> unit_vec 2 1" 


(* AB: why not use directly unit_vec to define zero_state ? 
Anyway, if I understand correctly you want to use the elements |0\<rangle> and |1\<rangle>. The elements of the
computational basis have very standard notations, so maybe you should stick to those notations and 
avoid something like |zero_state\<rangle>. So, I propose to use the standard notations.
If at some point Isabelle complains too much about the ambiguity you can still use |zero\<rangle> 
instead of |0\<rangle> and the same for 1. *)

lemma ket_zero_is_state: 
  shows "state 1 |0\<rangle>"
  by (simp add: state_def ket_vec_def cpx_vec_length_def numerals(2))

lemma ket_one_is_state:
  shows "state 1 |1\<rangle>" 
  by (simp add: state_def ket_vec_def cpx_vec_length_def numerals(2))

lemma ket_zero_to_mat_of_cols_list [simp]: "|0\<rangle> = mat_of_cols_list 2 [[1, 0]]"
  by (auto simp add: ket_vec_def mat_of_cols_list_def)

lemma ket_one_to_mat_of_cols_list [simp]: "|1\<rangle> = mat_of_cols_list 2 [[0, 1]]"
  apply (auto simp add: ket_vec_def unit_vec_def mat_of_cols_list_def)
  using less_2_cases by fastforce


(* AB: In the comments below you have forgotten some antiquotations. *)
text\<open>
Applying the Hadamard gate to state |0\<rangle> results in the new state @{text \<psi>\<^sub>0\<^sub>0}=(|0\<rangle>+|1\<rangle>)/$/sqrt(2)$.
\<close>

abbreviation \<psi>\<^sub>0\<^sub>0:: "complex Matrix.mat" where
"\<psi>\<^sub>0\<^sub>0 \<equiv> mat_of_cols_list 2 [[1/sqrt(2), 1/sqrt(2)]]"

lemma H_on_ket_zero: (*TODO: maybe rename it*)
  shows "(H * |0\<rangle>) = \<psi>\<^sub>0\<^sub>0"
proof 
  fix i j::nat
  assume "i<dim_row \<psi>\<^sub>0\<^sub>0" and "j < dim_col \<psi>\<^sub>0\<^sub>0"
  then have "i\<in>{0,1} \<and> j=0" using mat_of_cols_list_def by auto
  then show "(H * |0\<rangle>)$$(i,j) = \<psi>\<^sub>0\<^sub>0$$(i,j)"
    by (auto simp add: mat_of_cols_list_def times_mat_def scalar_prod_def H_def)
next
  show "dim_row (H * |0\<rangle>) = dim_row \<psi>\<^sub>0\<^sub>0" 
    by (metis H_inv mat_of_cols_list_def dim_row_mat(1) index_mult_mat(2) index_one_mat(2))
next 
  show "dim_col (H * |0\<rangle>) = dim_col \<psi>\<^sub>0\<^sub>0" 
    using H_def mat_of_cols_list_def by simp
qed

lemma H_on_ket_zero_is_state: 
  shows "state 1 (H * |0\<rangle>)"
proof
  show "gate 1 H" 
    using H_is_gate by auto
next
  show "state 1 |0\<rangle>" 
    using ket_zero_is_state by blast
qed



text\<open>
Applying the Hadamard gate to state |1\<rangle> results in the new state @{text \<psi>\<^sub>0\<^sub>1}=(|0\<rangle>-|1\<rangle>)/$/sqrt(2)$.
\<close>

abbreviation \<psi>\<^sub>0\<^sub>1:: "complex Matrix.mat" where
"\<psi>\<^sub>0\<^sub>1 \<equiv> mat_of_cols_list 2 [[1/sqrt(2), -1/sqrt(2)]]"

lemma H_on_ket_one: (*TODO: maybe rename it*) (* AB: now it is renamed! *)
  shows "(H * |1\<rangle>) = \<psi>\<^sub>0\<^sub>1"
proof 
  fix i j::nat
  assume "i<dim_row \<psi>\<^sub>0\<^sub>1" and "j < dim_col \<psi>\<^sub>0\<^sub>1"
  then have "i\<in>{0,1} \<and> j=0" using mat_of_cols_list_def by auto
  then show "(H * |1\<rangle>) $$ (i,j) = \<psi>\<^sub>0\<^sub>1 $$ (i,j)"
    by (auto simp add: mat_of_cols_list_def times_mat_def scalar_prod_def H_def ket_vec_def)
next
  show "dim_row (H * |1\<rangle>) = dim_row \<psi>\<^sub>0\<^sub>1" 
    by (metis H_inv mat_of_cols_list_def dim_row_mat(1) index_mult_mat(2) index_one_mat(2))
next 
  show "dim_col (H * |1\<rangle>) = dim_col \<psi>\<^sub>0\<^sub>1" 
    by (simp add: H_def mat_of_cols_list_def ket_vec_def)
qed

lemma H_on_ket_one_is_state: 
  shows "state 1 (H * |1\<rangle>)"
proof
  show "gate 1 H" 
    using H_is_gate by auto
next
  show "state 1 |1\<rangle>" 
    using ket_one_is_state by blast
qed


text\<open>
Then, state @{text \<psi>\<^sub>1}=(|00\<rangle>-|01\<rangle>+|10\<rangle>-|11\<rangle>)/2 is obtained by taking the tensor product of state 
 @{text \<psi>\<^sub>0\<^sub>0}=(|0\<rangle>+|1\<rangle>)/$/sqrt(2)$ and  @{text \<psi>\<^sub>0\<^sub>1}=(|0\<rangle>-|1\<rangle>)/$/sqrt(2)$.
\<close>

abbreviation \<psi>\<^sub>1:: "complex Matrix.mat" where
"\<psi>\<^sub>1 \<equiv> mat_of_cols_list 4 [[1/2,-1/2,1/2,-1/2]]"

lemma \<psi>\<^sub>0_to_\<psi>\<^sub>1: 
  shows "(\<psi>\<^sub>0\<^sub>0 \<Otimes> \<psi>\<^sub>0\<^sub>1) = \<psi>\<^sub>1"
proof 
  fix i j::nat
  assume "i < dim_row \<psi>\<^sub>1" and "j < dim_col \<psi>\<^sub>1"
  then have "i\<in>{0,1,2,3}" and "j=0" using mat_of_cols_list_def by auto  
  moreover have "complex_of_real (sqrt 2) * complex_of_real (sqrt 2) = 2" 
    by (metis mult_2_right numeral_Bit0 of_real_mult of_real_numeral real_sqrt_four real_sqrt_mult)
  ultimately show "(\<psi>\<^sub>0\<^sub>0 \<Otimes> \<psi>\<^sub>0\<^sub>1)$$(i,j) = \<psi>\<^sub>1$$(i,j)" using mat_of_cols_list_def by auto
next 
  show "dim_row (\<psi>\<^sub>0\<^sub>0 \<Otimes> \<psi>\<^sub>0\<^sub>1) = dim_row \<psi>\<^sub>1" using mat_of_cols_list_def by auto
next
  show "dim_col (\<psi>\<^sub>0\<^sub>0 \<Otimes> \<psi>\<^sub>0\<^sub>1) = dim_col \<psi>\<^sub>1" using mat_of_cols_list_def by auto
qed


lemma \<psi>\<^sub>1_is_state: 
  shows "state 2 \<psi>\<^sub>1"
proof 
  show  "dim_col \<psi>\<^sub>1 = 1" 
    by (simp add: Tensor.mat_of_cols_list_def)
next 
  show "dim_row \<psi>\<^sub>1 = 2\<^sup>2" 
    by (simp add: Tensor.mat_of_cols_list_def)
next
  show "\<parallel>Matrix.col \<psi>\<^sub>1 0\<parallel> = 1"
    using H_on_ket_one_is_state H_on_ket_zero_is_state state.length tensor_state2 \<psi>\<^sub>0_to_\<psi>\<^sub>1
H_on_ket_one H_on_ket_zero by force
qed



text \<open>Next, the gate @{text U\<^sub>f} is applied to state @{text \<psi>\<^sub>1}=(|00\<rangle>-|01\<rangle>+|10\<rangle>-|11\<rangle>)/2
 and @{text \<psi>\<^sub>2}= $(|0 f(0) \oplus 0\<rangle>-|0 f(0) \oplus 1\<rangle>+|1 f(1) \oplus 0\<rangle>-|1 f(1) \oplus 1\<rangle>)/2$ is obtained.
This simplifies to @{text \<psi>\<^sub>2}= $(|0 f(0)\<rangle>-|0 \overline{f(0)}\<rangle>+|1 f(1)\<rangle>-|1 \overline{f(1)}\<rangle>)/2$  \<close>

abbreviation (in deutsch) \<psi>\<^sub>2:: "complex Matrix.mat" where
"\<psi>\<^sub>2 \<equiv>  mat_of_cols_list 4 [[(1 - f(0))/2 - f(0)/2,
                            f(0)/2 - (1 - f(0))/2,
                            (1 - f(1))/2 - f(1)/2,
                            f(1)/2 - (1- f(1))/2]]"


text \<open> @{text U\<^sub>f} is applied to state @{text \<psi>\<^sub>1} and @{text \<psi>\<^sub>2} is obtained. \<close>

lemma (in deutsch) \<psi>\<^sub>1_to_\<psi>\<^sub>2: 
  shows "U\<^sub>f * \<psi>\<^sub>1 = \<psi>\<^sub>2"
proof 
  fix i j:: nat
  assume "i<dim_row \<psi>\<^sub>2 " and "j<dim_col \<psi>\<^sub>2"
  then have a0:"i\<in>{0,1,2,3} \<and> j=0 " 
    using mat_of_cols_list_def by auto
  then have "i<dim_row U\<^sub>f \<and> j<dim_col \<psi>\<^sub>1" using deutsch_transform_def mat_of_cols_list_def by auto
  then have "(U\<^sub>f * \<psi>\<^sub>1) $$ (i, j) 
        = (\<Sum> k \<in> {0 ..< dim_vec \<psi>\<^sub>1}. (Matrix.row U\<^sub>f i) $ k * (Matrix.col \<psi>\<^sub>1 j) $ k)"     
    using scalar_prod_def col_fst_is_col index_mult_mat sum.cong times_mat_def 
    by (smt dim_col)
  then show "(U\<^sub>f * \<psi>\<^sub>1) $$ (i, j) = \<psi>\<^sub>2 $$ (i, j)"
    using  mat_of_cols_list_def deutsch_transform_def a0 
      apply auto.
next
  show "dim_row (U\<^sub>f * \<psi>\<^sub>1) = dim_row \<psi>\<^sub>2" 
    using  mat_of_cols_list_def by auto
next
  show "dim_col (U\<^sub>f * \<psi>\<^sub>1) = dim_col \<psi>\<^sub>2"    
    using mat_of_cols_list_def by auto
qed


lemma (in deutsch) \<psi>\<^sub>2_is_state:
  shows "state 2 \<psi>\<^sub>2" 
proof
  show  "dim_col \<psi>\<^sub>2 = 1" 
    by (simp add: Tensor.mat_of_cols_list_def)
next 
  show "dim_row \<psi>\<^sub>2 = 2\<^sup>2" 
    by (simp add: Tensor.mat_of_cols_list_def)
next
  show "\<parallel>Matrix.col \<psi>\<^sub>2 0\<parallel> = 1"
    using \<psi>\<^sub>1_is_state deutsch_transform_is_gate \<psi>\<^sub>1_to_\<psi>\<^sub>2 
    by (smt gate_on_state_is_state state_def)
qed





lemma H_tensor_Id: 
  defines d:"v \<equiv>  mat_of_cols_list 4 [[1/sqrt(2), 0, 1/sqrt(2), 0],
                                 [0, 1/sqrt(2), 0, 1/sqrt(2)],
                                 [1/sqrt(2), 0, -1/sqrt(2), 0],
                                 [0, 1/sqrt(2), 0, -1/sqrt(2)]]"
  shows "(H \<Otimes> Id 1) = v" 
proof
  show "Matrix.dim_col (H \<Otimes> Id 1) = Matrix.dim_col v"  
    by(simp add: assms H_def Id_def mat_of_cols_list_def)
  show "dim_row (H \<Otimes> Id 1) = dim_row v"
    by(simp add: assms H_def Id_def mat_of_cols_list_def)
  fix i j::nat assume "i < dim_row v" and "j < dim_col v"
  then have "i \<in> {0..<4} \<and> j \<in> {0..<4}" 
    by (auto simp add: assms mat_of_cols_list_def)
  then show "(H \<Otimes> Id 1) $$ (i, j) = v $$ (i, j)"
    by (auto simp add: assms Id_def  H_def mat_of_cols_list_def)
qed


lemma H_tensor_Id_is_gate: "gate 2 (H \<Otimes> Id 1)" 

proof 
  show "dim_row (H \<Otimes> Quantum.Id 1) = 2\<^sup>2" using H_tensor_Id   
    by (simp add: Tensor.mat_of_cols_list_def)
next 
  show "square_mat (H \<Otimes> Quantum.Id 1)" 
    using H_is_gate id_is_gate tensor_gate_sqr_mat by blast
next 
  show "unitary (H \<Otimes> Quantum.Id 1)" 
    using H_is_gate gate_def id_is_gate tensor_gate by blast
qed


lemma (in deutsch) \<psi>\<^sub>3_is_state: 
   assumes "\<psi>\<^sub>2 \<equiv>  mat_of_cols_list 4 [[(inv_b (f 0))/2 - (f(0)::int)/2,
                                      (f(0)::int)/2 - (inv_b (f(0)))/2,
                                      (inv_b (f(1)))/2 - (f(1)::int)/2,
                                      (f(1)::int)/2 - inv_b(f(1))/2]]"
  shows "state 2 ((H \<Otimes> Id 1)*\<psi>\<^sub>2)"
proof 
  show "gate 2 (H \<Otimes> Quantum.Id 1)" 
    using H_tensor_Id_is_gate by blast
  show "state 2 \<psi>\<^sub>2" using \<psi>\<^sub>2_is_state \<psi>\<^sub>1_to_\<psi>\<^sub>2 assms by simp
qed

lemma (in deutsch) \<psi>\<^sub>2_to_\<psi>\<^sub>3: 
  assumes "\<psi>\<^sub>2 \<equiv>  mat_of_cols_list 4 [[(inv_b (f 0))/2 - (f(0)::int)/2,
                                      (f(0)::int)/2 - (inv_b (f(0)))/2,
                                      (inv_b (f(1)))/2 - (f(1)::int)/2,
                                      (f(1)::int)/2 - inv_b(f(1))/2]]"
  and "\<psi>\<^sub>3 \<equiv>  mat_of_cols_list 4 [[((inv_b (f 0))/(2* sqrt(2)) - f(0)/(2* sqrt(2)))
                                    + ((inv_b (f 1))/(2* sqrt(2)) -f(1)/(2* sqrt(2))),
                                 (f(0)/(2* sqrt(2)) - (inv_b (f(0)))/(2* sqrt(2)))
                                    + (f(1)/(2* sqrt(2)) - inv_b(f(1))/(2* sqrt(2))),
                                 ((inv_b (f 0))/(2* sqrt(2)) - f(0)/(2* sqrt(2))) 
                                    - ((inv_b (f(1)))/(2* sqrt(2)) - f(1)/(2* sqrt(2))),
                                  (f(0)/(2* sqrt(2)) -(inv_b (f(0)))/(2* sqrt(2))) 
                                    -(f(1)/(2* sqrt(2)) -inv_b(f(1))/(2* sqrt(2)))]]"
 shows "(H \<Otimes> Id 1)*\<psi>\<^sub>2 =  \<psi>\<^sub>3" 
proof
  fix i j ::nat
  assume "i < dim_row \<psi>\<^sub>3" and "j < dim_col \<psi>\<^sub>3" 
  then have a0: "i\<in>{0,1,2,3} \<and> j=0 " 
    using assms ket_vec_def mat_of_cols_list_def by auto
  then have "i<dim_row (H \<Otimes> Id 1)" and "j<dim_col \<psi>\<^sub>2" 
    using H_tensor_Id assms mat_of_cols_list_def by auto 
  then have "((H \<Otimes> Id 1) * \<psi>\<^sub>2) $$ (i, j) 
        = (\<Sum> k \<in> {0 ..< dim_vec \<psi>\<^sub>2}. (Matrix.row (H \<Otimes> Id 1) i) $ k * (Matrix.col \<psi>\<^sub>2 j) $ k)"     
    using scalar_prod_def col_fst_is_col index_mult_mat sum.cong
    by (smt a0)
  then have "((H \<Otimes> Id 1) * \<psi>\<^sub>2) $$ (i, j) = ((Matrix.row (H \<Otimes> Id 1) i) $ 0 * ( Matrix.col \<psi>\<^sub>2 0) $ 0) 
             + ((Matrix.row (H \<Otimes> Id 1) i) $ 1 * ( Matrix.col \<psi>\<^sub>2 0) $ 1) 
             + ((Matrix.row (H \<Otimes> Id 1) i) $ 2 * ( Matrix.col \<psi>\<^sub>2 0) $ 2) 
             + ((Matrix.row (H \<Otimes> Id 1) i) $ 3 * ( Matrix.col \<psi>\<^sub>2 0) $ 3) "
    using set_4 mat_of_cols_list_def assms scalar_prod_def times_mat_def a0 by simp
  then show "((H \<Otimes> Id 1) * \<psi>\<^sub>2) $$ (i, j) = \<psi>\<^sub>3 $$ (i, j)"
    using  H_tensor_Id mat_of_cols_list_def deutsch_transform_def assms a0 assms
      apply (auto simp add: algebra_simps)
    done
next
  show "dim_row ((H \<Otimes> Id 1) * \<psi>\<^sub>2) = dim_row \<psi>\<^sub>3" 
    using H_tensor_Id assms mat_of_cols_list_def by auto
next
  show "dim_col ((H \<Otimes> Id 1) * \<psi>\<^sub>2) = dim_col \<psi>\<^sub>3"    
    using assms mat_of_cols_list_def by auto
qed





definition (in deutsch) deutsch_algo::
"complex Matrix.mat" where (*TODO:Measurement*)
"deutsch_algo \<equiv> (H \<Otimes> Id 2) * U\<^sub>f * ((H * |x\<rangle>) \<Otimes> (H * |y\<rangle>))"

lemma (in deutsch) deutsch_algo_result: 
  shows "deutsch_algo = mat_of_cols_list 4 
                                        [[((inv_b (f 0))/(2* sqrt(2)) - f(0)/(2* sqrt(2)))
                                        + ((inv_b (f 1))/(2* sqrt(2)) -f(1)/(2* sqrt(2))),
                                        (f(0)/(2* sqrt(2)) - (inv_b (f(0)))/(2* sqrt(2)))
                                        + (f(1)/(2* sqrt(2)) - inv_b(f(1))/(2* sqrt(2))),
                                        ((inv_b (f 0))/(2* sqrt(2)) - f(0)/(2* sqrt(2))) 
                                        - ((inv_b (f(1)))/(2* sqrt(2)) - f(1)/(2* sqrt(2))),
                                       (f(0)/(2* sqrt(2)) -(inv_b (f(0)))/(2* sqrt(2))) 
                                        -(f(1)/(2* sqrt(2)) -inv_b(f(1))/(2* sqrt(2)))]]"
proof-
  have "deutsch_algo = (H \<Otimes> Id 2) * U\<^sub>f * ((H * |x\<rangle>) \<Otimes> (H * |y\<rangle>))" 
    using deutsch_algo_def by auto
  also have "... = (H \<Otimes> Id 2) * U\<^sub>f * (mat_of_cols_list 4 [[1/2, -1/2, 1/2, -1/2]])" 
    using \<psi>\<^sub>0_to_\<psi>\<^sub>1 sorry
  also have "... = (H \<Otimes> Id 2) * (mat_of_cols_list 4 [[(inv_b (f 0))/2 - (f(0)::int)/2,
                                      (f(0)::int)/2 - (inv_b (f(0)))/2,
                                      (inv_b (f(1)))/2 - (f(1)::int)/2,
                                      (f(1)::int)/2 - inv_b(f(1))/2]])" 
    apply (auto simp: \<psi>\<^sub>1_to_\<psi>\<^sub>2) sorry
  also have "... = mat_of_cols_list 4 [[((inv_b (f 0))/(2* sqrt(2)) - f(0)/(2* sqrt(2)))
                                        + ((inv_b (f 1))/(2* sqrt(2)) -f(1)/(2* sqrt(2))),
                                        (f(0)/(2* sqrt(2)) - (inv_b (f(0)))/(2* sqrt(2)))
                                        + (f(1)/(2* sqrt(2)) - inv_b(f(1))/(2* sqrt(2))),
                                        ((inv_b (f 0))/(2* sqrt(2)) - f(0)/(2* sqrt(2))) 
                                        - ((inv_b (f(1)))/(2* sqrt(2)) - f(1)/(2* sqrt(2))),
                                       (f(0)/(2* sqrt(2)) -(inv_b (f(0)))/(2* sqrt(2))) 
                                        -(f(1)/(2* sqrt(2)) -inv_b(f(1))/(2* sqrt(2)))]]"
    using \<psi>\<^sub>2_to_\<psi>\<^sub>3 sorry
  finally show "deutsch_algo = mat_of_cols_list 4 [[((inv_b (f 0))/(2* sqrt(2)) - f(0)/(2* sqrt(2)))
                                        + ((inv_b (f 1))/(2* sqrt(2)) -f(1)/(2* sqrt(2))),
                                        (f(0)/(2* sqrt(2)) - (inv_b (f(0)))/(2* sqrt(2)))
                                        + (f(1)/(2* sqrt(2)) - inv_b(f(1))/(2* sqrt(2))),
                                        ((inv_b (f 0))/(2* sqrt(2)) - f(0)/(2* sqrt(2))) 
                                        - ((inv_b (f(1)))/(2* sqrt(2)) - f(1)/(2* sqrt(2))),
                                       (f(0)/(2* sqrt(2)) -(inv_b (f(0)))/(2* sqrt(2))) 
                                        -(f(1)/(2* sqrt(2)) -inv_b(f(1))/(2* sqrt(2)))]]"  by blast
qed

lemma (in deutsch) deutsch_algo_result_state: 
  shows "state 2 deutsch_algo"
  sorry


lemma (in deutsch)
  assumes "const 0 \<or> const 1" 
  shows "fst ((meas 2 deutsch_algo 0)!0) = 0" sorry



lemma (in deutsch) prob0_bell_fst:
  assumes "const 0 \<or> const 1" 
  shows "prob0 2 deutsch_algo 0 = 1" 
proof -
  have set_0 [simp]:"{k| k::nat. (k<4) \<and> \<not> select_index 2 0 k} = {0,1}"
    using select_index_def by auto
  have "state 2 deutsch_algo" sorry
  then have "prob0 2 deutsch_algo 0 = (\<Sum>j\<in>{k| k::nat. (k<4) \<and> \<not> select_index 2 0 k}. (cmod(deutsch_algo $$ (j,0)))\<^sup>2)"
     apply (auto simp: prob0_def).
  then have "prob0 2 deutsch_algo 0= (\<Sum>j\<in>{0,1}. (cmod(deutsch_algo $$ (j,0)))\<^sup>2)"
    using set_0 by simp
  show "prob0 2 deutsch_algo 0 = 1" 
  proof (rule disjE)
    show "const 0 \<or> const 1" using assms by simp
  next
    assume a0: "const 0"
    have "prob0 2 deutsch_algo 0 = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(-1/sqrt(2)))\<^sup>2" sorry
    moreover have "deutsch_algo $$ (0,0)  = 1/ sqrt(2)" 
      using assms a0 const_def inv_b_def deutsch_algo_result by auto
    moreover have "deutsch_algo $$ (1,0)  = -1/ sqrt(2)" 
      using assms a0 const_def inv_b_def deutsch_algo_result by auto
    moreover have "deutsch_algo $$ (2,0)  = 0" 
      using assms const_def inv_b_def deutsch_algo_result by auto
    moreover have "deutsch_algo $$ (3,0)  = 0" 
      using assms const_def inv_b_def deutsch_algo_result by auto  
    ultimately show "prob0 2 deutsch_algo 0 = 1" sorry
  next
    assume a1: "const 1"
    have "prob0 2 deutsch_algo 0 = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(-1/sqrt(2)))\<^sup>2" sorry
    moreover have "deutsch_algo $$ (0,0)  = -1/ sqrt(2)" 
      using assms a1 const_def inv_b_def deutsch_algo_result by auto
    moreover have "deutsch_algo $$ (1,0)  = 1/ sqrt(2)" 
      using assms a1 const_def inv_b_def deutsch_algo_result by auto
    moreover have "deutsch_algo $$ (2,0)  = 0" 
      using assms const_def inv_b_def deutsch_algo_result by auto
    moreover have "deutsch_algo $$ (3,0)  = 0" 
      using assms const_def inv_b_def deutsch_algo_result by auto  
    ultimately show "prob0 2 deutsch_algo 0 = 1" sorry
qed



end
