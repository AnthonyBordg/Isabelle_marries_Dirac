
theory Deutsch_Algorithm 
imports
  MoreTensor
  Jordan_Normal_Form.Matrix
  Quantum(* , Jordan_Normal_Form.Matrix
            Quantum , no need for those files since they are imported when you import MoreTensor 
            HL: just temp seems to finds relevant facts better*)
begin

(*TODO: Change all matrices to mat_of_cols_list representation? Made proof of H_tensor_Id 
much easier.*)
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


(*
AB: I don't think this definition is useful, it's not really 
shorter than 1 - f(x) and it's less transparent
definition 1 - :: "nat \<Rightarrow> int" where
"1 -  n \<equiv> (case n of 0 \<Rightarrow> 1 
                     |(Suc 0) \<Rightarrow> 0)" *)


text \<open>Black box function @{text U\<^sub>f}. \<close>

definition (in deutsch) deutsch_transform:: "complex Matrix.mat" ("U\<^sub>f") where 

(*"U\<^sub>f \<equiv> Matrix.mat 4 4 (\<lambda>(i,j). 
        if i=0 \<and> j=0 then 1 -  (f(0)) else
          (if i=0 \<and> j=1 then f(0) else
            (if i=1 \<and> j=0 then f(0) else
              (if i=1 \<and> j=1 then 1 -  (f(0)) else
                (if i=2 \<and> j=2 then 1 -  (f(1)) else
                  (if i=2 \<and> j=3 then f(1) else
                    (if i=3 \<and> j=2 then f(1) else
                      (if i=3 \<and> j=3 then 1 -  (f(1)) else 0))))))))"
AB: the representation of U\<^sub>f below should be easier to handle. Also, note that this matrix being its
own transpose by writing the columns one below another we get the picture of our matrix ! *)
"U\<^sub>f \<equiv> mat_of_cols_list 4 [[1 - f(0), f(0), 0, 0],
                          [f(0), 1 - f(0), 0, 0],
                          [0, 0, 1 - f(1), f(1)],
                          [0, 0, f(1), 1 - f(1)]]"

lemma set_four [simp]: (* AB: for the statements themselves, I always prefer the structured style,
even when the statement is fairly simple like this one. *)
  fixes i:: nat
  assumes "i < 4"
  shows "i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3"
  by (auto simp add: assms)
(*"\<forall>i::nat. i < 4 \<longrightarrow> i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3" by auto*)

lemma (in deutsch) deutsch_transform_dim [simp]: 
  shows "dim_row U\<^sub>f = 4" and "dim_col U\<^sub>f = 4" 
  by (auto simp add: deutsch_transform_def mat_of_cols_list_def)
  (* using deutsch_transform_def by auto *)

lemma (in deutsch) deutsch_transform_coeff_is_zero [simp]: (* AB: I chose a less misleading name *)
  shows "U\<^sub>f $$ (0,2) = 0" and "U\<^sub>f $$ (0,3) = 0"
    and "U\<^sub>f $$ (1,2) = 0" and "U\<^sub>f $$(1,3) = 0"
    and "U\<^sub>f $$ (2,0) = 0" and "U\<^sub>f $$(2,1) = 0"
    and "U\<^sub>f $$ (3,0) = 0" and "U\<^sub>f $$ (3,1) = 0"
  using deutsch_transform_def by auto

lemma (in deutsch) deutsch_transform_coeff [simp]: (* AB: idem, indeed if f 0 = 0 then 
U\<^sub>f $$ (0,1) = 0 for instance *)
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

(* AB: by proving the lemma below one can build a bridge between the new representation of your matrix
and the former one, I am not sure it's useful though *)
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

(* AB: intermediate lemmas are needed to have a clean proof of adjoint_of_deutsch_transform *)

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

lemma (in deutsch) deutsch_transform_is_gate: 
  shows "gate 2 U\<^sub>f"
proof
  show "dim_row U\<^sub>f = 2\<^sup>2" by simp
next
  show "square_mat U\<^sub>f" by simp
next
  have "U\<^sub>f * U\<^sub>f = 1\<^sub>m (dim_col U\<^sub>f)" 
  proof 
    fix i j::nat
    assume a1: "i < dim_row (1\<^sub>m (dim_col U\<^sub>f))" and a2: "j < dim_col (1\<^sub>m (dim_col U\<^sub>f))" 
    then have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (Matrix.row U\<^sub>f i $ 0 * Matrix.col U\<^sub>f j $ 0) + 
(Matrix.row U\<^sub>f i $ 1 * Matrix.col U\<^sub>f j $ 1) + (Matrix.row U\<^sub>f i $ 2 * Matrix.col U\<^sub>f j $ 2) + 
(Matrix.row U\<^sub>f i $ 3 * Matrix.col U\<^sub>f j $ 3)" by (simp add: scalar_prod_def) 
    moreover have "\<dots> = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)"
      using a1 a2 deutsch_transform_alt_rep
      apply auto
      using f_values by auto[4]
    ultimately show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)" by simp
  next 
    show "dim_row (U\<^sub>f * U\<^sub>f) = dim_row (1\<^sub>m (dim_col U\<^sub>f))" by simp
  next
    show "dim_col (U\<^sub>f * U\<^sub>f) = dim_col (1\<^sub>m (dim_col U\<^sub>f))" by simp
  qed
  then show "unitary U\<^sub>f"  by (simp add: adjoint_of_deutsch_transform unitary_def)
qed
   

text \<open>Two qubits x and y are prepared, x in state 0 and y in state 1.\<close>

(*TODO: These two should be renamed. While sometimes x and y denote these matrices they might also 
denote the inputs of the Uf gate (e.g. Nielsen and Chuang)*)

abbreviation x where "x \<equiv> Matrix.vec 2 (\<lambda> i. if i= 0 then 1 else 0)"
abbreviation y where "y \<equiv> Matrix.vec 2 (\<lambda> i. if i= 0 then 0 else 1)"


lemma x_is_unit[simp]: 
  shows "x = unit_vec 2 0" 
  by (simp add: unit_vec_def)

lemma x_is_state: 
  shows "state 1 |x\<rangle>" 
  by (smt dim_col_mat(1) dim_row_mat(1) dim_vec ket_vec_col ket_vec_def pos2 power_one_right 
      state_def unit_cpx_vec_length x_is_unit)

lemma y_is_unit[simp]: 
  shows "y = unit_vec 2 1"  
  by auto

lemma y_is_state: 
  shows "state 1 |y\<rangle>" 
  by (smt dim_col_mat(1) dim_row_mat(1) dim_vec ket_vec_col ket_vec_def one_less_numeral_iff 
      power_one_right semiring_norm(76) state_def unit_cpx_vec_length y_is_unit)



text\<open>
State @{text \<psi>\<^sub>1} is obtained by applying an Hadamard gate to x and an Hadamard gate to y and then 
taking the tensor product of the results
\<close>
(*TODO: It would be nicer to have a lemma like (a \<cdot>\<^sub>m A) \<Otimes> (b \<cdot>\<^sub>m B) = (a*b) \<cdot>\<^sub>m (A \<Otimes> B) *)

lemma H_on_zero_state: "(H * |x\<rangle>) = 1/sqrt(2) \<cdot>\<^sub>m ( |x\<rangle> + |y\<rangle>)"
proof -
  define H'::"complex Matrix.mat" where "H'\<equiv> (Matrix.mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i=0 then 1 else -1)) * |x\<rangle>)"
  have "(H * |x\<rangle>) = 1/sqrt(2) \<cdot>\<^sub>m (Matrix.mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i=0 then 1 else -1)) * |x\<rangle>)"
    by (metis (no_types, lifting) H_def dim_vec ket_vec_def mat_carrier mult_smult_assoc_mat)
  moreover have "(Matrix.mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i=0 then 1 else -1)) * |x\<rangle>) = ( |x\<rangle> + |y\<rangle>)"
  proof
      show "dim_row (Matrix.mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i=0 then 1 else -1)) * |x\<rangle>) = dim_row( |x\<rangle> + |y\<rangle>)"
        by (simp add: ket_vec_def)
    next
      show "dim_col (Matrix.mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i=0 then 1 else -1)) * |x\<rangle>) = dim_col( |x\<rangle> + |y\<rangle>)"
        by (simp add: ket_vec_def)
    next
      fix i j::nat
      assume a1:"i < dim_row ( |x\<rangle> + |y\<rangle>)" and a2:"j < dim_col ( |x\<rangle> + |y\<rangle>)"
      then have "i=0 \<or> i=1" and "j=0"
        using ket_vec_def by auto
      moreover have "Matrix.row (Matrix.mat 2 2 (\<lambda>(i, j). if i \<noteq> j then 1 else if i = 0 then 1 else - 1)) i \<bullet> Matrix.col |x\<rangle> j = 
                    (\<Sum>k = 0..<2. Matrix.row (Matrix.mat 2 2 (\<lambda>(i, j). if i \<noteq> j then 1 else if i = 0 then 1 else - 1)) i $ k * Matrix.col |x\<rangle> j $ k)"
        by (smt a1 a2 One_nat_def dim_col_mat(1) dim_vec index_add_mat(3) ket_vec_col ket_vec_def less_Suc0 scalar_prod_def sum.cong)
      ultimately show "(Matrix.mat 2 2 (\<lambda>(i, j). if i \<noteq> j then 1 else if i = 0 then 1 else - 1) * |x\<rangle>) $$ (i, j) = ( |x\<rangle> + |y\<rangle>) $$(i,j) "
        using ket_vec_def by fastforce
  qed
  ultimately show "(H * |x\<rangle>) = 1/sqrt(2) \<cdot>\<^sub>m  ( |x\<rangle> + |y\<rangle>)" by auto
qed

lemma x_plus_y: "( |x\<rangle> + |y\<rangle>) = Matrix.mat 2 1 (\<lambda>(i,j). 1)"
proof
    fix i j::nat
    assume "i<dim_row (Matrix.mat 2 1 (\<lambda>(i,j). 1))" and "j<dim_col ( Matrix.mat 2 1 (\<lambda>(i,j). 1))"
    then have  "j=0" and "i \<in> {0,1}" using ket_vec_def by auto
    moreover have "( |x\<rangle> + |y\<rangle>)$$(0,0) = Matrix.mat 2 1 (\<lambda>(i,j). 1) $$(0,0)" using ket_vec_def less_Suc0 by simp 
    moreover have "( |x\<rangle> + |y\<rangle>)$$(1,0) = Matrix.mat 2 1 (\<lambda>(i,j). 1) $$(1,0)" using index_add_mat(1) ket_vec_def  by simp 
    ultimately show  "( |x\<rangle> + |y\<rangle>)$$(i,j) = Matrix.mat 2 1 (\<lambda>(i,j). 1) $$(i,j)" by blast
  next
    show "dim_row ( |x\<rangle> + |y\<rangle>) = dim_row (Matrix.mat 2 1 (\<lambda>(i, j). 1))" by (simp add: ket_vec_def)
  next
    show "dim_col ( |x\<rangle> + |y\<rangle>) = dim_col (Matrix.mat 2 1 (\<lambda>(i, j). 1))" by (simp add: ket_vec_def)
qed

lemma H_on_zero_state_square_inside: "(H * |x\<rangle>) =  (Matrix.mat 2 1 (\<lambda>(i,j). 1/sqrt(2)))"
  using cong_mat x_plus_y H_on_zero_state by auto

lemma H_on_zero_state_is_state: "state 1 (H * |x\<rangle>)"
proof
  show "gate 1 H" 
    using H_is_gate by auto
next
  show "state 1 |x\<rangle>" 
    using x_is_state by blast
qed



lemma H_on_one_state: "(H * |y\<rangle>) = 1/sqrt(2) \<cdot>\<^sub>m ( |x\<rangle> - |y\<rangle>)"
proof -
  have "(H * |y\<rangle>) = 1/sqrt(2) \<cdot>\<^sub>m ((Matrix.mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i=0 then 1 else -1)) * |y\<rangle>))"
    by (metis (no_types, lifting) H_def dim_vec ket_vec_def mat_carrier mult_smult_assoc_mat)
  moreover have "(Matrix.mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i=0 then 1 else -1)) * |y\<rangle>) = ( |x\<rangle> - |y\<rangle>)"
  proof
    show "dim_row (Matrix.mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i=0 then 1 else -1)) * |y\<rangle>) 
          = dim_row( |x\<rangle> - |y\<rangle>)"
        by (simp add: ket_vec_def)
    next
      show "dim_col (Matrix.mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i=0 then 1 else -1)) * |y\<rangle>) 
            = dim_col( |x\<rangle> - |y\<rangle>)"
        by (simp add: ket_vec_def)
    next
      fix i j::nat
      assume "i < dim_row ( |x\<rangle> - |y\<rangle>)" and "j < dim_col ( |x\<rangle> - |y\<rangle>)"
      then have "i=0 \<or> i=1" and "j=0"
        using ket_vec_def by auto
      moreover have "Matrix.row (Matrix.mat 2 2 (\<lambda>(i, j). if i \<noteq> j then 1 else if i = 0 then 1 else - 1)) i  \<bullet> Matrix.col |y\<rangle> j 
= (\<Sum>k = 0..<2. Matrix.row (Matrix.mat 2 2 (\<lambda>(i, j). if i \<noteq> j then 1 else if i = 0 then 1 else - 1)) i $ k * Matrix.col |y\<rangle> j $ k)"
        by (smt dim_col dim_row_mat(1) dim_vec ket_vec_def scalar_prod_def sum.cong)
      ultimately show "(Matrix.mat 2 2 (\<lambda>(i, j). if i \<noteq> j then 1 else if i = 0 then 1 else - 1) * |y\<rangle>) $$ (i, j) = ( |x\<rangle> - |y\<rangle>) $$(i,j) "
        using ket_vec_def by fastforce
   qed
  ultimately show "(H * |y\<rangle>) = 1/sqrt(2) \<cdot>\<^sub>m  ( |x\<rangle> - |y\<rangle>)" by auto
qed

lemma x_minus_y: "( |x\<rangle> - |y\<rangle>) = Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1 else -1)"
proof
  fix i j::nat
  assume "i<dim_row (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1 else -1))" 
     and "j<dim_col (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1 else -1))"
  then have  "j=0" and "i \<in> {0,1}" using ket_vec_def by auto
  moreover have "( |x\<rangle> - |y\<rangle>)$$(0,0) = Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1 else -1) $$(0,0)" 
    using ket_vec_def less_Suc0 by simp 
  moreover have "( |x\<rangle> - |y\<rangle>)$$(1,0) = Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1 else -1) $$(1,0)" 
    using index_add_mat(1) ket_vec_def by auto
  ultimately show  "( |x\<rangle> - |y\<rangle>)$$(i,j) = Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1 else -1) $$(i,j)" by blast
next
    show "dim_row ( |x\<rangle> - |y\<rangle>) = dim_row (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1 else -1))" 
      by (simp add: ket_vec_def)
next
  show "dim_col ( |x\<rangle> - |y\<rangle>) = dim_col (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1 else -1))"
    by (simp add: ket_vec_def)
qed

lemma H_on_one_state_square_inside: "(H * |y\<rangle>) =  Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then  1/sqrt(2) else - 1/sqrt(2))" 
  using cong_mat H_on_one_state x_minus_y by auto

lemma H_on_one_state_is_state: "state 1 (H * |y\<rangle>)"
proof
  show "gate 1 H" 
    using H_is_gate by auto
next
  show "state 1 |y\<rangle>" 
    using y_is_state by blast
qed





lemma \<psi>\<^sub>1_is_state: "state 2 ((H * |x\<rangle>) \<Otimes> (H * |y\<rangle>))"
proof 
  show  "dim_col (H * |x\<rangle> \<Otimes> H * |y\<rangle>) = 1" 
    using state.dim_col x_is_state y_is_state by auto
next 
  show "dim_row (H * |x\<rangle> \<Otimes> H * |y\<rangle>) = 2\<^sup>2" 
    using H_on_one_state_is_state H_on_zero_state_is_state state_def tensor_state2 by blast
next
  show "\<parallel>Matrix.col (H * |x\<rangle> \<Otimes> H * |y\<rangle>) 0\<parallel> = 1"
    using H_on_one_state_is_state H_on_zero_state_is_state state.length tensor_state2 by blast
qed


(*lemma \<psi>\<^sub>0_to_\<psi>\<^sub>1: 
  assumes  "v\<equiv>  mat_of_cols_list 4 [[1/2, -1/2, 1/2, -1/2]]"
  shows "((H * |x\<rangle>) \<Otimes> (H * |y\<rangle>)) =  v"
proof 
  show "Matrix.dim_col ((H * |x\<rangle>) \<Otimes> (H * |y\<rangle>)) = Matrix.dim_col v"  sorry
next
  show "dim_row ((H * |x\<rangle>) \<Otimes> (H * |y\<rangle>)) = Matrix.dim_row v" sorry
next 
  fix i j::nat assume "i < dim_row v" and "j < dim_col v"
  then have "i \<in> {0..<4} \<and> j \<in> {0..<4}" 
    by (auto simp add: assms mat_of_cols_list_def)
  then show "((H * |x\<rangle>) \<Otimes> (H * |y\<rangle>)) $$ (i, j) = v $$ (i, j)"
    using  H_on_one_state H_on_zero_state mat_of_cols_list_def
    sledgehammer*)



lemma \<psi>\<^sub>0_to_\<psi>\<^sub>1: "((H * |x\<rangle>) \<Otimes> (H * |y\<rangle>)) = 1/2 \<cdot>\<^sub>m |Matrix.vec 4 (\<lambda>i. if i=0 \<or> i=2 then 1 else -1)\<rangle>"
proof -
  define v::"complex Matrix.mat" where "v\<equiv> (Matrix.mat 2 1 (\<lambda>(i,j). 1/sqrt(2)))"
  define w::"complex Matrix.mat" where "w\<equiv> (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then  1/sqrt(2) else - 1/sqrt(2)))"
  have "state 1 v"  
    using v_def gate_on_state_is_state x_is_state x_plus_y H_on_zero_state H_is_gate H_on_zero_state_square_inside 
    by fastforce
  moreover have "state 1 w" 
    using w_def gate_on_state_is_state y_is_state x_minus_y H_on_one_state H_is_gate H_on_one_state_square_inside 
    by fastforce
  ultimately have f1: "v \<Otimes> w = |Matrix.vec 4 (\<lambda>i. if i = 0 then v $$ (0,0) * w $$ (0,0) else 
                                               if i = 3 then v $$ (1,0) * w $$ (1,0) else
                                               if i = 1 then v $$ (0,0) * w $$ (1,0) else 
                                                             v $$ (1,0) * w $$ (0,0))\<rangle>" 
    using mat_tensor_prod_2_bis v_def w_def by blast
  have f2:" (1/sqrt(2))*(1/sqrt(2)) = 1/2"  by auto
  have f3:"v $$ (0,0) = 1/sqrt(2)" using v_def by simp
  have f4:"w $$ (0,0) = 1/sqrt(2)" using w_def by simp
  have f5:"v $$ (0,0)* w $$ (0,0)  = 1/2" using f2 f3 f4
    by (metis (no_types, hide_lams) of_real_divide of_real_hom.hom_one of_real_mult of_real_numeral)
  have f6: "w $$ (1,0) = -1/sqrt(2)" using w_def by simp
  have f7:"v $$ (1,0)* w $$ (1,0)  = -1/2"
    using v_def w_def f5 f6 by auto
  have f8:"v $$ (1,0) = 1/sqrt(2)" using v_def by simp
  have "((H * |x\<rangle>) \<Otimes> (H * |y\<rangle>)) = v \<Otimes> w "  
    by (simp add: H_on_one_state_square_inside H_on_zero_state_square_inside v_def w_def)
  also have "...  = |Matrix.vec 4 (\<lambda>i. if i = 0 then 1/2 else
                                if i = 3 then -1/2 else
                                if i = 1 then -1/2 else 1/2)\<rangle>" 
      using f1 f3 f8 f5 f7 by presburger
  also have "...= 1/2 \<cdot>\<^sub>m |Matrix.vec 4 (\<lambda>i. if i = 0 then 1 else
                                             if i = 3 then -1 else
                                             if i = 1 then -1 else 1)\<rangle>" 
    using smult_mat_def ket_vec_def cong_mat by auto
  finally show "((H * |x\<rangle>) \<Otimes> (H * |y\<rangle>)) = 1/2 \<cdot>\<^sub>m |Matrix.vec 4 (\<lambda>i. if i=0 \<or> i=2 then 1 else -1)\<rangle>"  
    using cong_mat ket_vec_def numeral_eq_one_iff prod.simps(2) semiring_norm(85) semiring_norm(89) set_four 
    by (smt dim_vec index_vec numeral_eq_iff)
qed

text \<open> @{text U\<^sub>f} is applied to state @{text \<psi>\<^sub>1} and @{text \<psi>\<^sub>2} is obtained. \<close>

lemma (in deutsch) \<psi>\<^sub>2_is_state:
  assumes "\<psi>\<^sub>1 \<equiv> mat_of_cols_list 4 [[1/2, -1/2, 1/2, -1/2]]"
  shows "state 2 (U\<^sub>f * \<psi>\<^sub>1)" 
proof-
  have "gate 2 U\<^sub>f"
    using deutsch_transform_is_gate by auto
  moreover have "((H * |x\<rangle>) \<Otimes> (H * |y\<rangle>))  =  \<psi>\<^sub>1" using assms mat_of_cols_list_def sorry
  ultimately show "state 2 (U\<^sub>f * \<psi>\<^sub>1)" using deutsch_transform_is_gate assms \<psi>\<^sub>1_is_state gate_on_state_is_state 
    by simp
qed


text \<open> @{text U\<^sub>f} is applied to state @{text \<psi>\<^sub>1} and @{text \<psi>\<^sub>2} is obtained. \<close>

lemma (in deutsch) \<psi>\<^sub>2_is_state:
  assumes "\<psi>\<^sub>1 \<equiv> mat_of_cols_list 4 [[1/2, -1/2, 1/2, -1/2]]"
  shows "state 2 (U\<^sub>f * \<psi>\<^sub>1)" 
proof-
  have "gate 2 U\<^sub>f"
    using deutsch_transform_is_gate by auto
  moreover have "((H * |x\<rangle>) \<Otimes> (H * |y\<rangle>))  =  \<psi>\<^sub>1" using assms mat_of_cols_list_def sorry
  ultimately show "state 2 (U\<^sub>f * \<psi>\<^sub>1)" using deutsch_transform_is_gate assms \<psi>\<^sub>1_is_state gate_on_state_is_state 
    by simp
qed

lemma (in deutsch) \<psi>\<^sub>1_to_\<psi>\<^sub>2: 
  assumes "\<psi>\<^sub>1 \<equiv> mat_of_cols_list 4 [[1/2, -1/2, 1/2, -1/2]]"
      and "\<psi>\<^sub>2 \<equiv> mat_of_cols_list 4 [[(inv_b (f 0))/2 - (f(0)::int)/2,
                                      (f(0)::int)/2 - (inv_b (f(0)))/2,
                                      (inv_b (f(1)))/2 - (f(1)::int)/2,
                                      (f(1)::int)/2 - inv_b(f(1))/2]]"
  shows "U\<^sub>f * \<psi>\<^sub>1 = \<psi>\<^sub>2"
proof 
  fix i j:: nat
  assume "i<dim_row \<psi>\<^sub>2 " and "j<dim_col \<psi>\<^sub>2"
  then have a0: "i\<in>{0,1,2,3} \<and> j=0 " 
    using assms ket_vec_def mat_of_cols_list_def by auto
  then have "i<dim_row U\<^sub>f" and "j<dim_col \<psi>\<^sub>1" 
    using deutsch_transform_def assms mat_of_cols_list_def by auto 
  then have "(U\<^sub>f * \<psi>\<^sub>1) $$ (i, j) 
        = (\<Sum> k \<in> {0 ..< dim_vec \<psi>\<^sub>1}. (Matrix.row U\<^sub>f i) $ k * (Matrix.col \<psi>\<^sub>1 j) $ k)"     
    using scalar_prod_def col_fst_is_col index_mult_mat sum.cong
    by (smt a0)
  then have "(U\<^sub>f * \<psi>\<^sub>1) $$ (i, j) = ((Matrix.row U\<^sub>f i) $ 0 * ( Matrix.col \<psi>\<^sub>1 0) $ 0) 
             + ((Matrix.row U\<^sub>f i) $ 1 * ( Matrix.col \<psi>\<^sub>1 0) $ 1) + ((Matrix.row U\<^sub>f i) $ 2 * ( Matrix.col \<psi>\<^sub>1 0) $ 2) 
             + ((Matrix.row U\<^sub>f i) $ 3 * ( Matrix.col \<psi>\<^sub>1 0) $ 3) "
    using set_4 mat_of_cols_list_def assms scalar_prod_def times_mat_def a0 by simp
  then show "(U\<^sub>f * \<psi>\<^sub>1) $$ (i, j) = \<psi>\<^sub>2 $$ (i, j)"
    using  mat_of_cols_list_def deutsch_transform_def assms a0 assms
      apply (auto simp add: algebra_simps)
    done
next
  show "dim_row (U\<^sub>f * \<psi>\<^sub>1) = dim_row \<psi>\<^sub>2" 
    using assms mat_of_cols_list_def by auto
next
  show "dim_col (U\<^sub>f * \<psi>\<^sub>1) = dim_col \<psi>\<^sub>2"    
    using assms mat_of_cols_list_def by auto
qed


lemma H_tensor_Id: 
assumes "v \<equiv>  mat_of_cols_list 4 [[1/sqrt(2), 0, 1/sqrt(2), 0],
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

lemma (in deutsch) deutsch_algo_result: "deutsch_algo = mat_of_cols_list 4 
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


(*lemma inv_b_add_mult1:
  fixes f::"nat\<Rightarrow>nat" 
  assumes "deutsch f"
  shows "1 -  (f(0))*1 -  (f(0)) + f(0)*f(0) = 1" 
  using One_nat_def assms deutsch.f_values inv_b_def by fastforce

lemma inv_b_add_mult2:
  fixes f::"nat\<Rightarrow>nat" 
  assumes "deutsch f"
  shows "1 -  (f(1))*1 -  (f(1)) + f(1)*f(1) = 1"  
  using deutsch.f_values assms inv_b_def of_nat_1 by fastforce

lemma inv_b_add_mult3:
  fixes f::"nat\<Rightarrow>nat" 
  assumes "deutsch f"
  shows "1 -  (f(0))*f(0) + 1 -  (f(0))*f(0) = 0" 
  using deutsch.f_values diff_diff_cancel inv_b_def assms by force

lemma inv_b_add_mult4:
  fixes f::"nat\<Rightarrow>nat" 
  assumes "deutsch f"
  shows "1 -  (f(1))*f(1) + 1 -  (f(1))*f(1) = 0"  
  using deutsch.f_values inv_b_def assms by force*)

end
