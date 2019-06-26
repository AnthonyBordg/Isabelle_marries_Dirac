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
A constant function returns either always 0 or always 1. 
A balanced function is 0 for half of the values and 1 for the other half. (* added a missing comma *)
\<close>

locale deutsch = 
  fixes f:: "nat \<Rightarrow> nat"
  assumes f: "f \<in> ({0,1} \<rightarrow> {0,1})"
  
context deutsch
begin

definition const:: "nat \<Rightarrow> bool" where 
      "const n = (\<forall>x.(f x = n))"

definition bal where
      "bal = (\<forall>x.(f x = x))"
lemma f_values: "(f 0 = 0 \<or> f 0 = 1) \<and> (f 1 = 0 \<or> f 1 = 1)" using f by blast
end

definition inv_b :: "nat \<Rightarrow> int" where (*Better than (1-n) since it captures the partiality? *)
"inv_b n \<equiv> (case n of 0 \<Rightarrow> 1 
                     |(Suc 0) \<Rightarrow> 0)"

lemma inv_b_values:
  fixes f::"nat\<Rightarrow>nat" 
  assumes "deutsch f"
  shows "f(0) = 0 \<or> f(0) = 1" 
  and  "f(1) = 0 \<or> f(1) = 1" 
  and  "f(0) = 0 \<longrightarrow> inv_b (f(0)) - f(0) = 1"
  and "f(0) = 1 \<longrightarrow> inv_b (f 0) - f(0) = -1"
  and "f(1) = 0 \<longrightarrow> inv_b (f(1)) - f(1) = 1"
  and "f(1) = 1 \<longrightarrow> inv_b (f(1)) - f(1) = -1"
  using  inv_b_def assms deutsch.f_values by auto

lemma inv_b_add_mult1:
  fixes f::"nat\<Rightarrow>nat" 
  assumes "deutsch f"
  shows "inv_b (f(0))*inv_b (f(0)) + f(0)*f(0) = 1" 
  using One_nat_def assms deutsch.f_values inv_b_def by fastforce

lemma inv_b_add_mult2:
  fixes f::"nat\<Rightarrow>nat" 
  assumes "deutsch f"
  shows "inv_b (f(1))*inv_b (f(1)) + f(1)*f(1) = 1"  
  using deutsch.f_values assms inv_b_def of_nat_1 by fastforce

lemma inv_b_add_mult3:
  fixes f::"nat\<Rightarrow>nat" 
  assumes "deutsch f"
  shows "inv_b (f(0))*f(0) + inv_b (f(0))*f(0) = 0" 
  using deutsch.f_values diff_diff_cancel inv_b_def assms by force

lemma inv_b_add_mult4:
  fixes f::"nat\<Rightarrow>nat" 
  assumes "deutsch f"
  shows "inv_b (f(1))*f(1) + inv_b (f(1))*f(1) = 0"  
  using deutsch.f_values inv_b_def assms by force


text \<open>Black box function @{text U\<^sub>f}. \<close>

definition U\<^sub>f ::"(nat \<Rightarrow> nat) => complex Matrix.mat" where
"U\<^sub>f f \<equiv> Matrix.mat 4 4 (\<lambda>(i,j). if i=0 \<and> j=0 then (inv_b (f(0))) else
                  (if i=0 \<and> j=1 then f(0) else
                  (if i=1 \<and> j=0 then f(0) else
                  (if i=1 \<and> j=1 then (inv_b (f(0))) else
                    (if i=2 \<and> j=2 then (inv_b (f(1))) else
                    (if i=2 \<and> j=3 then f(1) else
                    (if i=3 \<and> j=2 then f(1) else
                      (if i=3 \<and> j=3 then (inv_b (f(1))) else 0))))))))"

lemma U\<^sub>f_dim [simp]: 
  shows "dim_row (U\<^sub>f f) = 4" and "dim_col (U\<^sub>f f) = 4"
  using U\<^sub>f_def by auto

lemma U\<^sub>f_is_zero [simp]:
  shows "(U\<^sub>f f)$$(0,2) = 0" and "(U\<^sub>f f)$$(0,3) = 0"
    and "(U\<^sub>f f)$$(1,2) = 0" and "(U\<^sub>f f)$$(1,3) = 0"
    and "(U\<^sub>f f)$$(2,0) = 0" and "(U\<^sub>f f)$$(2,1) = 0"
    and "(U\<^sub>f f)$$(3,0) = 0" and "(U\<^sub>f f)$$(3,1) = 0"
  using U\<^sub>f_def by auto

lemma U\<^sub>f_is_not_zero [simp]:
  shows "(U\<^sub>f f)$$(0,1) = f(0)" and "(U\<^sub>f f)$$(1,0) = f(0)"
    and "(U\<^sub>f f)$$(2,3) = f(1)" and "(U\<^sub>f f)$$(3,2) = f(1)"
    and "(U\<^sub>f f)$$(0,0) = inv_b (f(0))" and "(U\<^sub>f f)$$(1,1) = inv_b (f(0))"
    and "(U\<^sub>f f)$$(2,2) = inv_b (f(1))" and "(U\<^sub>f f)$$(3,3) = inv_b (f(1))"
  using U\<^sub>f_def by auto

text \<open>@{text U\<^sub>f} is a gate. \<close>

lemma set_four [simp]: "\<forall>i::nat. i < 4 \<longrightarrow> i = 0 \<or> i = 1 \<or> i = 2 \<or> i = 3" by auto

lemma adjoint_of_U\<^sub>f: 
  fixes f::"nat\<Rightarrow>nat"
  assumes "deutsch f"
  shows "(U\<^sub>f f)\<^sup>\<dagger> = (U\<^sub>f f)"
proof -
  have "(U\<^sub>f f)\<^sup>\<dagger> = ((U\<^sub>f f)\<^sup>t)" using cpx_mat_cnj_def deutsch_def U\<^sub>f_def 
    by (smt U\<^sub>f_dim(1) U\<^sub>f_dim(2) cnj_transpose complex_cnj_of_int cong_mat index_mat(1) old.prod.case)
  also have "... = (U\<^sub>f f)" using hermite_cnj_def cong_mat U\<^sub>f_def  
    by (smt U\<^sub>f_dim U\<^sub>f_is_not_zero U\<^sub>f_is_zero eq_matI index_transpose_mat set_four)
  finally show "(U\<^sub>f f)\<^sup>\<dagger> = (U\<^sub>f f)" by simp
qed

lemma U\<^sub>f_is_gate:
  fixes f::"nat\<Rightarrow>nat"
  assumes "deutsch f"
  shows "gate 2 (U\<^sub>f f)"
proof
  show "dim_row (U\<^sub>f f) = 2\<^sup>2"
    by (simp add: U\<^sub>f_def)
next
  show "square_mat(U\<^sub>f f)"
    by (simp add: U\<^sub>f_def)
next
  have "(U\<^sub>f f)*(U\<^sub>f f) = 1\<^sub>m (dim_col (U\<^sub>f f))" 
  proof 
    fix i j::nat
    assume a1: "i < dim_row (1\<^sub>m (dim_col (U\<^sub>f f)))" and a2: "j < dim_col (1\<^sub>m (dim_col (U\<^sub>f f)))" 
    then have "((U\<^sub>f f)*(U\<^sub>f f))$$(i,j) =(Matrix.row (U\<^sub>f f) i $ 0 * Matrix.col (U\<^sub>f f) j $ 0) + (Matrix.row (U\<^sub>f f) i $ 1 * Matrix.col (U\<^sub>f f) j $ 1) + (Matrix.row (U\<^sub>f f) i $ 2 * Matrix.col (U\<^sub>f f) j $ 2) + (Matrix.row (U\<^sub>f f) i $ 3 * Matrix.col (U\<^sub>f f) j $ 3)"
      by (simp add: scalar_prod_def)
    then show "(U\<^sub>f f * U\<^sub>f f) $$ (i, j) = 1\<^sub>m (dim_col (U\<^sub>f f)) $$ (i, j)"
      by (smt U\<^sub>f_dim U\<^sub>f_is_not_zero U\<^sub>f_is_zero a1 a2 add.commute add_Suc add_cancel_right_left add_less_cancel_left assms index_col index_one_mat(1) index_one_mat(2) index_one_mat(3) index_row(1) inv_b_add_mult3 inv_b_add_mult4 inv_b_values(1) inv_b_values(2) inv_b_values(3) inv_b_values(5) mult.commute mult_cancel_left1 neq0_conv numeral_2_eq_2 numeral_Bit0 numeral_Bit1 of_int_hom.hom_one of_int_hom.hom_zero of_nat_0 of_nat_1 plus_1_eq_Suc set_four zero_neq_numeral)
  next 
    show "dim_row (U\<^sub>f f * U\<^sub>f f) = dim_row (1\<^sub>m (dim_col (U\<^sub>f f)))" by simp
  next
    show "dim_col (U\<^sub>f f * U\<^sub>f f) = dim_col (1\<^sub>m (dim_col (U\<^sub>f f)))" by simp
  qed
  then show "unitary (U\<^sub>f f)" 
    by (simp add: adjoint_of_U\<^sub>f assms unitary_def)
qed



text\<open>Two qubits x and y are prepared, x in state 0 and y in state 1.\<close>

abbreviation x where "x \<equiv> Matrix.vec 2 (\<lambda> i. if i= 0 then 1 else 0)"
abbreviation y where "y \<equiv> Matrix.vec 2 (\<lambda> i. if i= 0 then 0 else 1)"

lemma x_is_unit: "x = unit_vec 2 0" 
  by (simp add: unit_vec_def)

lemma x_is_state: "state 1 |x\<rangle>" 
  by (smt dim_col_mat(1) dim_row_mat(1) dim_vec ket_vec_col ket_vec_def pos2 power_one_right state_def unit_cpx_vec_length x_is_unit)

lemma y_is_unit: "y = unit_vec 2 1"  
  using index_unit_vec(1) index_unit_vec(3) index_vec one_less_numeral_iff one_neq_zero by auto

lemma y_is_state: "state 1 |y\<rangle>" 
  by (smt dim_col_mat(1) dim_row_mat(1) dim_vec ket_vec_col ket_vec_def one_less_numeral_iff power_one_right semiring_norm(76) state_def unit_cpx_vec_length y_is_unit)



text\<open>State @{text \<psi>\<^sub>1} is obtained by applying an Hadamard gate to x and an Hadamard gate to y and then 
taking the tensor product of the results\<close>
(*TODO: It would be nicer to have a lemma like (a \<cdot>\<^sub>m A) \<Otimes> (b \<cdot>\<^sub>m B) = (a*b) \<cdot>\<^sub>m (A \<Otimes> B) *)

lemma H_on_zero_state: "(H * |x\<rangle>) = 1/sqrt(2) \<cdot>\<^sub>m ( |x\<rangle> + |y\<rangle>)"
proof -
  have "(H * |x\<rangle>) = 1/sqrt(2) \<cdot>\<^sub>m ((Matrix.mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i=0 then 1 else -1)) * |x\<rangle>))"
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
      moreover have "Matrix.row (Matrix.mat 2 2 (\<lambda>(i, j). if i \<noteq> j then 1 else if i = 0 then 1 else - 1)) i \<bullet> Matrix.col |x\<rangle> j = (\<Sum>k = 0..<2. Matrix.row (Matrix.mat 2 2 (\<lambda>(i, j). if i \<noteq> j then 1 else if i = 0 then 1 else - 1)) i $ k * Matrix.col |x\<rangle> j $ k)"
        by (smt a1 a2 One_nat_def dim_col_mat(1) dim_vec index_add_mat(3) ket_vec_col ket_vec_def less_Suc0 scalar_prod_def sum.cong)
      ultimately show "(Matrix.mat 2 2 (\<lambda>(i, j). if i \<noteq> j then 1 else if i = 0 then 1 else - 1) * |x\<rangle>) $$ (i, j) = ( |x\<rangle> + |y\<rangle>) $$(i,j) "
        using ket_vec_def by fastforce
  qed
  ultimately show "(H * |x\<rangle>) = 1/sqrt(2) \<cdot>\<^sub>m  ( |x\<rangle> + |y\<rangle>)" by auto
qed

lemma H_on_one_state: "(H * |y\<rangle>) = 1/sqrt(2) \<cdot>\<^sub>m ( |x\<rangle> - |y\<rangle>)"
proof -
  have "(H * |y\<rangle>) = 1/sqrt(2) \<cdot>\<^sub>m ((Matrix.mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i=0 then 1 else -1)) * |y\<rangle>))"
    by (metis (no_types, lifting) H_def dim_vec ket_vec_def mat_carrier mult_smult_assoc_mat)
  moreover have "(Matrix.mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i=0 then 1 else -1)) * |y\<rangle>) = ( |x\<rangle> - |y\<rangle>)"
  proof
      show "dim_row (Matrix.mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i=0 then 1 else -1)) * |y\<rangle>) = dim_row( |x\<rangle> - |y\<rangle>)"
        by (simp add: ket_vec_def)
    next
      show "dim_col (Matrix.mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i=0 then 1 else -1)) * |y\<rangle>) = dim_col( |x\<rangle> - |y\<rangle>)"
        by (simp add: ket_vec_def)
    next
      fix i j::nat
      assume "i < dim_row ( |x\<rangle> - |y\<rangle>)" and "j < dim_col ( |x\<rangle> - |y\<rangle>)"
      then have "i=0 \<or> i=1" and "j=0"
        using ket_vec_def by auto
      moreover have "Matrix.row (Matrix.mat 2 2 (\<lambda>(i, j). if i \<noteq> j then 1 else if i = 0 then 1 else - 1)) i \<bullet> Matrix.col |y\<rangle> j = (\<Sum>k = 0..<2. Matrix.row (Matrix.mat 2 2 (\<lambda>(i, j). if i \<noteq> j then 1 else if i = 0 then 1 else - 1)) i $ k * Matrix.col |y\<rangle> j $ k)"
        by (smt dim_col dim_row_mat(1) dim_vec ket_vec_def scalar_prod_def sum.cong)
      ultimately show "(Matrix.mat 2 2 (\<lambda>(i, j). if i \<noteq> j then 1 else if i = 0 then 1 else - 1) * |y\<rangle>) $$ (i, j) = ( |x\<rangle> - |y\<rangle>) $$(i,j) "
        using ket_vec_def by fastforce
   qed
  ultimately show "(H * |y\<rangle>) = 1/sqrt(2) \<cdot>\<^sub>m  ( |x\<rangle> - |y\<rangle>)" by auto
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

lemma x_minus_y: "( |x\<rangle> - |y\<rangle>) = Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1 else -1)"
proof
  fix i j::nat
  assume "i<dim_row (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1 else -1))" and "j<dim_col (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1 else -1))"
  then have  "j=0" and "i \<in> {0,1}" using ket_vec_def by auto
  moreover have "( |x\<rangle> - |y\<rangle>)$$(0,0) = Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1 else -1) $$(0,0)" using ket_vec_def less_Suc0 by simp 
  moreover have "( |x\<rangle> - |y\<rangle>)$$(1,0) = Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1 else -1) $$(1,0)" using index_add_mat(1) ket_vec_def by auto
  ultimately show  "( |x\<rangle> - |y\<rangle>)$$(i,j) = Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1 else -1) $$(i,j)" by blast
next
    show "dim_row ( |x\<rangle> - |y\<rangle>) = dim_row (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1 else -1))" 
      by (simp add: ket_vec_def)
next
  show "dim_col ( |x\<rangle> - |y\<rangle>) = dim_col (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1 else -1))"
    by (simp add: ket_vec_def)
qed



lemma H_on_zero_state_square_inside: "(H * |x\<rangle>) =  (Matrix.mat 2 1 (\<lambda>(i,j). 1/sqrt(2)))"
  using cong_mat x_plus_y H_on_zero_state by auto

lemma H_on_one_state_square_inside: "(H * |y\<rangle>) =  Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then  1/sqrt(2) else - 1/sqrt(2))" 
  using cong_mat H_on_one_state x_minus_y by auto

lemma \<psi>\<^sub>0_to_\<psi>\<^sub>1: "((H * |x\<rangle>) \<Otimes> (H * |y\<rangle>)) = 1/2 \<cdot>\<^sub>m |Matrix.vec 4 (\<lambda>i. if i=0 \<or> i=2 then 1 else -1)\<rangle>" 
proof -
  define v::"complex Matrix.mat" where "v\<equiv> (Matrix.mat 2 1 (\<lambda>(i,j). 1/sqrt(2)))"
  define w::"complex Matrix.mat" where "w\<equiv> (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then  1/sqrt(2) else - 1/sqrt(2)))"
  have "state 1 v"  
    using v_def gate_on_state_is_state x_is_state x_plus_y H_on_zero_state H_is_gate H_on_zero_state_square_inside by fastforce
  moreover have "state 1 w" 
    using w_def gate_on_state_is_state y_is_state x_minus_y H_on_one_state H_is_gate H_on_one_state_square_inside by fastforce
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
  have "((H * |x\<rangle>) \<Otimes> (H * |y\<rangle>)) = v \<Otimes> w "  by (simp add: H_on_one_state_square_inside H_on_zero_state_square_inside v_def w_def)
  also have "...  = |Matrix.vec 4 (\<lambda>i. if i = 0 then 1/2 else
                                if i = 3 then -1/2 else
                                if i = 1 then -1/2 else 1/2)\<rangle>" 
      using f1 f3 f8 f5 f7 by presburger
  also have "...= 1/2 \<cdot>\<^sub>m |Matrix.vec 4 (\<lambda>i. if i = 0 then 1 else
                                             if i = 3 then -1 else
                                             if i = 1 then -1 else 1)\<rangle>" 
    using smult_mat_def ket_vec_def cong_mat by auto
  finally show "((H * |x\<rangle>) \<Otimes> (H * |y\<rangle>)) = 1/2 \<cdot>\<^sub>m |Matrix.vec 4 (\<lambda>i. if i=0 \<or> i=2 then 1 else -1)\<rangle>"  
    using cong_mat ket_vec_def numeral_eq_one_iff prod.simps(2) semiring_norm(85) semiring_norm(89) set_four sledgehammer
    by (smt dim_vec index_vec numeral_eq_iff)
qed




text \<open> @{text U\<^sub>f} is applied to state @{text \<psi>\<^sub>1} and @{text \<psi>\<^sub>2} is obtained. \<close>

lemma \<psi>\<^sub>1_to_\<psi>\<^sub>2:
  fixes f::"nat\<Rightarrow>nat" 
  assumes "deutsch f" 
      and "\<psi>\<^sub>1 \<equiv> |Matrix.vec 4 (\<lambda>i. if i=0 \<or> i=2 then 1 else -1)\<rangle>"
      and "\<psi>\<^sub>2 \<equiv> |Matrix.vec 4 (\<lambda>i. if i=0 then ((inv_b (f 0)) - (f(0)::int)) else
                                    (if i=1 then ((f(0)::int)  -(inv_b (f(0)))) else
                                    (if i=2 then ((inv_b (f(1))) - (f(1)::int)) else ((f(1)::int) -inv_b(f(1))))))\<rangle>"
  shows "(U\<^sub>f f) * \<psi>\<^sub>1 = \<psi>\<^sub>2"
proof -
  have f1:"i<dim_row (U\<^sub>f f) \<longrightarrow> i\<in>{0,1,2,3}" for i
    using U\<^sub>f_def by auto
  have r1: "j<dim_col \<psi>\<^sub>1 \<longrightarrow> j=0" for j by (simp add: assms(2) ket_vec_def)
  then have "i<dim_row (U\<^sub>f f)\<and> j<dim_col \<psi>\<^sub>1 \<longrightarrow>  Matrix.row (U\<^sub>f f) i \<bullet> Matrix.col \<psi>\<^sub>1 0 = (\<Sum> k \<in> {0 ..< 4}. (Matrix.row (U\<^sub>f f) i) $ k * ( Matrix.col \<psi>\<^sub>1 0) $ k)"
    for i j by (smt assms(2) dim_col dim_row_mat(1) dim_vec ket_vec_def scalar_prod_def sum.cong)
  then have  "i<dim_row (U\<^sub>f f)\<and> j<dim_col \<psi>\<^sub>1 \<longrightarrow> (U\<^sub>f f * \<psi>\<^sub>1) $$ (i, 0)= ((Matrix.row (U\<^sub>f f) i) $ 0 * ( Matrix.col \<psi>\<^sub>1 0) $ 0) + ((Matrix.row (U\<^sub>f f) i) $ 1 * ( Matrix.col \<psi>\<^sub>1 0) $ 1) + ((Matrix.row (U\<^sub>f f) i) $ 2 * ( Matrix.col \<psi>\<^sub>1 0) $ 2) + ((Matrix.row (U\<^sub>f f) i) $ 3 * ( Matrix.col \<psi>\<^sub>1 0) $ 3) "
    for i j using f1 set_4 by auto
  then have f2: "i<dim_row (U\<^sub>f f) \<and> j<dim_col \<psi>\<^sub>1 \<longrightarrow> (U\<^sub>f f * \<psi>\<^sub>1) $$ (i, 0)= ((Matrix.row (U\<^sub>f f) i) $ 0 * ( Matrix.col \<psi>\<^sub>1 0) $ 0) + ((Matrix.row (U\<^sub>f f) i) $ 1 * ( Matrix.col \<psi>\<^sub>1 0) $ 1) + ((Matrix.row (U\<^sub>f f) i) $ 2 * ( Matrix.col \<psi>\<^sub>1 0) $ 2) + ((Matrix.row (U\<^sub>f f) i) $ 3 * ( Matrix.col \<psi>\<^sub>1 0) $ 3) "
    for i j by (simp add: assms(1) ket_vec_def)
  have "(U\<^sub>f f * \<psi>\<^sub>1) $$ (0, 0) = inv_b (f(0)) + -(f(0))"
    using f2[of 0 0]
    by (simp add: U\<^sub>f_def assms(2) ket_vec_def)
  moreover have "(U\<^sub>f f * \<psi>\<^sub>1) $$ (1, 0) = (f(0)) + - inv_b (f(0))"
    using f2[of 1 0]
    by (simp add: U\<^sub>f_def assms(2) ket_vec_def)
  moreover have "(U\<^sub>f f * \<psi>\<^sub>1) $$ (2, 0) = inv_b (f(1)) + -(f(1))"
    using f2[of 2 0]
    by (simp add: U\<^sub>f_def assms(2) ket_vec_def)
  moreover have "(U\<^sub>f f * \<psi>\<^sub>1) $$ (3, 0) = (f(1)) + -inv_b (f(1))"
    using f2[of 3 0]
    by (simp add: U\<^sub>f_def assms(2) ket_vec_def)
  ultimately have "i<dim_row (U\<^sub>f f) \<and> j<dim_col \<psi>\<^sub>1 \<longrightarrow> (U\<^sub>f f * \<psi>\<^sub>1) $$(i,j) = \<psi>\<^sub>2 $$(i,j)"
    for i j using assms f1 f2 set_4 r1
    by (smt atLeastLessThan_iff empty_iff index_mat(1) insert_iff prod.simps(2) less_numeral_extra(1))
  moreover have "dim_row (U\<^sub>f f * \<psi>\<^sub>1) = dim_row \<psi>\<^sub>2"
    by (simp add: U\<^sub>f_def assms(3))
  moreover have "dim_col (U\<^sub>f f * \<psi>\<^sub>1) = dim_col \<psi>\<^sub>2"
    by (simp add: assms(2) assms(3) ket_vec_def)
  ultimately show "(U\<^sub>f f * \<psi>\<^sub>1) = \<psi>\<^sub>2"
    by (simp add: eq_matI)
qed

lemma H_on_id2: "(H \<Otimes> id 2) = 1/sqrt(2) \<cdot>\<^sub>m  Matrix.mat 4 4 (\<lambda>(i,j). if i=0 \<and> j=0 then 1 else    \<comment> \<open>TODO\<close>
                                                (if i=0 \<and> j=2 then 1 else
                                                (if i=1 \<and> j=1 then 1 else
                                                (if i=1 \<and> j=3 then 1 else
                                                (if i=2 \<and> j=0 then 1 else
                                                (if i=2 \<and> j=2 then -1 else
                                                (if i=3 \<and> j=1 then 1 else
                                                (if i=3 \<and> j=3 then -1 else 0))))))))" 
proof
  define v::"complex Matrix.mat" where "v = 1/sqrt(2) \<cdot>\<^sub>m  Matrix.mat 4 4 (\<lambda>(i,j). if i=0 \<and> j=0 then 1 else    \<comment> \<open>TODO\<close>
                                                (if i=0 \<and> j=2 then 1 else
                                                (if i=1 \<and> j=1 then 1 else
                                                (if i=1 \<and> j=3 then 1 else
                                                (if i=2 \<and> j=0 then 1 else
                                                (if i=2 \<and> j=2 then -1 else
                                                (if i=3 \<and> j=1 then 1 else
                                                (if i=3 \<and> j=3 then -1 else 0))))))))"
  fix i j::nat
  assume "i<dim_row v" and "j<dim_col v" 
  then have "i\<in>{0,1,2,3}" and "j\<in>{0,1,2,3}"  using v_def by auto
  moreover have "Matrix.row (H \<Otimes> id 2) i \<bullet> Matrix.col v j = (\<Sum>k = 0..<4. Matrix.row (Matrix.mat 2 2 (\<lambda>(i, j). if i \<noteq> j then 1 else if i = 0 then 1 else - 1)) i $ k * Matrix.col |x\<rangle> j $ k)"
        by (smt a1 a2 One_nat_def dim_col_mat(1) dim_vec index_add_mat(3) ket_vec_col ket_vec_def less_Suc0 scalar_prod_def sum.cong)
     
  then have "v$$(i,j) = (H \<Otimes> id 2)$$(i,j)" using v_def scalar_prod_def cong_mat sorry
qed



lemma \<psi>\<^sub>2_to_\<psi>\<^sub>3:
  fixes "f"
  assumes "\<psi>\<^sub>2 \<equiv> Matrix.mat 4 1 (\<lambda>(i,j). if i=0 then ((inv_b (f 0))+ -f(0)) else
                                    (if i=1 then (f(0) + -(inv_b (f(0)))) else
                                    (if i=2 then ((inv_b (f(1)))+ -f(1)) else (f(1)+ -inv_b(f(1))))))" and "\<psi>\<^sub>3 \<equiv> Matrix.mat 4 1 (\<lambda>(i,j). if i = 0 then ((inv_b (f 0))+ -f(0))+ ((inv_b (f 1))+ -f(1)) else
                                    (if i = 1 then (f(0) + -(inv_b (f(0))))+ (f(1)+ -inv_b(f(1))) else
                                    (if i = 2 then  ((inv_b (f 0))+ -f(0))+-((inv_b (f(1)))+ -f(1)) else
                                    (f(0) + -(inv_b (f(0))))+ -(f(1)+ -inv_b(f(1))))))"
  shows "(H \<Otimes> id 2)*\<psi>\<^sub>2 =  \<psi>\<^sub>3"
proof
  fix i j::nat
  assume a1:"i < dim_row \<psi>\<^sub>3"
    and a2: "j < dim_col \<psi>\<^sub>3 "
  show "((H \<Otimes> Quantum.id 2) * \<psi>\<^sub>2) $$ (i, j) = \<psi>\<^sub>3 $$ (i,j)"
    (*by (smt H_inv  assms(1) dim_col_mat(1) dim_col_tensor_mat dim_row_mat(1) index_mult_mat(3) index_one_mat(3) index_row(2) index_smult_vec(2) mult.left_neutral mult_cancel_right numeral_eq_one_iff row_smult semiring_norm(85) t1 zero_less_numeral zero_neq_numeral)*)
    sorry
next
  show "dim_col ((H \<Otimes> Quantum.id 2) * \<psi>\<^sub>2) = dim_col \<psi>\<^sub>3"
    by (simp add: assms(1) assms(2))
next
  show "dim_row ((H \<Otimes> Quantum.id 2) * \<psi>\<^sub>2) = dim_row \<psi>\<^sub>3" sorry
     (*simp add:  H_on_id2 assms(1) assms(2) ket_vec_def*)
qed


definition DeutschAlgo:: "(nat\<Rightarrow>nat)\<Rightarrow> complex Matrix.mat" where (*TODO:Measurement*)
"DeutschAlgo f \<equiv> (H \<Otimes> id 2)*(U\<^sub>f f)*((H * |x\<rangle>) \<Otimes> (H * |y\<rangle>))"

lemma 
  fixes f::"nat\<Rightarrow>nat"
  assumes "deutsch f"
  shows "fun_is_con f \<longrightarrow> fst ((meas 2 (DeutschAlgo f) 0)!0) = 1" sorry


end
