(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk *)

theory Tensor
imports
  Main
  HOL.Complex
  Quantum
  Jordan_Normal_Form.Matrix
  Matrix_Tensor.Matrix_Tensor
begin

text{* There is already a formalization of tensor products in the Archive of Formal Proofs, 
namely Matrix_Tensor.thy in Tensor Product of Matrices[1] by T.V.H. Prathamesh, but it does not build 
on top of the formalization of vectors and matrices given in Matrices, Jordan Normal Forms, and 
Spectral Radius Theory[2] by René Thiemann and Akihisa Yamada. 
In the present theory our purpose consists in giving such a formalization. Of course, we will reuse 
Prathamesh's code as much as possible, and in order to achieve that we formalize some lemmas that
translate back and forth between vectors (resp. matrices) seen as lists (resp. lists of lists) and 
vectors (resp. matrices) as formalized in [2].
*}

section \<open>Tensor Products\<close>

subsection \<open>The Kronecker Product of Complex Vectors\<close>

definition tensor_vec ::"complex Matrix.vec \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" (infixl "\<otimes>" 63) 
where "tensor_vec u v \<equiv> vec_of_list (mult.vec_vec_Tensor ( * ) (list_of_vec u) (list_of_vec v))"

subsection \<open>The Tensor Product of Complex Matrices\<close>

text\<open>To see a matrix in the sense of [2] as a matrix in the sense of [1], we convert it into its list
of column vectors.\<close>

definition mat_to_cols_list :: "complex Matrix.mat \<Rightarrow> complex list list" where
  "mat_to_cols_list A = [ [A $$ (i,j) . i <- [0 ..< dim_row A]] . j <- [0 ..< dim_col A]]"

lemma length_mat_to_cols_list:
  shows "length (mat_to_cols_list A) = dim_col A"
  by (simp add: mat_to_cols_list_def)

lemma length_cols_mat_to_cols_list:
  assumes "j < dim_col A"
  shows "length [A $$ (i,j) . i <- [0 ..< dim_row A]] = dim_row A"
  using assms 
  by simp

lemma length_row_mat_to_cols_list:
  assumes "i < dim_row A"
  shows "length (row (mat_to_cols_list A) i) = dim_col A"
  using assms
  by (simp add: Matrix_Legacy.row_def length_mat_to_cols_list)

lemma length_col_mat_to_cols_list:
  assumes "j < dim_col A"
  shows "length (col (mat_to_cols_list A) j) = dim_row A"
  using assms
  by (simp add: Matrix_Legacy.col_def mat_to_cols_list_def)

lemma mat_to_cols_list_is_not_Nil:
  assumes "dim_col A > 0"
  shows "mat_to_cols_list A \<noteq> []"
  using assms
  by (simp add: mat_to_cols_list_def)

(* Link between Matrix_Tensor.row_length and Matrix.dim_row *)

lemma row_length_mat_to_cols_list:
  assumes "dim_col A > 0"
  shows "mult.row_length (mat_to_cols_list A) = dim_row A"
proof-
  have "mat_to_cols_list A \<noteq> []"
    using assms mat_to_cols_list_is_not_Nil 
    by auto
  then have "mult.row_length (mat_to_cols_list A) = length (hd (mat_to_cols_list A))"
    using mult.row_length_def[of "1" "( * )"]
    by (simp add: \<open>\<And>xs. Matrix_Tensor.mult 1 ( * ) \<Longrightarrow> mult.row_length xs \<equiv> if xs = [] then 0 else length (hd xs)\<close> mult.intro)
  thus ?thesis
    using assms mat_to_cols_list_def length_cols_mat_to_cols_list[of 0]
    by (simp add: upt_conv_Cons)
qed

(* mat_to_cols_list is a matrix in the sense of the theory Matrix_Legacy. *)

lemma mat_to_cols_list_is_mat:
  assumes "dim_col A > 0"
  shows "Matrix_Legacy.mat (mult.row_length (mat_to_cols_list A)) (length (mat_to_cols_list A)) (mat_to_cols_list A)"
proof-
  have "Ball (set (mat_to_cols_list A)) (Matrix_Legacy.vec (mult.row_length (mat_to_cols_list A)))"
    using assms row_length_mat_to_cols_list mat_to_cols_list_def Ball_def set_def Matrix_Legacy.vec_def
    by fastforce
  thus ?thesis
    using Matrix_Legacy.mat_def 
    by auto
qed

definition mat_of_cols_list :: "nat \<Rightarrow> complex list list \<Rightarrow> complex Matrix.mat" where
  "mat_of_cols_list nr cs = Matrix.mat nr (length cs) (\<lambda> (i,j). cs ! j ! i)"

lemma index_mat_of_cols_list:
  assumes "i < nr" and "j < length cs"
  shows "mat_of_cols_list nr cs $$ (i,j) = cs ! j ! i"
  using assms mat_of_cols_list_def 
  by simp 

lemma mat_to_cols_list_to_mat:
  shows "mat_of_cols_list (dim_row A) (mat_to_cols_list A) = A"
proof-
  have f1:"dim_row (mat_of_cols_list (dim_row A) (mat_to_cols_list A)) = dim_row A"
    by (simp add: Tensor.mat_of_cols_list_def)
  have f2:"dim_col (mat_of_cols_list (dim_row A) (mat_to_cols_list A)) = dim_col A"
    by (simp add: Tensor.mat_of_cols_list_def length_mat_to_cols_list)
  have "\<And>i j. i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> 
    (mat_of_cols_list (dim_row A) (mat_to_cols_list A)) $$ (i, j) = A $$ (i, j)"
    by (simp add: Tensor.mat_of_cols_list_def mat_to_cols_list_def)
  thus ?thesis
    using f1 f2 eq_matI 
    by auto
qed

lemma plus_mult_cpx:
  shows "plus_mult 1 ( * ) 0 (+) (a_inv cpx_rng)"
  apply unfold_locales
  apply (auto intro: cpx_cring simp: field_simps)
proof-
  show "\<And>x. x + \<ominus>\<^bsub>cpx_rng\<^esub> x = 0"
    using group.r_inv[of "cpx_rng"] cpx_cring field_def domain_def cpx_rng_def
    by (metis UNIV_I cring.cring_simprules(17) ordered_semiring_record_simps(1) 
        ordered_semiring_record_simps(11) ordered_semiring_record_simps(12))
  show "\<And>x. x + \<ominus>\<^bsub>cpx_rng\<^esub> x = 0"
    using group.r_inv[of "cpx_rng"] cpx_cring field_def domain_def cpx_rng_def
    by (metis UNIV_I cring.cring_simprules(17) ordered_semiring_record_simps(1) 
        ordered_semiring_record_simps(11) ordered_semiring_record_simps(12))
qed

lemma list_to_mat_to_cols_list:
  fixes l::"complex list list"
  assumes "mat nr nc l"
  shows "mat_to_cols_list (mat_of_cols_list nr l) = l"
proof-
  have f1:"length (mat_to_cols_list (mat_of_cols_list nr l)) = length l"
    by (simp add: Tensor.mat_of_cols_list_def length_mat_to_cols_list)
  have f2:"\<forall>j<length l. length(l ! j) = mult.row_length l"
    using assms plus_mult.row_length_constant plus_mult_cpx
    by fastforce
  have f3:"\<And>j. j<length l \<longrightarrow> mat_to_cols_list (mat_of_cols_list nr l) ! j = l ! j"
  proof
    fix j
    assume a1:"j < length l"
    then have f4:"length (mat_to_cols_list (mat_of_cols_list nr l) ! j) = length (l ! j)"
      by (metis Matrix_Legacy.col_def Matrix_Legacy.mat_def Matrix_Legacy.vec_def Tensor.mat_of_cols_list_def 
          assms dim_col_mat(1) dim_row_mat(1) length_col_mat_to_cols_list nth_mem)
    then have " \<forall>i<mult.row_length l. mat_to_cols_list (mat_of_cols_list nr l) ! j ! i = l ! j ! i"
      using a1 mat_to_cols_list_def mat_of_cols_list_def f2 
      by simp
    thus "mat_to_cols_list (Tensor.mat_of_cols_list nr l) ! j = l ! j"
      using f4
      by (simp add: nth_equalityI a1 f2)
  qed
  thus ?thesis
    using f1
    by (simp add: nth_equalityI)
qed

definition tensor_mat ::"complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" (infixl "\<Otimes>" 63)
  where 
"tensor_mat A B \<equiv> 
  mat_of_cols_list (dim_row A * dim_row B) (mult.Tensor ( * ) (mat_to_cols_list A) (mat_to_cols_list B))"
  
lemma dim_row_tensor_mat:
  shows "dim_row (A \<Otimes> B) = dim_row A * dim_row B"
  by (simp add: mat_of_cols_list_def tensor_mat_def)

lemma dim_col_tensor_mat:
  shows "dim_col (A \<Otimes> B) = dim_col A * dim_col B"
  using tensor_mat_def mat_of_cols_list_def Matrix_Tensor.mult.length_Tensor[of "1" "( * )"] 
    length_mat_to_cols_list
  by (smt ab_semigroup_mult_class.mult_ac(1) comm_monoid_mult_class.mult_1 dim_col_mat(1) 
      mult.commute mult.intro)

lemma index_tensor_mat:
  assumes "dim_row A = rA" and "dim_col A = cA" and "dim_row B = rB" and "dim_col B = cB"
    and "i < rA * rB" and "j < cA * cB" and "cA > 0" and "cB > 0"
  shows "(A \<Otimes> B) $$ (i,j) = A $$ (i div rB, j div cB) * B $$ (i mod rB, j mod cB)"
proof-
  have f1:"(A \<Otimes> B) $$ (i,j) = (mult.Tensor ( * ) (mat_to_cols_list A) (mat_to_cols_list B)) ! j ! i"
    using assms tensor_mat_def mat_of_cols_list_def dim_col_tensor_mat 
    by auto
  have f2:"i < mult.row_length (mat_to_cols_list A) * mult.row_length (mat_to_cols_list B)"
    using assms(1) assms(2) assms(3) assms(4) assms(5) assms(7) assms(8) row_length_mat_to_cols_list
    by simp
  have f3:"j < length (mat_to_cols_list A) * length (mat_to_cols_list B)"
    using assms(2) assms(4) assms(6) length_mat_to_cols_list 
    by simp
  have f4:"Matrix_Legacy.mat (mult.row_length (mat_to_cols_list A)) (length (mat_to_cols_list A)) (mat_to_cols_list A)"
    using assms(2) assms(7) mat_to_cols_list_is_mat 
    by simp
  have f5:"Matrix_Legacy.mat (mult.row_length (mat_to_cols_list B)) (length (mat_to_cols_list B)) (mat_to_cols_list B)"
    using assms(4) assms(8) mat_to_cols_list_is_mat
    by simp
  then have "(A \<Otimes> B) $$ (i,j) = 
    (mat_to_cols_list A) ! (j div length (mat_to_cols_list B)) ! (i div mult.row_length (mat_to_cols_list B)) 
    * (mat_to_cols_list B) ! (j mod length (mat_to_cols_list B)) ! (i mod mult.row_length (mat_to_cols_list B))"
    using mult.matrix_Tensor_elements[of "1" "( * )"] f1 f2 f3 f4 f5
    by (simp add: \<open>\<And>M2 M1. Matrix_Tensor.mult 1 ( * ) \<Longrightarrow> \<forall>i j. (i < mult.row_length M1 * mult.row_length M2 
    \<and> j < length M1 * length M2) \<and> Matrix_Legacy.mat (mult.row_length M1) (length M1) M1 \<and> 
    Matrix_Legacy.mat (mult.row_length M2) (length M2) M2 \<longrightarrow> 
    mult.Tensor ( * ) M1 M2 ! j ! i = M1 ! (j div length M2) ! (i div mult.row_length M2) * M2 ! (j mod length M2) ! (i mod mult.row_length M2)\<close> f1 f2 mult.intro)
  thus ?thesis
    using mat_to_cols_list_def
    by (metis Euclidean_Division.div_eq_0_iff assms(2) assms(3) assms(4) assms(6) assms(7) assms(8) 
        f2 index_mat_of_cols_list length_mat_to_cols_list less_mult_imp_div_less less_nat_zero_code 
        mat_to_cols_list_to_mat mod_div_trivial mult_eq_0_iff row_length_mat_to_cols_list)
qed

lemma dim_vec_vec_of_list:
  shows "dim_vec (vec_of_list l) = length l"
  by (metis dim_vec vec.abs_eq vec_of_list.abs_eq)

lemma index_vec_of_list:
  assumes "i < length l"
  shows "vec_of_list l $ i = l ! i"
  using assms
  by (metis index_vec vec.abs_eq vec_of_list.abs_eq) 

(* To go from Matrix.row to Matrix_Legacy.row *)

lemma Matrix_row_is_Legacy_row:
  assumes "i < dim_row A"
  shows "Matrix.row A i = vec_of_list (Matrix_Legacy.row (mat_to_cols_list A) i)"
proof-
  have f1:"dim_vec (Matrix.row A i) = dim_vec (vec_of_list (Matrix_Legacy.row (mat_to_cols_list A) i))"
    using length_mat_to_cols_list dim_vec_vec_of_list
    by (metis Matrix_Legacy.row_def index_row(2) length_map)
  have "\<And>j. j < dim_col A \<Longrightarrow> (Matrix.row A i) $ j = (vec_of_list (Matrix_Legacy.row (mat_to_cols_list A) i)) $ j"
    using Matrix.row_def vec_of_list_def mat_to_cols_list_def
    by (smt Matrix_Legacy.row_def Tensor.mat_of_cols_list_def assms index_mat(1) index_vec length_map 
        length_mat_to_cols_list mat_to_cols_list_to_mat nth_map old.prod.case vec.abs_eq vec_of_list.abs_eq)
  thus ?thesis
    using f1 eq_vecI 
    by auto
qed

lemma length_list_of_vec:
  shows "length (list_of_vec v) = dim_vec v"
  using Rep_vec mk_vec_def
  by (simp add: list_of_vec_def case_prod_unfold dim_vec.rep_eq)

lemma index_list_of_vec:
  assumes "i < dim_vec v"
  shows "list_of_vec v ! i = v $ i"
  apply (auto intro: index_vec simp add: list_of_vec_def)
  using assms Rep_vec mk_vec_def
  by (simp add: case_prod_unfold dim_vec.rep_eq vec_index.rep_eq) 

(* To go from Matrix_Legacy.row to Matrix.row *)

lemma Legacy_row_is_Matrix_row:
  assumes "i < mult.row_length A"
  shows "Matrix_Legacy.row A i = list_of_vec (Matrix.row (mat_of_cols_list (mult.row_length A) A) i)"
proof-
  have f1:"length (Matrix_Legacy.row A i) = length (list_of_vec (Matrix.row (mat_of_cols_list (mult.row_length A) A) i))"
    using Matrix_Legacy.row_def length_list_of_vec
    by (metis Tensor.mat_of_cols_list_def dim_col_mat(1) index_row(2) length_map)
  have f2:"\<forall>j<length (Matrix_Legacy.row A i). (Matrix_Legacy.row A i) ! j = A ! j ! i"
    by (simp add: Matrix_Legacy.row_def)
  have f3:"\<forall>j<length (Matrix_Legacy.row A i). (list_of_vec (Matrix.row (mat_of_cols_list (mult.row_length A) A) i)) ! j = A ! j ! i"
    using assms index_mat_of_cols_list index_list_of_vec
    by (simp add: index_list_of_vec Tensor.mat_of_cols_list_def f1 length_list_of_vec)
  then have "\<forall>j<length (Matrix_Legacy.row A i). (Matrix_Legacy.row A i) ! j = (list_of_vec (Matrix.row (mat_of_cols_list (mult.row_length A) A) i)) ! j"
    using f2 f3 
    by simp
  thus ?thesis
    using f1 nth_equalityI 
    by blast
qed

(* To go from Matrix.col to Matrix_Legacy.col *)

lemma Matrix_col_is_Legacy_col:
  assumes "j < dim_col A"
  shows "Matrix.col A j = vec_of_list (Matrix_Legacy.col (mat_to_cols_list A) j)"
proof-
  have f1:"dim_vec (Matrix.col A j) = dim_vec (vec_of_list (Matrix_Legacy.col (mat_to_cols_list A) j))"
    using length_mat_to_cols_list dim_vec_vec_of_list
    by (simp add: dim_vec_vec_of_list Matrix_Legacy.col_def assms mat_to_cols_list_def)
  have "\<And>i. i < dim_row A \<Longrightarrow> (Matrix.col A j) $ i = (vec_of_list (Matrix_Legacy.col (mat_to_cols_list A) j)) $ i"
    using Matrix.col_def vec_of_list_def mat_to_cols_list_def
    by (smt Matrix_Legacy.col_def assms diff_zero dim_col dim_vec_vec_of_list f1 index_mat_of_cols_list 
        index_vec length_map length_upt mat_to_cols_list_to_mat vec.abs_eq vec_of_list.abs_eq)
  thus ?thesis
    using f1 eq_vecI 
    by auto
qed

(* To go from Matrix_Legacy.col to Matrix.col *)

lemma Legacy_col_is_Matrix_col:
  assumes "j < length A" and "length (A ! j) = mult.row_length A"
  shows "Matrix_Legacy.col A j = list_of_vec (Matrix.col (mat_of_cols_list (mult.row_length A) A) j)"
proof-
  have "length (list_of_vec (Matrix.col (mat_of_cols_list (mult.row_length A) A) j)) = dim_vec (Matrix.col (mat_of_cols_list (mult.row_length A) A) j)"
    using length_list_of_vec
    by blast
  then have "length (list_of_vec (Matrix.col (mat_of_cols_list (mult.row_length A) A) j)) = dim_row (mat_of_cols_list (mult.row_length A) A)"
    using Matrix.col_def 
    by simp
  then have f1:"length (list_of_vec (Matrix.col (mat_of_cols_list (mult.row_length A) A) j)) = mult.row_length A"
    by (simp add: Tensor.mat_of_cols_list_def)
  then have f2:"length (Matrix_Legacy.col A j) = length (list_of_vec (Matrix.col (mat_of_cols_list (mult.row_length A) A) j))"
    using assms(2)
    by (simp add: Matrix_Legacy.col_def)
  have f3:"\<forall>i<mult.row_length A. (Matrix_Legacy.col A j) ! i = A ! j ! i"
    by (simp add: Matrix_Legacy.col_def)
  have f4:"\<forall>i<mult.row_length A. (list_of_vec (Matrix.col (mat_of_cols_list (mult.row_length A) A) j)) ! i = A ! j ! i"
    using assms index_mat_of_cols_list
    by (simp add: index_list_of_vec Tensor.mat_of_cols_list_def)
  then have "\<forall>i<mult.row_length A. (Matrix_Legacy.col A j) ! i = (list_of_vec (Matrix.col (mat_of_cols_list (mult.row_length A) A) j)) ! i"
    using f3
    by simp
  thus ?thesis
    using f1 f2
    by (simp add: nth_equalityI) 
qed

(* Link between Matrix_Tensor.scalar_product and Matrix.scalar_prod *)

lemma scalar_prod_is_Matrix_scalar_prod:
  fixes u::"complex list" and v::"complex list"
  assumes "length u = length v"
  shows "plus_mult.scalar_product ( * ) 0 (+) u v = (vec_of_list u) \<bullet> (vec_of_list v)"
proof-
  have f1:"(vec_of_list u) \<bullet> (vec_of_list v) = (\<Sum>i=0..<length v. u ! i * v ! i)"
    using assms scalar_prod_def[of "vec_of_list u" "vec_of_list v"] dim_vec_vec_of_list[of v] 
      index_vec_of_list
    by (metis (no_types, lifting) atLeastLessThan_iff sum.cong)
  thus ?thesis
  proof-
    have "plus_mult.scalar_product ( * ) 0 (+) u v = semiring_0_class.scalar_prod u v"
      using plus_mult_cpx Matrix_Tensor.plus_mult.scalar_product_def[of 1 "( * )" 0 "(+)" "a_inv cpx_rng" u v] 
      by simp
    then have f2:"plus_mult.scalar_product ( * ) 0 (+) u v = sum_list (map (\<lambda>(x,y). x * y) (zip u v))"
      using scalar_prod 
      by simp
    have "\<forall>i<length v. (zip u v) ! i = (u ! i, v ! i)"
      using assms zip_def 
      by simp
    then have "\<forall>i<length v. (map (\<lambda>(x,y). x * y) (zip u v)) ! i = u ! i * v ! i"
      by (simp add: assms)
    then have "plus_mult.scalar_product ( * ) 0 (+) u v = (\<Sum>i=0..<length v. u ! i * v ! i)"
      using assms f2
      by (metis (no_types, lifting) atLeastLessThan_iff length_map map_fst_zip sum.cong sum_list_sum_nth)
    thus ?thesis
      using f1 
      by simp
  qed
qed

(* Link between Matrix.times_mat and Matrix_Tensor.matrix_mult *)

lemma matrix_mult_to_times_mat:
  assumes "dim_col A > 0" and "dim_col B > 0" and "dim_col (A::complex Matrix.mat) = dim_row B"
  shows "A * B = mat_of_cols_list (dim_row A) (plus_mult.matrix_mult ( * ) 0 (+) (mat_to_cols_list A) (mat_to_cols_list B))"
proof-
  define M where "M = mat_of_cols_list (dim_row A) (plus_mult.matrix_mult ( * ) 0 (+) (mat_to_cols_list A) (mat_to_cols_list B))"
  then have f1:"dim_row (A * B) = dim_row M"
    using mat_of_cols_list_def times_mat_def 
    by simp
  have "length (plus_mult.matrix_mult ( * ) 0 (+) (mat_to_cols_list A) (mat_to_cols_list B)) = dim_col B"
    by (simp add: mat_multI_def length_mat_to_cols_list)
  then have f2:"dim_col (A * B) = dim_col M"
    using M_def times_mat_def mat_of_cols_list_def 
    by simp
  have "\<And>i j. i < dim_row A \<Longrightarrow> j < dim_col B \<Longrightarrow> (A * B) $$ (i, j) = M $$ (i, j)"
  proof-
    fix i j
    assume a1:"i < dim_row A" and a2:"j < dim_col B"
    have "(A * B) $$ (i,j) = Matrix.row A i \<bullet> Matrix.col B j"
      using a1 a2 index_mult_mat 
      by simp
    then have "(A * B) $$ (i,j) = vec_of_list (Matrix_Legacy.row (mat_to_cols_list A) i) \<bullet> vec_of_list (Matrix_Legacy.col (mat_to_cols_list B) j)"
      using a1 a2 Matrix_row_is_Legacy_row Matrix_col_is_Legacy_col 
      by simp
    then have f3:"(A * B) $$ (i,j) = plus_mult.scalar_product ( * ) 0 (+) (Matrix_Legacy.row (mat_to_cols_list A) i) (Matrix_Legacy.col (mat_to_cols_list B) j)"
      using length_row_mat_to_cols_list length_col_mat_to_cols_list a1 a2 assms(3)
      by (simp add: scalar_prod_is_Matrix_scalar_prod)
    have "M $$ (i,j) =  plus_mult.scalar_product ( * ) 0 (+) (Matrix_Legacy.row (mat_to_cols_list A) i) (Matrix_Legacy.col (mat_to_cols_list B) j)"
    proof-
      have f4:"M $$ (i,j) = (plus_mult.matrix_mult ( * ) 0 (+) (mat_to_cols_list A) (mat_to_cols_list B)) ! j ! i"
        using M_def Matrix.mat_of_cols_list_def
        by (simp add: \<open>length (mat_mult (mult.row_length (mat_to_cols_list A)) (mat_to_cols_list A) (mat_to_cols_list B)) = dim_col B\<close> a1 a2 index_mat_of_cols_list)
      have f5:"mat (mult.row_length (mat_to_cols_list A)) (dim_col A) (mat_to_cols_list A)"
        using mat_to_cols_list_is_mat assms(1) length_mat_to_cols_list 
        by simp
      have f6:"mat (dim_col A) (dim_col B) (mat_to_cols_list B)"
        using assms(2) assms(3) mat_to_cols_list_is_mat length_mat_to_cols_list
        by (simp add: row_length_mat_to_cols_list)
      thus ?thesis
        using assms(1) a1 a2 row_length_mat_to_cols_list plus_mult.matrix_index[of 1 "( * )" 0 "(+)"] f4 f5 f6
          plus_mult_cpx 
        by fastforce
    qed
    thus "(A * B) $$ (i, j) = M $$ (i, j)"
      using f3 
      by simp
  qed
  thus ?thesis
    using f1 f2 eq_matI M_def 
    by auto
qed

lemma mat_to_cols_list_times_mat:
  assumes "dim_col A = dim_row B" and "dim_col A > 0"
  shows "mat_to_cols_list (A * B) = plus_mult.matrix_mult ( * ) 0 (+) (mat_to_cols_list A) (mat_to_cols_list B)"
proof-
  define M where "M = plus_mult.matrix_mult ( * ) 0 (+) (mat_to_cols_list A) (mat_to_cols_list B)"
  have f1:"length (mat_to_cols_list (A * B)) = length M"
    using length_mat_to_cols_list M_def
    by (simp add: mat_multI_def)
  have f2:"\<And>j. j< dim_col B \<longrightarrow> mat_to_cols_list (A * B) ! j = M ! j"
  proof
    fix j
    assume a1:"j < dim_col B"
    then have f3:"length (mat_to_cols_list (A * B) ! j) = dim_row A"
      using length_cols_mat_to_cols_list
      by (simp add: mat_to_cols_list_def)
    have f4:"length (M ! j) = dim_row A"
      using M_def a1 mat_multI_def[of 0 "(+)" "( * )" "dim_row A" "mat_to_cols_list A" "mat_to_cols_list B"] 
        row_length_mat_to_cols_list assms(2)
      by (metis Matrix_Legacy.mat_def length_map length_mat_to_cols_list matT_vec_multI_def 
          mat_to_cols_list_is_mat nth_map transpose)
    from f3 f4 have f5:"length (mat_to_cols_list (A * B) ! j) = length (M ! j)" 
      by simp
    have "\<And>i. i<dim_row A \<longrightarrow> mat_to_cols_list (A * B) ! j ! i = M ! j ! i"
    proof
      fix i
      assume a2:"i < dim_row A"
      have f6:"mat (mult.row_length (mat_to_cols_list A)) (dim_col A) (mat_to_cols_list A)"
        using mat_to_cols_list_is_mat assms(2)
        by (simp add: length_mat_to_cols_list)
      have f7:"mat (dim_col A) (dim_col B) (mat_to_cols_list B)"
        using mat_to_cols_list_is_mat assms(1) length_mat_to_cols_list a1 row_length_mat_to_cols_list 
        by simp
      from f6 f7 have f8:"M ! j ! i = plus_mult.scalar_product ( * ) 0 (+) (row (mat_to_cols_list A) i) (col (mat_to_cols_list B) j)"
        using plus_mult.matrix_index a1 a2 row_length_mat_to_cols_list assms(2) plus_mult_cpx M_def
        by metis
      then have "M ! j ! i = vec_of_list (row (mat_to_cols_list A) i) \<bullet> vec_of_list (col (mat_to_cols_list B) j)"
        using scalar_prod_is_Matrix_scalar_prod length_row_mat_to_cols_list length_col_mat_to_cols_list 
          a2 a1 assms(1)
        by (simp add: scalar_prod_is_Matrix_scalar_prod)
      thus "mat_to_cols_list (A * B) ! j ! i = M ! j ! i"
        using mat_to_cols_list_def index_mult_mat(1) a1 a2 Matrix_row_is_Legacy_row Matrix_col_is_Legacy_col 
        by simp
    qed
    thus "mat_to_cols_list (A * B) ! j = M ! j"
      using f5 nth_equalityI
      by (simp add: nth_equalityI f4)
  qed
  thus ?thesis
    using f1 f2 nth_equalityI
    by (simp add: nth_equalityI M_def length_mat_to_cols_list)
qed

(* 
Finally, we prove that the tensor product of complex matrices is distributive over the 
multiplication of complex matrices. 
*)

lemma mult_distr_tensor:
  assumes "dim_col A = dim_row B" and "dim_col C = dim_row D" and "dim_col A > 0" and "dim_col B > 0"
    and "dim_col C > 0" and "dim_col D > 0"
  shows "(A * B) \<Otimes> (C * D) = (A \<Otimes> C) * (B \<Otimes> D)"
proof-
  define A' B' C' D' M N where "A' = mat_to_cols_list A" and "B' = mat_to_cols_list B" and 
    "C' = mat_to_cols_list C" and "D' = mat_to_cols_list D" and
    "M = mat_of_cols_list (dim_row A * dim_row C) (mult.Tensor ( * ) (mat_to_cols_list A) (mat_to_cols_list C))" and
    "N = mat_of_cols_list (dim_row B * dim_row D) (mult.Tensor ( * ) (mat_to_cols_list B) (mat_to_cols_list D))"
  then have "(A \<Otimes> C) * (B \<Otimes> D) = M * N"
    using tensor_mat_def 
    by simp
  then have "(A \<Otimes> C) * (B \<Otimes> D) = mat_of_cols_list (dim_row A * dim_row C) (plus_mult.matrix_mult ( * ) 0 (+) 
  (mat_to_cols_list M) (mat_to_cols_list N))"
    using assms matrix_mult_to_times_mat M_def N_def dim_col_tensor_mat dim_row_tensor_mat tensor_mat_def 
    by auto
  then have f1:"(A \<Otimes> C) * (B \<Otimes> D) = mat_of_cols_list (dim_row A * dim_row C) (plus_mult.matrix_mult ( * ) 0 (+) 
  (mult.Tensor ( * ) A' C') (mult.Tensor ( * ) B' D'))"
  proof-
    define M' N' where "M' = mult.Tensor ( * ) (mat_to_cols_list A) (mat_to_cols_list C)" and
      "N' = mult.Tensor ( * ) (mat_to_cols_list B) (mat_to_cols_list D)"
    then have 1:"mat (mult.row_length M') (length M') M'"
      using M'_def mult.effective_well_defined_Tensor[of 1 "( * )"] mat_to_cols_list_is_mat assms(3) assms(5)
      by (smt mult.length_Tensor mult.row_length_mat plus_mult_cpx plus_mult_def)
    have 2: "mat (mult.row_length N') (length N') N'"
      using N'_def mult.effective_well_defined_Tensor[of 1 "( * )"] mat_to_cols_list_is_mat assms(4) assms(6)
      by (smt mult.length_Tensor mult.row_length_mat plus_mult_cpx plus_mult_def)
    thus ?thesis
      using list_to_mat_to_cols_list 1 2 M_def N_def mult.row_length_mat row_length_mat_to_cols_list 
      assms(3) assms(4) assms(5) assms(6) A'_def B'_def C'_def D'_def
      by (metis M'_def N'_def \<open>(A \<Otimes> C) * (B \<Otimes> D) = Tensor.mat_of_cols_list (dim_row A * dim_row C) 
        (mat_mult (mult.row_length (mat_to_cols_list M)) (mat_to_cols_list M) (mat_to_cols_list N))\<close> plus_mult_cpx plus_mult_def)
   qed
   then have "(A \<Otimes> C) * (B \<Otimes> D) = mat_of_cols_list (dim_row A * dim_row C) (mult.Tensor ( * )
    (plus_mult.matrix_mult ( * ) 0 (+) A' B')
    (plus_mult.matrix_mult ( * ) 0 (+) C' D'))"
   proof-
     have f2:"mat (mult.row_length A') (length A') A'"
       using A'_def assms(3) mat_to_cols_list_is_mat 
       by simp
     have f3:"mat (mult.row_length B') (length B') B'"
       using B'_def assms(4) mat_to_cols_list_is_mat 
       by simp
     have f4:"mat (mult.row_length C') (length C') C'"
       using C'_def assms(5) mat_to_cols_list_is_mat 
       by simp
     have f5:"mat (mult.row_length D') (length D') D'"
       using D'_def assms(6) mat_to_cols_list_is_mat 
       by simp
     have f6:"length A' = mult.row_length B'"
       using A'_def B'_def assms(1) assms(4) row_length_mat_to_cols_list length_mat_to_cols_list 
       by simp
     have f7:"length C' = mult.row_length D'"
       using C'_def D'_def assms(2) assms(6) row_length_mat_to_cols_list length_mat_to_cols_list 
       by simp
     have f8:"A' \<noteq> [] \<and> B' \<noteq> [] \<and> C' \<noteq> [] \<and> D' \<noteq> []"
       using A'_def B'_def C'_def D'_def assms(3) assms(4) assms(5) assms(6) mat_to_cols_list_is_not_Nil 
       by simp
     from f2 f3 f4 f5 f6 f7 f8 have "plus_mult.matrix_match A' B' C' D'"
       using plus_mult.matrix_match_def[of 1 "( * )" 0 "(+)" "a_inv cpx_rng"] plus_mult_cpx 
       by simp
     thus ?thesis
       using f1 plus_mult.distributivity plus_mult_cpx
       by fastforce
   qed
   then have "(A \<Otimes> C) * (B \<Otimes> D) = mat_of_cols_list (dim_row A * dim_row C) (mult.Tensor ( * ) 
   (mat_to_cols_list (A * B)) (mat_to_cols_list (C * D)))"
     using mat_to_cols_list_times_mat A'_def B'_def C'_def D'_def assms(1) assms(2) assms(3) assms(5) 
     by auto
   thus ?thesis
     using tensor_mat_def 
     by simp
qed

lemma tensor_gate:
  assumes "G1 \<in> gate_of_dim m" and "G2 \<in> gate_of_dim n"
  shows "G1 \<Otimes> G2 \<in> gate_of_dim (m + n)" sorry




end