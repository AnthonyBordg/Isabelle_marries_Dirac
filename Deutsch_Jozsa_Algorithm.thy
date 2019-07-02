theory Deutsch_Jozsa_Algorithm 
imports
  MoreTensor
begin

  
section \<open>Deutsch-Jozsa algorithm\<close>


locale deutsch =
  fixes f:: "nat \<Rightarrow> nat"
  fixes n:: "nat"
  assumes dom: "f \<in> ({(i::nat). i < 2^n} \<rightarrow>\<^sub>E {0,1})"


context deutsch
begin

definition const:: "nat \<Rightarrow> bool" where 
"const c = (\<forall>x.(f x = c))"

definition deutsch_const:: "bool" where 
"deutsch_const \<equiv> const 0 \<or> const 1"

definition balanced:: "bool" where
"balanced \<equiv> \<exists>A B. A \<subseteq> {(i::nat). i \<le> 2^n} \<and> B \<subseteq> {(i::nat). i \<le> 2^n} 
            \<and> A \<inter> B = {} \<and> A \<union> B = {(i::nat). i \<le> 2^n}
            \<and> card A  = card B \<and> card A = (2^(n-1)) \<and> card B = (2^(n-1))  
            \<and> (\<forall>x \<in> A . f(x) = 0)  \<and> (\<forall>x \<in> B . f(x) = 1)"
(*TODO: in third row take either last two out or first one, is there a better way to define it?*)

lemma f_ge_0: "\<forall> x. (f x \<ge> 0)" by simp
end (* context deutsch *)


abbreviation zero where "zero \<equiv> unit_vec 2 0"
abbreviation one where "one \<equiv> unit_vec 2 1"

(*abbreviation (in deutsch) zero_tensor_n ("0\<^sup>\<oplus>") where "zero_tensor_n \<equiv> unit_vec (2^(n+1)) 0"*)


fun pow_tensor :: "complex Matrix.mat \<Rightarrow> nat \<Rightarrow>  complex Matrix.mat" (infixr "^\<^sub>\<oplus>" 75) where
  "A ^\<^sub>\<oplus> 0 = A"
| "A ^\<^sub>\<oplus> (Suc k) =  A \<Otimes> (A ^\<^sub>\<oplus> k)"


lemma (in deutsch)
  shows "|zero\<rangle> ^\<^sub>\<oplus> n  = |unit_vec (2^(n+1)) 0\<rangle>"
proof (induction n)
  show "|zero\<rangle> ^\<^sub>\<oplus> 0  = |unit_vec (2^(0+1)) 0\<rangle>" using ket_vec_def by auto
next
  fix n 
  assume "|zero\<rangle> ^\<^sub>\<oplus> n  = |unit_vec (2^(n+1)) 0\<rangle>" 
  then have f0: "|zero\<rangle> ^\<^sub>\<oplus> (Suc n)  = |zero\<rangle> \<Otimes> |unit_vec (2^(n+1)) 0\<rangle>" by auto
  show  "|zero\<rangle> ^\<^sub>\<oplus> (Suc n)  = |unit_vec (2^((Suc n)+1)) 0\<rangle>"
  proof
    fix i j::nat
    assume "i < dim_row |unit_vec (2^((Suc n)+1)) 0\<rangle>" and "j < dim_col |unit_vec (2^((Suc n)+1)) 0\<rangle>"
    then have a0: "i < 2^(n+2)" and a1: "j = 0" using ket_vec_def by auto
    then have "( |zero\<rangle> \<Otimes> |unit_vec (2^(n+1)) 0\<rangle>) $$(i,j)  = ( |unit_vec (2^((Suc n)+1)) 0\<rangle>)$$(i,j)" 
      using ket_vec_def mat_to_cols_list_def f0 mult.Tensor_def unit_vec_def by auto
    then show "( |zero\<rangle> ^\<^sub>\<oplus> (Suc n)) $$ (i,j)  = ( |unit_vec (2^((Suc n)+1)) 0\<rangle>)$$(i,j)" using f0 by auto
  next
    show "dim_row ( |zero\<rangle> ^\<^sub>\<oplus> Suc n) = dim_row |unit_vec (2 ^ (Suc n + 1)) 0\<rangle>" 
      using f0 ket_vec_def
      by (metis One_nat_def Suc_eq_plus1 dim_row_mat dim_row_tensor_mat index_unit_vec plus_1_eq_Suc power_Suc0_right power_add)
  next
    show "dim_col ( |zero\<rangle> ^\<^sub>\<oplus> Suc n) = dim_col |unit_vec (2 ^ (Suc n + 1)) 0\<rangle>"
      using f0 ket_vec_def by auto
  qed
qed


definition A:: "nat \<Rightarrow> complex Matrix.mat" where 
"A n \<equiv> mat_of_cols_list (2^(n+1)) [[ (if i=0 then 1 else 0). i<- [0..(2^(n+1)-1)]]]"

definition B:: "nat \<Rightarrow> complex Matrix.mat" where 
"B n \<equiv> mat_of_cols_list (2^(n+1)) [[1/(sqrt(2)^(n+1)). i<- [0..(2^(n+1)-1)]]]"

lemma (in deutsch)
  shows "(H ^\<^sub>\<oplus> n) * (A n)  = (B n)"
proof (induction n)
  show "(H ^\<^sub>\<oplus> 0) * (A 0)  = (B 0)" (*Base case*)
  proof
    fix i j::nat
    assume "i < dim_row (B 0)" and  
           "j < dim_col (B 0)"
    then have r0:"i < 2 \<and> j = 0" using B_def mat_of_cols_list_def by auto
    then have a0: "i < dim_row (H ^\<^sub>\<oplus> 0) \<and> j < dim_col (A 0)" sorry 
    then have "[[ (if i=0 then 1 else 0). i<- [0..(2^(0+1)-1)]]] = [[1,0]]"     
      by (simp add: list.simps(8) upto.simps)
    then have "(A 0) =  mat_of_cols_list 2 [[1,0]]" 
      by (smt A_def add.left_neutral power_one_right)
    then show  "((H ^\<^sub>\<oplus> 0) * (A 0)) $$ (i,j) = (B 0) $$ (i,j)"  
      by (auto simp add: a0 r0 mat_of_cols_list_def times_mat_def scalar_prod_def H_def A_def B_def)
  next
    have "dim_row (H * (A 0)) = dim_row (B 0)" (*TODO: Simplify this by assert dimensions*)
      using H_def A_def B_def mat_of_cols_list_def One_nat_def Suc_eq_plus1 dim_row_mat dim_row_tensor_mat 
        index_unit_vec plus_1_eq_Suc power_Suc0_right power_add
      by (metis (no_types, lifting) H_without_scalar_prod index_mult_mat(2)) 
   then show "dim_row (H ^\<^sub>\<oplus> 0 * A 0) = dim_row (B 0)" by auto
  next
    show  "dim_col (H ^\<^sub>\<oplus> 0 * A 0) = dim_col (B 0)" 
      using H_def A_def B_def mat_of_cols_list_def by auto
  qed
next (*Step case*)
  fix n
  assume "(H ^\<^sub>\<oplus> n) * (A n)  = (B n)"
  then have "(H ^\<^sub>\<oplus> (Suc n)) * (A (Suc n))  = (H * (A 0)) \<Otimes> (B n)" sorry
  moreover have "(H * (A 0)) = mat_of_cols_list 4 [[1/sqrt(2), 1/sqrt(2)]]" sorry 
  moreover have "mat_of_cols_list 4 [[1/sqrt(2), 1/sqrt(2)]] \<Otimes> (B n) = (B (Suc n))" sorry
  ultimately show "(H ^\<^sub>\<oplus> (Suc n)) * (A (Suc n))  = (B (Suc n))" by auto
qed



(*
  fix n 
  assume "|zero\<rangle> ^\<^sub>\<oplus> n  = |unit_vec (2^(n+1)) 0\<rangle>" 
  then have f0: "|zero\<rangle> ^\<^sub>\<oplus> (Suc n)  = |zero\<rangle> \<Otimes> |unit_vec (2^(n+1)) 0\<rangle>" by auto
  show  "|zero\<rangle> ^\<^sub>\<oplus> (Suc n)  = |unit_vec (2^((Suc n)+1)) 0\<rangle>"
  proof
    fix i j::nat
    assume "i < dim_row |unit_vec (2^((Suc n)+1)) 0\<rangle>" and "j < dim_col |unit_vec (2^((Suc n)+1)) 0\<rangle>"
    then have a0: "i < 2^(n+2)" and a1: "j = 0" using ket_vec_def by auto
    then have "( |zero\<rangle> \<Otimes> |unit_vec (2^(n+1)) 0\<rangle>) $$(i,j)  = ( |unit_vec (2^((Suc n)+1)) 0\<rangle>)$$(i,j)" 
      using ket_vec_def mat_to_cols_list_def f0 mult.Tensor_def unit_vec_def by auto
    then show "( |zero\<rangle> ^\<^sub>\<oplus> (Suc n)) $$ (i,j)  = ( |unit_vec (2^((Suc n)+1)) 0\<rangle>)$$(i,j)" using f0 by auto
  next
    show "dim_row ( |zero\<rangle> ^\<^sub>\<oplus> Suc n) = dim_row |unit_vec (2 ^ (Suc n + 1)) 0\<rangle>" 
      using f0 ket_vec_def
      by (metis One_nat_def Suc_eq_plus1 dim_row_mat dim_row_tensor_mat index_unit_vec plus_1_eq_Suc power_Suc0_right power_add)
  next
    show "dim_col ( |zero\<rangle> ^\<^sub>\<oplus> Suc n) = dim_col |unit_vec (2 ^ (Suc n + 1)) 0\<rangle>"
      using f0 ket_vec_def by auto
  qed*)
end