theory Deutsch_Jozsa_Algorithm 
imports
  MoreTensor
begin

  
section \<open>The Deutsch-Jozsa Algorithm\<close>


locale deutsch_jozsa =
  fixes f:: "nat \<Rightarrow> nat" and n:: "nat"
  assumes dom: "f \<in> ({(i::nat). i < 2^n} \<rightarrow>\<^sub>E {0,1})"
  assumes dim: "n \<ge> 1"


context deutsch_jozsa
begin

definition const:: "nat \<Rightarrow> bool" where 
"const c = (\<forall>x\<in>{i::nat. i < 2^n}. f x = c)"

definition is_const:: "bool" where 
"is_const \<equiv> const 0 \<or> const 1"

definition is_balanced:: "bool" where
"is_balanced \<equiv> \<exists>A B. A \<subseteq> {(i::nat). i < 2^n} \<and> B \<subseteq> {(i::nat). i < 2^n}
                   \<and> card A = (2^(n-1)) \<and> card B = (2^(n-1))  
                   \<and> (\<forall>x \<in> A. f(x) = 0)  \<and> (\<forall>x \<in> B. f(x) = 1)"
(*TODO: in third row take either last two out or first one, is there a better way to define it?*)

lemma is_balanced_inter:
  assumes "is_balanced"
  shows "A \<inter> B = {}" sorry

lemma is_balanced_union:
  assumes "is_balanced"
  shows "A \<union> B = {i::nat. i < 2^n}" sorry

lemma f_ge_0: "\<forall> x. (f x \<ge> 0)" by simp

lemma f_dom_not_zero: 
  shows "f \<in> ({(i::nat). n \<ge> 1 \<and>  i < 2^n} \<rightarrow>\<^sub>E {0,1})" 
  using dim dom by simp

end (* context deutsch_jozsa *)


definition (in deutsch_jozsa) deutsch_transform:: "complex Matrix.mat" ("U\<^sub>f") where 

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

lemma (in deutsch_jozsa) deutsch_transform_dim [simp]: 
  shows "dim_row U\<^sub>f = 4" and "dim_col U\<^sub>f = 4" 
  by (auto simp add: deutsch_transform_def mat_of_cols_list_def)

lemma (in deutsch_jozsa) deutsch_transform_coeff_is_zero [simp]: 
  shows "U\<^sub>f $$ (0,2) = 0" and "U\<^sub>f $$ (0,3) = 0"
    and "U\<^sub>f $$ (1,2) = 0" and "U\<^sub>f $$(1,3) = 0"
    and "U\<^sub>f $$ (2,0) = 0" and "U\<^sub>f $$(2,1) = 0"
    and "U\<^sub>f $$ (3,0) = 0" and "U\<^sub>f $$ (3,1) = 0"
  using deutsch_transform_def by auto

lemma (in deutsch_jozsa) deutsch_transform_coeff [simp]: 
  shows "U\<^sub>f $$ (0,1) = f(0)" and "U\<^sub>f $$ (1,0) = f(0)"
    and "U\<^sub>f $$(2,3) = f(1)" and "U\<^sub>f $$ (3,2) = f(1)"
    and "U\<^sub>f $$ (0,0) = 1 - f(0)" and "U\<^sub>f $$(1,1) = 1 - f(0)"
    and "U\<^sub>f $$ (2,2) = 1 - f(1)" and "U\<^sub>f $$ (3,3) = 1 - f(1)"
  using deutsch_transform_def by auto

abbreviation (in deutsch_jozsa) V\<^sub>f:: "complex Matrix.mat" where
"V\<^sub>f \<equiv> Matrix.mat 4 4 (\<lambda>(i,j). 
                if i=0 \<and> j=0 then 1 - f(0) else
                  (if i=0 \<and> j=1 then f(0) else
                    (if i=1 \<and> j=0 then f(0) else
                      (if i=1 \<and> j=1 then 1 - f(0) else
                        (if i=2 \<and> j=2 then 1 - f(1) else
                          (if i=2 \<and> j=3 then f(1) else
                            (if i=3 \<and> j=2 then f(1) else
                              (if i=3 \<and> j=3 then 1 - f(1) else 0))))))))"

lemma (in deutsch_jozsa) deutsch_transform_alt_rep_coeff_is_zero [simp]:
  shows "V\<^sub>f $$ (0,2) = 0" and "V\<^sub>f $$ (0,3) = 0"
    and "V\<^sub>f $$ (1,2) = 0" and "V\<^sub>f $$(1,3) = 0"
    and "V\<^sub>f $$ (2,0) = 0" and "V\<^sub>f $$(2,1) = 0"
    and "V\<^sub>f $$ (3,0) = 0" and "V\<^sub>f $$ (3,1) = 0"
  by auto

lemma (in deutsch_jozsa) deutsch_transform_alt_rep_coeff [simp]:
  shows "V\<^sub>f $$ (0,1) = f(0)" and "V\<^sub>f $$ (1,0) = f(0)"
    and "V\<^sub>f $$(2,3) = f(1)" and "V\<^sub>f $$ (3,2) = f(1)"
    and "V\<^sub>f $$ (0,0) = 1 - f(0)" and "V\<^sub>f $$(1,1) = 1 - f(0)"
    and "V\<^sub>f $$ (2,2) = 1 - f(1)" and "V\<^sub>f $$ (3,3) = 1 - f(1)"
  by auto

lemma (in deutsch_jozsa) deutsch_transform_alt_rep:
  shows "U\<^sub>f = V\<^sub>f"
proof
  show c0:"dim_row U\<^sub>f = dim_row V\<^sub>f" by simp
  show c1:"dim_col U\<^sub>f = dim_col V\<^sub>f" by simp
  fix i j:: nat
  assume "i < dim_row V\<^sub>f" and "j < dim_col V\<^sub>f"
  then have "i < 4" and "j < 4" by auto
  thus "U\<^sub>f $$ (i,j) = V\<^sub>f $$ (i,j)"
    by (smt deutsch_transform_alt_rep_coeff deutsch_transform_alt_rep_coeff_is_zero deutsch_transform_coeff
 deutsch_transform_coeff_is_zero set_four)
qed


text \<open>@{text U\<^sub>f} is a gate.\<close>


lemma (in deutsch_jozsa) transpose_of_deutsch_transform:
  shows "(U\<^sub>f)\<^sup>t = U\<^sub>f"
  sorry

lemma (in deutsch_jozsa) adjoint_of_deutsch_transform: 
  shows "(U\<^sub>f)\<^sup>\<dagger> = U\<^sub>f"
  sorry 

lemma (in deutsch_jozsa) deutsch_transform_is_gate:
  shows "gate 2 U\<^sub>f"
  sorry
   


abbreviation zero where "zero \<equiv> unit_vec 2 0"
abbreviation one where "one \<equiv> unit_vec 2 1"

fun pow_tensor :: "complex Matrix.mat \<Rightarrow> nat \<Rightarrow>  complex Matrix.mat" (infixr "^\<^sub>\<oplus>" 75) where
  "A ^\<^sub>\<oplus> (Suc 0) = A"  (*Seems more natural with 1 but might avoid stress if we fix the number to be the number of \<oplus>?*)
| "A ^\<^sub>\<oplus> (Suc k) =  A \<Otimes> (A ^\<^sub>\<oplus> k)"

lemma pow_tensor_1_is_id[simp]:
  fixes A
  shows "A ^\<^sub>\<oplus> 1 = A"
  using one_mat_def by auto

(*TODO: Use mat_of_cols_lists or Matrix.mat??? For Deutsch mat_of_cols_lists was better but
it seems as if Isabelle is not good with list comprehension and also Matrix.mat gives more natural
definition*)

(* There must be a better way to start an induction at 1 than this 
https://stackoverflow.com/questions/41384146/proof-by-induction-with-three-base-cases-isabelle
If not define induction rule*)

(*Proof outline*)


definition \<psi>\<^sub>0\<^sub>0:: "nat \<Rightarrow> complex Matrix.mat" where 
"\<psi>\<^sub>0\<^sub>0 k \<equiv> Matrix.mat (2^k) 1 (\<lambda>(i,j). if i=0 then 1 else 0)"

lemma \<psi>\<^sub>0\<^sub>0_is_unit:
  shows "\<psi>\<^sub>0\<^sub>0 n = |unit_vec (2^n) 0\<rangle>"
sorry 

lemma tensor_n_zero_is_\<psi>\<^sub>0\<^sub>0:
  assumes "n\<ge>1"
  shows " |zero\<rangle> ^\<^sub>\<oplus> n = \<psi>\<^sub>0\<^sub>0 n"
  sorry

definition \<psi>\<^sub>0\<^sub>1:: "complex Matrix.mat" where 
"\<psi>\<^sub>0\<^sub>1 \<equiv> |one\<rangle>"


(*------------------------------------------------------------------------------------------------*)

definition \<psi>\<^sub>1\<^sub>0:: "nat \<Rightarrow> complex Matrix.mat" where 
"\<psi>\<^sub>1\<^sub>0 n \<equiv> Matrix.mat (2^n) 1 (\<lambda>(i,j). 1/sqrt(2)^n)"

lemma "\<psi>\<^sub>0\<^sub>0_to_\<psi>\<^sub>1\<^sub>0":
  assumes "n\<ge>1"
  shows "(H ^\<^sub>\<oplus> n) * (\<psi>\<^sub>0\<^sub>0 n) = (\<psi>\<^sub>1\<^sub>0 n)"  
  sorry

definition \<psi>\<^sub>1\<^sub>1:: "complex Matrix.mat" where 
"\<psi>\<^sub>1\<^sub>1 \<equiv> Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1/sqrt(2) else -1/sqrt(2))"

lemma H_on_one_is_\<psi>\<^sub>1\<^sub>1:
  assumes "n\<ge>1"
  shows "H * \<psi>\<^sub>0\<^sub>1 = \<psi>\<^sub>1\<^sub>1"
  sorry


definition \<psi>\<^sub>1:: "nat \<Rightarrow> complex Matrix.mat" where 
"\<psi>\<^sub>1 k \<equiv> 1/sqrt(2)^k \<cdot>\<^sub>m  Matrix.mat (2^(k+1)) 1 (\<lambda>(i,j). if (even i) then 1  else -1)"

lemma \<psi>\<^sub>1\<^sub>0_tensor_\<psi>\<^sub>1\<^sub>1: 
  assumes "n\<ge>1"
  shows "(\<psi>\<^sub>1\<^sub>0 n) \<Otimes> \<psi>\<^sub>1\<^sub>1 = (\<psi>\<^sub>1 n)"
  sorry
(*------------------------------------------------------------------------------------------------*)


definition (in deutsch_jozsa) \<psi>\<^sub>2:: "nat \<Rightarrow> complex Matrix.mat" where 
"\<psi>\<^sub>2 k \<equiv> 1/sqrt(2)^k \<cdot>\<^sub>m  Matrix.mat (2^(k+1)) 1 (\<lambda>(i,j). if (even i) then (-1)^(f(i/2))
                                                       else (-1)^(f((i-1)/2)+1))"

lemma (in deutsch_jozsa) \<psi>\<^sub>1_tensor_\<psi>\<^sub>2: 
  assumes "n\<ge>1"
  shows "(U\<^sub>f ^\<^sub>\<oplus> n)* (\<psi>\<^sub>1 n) = (\<psi>\<^sub>2 n)"
  sorry



(*------------------------------------------------------------------------------------------------*)

lemma (in deutsch_jozsa) \<psi>\<^sub>1_tensor_\<psi>\<^sub>2: 
  assumes "n\<ge>1"
  shows "((H ^\<^sub>\<oplus> n) \<Otimes> Id 1 )* (\<psi>\<^sub>2 n) = (\<psi>\<^sub>3 n)"
  sorry


(*
lemma (in deutsch_jozsa)
  shows " |zero\<rangle> ^\<^sub>\<oplus> n  = |unit_vec (2^(n+1)) 0\<rangle>"
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


definition \<psi>\<^sub>0\<^sub>0:: "nat \<Rightarrow> complex Matrix.mat" where 
"\<psi>\<^sub>0\<^sub>0 n \<equiv> mat_of_cols_list (2^(n+1)) [[ (if i=0 then 1 else 0). i<- [0..(2^(n+1)-1)]]]"

definition \<psi>\<^sub>0\<^sub>0':: "nat \<Rightarrow> complex Matrix.mat" where 
"\<psi>\<^sub>0\<^sub>0' n \<equiv> Matrix.mat (2^(n+1)) 1 (\<lambda>(i,j). if i=0 then 1 else 0)"

lemma 
  fixes n
  shows "\<psi>\<^sub>0\<^sub>0' (n+1) = (\<psi>\<^sub>0\<^sub>0' 0) * (\<psi>\<^sub>0\<^sub>0' n)"
proof (induction n)
  have f0: "(\<psi>\<^sub>0\<^sub>0' 0) = Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1 else 0)" using \<psi>\<^sub>0\<^sub>0'_def by simp
  have f1: "(\<psi>\<^sub>0\<^sub>0' 1) = Matrix.mat 4 1 (\<lambda>(i,j). if i=0 then 1 else 0)" using \<psi>\<^sub>0\<^sub>0'_def by simp
  have  "i < dim_row (\<psi>\<^sub>0\<^sub>0' 0) \<and> j < dim_col  (\<psi>\<^sub>0\<^sub>0' 0) \<longrightarrow> i < 2 \<and> j < 1" sorry
  then have "i < dim_row (\<psi>\<^sub>0\<^sub>0' 0) \<and> j < dim_col  (\<psi>\<^sub>0\<^sub>0' 0) \<longrightarrow> 
            ((\<psi>\<^sub>0\<^sub>0' 0) * (\<psi>\<^sub>0\<^sub>0' 0)) $$ (i,j) = (\<psi>\<^sub>0\<^sub>0' (0+1)) $$ (i,j)" using f0 f1 \<psi>\<^sub>0\<^sub>0'_def
    scalar_prod_def times_mat_def sorry
  then show "\<psi>\<^sub>0\<^sub>0' (0+1) = (\<psi>\<^sub>0\<^sub>0' 0) * (\<psi>\<^sub>0\<^sub>0' 0)" using f0 f1 \<psi>\<^sub>0\<^sub>0'_def sorry
next
  show "\<psi>\<^sub>0\<^sub>0' (n+1) = (\<psi>\<^sub>0\<^sub>0' 0) * (\<psi>\<^sub>0\<^sub>0' n)" sorry
qed


definition \<psi>\<^sub>1\<^sub>0:: "nat \<Rightarrow> complex Matrix.mat" where 
"\<psi>\<^sub>1\<^sub>0 n \<equiv> mat_of_cols_list (2^(n+1)) [[1/(sqrt(2)^(n+1)). i<- [0..(2^(n+1)-1)]]]"

lemma (in deutsch_jozsa)
  shows "(H ^\<^sub>\<oplus> n) * (\<psi>\<^sub>0\<^sub>0 n)  = (\<psi>\<^sub>1\<^sub>0 n)"
proof (induction n)
  show "(H ^\<^sub>\<oplus> 0) * (\<psi>\<^sub>0\<^sub>0 0)  = (\<psi>\<^sub>1\<^sub>0 0)" (*Base case*)
  proof
    fix i j::nat
    assume a0: "i < dim_row (\<psi>\<^sub>1\<^sub>0 0)" and  
           a1: "j < dim_col (\<psi>\<^sub>1\<^sub>0 0)"
    then have f0: "i < 2 \<and> j = 0" using \<psi>\<^sub>1\<^sub>0_def mat_of_cols_list_def by auto
    then have "[[ (if i=0 then 1 else 0). i<- [0..(2^(0+1)-1)]]] = [[1,0]]"     
      by (simp add: list.simps(8) upto.simps)
    then have "(\<psi>\<^sub>0\<^sub>0 0) =  mat_of_cols_list 2 [[1,0]]" 
      by (smt \<psi>\<^sub>0\<^sub>0_def add.left_neutral power_one_right)
    then show  "((H ^\<^sub>\<oplus> 0) * (\<psi>\<^sub>0\<^sub>0 0)) $$ (i,j) = (\<psi>\<^sub>1\<^sub>0 0) $$ (i,j)"  
      by (auto simp add: a0 f0 mat_of_cols_list_def times_mat_def scalar_prod_def H_def \<psi>\<^sub>0\<^sub>0_def \<psi>\<^sub>1\<^sub>0_def)
  next
    have "dim_row (H * (\<psi>\<^sub>0\<^sub>0 0)) = dim_row (\<psi>\<^sub>1\<^sub>0 0)" (*TODO: Simplify this by assert dimensions*)
      using H_def \<psi>\<^sub>0\<^sub>0_def \<psi>\<^sub>1\<^sub>0_def mat_of_cols_list_def One_nat_def Suc_eq_plus1 dim_row_mat dim_row_tensor_mat 
        index_unit_vec plus_1_eq_Suc power_Suc0_right power_add
      by (metis (no_types, lifting) H_without_scalar_prod index_mult_mat(2)) 
   then show "dim_row (H ^\<^sub>\<oplus> 0 * \<psi>\<^sub>0\<^sub>0 0) = dim_row (\<psi>\<^sub>1\<^sub>0 0)" by auto
  next
    show  "dim_col (H ^\<^sub>\<oplus> 0 * \<psi>\<^sub>0\<^sub>0 0) = dim_col (\<psi>\<^sub>1\<^sub>0 0)" 
      using H_def \<psi>\<^sub>0\<^sub>0_def \<psi>\<^sub>1\<^sub>0_def mat_of_cols_list_def by auto
  qed
next (*Step case*)
  fix n
  assume "(H ^\<^sub>\<oplus> n) * (\<psi>\<^sub>0\<^sub>0 n)  = (\<psi>\<^sub>1\<^sub>0 n)"
  then have "(\<psi>\<^sub>0\<^sub>0 (Suc n)) = ((\<psi>\<^sub>0\<^sub>0 0)* (\<psi>\<^sub>0\<^sub>0 n))" sorry
  then have "(H ^\<^sub>\<oplus> (Suc n)) * (\<psi>\<^sub>0\<^sub>0 (Suc n))  = (H * (\<psi>\<^sub>0\<^sub>0 0)) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)" sorry
  moreover have "(H * (\<psi>\<^sub>0\<^sub>0 0)) = mat_of_cols_list 4 [[1/sqrt(2), 1/sqrt(2)]]" sorry 
  moreover have "mat_of_cols_list 4 [[1/sqrt(2), 1/sqrt(2)]] \<Otimes> (\<psi>\<^sub>1\<^sub>0 n) = (\<psi>\<^sub>1\<^sub>0 (Suc n))" sorry
  ultimately show "(H ^\<^sub>\<oplus> (Suc n)) * (\<psi>\<^sub>0\<^sub>0 (Suc n))  = (\<psi>\<^sub>1\<^sub>0 (Suc n))" by auto
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
  qed*)*)


end