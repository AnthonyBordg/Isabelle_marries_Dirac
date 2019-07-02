theory Deutsch_Jozsa_Algorithm 
imports
  MoreTensor
begin

  
section \<open>Deutsch-Jozsa algorithm\<close>


locale deutsch =
  fixes f:: "nat \<Rightarrow> nat"
  fixes n:: "nat"
  assumes dom: "f \<in> ({(i::nat). i \<le> 2^n} \<rightarrow>\<^sub>E {0,1})"


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
(*TODO: in third row take either last two out or first one*)

lemma f_ge_0: "\<forall> x. (f x \<ge> 0)" by simp




lemma (in deutsch) H_tensor_Id: 
  assumes "v \<equiv> Matrix.mat (2^(n+1)) (2^(n+1)) (\<lambda>(i,j). if i=j \<and> i \<le>(2^n) then 1/sqrt(2) else
                                                      (if i=j+(2^n) then 1/sqrt(2) else 
                                                        (if i+(2^n)=j then 1/sqrt(2) else
                                                          (if i=j \<and> i>(2^n) then -1/sqrt(2) else 0 ))))"
shows "(H \<Otimes> Id n) = v" 
proof
  show "dim_col (H \<Otimes> Id n) = dim_col v"  
    by(simp add: assms H_def Id_def)
  show "dim_row (H \<Otimes> Id n) = dim_row v"
    by(simp add: assms H_def Id_def)
  fix i j::nat assume "i < dim_row v" and "j < dim_col v"
  then have "i \<in> {0..<(2^(n+1))} \<and> j \<in> {0..<(2^(n+1))}" 
    by (auto simp add: assms mat_of_cols_list_def)
  thus "(H \<Otimes> Id n) $$ (i, j) = v $$ (i, j)" sorry
qed


end (* context deutsch *)


end