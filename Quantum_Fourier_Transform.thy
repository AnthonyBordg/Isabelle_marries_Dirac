theory Quantum_Fourier_Transform
imports
  More_Tensor
  Binary_Nat
  Basics
begin

section \<open>Quantum Fourier Tranform\<close>


(* Since I wanted to know early if the approach was feasible some proofs might have unnecessary intermediate
steps or are not needed anymore. Also the way I named the variables in the theorems is inconsistent. 
Of course this does not matter for the proofs themselves but for readability purposes it would be nice 
to use the same variable name if you talk about the same thing. E.g. sometimes j and sometimes jd is used, 
k stands for different things...*)

(*It might be nice to change all assumptions of the form
   "(\<forall>x \<in> set xs. dim_row x = 2)" and "(\<forall>y \<in> set ys. dim_row y = 2)"
 into "(\<forall>x \<in> set xs. x =zero \<or> x=one)" 
*)



(*It would be also possible to use this: abbreviation zero where "zero \<equiv> unit_vec 2 0" 
  Also the ket_vec def could be used here*)
abbreviation zero::"complex Matrix.mat" where "zero \<equiv> (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1 else 0))"
abbreviation one::"complex Matrix.mat" where "one \<equiv> (Matrix.mat 2 1 (\<lambda>(i,j). if i=1 then 1 else 0))" 

lemma Id_left_tensor[simp]: 
  shows "(Id 0) \<Otimes> A = A" 
  using one_mat_def Id_def by auto 

lemma Id_right_tensor[simp]:
  shows "A \<Otimes> (Id 0) = A"   
  using one_mat_def Id_def by auto 

lemma Id_mult_left[simp]:
  assumes "dim_row A = 2^m"
  shows "Id m * A = A"
  using Id_def one_mat_def by (simp add: assms)

lemma aux_calculation[simp]:
  fixes m k c::nat
  shows "m>k \<and> k\<ge>1 \<longrightarrow> (2::nat)^(k-Suc 0) * 2 * 2^(m-k) = 2^m"
    and "m>k \<and> k\<ge>1 \<longrightarrow> (2::nat)^(m-Suc 0) = 2^(k-Suc 0) * 2^(m-k)"
    and "m>k \<longrightarrow> Suc (m-Suc k) = m - k" 
    and "1\<le>k-c \<and> m\<ge>k \<and> m\<ge>c \<longrightarrow> (2::nat)^(k-Suc c) * 2 * 2^(m-k) = 2^(m-c)" 
    and "c\<le>m \<and> k\<ge>c+1 \<and> m\<ge>(Suc k) \<longrightarrow> k - c - 1 + 2 + (m - Suc k) = m - c"
    and "1\<le>k-c \<and> m\<ge>k \<and> m\<ge>c \<longrightarrow> (2::nat) * 2^(k-c-1) * 2 * 2^(m-k) = 2^(m-c+1)" 
    and "1\<le>k-c \<and> m\<ge>k \<and> m\<ge>c \<longrightarrow> (2::nat)^(m-c) = 2 * 2^(k-Suc c) * 2^(m-k)"
    and "k\<ge>c \<and> m\<ge>(Suc k) \<longrightarrow> (2::nat)^(k-c) * 2 * 2^(m-Suc k) = 2^(m-c)"
proof-
  show "m>k \<and> k\<ge>1 \<longrightarrow> (2::nat)^(k-Suc 0) * 2 * 2^(m-k) = 2^m"
    by (metis One_nat_def le_add_diff_inverse less_or_eq_imp_le not_less_eq_eq power_add power_commutes power_eq_if)
next
  show "m>k \<and> k\<ge>1 \<longrightarrow> (2::nat)^(m-Suc 0) = 2^(k-Suc 0) * 2^(m-k)"
    by (metis Nat.add_diff_assoc2 One_nat_def le_add_diff_inverse less_or_eq_imp_le power_add)
next
  show "m>k \<longrightarrow> Suc (m - Suc k) = m - k" 
    using Suc_diff_Suc by blast
next
  show "1\<le>k-c \<and> m\<ge>k \<and> m\<ge>c \<longrightarrow> (2::nat)^(k-Suc c) * 2 * 2^(m-k) = 2^(m-c)" 
    by (metis Nat.add_diff_assoc2 One_nat_def Suc_diff_Suc Suc_le_eq le_add_diff_inverse nat_diff_split 
        not_le not_one_le_zero power_add semiring_normalization_rules(28) zero_less_diff)
next
  show "c\<le>m \<and> k\<ge>c+1 \<and> m\<ge>(Suc k) \<longrightarrow> k - c - 1 + 2 + (m - Suc k) = m-c" by auto
next
  show "1\<le>k-c \<and> m\<ge>k \<and> m\<ge>c \<longrightarrow> (2::nat) * 2^(k-c-1) * 2 * 2^(m-k) = 2^(m-c+1)" 
    by (metis (no_types, lifting) Nat.add_diff_assoc2 le_add_diff_inverse nat_diff_split not_le not_one_le_zero 
        power_add power_commutes semigroup_mult_class.mult.assoc semiring_normalization_rules(33))
next 
  show "1\<le>k-c \<and> m\<ge>k \<and> m\<ge>c \<longrightarrow> (2::nat) ^ (m - c) = 2 * 2 ^ (k - Suc c) * 2 ^ (m - k)" 
    by (metis (no_types, hide_lams) add_diff_assoc2 diff_diff_right Suc_diff_Suc diff_diff_cancel diff_le_self
        less_imp_le_nat neq0_conv not_one_le_zero power_add semiring_normalization_rules(28) semiring_normalization_rules(7) zero_less_diff)
next
  show "k\<ge>c \<and> m\<ge>(Suc k) \<longrightarrow> (2::nat)^(k-c) * 2 * 2^(m-Suc k) = 2^(m-c)"
    by (metis (no_types, lifting) Nat.add_diff_assoc2 Suc_eq_plus1 add.assoc le_add_diff_inverse power_add semiring_normalization_rules(28))
qed


subsection \<open>Transformation of j into a tensor product of single qubits\<close>

(*Gives back a part of j starting at position s which is t qubits long. 
E.g. j=$|01011\rangle$, s=2 and l=3 gives [1,0,1]*)
primrec j_to_list_bound :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list" where
"j_to_list_bound s 0 m j = []" |
"j_to_list_bound s (Suc l) m j = (if (bin_rep m j)!(s-1) = 0 then zero else one) # (j_to_list_bound (s+1) l m j)"

(*Takes a list and the number of elements in this list and gives out the tensor product of the elements*)
fun pow_tensor_list :: "((complex Matrix.mat) list) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("pw _ _" 75)  where
  "(pw [] 0) = (Id 0)"  |
  "(pw (Cons x xs) (Suc k)) = x \<Otimes> (pw xs k)"

(*Defines the part of j where s is the start position and t the number of bits as tensor product of single qubits
where j is a decimal number that is smaller than m. E.g. $|j_1,...,j_n\rangle$ and s=2 and l=3 gives $|j_2,j_3,j_4\rangle$ *)
definition j_to_tensor_prod :: "nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>complex Matrix.mat" ("j\<Otimes> _ _ _ _" 75) where 
"(j\<Otimes> s l m j) = pw (j_to_list_bound s l m j) l"

lemma j_to_list_bound_one [simp]:
  shows "j_to_list_bound s 1 m j = [(if (bin_rep m j)!(s-1) = 0 then zero else one)]" by simp

lemma pow_tensor_list_one [simp]:
  assumes "xs = []" 
  shows "(pw (Cons x xs) 1) = x" 
  by (simp add: assms)

lemma j_to_tensor_prod_length_0[simp]:
  shows "(j\<Otimes> s 0 j m) = (Id 0)"    
  by (simp add: j_to_tensor_prod_def)

lemma j_to_tensor_prod_decomp_right_zero:
  shows "(bin_rep m j)!(s+l-1) = 0 \<longrightarrow> (j\<Otimes> s (l+1) m j) = (j\<Otimes> s l m j) \<Otimes> zero"
proof(induction l arbitrary: s)
  show "(bin_rep m j)!(s+0-1) = 0 \<longrightarrow> (j\<Otimes> s (0+1) m j) = (j\<Otimes> s 0 m j) \<Otimes> zero" for s
      using j_to_list_bound_one j_to_tensor_prod_def by auto
next
  fix l s
  assume IH: "(bin_rep m j)!(s+l-1) = 0 \<longrightarrow> (j\<Otimes> s (l+1) m j) = (j\<Otimes> s l m j) \<Otimes> zero" for s
  show "(bin_rep m j)!(s+(Suc l)-1) = 0 \<longrightarrow> (j\<Otimes> s ((Suc l)+1) m j) = (j\<Otimes> s (Suc l) m j) \<Otimes> zero"
  proof
    assume a0: "(bin_rep m j)!(s+(Suc l)-1) = 0"
    then have "(j\<Otimes> s ((Suc l)+1) m j) = (if (bin_rep m j)!(s-1) = 0 then zero else one) \<Otimes> pw ((j_to_list_bound (s+1) (Suc l) m j)) (Suc l)" 
      using j_to_tensor_prod_def by auto
    also have "... = (if (bin_rep m j)!(s-1) = 0 then zero else one) \<Otimes> (j\<Otimes> (s+1) (l+1) m j)" 
      by (metis Suc_eq_plus1 j_to_tensor_prod_def)
    also have "... = (if (bin_rep m j)!(s-1) = 0 then zero else one) \<Otimes> (j\<Otimes> (s+1) l m j) \<Otimes> zero"
      using a0 IH tensor_mat_is_assoc by auto
    also have "... = (pw (j_to_list_bound s (l+1) m j) (l+1)) \<Otimes> zero"
      using j_to_tensor_prod_def by auto
    finally show "(j\<Otimes> s ((Suc l)+1) m j) = (j\<Otimes> s (Suc l) m j) \<Otimes> zero"
      using j_to_tensor_prod_def by auto
  qed
qed

lemma j_to_tensor_prod_decomp_right_one:
   shows "(bin_rep m j)!(s+l-1) = 1 \<longrightarrow> (j\<Otimes> s (l+1) m j) = (j\<Otimes> s l m j) \<Otimes> one"
proof(induction l arbitrary: s)
  show "(bin_rep m j)!(s+0-1) = 1 \<longrightarrow> (j\<Otimes> s (0+1) m j) = (j\<Otimes> s 0 m j) \<Otimes> one" for s
    using j_to_list_bound_one j_to_tensor_prod_def by auto
next
  fix l s
  assume IH: "(bin_rep m j)!(s+l-1) = 1 \<longrightarrow> (j\<Otimes> s (l+1) m j) = (j\<Otimes> s l m j) \<Otimes> one" for s
  show "(bin_rep m j)!(s+(Suc l)-1) = 1 \<longrightarrow> (j\<Otimes> s ((Suc l)+1) m j) = (j\<Otimes> s (Suc l) m j) \<Otimes> one"
  proof (*Can be shortened but I think this is better*)
    assume a0: "(bin_rep m j)!(s+(Suc l)-1) = 1"
    have "(j\<Otimes> s ((Suc l)+1) m j) = (if (bin_rep m j)!(s-1) = 0 then zero else one) \<Otimes> pw ((j_to_list_bound (s+1) (Suc l) m j)) (Suc l)" 
      using j_to_tensor_prod_def by auto
    also have "... = (if (bin_rep m j)!(s-1) = 0 then zero else one) \<Otimes> (j\<Otimes> (s+1) (l+1) m j)" 
      by (metis Suc_eq_plus1 j_to_tensor_prod_def)
    also have "... = (if (bin_rep m j)!(s-1) = 0 then zero else one) \<Otimes> (j\<Otimes> (s+1) l m j) \<Otimes> one"
      using a0 IH tensor_mat_is_assoc by auto
    also have "... = (if (bin_rep m j)!(s-1) = 0 then zero else one) \<Otimes> (pw (j_to_list_bound (s+1) l m j) l) \<Otimes> one"
      using j_to_tensor_prod_def by auto
    also have "... = (pw (j_to_list_bound s (l+1) m j) (l+1)) \<Otimes> one"
      by auto
    finally show "(j\<Otimes> s ((Suc l)+1) m j) = (j\<Otimes> s (Suc l) m j) \<Otimes> one"
      using j_to_tensor_prod_def by auto
  qed
qed

(*TODO: Might be nicer to reformulate everything at just assert that all elements of this lists have to 
be unit vectors.*)
(*Could be generalized but is only used in this form*)
lemma pow_tensor_list_dim_col:
  assumes "length xs = k" and "(\<forall>x \<in> set xs. dim_col x = 1)"
  shows "dim_col (pw xs k) = 1" 
proof-
  have "length xs = k \<longrightarrow> (\<forall>x \<in> set xs. dim_col x = 1) \<longrightarrow> dim_col (pw xs k) = 1"
  proof(induction k arbitrary: xs)
    fix xs
    show "length xs = 0 \<longrightarrow> (\<forall>x \<in> set xs. dim_col x = 1) \<longrightarrow> dim_col (pw xs 0) = 1" 
      using Id_def one_mat_def by auto
  next
    fix k xs
    assume IH: "length xs = k \<longrightarrow> (\<forall>x \<in> set xs. dim_col x = 1) \<longrightarrow> dim_col (pw xs k) = 1" for xs
    show "length xs = (Suc k) \<longrightarrow> (\<forall>x \<in> set xs. dim_col x = 1) \<longrightarrow> dim_col (pw xs (Suc k)) = 1"
    proof(rule impI, rule impI)
      assume a0: "length xs = (Suc k)" and a1: "(\<forall>x \<in> set xs. dim_col x = 1)"
      then have "\<exists>x. xs = x # tl xs" by (metis length_Suc_conv list.sel(3))
      then obtain x where f0: "xs = x # tl xs" by blast 
      have "dim_col (pw xs (Suc k)) = dim_col (x \<Otimes> (pw (tl xs) k))" 
        using pow_tensor_list.simps f0 by metis
      also have "... = 1 * dim_col ((pw (tl xs) k))" 
        using a1 f0 by (metis dim_col_tensor_mat list.set_intros(1))
      finally show "dim_col (pw xs (Suc k)) = 1" 
        using IH a0 a1 f0 by (metis add_diff_cancel_left' length_tl list.distinct(1) list.set_sel(2) mult.left_neutral plus_1_eq_Suc)
    qed
  qed
  then show ?thesis using assms by auto
qed

lemma pow_tensor_list_dim_row:
  assumes "length xs = k" and "(\<forall>x \<in> set xs. dim_row x = m)"
  shows "dim_row (pw xs k) = m^k"
proof-
  have "length xs = k \<longrightarrow> (\<forall>x \<in> set xs. dim_row x = m) \<longrightarrow> dim_row (pw xs k) = m^k"
  proof(induction k arbitrary: xs)
    fix xs
    show "length xs = 0 \<longrightarrow> (\<forall>x \<in> set xs. dim_row x = m) \<longrightarrow> dim_row (pw xs 0) = m^0" 
      using Id_def one_mat_def by auto
  next
    fix k xs
    assume IH: "length xs = k \<longrightarrow> (\<forall>x \<in> set xs. dim_row x = m) \<longrightarrow> dim_row (pw xs k) = m^k" for xs
    show "length xs = (Suc k) \<longrightarrow> (\<forall>x \<in> set xs. dim_row x = m) \<longrightarrow> dim_row (pw xs (Suc k)) = m^(Suc k)"
    proof(rule impI, rule impI)
      assume a0: "length xs = (Suc k)" and a1: "(\<forall>x \<in> set xs. dim_row x = m)"
      then have "\<exists>x. xs = x # tl xs" by (metis length_Suc_conv list.sel(3))
      then obtain x where f0: "xs = x # tl xs" by blast 
      have "dim_row (pw xs (Suc k)) = dim_row (x \<Otimes> (pw (tl xs) k))" 
        using pow_tensor_list.simps f0 by metis
      also have "... = m * dim_row ((pw (tl xs) k))" 
        using a1 f0 by (metis dim_row_tensor_mat list.set_intros(1))
      also have "... = m * m^k" 
        using IH a0 a1 f0 by (metis add_diff_cancel_left' length_tl list.distinct(1) list.set_sel(2) plus_1_eq_Suc)
      finally show "dim_row (pw xs (Suc k)) = m^(Suc k)" by auto
    qed
  qed
  then show ?thesis using assms by auto
qed

lemma pow_tensor_decomp_left:
  fixes k::nat and x::"complex Matrix.mat" 
  assumes "length xs = k"
  shows "(pw xs k) \<Otimes> x = pw (xs@[x]) (k+1)" 
proof-
  have "length xs = k \<longrightarrow> (pw xs k) \<Otimes> x = pw (xs@[x]) (k+1)" 
  proof(induction k arbitrary: xs)
    fix xs
    show "length xs = 0 \<longrightarrow> (pw xs 0) \<Otimes> x = pw (xs@[x]) (0+1)"  
      using Id_left_tensor Id_def by auto
  next
    fix k xs
    assume IH: "length xs = k \<longrightarrow> (pw xs k) \<Otimes> x = pw (xs@[x]) (k+1)" for xs
    show "length xs = (Suc k) \<longrightarrow> (pw xs (Suc k)) \<Otimes> x = pw (xs@[x]) ((Suc k)+1)"
    proof
      assume a0: "length xs = (Suc k)"
      moreover have "xs=(y#ys) \<longrightarrow> pw (xs@[x]) ((Suc k)+1) = (pw xs (Suc k)) \<Otimes> x" 
        for y::"complex Matrix.mat" and ys::"complex Matrix.mat list"
      proof
        assume a2: "xs=y#ys"
        then have "pw (xs@[x]) ((Suc k)+1) = y \<Otimes> pw (ys@[x]) (k+1)" by simp
        moreover have "length ys = k" using a2 using a0 by auto 
        ultimately have "pw (xs@[x]) ((Suc k)+1) = y \<Otimes> ((pw ys k) \<Otimes> x)" using IH by auto
        also have "... = (y \<Otimes> (pw ys k)) \<Otimes> x" using tensor_mat_is_assoc by auto
        also have "... = (pw (y#ys) (Suc k)) \<Otimes> x" by auto
        finally show "pw (xs@[x]) ((Suc k)+1) = (pw xs (Suc k)) \<Otimes> x" using a2 by auto
      qed
      ultimately show "(pw xs (Suc k)) \<Otimes> x = pw (xs@[x]) ((Suc k)+1)" by (metis Suc_length_conv)
    qed
  qed
  then show ?thesis using assms by auto
qed

lemma pow_tensor_decomp_right:
  assumes "length xs = k"
  shows "x \<Otimes> (pw xs k) = pw (x#xs) (k+1)" 
  using Suc_le_D assms(1) by force

lemma j_to_list_bound_length:
  fixes s l m j::nat
  shows "length (j_to_list_bound s l m j) = l"
proof(induction l arbitrary: s)
  show "length (j_to_list_bound s 0 m j) = 0" for s by auto
next
  fix l s
  assume IH: "length (j_to_list_bound s l m j) = l" for s
  have "length (j_to_list_bound s (Suc l) m j) = length ((if (bin_rep m j)!(s-1) = 0 then zero else one) 
                                                 # (j_to_list_bound (s+1) l m j))" by auto
  then have "length (j_to_list_bound s (Suc l) m j) = length [(if (bin_rep m j)!(s-1) = 0 then zero else one)]
                                                    + length (j_to_list_bound (s+1) l m j)" by simp
  moreover have "length [(if (bin_rep m j)!(s-1) = 0 then zero else one)] = 1" by auto
  moreover have "length (j_to_list_bound (s+1) l m j) = l" using IH by auto
  ultimately show "length (j_to_list_bound s (Suc l) m j) = (Suc l)" by auto
qed

lemma j_to_list_bound_dim_row:
  shows "\<forall>x \<in> set (j_to_list_bound s l m j). dim_row x = 2"
  apply (induction l arbitrary: s)
   apply (auto simp: j_to_list_bound_def).
(* 
Without apply. Which one is nicer?
proof(induction l arbitrary: s)
  show "\<forall>x \<in> set (j_to_list_bound s 0 m j). dim_row x = 2" for s by auto
next
  fix l s
  assume IH: "\<forall>x \<in> set (j_to_list_bound s l m j). dim_row x = 2" for s
  show "\<forall>x \<in> set (j_to_list_bound s (Suc l) m j). dim_row x = 2"
  proof
    fix x 
    assume a0: "x \<in> set (j_to_list_bound s (Suc l) m j)"
    then have "set (j_to_list_bound s (Suc l) m j) = set ((if (bin_rep m j)!(s-1) = 0 then zero else one) # (j_to_list_bound (s+1) l m j))"
      using j_to_list_bound_def by auto
    then show "dim_row x = 2"
      using IH a0 by auto
  qed
qed*)

lemma j_to_list_bound_dim_col:
  shows "\<forall>x\<in>set (j_to_list_bound s l m j). dim_col x = 1"
  apply (induction l arbitrary: s)
   apply (auto simp: j_to_list_bound_def).
(* 
Without apply. Which one is nicer?
proof(induction l arbitrary: s)
  show "\<forall>x\<in>set (j_to_list_bound s 0 m j). dim_col x = 1" for s by auto
next
  fix l s
  assume IH: "\<forall>x\<in>set (j_to_list_bound s l m j). dim_col x = 1" for s
  show "\<forall>x\<in>set (j_to_list_bound s (Suc l) m j). dim_col x = 1"
  proof
    fix x 
    assume a0: "x \<in> set (j_to_list_bound s (Suc l) m j)"
    then have "set (j_to_list_bound s (Suc l) m j) = set ((if (bin_rep m j)!(s-1) = 0 then zero else one) # (j_to_list_bound (s+1) l m j))"
      using j_to_list_bound_def by auto
    then show "dim_col x = 1"
      using IH a0 by auto
  qed
qed
*)

lemma j_to_tensor_prod_dim_row:
  shows "dim_row (j\<Otimes> s l m j) = 2^l" 
proof-
  have "dim_row (j\<Otimes> s l m j) = dim_row (pw (j_to_list_bound s l m j) l)"
    using j_to_tensor_prod_def by auto
  moreover have "length (j_to_list_bound s l m j) = l" 
    using j_to_list_bound_length by auto
  moreover have "\<forall>x\<in>set (j_to_list_bound s l m j). dim_row x = 2" 
    using j_to_list_bound_dim_row by auto
  ultimately show "dim_row (j\<Otimes> s l m j) = 2^l"
    using pow_tensor_list_dim_row by auto
qed

lemma j_to_tensor_prod_dim_col:
  shows "dim_col (j\<Otimes> s l m j) = 1" 
proof-
  have "dim_col (j\<Otimes> s l m j) = dim_col (pw (j_to_list_bound s l m j) l)"
    using j_to_tensor_prod_def by auto
  moreover have "length (j_to_list_bound s l m j) = l" 
    using j_to_list_bound_length by auto
  moreover have "\<forall>x\<in>set (j_to_list_bound s l m j). dim_col x = 1" 
    using j_to_list_bound_dim_col by auto
  ultimately show "dim_col (j\<Otimes> s l m j) = 1"
    using pow_tensor_list_dim_col by auto
qed

lemma j_to_tensor_prod_decomp_left_zero:
  assumes "l\<ge>1" and "(bin_rep m j)!(s-1) = 0"
  shows "(j\<Otimes> s l m j) = zero \<Otimes> (j\<Otimes> (s+1) (l-1) m j)"
proof- 
  have "(j\<Otimes> s l m j) = pw (j_to_list_bound s l m j) l"
    using j_to_tensor_prod_def by auto
  also have "... = pw ((if (bin_rep m j)!(s-1) = 0 then zero else one) # (j_to_list_bound (s+1) (l-1) m j)) l"
    using assms by (metis j_to_list_bound.simps(2) ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
  also have "... = pw (zero # (j_to_list_bound (s+1) (l-1) m j)) l"
    using assms by auto
  also have "... = zero \<Otimes> pw (j_to_list_bound (s+1) (l-1) m j) (l-1)"
    using assms pow_tensor_list.simps by (metis One_nat_def Suc_pred less_eq_Suc_le)
  finally show "(j\<Otimes> s l m j) = zero \<Otimes> (j\<Otimes> (s+1) (l-1) m j)"
    using j_to_tensor_prod_def by auto
qed

lemma j_to_tensor_prod_decomp_left_one:
  assumes "l\<ge>1" and "(bin_rep m j)!(s-1) = 1"
  shows "(j\<Otimes> s l m j) = one \<Otimes> (j\<Otimes> (s+1) (l-1) m j)"
proof- 
  have "(j\<Otimes> s l m j) = pw (j_to_list_bound s l m j) l"
    using j_to_tensor_prod_def by auto
  also have "... = pw ((if (bin_rep m j)!(s-1) = 0 then zero else one) # (j_to_list_bound (s+1) (l-1) m j)) l"
    using assms by (metis j_to_list_bound.simps(2) ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
  also have "... = pw (one # (j_to_list_bound (s+1) (l-1) m j)) l"
    using assms by auto
  also have "... = one \<Otimes> pw (j_to_list_bound (s+1) (l-1) m j) (l-1)"
    using assms pow_tensor_list.simps by (metis One_nat_def Suc_pred less_eq_Suc_le)
  finally show "(j\<Otimes> s l m j) = one \<Otimes> (j\<Otimes> (s+1) (l-1) m j)"
    using j_to_tensor_prod_def by auto
qed


lemma j_to_tensor_prod_decomp_right:
  fixes j m t::nat
  assumes "j < 2^m" and "s+t-1 < m" 
  shows "(j\<Otimes> s (t+1) m j) = (j\<Otimes> s t m j) \<Otimes> (j\<Otimes> (s+t) 1 m j)"
proof(rule disjE)
  show "(bin_rep m j)!(s+t-1) = 0 \<or> (bin_rep m j)!(s+t-1) = 1" 
    using bin_rep_coeff assms by auto
next
  assume a0: "(bin_rep m j)!(s+t-1) = 0"
  then have "(j\<Otimes> (s+t) 1 m j) = zero" 
    using j_to_tensor_prod_def by auto
  moreover have "(j\<Otimes> s (t+1) m j) = (j\<Otimes> s t m j) \<Otimes> zero"
    using j_to_tensor_prod_decomp_right_zero a0 by auto
  ultimately show ?thesis by auto
next
  assume a0: "(bin_rep m j)!(s+t-1) = 1"
  then have "(j\<Otimes> (s+t) 1 m j) = one" 
    using j_to_tensor_prod_def by auto
  moreover have "(j\<Otimes> s (t+1) m j) = (j\<Otimes> s t m j) \<Otimes> one"
    using j_to_tensor_prod_decomp_right_one a0 by auto
  ultimately show ?thesis by auto
qed


lemma j_to_tensor_prod_decomp_half:
  fixes j m t s n::nat
  assumes "j < 2^m" and "n>s" and "n\<le>m" and "t\<ge>n-s" and "m\<ge>1"
  shows "s+t-1 \<le> m \<longrightarrow> (j\<Otimes> s t m j) = (j\<Otimes> s (n-s) m j) \<Otimes> (j\<Otimes> n (t-(n-s)) m j)"
proof(rule Nat.nat_induct_at_least[of "n-s" t])
  show "t\<ge>n-s" using assms by auto
next
  show "s+(n-s)-1 \<le> m \<longrightarrow> (j\<Otimes> s (n-s) m j) = (j\<Otimes> s (n-s) m j) \<Otimes> (j\<Otimes> n ((n-s)-(n-s)) m j)"
  proof
    assume a0: "s+(n-s)-1 \<le> m"
    then have "(j\<Otimes> n ((n-s)-(n-s)) m j) = Id 0" by simp
    then show "(j\<Otimes> s (n-s) m j) = (j\<Otimes> s (n-s) m j) \<Otimes> (j\<Otimes> n ((n-s)-(n-s)) m j)" 
      using Id_right_tensor by auto
  qed
next
  fix t 
  assume a0: "t\<ge>n-s"
     and IH: "s+t-1 \<le> m \<longrightarrow> (j\<Otimes> s t m j) = (j\<Otimes> s (n-s) m j) \<Otimes> (j\<Otimes> n (t-(n-s)) m j)"
  show "s+(Suc t)-1 \<le> m \<longrightarrow> (j\<Otimes> s (Suc t) m j) = (j\<Otimes> s (n-s) m j) \<Otimes> (j\<Otimes> n ((Suc t)-(n-s)) m j)"
  proof
    assume a1: "s+(Suc t)-1 \<le> m" 
    have "(j\<Otimes> s (t+1) m j) = (j\<Otimes> s (n-s) m j) \<Otimes> ((j\<Otimes> n (t-(n-s)) m j) \<Otimes> (j\<Otimes> (s+t) 1 m j))" 
    proof-
      have "s+t-1 < m" using assms(5) a1 by auto
      then have "(j\<Otimes> s (t+1) m j) = (j\<Otimes> s t m j) \<Otimes> (j\<Otimes> (s+t) 1 m j)" 
        using j_to_tensor_prod_decomp_right assms by blast
      then have "(j\<Otimes> s (t+1) m j) = ((j\<Otimes> s (n-s) m j) \<Otimes> (j\<Otimes> n (t-(n-s)) m j)) \<Otimes> (j\<Otimes> (s+t) 1 m j)" 
        using IH a1 by auto
      then show ?thesis 
        using tensor_mat_is_assoc by auto
    qed
    moreover have "(j\<Otimes> n (t-(n-s)+1) m j) = (j\<Otimes> n (t-(n-s)) m j) \<Otimes> (j\<Otimes> (s+t) 1 m j)"
    proof-
      have "n + (t - (n - s)) - 1 < m" using assms a1 by linarith
      then have "j\<Otimes> n (t-(n-s)+1) m j = (j\<Otimes> n (t-(n-s)) m j) \<Otimes> (j\<Otimes> (n+(t-(n-s))) 1 m j)"
        using j_to_tensor_prod_decomp_right[of j m n "(t-(n-s))"] assms a0 by auto
      moreover have "n+(t-(n-s)) = t+s" using assms a0 by linarith
      ultimately show ?thesis 
        by (metis linordered_field_class.sign_simps(2))
    qed
    ultimately have "(j\<Otimes> s (t+1) m j) = (j\<Otimes> s (n-s) m j) \<Otimes> (j\<Otimes> n (t-(n-s)+1) m j)"
      by auto
    then show "(j\<Otimes> s (Suc t) m j) = (j\<Otimes> s (n-s) m j) \<Otimes> (j\<Otimes> n ((Suc t)-(n-s)) m j)" 
      by (metis Suc_diff_le Suc_eq_plus1 a0)
  qed
qed



lemma j_to_tensor_prod_decomp_middle: 
 fixes j m t::nat
  assumes "j < 2^m" and "n>s" and "n\<le>m" and "t\<ge>n-s" and "s+t-1 \<le> m" and "m\<ge>1"
  shows "(j\<Otimes> s t m j) = (j\<Otimes> s (n-s-1) m j) \<Otimes> (j\<Otimes> (n-1) 1 m j) \<Otimes> (j\<Otimes> n (t-(n-s)) m j)"
proof-
  have "(j\<Otimes> s t m j) = (j\<Otimes> s (n-s) m j) \<Otimes> (j\<Otimes> n (t-(n-s)) m j)" 
    using assms j_to_tensor_prod_decomp_half by blast
  moreover have "(j\<Otimes> s (n-s) m j) = (j\<Otimes> s (n-s-1) m j) \<Otimes> (j\<Otimes> (n-1) 1 m j)"
  proof-
    have "s + (n-s-1) - 1 < m" using assms Suc_diff_Suc by linarith
    then have "(j\<Otimes> s (n-s-1+1) m j) = (j\<Otimes> s (n-s-1) m j) \<Otimes> (j\<Otimes> (s+(n-s-1)) 1 m j) "
      using j_to_tensor_prod_decomp_right[of j m s "n-s-1"] assms by auto
    moreover have "(s+(n-s-1)) = n-1" using assms by linarith
    moreover have "(n-s-1+1) = n-s" using assms(2) by auto
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis by auto
qed


lemma zero_neq_one_mat:
  shows "zero \<noteq> one" 
proof-
  have "zero $$ (0,0) = 1" by auto
  moreover have "one $$ (0,0) = 0" by auto
  ultimately show ?thesis  by (metis zero_neq_one)
qed

lemma j_to_tensor_bin_rep_zero: 
  fixes n m j::nat
  assumes "n\<ge>1"
  shows "(j\<Otimes> n 1 m j) = zero \<longleftrightarrow> bin_rep m j ! (n-1) = 0"
proof
  assume a0: "(j\<Otimes> n 1 m j) = zero"
  have "(j\<Otimes> n 1 m j) = (if (bin_rep m j)!(n-1) = 0 then zero else one)"
    using j_to_tensor_prod_def pow_tensor_list_one by auto 
  then have "zero = (if (bin_rep m j)!(n-1) = 0 then zero else one)"
    using a0 by auto
  then show "bin_rep m j ! (n-1) = 0" using a0 zero_neq_one_mat by auto
next
  assume a0: "bin_rep m j ! (n - 1) = 0"
  then show "(j\<Otimes> n 1 m j) = zero"
    using j_to_tensor_prod_def pow_tensor_list_one by auto 
qed


lemma j_to_tensor_bin_rep_one: 
  fixes n m j::nat
  assumes "n\<ge>1" and "j < 2^m" and "n-1 < m" 
  shows "(j\<Otimes> n 1 m j) = one \<longleftrightarrow> bin_rep m j ! (n-1) = 1"
proof
  assume a0: "(j\<Otimes> n 1 m j) = one"
  have "(j\<Otimes> n 1 m j) = (if (bin_rep m j)!(n-1) = 0 then zero else one)"
    using j_to_tensor_prod_def pow_tensor_list_one by auto 
  then have "one = (if (bin_rep m j)!(n-1) = 0 then zero else one)"
    using a0 zero_neq_one by auto
  moreover have "(bin_rep m j)!(n-1) = 0 \<or> (bin_rep m j)!(n-1) = 1" 
    using bin_rep_coeff assms by auto
  ultimately show "bin_rep m j ! (n-1) = 1" using a0 zero_neq_one_mat by auto
next
  assume a0: "bin_rep m j ! (n - 1) = 1"
  then show "(j\<Otimes> n 1 m j) = one"
    using j_to_tensor_prod_def pow_tensor_list_one by auto 
qed

lemma decomp_unit_vec_zero_left: (*This is not needed anymore -_- Might be useful for some other theory? Should be revised in that case*)
  fixes k::nat
  assumes "k\<ge>1" and "m<2^(k-1)"
  shows "|unit_vec (2^k) m\<rangle> = zero \<Otimes> |unit_vec (2^(k-1)) m\<rangle>" 
proof
  fix i j::nat
  assume a0: "i < dim_row (zero \<Otimes> |unit_vec (2^(k-1)) m\<rangle>)"
  and a1: "j < dim_col (zero \<Otimes> |unit_vec (2^(k-1)) m\<rangle>)"
  then have f0: "i < 2^k" using ket_vec_def unit_vec_def zero_def 
  proof -
    have "(2::nat) ^ k = 2 * 2 ^ (k - 1)" using assms le_Suc_ex by fastforce
    then show ?thesis
      using a0 ket_vec_def by auto
  qed
  have f1: "j = 0" using a1 ket_vec_def unit_vec_def zero_def by auto
  have f2: "dim_row ( |unit_vec (2^(k-1)) m\<rangle>) = 2^(k-1)" 
   and f3: "dim_col ( |unit_vec (2^(k-1)) m\<rangle>) = 1" using ket_vec_def unit_vec_def by auto
  have "i < (dim_row zero) * (dim_row ( |unit_vec (2^(k-1)) m\<rangle>))" 
   and "j < (dim_col zero) * (dim_col ( |unit_vec (2^(k-1)) m\<rangle>))" 
   and "(dim_col zero) > 0" and "dim_col ( |unit_vec (2^(k-1)) m\<rangle>) > 0" using zero_def f1 f2 assms a0 a1 by auto
  then have f4: "(zero \<Otimes> ( |unit_vec (2^(k-1)) m\<rangle>)) $$ (i,j) 
            = zero $$ (i div 2^(k-1), j div 1) * ( |unit_vec (2^(k-1)) m\<rangle>) $$ (i mod 2^(k-1), j mod 1)"
    using index_tensor_mat f1 f2 by simp 
  show "( |unit_vec (2^k) m\<rangle>) $$ (i,j)  = (zero \<Otimes> |unit_vec (2^(k-1)) m\<rangle>) $$ (i,j)"
  proof(rule disjE)
    show "i=m \<or> i\<noteq>m" by auto
  next
    assume a2: "i=m"
    then have "(zero \<Otimes> ( |unit_vec (2^(k-1)) m\<rangle>)) $$ (i,j) 
            = zero $$ (0, j div 1) * ( |unit_vec (2^(k-1)) m\<rangle>) $$ (i mod 2^(k-1), j mod 1)"
      using assms f4 by (metis div_less)
    then have "(zero \<Otimes> ( |unit_vec (2^(k-1)) m\<rangle>)) $$ (i,j) 
            = ( |unit_vec (2^(k-1)) m\<rangle>) $$ (i mod 2^(k-1), j mod 1)"
      using zero_def f1 by auto
    then have "(zero \<Otimes> ( |unit_vec (2^(k-1)) m\<rangle>)) $$ (i,j) 
             = ( |unit_vec (2^(k-1)) m\<rangle>) $$ (m, j mod 1)" using a2 assms by auto
    then have "(zero \<Otimes> ( |unit_vec (2^(k-1)) m\<rangle>)) $$ (i,j) = 1" using assms by simp
    moreover have "( |unit_vec (2^k) m\<rangle>) $$ (i,j)  = 1" using a2 assms ket_vec_def f0 f1 by auto
    ultimately show "( |unit_vec (2^k) m\<rangle>) $$ (i,j)  = (zero \<Otimes> |unit_vec (2^(k-1)) m\<rangle>) $$ (i,j)"
     by auto
 next
    assume a2: "i\<noteq>m"
    then have f5: "i<2^(k-1) \<longrightarrow> (zero \<Otimes> ( |unit_vec (2^(k-1)) m\<rangle>)) $$ (i,j) = 0"
      using assms a2 f4 by auto
    have "i\<ge>2^(k-1) \<longrightarrow> i div 2^(k-1) = 1" using f0 a0 ket_vec_def by auto
    then have f6: "i\<ge>2^(k-1) \<longrightarrow> (zero \<Otimes> ( |unit_vec (2^(k-1)) m\<rangle>)) $$ (i,j)  = 0"
      using assms f4 zero_def f1 by auto
    then have "(zero \<Otimes> ( |unit_vec (2^(k-1)) m\<rangle>)) $$ (i,j)  = 0" using f5 f6 by auto
    moreover have "( |unit_vec (2^k) m\<rangle>) $$ (i,j) = 0" using a2 assms ket_vec_def unit_vec_def f0 f1  
      by (smt One_nat_def assms(1) assms(2) col_index_of_mat_col dim_col_mat(1) dim_row_mat(1) index_unit_vec(3) index_vec ket_vec_col ket_vec_def less_Suc0 unit_vec_def)
    ultimately show "( |unit_vec (2^k) m\<rangle>) $$ (i,j)  = (zero \<Otimes> |unit_vec (2^(k-1)) m\<rangle>) $$ (i,j)"
      by auto
  qed
next
  have "(2::nat) ^ k = 2 * 2 ^ (k - 1)" using assms le_Suc_ex by fastforce
  then show  "dim_row |unit_vec (2 ^ k) m\<rangle> = dim_row (zero \<Otimes> |unit_vec (2 ^ (k - 1)) m\<rangle>)" 
    using ket_vec_def unit_vec_def zero_def by auto
next
  show " dim_col |unit_vec (2 ^ k) m\<rangle> = dim_col (zero \<Otimes> |unit_vec (2 ^ (k - 1)) m\<rangle>)" 
    using ket_vec_def unit_vec_def zero_def by auto
qed


lemma bin_rep_even: 
  fixes k m i::nat
  assumes "(bin_rep k m)!(k-1) = 0" and "k \<ge> 1" and "m < 2^k" 
  shows "even m" 
proof-
  have "bin_rep k m ! (k-1) = (m mod 2^(k-(k-1))) div 2^(k-1-(k-1))"
    using bin_rep_index[of k m "k-1"] assms by auto
  then have "0 = (m mod 2) div 2^0" using assms by auto
  then show "even m" by auto
qed

lemma bin_rep_div_even: 
  assumes "bin_rep m j ! k = 0" and "j < 2^m" and "m \<ge> 1" and "m-k \<ge> 1"
  shows "even (j div 2^(m-(k+1)))"
proof-
  have "(bin_rep m (j div 2^(m-k-1)))!(m-1) = 0" 
  proof-
    have "(j div 2^(m-k-1)) < 2^m" using assms by (meson div_le_dividend le_trans not_less)
    then have "(bin_rep m (j div 2^(m-k-1)))!(m-1) = ((j div 2^(m-k-1)) mod 2^(m-(m-1))) div 2^(m-1-(m-1))" 
      using assms bin_rep_index 
      by (meson diff_less le_trans linorder_not_le not_one_le_zero zero_le)
    then have "(bin_rep m (j div 2^(m-k-1)))!(m-1) = (j div 2^(m-k-1)) mod 2 div 1" using assms(3)
      by (metis cancel_comm_monoid_add_class.diff_cancel diff_diff_cancel power_0 power_one_right)
    then have "(bin_rep m (j div 2^(m-k-1)))!(m-1) = (j div 2^(m-k-1)) mod 2" by presburger
    moreover have "(j div 2^(m-k-1)) mod 2 = j mod 2^(m-k) div 2^(m-k-1)" 
      using assms(4)
      by (smt One_nat_def add.commute add.right_neutral div_add_self1 le_simps(3) mod_div_trivial 
          mod_mult2_eq mult.right_neutral mult_zero_right not_mod2_eq_Suc_0_eq_0 power_eq_0_iff power_minus_mult zero_neq_numeral)
    moreover have "0 = (j mod 2^(m-k)) div 2^(m-1-k)"  
      using assms(1) assms(2)
      by (metis bin_rep_index div_less mod_by_1 mod_if neq0_conv not_less not_less_zero pos2 power_0 zero_less_diff zero_less_power)
    ultimately show ?thesis 
      by (metis cancel_ab_semigroup_add_class.diff_right_commute)
  qed
  moreover have "j div 2^(m-k-1) < 2^m" using assms(2) by (meson div_le_dividend le_less_trans) 
  ultimately show ?thesis using bin_rep_even assms by (metis diff_diff_left)
qed


lemma decomp_unit_vec_zero_right:
  fixes k::nat
  assumes "k \<ge> 1" and "m < 2^k" and "even m" 
  shows "|unit_vec (2^k) m\<rangle> = |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero" 
proof
  fix i j
  assume a0: "i < dim_row ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero)" 
     and a1: "j < dim_col ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero)" 
  then have f0: "i < 2^k \<and> j = 0" 
    by (metis (no_types, lifting) One_nat_def assms(1) dim_col_mat(1) dim_col_tensor_mat dim_row_mat(1) dim_row_tensor_mat index_unit_vec(3) ket_vec_def less_eq_Suc_le less_one one_power2 power2_eq_square power_minus_mult)
  then have f1: "( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero) $$ (i,j) = |unit_vec (2^(k-1)) (m div 2)\<rangle> $$ (i div 2, j div 1) 
        * zero $$ (i mod 2, j mod 1)" using unit_vec_def assms ket_vec_def zero_def a0 by fastforce
  show "( |unit_vec (2^k) m\<rangle> ) $$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero) $$ (i,j)"
  proof (rule disjE)
    show "i = m \<or> i \<noteq> m" by auto
  next
    assume a2: "i = m"
    then have "( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero) $$ (i,j) = 1"
      using ket_vec_def unit_vec_def a0 f0 assms bin_rep_even by auto
    then show "( |unit_vec (2^k) m\<rangle> ) $$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero) $$ (i,j)"
      using ket_vec_def unit_vec_def f0 a2 by auto
  next
    assume a2: "i \<noteq> m"
    show "( |unit_vec (2^k) m\<rangle> ) $$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero) $$ (i,j)"
    proof(rule disjE)
      show "i div 2 = m div 2 \<or> i div 2 \<noteq> m div 2" by auto
    next
      assume "i div 2 = m div 2"
      then have "i = m + 1" using a2 assms bin_rep_even 
        by (metis add.right_neutral add_Suc_right dvd_mult_div_cancel even_zero less_one linordered_semidom_class.add_diff_inverse 
            odd_two_times_div_two_nat plus_1_eq_Suc)
      then have "i mod 2 = 1" using assms bin_rep_even 
        by (meson even_plus_one_iff mod_0_imp_dvd not_mod_2_eq_1_eq_0)
      then have "( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero) $$ (i,j) = 0" using f0 f1 by auto
      then show "( |unit_vec (2^k) m\<rangle> )$$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero) $$ (i,j)"
        using assms(2) f0 a2 by (metis index_unit_vec(1) index_unit_vec(3) ket_vec_index)
    next
      assume "i div 2 \<noteq> m div 2"
      then have "( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero) $$ (i,j) = 0" 
        using assms(1) assms(2) f0 f1 
        by (smt One_nat_def div_less ket_vec_def unit_vec_def index_unit_vec(1) index_unit_vec(3) ket_vec_index less_eq_Suc_le 
            less_mult_imp_div_less mult_eq_0_iff power_minus_mult zero_less_one_class.zero_less_one)
      then show "( |unit_vec (2^k) m\<rangle> )$$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero) $$ (i,j)"
        using assms(2) f0 a2 by (smt ket_vec_def unit_vec_def index_unit_vec(1) index_unit_vec(3) ket_vec_index)
    qed
  qed
next
  show "dim_row ( |unit_vec (2^k) m\<rangle> ) = dim_row ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero)"
    using unit_vec_def zero_def ket_vec_def assms(1)
    by (smt One_nat_def dim_row_mat(1) dim_row_tensor_mat index_unit_vec(3) less_eq_Suc_le power_minus_mult)
next
  show "dim_col ( |unit_vec (2^k) m\<rangle> ) = dim_col ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero)"
    using unit_vec_def zero_def ket_vec_def by simp
qed

lemma decomp_unit_vec_one_left:  (*This is not needed anymore -_- Might be useful for some other theory? Should be revised in that case*)
  fixes k::nat
  assumes "k\<ge>1" and "m\<ge>2^(k-1) \<and> m<2^k"
  shows " |unit_vec (2^k) m\<rangle> = one \<Otimes> |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>"
proof
  fix i j::nat
  assume a0: "i < dim_row (one \<Otimes> |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>)"
  and a1: "j < dim_col (one \<Otimes> |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>)"
  then have f0: "i < 2^k" using ket_vec_def unit_vec_def zero_def 
  proof -
   have "(2::nat) ^ k = 2 * 2 ^ (k - 1)" using assms le_Suc_ex by fastforce
    then show ?thesis
      using a0 ket_vec_def by auto
  qed
  have f1: "j = 0" using a1 ket_vec_def unit_vec_def zero_def by auto
  have f2: "dim_row ( |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>) = 2^(k-1)" 
   and f3: "dim_col ( |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>) = 1" using ket_vec_def unit_vec_def by auto
  have "i < (dim_row one) * (dim_row ( |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>))" 
   and "j < (dim_col one) * (dim_col ( |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>))" 
   and "(dim_col zero) > 0" and "dim_col ( |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>) > 0" using zero_def f1 f2 assms a0 a1 by auto
  then have f4: "(one \<Otimes> ( |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>)) $$ (i,j) 
            = one $$ (i div 2^(k-1), j div 1) * ( |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>) $$ (i mod 2^(k-1), j mod 1)"
    using index_tensor_mat f1 f2 by simp 
  show "( |unit_vec (2^k) m\<rangle>) $$ (i,j) = (one \<Otimes> |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>) $$ (i,j)"
  proof(rule disjE)
    show "i=m \<or> i\<noteq>m" by auto
  next
    assume a2: "i=m"
    have "i div 2^(k-1) = 1" using assms a0 a2 f2
      by (metis (no_types, lifting) Euclidean_Division.div_eq_0_iff One_nat_def dim_row_mat(1) dim_row_tensor_mat less_2_cases less_mult_imp_div_less not_le power_not_zero zero_neq_numeral)
    then have "(one \<Otimes> |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>) $$ (i,j) 
            = 1 * ( |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>) $$ (i mod 2^(k-1), j mod 1)"
      using f4 f1 by auto
    then have "(one \<Otimes> |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>) $$ (i,j) 
             = ( |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>) $$ (m mod 2^(k-1), 0)" using a2 assms f1 by auto
    then have "(one \<Otimes> |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>) $$ (i,j) = 1" using assms by simp
    moreover have "( |unit_vec (2^k) m\<rangle>) $$ (i,j) = 1" using a2 assms ket_vec_def f0 f1 by auto
    ultimately show "( |unit_vec (2^k) m\<rangle>) $$ (i,j) = (one \<Otimes> |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>) $$ (i,j)"
     by auto
 next
   assume a2: "i\<noteq>m"
   have "i\<ge>2^(k-1) \<longrightarrow> i div 2^(k-1) = 1" using f0 a0 ket_vec_def by auto
   then have f5: "i\<ge>2^(k-1) \<longrightarrow> (one \<Otimes> |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>) $$ (i,j) = 0"
      using assms a2 f4 f0 one_def 
      by (smt \<open>0 < dim_col |unit_vec (2 ^ (k - 1)) (m mod 2 ^ (k - 1))\<rangle>\<close> f2 index_col index_vec ket_vec_col less_2_cases 
          less_imp_le_nat less_power_add_imp_div_less linorder_not_le mod_by_Suc_0 mod_eq_self_iff_div_eq_0 mod_less_divisor 
          mult_eq_0_iff neq_imp_neq_div_or_mod ordered_cancel_comm_monoid_diff_class.add_diff_inverse pos2 power_one_right 
          unit_vec_def zero_less_power)
   have "i<2^(k-1) \<longrightarrow> i div 2^(k-1) = 0" using f0 a0 ket_vec_def by auto
   then have f6: "i<2^(k-1) \<longrightarrow> (one \<Otimes> |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>) $$ (i,j) = 0"
     using assms a2 f4 f0 f1 one_def by auto
   moreover have "( |unit_vec (2^k) m\<rangle>) $$ (i,j) = 0" using a2 assms ket_vec_def unit_vec_def f0 f1
      by (smt One_nat_def assms(1) assms(2) col_index_of_mat_col dim_col_mat(1) dim_row_mat(1) index_unit_vec(3) index_vec ket_vec_col ket_vec_def less_Suc0 unit_vec_def)
    ultimately show "( |unit_vec (2^k) m\<rangle>) $$ (i,j)  = (one \<Otimes> |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>) $$ (i,j)"
      using f5 f6 by auto
  qed
next
  have "(2::nat) ^ k = 2 * 2 ^ (k - 1)" using assms le_Suc_ex by fastforce
  then show "dim_row |unit_vec (2 ^ k) m\<rangle> = dim_row (one \<Otimes> |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>)" 
    using ket_vec_def unit_vec_def one_def by auto
next
  show " dim_col |unit_vec (2 ^ k) m\<rangle> = dim_col (one \<Otimes> |unit_vec (2^(k-1)) (m mod 2^(k-1))\<rangle>)" 
    using ket_vec_def unit_vec_def one_def by auto
qed


lemma bin_rep_odd: 
  fixes k m i::nat
  assumes "(bin_rep k m)!(k-1) = 1" and "k \<ge> 1" and "m < 2^k" 
  shows "odd m" 
proof-
  have "bin_rep k m ! (k-1) = (m mod 2^(k-(k-1))) div 2^(k-1-(k-1))"
    using bin_rep_index[of k m "k-1"] assms by auto
  then have "1 = (m mod 2) div 2^0" using assms by auto
  then show "odd m" by auto
qed


lemma bin_rep_div_odd: 
  assumes "bin_rep m j ! k = 1" and "j < 2^m" and "m\<ge>1" and "m-k\<ge>1"
  shows "odd (j div 2^(m-(k+1)))"
proof-
  have "(bin_rep m (j div 2^(m-k-1)))!(m-1) = 1" 
  proof-
    have "(j div 2^(m-k-1)) < 2^m" using assms by (meson div_le_dividend le_trans not_less)
    then have "(bin_rep m (j div 2^(m-k-1)))!(m-1) = ((j div 2^(m-k-1)) mod 2^(m-(m-1))) div 2^(m-1-(m-1))" using assms bin_rep_index 
      by (meson diff_less le_trans linorder_not_le not_one_le_zero zero_le)
    then have "(bin_rep m (j div 2^(m-k-1)))!(m-1) = (j div 2^(m-k-1)) mod 2 div 1" using assms(3)
      by (metis cancel_comm_monoid_add_class.diff_cancel diff_diff_cancel power_0 power_one_right)
    then have "(bin_rep m (j div 2^(m-k-1)))!(m-1) = (j div 2^(m-k-1)) mod 2" by presburger
    moreover have "(j div 2^(m-k-1)) mod 2 = j mod 2^(m-k) div 2^(m-k-1)" using assms(4) 
      by (smt One_nat_def add.commute add.right_neutral div_add_self1 le_simps(3) mod_div_trivial mod_mult2_eq mult.right_neutral 
          mult_zero_right not_mod2_eq_Suc_0_eq_0 power_eq_0_iff power_minus_mult zero_neq_numeral)
    moreover have "1 = (j mod 2^(m-k)) div 2^(m-1-k)" using assms 
      by (metis One_nat_def bin_rep_index div_by_0 div_le_dividend le_simps(3) zero_less_diff)                                                                                               
    ultimately show ?thesis 
      by (metis cancel_ab_semigroup_add_class.diff_right_commute)
  qed
  moreover have "m \<ge> 1" using assms(3) by blast
  moreover have "j div 2^(m-k-1) < 2^m" using assms(2) by (meson div_le_dividend le_less_trans) 
  ultimately show ?thesis using bin_rep_odd by (metis diff_diff_left)
qed



lemma decomp_unit_vec_one_right:
  fixes k::nat
  assumes "k \<ge> 1" and "m < 2^k" and "(bin_rep k m)!(k-1) = 1"
  shows "|unit_vec (2^k) m\<rangle> = |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> one"
proof
  fix i j
  assume a0: "i < dim_row ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> one)" 
     and a1: "j < dim_col ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> one)" 
  then have f0: "i < 2^k \<and> j = 0" 
    using assms(1)
    by (metis (no_types, lifting) One_nat_def dim_col_mat(1) dim_col_tensor_mat dim_row_mat(1) dim_row_tensor_mat index_unit_vec(3) 
        ket_vec_def less_eq_Suc_le less_one one_power2 power2_eq_square power_minus_mult)
  then have f1: "( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> one) $$ (i,j) = |unit_vec (2^(k-1)) (m div 2)\<rangle> $$ (i div 2, j div 1) 
        * one $$ (i mod 2, j mod 1)" using unit_vec_def assms ket_vec_def a0 by fastforce
  show "( |unit_vec (2^k) m\<rangle> ) $$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> one) $$ (i,j)"
  proof (rule disjE)
    show "i=m \<or> i\<noteq>m" by auto
  next
    assume a2: "i = m" 
    then have "i div 2 = m div 2" using bin_rep_odd assms by blast
    then have "|unit_vec (2^(k-1)) (m div 2)\<rangle> $$ (i div 2, j div 1) = 1" using a0 a1 unit_vec_def ket_vec_def by auto
    moreover have "i mod 2 = 1" using bin_rep_odd assms odd_iff_mod_2_eq_one a2 by blast
    ultimately have "( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> one) $$ (i,j) = 1"
      using ket_vec_def unit_vec_def a0 f0 assms bin_rep_odd a2 by auto 
    then show "( |unit_vec (2^k) m\<rangle> ) $$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> one) $$ (i,j)"
      using ket_vec_def unit_vec_def f0 a2 by auto
  next
    assume a2: "i \<noteq> m"
    show "( |unit_vec (2^k) m\<rangle> ) $$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> one) $$ (i,j)"
    proof(rule disjE)
      show "i div 2 = m div 2 \<or> i div 2 \<noteq> m div 2" by auto
    next
      assume "i div 2 = m div 2"
      then have "i=m-1" using a2 assms bin_rep_odd 
        by (metis dvd_mult_div_cancel even_zero less_one linordered_semidom_class.add_diff_inverse odd_two_times_div_two_nat plus_1_eq_Suc)
      then have "i mod 2 = 0" using assms bin_rep_odd by (simp add: \<open>m < 2 ^ k\<close>)
      then have "( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> one) $$ (i,j) = 0" using f1 zero_def f0 by auto
      then show "( |unit_vec (2^k) m\<rangle> )$$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> one) $$ (i,j)"
        using ket_vec_def unit_vec_def f0 a2 by (smt assms(2) index_unit_vec(1) index_unit_vec(3) ket_vec_index)
    next
      assume "i div 2 \<noteq> m div 2"
      then have "( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> one) $$ (i,j) = 0" 
        using f1 ket_vec_def unit_vec_def assms 
        by (smt diff_diff_cancel diff_le_self div_by_1 f0 index_unit_vec(1) index_unit_vec(3) ket_vec_index less_power_add_imp_div_less mult_eq_0_iff ordered_cancel_comm_monoid_diff_class.add_diff_inverse power_one_right)
      then show "( |unit_vec (2^k) m\<rangle> )$$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> one) $$ (i,j)"
        using ket_vec_def unit_vec_def f0 a2 by (smt assms(2) index_unit_vec(1) index_unit_vec(3) ket_vec_index)
    qed
  qed
next
  show "dim_row ( |unit_vec (2^k) m\<rangle> ) = dim_row ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> one)"
    using unit_vec_def ket_vec_def 
    by (smt One_nat_def assms(1) dim_row_mat(1) dim_row_tensor_mat index_unit_vec(3) less_eq_Suc_le power_minus_mult)
next
  show "dim_col ( |unit_vec (2^k) m\<rangle> ) = dim_col ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> one)"
    using unit_vec_def ket_vec_def by simp
qed

lemma div_of_div:
  fixes j n::nat
  assumes "n\<ge>1"
  shows "j div 2^(n-1) div 2 = j div 2^n" 
  by (metis One_nat_def Suc_1 assms diff_Suc_1 diff_self_eq_0 div_mult2_eq eq_iff less_imp_add_positive mult.commute not_less plus_1_eq_Suc power.simps(2))


lemma aux_j_as_unit: (*look up naming convention*)
  fixes k j m::nat
  assumes "j < 2^m" and "k\<ge>1"
  shows "k \<le> m \<longrightarrow> (j\<Otimes> 1 k m j) = |unit_vec (2^k) (j div 2^(m-k))\<rangle>"
proof(rule Nat.nat_induct_at_least[of 1 k])
  show "k \<ge> 1" using assms by auto
next
  show "1 \<le> m \<longrightarrow> (j\<Otimes> 1 1 m j) = |unit_vec (2^1) (j div 2^(m-1))\<rangle>"
  proof
    assume a0: "1 \<le> m"
    show "(j\<Otimes> 1 1 m j) = |unit_vec (2^1) (j div 2^(m-1))\<rangle>" 
    proof(rule disjE)
      show "(bin_rep m j)!0 = 0 \<or> (bin_rep m j)!0 = 1" 
        using a0 assms(1) bin_rep_coeff less_le_trans less_numeral_extra(1) by blast
    next
      assume a1: "(bin_rep m j)!0 = 0"
      then have "j div 2^(m-1) = 0" 
        using a0 assms(1)
        by (metis One_nat_def bin_rep_index diff_diff_left diff_zero div_by_0 div_le_dividend le_simps(3) mod_if plus_1_eq_Suc) 
      then have " |unit_vec (2^1) (j div 2^(m-1))\<rangle> = zero" using ket_vec_def by auto
      moreover have "(j\<Otimes> 1 1 m j) = zero" using j_to_tensor_prod_def a1 by auto
      ultimately show "(j\<Otimes> 1 1 m j) = |unit_vec (2^1) (j div 2^(m-1))\<rangle>" by auto
    next
      assume a1: "(bin_rep m j)!0 = 1"
      then have "j div 2^(m-1) = 1" 
        using a0 assms(1)
        by (metis One_nat_def bin_rep_index diff_diff_left diff_zero div_by_0 div_le_dividend le_simps(3) mod_if plus_1_eq_Suc) 
      then have " |unit_vec (2^1) (j div 2^(m-1))\<rangle> = one" using ket_vec_def by auto
      moreover have "(j\<Otimes> 1 1 m j) = one" using j_to_tensor_prod_def a1 by auto
      ultimately show "(j\<Otimes> 1 1 m j) = |unit_vec (2^1) (j div 2^(m-1))\<rangle>" by auto
    qed
  qed
next
  fix k 
  assume IH: "k \<le> m \<longrightarrow> (j\<Otimes> 1 k m j) = |unit_vec (2^k) (j div 2^(m-k))\<rangle>"
    and a0: "k\<ge>1"
  show "(Suc k) \<le> m \<longrightarrow> (j\<Otimes> 1 (Suc k) m j) = |unit_vec (2^(Suc k)) (j div 2^(m-(Suc k)))\<rangle>"
  proof
    assume a1: "(Suc k) \<le> m"
    show "(j\<Otimes> 1 (Suc k) m j) = |unit_vec (2^(Suc k)) (j div 2^(m-(Suc k)))\<rangle>"
    proof (rule disjE)
      show "(bin_rep m j)!k = 0 \<or> (bin_rep m j)!k = 1" 
        using bin_rep_coeff a1 assms(1) less_eq_Suc_le by blast
    next 
      assume a2: "(bin_rep m j)!k = 0"
      then have "(j\<Otimes> 1 (Suc k) m j) = (j\<Otimes> 1 k m j) \<Otimes> zero" 
        using j_to_tensor_prod_decomp_left_zero[of "k+1" m j 1]   
        by (metis Suc_eq_plus1 add_diff_cancel_left' j_to_tensor_prod_decomp_right_zero)
      then have "(j\<Otimes> 1 (Suc k) m j) = |unit_vec (2^k) (j div 2^(m-k))\<rangle> \<Otimes> zero" 
        using IH a1 Suc_leD by presburger
      then have "(j\<Otimes> 1 (Suc k) m j) = |unit_vec (2^k) (j div 2^(m-(Suc k)) div 2)\<rangle> \<Otimes> zero" 
        using div_of_div[of "m-k" "j"] a1 by auto
      moreover have "even (j div 2^(m-(Suc k)))" using a1 assms bin_rep_div_even 
        by (smt One_nat_def Suc_eq_plus1 Suc_leD Suc_le_eq a0 a2 le_trans zero_less_diff) 
      ultimately show "(j\<Otimes> 1 (Suc k) m j) = |unit_vec (2^(Suc k)) (j div 2^(m-(Suc k)))\<rangle> " 
        using decomp_unit_vec_zero_right[of "(Suc k)" "(j div 2^(m-(Suc k)))"] a0 a1 
        by (metis (no_types, lifting) add_diff_cancel_left' assms(1) le_SucI less_power_add_imp_div_less ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
    next
      assume a2: "(bin_rep m j)!k = 1"
      then have "(j\<Otimes> 1 (Suc k) m j) = (j\<Otimes> 1 k m j) \<Otimes> one" 
        using j_to_tensor_prod_decomp_left_one[of "k+1" m j 1]   
        by (metis Suc_eq_plus1 add_diff_cancel_left' j_to_tensor_prod_decomp_right_one)
      then have "(j\<Otimes> 1 (Suc k) m j) = |unit_vec (2^k) (j div 2^(m-k))\<rangle> \<Otimes> one" 
        using IH a1 Suc_leD by presburger
      then have "(j\<Otimes> 1 (Suc k) m j) = |unit_vec (2^k) (j div 2^(m-(Suc k)) div 2)\<rangle> \<Otimes> one" 
        using div_of_div[of "m-k" "j"] a1 by auto
      moreover have "odd (j div 2^(m-(Suc k)))" using a1 assms bin_rep_div_odd 
        by (smt Suc_eq_plus1 Suc_leD a0 a2 add_le_imp_le_diff le_trans plus_1_eq_Suc)
      show "(j\<Otimes> 1 (Suc k) m j) = |unit_vec (2^(Suc k)) (j div 2^(m-(Suc k)))\<rangle> " 
        by (smt One_nat_def \<open>odd (j div 2 ^ (m - Suc k))\<close> a0 a1 add_diff_cancel_left' add_diff_cancel_right' assms(1) bin_rep_even bin_rep_index calculation cancel_ab_semigroup_add_class.diff_right_commute decomp_unit_vec_one_right div_by_1 le_SucI lessI less_power_add_imp_div_less linorder_not_less not_less_zero not_mod2_eq_Suc_0_eq_0 ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc power.simps(1) power_one_right)
    qed
  qed
qed

lemma j_as_unit:
  fixes k j m::nat
  assumes "j < 2^m" and "m\<ge>1"
  shows "(j\<Otimes> 1 m m j) = |unit_vec (2^m) j\<rangle>" 
  using aux_j_as_unit assms by auto



(*------------------------------------------------------------------------------------------------*)
(*-------------------------------Controlled phase gate CR ----------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

definition binary_fraction::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" ("bf _ _") where
"binary_fraction l k m j \<equiv> (\<Sum>i\<in>{l..k}. ((bin_rep m j)!i) /2^(i-l+1) )"

(*k is not the index of the control qubit but of the distance between the current and the control qubit
e.g. if the current qubit is the first qubit CR\<^sub>2 should be applied to the first and second qubit, if 
the current qubit is n-1 CR\<^sub>2 should be applied to the n-1th qubit and the nth qubit. *)
definition controlled_phase_shift:: " nat \<Rightarrow> complex Matrix.mat" ("CR _") where
"CR k \<equiv> Matrix.mat 4 4 (\<lambda>(i,j). if i = j then (if i = 3 then (exp (2*pi*\<i>*1/2^k)) else 1) else 0)"

(*Find appropriate name*)
(*qr 1 n n j_dec is 1\sqrt(2)*(|0\<rangle> + e\<^sup>2\<^sup>\<pi>\<^sup>i\<^sup>0\<^sup>.\<^sup>j\<^sup>1\<^sup>j\<^sup>2\<^sup>.\<^sup>.\<^sup>.\<^sup>j\<^sup>n|1\<rangle>) 
  qr n n n j_dec is 1\sqrt(2)*(|0\<rangle> + e\<^sup>2\<^sup>\<pi>\<^sup>i\<^sup>0\<^sup>.\<^sup>j\<^sup>n|1\<rangle>) *)
definition qr::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where 
"qr s t m jd \<equiv> (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then (1::complex)/sqrt(2) 
              else (exp (complex_of_real (2*pi)*\<i>*(bf (s-1) (t-1) m jd)))*1/sqrt(2)))"


lemma transpose_of_controlled_phase_shift:
  shows "(CR k)\<^sup>t = (CR k)"
proof
  fix i j::nat
  assume a0: "i < dim_row (CR k)" and a1: "j < dim_col (CR k)"
  then show  "(CR k)\<^sup>t $$ (i,j) = (CR k) $$ (i,j)" 
    using controlled_phase_shift_def by (simp add: hermite_cnj_def)
next
  show "dim_row (CR k)\<^sup>t = dim_row (CR k)" using controlled_phase_shift_def by simp
next
  show "dim_col (CR k)\<^sup>t = dim_col (CR k)" using controlled_phase_shift_def by simp
qed

lemma adjoint_of_controlled_phase_shift: 
  fixes k
  defines "CR_adjoint \<equiv> Matrix.mat 4 4 (\<lambda>(i,j). if i = j then (if i = 3 then (exp (2*pi*-\<i>*1/2^k)) else 1) else 0)"
  shows "(CR k)\<^sup>\<dagger> = CR_adjoint"
proof
  fix i j:: nat
  assume "i < dim_row CR_adjoint" and "j < dim_col CR_adjoint"
  then have "i \<in> {0,1,2,3}" and "j \<in> {0,1,2,3}" using controlled_phase_shift_def CR_adjoint_def by auto
  moreover have "cnj (exp (2 * complex_of_real pi * \<i> / 2 ^ k)) = exp (2 * complex_of_real pi * -\<i> / 2 ^ k)"
  proof
    show "Re (cnj (exp (2 * complex_of_real pi * \<i> / 2 ^ k))) = Re (exp (2 * complex_of_real pi * -\<i> / 2 ^ k))"
    proof-
      have "Re (cnj (exp (2 * complex_of_real pi * \<i> / 2 ^ k))) = Re (exp (2 * complex_of_real pi * \<i> / 2 ^ k))"
        by auto
      then have "Re (exp (2 * complex_of_real pi * \<i> / 2 ^ k)) = cos (2*pi*1/2^k)" 
        by (smt cis.simps(1) cis_conv_exp mult.commute mult_2 of_real_add of_real_divide of_real_hom.hom_one of_real_power one_add_one times_divide_eq_left)
      moreover have "Re (exp (2 * complex_of_real pi * -\<i> / 2 ^ k)) = cos (2*pi*1/2^k)" 
        using cis.simps(1) cis_conv_exp mult.commute mult_2 of_real_add of_real_divide of_real_hom.hom_one of_real_power one_add_one times_divide_eq_left
      proof- (*Replace this automated proof*)
        have "\<forall>x0. - (x0::real) = - 1 * x0" by auto
        moreover have f2: "\<i> * complex_of_real (- 1 * (2 * pi / 2 ^ k)) = 2 * complex_of_real pi / 2 ^ k * - \<i>"
          by (simp add: mult.commute)
        moreover have "2 * pi * 1 = 2 * pi"
          by auto
        ultimately show ?thesis
           by (metis (no_types) cis.simps(1) cis_conv_exp cos_minus times_divide_eq_left)
      qed
      ultimately show ?thesis by auto
    qed
  next
    show "Im (cnj (exp (2 * complex_of_real pi * \<i> / 2 ^ k))) = Im (exp (2 * complex_of_real pi * -\<i> / 2 ^ k))"
    proof-
      have "Im (cnj (exp (2 * complex_of_real pi * \<i> / 2 ^ k))) = -Im (exp (2 * complex_of_real pi * \<i> / 2 ^ k))" 
        using cnj_def by auto
      then have "Im (cnj (exp (2 * complex_of_real pi * \<i> / 2 ^ k))) = -sin(2*pi*1/2^k)" 
      proof -
        have "Im (cnj (exp (complex_of_real 2 * complex_of_real pi * \<i> / complex_of_real 2 ^ k))) = - Im (exp (\<i> * complex_of_real (2 * pi / 2 ^ k)))"
          by (simp add: mult.commute)
        then show ?thesis
          by (metis cis.simps(2) cis_conv_exp mult.right_neutral of_real_numeral)
      qed
      moreover have "Im (exp (2 * complex_of_real pi * -\<i> / 2 ^ k)) = - sin(2*pi*1/2^k)" 
        using cis.simps(1) cis_conv_exp mult.commute mult_2 of_real_add of_real_divide of_real_hom.hom_one of_real_power one_add_one 
              times_divide_eq_left Im_exp by auto
      ultimately show ?thesis by auto
    qed
  qed
  ultimately show "(CR k)\<^sup>\<dagger> $$ (i, j) = CR_adjoint $$ (i, j)"
    apply (auto simp add: hermite_cnj_def)
    apply (auto simp add: controlled_phase_shift_def CR_adjoint_def).
next
  show "dim_row (CR k)\<^sup>\<dagger> = dim_row CR_adjoint" using controlled_phase_shift_def CR_adjoint_def by simp
next
  show "dim_col (CR k)\<^sup>\<dagger> = dim_col CR_adjoint" using controlled_phase_shift_def CR_adjoint_def by simp
qed


lemma controlled_phase_shift_is_gate:
  shows "gate 2 (CR k)"
proof
  show "dim_row (CR k) = 2\<^sup>2" using controlled_phase_shift_def by auto
next
  show "square_mat (CR k)" by (simp add: controlled_phase_shift_def)
next
  show "unitary (CR k)"
  proof-
    have "(CR k)\<^sup>\<dagger> * (CR k) = 1\<^sub>m (dim_col (CR k))"
    proof
      show "dim_row ((CR k)\<^sup>\<dagger> * (CR k)) = dim_row (1\<^sub>m (dim_col (CR k)))" by simp
    next
      show "dim_col ((CR k)\<^sup>\<dagger> * (CR k)) = dim_col (1\<^sub>m (dim_col (CR k)))" by simp
    next
      fix i j:: nat
      assume "i < dim_row (1\<^sub>m (dim_col (CR k)))" and "j < dim_col (1\<^sub>m (dim_col (CR k)))"
      then have "i \<in> {0,1,2,3}" and "j \<in> {0,1,2,3}" using controlled_phase_shift_def by auto
      moreover have "(CR k)\<^sup>\<dagger> = Matrix.mat 4 4 (\<lambda>(i,j). if i = j then (if i = 3 then (exp (2*pi*-\<i>*1/2^k)) else 1) else 0)"
        using adjoint_of_controlled_phase_shift by auto     
      moreover have "exp (- (2 * complex_of_real pi * \<i> / 2 ^ k)) * exp (2 * complex_of_real pi * \<i> / 2 ^ k) = 1" 
        by (simp add: mult_exp_exp)
      ultimately show "((CR k)\<^sup>\<dagger> * (CR k)) $$ (i,j) = 1\<^sub>m (dim_col (CR k)) $$ (i, j)"
        apply (auto simp add: one_mat_def times_mat_def)
         apply (auto simp: scalar_prod_def controlled_phase_shift_def).
    qed
    then show ?thesis 
      by (metis cpx_mat_cnj_cnj cpx_mat_cnj_id cpx_mat_cnj_prod hermite_cnj_dim_col index_transpose_mat(2) transpose_cnj transpose_of_controlled_phase_shift unitary_def)
  qed
qed



lemma exp_mult: 
  fixes r jd m s::nat
  assumes  "r-1 < m" and "s\<le>r-1" and "s\<ge>1"
  shows "(exp (complex_of_real (2*pi)*\<i>*(bf (s-1) (r-1-1) m jd))) * (exp (2*pi*\<i>*((bin_rep m jd)!(r-1))/2^(r-s+1)))
        = (exp (complex_of_real (2*pi)*\<i>*(bf (s-1) (r-1) m jd)))" 
proof-
  have "(exp (2*pi*\<i>*(bf (s-1) (r-1-1) m jd))) * (exp (2*pi*\<i>*((bin_rep m jd)!(r-1))/2^(r-s+1)))
      = exp (2*pi*\<i>*(bf (s-1) (r-1-1) m jd) + 2*pi*\<i>*((bin_rep m jd)!(r-1))/2^(r-s+1))" 
    by (simp add: exp_add)
  moreover have "2*pi*\<i>*(bf (s-1) (r-1-1) m jd) + 2*pi*\<i>*((bin_rep m jd)!(r-1))/2^(r-s+1)
      = 2*pi*\<i>*((bf (s-1) (r-1-1) m jd)+((bin_rep m jd)!(r-1))/2^(r-s+1))" 
    using comm_semiring_class.distrib[of "(bf (s-1) (r-1-1) m jd)" "((bin_rep m jd)!(r-1))/2^(r-s+1)" "(2*pi*\<i>)::complex"] 
    by (simp add: mult.commute)
  moreover have "2*pi*\<i>*((bf (s-1) (r-1-1) m jd)+((bin_rep m jd)!(r-1))/2^(r-s+1)) = 2*pi*\<i>*(bf (s-1) (r-1) m jd)"
  proof-
    have "s-1 < (r-1)+1" using assms by auto
    moreover have "finite {(s-1)..(r-1-1)}" and "finite {r-1}" and "{(s-1)..(r-1-1)}\<inter>{r-1} = {}" 
         and "{(s-1)..(r-1-1)} \<union> {r-1} = {(s-1)..(r-1)}" using assms by auto
    ultimately have "(\<Sum>i\<in>{(s-1)..(r-1-1)}. ((bin_rep m jd)!i) /2^(i-(s-1)+1)) 
                   + ((bin_rep m jd)!(r-1))/2^((r-1)-(s-1)+1)
                  = (\<Sum>i\<in>{(s-1)..(r-1)}. ((bin_rep m jd)!i) /2^(i-(s-1)+1))" 
      using sum_Un 
      by (smt assms(2) assms(3) atLeastatMost_empty atLeastatMost_empty_iff diff_le_self le_trans ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc sum.cl_ivl_Suc)
    moreover have "((bin_rep m jd)!(r-1))/2^(r-s+1) = ((bin_rep m jd)!(r-1))/2^((r-1)-(s-1)+1)" 
      using assms(3) by auto
    ultimately have "(\<Sum>i\<in>{(s-1)..(r-1-1)}. ((bin_rep m jd)!i) /2^(i-(s-1)+1)) 
                   + ((bin_rep m jd)!(r-1))/2^(r-s+1)
                   = (\<Sum>i\<in>{(s-1)..(r-1)}. ((bin_rep m jd)!i) /2^(i-(s-1)+1))"  
      by auto
    moreover have "(bf (s-1) (r-1-1) m jd)+((bin_rep m jd)!(r-1))/2^(r-s+1) 
        = (\<Sum>i\<in>{(s-1)..(r-1-1)}. ((bin_rep m jd)!i) /2^(i-(s-1)+1)) + ((bin_rep m jd)!(r-1))/2^(r-s+1)"
      using binary_fraction_def by auto
    ultimately have "(bf (s-1) (r-1-1) m jd)+((bin_rep m jd)!(r-1))/2^(r-s+1) 
                   = (\<Sum>i\<in>{(s-1)..(r-1)}. ((bin_rep m jd)!i) /2^(i-(s-1)+1))"  
      by presburger
    moreover have "(\<Sum>i\<in>{(s-1)..(r-1)}. ((bin_rep m jd)!i) /2^(i-(s-1)+1)) = bf (s-1) (r-1) m jd" using binary_fraction_def by auto
    ultimately show ?thesis 
      by presburger
  qed
  ultimately show "(exp (complex_of_real (2*pi)*\<i>*(bf (s-1) (r-1-1) m jd))) * (exp (2*pi*\<i>*((bin_rep m jd)!(r-1))/2^(r-s+1)))
        = (exp (complex_of_real (2*pi)*\<i>*(bf (s-1) (r-1) m jd)))"  by auto
qed


(*I did this proof ad hoc there is certainly a much nicer one*)
(*E.g. for 1\sqrt(2)*(|0\<rangle> + e\<^sup>2\<^sup>\<pi>\<^sup>i\<^sup>0\<^sup>.\<^sup>j\<^sup>1\<^sup>j\<^sup>2|1\<rangle> one has s=1 and r=2. Then, CR (2-1+2) = CR 3 is applied and 
1\sqrt(2)*(|0\<rangle> + e\<^sup>2\<^sup>\<pi>\<^sup>i\<^sup>0\<^sup>.\<^sup>j\<^sup>1\<^sup>j\<^sup>2\<^sup>j\<^sup>3|1\<rangle> is obtained.*)
lemma app_controlled_phase_shift_zero:
  fixes s r m jd::nat
  assumes "r-1 < m" and "s\<le>r-1" and "s\<ge>1" and "((bin_rep m jd)!(r-1)) = 0" 
  shows "(CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> zero) = (qr s r m jd) \<Otimes> zero"
proof
  fix i j::nat
  assume "i < Matrix.dim_row ((qr s r m jd) \<Otimes> zero)" and "j < Matrix.dim_col ((qr s r m jd) \<Otimes> zero)" 
  then have f0: "i<4 \<and> j=0" using ket_vec_def qr_def  by auto
  then have "((CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> zero)) $$ (i,j) 
           = (\<Sum>k\<in>{0,1,2,3}. ((CR (r-s+1)) $$ (i,k)) * (((qr s (r-1) m jd) \<Otimes> zero) $$ (k,j)))" 
    using f0 ket_vec_def qr_def set_4 atLeast0LessThan controlled_phase_shift_def by auto
  then have f1: "((CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> zero)) $$ (i,j) 
           = ((CR (r-s+1)) $$ (i,0)) * (1::complex)/sqrt(2)
           + ((CR (r-s+1)) $$ (i,2)) * exp (complex_of_real (2*pi) *\<i>*(bf (s-1) (r-1-1) m jd))*1/sqrt(2)" 
    using f0 ket_vec_def qr_def by auto
  moreover have "i=0 \<longrightarrow> ((CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> zero)) $$ (i,j) = 1/sqrt(2)"
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=0 \<longrightarrow> ((qr s r m jd) \<Otimes> zero) $$ (i,j) = 1/sqrt(2)" 
    using qr_def ket_vec_def f0 by auto
  moreover have "i=1 \<longrightarrow> ((CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> zero)) $$ (i,j) = 0"
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=1 \<longrightarrow> ((qr s r m jd) \<Otimes> zero) $$ (i,j) = 0" 
    using qr_def ket_vec_def f0 by auto
  moreover have "i=2 \<longrightarrow> ((CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> zero)) $$ (i,j) 
           = (exp (complex_of_real (2*pi)*\<i>*(bf (s-1) (r-1) m jd))) *1/sqrt(2)" 
  proof-
    have "i=2 \<longrightarrow> ((CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> zero)) $$ (i,j) 
           = (exp (complex_of_real (2*pi)*\<i>*(bf (s-1) (r-1-1) m jd))) * 1 * 1/sqrt(2)" 
      using controlled_phase_shift_def f1 by auto
    moreover have "(exp (2*pi*\<i>*((bin_rep m jd)!(r-1))/2^(r-s+1))) = 1" 
      using assms by auto
    moreover have "(exp (complex_of_real (2*pi)*\<i>*(bf (s-1) (r-1-1) m jd))) * (exp (2*pi*\<i>*((bin_rep m jd)!(r-1))/2^(r-s+1)))
        = (exp (complex_of_real (2*pi)*\<i>*(bf (s-1) (r-1) m jd)))" using exp_mult assms by blast
    ultimately show ?thesis by auto
  qed
  moreover have "i=2 \<longrightarrow> ((qr s r m jd) \<Otimes> zero) $$ (i,j) = exp (complex_of_real (2*pi)*\<i>*(bf (s-1) (r-1) m jd))*1/sqrt(2)" 
    using qr_def ket_vec_def f0 by auto
  moreover have "i=3 \<longrightarrow> ((CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> zero)) $$ (i,j) = 0"
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=3 \<longrightarrow> ((qr s r m jd) \<Otimes> zero) $$ (i,j) = 0" 
    using qr_def ket_vec_def f0 by auto
  moreover have "i\<in>{0,1,2,3}" using f0 by auto
  ultimately show "((CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> zero)) $$ (i,j) = ((qr s r m jd) \<Otimes> zero) $$ (i,j)" 
    using f0 ket_vec_def qr_def by (smt set_four)
next
  show "dim_row ((CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> zero)) = dim_row ((qr s r m jd) \<Otimes> zero)" 
    by (simp add: controlled_phase_shift_def ket_vec_def qr_def)
next
  show "dim_col ((CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> zero)) = dim_col ((qr s r m jd) \<Otimes> zero)"
    using ket_vec_def controlled_phase_shift_def qr_def by auto
qed



lemma app_controlled_phase_shift_one:
  fixes s r m jd::nat
  assumes "r-1 < m" and "s\<le>r-1" and "s\<ge>1" and "((bin_rep m jd)!(r-1)) = 1"
  shows "(CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> one) = (qr s r m jd) \<Otimes> one"
proof
  fix i j::nat
  assume "i < Matrix.dim_row ((qr s r m jd) \<Otimes> one)" and "j < Matrix.dim_col ((qr s r m jd) \<Otimes> one)" 
  then have f0: "i<4 \<and> j=0" using ket_vec_def qr_def  by auto
  then have "((CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> one)) $$ (i,j) 
           = (\<Sum>k\<in>{0,1,2,3}. ((CR (r-s+1)) $$ (i,k)) * (((qr s (r-1) m jd) \<Otimes> one) $$ (k,j)))" 
    using f0 ket_vec_def qr_def set_4 atLeast0LessThan controlled_phase_shift_def by auto
  then have f1: "((CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> one)) $$ (i,j) 
           = ((CR (r-s+1)) $$ (i,1)) * (1::complex)/sqrt(2)
           + ((CR (r-s+1)) $$ (i,3)) * exp (complex_of_real (2*pi) *\<i>*(bf (s-1) (r-1-1) m jd))*1/sqrt(2)" 
    using f0 ket_vec_def qr_def by auto
  moreover have "i=0 \<longrightarrow> ((CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> one)) $$ (i,j) =0"
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=0 \<longrightarrow> ((qr s r m jd) \<Otimes> one) $$ (i,j) = 0" 
    using qr_def ket_vec_def f0 by auto
  moreover have "i=1 \<longrightarrow> ((CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> one)) $$ (i,j) = 1/sqrt(2)"
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=1 \<longrightarrow> ((qr s r m jd) \<Otimes> one) $$ (i,j) = 1/sqrt(2)"
    using qr_def ket_vec_def f0 by auto
  moreover have "i=2 \<longrightarrow> ((CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> one)) $$ (i,j) = 0" 
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=2 \<longrightarrow> ((qr s r m jd) \<Otimes> one) $$ (i,j) = 0" 
    using qr_def ket_vec_def f0 by auto
  moreover have "i=3 \<longrightarrow> ((CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> one)) $$ (i,j) = (exp (complex_of_real (2*pi)*\<i>*(bf (s-1) (r-1) m jd))) * 1/sqrt(2)" 
  proof-
   have "i=3 \<longrightarrow> ((CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> one)) $$ (i,j) 
           = (exp (complex_of_real (2*pi)*\<i>*(bf (s-1) (r-1-1) m jd))) * (exp (complex_of_real (2*pi)*\<i>*1/2^(r-s+1))) * 1/sqrt(2)" 
     using controlled_phase_shift_def f1 by auto
   moreover have "exp (complex_of_real (2*pi)*\<i>*1/2^(r-s+1)*(bin_rep m jd)!(r-1)) 
                 = exp (complex_of_real (2*pi)*\<i>*1/2^(r-s+1)) " using assms by auto
   moreover have "(exp (complex_of_real (2*pi)*\<i>*(bf (s-1) (r-1-1) m jd))) * (exp (2*pi*\<i>*((bin_rep m jd)!(r-1))/2^(r-s+1)))
        = (exp (complex_of_real (2*pi)*\<i>*(bf (s-1) (r-1) m jd)))" using exp_mult assms by blast
   ultimately show ?thesis using assms by auto
 qed
  moreover have "i=3 \<longrightarrow> ((qr s r m jd) \<Otimes> one) $$ (i,j) = (exp (complex_of_real (2*pi)*\<i>*(bf (s-1) (r-1) m jd))) * 1/sqrt(2)" 
    using qr_def ket_vec_def f0 by auto
  moreover have "i\<in>{0,1,2,3}" using f0 by auto
  ultimately show "((CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> one)) $$ (i,j) = ((qr s r m jd) \<Otimes> one) $$ (i,j)" 
    using f0 ket_vec_def qr_def by (smt set_four)
next
  show "dim_row ((CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> one)) = dim_row ((qr s r m jd) \<Otimes> one)" 
    by (simp add: controlled_phase_shift_def ket_vec_def qr_def)
next
  show "dim_col ((CR (r-s+1)) * ((qr s (r-1) m jd) \<Otimes> one)) = dim_col ((qr s r m jd) \<Otimes> one)"
    using ket_vec_def controlled_phase_shift_def qr_def by auto
qed

(*------------------------------------------------------------------------------------------------*)
(*-----------------------------------------Swapping------ ----------------------------------------*)
(*------------------------------------------------------------------------------------------------*)



(*The idea is to apply the controlled R gate only to the tensor product of two single qubits. The first qubit is 
already at the current position. This is the qubit we want to apply the R_j gate too. The second qubit is "hidden" 
in the unit vector (which is just a tensor product of single qubit where the qubit at position j is the one we need). 
Thus, we repeatedly swap qubit j with the qubit in front of it until it directly follows the current qubit. Then, 
we can apply the controlled R gate which leaves the second qubit untouched (see proofs above). Then we can switch the
qubit back to its original position. *)
abbreviation swapping_gate :: "complex Matrix.mat" ("SWAP") where  (*TODO: do not capitalize?*)
"SWAP \<equiv> Matrix.mat 4 4 (\<lambda>(i,j). if i=0 \<and> j=0 then 1 else 
                                (if i=1 \<and> j=2 then 1 else 
                                (if i=2 \<and> j=1 then 1 else 
                                (if i=3 \<and> j=3 then 1 else 0))))"


lemma transpose_of_swapping_gate:
  shows "(SWAP)\<^sup>t = SWAP"
proof
  fix i j::nat
  assume a0: "i < dim_row SWAP" and a1: "j < dim_col SWAP"
  then have "i \<in> {0,1,2,3}" and "j \<in> {0,1,2,3}" by auto
  then show  "(SWAP)\<^sup>t $$ (i,j) = SWAP $$ (i,j)" by auto    
next
  show "dim_row (SWAP)\<^sup>t = dim_row SWAP" by simp
next
  show "dim_col (SWAP)\<^sup>t = dim_col SWAP"  by simp
qed

lemma adjoint_of_SWAP: 
  shows "(SWAP)\<^sup>\<dagger> = SWAP"
proof
  show "dim_row (SWAP\<^sup>\<dagger>) = dim_row SWAP" by simp
next
  show "dim_col (SWAP\<^sup>\<dagger>) = dim_col SWAP" by simp
next
  fix i j:: nat
  assume "i < dim_row SWAP" and "j < dim_col SWAP"
  then have "i \<in> {0,1,2,3}" and "j \<in> {0,1,2,3}" by auto
  thus "SWAP\<^sup>\<dagger> $$ (i, j) = SWAP $$ (i, j)" 
    using hermite_cnj_def by auto
qed

lemma SWAP_gate:
  shows "gate 2 SWAP" 
proof
  show "dim_row SWAP = 2\<^sup>2" by simp
next
  show "square_mat SWAP" by simp
next
  show "unitary SWAP" 
  proof-
    have "(SWAP)\<^sup>\<dagger> * SWAP = 1\<^sub>m (dim_col SWAP)"
    proof
      show "dim_row ((SWAP)\<^sup>\<dagger> * SWAP) = dim_row (1\<^sub>m (dim_col SWAP))" by simp
    next
      show "dim_col ((SWAP)\<^sup>\<dagger> * SWAP) = dim_col (1\<^sub>m (dim_col SWAP))" by simp
    next
      fix i j:: nat
      assume "i < dim_row (1\<^sub>m (dim_col SWAP))" and "j < dim_col (1\<^sub>m (dim_col SWAP))"
      then have "i \<in> {0,1,2,3}" and "j \<in> {0,1,2,3}" using controlled_phase_shift_def by auto 
      then show "((SWAP)\<^sup>\<dagger> * SWAP) $$ (i,j) = 1\<^sub>m (dim_col SWAP) $$ (i, j)"
        apply (auto simp add: one_mat_def times_mat_def)
         apply (auto simp: scalar_prod_def controlled_phase_shift_def).
    qed
    then show ?thesis 
      by (simp add: adjoint_of_SWAP unitary_def)
  qed    
qed


lemma app_SWAP:
  assumes "dim_row v = 2" and "dim_col v = 1"
      and "dim_row w = 2" and "dim_col w = 1"
  shows "SWAP * (v \<Otimes> w) = w \<Otimes> v"
proof
  fix i j
  assume "i < dim_row (w \<Otimes> v)" and "j < dim_col (w \<Otimes> v)"
  then have f0: "i \<in> {0,1,2,3}" and f1: "j = 0" using assms by auto 
  then have f2: "(SWAP * (v \<Otimes> w)) $$ (i,j) = (\<Sum>k < 4. (SWAP $$ (i,k)) * ((v \<Otimes> w) $$ (k,0)))" 
    using assms index_matrix_prod by auto
  moreover have "i=0 \<longrightarrow> (SWAP * (v \<Otimes> w)) $$ (i,j) = (w \<Otimes> v) $$ (i,j)" using lessThan_atLeast0 assms f1 f2 by auto
  moreover have "i=1 \<longrightarrow> (SWAP * (v \<Otimes> w)) $$ (i,j) = (w \<Otimes> v) $$ (i,j)" using lessThan_atLeast0 assms f1 f2 by auto 
  moreover have "i=2 \<longrightarrow> (SWAP * (v \<Otimes> w)) $$ (i,j) = (w \<Otimes> v) $$ (i,j)" using lessThan_atLeast0 assms f1 f2 by auto 
  moreover have "i=3 \<longrightarrow> (SWAP * (v \<Otimes> w)) $$ (i,j) = (w \<Otimes> v) $$ (i,j)" using lessThan_atLeast0 assms f1 f2 by auto 
  ultimately show "(SWAP * (v \<Otimes> w)) $$ (i,j) = (w \<Otimes> v) $$ (i,j)" using f0 by blast
next
  show "dim_row (SWAP * (v \<Otimes> w)) = dim_row (w \<Otimes> v)" using assms by auto
next
  show "dim_col (SWAP * (v \<Otimes> w)) = dim_col (w \<Otimes> v)" using assms by auto
qed


(*Swaps the k+1 and k+2 qubit of a k+2+t qubit system. E.g. |011010\<rangle> and k=1 and t=3 gives |001110\<rangle> *)
definition SWAP_all :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
"SWAP_all k t \<equiv> (Id k) \<Otimes> SWAP \<Otimes> (Id t)"

lemma SWAP_all_special_cases:
  shows "SWAP_all 0 t = SWAP \<Otimes> (Id t)"
    and "SWAP_all k 0 = (Id k) \<Otimes> SWAP"
  using Id_left_tensor Id_right_tensor SWAP_all_def Id_def by auto

lemma SWAP_all_dim:
  shows "dim_row (SWAP_all k t) = 2^(k+2+t)"
    and "dim_col (SWAP_all k t) = 2^(k+2+t)" 
proof-
  show "dim_row (SWAP_all k t) = 2^(k+2+t)"
    using Id_def SWAP_all_def by (simp add: power_add)
next 
  show "dim_col (SWAP_all k t) = 2^(k+2+t)" 
    using Id_def SWAP_all_def by (simp add: power_add)
qed


lemma app_SWAP_all:
  assumes "dim_row v = 2" and "dim_col v = 1"  
      and "dim_row w = 2" and "dim_col w = 1" 
      and "length xs = k" and "length ys = t"
      and "\<forall>x \<in> set xs. dim_row x = 2" and "\<forall>y \<in> set ys. dim_row y = 2"
      and "\<forall>x \<in> set xs. dim_col x = 1" and "\<forall>y \<in> set ys. dim_col y = 1"
  shows "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) = ((pw xs k) \<Otimes> w \<Otimes> v \<Otimes> (pw ys t))"
proof-
  have "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) = ((Id k) \<Otimes> SWAP \<Otimes> (Id t)) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t))"
    using SWAP_all_def assms by auto
  then have "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) = ((Id k) \<Otimes> (SWAP \<Otimes> (Id t))) * ((pw xs k) \<Otimes> (v \<Otimes> w \<Otimes> (pw ys t)))"
    using tensor_mat_is_assoc by auto
  moreover have "dim_col (Id k) = dim_row (pw xs k)"  
    using Id_def pow_tensor_list_dim_row assms by (metis index_one_mat(3) nat_less_le)
  moreover have "dim_col (SWAP \<Otimes> (Id t)) = dim_row (v \<Otimes> w \<Otimes> (pw ys t))" 
    using Id_def assms pow_tensor_list_dim_row[of ys t 2] by auto
  moreover have "dim_col (Id k) > 0" and "dim_col (SWAP \<Otimes> (Id t)) > 0" and
                "dim_col (pw xs k) > 0" and "dim_col (v \<Otimes> w \<Otimes> (pw ys t)) > 0" 
    apply (auto simp: Id_def assms pow_tensor_list_dim_col[of xs k] pow_tensor_list_dim_col[of ys t]).
  ultimately have "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) =
              ((Id k)*(pw xs k)) \<Otimes> ((SWAP \<Otimes> (Id t)) * (v \<Otimes> w \<Otimes> (pw ys t)))"
    using mult_distr_tensor by auto
  then have "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) =
             ((pw xs k)) \<Otimes> ((SWAP \<Otimes> (Id t)) * (v \<Otimes> w \<Otimes> (pw ys t)))" 
    using Id_def \<open>dim_col (Id k) = dim_row (pw xs k)\<close> by auto
  moreover have "dim_col SWAP = dim_row (v \<Otimes> w)" using assms by simp
  moreover have "dim_col (Id t) = dim_row (pw ys t)" using Id_def pow_tensor_list_dim_row[of ys t] assms 
    by (metis index_one_mat(3))
  moreover have "dim_col SWAP > 0" and "dim_col (v \<Otimes> w) > 0" and "dim_col (Id t) > 0" and "dim_col (pw ys t) > 0" 
    apply (auto simp: assms Id_def pow_tensor_list_dim_col[of ys t]). 
  ultimately have "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) =
                   (pw xs k) \<Otimes> ((SWAP * (v \<Otimes> w)) \<Otimes> ((Id t) * (pw ys t)))" 
    using mult_distr_tensor by auto
  then have "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) =
                   (pw xs k) \<Otimes> ((SWAP * (v \<Otimes> w)) \<Otimes> (pw ys t))" 
    using Id_def \<open>dim_col (Id t) = dim_row (pw ys t)\<close> by auto
  then have "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) =
                   (pw xs k) \<Otimes> ((w \<Otimes> v) \<Otimes> (pw ys t))" 
    using assms app_SWAP by auto
  then show "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) = ((pw xs k) \<Otimes> w \<Otimes> v \<Otimes> (pw ys t))"
    using tensor_mat_is_assoc by auto
qed

(*Could go into generic mult function would be more confusing to understand though*)
(*Takes a the position k of a qubit that should be swapped to the front and the number of remaining qubits t. If the 
qubit is already at the front the Id matrix is applied
E.g. |111011\<rangle> and k=4 and t=2 gives |011111\<rangle> *)
fun SWAP_front:: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("fSWAP _ _" 75)  where
  "(fSWAP (Suc 0) t) = Id (t+1)" 
| "(fSWAP (Suc k) t) = (fSWAP k (t+1)) * (SWAP_all (k-1) t)"
 
lemma SWAP_front_dim [simp]:
  assumes "k\<ge>1"
  shows "dim_row (fSWAP k t) = 2^(k+t)" and "dim_col (fSWAP k t) = 2^(k+t)" 
proof-
  have "\<forall>t. dim_row (fSWAP k t) = 2^(k+t) \<and> dim_col (fSWAP k t) = 2^(k+t)" 
  proof(rule Nat.nat_induct_at_least[of 1 k])
    show "k\<ge>1" using assms by auto
  next
    show "\<forall>t. dim_row (fSWAP 1 t) = 2^(1+t) \<and> dim_col (fSWAP 1 t) = 2^(1+t)" using Id_def by auto
  next
    fix k::nat
    assume a0: "k\<ge>1" 
    and IH: "\<forall>t. dim_row (fSWAP k t) = 2^(k+t) \<and> dim_col (fSWAP k t) = 2^(k+t)" 
    show "\<forall>t. dim_row (fSWAP (Suc k) t) = 2^((Suc k)+t) \<and> dim_col (fSWAP (Suc k) t) = 2^((Suc k)+t)" 
    proof
      fix t 
      have f0: "fSWAP (Suc k) t = (fSWAP k (t+1)) * (SWAP_all (k-1) t)" 
        using SWAP_front.simps a0 by (metis Suc_diff_le diff_Suc_1)
      have "dim_row (fSWAP (Suc k) t) = 2^((Suc k)+t)" 
      proof-
        have "dim_row (fSWAP (Suc k) t) = dim_row ((fSWAP k (t+1)) * (SWAP_all (k-1) t))" using f0 by auto
        then have "dim_row (fSWAP (Suc k) t) = dim_row (fSWAP k (t+1))" by auto
        then have "dim_row (fSWAP (Suc k) t) = 2^(k+t+1)" using IH by auto
        then show ?thesis by auto
      qed
      moreover have "dim_col (fSWAP (Suc k) t) = 2^((Suc k)+t)" 
      proof-
        have "dim_col (fSWAP (Suc k) t) = dim_col ((fSWAP k (t+1)) * (SWAP_all (k-1) t))" using f0 by auto
        then have "dim_col (fSWAP (Suc k) t) = dim_col (SWAP_all (k-1) t)" by auto
        then have "dim_col (fSWAP (Suc k) t) = 2^(k-1+2+t)" using SWAP_all_dim by auto
        then show ?thesis using a0 by auto
      qed
      ultimately show "dim_row (fSWAP (Suc k) t) = 2^((Suc k)+t) \<and> dim_col (fSWAP (Suc k) t) = 2^((Suc k)+t)" by auto
    qed
  qed
  then show "dim_row (fSWAP k t) = 2^(k+t)" and "dim_col (fSWAP k t) = 2^(k+t)"  by auto
qed

lemma fSWAP_dim [simp]: (*Might not be needed change name*)
  assumes "m\<ge>k" and "k-c \<ge>1"
  shows "dim_row (fSWAP (k-c) (m-k)) = 2^(m-c)"
    and "dim_col (fSWAP (k-c) (m-k)) = 2^(m-c)"
  using SWAP_front_dim assms by auto

lemma Id_fSWAP_dim [simp]:
  assumes "m\<ge>k" and "k-c \<ge>1"
  shows "dim_row (Id 1 \<Otimes> (fSWAP (k-c) (m-k))) = 2^(m-c+1)"
    and "dim_col (Id 1 \<Otimes> (fSWAP (k-c) (m-k))) = 2^(m-c+1)"
  using SWAP_front_dim assms Id_def by auto


lemma SWAP_unitary:
  assumes "k\<ge>1"
  shows "unitary (fSWAP k t)" 
proof-
  have "(fSWAP k t)\<^sup>\<dagger> * (fSWAP k t) = 1\<^sub>m (dim_col (fSWAP k t))"
    sorry
  show ?thesis sorry
qed



lemma SWAP_front_gate: 
  assumes "k\<ge>1" (*This is important ^^ Otw inconsistency*)
  shows "gate (k+t) (fSWAP k t)" 
proof
  show "dim_row (fSWAP k t) = 2^(k+t)" using assms by auto
next
  show "square_mat (fSWAP k t)" using assms by auto
next
  show "unitary (fSWAP k t)"
    sorry
qed

lemma SWAP_front_hermite_cnj_dim:
  assumes "k\<ge>1"
  shows "dim_row (fSWAP k t)\<^sup>\<dagger> = 2^(k+t)"
  and "dim_col (fSWAP k t)\<^sup>\<dagger> = 2^(k+t)" 
  using SWAP_front_dim assms by auto

lemma Id_fSWAP_herm_cnj_dim [simp]:
  fixes k m c::nat
  assumes "m\<ge>k" and "k-c \<ge>1"
  shows "dim_row (Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) = 2^(m-c+1)"
    and "dim_col (Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) = 2^(m-c+1)"
  using SWAP_front_hermite_cnj_dim assms Id_def by auto


(*This need revision*)
lemma aux_app_fSWAP:
  fixes k m::nat 
  assumes "k\<ge>c+1" and "k\<ge>1" and "c\<le>m" 
      and "dim_row v = 2" and "dim_col v = 1" 
    shows "\<forall>xs ys. (\<forall>x \<in> set xs. dim_row x = 2) \<and> (\<forall>y \<in> set ys. dim_row y = 2) \<and>
           (\<forall>x \<in> set xs. dim_col x = 1) \<and> (\<forall>y \<in> set ys. dim_col y = 1) \<and>
           length xs = k-c-1 \<and> length ys = m-k \<and> m\<ge>k \<longrightarrow> 
           (fSWAP (k-c) (m-k)) * ((pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) 
          = v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))" 
proof(rule Nat.nat_induct_at_least[of "c+1" k])
  show "k\<ge>c+1" using assms by auto
next
  show "\<forall>xs ys. (\<forall>x \<in> set xs. dim_row x = 2) \<and> (\<forall>y \<in> set ys. dim_row y = 2) \<and>
           (\<forall>x \<in> set xs. dim_col x = 1) \<and> (\<forall>y \<in> set ys. dim_col y = 1) \<and>
           length xs = ((c+1)-c-1) \<and> length ys = m-(c+1) \<and> m\<ge>(c+1) \<longrightarrow> 
           (fSWAP ((c+1)-c) (m-(c+1))) * ((pw xs ((c+1)-c-1)) \<Otimes> v \<Otimes> (pw ys (m-(c+1)))) 
          = v \<Otimes> (pw xs ((c+1)-c-1)) \<Otimes> (pw ys (m-(c+1)))" 
  proof(rule allI, rule allI, rule impI)
    fix xs ys::"complex Matrix.mat list"
    assume a0: "(\<forall>x \<in> set xs. dim_row x = 2) \<and> (\<forall>y \<in> set ys. dim_row y = 2) \<and>
           (\<forall>x \<in> set xs. dim_col x = 1) \<and> (\<forall>y \<in> set ys. dim_col y = 1) \<and>
           length xs = ((c+1)-c-1) \<and> length ys = m-(c+1) \<and> m\<ge>(c+1)"
    then have "(fSWAP 1 (m-c-1)) * ((pw xs 0) \<Otimes> v \<Otimes> (pw ys (m-(c+1)))) = Id (m-c-1+1) * ((pw xs 0) \<Otimes> v \<Otimes> (pw ys (m-(c+1))))"
      using assms by auto
    then have "(fSWAP 1 (m-c-1)) * ((pw xs 0) \<Otimes> v \<Otimes> (pw ys (m-(c+1)))) = Id (m-c-1+1) * (v \<Otimes> (pw ys (m-(c+1))))"
      using a0 Id_left_tensor by auto
    moreover have "dim_row (v \<Otimes> (pw ys (m-(c+1)))) = 2 * 2^(m-(c+1))" 
      using assms pow_tensor_list_dim_row[of ys "(m-(c+1))" "2"] a0 by simp
    moreover have "2 * 2^(m-(c+1)) = 2^(m-c-1+1)" by auto
    ultimately have "(fSWAP 1 (m-c-1)) * ((pw xs 0) \<Otimes> v \<Otimes> (pw ys (m-(c+1)))) = (v \<Otimes> (pw ys (m-(c+1))))"
      using Id_def assms a0 one_mat_def Id_mult_left by smt
    then show "(fSWAP ((c+1)-c) (m-(c+1))) * ((pw xs ((c+1)-c-1)) \<Otimes> v \<Otimes> (pw ys (m-(c+1)))) 
              = v \<Otimes> (pw xs ((c+1)-c-1)) \<Otimes> (pw ys (m-(c+1)))"
      using Id_right_tensor a0 by auto
  qed
next
  fix k::nat
  assume a0: "k\<ge>c+1"
  assume IH: "\<forall>xs ys. (\<forall>x \<in> set xs. dim_row x = 2) \<and> (\<forall>y \<in> set ys. dim_row y = 2) \<and>
           (\<forall>x \<in> set xs. dim_col x = 1) \<and> (\<forall>y \<in> set ys. dim_col y = 1) \<and>
           length xs = (k-c-1) \<and> length ys = m-k \<and> m\<ge>k  \<longrightarrow> 
           (fSWAP (k-c) (m-k)) * ((pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) 
          = v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))" 
  show "\<forall>xs ys. (\<forall>x \<in> set xs. dim_row x = 2) \<and> (\<forall>y \<in> set ys. dim_row y = 2) \<and>
           (\<forall>x \<in> set xs. dim_col x = 1) \<and> (\<forall>y \<in> set ys. dim_col y = 1) \<and>
           length xs = ((Suc k)-c-1) \<and> length ys = m-(Suc k) \<and> m\<ge>(Suc k)  \<longrightarrow> 
           (fSWAP ((Suc k)-c) (m-(Suc k))) * ((pw xs ((Suc k)-c-1)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) 
          = v \<Otimes> (pw xs ((Suc k)-c-1)) \<Otimes> (pw ys (m-(Suc k)))" 
  proof(rule allI, rule allI, rule impI)
    fix xs ys::"complex Matrix.mat list"
    assume a1: "(\<forall>x \<in> set xs. dim_row x = 2) \<and> (\<forall>y \<in> set ys. dim_row y = 2) \<and>
           (\<forall>x \<in> set xs. dim_col x = 1) \<and> (\<forall>y \<in> set ys. dim_col y = 1) \<and>
           length xs = ((Suc k)-c-1) \<and> length ys = m-(Suc k) \<and> m\<ge>(Suc k)" 
    have "(fSWAP ((Suc k)-c) (m-(Suc k))) * ((pw xs ((Suc k)-c-1)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) 
         = (fSWAP ((Suc k)-c-1) (m-(Suc k)+1)) * (SWAP_all (((Suc k)-c-1)-1) (m-(Suc k)))  * ((pw xs ((Suc k)-c-1)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) "
      using a0 SWAP_front.simps le_Suc_ex by fastforce
    moreover have "(Suc k)-c-1 = k-c" using assms by auto
    moreover have "(m-(Suc k)+1) = m-k" using assms a1 by auto
    moreover have "(((Suc k)-c-1)-1) = k-c-1" using assms by auto
    moreover have "((Suc k)-c-1) = k-c" using calculation(2) by blast
    ultimately have "(fSWAP ((Suc k)-c) (m-(Suc k))) * ((pw xs ((Suc k)-c-1)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) 
         = (fSWAP (k-c) (m-k)) * (SWAP_all (k-c-1) (m-(Suc k))) * ((pw xs (k-c)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k))))"
      by auto
    moreover have f1: "(pw xs (k-c)) = (pw (butlast xs) ((k-c)-1)) \<Otimes> (last xs)" 
    proof-
      have "length (butlast xs) = (k-c-1)" using a1 by auto
      moreover have "(butlast xs)@[last xs] = xs" using a1 
        by (metis a0 append_butlast_last_id butlast.simps(1) calculation diff_diff_left le_imp_less_Suc less_imp_le_nat n_not_Suc_n ordered_cancel_comm_monoid_diff_class.diff_add)
      moreover have "k - c - 1 + 1 = k - c" using a0 by auto
      ultimately show "(pw xs (k-c)) = (pw (butlast xs) ((k-c)-1)) \<Otimes> (last xs)" 
        using assms pow_tensor_decomp_left[of "butlast xs" "k-c-1" "last xs"] by auto
    qed
    moreover have "(fSWAP (k-c) (m-k)) * (SWAP_all (k-c-1) (m-(Suc k))) * ((pw xs (k-c)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k))))
                = (fSWAP (k-c) (m-k)) * ((SWAP_all (k-c-1) (m-(Suc k))) * ((pw xs (k-c)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))))"
    proof-
      have "(fSWAP (k-c) (m-k)) \<in> carrier_mat (2^(m-c)) (2^(m-c))"
        using fSWAP_dim[of k m c] assms a1 
        by (smt Nat.le_diff_conv2 a0 add.right_neutral add_Suc_right add_leD2 carrier_matI plus_1_eq_Suc)
      moreover have "(SWAP_all (k-c-1) (m-(Suc k))) \<in> carrier_mat (2^(m-c)) (2^(m-c))"
        using SWAP_all_dim[of "k-c-1" "m-(Suc k)"] aux_calculation(5) a1 assms by (smt a0 carrier_matI less_imp_le_nat)
      moreover have "((pw xs (k-c)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) \<in> carrier_mat (2^(m-c)) 1" 
      proof
        have "m \<ge> Suc k" using a1 by auto
        moreover have "dim_row (pw xs (k-c)) = 2^(k-c)" 
          using pow_tensor_list_dim_row[of xs "k-c"] a0 a1 by auto
        moreover have "dim_row (pw ys (m-(Suc k))) = 2^(m-(Suc k))"  
          using pow_tensor_list_dim_row[of ys "m-(Suc k)"] a0 a1 by auto
        ultimately show "dim_row ((pw xs (k-c)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) = 2^(m-c)" 
          using assms a0 a1 by auto
      next
        have "m \<ge> Suc k" using a1 by auto
        moreover have "dim_col (pw xs (k-c)) = 1" 
          using pow_tensor_list_dim_col[of xs "k-c"] a0 a1 by auto
        moreover have "dim_col (pw ys (m-(Suc k))) = 1"  
          using pow_tensor_list_dim_col[of ys "m-(Suc k)"] a0 a1 by auto
        show "dim_col ((pw xs (k-c)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) = 1" 
          using assms a0 a1 by (simp add: assms(4) assms(5) \<open>dim_col (pw ys m - Suc k) = 1\<close> calculation(2))
      qed
      ultimately show ?thesis by auto
    qed
    moreover have "(SWAP_all (k-c-1) (m-(Suc k))) * ((pw (butlast xs) (k-c-1)) \<Otimes> (last xs) \<Otimes> v \<Otimes> (pw ys (m-(Suc k))))
          = ((pw (butlast xs) (k-c-1)) \<Otimes> v \<Otimes> (last xs) \<Otimes> (pw ys (m-(Suc k))))" 
    proof-
      have "dim_row (last xs) = 2" and "dim_col (last xs) = 1" using a1 
        apply (metis One_nat_def Suc_diff_le \<open>Suc k - c - 1 = k - c\<close> a0 butlast.simps(1) diff_diff_left last_in_set length_butlast list.size(3) zero_neq_one)
        by (metis One_nat_def Suc_diff_le \<open>Suc k - c - 1 = k - c\<close> a0 a1 butlast.simps(1) diff_diff_left last_in_set length_butlast list.size(3) zero_neq_one)
      moreover have "length (butlast xs) = k-c-1" using a1 by simp
      moreover have  "\<forall>x \<in> set (butlast xs). dim_row x = 2"
        and "\<forall>x \<in> set (butlast xs). dim_col x = 1" 
       by (auto simp: a1 in_set_butlastD)
      ultimately show ?thesis  using app_SWAP_all assms a1 by auto 
    qed
    ultimately have "(fSWAP ((Suc k)-c) (m-(Suc k))) * ((pw xs ((Suc k)-c-1)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) 
         = (fSWAP (k-c) (m-k)) * ((pw (butlast xs) (k-c-1)) \<Otimes> v \<Otimes> (last xs) \<Otimes> (pw ys (m-(Suc k))))" 
      using tensor_mat_is_assoc by auto
    then have "(fSWAP ((Suc k)-c) (m-(Suc k))) * ((pw xs ((Suc k)-c-1)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) 
         = (fSWAP (k-c) (m-k)) * ((pw (butlast xs) (k-c-1)) \<Otimes> v \<Otimes> ((last xs) \<Otimes> (pw ys (m-(Suc k)))))" 
      using tensor_mat_is_assoc by auto
    then have "(fSWAP ((Suc k)-c) (m-(Suc k))) * ((pw xs ((Suc k)-c-1)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) 
         = (fSWAP (k-c) (m-k)) * ((pw (butlast xs) (k-c-1)) \<Otimes> v \<Otimes> (pw ((last xs)#ys) (m-k)))" 
      using pow_tensor_decomp_right[of ys "m-(Suc k)" "last xs"] a1 by auto
    moreover have "(fSWAP (k-c) (m-k)) * ((pw (butlast xs) (k-c-1)) \<Otimes> v \<Otimes> (pw ((last xs)#ys) (m-k)))
         = v \<Otimes> (pw (butlast xs) (k-c-1)) \<Otimes> (pw ((last xs)#ys) (m-k))"
    proof-
      have "(\<forall>x \<in> set (butlast xs). dim_row x = 2) \<and> (\<forall>x \<in> set (butlast xs). dim_col x = 1) " 
        using a1 by (simp add: in_set_butlastD)
      moreover have "dim_row (last xs) = 2 \<and> dim_col (last xs) = 1" 
        by (metis Suc_diff_le Zero_not_Suc a0 a1 diff_diff_left last_in_set list.size(3))
      moreover have "(\<forall>y \<in> set ((last xs)#ys). dim_row y = 2) \<and> (\<forall>y \<in> set ((last xs)#ys). dim_col y = 1)"
        using a1 calculation by auto
      moreover have "length (butlast xs) = (k-c-1) \<and> length ((last xs)#ys) = m-k \<and> m>k" 
        using a1 by auto
      ultimately show "(fSWAP (k-c) (m-k)) * ((pw (butlast xs) (k-c-1)) \<Otimes> v \<Otimes> (pw ((last xs)#ys) (m-k))) 
          = v \<Otimes> (pw (butlast xs) (k-c-1)) \<Otimes> (pw ((last xs)#ys) (m-k))"
        using IH by auto
    qed
    ultimately have "(fSWAP ((Suc k)-c) (m-(Suc k))) * ((pw xs ((Suc k)-c-1)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) 
         = v \<Otimes> (pw (butlast xs) (k-c-1)) \<Otimes> (pw ((last xs)#ys) (m-k))" by auto
    then have "(fSWAP ((Suc k)-c) (m-(Suc k))) * ((pw xs ((Suc k)-c-1)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) 
         = (v \<Otimes> (pw (butlast xs) (k-c-1)) \<Otimes> ((last xs) \<Otimes> (pw ys (m-k-1))))" 
      using pow_tensor_decomp_right[of ys "m-k-1" "last xs"] a1 by auto
    then have "(fSWAP ((Suc k)-c) (m-(Suc k))) * ((pw xs ((Suc k)-c-1)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) 
         = (v \<Otimes> ((pw (butlast xs) (k-c-1)) \<Otimes> (last xs)) \<Otimes> (pw ys (m-k-1)))" 
      using tensor_mat_is_assoc by auto
    then have "(fSWAP ((Suc k)-c) (m-(Suc k))) * ((pw xs ((Suc k)-c-1)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) 
         = (v \<Otimes> (pw xs (k-c)) \<Otimes> (pw ys (m-(Suc k))))" 
      using f1 by auto
    then show "(fSWAP ((Suc k)-c) (m-(Suc k))) * ((pw xs ((Suc k)-c-1)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) 
          = v \<Otimes> (pw xs ((Suc k)-c-1)) \<Otimes> (pw ys (m-(Suc k)))"
      by auto
  qed
qed


lemma app_fSWAP:
  fixes k m c::nat 
  assumes "k\<ge>c+1" and "k\<ge>1" and "c\<le>m"  and "m\<ge>k" and "dim_row v = 2" and "dim_col v = 1" 
      and "(\<forall>x \<in> set xs. dim_row x = 2)" and "(\<forall>y \<in> set ys. dim_row y = 2)"
      and "(\<forall>x \<in> set xs. dim_col x = 1)" and "(\<forall>y \<in> set ys. dim_col y = 1)" 
      and "length xs = (k-c-1)" and "length ys = m-k"
    shows "(fSWAP (k-c) (m-k)) * ((pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) 
          = v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))" 
  using aux_app_fSWAP assms by auto





(*The current qubit should not be altered by the swapping *)
lemma app_Id_fSWAP:
  assumes "k\<ge>1" and "m\<ge>k" and "1\<le>k-c"and "m\<ge>c" 
      and "dim_row v = 2" and "dim_col v = 1" 
      and "(\<forall>x \<in> set xs. dim_row x = 2)" and "(\<forall>y \<in> set ys. dim_row y = 2)"
      and "(\<forall>x \<in> set xs. dim_col x = 1)" and "(\<forall>y \<in> set ys. dim_col y = 1)" 
      and "length xs = (k-c-1)" and "length ys = m-k"
  shows "(Id 1 \<Otimes> (fSWAP (k-c) (m-k))) * ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k)))
       = (qr c (k-1) m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))"
proof-
  have "dim_col (Id 1) = dim_row (qr c (k-1) m j)" by (simp add: Id_def qr_def)
  moreover have "dim_col (fSWAP (k-c) (m-k)) = dim_row ((pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k)))" 
    using fSWAP_dim[of k m c] assms pow_tensor_list_dim_row[of xs "(k-c-1)" "2"] pow_tensor_list_dim_row[of ys "m-k" "2"] 
          tensor_mat_is_assoc by auto
  moreover have "dim_col (Id 1) > 0" and "dim_col (qr c (k-1) m j) > 0" and "dim_col (fSWAP (k-c) (m-k)) > 0"
            and "dim_col ((pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) > 0" 
       apply (auto simp: Id_def assms qr_def ) 
       using SWAP_front_dim assms apply auto[1] 
       apply (auto simp: assms pow_tensor_list_dim_col[of xs "(k-(Suc c))"])
       apply (auto simp: assms pow_tensor_list_dim_col[of ys "m-k"]).
  ultimately have "((Id 1) \<Otimes> (fSWAP (k-c) (m-k))) * ((qr c (k-1) m j) \<Otimes> ((pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))))
           = ((Id 1) * (qr c (k-1) m j)) \<Otimes> ((fSWAP (k-c) (m-k)) * ((pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))))" 
    using mult_distr_tensor by auto
  then have "((Id 1) \<Otimes> (fSWAP (k-c) (m-k))) * ((qr c (k-1) m j) \<Otimes> ((pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))))
           = ((qr c (k-1) m j) \<Otimes> (fSWAP (k-c) (m-k)) * ((pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))))" 
    using Id_def qr_def by auto
  then show "(Id 1 \<Otimes> (fSWAP (k-c) (m-k))) * ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k)))
           = (qr c (k-1) m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))" 
    using app_fSWAP assms tensor_mat_is_assoc by auto
qed


lemma CR_on_all_Id:
  fixes k c m j::nat
  assumes "k\<ge>2" and "m\<ge>1" and "k\<le>m" and "dim_row v = 2" and "dim_col v = 1" 
      and "c\<ge>1" and "c \<le> k - 1" and "c\<le>m" 
      and "v = zero \<or> v = one"
      and "v = zero \<longrightarrow> ((bin_rep m j)!(k-1)) = 0"
      and "v = one \<longrightarrow>  ((bin_rep m j)!(k-1)) = 1" 
      and "(\<forall>x \<in> set xs. dim_row x = 2)" and "(\<forall>y \<in> set ys. dim_row y = 2)"
      and "(\<forall>x \<in> set xs. dim_col x = 1)" and "(\<forall>y \<in> set ys. dim_col y = 1)" 
      and "length xs = (k-c-1)" and "length ys = m-k"
   shows "(CR (k-c+1) \<Otimes> Id (m-c-1)) * ((qr c (k-1) m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))) 
        = (qr c k m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))" 
proof-
  have "(CR (k-c+1) \<Otimes> Id (m-c-1)) * ((qr c (k-1) m j) \<Otimes> v \<Otimes> ((pw xs (k-c-1)) \<Otimes> (pw ys (m-k)))) = 
        (CR (k-c+1) * ((qr c (k-1) m j) \<Otimes> v)) \<Otimes> (Id (m-c-1) * ((pw xs (k-c-1)) \<Otimes> (pw ys (m-k))))" 
  proof-
    have "dim_col (CR (k-c+1)) = dim_row ((qr c (k-1) m j) \<Otimes> v)" 
      using controlled_phase_shift_def qr_def assms by auto
    moreover have "dim_col (Id (m-c-1)) = dim_row ((pw xs (k-c-1)) \<Otimes> (pw ys (m-k)))" 
      using Id_def pow_tensor_list_dim_row[of xs "k-c-1" "2"] pow_tensor_list_dim_row[of ys "m-k" "2"] assms 
      by (smt Nat.add_diff_assoc2 Nat.le_diff_conv2 add_leD1 diff_diff_left dim_row_tensor_mat index_one_mat(3) less_imp_le_nat one_add_one ordered_cancel_comm_monoid_diff_class.add_diff_inverse power_add)
    moreover have "dim_col (CR (k-c+1)) > 0" 
            and "dim_col ((qr c (k-1) m j) \<Otimes> v) > 0" 
            and "dim_col (Id (m-c-1)) > 0" 
            and "dim_col ((pw xs (k-c-1)) \<Otimes> (pw ys (m-k))) > 0" 
      using controlled_phase_shift_def qr_def Id_def qr_def pow_tensor_list_dim_col[of ys "m-k"] 
          pow_tensor_list_dim_col[of xs "k-c-1"] assms 
      by auto
    ultimately show ?thesis 
      using mult_distr_tensor by auto
  qed
  moreover have "dim_row ((pw xs (k-c-1)) \<Otimes> (pw ys (m-k))) = 2^(m-c-1)" 
    using pow_tensor_list_dim_row[of xs "k-c-1"] assms pow_tensor_list_dim_row[of ys "m-k"] 
    by (smt Nat.add_diff_assoc2 Nat.le_diff_conv2 add_leD1 diff_diff_left dim_row_tensor_mat less_imp_le_nat one_add_one ordered_cancel_comm_monoid_diff_class.add_diff_inverse power_add)
  ultimately have "(CR (k-c+1) \<Otimes> Id (m-c-1)) * ((qr c (k-1) m j) \<Otimes> v \<Otimes> ((pw xs (k-c-1)) \<Otimes> (pw ys (m-k)))) = 
        (CR (k-c+1) * ((qr c (k-1) m j) \<Otimes> v)) \<Otimes> ((pw xs (k-c-1)) \<Otimes> (pw ys (m-k)))" 
    using Id_mult_left by auto
  then have f0: "(CR (k-c+1) \<Otimes> Id (m-c-1)) * ((qr c (k-1) m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))) =
        (CR (k-c+1) * ((qr c (k-1) m j) \<Otimes> v)) \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))" 
    using tensor_mat_is_assoc by auto
  show "(CR (k-c+1) \<Otimes> Id (m-c-1)) * ((qr c (k-1) m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))) 
      = (qr c k m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))" 
  proof(rule disjE)
    show "v = zero \<or> v = one" using assms by auto
  next
    assume "v=zero" 
    then show "(CR (k-c+1) \<Otimes> Id (m-c-1)) * ((qr c (k-1) m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))) 
             = (qr c k m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))" 
      using app_controlled_phase_shift_zero[of k m c j] assms zero_def f0 by auto
  next
    assume "v=one" 
    then show "(CR (k-c+1) \<Otimes> Id (m-c-1)) * ((qr c (k-1) m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))) 
             = (qr c k m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))" 
      using app_controlled_phase_shift_one assms zero_def f0 by auto
  qed
qed



lemma SWAP_front_herm_cnj_dual:
  assumes "k\<ge>1" and "(fSWAP k t) * A = B" 
    and "dim_row A = 2^(k+t)" and "dim_col A = 1"
    and "dim_row B = 2^(k+t)" and "dim_col B = 1"
  shows "(fSWAP k t)\<^sup>\<dagger> * B = A" 
proof-
  have "(fSWAP k t)\<^sup>\<dagger> * ((fSWAP k t) * A) = (fSWAP k t)\<^sup>\<dagger> * B" using assms arg_cong by auto
  then have "((fSWAP k t)\<^sup>\<dagger> * (fSWAP k t)) * A = (fSWAP k t)\<^sup>\<dagger> * B" 
    using assoc_mult_mat[of "(fSWAP k t)\<^sup>\<dagger>" "2^(k+t)" "2^(k+t)" "(fSWAP k t)" "2^(k+t)" A 1] assms 
    by (metis SWAP_front_hermite_cnj_dim(1) carrier_matI hermite_cnj_dim_col hermite_cnj_dim_row index_mult_mat(2))
  then have "(1\<^sub>m (2^(k+t))) * A = (fSWAP k t)\<^sup>\<dagger> * B" 
    using assms gate.unitary unitary_def SWAP_front_hermite_cnj_dim SWAP_front_gate 
    by (metis hermite_cnj_dim_row)
  then show "(fSWAP k t)\<^sup>\<dagger> * B = A" by (simp add: assms(3))
qed

lemma SWAP_front_herm_cnj_app:
  fixes k m c::nat 
  assumes "k-c\<ge>1" and "k\<ge>1" and "c\<le>m"  and "m\<ge>k" and "dim_row v = 2" and "dim_col v = 1" 
      and "(\<forall>x \<in> set xs. dim_row x = 2)" and "(\<forall>y \<in> set ys. dim_row y = 2)"
      and "(\<forall>x \<in> set xs. dim_col x = 1)" and "(\<forall>y \<in> set ys. dim_col y = 1)" 
      and "length xs = (k-c-1)" and "length ys = m-k"
  shows "((fSWAP (k-c) (m-k))\<^sup>\<dagger>) * (v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))) 
       = ((pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k)))" 
proof-
  have "(fSWAP (k-c) (m-k)) * ((pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) 
          = v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))" using assms app_fSWAP by auto
  moreover have "dim_row ((pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) = 2^(k-c+(m-k))" 
    by (metis SWAP_front_dim(1) assms(1) calculation dim_row_tensor_mat index_mult_mat(2) mult.commute)
  moreover have "dim_col ((pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) = 1" 
    by (simp add: assms(10) assms(11) assms(12) assms(6) assms(9) pow_tensor_list_dim_col)
  moreover have "dim_row (v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))) = 2^(k-c+(m-k))" 
    by (metis SWAP_front_dim(1) assms(1) calculation(1) index_mult_mat(2))
  moreover have "dim_col (v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))) = 1" 
    using calculation(3) by auto
  ultimately show "((fSWAP (k-c) (m-k))\<^sup>\<dagger>) * (v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))) 
       = ((pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k)))" 
    using SWAP_front_herm_cnj_dual[of "k-c" "m-k" "(pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))"
                                      "v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))"] assms by auto
qed



lemma app_Id_SWAP_front_herm_cnj:
  fixes k c m j::nat
  assumes "k\<ge>2" and "m\<ge>1" and "k\<le>m" 
      and "dim_row v = 2" and "dim_col v = 1" 
      and "c\<ge>1" and "c \<le> k - 1" and "c\<le>m" 
      and "(\<forall>x \<in> set xs. dim_row x = 2)" and "(\<forall>y \<in> set ys. dim_row y = 2)"
      and "(\<forall>x \<in> set xs. dim_col x = 1)" and "(\<forall>y \<in> set ys. dim_col y = 1)" 
      and "length xs = (k-c-1)" and "length ys = m-k"
  shows "(Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * ((qr c k m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k)))
  = (qr c k m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))"
proof-
  have "dim_col (Id 1) = dim_row (qr c k m j)" by (simp add: Id_def qr_def)
  moreover have "dim_col ((fSWAP (k-c) (m-k))\<^sup>\<dagger>) = dim_row (v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k)))" 
    using fSWAP_dim[of k m c] assms pow_tensor_list_dim_row[of xs "(k-c-1)" "2"] pow_tensor_list_dim_row[of ys "m-k" "2"] 
          tensor_mat_is_assoc by auto
  moreover have "dim_col (Id 1) > 0" and "dim_col (qr c k m j) > 0" and "dim_col ((fSWAP (k-c) (m-k))\<^sup>\<dagger>) > 0"
            and "dim_col (v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))) > 0" 
       apply (auto simp: Id_def assms qr_def ) 
       using SWAP_front_dim assms apply auto[1] 
       apply (auto simp: assms pow_tensor_list_dim_col[of xs "(k-(Suc c))"])
       apply (auto simp: assms pow_tensor_list_dim_col[of ys "m-k"]).
  ultimately have "(Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * ((qr c k m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k)))
           = ((Id 1) * (qr c k m j)) \<Otimes> (((fSWAP (k-c) (m-k))\<^sup>\<dagger>) * (v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))))" 
    using mult_distr_tensor tensor_mat_is_assoc by auto
  then have "(Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * ((qr c k m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k)))
           = (qr c k m j) \<Otimes> (((fSWAP (k-c) (m-k))\<^sup>\<dagger>) * (v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))))" 
    using qr_def Id_mult_left by auto
  then have "(Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * ((qr c k m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k)))
           = (qr c k m j) \<Otimes> ( ((pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))))" 
    using SWAP_front_herm_cnj_app assms by auto
  then show "(Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * ((qr c k m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k)))
           = (qr c k m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))"
    using tensor_mat_is_assoc by auto
qed   
 


lemma CR_Id_dim [simp]:
  assumes "k\<ge>1" and "m\<ge>k" and "c \<le> k - 1" and "c\<le>m"  (*Rather c<m*)
  shows "dim_row (CR (k-c+1) \<Otimes> (Id (m-c-1))) = 2^(m-c+1)"
    and "dim_col (CR (k-c+1) \<Otimes> (Id (m-c-1))) = 2^(m-c+1)"
proof-
  have "4 * 2^(m-c-1) = (2::nat)^(m-c+1)" 
    by (smt Suc_le_lessD assms(1) assms(2) assms(3) diff_is_0_eq le_add_diff_inverse le_trans less_or_eq_imp_le mult_2 not_le numeral_Bit0 plus_1_eq_Suc power_add power_eq_if semiring_normalization_rules(16) semiring_normalization_rules(33))
  then show "dim_row (CR (k-c+1) \<Otimes> (Id (m-c-1))) = 2^(m-c+1)"
    using Id_def controlled_phase_shift_def by (smt dim_row_mat(1) dim_row_tensor_mat index_one_mat(2))
next
  have "4 * 2^(m-c-1) = (2::nat)^(m-c+1)" 
    by (smt Suc_le_lessD assms(1) assms(2) assms(3) diff_is_0_eq le_add_diff_inverse le_trans less_or_eq_imp_le mult_2 not_le numeral_Bit0 plus_1_eq_Suc power_add power_eq_if semiring_normalization_rules(16) semiring_normalization_rules(33))
  then show "dim_col (CR (k-c+1) \<Otimes> (Id (m-c-1))) = 2^(m-c+1)"
    by (simp add: Quantum.Id_def controlled_phase_shift_def)
qed







(*------------------------------------------------------------------------------------------------*)
(*-----------------------------------Applying an R\<^sub>k------ ----------------------------------------*)
(*------------------------------------------------------------------------------------------------*)


(*ABBREV DOES NOT WORK*)
(*k is the index of the qubit that should be added to the binary fraction, i.e. the controll qubit. 
c is the current qubit *)
definition CR_on_all::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("CR\<^sub>_ _ _" 75) where
"CR_on_all k c m \<equiv> (Id (c-1)) \<Otimes> ((Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> Id (m-c-1)) * (Id 1 \<Otimes> (fSWAP (k-c) (m-k)))) "

lemma CR_on_all_dim:
  assumes "k-c\<ge>1" and "c\<ge>1" and "m\<ge>k"
  shows "dim_row (CR_on_all k c m) = 2^m"
    and "dim_col (CR_on_all k c m) = 2^m"
proof-
  have "dim_row (CR_on_all k c m) = dim_row (Id (c-1)) * dim_row ((Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)))"
    using CR_on_all_def by auto
  moreover have "2^(c-Suc 0) * (2 * 2^(k+(m-k)-c)) = (2::nat)^m" using assms 
    by (metis (no_types, lifting) One_nat_def Suc_le_eq aux_calculation(1) le_add_diff_inverse semigroup_mult_class.mult.assoc trans_less_add1 zero_less_diff)
  ultimately show "dim_row (CR_on_all k c m) = 2^m"
    using Id_def[of "c-1"] Id_def[of 1] SWAP_front_hermite_cnj_dim[of "k-c" "m-k"] assms by auto
next
  have "dim_col (CR_on_all k c m) = dim_col (Id (c-1)) * dim_col (Id 1 \<Otimes> (fSWAP (k-c) (m-k)))"
    using CR_on_all_def by auto
  moreover have "2^(c-Suc 0) * (2 * 2^(k+(m-k)-c)) = (2::nat)^m" using assms 
    by (metis (no_types, lifting) One_nat_def Suc_le_eq aux_calculation(1) le_add_diff_inverse semigroup_mult_class.mult.assoc trans_less_add1 zero_less_diff)
  ultimately show "dim_col (CR_on_all k c m) = 2^m"
    using Id_def[of "c-1"] Id_def[of 1] SWAP_front_hermite_cnj_dim[of "k-c" "m-k"] assms by auto
qed


lemma [simp]: (*Put into aux calculation*)
  fixes m k::nat
  assumes "m>k" and "k\<ge>1"
  shows "2 * ((2::nat) ^ (m - k) * 2 ^ (k - Suc 0)) = 2 ^ m"  
  by (metis Nat.add_diff_assoc One_nat_def add.commute assms(1) assms(2) less_imp_le_nat not_less_eq_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse power_add power_eq_if)



(*"c \<le> k - 1" Put this everywhere or put 1 \<le> k - c everywhere seems to cause a lot of problems *)
lemma app_CR_on_all_wo_Id:
  fixes k c m j::nat
  assumes "k\<ge>2" and "m\<ge>1" and "k\<le>m" and "dim_row v = 2" and "dim_col v = 1" 
      and "c\<ge>1" and "c \<le> k - 1" and "c\<le>m" 
      and "v = zero \<or> v = one"
      and "v = zero \<longrightarrow> ((bin_rep m j)!(k-1)) = 0"
      and "v = one \<longrightarrow>  ((bin_rep m j)!(k-1)) = 1" 
      and "(\<forall>x \<in> set xs. dim_row x = 2)" and "(\<forall>y \<in> set ys. dim_row y = 2)"
      and "(\<forall>x \<in> set xs. dim_col x = 1)" and "(\<forall>y \<in> set ys. dim_col y = 1)" 
      and "length xs = (k-c-1)" and "length ys = m-k"
  shows "((Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> (Id (m-c-1))) * (Id 1 \<Otimes> (fSWAP (k-c) (m-k))))
        * ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) 
        = (qr c k m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))"
proof-
  have f0: "1 \<le> k - c \<and> 1 \<le> k" using assms 
    by (metis Nat.diff_diff_right diff_add_inverse diff_le_self le_diff_iff' le_trans)
  have "((Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> (Id (m-c-1))) * (Id 1 \<Otimes> (fSWAP (k-c) (m-k))))
        * ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) 
        = (Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> (Id (m-c-1))) * ((Id 1 \<Otimes> (fSWAP (k-c) (m-k)))
        * ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))))" 
  proof-
    have "(Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> Id (m-c-1)) \<in> carrier_mat (2^(m-c+1)) (2^(m-c+1))" 
      using Id_fSWAP_herm_cnj_dim[of k m c] CR_Id_dim[of k m c] assms f0 by (metis carrier_matI index_mult_mat(2) index_mult_mat(3))
    moreover have "(Id 1 \<Otimes> (fSWAP (k-c) (m-k))) \<in> carrier_mat (2^(m-c+1)) (2^(m-c+1))"
      using Id_fSWAP_dim[of k m c] assms using f0 by blast       
    moreover have "((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) \<in> carrier_mat (2^(m-c+1)) 1" 
    proof- 
      have "dim_row (pw xs (k-c-1)) = 2^(k-c-1)"  
        using pow_tensor_list_dim_row[of xs "(k-c-1)" 2] assms(12) assms(16) by blast
      moreover have "dim_row (pw ys (m-k)) = 2^(m-k)" using pow_tensor_list_dim_row[of ys "m-k" 2] assms(13) assms(17) by blast
      moreover have "2 * (2 ^ (m - k) * 2 ^ (k - Suc c)) = (2::nat) ^ (m - c)" 
        using assms(3) assms (7) f0 
        by (metis Nat.add_diff_assoc2 add.commute diff_diff_left le_SucI ordered_cancel_comm_monoid_diff_class.add_diff_inverse 
            plus_1_eq_Suc power_add power_commutes semiring_normalization_rules(19) semiring_normalization_rules(28))
      ultimately have "dim_row ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) = 2^(m-c+1)" 
        using assms qr_def aux_calculation(6)[of k c m] by auto
      moreover have "dim_col ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) = 1" 
        using pow_tensor_list_dim_col[of xs "(k-c-1)"] pow_tensor_list_dim_col[of ys "m-k"]
          qr_def assms by auto
      ultimately show ?thesis by blast
    qed
    ultimately show ?thesis 
      using assoc_mult_mat[of "(Id 1 \<Otimes> ((fSWAP k (m-k))\<^sup>\<dagger>)) * (CR k \<Otimes> (Id (m-c)))" "2^(m+1)" "2^(m+1)"
            "(Id 1 \<Otimes> (fSWAP k (m-k)))" "2^(m+1)" "((qr c k m j) \<Otimes> (pw xs (k-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) " "1"]
          assms by auto
  qed
  then have "((Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> (Id (m-c-1))) * (Id 1 \<Otimes> (fSWAP (k-c) (m-k))))
        * ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) 
     = (Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> (Id (m-c-1))) * ((qr c (k-1) m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))) "
    using app_Id_fSWAP[of k m c v xs ys] assms tensor_mat_is_assoc by auto
  moreover have "(Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> (Id (m-c-1))) * ((qr c (k-1) m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k)))
              = (Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * ((CR (k-c+1) \<Otimes> (Id (m-c-1))) * ((qr c (k-1) m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))))"
  proof-
    have "(Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) \<in> carrier_mat (2^(m-c+1)) (2^(m-c+1))" 
      using Id_fSWAP_herm_cnj_dim assms f0 by auto
    moreover have "(CR (k-c+1) \<Otimes> (Id (m-c-1))) \<in> carrier_mat (2^(m-c+1)) (2^(m-c+1))" 
      using CR_Id_dim assms by auto
    moreover have "((qr c (k-1) m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))) \<in> carrier_mat (2^(m-c+1)) 1"
    proof-
      have "dim_row ((qr c (k-1) m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))) = (2^(m-c+1))"
        using assms qr_def pow_tensor_list_dim_row[of xs "k-c-1" 2] pow_tensor_list_dim_row[of ys "m-k" 2] f0 by auto 
      moreover have "dim_col ((qr c (k-1) m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))) = 1"
        using assms qr_def pow_tensor_list_dim_col[of xs "k-c-1"] pow_tensor_list_dim_col[of ys "m-k"] f0 by auto 
      ultimately show ?thesis by auto
    qed
    ultimately show ?thesis by auto
  qed
  ultimately have "((Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> (Id (m-c-1))) * (Id 1 \<Otimes> (fSWAP (k-c) (m-k))))
        * ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) 
     = (Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * ((CR (k-c+1) \<Otimes> (Id (m-c-1))) * ((qr c (k-1) m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))))"
    by auto
  moreover have "(CR (k-c+1) \<Otimes> Id (m-c-1)) * ((qr c (k-1) m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))) 
        = (qr c k m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))" 
    using CR_on_all_Id[of k m v c j xs ys] assms by auto
  ultimately have "((Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> (Id (m-c-1))) * (Id 1 \<Otimes> (fSWAP (k-c) (m-k))))
                 * ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) 
                 = (Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * ((qr c k m j) \<Otimes> v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k)))" 
    by auto
  then show "((Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> (Id (m-c-1))) * (Id 1 \<Otimes> (fSWAP (k-c) (m-k))))
                 * ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) 
                 = ((qr c k m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k)))" 
    using assms f0 app_Id_SWAP_front_herm_cnj by auto
qed



lemma app_CR_on_all:
   fixes k c m j::nat
  assumes "k\<ge>2" and "m\<ge>1" and "k\<le>m" and "dim_row v = 2" and "dim_col v = 1" 
      and "c\<ge>1" and "c \<le> k - 1" and "c\<le>m" 
      and "v = zero \<or> v = one"
      and "v = zero \<longrightarrow> ((bin_rep m j)!(k-1)) = 0"
      and "v = one \<longrightarrow>  ((bin_rep m j)!(k-1)) = 1" 
      and "(\<forall>x \<in> set xs. dim_row x = 2)" and "(\<forall>y \<in> set ys. dim_row y = 2)"
      and "(\<forall>x \<in> set xs. dim_col x = 1)" and "(\<forall>y \<in> set ys. dim_col y = 1)" 
      and "(\<forall>c \<in> set cs. dim_row c = 2)" and "(\<forall>c \<in> set cs. dim_col c = 1)" 
      and "length xs = (k-c-1)" and "length ys = m-k" and "length cs = c-1"
  shows "(CR_on_all k c m) * ((pw cs (c-1)) \<Otimes> (qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) 
       = ((pw cs (c-1)) \<Otimes> (qr c k m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k)))"
proof-
  have "(CR_on_all k c m) * ((pw cs (c-1)) \<Otimes> (qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) 
       = (Id (c-1) \<Otimes> (Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> Id (m-c-1)) * (Id 1 \<Otimes> (fSWAP (k-c) (m-k))))
       * ((pw cs (c-1)) \<Otimes> (qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k)))" 
    using CR_on_all_def[of k c m] by auto
  then have "(CR_on_all k c m) * ((pw cs (c-1)) \<Otimes> (qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) 
       = (Id (c-1) \<Otimes> ((Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> Id (m-c-1)) * (Id 1 \<Otimes> (fSWAP (k-c) (m-k)))))
       * ((pw cs (c-1)) \<Otimes> ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))))" 
    using tensor_mat_is_assoc by auto
  moreover have "(Id (c-1) \<Otimes> ((Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> Id (m-c-1)) * (Id 1 \<Otimes> (fSWAP (k-c) (m-k)))))
       * ((pw cs (c-1)) \<Otimes> ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))))
       = (Id (c-1) * pw cs (c-1)) 
      \<Otimes> ( ((Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> Id (m-c-1)) * (Id 1 \<Otimes> (fSWAP (k-c) (m-k)))) 
         * ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) )" 
  proof- 
    have "dim_col (Id (c-1)) = dim_row (pw cs (c-1))" 
      using Id_def pow_tensor_list_dim_row[of cs "c-1" 2] assms by auto
    moreover have "dim_col ((Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> Id (m-c-1)) * (Id 1 \<Otimes> (fSWAP (k-c) (m-k)))) 
        = dim_row ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k)))" 
    proof-
      have "dim_col ((Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> Id (m-c-1)) * (Id 1 \<Otimes> (fSWAP (k-c) (m-k))))
          = dim_col (Id 1 \<Otimes> (fSWAP (k-c) (m-k)))" by auto
      moreover have "dim_col (Id 1 \<Otimes> (fSWAP (k-c) (m-k))) = 2^(m-c+1)"
        using Id_def fSWAP_dim assms by auto
      moreover have " 2 ^ (k - Suc c) * (2 * 2 ^ (m - k)) = (2::nat) ^ (m - c) " 
        using  assms(1) assms(3) assms(7) assms(8) aux_calculation(4)
        by (smt Suc_1 Suc_diff_le add_leD1 cancel_comm_monoid_add_class.diff_cancel diff_Suc_1 le_neq_implies_less le_numeral_extra(4) less_imp_le_nat plus_1_eq_Suc semigroup_mult_class.mult.assoc zero_less_diff)
      moreover have "dim_row ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) = 2^(m-c+1)"
        using qr_def pow_tensor_list_dim_row[of xs "k-c-1" 2] pow_tensor_list_dim_row[of ys "m-k" 2] assms(18-20) 
        assms(12-13) assms(9) calculation by auto
      ultimately show ?thesis by auto
    qed
    moreover have "dim_col (Id (c-1)) > 0" and "dim_col (pw cs (c-1)) > 0" and 
                  "dim_col ((Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> Id (m-c-1)) * (Id 1 \<Otimes> (fSWAP (k-c) (m-k)))) > 0" and
                  "dim_col ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) > 0" sorry
    ultimately show ?thesis 
      using mult_distr_tensor[of "(Id (c-1))" "(pw cs (c-1))" 
            "((Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> Id (m-c-1)) * (Id 1 \<Otimes> (fSWAP (k-c) (m-k))))"
            "((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k)))"] by auto
  qed
  moreover have "(Id (c-1) * pw cs (c-1)) = pw cs (c-1)" 
    using Id_mult_left[of "pw cs (c-1)" "(c-1)"] pow_tensor_list_dim_row[of cs "c-1" 2] assms by auto
  ultimately have "(CR_on_all k c m) * ((pw cs (c-1)) \<Otimes> (qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) 
       =  pw cs (c-1) 
      \<Otimes> ( ((Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> Id (m-c-1)) * (Id 1 \<Otimes> (fSWAP (k-c) (m-k)))) 
         * ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) )" 
    by auto
  moreover have "((Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> (Id (m-c-1))) * (Id 1 \<Otimes> (fSWAP (k-c) (m-k))))
        * ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) 
        = (qr c k m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))" 
    using app_CR_on_all_wo_Id[of k m v c j xs ys ] apply (auto simp: assms) 
    by (metis One_nat_def assms(10) assms(11) assms(6) assms(7) assms(9))
  ultimately show "(CR_on_all k c m) * ((pw cs (c-1)) \<Otimes> (qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) 
       =  pw cs (c-1) \<Otimes> (qr c k m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))"
    using tensor_mat_is_assoc by auto
qed



lemma CR_on_all_j:
 fixes n c m j::nat
 assumes "j < 2^m" and "n\<le>m" and "c\<le>m" and "c<n" and "m\<ge>c+1"
     and "n\<ge>2" and "m\<ge>1" and "c\<ge>1"
  shows 
 "(CR_on_all n c m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (n-1) m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))
= ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c n m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
proof-
  have f0: "(j\<Otimes> (c+1) (m-c) m j) = (j\<Otimes> (c+1) (n-(c+1)) m j) \<Otimes> (j\<Otimes> n 1 m j) \<Otimes> (j\<Otimes> (n+1) (m-n) m j)"
  proof(rule disjE)
    show "n<m \<or> n=m" using assms by auto
  next
     assume a0: "n<m"
     moreover have "n + 1 - (c + 1) \<le> m - c" using assms by simp
     moreover have "c + 1 + (m - c) - 1 \<le> m" using assms a0 by simp
     ultimately have "(j\<Otimes> (c+1) (m-c) m j) = (j\<Otimes> (c+1) ((n+1)-(c+1)-1) m j) \<Otimes> (j\<Otimes> (n+1-1) 1 m j) \<Otimes> (j\<Otimes> (n+1) ((m-c)-((n+1)-(c+1))) m j)"  
       using j_to_tensor_prod_decomp_middle[of j m "c+1" "n+1" "m-c"] assms a0 by auto
     moreover have "(m-c)-((n+1)-(c+1)) = m-n" using assms by auto
     ultimately show ?thesis by auto
   next
     assume a0: "n=m" 
     moreover have f0: "(c+1)+(m-c-1)-1 < m" using assms by auto
     then have "(j\<Otimes> (c+1) (m-c) m j) = (j\<Otimes> (c+1) (m-c-1) m j) \<Otimes> (j\<Otimes> ((c+1)+(m-c-1)) 1 m j)" 
       using assms j_to_tensor_prod_decomp_right[of j m "c+1" "m-c-1"] by auto
     moreover have "((c+1)+(m-c-1)) = m" using f0 add.left_commute add_diff_cancel_left by linarith
     ultimately have "(j\<Otimes> (c+1) (m-c) m j) = (j\<Otimes> (c+1) (n-(c+1)) m j) \<Otimes> (j\<Otimes> n 1 m j)" by auto
     moreover have "(j\<Otimes> (n+1) (m-n) m j) = (Id 0)" using a0 by simp
     ultimately show ?thesis by (simp add: Id_right_tensor)
   qed
  then have "(CR_on_all n c m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (n-1) m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))
= (CR_on_all n c m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (n-1) m j) \<Otimes> (j\<Otimes> (c+1) (n-(c+1)) m j) \<Otimes> (j\<Otimes> n 1 m j) \<Otimes> (j\<Otimes> (n+1) (m-n) m j))"
    using tensor_mat_is_assoc by auto
  moreover have "(CR_on_all n c m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (n-1) m j) \<Otimes> (j\<Otimes> (c+1) (n-(c+1)) m j) \<Otimes> (j\<Otimes> n 1 m j) \<Otimes> (j\<Otimes> (n+1) (m-n) m j))
= ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c n m j) \<Otimes> (j\<Otimes> (c+1) (n-(c+1)) m j) \<Otimes> (j\<Otimes> n 1 m j) \<Otimes> (j\<Otimes> (n+1) (m-n) m j))"
  proof-
    have "(CR_on_all n c m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (n-1) m j) 
    \<Otimes> (pw (j_to_list_bound (c+1) (n-(c+1)) m j) (n-c-1)) 
    \<Otimes> (pw (j_to_list_bound n 1 m j) 1) 
    \<Otimes> (pw (j_to_list_bound (n+1) (m-n) m j) (m-n)))
    =  (pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c n m j) 
    \<Otimes> (pw (j_to_list_bound (c+1) (n-(c+1)) m j) (n-c-1))  
    \<Otimes> (pw (j_to_list_bound n 1 m j) 1) 
    \<Otimes> (pw (j_to_list_bound (n+1) (m-n) m j) (m-n))"
    proof-
      have "2 \<le> n \<and> 1 \<le> m \<and> n \<le> m \<and> 1 \<le> c \<and> c \<le> n - 1 \<and> c \<le> m " using assms by auto
      moreover have "dim_row (pw (j_to_list_bound n 1 m j) 1) = 2" 
                and "dim_col (pw (j_to_list_bound n 1 m j) 1) = 1" using pow_tensor_list_one by auto
      moreover have "length [qr (nat i) m m j. i<-[1..(c-1)]] = c-1" by simp
      moreover have "(\<forall>x \<in> set (j_to_list_bound (c+1) (n-(c+1)) m j). dim_row x = 2)" using j_to_list_bound_dim_row by blast
      moreover have "(\<forall>x \<in> set (j_to_list_bound (c+1) (n-(c+1)) m j). dim_col x = 1)" using j_to_list_bound_dim_col by blast
      moreover have "length (j_to_list_bound (c+1) (n-(c+1)) m j) = n-c-1" by (simp add: j_to_list_bound_length)
      moreover have "(\<forall>y \<in> set (j_to_list_bound (n+1) (m-n) m j). dim_row y = 2)" using j_to_list_bound_dim_row by blast
      moreover have "(\<forall>y \<in> set (j_to_list_bound (n+1) (m-n) m j). dim_col y = 1)" using j_to_list_bound_dim_col by blast
      moreover have "length (j_to_list_bound (n+1) (m-n) m j) = m-n" by (simp add: j_to_list_bound_length)
      moreover have "(pw (j_to_list_bound n 1 m j) 1) = zero \<or> (pw (j_to_list_bound n 1 m j) 1) = one" using pow_tensor_list_one by auto
      moreover have "(pw (j_to_list_bound n 1 m j) 1) = zero \<longrightarrow> bin_rep m j ! (n - 1) = 0" 
        using j_to_tensor_bin_rep_zero j_to_tensor_prod_def assms by auto 
      moreover have "(pw (j_to_list_bound n 1 m j) 1) = one \<longrightarrow> bin_rep m j ! (n - 1) = 1" 
        using j_to_tensor_bin_rep_one j_to_tensor_prod_def assms(1-2) assms by auto 
      moreover have " (\<forall>c\<in>set (map (\<lambda>i. qr (nat i) m m j) [1..int (c - 1)]). dim_row c = 2)"
        using qr_def sorry
      moreover have 
        "(\<forall>c\<in>set (map (\<lambda>i. qr (nat i) m m j) [1..int (c - 1)]). dim_col c = 1)" using qr_def assms(7) sorry
      ultimately show ?thesis
        using app_CR_on_all[of n m "(pw (j_to_list_bound n 1 m j) 1)" c j "(j_to_list_bound (c+1) (n-(c+1)) m j)"
                                   "(j_to_list_bound (n+1) (m-n) m j)" "[qr (nat i) m m j. i<-[1..(c-1)]]"] 
        by blast   
    qed
    then have "(CR_on_all n c m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (n-1) m j) 
    \<Otimes> (pw (j_to_list_bound (c+1) (n-(c+1)) m j) (n-(c+1))) 
    \<Otimes> (pw (j_to_list_bound n 1 m j) 1) 
    \<Otimes> (pw (j_to_list_bound (n+1) (m-n) m j) (m-n)))
    =  (pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c n m j) 
    \<Otimes> (pw (j_to_list_bound (c+1) (n-(c+1)) m j) (n-(c+1)))  
    \<Otimes> (pw (j_to_list_bound n 1 m j) 1) 
    \<Otimes> (pw (j_to_list_bound (n+1) (m-n) m j) (m-n))" by auto
    moreover have "(j\<Otimes> (c+1) (n-(c+1)) m j) = (pw (j_to_list_bound (c+1) (n-(c+1)) m j) (n-(c+1)))" 
      using j_to_tensor_prod_def by auto
    moreover have "(j\<Otimes> n 1 m j) = (pw (j_to_list_bound n 1 m j) 1) " 
      using j_to_tensor_prod_def by auto
    moreover have "(j\<Otimes> (n+1) (m-n) m j) =(pw (j_to_list_bound (n+1) (m-n) m j) (m-n))"       
      using j_to_tensor_prod_def by auto
    ultimately show ?thesis by auto
  qed
ultimately have "(CR_on_all n c m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (n-1) m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))
=((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c n m j) \<Otimes> (j\<Otimes> (c+1) (n-(c+1)) m j) \<Otimes> (j\<Otimes> n 1 m j) \<Otimes> (j\<Otimes> (n+1) (m-n) m j))"
  by auto
then have "(CR_on_all n c m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (n-1) m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))
=((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c n m j) \<Otimes> ((j\<Otimes> (c+1) (n-(c+1)) m j) \<Otimes> (j\<Otimes> n 1 m j) \<Otimes> (j\<Otimes> (n+1) (m-n) m j)))"
  using tensor_mat_is_assoc by auto
then show "(CR_on_all n c m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (n-1) m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))
=((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c n m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
  using f0 by auto
qed






(*TODO Is the order of c and k different from other proofs? If so rename to avoid confusion.*)
(*Could go into generic mult function would be more confusing to understand though*)
(*c is the current qubit k=(n-c) ensures that R_2 to R_(n-c+1) are applied to the qubit with the 
special case for c=n that nothing is applied. *)
fun all_CR:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("aCR _ _ _" 75) where
  "(aCR c 0 m) = (Id m)"  
| "(aCR c (Suc k) m) = (CR_on_all (c+(Suc k)) c m) * (aCR c k m)"


lemma all_CR_dim:
  assumes "c\<le>m" and "1 \<le> c"
  shows "c + k \<le> m \<longrightarrow> dim_row (aCR c k m) = 2^m \<and> dim_col (aCR c k m) = 2^m"
proof(induction k)
  show "c + 0 \<le> m \<longrightarrow> dim_row (aCR c 0 m) = 2^m \<and> dim_col (aCR c 0 m) = 2^m"
    using Id_def by auto
next
  fix k
  assume IH: "c + k \<le> m \<longrightarrow> dim_row (aCR c k m) = 2^m \<and> dim_col (aCR c k m) = 2^m"
  have "c + (Suc k) \<le> m \<longrightarrow> dim_row (aCR c (Suc k) m) = 2^m"
  proof
    assume a0: "c + (Suc k) \<le> m"
    have "dim_row (aCR c (Suc k) m) = dim_row (CR_on_all (c+(Suc k)) c m)" by auto
    moreover have " 1 \<le> c + Suc k - c \<and> 1 \<le> c \<and> c + Suc k \<le> m" using assms a0 by auto
    ultimately show "dim_row (aCR c (Suc k) m) = 2^m" 
      using CR_on_all_dim[of "c+(Suc k)" c m] assms by auto
  qed
  moreover have "c + (Suc k) \<le> m \<longrightarrow> dim_col (aCR c (Suc k) m) = 2^m"
  proof
    assume a0: "c + (Suc k) \<le> m"
    have "dim_col (aCR c (Suc k) m) = dim_col (aCR c k m)" by auto
    moreover have "c + k \<le> m" using a0 by auto
    ultimately show "dim_col (aCR c (Suc k) m) = 2^m" 
      using CR_on_all_dim[of "c+(Suc k)" c m] assms IH by auto
  qed
  ultimately show "c + (Suc k) \<le> m \<longrightarrow> dim_row (aCR c (Suc k) m) = 2^m \<and> dim_col (aCR c (Suc k) m) = 2^m"
    by auto
qed

lemma all_CR_app_aux:
  fixes c m j n::nat
  assumes "c\<ge>1" and "c+1\<le>m" and "n\<ge>c" and "j<2^m" and "n\<ge>1" and "m\<ge>1"
  shows "n\<le>m \<longrightarrow> aCR c (n-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
        = ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c n m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
proof(rule Nat.nat_induct_at_least[of c n])
  show "c\<le>n" using assms by auto
next
  show "c\<le>m \<longrightarrow> aCR c (c-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
        = ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
  proof
    assume a0: "c\<le>m"
    then have "aCR c (c-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
            = (Id m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
      by auto
    moreover have "dim_row ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))
                  = 2^m" 
      using qr_def j_to_tensor_prod_def sorry
    ultimately show  "aCR c (c-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
            = ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
      using Id_mult_left by auto
  qed
next
  fix n 
  assume a0: "n\<ge>c"
  assume IH: "n\<le>m \<longrightarrow> aCR c (n-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
        = ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c n m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
  show "(Suc n)\<le>m \<longrightarrow> aCR c ((Suc n)-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
        = ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (Suc n) m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
  proof
    assume a1: "(Suc n)\<le>m"
    have " aCR c ((Suc n)-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
        =  ((CR_on_all (Suc n) c m) * (aCR c (n-c) m)) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) "
      by (simp add: Suc_diff_le a0)
    then have " aCR c ((Suc n)-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
        =  (CR_on_all (Suc n) c m) * ((aCR c (n-c) m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))) "
      sorry
    then have " aCR c ((Suc n)-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
        =  (CR_on_all (Suc n) c m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (Suc n - 1) m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) "
      using a1 IH by auto
    moreover have "c < Suc n " by (simp add: a0 less_Suc_eq_le)
    ultimately show " aCR c ((Suc n)-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
        = ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (Suc n) m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) "
      using CR_on_all_j[of j m "Suc n" c] a1 assms by (smt Suc_le_mono a0 add_leD1 le_trans one_add_one plus_1_eq_Suc)
  qed
qed

lemma all_CR_app:
  fixes c m j::nat 
  assumes "c\<ge>1" and "c+1\<le>m" and "c\<le>m" and "j<2^m" and "m\<ge>1"
  shows "aCR c (m-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
        = ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c m m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
  using all_CR_app_aux[of c m m j] assms by auto





(*Apply the H gate to the current qubit then apply R_2 to R_(m-c)*)
definition all_gates_on_single_qubit:: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("G _ _" 75)  where
 "G c m = aCR c (m-c) m * (Id (c-1) \<Otimes> H \<Otimes> Id (m-c))"  

lemma G_dim:
  fixes c m::nat
  assumes "c\<le>m" and "c\<ge>1"  
  shows "dim_row (G c m) = 2^m"
    and "dim_col (G c m) = 2^m" 
proof-
  have "dim_row (G c m) = dim_row (aCR c (m-c) m )" using all_gates_on_single_qubit_def by auto
  moreover have "c + (m - c) \<le> m" by (simp add: assms(1))
  ultimately show "dim_row (G c m) = 2^m" using all_CR_dim[of c m "m-c"] assms by auto
next
  have "dim_col (G c m) = dim_col (Id (c-1) \<Otimes> H \<Otimes> Id (m-c))" using all_gates_on_single_qubit_def by auto
  moreover have "2^(c-1) * 2 * 2^(m-c) = (2::nat)^m" using assms(1) assms(2) by auto (*Put in aux_calculation*)
  then show "dim_col (G c m) = 2^m" using Id_def by (simp add: H_without_scalar_prod calculation)
qed


lemma app_H_zero: (*Do again with k-1?*)
  assumes "((bin_rep m jd)!k) = 0"
    shows "H * zero = (qr (k+1) (k+1) m jd)" 
proof
  fix i j::nat
  assume "i < dim_row (qr (k+1) (k+1) m jd)" and "j < dim_col (qr (k+1) (k+1) m jd)"
  then have f0: "i \<in> {0,1} \<and> j = 0" using qr_def by auto 
  then have "(H * zero) $$ (i,j) = (\<Sum>k<dim_row zero. (H $$ (i,k)) * (zero $$ (k,0)))" 
    apply (simp add: H_without_scalar_prod) by fastforce
  then have f1: "(H * zero) $$ (i,j) = (H $$ (i,0)) * (zero $$ (0,0)) + (H $$ (i,1)) * (zero $$ (1,0))"
    using zero_def set_2 by (simp add: lessThan_atLeast0)
  moreover have "i=0 \<longrightarrow> (qr (k+1) (k+1) m jd) $$ (i,j) = (1::complex)/sqrt(2)"
    using qr_def f0 by auto
  moreover have "i=1 \<longrightarrow> (qr (k+1) (k+1) m jd) $$ (i,j) = (exp (complex_of_real (2*pi)*\<i>*(bf k k m jd)))*1/sqrt(2)"
    using qr_def f0 by auto
  moreover have "i=0 \<longrightarrow> (H * zero) $$ (i,j) = (1::complex)/sqrt(2)" 
    using f0 f1 apply auto apply (auto simp: H_without_scalar_prod).
  moreover have "i=1 \<longrightarrow> (H * zero) $$ (i,j) = (1::complex)/sqrt(2)" 
    using f0 f1 apply auto apply (auto simp: H_without_scalar_prod).
  moreover have "(exp (complex_of_real (2*pi)*\<i>*(bf k k m jd)))*1/sqrt(2) = (1::complex)/sqrt(2)"
  proof-
    have "(bf k k m jd) = 0"
      using binary_fraction_def assms by auto
    then have "(exp (complex_of_real (2*pi)*\<i>*(bf k k m jd))) = 1" by auto
    then show ?thesis by auto
  qed
  ultimately show "(H * zero) $$ (i,j) = (qr (k+1) (k+1) m jd) $$ (i,j)" 
    by (metis One_nat_def f0 lessThan_atLeast0 lessThan_iff less_2_cases set_2)
next
  show "dim_row (H * zero) = dim_row (qr (k+1) (k+1) m jd)" 
    by (simp add: H_without_scalar_prod qr_def)
next
  show "dim_col (H * zero) = dim_col (qr (k+1) (k+1) m jd)" 
    by (simp add: H_without_scalar_prod qr_def)
qed

lemma app_H_one: (*Do again with k-1?*)
  assumes "((bin_rep m jd)!k) = 1"
    shows "H * one = (qr (k+1) (k+1) m jd)" 
proof
  fix i j::nat
  assume a0: "i < dim_row (qr (k+1) (k+1) m jd)" and "j < dim_col (qr (k+1) (k+1) m jd)"
  then have f0: "i \<in> {0,1} \<and> j = 0" using qr_def by auto 
  then have "(H * one) $$ (i,j) = (\<Sum>k<dim_row one. (H $$ (i,k)) * (one $$ (k,0)))" 
    apply (simp add: H_without_scalar_prod) by fastforce
  then have f1: "(H * one) $$ (i,j) = (H $$ (i,0)) * (one $$ (0,0)) + (H $$ (i,1)) * (one $$ (1,0))" 
    using zero_def set_2 by (simp add: lessThan_atLeast0)
  moreover have "i=0 \<longrightarrow> (qr (k+1) (k+1) m jd) $$ (i,j) = (1::complex)/sqrt(2)"
    using qr_def f0 by auto
  moreover have "i=1 \<longrightarrow> (qr (k+1) (k+1) m jd) $$ (i,j) = (exp (complex_of_real (2*pi)*\<i>*(bf k k m jd)))*1/sqrt(2)"
    using qr_def f0 by auto
  moreover have "i=0 \<longrightarrow> (H * one) $$ (i,j) = 1/sqrt(2)" 
    using f0 f1 apply auto apply (auto simp: H_without_scalar_prod).
  moreover have "i=1 \<longrightarrow> (H * one) $$ (i,j) = -1/sqrt(2)" 
    using f0 f1 apply auto apply (auto simp: H_without_scalar_prod).
  moreover have "(exp (complex_of_real (2*pi)*\<i>*(bf k k m jd)))*1/sqrt(2) = -1/sqrt(2)"
  proof-
    have "(bf k k m jd) = 1/2"
      using binary_fraction_def assms by auto
    then have "(exp (complex_of_real (2*pi)*\<i>*(bf k k m jd))) = -1" 
      by (simp add: \<open>bf k k m jd = 1 / 2\<close>)
    then show ?thesis by auto
  qed
  ultimately show "(H * one) $$ (i,j) = (qr (k+1) (k+1) m jd) $$ (i,j)" 
    by (metis (no_types, lifting) One_nat_def a0 dim_row_mat(1) less_2_cases of_real_divide of_real_hom.hom_one qr_def)
next
  show "dim_row (H * one) = dim_row (qr (k+1) (k+1) m jd)" 
    by (simp add: H_without_scalar_prod qr_def)
next
  show "dim_col (H * one) = dim_col (qr (k+1) (k+1) m jd)" 
    by (simp add: H_without_scalar_prod qr_def)
qed

lemma app_H:
  assumes "c\<ge>1" and "v=zero \<or> v=one"  
      and "v = zero \<longrightarrow> ((bin_rep m jd)!(c-1)) = 0"
      and "v = one \<longrightarrow>  ((bin_rep m jd)!(c-1)) = 1" 
    shows "H * v = (qr c c m jd)"  using  app_H_zero assms app_H_one by auto

lemma app_H_all:
  assumes "c\<ge>1" and "m\<ge>c" and "j < 2 ^ m" 
  shows "(Id (c-1) \<Otimes> H \<Otimes> Id (m-c)) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (j\<Otimes> c (m-c+1) m j))
= ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
proof-
  have "(Id (c-1) \<Otimes> H \<Otimes> Id (m-c)) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (j\<Otimes> c (m-c+1) m j))
  = Id (c-1) * (pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) 
  \<Otimes> (H \<Otimes> Id (m-c)) * (j\<Otimes> c (m-c+1) m j)"
  proof-
    have "dim_col (Id (c-1)) = dim_row (pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1))"
      using Id_def pow_tensor_list_dim_row[of "[qr (nat i) m m j. i<-[1..(c-1)]]" "c-1" 2] qr_def by auto
    moreover have "dim_col (H \<Otimes> Id (m-c)) = dim_row (j\<Otimes> c (m-c+1) m j)"
      using Id_def[of "m-c"] j_to_tensor_prod_dim_row[of c "m-c+1" m j] by (simp add: H_without_scalar_prod)
    moreover have "dim_col (Id (c-1)) > 0" using Id_def by auto
    moreover have "dim_col H > 0" by (simp add: H_without_scalar_prod)
    moreover have "dim_col (j\<Otimes> c (m-c+1) m j) > 0" using j_to_tensor_prod_dim_col[of c "m-c+1" m j] by auto
    moreover have "dim_col (pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) > 0"
      using pow_tensor_list_dim_col qr_def by auto
    ultimately show ?thesis using tensor_mat_is_assoc j_to_tensor_prod_dim_row mult_distr_tensor pos2 by presburger
  qed
  then have "(Id (c-1) \<Otimes> H \<Otimes> Id (m-c)) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (j\<Otimes> c (m-c+1) m j))
  = (pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (H \<Otimes> Id (m-c)) * (j\<Otimes> c (m-c+1) m j)"
    using Id_mult_left pow_tensor_list_dim_row[of "[qr (nat i) m m j. i<-[1..(c-1)]]" "c-1" 2] qr_def by auto
  moreover have f1: "v = zero \<or> v=one \<longrightarrow> (H \<Otimes> Id (m-c)) * (v \<Otimes> j\<Otimes> (c+1) (m-c) m j) = (H * v) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)" for v 
  proof
    assume a0: "v = zero \<or> v=one"
    then have "dim_col H = dim_row v" by (smt H_without_scalar_prod dim_col_mat(1) dim_row_mat(1))
    moreover have "dim_col (Id (m-c)) = dim_row (j\<Otimes> (c+1) (m-c) m j)" 
      using Id_def by (simp add: j_to_tensor_prod_dim_row)
    moreover have "dim_col H > 0" and "dim_col (Id (m-c)) > 0" and "dim_col (j\<Otimes> (c+1) (m-c) m j) > 0" 
              and "dim_col v > 0"
         apply (simp add: H_without_scalar_prod)
        apply (simp add: Id_def)
       apply (simp add: j_to_tensor_prod_dim_col)
      using a0 by auto
    ultimately have "(H \<Otimes> Id (m-c)) * (v \<Otimes> j\<Otimes> (c+1) (m-c) m j) = (H * v) \<Otimes> (Id (m-c) * j\<Otimes> (c+1) (m-c) m j)"
      using mult_distr_tensor by auto
    then show "(H \<Otimes> Id (m-c)) * (v \<Otimes> j\<Otimes> (c+1) (m-c) m j) = (H * v) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)"
      using Id_mult_left j_to_tensor_prod_dim_row by auto
  qed
  moreover have "(H \<Otimes> Id (m-c)) * (j\<Otimes> c (m-c+1) m j) = qr c c m j \<Otimes> (j\<Otimes> (c+1) (m-c) m j)"
  proof(rule disjE)
    show "(bin_rep m j)!(c-1) = 0 \<or> (bin_rep m j)!(c-1) = 1" using bin_rep_coeff[of j m "c-1"] assms by auto
  next
    assume a0: "(bin_rep m j)!(c-1) = 1"
    then have "(j\<Otimes> c (m-c+1) m j) = one \<Otimes> (j\<Otimes> (c+1) (m-c) m j)"
      using j_to_tensor_prod_decomp_left_one assms a0 by auto
    then have "(H \<Otimes> Id (m-c)) * (j\<Otimes> c (m-c+1) m j) = (H * one) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)" 
      using f1 by simp
    then show "(H \<Otimes> Id (m-c)) * (j\<Otimes> c (m-c+1) m j) = (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)" 
      using a0 app_H_one assms(1) by auto
  next
    assume a0: "(bin_rep m j)!(c-1) = 0"
    then have "(j\<Otimes> c (m-c+1) m j) = zero \<Otimes> (j\<Otimes> (c+1) (m-c) m j)"
      using j_to_tensor_prod_decomp_left_zero assms a0 by auto
    then have "(H \<Otimes> Id (m-c)) * (j\<Otimes> c (m-c+1) m j) = (H * zero) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)" 
      using f1 by simp
    then show "(H \<Otimes> Id (m-c)) * (j\<Otimes> c (m-c+1) m j) = (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)" 
      using a0 app_H_zero assms(1) by auto
  qed
  ultimately show "(Id (c-1) \<Otimes> H \<Otimes> Id (m-c)) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (j\<Otimes> c (m-c+1) m j))
  = (pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> qr c c m j \<Otimes> (j\<Otimes> (c+1) (m-c) m j)"
    using tensor_mat_is_assoc by auto
qed


lemma app_G: (*Might be nicer to seperate th case m=c since (j\<Otimes> (m+1) (m-m+1-1) m j) is okay but conceptually not great.*)
  fixes c m j::nat
  assumes "c\<ge>1" and "m\<ge>c" and "j < 2 ^ m" 
  shows "G c m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (j\<Otimes> c (m-c+1) m j))
      = ((pw [qr (nat i) m m j. i<-[1..c]] c) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
proof(rule disjE)
  show "m>c \<or> m=c" using assms by auto
next
  assume a0: "m=c"
  then have "G c m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (j\<Otimes> c (m-c+1) m j))
      = G m m * ((pw [qr (nat i) m m j. i<-[1..(m-1)]] (m-1)) \<Otimes> (j\<Otimes> m (m-m+1) m j))" by auto
 then have "G c m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (j\<Otimes> c (m-c+1) m j))
      = (Id m * (Id (m-1) \<Otimes> H \<Otimes> Id (m-m))) * ((pw [qr (nat i) m m j. i<-[1..(m-1)]] (m-1)) \<Otimes> (j\<Otimes> m (m-m+1) m j))" 
   using all_gates_on_single_qubit_def by auto
  moreover have "dim_row (Id (m-1) \<Otimes> H \<Otimes> Id (m-m)) = 2^m" 
    by (metis (no_types, lifting) H_without_scalar_prod Id_right_tensor One_nat_def Quantum.Id_def a0 assms(1) diff_self_eq_0 dim_row_mat(1) dim_row_tensor_mat index_one_mat(2) less_eq_Suc_le power_minus_mult)
  ultimately have "G c m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (j\<Otimes> c (m-c+1) m j))
      = ((Id (m-1) \<Otimes> H \<Otimes> Id (m-m))) * ((pw [qr (nat i) m m j. i<-[1..(m-1)]] (m-1)) \<Otimes> (j\<Otimes> m (m-m+1) m j))" 
    using Id_mult_left by auto
  then have "G c m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (j\<Otimes> c (m-c+1) m j))
      = (pw [qr (nat i) m m j. i<-[1..(m-1)]] (m-1)) \<Otimes> (qr m m m j) \<Otimes> (j\<Otimes> (m+1) (m-m+1-1) m j)" 
    using app_H_all[of m m j] assms by auto
  moreover have "length  [qr (nat i) m m j. i<-[1..(m-1)]] = m-1" by simp
  ultimately have "G c m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (j\<Otimes> c (m-c+1) m j))
      = (pw ([qr (nat i) m m j. i<-[1..int(m-1)]]@[qr m m m j]) ((m-1)+1)) \<Otimes> (j\<Otimes> (m+1) (m-m+1-1) m j)"
    using pow_tensor_decomp_left a0 by auto
  moreover have "[qr (nat i) m m j. i<-[1..(m-1)]]@[qr m m m j] = [qr (nat i) m m j. i<-[1..m]]"
    using a0
    by (metis (no_types, lifting) assms(1) linordered_nonzero_semiring_class.of_nat_mono list.simps(8) list.simps(9) map_append nat_int of_nat_1 of_nat_diff upto_rec2)
  ultimately have "G c m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (j\<Otimes> c (m-c+1) m j))
      = ((pw [qr (nat i) m m j. i<-[1..m]] m) \<Otimes> (j\<Otimes> (m+1) (m-m+1-1) m j))" 
    using assms by auto
  then show "G c m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (j\<Otimes> c (m-c+1) m j))
      = ((pw [qr (nat i) m m j. i<-[1..c]] c) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))" using a0 by auto
next
  assume a0: "m>c"
  have "G c m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (j\<Otimes> c (m-c+1) m j))
      = (aCR c (m-c) m * (Id (c-1) \<Otimes> H \<Otimes> Id (m-c))) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (j\<Otimes> c (m-c+1) m j))"
    using all_gates_on_single_qubit_def by auto
  then have "G c m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (j\<Otimes> c (m-c+1) m j))
      = aCR c (m-c) m * ((Id (c-1) \<Otimes> H \<Otimes> Id (m-c)) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (j\<Otimes> c (m-c+1) m j)))"
    sorry
  then have "G c m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (j\<Otimes> c (m-c+1) m j))
      = aCR c (m-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
    using app_H_all assms by auto
  then have "G c m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (j\<Otimes> c (m-c+1) m j))
      = ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c m m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
    using all_CR_app assms a0 by auto
  moreover have "length  [qr (nat i) m m j. i<-[1..(c-1)]] = c-1" by simp
  ultimately have "G c m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (j\<Otimes> c (m-c+1) m j))
      = ((pw ([qr (nat i) m m j. i<-[1..(c-1)]]@[qr c m m j]) (c-1+1)) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
    using pow_tensor_decomp_left by auto
  moreover have "[qr (nat i) m m j. i<-[1..(c-1)]]@[qr c m m j] = [qr (nat i) m m j. i<-[1..c]]"
    by (metis (no_types, lifting) assms(1) linordered_nonzero_semiring_class.of_nat_mono list.simps(8) list.simps(9) map_append nat_int of_nat_1 of_nat_diff upto_rec2)
  ultimately show "G c m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (j\<Otimes> c (m-c+1) m j))
      = ((pw [qr (nat i) m m j. i<-[1..c]] c) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
    using assms by auto
qed


fun pow_mult :: "(complex Matrix.mat) list \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("pm _ _" 75)  where
  "(pm (Cons x []) (Suc 0)) = x"  
| "(pm (Cons x xs) (Suc k)) = (pm xs k) * x"

lemma pow_mult_dim:
  assumes "k\<ge>1"
  shows "\<forall>xs. length xs = k \<and> (\<forall>x \<in> set xs. dim_row x = n \<and> dim_col x = n) \<longrightarrow> dim_row (pm xs k) = n \<and> dim_col (pm xs k) = n"
proof(rule Nat.nat_induct_at_least[of 1 k])
  show "k\<ge>1" using assms by auto
next
  show "\<forall>xs. length xs = 1 \<and> (\<forall>x \<in> set xs. dim_row x = n \<and> dim_col x = n) \<longrightarrow> dim_row (pm xs 1) = n \<and> dim_col (pm xs 1) = n"
    by (metis One_nat_def cancel_comm_monoid_add_class.diff_cancel last_ConsL last_in_set length_0_conv length_tl list.exhaust_sel pow_mult.simps(1) zero_neq_one)
next
  fix k::nat
  assume a0: "k\<ge>1"
  assume IH: "\<forall>xs. length xs = k \<and> (\<forall>x \<in> set xs. dim_row x = n \<and> dim_col x = n) \<longrightarrow> dim_row (pm xs k) = n \<and> dim_col (pm xs k) = n"
  show "\<forall>xs. length xs = (Suc k) \<and> (\<forall>x \<in> set xs. dim_row x = n \<and> dim_col x = n) \<longrightarrow> dim_row (pm xs (Suc k)) = n \<and> dim_col (pm xs (Suc k)) = n"
  proof(rule allI, rule impI)
    fix xs::"complex Matrix.mat list"
    assume a1: "length xs = (Suc k) \<and> (\<forall>x \<in> set xs. dim_row x = n \<and> dim_col x = n)"
    have "dim_row (pm xs (Suc k)) = dim_row ((pm (tl xs) k) * (hd xs))" using a0 
      by (metis a1 le_iff_add length_0_conv list.exhaust_sel nat.simps(3) plus_1_eq_Suc pow_mult.simps(3))
    then have "dim_row (pm xs (Suc k)) = dim_row (pm (tl xs) k)" by auto
    then have f0: "dim_row (pm xs (Suc k)) = n" using IH 
      by (metis a1 diff_Suc_1 length_0_conv length_tl list.set_sel(2) nat.simps(3))
    have "dim_col (pm xs (Suc k)) = dim_col ((pm (tl xs) k) * (hd xs))" using a0 
      by (metis a1 le_iff_add length_0_conv list.exhaust_sel nat.simps(3) plus_1_eq_Suc pow_mult.simps(3))
    then have "dim_col (pm xs (Suc k)) = dim_col (hd xs)" by auto
    then have f1: "dim_col (pm xs (Suc k)) = n" 
      by (metis a1 hd_in_set length_greater_0_conv zero_less_Suc)
    then show "dim_row (pm xs (Suc k)) = n \<and> dim_col (pm xs (Suc k)) = n" using f0 f1 by auto
  qed
qed


lemma pow_mult_decomp:
  fixes k m s::nat
  assumes "k\<ge>2"
  shows "\<forall>xs. length xs = k \<and> (\<forall>x \<in> set xs. dim_row x = n \<and> dim_col x = n) 
    \<longrightarrow> (pm xs k) = (last xs) * (pm (butlast xs) (k-1))" 
proof(rule Nat.nat_induct_at_least[of 2 k])
  show "k\<ge>2" using assms by auto
next
  show "\<forall>xs. length xs = 2 \<and> (\<forall>x \<in> set xs. dim_row x = n \<and> dim_col x = n) 
    \<longrightarrow> (pm xs 2) = (last xs) * (pm (butlast xs) (2-1))" 
  proof(rule allI, rule impI)
    fix xs::"complex Matrix.mat list"
    assume a0: "length xs = 2 \<and> (\<forall>x \<in> set xs. dim_row x = n \<and> dim_col x = n)"
    then have "(pm xs 2) = (pm (tl xs) 1) * (hd xs)" 
      by (metis One_nat_def Suc_length_conv list.sel(1) list.sel(3) numeral_2_eq_2 pow_mult.simps(3))
    then have "(pm xs 2) = (hd (tl xs)) * (hd xs)" 
      by (metis One_nat_def Suc_1 a0 diff_Suc_1 length_0_conv length_tl list.exhaust_sel not_less_eq_eq pow_mult.simps(1))
    then have "(pm xs 2) = (last xs) * (hd xs)" 
      by (metis a0 last.simps length_0_conv length_Suc_conv list.sel(1) list.sel(3) numeral_2_eq_2)
    then show "(pm xs 2) = (last xs) * (pm (butlast xs) (2-1))"  
      by (metis a0 butlast.simps(2) length_0_conv length_Suc_conv length_butlast list.sel(1) numeral_2_eq_2 pow_mult.simps(1))
  qed
next
  fix k 
  assume a0: "k\<ge>2"
    and  IH: "\<forall>xs. length xs = k \<and> (\<forall>x \<in> set xs. dim_row x = n \<and> dim_col x = n) 
         \<longrightarrow> (pm xs k) = (last xs) * (pm (butlast xs) (k-1))" 
  show "\<forall>xs. length xs = (Suc k) \<and> (\<forall>x \<in> set xs. dim_row x = n \<and> dim_col x = n) 
    \<longrightarrow> (pm xs (Suc k)) = (last xs) * (pm (butlast xs) ((Suc k)-1))" 
  proof(rule allI, rule impI)
    fix xs::"complex Matrix.mat list"
    assume a1: "length xs = (Suc k) \<and> (\<forall>x \<in> set xs. dim_row x = n \<and> dim_col x = n)"
    then have "(pm xs (Suc k)) = (pm (tl xs) k) * (hd xs)" using a0 
      by (metis Suc_1 Suc_le_D Suc_length_conv list.sel(1) list.sel(3) pow_mult.simps(3))
    moreover have f0: "length (tl xs) = k" by (simp add: a1)
    moreover have "last (tl xs) = last xs" using a1 by (metis a0 f0 last_tl le_zero_eq list.size(3) zero_neq_numeral)
    ultimately have "(pm xs (Suc k)) = (last xs) * (pm (butlast (tl xs)) (k-1)) * (hd xs)" 
      using IH a1 by (metis One_nat_def Suc_eq_plus1 Suc_less_eq le_add2 le_imp_less_Suc length_greater_0_conv list.set_sel(2))
    moreover have "(last xs) * (pm (butlast (tl xs)) (k-1)) * (hd xs) = (last xs) * ((pm (butlast (tl xs)) (k-1)) * (hd xs))" 
    proof- 
      have "length (butlast (tl xs)) = k-1" using f0 length_butlast by blast
      moreover have "1 \<le> k - 1" using a0 by linarith
      moreover have "(\<forall>x\<in>set (butlast (tl xs)). dim_row x = n \<and> dim_col x = n)" 
        by (metis a1 butlast.simps(1) in_set_butlastD list.set_sel(2) tl_Nil)
      then have "(pm (butlast (tl xs)) (k-1)) \<in> carrier_mat n n" 
        using a0 a1 pow_mult_dim[of "k-1" n ] by auto
      moreover  have "(last xs) \<in> carrier_mat n n" using a1 
        by (metis carrier_matI last_in_set length_0_conv nat.simps(3))
      moreover have "(hd xs) \<in> carrier_mat n n" using a1 
        by (metis Suc_eq_plus1 Zero_not_Suc carrier_mat_triv list.set_sel(1) list.size(3))
      ultimately show ?thesis using assoc_mult_mat by auto
    qed
    ultimately have "(pm xs (Suc k)) = (last xs) * ((pm (butlast (tl xs)) (k-1)) * (hd xs))" by auto
    moreover have "(hd xs)#(butlast (tl xs)) = butlast xs" using a0 a1 
      by (metis butlast.simps(2) f0 length_0_conv length_greater_0_conv less_le_trans list.exhaust_sel nat.simps(3) pos2)
    ultimately show "(pm xs (Suc k)) = (last xs) * (pm (butlast xs) ((Suc k)-1))" 
      using a0 a1 f0 pow_mult.simps 
      by (metis (no_types, lifting) Suc_1 Suc_diff_le diff_Suc_Suc length_Cons length_butlast)
  qed
qed


lemma pow_mult_decomp_G:
  fixes k::nat
  assumes "k\<ge>1" and "k<m" 
  shows "(pm [G (nat i) m. i<-[1..(Suc k)]] (Suc k)) = (G (Suc k) m) * (pm [G (nat i) m. i<-[1..k]] k)" 
proof-
  have "length [G (nat i) m. i<-[1..(Suc k)]] = k+1" by auto
  moreover have "(\<forall>x \<in> set [G (nat i) m. i<-[1..(Suc k)]]. dim_row x = 2^m \<and> dim_col x = 2^m)" 
    using assms G_dim(1) G_dim(2) by auto
  moreover have "2 \<le> k + 1" 
    using assms by linarith
  ultimately have "(pm [G (nat i) m. i<-[1..(Suc k)]] (Suc k)) 
      = (last [G (nat i) m. i<-[1..(Suc k)]]) * (pm (butlast [G (nat i) m. i<-[1..(Suc k)]]) (k+1-1))"  
    using pow_mult_decomp[of "k+1" "2^m"] assms by auto
  moreover have "(last [G (nat i) m. i<-[1..(Suc k)]]) = G (nat (Suc k)) m " by (simp add: upto_rec2)
  moreover have "(butlast [G (nat i) m. i<-[1..(Suc k)]]) = [G (nat i) m. i<-[1..k]]" by (simp add: upto_rec2) 
  ultimately show "(pm [G (nat i) m. i<-[1..(Suc k)]] (Suc k)) 
      = (G (Suc k) m) * (pm [G (nat i) m. i<-[1..k]] k)" 
    by (metis add_diff_cancel_right' nat_int)
qed



lemma app_all_G: 
  fixes k m j::nat
  assumes "k\<ge>1" and "j<2^m" and "m\<ge>1" (*Make a special case for k=m*)
  shows "k\<le>m \<longrightarrow> (pm [G (nat i) m. i<-[1..k]] k) * (j\<Otimes> 1 m m j)
      = ((pw [qr (nat i) m m j. i<-[1..k]] k) \<Otimes> (j\<Otimes> (k+1) (m-k) m j))" 
proof(rule Nat.nat_induct_at_least[of 1 k])
  show "k\<ge>1" using assms by auto
next
  show "1\<le>m \<longrightarrow>(pm [G (nat i) m. i<-[1..int 1]] 1) * (j\<Otimes> 1 m m j)
      = ((pw [qr (nat i) m m j. i<-[1..int 1]] 1) \<Otimes> (j\<Otimes> (1+1) (m-1) m j))" 
  proof
    assume "1\<le>m" 
    have "(pm [G (nat i) m. i<-[1..int 1]] 1) * (j\<Otimes> 1 m m j)
       = (G 1 m) * (j\<Otimes> 1 m m j)"
     by auto
    moreover have "(j\<Otimes> 1 m m j) = ((pw [qr (nat i) m m j. i<-[1..(1-1)]] (1-1)) \<Otimes> (j\<Otimes> 1 (m-1+1) m j))" 
    proof-
      have "(pw [qr (nat i) m m j. i<-[1..(1-1)]] (1-1)) = (Id 0)" by simp
      moreover have "(j\<Otimes> 1 m m j) = (j\<Otimes> 1 (m-1+1) m j)" using assms by auto
      ultimately show ?thesis using Id_left_tensor by auto
    qed
    moreover have "G 1 m * ((pw [qr (nat i) m m j. i<-[1..(1-1)]] (1-1)) \<Otimes> (j\<Otimes> 1 (m-1+1) m j))
       = ((pw [qr (nat i) m m j. i<-[1..1]] 1) \<Otimes> (j\<Otimes> (1+1) (m-1) m j))"
      using app_G[of 1 m j] assms by auto 
    ultimately show "(pm [G (nat i) m. i<-[1..int 1]] 1) * (j\<Otimes> 1 m m j)
      = ((pw [qr (nat i) m m j. i<-[1..int 1]] 1) \<Otimes> (j\<Otimes> (1+1) (m-1) m j))"  by auto
 qed
next
  fix k::nat
  assume a0: "k\<ge>1"
  assume IH: "k\<le>m \<longrightarrow>(pm [G (nat i) m. i<-[1..k]] k) * (j\<Otimes> 1 m m j)
            = ((pw [qr (nat i) m m j. i<-[1..k]] k) \<Otimes> (j\<Otimes> (k+1) (m-k) m j))" 
  show  "(Suc k)\<le>m \<longrightarrow> (pm [G (nat i) m. i<-[1..(Suc k)]] (Suc k)) * (j\<Otimes> 1 m m j)
      = ((pw [qr (nat i) m m j. i<-[1..(Suc k)]] (Suc k)) \<Otimes> (j\<Otimes> ((Suc k)+1) (m-(Suc k)) m j))" 
  proof
    assume a1: "(Suc k)\<le>m"
    then have "(pm [G (nat i) m. i<-[1..int (Suc k)]] (Suc k)) * (j\<Otimes> 1 m m j)
             = ((G (Suc k) m) * (pm [G (nat i) m. i<-[1..int k]] k)) * (j\<Otimes> 1 m m j)"
      using a0 pow_mult_decomp_G[of k m] by auto
    then have "(pm [G (nat i) m. i<-[1..int (Suc k)]] (Suc k)) * (j\<Otimes> 1 m m j)
            = (G (Suc k) m) * ((pm [G (nat i) m. i<-[1..int k]] k) * (j\<Otimes> 1 m m j))"
    sorry
    then have  "(pm [G (nat i) m. i<-[1..int (Suc k)]] (Suc k)) * (j\<Otimes> 1 m m j)
            = (G (Suc k) m) * ((pw [qr (nat i) m m j. i<-[1..k]] k) \<Otimes> (j\<Otimes> (k+1) (m-k) m j))"
      using IH a1 by auto
    then show "(pm [G (nat i) m. i<-[1..int (Suc k)]] (Suc k)) * (j\<Otimes> 1 m m j)
            = ((pw [qr (nat i) m m j. i<-[1..int (Suc k)]] (Suc k)) \<Otimes> (j\<Otimes> ((Suc k)+1) (m-(Suc k)) m j))"
      using app_G[of "Suc k" m j] assms a0 a1 by auto
  qed
qed



abbreviation \<psi>\<^sub>1::"nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where 
  "\<psi>\<^sub>1 m j \<equiv> pw [qr (nat k) m m j. k<-[1..m] ] m"

theorem quantum_fourier_transform_tensor_prod_rep: (*Change name*)
  fixes j m::nat
  assumes "j < 2^m" and "m\<ge>1"
  shows "(pm [G (nat i) m. i<-[1..m]] m) * |unit_vec (2^m) j\<rangle>  = \<psi>\<^sub>1 m j" 
proof-
  have "(pm [G (nat i) m. i<-[1..m]] m) * |unit_vec (2^m) j\<rangle>  = (pm [G (nat i) m. i<-[1..m]] m) * (j\<Otimes> 1 m m j)"
    using assms(1) assms(2) j_as_unit by auto
  then have "(pm [G (nat i) m. i<-[1..m]] m) * |unit_vec (2^m) j\<rangle> = ((pw [qr (nat i) m m j. i<-[1..m]] m) \<Otimes> (j\<Otimes> (m+1) (m-m) m j))" 
    using app_all_G assms by auto
  moreover have "(j\<Otimes> (m+1) (m-m) m j) = (Id 0)" by simp
  ultimately have "(pm [G (nat i) m. i<-[1..m]] m) * |unit_vec (2^m) j\<rangle> = (pw [qr (nat i) m m j. i<-[1..m]] m)" by simp
  then show ?thesis by auto
qed


(*MISSING: Reverse order of qubits. Maybe also put sqrt(2) in front? *)

abbreviation \<psi>\<^sub>2::"nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where 
  "\<psi>\<^sub>2 m jd \<equiv> Matrix.mat (2^m) 1 (\<lambda>(i,j). exp(2*pi*\<i>*jd*i/2^m)/(sqrt(2)^m))"


lemma aux_exp_term_one_1: 
  assumes "m\<ge>k" and "k\<ge>1" and "m\<ge>i" and "k\<ge>i+1" 
  shows "1/2^(m-k+1)*(2::nat)^(m-i) = 2^(k-i-1)"
proof-
  have " m - k + 1 \<le> m - i" 
    using assms(1) assms(4) by linarith
  then have "1/2^(m-k+1)*(2::nat)^(m-i) = 2^(m-i-(m-k+1))"
    using power_diff[of 2 "m-k+1" "m-i"] 
    by (metis One_nat_def add.right_neutral add_Suc_right diff_diff_left mult.left_neutral of_nat_numeral 
        of_nat_power one_add_one times_divide_eq_left zero_neq_numeral)   
  moreover have "m-i-(m-k+1) = k-i-1" using assms by auto
  ultimately show ?thesis by auto
qed 

lemma aux_exp_term_one_2: 
  assumes "i\<in>{k-1..m-1}" and "m\<ge>1" and "m\<ge>k" and "k\<ge>1" and "jd < 2^m"
  shows "1/2^(m-k+1)*real 2^(m-(i+1)) = 1/2^(i-(k-1)+1)" 
proof-
  have "(m::nat) - ((i::nat) + (1::nat)) \<le> m - (k::nat) + (1::nat)"
    using assms diff_le_mono2 by auto
  then have "(2::nat)^(m-k+1) * 1/2^(m-(i+1)) = 2^(m-k+1-(m-(i+1)))"
    using power_diff[of "2::nat" "m-(i+1)" "m-k+1"] 
    by (smt mult.right_neutral of_nat_1 of_nat_add of_nat_power one_add_one power_diff)
  then have "(2::nat)^(m-k+1) * 1/2^(m-(i+1)) = 2^(i-(k-1)+1)" 
    using assms
    by (smt Nat.add_diff_assoc2 add_diff_cancel_right atLeastAtMost_iff cancel_ab_semigroup_add_class.diff_right_commute diff_diff_cancel diff_le_mono2 le_add_diff_inverse2) 
  then show ?thesis
    by (metis (no_types, lifting) divide_divide_eq_right nat_mult_1_right of_nat_1 of_nat_add of_nat_power one_add_one times_divide_eq_left)
qed


lemma j_bit_representation:
  assumes "j < 2^m" and "m\<ge>1"
  shows "j = (\<Sum>i\<in>{1..m}. (bin_rep m j)!(i-1) * 2^(m-i))" 
proof-
  have "j = (\<Sum>i<m. bin_rep m j ! i * 2^(m-1-i))" 
    using bin_rep_eq[of m j] assms by auto
  also have "... = (\<Sum>i\<in>{0..m-1}. bin_rep m j ! i * 2^(m-1-i))" 
    using assms(2)
    by (metis atLeast0AtMost lessThan_Suc_atMost ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
  also have "... = (\<Sum>i\<in>{1..m-1+1}. bin_rep m j ! (i-1) * 2^(m-1-(i-1)))"
    using sum.shift_bounds_cl_nat_ivl[of "\<lambda>i. bin_rep m j ! (i-1) * 2^(m-1-(i-1))" 0 1 "m-1"] by auto 
  also have "... = (\<Sum>i\<in>{1..m}. bin_rep m j ! (i-1) * 2^(m-1-(i-1)))"
    using add_Suc_right assms(2) ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc by auto
  finally show ?thesis by auto
qed

lemma exp_term_one:
  assumes "m \<ge> 1" and "k \<ge> 1" and "jd < 2^m"
  shows "k \<le> m \<longrightarrow> exp(2*pi*\<i>*(\<Sum>i\<in>{1..<k}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i))) = 1"
proof(rule Nat.nat_induct_at_least[of 1 k])
  show "k\<ge>1" using assms by auto
next
  have "(\<Sum>i\<in>{(1::nat)..<1}. (bin_rep m jd)!(i-1) * 1/2^(m-1+1)*real 2^(m-i)) = 0" 
    by auto 
  then show "1\<le>m \<longrightarrow>exp(2*pi*\<i>*(\<Sum>i\<in>{1..<1}. (bin_rep m jd)!(i-1) * 1/2^(m-1+1)*real 2^(m-i))) = 1"
    by simp
next
  fix k::nat
  assume a0: "k\<ge> 1"
  assume IH: "k\<le>m \<longrightarrow> exp(2*pi*\<i>*(\<Sum>i\<in>{1..<k}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i))) = 1"
  show "(Suc k)\<le>m \<longrightarrow> exp(2*pi*\<i>*(\<Sum>i\<in>{1..<(Suc k)}. (bin_rep m jd)!(i-1) * 1/2^(m-(Suc k)+1)*real 2^(m-i))) = 1"
  proof
    assume a1: "(Suc k)\<le>m"
    have "(\<Sum>i\<in>{1..<(Suc k)}. (bin_rep m jd)!(i-1) * 1/2^(m-(Suc k)+1)*real 2^(m-i)) =
          (\<Sum>i\<in>{1..<k}. (bin_rep m jd)!(i-1) * 1/2^(m-(Suc k)+1)*real 2^(m-i))
        + (bin_rep m jd)!(k-1) * 1/2^(m-(Suc k)+1)*real 2^(m-k)" using sum_Un a0 by auto 
    then have "(\<Sum>i\<in>{1..<(Suc k)}. (bin_rep m jd)!(i-1) * 1/2^(m-(Suc k)+1)*real 2^(m-i)) =
               (2::nat) *(\<Sum>i\<in>{1..<k}.  ((bin_rep m jd)!(i-1) * 1/2^(m-k+1) * real 2^(m-i))) 
             + (bin_rep m jd)!(k-1) * 1/2^(m-(Suc k)+1)*real 2^(m-k)"
      using sum_distrib_left[of 2 "\<lambda>i.((bin_rep m jd)!(i-1) * 1/2^(m-k+1) * real 2^(m-i))" "{1..<k}" ] a1 by auto
    then have "exp(2*pi*\<i>*(\<Sum>i\<in>{1..<(Suc k)}. (bin_rep m jd)!(i-1) * 1/2^(m-(Suc k)+1)*real 2^(m-i))) =
               exp((2::nat)*(2*pi*\<i>*(\<Sum>i\<in>{1..<k}. ((bin_rep m jd)!(i-1) * 1/2^(m-k+1) * real 2^(m-i))))) 
             * exp(2*pi*\<i>*((bin_rep m jd)!(k-1) * 1/2^(m-(Suc k)+1)*real 2^(m-k)))" 
      using exp_add distrib_left[of "(2*pi*\<i>)" "((2::nat)*(\<Sum>i\<in>{1..<k}. ((bin_rep m jd)!(i-1) * 1/2^(m-k+1) * real 2^(m-i))))"] 
      by auto
    then have "exp(2*pi*\<i>*(\<Sum>i\<in>{1..<(Suc k)}. (bin_rep m jd)!(i-1) * 1/2^(m-(Suc k)+1)*real 2^(m-i))) =
               exp((2*pi*\<i>*(\<Sum>i\<in>{1..<k}. ((bin_rep m jd)!(i-1) * 1/2^(m-k+1) * real 2^(m-i)))))^2
             * exp(2*pi*\<i>*((bin_rep m jd)!(k-1) * 1/2^(m-(Suc k)+1)*real 2^(m-k)))" 
      by (metis (mono_tags, lifting) exp_double of_nat_numeral)
    then have "exp(2*pi*\<i>*(\<Sum>i\<in>{1..<(Suc k)}. (bin_rep m jd)!(i-1) * 1/2^(m-(Suc k)+1)*real 2^(m-i))) =
                   exp(2*pi*\<i>*((bin_rep m jd)!(k-1) * 1/2^(m-(Suc k)+1)*real 2^(m-k)))" 
      using IH a1 by auto
    moreover have "exp(2*pi*\<i>*((bin_rep m jd)!(k-1) * 1/2^(m-(Suc k)+1)*real 2^(m-k))) = 1"
    proof(rule disjE)
      show "(bin_rep m jd)!(k-1) = 0 \<or> (bin_rep m jd)!(k-1) = 1" 
        using bin_rep_coeff a0 a1 assms diff_less_Suc less_le_trans by blast
    next
      assume a2: "(bin_rep m jd)!(k-1) = 0"
      then show ?thesis by auto
    next
      assume a2: "(bin_rep m jd)!(k-1) = 1"
      then have "exp(2*pi*\<i>*((bin_rep m jd)!(k-1) * 1/2^(m-(Suc k)+1)*real 2^(m-k)))
               = exp(2*pi*\<i>*( 1/2^(m-(Suc k)+1)*real 2^(m-k)))" using a2 by auto
      then have "exp(2*pi*\<i>*((bin_rep m jd)!(k-1) * 1/2^(m-(Suc k)+1)*real 2^(m-k)))
               = exp(2*pi*\<i>*( 1/2^(m-k)*real 2^(m-k)))" 
        using a1
        by (metis (no_types, lifting) One_nat_def Suc_diff_le add.right_neutral add_Suc_right diff_Suc_Suc)
      then have "exp(2*pi*\<i>*((bin_rep m jd)!(k-1) * 1/2^(m-(Suc k)+1)*real 2^(m-k))) = exp(2*pi*\<i>)"  
          by (smt Suc_diff_le Suc_eq_plus1 Suc_leD a0 a1 add.right_neutral add_diff_cancel_right' diff_Suc_Suc aux_exp_term_one_1 le_SucI mult.right_neutral of_nat_power of_real_hom.hom_one order_refl plus_1_eq_Suc power.simps(1))
      then show "exp(2*pi*\<i>*((bin_rep m jd)!(k-1) * 1/2^(m-(Suc k)+1)*real 2^(m-k))) = 1" by simp
    qed
    ultimately show "exp(2*pi*\<i>*(\<Sum>i\<in>{1..<(Suc k)}. (bin_rep m jd)!(i-1) * 1/2^(m-(Suc k)+1)*real 2^(m-i))) = 1" 
      by auto
  qed
qed



lemma qr_different_rep:
  fixes k m jd::nat
  assumes "m\<ge>1" and "m\<ge>k" and "k\<ge>1" and "jd < 2^m"
  shows "qr k m m jd = Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1/sqrt(2) else exp(2*pi*\<i>*jd/2^(m-k+1))*1/sqrt(2))" 
proof- 
  have "qr k m m jd = (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then (1::complex)/sqrt(2) 
              else (exp (complex_of_real (2*pi)*\<i>*(bf (k-1) (m-1) m jd)))*1/sqrt(2)))"
        using qr_def by auto
  moreover have "exp(2*pi*\<i>*jd/2^(m-k+1)) = exp (complex_of_real (2*pi)*\<i>*(bf (k-1) (m-1) m jd))" 
  proof-
    have "exp(2*pi*\<i>*jd/2^(m-k+1)) = exp(2*pi*\<i>*(\<Sum>i\<in>{1..m}. (bin_rep m jd)!(i-1) * 2^(m-i))*1/2^(m-k+1))" 
      using j_bit_representation assms by auto
    then have "exp(2*pi*\<i>*jd/2^(m-k+1)) = exp(2*pi*\<i>*(1/2^(m-k+1)*real(\<Sum>i\<in>{1..m}. (bin_rep m jd)!(i-1) * 2^(m-i))))" 
      using Groups.mult_ac(1) mult.right_neutral times_divide_eq_left by simp
    moreover have "(1/2^(m-k+1)*real(\<Sum>i\<in>{1..m}. (bin_rep m jd)!(i-1) * 2^(m-i)))
                 = (\<Sum>i\<in>{1..m}. 1/2^(m-k+1)*((bin_rep m jd)!(i-1) * 2^(m-i)))"
      using sum_distrib_left[of "1/2^(m-k+1)" "\<lambda>i.(bin_rep m jd)!(i-1) * 2^(m-i)" "{1..m}"] by auto 
    ultimately have "exp(2*pi*\<i>*jd/2^(m-k+1)) = exp(2*pi*\<i>*(\<Sum>i\<in>{1..m}. 1/2^(m-k+1)*((bin_rep m jd)!(i-1) * 2^(m-i))))"
      by presburger
    then have "exp(2*pi*\<i>*jd/2^(m-k+1)) = exp(2*pi*\<i>*(\<Sum>i\<in>{1..m}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i)))"
      by auto
    moreover have "(\<Sum>i\<in>{1..m}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i)) = 
          (\<Sum>i\<in>{1..<k}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i)) +
          (\<Sum>i\<in>{k..m}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i))" 
      using assms(2) assms(3) 
      by (smt atLeastLessThanSuc_atLeastAtMost le_eq_less_or_eq le_less_trans lessI sum.atLeastLessThan_concat)
    ultimately have "exp(2*pi*\<i>*jd/2^(m-k+1)) 
        = exp(2*pi*\<i>*((\<Sum>i\<in>{1..<k}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i))+(\<Sum>i\<in>{k..m}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i))))"
      by metis
    then have "exp(2*pi*\<i>*jd/2^(m-k+1)) 
             = exp(2*pi*\<i>*(\<Sum>i\<in>{1..<k}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i))) *
               exp(2*pi*\<i>*(\<Sum>i\<in>{k..m}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i)))"
      using exp_add by (simp add: distrib_left)
    then have "exp(2*pi*\<i>*jd/2^(m-k+1)) = exp(2*pi*\<i>*(\<Sum>i\<in>{k..m}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i)))"
      using assms exp_term_one by auto
    moreover have "exp(2*pi*\<i>*(\<Sum>i\<in>{k..m}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i)))
                 = exp(2*pi*\<i>*(bf (k-1) (m-1) m jd))" 
    proof-
      have "(\<Sum>i\<in>{k..m}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i))
          = (\<Sum>i\<in>{k-1..m-1}. (bin_rep m jd)!i* 1/2^(m-k+1)*real 2^(m-(i+1)))"
        using sum.shift_bounds_cl_nat_ivl[of "\<lambda>i.(bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i)" "k-1" 1 "m-1"] assms(1) assms(3)
        by auto
      moreover have "(\<Sum>i\<in>{k-1..m-1}. (bin_rep m jd)!i * (1/2^(m-k+1)*real 2^(m-(i+1))))
                   = (\<Sum>i\<in>{k-1..m-1}. (bin_rep m jd)!i * (1/2^(i-(k-1)+1)))" 
        using aux_exp_term_one_2 assms by (metis (no_types, lifting) sum.cong) 
      ultimately have "(\<Sum>i\<in>{k..m}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i))
           =(\<Sum>i\<in>{k-1..m-1}. (bin_rep m jd)!i* 1/2^(i-(k-1)+1))"
        by auto
      then show ?thesis using binary_fraction_def by auto
    qed
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis by auto
qed

lemma qr_different_rep':
  fixes k m jd::nat
  assumes "m\<ge>1" and "m\<ge>k" and "k\<ge>1" and "jd < 2^m"
  shows "qr k m m jd = Matrix.mat 2 1 (\<lambda>(i,j). exp(2*pi*\<i>*i*jd/2^(m-k+1))*1/sqrt(2))" 
proof-
  have "qr k m m jd = Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1/sqrt(2) else exp(2*pi*\<i>*jd/2^(m-k+1))*1/sqrt(2))" 
    using qr_different_rep assms by simp
  moreover have "Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1/sqrt(2) else exp(2*pi*\<i>*jd/2^(m-k+1))*1/sqrt(2))
              = Matrix.mat 2 1 (\<lambda>(i,j). exp(2*pi*\<i>*i*jd/2^(m-k+1))*1/sqrt(2))"
  proof
    fix i j
    assume "i < dim_row (Matrix.mat 2 1 (\<lambda>(i,j). exp(2*pi*\<i>*i*jd/2^(m-k+1))*1/sqrt(2)))"
       and "j < dim_col( Matrix.mat 2 1 (\<lambda>(i,j). exp(2*pi*\<i>*i*jd/2^(m-k+1))*1/sqrt(2)))"
    then have "i \<in> {0,1} \<and> j = 0" by auto
    moreover have "Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1/sqrt(2) else exp(2*pi*\<i>*jd/2^(m-k+1))*1/sqrt(2)) $$ (0,0)
              = Matrix.mat 2 1 (\<lambda>(i,j). exp(2*pi*\<i>*i*jd/2^(m-k+1))*1/sqrt(2)) $$ (0,0)"
      by auto
    moreover have "Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1/sqrt(2) else exp(2*pi*\<i>*jd/2^(m-k+1))*1/sqrt(2)) $$ (1,0)
              = Matrix.mat 2 1 (\<lambda>(i,j). exp(2*pi*\<i>*i*jd/2^(m-k+1))*1/sqrt(2)) $$ (1,0)" by auto  
    ultimately show "Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1/sqrt(2) else exp(2*pi*\<i>*jd/2^(m-k+1))*1/sqrt(2)) $$ (i,j)
              = Matrix.mat 2 1 (\<lambda>(i,j). exp(2*pi*\<i>*i*jd/2^(m-k+1))*1/sqrt(2)) $$ (i,j)" by auto
  next
    show "dim_row (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1/sqrt(2) else exp(2*pi*\<i>*jd/2^(m-k+1))*1/sqrt(2)))
              = dim_row (Matrix.mat 2 1 (\<lambda>(i,j). exp(2*pi*\<i>*i*jd/2^(m-k+1))*1/sqrt(2)))" 
      by simp
  next
    show "dim_col (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1/sqrt(2) else exp(2*pi*\<i>*jd/2^(m-k+1))*1/sqrt(2)))
              = dim_col (Matrix.mat 2 1 (\<lambda>(i,j). exp(2*pi*\<i>*i*jd/2^(m-k+1))*1/sqrt(2)))" by simp
  qed
  ultimately show ?thesis by auto
qed

lemma
  assumes "m\<ge>1"
  shows "1/(2::real)^(m+1)*2 = 1/2^m" by auto

lemma
  fixes a b c::nat
  shows "a * (b+c) = a*b + a*c" 
  by (simp add: distrib_left)
lemma 
  assumes "i\<in>{0,1}" and "m>1"
  shows "(bin_rep m i)!0 = 0"
  by (metis assms(1) assms(2) bin_rep_index_0 insert_iff lessI one_add_one plus_1_eq_Suc pos2 power_one_right singletonD)

lemma bin_rep_div:
  assumes "i < 2^(Suc n)" and "n\<ge>1" and "l\<le>n" and "l\<ge>1"
  shows "(bin_rep n (i div 2))!(l-1) = (bin_rep (Suc n) i)!(l-1) " 
proof-
  have "m \<le> n \<longrightarrow> i div 2 mod 2^m = i mod 2^(m+1) div 2" for m::nat
    using assms by (simp add: mod_mult2_eq)
  then have f0: "i div 2 mod 2^(n-l+1) = i mod 2^(n-l+1+1) div 2" 
    by (metis assms(3) assms(4) le_add_diff_inverse2 nat_add_left_cancel_le)
  have "(bin_rep n (i div 2))!(l-1) = ((i div 2) mod 2^(n-(l-1))) div 2^(n-1-(l-1))"
    using bin_rep_index assms by auto
  then have "(bin_rep n (i div 2))!(l-1) = (i mod 2^(n-l+1+1) div 2) div 2^(n-1-(l-1))" 
    using f0 assms(3) assms(4) 
    by (metis Nat.add_diff_assoc2 Nat.diff_diff_right)
  then have "(bin_rep n (i div 2))!(l-1) = i mod 2^(n-l+1+1) div 2^(n-1-(l-1)+1)" 
    by (metis (no_types, lifting) Groups.mult_ac(2) div_mult2_eq power_add power_one_right)
  then have "(bin_rep n (i div 2))!(l-1) = (i mod 2^((Suc n)-(l-1))) div 2^(n-1-(l-1)+1)" 
    by (smt Nat.diff_diff_eq One_nat_def Suc_diff_le add.right_neutral add_Suc_right assms(2) assms(3) assms(4) diff_Suc_1 le_SucI)
  then have "(bin_rep n (i div 2))!(l-1) = (i mod 2^((Suc n)-(l-1))) div 2^((Suc n)-1-(l-1))" 
    by (smt Suc_diff_le add.right_neutral add_Suc_right assms(2) assms(3) assms(4) diff_Suc_Suc ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
  then show "(bin_rep n (i div 2))!(l-1) = (bin_rep (Suc n) i)!(l-1)"
    using bin_rep_index assms by auto
qed

(*Da die Elemente der pw liste noch geswitched werden müssen ergibt sich die veränderte Matrix *)
lemma product_rep_to_def: 
  fixes n m jd::nat
  assumes "n \<ge> 1" and "m \<ge> 1" and "jd < 2^m"
  shows "n \<le> m \<longrightarrow> (pw [Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..n] ] n)
       =  Matrix.mat (2^n) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)"
proof(rule Nat.nat_induct_at_least[of 1 n])
  show "n \<ge> 1" using assms by auto
next
  show "1 \<le> m \<longrightarrow> (pw [Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..int 1] ] 1)
       = Matrix.mat (2^1) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..1}. (bin_rep 1 (of_nat i))!(l-1)/2^l))*1/sqrt(2)^1)"
  proof
    assume a0: "1 \<le> m"
    have "(pw [Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..int 1] ] 1)
       = Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^1)*1/sqrt(2))" by auto
    moreover have "Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^1)*1/sqrt(2))
                = Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(bin_rep 1 (of_nat i))!(1-1)/2^1)*1/sqrt(2))" 
    proof
      fix i j
      assume "i < dim_row (Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(bin_rep 1 (of_nat i))!(1-1)/2^1)*1/sqrt(2)))" 
      and "j < dim_col (Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(bin_rep 1 (of_nat i))!(1-1)/2^1)*1/sqrt(2)))" 
      then have f0: "i \<in> {0,1} \<and> j = 0" by auto
      moreover have "(Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*i/2^1)*1/sqrt(2))) $$ (0,j)
                = (Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(bin_rep 1 i)!(1-1)/2^1)*1/sqrt(2))) $$ (0,j)"  
        using f0 by (simp add: bin_rep_index_0)
      moreover have "(Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*i/2^1)*1/sqrt(2))) $$ (1,j)
                = (Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(bin_rep 1 i)!(1-1)/2^1)*1/sqrt(2))) $$ (1,j)" 
        using f0 
      proof-
        have "(Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(bin_rep 1 i)!(1-1)/2^1)*1/sqrt(2))) $$ (1,j)
            = exp(complex_of_real(2*pi)*\<i>*jd*(bin_rep 1 1)!(1-1)/2^1)*1/sqrt(2)" using f0 by auto
        moreover have "(bin_rep 1 1)!(1-1) = 1" using a0 
          by (metis One_nat_def Suc_eq_plus1 add_diff_cancel_left' bin_rep_index_0_geq le_numeral_extra(4) lessI one_add_one plus_1_eq_Suc power.simps(1) power_one_right)
        ultimately have "(Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(bin_rep 1 i)!(1-1)/2^1)*1/sqrt(2))) $$ (1,j)
            = exp(complex_of_real(2*pi)*\<i>*jd*1/2^1)*1/sqrt(2)" by auto
        moreover have "(Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*i/2^1)*1/sqrt(2))) $$ (1,j)
            = exp(complex_of_real(2*pi)*\<i>*jd*1/2^1)*1/sqrt(2)" using f0 by auto
        ultimately show ?thesis by auto
      qed 
      ultimately show "Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^1)*1/sqrt(2)) $$ (i,j)
                = Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(bin_rep 1 (of_nat i))!(1-1)/2^1)*1/sqrt(2)) $$ (i,j)" by auto
    next
      show "dim_row (Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^1)*1/sqrt(2)))
          = dim_row (Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(bin_rep 1 (of_nat i))!(1-1)/2^1)*1/sqrt(2)))" by auto
    next
      show "dim_col (Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^1)*1/sqrt(2)))
          = dim_col (Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(bin_rep 1 (of_nat i))!(1-1)/2^1)*1/sqrt(2)))" by auto
    qed
    ultimately have "(pw [Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..int 1] ] 1)
       =  Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(bin_rep 1 (of_nat i))!(1-1)/2^1)*1/sqrt(2))" 
      by auto
    then show "(pw [Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..int 1] ] 1)
       =  Matrix.mat (2^1) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..1}. (bin_rep 1 (of_nat i))!(l-1)/2^l))*1/sqrt(2)^1)"
      using a0 by auto
  qed
next
  fix n::nat
  assume a0: "n \<ge> 1"
  assume IH: "n \<le> m \<longrightarrow> (pw [Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..n] ] n)
       =  Matrix.mat (2^n) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)"
  show  "(Suc n) \<le> m \<longrightarrow> (pw [Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..(Suc n)] ] (Suc n))
       =  Matrix.mat (2^(Suc n)) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l))*1/sqrt(2)^(Suc n))"
  proof
    assume a1: "(Suc n) \<le> m"
    have "length [Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..n]] = n" by auto
    moreover have "[Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..n]]
              @ [Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k <-[Suc n..Suc n]]
            = [Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..(Suc n)]]" 
      by (smt One_nat_def a0 map_append nat_1 nat_le_iff of_nat_Suc upto_split1)
    moreover have "[Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k <-[Suc n..Suc n]]
                 = [Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2))]" by auto
    ultimately have "(pw ([Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..(Suc n)]]) (n+1))
      = (pw [Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..n]] n)
      \<Otimes> (Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))" 
      using pow_tensor_decomp_left[of "[Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..n]]"
          "n" "(Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))"] by auto
    then have "(pw ([Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..(Suc n)]]) (n+1))
      = Matrix.mat (2^n) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)
      \<Otimes> (Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))"
    using a1 IH by auto
    moreover have "Matrix.mat (2^n) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)
      \<Otimes> (Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))
=  Matrix.mat (2^(Suc n)) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l))*1/sqrt(2)^(Suc n))"
    proof
      fix i j
      assume "i < dim_row (Matrix.mat (2^(Suc n)) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l))*1/sqrt(2)^(Suc n)))"
      and "j < dim_col (Matrix.mat (2^(Suc n)) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l))*1/sqrt(2)^(Suc n)))"
      then have f0: "i < 2^(Suc n) \<and> j=0" by auto
      then have "(Matrix.mat (2^n) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)
      \<Otimes> (Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))) $$ (i,j)
        = (Matrix.mat (2^n) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)) $$ (i div 2, j div 2)
        * (Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))$$ (i mod 2, j mod 2)" 
        by (smt One_nat_def add_self_mod_2 dim_col_mat(1) dim_row_mat(1) index_tensor_mat less_numeral_extra(1) mod_add_self1 mod_div_trivial mod_if one_add_one one_power2 plus_1_eq_Suc plus_nat.simps(2) power_Suc2 power_one_right)
      then have "(Matrix.mat (2^n) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)
      \<Otimes> (Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))) $$ (i,j)
        = (exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..n}. (bin_rep n (of_nat (i div 2)))!(l-1)/2^l))
        * exp(complex_of_real(2*pi)*\<i>*jd*(of_nat (i mod 2))/2^(nat (Suc n))))*1/sqrt(2)^(Suc n)" using f0 by auto
      then have "(Matrix.mat (2^n) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)
      \<Otimes> (Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))) $$ (i,j)
        = (exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..n}. (bin_rep n (of_nat (i div 2)))!(l-1)/2^l) 
        + complex_of_real(2*pi)*\<i>*jd*(of_nat (i mod 2))/2^(nat (Suc n))))*1/sqrt(2)^(Suc n)"
        by (simp add: exp_add)
      moreover have "complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..n}. (bin_rep n (of_nat (i div 2)))!(l-1)/2^l)
                   + complex_of_real(2*pi)*\<i>*jd*(of_nat (i mod 2))/2^(nat (Suc n))
        = complex_of_real(2*pi)*\<i>*jd*((\<Sum>l\<in>{1..n}. (bin_rep n (i div 2))!(l-1)/2^l) + (of_nat (i mod 2))/2^(nat (Suc n)))" 
        using distrib_left[of "(complex_of_real(2*pi)*\<i>*jd)" "(\<Sum>l\<in>{1..n}. (bin_rep n (of_nat (i div 2)))!(l-1)/2^l)" 
                              "(of_nat (i mod 2))/2^(nat (Suc n))"] by auto
      ultimately have "(Matrix.mat (2^n) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)
      \<Otimes> (Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))) $$ (i,j)
        = (exp(complex_of_real(2*pi)*\<i>*jd*((\<Sum>l\<in>{1..n}. (bin_rep n (i div 2))!(l-1)/2^l) + (of_nat (i mod 2))/2^(nat (Suc n)))))*1/sqrt(2)^(Suc n)"
        by auto
      moreover have "(\<Sum>l\<in>{1..n}. (bin_rep n (i div 2))!(l-1)/2^l) + (of_nat (i mod 2))/2^(nat (Suc n))
                    = (\<Sum>l\<in>{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l)"
      proof-
        have "(i mod 2) = (bin_rep (Suc n) i)!((Suc n)-1)" 
          using a0 f0
          by (metis bin_rep_coeff bin_rep_even bin_rep_odd diff_less dvd_imp_mod_0 le_SucI le_imp_less_Suc less_one odd_iff_mod_2_eq_one zero_le) 
        then have "(\<Sum>l\<in>{1..n}. (bin_rep n (i div 2))!(l-1)/2^l) + (of_nat (i mod 2))/2^(nat (Suc n))
           = (\<Sum>l\<in>{1..n}. (bin_rep n (i div 2))!(l-1)/2^l) + ((bin_rep (Suc n) i)!((Suc n)-1))/2^(nat (Suc n))" by auto
        moreover have "(\<Sum>l\<in>{1..n}. (bin_rep n (i div 2))!(l-1)/2^l) = (\<Sum>l\<in>{1..n}. (bin_rep (Suc n) i)!(l-1)/2^l)" 
            using bin_rep_div a1 a0 assms atLeastAtMost_iff f0 by auto
        ultimately have "(\<Sum>l\<in>{1..n}. (bin_rep n (i div 2))!(l-1)/2^l) + (of_nat (i mod 2))/2^(nat (Suc n))
           =  (\<Sum>l\<in>{1..n}. (bin_rep (Suc n) i)!(l-1)/2^l) + ((bin_rep (Suc n) i)!((Suc n)-1))/2^(nat (Suc n))"
          by auto
        then have "(\<Sum>l\<in>{1..n}. (bin_rep n (i div 2))!(l-1)/2^l) + (of_nat (i mod 2))/2^(nat (Suc n))
           =  (\<Sum>l\<in>{1..n}. (bin_rep (Suc n) i)!(l-1)/2^l) + ((bin_rep (Suc n) i)!((Suc n)-1))/2^(Suc n)" 
          by (metis nat_int)
        moreover have "(\<Sum>l\<in>{1..n}. (bin_rep (Suc n) i)!(l-1)/2^l) + ((bin_rep (Suc n) i)!((Suc n)-1))/2^(Suc n)
           = (\<Sum>l\<in>{1..(Suc n)}. (bin_rep (Suc n) i)!(l-1)/2^l)" by auto
        ultimately show ?thesis by auto
      qed
      ultimately have "(Matrix.mat (2^n) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)
      \<Otimes> (Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))) $$ (i,j)
        = (exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l)))*1/sqrt(2)^(Suc n)"
        by presburger
      moreover have "(Matrix.mat (2^(Suc n)) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l))*1/sqrt(2)^(Suc n))) $$ (i,j)
      = exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l))*1/sqrt(2)^(Suc n)" using f0 by auto
      ultimately show "(Matrix.mat (2^n) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)
      \<Otimes> (Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))) $$ (i,j)
        = (Matrix.mat (2^(Suc n)) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l))*1/sqrt(2)^(Suc n))) $$ (i,j) "
        by auto
    next
      show "dim_row (Matrix.mat (2^n) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)
      \<Otimes> (Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2))))
        = dim_row (Matrix.mat (2^(Suc n)) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l))*1/sqrt(2)^(Suc n)))"
        by auto
    next
      show "dim_col (Matrix.mat (2^n) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)
      \<Otimes> (Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2))))
        = dim_col (Matrix.mat (2^(Suc n)) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l))*1/sqrt(2)^(Suc n)))"
        by auto
    qed
    ultimately show "(pw [Matrix.mat 2 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..(Suc n)] ] (Suc n))
       =  Matrix.mat (2^(Suc n)) 1 (\<lambda>(i,j). exp(complex_of_real(2*pi)*\<i>*jd*(\<Sum>l\<in>{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l))*1/sqrt(2)^(Suc n))"
      by auto
  qed
qed


















lemma
  shows "Matrix.mat (2^m) 1 (\<lambda>(i,j). exp(2*pi*\<i>*((\<Sum>k\<in>{0..<i}. (bin_rep n i) ! k * (bin_rep n j) ! k))/2^m)/(sqrt(2)^m)) 
      = (qr 1 m m j) \<Otimes> (Matrix.mat (2^m) 1 (\<lambda>(i,j). exp(2*pi*\<i>*(bip i m j)/2^m)/(sqrt(2)^m)))"
  sorry


(*subsection \<open>The Bitwise Inner Product\<close> (* contribution by Hanna Lachnitt *)

definition bitwise_inner_prod:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"bitwise_inner_prod n i j = (\<Sum>k\<in>{0..<n}. (bin_rep n i) ! k * (bin_rep n j) ! k)"

abbreviation bip:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" ("_ \<cdot>\<^bsub>_\<^esub>  _") where
"bip i n j \<equiv> bitwise_inner_prod n i j"
*)

end