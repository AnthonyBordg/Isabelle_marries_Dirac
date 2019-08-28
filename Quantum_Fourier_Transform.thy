theory Quantum_Fourier_Transform
imports
  More_Tensor
  Binary_Nat
  Basics
begin

(*A lot of the proofs are ad hoc and by no means perfect. Feel free to revise them. Since the approach 
was a bit risky my tactic was to first try out what could be achieved with it. Also I made a lot of 
changes and just adapted proofs as fast as possible.*)
(*There might be some errors later on (esp. false indices) as I revised the file and this changed a lot 
of definitions.*)
(*There might be a lot of lemmas be able to be written without pw. But I am not sure at this point so I 
will leave them in at first.*)
(*It might be nice to change all assumptions of the form
   "(\<forall>x \<in> set xs. dim_row x = 2)" and "(\<forall>y \<in> set ys. dim_row y = 2)"
 into "(\<forall>x \<in> set xs. x =zero \<or> x=one)" 
*)


(*Use the other defs right now to not worry about ket_vec_def all the time. Can switch to this easily later
abbreviation zero where "zero \<equiv> unit_vec 2 0"
abbreviation one where "one \<equiv> unit_vec 2 1" 
When I used abbreviation there where strange errors so I changed this. Some proof might be shortable now*)

definition zero where "zero = (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1 else 0))"
definition one where "one = (Matrix.mat 2 1 (\<lambda>(i,j). if i=1 then 1 else 0))" 


lemma Id_left_tensor: (*Could go into some other theory as well*)
  shows "(Id 0) \<Otimes> A = A"
proof
  fix i j
  assume a0: "i < dim_row A" and a1: "j < dim_col A" 
  have "((Id 0) \<Otimes> A) $$ (i,j) = (Id 0) $$ (i div (dim_row A), j div (dim_col A)) * A $$(i mod (dim_row A), j mod (dim_col A))"
    using index_tensor_mat one_mat_def a0 a1 Id_def by auto
  moreover have "i div (dim_row A) = 0" using a0 by auto
  moreover have "j div (dim_col A) = 0" using a1 by auto
  moreover have "i mod (dim_row A) = i" using a0 by auto
  moreover have "j mod (dim_col A) = j" using a1 by auto
  ultimately show "((Id 0) \<Otimes> A) $$ (i,j) = A $$(i, j)"
    using one_mat_def Id_def by auto
next
  show "dim_row ((Id 0) \<Otimes> A) = dim_row A" using one_mat_def Id_def by auto
next
  show "dim_col ((Id 0) \<Otimes> A) = dim_col A" using one_mat_def Id_def by auto
qed

lemma Id_right_tensor:
  shows "A \<Otimes> (Id 0) = A" 
proof
  fix i j
  assume a0: "i < dim_row A" and a1: "j < dim_col A" 
  have "(A \<Otimes> (Id 0)) $$ (i,j) 
  = A $$ (i div (dim_row (Id 0)), j div (dim_col (Id 0))) * (Id 0) $$(i mod (dim_row (Id 0)), j mod (dim_col (Id 0)))"
    using index_tensor_mat one_mat_def a0 a1 Id_def by auto
  moreover have "i div (dim_row (Id 0)) = i" using a0 Id_def by auto
  moreover have "j div (dim_col (Id 0)) = j" using a1 Id_def by auto
  moreover have "i mod (dim_row (Id 0)) = 0" using a0 Id_def by auto
  moreover have "j mod (dim_col (Id 0)) = 0" using a1 Id_def by auto
  ultimately show "(A \<Otimes> (Id 0)) $$ (i,j) = A $$(i, j)"
    using one_mat_def Id_def by auto
next
  show "dim_row (A \<Otimes> (Id 0)) = dim_row A" using one_mat_def Id_def by auto
next
  show "dim_col (A \<Otimes> (Id 0)) = dim_col A" using one_mat_def Id_def by auto
qed


lemma Id_mult_left: 
  assumes "dim_row A = 2^m"
  shows "Id m * A = A"
  using Id_def one_mat_def by (simp add: assms)

lemma aux_calculation[simp]:
  fixes m k c::nat
  shows "m>k \<and> k\<ge>1 \<longrightarrow> (2::nat) ^ (k - Suc 0) * 2 * 2 ^ (m - k) = 2^m"
    and "m>k \<and> k\<ge>1 \<longrightarrow> (2::nat) ^ (m - Suc 0) = 2 ^ (k - Suc 0) * 2 ^ (m - k)"
    and "m>k \<longrightarrow> Suc (m - Suc k) = m - k" 
    and "1\<le>k-c \<and> m>k \<and> m\<ge>c \<longrightarrow> (2::nat)^(k-Suc c) * 2 * 2^(m-k) = 2^(m-c)" 
    and "c\<le>m \<and> k\<ge>c+1 \<and> m\<ge>(Suc k) \<longrightarrow> k - c - 1 + 2 + (m - Suc k) = m-c"
    and "1\<le>k-c \<and> m>k \<and> m\<ge>c \<longrightarrow> (2::nat) * 2^(k-c-1) * 2 * 2^(m-k) = 2^(m-c+1)" 
    and "1\<le>k-c \<and> m>k \<and> m\<ge>c \<longrightarrow> (2::nat) ^ (m - c) = 2 * 2 ^ (k - Suc c) * 2 ^ (m - k)"
proof-
  show "m>k \<and> k\<ge>1 \<longrightarrow> (2::nat) ^ (k - Suc 0) * 2 * 2 ^ (m - k) = 2^m"
    by (metis One_nat_def le_add_diff_inverse less_or_eq_imp_le not_less_eq_eq power_add power_commutes power_eq_if)
next
  show "m>k \<and> k\<ge>1 \<longrightarrow> (2::nat) ^ (m - Suc 0) = 2 ^ (k - Suc 0) * 2 ^ (m - k)"
    by (metis Nat.add_diff_assoc2 One_nat_def le_add_diff_inverse less_or_eq_imp_le power_add)
next
  show "m>k \<longrightarrow> Suc (m - Suc k) = m - k" 
    using Suc_diff_Suc by blast
next
  show "1\<le>k-c \<and> m>k \<and> m\<ge>c \<longrightarrow> (2::nat)^(k-Suc c) * 2 * 2^(m-k) = 2^(m-c)" 
    by (metis Nat.add_diff_assoc2 One_nat_def Suc_diff_Suc Suc_le_eq le_add_diff_inverse nat_diff_split not_le not_one_le_zero power_add semiring_normalization_rules(28) zero_less_diff)
next
  show "c\<le>m \<and> k\<ge>c+1 \<and> m\<ge>(Suc k) \<longrightarrow> k - c - 1 + 2 + (m - Suc k) = m-c" by auto
next
  show "1\<le>k-c \<and> m>k \<and> m\<ge>c \<longrightarrow> (2::nat) * 2^(k-c-1) * 2 * 2^(m-k) = 2^(m-c+1)" 
    by (metis (no_types, lifting) Nat.add_diff_assoc2 le_add_diff_inverse less_or_eq_imp_le nat_diff_split not_le 
        not_one_le_zero power_add power_commutes semigroup_mult_class.mult.assoc semiring_normalization_rules(33))
next 
  show "1\<le>k-c \<and> m>k \<and> m\<ge>c \<longrightarrow> (2::nat) ^ (m - c) = 2 * 2 ^ (k - Suc c) * 2 ^ (m - k)" 
    by (metis (no_types, hide_lams) Nat.add_diff_assoc2 Nat.diff_diff_right Suc_diff_Suc diff_diff_cancel diff_le_self 
        less_imp_le_nat neq0_conv not_one_le_zero power_add semiring_normalization_rules(28) semiring_normalization_rules(7) 
        zero_less_diff)
qed


(*------------------------------------------------------------------------------------------------*)
(*---------------Transform j into a tensor product of single qubits ------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(*Gives back a part of j starting at s being t qubits long
E.g. $|01011\rangle$, s=2 and l=3 transforms to $[1,0,1]*)

primrec j_to_list_bound :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list" where
"j_to_list_bound s 0 m j = []" |
"j_to_list_bound s (Suc l) m j = (if (bin_rep m j)!(s-1) = 0 then zero else one) # (j_to_list_bound (s+1) l m j)"

(*TODO: Would exchanging the arguments help with induction problem?*) (*TODO: delete second argument?*)
(*Takes a list and the number of elements in this list and gives out the tensor product of the elements*)
fun pow_tensor_list :: "((complex Matrix.mat) list) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("pw _ _" 75)  where
  "(pw [] 0) = (Id 0)"  |
  "(pw (Cons x xs) (Suc k)) = x \<Otimes> (pw xs k)"

(*gives back a part of j as tensor product of single qubits s is the start and t the number of bits
where j is a decimal number that is smaller than m
I.e. $|j_1,...,j_n\rangle$ and s=2 and l=3 gives $|j_2,j_3,j_4\rangle$ *)
definition j_to_tensor_prod :: "nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>complex Matrix.mat" ("j\<Otimes> _ _ _ _" 75) where 
"(j\<Otimes> s l m j) = pw (j_to_list_bound s l m j) l"

(*Missing: result is gate, state,... Easy to proof*)

lemma j_to_list_bound_one [simp]:
  shows "j_to_list_bound s 1 m j = [(if (bin_rep m j)!(s-1) = 0 then zero else one)]" by simp

lemma pow_tensor_list_one [simp]:
  assumes "xs = []" 
  shows "(pw (Cons x xs) 1) = x" 
  by (simp add: Id_right_tensor assms)

lemma j_to_tensor_prod_length_0[simp]:
  shows "(j\<Otimes> s 0 j m) = (Id 0)"    
  by (simp add: j_to_tensor_prod_def)

lemma j_to_tensor_prod_decomp_right_zero:
  shows "(bin_rep m j)!(s+l-1) = 0 \<longrightarrow> (j\<Otimes> s (l+1) m j) = (j\<Otimes> s l m j) \<Otimes> zero"
proof(induction l arbitrary: s)
  show "(bin_rep m j)!(s+0-1) = 0 \<longrightarrow> (j\<Otimes> s (0+1) m j) = (j\<Otimes> s 0 m j) \<Otimes> zero" for s
  proof
    assume a0: "(bin_rep m j)!(s+0-1) = 0"
    have "(j\<Otimes> s 1 m j) = pw (j_to_list_bound s 1 m j) 1" using j_to_tensor_prod_def by auto
    then have "(j\<Otimes> s 1 m j) = pw ([(if (bin_rep m j)!(s-1) = 0 then zero else one)]) 1" 
      using j_to_list_bound_one by auto
    then have "(j\<Otimes> s 1 m j) = zero" using a0 pow_tensor_list_one by auto
    then show "(j\<Otimes> s (0+1) m j) = (j\<Otimes> s 0 m j) \<Otimes> zero" using j_to_tensor_prod_def Id_left_tensor by auto
  qed
next
  fix l s
  assume IH: "(bin_rep m j)!(s+l-1) = 0 \<longrightarrow> (j\<Otimes> s (l+1) m j) = (j\<Otimes> s l m j) \<Otimes> zero" for s
  show "(bin_rep m j)!(s+(Suc l)-1) = 0 \<longrightarrow> (j\<Otimes> s ((Suc l)+1) m j) = (j\<Otimes> s (Suc l) m j) \<Otimes> zero"
  proof
    assume a0: "(bin_rep m j)!(s+(Suc l)-1) = 0"
    have "(j\<Otimes> s ((Suc l)+1) m j) = pw ((if (bin_rep m j)!(s-1) = 0 then zero else one) # (j_to_list_bound (s+1) (Suc l) m j)) ((Suc l)+1)" 
      using j_to_tensor_prod_def by auto
    then have "(j\<Otimes> s ((Suc l)+1) m j) = (if (bin_rep m j)!(s-1) = 0 then zero else one) \<Otimes> pw ((j_to_list_bound (s+1) (Suc l) m j)) (Suc l)" 
      by simp
    then have "(j\<Otimes> s ((Suc l)+1) m j) = (if (bin_rep m j)!(s-1) = 0 then zero else one) \<Otimes> (j\<Otimes> (s+1) (l+1) m j)" 
      by (metis Suc_eq_plus1 j_to_tensor_prod_def)
    then have "(j\<Otimes> s ((Suc l)+1) m j) = (if (bin_rep m j)!(s-1) = 0 then zero else one) \<Otimes> (j\<Otimes> (s+1) l m j) \<Otimes> zero"
      using a0 IH tensor_mat_is_assoc by auto
    then have "(j\<Otimes> s ((Suc l)+1) m j) = (if (bin_rep m j)!(s-1) = 0 then zero else one) \<Otimes> (pw (j_to_list_bound (s+1) l m j) l) \<Otimes> zero"
      using j_to_tensor_prod_def by auto
    then have "(j\<Otimes> s ((Suc l)+1) m j) = (pw (j_to_list_bound s (l+1) m j) (l+1)) \<Otimes> zero"
      by auto
    then show "(j\<Otimes> s ((Suc l)+1) m j) = (j\<Otimes> s (Suc l) m j) \<Otimes> zero"
      using j_to_tensor_prod_def by auto
  qed
qed

lemma j_to_tensor_prod_decomp_right_one:
   shows "(bin_rep m j)!(s+l-1) = 1 \<longrightarrow> (j\<Otimes> s (l+1) m j) = (j\<Otimes> s l m j) \<Otimes> one"
proof(induction l arbitrary: s)
  show "(bin_rep m j)!(s+0-1) = 1 \<longrightarrow> (j\<Otimes> s (0+1) m j) = (j\<Otimes> s 0 m j) \<Otimes> one" for s
  proof
    assume a0: "(bin_rep m j)!(s+0-1) = 1"
    have "(j\<Otimes> s 1 m j) = pw (j_to_list_bound s 1 m j) 1" using j_to_tensor_prod_def by auto
    then have "(j\<Otimes> s 1 m j) = pw ([(if (bin_rep m j)!(s-1) = 0 then zero else one)]) 1" 
      using j_to_list_bound_one by auto
    then have "(j\<Otimes> s 1 m j) = one" using a0 pow_tensor_list_one by auto
    then show "(j\<Otimes> s (0+1) m j) = (j\<Otimes> s 0 m j) \<Otimes> one" using j_to_tensor_prod_def Id_left_tensor by auto
  qed
next
  fix l s
  assume IH: "(bin_rep m j)!(s+l-1) = 1 \<longrightarrow> (j\<Otimes> s (l+1) m j) = (j\<Otimes> s l m j) \<Otimes> one" for s
  show "(bin_rep m j)!(s+(Suc l)-1) = 1 \<longrightarrow> (j\<Otimes> s ((Suc l)+1) m j) = (j\<Otimes> s (Suc l) m j) \<Otimes> one"
  proof
    assume a0: "(bin_rep m j)!(s+(Suc l)-1) = 1"
    have "(j\<Otimes> s ((Suc l)+1) m j) = pw ((if (bin_rep m j)!(s-1) = 0 then zero else one) # (j_to_list_bound (s+1) (Suc l) m j)) ((Suc l)+1)" 
      using j_to_tensor_prod_def by auto
    then have "(j\<Otimes> s ((Suc l)+1) m j) = (if (bin_rep m j)!(s-1) = 0 then zero else one) \<Otimes> pw ((j_to_list_bound (s+1) (Suc l) m j)) (Suc l)" 
      by simp
    then have "(j\<Otimes> s ((Suc l)+1) m j) = (if (bin_rep m j)!(s-1) = 0 then zero else one) \<Otimes> (j\<Otimes> (s+1) (l+1) m j)" 
      by (metis Suc_eq_plus1 j_to_tensor_prod_def)
    then have "(j\<Otimes> s ((Suc l)+1) m j) = (if (bin_rep m j)!(s-1) = 0 then zero else one) \<Otimes> (j\<Otimes> (s+1) l m j) \<Otimes> one"
      using a0 IH tensor_mat_is_assoc by auto
    then have "(j\<Otimes> s ((Suc l)+1) m j) = (if (bin_rep m j)!(s-1) = 0 then zero else one) \<Otimes> (pw (j_to_list_bound (s+1) l m j) l) \<Otimes> one"
      using j_to_tensor_prod_def by auto
    then have "(j\<Otimes> s ((Suc l)+1) m j) = (pw (j_to_list_bound s (l+1) m j) (l+1)) \<Otimes> one"
      by auto
    then show "(j\<Otimes> s ((Suc l)+1) m j) = (j\<Otimes> s (Suc l) m j) \<Otimes> one"
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
      then have "\<exists>x. xs = x # tl xs" using a0 by (metis length_Suc_conv list.sel(3))
      moreover have "xs = x # tl xs \<longrightarrow> dim_col (pw xs (Suc k)) = 1" for x
      proof
        assume a2: "xs = x # tl xs"
        moreover have f1: "length (tl xs) = k" using a0 by force
        moreover have "tl xs = [] \<longrightarrow> dim_col (x \<Otimes> pw tl xs k) = dim_col (pw xs Suc k)" 
          using IH a2 f1 by auto 
        ultimately have "dim_col (pw xs (Suc k)) = dim_col (x \<Otimes> (pw (tl xs) k))" using pow_tensor_list.simps 
          using f1 a2 by metis
        then have "dim_col (pw xs (Suc k)) = 1 * dim_col ((pw (tl xs) k))" 
          using a0 a1 a2 by (metis dim_col_tensor_mat list.set_intros(1))
        then show "dim_col (pw xs (Suc k)) = 1" using IH a0 a1 f1 a2
          by (metis list.discI list.set_sel(2) mult.left_neutral)
      qed
      ultimately show "dim_col (pw xs (Suc k)) = 1" by blast
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
      then have "\<exists>x. xs = x # tl xs" using a0 by (metis length_Suc_conv list.sel(3))
      moreover have "xs = x # tl xs \<longrightarrow> dim_row (pw xs (Suc k)) = m^(Suc k)" for x
      proof
        assume a2: "xs = x # tl xs"
        moreover have f1: "length (tl xs) = k" using a0 by force
        moreover have "tl xs = [] \<longrightarrow> dim_row (x \<Otimes> pw tl xs k) = dim_row (pw xs Suc k)" 
          using IH a2 f1 by auto 
        ultimately have "dim_row (pw xs (Suc k)) = dim_row (x \<Otimes> (pw (tl xs) k))" using pow_tensor_list.simps 
          using f1 a2 by metis
        then have "dim_row (pw xs (Suc k)) = m * dim_row ((pw (tl xs) k))" 
          using a1 a2 by (metis dim_row_tensor_mat list.set_intros(1))
        then show "dim_row (pw xs (Suc k)) = m^(Suc k)" 
          by (metis IH a0 a1 f1 length_0_conv list.set_sel(2) mult.commute nat.simps(3) power_Suc)
      qed
      ultimately show "dim_row (pw xs (Suc k)) = m^(Suc k)" by blast
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
        then have "pw (xs@[x]) ((Suc k)+1) = (y \<Otimes> (pw ys k)) \<Otimes> x" using tensor_mat_is_assoc by auto
        then have "pw (xs@[x]) ((Suc k)+1) = (pw (y#ys) (Suc k)) \<Otimes> x" using pow_tensor_list.simps 
          by (metis One_nat_def Suc_pred a0 less_eq_Suc_le) 
        then show "pw (xs@[x]) ((Suc k)+1) = (pw xs (Suc k)) \<Otimes> x" using a2 by auto
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
                                                 # (j_to_list_bound (s+1) l m j))" 
    using j_to_list_bound.simps by auto
  then have "length (j_to_list_bound s (Suc l) m j) = length [(if (bin_rep m j)!(s-1) = 0 then zero else one)]
                                                    + length (j_to_list_bound (s+1) l m j)"
    by simp
  moreover have "length [(if (bin_rep m j)!(s-1) = 0 then zero else one)] = 1" by auto
  moreover have " length (j_to_list_bound (s+1) l m j) = l" using IH by auto
  ultimately show "length (j_to_list_bound s (Suc l) m j) = (Suc l)" by auto
qed

lemma j_to_list_bound_dim_row:
  shows "\<forall>x\<in>set (j_to_list_bound s l m j). dim_row x = 2"
proof(induction l arbitrary: s)
  show "\<forall>x\<in>set (j_to_list_bound s 0 m j). dim_row x = 2" for s by auto
next
  fix l s
  assume IH: "\<forall>x\<in>set (j_to_list_bound s l m j). dim_row x = 2" for s
  show "\<forall>x\<in>set (j_to_list_bound s (Suc l) m j). dim_row x = 2"
  proof
    fix x 
    assume a0: "x \<in> set (j_to_list_bound s (Suc l) m j)"
    then have "set (j_to_list_bound s (Suc l) m j) = set ((if (bin_rep m j)!(s-1) = 0 then zero else one) # (j_to_list_bound (s+1) l m j))"
      using j_to_list_bound_def by auto
    then show "dim_row x = 2"
      using IH a0 zero_def one_def by (smt dim_row_mat(1) set_ConsD)
  qed
qed

lemma j_to_list_bound_dim_col:
  shows "\<forall>x\<in>set (j_to_list_bound s l m j). dim_col x = 1"
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
      using IH a0 zero_def one_def by (smt dim_col_mat(1) set_ConsD)
  qed
qed

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
  then have "(j\<Otimes> s l m j) = pw ((if (bin_rep m j)!(s-1) = 0 then zero else one) # (j_to_list_bound (s+1) (l-1) m j)) l"
    using assms by (metis j_to_list_bound.simps(2) ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
  then have "(j\<Otimes> s l m j) = pw (zero # (j_to_list_bound (s+1) (l-1) m j)) l"
    using assms by auto
  then have "(j\<Otimes> s l m j) = zero \<Otimes> pw (j_to_list_bound (s+1) (l-1) m j) (l-1)"
    using assms pow_tensor_list.simps by (metis One_nat_def Suc_pred less_eq_Suc_le)
  then show "(j\<Otimes> s l m j) = zero \<Otimes> (j\<Otimes> (s+1) (l-1) m j)"
    using j_to_tensor_prod_def by auto
qed

lemma j_to_tensor_prod_decomp_left_one:
  assumes "l\<ge>1" and "(bin_rep m j)!(s-1) = 1"
  shows "(j\<Otimes> s l m j) = one \<Otimes> (j\<Otimes> (s+1) (l-1) m j)"
proof- 
  have "(j\<Otimes> s l m j) = pw (j_to_list_bound s l m j) l"
    using j_to_tensor_prod_def by auto
  then have "(j\<Otimes> s l m j) = pw ((if (bin_rep m j)!(s-1) = 0 then zero else one) # (j_to_list_bound (s+1) (l-1) m j)) l"
    using assms by (metis j_to_list_bound.simps(2) ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
  then have "(j\<Otimes> s l m j) = pw (one # (j_to_list_bound (s+1) (l-1) m j)) l"
    using assms by auto
  then have "(j\<Otimes> s l m j) = one \<Otimes> pw (j_to_list_bound (s+1) (l-1) m j) (l-1)"
    using assms pow_tensor_list.simps by (metis One_nat_def Suc_pred less_eq_Suc_le)
  then show "(j\<Otimes> s l m j) = one \<Otimes> (j\<Otimes> (s+1) (l-1) m j)"
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
  then have "(j\<Otimes> (s+t) 1 m j) = pw (j_to_list_bound (s+t) 1 m j) 1" 
    using j_to_tensor_prod_def by auto
  then have "(j\<Otimes> (s+t) 1 m j) = (if (bin_rep m j)!(s+t-1) = 0 then zero else one)" 
    using pow_tensor_list_one by auto
  then have "(j\<Otimes> (s+t) 1 m j) = zero" 
    using a0 by auto
  moreover have "(j\<Otimes> s (t+1) m j) = (j\<Otimes> s t m j) \<Otimes> zero"
    using j_to_tensor_prod_decomp_right_zero a0 by auto
  ultimately show ?thesis by auto
next
  assume a0: "(bin_rep m j)!(s+t-1) = 1"
  then have "(j\<Otimes> (s+t) 1 m j) = pw (j_to_list_bound (s+t) 1 m j) 1" 
    using j_to_tensor_prod_def by auto
  then have "(j\<Otimes> (s+t) 1 m j) = (if (bin_rep m j)!(s+t-1) = 0 then zero else one)" 
    using pow_tensor_list_one by auto
  then have "(j\<Otimes> (s+t) 1 m j) = one" 
    using a0 by auto
  moreover have "(j\<Otimes> s (t+1) m j) = (j\<Otimes> s t m j) \<Otimes> one"
    using j_to_tensor_prod_decomp_right_one a0 by auto
  ultimately show ?thesis by auto
qed

lemma j_to_tensor_prod_decomp_half:
  fixes j m t::nat
  assumes "j < 2^m" and "n>s" and "n\<le>m" and "s\<le>m" and "t\<ge>n-s"
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
    then have "s+t-1 < m" 
      using assms(2) assms(3) by linarith
    then have "(j\<Otimes> s (t+1) m j) = (j\<Otimes> s t m j) \<Otimes> (j\<Otimes> (s+t) 1 m j)" 
      using j_to_tensor_prod_decomp_right assms by blast
    then have "(j\<Otimes> s (t+1) m j) = ((j\<Otimes> s (n-s) m j) \<Otimes> (j\<Otimes> n (t-(n-s)) m j)) \<Otimes> (j\<Otimes> (s+t) 1 m j)" 
      using IH a1 by auto
    then have "(j\<Otimes> s (t+1) m j) = (j\<Otimes> s (n-s) m j) \<Otimes> ((j\<Otimes> n (t-(n-s)) m j) \<Otimes> (j\<Otimes> (s+t) 1 m j))" 
      using tensor_mat_is_assoc by auto
    moreover have "(j\<Otimes> n (t-(n-s)+1) m j) = (j\<Otimes> n (t-(n-s)) m j) \<Otimes> (j\<Otimes> (s+t) 1 m j)"
    proof-
      have "n + (t - (n - s)) - 1 < m" using assms a1 by linarith
      then have "j\<Otimes> n (t-(n-s)+1) m j = (j\<Otimes> n (t-(n-s)) m j) \<Otimes> (j\<Otimes> (n+(t-(n-s))) 1 m j)"
        using j_to_tensor_prod_decomp_right[of j m n "(t-(n-s))"] assms a0 by auto
      moreover have "n+(t-(n-s)) = t+s" using assms a0 a1 by linarith
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
  assumes "j < 2^m" and "n>s" and "n\<le>m" and "s\<le>m" and "t\<ge>n-s" and "s+t-1 \<le> m"
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

(*This is where I stoped today. Why is this so hard? Look at it tomorrow*)
lemma eq_matE: 
  assumes "A = B" 
  shows "(\<And> i j . i < dim_row B \<Longrightarrow> j < dim_col B \<Longrightarrow> A $$ (i,j) = B $$ (i,j))"
  using assms by blast

lemma zero_neq_one:
  shows "zero \<noteq> one" 
proof(rule ccontr)
  have "zero $$ (0,0) = 1" by (simp add: zero_def)
  moreover have "one $$ (0,0) = 0" by (simp add: one_def)
  moreover have " 0 < dim_row Quantum_Fourier_Transform.one" sorry
  moreover have "0 < dim_col Quantum_Fourier_Transform.one" sorry
  ultimately show ?thesis using eq_matE[of zero one 0 0] zero_def one_def sorry
qed


lemma j_to_tensor_bin_rep_zero:
  fixes n m j::nat
  assumes "n\<ge>1"
  shows "(j\<Otimes> n 1 m j) = zero \<longleftrightarrow> bin_rep m j ! (n-1) = 0"
proof
  assume a0: "(j\<Otimes> n 1 m j) = zero"
  have "(j\<Otimes> n 1 m j) = (if (bin_rep m j)!(n-1) = 0 then zero else one)"
    using j_to_tensor_prod_def pow_tensor_list_one by auto 
  moreover have "Matrix.mat 2 (Suc 0) (\<lambda>(i, j). if i = Suc 0 then 1 else 0) \<noteq> Matrix.mat 2 (Suc 0) (\<lambda>(i, j). if i = 0 then 1 else 0)"
    using zero_def one_def a0 zero_neq_one 
    by (metis numeral_1_eq_Suc_0 numeral_One)
  ultimately have "zero = (if (bin_rep m j)!(n-1) = 0 then zero else one)"
    using a0 by (smt zero_neq_one)
  then show "bin_rep m j ! (n-1) = 0" using a0 
    by (smt zero_def one_def zero_neq_one)
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
  ultimately show "bin_rep m j ! (n-1) = 1" using a0 by (smt zero_neq_one)
next
  assume a0: "bin_rep m j ! (n - 1) = 1"
  then show "(j\<Otimes> n 1 m j) = one"
    using j_to_tensor_prod_def pow_tensor_list_one by auto 
qed

lemma decomp_unit_vec_zero_left:
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

lemma decomp_unit_vec_zero_right:
  fixes k::nat
  assumes "k\<ge>1" and "m<2^k" and "even m" 
  shows "|unit_vec (2^k) m\<rangle> = |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero" 
proof
  fix i j
  assume a0: "i < dim_row ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero)" 
     and a1: "j < dim_col ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero)" 
  then have f0: "i < 2^k \<and> j=0" 
    by (metis (no_types, lifting) One_nat_def assms(1) dim_col_mat(1) dim_col_tensor_mat dim_row_mat(1) dim_row_tensor_mat index_unit_vec(3) ket_vec_def less_eq_Suc_le less_one one_power2 power2_eq_square power_minus_mult)
  then have f1: "( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero) $$ (i,j) = |unit_vec (2^(k-1)) (m div 2)\<rangle> $$ (i div 2, j div 1) 
        * zero $$ (i mod 2, j mod 1)" using unit_vec_def assms ket_vec_def zero_def a0 by fastforce
  show "( |unit_vec (2^k) m\<rangle> ) $$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero) $$ (i,j)"
  proof (rule disjE)
    show "i=m \<or> i\<noteq>m" by auto
  next
    assume a2: "i = m"
    then have "( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero) $$ (i,j) = 1"
      using ket_vec_def unit_vec_def a0 f0 assms by auto
    then show "( |unit_vec (2^k) m\<rangle> ) $$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero) $$ (i,j)"
      using ket_vec_def unit_vec_def f0 a2 by auto
  next
    assume a2: "i \<noteq> m"
    show "( |unit_vec (2^k) m\<rangle> ) $$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero) $$ (i,j)"
    proof(rule disjE)
      show "i div 2 = m div 2 \<or> i div 2 \<noteq> m div 2" by auto
    next
      assume "i div 2 = m div 2"
      then have "i=m+1" using a2 assms(3) by auto
      then have "i mod 2 = 1" using assms by auto
      then have "( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero) $$ (i,j) = 0" using f1 zero_def f0 by auto
      then show "( |unit_vec (2^k) m\<rangle> )$$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero) $$ (i,j)"
        using ket_vec_def unit_vec_def f0 a2 by (smt assms(2) index_unit_vec(1) index_unit_vec(3) ket_vec_index)
    next
      assume "i div 2 \<noteq> m div 2"
      then have "( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero) $$ (i,j) = 0" 
        using f1 ket_vec_def unit_vec_def 
        by (smt One_nat_def assms(1) assms(2) div_less f0 index_unit_vec(1) index_unit_vec(3) ket_vec_index less_eq_Suc_le less_mult_imp_div_less mult_eq_0_iff power_minus_mult zero_less_one_class.zero_less_one)
      then show "( |unit_vec (2^k) m\<rangle> )$$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero) $$ (i,j)"
        using ket_vec_def unit_vec_def f0 a2 by (smt assms(2) index_unit_vec(1) index_unit_vec(3) ket_vec_index)
    qed
  qed
next
  show "dim_row ( |unit_vec (2^k) m\<rangle> ) = dim_row ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero)"
    using unit_vec_def zero_def ket_vec_def 
    by (smt One_nat_def assms(1) dim_row_mat(1) dim_row_tensor_mat index_unit_vec(3) less_eq_Suc_le power_minus_mult)
next
  show "dim_col ( |unit_vec (2^k) m\<rangle> ) = dim_col ( |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> zero)"
    using unit_vec_def zero_def ket_vec_def by simp
qed

lemma decomp_unit_vec_one_left:
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


lemma decomp_unit_vec_one_right:
  fixes k::nat
  assumes "k\<ge>1" and "m<2^k" and "odd m" 
  shows "|unit_vec (2^k) m\<rangle> = |unit_vec (2^(k-1)) (m div 2)\<rangle> \<Otimes> one"
  sorry

lemma h1:
  fixes j n::nat
  assumes "n\<ge>1"
  shows "j div 2^(n-1) div 2 = j div 2^n" 
  by (metis One_nat_def Suc_1 assms diff_Suc_1 diff_self_eq_0 div_mult2_eq eq_iff less_imp_add_positive mult.commute not_less plus_1_eq_Suc power.simps(2))

lemma h2:
  fixes j m k::nat
  assumes "m \<ge> 1" and "k < m" and "(bin_rep m j)!k = 0 \<and> j < 2^m"
  shows "even (j div 2^(m-(Suc k)))" (*j div ... takes substring of binary rep which ends with 0 \<rightarrow> even*)
  sorry

lemma h3:
  fixes j m k::nat
  assumes "(bin_rep m j)!k = 0" and "m \<ge> 1" and "j < 2^m" and "k < m"
  shows "odd (j div 2^(m-(Suc k)))"
  sorry


lemma j_as_unit:
  fixes k j m::nat
  assumes "j < 2^m" and "k\<ge>1"
  shows "k \<le> m \<longrightarrow> (j\<Otimes> 1 k m j) = |unit_vec (2^k) (j div 2^(m-k))\<rangle>"
proof(rule Nat.nat_induct_at_least[of 1 k])
  show "k \<ge> 1" using assms by auto
next
  show "1 \<le> m \<longrightarrow> (j\<Otimes> 1 1 m j) = |unit_vec (2^1) (j div 2^(m-1))\<rangle>" sorry
next
  fix k 
  assume IH: "k \<le> m \<longrightarrow> (j\<Otimes> 1 k m j) = |unit_vec (2^k) (j div 2^(m-k))\<rangle>"
    and asm: "k\<ge>1"
  show "(Suc k) \<le> m \<longrightarrow> (j\<Otimes> 1 (Suc k) m j) = |unit_vec (2^(Suc k)) (j div 2^(m-(Suc k)))\<rangle>"
  proof
    assume a0: "(Suc k) \<le> m"
    show "(j\<Otimes> 1 (Suc k) m j) = |unit_vec (2^(Suc k)) (j div 2^(m-(Suc k)))\<rangle>"
    proof (rule disjE)
      show "(bin_rep m j)!k = 0 \<or> (bin_rep m j)!k = 1" 
        using bin_rep_coeff a0 assms(1) less_eq_Suc_le by blast
    next 
      assume a1: "(bin_rep m j)!k = 0"
      then have "(j\<Otimes> 1 (Suc k) m j) = (j\<Otimes> 1 k m j) \<Otimes> zero" 
        using j_to_tensor_prod_decomp_zero by auto
      then have "(j\<Otimes> 1 (Suc k) m j) = |unit_vec (2^k) (j div 2^(m-k))\<rangle> \<Otimes> zero" 
        using IH a0 Suc_leD by presburger
      then have "(j\<Otimes> 1 (Suc k) m j) = |unit_vec (2^k) (j div 2^(m-(Suc k)) div 2)\<rangle> \<Otimes> zero" 
        using h1[of "m-k" "j"] a0 by auto
      moreover have "even (j div 2^(m-(Suc k)))" using a0 assms sorry 
      ultimately show "(j\<Otimes> 1 (Suc k) m j) = |unit_vec (2^(Suc k)) (j div 2^(m-(Suc k)))\<rangle> " 
        using decomp_unit_vec_zero_right[of "(Suc k)" "(j div 2^(m-(Suc k)))"] asm 
        by (metis a0 assms(1) diff_Suc_1 le_SucI less_power_add_imp_div_less ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
    next
      show "(j\<Otimes> 1 (Suc k) m j) = |unit_vec (2^(Suc k)) (j div 2^(m-(Suc k)))\<rangle> " sorry
    qed
  qed
qed

lemma j_dec_as_unit:
  assumes "1 \<le> n" and "j < 2^n" 
  shows "(j\<Otimes> 1 n n j) = |unit_vec (2^n) j\<rangle>"
proof-
  have "(j\<Otimes> 1 n n j) = |unit_vec (2^n) (j mod 2^n)\<rangle>" using assms j_as_unit by auto
  moreover have "j mod 2^n = j" using assms by auto
  ultimately show ?thesis by auto
qed 


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


(*Missing: CR is gate*)

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

lemma SWAP_gate:
  shows "gate 2 SWAP" sorry

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
  assumes "m>k" and "k-c \<ge>1"
  shows "dim_row (fSWAP (k-c) (m-k)) = 2^(m-c)"
    and "dim_col (fSWAP (k-c) (m-k)) = 2^(m-c)"
  using SWAP_front_dim assms by auto

lemma Id_fSWAP_dim [simp]:
  assumes "m>k" and "k-c \<ge>1"
  shows "dim_row (Id 1 \<Otimes> (fSWAP (k-c) (m-k))) = 2^(m-c+1)"
    and "dim_col (Id 1 \<Otimes> (fSWAP (k-c) (m-k))) = 2^(m-c+1)"
  using SWAP_front_dim assms Id_def by auto


lemma SWAP_unitary:
  assumes "k\<ge>1"
  shows "unitary (fSWAP k t)" sorry

lemma SWAP_front_gate: 
  assumes "k\<ge>1" (*This is important ^^ Otw inconsistency*)
  shows "gate (k+t) (fSWAP k t)" sorry


lemma SWAP_front_hermite_cnj_dim:
  assumes "k\<ge>1"
  shows "dim_row (fSWAP k t)\<^sup>\<dagger> = 2^(k+t)"
  and "dim_col (fSWAP k t)\<^sup>\<dagger> = 2^(k+t)" 
  using SWAP_front_dim assms by auto

lemma Id_fSWAP_herm_cnj_dim [simp]:
  fixes k m c::nat
  assumes "m>k" and "k-c \<ge>1"
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
           length xs = k-c-1 \<and> length ys = m-k \<and> m>k \<longrightarrow> 
           (fSWAP (k-c) (m-k)) * ((pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) 
          = v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))" 
proof(rule Nat.nat_induct_at_least[of "c+1" k])
  show "k\<ge>c+1" using assms by auto
next
  show "\<forall>xs ys. (\<forall>x \<in> set xs. dim_row x = 2) \<and> (\<forall>y \<in> set ys. dim_row y = 2) \<and>
           (\<forall>x \<in> set xs. dim_col x = 1) \<and> (\<forall>y \<in> set ys. dim_col y = 1) \<and>
           length xs = ((c+1)-c-1) \<and> length ys = m-(c+1) \<and> m>(c+1) \<longrightarrow> 
           (fSWAP ((c+1)-c) (m-(c+1))) * ((pw xs ((c+1)-c-1)) \<Otimes> v \<Otimes> (pw ys (m-(c+1)))) 
          = v \<Otimes> (pw xs ((c+1)-c-1)) \<Otimes> (pw ys (m-(c+1)))" 
  proof(rule allI, rule allI, rule impI)
    fix xs ys::"complex Matrix.mat list"
    assume a0: "(\<forall>x \<in> set xs. dim_row x = 2) \<and> (\<forall>y \<in> set ys. dim_row y = 2) \<and>
           (\<forall>x \<in> set xs. dim_col x = 1) \<and> (\<forall>y \<in> set ys. dim_col y = 1) \<and>
           length xs = ((c+1)-c-1) \<and> length ys = m-(c+1) \<and> m>(c+1)"
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
           length xs = (k-c-1) \<and> length ys = m-k \<and> m>k  \<longrightarrow> 
           (fSWAP (k-c) (m-k)) * ((pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) 
          = v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))" 
  show "\<forall>xs ys. (\<forall>x \<in> set xs. dim_row x = 2) \<and> (\<forall>y \<in> set ys. dim_row y = 2) \<and>
           (\<forall>x \<in> set xs. dim_col x = 1) \<and> (\<forall>y \<in> set ys. dim_col y = 1) \<and>
           length xs = ((Suc k)-c-1) \<and> length ys = m-(Suc k) \<and> m>(Suc k)  \<longrightarrow> 
           (fSWAP ((Suc k)-c) (m-(Suc k))) * ((pw xs ((Suc k)-c-1)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) 
          = v \<Otimes> (pw xs ((Suc k)-c-1)) \<Otimes> (pw ys (m-(Suc k)))" 
  proof(rule allI, rule allI, rule impI)
    fix xs ys::"complex Matrix.mat list"
    assume a1: "(\<forall>x \<in> set xs. dim_row x = 2) \<and> (\<forall>y \<in> set ys. dim_row y = 2) \<and>
           (\<forall>x \<in> set xs. dim_col x = 1) \<and> (\<forall>y \<in> set ys. dim_col y = 1) \<and>
           length xs = ((Suc k)-c-1) \<and> length ys = m-(Suc k) \<and> m>(Suc k)" 
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
        by (smt Nat.le_diff_conv2 Suc_lessD a0 add.right_neutral add_Suc_right add_leD1 carrier_matI plus_1_eq_Suc)
      moreover have "(SWAP_all (k-c-1) (m-(Suc k))) \<in> carrier_mat (2^(m-c)) (2^(m-c))"
        using SWAP_all_dim[of "k-c-1" "m-(Suc k)"] aux_calculation(5) a1 assms by (smt a0 carrier_matI less_imp_le_nat)
      moreover have "((pw xs (k-c)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) \<in> carrier_mat (2^(m-c)) (2^(m-c))" 
        using pow_tensor_list_dim_row pow_tensor_list_dim_col assms a1 sorry
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
      moreover have "dim_row (last xs) = 2 \<and> dim_col (last xs) = 1" sorry
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
  assumes "k\<ge>c+1" and "k\<ge>1" and "c\<le>m"  and "m>k" and "dim_row v = 2" and "dim_col v = 1" 
      and "(\<forall>x \<in> set xs. dim_row x = 2)" and "(\<forall>y \<in> set ys. dim_row y = 2)"
      and "(\<forall>x \<in> set xs. dim_col x = 1)" and "(\<forall>y \<in> set ys. dim_col y = 1)" 
      and "length xs = (k-c-1)" and "length ys = m-k"
    shows "(fSWAP (k-c) (m-k)) * ((pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) 
          = v \<Otimes> (pw xs (k-c-1)) \<Otimes> (pw ys (m-k))" 
  using aux_app_fSWAP assms by auto





(*The current qubit should not be altered by the swapping *)
lemma app_Id_fSWAP:
  assumes "k\<ge>1" and "m>k" and "1\<le>k-c"and "m\<ge>c" 
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
  assumes "k\<ge>2" and "m\<ge>1" and "k<m" and "dim_row v = 2" and "dim_col v = 1" 
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
    by (metis hermite_cnj_dim_row index_mult_mat(2) SWAP_front_dim(1))
  then show "(fSWAP k t)\<^sup>\<dagger> * B = A" by (simp add: assms(3))
qed

lemma SWAP_front_herm_cnj_app:
  fixes k m c::nat 
  assumes "k-c\<ge>1" and "k\<ge>1" and "c\<le>m"  and "m>k" and "dim_row v = 2" and "dim_col v = 1" 
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
  assumes "k\<ge>2" and "m\<ge>1" and "k<m" 
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
          tensor_mat_is_assoc  by auto
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
  assumes "k\<ge>1" and "m>k" and "c \<le> k - 1" and "c\<le>m"  (*Rather c<m*)
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
  assumes "k-c\<ge>1" and "c\<ge>1" and "m>k"
  shows "dim_row (CR_on_all k c m) = 2^m"
    and "dim_col (CR_on_all k c m) = 2^m"
proof-
  have "dim_row (CR_on_all k c m) = dim_row (Id (c-1)) * dim_row ((Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)))"
    using CR_on_all_def by auto
  moreover have "2^(c-Suc 0) * (2 * 2^(k+(m-k)-c)) = (2::nat)^m" using assms 
    by (metis (no_types, lifting) One_nat_def Suc_le_eq aux_calculation(1) le_add_diff_inverse less_imp_le_nat semigroup_mult_class.mult.assoc trans_less_add1 zero_less_diff)
  ultimately show "dim_row (CR_on_all k c m) = 2^m"
    using Id_def[of "c-1"] Id_def[of 1] SWAP_front_hermite_cnj_dim[of "k-c" "m-k"] assms by auto
next
  have "dim_col (CR_on_all k c m) = dim_col (Id (c-1)) * dim_col (Id 1 \<Otimes> (fSWAP (k-c) (m-k)))"
    using CR_on_all_def by auto
  moreover have "2^(c-Suc 0) * (2 * 2^(k+(m-k)-c)) = (2::nat)^m" using assms 
    by (metis (no_types, lifting) One_nat_def Suc_le_eq aux_calculation(1) le_add_diff_inverse less_imp_le_nat semigroup_mult_class.mult.assoc trans_less_add1 zero_less_diff)
  ultimately show "dim_col (CR_on_all k c m) = 2^m"
    using Id_def[of "c-1"] Id_def[of 1] SWAP_front_hermite_cnj_dim[of "k-c" "m-k"] assms by auto
qed

lemma SWAP_front_hermite_cnj_dim:
  assumes "k\<ge>1"
  shows "dim_row (fSWAP k t)\<^sup>\<dagger> = 2^(k+t)"
  and "dim_col (fSWAP k t)\<^sup>\<dagger> = 2^(k+t)" 



lemma [simp]:
  fixes m k::nat
  assumes "m>k" and "k\<ge>1"
  shows "2 * ((2::nat) ^ (m - k) * 2 ^ (k - Suc 0)) = 2 ^ m"  
  by (metis Nat.add_diff_assoc One_nat_def add.commute assms(1) assms(2) less_imp_le_nat not_less_eq_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse power_add power_eq_if)



(*"c \<le> k - 1" Put this everywhere or put 1 \<le> k - c everywhere seems to cause a lot of problems *)
(*get indices right!*)
lemma app_CR_on_all_wo_Id:
  fixes k c m j::nat
  assumes "k\<ge>2" and "m\<ge>1" and "k<m" and "dim_row v = 2" and "dim_col v = 1" 
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
      have "dim_row ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k))) = 2^(m-c+1)" 
        using pow_tensor_list_dim_row[of xs "(k-c-1)" 2]  pow_tensor_list_dim_row[of ys "m-k" 2] assms 
          qr_def aux_calculation(6)[of k c m] 
        by (smt dim_row_mat(1) dim_row_tensor_mat f0)
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
  assumes "k\<ge>2" and "m\<ge>1" and "k<m" and "dim_row v = 2" and "dim_col v = 1" 
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
    have "dim_col (Id (c-1)) = dim_row (pw cs (c-1))" sorry
    moreover have "dim_col ((Id 1 \<Otimes> ((fSWAP (k-c) (m-k))\<^sup>\<dagger>)) * (CR (k-c+1) \<Otimes> Id (m-c-1)) * (Id 1 \<Otimes> (fSWAP (k-c) (m-k)))) 
        = dim_row ((qr c (k-1) m j) \<Otimes> (pw xs (k-c-1)) \<Otimes> v \<Otimes> (pw ys (m-k)))" sorry
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

lemma h11: 
  fixes n m j c::nat
  assumes "2 \<le> n " and "1 \<le> m " and "n < m"  
      and "dim_row (pw (j_to_list_bound n 1 m j) 1) = 2" and "dim_col (pw (j_to_list_bound n 1 m j) 1) = 1"
      and "1 \<le> c" and "c \<le> n - 1" and "c \<le> m " and
    "(pw (j_to_list_bound n 1 m j) 1) = Quantum_Fourier_Transform.zero \<or>
    (pw (j_to_list_bound n 1 m j) 1) = Quantum_Fourier_Transform.one" and
    "(pw (j_to_list_bound n 1 m j) 1) = Quantum_Fourier_Transform.zero \<longrightarrow> bin_rep m j ! (n - 1) = 0 "and
    "(pw (j_to_list_bound n 1 m j) 1) = Quantum_Fourier_Transform.one \<longrightarrow> bin_rep m j ! (n - 1) = 1 "and
    "\<forall>x\<in>set (j_to_list_bound (c+1) (n-(c+1)) m j). dim_row x = 2 "and
    "\<forall>y\<in>set (j_to_list_bound (n+1) (m-n) m j). dim_row y = 2 "and
    "\<forall>x\<in>set (j_to_list_bound (c+1) (n-(c+1)) m j). dim_col x = 1 "and
    "\<forall>y\<in>set (j_to_list_bound (n+1) (m-n) m j). dim_col y = 1 "and
    "\<forall>c\<in>set (map (\<lambda>i. qr (nat i) m m j) [1..int (c - 1)]). dim_row c = 2 "and
    "\<forall>c\<in>set (map (\<lambda>i. qr (nat i) m m j) [1..int (c - 1)]). dim_col c = 1 "and
    "length (j_to_list_bound (c+1) (n-(c+1)) m j) = n - c - 1 "and
    "length (j_to_list_bound (n+1) (m-n) m j) = m - n "and
    "length (map (\<lambda>i. qr (nat i) m m j) [1..int (c - 1)]) = c - 1 "
shows 
"(CR_on_all n c m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (n-1) m j) 
  \<Otimes> (pw (j_to_list_bound (c+1) (n-(c+1)) m j) (n-c-1)) 
  \<Otimes> (pw (j_to_list_bound n 1 m j) 1) 
  \<Otimes> (pw (j_to_list_bound (n+1) (m-n) m j) (m-n)))
  =  (pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c n m j) 
  \<Otimes> (pw (j_to_list_bound (c+1) (n-(c+1)) m j) (n-c-1))  
  \<Otimes> (pw (j_to_list_bound n 1 m j) 1) 
  \<Otimes> (pw (j_to_list_bound (n+1) (m-n) m j) (m-n))"
    using app_CR_on_all[of n m "(pw (j_to_list_bound n 1 m j) 1)" c j "(j_to_list_bound (c+1) (n-(c+1)) m j)"
                               "(j_to_list_bound (n+1) (m-n) m j)" "[qr (nat i) m m j. i<-[1..(c-1)]]"] 
    sorry



lemma CR_on_all_j:
 fixes n c m j::nat
 assumes "j < 2^m" and "n<m" and "m\<ge>n" and "c\<le>m" and "c<n" 
     and "n\<ge>2" and "m\<ge>1" and "c\<ge>1"
  shows 
 "(CR_on_all n c m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c n m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))
= ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (n+1) m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
proof-
  have f0: "(j\<Otimes> (c+1) (m-c) m j) = (j\<Otimes> (c+1) (n-(c+1)) m j) \<Otimes> (j\<Otimes> n 1 m j) \<Otimes> (j\<Otimes> (n+1) (m-n) m j)"
  proof-
     have "n + 1 - (c + 1) \<le> m - c" using assms by simp
     moreover have "c + 1 + (m - c) - 1 \<le> m" using assms by auto
     ultimately have "(j\<Otimes> (c+1) (m-c) m j) = (j\<Otimes> (c+1) ((n+1)-(c+1)-1) m j) \<Otimes> (j\<Otimes> (n+1-1) 1 m j) \<Otimes> (j\<Otimes> (n+1) ((m-c)-((n+1)-(c+1))) m j)"  
       using j_to_tensor_prod_decomp_middle[of j m "c+1" "n+1" "m-c"] assms by auto
     moreover have "(m-c)-((n+1)-(c+1)) = m-n" using assms by auto
     ultimately show ?thesis by auto
   qed
  then have "(CR_on_all n c m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c n m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))
= (CR_on_all n c m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c n m j) \<Otimes> (j\<Otimes> (c+1) (n-(c+1)) m j) \<Otimes> (j\<Otimes> n 1 m j) \<Otimes> (j\<Otimes> (n+1) (m-n) m j))"
    using tensor_mat_is_assoc by auto
  moreover have "(CR_on_all n c m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c n m j) \<Otimes> (j\<Otimes> (c+1) (n-(c+1)) m j) \<Otimes> (j\<Otimes> n 1 m j) \<Otimes> (j\<Otimes> (n+1) (m-n) m j))
= ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (n+1) m j) \<Otimes> (j\<Otimes> (c+1) (n-(c+1)) m j) \<Otimes> (j\<Otimes> n 1 m j) \<Otimes> (j\<Otimes> (n+1) (m-n) m j))"
  proof-
  have "(CR_on_all n c m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (n-1) m j) 
  \<Otimes> (pw (j_to_list_bound (c+1) (n-(c+1)) m j) (n-(c+1))) 
  \<Otimes> (pw (j_to_list_bound n 1 m j) 1) 
  \<Otimes> (pw (j_to_list_bound (n+1) (m-n) m j) (m-n)))
  =  (pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c n m j) 
  \<Otimes> (pw (j_to_list_bound (c+1) (n-(c+1)) m j) (n-(c+1)))  
  \<Otimes> (pw (j_to_list_bound n 1 m j) 1) 
  \<Otimes> (pw (j_to_list_bound (n+1) (m-n) m j) (m-n))"
  proof-
    have "2 \<le> n \<and> 1 \<le> m \<and> n < m \<and> 1 \<le> c \<and> c \<le> n - 1 \<and> c \<le> m " using assms by auto
    moreover have "dim_row (pw (j_to_list_bound n 1 m j) 1) = 2" 
              and "dim_col (pw (j_to_list_bound n 1 m j) 1) = 1" using pow_tensor_list_one by auto
    moreover have "length [qr (nat i) m m j. i<-[1..(c-1)]] = c-1" by simp
    moreover have "(\<forall>x \<in> set (j_to_list_bound (c+1) (n-(c+1)) m j). dim_row x = 2)" using j_to_list_bound_dim_row by blast
    moreover have "(\<forall>x \<in> set (j_to_list_bound (c+1) (n-(c+1)) m j). dim_col x = 1)" using j_to_list_bound_dim_col by blast
    moreover have "length (j_to_list_bound (c+1) (n-(c+1)) m j) = (n-(c+1))" by (simp add: j_to_list_bound_length)
    moreover have "(\<forall>y \<in> set (j_to_list_bound (n+1) (m-n) m j). dim_row y = 2)" using j_to_list_bound_dim_row by blast
    moreover have "(\<forall>y \<in> set (j_to_list_bound (n+1) (m-n) m j). dim_col y = 1)" using j_to_list_bound_dim_col by blast
    moreover have "length (j_to_list_bound (n+1) (m-n) m j) = m-n" by (simp add: j_to_list_bound_length)
    moreover have "(pw (j_to_list_bound n 1 m j) 1) = zero \<or> (pw (j_to_list_bound n 1 m j) 1) = one" using pow_tensor_list_one by auto
    moreover have "(pw (j_to_list_bound n 1 m j) 1) = zero \<longrightarrow> bin_rep m j ! (n - 1) = 1" 
    moreover have "(pw (j_to_list_bound n 1 m j) 1) = one \<longrightarrow> bin_rep m j ! (n - 1) = 0" sorry
    moreover have " (\<forall>c\<in>set (map (\<lambda>i. qr (nat i) m m j) [1..int (c - 1)]). dim_row c = 2) \<and>
      (\<forall>c\<in>set (map (\<lambda>i. qr (nat i) m m j) [1..int (c - 1)]). dim_col c = 1)" sorry
    moreover have "length [qr (nat i) m m j. i<-[1..(c-1)]] = c-1" sorry
    ultimately show ?thesis
      using app_CR_on_all[of n m "(pw (j_to_list_bound n 1 m j) 1)" c j "(j_to_list_bound (c+1) (n-(c+1)) m j)"
                                 "(j_to_list_bound (n+1) (m-n) m j)" "[qr (nat i) m m j. i<-[1..(c-1)]]"] 
      sorry
   
  qed
  moreover have "(j\<Otimes> (c+1) n m j) = (pw (j_to_list_bound (c+1) n m j) n)" sorry
  moreover have "(j\<Otimes> n n m j) = (pw (j_to_list_bound n n m j) n)" sorry
  moreover have "(j\<Otimes> (n+1) (m-c) m j) = (pw (j_to_list_bound (n+1) (m-c) m j) (m-c))" sorry
  ultimately show ?thesis by auto
qed
ultimately have "(CR_on_all (Suc n) c m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c n m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))
= ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (n+1) m j) \<Otimes> (j\<Otimes> (c+1) n m j) \<Otimes> (j\<Otimes> n n m j) \<Otimes> (j\<Otimes> (n+1) (m-c) m j))"
  by auto
then have "(CR_on_all (Suc n) c m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c n m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))
= ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (n+1) m j) \<Otimes> ((j\<Otimes> (c+1) n m j) \<Otimes> (j\<Otimes> n n m j) \<Otimes> (j\<Otimes> (n+1) (m-c) m j)))"
  using tensor_mat_is_assoc by auto
then show ?thesis using f0 by auto
qed

(*
lemma j_to_tensor_prod_decomp_middle_aux: 
 fixes j m t::nat
  assumes "j < 2^m" and "n>s" and "n\<le>m" and "s\<le>m" and "t\<ge>n-s" and "s+t-1 < m"
  shows "(j\<Otimes> s t m j) = (j\<Otimes> s (n-s-1) m j) \<Otimes> (j\<Otimes> (n-1) 1 m j) \<Otimes> (j\<Otimes> n (t-(n-s)) m j)" 

 "j < 2^m" and "n>(c+1)" and "n\<le>m" and "(c+1)\<le>m" and "(m-c)\<ge>n-(c+1)" and "(c+1)+(m-c)-1 < m"
(j\<Otimes> (c+1) (m-c) m j) = (j\<Otimes> (c+1) (n-(c+1)-1) m j) \<Otimes> (j\<Otimes> (n-1) 1 m j) \<Otimes> (j\<Otimes> n ((m-c)-(n-(c+1))) m j)" 

 "j < 2^m" and "(n+1)>(c+1)" and "(n+1)\<le>m" and "(c+1)\<le>m" and "(m-c)\<ge>(n+1)-(c+1)" and "(c+1)+(m-c)-1 < m"
(j\<Otimes> (c+1) (m-c) m j) = (j\<Otimes> (c+1) ((n+1)-(c+1)-1) m j) \<Otimes> (j\<Otimes> n 1 m j) \<Otimes> (j\<Otimes> (n+1) ((m-c)-((n+1)-(c+1))) m j)" 

*)



(*TODO Is the order of c and k different from other proofs? If so rename to avoid confusion.*)
(*Could go into generic mult function would be more confusing to understand though*)
(*c is the current qubit k=(n-c) ensures that R_2 to R_(n-c+1) are applied to the qubit with the 
special case for c=n that nothing is applied. *)
fun all_CR:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("aCR _ _ _" 75) where
  "(aCR c 0 m) = (Id m)"  
| "(aCR c (Suc k) m) = (CR_on_all (c+(Suc k)) c m) * (aCR c k m)"


lemma all_CR_dim:
  assumes "c<m" and "1 \<le> c"
  shows "c + k < m \<longrightarrow> dim_row (aCR c k m) = 2^m \<and> dim_col (aCR c k m) = 2^m"
proof(induction k)
  show "c + 0 < m \<longrightarrow> dim_row (aCR c 0 m) = 2^m \<and> dim_col (aCR c 0 m) = 2^m"
    using Id_def by auto
next
  fix k
  assume IH: "c + k < m \<longrightarrow> dim_row (aCR c k m) = 2^m \<and> dim_col (aCR c k m) = 2^m"
  have "c + (Suc k) < m \<longrightarrow> dim_row (aCR c (Suc k) m) = 2^m"
  proof
    assume a0: "c + (Suc k) < m"
    have "dim_row (aCR c (Suc k) m) = dim_row (CR_on_all (c+(Suc k)) c m)" by auto
    moreover have " 1 \<le> c + Suc k - c \<and> 1 \<le> c \<and> c + Suc k < m" using assms a0 by auto
    ultimately show "dim_row (aCR c (Suc k) m) = 2^m" 
      using CR_on_all_dim[of "c+(Suc k)" c m] assms by auto
  qed
  moreover have "c + (Suc k) < m \<longrightarrow> dim_col (aCR c (Suc k) m) = 2^m"
  proof
    assume a0: "c + (Suc k) < m"
    have "dim_col (aCR c (Suc k) m) = dim_col (aCR c k m)" by auto
    moreover have "c + k < m" using a0 by auto
    ultimately show "dim_col (aCR c (Suc k) m) = 2^m" 
      using CR_on_all_dim[of "c+(Suc k)" c m] assms IH by auto
  qed
  ultimately show "c + (Suc k) < m \<longrightarrow> dim_row (aCR c (Suc k) m) = 2^m \<and> dim_col (aCR c (Suc k) m) = 2^m"
    by auto
qed



(*Apply the H gate to the current qubit then apply R_2 to R_(m-c)*)
definition all_gates_on_single_qubit:: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("G _ _" 75)  where
 "G c m =  aCR c (m-c) m * (Id (c-1) \<Otimes> H \<Otimes> Id (m-c))"  

lemma app_H_zero: (*Do again with k-1?*)
  assumes "((bin_rep m jd)!k) = 0"
    shows "H * zero = (qr (k+1) (k+1) m jd)" 
proof
  fix i j::nat
  assume "i < dim_row (qr (k+1) (k+1) m jd)" and "j < dim_col (qr (k+1) (k+1) m jd)"
  then have f0: "i \<in> {0,1} \<and> j = 0" using qr_def by auto 
  then have "(H * zero) $$ (i,j) = (\<Sum>k<dim_row zero. (H $$ (i,k)) * (zero $$ (k,0)))" 
    by (metis (no_types, lifting) H_without_scalar_prod dim_col_mat(1) dim_row_mat(1) index_matrix_prod lessThan_atLeast0 lessThan_iff less_numeral_extra(1) set_2 sum.cong)
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
    by (metis (no_types, lifting) H_without_scalar_prod dim_col_mat(1) dim_row_mat(1) index_matrix_prod lessThan_atLeast0 lessThan_iff less_numeral_extra(1) set_2 sum.cong)
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

lemma app_H_gate:
  assumes "c\<ge>1" and "m>c" and "j < 2 ^ m" 
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


lemma o1:
  fixes c m
  assumes "c\<ge>1" and "c<m" and "n\<ge>c"
  shows "n < m \<longrightarrow> aCR c (n-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
        = ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c n m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
proof(rule Nat.nat_induct_at_least[of c n])
  show "n\<ge>c" using assms by auto
next
  show "c < m \<longrightarrow> aCR c (c-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
        = ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))" sorry
next
  fix n
  assume a0: "c \<le> n"
  assume IH: "n < m \<longrightarrow> aCR c (n-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
        = ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c n m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
  show "(Suc n) < m \<longrightarrow> aCR c ((Suc n)-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
        = ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (Suc n) m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
  proof
    assume a1: "(Suc n) < m"
    have "aCR c ((Suc n)-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
    = ((CR_on_all (Suc n) c m) * (aCR c (n-c) m)) *  ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
      by (simp add: Suc_diff_le a0)
    then have "aCR c ((Suc n)-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
    = (CR_on_all (Suc n) c m) * ((aCR c (n-c) m) *  ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)))"
      sorry
    then have "aCR c ((Suc n)-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
    = (CR_on_all (Suc n) c m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c n m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
      using IH a1 by auto
    then have "aCR c ((Suc n)-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
    = ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (n+1) m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
      using CR_on_all_j assms a1 a0 by auto
    then show "aCR c ((Suc n)-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
        = ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (Suc n) m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))" by auto
  qed
qed


lemma 
  fixes c m
  assumes "c\<ge>1" and "c<m" and "(m-1)\<ge>c"
  shows " aCR c (m-1-c) m * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j)) 
        = ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c (m-1) m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
  using o1[of c m "m-1"] assms by auto


lemma o1: "(Id (c-1) \<Otimes> aCR c (m-c) m) * ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c c m j) 
        \<Otimes> (j\<Otimes> (c+1) (m-c) m j))
= ((pw [qr (nat i) m m j. i<-[1..(c-1)]] (c-1)) \<Otimes> (qr c m m j) \<Otimes> (j\<Otimes> (c+1) (m-c) m j))"
  sorry (*Do this with induction*)



lemma o2: 
  fixes k::nat
  assumes "k\<ge>1" and "k\<le>m" 
  shows "(G k m) * ((pw [qr (nat i) m j. i<-[1..k]] k) \<Otimes> (j\<Otimes> k (n-k) m j)) 
      = ((pw [qr (nat i) m j. i<-[1..(k+1)]] (k+1)) \<Otimes> (j\<Otimes> k (n-k-1) m j))" (*Do not do it with induction *)
  sorry (*Just use lemmas above*)


fun pow_mult :: "(complex Matrix.mat) list \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("pm _ _" 75)  where
  "(pm (Cons x []) 0) = x"  
| "(pm (Cons x xs) (Suc k)) = x * (pm xs k)"


value "[k . k<-[(0::nat),1]]"
(*How does list comprehension work?*)
(*Might need to rev this*)
abbreviation \<psi>\<^sub>1::"nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where 
  "\<psi>\<^sub>1 m j \<equiv> pw [qr (nat k) m j. k<-[1..m] ] m"

(*Application of all R gates on a current qubit k*)


lemma o2: 
  assumes "k\<ge>1" and "k<m"
  shows "(pm [G (nat i) m. i<-[1..k]] (k-1)) * (j\<Otimes> 1 m m j)
      = ((pw [qr (nat i) m j. i<-[1..k]] k) \<Otimes> (j\<Otimes> k (n-k) m j))" 
proof(rule Nat.nat_induct_at_least[of 1 k])
  have "(pm [G (nat i) m. i<-[1..1]] (1-1)) * (j\<Otimes> 1 m m j)
      = ((pw [qr (nat i) m j. i<-[1..1]] 1) \<Otimes> (j\<Otimes> 1 (n-1) m j))" sorry
next
  fix k ::nat
  assume a0: "k\<ge>1"
     and IH: "(pm [G (nat i) m. i<-[1..k]] (k-1)) * (j\<Otimes> 1 m m j)
      = ((pw [qr (nat i) m j. i<-[1..k]] k) \<Otimes> (j\<Otimes> k (n-k) m j))" 
  show  "(pm [G (nat i) m. i<-[1..(Suc k)]] ((Suc k)-1)) * (j\<Otimes> 1 m m j)
      = ((pw [qr (nat i) m j. i<-[1..(Suc k)]] (Suc k)) \<Otimes> (j\<Otimes> (Suc k) (n-(Suc k)) m j))"  sorry
qed



theorem(in qft)
  shows "(pm [G (nat k). k<-[1..n]] (n-1)) * (j\<Otimes> 1 n j_dec n) = \<psi>\<^sub>1"
proof-
  have "(pm [G (nat i). i<-[1..(n-1)]] (n-1)) * (j\<Otimes> 1 n j_dec n)
      = ((pw [qr (nat i). i<-[1..(n-1)]] (n-1)) \<Otimes> (j\<Otimes> (n-1) (n-(n-1)) j_dec n))" using o2 sorry
  have "(pm [G (nat k). k<-[1..n]] n) = G n * (pm [G (nat i). i<-[1..(n-1)]] (n-1))" sorry
  have "G n * ((pw [qr (nat i). i<-[1..(n-1)]] (n-1)) \<Otimes> (j\<Otimes> (n-1) (n-(n-1)) j_dec n))
= (Id (n-1) \<Otimes> aCR n 0) * (Id (n-1) \<Otimes> H \<Otimes> Id 0)* ((pw [qr (nat i). i<-[1..(n-1)]] (n-1)) \<Otimes> (j\<Otimes> (n-1) (n-(n-1)) j_dec n))"
    sorry
 have "G n * ((pw [qr (nat i). i<-[1..(n-1)]] (n-1)) \<Otimes> (j\<Otimes> (n-1) (n-(n-1)) j_dec n))
= (Id (n-1) \<Otimes> aCR n 0) * ( (pw [qr (nat i). i<-[1..(n-1)]] (n-1)) \<Otimes> (H * (j\<Otimes> (n-1) (n-(n-1)) j_dec n)) )" sorry
 have "G n * ((pw [qr (nat i). i<-[1..(n-1)]] (n-1)) \<Otimes> (j\<Otimes> (n-1) (n-(n-1)) j_dec n))
= ( (pw [qr (nat i). i<-[1..(n-1)]] (n-1)) \<Otimes> (aCR n 0 * H * (j\<Otimes> (n-1) (n-(n-1)) j_dec n)) )" sorry
 have "G n * ((pw [qr (nat i). i<-[1..(n-1)]] (n-1)) \<Otimes> (j\<Otimes> (n-1) (n-(n-1)) j_dec n))
= (pw [qr (nat i). i<-[1..(n-1)]] (n-1)) \<Otimes> (qr n)" sorry
 have "G n * ((pw [qr (nat i). i<-[1..(n-1)]] (n-1)) \<Otimes> (j\<Otimes> (n-1) (n-(n-1)) j_dec n))
= (pw [qr (nat i). i<-[1..n]] n)" sorry



















lemma(in qft)
  assumes "(bin_rep n j_dec)!m = 1" and "m<n" (*Change def of j\<Otimes> n and extend to smaller equal*)
  shows "j\<Otimes> m (n-m) = zero \<Otimes> (j\<Otimes> (m+1) (n-m-1))" sorry
(*proof-
 have "j\<Otimes> (n-m) = pw (rev (j_to_list (n-m))) (n-m)" 
   by (simp add: j_to_tensor_prod_rest_def)
  have "last (rev (j_to_list (n-m))) = hd (j_to_list (n-m))" sorry
  have "(rev (j_to_list (n-m))) = butlast (rev (j_to_list (n-m))) @ [last (rev (j_to_list (n-m)))]" sorry
  then have "j\<Otimes> (n-m) = hd (j_to_list (n-m)) \<Otimes> (pw (rev (j_to_list (n-m))) (n-m-1))" sorry
  moreover have "hd (j_to_list (n-m)) = one" sorry
  show "j\<Otimes> (n-m) = zero \<Otimes> j\<Otimes> (n-m-1)" sorry
qed*)

lemma(in qft)
  shows "(bin_rep n j_dec)!m = 0 \<longrightarrow> j\<Otimes> (n-m) = zero \<Otimes> j\<Otimes> (n-m-1)" sorry


lemma(in qft) h1:
  fixes m::nat
  assumes "m\<ge>1"
  shows "m\<le>n \<longrightarrow> (pow_mult [G (nat k). k<-[1..m]] m) * j\<Otimes> 
      = (pow_mult [G (nat k). k<-[1..(m-1)]] (m-1)) * ((pow_tensor_list [qr (nat i). i<-[1..(m+1)]] (m+1)) \<Otimes> (j\<Otimes> (n-m)))"
proof(rule ind_from_1[of m])
  fix m::nat
  assume "m\<ge>1"
  and IH:"(pow_mult [G (nat k). k<-[1..m]] m) * j\<Otimes> = ((pow_tensor_list [G (nat i). i<-[1..(m+1)]] (m+1)) \<Otimes> (j\<Otimes> (n-m)))"
  then have "(pow_mult [G (nat k). k<-[1..(Suc m)]] (Suc m)) * j\<Otimes>
       = (G (Suc m) * (pow_mult [G (nat k). k<-[1..m]] m)) * j\<Otimes>" sorry
  then have "(pow_mult [G (nat k). k<-[1..(Suc m)]] (Suc m)) * j\<Otimes> 
       = G (Suc m) * ((pow_mult [G (nat k). k<-[1..m]] m) * j\<Otimes>)" sorry
  then have "(pow_mult [G (nat k). k<-[1..(Suc m)]] (Suc m)) * j\<Otimes> 
       = G (Suc m) * ((pow_tensor_list [G (nat i). i<-[1..(m+1)]] (m+1)) \<Otimes> (j\<Otimes> (n-m)))" sorry
  then have "(pow_mult [G (nat k). k<-[1..(Suc m)]] (Suc m)) * j\<Otimes> 
       = ((aCR (Suc m) (n-(Suc m))) * (Id (Suc m) \<Otimes> H \<Otimes> Id (n-(Suc m)))) * ((pow_tensor_list [G (nat i). i<-[1..(m+1)]] (m+1)) \<Otimes> (j\<Otimes> (n-m)))" sorry
  
  have "(pow_mult [G (nat k). k<-[1..m]] m) * j\<Otimes> = ((pow_tensor_list [G (nat i). i<-[1..(m+1)]] (m+1)) \<Otimes> (j\<Otimes> (n-m)))"
  proof(rule disjE)
    show "(bin_rep n j_dec)!m = 1 \<or> (bin_rep n j_dec)!m = 0" sorry
  next
    assume "(bin_rep n j_dec)!m = 1"
    then have "(pow_mult [G (nat k). k<-[1..(Suc m)]] (Suc m)) * j\<Otimes> 
       = ((aCR (Suc m) (n-(Suc m))) * (Id (Suc m) \<Otimes> H \<Otimes> Id (n-(Suc m)))) * ((pow_tensor_list [G (nat i). i<-[1..(m+1)]] (m+1)) \<Otimes> zero \<Otimes> (j\<Otimes> (n-m-1)))" sorry
    have "(Id (Suc m) \<Otimes> H \<Otimes> Id (n-(Suc m))) * ((pow_tensor_list [G (nat i). i<-[1..(m+1)]] (m+1)) \<Otimes> (j\<Otimes> (n-m)))
      = ((pow_tensor_list [G (nat i). i<-[1..(m+1)]] (m+1)) \<Otimes> 
        (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1/sqrt(2) else 1/sqrt(2)*exp(2*pi*\<i>*bf (m+1) (m+1))))  \<Otimes> (j\<Otimes> (n-m-1)))" sorry
have "(aCR (Suc m) (n-(Suc m))) *
        (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1/sqrt(2) else 1/sqrt(2)*exp(2*pi*\<i>*bf (m+1) (m+1))))  \<Otimes> (j\<Otimes> (n-m-1)))" sorry













(*Make this more general, this will appear in the induction showing what the result of applying all necessary Ri is*)
lemma(in qft)
  shows "(R\<^sub>m (n-m) (n-k)) * (H \<Otimes> Id (n-k)) * (j\<Otimes> k) 
= (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then (1::complex)/sqrt(2) else exp(complex_of_real (2*pi)*\<i>*(bf 0 (k+1))) * 1/sqrt(2))) \<Otimes> (j\<Otimes> (k-1))"
  sorry

(*Will not be needed anymore*)
(*Gives the unit vector corresponding to |j\<^sub>sj\<^sub>s\<^sub>+\<^sub>1,..,j\<^sub>n> for given s. *)
(*E.g. n=3 j=5, 101 is shortened to 01 (start=1) or 1 (start=0)*)
definition(in qft) unit_vec_j:: "nat \<Rightarrow> complex Matrix.mat" ("UV _") where
"UV start \<equiv> Matrix.mat (2^(n-start)) 1 (\<lambda>(i,j). if (i = j mod 2^(n-start)) then 1 else 0)"

