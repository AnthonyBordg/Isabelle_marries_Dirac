(*
Author: 
  Hanna Lachnitt, TU Wien, lachnitt@student.tuwien.ac.at
*)

theory Quantum_Fourier_Transform
imports
  More_Tensor
  Binary_Nat
  Basics
begin


section ‹The Quantum Fourier Transform›

abbreviation zero where "zero ≡ unit_vec 2 0"
abbreviation one where "one ≡ unit_vec 2 1" 

lemma Id_left_tensor [simp]: 
  shows "(Id 0) ⨂ A = A" 
  using one_mat_def Id_def by auto 

lemma Id_right_tensor [simp]:
  shows "A ⨂ (Id 0) = A"   
  using one_mat_def Id_def by auto 

lemma Id_mult_left [simp]:
  assumes "dim_row A = 2^m"
  shows "Id m * A = A"
  using Id_def one_mat_def by (simp add: assms)

lemma aux_calculation [simp]:
  shows "m > k ∧ k ≥ 1 ⟶ (2::nat)^(k-Suc 0) * 2 * 2^(m-k) = 2^m"
    and "m > k ∧ k ≥ 1 ⟶ (2::nat)^(m-Suc 0) = 2^(k-Suc 0) * 2^(m-k)"
    and "m > k ⟶ Suc (m-Suc k) = m - k" 
    and "1 ≤ k - c ∧ m ≥ k ∧ m ≥ c ⟶ (2::nat)^(k-Suc c) * 2 * 2^(m-k) = 2^(m-c)" 
    and "c ≤ m ∧ k ≥ c + 1 ∧ m ≥ (Suc k) ⟶ k - c - 1 + 2 + (m - Suc k) = m - c"
    and "1 ≤ k - c ∧ m ≥ k ∧ m ≥ c ⟶ (2::nat) * 2^(k-c-1) * 2 * 2^(m-k) = 2^(m-c+1)" 
    and "1 ≤ k - c ∧ m ≥ k ∧ m ≥ c ⟶ (2::nat)^(m-c) = 2 * 2^(k-Suc c) * 2^(m-k)"
    and "k ≥ c ∧ m ≥ (Suc k) ⟶ (2::nat)^(k-c) * 2 * 2^(m-Suc k) = 2^(m-c)"
    and "m > k ∧ k ≥ 1 ⟶ 2 * ((2::nat) ^ (m - k) * 2 ^ (k - Suc 0)) = 2 ^ m"  
    and "c ≥ 1 ∧ c ≤ m ⟶ 2^(c-Suc 0) * 2 * 2^(m-c) = (2::nat)^m" 
proof-
  show "m > k ∧ k ≥ 1 ⟶ (2::nat)^(k-Suc 0) * 2 * 2^(m-k) = 2^m"
    by (metis One_nat_def le_add_diff_inverse less_or_eq_imp_le not_less_eq_eq power_add power_commutes power_eq_if)
next
  show "m > k ∧ k ≥ 1 ⟶ (2::nat)^(m-Suc 0) = 2^(k-Suc 0) * 2^(m-k)"
    by (metis Nat.add_diff_assoc2 One_nat_def le_add_diff_inverse less_or_eq_imp_le power_add)
next
  show "m > k ⟶ Suc (m - Suc k) = m - k" 
    using Suc_diff_Suc by simp
next
  show "1 ≤ k - c ∧ m ≥ k ∧ m ≥ c ⟶ (2::nat)^(k-Suc c) * 2 * 2^(m-k) = 2^(m-c)" 
    by (metis Nat.add_diff_assoc2 One_nat_def Suc_diff_Suc Suc_le_eq le_add_diff_inverse nat_diff_split 
        not_le not_one_le_zero power_add semiring_normalization_rules(28) zero_less_diff)
next
  show "c ≤ m ∧ k ≥ c + 1 ∧ m ≥ (Suc k) ⟶ k - c - 1 + 2 + (m - Suc k) = m-c" by auto
next
  show "1 ≤ k - c ∧ m ≥ k ∧ m ≥ c ⟶ (2::nat) * 2^(k-c-1) * 2 * 2^(m-k) = 2^(m-c+1)" 
    by (metis (no_types, lifting) Nat.add_diff_assoc2 le_add_diff_inverse nat_diff_split not_le not_one_le_zero 
        power_add power_commutes semigroup_mult_class.mult.assoc semiring_normalization_rules(33))
next 
  show "1 ≤ k - c ∧ m ≥ k ∧ m ≥ c ⟶ (2::nat) ^ (m - c) = 2 * 2 ^ (k - Suc c) * 2 ^ (m - k)" 
    by (metis (no_types, hide_lams) add_diff_assoc2 diff_diff_right Suc_diff_Suc diff_diff_cancel diff_le_self
        less_imp_le_nat neq0_conv not_one_le_zero power_add semiring_normalization_rules(28) semiring_normalization_rules(7) zero_less_diff)
next
  show "k ≥ c ∧ m ≥ (Suc k) ⟶ (2::nat)^(k-c) * 2 * 2^(m-Suc k) = 2^(m-c)"
    by (metis (no_types, lifting) Nat.add_diff_assoc2 Suc_eq_plus1 add.assoc le_add_diff_inverse power_add semiring_normalization_rules(28))
next
  show "m > k ∧ k ≥ 1 ⟶ 2 * ((2::nat) ^ (m - k) * 2 ^ (k - Suc 0)) = 2 ^ m"  
    by (metis Nat.add_diff_assoc One_nat_def add.commute less_imp_le_nat not_less_eq_eq 
        ordered_cancel_comm_monoid_diff_class.add_diff_inverse power_add power_eq_if)
next
  show "c ≥ 1 ∧ c ≤ m ⟶ 2^(c-Suc 0) * 2 * 2^(m-c) = (2::nat)^m" 
    by (metis One_nat_def dual_order.strict_trans1 le_add_diff_inverse2 less_numeral_extra(1) mult.commute power_add power_minus_mult)
qed


subsection ‹The Transformation of a State into a Tensor Product of Single Qubits›

(* Each number j < 2⇧m corresponds to a unit vector which is 0 at all positions except at entry j. 
Let |j⟩ be |unit_vec (2^m) j⟩ where j is simultaneously seen as a string j⇩1j⇩2...j⇩m of length m, namely 
as a natural number strictly less then 2⇧m and its binary representation. Clearly
|j⟩ is a state. Moreover, |j⟩ might be written as a tensor product of length n of the 
matrices |zero⟩ and |one⟩, where a factor at position i is |one⟩ if j⇩i = 1 and |zero⟩ otherwise. 
For example, if j = 9 and m = 4, it holds that |1001⟩ = |one⟩ ⨂ |zero⟩ ⨂ |zero⟩ ⨂ |one⟩. 
This result is proven in this subsection.*)

(* The function to_list_bound returns the part of the decomposition of j in |zero⟩ and |one⟩ matrices 
where s is the starting position and l is the length of the partition. The result is returned as a list.
E.g. j=9, s=2 and l=3. The binary representation of 9 being 1001, it follows that
to_list_bound s l j = [|zero⟩,|zero⟩,|one⟩] *)
primrec to_list_bound :: "nat ⇒ nat ⇒ nat ⇒ nat ⇒ complex Matrix.mat list" where
"to_list_bound s 0 n j = []" |
"to_list_bound s (Suc l) n j = (if (bin_rep n j)!(s-1) = 0 then |zero⟩ else |one⟩) # (to_list_bound (s+1) l n j)"

(* The function pow_tensor_list takes a list and the number of its elements and returns the tensor 
product of the elements *)
fun pow_tensor_list:: "((complex Matrix.mat) list) ⇒ nat ⇒ complex Matrix.mat" ("pr _ _" 75) where
  "(pr [] 0) = Id 0" |
  "(pr (Cons x xs) (Suc k)) = x ⨂ (pr xs k)"

(* The definition to_tensor_prod declares the decomposition of a number j into a tensor product of 
|zero⟩ and |one⟩ matrices. Parameter s is the starting position, l the number of bits and n a number 
such that j < 2⇧n. E.g. For j=j⇩1...j⇩n, s=2 and l=3, ⨂r is |j⇩2,j⇩3,j⇩4⟩ *)
definition to_tensor_prod:: "nat ⇒ nat ⇒ nat ⇒ nat ⇒ complex Matrix.mat" ("⨂r _ _ _ _" 75) where 
"(⨂r s l n j) = pr (to_list_bound s l n j) l"

lemma to_list_bound_length_1 [simp]: 
  shows "to_list_bound s 1 n j = [(if (bin_rep n j)!(s-1) = 0 then |zero⟩ else |one⟩)]" by simp

lemma pow_tensor_length_1:
  shows "(pr [X] 1) = X"
  by simp    

lemma to_tensor_prod_length_0 [simp]:
  shows "(⨂r s 0 j n) = (Id 0)"    
  by (simp add: to_tensor_prod_def)

lemma to_tensor_prod_decomp_right_zero:
  shows "(bin_rep n j)!(s+l-1) = 0 ⟶ (⨂r s (l+1) n j) = (⨂r s l n j) ⨂ |zero⟩"
proof(induction l arbitrary: s)
  show "(bin_rep n j)!(s+0-1) = 0 ⟶ (⨂r s (0+1) n j) = (⨂r s 0 n j) ⨂ |zero⟩" for s
      using to_list_bound_length_1 to_tensor_prod_def by simp
next
  fix l s
  assume IH: "(bin_rep n j)!(s+l-1) = 0 ⟶ (⨂r s (l+1) n j) = (⨂r s l n j) ⨂ |zero⟩" for s
  show "(bin_rep n j)!(s+(Suc l)-1) = 0 ⟶ (⨂r s ((Suc l)+1) n j) = (⨂r s (Suc l) n j) ⨂ |zero⟩"
  proof
    assume a0: "(bin_rep n j)!(s+(Suc l)-1) = 0"
    then have "(⨂r s ((Suc l)+1) n j) = (if (bin_rep n j)!(s-1) = 0 then |zero⟩ else |one⟩) ⨂ pr ((to_list_bound (s+1) (Suc l) n j)) (Suc l)" 
      using to_tensor_prod_def by simp
    also have "... = (if (bin_rep n j)!(s-1) = 0 then |zero⟩ else |one⟩) ⨂ (⨂r (s+1) (l+1) n j)" 
      by (metis Suc_eq_plus1 to_tensor_prod_def)
    also have "... = (if (bin_rep n j)!(s-1) = 0 then |zero⟩ else |one⟩) ⨂ (⨂r (s+1) l n j) ⨂ |zero⟩"
      using a0 IH tensor_mat_is_assoc by simp
    also have "... = (pr (to_list_bound s (l+1) n j) (l+1)) ⨂ |zero⟩"
      using to_tensor_prod_def by simp
    finally show "(⨂r s ((Suc l)+1) n j) = (⨂r s (Suc l) n j) ⨂ |zero⟩"
      using to_tensor_prod_def by simp
  qed
qed

lemma to_tensor_prod_decomp_right_one:
   shows "(bin_rep n j)!(s+l-1) = 1 ⟶ (⨂r s (l+1) n j) = (⨂r s l n j) ⨂ |one⟩"
proof(induction l arbitrary: s)
  show "(bin_rep n j)!(s+0-1) = 1 ⟶ (⨂r s (0+1) n j) = (⨂r s 0 n j) ⨂ |one⟩" for s
    using to_list_bound_length_1 to_tensor_prod_def by simp
next
  fix l s
  assume IH: "(bin_rep n j)!(s+l-1) = 1 ⟶ (⨂r s (l+1) n j) = (⨂r s l n j) ⨂ |one⟩" for s
  show "(bin_rep n j)!(s+(Suc l)-1) = 1 ⟶ (⨂r s ((Suc l)+1) n j) = (⨂r s (Suc l) n j) ⨂ |one⟩"
  proof 
    assume a0: "(bin_rep n j)!(s+(Suc l)-1) = 1"
    have "(⨂r s ((Suc l)+1) n j) = (if (bin_rep n j)!(s-1) = 0 then |zero⟩ else |one⟩) ⨂ pr ((to_list_bound (s+1) (Suc l) n j)) (Suc l)" 
      using to_tensor_prod_def by simp
    also have "... = (if (bin_rep n j)!(s-1) = 0 then |zero⟩ else |one⟩) ⨂ (⨂r (s+1) (l+1) n j)" 
      by (metis Suc_eq_plus1 to_tensor_prod_def)
    also have "... = (if (bin_rep n j)!(s-1) = 0 then |zero⟩ else |one⟩) ⨂ (⨂r (s+1) l n j) ⨂ |one⟩"
      using a0 IH tensor_mat_is_assoc by simp
    also have "... = (if (bin_rep n j)!(s-1) = 0 then |zero⟩ else |one⟩) ⨂ (pr (to_list_bound (s+1) l n j) l) ⨂ |one⟩"
      using to_tensor_prod_def by simp
    also have "... = (pr (to_list_bound s (l+1) n j) (l+1)) ⨂ |one⟩" by simp
    finally show "(⨂r s ((Suc l)+1) n j) = (⨂r s (Suc l) n j) ⨂ |one⟩"
      using to_tensor_prod_def by simp
  qed
qed

lemma pow_tensor_list_dim_col [simp]:
  assumes "length xs = l" and "(∀x ∈ set xs. dim_col x = 1)"
  shows "dim_col (pr xs l) = 1" 
proof-
  have "length xs = l ⟶ (∀x ∈ set xs. dim_col x = 1) ⟶ dim_col (pr xs l) = 1"
  proof(induction l arbitrary: xs)
    fix xs
    show "length xs = 0 ⟶ (∀x ∈ set xs. dim_col x = 1) ⟶ dim_col (pr xs 0) = 1" 
      using Id_def one_mat_def by simp
  next
    fix l xs
    assume IH: "length xs = l ⟶ (∀x ∈ set xs. dim_col x = 1) ⟶ dim_col (pr xs l) = 1" for xs
    show "length xs = (Suc l) ⟶ (∀x ∈ set xs. dim_col x = 1) ⟶ dim_col (pr xs (Suc l)) = 1"
    proof(rule impI, rule impI)
      assume a0: "length xs = (Suc l)" and a1: "(∀x ∈ set xs. dim_col x = 1)"
      then have "∃x. xs = x # tl xs" by (metis length_Suc_conv list.sel(3))
      then obtain x where f0: "xs = x # tl xs" by auto 
      have "dim_col (pr xs (Suc l)) = dim_col (x ⨂ (pr (tl xs) l))" 
        using pow_tensor_list.simps f0 by metis
      also have "... = 1 * dim_col ((pr (tl xs) l))" 
        using a1 f0 by (metis dim_col_tensor_mat list.set_intros(1))
      finally show "dim_col (pr xs (Suc l)) = 1" 
        using IH a0 a1 f0 
        by (metis add_diff_cancel_left' length_tl list.distinct(1) list.set_sel(2) mult.left_neutral plus_1_eq_Suc)
    qed
  qed
  then show ?thesis using assms by simp
qed

lemma pow_tensor_list_dim_row:
  assumes "length xs = l" and "(∀x ∈ set xs. dim_row x = m)"
  shows "dim_row (pr xs l) = m^l"
proof-
  have "length xs = l ⟶ (∀x ∈ set xs. dim_row x = m) ⟶ dim_row (pr xs l) = m^l"
  proof(induction l arbitrary: xs)
    fix xs
    show "length xs = 0 ⟶ (∀x ∈ set xs. dim_row x = m) ⟶ dim_row (pr xs 0) = m^0" 
      using Id_def one_mat_def by simp
  next
    fix l xs
    assume IH: "length xs = l ⟶ (∀x ∈ set xs. dim_row x = m) ⟶ dim_row (pr xs l) = m^l" for xs
    show "length xs = (Suc l) ⟶ (∀x ∈ set xs. dim_row x = m) ⟶ dim_row (pr xs (Suc l)) = m^(Suc l)"
    proof(rule impI, rule impI)
      assume a0: "length xs = (Suc l)" and a1: "(∀x ∈ set xs. dim_row x = m)"
      then have "∃x. xs = x # tl xs" by (metis length_Suc_conv list.sel(3))
      then obtain x where f0: "xs = x # tl xs" by auto 
      have "dim_row (pr xs (Suc l)) = dim_row (x ⨂ (pr (tl xs) l))" 
        using pow_tensor_list.simps f0 by metis
      also have "... = m * dim_row ((pr (tl xs) l))" 
        using a1 f0 by (metis dim_row_tensor_mat list.set_intros(1))
      also have "... = m * m^l" 
        using IH a0 a1 f0 by (metis add_diff_cancel_left' length_tl list.distinct(1) list.set_sel(2) plus_1_eq_Suc)
      finally show "dim_row (pr xs (Suc l)) = m^(Suc l)" by simp
    qed
  qed
  then show ?thesis using assms by simp
qed

lemma pow_tensor_decomp_left:
  assumes "length xs = l"
  shows "(pr xs l) ⨂ x = pr (xs @ [x]) (l+1)" 
proof-
  have "length xs = l ⟶ (pr xs l) ⨂ x = pr (xs @ [x]) (l+1)" 
  proof(induction l arbitrary: xs)
    fix xs
    show "length xs = 0 ⟶ (pr xs 0) ⨂ x = pr (xs @ [x]) (0+1)" 
      using Id_left_tensor Id_def by auto
  next
    fix l xs
    assume IH: "length xs = l ⟶ (pr xs l) ⨂ x = pr (xs @ [x]) (l+1)" for xs
    show "length xs = (Suc l) ⟶ (pr xs (Suc l)) ⨂ x = pr (xs @ [x]) ((Suc l)+1)"
    proof
      assume a0: "length xs = (Suc l)"
      moreover have "xs = (y#ys) ⟶ pr (xs @ [x]) ((Suc l)+1) = (pr xs (Suc l)) ⨂ x" 
        for y::"complex Matrix.mat" and ys::"complex Matrix.mat list"
      proof
        assume a2: "xs = y#ys"
        then have "pr (xs @ [x]) ((Suc l)+1) = y ⨂ pr (ys @ [x]) (l+1)" by simp
        also have "... = y ⨂ ((pr ys l) ⨂ x)" using a0 a2 IH by simp
        also have "... = (y ⨂ (pr ys l)) ⨂ x" using tensor_mat_is_assoc by simp
        also have "... = (pr (y#ys) (Suc l)) ⨂ x" by auto
        finally show "pr (xs @ [x]) ((Suc l)+1) = (pr xs (Suc l)) ⨂ x" using a2 by simp
      qed
      ultimately show "(pr xs (Suc l)) ⨂ x = pr (xs @ [x]) ((Suc l)+1)" by (metis Suc_length_conv)
    qed
  qed
  then show ?thesis using assms by simp
qed

lemma pow_tensor_decomp_right:
  assumes "length xs = l"
  shows "x ⨂ (pr xs l) = pr (x # xs) (l+1)" 
  using Suc_le_D assms(1) by simp

lemma to_list_bound_length:
  shows "length (to_list_bound s l n j) = l"
proof(induction l arbitrary: s)
  show "length (to_list_bound s 0 n j) = 0" for s by simp
next
  fix l s
  assume IH: "length (to_list_bound s l n j) = l" for s
  have "length (to_list_bound s (Suc l) n j) = length ((if (bin_rep n j)!(s-1) = 0 then |zero⟩ else |one⟩) 
                                                 # (to_list_bound (s+1) l n j))" by simp
  then have "length (to_list_bound s (Suc l) n j) = length [(if (bin_rep n j)!(s-1) = 0 then |zero⟩ else |one⟩)]
                                                    + length (to_list_bound (s+1) l n j)" by simp
  moreover have "length [(if (bin_rep n j)!(s-1) = 0 then |zero⟩ else |one⟩)] = 1" by simp
  moreover have "length (to_list_bound (s+1) l n j) = l" using IH by simp
  ultimately show "length (to_list_bound s (Suc l) n j) = (Suc l)" by simp
qed

lemma to_list_bound_dim:
  shows "(∀x ∈ set (to_list_bound s l n j). dim_row x = 2) ∧ (∀x∈set (to_list_bound s l n j). dim_col x = 1)"
  apply (induction l arbitrary: s)
   apply (auto simp: to_list_bound_def ket_vec_def).

lemma to_tensor_prod_dim:
  shows "dim_row (⨂r s l n j) = 2^l ∧ dim_col (⨂r s l n j) = 1" 
  using to_tensor_prod_def to_list_bound_length to_list_bound_dim pow_tensor_list_dim_row pow_tensor_list_dim_col 
  by simp

lemma to_tensor_prod_decomp_left_zero:
  assumes "l ≥ 1" and "(bin_rep n j)!(s-1) = 0"
  shows "(⨂r s l n j) = |zero⟩ ⨂ (⨂r (s+1) (l-1) n j)"
proof- 
  have "(⨂r s l n j) = pr (to_list_bound s l n j) l"
    using to_tensor_prod_def by simp
  also have "... = pr ((if (bin_rep n j)!(s-1) = 0 then |zero⟩ else |one⟩) # (to_list_bound (s+1) (l-1) n j)) l"
    using assms(1) by (metis to_list_bound.simps(2) ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
  also have "... = pr ( |zero⟩ # (to_list_bound (s+1) (l-1) n j)) l"
    using assms(2) by simp
  also have "... = |zero⟩ ⨂ pr (to_list_bound (s+1) (l-1) n j) (l-1)"
    using assms(1) pow_tensor_list.simps by (metis One_nat_def Suc_pred less_eq_Suc_le)
  finally show "(⨂r s l n j) = |zero⟩ ⨂ (⨂r (s+1) (l-1) n j)"
    using to_tensor_prod_def by simp
qed

lemma to_tensor_prod_decomp_left_one:
  assumes "l ≥ 1" and "(bin_rep n j)!(s-1) = 1"
  shows "(⨂r s l n j) = |one⟩ ⨂ (⨂r (s+1) (l-1) n j)"
proof- 
  have "(⨂r s l n j) = pr (to_list_bound s l n j) l"
    using to_tensor_prod_def by simp
  also have "... = pr ((if (bin_rep n j)!(s-1) = 0 then |zero⟩ else |one⟩) # (to_list_bound (s+1) (l-1) n j)) l"
    using assms(1) by (metis Suc_diff_1 less_le_trans less_one to_list_bound.simps(2))
  also have "... = pr ( |one⟩ # (to_list_bound (s+1) (l-1) n j)) l"
    using assms(2) by simp
  also have "... = |one⟩ ⨂ pr (to_list_bound (s+1) (l-1) n j) (l-1)"
    using assms(1) pow_tensor_list.simps by (metis One_nat_def Suc_pred less_eq_Suc_le)
  finally show "(⨂r s l n j) = |one⟩ ⨂ (⨂r (s+1) (l-1) n j)"
    using to_tensor_prod_def by simp
qed

lemma to_tensor_prod_decomp_right:
  assumes "j < 2^n" and "s + t - 1 < n" 
  shows "(⨂r s (t+1) n j) = (⨂r s t n j) ⨂ (⨂r (s+t) 1 n j)"
proof(rule disjE)
  show "(bin_rep n j)!(s+t-1) = 0 ∨ (bin_rep n j)!(s+t-1) = 1" 
    using bin_rep_coeff assms by simp
next
  assume a0: "(bin_rep n j)!(s+t-1) = 0"
  then have "(⨂r (s+t) 1 n j) = |zero⟩" 
    using to_tensor_prod_def by simp
  moreover have "(⨂r s (t+1) n j) = (⨂r s t n j) ⨂ |zero⟩"
    using to_tensor_prod_decomp_right_zero a0 by simp
  ultimately show ?thesis by simp
next
  assume a0: "(bin_rep n j)!(s+t-1) = 1"
  then have "(⨂r (s+t) 1 n j) = |one⟩" 
    using to_tensor_prod_def by simp
  moreover have "(⨂r s (t+1) n j) = (⨂r s t n j) ⨂ |one⟩"
    using to_tensor_prod_decomp_right_one a0 by simp
  ultimately show ?thesis by simp
qed

lemma to_tensor_prod_decomp_half:
  assumes "j < 2^n" and "m > s" and "m ≤ n" and "t ≥ m - s" and "n ≥ 1"
  shows "s + t - 1 ≤ n ⟶ (⨂r s t n j) = (⨂r s (m-s) n j) ⨂ (⨂r m (t-(m-s)) n j)"
proof(rule Nat.nat_induct_at_least[of "m-s" t])
  show "t ≥ m - s" using assms(4) by simp
next
  show "s + (m - s) - 1 ≤ n ⟶ (⨂r s (m-s) n j) = (⨂r s (m-s) n j) ⨂ (⨂r m ((m-s)-(m-s)) n j)"
  proof
    assume a0: "s + (m - s) - 1 ≤ n"
    then have "(⨂r m ((m-s)-(m-s)) n j) = Id 0" by simp
    then show "(⨂r s (m-s) n j) = (⨂r s (m-s) n j) ⨂ (⨂r m ((m-s)-(m-s)) n j)" 
      using Id_right_tensor by simp
  qed
next
  fix t 
  assume a0: "t ≥ m - s"
     and IH: "s + t - 1 ≤ n ⟶ (⨂r s t n j) = (⨂r s (m-s) n j) ⨂ (⨂r m (t-(m-s)) n j)"
  show "s + (Suc t) - 1 ≤ n ⟶ (⨂r s (Suc t) n j) = (⨂r s (m-s) n j) ⨂ (⨂r m ((Suc t)-(m-s)) n j)"
  proof
    assume a1: "s + (Suc t) - 1 ≤ n" 
    have "(⨂r s (t+1) n j) = (⨂r s (m-s) n j) ⨂ ((⨂r m (t-(m-s)) n j) ⨂ (⨂r (s+t) 1 n j))" 
    proof-
      have "s + t - 1 < n" using assms a1 by simp
      then have "(⨂r s (t+1) n j) = (⨂r s t n j) ⨂ (⨂r (s+t) 1 n j)" 
        using to_tensor_prod_decomp_right assms by blast
      then have "(⨂r s (t+1) n j) = ((⨂r s (m-s) n j) ⨂ (⨂r m (t-(m-s)) n j)) ⨂ (⨂r (s+t) 1 n j)" 
        using IH a1 by simp
      then show ?thesis 
        using tensor_mat_is_assoc by simp
    qed
    moreover have "(⨂r m (t-(m-s)+1) n j) = (⨂r m (t-(m-s)) n j) ⨂ (⨂r (s+t) 1 n j)"
    proof-
      have "m + (t - (m - s)) - 1 < n" using assms a1 by linarith
      then have "⨂r m (t-(m-s)+1) n j = (⨂r m (t-(m-s)) n j) ⨂ (⨂r (m+(t-(m-s))) 1 n j)"
        using to_tensor_prod_decomp_right[of j n m "(t-(m-s))"] assms a0 by simp
      moreover have "m + (t - (m - s)) = t + s" using assms a0 by linarith
      ultimately show ?thesis 
        by (metis linordered_field_class.sign_simps(2))
    qed
    ultimately have "(⨂r s (t+1) n j) = (⨂r s (m-s) n j) ⨂ (⨂r m (t-(m-s)+1) n j)"
      by simp
    then show "(⨂r s (Suc t) n j) = (⨂r s (m-s) n j) ⨂ (⨂r m ((Suc t)-(m-s)) n j)" 
      by (metis Suc_diff_le Suc_eq_plus1 a0)
  qed
qed

lemma to_tensor_prod_decomp_middle: 
  assumes "j < 2^n" and "m > s" and "m ≤ n" and "t ≥ m - s" and "s + t - 1 ≤ n" and "n ≥ 1"
  shows "(⨂r s t n j) = (⨂r s (m-s-1) n j) ⨂ (⨂r (m-1) 1 n j) ⨂ (⨂r m (t-(m-s)) n j)"
proof-
  have "(⨂r s t n j) = (⨂r s (m-s) n j) ⨂ (⨂r m (t-(m-s)) n j)" 
    using assms to_tensor_prod_decomp_half by blast
  moreover have "(⨂r s (m-s) n j) = (⨂r s (m-s-1) n j) ⨂ (⨂r (m-1) 1 n j)"
  proof-
    have "s + (m - s - 1) - 1 < n" using assms Suc_diff_Suc by linarith
    then have "(⨂r s (m-s-1+1) n j) = (⨂r s (m-s-1) n j) ⨂ (⨂r (s+(m-s-1)) 1 n j) "
      using to_tensor_prod_decomp_right[of j n s "m-s-1"] assms by simp
    moreover have "(s + (m - s - 1)) = m - 1" using assms by linarith
    moreover have "(m - s - 1 + 1) = m - s" using assms by simp
    ultimately show ?thesis by simp
  qed
  ultimately show ?thesis by simp
qed

lemma ket_zero_neq_ket_one:
  shows "|zero⟩ ≠ |one⟩"
proof-
  have "|zero⟩ $$ (0,0) = 1" by simp
  moreover have "|one⟩ $$ (0,0) = 0" by simp
  ultimately show ?thesis by (metis zero_neq_one)
qed

lemma to_tensor_bin_rep_zero: 
  assumes "m ≥ 1"
  shows "(⨂r m 1 n j) = |zero⟩ ⟷ bin_rep n j ! (m-1) = 0"
proof
  assume a0: "(⨂r m 1 n j) = |zero⟩"
  have "(⨂r m 1 n j) = (if (bin_rep n j)!(m-1) = 0 then |zero⟩ else |one⟩)"  using to_tensor_prod_def by simp 
  then have "|zero⟩ = (if (bin_rep n j)!(m-1) = 0 then |zero⟩ else |one⟩)" using a0 by simp
  then show "bin_rep n j ! (m-1) = 0" using ket_zero_neq_ket_one by auto
next
  assume "bin_rep n j ! (m - 1) = 0"
  then show "(⨂r m 1 n j) = |zero⟩" using to_tensor_prod_def by simp 
qed

lemma to_tensor_bin_rep_one: 
  assumes "m ≥ 1" and "j < 2^n" and "m - 1 < n" 
  shows "(⨂r m 1 n j) = |one⟩ ⟷ bin_rep n j ! (m-1) = 1"
proof
  assume a0: "(⨂r m 1 n j) = |one⟩"
  have "(⨂r m 1 n j) = (if (bin_rep n j)!(m-1) = 0 then |zero⟩ else |one⟩)"
    using to_tensor_prod_def by simp 
  then have "|one⟩ = (if (bin_rep n j)!(m-1) = 0 then |zero⟩ else |one⟩)"
    using a0 by simp
  moreover have "(bin_rep n j)!(m-1) = 0 ∨ (bin_rep n j)!(m-1) = 1" 
    using bin_rep_coeff assms by simp
  ultimately show "bin_rep n j ! (m-1) = 1" 
    using ket_zero_neq_ket_one ket_vec_def by auto
next
  assume a0: "bin_rep n j ! (m - 1) = 1"
  then show "(⨂r m 1 n j) = |one⟩"
    using to_tensor_prod_def by simp 
qed

lemma bin_rep_even: (* AB: I will move that in Binary_Nat.thy *)
  assumes "(bin_rep k m)!(k-1) = 0" and "k ≥ 1" and "m < 2^k" 
  shows "even m" 
proof-
  have "bin_rep k m ! (k-1) = (m mod 2^(k-(k-1))) div 2^(k-1-(k-1))"
    using bin_rep_index[of k m "k-1"] assms(2,3) by simp
  moreover have "… = (m mod 2) div 2^0" using assms(2) by simp
  finally have "… = 0" using assms(1) by simp
  then show "even m" by auto
qed

lemma bin_rep_div_even: (* AB: idem *)
  assumes "bin_rep m j ! k = 0" and "j < 2^m" and "m ≥ 1" and "m - k ≥ 1"
  shows "even (j div 2^(m-(k+1)))"
proof-
  have "(bin_rep m (j div 2^(m-k-1)))!(m-1) = 0" 
  proof-
    have "(j div 2^(m-k-1)) < 2^m" using assms by (meson div_le_dividend le_trans not_less)
    then have "(bin_rep m (j div 2^(m-k-1)))!(m-1) = ((j div 2^(m-k-1)) mod 2^(m-(m-1))) div 2^(m-1-(m-1))" 
      using assms bin_rep_index by (meson diff_less le_trans linorder_not_le not_one_le_zero zero_le)
    then have "(bin_rep m (j div 2^(m-k-1)))!(m-1) = (j div 2^(m-k-1)) mod 2 div 1" using assms(3)
      by (metis cancel_comm_monoid_add_class.diff_cancel diff_diff_cancel power_0 power_one_right)
    then have "(bin_rep m (j div 2^(m-k-1)))!(m-1) = (j div 2^(m-k-1)) mod 2" by presburger
    moreover have "(j div 2^(m-k-1)) mod 2 = j mod 2^(m-k) div 2^(m-k-1)" 
      using assms(4) 
      by (smt One_nat_def add.commute add.right_neutral div_add_self1 le_simps(3) mod_div_trivial 
          mod_mult2_eq mult.right_neutral mult_zero_right not_mod2_eq_Suc_0_eq_0 power_eq_0_iff power_minus_mult zero_neq_numeral)
    moreover have "0 = (j mod 2^(m-k)) div 2^(m-1-k)"  
      using assms(1-2)
      by (metis bin_rep_index div_less mod_by_1 mod_if neq0_conv not_less not_less_zero pos2 power_0 zero_less_diff zero_less_power)
    ultimately show ?thesis 
      by (metis cancel_ab_semigroup_add_class.diff_right_commute)
  qed
  moreover have "j div 2^(m-k-1) < 2^m" using assms(2) by (meson div_le_dividend le_less_trans) 
  ultimately show ?thesis using bin_rep_even assms by (metis diff_diff_left)
qed

lemma decomp_unit_vec_zero_right:
  assumes "k ≥ 1" and "m < 2^k" and "even m" 
  shows "|unit_vec (2^k) m⟩ = |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |zero⟩" 
proof
  fix i j
  assume a0: "i < dim_row ( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |zero⟩)" 
     and a1: "j < dim_col ( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |zero⟩)" 
  then have f0: "i < 2^k ∧ j = 0" 
    by (metis (no_types, lifting) One_nat_def assms(1) dim_col_mat(1) dim_col_tensor_mat dim_row_mat(1) dim_row_tensor_mat 
        index_unit_vec(3) ket_vec_def less_eq_Suc_le less_one one_power2 power2_eq_square power_minus_mult)
  then have f1: "( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |zero⟩) $$ (i,j) = |unit_vec (2^(k-1)) (m div 2)⟩ $$ (i div 2, j div 1) 
                 * |zero⟩ $$ (i mod 2, j mod 1)" using unit_vec_def assms ket_vec_def zero_def a0 by simp
  show "( |unit_vec (2^k) m⟩ ) $$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |zero⟩) $$ (i,j)"
  proof (rule disjE)
    show "i = m ∨ i ≠ m" by simp
  next
    assume a2: "i = m"
    then have "( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |zero⟩) $$ (i,j) = 1"
      using a0 f0 assms ket_vec_def unit_vec_def by simp
    then show "( |unit_vec (2^k) m⟩ ) $$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |zero⟩) $$ (i,j)"
      using f0 a2 by simp
  next
    assume a2: "i ≠ m"
    show "( |unit_vec (2^k) m⟩ ) $$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |zero⟩) $$ (i,j)"
    proof(rule disjE)
      show "i div 2 = m div 2 ∨ i div 2 ≠ m div 2" by simp
    next
      assume "i div 2 = m div 2"
      then have "i = m + 1" using a2 assms(3) 
        by (metis add.right_neutral add_Suc_right dvd_mult_div_cancel even_zero less_one linordered_semidom_class.add_diff_inverse 
            odd_two_times_div_two_nat plus_1_eq_Suc)
      then have "i mod 2 = 1" using assms by (meson even_plus_one_iff mod_0_imp_dvd not_mod_2_eq_1_eq_0)
      then have "( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |zero⟩) $$ (i,j) = 0" using f1 by auto
      then show "( |unit_vec (2^k) m⟩ )$$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |zero⟩) $$ (i,j)"
        using assms(2) f0 a2 by (metis index_unit_vec(1) index_unit_vec(3) ket_vec_index)
    next
      assume "i div 2 ≠ m div 2"
      then have "( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |zero⟩) $$ (i,j) = 0" 
        using assms(1-2) f0 f1 
        by (smt One_nat_def div_less ket_vec_def unit_vec_def index_unit_vec(1) index_unit_vec(3) ket_vec_index less_eq_Suc_le 
            less_mult_imp_div_less mult_eq_0_iff power_minus_mult zero_less_one_class.zero_less_one)
      then show "( |unit_vec (2^k) m⟩ )$$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |zero⟩) $$ (i,j)"
        using assms(2) f0 a2 by (smt ket_vec_def unit_vec_def index_unit_vec(1) index_unit_vec(3) ket_vec_index)
    qed
  qed
next
  show "dim_row ( |unit_vec (2^k) m⟩ ) = dim_row ( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |zero⟩)"
    using unit_vec_def zero_def ket_vec_def assms(1)
    by (smt One_nat_def dim_row_mat(1) dim_row_tensor_mat index_unit_vec(3) less_eq_Suc_le power_minus_mult)
next
  show "dim_col ( |unit_vec (2^k) m⟩ ) = dim_col ( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |zero⟩)"
    using unit_vec_def zero_def ket_vec_def by simp
qed

lemma bin_rep_odd: (* AB: I will move that in Binary_Nat.thy *)
  assumes "(bin_rep k m)!(k-1) = 1" and "k ≥ 1" and "m < 2^k" 
  shows "odd m" 
proof-
  have "bin_rep k m ! (k-1) = (m mod 2^(k-(k-1))) div 2^(k-1-(k-1))"
    using bin_rep_index[of k m "k-1"] assms by simp
  then have "1 = (m mod 2) div 2^0" using assms by simp
  then show "odd m" by auto
qed
 
lemma bin_rep_div_odd: (* AB: idem *)
  assumes "bin_rep m j ! k = 1" and "j < 2^m" and "m ≥ 1" and "m - k ≥ 1"
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
  moreover have "m ≥ 1" using assms(3) by simp
  moreover have "j div 2^(m-k-1) < 2^m" using assms(2) by (meson div_le_dividend le_less_trans) 
  ultimately show ?thesis using bin_rep_odd by (metis diff_diff_left)
qed

lemma ket_unit_tensor_ket_one: 
  assumes "k ≥ 1" and "m < 2^k" and "(bin_rep k m)!(k-1) = 1"
  shows "|unit_vec (2^k) m⟩ = |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |one⟩"
proof
  fix i j
  assume a0: "i < dim_row ( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |one⟩)" 
     and a1: "j < dim_col ( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |one⟩)" 
  then have f0: "i < 2^k ∧ j = 0" 
    using assms(1)
    by (metis (no_types, lifting) One_nat_def dim_col_mat(1) dim_col_tensor_mat dim_row_mat(1) dim_row_tensor_mat index_unit_vec(3) 
        ket_vec_def less_eq_Suc_le less_one one_power2 power2_eq_square power_minus_mult)
  then have f1: "( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |one⟩) $$ (i,j) = |unit_vec (2^(k-1)) (m div 2)⟩ $$ (i div 2, j div 1) 
                 * |one⟩ $$ (i mod 2, j mod 1)" using assms a0 unit_vec_def ket_vec_def by simp
  show "( |unit_vec (2^k) m⟩ ) $$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |one⟩) $$ (i,j)"
  proof (rule disjE)
    show "i=m ∨ i≠m" by simp
  next
    assume a2: "i = m" 
    then have "i div 2 = m div 2" using assms by simp
    then have "|unit_vec (2^(k-1)) (m div 2)⟩ $$ (i div 2, j div 1) = 1" using a0 a1 ket_vec_def by simp
    moreover have "i mod 2 = 1" using assms a2 bin_rep_odd odd_iff_mod_2_eq_one by blast
    ultimately have "( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |one⟩) $$ (i,j) = 1"
      using a0 a2 f0 assms ket_vec_def unit_vec_def bin_rep_odd by simp 
    then show "( |unit_vec (2^k) m⟩ ) $$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |one⟩) $$ (i,j)"
      using f0 a2 by simp
  next
    assume a2: "i ≠ m"
    show "( |unit_vec (2^k) m⟩ ) $$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |one⟩) $$ (i,j)"
    proof(rule disjE)
      show "i div 2 = m div 2 ∨ i div 2 ≠ m div 2" by simp
    next
      assume "i div 2 = m div 2"
      then have "i = m - 1" using a2 assms bin_rep_odd 
        by (metis dvd_mult_div_cancel even_zero less_one linordered_semidom_class.add_diff_inverse 
odd_two_times_div_two_nat plus_1_eq_Suc)
      then have "i mod 2 = 0" using assms bin_rep_odd by (simp add: assms(2))
      then have "( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |one⟩) $$ (i,j) = 0" using f1 f0 by simp
      then show "( |unit_vec (2^k) m⟩ )$$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |one⟩) $$ (i,j)"
        using assms(2) f0 a2 by (metis index_unit_vec(1) index_unit_vec(3) ket_vec_index)
    next
      assume "i div 2 ≠ m div 2"
      then have "( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |one⟩) $$ (i,j) = 0" 
        using f0 f1 assms 
        by (metis diff_diff_cancel diff_le_self div_by_1 index_unit_vec(1) index_unit_vec(3) ket_vec_index 
less_power_add_imp_div_less mult_eq_0_iff ordered_cancel_comm_monoid_diff_class.add_diff_inverse power_one_right)
      then show "( |unit_vec (2^k) m⟩ )$$ (i,j) = ( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |one⟩) $$ (i,j)"
        using f0 a2 assms(2) by (metis index_unit_vec(1) index_unit_vec(3) ket_vec_index)
    qed
  qed
next
  show "dim_row ( |unit_vec (2^k) m⟩ ) = dim_row ( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |one⟩)"
    using ket_vec_def assms 
    by (smt One_nat_def dim_row_mat(1) dim_row_tensor_mat index_unit_vec(3) le_simps(3) power_minus_mult)
next
  show "dim_col ( |unit_vec (2^k) m⟩ ) = dim_col ( |unit_vec (2^(k-1)) (m div 2)⟩ ⨂ |one⟩)"
    using ket_vec_def by simp
qed

lemma div_of_div: (* AB: I should later move that in Basics.thy *)
  fixes j n:: nat
  assumes "n ≥ 1"
  shows "j div 2^(n-1) div 2 = j div 2^n" 
  using assms
  by (metis One_nat_def Suc_1 diff_Suc_1 diff_self_eq_0 div_mult2_eq eq_iff less_imp_add_positive mult.commute not_less plus_1_eq_Suc power.simps(2))

lemma aux_ket_unit_to_tensor_prod: 
  assumes "j < 2^m" and "k ≥ 1"
  shows "k ≤ m ⟶ (⨂r 1 k m j) = |unit_vec (2^k) (j div 2^(m-k))⟩"
proof(rule Nat.nat_induct_at_least[of 1 k])
  show "k ≥ 1" using assms by simp
next
  show "1 ≤ m ⟶ (⨂r 1 1 m j) = |unit_vec (2^1) (j div 2^(m-1))⟩"
  proof
    assume a0: "1 ≤ m"
    show "(⨂r 1 1 m j) = |unit_vec (2^1) (j div 2^(m-1))⟩" 
    proof(rule disjE)
      show "(bin_rep m j)!0 = 0 ∨ (bin_rep m j)!0 = 1" 
        using a0 assms(1) bin_rep_coeff less_le_trans less_numeral_extra(1) by simp
    next
      assume a1: "(bin_rep m j)!0 = 0"
      then have "j div 2^(m-1) = 0" 
        using a0 assms(1)
        by (metis One_nat_def bin_rep_index diff_diff_left diff_zero div_by_0 div_le_dividend le_simps(3) mod_if plus_1_eq_Suc) 
      then have " |unit_vec (2^1) (j div 2^(m-1))⟩ = |zero⟩" using ket_vec_def by auto
      moreover have "(⨂r 1 1 m j) = |zero⟩" using to_tensor_prod_def a1 by simp
      ultimately show "(⨂r 1 1 m j) = |unit_vec (2^1) (j div 2^(m-1))⟩" by simp
    next
      assume a1: "(bin_rep m j)!0 = 1"
      then have "j div 2^(m-1) = 1" 
        using a0 assms(1)
        by (metis One_nat_def bin_rep_index diff_diff_left diff_zero div_by_0 div_le_dividend le_simps(3) mod_if plus_1_eq_Suc) 
      then have " |unit_vec (2^1) (j div 2^(m-1))⟩ = |one⟩" using ket_vec_def by auto
      moreover have "(⨂r 1 1 m j) = |one⟩" using to_tensor_prod_def a1 by simp
      ultimately show "(⨂r 1 1 m j) = |unit_vec (2^1) (j div 2^(m-1))⟩" by simp
    qed
  qed
next
  fix k 
  assume IH: "k ≤ m ⟶ (⨂r 1 k m j) = |unit_vec (2^k) (j div 2^(m-k))⟩"
     and a0: "k ≥ 1"
  show "(Suc k) ≤ m ⟶ (⨂r 1 (Suc k) m j) = |unit_vec (2^(Suc k)) (j div 2^(m-(Suc k)))⟩"
  proof
    assume a1: "(Suc k) ≤ m"
    show "(⨂r 1 (Suc k) m j) = |unit_vec (2^(Suc k)) (j div 2^(m-(Suc k)))⟩"
    proof (rule disjE)
      show "(bin_rep m j)!k = 0 ∨ (bin_rep m j)!k = 1" 
        using bin_rep_coeff a1 assms(1) less_eq_Suc_le by simp
    next 
      assume a2: "(bin_rep m j)!k = 0"
      then have "(⨂r 1 (Suc k) m j) = (⨂r 1 k m j) ⨂ |zero⟩" 
        using to_tensor_prod_decomp_left_zero[of "k+1" m j 1]   
        by (metis Suc_eq_plus1 add_diff_cancel_left' to_tensor_prod_decomp_right_zero)
      then have "(⨂r 1 (Suc k) m j) = |unit_vec (2^k) (j div 2^(m-k))⟩ ⨂ |zero⟩" 
        using IH a1 Suc_leD by presburger
      then have "(⨂r 1 (Suc k) m j) = |unit_vec (2^k) (j div 2^(m-(Suc k)) div 2)⟩ ⨂ |zero⟩" 
        using div_of_div[of "m-k" "j"] a1 by simp
      moreover have "even (j div 2^(m-(Suc k)))" using a0 a1 a2 assms bin_rep_div_even 
        by (metis Suc_eq_plus1 Suc_leD add_le_imp_le_diff le_trans plus_1_eq_Suc)
      ultimately show "(⨂r 1 (Suc k) m j) = |unit_vec (2^(Suc k)) (j div 2^(m-(Suc k)))⟩ " 
        using decomp_unit_vec_zero_right a0 a1 assms(1) 
        by (metis (no_types, lifting) add_diff_cancel_left' le_SucI less_power_add_imp_div_less 
            ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
    next
      assume a2: "(bin_rep m j)!k = 1"
      then have "(⨂r 1 (Suc k) m j) = (⨂r 1 k m j) ⨂ |one⟩" 
        using to_tensor_prod_decomp_left_one[of "k+1" m j 1]   
        by (metis Suc_eq_plus1 add_diff_cancel_left' to_tensor_prod_decomp_right_one)
      then have "(⨂r 1 (Suc k) m j) = |unit_vec (2^k) (j div 2^(m-k))⟩ ⨂ |one⟩" 
        using IH a1 Suc_leD by presburger
      then have "(⨂r 1 (Suc k) m j) = |unit_vec (2^k) (j div 2^(m-(Suc k)) div 2)⟩ ⨂ |one⟩" 
        using div_of_div[of "m-k" "j"] a1 by simp
      moreover have "odd (j div 2^(m-(Suc k)))" 
        using a0 a1 a2 assms bin_rep_div_odd 
        by (metis Suc_eq_plus1 Suc_leD add_le_imp_le_diff le_trans plus_1_eq_Suc)
      ultimately show "(⨂r 1 (Suc k) m j) = |unit_vec (2^(Suc k)) (j div 2^(m-(Suc k)))⟩"
        using a0 a1 assms(1) ket_unit_tensor_ket_one
        by (metis (no_types, lifting) add_diff_cancel_left' bin_rep_coeff bin_rep_even le_SucI lessI less_power_add_imp_div_less 
            ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc zero_order(1))
    qed
  qed
qed

lemma ket_unit_to_tensor_prod: 
  assumes "j < 2^n" and "n ≥ 1"
  shows "(⨂r 1 n n j) = |unit_vec (2^n) j⟩" 
  using aux_ket_unit_to_tensor_prod assms by simp


subsection ‹The Controlled Phase Gate CR›

(*bin_frac l k m j is defined as j⇩l/2+j⇩l⇩+⇩1/2⇧2+...+j⇩m/2⇧m⇧-⇧l⇧+⇧1 *)
definition bin_frac :: "nat ⇒ nat ⇒ nat ⇒ nat ⇒ complex" where
"bin_frac l k m j ≡ (∑i∈{l..k}. ((bin_rep m j)!i) /2^(i-l+1) )"

(* The controlled phase gate is applied to two qubits and performs a phase shift on the first qubit
(current qubit) iff the second qubit (control qubit) is |1⟩. The parameter k is not the index of the 
control qubit but of the distance between the current and the control qubit.
E.g. if the current qubit is the first qubit CR⇩2 should be applied to the first and second qubit, if 
the current qubit is the n-1th qubit, CR⇩2 should be applied to the n-1th qubit and the nth qubit. *)
definition controlled_phase_shift:: "nat ⇒ complex Matrix.mat" ("CR _") where
"CR k ≡ Matrix.mat 4 4 (λ(i,j). if i = j then (if i = 3 then (exp (2*pi*𝗂*1/2^k)) else 1) else 0)"

(* AB: note to myself, maybe it should be cR with a lower-case as it's common in textbooks.
In that case I should rename CNOT in Quantum.thy with cNOT. *)

(* phase_shifted_qubit defines the result of applying CR gates to the current qubit (H*|j⇩i⟩)
E.g. psq 1 n n j_dec is 1\sqrt(2)*(|0⟩ + e⇧2⇧π⇧i⇧0⇧.⇧j⇧1⇧j⇧2⇧.⇧.⇧.⇧j⇧n|1⟩) 
     psq n n n j_dec is 1\sqrt(2)*(|0⟩ + e⇧2⇧π⇧i⇧0⇧.⇧j⇧n|1⟩) *)
definition phase_shifted_qubit :: "nat ⇒ nat ⇒ nat ⇒ nat ⇒ complex Matrix.mat" ("psq _ _ _ _") where 
"psq s t m jd ≡ (Matrix.mat 2 1 (λ(i,j). if i=0 then (1::complex)/sqrt(2) 
              else (exp (complex_of_real (2*pi)*𝗂*(bin_frac (s-1) (t-1) m jd)))*1/sqrt(2)))"

lemma transpose_of_CR: 
  shows "(CR k)⇧t = (CR k)"
  using controlled_phase_shift_def dagger_def by auto

lemma dagger_of_CR:
  fixes k
  defines "CR_dagger ≡ Matrix.mat 4 4 (λ(i,j). if i = j then (if i = 3 then (exp (2*pi*-𝗂*1/2^k)) else 1) else 0)"
  shows "(CR k)⇧† = CR_dagger"
proof
  fix i j:: nat
  assume "i < dim_row CR_dagger" and "j < dim_col CR_dagger"
  then have "i ∈ {0,1,2,3}" and "j ∈ {0,1,2,3}" using controlled_phase_shift_def CR_dagger_def by auto
  moreover have "cnj (exp (2 * complex_of_real pi * 𝗂 / 2^k)) = exp (2 * complex_of_real pi * -𝗂 / 2^k)"
  proof
    show "Re (cnj (exp (2 * complex_of_real pi * 𝗂 / 2^k))) = Re (exp (2 * complex_of_real pi * -𝗂 / 2^k))"
    proof-
      have "Re (exp (2 * complex_of_real pi * 𝗂 / 2^k)) = cos (2 * pi * 1/2^k)" 
        by (smt cis.simps(1) cis_conv_exp mult.commute mult_2 of_real_add of_real_divide of_real_hom.hom_one of_real_power one_add_one 
            times_divide_eq_left)
      moreover have "Re (exp (2 * complex_of_real pi * -𝗂 / 2^k)) = cos (2 * pi * 1/2^k)" 
      proof-
        have "2 * complex_of_real pi * -𝗂 / 2^k = 𝗂 * complex_of_real (-1 * (2 * pi / 2^k))" by (simp add: mult.commute)
        then have "Re (exp (2 * complex_of_real pi * -𝗂 / 2^k)) = Re (exp (𝗂 * complex_of_real (-1 * (2 * pi / 2^k))))" by presburger
        then have "Re (exp (2 * complex_of_real pi * -𝗂 / 2^k)) = Re (cis (-1 * (2 * pi / 2^k)))" using cis_conv_exp by auto
        then show ?thesis by simp
      qed
      ultimately show ?thesis by simp
    qed
  next
    show "Im (cnj (exp (2 * complex_of_real pi * 𝗂 / 2^k))) = Im (exp (2 * complex_of_real pi * -𝗂 / 2^k))"
    proof-
      have "Im (cnj (exp (2 * complex_of_real pi * 𝗂 / 2^k))) = -Im (exp (2 * complex_of_real pi * 𝗂 / 2^k))" 
        using cnj_def by simp
      then have "Im (cnj (exp (2 * complex_of_real pi * 𝗂 / 2^k))) = -sin(2 * pi * 1/2^k)" 
      proof -
        have "Im (cnj (exp (complex_of_real 2 * complex_of_real pi * 𝗂 / complex_of_real 2^k))) = - Im (exp (𝗂 * complex_of_real (2 * pi / 2^k)))"
          by (simp add: mult.commute)
        then show ?thesis
          by (metis cis.simps(2) cis_conv_exp mult.right_neutral of_real_numeral)
      qed
      moreover have "Im (exp (2 * complex_of_real pi * -𝗂 / 2^k)) = - sin(2 * pi * 1/2^k)" using Im_exp by auto
      ultimately show ?thesis by simp
    qed
  qed
  ultimately show "(CR k)⇧† $$ (i, j) = CR_dagger $$ (i, j)"
    apply (auto simp add: dagger_def)
    apply (auto simp add: controlled_phase_shift_def CR_dagger_def).
next
  show "dim_row (CR k)⇧† = dim_row CR_dagger" using controlled_phase_shift_def CR_dagger_def by simp
next
  show "dim_col (CR k)⇧† = dim_col CR_dagger" using controlled_phase_shift_def CR_dagger_def by simp
qed

lemma controlled_CR_is_gate: 
  shows "gate 2 (CR k)"
proof
  show "dim_row (CR k) = 2⇧2" using controlled_phase_shift_def by simp
next
  show "square_mat (CR k)" by (simp add: controlled_phase_shift_def)
next
  show "unitary (CR k)"
  proof-
    have "(CR k)⇧† * (CR k) = 1⇩m (dim_col (CR k))"
    proof
      show "dim_row ((CR k)⇧† * (CR k)) = dim_row (1⇩m (dim_col (CR k)))" by simp
    next
      show "dim_col ((CR k)⇧† * (CR k)) = dim_col (1⇩m (dim_col (CR k)))" by simp
    next
      fix i j:: nat
      assume "i < dim_row (1⇩m (dim_col (CR k)))" and "j < dim_col (1⇩m (dim_col (CR k)))"
      then have "i ∈ {0,1,2,3}" and "j ∈ {0,1,2,3}" using controlled_phase_shift_def by auto
      moreover have "(CR k)⇧† = Matrix.mat 4 4 (λ(i,j). if i = j then (if i = 3 then (exp (2*pi*-𝗂*1/2^k)) else 1) else 0)"
        using dagger_of_CR by simp     
      moreover have "exp (- (2 * complex_of_real pi * 𝗂 / 2 ^ k)) * exp (2 * complex_of_real pi * 𝗂 / 2 ^ k) = 1" 
        by (simp add: mult_exp_exp)
      ultimately show "((CR k)⇧† * (CR k)) $$ (i,j) = 1⇩m (dim_col (CR k)) $$ (i, j)"
        apply (auto simp add: one_mat_def times_mat_def)
         apply (auto simp: scalar_prod_def controlled_phase_shift_def).
    qed
    then show ?thesis 
      by (metis cnj_transpose_is_dagger dim_col_of_dagger index_transpose_mat(2) transpose_cnj_is_dagger 
          transpose_of_CR transpose_of_prod transpose_one unitary_def)
  qed
qed

lemma exp_mult: 
  assumes "r - 1 < m" and "s ≤ r - 1" and "s ≥ 1"
  shows "(exp (complex_of_real (2*pi)*𝗂*(bin_frac (s-1) (r-1-1) m jd))) * (exp (2*pi*𝗂*((bin_rep m jd)!(r-1))/2^(r-s+1)))
        = (exp (complex_of_real (2*pi)*𝗂*(bin_frac (s-1) (r-1) m jd)))" 
proof-
  have "(exp (2*pi*𝗂*(bin_frac (s-1) (r-1-1) m jd))) * (exp (2*pi*𝗂*((bin_rep m jd)!(r-1))/2^(r-s+1)))
      = exp (2*pi*𝗂*(bin_frac (s-1) (r-1-1) m jd) + 2*pi*𝗂*((bin_rep m jd)!(r-1))/2^(r-s+1))" 
    by (simp add: exp_add)
  moreover have "2*pi*𝗂*(bin_frac (s-1) (r-1-1) m jd) + 2*pi*𝗂*((bin_rep m jd)!(r-1))/2^(r-s+1)
      = 2*pi*𝗂*((bin_frac (s-1) (r-1-1) m jd)+((bin_rep m jd)!(r-1))/2^(r-s+1))" 
    using comm_semiring_class.distrib[of "(bin_frac (s-1) (r-1-1) m jd)" "((bin_rep m jd)!(r-1))/2^(r-s+1)" "(2*pi*𝗂)::complex"] 
    by (simp add: mult.commute)
  moreover have "2*pi*𝗂*((bin_frac (s-1) (r-1-1) m jd)+((bin_rep m jd)!(r-1))/2^(r-s+1)) = 2*pi*𝗂*(bin_frac (s-1) (r-1) m jd)"
  proof-
    have "s - 1 < (r - 1) + 1" using assms by simp
    moreover have "finite {(s-1)..(r-1-1)}" and "finite {r-1}" and "{(s-1)..(r-1-1)} ∩ {r-1} = {}" 
              and "{(s-1)..(r-1-1)} ∪ {r-1} = {(s-1)..(r-1)}" using assms by auto
    ultimately have "(∑i∈{(s-1)..(r-1-1)}. ((bin_rep m jd)!i) /2^(i-(s-1)+1)) 
                   + ((bin_rep m jd)!(r-1))/2^((r-1)-(s-1)+1)
                   = (∑i∈{(s-1)..(r-1)}. ((bin_rep m jd)!i) /2^(i-(s-1)+1))" 
      using sum_Un assms(2-3) by (smt atLeastatMost_empty atLeastatMost_empty_iff diff_le_self le_trans plus_1_eq_Suc 
            ordered_cancel_comm_monoid_diff_class.add_diff_inverse sum.cl_ivl_Suc)
    moreover have "((bin_rep m jd)!(r-1))/2^(r-s+1) = ((bin_rep m jd)!(r-1))/2^((r-1)-(s-1)+1)" 
      using assms(3) by simp
    ultimately have "(∑i∈{(s-1)..(r-1-1)}. ((bin_rep m jd)!i) /2^(i-(s-1)+1)) 
                   + ((bin_rep m jd)!(r-1))/2^(r-s+1)
                   = (∑i∈{(s-1)..(r-1)}. ((bin_rep m jd)!i) /2^(i-(s-1)+1))"  
      by auto
    moreover have "(bin_frac (s-1) (r-1-1) m jd)+((bin_rep m jd)!(r-1))/2^(r-s+1) 
                 = (∑i∈{(s-1)..(r-1-1)}. ((bin_rep m jd)!i) /2^(i-(s-1)+1)) + ((bin_rep m jd)!(r-1))/2^(r-s+1)"
      using bin_frac_def by simp
    ultimately have "(bin_frac (s-1) (r-1-1) m jd)+((bin_rep m jd)!(r-1))/2^(r-s+1) 
                   = (∑i∈{(s-1)..(r-1)}. ((bin_rep m jd)!i) /2^(i-(s-1)+1))"  
      by auto
    moreover have "(∑i∈{(s-1)..(r-1)}. ((bin_rep m jd)!i) /2^(i-(s-1)+1)) = bin_frac (s-1) (r-1) m jd" using bin_frac_def by auto
    ultimately show ?thesis by auto
  qed
  ultimately show "(exp (complex_of_real (2*pi)*𝗂*(bin_frac (s-1) (r-1-1) m jd))) * (exp (2*pi*𝗂*((bin_rep m jd)!(r-1))/2^(r-s+1)))
                 = (exp (complex_of_real (2*pi)*𝗂*(bin_frac (s-1) (r-1) m jd)))" by simp
qed

(*E.g. for 1\sqrt(2)*(|0⟩ + e⇧2⇧π⇧i⇧0⇧.⇧j⇧1⇧j⇧2|1⟩ one has s=1 and r=2. Then, CR (2-1+2) = CR 3 is applied and 
1\sqrt(2)*(|0⟩ + e⇧2⇧π⇧i⇧0⇧.⇧j⇧1⇧j⇧2⇧j⇧3|1⟩ is obtained.*)

lemma app_CR_on_ket_zero:
  assumes "r - 1 < m" and "s ≤ r - 1" and "s ≥ 1" and "((bin_rep m jd)!(r-1)) = 0" 
  shows "(CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |zero⟩) = (psq s r m jd) ⨂ |zero⟩"
proof
  fix i j::nat
  assume "i < Matrix.dim_row ((psq s r m jd) ⨂ |zero⟩)" and "j < Matrix.dim_col ((psq s r m jd) ⨂ |zero⟩)" 
  then have f0: "i < 4 ∧ j = 0" using ket_vec_def phase_shifted_qubit_def by simp
  then have "((CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |zero⟩)) $$ (i,j) 
           = (∑k∈{0,1,2,3}. ((CR (r-s+1)) $$ (i,k)) * (((psq s (r-1) m jd) ⨂ |zero⟩) $$ (k,j)))" 
    using f0 ket_vec_def phase_shifted_qubit_def set_4 atLeast0LessThan controlled_phase_shift_def by simp
  then have f1: "((CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |zero⟩)) $$ (i,j) 
               = ((CR (r-s+1)) $$ (i,0)) * (1::complex)/sqrt(2)
               + ((CR (r-s+1)) $$ (i,2)) * exp (complex_of_real (2*pi) *𝗂*(bin_frac (s-1) (r-1-1) m jd))*1/sqrt(2)" 
    using f0 ket_vec_def phase_shifted_qubit_def by simp
  moreover have "i=0 ⟶ ((CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |zero⟩)) $$ (i,j) = 1/sqrt(2)"
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=0 ⟶ ((psq s r m jd) ⨂ |zero⟩) $$ (i,j) = 1/sqrt(2)" 
    using phase_shifted_qubit_def ket_vec_def f0 by simp
  moreover have "i=1 ⟶ ((CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |zero⟩)) $$ (i,j) = 0"
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=1 ⟶ ((psq s r m jd) ⨂ |zero⟩) $$ (i,j) = 0" 
    using phase_shifted_qubit_def ket_vec_def f0 by simp
  moreover have "i=2 ⟶ ((CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |zero⟩)) $$ (i,j) 
           = (exp (complex_of_real (2*pi)*𝗂*(bin_frac (s-1) (r-1) m jd))) *1/sqrt(2)" 
  proof-
    have "i=2 ⟶ ((CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |zero⟩)) $$ (i,j) 
           = (exp (complex_of_real (2*pi)*𝗂*(bin_frac (s-1) (r-1-1) m jd))) * 1 * 1/sqrt(2)" 
      using controlled_phase_shift_def f1 by auto
    moreover have "(exp (2*pi*𝗂*((bin_rep m jd)!(r-1))/2^(r-s+1))) = 1" 
      using assms by simp
    moreover have "(exp (complex_of_real (2*pi)*𝗂*(bin_frac (s-1) (r-1-1) m jd))) * (exp (2*pi*𝗂*((bin_rep m jd)!(r-1))/2^(r-s+1)))
        = (exp (complex_of_real (2*pi)*𝗂*(bin_frac (s-1) (r-1) m jd)))" 
      using exp_mult assms by blast
    ultimately show ?thesis by simp
  qed
  moreover have "i=2 ⟶ ((psq s r m jd) ⨂ |zero⟩) $$ (i,j) = exp (complex_of_real (2*pi)*𝗂*(bin_frac (s-1) (r-1) m jd))*1/sqrt(2)" 
    using phase_shifted_qubit_def ket_vec_def f0 by simp
  moreover have "i=3 ⟶ ((CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |zero⟩)) $$ (i,j) = 0"
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=3 ⟶ ((psq s r m jd) ⨂ |zero⟩) $$ (i,j) = 0" 
    using phase_shifted_qubit_def ket_vec_def f0 by simp
  moreover have "i∈{0,1,2,3}" using f0 by auto
  ultimately show "((CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |zero⟩)) $$ (i,j) = ((psq s r m jd) ⨂ |zero⟩) $$ (i,j)" 
    using f0 ket_vec_def phase_shifted_qubit_def by (smt index_sl_four)
next
  show "dim_row ((CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |zero⟩)) = dim_row ((psq s r m jd) ⨂ |zero⟩)" 
    by (simp add: controlled_phase_shift_def phase_shifted_qubit_def ket_vec_def)
next
  show "dim_col ((CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |zero⟩)) = dim_col ((psq s r m jd) ⨂ |zero⟩)"
    using controlled_phase_shift_def phase_shifted_qubit_def by simp
qed

lemma app_CR_on_ket_one: 
  assumes "r-1 < m" and "s≤r-1" and "s≥1" and "((bin_rep m jd)!(r-1)) = 1"
  shows "(CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |one⟩) = (psq s r m jd) ⨂ |one⟩"
proof
  fix i j::nat
  assume "i < Matrix.dim_row ((psq s r m jd) ⨂ |one⟩)" and "j < Matrix.dim_col ((psq s r m jd) ⨂ |one⟩)" 
  then have f0: "i<4 ∧ j=0" using ket_vec_def phase_shifted_qubit_def by simp
  then have "((CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |one⟩)) $$ (i,j) 
           = (∑k∈{0,1,2,3}. ((CR (r-s+1)) $$ (i,k)) * (((psq s (r-1) m jd) ⨂ |one⟩) $$ (k,j)))" 
    using f0 ket_vec_def phase_shifted_qubit_def set_4 atLeast0LessThan controlled_phase_shift_def by simp
  then have f1: "((CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |one⟩)) $$ (i,j) 
           = ((CR (r-s+1)) $$ (i,1)) * (1::complex)/sqrt(2)
           + ((CR (r-s+1)) $$ (i,3)) * exp (complex_of_real (2*pi) *𝗂*(bin_frac (s-1) (r-1-1) m jd))*1/sqrt(2)" 
    using f0 ket_vec_def phase_shifted_qubit_def by simp
  moreover have "i=0 ⟶ ((CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |one⟩)) $$ (i,j) =0"
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=0 ⟶ ((psq s r m jd) ⨂ |one⟩) $$ (i,j) = 0" 
    using phase_shifted_qubit_def ket_vec_def f0 by simp
  moreover have "i=1 ⟶ ((CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |one⟩)) $$ (i,j) = 1/sqrt(2)"
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=1 ⟶ ((psq s r m jd) ⨂ |one⟩) $$ (i,j) = 1/sqrt(2)"
    using phase_shifted_qubit_def ket_vec_def f0 by simp
  moreover have "i=2 ⟶ ((CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |one⟩)) $$ (i,j) = 0" 
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=2 ⟶ ((psq s r m jd) ⨂ |one⟩) $$ (i,j) = 0" 
    using phase_shifted_qubit_def ket_vec_def f0 by simp
  moreover have "i=3 ⟶ ((CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |one⟩)) $$ (i,j) = (exp (complex_of_real (2*pi)*𝗂*(bin_frac (s-1) (r-1) m jd))) * 1/sqrt(2)" 
  proof-
   have "i=3 ⟶ ((CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |one⟩)) $$ (i,j) 
           = (exp (complex_of_real (2*pi)*𝗂*(bin_frac (s-1) (r-1-1) m jd))) * (exp (complex_of_real (2*pi)*𝗂*1/2^(r-s+1))) * 1/sqrt(2)" 
     using controlled_phase_shift_def f1 by auto
   moreover have "exp (complex_of_real (2*pi)*𝗂*1/2^(r-s+1)*(bin_rep m jd)!(r-1)) 
                = exp (complex_of_real (2*pi)*𝗂*1/2^(r-s+1)) " using assms by simp
   moreover have "(exp (complex_of_real (2*pi)*𝗂*(bin_frac (s-1) (r-1-1) m jd))) * (exp (2*pi*𝗂*((bin_rep m jd)!(r-1))/2^(r-s+1)))
        = (exp (complex_of_real (2*pi)*𝗂*(bin_frac (s-1) (r-1) m jd)))" using exp_mult assms by blast
   ultimately show ?thesis using assms by simp
 qed
  moreover have "i=3 ⟶ ((psq s r m jd) ⨂ |one⟩) $$ (i,j) = (exp (complex_of_real (2*pi)*𝗂*(bin_frac (s-1) (r-1) m jd))) * 1/sqrt(2)" 
    using phase_shifted_qubit_def ket_vec_def f0 by simp
  moreover have "i∈{0,1,2,3}" using f0 by auto
  ultimately show "((CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |one⟩)) $$ (i,j) = ((psq s r m jd) ⨂ |one⟩) $$ (i,j)" 
    using f0 ket_vec_def phase_shifted_qubit_def by (smt index_sl_four)
next
  show "dim_row ((CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |one⟩)) = dim_row ((psq s r m jd) ⨂ |one⟩)" 
    by (simp add: controlled_phase_shift_def ket_vec_def phase_shifted_qubit_def)
next
  show "dim_col ((CR (r-s+1)) * ((psq s (r-1) m jd) ⨂ |one⟩)) = dim_col ((psq s r m jd) ⨂ |one⟩)"
    using ket_vec_def controlled_phase_shift_def phase_shifted_qubit_def by simp
qed


subsection ‹Swapping of the Qubits›

(*The idea is to apply the controlled R gate only to the tensor product of two single qubits. The first qubit is 
already at the current position. This is the qubit we want to apply the R_j gate too. The second qubit is "hidden" 
in the unit vector (which is just a tensor product of single qubit where the qubit at position j is the one we need). 
Thus, we repeatedly swap qubit j with the qubit in front of it until it directly follows the current qubit. Then, 
we can apply the controlled R gate which leaves the second qubit untouched (see proofs above). Then we can switch the
qubit back to its original position. *)
abbreviation swapping_gate :: "complex Matrix.mat" ("SWAP") where
"SWAP ≡ Matrix.mat 4 4 (λ(i,j). if i=0 ∧ j=0 then 1 else 
                                (if i=1 ∧ j=2 then 1 else 
                                (if i=2 ∧ j=1 then 1 else 
                                (if i=3 ∧ j=3 then 1 else 0))))"

lemma transpose_of_swapping_gate: 
  shows "(SWAP)⇧t = SWAP"
proof
  fix i j::nat
  assume a0: "i < dim_row SWAP" and a1: "j < dim_col SWAP"
  then have "i ∈ {0,1,2,3}" and "j ∈ {0,1,2,3}" by auto
  then show  "(SWAP)⇧t $$ (i,j) = SWAP $$ (i,j)" by auto    
next
  show "dim_row (SWAP)⇧t = dim_row SWAP" by simp
next
  show "dim_col (SWAP)⇧t = dim_col SWAP"  by simp
qed

lemma dagger_of_SWAP: 
  shows "(SWAP)⇧† = SWAP"
proof
  show "dim_row (SWAP⇧†) = dim_row SWAP" by simp
next
  show "dim_col (SWAP⇧†) = dim_col SWAP" by simp
next
  fix i j:: nat
  assume "i < dim_row SWAP" and "j < dim_col SWAP"
  then have "i ∈ {0,1,2,3}" and "j ∈ {0,1,2,3}" by auto
  thus "SWAP⇧† $$ (i, j) = SWAP $$ (i, j)" 
    using dagger_def by auto
qed

lemma SWAP_gate:
  shows "gate 2 SWAP" 
proof
  show "dim_row SWAP = 2⇧2" by simp
next
  show "square_mat SWAP" by simp
next
  show "unitary SWAP" 
  proof-
    have "(SWAP)⇧† * SWAP = 1⇩m (dim_col SWAP)"
    proof
      show "dim_row ((SWAP)⇧† * SWAP) = dim_row (1⇩m (dim_col SWAP))" by simp
    next
      show "dim_col ((SWAP)⇧† * SWAP) = dim_col (1⇩m (dim_col SWAP))" by simp
    next
      fix i j:: nat
      assume "i < dim_row (1⇩m (dim_col SWAP))" and "j < dim_col (1⇩m (dim_col SWAP))"
      then have "i ∈ {0,1,2,3}" and "j ∈ {0,1,2,3}" using controlled_phase_shift_def by auto 
      then show "((SWAP)⇧† * SWAP) $$ (i,j) = 1⇩m (dim_col SWAP) $$ (i, j)"
        apply (auto simp add: one_mat_def times_mat_def)
         apply (auto simp: scalar_prod_def controlled_phase_shift_def).
    qed
    then show ?thesis 
      by (simp add: dagger_of_SWAP unitary_def)
  qed    
qed

lemma app_SWAP:
  assumes "dim_row v = 2" and "dim_col v = 1"
      and "dim_row w = 2" and "dim_col w = 1"
  shows "SWAP * (v ⨂ w) = w ⨂ v"
proof
  fix i j
  assume "i < dim_row (w ⨂ v)" and "j < dim_col (w ⨂ v)"
  then have "i ∈ {0,1,2,3}" and "j = 0" using assms by auto 
  moreover have "(SWAP * (v ⨂ w)) $$ (0,0) = (w ⨂ v) $$ (0,0)" using lessThan_atLeast0 assms by simp
  moreover have "(SWAP * (v ⨂ w)) $$ (1,0) = (w ⨂ v) $$ (1,0)" using lessThan_atLeast0 assms by simp 
  moreover have "(SWAP * (v ⨂ w)) $$ (2,0) = (w ⨂ v) $$ (2,0)" using lessThan_atLeast0 assms by simp 
  moreover have "(SWAP * (v ⨂ w)) $$ (3,0) = (w ⨂ v) $$ (3,0)" using lessThan_atLeast0 assms by simp 
  ultimately show "(SWAP * (v ⨂ w)) $$ (i,j) = (w ⨂ v) $$ (i,j)" by blast
next
  show "dim_row (SWAP * (v ⨂ w)) = dim_row (w ⨂ v)" using assms by simp
next
  show "dim_col (SWAP * (v ⨂ w)) = dim_col (w ⨂ v)" using assms by simp
qed

(*Swaps the k+1 and k+2 qubit of a k+2+t qubit system. E.g. |011010⟩ and k=1 and t=3 gives |001110⟩ *)
definition SWAP_all :: "nat ⇒ nat ⇒ complex Matrix.mat" where
"SWAP_all k t ≡ (Id k) ⨂ SWAP ⨂ (Id t)"

lemma SWAP_all_dim [simp]:
  shows "dim_row (SWAP_all k t) = 2^(k+2+t)"
    and "dim_col (SWAP_all k t) = 2^(k+2+t)" 
proof-
  show "dim_row (SWAP_all k t) = 2^(k+2+t)"
    using Id_def SWAP_all_def by (simp add: power_add)
next 
  show "dim_col (SWAP_all k t) = 2^(k+2+t)" 
    using Id_def SWAP_all_def by (simp add: power_add)
qed

lemma SWAP_tensor_Id_is_gate:
  shows "gate (k+2) ((Id k) ⨂ SWAP)"
proof
  show "dim_row ((Id k) ⨂ SWAP) = 2^(k+2)" using Id_def by simp
next
  show "square_mat ((Id k) ⨂ SWAP)" using Id_def by simp
next
  have "gate 2 SWAP" using SWAP_gate by simp
  moreover have "gate k (Id k)" by simp 
  ultimately show "unitary ((Id k) ⨂ SWAP)"
    using gate.unitary tensor_gate SWAP_gate by blast
qed

lemma SWAP_all_is_gate:
  shows "gate (k+2+t) (SWAP_all k t)"
proof
  show "dim_row (SWAP_all k t) = 2^(k+2+t)" by simp
next
  show "square_mat (SWAP_all k t)" by simp
next
  show "unitary (SWAP_all k t)"
  proof-
    have "((SWAP_all k t)⇧†) * (SWAP_all k t) = 1⇩m (dim_col (SWAP_all k t))"
    proof-
      have "((SWAP_all k t)⇧†) * (SWAP_all k t) = ((Id k) ⨂ SWAP ⨂ (Id t))⇧† * ((Id k) ⨂ SWAP ⨂ (Id t))" 
        using SWAP_all_def by simp
      moreover have "((Id k) ⨂ SWAP ⨂ (Id t))⇧† * ((Id k) ⨂ SWAP ⨂ (Id t)) = 1⇩m (2^(k+2+t))"
      proof-
        have "gate (k+2) ((Id k) ⨂ SWAP)" using SWAP_tensor_Id_is_gate by simp
        moreover have "gate t (Id t)" by simp
        moreover have "dim_col ((Id k) ⨂ SWAP) * dim_col (Id t) = 2^(k+2+t)" 
          using SWAP_all_def SWAP_all_dim(2) by simp
        ultimately show "((Id k) ⨂ SWAP ⨂ (Id t))⇧† * ((Id k) ⨂ SWAP ⨂ (Id t)) = 1⇩m (2^(k+2+t))"
        using tensor_gate_unitary1[of "k+2" "((Id k) ⨂ SWAP)" t "Id t"] by auto
     qed
     ultimately show ?thesis by auto
   qed
    then show ?thesis 
      by (simp add: carrier_matI mat_mult_left_right_inverse unitary_def)
  qed
qed

lemma app_SWAP_all:
  assumes "dim_row v = 2" and "dim_col v = 1"  
      and "dim_row w = 2" and "dim_col w = 1" 
      and "length xs = k" and "length ys = t"
      and "∀x ∈ set xs. dim_row x = 2" and "∀y ∈ set ys. dim_row y = 2"
      and "∀x ∈ set xs. dim_col x = 1" and "∀y ∈ set ys. dim_col y = 1"
  shows "(SWAP_all k t) * ((pr xs k) ⨂ v ⨂ w ⨂ (pr ys t)) = ((pr xs k) ⨂ w ⨂ v ⨂ (pr ys t))"
proof-
  have "(SWAP_all k t) * ((pr xs k) ⨂ v ⨂ w ⨂ (pr ys t)) = ((Id k) ⨂ SWAP ⨂ (Id t)) * ((pr xs k) ⨂ v ⨂ w ⨂ (pr ys t))"
    using SWAP_all_def assms by simp
  then have "(SWAP_all k t) * ((pr xs k) ⨂ v ⨂ w ⨂ (pr ys t)) = ((Id k) ⨂ (SWAP ⨂ (Id t))) * ((pr xs k) ⨂ (v ⨂ w ⨂ (pr ys t)))"
    using tensor_mat_is_assoc by simp
  moreover have f0: "dim_col (Id k) = dim_row (pr xs k)"  
    using Id_def pow_tensor_list_dim_row assms by (metis index_one_mat(3))
  moreover have "dim_col (SWAP ⨂ (Id t)) = dim_row (v ⨂ w ⨂ (pr ys t))" 
    using Id_def assms pow_tensor_list_dim_row[of ys t 2] by simp
  moreover have "dim_col (Id k) > 0" and "dim_col (SWAP ⨂ (Id t)) > 0" and
                "dim_col (pr xs k) > 0" and "dim_col (v ⨂ w ⨂ (pr ys t)) > 0" 
    using Id_def assms by auto
  ultimately have "(SWAP_all k t) * ((pr xs k) ⨂ v ⨂ w ⨂ (pr ys t)) =
              ((Id k)*(pr xs k)) ⨂ ((SWAP ⨂ (Id t)) * (v ⨂ w ⨂ (pr ys t)))"
    using mult_distr_tensor by simp
  then have "(SWAP_all k t) * ((pr xs k) ⨂ v ⨂ w ⨂ (pr ys t)) = ((pr xs k)) ⨂ ((SWAP ⨂ (Id t)) * (v ⨂ w ⨂ (pr ys t)))" 
    using Id_def f0 by simp
  moreover have "dim_col SWAP = dim_row (v ⨂ w)" using assms by simp
  moreover have f1: "dim_col (Id t) = dim_row (pr ys t)" using Id_def pow_tensor_list_dim_row assms by (metis index_one_mat(3))
  moreover have "dim_col SWAP > 0" and "dim_col (v ⨂ w) > 0" and "dim_col (Id t) > 0" and "dim_col (pr ys t) > 0" 
    apply (auto simp: assms Id_def pow_tensor_list_dim_col[of ys t]). 
  ultimately have "(SWAP_all k t) * ((pr xs k) ⨂ v ⨂ w ⨂ (pr ys t)) = (pr xs k) ⨂ ((SWAP * (v ⨂ w)) ⨂ ((Id t) * (pr ys t)))" 
    using mult_distr_tensor by simp
  then have "(SWAP_all k t) * ((pr xs k) ⨂ v ⨂ w ⨂ (pr ys t)) = (pr xs k) ⨂ ((SWAP * (v ⨂ w)) ⨂ (pr ys t))" 
    using Id_def f1 by simp
  then have "(SWAP_all k t) * ((pr xs k) ⨂ v ⨂ w ⨂ (pr ys t)) = (pr xs k) ⨂ ((w ⨂ v) ⨂ (pr ys t))" 
    using assms app_SWAP by simp
  then show "(SWAP_all k t) * ((pr xs k) ⨂ v ⨂ w ⨂ (pr ys t)) = ((pr xs k) ⨂ w ⨂ v ⨂ (pr ys t))"
    using tensor_mat_is_assoc by simp
qed

(*Could go into generic mult function would be more confusing to understand though*)
(*Should this be named FSWAP?*)

(*Takes a the position k of a qubit that should be swapped to the front and the number of remaining qubits t. 
If the qubit is already at the front the Id matrix is applied. E.g. |111011⟩ and k=4 and t=2 gives |011111⟩ *)
fun SWAP_front:: "nat ⇒ nat ⇒ complex Matrix.mat" ("fSWAP _ _" 75)  where
  "(fSWAP (Suc 0) t) = Id (t+1)" 
| "(fSWAP (Suc k) t) = (fSWAP k (t+1)) * (SWAP_all (k-1) t)"
 
lemma SWAP_front_dim [simp]:
  assumes "k≥1"
  shows "dim_row (fSWAP k t) = 2^(k+t)" and "dim_col (fSWAP k t) = 2^(k+t)" 
proof-
  have "∀t. dim_row (fSWAP k t) = 2^(k+t) ∧ dim_col (fSWAP k t) = 2^(k+t)" 
  proof(rule Nat.nat_induct_at_least[of 1 k])
    show "k≥1" using assms by simp
  next
    show "∀t. dim_row (fSWAP 1 t) = 2^(1+t) ∧ dim_col (fSWAP 1 t) = 2^(1+t)" using Id_def by simp
  next
    fix k::nat
    assume a0: "k≥1" 
    and IH: "∀t. dim_row (fSWAP k t) = 2^(k+t) ∧ dim_col (fSWAP k t) = 2^(k+t)" 
    show "∀t. dim_row (fSWAP (Suc k) t) = 2^((Suc k)+t) ∧ dim_col (fSWAP (Suc k) t) = 2^((Suc k)+t)" 
    proof
      fix t 
      have f0: "fSWAP (Suc k) t = (fSWAP k (t+1)) * (SWAP_all (k-1) t)" 
        using SWAP_front.simps a0 by (metis Suc_diff_le diff_Suc_1)
      have "dim_row (fSWAP (Suc k) t) = 2^((Suc k)+t)" 
      proof-
        have "dim_row (fSWAP (Suc k) t) = dim_row ((fSWAP k (t+1)) * (SWAP_all (k-1) t))" using f0 by simp
        also have "... = dim_row (fSWAP k (t+1))" by simp
        also have "... = 2^(k+t+1)" using IH by simp
        finally show ?thesis by simp
      qed
      moreover have "dim_col (fSWAP (Suc k) t) = 2^((Suc k)+t)" 
      proof-
        have "dim_col (fSWAP (Suc k) t) = dim_col ((fSWAP k (t+1)) * (SWAP_all (k-1) t))" using f0 by simp
        also have "... = dim_col (SWAP_all (k-1) t)" by simp 
        also have "... = 2^(k-1+2+t)" by simp 
        finally show ?thesis using a0 by simp
      qed
      ultimately show "dim_row (fSWAP (Suc k) t) = 2^((Suc k)+t) ∧ dim_col (fSWAP (Suc k) t) = 2^((Suc k)+t)" by simp
    qed
  qed
  then show "dim_row (fSWAP k t) = 2^(k+t)" and "dim_col (fSWAP k t) = 2^(k+t)" by auto
qed

lemma SWAP_front_dim2 [simp]: (*TODO better name *)
  assumes "m ≥ k" and "k - c ≥ 1"
  shows "dim_row (fSWAP (k-c) (m-k)) = 2^(m-c)"
    and "dim_col (fSWAP (k-c) (m-k)) = 2^(m-c)"
  using SWAP_front_dim assms by auto

lemma Id_tensor_SWAP_front_dim [simp]:
  assumes "m ≥ k" and "k - c ≥ 1"
  shows "dim_row (Id 1 ⨂ (fSWAP (k-c) (m-k))) = 2^(m-c+1)"
    and "dim_col (Id 1 ⨂ (fSWAP (k-c) (m-k))) = 2^(m-c+1)"
  using SWAP_front_dim2 assms Id_def by auto

lemma SWAP_front_unitary: 
  assumes "k ≥ 1"
  shows "∀t. unitary (fSWAP k t)" 
proof-
  have "∀t.(fSWAP k t)⇧† * (fSWAP k t) = 1⇩m (dim_col (fSWAP k t))"
  proof(rule Nat.nat_induct_at_least[of 1 k])
    show "k≥1" using assms by simp
  next
    show "∀t. (fSWAP 1 t)⇧† * (fSWAP 1 t) = 1⇩m (dim_col (fSWAP 1 t))" by (simp add: Quantum.Id_def) 
  next
    fix k::nat
    assume a0: "k ≥ 1"
    and IH: "∀t. (fSWAP k t)⇧† * (fSWAP k t) = 1⇩m (dim_col (fSWAP k t))"
    show "∀t. (fSWAP (Suc k) t)⇧† * (fSWAP (Suc k) t) = 1⇩m (dim_col (fSWAP (Suc k) t))"
    proof
      fix t
      have "(fSWAP (Suc k) t)⇧† * (fSWAP (Suc k) t) = ((fSWAP k (t+1)) * (SWAP_all (k-1) t))⇧† * ((fSWAP k (t+1)) * (SWAP_all (k-1) t))"
        using Suc_le_D assms a0 by fastforce
      then have "(fSWAP (Suc k) t)⇧† * (fSWAP (Suc k) t) = ((SWAP_all (k-1) t)⇧† * ((fSWAP k (t+1))⇧†)) * ((fSWAP k (t+1)) * (SWAP_all (k-1) t))"
        using a0 dagger_of_prod[of "fSWAP k (t+1)" "(SWAP_all (k-1) t)"] by simp
      moreover have "(SWAP_all (k-1) t)⇧† ∈ carrier_mat (2^(k+t+1)) (2^(k+t+1))" using a0 by auto
      moreover have "(fSWAP k (t+1))⇧† ∈ carrier_mat (2^(k+t+1)) (2^(k+t+1))" using a0 by auto
      moreover have "((fSWAP k (t+1)) * (SWAP_all (k-1) t)) ∈ carrier_mat (2^(k+t+1)) (2^(k+t+1))" using a0 by auto
      ultimately have "(fSWAP (Suc k) t)⇧† * (fSWAP (Suc k) t) 
                     = (SWAP_all (k-1) t)⇧† * (((fSWAP k (t+1))⇧†) * ((fSWAP k (t+1)) * (SWAP_all (k-1) t)))" 
        by simp
      moreover have "(fSWAP k (t+1))⇧† ∈ carrier_mat (2^(k+t+1)) (2^(k+t+1))" using a0 by auto
      moreover have "(fSWAP k (t+1)) ∈ carrier_mat (2^(k+t+1)) (2^(k+t+1))" using a0 by auto
      moreover have "(SWAP_all (k-1) t) ∈ carrier_mat (2^(k+t+1)) (2^(k+t+1))" using a0 by auto
      ultimately have "(fSWAP (Suc k) t)⇧† * (fSWAP (Suc k) t) 
        = (SWAP_all (k-1) t)⇧† * ((((fSWAP k (t+1))⇧†) * (fSWAP k (t+1))) * (SWAP_all (k-1) t))" 
        by simp
      then have "(fSWAP (Suc k) t)⇧† * (fSWAP (Suc k) t) = (SWAP_all (k-1) t)⇧† * (1⇩m (dim_col (fSWAP k (t+1))) * (SWAP_all (k-1) t))"
        using IH by simp
      then have "(fSWAP (Suc k) t)⇧† * (fSWAP (Suc k) t) = (SWAP_all (k-1) t)⇧† * (SWAP_all (k-1) t)" using a0 by simp
      then show "(fSWAP (Suc k) t)⇧† * (fSWAP (Suc k) t) = 1⇩m (dim_col (fSWAP (Suc k) t))" 
        by (metis SWAP_all_is_gate gate.unitary index_mult_mat(3) unitary_def)
    qed
  qed
  then show ?thesis using SWAP_front_dim assms cnj_transpose_is_dagger 
    by (metis carrier_matI dim_col_of_dagger dim_row_of_dagger mat_mult_left_right_inverse unitary_def)
qed

lemma SWAP_front_gate: 
  assumes "k≥1"
  shows "gate (k+t) (fSWAP k t)" 
proof
  show "dim_row (fSWAP k t) = 2^(k+t)" using assms by simp
next
  show "square_mat (fSWAP k t)" using assms by simp
next
  show "unitary (fSWAP k t)" using SWAP_front_unitary assms by simp
qed

lemma SWAP_front_dagger_dim [simp]:
  assumes "k≥1"
  shows "dim_row (fSWAP k t)⇧† = 2^(k+t)"
  and "dim_col (fSWAP k t)⇧† = 2^(k+t)" 
  using assms by auto

lemma Id_tensor_SWAP_front_herm_cnj_dim [simp]:
  assumes "m≥k" and "k-c ≥1"
  shows "dim_row (Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) = 2^(m-c+1)"
    and "dim_col (Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) = 2^(m-c+1)"
  using assms Id_def by auto

lemma aux_app_SWAP_front:
  assumes "k ≥ c + 1" and "k ≥ 1" and "c ≤ m" 
      and "dim_row v = 2" and "dim_col v = 1" 
    shows "∀xs ys. (∀x ∈ set xs. dim_row x = 2) ∧ (∀y ∈ set ys. dim_row y = 2) ∧
           (∀x ∈ set xs. dim_col x = 1) ∧ (∀y ∈ set ys. dim_col y = 1) ∧
           length xs = k - c - 1 ∧ length ys = m - k ∧ m ≥ k ⟶ 
           (fSWAP (k-c) (m-k)) * ((pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) = v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))" 
proof(rule Nat.nat_induct_at_least[of "c+1" k])
  show "k ≥ c + 1" using assms by simp
next
  show "∀xs ys. (∀x ∈ set xs. dim_row x = 2) ∧ (∀y ∈ set ys. dim_row y = 2) ∧
                (∀x ∈ set xs. dim_col x = 1) ∧ (∀y ∈ set ys. dim_col y = 1) ∧
                length xs = ((c + 1) - c - 1) ∧ length ys = m - (c + 1) ∧ m ≥ (c + 1) ⟶ 
        (fSWAP ((c+1)-c) (m-(c+1))) * ((pr xs ((c+1)-c-1)) ⨂ v ⨂ (pr ys (m-(c+1)))) 
       = v ⨂ (pr xs ((c+1)-c-1)) ⨂ (pr ys (m-(c+1)))" 
  proof(rule allI, rule allI, rule impI)
    fix xs ys::"complex Matrix.mat list"
    assume a0: "(∀x ∈ set xs. dim_row x = 2) ∧ (∀y ∈ set ys. dim_row y = 2) ∧
                (∀x ∈ set xs. dim_col x = 1) ∧ (∀y ∈ set ys. dim_col y = 1) ∧
                length xs = ((c + 1) - c - 1) ∧ length ys = m - (c + 1) ∧ m ≥ (c + 1)"
    then have "(fSWAP 1 (m-c-1)) * ((pr xs 0) ⨂ v ⨂ (pr ys (m-(c+1)))) = Id (m-c-1+1) * ((pr xs 0) ⨂ v ⨂ (pr ys (m-(c+1))))"
      using assms by simp
    then have "(fSWAP 1 (m-c-1)) * ((pr xs 0) ⨂ v ⨂ (pr ys (m-(c+1)))) = Id (m-c-1+1) * (v ⨂ (pr ys (m-(c+1))))"
      using a0 Id_left_tensor by simp
    moreover have "dim_row (v ⨂ (pr ys (m-(c+1)))) = 2 * 2^(m-(c+1))" 
      using assms pow_tensor_list_dim_row a0 by simp
    moreover have "2 * 2^(m-(c+1)) = 2^(m-c-1+1)" by simp
    ultimately have "(fSWAP 1 (m-c-1)) * ((pr xs 0) ⨂ v ⨂ (pr ys (m-(c+1)))) = (v ⨂ (pr ys (m-(c+1))))"
      using assms Id_mult_left[of "(v ⨂ (pr ys (m-(c+1))))" "m-c-1+1"] by metis
    then show "(fSWAP ((c+1)-c) (m-(c+1))) * ((pr xs ((c+1)-c-1)) ⨂ v ⨂ (pr ys (m-(c+1)))) 
              = v ⨂ (pr xs ((c+1)-c-1)) ⨂ (pr ys (m-(c+1)))" 
      using a0 by simp
  qed
next
  fix k::nat
  assume a0: "k ≥ c + 1"
  assume IH: "∀xs ys. (∀x ∈ set xs. dim_row x = 2) ∧ (∀y ∈ set ys. dim_row y = 2) ∧
           (∀x ∈ set xs. dim_col x = 1) ∧ (∀y ∈ set ys. dim_col y = 1) ∧
           length xs = (k - c - 1) ∧ length ys = m - k ∧ m ≥ k  ⟶ 
           (fSWAP (k-c) (m-k)) * ((pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) 
          = v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))" 
  show "∀xs ys. (∀x ∈ set xs. dim_row x = 2) ∧ (∀y ∈ set ys. dim_row y = 2) ∧
           (∀x ∈ set xs. dim_col x = 1) ∧ (∀y ∈ set ys. dim_col y = 1) ∧
           length xs = ((Suc k) - c - 1) ∧ length ys = m - (Suc k) ∧ m ≥ (Suc k)  ⟶ 
           (fSWAP ((Suc k)-c) (m-(Suc k))) * ((pr xs ((Suc k)-c-1)) ⨂ v ⨂ (pr ys (m-(Suc k)))) 
          = v ⨂ (pr xs ((Suc k)-c-1)) ⨂ (pr ys (m-(Suc k)))" 
  proof(rule allI, rule allI, rule impI)
    fix xs ys::"complex Matrix.mat list"
    assume a1: "(∀x ∈ set xs. dim_row x = 2) ∧ (∀y ∈ set ys. dim_row y = 2) ∧
           (∀x ∈ set xs. dim_col x = 1) ∧ (∀y ∈ set ys. dim_col y = 1) ∧
           length xs = ((Suc k) - c - 1) ∧ length ys = m - (Suc k) ∧ m ≥ (Suc k)" 
    have "(fSWAP ((Suc k)-c) (m-(Suc k))) * ((pr xs ((Suc k)-c-1)) ⨂ v ⨂ (pr ys (m-(Suc k)))) 
        = (fSWAP ((Suc k)-c-1) (m-(Suc k)+1)) * (SWAP_all (((Suc k)-c-1)-1) (m-(Suc k)))  * ((pr xs ((Suc k)-c-1)) ⨂ v ⨂ (pr ys (m-(Suc k)))) "
      using a0 SWAP_front.simps le_Suc_ex by fastforce
    then have "(fSWAP ((Suc k)-c) (m-(Suc k))) * ((pr xs ((Suc k)-c-1)) ⨂ v ⨂ (pr ys (m-(Suc k)))) 
             = (fSWAP (k-c) (m-k)) * (SWAP_all (k-c-1) (m-(Suc k))) * ((pr xs (k-c)) ⨂ v ⨂ (pr ys (m-(Suc k))))"
      using assms a1 by simp
    moreover have "(fSWAP (k-c) (m-k)) * (SWAP_all (k-c-1) (m-(Suc k))) * ((pr xs (k-c)) ⨂ v ⨂ (pr ys (m-(Suc k))))
                 = (fSWAP (k-c) (m-k)) * ((SWAP_all (k-c-1) (m-(Suc k))) * ((pr xs (k-c)) ⨂ v ⨂ (pr ys (m-(Suc k)))))"
    proof-
      have "(fSWAP (k-c) (m-k)) ∈ carrier_mat (2^(m-c)) (2^(m-c))"
        using SWAP_front_dim2 assms a0 a1 
        by (metis Nat.le_diff_conv2 add.right_neutral add_Suc_right add_leD2 carrier_matI plus_1_eq_Suc)
      moreover have "(SWAP_all (k-c-1) (m-(Suc k))) ∈ carrier_mat (2^(m-c)) (2^(m-c))"
        using SWAP_all_dim aux_calculation(5) a0 a1 assms by (metis carrier_matI)
      moreover have "((pr xs (k-c)) ⨂ v ⨂ (pr ys (m-(Suc k)))) ∈ carrier_mat (2^(m-c)) 1" 
      proof
        have "m ≥ Suc k" using a1 by simp
        moreover have "dim_row (pr xs (k-c)) = 2^(k-c)" using a0 a1 pow_tensor_list_dim_row by simp
        moreover have "dim_row (pr ys (m-(Suc k))) = 2^(m-(Suc k))" using a0 a1 pow_tensor_list_dim_row by simp
        ultimately show "dim_row ((pr xs (k-c)) ⨂ v ⨂ (pr ys (m-(Suc k)))) = 2^(m-c)" 
          using assms a0 a1 by (metis add_leD1 aux_calculation(8) dim_row_tensor_mat)
      next
        have "m ≥ Suc k" using a1 by simp
        moreover have "dim_col (pr xs (k-c)) = 1" using a0 a1 by simp
        moreover have "dim_col (pr ys (m-(Suc k))) = 1" using a0 a1 by simp
        ultimately show "dim_col ((pr xs (k-c)) ⨂ v ⨂ (pr ys (m-(Suc k)))) = 1" 
          using assms a0 a1 by simp
      qed
      ultimately show ?thesis by simp
    qed
    moreover have f1: "(pr xs (k-c)) = (pr (butlast xs) ((k-c)-1)) ⨂ (last xs)" 
    proof-
      have "length (butlast xs) = (k - c - 1)" using a1 by simp
      moreover have "(butlast xs)@[last xs] = xs" using a0 a1 calculation
        by (metis append_butlast_last_id butlast.simps(1) diff_diff_left le_imp_less_Suc less_imp_le_nat n_not_Suc_n 
            ordered_cancel_comm_monoid_diff_class.diff_add)
      moreover have "k - c - 1 + 1 = k - c" using a0 by simp
      ultimately show "(pr xs (k-c)) = (pr (butlast xs) ((k-c)-1)) ⨂ (last xs)" 
        using assms pow_tensor_decomp_left by simp
    qed
    moreover have "(SWAP_all (k-c-1) (m-(Suc k))) * ((pr (butlast xs) (k-c-1)) ⨂ (last xs) ⨂ v ⨂ (pr ys (m-(Suc k))))
                 = ((pr (butlast xs) (k-c-1)) ⨂ v ⨂ (last xs) ⨂ (pr ys (m-(Suc k))))" 
    proof-
      have "Suc k - c - 1 = k - c" by simp
      then have "dim_row (last xs) = 2 ∧ dim_col (last xs) = 1" 
        using a0 a1 by (metis One_nat_def Suc_diff_le butlast.simps(1) diff_diff_left last_in_set length_butlast list.size(3) zero_neq_one)
      moreover have "length (butlast xs) = k-c-1" using a1 by simp
      moreover have  "∀x ∈ set (butlast xs). dim_row x = 2" and "∀x ∈ set (butlast xs). dim_col x = 1" 
       by (auto simp: a1 in_set_butlastD)
      ultimately show ?thesis using app_SWAP_all assms a1 by simp 
    qed
    ultimately have "(fSWAP ((Suc k)-c) (m-(Suc k))) * ((pr xs ((Suc k)-c-1)) ⨂ v ⨂ (pr ys (m-(Suc k)))) 
                   = (fSWAP (k-c) (m-k)) * ((pr (butlast xs) (k-c-1)) ⨂ v ⨂ ((last xs) ⨂ (pr ys (m-(Suc k)))))" 
      using tensor_mat_is_assoc by simp
    then have "(fSWAP ((Suc k)-c) (m-(Suc k))) * ((pr xs ((Suc k)-c-1)) ⨂ v ⨂ (pr ys (m-(Suc k)))) 
             = (fSWAP (k-c) (m-k)) * ((pr (butlast xs) (k-c-1)) ⨂ v ⨂ (pr ((last xs)#ys) (m-k)))" 
      using pow_tensor_decomp_right[of ys "m-(Suc k)" "last xs"] a1 by simp
    moreover have "(fSWAP (k-c) (m-k)) * ((pr (butlast xs) (k-c-1)) ⨂ v ⨂ (pr ((last xs)#ys) (m-k)))
                 = v ⨂ (pr (butlast xs) (k-c-1)) ⨂ (pr ((last xs)#ys) (m-k))"
    proof-
      have "(∀x ∈ set (butlast xs). dim_row x = 2) ∧ (∀x ∈ set (butlast xs). dim_col x = 1)" 
        using a1 by (simp add: in_set_butlastD)
      moreover have "dim_row (last xs) = 2 ∧ dim_col (last xs) = 1" 
        by (metis Suc_diff_le Zero_not_Suc a0 a1 diff_diff_left last_in_set list.size(3))
      moreover have "(∀y ∈ set ((last xs)#ys). dim_row y = 2) ∧ (∀y ∈ set ((last xs)#ys). dim_col y = 1)"
        using a1 calculation by simp
      moreover have "length (butlast xs) = (k-c-1) ∧ length ((last xs)#ys) = m-k ∧ m>k" 
        using a1 by simp
      ultimately show "(fSWAP (k-c) (m-k)) * ((pr (butlast xs) (k-c-1)) ⨂ v ⨂ (pr ((last xs)#ys) (m-k))) 
          = v ⨂ (pr (butlast xs) (k-c-1)) ⨂ (pr ((last xs)#ys) (m-k))"
        using IH by simp
    qed
    ultimately have "(fSWAP ((Suc k)-c) (m-(Suc k))) * ((pr xs ((Suc k)-c-1)) ⨂ v ⨂ (pr ys (m-(Suc k)))) 
                   = v ⨂ (pr (butlast xs) (k-c-1)) ⨂ (pr ((last xs)#ys) (m-k))" by simp
    then have "(fSWAP ((Suc k)-c) (m-(Suc k))) * ((pr xs ((Suc k)-c-1)) ⨂ v ⨂ (pr ys (m-(Suc k)))) 
             = (v ⨂ (pr (butlast xs) (k-c-1)) ⨂ ((last xs) ⨂ (pr ys (m-k-1))))" 
      using pow_tensor_decomp_right[of ys "m-k-1" "last xs"] a1 by simp
    then show "(fSWAP ((Suc k)-c) (m-(Suc k))) * ((pr xs ((Suc k)-c-1)) ⨂ v ⨂ (pr ys (m-(Suc k)))) 
          = v ⨂ (pr xs ((Suc k)-c-1)) ⨂ (pr ys (m-(Suc k)))"
      using f1 tensor_mat_is_assoc by simp
  qed
qed

lemma app_SWAP_front:
  assumes "k ≥ c + 1" and "k ≥ 1" and "c ≤ m" and "m ≥ k" 
      and "dim_row v = 2" and "dim_col v = 1" 
      and "(∀x ∈ set xs. dim_row x = 2)" and "(∀y ∈ set ys. dim_row y = 2)"
      and "(∀x ∈ set xs. dim_col x = 1)" and "(∀y ∈ set ys. dim_col y = 1)" 
      and "length xs = k - c - 1" and "length ys = m - k"
    shows "(fSWAP (k-c) (m-k)) * ((pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) 
          = v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))" 
  using aux_app_SWAP_front assms by auto

lemma app_Id_tensor_fSWAP:
  assumes "k ≥ 1" and "m ≥ k" and "1 ≤ k - c"and "m ≥ c" 
      and "dim_row v = 2" and "dim_col v = 1" 
      and "(∀x ∈ set xs. dim_row x = 2)" and "(∀y ∈ set ys. dim_row y = 2)"
      and "(∀x ∈ set xs. dim_col x = 1)" and "(∀y ∈ set ys. dim_col y = 1)" 
      and "length xs = k - c - 1" and "length ys = m - k"
  shows "(Id 1 ⨂ (fSWAP (k-c) (m-k))) * ((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k)))
       = (psq c (k-1) m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))"
proof-
  have "dim_col (Id 1) = dim_row (psq c (k-1) m j)" by (simp add: Id_def phase_shifted_qubit_def)
  moreover have "dim_col (fSWAP (k-c) (m-k)) = dim_row ((pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k)))" 
    using assms pow_tensor_list_dim_row[of xs "(k-c-1)" "2"] pow_tensor_list_dim_row[of ys "m-k" "2"] SWAP_front_dim
    by (metis (no_types, lifting) One_nat_def dim_row_tensor_mat le_simps(3) power_add power_minus_mult)
  moreover have "dim_col (Id 1) > 0" and "dim_col (psq c (k-1) m j) > 0" and "dim_col (fSWAP (k-c) (m-k)) > 0"
            and "dim_col ((pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) > 0" 
       using SWAP_front_dim assms Id_def assms phase_shifted_qubit_def by auto
  ultimately have "((Id 1) ⨂ (fSWAP (k-c) (m-k))) * ((psq c (k-1) m j) ⨂ ((pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))))
                 = ((Id 1) * (psq c (k-1) m j)) ⨂ ((fSWAP (k-c) (m-k)) * ((pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))))" 
    using mult_distr_tensor by auto
  then have "((Id 1) ⨂ (fSWAP (k-c) (m-k))) * ((psq c (k-1) m j) ⨂ ((pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))))
           = ((psq c (k-1) m j) ⨂ (fSWAP (k-c) (m-k)) * ((pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))))" 
    using Id_def phase_shifted_qubit_def by simp
  then show "(Id 1 ⨂ (fSWAP (k-c) (m-k))) * ((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k)))
           = (psq c (k-1) m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))" 
    using app_SWAP_front[of c k m v xs ys] assms tensor_mat_is_assoc by auto
qed

lemma app_CR_tensor_Id:
  assumes "k ≥ 2" and "m ≥ 1" and "k ≤ m" and "c ≥ 1" and "c ≤ k - 1" and "c ≤ m" 
      and "dim_row v = 2" and "dim_col v = 1" 
      and "v = |zero⟩ ∨ v = |one⟩"
      and "v = |zero⟩ ⟶ ((bin_rep m j)!(k-1)) = 0"
      and "v = |one⟩ ⟶  ((bin_rep m j)!(k-1)) = 1" 
      and "(∀x ∈ set xs. dim_row x = 2)" and "(∀y ∈ set ys. dim_row y = 2)"
      and "(∀x ∈ set xs. dim_col x = 1)" and "(∀y ∈ set ys. dim_col y = 1)" 
      and "length xs = k - c - 1" and "length ys = m - k"
   shows "(CR (k-c+1) ⨂ Id (m-c-1)) * ((psq c (k-1) m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))) 
        = (psq c k m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))" 
proof-
  have "(CR (k-c+1) ⨂ Id (m-c-1)) * ((psq c (k-1) m j) ⨂ v ⨂ ((pr xs (k-c-1)) ⨂ (pr ys (m-k)))) = 
        (CR (k-c+1) * ((psq c (k-1) m j) ⨂ v)) ⨂ (Id (m-c-1) * ((pr xs (k-c-1)) ⨂ (pr ys (m-k))))" 
  proof-
    have "dim_col (CR (k-c+1)) = dim_row ((psq c (k-1) m j) ⨂ v)"
      using controlled_phase_shift_def phase_shifted_qubit_def assms by simp
    moreover have "dim_row ((pr xs (k-c-1)) ⨂ (pr ys (m-k))) = dim_col (Id (m-c-1))"
      using assms pow_tensor_list_dim_row[of xs "k-c-1" "2"] pow_tensor_list_dim_row[of ys "m-k" "2"] dim_row_tensor_mat 
      by (smt Nat.add_diff_assoc2 Nat.le_diff_conv2 Quantum.Id_def add_leD1 diff_diff_left index_one_mat(3) one_add_one 
          ordered_cancel_comm_monoid_diff_class.add_diff_inverse power_add)
    moreover have "dim_col (CR (k-c+1)) > 0" and "dim_col ((psq c (k-1) m j) ⨂ v) > 0" 
              and "dim_col (Id (m-c-1)) > 0" and "dim_col ((pr xs (k-c-1)) ⨂ (pr ys (m-k))) > 0" 
      using controlled_phase_shift_def phase_shifted_qubit_def Id_def phase_shifted_qubit_def pow_tensor_list_dim_col[of ys "m-k"] 
            pow_tensor_list_dim_col[of xs "k-c-1"] assms by auto
    ultimately show ?thesis 
      using mult_distr_tensor by auto
  qed
  moreover have "dim_row ((pr xs (k-c-1)) ⨂ (pr ys (m-k))) = 2^(m-c-1)" 
    using pow_tensor_list_dim_row[of xs "k-c-1"] assms pow_tensor_list_dim_row[of ys "m-k"] 
    by (smt Nat.add_diff_assoc2 Nat.le_diff_conv2 add_leD1 diff_diff_left dim_row_tensor_mat less_imp_le_nat one_add_one 
        ordered_cancel_comm_monoid_diff_class.add_diff_inverse power_add)
  ultimately have "(CR (k-c+1) ⨂ Id (m-c-1)) * ((psq c (k-1) m j) ⨂ v ⨂ ((pr xs (k-c-1)) ⨂ (pr ys (m-k)))) = 
        (CR (k-c+1) * ((psq c (k-1) m j) ⨂ v)) ⨂ ((pr xs (k-c-1)) ⨂ (pr ys (m-k)))" 
    using Id_mult_left by simp
  then have f0: "(CR (k-c+1) ⨂ Id (m-c-1)) * ((psq c (k-1) m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))) =
        (CR (k-c+1) * ((psq c (k-1) m j) ⨂ v)) ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))" 
    using tensor_mat_is_assoc by simp
  show "(CR (k-c+1) ⨂ Id (m-c-1)) * ((psq c (k-1) m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))) 
      = (psq c k m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))" 
  proof(rule disjE)
    show "v = |zero⟩ ∨ v = |one⟩" using assms by simp
  next
    assume "v = |zero⟩" 
    then show "(CR (k-c+1) ⨂ Id (m-c-1)) * ((psq c (k-1) m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))) 
             = (psq c k m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))" 
      using app_CR_on_ket_zero assms f0 by auto
  next
    assume "v = |one⟩" 
    then show "(CR (k-c+1) ⨂ Id (m-c-1)) * ((psq c (k-1) m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))) 
             = (psq c k m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))" 
      using app_CR_on_ket_one assms f0 by auto
  qed
qed

lemma SWAP_front_herm_cnj_dual:
  assumes "k ≥ 1" and "(fSWAP k t) * A = B" 
    and "dim_row A = 2^(k+t)" and "dim_col A = 1"
    and "dim_row B = 2^(k+t)" and "dim_col B = 1"
  shows "(fSWAP k t)⇧† * B = A" 
proof-
  have "(fSWAP k t)⇧† * ((fSWAP k t) * A) = (fSWAP k t)⇧† * B" using assms arg_cong by simp
  then have "((fSWAP k t)⇧† * (fSWAP k t)) * A = (fSWAP k t)⇧† * B" 
    using assoc_mult_mat[of "(fSWAP k t)⇧†" "2^(k+t)" "2^(k+t)" "(fSWAP k t)" "2^(k+t)" A 1] assms 
    by (metis SWAP_front_dagger_dim(1) carrier_matI dim_col_of_dagger dim_row_of_dagger index_mult_mat(2))
  then have "(1⇩m (2^(k+t))) * A = (fSWAP k t)⇧† * B" 
    using assms gate.unitary unitary_def SWAP_front_dagger_dim SWAP_front_gate 
    by (metis dim_row_of_dagger)
  then show "(fSWAP k t)⇧† * B = A" by (simp add: assms(3))
qed

lemma app_SWAP_front_herm_cnj:
  assumes "k - c ≥ 1" and "k ≥ 1" and "c ≤ m"  and "m ≥ k" 
      and "dim_row v = 2" and "dim_col v = 1" 
      and "(∀x ∈ set xs. dim_row x = 2)" and "(∀y ∈ set ys. dim_row y = 2)"
      and "(∀x ∈ set xs. dim_col x = 1)" and "(∀y ∈ set ys. dim_col y = 1)" 
      and "length xs = k - c - 1" and "length ys = m - k"
  shows "((fSWAP (k-c) (m-k))⇧†) * (v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))) 
       = ((pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k)))" 
proof-
  have "(fSWAP (k-c) (m-k)) * ((pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) 
      = v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))" using assms app_SWAP_front by auto
  moreover have "dim_row ((pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) = 2^(k-c+(m-k))" 
    by (metis SWAP_front_dim(1) assms(1) calculation dim_row_tensor_mat index_mult_mat(2) mult.commute)
  moreover have "dim_col ((pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) = 1" 
    by (simp add: assms(6,9-12))
  moreover have "dim_row (v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))) = 2^(k-c+(m-k))" 
    by (metis SWAP_front_dim(1) assms(1) calculation(1) index_mult_mat(2))
  moreover have "dim_col (v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))) = 1" 
    using calculation(3) by simp
  ultimately show "((fSWAP (k-c) (m-k))⇧†) * (v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))) 
                 = ((pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k)))" 
    using SWAP_front_herm_cnj_dual[of "k-c" "m-k" "(pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))"
                                      "v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))"] assms by auto
qed

lemma app_Id_SWAP_front_herm_cnj:
 assumes "k ≥ 2" and "m ≥ 1" and "k ≤ m" and "c ≥ 1" and "c ≤ k - 1" and "c ≤ m"
      and "dim_row v = 2" and "dim_col v = 1" 
      and "(∀x ∈ set xs. dim_row x = 2)" and "(∀y ∈ set ys. dim_row y = 2)"
      and "(∀x ∈ set xs. dim_col x = 1)" and "(∀y ∈ set ys. dim_col y = 1)" 
      and "length xs = k - c - 1" and "length ys = m - k"
  shows "(Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * ((psq c k m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k)))
  = (psq c k m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))"
proof-
  have "dim_col (Id 1) = dim_row (psq c k m j)" by (simp add: Id_def phase_shifted_qubit_def)
  moreover have "dim_col ((fSWAP (k-c) (m-k))⇧†) = dim_row (v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k)))" 
    using SWAP_front_dim2[of k m c] assms pow_tensor_list_dim_row[of xs "(k-c-1)" "2"] pow_tensor_list_dim_row[of ys "m-k" "2"] 
          tensor_mat_is_assoc by auto
  moreover have "dim_col (Id 1) > 0" and "dim_col (psq c k m j) > 0" and "dim_col ((fSWAP (k-c) (m-k))⇧†) > 0"
            and "dim_col (v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))) > 0" 
    using Id_def assms phase_shifted_qubit_def SWAP_front_dim by auto
  ultimately have "(Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * ((psq c k m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k)))
           = ((Id 1) * (psq c k m j)) ⨂ (((fSWAP (k-c) (m-k))⇧†) * (v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))))" 
    using mult_distr_tensor tensor_mat_is_assoc by simp
  then have "(Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * ((psq c k m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k)))
           = (psq c k m j) ⨂ (((fSWAP (k-c) (m-k))⇧†) * (v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))))" 
    using phase_shifted_qubit_def Id_mult_left by simp
  then have "(Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * ((psq c k m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k)))
           = (psq c k m j) ⨂ ( ((pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))))" 
    using app_SWAP_front_herm_cnj assms by auto
  then show "(Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * ((psq c k m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k)))
           = (psq c k m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))"
    using tensor_mat_is_assoc by simp
qed

lemma CR_Id_dim [simp]:
  assumes "m ≥ c + 1"
  shows "dim_row (CR (k-c+1) ⨂ (Id (m-c-1))) = 2^(m-c+1)"
    and "dim_col (CR (k-c+1) ⨂ (Id (m-c-1))) = 2^(m-c+1)"
proof-
  have "2 + (m - c - 1) = m - c + 1" using assms by linarith
  moreover have "(4::nat) = 2^2" by simp
  ultimately have "4 * 2^(m-c-1) = (2::nat)^(m-c+1)" 
    using assms power_add by metis
  then show "dim_row (CR (k-c+1) ⨂ (Id (m-c-1))) = 2^(m-c+1)"
    using Id_def controlled_phase_shift_def by (smt dim_row_mat(1) dim_row_tensor_mat index_one_mat(2))
next
  have "2 + (m - c - 1) = m - c + 1" using assms by linarith
  moreover have "(4::nat) = 2^2" by simp
  ultimately have "4 * 2^(m-c-1) = (2::nat)^(m-c+1)" 
    using assms power_add by metis
  then show "dim_col (CR (k-c+1) ⨂ (Id (m-c-1))) = 2^(m-c+1)"
    by (simp add: Quantum.Id_def controlled_phase_shift_def)
qed

(*Better? ‹The Application of a $CR_k$ t all Qubits›*)
subsection ‹Applying an $R_k$›

(*Find a good abbreviation for this. Why doesn't something like R⇩_ _ _ work? *)

(*k is the index of the qubit that should be added to the binary fraction, i.e. the controll qubit. 
c is the current qubit *)
definition CR_on_all :: "nat ⇒ nat ⇒ nat ⇒ complex Matrix.mat" ("R⇩_ _ _" 75) where
"CR_on_all c k m ≡ (Id (c-1)) ⨂ ((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ Id (m-c-1)) * (Id 1 ⨂ (fSWAP (k-c) (m-k))))"

lemma CR_on_all_dim[simp]:
  assumes "k - c ≥ 1" and "c ≥ 1" and "m ≥ k"
  shows "dim_row (CR_on_all c k m) = 2^m"
    and "dim_col (CR_on_all c k m) = 2^m"
proof-
  have "dim_row (CR_on_all c k m) = dim_row (Id (c-1)) * dim_row ((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)))"
    using CR_on_all_def by simp
  moreover have "2^(c-Suc 0) * (2 * 2^(k+(m-k)-c)) = (2::nat)^m" using assms 
    by (metis (no_types, lifting) One_nat_def Suc_le_eq aux_calculation(1) le_add_diff_inverse 
        semigroup_mult_class.mult.assoc trans_less_add1 zero_less_diff)
  ultimately show "dim_row (CR_on_all c k m) = 2^m"
    using Id_def[of "c-1"] Id_def[of 1] SWAP_front_dagger_dim[of "k-c" "m-k"] assms by simp
next
  have "dim_col (CR_on_all c k m) = dim_col (Id (c-1)) * dim_col (Id 1 ⨂ (fSWAP (k-c) (m-k)))"
    using CR_on_all_def by simp
  moreover have "2^(c-Suc 0) * (2 * 2^(k+(m-k)-c)) = (2::nat)^m" using assms 
    by (metis (no_types, lifting) One_nat_def Suc_le_eq aux_calculation(1) le_add_diff_inverse 
        semigroup_mult_class.mult.assoc trans_less_add1 zero_less_diff)
  ultimately show "dim_col (CR_on_all c k m) = 2^m"
    using Id_def[of "c-1"] Id_def[of 1] SWAP_front_dagger_dim[of "k-c" "m-k"] assms by simp
qed

lemma Id_tensor_SWAP_front_is_gate:
  assumes "m ≥ k" and "k > c"
  shows "gate (m-c+1) (Id 1 ⨂ (fSWAP (k-c) (m-k)))"
proof-
  have "k - c + (m - k) = m - c" using assms by simp
  then have "gate (m-c) (fSWAP (k-c) (m-k))" using SWAP_front_gate[of "k-c" "m-k"] assms by simp
  moreover have "gate 1 (Id 1)" by simp
  moreover have "1+(m-c) = m-c+1" using assms by simp
  ultimately show ?thesis 
    using tensor_gate[of 1 "Id 1" "m-c" "(fSWAP (k-c) (m-k))"] by simp
qed

lemma CR_tensor_Id_is_gate:
  assumes "m > c"
  shows "gate (m-c+1) (CR (k-c+1) ⨂ Id (m-c-1))"
proof-
  have "gate (m-c-1) (Id (m-c-1))" by simp
  moreover have "gate 2 (CR (k-c+1))" using controlled_CR_is_gate by simp
  moreover have "(m-c-1) + 2 = m-c+1" using assms by simp
  ultimately show ?thesis by (metis add.commute tensor_gate)
qed

lemma SWAP_front_cnj_is_gate:
  assumes "m - c ≥ 1" and "k ≤ m" and "1 ≤ k - c" 
  shows "gate (m-c) ((fSWAP (k-c) (m-k))⇧†)"
proof
  show "dim_row ((fSWAP (k-c) (m-k))⇧†) = 2^(m-c)" using SWAP_front_dim2[of k m c] assms by simp
next
  show "square_mat ((fSWAP (k-c) (m-k))⇧†)" using SWAP_front_dim2[of k m c] assms by simp 
next
  show "unitary ((fSWAP (k-c) (m-k))⇧†)"
    using assms SWAP_front_unitary
    by (metis dagger_of_prod dim_col_of_dagger dim_row_of_dagger dagger_of_id_is_id unitary_def)
qed

lemma Id_tensor_SWAP_front_cnj_is_gate:
  assumes "m - c ≥ 1" and "k ≤ m" and "1 ≤ k - c" 
  shows "gate (m-c+1) (Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†))"
  using assms
  by (metis SWAP_front_cnj_is_gate add.commute id_is_gate tensor_gate)

lemma CR_on_all_wth_Id_is_gate:
  assumes "m > c" and "c < k" and "k ≤ m"
  shows "gate (m-c+1) ((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ Id (m-c-1)) * (Id 1 ⨂ (fSWAP (k-c) (m-k))))"
proof-
  have "gate (m-c+1) ((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ Id (m-c-1)))" 
    using prod_of_gate_is_gate CR_tensor_Id_is_gate Id_tensor_SWAP_front_cnj_is_gate assms by simp
  moreover have "gate (m-c+1) (Id 1 ⨂ (fSWAP (k-c) (m-k)))" using Id_tensor_SWAP_front_is_gate assms by simp
  ultimately show "gate (m-c+1) ((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ Id (m-c-1)) * (Id 1 ⨂ (fSWAP (k-c) (m-k))))"
    using prod_of_gate_is_gate by simp
qed

lemma CR_on_all_is_gate:
  assumes "k - c ≥ 1" and "c ≥ 1" and "m ≥ k" and "c < k" 
  shows "gate m (CR_on_all c k m)"
proof
  show "dim_row (CR_on_all c k m) = 2^m" using assms CR_on_all_dim by simp
next
  show "square_mat (CR_on_all c k m)" using assms CR_on_all_dim by simp
next
  show "unitary (CR_on_all c k m)"
  proof-
    have "((CR_on_all c k m)⇧†) * (CR_on_all c k m) = 1⇩m (dim_col (CR_on_all c k m))" 
    proof-
      have "gate (c - 1) (Quantum.Id (c - 1))" using id_is_gate by blast
      moreover have "gate (m-c+1) ((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ Id (m-c-1)) * (Id 1 ⨂ (fSWAP (k-c) (m-k))))" 
        using CR_on_all_wth_Id_is_gate assms by simp
      ultimately have "((CR_on_all c k m)⇧†) * (CR_on_all c k m) 
  = 1⇩m (dim_col (Id (c-1)) * dim_col ((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ Id (m-c-1)) * (Id 1 ⨂ (fSWAP (k-c) (m-k)))))" 
        using CR_on_all_def tensor_gate_unitary1[of "c-1" "Id (c-1)" "m-c+1" 
              "((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ Id (m-c-1)) * (Id 1 ⨂ (fSWAP (k-c) (m-k))))"]
        by simp
      moreover have "(dim_col (Id (c-1)) * dim_col ((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ Id (m-c-1)) * (Id 1 ⨂ (fSWAP (k-c) (m-k))))) = 2^m" 
      proof-
        have "dim_col (Id (c-1)) = 2^(c-1)" using Id_def by simp
        moreover have "dim_col ((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ Id (m-c-1)) * (Id 1 ⨂ (fSWAP (k-c) (m-k)))) = 2^(m-c+1)" 
          using Id_tensor_SWAP_front_dim(2) assms(1,3) by simp
        moreover have "2^(c-1) * 2^(m-c+1) = (2::nat)^m" using assms 
          by (metis CR_on_all_def CR_on_all_dim(2) calculation(1) calculation(2) dim_col_tensor_mat)
        ultimately show ?thesis by metis
      qed
      moreover have "dim_col (CR_on_all c k m) = (2::real)^m" using CR_on_all_dim assms by simp
      ultimately show ?thesis by simp
    qed
    moreover have "((CR_on_all c k m) * ((CR_on_all c k m)⇧†)) = 1⇩m (dim_col (CR_on_all c k m))" 
      using calculation assms
      by (metis CR_on_all_dim(1) CR_on_all_dim(2) carrier_matI dim_col_of_dagger dim_row_of_dagger mat_mult_left_right_inverse)
    ultimately show ?thesis by (metis dim_col_of_dagger index_mult_mat(3) unitary_def)
  qed
qed

lemma app_CR_on_all_wo_Id:
  assumes "k ≥ 2" and "m ≥ 1" and "k ≤ m" and "c ≥ 1" and "c ≤ k - 1" and "c < m" 
      and "dim_row v = 2" and "dim_col v = 1" 
      and "v = |zero⟩ ∨ v = |one⟩"
      and "v = |zero⟩ ⟶ ((bin_rep m j)!(k-1)) = 0"
      and "v = |one⟩ ⟶  ((bin_rep m j)!(k-1)) = 1" 
      and "(∀x ∈ set xs. dim_row x = 2)" and "(∀y ∈ set ys. dim_row y = 2)"
      and "(∀x ∈ set xs. dim_col x = 1)" and "(∀y ∈ set ys. dim_col y = 1)" 
      and "length xs = (k-c-1)" and "length ys = m-k"
  shows "((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ (Id (m-c-1))) * (Id 1 ⨂ (fSWAP (k-c) (m-k))))
       * ((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) 
       = (psq c k m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))"
proof-
  have f0: "1 ≤ k - c ∧ 1 ≤ k" using assms 
    by (metis Nat.diff_diff_right diff_add_inverse diff_le_self le_diff_iff' le_trans)
  have "((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ (Id (m-c-1))) * (Id 1 ⨂ (fSWAP (k-c) (m-k))))
        * ((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) 
        = (Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ (Id (m-c-1))) * ((Id 1 ⨂ (fSWAP (k-c) (m-k)))
        * ((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))))" 
  proof-
    have "k ≤ m ∧ 1 ≤ k - c ∧ c + 1 ≤ m" using assms(3) f0 by linarith
    then have "(Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ Id (m-c-1)) ∈ carrier_mat (2^(m-c+1)) (2^(m-c+1))" 
      using Id_tensor_SWAP_front_herm_cnj_dim[of k m c] CR_Id_dim[of c m k] assms f0 
      by (metis carrier_matI index_mult_mat(2) index_mult_mat(3))
    moreover have "(Id 1 ⨂ (fSWAP (k-c) (m-k))) ∈ carrier_mat (2^(m-c+1)) (2^(m-c+1))"
      using Id_tensor_SWAP_front_dim[of k m c] assms using f0 by blast       
    moreover have "((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) ∈ carrier_mat (2^(m-c+1)) 1" 
    proof- 
      have "dim_row (pr xs (k-c-1)) = 2^(k-c-1)"  
        using pow_tensor_list_dim_row[of xs "(k-c-1)" 2] assms(12,16) by blast
      moreover have "dim_row (pr ys (m-k)) = 2^(m-k)" using pow_tensor_list_dim_row[of ys "m-k" 2] assms(13,17) by blast
      moreover have "2 * (2^(m-k) * 2^(k-Suc c)) = (2::nat)^(m-c)" 
        using assms f0 
        by (metis Nat.add_diff_assoc2 add.commute diff_diff_left le_SucI ordered_cancel_comm_monoid_diff_class.add_diff_inverse 
            plus_1_eq_Suc power_add power_commutes semiring_normalization_rules(19) semiring_normalization_rules(28))
      ultimately have "dim_row ((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) = 2^(m-c+1)" 
        using assms phase_shifted_qubit_def aux_calculation(6)[of k c m] by auto
      moreover have "dim_col ((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) = 1" 
        using pow_tensor_list_dim_col[of xs "(k-c-1)"] pow_tensor_list_dim_col[of ys "m-k"]
          phase_shifted_qubit_def assms by auto
      ultimately show ?thesis by blast
    qed
    ultimately show ?thesis 
      using assoc_mult_mat[of "(Id 1 ⨂ ((fSWAP k (m-k))⇧†)) * (CR k ⨂ (Id (m-c)))" "2^(m+1)" "2^(m+1)"
            "(Id 1 ⨂ (fSWAP k (m-k)))" "2^(m+1)" "((psq c k m j) ⨂ (pr xs (k-1)) ⨂ v ⨂ (pr ys (m-k))) " "1"]
          assms by auto
  qed
  then have "((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ (Id (m-c-1))) * (Id 1 ⨂ (fSWAP (k-c) (m-k))))
        * ((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) 
     = (Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ (Id (m-c-1))) * ((psq c (k-1) m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))) "
    using app_Id_tensor_fSWAP[of k m c v xs ys] assms tensor_mat_is_assoc by auto
  moreover have "(Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ (Id (m-c-1))) * ((psq c (k-1) m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k)))
               = (Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * ((CR (k-c+1) ⨂ (Id (m-c-1))) * ((psq c (k-1) m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))))"
  proof-
    have "(Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) ∈ carrier_mat (2^(m-c+1)) (2^(m-c+1))" 
      using Id_tensor_SWAP_front_herm_cnj_dim assms f0 by auto
    moreover have "(CR (k-c+1) ⨂ (Id (m-c-1))) ∈ carrier_mat (2^(m-c+1)) (2^(m-c+1))" 
      using CR_Id_dim assms by auto
    moreover have "((psq c (k-1) m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))) ∈ carrier_mat (2^(m-c+1)) 1"
    proof-
      have "dim_row ((psq c (k-1) m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))) = (2^(m-c+1))"
        using assms phase_shifted_qubit_def pow_tensor_list_dim_row[of xs "k-c-1" 2] pow_tensor_list_dim_row[of ys "m-k" 2] f0 by auto 
      moreover have "dim_col ((psq c (k-1) m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))) = 1"
        using assms phase_shifted_qubit_def pow_tensor_list_dim_col[of xs "k-c-1"] pow_tensor_list_dim_col[of ys "m-k"] f0 by simp 
      ultimately show ?thesis by auto
    qed
    ultimately show ?thesis by simp
  qed
  ultimately have "((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ (Id (m-c-1))) * (Id 1 ⨂ (fSWAP (k-c) (m-k))))
        * ((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) 
     = (Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * ((CR (k-c+1) ⨂ (Id (m-c-1))) * ((psq c (k-1) m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))))"
    by simp
  moreover have "(CR (k-c+1) ⨂ Id (m-c-1)) * ((psq c (k-1) m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))) 
        = (psq c k m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k))" 
    using app_CR_tensor_Id[of k m c v j xs ys] assms by auto
  ultimately have "((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ (Id (m-c-1))) * (Id 1 ⨂ (fSWAP (k-c) (m-k))))
                 * ((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) 
                 = (Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * ((psq c k m j) ⨂ v ⨂ (pr xs (k-c-1)) ⨂ (pr ys (m-k)))" 
    by simp
  then show "((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ (Id (m-c-1))) * (Id 1 ⨂ (fSWAP (k-c) (m-k))))
                 * ((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) 
                 = ((psq c k m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k)))" 
    using assms f0 app_Id_SWAP_front_herm_cnj by auto
qed

lemma app_CR_on_all:
  assumes "k ≥ 2" and "m ≥ 1" and "k ≤ m" and "c ≥ 1" and "c ≤ k - 1" and "c ≤ m" 
      and "dim_row v = 2" and "dim_col v = 1" 
      and "v = |zero⟩ ∨ v = |one⟩"
      and "v = |zero⟩ ⟶ ((bin_rep m j)!(k-1)) = 0"
      and "v = |one⟩ ⟶  ((bin_rep m j)!(k-1)) = 1" 
      and "(∀x ∈ set xs. dim_row x = 2)" and "(∀y ∈ set ys. dim_row y = 2)"
      and "(∀x ∈ set xs. dim_col x = 1)" and "(∀y ∈ set ys. dim_col y = 1)" 
      and "(∀c ∈ set cs. dim_row c = 2)" and "(∀c ∈ set cs. dim_col c = 1)" 
      and "length xs = (k-c-1)" and "length ys = m-k" and "length cs = c-1"
  shows "(CR_on_all c k m) * ((pr cs (c-1)) ⨂ (psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) 
       = ((pr cs (c-1)) ⨂ (psq c k m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k)))"
proof-
  have f0: "1 ≤ k - c" using assms(4,5) by linarith
  have "(CR_on_all c k m) * ((pr cs (c-1)) ⨂ (psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) 
       = (Id (c-1) ⨂ (Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ Id (m-c-1)) * (Id 1 ⨂ (fSWAP (k-c) (m-k))))
       * ((pr cs (c-1)) ⨂ (psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k)))" 
    using CR_on_all_def[of c k m] by simp
  then have "(CR_on_all c k m) * ((pr cs (c-1)) ⨂ (psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) 
       = (Id (c-1) ⨂ ((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ Id (m-c-1)) * (Id 1 ⨂ (fSWAP (k-c) (m-k)))))
       * ((pr cs (c-1)) ⨂ ((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))))" 
    using tensor_mat_is_assoc by simp
  moreover have "(Id (c-1) ⨂ ((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ Id (m-c-1)) * (Id 1 ⨂ (fSWAP (k-c) (m-k)))))
       * ((pr cs (c-1)) ⨂ ((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))))
       = (Id (c-1) * pr cs (c-1)) 
      ⨂ (((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ Id (m-c-1)) * (Id 1 ⨂ (fSWAP (k-c) (m-k)))) 
         * ((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))))" 
  proof- 
    have "dim_col (Id (c-1)) = dim_row (pr cs (c-1))" 
      using Id_def pow_tensor_list_dim_row[of cs "c-1" 2] assms by auto
    moreover have "dim_col ((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ Id (m-c-1)) * (Id 1 ⨂ (fSWAP (k-c) (m-k)))) 
        = dim_row ((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k)))" 
    proof-
      have "2^(k-Suc c) * (2 * 2^(m-k)) = (2::nat)^(m-c) " 
        using assms(1,3,5,6) aux_calculation(4)[of k c m] f0 by (metis (no_types, lifting) semigroup_mult_class.mult.assoc)
      then have "dim_row ((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) = 2^(m-c+1)"
      proof-
        have "dim_row (pr xs (k-c-1)) = 2^(k-c-1)" using pow_tensor_list_dim_row[of xs "k-c-1" 2] assms(12-13,18-20) by simp
        moreover have "dim_row v = 2" using assms(9) ket_vec_def by auto
        moreover have "dim_row (pr ys (m-k)) = 2^(m-k)" using pow_tensor_list_dim_row[of ys "m-k" 2] assms(12-13,18-20) by simp
        moreover have "dim_row (psq c (k-1) m j) = 2" using phase_shifted_qubit_def by simp
        moreover have "2 * (2 ^ (m - k) * 2 ^ (k - Suc c)) = (2::nat) ^ (m - c)" using assms 
          by (metis ‹2 ^ (k - Suc c) * (2 * 2 ^ (m - k)) = 2 ^ (m - c)› mult.commute semigroup_mult_class.mult.assoc)
        ultimately show ?thesis using dim_row_tensor_mat[of "(psq c (k-1) m j)" "((pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k)))"] by auto
      qed
      moreover have "dim_col ((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ Id (m-c-1)) * (Id 1 ⨂ (fSWAP (k-c) (m-k))))
          = dim_col (Id 1 ⨂ (fSWAP (k-c) (m-k)))" by auto
      moreover have "dim_col (Id 1 ⨂ (fSWAP (k-c) (m-k))) = 2^(m-c+1)"
        using Id_def SWAP_front_dim assms by simp
      ultimately show ?thesis by simp
    qed
    moreover have "dim_col (Id (c-1)) > 0" and "dim_col (pr cs (c-1)) > 0" and 
                  "dim_col ((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ Id (m-c-1)) * (Id 1 ⨂ (fSWAP (k-c) (m-k)))) > 0" and
                  "dim_col ((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) > 0" 
         apply (auto simp: pow_tensor_list_dim_col[of cs "c-1"] assms phase_shifted_qubit_def Id_def)
        using SWAP_front_dim2(2)[of k m c] assms(3,5) f0 by simp
    ultimately show ?thesis
      using mult_distr_tensor[of "(Id (c-1))" "(pr cs (c-1))" 
            "((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ Id (m-c-1)) * (Id 1 ⨂ (fSWAP (k-c) (m-k))))"
            "((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k)))"] by auto
  qed
  moreover have "(Id (c-1) * pr cs (c-1)) = pr cs (c-1)" 
    using Id_mult_left[of "pr cs (c-1)" "(c-1)"] pow_tensor_list_dim_row[of cs "c-1" 2] assms by auto
  ultimately have "(CR_on_all c k m) * ((pr cs (c-1)) ⨂ (psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) 
       =  pr cs (c-1) 
      ⨂ ( ((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ Id (m-c-1)) * (Id 1 ⨂ (fSWAP (k-c) (m-k)))) 
         * ((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) )" 
    by simp
  moreover have "((Id 1 ⨂ ((fSWAP (k-c) (m-k))⇧†)) * (CR (k-c+1) ⨂ (Id (m-c-1))) * (Id 1 ⨂ (fSWAP (k-c) (m-k))))
        * ((psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) 
        = (psq c k m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))" 
    using app_CR_on_all_wo_Id[of k m c v j xs ys] assms by linarith
  ultimately show "(CR_on_all c k m) * ((pr cs (c-1)) ⨂ (psq c (k-1) m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))) 
       =  pr cs (c-1) ⨂ (psq c k m j) ⨂ (pr xs (k-c-1)) ⨂ v ⨂ (pr ys (m-k))"
    using tensor_mat_is_assoc by simp
qed

lemma CR_on_all_on_qr:
 assumes "j < 2^m" and "n ≤ m" and "c ≤ m" and "c < n" and "m ≥ c + 1"
     and "n ≥ 2" and "m ≥ 1" and "c ≥ 1"
  shows 
 "(CR_on_all c n m) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c (n-1) m j) ⨂ (⨂r (c+1) (m-c) m j))
= ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c n m j) ⨂ (⨂r (c+1) (m-c) m j))"
proof-
  have f0: "(⨂r (c+1) (m-c) m j) = (⨂r (c+1) (n-(c+1)) m j) ⨂ (⨂r n 1 m j) ⨂ (⨂r (n+1) (m-n) m j)"
  proof(rule disjE)
    show "n < m ∨ n = m" using assms by auto
  next
     assume a0: "n < m"
     moreover have "n + 1 - (c + 1) ≤ m - c" using assms by simp
     moreover have "c + 1 + (m - c) - 1 ≤ m" using assms a0 by simp
     ultimately have "(⨂r (c+1) (m-c) m j) = (⨂r (c+1) ((n+1)-(c+1)-1) m j) ⨂ (⨂r (n+1-1) 1 m j) ⨂ (⨂r (n+1) ((m-c)-((n+1)-(c+1))) m j)"  
       using to_tensor_prod_decomp_middle[of j m "c+1" "n+1" "m-c"] assms a0 by simp
     moreover have "(m-c)-((n+1)-(c+1)) = m-n" using assms by simp
     ultimately show ?thesis by simp
  next
     assume a0: "n = m" 
     have "((c + 1) + (m - c - 1)) = m" using add.left_commute add_diff_cancel_left assms by linarith
     moreover have "(⨂r (c+1) (m-c) m j) = (⨂r (c+1) (m-c-1) m j) ⨂ (⨂r ((c+1)+(m-c-1)) 1 m j)" 
       using assms to_tensor_prod_decomp_right[of j m "c+1" "m-c-1"] by simp
     ultimately have "(⨂r (c+1) (m-c) m j) = (⨂r (c+1) (n-(c+1)) m j) ⨂ (⨂r n 1 m j)" 
       by (simp add: a0)
     moreover have "(⨂r (n+1) (m-n) m j) = (Id 0)" using a0 by simp
     ultimately show ?thesis by simp
  qed
  then have "(CR_on_all c n m) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c (n-1) m j) ⨂ (⨂r (c+1) (m-c) m j))
= (CR_on_all c n m) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c (n-1) m j) ⨂ (⨂r (c+1) (n-(c+1)) m j) ⨂ (⨂r n 1 m j) ⨂ (⨂r (n+1) (m-n) m j))"
    using tensor_mat_is_assoc by simp
  moreover have "(CR_on_all c n m) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c (n-1) m j) ⨂ (⨂r (c+1) (n-(c+1)) m j) ⨂ (⨂r n 1 m j) ⨂ (⨂r (n+1) (m-n) m j))
= ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c n m j) ⨂ (⨂r (c+1) (n-(c+1)) m j) ⨂ (⨂r n 1 m j) ⨂ (⨂r (n+1) (m-n) m j))"
  proof-
    have "(CR_on_all c n m) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c (n-1) m j) 
       ⨂ (pr (to_list_bound (c+1) (n-(c+1)) m j) (n-c-1)) 
       ⨂ (pr (to_list_bound n 1 m j) 1) 
       ⨂ (pr (to_list_bound (n+1) (m-n) m j) (m-n)))
       =  (pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c n m j) 
       ⨂ (pr (to_list_bound (c+1) (n-(c+1)) m j) (n-c-1))  
       ⨂ (pr (to_list_bound n 1 m j) 1) 
       ⨂ (pr (to_list_bound (n+1) (m-n) m j) (m-n))"
    proof-
      have "2 ≤ n ∧ 1 ≤ m ∧ n ≤ m ∧ 1 ≤ c ∧ c ≤ n - 1 ∧ c ≤ m " using assms by simp
      moreover have "dim_row (pr (to_list_bound n 1 m j) 1) = 2" 
                and "dim_col (pr (to_list_bound n 1 m j) 1) = 1" using pow_tensor_length_1 
        apply (metis add_left_cancel power_one_right to_tensor_prod_def to_tensor_prod_dim)
        using to_tensor_prod_def to_tensor_prod_dim by presburger
      moreover have "length [psq (nat i) m m j. i<-[1..(c-1)]] = c-1" by simp
      moreover have "(∀x ∈ set (to_list_bound (c+1) (n-(c+1)) m j). dim_row x = 2)" using to_list_bound_dim by simp
      moreover have "(∀x ∈ set (to_list_bound (c+1) (n-(c+1)) m j). dim_col x = 1)" using to_list_bound_dim by simp
      moreover have "length (to_list_bound (c+1) (n-(c+1)) m j) = n-c-1" by (simp add: to_list_bound_length)
      moreover have "(∀y ∈ set (to_list_bound (n+1) (m-n) m j). dim_row y = 2)" using to_list_bound_dim by simp
      moreover have "(∀y ∈ set (to_list_bound (n+1) (m-n) m j). dim_col y = 1)" using to_list_bound_dim by simp
      moreover have "length (to_list_bound (n+1) (m-n) m j) = m-n" by (simp add: to_list_bound_length)
      moreover have "(pr (to_list_bound n 1 m j) 1) = |zero⟩ ∨ (pr (to_list_bound n 1 m j) 1) = |one⟩" 
        using pow_tensor_length_1 by simp
      moreover have "(pr (to_list_bound n 1 m j) 1) = |zero⟩ ⟶ bin_rep m j ! (n - 1) = 0" 
        using to_tensor_bin_rep_zero to_tensor_prod_def assms by simp 
      moreover have "(pr (to_list_bound n 1 m j) 1) = |one⟩ ⟶ bin_rep m j ! (n - 1) = 1" 
        using to_tensor_bin_rep_one to_tensor_prod_def assms(1-2) assms by simp 
      moreover have "(∀c∈set (map (λi. psq (nat i) m m j) [1..int (c - 1)]). dim_row c = 2)"
        using phase_shifted_qubit_def by simp
      moreover have 
        "(∀c∈set (map (λi. psq (nat i) m m j) [1..int (c - 1)]). dim_col c = 1)" 
        using phase_shifted_qubit_def assms(7) by simp
      ultimately show ?thesis
        using app_CR_on_all[of n m c "(pr (to_list_bound n 1 m j) 1)" j "(to_list_bound (c+1) (n-(c+1)) m j)"
                                   "(to_list_bound (n+1) (m-n) m j)" "[psq (nat i) m m j. i<-[1..(c-1)]]"] 
        by blast   
    qed
    then have "(CR_on_all c n m) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c (n-1) m j) 
    ⨂ (pr (to_list_bound (c+1) (n-(c+1)) m j) (n-(c+1))) 
    ⨂ (pr (to_list_bound n 1 m j) 1) 
    ⨂ (pr (to_list_bound (n+1) (m-n) m j) (m-n)))
    =  (pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c n m j) 
    ⨂ (pr (to_list_bound (c+1) (n-(c+1)) m j) (n-(c+1)))  
    ⨂ (pr (to_list_bound n 1 m j) 1) 
    ⨂ (pr (to_list_bound (n+1) (m-n) m j) (m-n))" by auto
    moreover have "(⨂r (c+1) (n-(c+1)) m j) = (pr (to_list_bound (c+1) (n-(c+1)) m j) (n-(c+1)))" 
      using to_tensor_prod_def by simp
    moreover have "(⨂r n 1 m j) = (pr (to_list_bound n 1 m j) 1) " 
      using to_tensor_prod_def by simp
    moreover have "(⨂r (n+1) (m-n) m j) = (pr (to_list_bound (n+1) (m-n) m j) (m-n))"       
      using to_tensor_prod_def by simp
    ultimately show ?thesis by auto
  qed
ultimately have "(CR_on_all c n m) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c (n-1) m j) ⨂ (⨂r (c+1) (m-c) m j))
=((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c n m j) ⨂ (⨂r (c+1) (n-(c+1)) m j) ⨂ (⨂r n 1 m j) ⨂ (⨂r (n+1) (m-n) m j))"
  by auto
then have "(CR_on_all c n m) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c (n-1) m j) ⨂ (⨂r (c+1) (m-c) m j))
=((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c n m j) ⨂ ((⨂r (c+1) (n-(c+1)) m j) ⨂ (⨂r n 1 m j) ⨂ (⨂r (n+1) (m-n) m j)))"
  using tensor_mat_is_assoc by simp
then show "(CR_on_all c n m) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c (n-1) m j) ⨂ (⨂r (c+1) (m-c) m j))
=((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c n m j) ⨂ (⨂r (c+1) (m-c) m j))"
  using f0 by simp
qed


subsection ‹Applying all $R_k$'s›

(*Could go into generic mult function would be more confusing to understand though*)

(*A series of R⇩k gates should be applied to each qubit, e.g. R⇩2...R⇩n are applied to |j⇩1⟩, R⇩2...R⇩n⇩-⇩1 are 
applied to |j⇩2⟩ etc.  
c is the current qubit and k=(n-c) ensures that R⇩2 to R⇩n⇩-⇩c⇩+⇩1 are applied to the qubit with the 
special case for c=n that nothing is applied. *)
fun all_CR:: "nat ⇒ nat ⇒ nat ⇒ complex Matrix.mat" ("aCR _ _ _" 75) where
  "(aCR c 0 m) = (Id m)"  
| "(aCR c (Suc k) m) = (CR_on_all c (c+(Suc k)) m) * (aCR c k m)"

lemma all_CR_dim [simp]:
  assumes "c ≤ m" and "1 ≤ c"
  shows "c + k ≤ m ⟶ dim_row (aCR c k m) = 2^m ∧ dim_col (aCR c k m) = 2^m"
proof(induction k)
  show "c + 0 ≤ m ⟶ dim_row (aCR c 0 m) = 2^m ∧ dim_col (aCR c 0 m) = 2^m"
    using Id_def by simp
next
  fix k
  assume IH: "c + k ≤ m ⟶ dim_row (aCR c k m) = 2^m ∧ dim_col (aCR c k m) = 2^m"
  have "c + (Suc k) ≤ m ⟶ dim_row (aCR c (Suc k) m) = 2^m" using CR_on_all_dim assms by simp
  moreover have "c + (Suc k) ≤ m ⟶ dim_col (aCR c (Suc k) m) = 2^m" using IH by simp
  ultimately show "c + (Suc k) ≤ m ⟶ dim_row (aCR c (Suc k) m) = 2^m ∧ dim_col (aCR c (Suc k) m) = 2^m"
    by simp
qed

lemma all_CR_is_gate:
  assumes "c ≥ 1" and "c ≤ m"
  shows "c + k ≤ m ⟶ gate m (aCR c k m)" 
proof(induction k)
  show "c + 0 ≤ m ⟶ gate m (aCR c 0 m)" by simp
next
  fix k
  assume IH: "c + k ≤ m ⟶ gate m (aCR c k m)" 
  moreover have "(aCR c (Suc k) m) = (CR_on_all c (c+(Suc k)) m) * (aCR c k m)" by simp
  moreover have "c + (Suc k) ≤ m ⟶ gate m (CR_on_all c (c+(Suc k)) m)" using CR_on_all_is_gate assms by simp
  ultimately show "c + (Suc k) ≤ m ⟶ gate m (aCR c (Suc k) m)" using prod_of_gate_is_gate by simp
qed

lemma aux_all_CR_app:
  assumes "c ≥ 1" and "c + 1 ≤ m" and "n ≥ c" and "j < 2^m" and "n ≥ 1" and "m ≥ 1"
  shows "n ≤ m ⟶ aCR c (n-c) m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j)) 
        = ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c n m j) ⨂ (⨂r (c+1) (m-c) m j))"
proof(rule Nat.nat_induct_at_least[of c n])
  show "c ≤ n" using assms by simp
next
  show "c ≤ m ⟶ aCR c (c-c) m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j)) 
        = ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j))"
  proof
    assume a0: "c ≤ m"
    then have "aCR c (c-c) m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j)) 
            = (Id m) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j))"
      by simp
    moreover have "dim_row ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j)) = 2^m" 
    proof-
      have "dim_row (pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) = 2^(c-1)" 
        using phase_shifted_qubit_def pow_tensor_list_dim_row[of "[psq (nat i) m m j. i<-[1..(c-1)]]" "c-1" 2] by simp
      then show ?thesis using phase_shifted_qubit_def to_tensor_prod_dim aux_calculation(10) assms a0 by simp
    qed
    ultimately show  "aCR c (c-c) m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j)) 
            = ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j))"
      using Id_mult_left by simp
  qed
next
  fix n 
  assume a0: "n ≥ c"
  assume IH: "n ≤ m ⟶ aCR c (n-c) m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j)) 
        = ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c n m j) ⨂ (⨂r (c+1) (m-c) m j))"
  show "(Suc n) ≤ m ⟶ aCR c ((Suc n)-c) m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j)) 
        = ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c (Suc n) m j) ⨂ (⨂r (c+1) (m-c) m j))"
  proof
    assume a1: "(Suc n) ≤ m"
    have "aCR c ((Suc n)-c) m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j)) 
        = ((CR_on_all c (Suc n) m) * (aCR c (n-c) m)) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j))"
      by (simp add: Suc_diff_le a0)
    moreover have "((CR_on_all c (Suc n) m) * (aCR c (n-c) m)) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j))
        = (CR_on_all c (Suc n) m) * ((aCR c (n-c) m) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j)))"
    proof-
      have "dim_row (pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) = (2^(c-1))" 
        using phase_shifted_qubit_def pow_tensor_list_dim_row[of "[psq (nat i) m m j. i<-[1..(c-1)]]" "c-1" 2] by simp 
      moreover have "dim_row (⨂r (c+1) (m-c) m j) = (2^(m-c))" using to_tensor_prod_dim by blast
      moreover have "2^(c-1) * 2 * 2^(m-c) = (2::nat)^m" using assms(1-2) by simp
      ultimately have "dim_row ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j)) = (2^m)" 
        using phase_shifted_qubit_def assms by simp
      moreover have "dim_col ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j)) = 1" 
        using phase_shifted_qubit_def assms pow_tensor_list_dim_col to_tensor_prod_dim by simp
      ultimately have "((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j)) ∈ carrier_mat (2^m) 1" 
        by auto
      moreover have "(CR_on_all c (Suc n) m) ∈ carrier_mat (2^m) (2^m)" 
        by (metis CR_on_all_dim(1) CR_on_all_dim(2) One_nat_def Suc_le_eq a0 a1 assms(1) carrier_matI le_imp_less_Suc zero_less_diff)
      moreover have "(aCR c (n-c) m) ∈ carrier_mat (2^m) (2^m)" using a0 a1 assms(1) by auto
      ultimately show ?thesis by simp
    qed
    ultimately have "aCR c ((Suc n)-c) m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j)) 
        = (CR_on_all c (Suc n) m) * ((aCR c (n-c) m) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j)))"
      by simp
    then have "aCR c ((Suc n)-c) m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j)) 
        =  (CR_on_all c (Suc n) m) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c (Suc n - 1) m j) ⨂ (⨂r (c+1) (m-c) m j))"
      using a1 IH by simp
    moreover have "c < Suc n " by (simp add: a0 less_Suc_eq_le)
    ultimately show "aCR c ((Suc n)-c) m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j)) 
        = ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c (Suc n) m j) ⨂ (⨂r (c+1) (m-c) m j))"
      using CR_on_all_on_qr[of j m "Suc n" c] a0 a1 assms by (metis Suc_le_mono add_leD1 le_trans one_add_one plus_1_eq_Suc)
  qed
qed

lemma all_CR_app:
  assumes "c ≥ 1" and "c + 1 ≤ m" and "c ≤ m" and "j < 2^m" and "m ≥ 1"
  shows "aCR c (m-c) m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j)) 
        = ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c m m j) ⨂ (⨂r (c+1) (m-c) m j))"
  using aux_all_CR_app[of c m m j] assms by simp


subsection ‹Application of all Necessary Gates to a Single Qubit›

(*Apply the H gate to the current qubit then apply R⇩2 to R⇩m⇩-⇩c*)
definition all_gates_on_single_qubit:: "nat ⇒ nat ⇒ complex Matrix.mat" ("G _ _" 75)  where
 "G c m = aCR c (m-c) m * (Id (c-1) ⨂ H ⨂ Id (m-c))"  

lemma G_dim [simp]:
  assumes "c ≤ m" and "c ≥ 1"  
  shows "dim_row (G c m) = 2^m"
    and "dim_col (G c m) = 2^m" 
proof-
  have "dim_row (G c m) = dim_row (aCR c (m-c) m )" using all_gates_on_single_qubit_def by auto
  moreover have "c + (m - c) ≤ m" by (simp add: assms(1))
  ultimately show "dim_row (G c m) = 2^m" using all_CR_dim[of c m "m-c"] assms by simp
next
  have "dim_col (G c m) = dim_col (Id (c-1) ⨂ H ⨂ Id (m-c))" using all_gates_on_single_qubit_def by simp
  then show "dim_col (G c m) = 2^m" using Id_def assms(1-2) by (simp add: H_without_scalar_prod)
qed

lemma G_is_gate:
  assumes "c ≥ 1" and "c ≤ m"
  shows "gate m (G c m)"
proof-
  have "gate m (aCR c (m-c) m)" using all_CR_is_gate assms by simp
  moreover have "gate m (Id (c-1) ⨂ H ⨂ Id (m-c))" 
    by (metis H_is_gate assms(1-2) id_is_gate le_add_diff_inverse2 ordered_cancel_comm_monoid_diff_class.add_diff_inverse tensor_gate)
  ultimately show ?thesis using prod_of_gate_is_gate all_gates_on_single_qubit_def by simp
qed

lemma app_H_zero:
  assumes "((bin_rep m jd)!k) = 0"
    shows "H * |zero⟩ = (psq (k+1) (k+1) m jd)" 
proof
  fix i j::nat
  assume "i < dim_row (psq (k+1) (k+1) m jd)" and "j < dim_col (psq (k+1) (k+1) m jd)"
  then have f0: "i ∈ {0,1} ∧ j = 0" using phase_shifted_qubit_def by auto 
  then have "(H * |zero⟩) $$ (i,j) = (∑k<dim_row |zero⟩. (H $$ (i,k)) * ( |zero⟩ $$ (k,0)))" 
    apply (simp add: H_without_scalar_prod ket_vec_def) by fastforce
  then have f1: "(H * |zero⟩) $$ (i,j) = (H $$ (i,0)) * ( |zero⟩ $$ (0,0)) + (H $$ (i,1)) * ( |zero⟩ $$ (1,0))"
    using zero_def set_2 ket_vec_def by (simp add: lessThan_atLeast0)
  moreover have "i=0 ⟶ (psq (k+1) (k+1) m jd) $$ (0,0) = (1::complex)/sqrt(2)"
    using phase_shifted_qubit_def f0 by auto
  moreover have "i=0 ⟶ (H * |zero⟩) $$ (i,j) = (1::complex)/sqrt(2)" 
    using f0 f1 apply auto apply (auto simp: H_without_scalar_prod).
  moreover have "i=1 ⟶ (psq (k+1) (k+1) m jd) $$ (i,j) = (exp (complex_of_real (2*pi)*𝗂*(bin_frac k k m jd)))*1/sqrt(2)"
    using phase_shifted_qubit_def f0 by auto
  moreover have "i=1 ⟶ (H * |zero⟩) $$ (i,j) = (1::complex)/sqrt(2)" 
    using f0 f1 apply auto apply (auto simp: H_without_scalar_prod).
  moreover have "(exp (complex_of_real (2*pi)*𝗂*(bin_frac k k m jd)))*1/sqrt(2) = (1::complex)/sqrt(2)"   
  proof-
    have "(bin_frac k k m jd) = 0"
      using bin_frac_def assms by simp
    then have "(exp (complex_of_real (2*pi)*𝗂*(bin_frac k k m jd))) = 1" by auto
    then show ?thesis by simp
  qed
  ultimately show "(H * |zero⟩) $$ (i,j) = (psq (k+1) (k+1) m jd) $$ (i,j)" 
    by (metis One_nat_def f0 lessThan_atLeast0 lessThan_iff less_2_cases set_2)
next
  show "dim_row (H * |zero⟩) = dim_row (psq (k+1) (k+1) m jd)" 
    by (simp add: H_without_scalar_prod phase_shifted_qubit_def)
next
  show "dim_col (H * |zero⟩) = dim_col (psq (k+1) (k+1) m jd)" 
    by (simp add: phase_shifted_qubit_def ket_vec_def)
qed

lemma app_H_one: 
  assumes "((bin_rep m jd)!k) = 1"
    shows "H * |one⟩ = (psq (k+1) (k+1) m jd)" 
proof
  fix i j::nat
  assume a0: "i < dim_row (psq (k+1) (k+1) m jd)" and "j < dim_col (psq (k+1) (k+1) m jd)"
  then have f0: "i ∈ {0,1} ∧ j = 0" using phase_shifted_qubit_def by auto 
  then have "(H * |one⟩) $$ (i,j) = (∑k<dim_row |one⟩. (H $$ (i,k)) * ( |one⟩ $$ (k,0)))" 
    apply (simp add: H_without_scalar_prod ket_vec_def) by fastforce
  then have f1: "(H * |one⟩) $$ (i,j) = (H $$ (i,0)) * ( |one⟩ $$ (0,0)) + (H $$ (i,1)) * ( |one⟩ $$ (1,0))" 
    using zero_def set_2 by (simp add: lessThan_atLeast0 ket_vec_def)
  moreover have "i=0 ⟶ (psq (k+1) (k+1) m jd) $$ (i,j) = (1::complex)/sqrt(2)"
    using phase_shifted_qubit_def f0 by auto
  moreover have "i=0 ⟶ (H * |one⟩) $$ (i,j) = 1/sqrt(2)" 
    using f0 f1 apply auto apply (auto simp: H_without_scalar_prod).
  moreover have "i=1 ⟶ (psq (k+1) (k+1) m jd) $$ (i,j) = (exp (complex_of_real (2*pi)*𝗂*(bin_frac k k m jd)))*1/sqrt(2)"
    using phase_shifted_qubit_def f0 by auto
  moreover have "i=1 ⟶ (H * |one⟩) $$ (i,j) = -1/sqrt(2)" 
    using f0 f1 apply auto apply (auto simp: H_without_scalar_prod).
  moreover have "(exp (complex_of_real (2*pi)*𝗂*(bin_frac k k m jd)))*1/sqrt(2) = -1/sqrt(2)"
  proof-
    have "(bin_frac k k m jd) = 1/2"
      using bin_frac_def assms by auto
    then have "(exp (complex_of_real (2*pi)*𝗂*(bin_frac k k m jd))) = -1" 
      by (simp add: ‹bin_frac k k m jd = 1 / 2›)
    then show ?thesis by auto
  qed
  ultimately show "(H * |one⟩) $$ (i,j) = (psq (k+1) (k+1) m jd) $$ (i,j)" 
    by (metis (no_types, lifting) One_nat_def a0 dim_row_mat(1) less_2_cases of_real_divide of_real_hom.hom_one phase_shifted_qubit_def)
next
  show "dim_row (H * |one⟩) = dim_row (psq (k+1) (k+1) m jd)" 
    by (simp add: H_without_scalar_prod phase_shifted_qubit_def)
next
  show "dim_col (H * |one⟩) = dim_col (psq (k+1) (k+1) m jd)" 
    by (simp add: ket_vec_def phase_shifted_qubit_def)
qed

lemma app_H:
  assumes "c ≥ 1" and "v = |zero⟩ ∨ v = |one⟩"  
      and "v = |zero⟩ ⟶ ((bin_rep m jd)!(c-1)) = 0"
      and "v = |one⟩ ⟶  ((bin_rep m jd)!(c-1)) = 1" 
    shows "H * v = (psq c c m jd)" using  app_H_zero assms app_H_one by auto

lemma app_H_all:
  assumes "c ≥ 1" and "m ≥ c" and "j < 2^m" 
  shows "(Id (c-1) ⨂ H ⨂ Id (m-c)) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j))
       = ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j))"
proof-
  have "(Id (c-1) ⨂ H ⨂ Id (m-c)) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j))
  = Id (c-1) * (pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (H ⨂ Id (m-c)) * (⨂r c (m-c+1) m j)"
  proof-
    have "dim_col (Id (c-1)) = dim_row (pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1))"
      using Id_def pow_tensor_list_dim_row[of "[psq (nat i) m m j. i<-[1..(c-1)]]" "c-1" 2] phase_shifted_qubit_def by auto
    moreover have "dim_col (H ⨂ Id (m-c)) = dim_row (⨂r c (m-c+1) m j)"
      using Id_def to_tensor_prod_dim by (simp add: H_without_scalar_prod)
    moreover have "dim_col (Id (c-1)) > 0" using Id_def by simp
    moreover have "dim_col H > 0" by (simp add: H_without_scalar_prod)
    moreover have "dim_col (⨂r c (m-c+1) m j) > 0" using to_tensor_prod_dim by simp
    moreover have "dim_col (pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) > 0"
      using pow_tensor_list_dim_col phase_shifted_qubit_def by simp
    ultimately show ?thesis using tensor_mat_is_assoc to_tensor_prod_dim mult_distr_tensor pos2 by auto
  qed
  then have "(Id (c-1) ⨂ H ⨂ Id (m-c)) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j))
  = (pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (H ⨂ Id (m-c)) * (⨂r c (m-c+1) m j)"
    using Id_mult_left pow_tensor_list_dim_row phase_shifted_qubit_def by simp
  moreover have f1: "v = |zero⟩ ∨ v = |one⟩ ⟶ (H ⨂ Id (m-c)) * (v ⨂ ⨂r (c+1) (m-c) m j) = (H * v) ⨂ (⨂r (c+1) (m-c) m j)" for v 
  proof
    assume a0: "v = |zero⟩ ∨ v = |one⟩"
    then have "dim_col H = dim_row v" using ket_vec_def H_without_scalar_prod 
      by (metis (no_types, lifting) dim_col_mat(1) dim_row_mat(1) index_unit_vec(3))
    moreover have "dim_col (Id (m-c)) = dim_row (⨂r (c+1) (m-c) m j)" 
      using Id_def by (simp add: to_tensor_prod_dim)
    moreover have "dim_col H > 0" and "dim_col (Id (m-c)) > 0" and "dim_col (⨂r (c+1) (m-c) m j) > 0" 
              and "dim_col v > 0"
      using a0 ket_vec_def apply (auto simp: H_without_scalar_prod Id_def to_tensor_prod_dim).
    ultimately have "(H ⨂ Id (m-c)) * (v ⨂ ⨂r (c+1) (m-c) m j) = (H * v) ⨂ (Id (m-c) * ⨂r (c+1) (m-c) m j)"
      using mult_distr_tensor by simp
    then show "(H ⨂ Id (m-c)) * (v ⨂ ⨂r (c+1) (m-c) m j) = (H * v) ⨂ (⨂r (c+1) (m-c) m j)"
      using Id_mult_left to_tensor_prod_dim by simp
  qed
  moreover have "(H ⨂ Id (m-c)) * (⨂r c (m-c+1) m j) = psq c c m j ⨂ (⨂r (c+1) (m-c) m j)"
  proof(rule disjE)
    show "(bin_rep m j)!(c-1) = 0 ∨ (bin_rep m j)!(c-1) = 1" using bin_rep_coeff assms by simp
  next
    assume a0: "(bin_rep m j)!(c-1) = 1"
    then have "(⨂r c (m-c+1) m j) = |one⟩ ⨂ (⨂r (c+1) (m-c) m j)"
      using to_tensor_prod_decomp_left_one assms a0 by simp
    then have "(H ⨂ Id (m-c)) * (⨂r c (m-c+1) m j) = (H * |one⟩) ⨂ (⨂r (c+1) (m-c) m j)" 
      using f1 by simp
    then show "(H ⨂ Id (m-c)) * (⨂r c (m-c+1) m j) = (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j)" 
      using a0 app_H_one assms(1) by simp
  next
    assume a0: "(bin_rep m j)!(c-1) = 0"
    then have "(⨂r c (m-c+1) m j) = |zero⟩ ⨂ (⨂r (c+1) (m-c) m j)"
      using to_tensor_prod_decomp_left_zero assms a0 by simp
    then have "(H ⨂ Id (m-c)) * (⨂r c (m-c+1) m j) = (H * |zero⟩) ⨂ (⨂r (c+1) (m-c) m j)" 
      using f1 by simp
    then show "(H ⨂ Id (m-c)) * (⨂r c (m-c+1) m j) = (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j)" 
      using a0 app_H_zero assms(1) by simp
  qed
  ultimately show "(Id (c-1) ⨂ H ⨂ Id (m-c)) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j))
  = (pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ psq c c m j ⨂ (⨂r (c+1) (m-c) m j)"
    using tensor_mat_is_assoc by simp
qed

lemma app_G:
  assumes "c ≥ 1" and "m ≥ c" and "j < 2^m" 
  shows "G c m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j))
      = ((pr [psq (nat i) m m j. i<-[1..c]] c) ⨂ (⨂r (c+1) (m-c) m j))"
proof(rule disjE)
  show "m > c ∨ m = c" using assms by auto
next
  assume a0: "m = c"
  then have "G c m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j))
           = G m m * ((pr [psq (nat i) m m j. i<-[1..(m-1)]] (m-1)) ⨂ (⨂r m (m-m+1) m j))" by simp
 then have "G c m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j))
         = (Id m * (Id (m-1) ⨂ H ⨂ Id (m-m))) * ((pr [psq (nat i) m m j. i<-[1..(m-1)]] (m-1)) ⨂ (⨂r m (m-m+1) m j))" 
   using all_gates_on_single_qubit_def by simp
  moreover have "dim_row (Id (m-1) ⨂ H ⨂ Id (m-m)) = 2^m" 
    using a0 assms(1)
    by (metis (no_types, lifting) H_without_scalar_prod Id_right_tensor One_nat_def Quantum.Id_def diff_self_eq_0 dim_row_mat(1) 
        dim_row_tensor_mat index_one_mat(2) less_eq_Suc_le power_minus_mult)
  ultimately have "G c m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j))
      = ((Id (m-1) ⨂ H ⨂ Id (m-m))) * ((pr [psq (nat i) m m j. i<-[1..(m-1)]] (m-1)) ⨂ (⨂r m (m-m+1) m j))" 
    using Id_mult_left by simp
  then have "G c m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j))
      = (pr [psq (nat i) m m j. i<-[1..(m-1)]] (m-1)) ⨂ (psq m m m j) ⨂ (⨂r (m+1) (m-m+1-1) m j)" 
    using app_H_all[of m m j] assms by simp
  moreover have "length  [psq (nat i) m m j. i<-[1..(m-1)]] = m-1" by simp
  ultimately have "G c m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j))
      = (pr ([psq (nat i) m m j. i<-[1..int(m-1)]]@[psq m m m j]) ((m-1)+1)) ⨂ (⨂r (m+1) (m-m+1-1) m j)"
    using pow_tensor_decomp_left a0 by simp
  moreover have "[psq (nat i) m m j. i<-[1..(m-1)]]@[psq m m m j] = [psq (nat i) m m j. i<-[1..m]]"
    using a0 assms(1) 
    by (metis (no_types, lifting) linordered_nonzero_semiring_class.of_nat_mono list.simps(8) list.simps(9) 
        map_append nat_int of_nat_1 of_nat_diff upto_rec2)
  ultimately have "G c m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j))
      = ((pr [psq (nat i) m m j. i<-[1..m]] m) ⨂ (⨂r (m+1) (m-m+1-1) m j))" 
    using assms by simp
  then show "G c m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j))
      = ((pr [psq (nat i) m m j. i<-[1..c]] c) ⨂ (⨂r (c+1) (m-c) m j))" using a0 by auto
next
  assume a0: "m > c"
  have "G c m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j))
      = (aCR c (m-c) m * (Id (c-1) ⨂ H ⨂ Id (m-c))) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j))"
    using all_gates_on_single_qubit_def by simp
  moreover have "(aCR c (m-c) m * (Id (c-1) ⨂ H ⨂ Id (m-c))) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j))
               = aCR c (m-c) m * ((Id (c-1) ⨂ H ⨂ Id (m-c)) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j)))"
  proof-
    have "aCR c (m-c) m ∈ carrier_mat (2^m) (2^m)" using assms(1-2) by auto
    moreover have "(Id (c-1) ⨂ H ⨂ Id (m-c)) ∈ carrier_mat (2^m) (2^m)" 
      using Id_def H_without_scalar_prod aux_calculation(10) a0 assms carrier_matI[of H 2 2] carrier_matI[of "Id (c-1)" "c-1" "c-1"] 
            carrier_matI[of "Id (m-c)" "m-c" "m-c"]
      by (smt One_nat_def carrier_matI dim_col_mat(1) dim_col_tensor_mat dim_row_mat(1) dim_row_tensor_mat index_one_mat(2) index_one_mat(3))
    moreover have "((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j)) ∈ carrier_mat (2^m) 1" 
    proof-
      have "length [psq (nat i) m m j. i<-[1..(c-1)]] = c-1" by simp
      moreover have "∀x∈set [psq (nat i) m m j. i<-[1..(c-1)]]. dim_row x = 2" using phase_shifted_qubit_def by simp
      moreover have "∀x∈set [psq (nat i) m m j. i<-[1..(c-1)]]. dim_col x = 1" using phase_shifted_qubit_def by simp
      ultimately have "(pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ∈ carrier_mat (2^(c-1)) 1"         
        using pow_tensor_list_dim_row[of "[psq (nat i) m m j. i<-[1..(c-1)]]" "c-1" 2] by auto
      moreover have "(⨂r c (m-c+1) m j) ∈ carrier_mat (2^(m-c+1)) 1" using to_tensor_prod_dim by auto
      moreover have "2^(c-1) * 2^(m-c+1) = (2::nat)^m" 
        using a0 assms aux_calculation(10) by (simp add: semigroup_mult_class.mult.assoc)
      ultimately show ?thesis by auto
    qed
    ultimately show ?thesis using a0 assms(1) by simp
  qed
  ultimately have "G c m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j))
      = aCR c (m-c) m * ((Id (c-1) ⨂ H ⨂ Id (m-c)) * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j)))" by simp
  then have "G c m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j))
      = aCR c (m-c) m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c c m j) ⨂ (⨂r (c+1) (m-c) m j))"
    using app_H_all assms by simp
  then have "G c m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j))
      = ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (psq c m m j) ⨂ (⨂r (c+1) (m-c) m j))"
    using all_CR_app assms a0 by simp
  moreover have "length  [psq (nat i) m m j. i<-[1..(c-1)]] = c-1" by simp
  ultimately have "G c m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j))
      = ((pr ([psq (nat i) m m j. i<-[1..(c-1)]]@[psq c m m j]) (c-1+1)) ⨂ (⨂r (c+1) (m-c) m j))"
    using pow_tensor_decomp_left by simp
  moreover have "[psq (nat i) m m j. i<-[1..(c-1)]]@[psq c m m j] = [psq (nat i) m m j. i<-[1..c]]"
    using assms(1) 
    by (metis (no_types, lifting) linordered_nonzero_semiring_class.of_nat_mono list.simps(8) list.simps(9) map_append nat_int of_nat_1 of_nat_diff upto_rec2)
  ultimately show "G c m * ((pr [psq (nat i) m m j. i<-[1..(c-1)]] (c-1)) ⨂ (⨂r c (m-c+1) m j))
      = ((pr [psq (nat i) m m j. i<-[1..c]] c) ⨂ (⨂r (c+1) (m-c) m j))"
    using assms by simp
qed


subsection ‹Extension of the Application of all Necessary Gates to all Qubits›

fun pow_mult :: "(complex Matrix.mat) list ⇒ nat ⇒ complex Matrix.mat" ("pm _ _" 75)  where
  "(pm (Cons x []) (Suc 0)) = x"  
| "(pm (Cons x xs) (Suc k)) = (pm xs k) * x"

lemma aux_pow_mult_dim:
  assumes "k ≥ 1"
  shows "∀xs. length xs = k ∧ (∀x ∈ set xs. dim_row x = n ∧ dim_col x = n) ⟶ dim_row (pm xs k) = n ∧ dim_col (pm xs k) = n"
proof(rule Nat.nat_induct_at_least[of 1 k])
  show "k≥1" using assms by simp
next
  show "∀xs. length xs = 1 ∧ (∀x ∈ set xs. dim_row x = n ∧ dim_col x = n) ⟶ dim_row (pm xs 1) = n ∧ dim_col (pm xs 1) = n"
    by (metis One_nat_def cancel_comm_monoid_add_class.diff_cancel last_ConsL last_in_set length_0_conv length_tl list.exhaust_sel 
        pow_mult.simps(1) zero_neq_one)
next
  fix k::nat
  assume a0: "k ≥ 1"
  assume IH: "∀xs. length xs = k ∧ (∀x ∈ set xs. dim_row x = n ∧ dim_col x = n) ⟶ dim_row (pm xs k) = n ∧ dim_col (pm xs k) = n"
  show "∀xs. length xs = (Suc k) ∧ (∀x ∈ set xs. dim_row x = n ∧ dim_col x = n) ⟶ dim_row (pm xs (Suc k)) = n ∧ dim_col (pm xs (Suc k)) = n"
  proof(rule allI, rule impI)
    fix xs::"complex Matrix.mat list"
    assume a1: "length xs = (Suc k) ∧ (∀x ∈ set xs. dim_row x = n ∧ dim_col x = n)"
    show "dim_row (pm xs (Suc k)) = n ∧ dim_col (pm xs (Suc k)) = n"
    proof
      have "dim_row (pm xs (Suc k)) = dim_row ((pm (tl xs) k) * (hd xs))" using a0 a1
        by (metis le_iff_add length_0_conv list.exhaust_sel nat.simps(3) plus_1_eq_Suc pow_mult.simps(3))
      then have "dim_row (pm xs (Suc k)) = dim_row (pm (tl xs) k)" by simp
      then show "dim_row (pm xs (Suc k)) = n" using IH a1
        by (metis diff_Suc_1 length_0_conv length_tl list.set_sel(2) nat.simps(3))
    next
      have "dim_col (pm xs (Suc k)) = dim_col ((pm (tl xs) k) * (hd xs))" using a0 a1
        by (metis le_iff_add length_0_conv list.exhaust_sel nat.simps(3) plus_1_eq_Suc pow_mult.simps(3))
      then have "dim_col (pm xs (Suc k)) = dim_col (hd xs)" by simp
      then show "dim_col (pm xs (Suc k)) = n" 
        by (metis a1 hd_in_set length_greater_0_conv zero_less_Suc)
    qed
  qed
qed

lemma pow_mult_dim [simp]:
  assumes "k ≥ 1" and "length xs = k" and "(∀x ∈ set xs. dim_row x = n ∧ dim_col x = n)"
  shows "dim_row (pm xs k) = n ∧ dim_col (pm xs k) = n"
  using assms aux_pow_mult_dim by simp

lemma aux_pow_mult_decomp_left:
  assumes "k ≥ 1" and "(dim_row x = n ∧ dim_col x = n)"
  shows "∀xs. length xs = k ∧ (∀y ∈ set xs. dim_row y = n ∧ dim_col y = n) ⟶ pm (xs@[x]) (Suc k) = x * (pm xs k)"
proof(rule Nat.nat_induct_at_least)
  show "k ≥ 1" using assms by simp
next
  show "∀xs. length xs = 1 ∧ (∀x ∈ set xs. dim_row x = n ∧ dim_col x = n)⟶ pm (xs@[x]) (Suc 1) = x * (pm xs 1)"
  proof(rule allI, rule impI)
    fix xs:: "complex Matrix.mat list"
    assume a0: "length xs = 1 ∧ (∀x ∈ set xs. dim_row x = n ∧ dim_col x = n)"
    then have "∃y. xs = y # tl xs" by (metis One_nat_def length_Suc_conv list.sel(3))
    then have "∃y. xs = [y]" using a0 
      by (metis One_nat_def Suc_le_mono add_diff_cancel_left' butlast.simps(2) impossible_Cons le_numeral_extra(4) 
          length_butlast length_tl list.sel(2) list.size(3) plus_1_eq_Suc)
    then obtain y where f0: "xs = [y]" by auto
    have "pm (xs@[x]) (Suc 1) = pm ([y]@[x]) (Suc 1)" using f0 by simp
    then have "pm (xs@[x]) (Suc 1) = x * y" by simp
    moreover have "x * (pm xs 1) = x * y" using f0 by simp
    ultimately show "pm (xs@[x]) (Suc 1) = x * (pm xs 1)" by simp
  qed
next
  fix k::nat
  assume a0: "k ≥ 1"
     and IH: "∀xs. length xs = k ∧ (∀x ∈ set xs. dim_row x = n ∧ dim_col x = n) ⟶ pm (xs@[x]) (Suc k) = x * (pm xs k)"
  show "∀xs. length xs = (Suc k) ∧ (∀x ∈ set xs. dim_row x = n ∧ dim_col x = n) ⟶ pm (xs@[x]) (Suc (Suc k)) = x * (pm xs (Suc k))"
  proof(rule allI, rule impI)
    fix xs:: "complex Matrix.mat list"
    assume a1: "length xs = (Suc k) ∧ (∀x ∈ set xs. dim_row x = n ∧ dim_col x = n)"
    then have "∃y. xs = y # tl xs" by (metis length_Suc_conv list.sel(3))
    then obtain y::"complex Matrix.mat" where f0: "xs = y # tl xs" by auto
    then have "pm (xs@[x]) (Suc (Suc k)) = pm (tl xs @ [x]) (Suc k) * y" by (metis append_Cons pow_mult.simps(3)) 
    then have "pm (xs@[x]) (Suc (Suc k)) = x * (pm (tl xs) k) * y" using IH a1 
      by (metis Nitpick.size_list_simp(2) add_diff_cancel_left' list.set_sel(2) nat.distinct(1) plus_1_eq_Suc)
    moreover have "x ∈ carrier_mat n n" using assms by auto
    moreover have "(pm (tl xs) k) ∈ carrier_mat n n" using pow_mult_dim[of k "tl xs" n] a0 a1 f0
      by (metis Ex_list_of_length carrier_matI length_Cons length_tl list.distinct(1) list.sel(3) list.set_sel(2))
      moreover have "y ∈ carrier_mat n n" by (metis a1 carrier_matI f0 list.set_intros(1))
    ultimately have "pm (xs@[x]) (Suc (Suc k)) = x * ((pm (tl xs) k) * y)" by simp
    then have "pm (xs@[x]) (Suc (Suc k)) = x * (pm (y#tl xs) (Suc k))" 
      using f0 a1
      by (metis append_Cons append_self_conv2 length_0_conv length_Cons not0_implies_Suc old.nat.inject pow_mult.simps)
    then show "pm (xs@[x]) (Suc (Suc k)) = x * (pm xs (Suc k))" using f0 by simp
  qed
qed

lemma pow_mult_decomp_left:
  assumes "k ≥ 1" and "(dim_row x = n ∧ dim_col x = n)" and "length xs = k" "(∀y ∈ set xs. dim_row y = n ∧ dim_col y = n)"
  shows "pm (xs@[x]) (Suc k) = x * (pm xs k)"
  using aux_pow_mult_decomp_left assms by simp

lemma pow_mult_decomp_G:
  assumes "k ≥ 1" and "k < m" 
  shows "(pm [G (nat i) m. i<-[1..(Suc k)]] (Suc k)) = (G (Suc k) m) * (pm [G (nat i) m. i<-[1..k]] k)" 
proof-
  have "dim_row (G nat (int (Suc k)) m) = 2 ^ m ∧ dim_col (G nat (int (Suc k)) m) = 2 ^ m"
    using G_dim[of "nat (int (Suc k))" m] assms by simp
  moreover have "length (map (λi. G nat i m) [1..int k]) = k" by simp
  moreover have "(∀y∈set (map (λi. G nat i m) [1..int k]). dim_row y = 2 ^ m ∧ dim_col y = 2 ^ m)" 
    using G_dim assms by auto
  moreover have "[G (Suc k) m ] = [G (nat i) m. i<-[(Suc k)..(Suc k)]]" 
    by (metis Cons_eq_map_conv list.simps(8) nat_int upto_single)
  moreover have "[G (nat i) m. i<-[1..(Suc k)]] = [G (nat i) m. i<-[1..k]] @ [G (Suc k) m ]"
    using calculation by (smt map_append of_nat_Suc of_nat_le_0_iff upto_split1)
  ultimately show ?thesis using pow_mult_decomp_left[of k "G (nat (Suc k)) m" "2^m" "[G (nat i) m. i<-[1..k]]"] assms by auto
qed

lemma all_G_is_gate:
  assumes "1 ≤ k" and "1 ≤ m"
  shows "k ≤ m ⟶ gate m (pm [G (nat i) m. i<-[1..k]] k)"
proof(rule Nat.nat_induct_at_least[of 1 k])
  show "1 ≤ k" using assms by simp
next
  show "1 ≤ m ⟶ gate m (pm [G (nat i) m. i<-[1..int 1]] 1)" using G_is_gate[of 1 m] assms by simp
next
  fix k
  assume IH: "k ≤ m ⟶ gate m (pm [G (nat i) m. i<-[1..int k]] k)"
     and a0: "k ≥ 1"
  show "(Suc k) ≤ m ⟶ gate m (pm [G (nat i) m. i<-[1..int (Suc k)]] (Suc k))" 
  proof
    assume a1: "(Suc k) ≤ m"
    have "(pm [G (nat i) m. i<-[1..(Suc k)]] (Suc k)) = G (nat (Suc k)) m * (pm [G (nat i) m. i<-[1..k]] k)" 
    proof-
      have "dim_row (G nat (int (Suc k)) m) = 2 ^ m ∧ dim_col (G nat (int (Suc k)) m) = 2 ^ m"
        using G_dim[of "nat (int (Suc k))" m] a1 by simp
      moreover have "length (map (λi. G nat i m) [1..int k]) = k" by simp
      moreover have "(∀y∈set (map (λi. G nat i m) [1..int k]). dim_row y = 2 ^ m ∧ dim_col y = 2 ^ m)" 
        using G_dim a1 by auto
      moreover have "[G (Suc k) m ] = [G (nat i) m. i<-[(Suc k)..(Suc k)]]" 
        by (metis Cons_eq_map_conv list.simps(8) nat_int upto_single)
      moreover have "[G (nat i) m. i<-[1..(Suc k)]] = [G (nat i) m. i<-[1..k]] @ [G (Suc k) m ]"
        using calculation by (smt map_append of_nat_Suc of_nat_le_0_iff upto_split1)
      ultimately show ?thesis using pow_mult_decomp_left[of k "G (nat (Suc k)) m" "2^m" "[G (nat i) m. i<-[1..k]]"] a0 by simp
    qed
    moreover have "gate m (G (nat (Suc k)) m)" using G_is_gate[of "Suc k" m] a0 a1 by (simp add: G_is_gate)
    ultimately show "gate m (pm [G (nat i) m. i<-[1..int (Suc k)]] (Suc k))" 
      by (simp add: IH Suc_leD a1 prod_of_gate_is_gate)
  qed
qed

lemma app_all_G: 
  assumes "k ≥ 1" and "j < 2^m" and "m ≥ 1"
  shows "k ≤ m ⟶ (pm [G (nat i) m. i<-[1..k]] k) * (⨂r 1 m m j)
      = ((pr [psq (nat i) m m j. i<-[1..k]] k) ⨂ (⨂r (k+1) (m-k) m j))" 
proof(rule Nat.nat_induct_at_least[of 1 k])
  show "k ≥ 1" using assms by simp
next
  show "1 ≤ m ⟶(pm [G (nat i) m. i<-[1..int 1]] 1) * (⨂r 1 m m j)
      = ((pr [psq (nat i) m m j. i<-[1..int 1]] 1) ⨂ (⨂r (1+1) (m-1) m j))" 
  proof
    assume "1 ≤ m" 
    have "(pm [G (nat i) m. i<-[1..int 1]] 1) * (⨂r 1 m m j) = (G 1 m) * (⨂r 1 m m j)"
     by simp
    moreover have "(⨂r 1 m m j) = ((pr [psq (nat i) m m j. i<-[1..(1-1)]] (1-1)) ⨂ (⨂r 1 (m-1+1) m j))" 
    proof-
      have "(pr [psq (nat i) m m j. i<-[1..(1-1)]] (1-1)) = (Id 0)" by simp
      moreover have "(⨂r 1 m m j) = (⨂r 1 (m-1+1) m j)" using assms by simp
      ultimately show ?thesis using Id_left_tensor by simp
    qed
    moreover have "G 1 m * ((pr [psq (nat i) m m j. i<-[1..(1-1)]] (1-1)) ⨂ (⨂r 1 (m-1+1) m j))
       = ((pr [psq (nat i) m m j. i<-[1..1]] 1) ⨂ (⨂r (1+1) (m-1) m j))"
      using app_G[of 1 m j] assms by simp 
    ultimately show "(pm [G (nat i) m. i<-[1..int 1]] 1) * (⨂r 1 m m j)
      = ((pr [psq (nat i) m m j. i<-[1..int 1]] 1) ⨂ (⨂r (1+1) (m-1) m j))" by simp
 qed
next
  fix k::nat
  assume a0: "k ≥ 1"
  assume IH: "k ≤ m ⟶(pm [G (nat i) m. i<-[1..k]] k) * (⨂r 1 m m j)
            = ((pr [psq (nat i) m m j. i<-[1..k]] k) ⨂ (⨂r (k+1) (m-k) m j))" 
  show  "(Suc k) ≤ m ⟶ (pm [G (nat i) m. i<-[1..(Suc k)]] (Suc k)) * (⨂r 1 m m j)
       = ((pr [psq (nat i) m m j. i<-[1..(Suc k)]] (Suc k)) ⨂ (⨂r ((Suc k)+1) (m-(Suc k)) m j))" 
  proof
    assume a1: "(Suc k) ≤ m"
    then have "(pm [G (nat i) m. i<-[1..int (Suc k)]] (Suc k)) * (⨂r 1 m m j)
             = ((G (Suc k) m) * (pm [G (nat i) m. i<-[1..int k]] k)) * (⨂r 1 m m j)"
      using a0 pow_mult_decomp_G[of k m] by simp
    moreover have "((G (Suc k) m) * (pm [G (nat i) m. i<-[1..int k]] k)) * (⨂r 1 m m j)
                 = (G (Suc k) m) * ((pm [G (nat i) m. i<-[1..int k]] k) * (⨂r 1 m m j))"
    proof-
      have "length [G (nat i) m. i<-[1..int k]] = k" by simp
      moreover have "∀x∈set (map (λi. G nat i m) [1..int k]). dim_row x = 2^m ∧ dim_col x = 2^m" 
        using G_dim a0 a1 by auto
      ultimately have "(pm [G (nat i) m. i<-[1..int k]] k) ∈ carrier_mat (2^m) (2^m)" 
        using a0 pow_mult_dim[of k "[G (nat i) m. i<-[1..int k]]" "2^m"] by auto
      moreover have "(G (Suc k) m) ∈ carrier_mat (2^m) (2^m)" 
        using G_dim[of "Suc k" m] a1 a0 le_SucI by blast
      moreover have "(⨂r 1 m m j) ∈ carrier_mat (2^m) 1" using to_tensor_prod_dim[of 1 m m j] by auto
      ultimately show ?thesis by simp
    qed
    ultimately have "(pm [G (nat i) m. i<-[1..int (Suc k)]] (Suc k)) * (⨂r 1 m m j)
             = (G (Suc k) m) * ((pm [G (nat i) m. i<-[1..int k]] k) * (⨂r 1 m m j))" by auto
    then have  "(pm [G (nat i) m. i<-[1..int (Suc k)]] (Suc k)) * (⨂r 1 m m j)
            = (G (Suc k) m) * ((pr [psq (nat i) m m j. i<-[1..k]] k) ⨂ (⨂r (k+1) (m-k) m j))"
      using IH a1 by auto
    then show "(pm [G (nat i) m. i<-[1..int (Suc k)]] (Suc k)) * (⨂r 1 m m j)
            = ((pr [psq (nat i) m m j. i<-[1..int (Suc k)]] (Suc k)) ⨂ (⨂r ((Suc k)+1) (m-(Suc k)) m j))"
      using app_G[of "Suc k" m j] assms a0 a1 by simp
  qed
qed


subsection ‹Reversing the Qubits›

fun reverse_qubits:: "nat ⇒ nat ⇒ complex Matrix.mat" ("rQB _ _" 75) where
  "(rQB 0 m) = (Id m)" 
| "(rQB (Suc k) m) = fSWAP (Suc k) (m-(Suc k)) * rQB k m"

lemma reverse_qubits_dim[simp]:
  shows "k ≤ m ⟶ dim_row (rQB k m) = 2^m ∧ dim_col (rQB k m) = 2^m" 
proof(induction k)
  show "0 ≤ m ⟶ dim_row (rQB 0 m) = 2^m ∧ dim_col (rQB 0 m) = 2^m" using Id_def by simp
next
  fix k::nat
  assume IH: "k ≤ m ⟶ dim_row (rQB k m) = 2^m ∧ dim_col (rQB k m) = 2^m" 
  show "(Suc k) ≤ m ⟶ dim_row (rQB (Suc k) m) = 2^m ∧ dim_col (rQB (Suc k) m) = 2^m" 
  proof
    assume a0: "(Suc k) ≤ m"
    then have "dim_row (rQB (Suc k) m) = 2^m" using SWAP_front_dim[of "Suc k" "m-(Suc k)"] by simp
    moreover have "dim_col (rQB (Suc k) m) = 2^m" using a0 IH by simp
    ultimately show "dim_row (rQB (Suc k) m) = 2^m ∧ dim_col (rQB (Suc k) m) = 2^m" by simp
  qed
qed

lemma reverse_qubits_is_gate:
  shows "k ≤ m ⟶ gate m (rQB k m)"
proof(induction k)
  show "0 ≤ m ⟶ gate m (rQB 0 m)" by simp
next
  fix k
  assume IH: "k ≤ m ⟶ gate m (rQB k m)"
  moreover have "(Suc k) ≤ m ⟶ gate m (fSWAP (Suc k) (m-(Suc k)))" 
    using SWAP_front_gate 
    by (metis le_add1 ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
  ultimately show "(Suc k) ≤ m ⟶ gate m (rQB (Suc k) m)"
    using prod_of_gate_is_gate by simp
qed

lemma app_reverse_qubits:
  shows "i ≤ m ⟶ (rQB i m) * (pr [psq (nat k) m m j. k<-[1..m]] m) 
       = (pr (rev [psq (nat k) m m j. k<-[1..i]]) i) ⨂ (pr [psq (nat k) m m j. k<-[i+1..m]] (m-i))"
proof(induction i)
  have "(rQB 0 m) * (pr [psq (nat k) m m j. k<-[1..int m]] m) 
      = (Id m) * (pr [psq (nat k) m m j. k<-[1..int m]] m)" by simp
  moreover have "dim_row (pr [psq (nat k) m m j. k<-[1..int m]] m) = 2^m" 
    using pow_tensor_list_dim_row[of "[psq (nat k) m m j. k<-[1..int m]]" m 2] phase_shifted_qubit_def by simp 
  ultimately have "(rQB 0 m) * (pr [psq (nat k) m m j. k<-[1..int m]] m) 
       = (pr [psq (nat k) m m j. k<-[1..int m]] m)" by simp
  moreover have "(pr (rev [psq (nat k) m m j. k<-[1..int 0]]) 0) = (Id 0)" by simp
  ultimately show "0 ≤ m ⟶ (rQB 0 m) * (pr [psq (nat k) m m j. k<-[1..int m]] m) 
       = (pr (rev [psq (nat k) m m j. k<-[1..int 0]]) 0) ⨂ (pr [psq (nat k) m m j. k<-[int (0+1)..int m]] (m-0))" by simp
next
  fix i::nat
  assume IH: "i ≤ m ⟶ (rQB i m) * (pr [psq (nat k) m m j. k<-[1..int m]] m) 
       = (pr (rev [psq (nat k) m m j. k<-[1..int i]]) i) ⨂ (pr [psq (nat k) m m j. k<-[int (i+1)..int m]] (m-i))"
  show "(Suc i) ≤ m ⟶ (rQB (Suc i) m) * (pr [psq (nat k) m m j. k<-[1..int m]] m) 
      = (pr (rev [psq (nat k) m m j. k<-[1..int (Suc i)]]) (Suc i)) ⨂ (pr [psq (nat k) m m j. k<-[int ((Suc i)+1)..int m]] (m-(Suc i)))"
  proof
    assume a0: "(Suc i) ≤ m"
    have "(rQB (Suc i) m) * (pr [psq (nat k) m m j. k<-[1..int m]] m) 
        = (fSWAP (Suc i) (m-(Suc i)) * rQB i m) * (pr [psq (nat k) m m j. k<-[1..int m]] m)" by simp
    moreover have "(fSWAP (Suc i) (m-(Suc i))) ∈ carrier_mat (2^m) (2^m)"  using SWAP_front_dim[of "Suc i" "m-(Suc i)"] a0 by auto
    moreover have "(rQB i m) ∈ carrier_mat (2^m) (2^m)" using reverse_qubits_dim a0 by auto
    moreover have "(pr [psq (nat k) m m j. k<-[1..int m]] m) ∈ carrier_mat (2^m) 1" 
      using pow_tensor_list_dim_row[of "[psq (nat k) m m j. k<-[1..int m]]" m 2]   
            pow_tensor_list_dim_col[of "[psq (nat k) m m j. k<-[1..int m]]" m] phase_shifted_qubit_def by auto
    ultimately have "(rQB (Suc i) m) * (pr [psq (nat k) m m j. k<-[1..int m]] m) 
       = fSWAP (Suc i) (m-(Suc i)) * (rQB i m * (pr [psq (nat k) m m j. k<-[1..int m]] m))" by simp
    then have "(rQB (Suc i) m) * (pr [psq (nat k) m m j. k<-[1..int m]] m) 
       = fSWAP (Suc i) (m-(Suc i)) * ((pr (rev [psq (nat k) m m j. k<-[1..int i]]) i) ⨂ (pr [psq (nat k) m m j. k<-[int (i+1)..int m]] (m-i)))" 
      using IH a0 by simp
    moreover have "(pr [psq (nat k) m m j. k<-[int (i+1)..int m]] (m-i))
                = psq (nat (i+1)) m m j ⨂ (pr [psq (nat k) m m j. k<-[int ((Suc i)+1)..int m]] (m-i-1))" 
    proof-
      have "length (map (λk. psq (nat k) m m j) [int ((Suc i)+1)..int m]) = m - i - 1" 
        using a0 by simp
      then have "psq (nat (i+1)) m m j ⨂ (pr [psq (nat k) m m j. k<-[int ((Suc i)+1)..int m]] (m-i-1))
          = (pr (psq (nat (i+1)) m m j # [psq (nat k) m m j. k<-[int ((Suc i)+1)..int m]]) (m-i-1+1))"
        using pow_tensor_decomp_right[of "[psq (nat k) m m j. k<-[int ((Suc i)+1)..int m]]" "m-i-1" "psq (nat (i+1)) m m j"] by simp
      moreover have "psq (nat (i+1)) m m j # [psq (nat k) m m j. k<-[int ((Suc i)+1)..int m]]
          = [psq (nat k) m m j. k<-[int (Suc i)..int m]]" using a0 upto_rec1 by simp
      ultimately have "psq (nat (i+1)) m m j ⨂ (pr [psq (nat k) m m j. k<-[int ((Suc i)+1)..int m]] (m-i-1))
          = (pr [psq (nat k) m m j. k<-[int (Suc i)..int m]] (m-i-1+1))" by auto
      then show ?thesis 
        by (metis (mono_tags, lifting) Suc_diff_le Suc_eq_plus1 a0 diff_Suc_Suc diff_diff_left)
    qed
    ultimately have "(rQB (Suc i) m) * (pr [psq (nat k) m m j. k<-[1..int m]] m) 
= fSWAP (Suc i) (m-(Suc i)) * ((pr (rev [psq (nat k) m m j. k<-[1..int i]]) i) ⨂ psq (nat (i+1)) m m j ⨂ (pr [psq (nat k) m m j. k<-[int ((Suc i)+1)..int m]] (m-i-1)))" 
      using tensor_mat_is_assoc by simp
    moreover have "fSWAP (Suc i-0) (m-(Suc i)) *
((pr (rev [psq (nat k) m m j. k<-[1..int i]]) (Suc i - 0 - 1)) ⨂ psq (nat (i+1)) m m j ⨂ (pr [psq (nat k) m m j. k<-[int ((Suc i)+1)..int m]] (m-(Suc i))))
= psq (nat (i+1)) m m j ⨂ (pr (rev [psq (nat k) m m j. k<-[1..int i]]) (Suc i - 0 - 1)) ⨂ (pr [psq (nat k) m m j. k<-[int ((Suc i)+1)..int m]] (m-(Suc i)))"
    proof-
      have "0 + 1 ≤ Suc i" by simp
      moreover have "1 ≤ Suc i" by simp
      moreover have " length (rev [psq (nat k) m m j. k<-[1..int i]]) = Suc i - 0 - 1" by simp
      moreover have " length [psq (nat k) m m j. k<-[int ((Suc i)+1)..int m]] = m - Suc i" by simp
      moreover have "∀y∈set (map (λk. psq (nat k) m m j) [int (Suc i + 1)..int m]). dim_col y = 1" using phase_shifted_qubit_def by simp
      moreover have "∀x∈set (rev (map (λk. psq (nat k) m m j) [1..int i])). dim_col x = 1" using phase_shifted_qubit_def by simp
      moreover have "∀y∈set (map (λk. psq (nat k) m m j) [int (Suc i + 1)..int m]). dim_row y = 2" using phase_shifted_qubit_def by simp
      moreover have "∀x∈set (rev (map (λk. psq (nat k) m m j) [1..int i])). dim_row x = 2 " using phase_shifted_qubit_def by simp
      moreover have "dim_col (psq (nat (int (i + 1))) m m j) = 1" using phase_shifted_qubit_def by simp
      moreover have "dim_row (psq (nat (int (i + 1))) m m j) = 2" using phase_shifted_qubit_def by simp
      moreover have "Suc i ≤ m" using a0 by auto
      ultimately show ?thesis 
        using app_SWAP_front[of 0 "Suc i" m "psq (nat (i+1)) m m j" "(rev [psq (nat k) m m j. k<-[1..int i]])" 
                       "[psq (nat k) m m j. k<-[int ((Suc i)+1)..int m]]"] tensor_mat_is_assoc a0 by auto
    qed
    ultimately have "(rQB (Suc i) m) * (pr [psq (nat k) m m j. k<-[1..int m]] m) 
= (psq (nat (i+1)) m m j ⨂ (pr (rev [psq (nat k) m m j. k<-[1..int i]]) i) ⨂ (pr [psq (nat k) m m j. k<-[int ((Suc i)+1)..int m]] (m-i-1)))" 
      by simp
    moreover have "psq (nat (i+1)) m m j ⨂ (pr (rev [psq (nat k) m m j. k<-[1..int i]]) i)
                 = pr (rev [psq (nat k) m m j. k<-[1..int (Suc i)]]) (Suc i)"
    proof-
      have "psq (nat (i+1)) m m j # (rev [psq (nat k) m m j. k<-[1..int i]])
          = rev (([psq (nat k) m m j. k<-[1..int i]]) @ [psq (nat (i+1)) m m j])" 
        by simp
      moreover have "[psq (nat k) m m j. k<-[1..int i]] @ [psq (nat (i+1)) m m j] = [psq (nat k) m m j. k<-[1..int (i+1)]]" 
        by (simp add: upto_rec2)
      moreover have "length [psq (nat k) m m j. k<-[1..int i]] = i" by simp
      ultimately show ?thesis using pow_tensor_decomp_right[of "[psq (nat k) m m j. k<-[1..int i]]" i "psq (nat (i+1)) m m j "]
        by (metis Suc_eq_plus1 pow_tensor_list.simps(2))
    qed
    ultimately show "(rQB (Suc i) m) * (pr [psq (nat k) m m j. k<-[1..int m]] m) 
       = (pr (rev [psq (nat k) m m j. k<-[1..int (Suc i)]]) (Suc i)) ⨂ (pr [psq (nat k) m m j. k<-[int ((Suc i)+1)..int m]] (m-(Suc i)))"
    by simp
  qed
qed


subsection ‹The Quantum Fourier Transform›

definition quantum_fourier_transform :: "nat⇒complex Matrix.mat" ("QFT _" 75) where 
"(QFT m) = (rQB m m) * (pm [G (nat i) m. i<-[1..m]] m)"

lemma quantum_fourier_transform_is_gate:
  assumes "1 ≤ m"
  shows "gate m (QFT m)"
proof-
  have "gate m (rQB m m)" using reverse_qubits_is_gate by simp
  moreover have "gate m (pm [G (nat i) m. i<-[1..m]] m)" using all_G_is_gate[of m m] assms by simp
  ultimately show ?thesis using prod_of_gate_is_gate quantum_fourier_transform_def by simp
qed

abbreviation ψ⇩1 :: "nat ⇒ nat ⇒ complex Matrix.mat" where
  "ψ⇩1 m j ≡ pr [psq (nat k) m m j. k<-[1..m] ] m"

lemma aux_quantum_fourier_transform_prod_rep:
  assumes "j < 2^m" and "m ≥ 1"
  shows "(pm [G (nat i) m. i<-[1..m]] m) * |unit_vec (2^m) j⟩  = ψ⇩1 m j" 
proof-
  have "(pm [G (nat i) m. i<-[1..m]] m) * |unit_vec (2^m) j⟩  = (pm [G (nat i) m. i<-[1..m]] m) * (⨂r 1 m m j)"
    using assms(1-2) ket_unit_to_tensor_prod by simp
  then have "(pm [G (nat i) m. i<-[1..m]] m) * |unit_vec (2^m) j⟩ = ((pr [psq (nat i) m m j. i<-[1..m]] m) ⨂ (⨂r (m+1) (m-m) m j))" 
    using app_all_G assms by simp
  moreover have "(⨂r (m+1) (m-m) m j) = (Id 0)" by simp
  ultimately have "(pm [G (nat i) m. i<-[1..m]] m) * |unit_vec (2^m) j⟩ = (pr [psq (nat i) m m j. i<-[1..m]] m)" by simp
  then show ?thesis by simp
qed

abbreviation ψ⇩2 :: "nat ⇒ nat ⇒ complex Matrix.mat" where 
  "ψ⇩2 m j ≡ pr [psq (m+1-nat k) m m j. k<-[1..m] ] m"

lemma list_shift_one:
  assumes "n ≥ 1"
  shows "[A k. k<-[1..int n]] = [A (k-1). k<-[2..int (Suc n)]]" 
proof(rule Nat.nat_induct_at_least[of 1 n])
  show "n ≥ 1" using assms by simp
next
  show "[A k. k<-[1..int 1]] = [A (k-1). k<-[2..int (Suc 1)]]" by simp
next
  fix n
  assume a0: "n ≥ 1"
     and IH: "[A k. k<-[1..int n]] = [A (k-1). k<-[2..int (Suc n)]]" 
  have "[A k. k<-[1..int (Suc n)]] = [A k. k<-[1..int n]] @ [A (Suc n)]"
    by (smt append_self_conv2 list.map(1) list.map(2) map_append of_nat_le_0_iff semiring_1_class.of_nat_simps(2) 
        upto_empty upto_single upto_split2)
  then have "[A k. k<-[1..int (Suc n)]] = [A (k-1). k<-[2..int (Suc n)]] @ [A (Suc n)]" by (simp add: IH)
  moreover have "[A (Suc n)] = [A (k-1). k<-[(Suc (Suc n))..int (Suc (Suc n))]]" using a0 by simp
  ultimately show "[A k. k<-[1..int (Suc n)]] = [A (k-1). k<-[2..int (Suc (Suc n))]]" 
    by (simp add: upto_rec2)
qed
 
lemma rev_of_qr_list:
  assumes "n ≥ 1"
  shows "n ≤ m ⟶ (rev [psq (nat k) m m j. k<-[1..n]]) = [psq (n+1-nat k) m m j. k<-[1..n]]"
proof(rule Nat.nat_induct_at_least)
  show "n≥1" using assms by simp
next
  show "1 ≤ m ⟶ (rev [psq (nat k) m m j. k<-[1..int 1]]) = [psq (1+1-nat k) m m j. k<-[1..int 1]]" by auto
next
  fix n 
  assume a0: "n ≥ 1"
     and IH: "n ≤ m ⟶ (rev [psq (nat k) m m j. k<-[1..n]]) = [psq (n+1-nat k) m m j. k<-[1..n]]"
  show "(Suc n) ≤ m ⟶ (rev [psq (nat k) m m j. k<-[1..(Suc n)]]) = [psq ((Suc n)+1-nat k) m m j. k<-[1..(Suc n)]]"
  proof
    assume a1: "(Suc n) ≤ m " 
    have "[psq (nat (Suc n)) m m j] = [psq (nat k) m m j. k<-[(Suc n)..(Suc n)]]" by simp
    then have "(rev [psq (nat k) m m j. k<-[1..(Suc n)]]) = psq (nat (Suc n)) m m j # (rev [psq (nat k) m m j. k<-[1..n]])"
      by (simp add: upto_rec2)
    then have "(rev [psq (nat k) m m j. k<-[1..(Suc n)]]) = psq (nat (Suc n)) m m j # [psq (n+1-nat k) m m j. k<-[1..n]]"
      using IH a1 by simp
    moreover have "[psq (n+1-nat k) m m j. k<-[1..n]] = [psq (Suc n+1-nat k) m m j. k<-[2..Suc n]]" 
    proof-
      have "[psq (n+1-nat k) m m j. k<-[1..int n]] = [psq (n+1-nat (k-1)) m m j. k<-[2..int (Suc n)]]"
        using list_shift_one[of n "λk. psq (n+1-nat k) m m j" ] a0 by simp
      moreover have "k ≥ 1 ⟶ n+1-nat (k-1) = Suc n+1-nat k" for k by auto
      ultimately show ?thesis by simp
    qed
    ultimately have "(rev [psq (nat k) m m j. k<-[1..(Suc n)]]) =  psq (nat (Suc n)+1-1) m m j # [psq (Suc n+1-nat k) m m j. k<-[2..Suc n]]"
      by simp
    then show "(rev [psq (nat k) m m j. k<-[1..(Suc n)]]) = [psq ((Suc n)+1-nat k) m m j. k<-[1..(Suc n)]]" 
      by (smt Cons_eq_map_conv One_nat_def nat.simps(3) nat_1 nat_int of_nat_le_0_iff upto_rec1)
  qed
qed

theorem quantum_fourier_transform_prod_rep:
  assumes "j < 2^m" and "m ≥ 1"
  shows "(QFT m) * |unit_vec (2^m) j⟩ = ψ⇩2 m j" 
proof-
  have "length [G (nat i) m. i<-[1..m]] = m" by simp
  moreover have "∀x∈set (map (λi. G nat i m) [1..int m]). dim_row x = 2 ^ m ∧ dim_col x = 2 ^ m" using G_dim by auto
  ultimately have "(pm [G (nat i) m. i<-[1..m]] m) ∈ carrier_mat (2^m) (2^m)" 
    using assms pow_mult_dim[of m "[G (nat i) m. i<-[1..m]]" "2^m"] by auto
  moreover have "(rQB m m) ∈ carrier_mat (2^m) (2^m)" using reverse_qubits_dim by auto
  moreover have "|unit_vec (2^m) j⟩ ∈ carrier_mat (2^m) 1" by (simp add: ket_vec_def)
  ultimately have "(QFT m) * |unit_vec (2^m) j⟩  = (rQB m m) * ((pm [G (nat i) m. i<-[1..m]] m) * |unit_vec (2^m) j⟩)"
    using quantum_fourier_transform_def by simp
  then have "(QFT m) * |unit_vec (2^m) j⟩  = (rQB m m) * (ψ⇩1 m j)" 
    using assms aux_quantum_fourier_transform_prod_rep by simp
  moreover have "(rQB m m) * (ψ⇩1 m j) = (ψ⇩2 m j)" 
  proof-
    have "m ≤ m ⟶ (rQB m m) * (pr [psq (nat k) m m j. k<-[1..m]] m) 
       = (pr (rev [psq (nat k) m m j. k<-[1..m]]) m) ⨂ (pr [psq (nat k) m m j. k<-[m+1..m]] (m-m))" 
      using app_reverse_qubits by simp 
    then have "(rQB m m) * (ψ⇩1 m j) = (pr (rev [psq (nat k) m m j. k<-[1..m]]) m)" by auto 
    moreover have "(rev [psq (nat k) m m j. k<-[1..m]]) = [psq (m+1-nat k) m m j. k<-[1..m]]" 
      using rev_of_qr_list[of m m j] assms by simp
    ultimately show ?thesis by simp
  qed
  ultimately show ?thesis by simp
qed

lemma aux_exp_term_one_1: 
  assumes "m ≥ k" and "k ≥ 1" and "m ≥ i" and "k ≥ i + 1" 
  shows "1/2^(m-k+1) * (2::nat)^(m-i) = 2^(k-i-1)"
proof-
  have "m - k + 1 ≤ m - i" 
    using assms(1,4) by linarith
  then have "1/2^(m-k+1)*(2::nat)^(m-i) = 2^(m-i-(m-k+1))"
    using power_diff[of 2 "m-k+1" "m-i"] 
    by (metis One_nat_def add.right_neutral add_Suc_right diff_diff_left mult.left_neutral of_nat_numeral 
        of_nat_power one_add_one times_divide_eq_left zero_neq_numeral)   
  moreover have "m - i - (m - k + 1) = k - i - 1" using assms by simp
  ultimately show ?thesis by simp
qed 

lemma aux_exp_term_one_2: 
  assumes "i ∈ {k-1..m-1}" and "m ≥ 1" and "m ≥ k" and "k ≥ 1" and "jd < 2^m"
  shows "1/2^(m-k+1)*real 2^(m-(i+1)) = 1/2^(i-(k-1)+1)" 
proof-
  have "(m::nat) - ((i::nat) + (1::nat)) ≤ m - (k::nat) + (1::nat)"
    using assms diff_le_mono2 by auto
  then have "(2::nat)^(m-k+1) * 1/2^(m-(i+1)) = 2^(m-k+1-(m-(i+1)))"
    using power_diff[of "2::nat" "m-(i+1)" "m-k+1"] 
    by (smt mult.right_neutral of_nat_1 of_nat_add of_nat_power one_add_one power_diff)
  then have "(2::nat)^(m-k+1) * 1/2^(m-(i+1)) = 2^(i-(k-1)+1)" 
    using assms
    by (smt Nat.add_diff_assoc2 add_diff_cancel_right atLeastAtMost_iff le_add_diff_inverse2
        cancel_ab_semigroup_add_class.diff_right_commute diff_diff_cancel diff_le_mono2) 
  then show ?thesis
    by (metis (no_types, lifting) divide_divide_eq_right nat_mult_1_right of_nat_1 of_nat_add of_nat_power 
        one_add_one times_divide_eq_left)
qed

lemma bit_representation:
  assumes "j < 2^m" and "m ≥ 1"
  shows "j = (∑i∈{1..m}. (bin_rep m j)!(i-1) * 2^(m-i))" 
proof-
  have "j = (∑i<m. bin_rep m j ! i * 2^(m-1-i))" 
    using bin_rep_eq[of m j] assms by simp
  also have "... = (∑i∈{0..m-1}. bin_rep m j ! i * 2^(m-1-i))" 
    using assms(2)
    by (metis atLeast0AtMost lessThan_Suc_atMost ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
  also have "... = (∑i∈{1..m-1+1}. bin_rep m j ! (i-1) * 2^(m-1-(i-1)))"
    using sum.shift_bounds_cl_nat_ivl[of "λi. bin_rep m j ! (i-1) * 2^(m-1-(i-1))" 0 1 "m-1"] by simp 
  also have "... = (∑i∈{1..m}. bin_rep m j ! (i-1) * 2^(m-1-(i-1)))"
    using add_Suc_right assms(2) ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc by simp
  finally show ?thesis by simp
qed

lemma exp_term_one:
  assumes "m ≥ 1" and "k ≥ 1" and "jd < 2^m"
  shows "k ≤ m ⟶ exp(2*pi*𝗂*(∑i∈{1..<k}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i))) = 1"
proof(rule Nat.nat_induct_at_least[of 1 k])
  show "k≥1" using assms by simp
next
  have "(∑i∈{(1::nat)..<1}. (bin_rep m jd)!(i-1) * 1/2^(m-1+1)*real 2^(m-i)) = 0" 
    by simp 
  then show "1≤m ⟶exp(2*pi*𝗂*(∑i∈{1..<1}. (bin_rep m jd)!(i-1) * 1/2^(m-1+1)*real 2^(m-i))) = 1"
    by simp
next
  fix k::nat
  assume a0: "k ≥ 1"
  assume IH: "k ≤ m ⟶ exp(2*pi*𝗂*(∑i∈{1..<k}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i))) = 1"
  show "(Suc k) ≤ m ⟶ exp(2*pi*𝗂*(∑i∈{1..<(Suc k)}. (bin_rep m jd)!(i-1) * 1/2^(m-(Suc k)+1)*real 2^(m-i))) = 1"
  proof
    assume a1: "(Suc k) ≤ m"
    have "(∑i∈{1..<(Suc k)}. (bin_rep m jd)!(i-1) * 1/2^(m-(Suc k)+1)*real 2^(m-i)) =
          (∑i∈{1..<k}. (bin_rep m jd)!(i-1) * 1/2^(m-(Suc k)+1)*real 2^(m-i))
        + (bin_rep m jd)!(k-1) * 1/2^(m-(Suc k)+1)*real 2^(m-k)" using sum_Un a0 by simp 
    then have "(∑i∈{1..<(Suc k)}. (bin_rep m jd)!(i-1) * 1/2^(m-(Suc k)+1)*real 2^(m-i)) =
               (2::nat) * (∑i∈{1..<k}.  ((bin_rep m jd)!(i-1) * 1/2^(m-k+1) * real 2^(m-i))) 
             + (bin_rep m jd)!(k-1) * 1/2^(m-(Suc k)+1)*real 2^(m-k)"
      using sum_distrib_left[of 2 "λi.((bin_rep m jd)!(i-1) * 1/2^(m-k+1) * real 2^(m-i))" "{1..<k}" ] a1 by simp
    then have "exp(2*pi*𝗂*(∑i∈{1..<(Suc k)}. (bin_rep m jd)!(i-1) * 1/2^(m-(Suc k)+1)*real 2^(m-i))) =
               exp((2::nat)*(2*pi*𝗂*(∑i∈{1..<k}. ((bin_rep m jd)!(i-1) * 1/2^(m-k+1) * real 2^(m-i))))) 
             * exp(2*pi*𝗂*((bin_rep m jd)!(k-1) * 1/2^(m-(Suc k)+1)*real 2^(m-k)))" 
      using exp_add distrib_left[of "(2*pi*𝗂)" "((2::nat)*(∑i∈{1..<k}. ((bin_rep m jd)!(i-1) * 1/2^(m-k+1) * real 2^(m-i))))"] 
      by simp
    then have "exp(2*pi*𝗂*(∑i∈{1..<(Suc k)}. (bin_rep m jd)!(i-1) * 1/2^(m-(Suc k)+1)*real 2^(m-i))) =
               exp((2*pi*𝗂*(∑i∈{1..<k}. ((bin_rep m jd)!(i-1) * 1/2^(m-k+1) * real 2^(m-i)))))^2
             * exp(2*pi*𝗂*((bin_rep m jd)!(k-1) * 1/2^(m-(Suc k)+1)*real 2^(m-k)))" 
      by (metis (mono_tags, lifting) exp_double of_nat_numeral)
    then have "exp(2*pi*𝗂*(∑i∈{1..<(Suc k)}. (bin_rep m jd)!(i-1) * 1/2^(m-(Suc k)+1)*real 2^(m-i))) =
               exp(2*pi*𝗂*((bin_rep m jd)!(k-1) * 1/2^(m-(Suc k)+1)*real 2^(m-k)))" 
      using IH a1 by simp
    moreover have "exp(2*pi*𝗂*((bin_rep m jd)!(k-1) * 1/2^(m-(Suc k)+1)*real 2^(m-k))) = 1"
    proof(rule disjE)
      show "(bin_rep m jd)!(k-1) = 0 ∨ (bin_rep m jd)!(k-1) = 1" 
        using bin_rep_coeff a0 a1 assms diff_less_Suc less_le_trans by blast
    next
      assume "(bin_rep m jd)!(k-1) = 0"
      then show ?thesis by simp
    next
      assume "(bin_rep m jd)!(k-1) = 1"
      then have "exp(2*pi*𝗂*((bin_rep m jd)!(k-1) * 1/2^(m-(Suc k)+1)*real 2^(m-k)))
               = exp(2*pi*𝗂*( 1/2^(m-(Suc k)+1)*real 2^(m-k)))" by auto
      then have "exp(2*pi*𝗂*((bin_rep m jd)!(k-1) * 1/2^(m-(Suc k)+1)*real 2^(m-k)))
               = exp(2*pi*𝗂*( 1/2^(m-k)*real 2^(m-k)))" 
        using a1
        by (metis (no_types, lifting) One_nat_def Suc_diff_le add.right_neutral add_Suc_right diff_Suc_Suc)
      then have "exp(2*pi*𝗂*((bin_rep m jd)!(k-1) * 1/2^(m-(Suc k)+1)*real 2^(m-k))) = exp(2*pi*𝗂)"  
        using  a0 a1 aux_exp_term_one_1
        by (smt Suc_diff_le Suc_eq_plus1 Suc_leD add.right_neutral add_diff_cancel_right' diff_Suc_Suc le_SucI mult.right_neutral 
            of_nat_power of_real_hom.hom_one order_refl plus_1_eq_Suc power.simps(1))
      then show "exp(2*pi*𝗂*((bin_rep m jd)!(k-1) * 1/2^(m-(Suc k)+1)*real 2^(m-k))) = 1" by simp
    qed
    ultimately show "exp(2*pi*𝗂*(∑i∈{1..<(Suc k)}. (bin_rep m jd)!(i-1) * 1/2^(m-(Suc k)+1)*real 2^(m-i))) = 1" 
      by simp
  qed
qed

lemma aux_qr_different_rep:
  assumes "m ≥ 1" and "m ≥ k" and "k ≥ 1" and "jd < 2^m"
  shows "psq k m m jd = Matrix.mat 2 1 (λ(i,j). if i=0 then 1/sqrt(2) else exp(2*pi*𝗂*jd/2^(m-k+1))*1/sqrt(2))" 
proof- 
  have "psq k m m jd = (Matrix.mat 2 1 (λ(i,j). if i=0 then (1::complex)/sqrt(2) 
              else (exp (complex_of_real (2*pi)*𝗂*(bin_frac (k-1) (m-1) m jd)))*1/sqrt(2)))"
        using phase_shifted_qubit_def by auto
  moreover have "exp(2*pi*𝗂*jd/2^(m-k+1)) = exp (complex_of_real (2*pi)*𝗂*(bin_frac (k-1) (m-1) m jd))" 
  proof-
    have "exp(2*pi*𝗂*jd/2^(m-k+1)) = exp(2*pi*𝗂*(∑i∈{1..m}. (bin_rep m jd)!(i-1) * 2^(m-i))*1/2^(m-k+1))" 
      using bit_representation assms by simp
    then have "exp(2*pi*𝗂*jd/2^(m-k+1)) = exp(2*pi*𝗂*(1/2^(m-k+1)*real(∑i∈{1..m}. (bin_rep m jd)!(i-1) * 2^(m-i))))" 
      using Groups.mult_ac(1) mult.right_neutral times_divide_eq_left by simp
    moreover have "(1/2^(m-k+1)*real(∑i∈{1..m}. (bin_rep m jd)!(i-1) * 2^(m-i)))
                 = (∑i∈{1..m}. 1/2^(m-k+1)*((bin_rep m jd)!(i-1) * 2^(m-i)))"
      using sum_distrib_left[of "1/2^(m-k+1)" "λi.(bin_rep m jd)!(i-1) * 2^(m-i)" "{1..m}"] by auto 
    ultimately have "exp(2*pi*𝗂*jd/2^(m-k+1)) = exp(2*pi*𝗂*(∑i∈{1..m}. 1/2^(m-k+1)*((bin_rep m jd)!(i-1) * 2^(m-i))))"
      by presburger
    then have "exp(2*pi*𝗂*jd/2^(m-k+1)) = exp(2*pi*𝗂*(∑i∈{1..m}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i)))"
      by simp
    moreover have "(∑i∈{1..m}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i)) = 
          (∑i∈{1..<k}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i)) +
          (∑i∈{k..m}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i))" 
      using assms(2-3) 
      by (smt atLeastLessThanSuc_atLeastAtMost le_eq_less_or_eq le_less_trans lessI sum.atLeastLessThan_concat)
    ultimately have "exp(2*pi*𝗂*jd/2^(m-k+1)) 
= exp(2*pi*𝗂*((∑i∈{1..<k}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i))+(∑i∈{k..m}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i))))"
      by metis
    then have "exp(2*pi*𝗂*jd/2^(m-k+1)) 
             = exp(2*pi*𝗂*(∑i∈{1..<k}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i))) *
               exp(2*pi*𝗂*(∑i∈{k..m}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i)))"
      using exp_add by (simp add: distrib_left)
    then have "exp(2*pi*𝗂*jd/2^(m-k+1)) = exp(2*pi*𝗂*(∑i∈{k..m}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i)))"
      using assms exp_term_one by auto
    moreover have "exp(2*pi*𝗂*(∑i∈{k..m}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i)))
                 = exp(2*pi*𝗂*(bin_frac (k-1) (m-1) m jd))" 
    proof-
      have "(∑i∈{k..m}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i))
          = (∑i∈{k-1..m-1}. (bin_rep m jd)!i* 1/2^(m-k+1)*real 2^(m-(i+1)))"
        using sum.shift_bounds_cl_nat_ivl[of "λi.(bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i)" "k-1" 1 "m-1"] assms(1,3)
        by simp
      moreover have "(∑i∈{k-1..m-1}. (bin_rep m jd)!i * (1/2^(m-k+1)*real 2^(m-(i+1))))
                   = (∑i∈{k-1..m-1}. (bin_rep m jd)!i * (1/2^(i-(k-1)+1)))" 
        using aux_exp_term_one_2 assms by (metis (no_types, lifting) sum.cong) 
      ultimately have "(∑i∈{k..m}. (bin_rep m jd)!(i-1) * 1/2^(m-k+1)*real 2^(m-i))
           =(∑i∈{k-1..m-1}. (bin_rep m jd)!i* 1/2^(i-(k-1)+1))"
        by simp
      then show ?thesis using bin_frac_def by simp
    qed
    ultimately show ?thesis by simp
  qed
  ultimately show ?thesis by auto
qed

lemma qr_different_rep:
  assumes "m ≥ 1" and "m ≥ k" and "k ≥ 1" and "jd < 2^m"
  shows "psq k m m jd = Matrix.mat 2 1 (λ(i,j). exp(2*pi*𝗂*jd*i/2^(m-k+1))*1/sqrt(2))" 
proof-
  have "psq k m m jd = Matrix.mat 2 1 (λ(i,j). if i=0 then 1/sqrt(2) else exp(2*pi*𝗂*jd/2^(m-k+1))*1/sqrt(2))" 
    using aux_qr_different_rep assms by simp
  moreover have "Matrix.mat 2 1 (λ(i,j). if i=0 then 1/sqrt(2) else exp(2*pi*𝗂*jd/2^(m-k+1))*1/sqrt(2))
               = Matrix.mat 2 1 (λ(i,j). exp(2*pi*𝗂*jd*i/2^(m-k+1))*1/sqrt(2))"
  proof
    fix i j
    assume "i < dim_row (Matrix.mat 2 1 (λ(i,j). exp(2*pi*𝗂*jd*i/2^(m-k+1))*1/sqrt(2)))"
       and "j < dim_col (Matrix.mat 2 1 (λ(i,j). exp(2*pi*𝗂*jd*i/2^(m-k+1))*1/sqrt(2)))"
    then have "i ∈ {0,1} ∧ j = 0" by auto
    moreover have "Matrix.mat 2 1 (λ(i,j). if i=0 then 1/sqrt(2) else exp(2*pi*𝗂*jd/2^(m-k+1))*1/sqrt(2)) $$ (0,0)
              = Matrix.mat 2 1 (λ(i,j). exp(2*pi*𝗂*jd*i/2^(m-k+1))*1/sqrt(2)) $$ (0,0)"
      by simp
    moreover have "Matrix.mat 2 1 (λ(i,j). if i=0 then 1/sqrt(2) else exp(2*pi*𝗂*jd/2^(m-k+1))*1/sqrt(2)) $$ (1,0)
              = Matrix.mat 2 1 (λ(i,j). exp(2*pi*𝗂*jd*i/2^(m-k+1))*1/sqrt(2)) $$ (1,0)" by simp  
    ultimately show "Matrix.mat 2 1 (λ(i,j). if i=0 then 1/sqrt(2) else exp(2*pi*𝗂*jd/2^(m-k+1))*1/sqrt(2)) $$ (i,j)
              = Matrix.mat 2 1 (λ(i,j). exp(2*pi*𝗂*jd*i/2^(m-k+1))*1/sqrt(2)) $$ (i,j)" by auto
  next
    show "dim_row (Matrix.mat 2 1 (λ(i,j). if i=0 then 1/sqrt(2) else exp(2*pi*𝗂*jd/2^(m-k+1))*1/sqrt(2)))
              = dim_row (Matrix.mat 2 1 (λ(i,j). exp(2*pi*𝗂*jd*i/2^(m-k+1))*1/sqrt(2)))" 
      by simp
  next
    show "dim_col (Matrix.mat 2 1 (λ(i,j). if i=0 then 1/sqrt(2) else exp(2*pi*𝗂*jd/2^(m-k+1))*1/sqrt(2)))
              = dim_col (Matrix.mat 2 1 (λ(i,j). exp(2*pi*𝗂*jd*i/2^(m-k+1))*1/sqrt(2)))" by simp
  qed
  ultimately show ?thesis by simp
qed

lemma bin_rep_div:
  assumes "i < 2^(Suc n)" and "n ≥ 1" and "l ≤ n" and "l ≥ 1"
  shows "(bin_rep n (i div 2))!(l-1) = (bin_rep (Suc n) i)!(l-1) " 
proof-
  have "m ≤ n ⟶ i div 2 mod 2^m = i mod 2^(m+1) div 2" for m::nat
    using assms by (simp add: mod_mult2_eq)
  then have f0: "i div 2 mod 2^(n-l+1) = i mod 2^(n-l+1+1) div 2" 
    by (metis assms(3-4) le_add_diff_inverse2 nat_add_left_cancel_le)
  have "(bin_rep n (i div 2))!(l-1) = ((i div 2) mod 2^(n-(l-1))) div 2^(n-1-(l-1))"
    using bin_rep_index assms by auto
  then have "(bin_rep n (i div 2))!(l-1) = (i mod 2^(n-l+1+1) div 2) div 2^(n-1-(l-1))" 
    using f0 assms(3-4)
    by (metis Nat.add_diff_assoc2 Nat.diff_diff_right)
  then have "(bin_rep n (i div 2))!(l-1) = i mod 2^(n-l+1+1) div 2^(n-1-(l-1)+1)" 
    by (metis (no_types, lifting) Groups.mult_ac(2) div_mult2_eq power_add power_one_right)
  then have "(bin_rep n (i div 2))!(l-1) = (i mod 2^((Suc n)-(l-1))) div 2^(n-1-(l-1)+1)" 
    using assms(2-4)
    by (smt Nat.diff_diff_eq One_nat_def Suc_diff_le add.right_neutral add_Suc_right diff_Suc_1 le_SucI)
  then have "(bin_rep n (i div 2))!(l-1) = (i mod 2^((Suc n)-(l-1))) div 2^((Suc n)-1-(l-1))" 
    using assms(2-4)
    by (smt Suc_diff_le add.right_neutral add_Suc_right  diff_Suc_Suc ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
  then show "(bin_rep n (i div 2))!(l-1) = (bin_rep (Suc n) i)!(l-1)"
    using bin_rep_index assms by auto
qed

lemma product_rep_to_matrix_rep: 
  assumes "n ≥ 1" and "m ≥ 1" and "jd < 2^m"
  shows "n ≤ m ⟶ (pr [Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..n] ] n)
       = Matrix.mat (2^n) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)"
proof(rule Nat.nat_induct_at_least[of 1 n])
  show "n ≥ 1" using assms by simp
next
  show "1 ≤ m ⟶ (pr [Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..int 1] ] 1)
       = Matrix.mat (2^1) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..1}. (bin_rep 1 (of_nat i))!(l-1)/2^l))*1/sqrt(2)^1)"
  proof
    assume a0: "1 ≤ m"
    have "(pr [Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..int 1] ] 1)
       = Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^1)*1/sqrt(2))" by simp
    moreover have "Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^1)*1/sqrt(2))
                 = Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(bin_rep 1 (of_nat i))!(1-1)/2^1)*1/sqrt(2))" 
    proof
      fix i j
      assume "i < dim_row (Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(bin_rep 1 (of_nat i))!(1-1)/2^1)*1/sqrt(2)))" 
      and "j < dim_col (Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(bin_rep 1 (of_nat i))!(1-1)/2^1)*1/sqrt(2)))" 
      then have f0: "i ∈ {0,1} ∧ j = 0" by auto
      moreover have "(Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*i/2^1)*1/sqrt(2))) $$ (0,j)
                   = (Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(bin_rep 1 i)!(1-1)/2^1)*1/sqrt(2))) $$ (0,j)"  
        using f0 by (simp add: bin_rep_index_0)
      moreover have "(Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*i/2^1)*1/sqrt(2))) $$ (1,j)
                   = (Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(bin_rep 1 i)!(1-1)/2^1)*1/sqrt(2))) $$ (1,j)" 
      proof-
        have "(Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(bin_rep 1 i)!(1-1)/2^1)*1/sqrt(2))) $$ (1,j)
            = exp(complex_of_real(2*pi)*𝗂*jd*(bin_rep 1 1)!(1-1)/2^1)*1/sqrt(2)" using f0 by auto
        moreover have "(bin_rep 1 1)!(1-1) = 1" using a0 
          by (metis One_nat_def Suc_eq_plus1 add_diff_cancel_left' bin_rep_index_0_geq le_numeral_extra(4) lessI one_add_one plus_1_eq_Suc power.simps(1) power_one_right)
        ultimately have "(Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(bin_rep 1 i)!(1-1)/2^1)*1/sqrt(2))) $$ (1,j)
            = exp(complex_of_real(2*pi)*𝗂*jd*1/2^1)*1/sqrt(2)" by simp
        moreover have "(Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*i/2^1)*1/sqrt(2))) $$ (1,j)
            = exp(complex_of_real(2*pi)*𝗂*jd*1/2^1)*1/sqrt(2)" using f0 by simp
        ultimately show ?thesis by auto
      qed 
      ultimately show "Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^1)*1/sqrt(2)) $$ (i,j)
                = Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(bin_rep 1 (of_nat i))!(1-1)/2^1)*1/sqrt(2)) $$ (i,j)" by auto
    next
      show "dim_row (Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^1)*1/sqrt(2)))
          = dim_row (Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(bin_rep 1 (of_nat i))!(1-1)/2^1)*1/sqrt(2)))" by simp
    next
      show "dim_col (Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^1)*1/sqrt(2)))
          = dim_col (Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(bin_rep 1 (of_nat i))!(1-1)/2^1)*1/sqrt(2)))" by simp
    qed
    ultimately have "(pr [Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..int 1] ] 1)
       =  Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(bin_rep 1 (of_nat i))!(1-1)/2^1)*1/sqrt(2))" 
      by simp
    then show "(pr [Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..int 1] ] 1)
       =  Matrix.mat (2^1) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..1}. (bin_rep 1 (of_nat i))!(l-1)/2^l))*1/sqrt(2)^1)"
      using a0 by simp
  qed
next
  fix n::nat
  assume a0: "n ≥ 1"
  assume IH: "n ≤ m ⟶ (pr [Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..n] ] n)
=  Matrix.mat (2^n) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)"
  show "(Suc n) ≤ m ⟶ (pr [Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..(Suc n)] ] (Suc n))
=  Matrix.mat (2^(Suc n)) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l))*1/sqrt(2)^(Suc n))"
  proof
    assume a1: "(Suc n) ≤ m"
    have "length [Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..n]] = n" by simp
    moreover have "[Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..n]]
              @ [Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k <-[Suc n..Suc n]]
            = [Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..(Suc n)]]" 
      using a0 by (smt One_nat_def map_append nat_1 nat_le_iff of_nat_Suc upto_split1)
    moreover have "[Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k <-[Suc n..Suc n]]
                 = [Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2))]" by simp
    ultimately have "(pr ([Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..(Suc n)]]) (n+1))
      = (pr [Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..n]] n)
      ⨂ (Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))" 
      using pow_tensor_decomp_left[of "[Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..n]]"
          "n" "(Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))"] by simp
    then have "(pr ([Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..(Suc n)]]) (n+1))
      = Matrix.mat (2^n) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)
      ⨂ (Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))"
    using a1 IH by simp
    moreover have "Matrix.mat (2^n) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)
      ⨂ (Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))
=  Matrix.mat (2^(Suc n)) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l))*1/sqrt(2)^(Suc n))"
    proof
      fix i j
      assume "i < dim_row (Matrix.mat (2^(Suc n)) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l))*1/sqrt(2)^(Suc n)))"
      and "j < dim_col (Matrix.mat (2^(Suc n)) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l))*1/sqrt(2)^(Suc n)))"
      then have f0: "i < 2^(Suc n) ∧ j=0" by auto
      then have "(Matrix.mat (2^n) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)
      ⨂ (Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))) $$ (i,j)
        = (Matrix.mat (2^n) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)) $$ (i div 2, j div 2)
        * (Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))$$ (i mod 2, j mod 2)" 
        by (smt One_nat_def add_self_mod_2 dim_col_mat(1) dim_row_mat(1) index_tensor_mat less_numeral_extra(1) 
            mod_add_self1 mod_div_trivial mod_if one_add_one one_power2 plus_1_eq_Suc plus_nat.simps(2) power_Suc2 power_one_right)
      then have "(Matrix.mat (2^n) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)
      ⨂ (Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))) $$ (i,j)
        = (exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..n}. (bin_rep n (of_nat (i div 2)))!(l-1)/2^l))
        * exp(complex_of_real(2*pi)*𝗂*jd*(of_nat (i mod 2))/2^(nat (Suc n))))*1/sqrt(2)^(Suc n)" using f0 by auto
      then have "(Matrix.mat (2^n) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)
      ⨂ (Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))) $$ (i,j)
        = (exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..n}. (bin_rep n (of_nat (i div 2)))!(l-1)/2^l) 
        + complex_of_real(2*pi)*𝗂*jd*(of_nat (i mod 2))/2^(nat (Suc n))))*1/sqrt(2)^(Suc n)"
        by (simp add: exp_add)
      moreover have "complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..n}. (bin_rep n (of_nat (i div 2)))!(l-1)/2^l)
                   + complex_of_real(2*pi)*𝗂*jd*(of_nat (i mod 2))/2^(nat (Suc n))
        = complex_of_real(2*pi)*𝗂*jd*((∑l∈{1..n}. (bin_rep n (i div 2))!(l-1)/2^l) + (of_nat (i mod 2))/2^(nat (Suc n)))" 
        using distrib_left[of "(complex_of_real(2*pi)*𝗂*jd)" "(∑l∈{1..n}. (bin_rep n (of_nat (i div 2)))!(l-1)/2^l)" 
                              "(of_nat (i mod 2))/2^(nat (Suc n))"] by auto
      ultimately have "(Matrix.mat (2^n) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)
      ⨂ (Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))) $$ (i,j)
    = (exp(complex_of_real(2*pi)*𝗂*jd*((∑l∈{1..n}. (bin_rep n (i div 2))!(l-1)/2^l) + (of_nat (i mod 2))/2^(nat (Suc n)))))*1/sqrt(2)^(Suc n)"
        by simp
      moreover have "(∑l∈{1..n}. (bin_rep n (i div 2))!(l-1)/2^l) + (of_nat (i mod 2))/2^(nat (Suc n))
                    = (∑l∈{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l)"
      proof-
        have "(i mod 2) = (bin_rep (Suc n) i)!((Suc n)-1)" 
          using a0 f0
          by (metis bin_rep_coeff bin_rep_even bin_rep_odd diff_less dvd_imp_mod_0 le_SucI le_imp_less_Suc less_one odd_iff_mod_2_eq_one zero_le) 
        then have "(∑l∈{1..n}. (bin_rep n (i div 2))!(l-1)/2^l) + (of_nat (i mod 2))/2^(nat (Suc n))
           = (∑l∈{1..n}. (bin_rep n (i div 2))!(l-1)/2^l) + ((bin_rep (Suc n) i)!((Suc n)-1))/2^(nat (Suc n))" by auto
        moreover have "(∑l∈{1..n}. (bin_rep n (i div 2))!(l-1)/2^l) = (∑l∈{1..n}. (bin_rep (Suc n) i)!(l-1)/2^l)" 
            using bin_rep_div a1 a0 assms atLeastAtMost_iff f0 by simp
        ultimately have "(∑l∈{1..n}. (bin_rep n (i div 2))!(l-1)/2^l) + (of_nat (i mod 2))/2^(nat (Suc n))
           =  (∑l∈{1..n}. (bin_rep (Suc n) i)!(l-1)/2^l) + ((bin_rep (Suc n) i)!((Suc n)-1))/2^(nat (Suc n))"
          by simp
        then have "(∑l∈{1..n}. (bin_rep n (i div 2))!(l-1)/2^l) + (of_nat (i mod 2))/2^(nat (Suc n))
           =  (∑l∈{1..n}. (bin_rep (Suc n) i)!(l-1)/2^l) + ((bin_rep (Suc n) i)!((Suc n)-1))/2^(Suc n)" 
          by (metis nat_int)
        moreover have "(∑l∈{1..n}. (bin_rep (Suc n) i)!(l-1)/2^l) + ((bin_rep (Suc n) i)!((Suc n)-1))/2^(Suc n)
           = (∑l∈{1..(Suc n)}. (bin_rep (Suc n) i)!(l-1)/2^l)" by simp
        ultimately show ?thesis by simp
      qed
      ultimately have "(Matrix.mat (2^n) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)
      ⨂ (Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))) $$ (i,j)
        = (exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l)))*1/sqrt(2)^(Suc n)"
        by presburger
      moreover have "(Matrix.mat (2^(Suc n)) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l))*1/sqrt(2)^(Suc n))) $$ (i,j)
      = exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l))*1/sqrt(2)^(Suc n)" using f0 by auto
      ultimately show "(Matrix.mat (2^n) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)
      ⨂ (Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2)))) $$ (i,j)
        = (Matrix.mat (2^(Suc n)) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l))*1/sqrt(2)^(Suc n))) $$ (i,j) "
        by simp
    next
      show "dim_row (Matrix.mat (2^n) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)
      ⨂ (Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2))))
        = dim_row (Matrix.mat (2^(Suc n)) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l))*1/sqrt(2)^(Suc n)))"
        by simp
    next
      show "dim_col (Matrix.mat (2^n) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..n}. (bin_rep n (of_nat i))!(l-1)/2^l))*1/sqrt(2)^n)
      ⨂ (Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat (Suc n)))*1/sqrt(2))))
        = dim_col (Matrix.mat (2^(Suc n)) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l))*1/sqrt(2)^(Suc n)))"
        by simp
    qed
    ultimately show "(pr [Matrix.mat 2 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..(Suc n)] ] (Suc n))
       =  Matrix.mat (2^(Suc n)) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..(Suc n)}. (bin_rep (Suc n) (of_nat i))!(l-1)/2^l))*1/sqrt(2)^(Suc n))"
      by simp
  qed
qed

abbreviation ψ⇩3 :: "nat ⇒ nat ⇒ complex Matrix.mat" where 
  "ψ⇩3 m jd ≡ Matrix.mat (2^m) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*i/2^m)*1/sqrt(2)^m)"

lemma product_rep_equals_matrix_rep: 
  assumes "jd < 2^m" and "m ≥ 1"
  shows "(ψ⇩2 m jd) = (ψ⇩3 m jd)"
proof-
  have  "k ∈ {1..m} ⟶ psq (m+1-nat k) m m jd = Matrix.mat 2 1 (λ(i,j). exp(2*pi*𝗂*jd*i/2^(nat k))*1/sqrt(2))" for k::int
    using qr_different_rep[of m "m+1-nat k" jd] assms by auto
  then have "[psq (m+1-nat k) m m jd. k<-[1..m]] = [Matrix.mat 2 1 (λ(i,j). exp(2*pi*𝗂*jd*i/2^(nat k))*1/sqrt(2)). k<-[1..m]]" 
    by simp
  then have "(ψ⇩2 m jd) = pr [Matrix.mat 2 1 (λ(i,j). exp(2*pi*𝗂*jd*(of_nat i)/2^(nat k))*1/sqrt(2)). k<-[1..m]] m" 
    by presburger   
  then have "(ψ⇩2 m jd) = Matrix.mat (2^m) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..m}. (bin_rep m (of_nat i))!(l-1)/2^l))*1/sqrt(2)^m)"
    using product_rep_to_matrix_rep assms by simp
  moreover have "Matrix.mat (2^m) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..m}. (bin_rep m (of_nat i))!(l-1)/2^l))*1/sqrt(2)^m)
               = (ψ⇩3 m jd)"
  proof
    fix i j::nat
    assume a0: "i < dim_row (ψ⇩3 m jd)" and a1: "j < dim_col (ψ⇩3 m jd)"
    then have "Matrix.mat (2^m) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..m}. (bin_rep m (of_nat i))!(l-1)/2^l))*1/sqrt(2)^m) $$ (i,j)
    = exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..m}. (bin_rep m (of_nat i))!(l-1)/2^l))*1/sqrt(2)^m" by simp
    then have "Matrix.mat (2^m) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..m}. (bin_rep m (of_nat i))!(l-1)/2^l))*1/sqrt(2)^m) $$ (i,j)
    = exp(complex_of_real(2*pi)*𝗂*jd*((∑l∈{1..m}. (bin_rep m (of_nat i))!(l-1)/2^l)*2^m/2^m))*1/sqrt(2)^m" by simp
    then have "Matrix.mat (2^m) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..m}. (bin_rep m (of_nat i))!(l-1)/2^l))*1/sqrt(2)^m) $$ (i,j)
    = exp(complex_of_real(2*pi)*𝗂*jd*((∑l∈{1..m}. (bin_rep m (of_nat i))!(l-1)/2^l*2^m)*1/2^m))*1/sqrt(2)^m" 
      by (smt sum.cong sum_distrib_right)
    then have "Matrix.mat (2^m) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..m}. (bin_rep m (of_nat i))!(l-1)/2^l))*1/sqrt(2)^m) $$ (i,j)
    = exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..m}. (bin_rep m (of_nat i))!(l-1)*(1/2^l*2^m))*1/2^m)*1/sqrt(2)^m" 
      using mult.commute by simp
    moreover have "(∑l∈{1..m}. (bin_rep m (of_nat i))!(l-1)*(1/2^l*2^m)) = (∑l∈{1..m}. (bin_rep m (of_nat i))!(l-1)*2^(m-l))"
    proof-
      have "l∈{1..m} ⟶ (1/2^l*2^m) = (2::real)^(m-l)" for l::nat by (simp add: power_diff)
      then show ?thesis by simp
    qed
    ultimately have "Matrix.mat (2^m) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..m}. (bin_rep m (of_nat i))!(l-1)/2^l))*1/sqrt(2)^m) $$ (i,j)
    = exp(complex_of_real(2*pi)*𝗂*jd*real (∑l∈{1..m}. (bin_rep m (of_nat i))!(l-1)*2^(m-l))*1/2^m)*1/sqrt(2)^m" 
      by metis
    then have "Matrix.mat (2^m) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..m}. (bin_rep m (of_nat i))!(l-1)/2^l))*1/sqrt(2)^m) $$ (i,j)
    = exp(complex_of_real(2*pi)*𝗂*jd*real i*1/2^m)*1/sqrt(2)^m" 
      using bit_representation[of i m] assms nat_mult_1_right 
      by (metis (mono_tags, lifting) a0 dim_row_mat(1) of_nat_id sum.cong)
    then show "Matrix.mat (2^m) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..m}. (bin_rep m (of_nat i))!(l-1)/2^l))*1/sqrt(2)^m) $$ (i,j)
            = (ψ⇩3 m jd) $$ (i,j)" using a0 a1 by simp
  next
    show "dim_row (Matrix.mat (2^m) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..m}. (bin_rep m (of_nat i))!(l-1)/2^l))*1/sqrt(2)^m))
        = dim_row (ψ⇩3 m jd)" by simp
  next
    show "dim_col (Matrix.mat (2^m) 1 (λ(i,j). exp(complex_of_real(2*pi)*𝗂*jd*(∑l∈{1..m}. (bin_rep m (of_nat i))!(l-1)/2^l))*1/sqrt(2)^m))
        = dim_col (ψ⇩3 m jd)" by simp
  qed
  ultimately show ?thesis by simp
qed

theorem quantum_fourier_transform_matrix_rep:
  assumes "j < 2^m" and "m ≥ 1"
  shows "(QFT m) * |unit_vec (2^m) j⟩ = ψ⇩3 m j" 
  using quantum_fourier_transform_prod_rep assms product_rep_equals_matrix_rep by simp

theorem quantum_fourier_transform_is_state:
  assumes "j < 2^m" and "m ≥ 1"
  shows "state m (ψ⇩3 m j)"
proof-
  have "(QFT m) * |unit_vec (2^m) j⟩ = ψ⇩3 m j" using quantum_fourier_transform_matrix_rep assms by simp
  moreover have "gate m (QFT m)" using assms quantum_fourier_transform_is_gate by simp
  moreover have "state m |unit_vec (2^m) j⟩" 
    using assms(1) 
    by (metis (no_types, lifting) dim_col_mat(1) dim_row_mat(1) index_unit_vec(3) ket_vec_col ket_vec_def state_def unit_cpx_vec_length)
  ultimately show ?thesis
    by (metis gate_on_state_is_state)
qed

end