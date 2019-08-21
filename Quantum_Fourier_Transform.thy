theory Quantum_Fourier_Transform
imports
  More_Tensor
  Binary_Nat
begin

(*Just for convenience*)
locale qft =
  fixes j_dec n::nat (*Can be renamed to j in the end*)
  assumes dom: "j_dec < 2^n"
  assumes dim: "n\<ge>1"

(*Sometimes Nat.nat_induct_at_least does not work (takes wrong induction variable). To temp fix this 
and try out things I used this.*)
lemma ind_from_1:
  fixes n
  assumes "n \<ge> 1"
  assumes "P(1)" 
  assumes "\<And>n. n \<ge> 1 \<Longrightarrow> P n \<Longrightarrow> P (Suc n)"
  shows "P n"
  using nat_induct_at_least assms by auto

(*Use the other defs right now to not worry about ket_vec_def all the time. Can switch to this easily later
abbreviation zero where "zero \<equiv> unit_vec 2 0"
abbreviation one where "one \<equiv> unit_vec 2 1" *)

abbreviation zero where "zero \<equiv> (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1 else 0))"
abbreviation one where "one \<equiv> (Matrix.mat 2 1 (\<lambda>(i,j). if i=1 then 1 else 0))" 




(*------------------------------------------------------------------------------------------------*)
(*---------------Transform j into a tensor product of single qubits ------------------------------*)
(*------------------------------------------------------------------------------------------------*)

(*Gives back a part of j starting at (s+1) being (k+1) qubits long
E.g. $|01011\rangle$, s=1 and k=2 transforms to $[1,0,1]*)
primrec(in qft) j_to_list_bound :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat list" where
"j_to_list_bound s 0 j m = (if (bin_rep m j)!s = 0 then [zero] else [one])" |
"j_to_list_bound s (Suc k) j m = (if (bin_rep m j)!((Suc k)+s) = 0 then zero else one) # (j_to_list_bound s k j m)"

(*TODO: Would exchanging the arguments help with induction problem?*) (*TODO: delete second argument?*)
(*Takes a list and the number of elements in this list and gives out the tensor product of the elements*)
fun pow_tensor_list :: "((complex Matrix.mat) list) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("pw _ _" 75)  where
  "(pw (Cons x []) (Suc 0)) = x"  |
  "(pw (Cons x xs) (Suc k)) = x \<Otimes> (pw xs k)"

(*gives back a part of j as tensor product of single qubits s is the start and t the number of bits
I.e. $|j_1,...,j_n\rangle$ and s=2 and t=3 gives $|j_2,j_3,j_4\rangle$ *)
definition(in qft) j_to_tensor_prod :: "nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>complex Matrix.mat" ("j\<Otimes> _ _ _ _" 75) where 
"(j\<Otimes> s t j m) = pw (j_to_list_bound (s-1) (t-1) j m) (s+t-1)"

(*Missing: result is gate, state,... Easy to proof*)

lemma pow_tensor_list_dim_col:
  assumes "k \<ge> 1" and "length xs = k"
  shows "(\<forall>x \<in> set xs. dim_col x = 1) \<longrightarrow> dim_col (pw xs k) = 1"
proof-
  have "\<forall>xs. length xs = k \<longrightarrow> (\<forall>x \<in> set xs. dim_col x = 1) \<longrightarrow> dim_col (pw xs k) = 1"
  proof(rule ind_from_1[of k])
    show "k \<ge> 1" using assms by auto
  next
    show "\<forall>xs. length xs = 1 \<longrightarrow> (\<forall>x \<in> set xs. dim_col x = 1) \<longrightarrow> dim_col (pw xs 1) = 1"
    proof(rule allI, rule impI, rule impI)
      fix xs::"(complex Matrix.mat) list" 
      assume a0: "length xs = 1"
      assume a1: "(\<forall>x \<in> set xs. dim_col x = 1)"
      have "\<exists>x. xs = [x]" using a0 
        by (metis One_nat_def Suc_length_conv length_0_conv)
      moreover have "xs = [x] \<longrightarrow> dim_col (pw xs 1) = 1" for x
      proof
        assume a2: "xs = [x]"
        then have "dim_col (pw xs 1) = dim_col (x)" by auto
        then show "dim_col (pw xs 1) = 1" using a1 by (simp add: a2)
      qed
      ultimately show "dim_col (pw xs 1) = 1" using a1 by force
    qed
  next
    fix k
    assume IH: "\<forall>xs. length xs = k \<longrightarrow> (\<forall>x \<in> set xs. dim_col x = 1) \<longrightarrow> dim_col (pw xs k) = 1"
    show "\<forall>xs. length xs = (Suc k) \<longrightarrow> (\<forall>x \<in> set xs. dim_col x = 1) \<longrightarrow> dim_col (pw xs (Suc k)) = 1"
    proof(rule allI, rule impI, rule impI)
      fix xs::"(complex Matrix.mat) list" 
      assume a0: "length xs = (Suc k)"
      assume a1: "(\<forall>x \<in> set xs. dim_col x = 1)"
      have "\<exists>x. xs = x # tl xs" using a0 by (metis length_Suc_conv list.sel(3))
      moreover have "xs = x # tl xs \<longrightarrow> dim_col (pw xs (Suc k)) = 1" for x
      proof
        assume a2: "xs = x # tl xs"
        then have "dim_col (pw xs (Suc k)) = dim_col (x \<Otimes> (pw (tl xs) k))" using pow_tensor_list.simps 
          by (metis IH One_nat_def a0 a1 diff_Suc_1 dim_col_tensor_mat length_Cons list.exhaust list.inject list.sel(3) 
            list.set_intros(1) list.set_sel(2) list.size(3) semiring_normalization_rules(12))
        then have "dim_col (pw xs (Suc k)) = 1 * dim_col ((pw (tl xs) k))" using a0 a1 a2 by (metis dim_col_tensor_mat list.set_intros(1))
        then show "dim_col (pw xs (Suc k)) = 1" using a0 IH by (metis a1 diff_Suc_1 length_0_conv length_tl list.set_sel(2) mult.right_neutral nat.simps(3))
      qed
      ultimately show "dim_col (pw xs (Suc k)) = 1" by auto
    qed
  qed
  then show ?thesis using assms by auto
qed

lemma pow_tensor_list_dim_row: 
  assumes "k \<ge> 1" and "length xs = k" and "(\<forall>x \<in> set xs. dim_row x = m)"
  shows "dim_row (pw xs k) = m^k"
proof-
  have "\<forall>xs. length xs = k \<longrightarrow> (\<forall>x \<in> set xs. dim_row x = m) \<longrightarrow> dim_row (pw xs k) = m^k"
  proof(rule ind_from_1[of k])
    show "k \<ge> 1" using assms by auto
  next
    show "\<forall>xs. length xs = 1 \<longrightarrow> (\<forall>x \<in> set xs. dim_row x = m) \<longrightarrow> dim_row (pw xs 1) = m^1"
    proof(rule allI, rule impI, rule impI)
      fix xs::"(complex Matrix.mat) list" 
      assume a0: "length xs = 1"
      assume a1: "(\<forall>x \<in> set xs. dim_row x = m)"
      have "\<exists>x. xs = [x]" using a0 
        by (metis One_nat_def Suc_length_conv length_0_conv)
      moreover have "xs = [x] \<longrightarrow> dim_row (pw xs 1) = m" for x
      proof
        assume a2: "xs = [x]"
        then have "dim_row (pw xs 1) = dim_row (x)" by auto
        then show "dim_row (pw xs 1) = m" using a1 by (simp add: a2)
      qed
      ultimately show "dim_row (pw xs 1) = m^1" using a1 by force
    qed
  next
    fix k
    assume IH: "\<forall>xs. length xs = k \<longrightarrow> (\<forall>x \<in> set xs. dim_row x = m) \<longrightarrow> dim_row (pw xs k) = m^k"
    show "\<forall>xs. length xs = (Suc k) \<longrightarrow> (\<forall>x \<in> set xs. dim_row x = m) \<longrightarrow> dim_row (pw xs (Suc k)) = m^(Suc k)"
    proof(rule allI, rule impI, rule impI)
      fix xs::"(complex Matrix.mat) list" 
      assume a0: "length xs = (Suc k)"
      assume a1: "(\<forall>x \<in> set xs. dim_row x = m)"
      have "\<exists>x. xs = x # tl xs" using a0 by (metis length_Suc_conv list.sel(3))
      moreover have "xs = x # tl xs \<longrightarrow> dim_row (pw xs (Suc k)) = m^(Suc k)" for x
      proof
        assume a2: "xs = x # tl xs"
        moreover have f1: "length (tl xs) = k" using a0 by force
        moreover have "tl xs = [] \<longrightarrow> dim_row (x \<Otimes> pw tl xs k) = dim_row (pw xs Suc k)" 
          using IH a2 f1 by auto 
        ultimately have "dim_row (pw xs (Suc k)) = dim_row (x \<Otimes> (pw (tl xs) k))" using pow_tensor_list.simps 
          using f1 by (metis (full_types) Nitpick.size_list_simp(2) a2 dim_row_tensor_mat mult.commute pow_tensor_list.simps(3))
        then have "dim_row (pw xs (Suc k)) = m * dim_row ((pw (tl xs) k))" 
          using a1 a2 by (metis dim_row_tensor_mat list.set_intros(1))
        then show "dim_row (pw xs (Suc k)) = m^(Suc k)" 
          by (metis IH a0 a1 f1 length_0_conv list.set_sel(2) mult.commute nat.simps(3) power_Suc)
      qed
      ultimately show "dim_row (pw xs (Suc k)) = m^(Suc k)" by auto
    qed
  qed
  then show ?thesis using assms by auto
qed

lemma pow_tensor_app_left:
  fixes k::nat
  and x::"complex Matrix.mat" 
  assumes "k\<ge>1" 
  shows "\<forall>xs. length xs = k \<longrightarrow> (pw xs k) \<Otimes> x = pw (xs@[x]) (k+1)" 
proof(rule ind_from_1[of k])
  show "k\<ge>1" using assms by auto
next
  show "\<forall>xs. length xs = 1 \<longrightarrow> (pw xs 1) \<Otimes> x = pw (xs@[x]) (1+1)" 
  proof(rule allI, rule impI)
    fix xs::"complex Matrix.mat list"
    assume a0: "length xs = 1"
    moreover have "xs=[y] \<longrightarrow> pw (xs@[x]) (1+1) = (pw xs 1) \<Otimes> x" for y::"complex Matrix.mat" by auto
    ultimately show "(pw xs 1) \<Otimes> x = pw (xs@[x]) (1+1)" 
      by (metis One_nat_def length_0_conv length_Suc_conv)
  qed
next
  fix k::nat
  assume a0: "k\<ge>1" 
  assume IH: "\<forall>xs. length xs = k \<longrightarrow> (pw xs k) \<Otimes> x = pw (xs@[x]) (k+1)" 
  show "\<forall>xs. length xs = (Suc k) \<longrightarrow> (pw xs (Suc k)) \<Otimes> x = pw (xs@[x]) ((Suc k)+1)" 
  proof(rule allI, rule impI)
    fix xs::"complex Matrix.mat list"
    assume a1: "length xs = (Suc k)"
    moreover have "xs=(y#ys) \<longrightarrow> pw (xs@[x]) ((Suc k)+1) = (pw xs (Suc k)) \<Otimes> x" 
      for y::"complex Matrix.mat" and ys::"complex Matrix.mat list"
    proof
      assume a2: "xs=y#ys"
      then have "pw (xs@[x]) ((Suc k)+1) = y \<Otimes> pw (ys@[x]) (k+1)" by simp
      moreover have "length ys = k" using a2 using a1 by auto 
      ultimately have "pw (xs@[x]) ((Suc k)+1) = y \<Otimes> ((pw ys k) \<Otimes> x)" using IH by auto
      then have "pw (xs@[x]) ((Suc k)+1) = (y \<Otimes> (pw ys k)) \<Otimes> x" using tensor_mat_is_assoc by auto
      then have "pw (xs@[x]) ((Suc k)+1) = (pw (y#ys) (Suc k)) \<Otimes> x" using pow_tensor_list.simps 
        by (metis One_nat_def Suc_pred a0 less_eq_Suc_le) 
      then show "pw (xs@[x]) ((Suc k)+1) = (pw xs (Suc k)) \<Otimes> x" using a2 by auto
    qed
    ultimately show "(pw xs (Suc k)) \<Otimes> x = pw (xs@[x]) ((Suc k)+1)" by (metis Suc_length_conv)
  qed
qed

lemma pow_tensor_app_right:
  assumes "k\<ge>1" and "length xs = k"
  shows "x \<Otimes> (pw xs k) = pw (x#xs) (k+1)" 
  using Suc_le_D assms(1) by force


lemma temp1:
  fixes k::nat
  assumes "k>1" and "m<2^(k-1)"
  shows "|unit_vec (2^k) m\<rangle> = zero \<Otimes> |unit_vec (2^(k-1)) m\<rangle>"
proof
  fix i j::nat
  assume a0: "i < dim_row (zero \<Otimes> |unit_vec (2^(k-1)) m\<rangle>)"
  and a1: "j < dim_col (zero \<Otimes> |unit_vec (2^(k-1)) m\<rangle>)"
  then have f0: "i < 2^k" using ket_vec_def unit_vec_def zero_def 
  proof -
    have "(2::nat) ^ k = 2 * 2 ^ (k - 1)"
      by (metis (no_types) assms(1) gr_implies_not0 power_eq_if)
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
  show  "dim_row |unit_vec (2 ^ k) m\<rangle> = dim_row (Quantum_Fourier_Transform.zero \<Otimes> |unit_vec (2 ^ (k - 1)) m\<rangle>)" sorry
next
  show " dim_col |unit_vec (2 ^ k) m\<rangle> = dim_col (Quantum_Fourier_Transform.zero \<Otimes> |unit_vec (2 ^ (k - 1)) m\<rangle>)" sorry
qed


lemma temp2:
  fixes k::nat
  assumes "k>1"
  shows "m\<ge>2^(k-1) \<and> m<2^k \<longrightarrow> |unit_vec (2^k) m\<rangle> = one \<Otimes> |unit_vec (2^(k-1)) (m mod 2)\<rangle>"
  sorry


lemma(in qft) j_as_unit:
  fixes k j m::nat
  assumes "k\<ge>1"
  shows "(j\<Otimes> 1 k j m) = |unit_vec (2^k) (j mod 2^k)\<rangle>"
proof(rule ind_from_1[of k])
  show "k\<ge>1" using assms by auto
next
  have "(bin_rep m j)!0 = 0 \<longrightarrow> (j\<Otimes> 1 1 j m) = zero"
    using pow_tensor_list.simps j_to_tensor_prod_def by auto
  moreover have "(bin_rep m j)!0 = 1 \<longrightarrow> (j\<Otimes> 1 1 j m) = one"
    using pow_tensor_list.simps j_to_tensor_prod_def by auto
  moreover have "(bin_rep m j)!0 = 0 \<longrightarrow> j mod 2^1 = 0" sorry 
  moreover have "(bin_rep m j)!0 = 1 \<longrightarrow> j mod 2^1 = 1" sorry 
  moreover have "|unit_vec (2^1) 0\<rangle> = zero" sorry
  moreover have "|unit_vec (2^1) 1\<rangle> = one" sorry
  ultimately show "(j\<Otimes> 1 1 j m) = |unit_vec (2^1) (j mod 2^1)\<rangle>"
    using ket_vec_def unit_vec_def sorry
next
  fix k::nat
  assume a0: "k\<ge>1"
     and IH: "(j\<Otimes> 1 k j m) = |unit_vec (2^k) (j mod 2^k)\<rangle>"
  have f0: "(j\<Otimes> 1 (Suc k) j m) = pw (j_to_list_bound 0 k j m) (Suc k)" 
    using j_to_tensor_prod_def a0 by auto
  show "(j\<Otimes> 1 (Suc k) j m) = |unit_vec (2^(Suc k)) (j mod 2^(Suc k))\<rangle>"
  proof(rule disjE)
    show "(bin_rep m j)!k = 0 \<or> (bin_rep m j)!k = 1" sorry
  next
    assume a1: "(bin_rep m j)!k = 0"
    then have "bin_rep m j ! (Suc (k - 1)) = 0"
      by (metis (no_types) One_nat_def Suc_diff_le a1 a0 diff_Suc_Suc minus_nat.diff_0)
    then have "j_to_list_bound 0 (Suc (k - 1)) j m = zero # j_to_list_bound 0 (k - 1) j m" 
      using j_to_list_bound.simps by auto
    then have "(j_to_list_bound 0 k j m) = zero # (j_to_list_bound 0 (k-1) j m)" 
      using j_to_list_bound.simps f0 a0     
      by (metis (no_types) One_nat_def Suc_diff_le a0 diff_Suc_Suc minus_nat.diff_0)
    then have "(j\<Otimes> 1 (Suc k) j m) = pw (zero # (j_to_list_bound 0 (k-1) j m)) (Suc k)" 
      using f0 by auto 
    then have "(j\<Otimes> 1 (Suc k) j m) = zero \<Otimes> (pw (j_to_list_bound 0 (k-1) j m) k)" 
      using pow_tensor_list.simps a0 by (metis le_add_diff_inverse plus_1_eq_Suc)
    then have "(j\<Otimes> 1 (Suc k) j m) = zero \<Otimes> (j\<Otimes> 1 k j m)" 
      using j_to_tensor_prod_def a0 by auto
    then have "(j\<Otimes> 1 (Suc k) j m) = zero \<Otimes> |unit_vec (2^k) (j mod 2^k)\<rangle>" 
      using IH by auto
    then have "(j\<Otimes> 1 (Suc k) j m) = |unit_vec (2^(k+1)) (j mod 2^k)\<rangle>" using temp1 sorry
    moreover have "j < 2^k" sorry 
    moreover have "j mod 2^k = j mod 2^(k-1)" sorry
    ultimately show "(j\<Otimes> 1 (Suc k) j m) = |unit_vec (2^(Suc k)) (j mod 2^(Suc k))\<rangle>" sorry
  next
    assume a1: "(bin_rep m j)!k = 1"
    then show "(j\<Otimes> 1 (Suc k) j m) = |unit_vec (2^(Suc k)) (j mod 2^(Suc k))\<rangle>" sorry
  qed
qed



lemma(in qft) j_dec_as_unit:
  shows "(j\<Otimes> 1 n j_dec n) = |unit_vec (2^n) j_dec\<rangle>"
proof-
  have "(j\<Otimes> 1 n j_dec n) = |unit_vec (2^n) (j_dec mod 2^n)\<rangle>" using dim j_as_unit by auto
  moreover have "j_dec mod 2^n = j_dec" using dom by auto
  ultimately show ?thesis by auto
qed

(*lemma(in qft)
  assumes "k\<ge>1" and "m\<ge>1"
  shows "\<forall>j m. j\<le>k \<and> j\<le>m \<longrightarrow> (j\<Otimes> 1 k j m) = |unit_vec (2^k) j\<rangle>" 
proof(rule ind_from_1[of k])
  show "\<forall>j m. j\<le>1 \<and> j\<le>m \<longrightarrow> (j\<Otimes> 1 1 j m) = |unit_vec (2^1) j\<rangle>"
  proof(rule allI, rule allI, rule impI)
    fix j m::nat
    assume a0: "j\<le>1 \<and> j\<le>m"
    show "(j\<Otimes> 1 1 j m) = |unit_vec (2^1) j\<rangle>"
    proof(rule disjE)
      show "j=0 \<or> j=1" using a0 by auto
    next
      assume a1: "j=0"
      have "(j\<Otimes> 1 1 j m) = pow_tensor_list (j_to_list_bound 0 0 j m) 1" using j_to_tensor_prod_def by auto
      moreover have "(bin_rep m j)!0 = 0" using a0 a1 assms sorry
      ultimately have "(j\<Otimes> 1 1 j m) = zero" using j_to_list_bound_def a1 by auto
      then show "(j\<Otimes> 1 1 j m) = |unit_vec (2^1) j\<rangle>" using a1 ket_vec_def by auto
    next
      assume a1: "j=1"
      have "(j\<Otimes> 1 1 j m) = pow_tensor_list (j_to_list_bound 0 0 j m) 1" using j_to_tensor_prod_def by auto
      moreover have "(bin_rep m j)!0 = 1" using a0 a1 assms sorry
      ultimately have "(j\<Otimes> 1 1 j m) = one" using j_to_list_bound_def by auto
      then show "(j\<Otimes> 1 1 j m) = |unit_vec (2^1) j\<rangle>" using a1 ket_vec_def by auto
    qed
  qed
next
  fix k 
  assume a0: "k\<ge>1"
     and IH: "\<forall>j m. j\<le>k \<and> j\<le>m \<longrightarrow> (j\<Otimes> 1 k j m) = |unit_vec (2^k) j\<rangle>" 
  show "\<forall>j m. j\<le>(Suc k) \<and> j\<le>m \<longrightarrow> (j\<Otimes> 1 (Suc k) j m) = |unit_vec (2^(Suc k)) j\<rangle>" 
  proof (rule allI, rule allI, rule impI)
    fix j m 
    assume a1: "j\<le>(Suc k) \<and> j\<le>m" 
    then have "(j\<Otimes> 1 (Suc k) j m) = pow_tensor_list (j_to_list_bound 0 k j m) (k+1)" 
      using j_to_tensor_prod_def assms by auto
    then have "(bin_rep (Suc m) j)!m = 0 \<longrightarrow> 
               pow_tensor_list (j_to_list_bound 0 k j m) (k+1) 
             = zero \<Otimes> pow_tensor_list (j_to_list_bound 0 (k-1) j m) k"
    proof -
      have f1: "Suc 0 \<le> k"
        using a0 by presburger
      have "bin_rep m j ! (Suc (k - 1) + 0) = 0 \<longrightarrow> j_to_list_bound 0 (Suc (k - 1)) j m 
          = zero # j_to_list_bound 0 (k - 1) j m"
        using j_to_list_bound.simps(2) by presburger
      then have "(bin_rep m j)!k = 0 \<longrightarrow> pow_tensor_list (j_to_list_bound 0 k j m) (1+k) 
             = zero \<Otimes> pow_tensor_list (j_to_list_bound 0 (k-1) j m) k"
        using f1 pow_tensor_list.simps 
        by (smt add.right_neutral ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc)
      then have "(bin_rep m j)!k = 0 \<longrightarrow> pow_tensor_list (j_to_list_bound 0 k j m) (1+k) 
             = zero \<Otimes> (j\<Otimes> 1 k j m)" using j_to_tensor_prod_def by auto
      moreover have "j \<le> k \<and> j \<le>m" sorry 
      ultimately have "(bin_rep m j)!k = 0 \<longrightarrow> pow_tensor_list (j_to_list_bound 0 k j m) (1+k) 
             = zero \<Otimes> |unit_vec (2^k) j\<rangle>" using IH by simp
    qed
    moreover have "(bin_rep (Suc m) j)!m = 1 \<longrightarrow> 
               pow_tensor_list (j_to_list_bound 0 m j (Suc m)) (1+m) 
             = pow_tensor_list (one # (j_to_list_bound 0 (m-1) j (Suc m))) (1+m)"
    proof -
      have f1: "Suc 0 \<le> m"
        using a0 by presburger
      have "bin_rep (Suc m) j ! (Suc (m - 1) + 0) = 1 \<longrightarrow> j_to_list_bound 0 (Suc (m - 1)) j (Suc m) = one # j_to_list_bound 0 (m - 1) j (Suc m)"
        using j_to_list_bound.simps(2) by presburger
      then show ?thesis
        using f1 by simp
    qed
    moreover have "
*)
lemma
(j_to_list_bound 0 m j (Suc m))
"j_to_list_bound 0 (Suc k) j (Suc m) = (if (bin_rep (Suc m) j)!((Suc k)) = 0 then zero else one) # (j_to_list_bound 0 k j (Suc m))"


lemma(in qft)
  shows "(j\<Otimes> 1 n) = |unit_vec n j_dec\<rangle>" 


(*------------------------------------------------------------------------------------------------*)
(*-------------------------------Controlled phase gate CR ----------------------------------------*)
(*------------------------------------------------------------------------------------------------*)

definition(in qft) binary_fraction::"nat \<Rightarrow> nat \<Rightarrow> complex" ("bf _ _") where
"binary_fraction l m \<equiv> (\<Sum>i\<in>{l..m}. ((bin_rep n j_dec)!i) /2^(i-l+1) )"

definition controlled_phase_shift:: " nat \<Rightarrow> complex Matrix.mat" ("CR _") where
"CR k \<equiv> Matrix.mat 4 4 (\<lambda>(i,j). if i = j then (if i = 2 then (exp (2*pi*\<i>*1/2^k)) else 1) else 0)"

(*Missing: CR is gate*)

lemma(in qft) exp_mult: 
  fixes r::nat
  shows "(exp (2*pi*\<i>*(bf 0 r))) * (exp (2*pi*\<i>*((bin_rep n j_dec)!(r+1))/2^(r+2)))
        = (exp (2*pi*\<i>*(bf 0 (r+1))))" 
proof-
  have "(exp (2*pi*\<i>*(bf 0 r))) * (exp (2*pi*\<i>*((bin_rep n j_dec)!(r+1))/2^(r+2)))
      = exp (2*pi*\<i>*(bf 0 r) + 2*pi*\<i>*((bin_rep n j_dec)!(r+1))/2^(r+2))" 
    by (simp add: exp_add)
  moreover have "2*pi*\<i>*(bf 0 r) + 2*pi*\<i>*((bin_rep n j_dec)!(r+1))/2^(r+2)
      = 2*pi*\<i>*((bf 0 r)+((bin_rep n j_dec)!(r+1))/2^(r+2))" 
    using comm_semiring_class.distrib[of "(bf 0 r)" "((bin_rep n j_dec)!(r+1))/2^(r+2)" "(2*pi*\<i>)::complex"] 
    by (simp add: mult.commute)
  moreover have "2*pi*\<i>*((bf 0 r)+((bin_rep n j_dec)!(r+1))/2^(r+2)) = 2*pi*\<i>*(bf 0 (r+1))"
  proof-
    have "(bf 0 r)+((bin_rep n j_dec)!(r+1))/2^(r+2) = (\<Sum>i\<in>{0..r}. ((bin_rep n j_dec)!i) /2^(i-0+1)) + ((bin_rep n j_dec)!(r+1))/2^(r+2)" 
      using binary_fraction_def by auto
    moreover have "(\<Sum>i\<in>{0..r}. ((bin_rep n j_dec)!i) /2^(i-0+1)) + ((bin_rep n j_dec)!(r+1))/2^(r+2) 
                  =(\<Sum>i\<in>{0..(r+1)}. ((bin_rep n j_dec)!i) /2^(i-0+1))" by simp
    moreover have "(\<Sum>i\<in>{0..(r+1)}. ((bin_rep n j_dec)!i) /2^(i-0+1)) = bf 0 (r+1)" using binary_fraction_def by auto
    ultimately show "2*pi*\<i>*((bf 0 r)+((bin_rep n j_dec)!(r+1))/2^(r+2)) = 2*pi*\<i>*(bf 0 (r+1))" by auto
  qed
  ultimately show "(exp (2*pi*\<i>*(bf 0 r))) * (exp (2*pi*\<i>*((bin_rep n j_dec)!(r+1))/2^(r+2)))
                 = (exp (2*pi*\<i>*(bf 0 (r+1))))" by auto
qed

(*Find appropriate name*)
definition(in qft) qr::"nat \<Rightarrow> complex Matrix.mat" where 
"qr k \<equiv> (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then (1::complex)/sqrt(2) else (exp (complex_of_real (2*pi)*\<i>*(bf 0 k)))*1/sqrt(2)))"

(*I did this proof ad hoc there is certainly a much nicer one*)
lemma(in qft) app_controlled_phase_shift_zero:
  fixes r::nat
  assumes "r < n" and "((bin_rep n j_dec)!(r+1)) = 1"
  shows "(CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>) = (qr (r+1)) \<Otimes> |zero\<rangle>"
proof
  fix i j::nat
  assume "i < Matrix.dim_row ((qr (r+1)) \<Otimes> |zero\<rangle>)" and "j < Matrix.dim_col ((qr (r+1)) \<Otimes> |zero\<rangle>)" 
  then have f0: "i<4 \<and> j=0" using ket_vec_def qr_def  by auto
  then have "((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) $$ (i,j) 
           = (\<Sum>k\<in>{0,1,2,3}. ((CR (r+2)) $$ (i,k)) * (((qr r) \<Otimes> |zero\<rangle>) $$ (k,j)))" 
    using f0 ket_vec_def qr_def set_4 atLeast0LessThan controlled_phase_shift_def by auto
  then have f1: "((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) $$ (i,j) 
           = ((CR (r+2)) $$ (i,0)) * (1::complex)/sqrt(2)
           + ((CR (r+2)) $$ (i,2)) * exp (complex_of_real (2*pi) *\<i>*(bf 0 r))*1/sqrt(2)" 
    using f0 ket_vec_def qr_def by auto
  moreover have "i=0 \<longrightarrow> ((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) $$ (i,j) = 1/sqrt(2)"
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=0 \<longrightarrow> ((qr (r+1)) \<Otimes> |zero\<rangle>) $$ (i,j) = 1/sqrt(2)" 
    using qr_def ket_vec_def f0 by auto
  moreover have "i=1 \<longrightarrow> ((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) $$ (i,j) = 0"
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=1 \<longrightarrow> ((qr (r+1)) \<Otimes> |zero\<rangle>) $$ (i,j) = 0" 
    using qr_def ket_vec_def f0 by auto
  moreover have "i=2 \<longrightarrow> ((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) $$ (i,j) 
           = (exp (complex_of_real (2*pi)*\<i>*(bf 0 (r+1)))) *1/sqrt(2)" 
  proof-
   have "i=2 \<longrightarrow> ((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) $$ (i,j) 
           = (exp (complex_of_real (2*pi)*\<i>*(bf 0 r))) * (exp (complex_of_real (2*pi)*\<i>*1/2^(r+2))) * 1/sqrt(2)" 
      using controlled_phase_shift_def f1 by auto
   moreover have "exp (complex_of_real (2*pi)*\<i>*1/2^(r+2)*(bin_rep n j_dec)!(r+1)) = exp (complex_of_real (2*pi)*\<i>*1/2^(r+2)) " using assms by auto
   ultimately show "i=2 \<longrightarrow> ((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) $$ (i,j) 
           = (exp (complex_of_real (2*pi)*\<i>*(bf 0 (r+1)))) * 1/sqrt(2)" using exp_mult by (smt assms(2) of_nat_1)
 qed
  moreover have "i=2 \<longrightarrow> ((qr (r+1)) \<Otimes> |zero\<rangle>) $$ (i,j) = exp (complex_of_real (2*pi)*\<i>*(bf 0 (r+1)))*1/sqrt(2)" 
    using qr_def ket_vec_def f0 by auto
  moreover have "i=3 \<longrightarrow> ((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) $$ (i,j) = 0"
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=3 \<longrightarrow> ((qr (r+1)) \<Otimes> |zero\<rangle>) $$ (i,j) = 0" 
    using qr_def ket_vec_def f0 by auto
  moreover have "i\<in>{0,1,2,3}" using f0 by auto
  ultimately show "((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) $$ (i,j) = ((qr (r+1)) \<Otimes> |zero\<rangle>) $$ (i,j)" 
    using f0 ket_vec_def qr_def by (smt set_four)
  fix i j::nat
  assume "i < Matrix.dim_row ((qr (r+1)) \<Otimes> |zero\<rangle>)" and "j < Matrix.dim_col ((qr (r+1)) \<Otimes> |zero\<rangle>)" 
  then have f0: "i<4 \<and> j=0" using ket_vec_def qr_def  by auto
  then have "((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) $$ (i,j) 
           = (\<Sum>k\<in>{0,1,2,3}. ((CR (r+2)) $$ (i,k)) * (((qr r) \<Otimes> |zero\<rangle>) $$ (k,j)))" 
    using f0 ket_vec_def qr_def set_4 atLeast0LessThan controlled_phase_shift_def by auto
  then have f1: "((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) $$ (i,j) 
           = ((CR (r+2)) $$ (i,0)) * (1::complex)/sqrt(2)
           + ((CR (r+2)) $$ (i,2)) * exp (complex_of_real (2*pi) *\<i>*(bf 0 r))*1/sqrt(2)" 
    using f0 ket_vec_def qr_def by auto
  moreover have "i=0 \<longrightarrow> ((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) $$ (i,j) = 1/sqrt(2)"
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=0 \<longrightarrow> ((qr (r+1)) \<Otimes> |zero\<rangle>) $$ (i,j) = 1/sqrt(2)" 
    using qr_def ket_vec_def f0 by auto
  moreover have "i=1 \<longrightarrow> ((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) $$ (i,j) = 0"
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=1 \<longrightarrow> ((qr (r+1)) \<Otimes> |zero\<rangle>) $$ (i,j) = 0" 
    using qr_def ket_vec_def f0 by auto
  moreover have "i=2 \<longrightarrow> ((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) $$ (i,j) 
           = (exp (complex_of_real (2*pi)*\<i>*(bf 0 (r+1)))) *1/sqrt(2)" 
  proof-
   have "i=2 \<longrightarrow> ((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) $$ (i,j) 
           = (exp (complex_of_real (2*pi)*\<i>*(bf 0 r))) * (exp (complex_of_real (2*pi)*\<i>*1/2^(r+2))) * 1/sqrt(2)" 
      using controlled_phase_shift_def f1 by auto
   moreover have "exp (complex_of_real (2*pi)*\<i>*1/2^(r+2)*(bin_rep n j_dec)!(r+1)) = exp (complex_of_real (2*pi)*\<i>*1/2^(r+2)) " using assms by auto
   ultimately show "i=2 \<longrightarrow> ((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) $$ (i,j) 
           = (exp (complex_of_real (2*pi)*\<i>*(bf 0 (r+1)))) * 1/sqrt(2)" using exp_mult by (smt assms(2) of_nat_1)
  qed
  moreover have "i=2 \<longrightarrow> ((qr (r+1)) \<Otimes> |zero\<rangle>) $$ (i,j) = exp (complex_of_real (2*pi)*\<i>*(bf 0 (r+1)))*1/sqrt(2)" 
    using qr_def ket_vec_def f0 by auto
  moreover have "i=3 \<longrightarrow> ((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) $$ (i,j) = 0"
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=3 \<longrightarrow> ((qr (r+1)) \<Otimes> |zero\<rangle>) $$ (i,j) = 0" 
    using qr_def ket_vec_def f0 by auto
  moreover have "i\<in>{0,1,2,3}" using f0 by auto
  ultimately show "((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) $$ (i,j) = ((qr (r+1)) \<Otimes> |zero\<rangle>) $$ (i,j)" 
    using f0 ket_vec_def qr_def by (smt set_four)
next
  show "dim_row ((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) = dim_row ((qr (r+1)) \<Otimes> |zero\<rangle>)" 
    by (simp add: controlled_phase_shift_def ket_vec_def qr_def)
next
  show "dim_col ((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) = dim_col ((qr (r+1)) \<Otimes> |zero\<rangle>)"
    using ket_vec_def controlled_phase_shift_def qr_def by auto
qed

lemma(in qft) app_controlled_phase_shift_one: 
  fixes r::nat
  assumes "r < n" and "((bin_rep n j)!(r+1)) = 0"
  shows"(CR (r+2)) * ((qr r) \<Otimes> |one\<rangle>) = (qr (r+1)) \<Otimes> |one\<rangle>"
  sorry


(*The idea is to apply the controlled R gate only to the tensor product of two single qubits. The first qubit is 
already at the current position. This is the qubit we want to apply the R_j gate too. The second qubit is "hidden" 
in the unit vector (which is just a tensor product of single qubit where the qubit at position j is the one we need). 
Thus, we repeatedly swap qubit j with the qubit in front of it until it directly follows the current qubit. Then, 
we can apply the controlled R gate which leaves the second qubit untouched (see proofs above). Then we can switch the
qubit back to its original position. *)
definition(in qft) SWAP :: "complex Matrix.mat" where
"SWAP \<equiv> Matrix.mat 4 4 (\<lambda>(i,j). if i=0 \<and> j=0 then 1 else 
                                (if i=1 \<and> j=2 then 1 else 
                                (if i=2 \<and> j=1 then 1 else 
                                (if i=3 \<and> j=3 then 1 else 0))))"

lemma(in qft) app_SWAP:
  assumes "dim_row v = 2" and "dim_col v = 1"
      and "dim_row w = 2" and "dim_col w = 1"
  shows "SWAP * (v \<Otimes> w) = w \<Otimes> v"
  sorry

definition(in qft) SWAP_all :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
"SWAP_all k t \<equiv> if k>1 then (Id k) \<Otimes> SWAP \<Otimes> (Id t) else SWAP \<Otimes> (Id t)"

lemma(in qft) SWAP_all_dim:
  shows "dim_row (SWAP_all k t) = 2^(k+2+t)"
    and "dim_col (SWAP_all k t) = 2^(k+2+t)"    
  sorry

lemma(in qft) app_SWAP_all:
  assumes "k>1" and "t\<ge>1"
      and "dim_row v = 2" and "dim_row w = 2" 
      and "dim_col v = 1" and "dim_col w = 1" 
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
    using Id_def assms pow_tensor_list_dim_row[of t ys 2] by (simp add: SWAP_def)
  moreover have "dim_col (Id k) > 0" and "dim_col (SWAP \<Otimes> (Id t)) > 0" and
                "dim_col (pw xs k) > 0" and "dim_col (v \<Otimes> w \<Otimes> (pw ys t)) > 0" 
    apply (auto simp: Id_def SWAP_def assms pow_tensor_list_dim_col[of k xs] pow_tensor_list_dim_col[of t ys])
    using assms(1) assms(11) assms(7) pow_tensor_list_dim_col apply auto[1]
    using assms(12) assms(2) assms(8) pow_tensor_list_dim_col by auto
  ultimately have "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) =
              ((Id k)*(pw xs k)) \<Otimes> ((SWAP \<Otimes> (Id t)) * (v \<Otimes> w \<Otimes> (pw ys t)))"
    using mult_distr_tensor by auto
  then have "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) =
             ((pw xs k)) \<Otimes> ((SWAP \<Otimes> (Id t)) * (v \<Otimes> w \<Otimes> (pw ys t)))" 
    using Id_def \<open>dim_col (Id k) = dim_row (pw xs k)\<close> by auto
  moreover have "dim_col SWAP = dim_row (v \<Otimes> w)" using assms by (simp add: SWAP_def)
  moreover have "dim_col (Id t) = dim_row (pw ys t)" using Id_def pow_tensor_list_dim_row[of t ys] assms 
    by (metis index_one_mat(3) pow_tensor_list_dim_row)
  moreover have "dim_col SWAP > 0" and "dim_col (v \<Otimes> w) > 0" and "dim_col (Id t) > 0" and "dim_col (pw ys t) > 0" 
    apply (auto simp: SWAP_def assms Id_def pow_tensor_list_dim_col[of t ys]) 
    using assms(12) assms(2) assms(8) pow_tensor_list_dim_col by auto
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

lemma(in qft) app_SWAP_all_fst_empty:
  assumes "k=1" and "t\<ge>1"
      and "dim_row v = 2" and "dim_row w = 2" 
      and "dim_col v = 1" and "dim_col w = 1" 
      and "length ys = t"
      and "\<forall>y \<in> set ys. dim_row y = 2" and "\<forall>y \<in> set ys. dim_col y = 1"
  shows "(SWAP_all k t) * (v \<Otimes> w \<Otimes> (pw ys t)) = (w \<Otimes> v \<Otimes> (pw ys t))"
proof-
  have "(SWAP_all k t) * (v \<Otimes> w \<Otimes> (pw ys t)) = (SWAP \<Otimes> (Id t)) * (v \<Otimes> w \<Otimes> (pw ys t))"
    using assms SWAP_all_def by auto
  moreover have "dim_row SWAP = dim_row (v \<Otimes> w)" using assms by (simp add: SWAP_def)
  moreover have "dim_col (Id t) = dim_row (pw ys t)" using Id_def pow_tensor_list_dim_row[of t ys 2] assms by auto
  moreover have "dim_col SWAP > 0" and "dim_col (v \<Otimes> w) > 0" 
            and "dim_col (Id t) > 0" and "dim_col (pw ys t) > 0" sorry
  ultimately have "(SWAP_all k t) * (v \<Otimes> w \<Otimes> (pw ys t)) = (SWAP * (v \<Otimes> w)) \<Otimes> ((Id t) * (pw ys t))"
    using tensor_mat_is_assoc by (simp add: SWAP_def mult_distr_tensor)
  then have "(SWAP_all k t) * (v \<Otimes> w \<Otimes> (pw ys t)) = (w \<Otimes> v) \<Otimes> ((Id t) * (pw ys t))"
    using assms app_SWAP by auto
  then show "(SWAP_all k t) * (v \<Otimes> w \<Otimes> (pw ys t)) = w \<Otimes> v \<Otimes> (pw ys t)"
    using Id_def \<open>dim_col (Id t) = dim_row (pw ys t)\<close> by auto
qed

(*Could go into generic mult function would be more confusing to understand though*)

(*Takes a the position of a qubit that should be swapped to the front and the number of remaining qubits*)
fun(in qft)pow_SWAP_front:: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("fSWAP _ _" 75)  where
  "(fSWAP 0 t) = Id (t+1)" |  (*Added this see if it stays*)
  "(fSWAP (Suc 0) t) = SWAP_all (Suc 0) t"  
| "(fSWAP (Suc k) t) = (fSWAP k (t+1)) * (SWAP_all k t)"

lemma(in qft) pow_SWAP_front_dim:
  shows "k\<ge>1 \<longrightarrow> dim_row (fSWAP k t) = 2^(k+2+t)"
  and "k\<ge>1 \<longrightarrow> dim_col (fSWAP k t) = 2^(k+2+t)" sorry

lemma(in qft) app_fSWAP:
  fixes k m::nat 
  assumes "k\<ge>1" and "m>k"
      and "dim_row v = 2" and "dim_col v = 1" 
    shows "\<forall>xs ys. (\<forall>x \<in> set xs. dim_row x = 2) \<and> (\<forall>y \<in> set ys. dim_row y = 2) \<and>
                   (\<forall>x \<in> set xs. dim_col x = 1) \<and> (\<forall>y \<in> set ys. dim_col y = 1) \<and>
                   length xs = k \<and> length ys = m-k \<longrightarrow> 
          (fSWAP k (m-k)) * ((pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k))) = v \<Otimes> (pw xs k) \<Otimes> (pw ys (m-k))" 
proof(rule ind_from_1[of k])
  show "k\<ge>1" using assms by auto
next
  show "\<forall>xs ys. (\<forall>x \<in> set xs. dim_row x = 2) \<and> (\<forall>y \<in> set ys. dim_row y = 2) \<and>
                   (\<forall>x \<in> set xs. dim_col x = 1) \<and> (\<forall>y \<in> set ys. dim_col y = 1) \<and>
                   length xs = 1 \<and> length ys = m-1 \<longrightarrow> 
          (fSWAP 1 (m-1)) * ((pw xs 1) \<Otimes> v \<Otimes> (pw ys (m-1))) = v \<Otimes> (pw xs 1) \<Otimes> (pw ys (m-1))" sorry
next
  fix k
  assume IH: "\<forall>xs ys. (\<forall>x \<in> set xs. dim_row x = 2) \<and> (\<forall>y \<in> set ys. dim_row y = 2) \<and>
                   (\<forall>x \<in> set xs. dim_col x = 1) \<and> (\<forall>y \<in> set ys. dim_col y = 1) \<and>
                   length xs = k \<and> length ys = m-k \<longrightarrow> 
          (fSWAP k (m-k)) * ((pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k))) = v \<Otimes> (pw xs k) \<Otimes> (pw ys (m-k))" 
  show "\<forall>xs ys. (\<forall>x \<in> set xs. dim_row x = 2) \<and> (\<forall>y \<in> set ys. dim_row y = 2) \<and>
                (\<forall>x \<in> set xs. dim_col x = 1) \<and> (\<forall>y \<in> set ys. dim_col y = 1) \<and>
                 length xs = (Suc k) \<and> length ys = m-(Suc k) \<longrightarrow> 
        (fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) 
                = v \<Otimes> (pw xs (Suc k)) \<Otimes> (pw ys (m-(Suc k)))" 
  proof(rule allI, rule allI, rule impI)
    fix xs ys::"complex Matrix.mat list"
    assume a0: "(\<forall>x \<in> set xs. dim_row x = 2) \<and> (\<forall>y \<in> set ys. dim_row y = 2) \<and>
                (\<forall>x \<in> set xs. dim_col x = 1) \<and> (\<forall>y \<in> set ys. dim_col y = 1) \<and>
                length xs = (Suc k) \<and> length ys = m-(Suc k)"
    have "(fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) = 
          (fSWAP k (m-k)) * (SWAP_all k (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k))))" sorry
    have "(fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) = 
          (fSWAP k (m-k)) * (SWAP_all k (m-(Suc k))) * ((pw (tl xs) k) \<Otimes> (hd xs) \<Otimes> v \<Otimes> (pw ys (m-(Suc k))))" sorry
    have "(fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) = 
          (fSWAP k (m-k)) * ((pw (tl xs) k) \<Otimes> v \<Otimes> (hd xs) \<Otimes> (pw ys (m-(Suc k))))" sorry
    have "(fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) = 
         (v \<Otimes> (pw (tl xs) k) \<Otimes> (hd xs) \<Otimes> (pw ys (m-(Suc k))))" using IH sorry
    show "(fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) = 
         (v \<Otimes> (pw xs (Suc k)) \<Otimes> (pw ys (m-(Suc k))))" using IH sorry
  qed
qed

(*
proof(rule ind_from_1[of k])
  show "k\<ge>1" using assms by auto
next
  show "\<forall>xs ys. length xs = 1  \<and> length ys = m-1 \<longrightarrow> (fSWAP 1 (m-1)) * ((pw xs 1) \<Otimes> v \<Otimes>(pw ys (m-1))) = v \<Otimes> (pw xs 1) \<Otimes> (pw ys (m-1))" 
  proof(rule allI, rule allI, rule impI)
    fix xs ys::"complex Matrix.mat list"
    assume a0: "length xs = 1"
    and a1: "length ys = m-1"

    then have "(fSWAP 1 (m-1)) * ((pw xs 1) \<Otimes> v \<Otimes>(pw ys (m-1))) = (SWAP_all (Suc 0) (m-1)) * ((pw xs 1) \<Otimes> v \<Otimes>(pw ys (m-1)))"
      by auto
    then have "(fSWAP 1 (m-1)) * ((pw xs 1) \<Otimes> v \<Otimes>(pw ys (m-1))) = 
               (SWAP_all 1 (m-1)) * ((pw xs 1) \<Otimes> v \<Otimes>(pw ys (m-1)))"
      by auto
    moreover have "dim_row (pw xs 1) = 2" and "dim_col (pw xs 1) = 1" sorry
    moreover have "m-1\<ge>1" sorry
      ultimately have "(fSWAP 1 (m-1)) * ((pw xs 1) \<Otimes> v \<Otimes>(pw ys (m-1))) = 
               (v \<Otimes> (pw xs 1) \<Otimes> (pw ys (m-1)))"
        using app_SWAP_all assms a0 a1 sorry
      show "(fSWAP 1 (m-1)) * ((pw xs 1) \<Otimes> v \<Otimes>(pw ys (m-1))) = v \<Otimes> (pw xs 1) \<Otimes> (pw ys (m-1))" sorry
    qed
next
  fix k::nat
  assume a0: "k\<ge>1"
  assume IH: "\<forall>xs ys. length xs = k \<longrightarrow> (fSWAP k (m-k)) * ((pw xs k) \<Otimes> v \<Otimes>(pw ys (m-k))) = v \<Otimes> (pw xs k) \<Otimes> (pw ys (m-k))"
  show "\<forall>xs ys. length xs = (Suc k) \<longrightarrow> (fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes>(pw ys (m-(Suc k)))) = v \<Otimes> (pw xs (Suc k)) \<Otimes> (pw ys (m-(Suc k)))"
  proof(rule allI, rule allI, rule impI)
    fix xs ys::"complex Matrix.mat list"
    assume a1: "length xs = (Suc k)"
    have f0: "(fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes>(pw ys (m-(Suc k)))) = 
              (fSWAP k (m-(Suc k)+1)) * (SWAP_all k (m-(Suc k))) * ((pw xs (k+1)) \<Otimes> v \<Otimes>(pw ys (m-(Suc k))))"
      using a0 
      by (metis Suc_eq_plus1 ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc pow_SWAP_front.simps(2))
    have "length (tl xs) = k" by (simp add: a1)
    then have "(pw xs (k+1)) = (pw (tl xs) k) \<Otimes> (hd xs)" 
      by (metis Nitpick.size_list_simp(2) Suc_eq_plus1 a0 a1 list.exhaust_sel nat.simps(3) ordered_cancel_comm_monoid_diff_class.add_diff_inverse plus_1_eq_Suc pow_tensor_list.simps(3))
    then have "(fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes>(pw ys (m-(Suc k)))) = 
               (fSWAP k (m-(Suc k)+1)) * (SWAP_all k (m-(Suc k))) * ((pw (tl xs) k) \<Otimes> (hd xs) \<Otimes> v \<Otimes>(pw ys (m-(Suc k))))"
      using f0 by auto
    then have "(fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes>(pw ys (m-(Suc k)))) = 
               (fSWAP k (m-(Suc k)+1)) * ((SWAP_all k (m-(Suc k))) * ((pw (tl xs) k) \<Otimes> (hd xs) \<Otimes> v \<Otimes>(pw ys (m-(Suc k)))))"
      sorry
    moreover have "(SWAP_all k (m-(Suc k))) * ((pw (tl xs) k) \<Otimes> (hd xs) \<Otimes> v \<Otimes>(pw ys (m-(Suc k)))) = 
                   ((pw (tl xs) k) \<Otimes> v \<Otimes> (hd xs) \<Otimes> (pw ys (m-(Suc k))))"
      using app_SWAP_all[of "k" "(m-(Suc k))" "(tl xs)" "(hd xs)" "v" "ys"] by auto
    ultimately have "(fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes>(pw ys (m-(Suc k)))) = 
                     (fSWAP k (m-(Suc k)+1)) * ((pw (tl xs) k) \<Otimes> v \<Otimes> (hd xs) \<Otimes> (pw ys (m-(Suc k))))" by auto
    then have "(fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes>(pw ys (m-(Suc k)))) = 
                     (fSWAP k (m-(Suc k)+1)) * ((pw (tl xs) k) \<Otimes> v \<Otimes> ((hd xs) \<Otimes> (pw ys (m-(Suc k)))))" sorry
    moreover have "(hd xs) \<Otimes> (pw ys (m-(Suc k))) = (pw (ys@[(hd xs)]) (m-(Suc k)+1))" 
      using pow_tensor_app_left sorry
    ultimately have "(fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes>(pw ys (m-(Suc k)))) = 
                     (fSWAP k (m-(Suc k)+1)) * ((pw (tl xs) k) \<Otimes> v \<Otimes> (pw (ys@[(hd xs)]) (m-(Suc k)+1)))" by auto
    then have "(fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes>(pw ys (m-(Suc k)))) = 
                     (fSWAP k (m-k)) * ((pw (tl xs) k) \<Otimes> v \<Otimes> (pw (ys@[(hd xs)]) (m-k)))" sorry
    moreover have "length (tl xs) = k" sorry
    ultimately have "(fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes>(pw ys (m-(Suc k)))) = 
               v \<Otimes> (pw (tl xs) k) \<Otimes> (pw (ys@[(hd xs)]) (m-k))" (*IH*)
      using IH by auto
    then have "(fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes>(pw ys (m-(Suc k)))) = 
               v \<Otimes> (pw (tl xs) k) \<Otimes> (pw (ys@[(hd xs)]) (m-k-1+1))" 
      sorry
    then have "(fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes>(pw ys (m-(Suc k)))) = 
               v \<Otimes> (pw (tl xs) k) \<Otimes> ((hd xs) \<Otimes> (pw (ys) (m-k-1)))"
      using pow_tensor_app_left sorry
    then have "(fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes>(pw ys (m-(Suc k)))) = 
               v \<Otimes> ((pw (tl xs) k) \<Otimes> (hd xs)) \<Otimes> (pw (ys) (m-k-1))" 
      using tensor_mat_is_assoc by auto 
    then have "(fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes>(pw ys (m-(Suc k)))) = 
               v \<Otimes> (pw ((hd xs)#(tl xs)) (k+1)) \<Otimes> (pw ys (m-k-1))" 
       using pow_tensor_app_right  sorry
  then have "(fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes>(pw ys (m-(Suc k)))) = 
               v \<Otimes> (pw xs (k+1)) \<Otimes> (pw ys (m-k-1))"  sorry 
  then show "(fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes>(pw ys (m-(Suc k)))) = 
               v \<Otimes> (pw xs (Suc k)) \<Otimes> (pw ys (m-(Suc k)))"  sorry
  qed
qed
*)


lemma(in qft) app_fSWAP_fst_empty:
  fixes  m::nat 
  assumes "m>0"
      and "dim_row v = 2" and "dim_col v = 1" 
      and "\<forall>y \<in> set ys. dim_row y = 2"
      and "\<forall>y \<in> set ys. dim_col y = 1"
    shows "\<forall>xs ys. length ys = m \<longrightarrow> 
          (fSWAP 0 m) * (v \<Otimes> (pw ys m)) = v \<Otimes> (pw ys (m-k))" sorry




lemma(in qft) app_Id_fSWAP:
  assumes "length xs = k" and "k\<ge>1" and "m>k"
    and  "dim_row v = 2"  and "dim_col v = 1"
  shows "(Id 1 \<Otimes> (fSWAP k (m-k))) * ((qr k) \<Otimes> (pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k)))
= (qr k) \<Otimes> v \<Otimes> (pw xs k) \<Otimes> (pw ys (m-k))"
proof-
  have "dim_col (Id 1) = dim_row (qr k)" by (simp add: Id_def qr_def)
  moreover have "dim_col (fSWAP k (m-k)) = dim_row ((pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k)))" 
    using pow_SWAP_front_dim assms pow_tensor_list_dim_row[of xs k] pow_tensor_list_dim_row[of ys "m-k"] tensor_mat_is_assoc 
    sorry
 moreover have "dim_col (Id 1) > 0" and "dim_col (qr k) > 0" and "dim_col (fSWAP k (m-k)) > 0"
            and "dim_col ((pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k))) > 0" sorry
  ultimately have "((Id 1) \<Otimes> (fSWAP k (m-k))) * ((qr k) \<Otimes> ((pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k))))
           = ((Id 1) * (qr k)) \<Otimes> ((fSWAP k (m-k)) * ((pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k))))" 
    using mult_distr_tensor by auto
  then have "((Id 1) \<Otimes> (fSWAP k (m-k))) * ((qr k) \<Otimes> ((pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k))))
           = ((qr k) \<Otimes> (fSWAP k (m-k)) * ((pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k))))" 
    using Id_def qr_def by simp
  then show "(Id 1 \<Otimes> (fSWAP k (m-k))) * ((qr k) \<Otimes> (pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k)))
           = (qr k) \<Otimes> v \<Otimes> (pw xs k) \<Otimes> (pw ys (m-k))" 
    using app_fSWAP assms tensor_mat_is_assoc by auto
qed


(*Needs some assumptions abount bin_rep_values. Should already use j probably?*)
lemma(in qft) app_CR_Id:
 assumes "length xs = k" and "k\<ge>1" and "k<n" and "m>k"
     and "dim_row v = 2"  and "dim_col v = 1"
     and "v = zero \<or> v = one"
     and "v = zero \<longrightarrow> ((bin_rep n j_dec)!(k+1)) = 1"
     and "v = one \<longrightarrow>  ((bin_rep n j_dec)!(k+1)) = 0" 
  shows "(CR (k+2) \<Otimes> Id m) * ((qr k) \<Otimes> v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k))) = (qr (k+1)) \<Otimes> v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k))"
proof-
  have "(CR (k+2) \<Otimes> Id m) * ((qr k) \<Otimes> v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k))) = 
        ((CR (k+2))*((qr k) \<Otimes> v)) \<Otimes> (Id m * ((pw xs k) \<Otimes>(pw ys (m-k))))" sorry
  then have f0: "(CR (k+2) \<Otimes> Id m) * ((qr k) \<Otimes> v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k))) = 
        ((CR (k+2))*((qr k) \<Otimes> v)) \<Otimes> ((pw xs k) \<Otimes>(pw ys (m-k)))" sorry
  show "(CR (k+2) \<Otimes> Id m) * ((qr k) \<Otimes> v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k))) = (qr (k+1)) \<Otimes> v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k))"
  proof(rule disjE)
    show "v = zero \<or> v = one" using assms by auto
  next
    assume a0: "v = zero"
    then have "((bin_rep n j_dec)!(k+1)) = 1" using assms by auto
    moreover have "(CR (k+2))*((qr k) \<Otimes> v) = qr (k+1) \<Otimes> v" 
      using app_controlled_phase_shift_zero[of k] assms qr_def[of k] qr_def[of "k+1"] a0 sorry
        (*Shouldn't be a problem if app_controlled_phase... is rewritten with qr_def*)
    ultimately show "(CR (k+2) \<Otimes> Id m) * ((qr k) \<Otimes> v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k))) = 
               (qr (k+1)) \<Otimes> v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k))" using f0 tensor_mat_is_assoc by auto
     
  next
    assume a0: "v = one"
    then have "((bin_rep n j_dec)!(k+1)) = 0" using assms by auto
    moreover have "(CR (k+2))*((qr k) \<Otimes> v) = qr (k+1) \<Otimes> v" 
      using app_controlled_phase_shift_zero[of k] assms qr_def[of k] qr_def[of "k+1"] a0 sorry
        (*Shouldn't be a problem if app_controlled_phase... is rewritten with qr_def*)
    ultimately show "(CR (k+2) \<Otimes> Id m) * ((qr k) \<Otimes> v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k))) = 
               (qr (k+1)) \<Otimes> v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k))" using f0 tensor_mat_is_assoc by auto
  qed
qed


lemma (in qft) 
  assumes "(fSWAP k t) * A = B" and "gate (k+t+2) (fSWAP k t)"
  shows "(fSWAP k t)\<^sup>\<dagger> * B = A" 
  oops


(*Maybe possible to work with transpose here otw just prove this too*)
lemma(in qft) 
  assumes "length xs = k" and "k\<ge>1" and "m>k"
    and  "dim_row v = 2"  and "dim_col v = 1"
  shows "(Id 1 \<Otimes> ((fSWAP k t)\<^sup>\<dagger>)) * ((qr (k+1)) \<Otimes> v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k)))
  = (qr (k+1)) \<Otimes> (pw xs k)\<Otimes> v \<Otimes>(pw ys (m-k))"
  sorry



(*k is the index of the qubit that should be added to the binary fraction. c is the current qubit *)
definition(in qft) app_CR::"nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("CR\<^sub>_ _" 75) where
"app_CR k c \<equiv> (Id c) \<Otimes> ((Id 1 \<Otimes> ((fSWAP k (n-c-k))\<^sup>\<dagger>)) *(CR k * Id (n-c)) * (Id 1 \<Otimes> (fSWAP k (n-c-k)))) "



(*Could go into generic mult function would be more confusing to understand though*)
(*c is the current qubit *)
fun(in qft) app_all_CR:: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("aCR _ _" 75) where
  "(aCR c (Suc (Suc 0))) = app_CR (n+1-c) c"  
| "(aCR c (Suc k)) = (fSWAP c k) * (app_CR (n+2-(Suc k)) c)"


(*Apply the H gate to the current qubit then apply R_2 to R_(n-c)*)
definition(in qft) all_gates_on_single_qubit:: "nat \<Rightarrow> complex Matrix.mat" ("G _" 75)  where
 "G c = (Id c \<Otimes> aCR c (n-c)) * (Id c \<Otimes> H \<Otimes> Id (n-c))"  

lemma(in qft) o1: 
  fixes k::nat
  assumes "k<n"
  shows "(G k) * ((pow_tensor_list [qr (nat i). i<-[1..k]] k) \<Otimes> (j\<Otimes> k (n-k))) 
      = ((pow_tensor_list [qr (nat i). i<-[1..(k+1)]] (k+1)) \<Otimes> (j\<Otimes> k (n-k-1)))"
  sorry


fun pow_mult :: "(complex Matrix.mat) list \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("pm _ _" 75)  where
  "(pm (Cons x []) 0) = x"  
| "(pm (Cons x xs) (Suc k)) = x * (pm xs k)"


value "[k . k<-[(0::nat),1]]"
(*How does list comprehension work?*)
(*Might need to rev this*)
abbreviation(in qft) \<psi>\<^sub>1 where 
  "\<psi>\<^sub>1 \<equiv> pow_tensor_list [qr (nat k). k<-[1..n] ] n"

(*Application of all R gates on a current qubit k*)


lemma(in qft) o1_end: 
  fixes k::nat
  assumes "k<n"
  shows "(G k) * ((pow_tensor_list [qr (nat i). i<-[1..(n-1)]] (n-1)) \<Otimes> (j\<Otimes> (n-1) 1)) 
      = (pow_tensor_list [qr (nat i). i<-[1..n]] n) "
  sorry


lemma(in qft) o2: 
  assumes "k<n"
  shows "(pow_mult [G (nat i). i<-[1..k]] k) * (j\<Otimes> 0 n)
      = ((pow_tensor_list [qr (nat i). i<-[1..k]] k) \<Otimes> (j\<Otimes> k (n-k)))" 
  sorry

lemma(in qft) o2_end: 
  shows "(pow_mult [G (nat i). i<-[1..n]] n) * (j\<Otimes> 0 n)
      = (pow_tensor_list [qr (nat i). i<-[1..n]] n)" 
  sorry (*Use o2 until only one member left than show it manually k=n-1*)

theorem(in qft)
  shows "(pow_mult [G (nat k). k<-[1..n]] n) * (j\<Otimes> 0 n) = \<psi>\<^sub>1"
  sorry (*using o2 k=n*)





















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

