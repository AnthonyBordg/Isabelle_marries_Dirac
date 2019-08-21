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
  "(pw [] 0) = (Id 0)"  |
  "(pw (Cons x xs) (Suc k)) = x \<Otimes> (pw xs k)"

(*gives back a part of j as tensor product of single qubits s is the start and t the number of bits
I.e. $|j_1,...,j_n\rangle$ and s=2 and t=3 gives $|j_2,j_3,j_4\rangle$ *)
definition(in qft) j_to_tensor_prod :: "nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>nat\<Rightarrow>complex Matrix.mat" ("j\<Otimes> _ _ _ _" 75) where 
"(j\<Otimes> s t j m) = pw (j_to_list_bound (s-1) (t-1) j m) (s+t-1)"

(*Missing: result is gate, state,... Easy to proof*)

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

(*Rephrase that with Id*)
lemma one_mat_left_tensor:
  shows "(1\<^sub>m 1) \<Otimes> A = A"
proof
  fix i j
  assume a0: "i < dim_row A" and a1: "j < dim_col A" 
  have "((1\<^sub>m 1) \<Otimes> A) $$ (i,j) = (1\<^sub>m 1) $$ (i div (dim_row A), j div (dim_col A)) * A $$(i mod (dim_row A), j mod (dim_col A))"
    using index_tensor_mat one_mat_def a0 a1 by auto
  moreover have "i div (dim_row A) = 0" using a0 by auto
  moreover have "j div (dim_col A) = 0" using a1 by auto
  moreover have "i mod (dim_row A) = i" using a0 by auto
  moreover have "j mod (dim_col A) = j" using a1 by auto
  ultimately show "((1\<^sub>m 1) \<Otimes> A) $$ (i,j) = A $$(i, j)"
    using one_mat_def by auto
next
  show "dim_row ((1\<^sub>m 1) \<Otimes> A) = dim_row A" using one_mat_def by auto
next
  show "dim_col ((1\<^sub>m 1) \<Otimes> A) = dim_col A" using one_mat_def by auto
qed

lemma one_mat_right_tensor:
  shows "A \<Otimes> (1\<^sub>m 1) = A" sorry


lemma pow_tensor_app_left:
  fixes k::nat and x::"complex Matrix.mat" 
  shows "length xs = k \<longrightarrow> (pw xs k) \<Otimes> x = pw (xs@[x]) (k+1)" 
proof(induction k arbitrary: xs)
  fix xs
  show "length xs = 0 \<longrightarrow> (pw xs 0) \<Otimes> x = pw (xs@[x]) (0+1)"  
    using one_mat_left_tensor Id_def by auto
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

lemma pow_tensor_app_right:
  assumes "k\<ge>1" and "length xs = k"
  shows "x \<Otimes> (pw xs k) = pw (x#xs) (k+1)" 
  using Suc_le_D assms(1) by force

lemma decomp_unit_vec_zero:
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

lemma decomp_unit_vec_oen:
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
next
  show "dim_row ((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) = dim_row ((qr (r+1)) \<Otimes> |zero\<rangle>)" 
    by (simp add: controlled_phase_shift_def ket_vec_def qr_def)
next
  show "dim_col ((CR (r+2)) * ((qr r) \<Otimes> |zero\<rangle>)) = dim_col ((qr (r+1)) \<Otimes> |zero\<rangle>)"
    using ket_vec_def controlled_phase_shift_def qr_def by auto
qed

lemma(in qft) app_controlled_phase_shift_one: 
  fixes r::nat
  assumes "r < n" and "((bin_rep n j_dec)!(r+1)) = 0"
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

(*Swaps the k+1 and k+2 qubit of a k+2+t qubit system. *)
definition(in qft) SWAP_all :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
"SWAP_all k t \<equiv> (Id k) \<Otimes> SWAP \<Otimes> (Id t)"

lemma(in qft) SWAP_all_special_cases:
  shows "SWAP_all 0 t = SWAP \<Otimes> (Id t)"
    and "SWAP_all k 0 = (Id k) \<Otimes> SWAP"
  using one_mat_left_tensor one_mat_right_tensor SWAP_all_def Id_def by auto

lemma(in qft) SWAP_all_dim:
  shows "dim_row (SWAP_all k t) = 2^(k+2+t)"
    and "dim_col (SWAP_all k t) = 2^(k+2+t)"    
  sorry

lemma(in qft) app_SWAP_all:
  assumes "dim_row v = 2" and "dim_row w = 2" 
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
    using Id_def assms pow_tensor_list_dim_row[of ys t 2] by (simp add: SWAP_def)
  moreover have "dim_col (Id k) > 0" and "dim_col (SWAP \<Otimes> (Id t)) > 0" and
                "dim_col (pw xs k) > 0" and "dim_col (v \<Otimes> w \<Otimes> (pw ys t)) > 0" 
    apply (auto simp: Id_def SWAP_def assms pow_tensor_list_dim_col[of xs k] pow_tensor_list_dim_col[of ys t]).
  ultimately have "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) =
              ((Id k)*(pw xs k)) \<Otimes> ((SWAP \<Otimes> (Id t)) * (v \<Otimes> w \<Otimes> (pw ys t)))"
    using mult_distr_tensor by auto
  then have "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) =
             ((pw xs k)) \<Otimes> ((SWAP \<Otimes> (Id t)) * (v \<Otimes> w \<Otimes> (pw ys t)))" 
    using Id_def \<open>dim_col (Id k) = dim_row (pw xs k)\<close> by auto
  moreover have "dim_col SWAP = dim_row (v \<Otimes> w)" using assms by (simp add: SWAP_def)
  moreover have "dim_col (Id t) = dim_row (pw ys t)" using Id_def pow_tensor_list_dim_row[of ys t] assms 
    by (metis index_one_mat(3))
  moreover have "dim_col SWAP > 0" and "dim_col (v \<Otimes> w) > 0" and "dim_col (Id t) > 0" and "dim_col (pw ys t) > 0" 
    apply (auto simp: SWAP_def assms Id_def pow_tensor_list_dim_col[of ys t]). 
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
qubit is already at the front the Id matrix is applied*)
fun(in qft)pow_SWAP_front:: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("fSWAP _ _" 75)  where
  "(fSWAP 0 t) = Id (t+1)" 
| "(fSWAP (Suc k) t) = (fSWAP k (t+1)) * (SWAP_all k t)"

lemma(in qft) pow_SWAP_front_dim:
  shows "dim_row (fSWAP k t) = 2^(k+2+t)"
  and "dim_col (fSWAP k t) = 2^(k+2+t)" sorry

lemma(in qft) pow_SWAP_front_hermite_cnj_dim:
  shows "dim_row (fSWAP k t)\<^sup>\<dagger> = 2^(k+2+t)"
  and "dim_col (fSWAP k t)\<^sup>\<dagger> = 2^(k+2+t)" sorry

lemma(in qft) pow_SWAP_front_gate:
  shows "gate (k+2+t) (fSWAP k t)" sorry


lemma(in qft) aux_app_fSWAP:
  fixes k m::nat 
  assumes "m>k" and "dim_row v = 2" and "dim_col v = 1" 
    shows "(\<forall>x \<in> set xs. dim_row x = 2) \<and> (\<forall>y \<in> set ys. dim_row y = 2) \<and>
                   (\<forall>x \<in> set xs. dim_col x = 1) \<and> (\<forall>y \<in> set ys. dim_col y = 1) \<and>
                   length xs = k \<and> length ys = m-k \<longrightarrow> 
          (fSWAP k (m-k)) * ((pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k))) = v \<Otimes> (pw xs k) \<Otimes> (pw ys (m-k))" 
proof(induction k arbitrary: xs ys)
  fix xs ys
  show "(\<forall>x \<in> set xs. dim_row x = 2) \<and> (\<forall>y \<in> set ys. dim_row y = 2) \<and>
                   (\<forall>x \<in> set xs. dim_col x = 1) \<and> (\<forall>y \<in> set ys. dim_col y = 1) \<and>
                   length xs = 0 \<and> length ys = m-0 \<longrightarrow> 
          (fSWAP 0 (m-0)) * ((pw xs 0) \<Otimes> v \<Otimes> (pw ys (m-0))) = v \<Otimes> (pw xs 0) \<Otimes> (pw ys (m-0))" 
  proof
    assume a0:  "(\<forall>x \<in> set xs. dim_row x = 2) \<and> (\<forall>y \<in> set ys. dim_row y = 2) \<and>
                 (\<forall>x \<in> set xs. dim_col x = 1) \<and> (\<forall>y \<in> set ys. dim_col y = 1) \<and> length xs = 0 \<and> length ys = m-0"
    then have "(fSWAP 0 (m-0)) * ((pw xs 0) \<Otimes> v \<Otimes> (pw ys (m-0))) 
             = (Id (m+1)) * ((Id 0) \<Otimes> v \<Otimes> (pw ys (m-0)))" 
      by auto
    moreover have "dim_row ((Id 0) \<Otimes> v \<Otimes> (pw ys (m-0))) = 2^(m+1)" 
      using Id_def assms pow_tensor_list_dim_row[of ys "m-0"] sorry
    ultimately have "(fSWAP 0 (m-0)) * ((pw xs 0) \<Otimes> v \<Otimes> (pw ys (m-0))) 
             = ((Id 0) \<Otimes> v \<Otimes> (pw ys (m-0)))" 
      using Id_def by auto
    then have "(fSWAP 0 (m-0)) * ((pw xs 0) \<Otimes> v \<Otimes> (pw ys (m-0))) 
             = (v \<Otimes> (pw ys (m-0)))" using Id_def one_mat_left_tensor by auto
    then have "(fSWAP 0 (m-0)) * ((pw xs 0) \<Otimes> v \<Otimes> (pw ys (m-0))) 
             = (v \<Otimes> (Id 0) \<Otimes> (pw ys (m-0)))" using Id_def one_mat_right_tensor by auto
    then show "(fSWAP 0 (m-0)) * ((pw xs 0) \<Otimes> v \<Otimes> (pw ys (m-0))) 
             = (v \<Otimes> (pw xs 0) \<Otimes> (pw ys (m-0)))" 
      using a0 by auto
  qed
next
  fix k xs ys
  assume IH: "(\<forall>x \<in> set xs. dim_row x = 2) \<and> (\<forall>y \<in> set ys. dim_row y = 2) \<and>
                   (\<forall>x \<in> set xs. dim_col x = 1) \<and> (\<forall>y \<in> set ys. dim_col y = 1) \<and>
                   length xs = k \<and> length ys = m-k \<longrightarrow> 
          (fSWAP k (m-k)) * ((pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k))) = v \<Otimes> (pw xs k) \<Otimes> (pw ys (m-k))" for xs ys
  show  "(\<forall>x \<in> set xs. dim_row x = 2) \<and> (\<forall>y \<in> set ys. dim_row y = 2) \<and>
                   (\<forall>x \<in> set xs. dim_col x = 1) \<and> (\<forall>y \<in> set ys. dim_col y = 1) \<and>
                   length xs = (Suc k) \<and> length ys = m-(Suc k) \<longrightarrow> 
          (fSWAP (Suc k) (m-(Suc k))) * ((pw xs (Suc k)) \<Otimes> v \<Otimes> (pw ys (m-(Suc k)))) = v \<Otimes> (pw xs (Suc k)) \<Otimes> (pw ys (m-(Suc k)))"
  proof
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

(*Rename to full name*)
lemma(in qft) app_fSWAP:
  fixes k m::nat 
  assumes "m>k" and "dim_row v = 2" and "dim_col v = 1" 
      and "(\<forall>x \<in> set xs. dim_row x = 2)" and "(\<forall>y \<in> set ys. dim_row y = 2)"
      and "(\<forall>x \<in> set xs. dim_col x = 1)" and "(\<forall>y \<in> set ys. dim_col y = 1)" 
      and "length xs = k" and "length ys = m-k"
    shows "(fSWAP k (m-k)) * ((pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k))) = v \<Otimes> (pw xs k) \<Otimes> (pw ys (m-k))" 
  using aux_app_fSWAP assms by simp

lemma(in qft) app_Id_fSWAP:
  assumes "m>k" 
      and "dim_row v = 2" and "dim_col v = 1" 
      and "(\<forall>x \<in> set xs. dim_row x = 2)" and "(\<forall>y \<in> set ys. dim_row y = 2)"
      and "(\<forall>x \<in> set xs. dim_col x = 1)" and "(\<forall>y \<in> set ys. dim_col y = 1)" 
      and "length xs = k" and "length ys = m-k"
  shows "(Id 1 \<Otimes> (fSWAP k (m-k))) * ((qr k) \<Otimes> (pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k)))
       = (qr k) \<Otimes> v \<Otimes> (pw xs k) \<Otimes> (pw ys (m-k))"
proof-
  have "dim_col (Id 1) = dim_row (qr k)" by (simp add: Id_def qr_def)
  moreover have "dim_col (fSWAP k (m-k)) = dim_row ((pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k)))" 
    using pow_SWAP_front_dim assms pow_tensor_list_dim_row[of xs k] pow_tensor_list_dim_row[of ys "m-k"] 
          tensor_mat_is_assoc sorry
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


(*Needs some assumptions about bin_rep_values. Should already use j probably?*)
lemma(in qft) app_CR_Id:
 assumes "length xs = k" and "k\<ge>1" and "k<n" and "m\<ge>k"
     and "dim_row v = 2"  and "dim_col v = 1"
     and "v = zero \<or> v = one"
     and "v = zero \<longrightarrow> ((bin_rep n j_dec)!(k+1)) = 1"
     and "v = one \<longrightarrow>  ((bin_rep n j_dec)!(k+1)) = 0" 
   shows "(CR (k+2) \<Otimes> Id m) * ((qr k) \<Otimes> v \<Otimes> (pw ys (m-k))) = (qr (k+1)) \<Otimes> v \<Otimes>(pw ys (m-k))" sorry

(*proof-
  have "(CR (k+2) \<Otimes> Id m) * ((qr k) \<Otimes> v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k))) = 
        ((CR (k+2))*((qr k) \<Otimes> v)) \<Otimes> (Id m * ((pw xs k) \<Otimes>(pw ys (m-k))))" 
  sorry
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
qed*)

(*May be written without pw?*)
lemma (in qft) app_pow_SWAP_front:
  assumes "(fSWAP k t) * A = B" 
    and "dim_row A = 2^(k+t+2)" and "dim_col A = 1"
    and "dim_row B = 2^(k+t+2)" and "dim_col B = 1"
  shows "(fSWAP k t)\<^sup>\<dagger> * B = A" 
proof-
  have "(fSWAP k t)\<^sup>\<dagger> * ((fSWAP k t) * A) = (fSWAP k t)\<^sup>\<dagger> * B" using assms arg_cong by auto
  then have "((fSWAP k t)\<^sup>\<dagger> * (fSWAP k t)) * A = (fSWAP k t)\<^sup>\<dagger> * B" 
    using assoc_mult_mat[of "(fSWAP k t)\<^sup>\<dagger>" "2^(k+t+2)" "2^(k+t+2)" "(fSWAP k t)" "2^(k+t+2)" A 1]  
    by (simp add: assms carrier_matI pow_SWAP_front_hermite_cnj_dim pow_SWAP_front_dim)
  then have "(1\<^sub>m (2^(k+t+2))) * A = (fSWAP k t)\<^sup>\<dagger> * B" 
    using assms gate.unitary unitary_def pow_SWAP_front_hermite_cnj_dim pow_SWAP_front_gate 
    by (metis hermite_cnj_dim_row index_mult_mat(2) pow_SWAP_front_dim(1))
  then show "(fSWAP k t)\<^sup>\<dagger> * B = A" by (simp add: assms(2))
qed

(*May be written without pw?*)
lemma(in qft) app_pow_SWAP_front_herm_cnj:
  assumes "m>k"
      and "dim_row v = 2" and "dim_col v = 1" 
      and "(\<forall>x \<in> set xs. dim_row x = 2)" and "(\<forall>y \<in> set ys. dim_row y = 2)"
      and "(\<forall>x \<in> set xs. dim_col x = 1)" and "(\<forall>y \<in> set ys. dim_col y = 1)" 
      and "length xs = k" and "length ys = m-k"
    and "dim_row v = 2"  and "dim_col v = 1"
  shows "(Id 1 \<Otimes> ((fSWAP k (m-k))\<^sup>\<dagger>)) * ((qr (k+1)) \<Otimes> v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k)))
  = (qr (k+1)) \<Otimes> (pw xs k)\<Otimes> v \<Otimes>(pw ys (m-k))"
proof-
  have "(Id 1 \<Otimes> ((fSWAP k (m-k))\<^sup>\<dagger>)) * ((qr (k+1)) \<Otimes> v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k)))
  = (Id 1 * (qr (k+1))) \<Otimes> (((fSWAP k (m-k))\<^sup>\<dagger>) * (v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k))))"
    using Id_def qr_def pow_tensor_list_dim_row pow_tensor_list_dim_col pow_SWAP_front_dim assms 
          mult_distr_tensor[of "Id 1" "(fSWAP k (m-k))\<^sup>\<dagger>" "(qr (k+1))" " v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k))"] 
    sorry
  then have "(Id 1 \<Otimes> ((fSWAP k (m-k))\<^sup>\<dagger>)) * ((qr (k+1)) \<Otimes> v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k)))
  = (qr (k+1)) \<Otimes> (((fSWAP k (m-k))\<^sup>\<dagger>) * (v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k))))"
    using Id_def qr_def by auto
  moreover have "(fSWAP k (m-k)) * ((pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k))) = v \<Otimes> (pw xs k) \<Otimes> (pw ys (m-k))"  
    using app_fSWAP assms by auto
  moreover have "dim_row ((pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k))) = 2^(k+(m-k)+2)" 
            and "dim_col ((pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k))) = 1"
            and "dim_row (v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k))) = 2^(k+(m-k)+2)" 
            and "dim_col (v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k))) = 1"
            sorry
  ultimately have "(Id 1 \<Otimes> ((fSWAP k (m-k))\<^sup>\<dagger>)) * ((qr (k+1)) \<Otimes> v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k)))
  = (qr (k+1)) \<Otimes> ((pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k)))"
    using app_pow_SWAP_front[of k "(m-k)" "((pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k)))" "v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k))" ] assms 
    by auto
  then show "(Id 1 \<Otimes> ((fSWAP k (m-k))\<^sup>\<dagger>)) * ((qr (k+1)) \<Otimes> v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k)))
  = (qr (k+1)) \<Otimes> (pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k))" using tensor_mat_is_assoc by auto
qed


(*k is the index of the qubit that should be added to the binary fraction. c is the current qubit *)
definition(in qft) app_CR::"nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("CR\<^sub>_ _" 75) where
"app_CR k c \<equiv> (Id c) \<Otimes> ((Id 1 \<Otimes> ((fSWAP k (n-c-k))\<^sup>\<dagger>)) *(CR k * Id (n-c)) * (Id 1 \<Otimes> (fSWAP k (n-c-k)))) "

lemma(in qft)
  assumes "dim_row v = c" and "dim_col v = 1"
      and "dim_row w = 2^(n-c-1)" and "dim_col v = 1"
    shows "(appCR k c) * (v \<Otimes> (qr (k+1)) \<Otimes> w) = (v \<Otimes> (qr (k+2)) \<Otimes> w)"
proof-
  have "(appCR k c) * (v \<Otimes> (qr (k+1)) \<Otimes> w) = 
  ((Id c) \<Otimes> ((Id 1 \<Otimes> ((fSWAP k (n-c-k))\<^sup>\<dagger>)) * (CR k * Id (n-c)) * (Id 1 \<Otimes> (fSWAP k (n-c-k))))) 
  * (v \<Otimes> (qr (k+1)) \<Otimes> w)" using app_CR_def 
    by (metis Quantum.Id_def add_eq_self_zero index_one_mat(2) mult_2 nat.simps(3) nat_1_add_1 plus_1_eq_Suc plus_nat.add_0 pow_SWAP_front.simps(1) power2_eq_square power_one_right qft.pow_SWAP_front_dim(1) qft_axioms semiring_normalization_rules(24))
  then have "(appCR k c) * (v \<Otimes> (qr (k+1)) \<Otimes> w) = 
  ((Id c) * v) \<Otimes> (((Id 1 \<Otimes> ((fSWAP k (n-c-k))\<^sup>\<dagger>)) * (CR k * Id (n-c)) * (Id 1 \<Otimes> (fSWAP k (n-c-k)))) * ((qr (k+1)) \<Otimes> w))"
    using Id_def assms sorry
  then have "(appCR k c) * (v \<Otimes> (qr (k+1)) \<Otimes> w) = 
   v \<Otimes> (((Id 1 \<Otimes> ((fSWAP k (n-c-k))\<^sup>\<dagger>)) * (CR k * Id (n-c)) * (Id 1 \<Otimes> (fSWAP k (n-c-k)))) * ((qr (k+1)) \<Otimes> w))"
    sorry
  then have "(appCR k c) * (v \<Otimes> (qr (k+1)) \<Otimes> w) = 
   v \<Otimes> ((Id 1 \<Otimes> ((fSWAP k (n-c-k))\<^sup>\<dagger>)) * (CR k * Id (n-c)) * (Id 1 \<Otimes> (fSWAP k (n-c-k))) * ((qr (k+1)) \<Otimes> w))"
     sorry
  show "(appCR k c) * (v \<Otimes> (qr (k+1)) \<Otimes> w) = (v \<Otimes> (qr (k+2)) \<Otimes> w)" sorry
qed

(*Could go into generic mult function would be more confusing to understand though*)
(*c is the current qubit k=(n-c) ensures that R_2 to R_(n-c+1) are applied to the qubit with the 
special case for c=n that nothing is applied.  *)
fun(in qft) app_all_CR:: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("aCR _ _" 75) where
  "(aCR c 0) = (Id n)"  
| "(aCR c (Suc k)) = (app_CR (2+k) c) * (aCR c k)"

(*Apply the H gate to the current qubit then apply R_2 to R_(n-c)*)
definition(in qft) all_gates_on_single_qubit:: "nat \<Rightarrow> complex Matrix.mat" ("G _" 75)  where
 "G c = (Id (c-1) \<Otimes> aCR c (n-c)) * (Id (c-1) \<Otimes> H \<Otimes> Id (n-c))"  

lemma(in qft) o1: 
  fixes k::nat
  assumes "k<n"
  shows "(G k) * ((pw [qr (nat i). i<-[1..k]] k) \<Otimes> (j\<Otimes> k (n-k) j_dec n)) 
      = ((pw [qr (nat i). i<-[1..(k+1)]] (k+1)) \<Otimes> (j\<Otimes> k (n-k-1) j_dec n))"
  sorry


fun pow_mult :: "(complex Matrix.mat) list \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("pm _ _" 75)  where
  "(pm (Cons x []) 0) = x"  
| "(pm (Cons x xs) (Suc k)) = x * (pm xs k)"


value "[k . k<-[(0::nat),1]]"
(*How does list comprehension work?*)
(*Might need to rev this*)
abbreviation(in qft) \<psi>\<^sub>1 where 
  "\<psi>\<^sub>1 \<equiv> pw [qr (nat k). k<-[1..n] ] n"

(*Application of all R gates on a current qubit k*)


lemma(in qft) o2: 
  assumes "k<n"
  shows "(pm [G (nat i). i<-[1..k]] k) * (j\<Otimes> 1 n j_dec n)
      = ((pw [qr (nat i). i<-[1..k]] k) \<Otimes> (j\<Otimes> k (n-k) j_dec n))" 
  sorry

theorem(in qft)
  shows "(pm [G (nat k). k<-[1..n]] n) * (j\<Otimes> 1 n j_dec n) = \<psi>\<^sub>1"
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

