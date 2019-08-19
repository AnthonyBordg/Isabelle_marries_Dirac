theory Quantum_Fourier_Transform
imports
  More_Tensor
  Binary_Nat
begin

(*Just for convenience*)
locale qft =
  fixes j_dec n::nat (*Can be renamed to j in the end*)
  assumes "j_dec < 2^n"

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

primrec(in qft) j_to_list :: "nat \<Rightarrow> complex Matrix.mat list" where
"j_to_list 0 = (if (bin_rep n j_dec)!0 = 0 then [zero] else [one])" |
"j_to_list (Suc k) = (if (bin_rep n j_dec)!(Suc k) = 0 then zero else one) # (j_to_list k)"

fun pow_tensor :: "complex Matrix.mat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("_ \<otimes>\<^bsup>_\<^esup>" 75)  where
  "A \<otimes>\<^bsup>(Suc 0)\<^esup> = A"  
| "A \<otimes>\<^bsup>(Suc k)\<^esup> = A \<Otimes> (A \<otimes>\<^bsup>k\<^esup>)"

(*Missing: result is gate, state,... Easy to proof*)

(*TODO: Would exchanging the arguments help with induction problem?*)
fun pow_tensor_list :: "((complex Matrix.mat) list) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("pw _ _" 75)  where
  "(pw (Cons x []) (Suc 0)) = x"  |
  "(pw (Cons x xs) (Suc k)) = (pw xs k) \<Otimes> x"

(*Missing: result is gate, state,... Easy to proof*)

(*Could also be generalized*)
lemma pow_tensor_list_dim_col:
  assumes "k \<ge> 1"
  shows "\<forall>xs. length xs = k \<longrightarrow> (\<forall>x \<in> set xs. dim_col x = 1) \<longrightarrow> dim_col (pw xs k) = 1"
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
      then have "dim_col (pw xs (Suc k)) = dim_col ((pw (tl xs) k) \<Otimes> x)" using pow_tensor_list.simps 
        by (metis IH One_nat_def a0 a1 diff_Suc_1 dim_col_tensor_mat length_Cons list.exhaust list.inject list.sel(3) 
            list.set_intros(1) list.set_sel(2) list.size(3) semiring_normalization_rules(12))
      then have "dim_col (pw xs (Suc k)) = dim_col ((pw (tl xs) k)) * 1" using a0 a1 a2 by (metis dim_col_tensor_mat list.set_intros(1))
      then show "dim_col (pw xs (Suc k)) = 1" using a0 IH by (metis a1 diff_Suc_1 length_0_conv length_tl list.set_sel(2) mult.right_neutral nat.simps(3))
    qed
    ultimately show "dim_col (pw xs (Suc k)) = 1" by auto
  qed
qed

lemma pow_tensor_list_dim_col': (*Integrate last lemma into this*)
  assumes "k \<ge> 1"
  shows "length xs = k \<longrightarrow> (\<forall>x \<in> set xs. dim_col x = 1) \<longrightarrow> dim_col (pw xs k) = 1"
  using assms pow_tensor_list_dim_col by auto

lemma pow_tensor_list_dim_row:
  assumes "k \<ge> 1"
  shows "\<forall>xs. length xs = k \<longrightarrow> (\<forall>x \<in> set xs. dim_row x = m) \<longrightarrow> dim_row (pw xs k) = m^k"
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
      ultimately have "dim_row (pw xs (Suc k)) = dim_row ((pw (tl xs) k) \<Otimes> x)" using pow_tensor_list.simps 
        using f1 by (metis (full_types) Nitpick.size_list_simp(2) a2 dim_row_tensor_mat mult.commute pow_tensor_list.simps(3))
      then have "dim_row (pw xs (Suc k)) = dim_row ((pw (tl xs) k)) * m" 
        using a1 a2 by (metis dim_row_tensor_mat list.set_intros(1))
      then show "dim_row (pw xs (Suc k)) = m^(Suc k)" 
        by (metis IH a0 a1 f1 length_0_conv list.set_sel(2) mult.commute nat.simps(3) power_Suc)
    qed
    ultimately show "dim_row (pw xs (Suc k)) = m^(Suc k)" by auto
  qed
qed

lemma pow_tensor_list_dim_row': (*Integrate last lemma into this*)
  assumes "k \<ge> 1"
  shows "length xs = k \<longrightarrow> (\<forall>x \<in> set xs. dim_row x = m) \<longrightarrow> dim_row (pw xs k) = m^k"
  using assms pow_tensor_list_dim_row by auto

lemma pow_tensor_app_left:
  fixes k::nat
  and x::"complex Matrix.mat" and xs::"complex Matrix.mat list"
  assumes "k\<ge>1" and "length xs = k"
  shows "x \<Otimes> (pw xs k) = pw (xs@[x]) (k+1)" sorry
(*proof(rule ind_from_1[of k]) 
  show "k\<ge>1" using assms by auto*)
(*Other induction does not work. Why does Isabelle not see the k in (pw xs k)*)

lemma pow_tensor_app_right:
  assumes "k\<ge>1" and "length xs = k"
  shows "(pw xs k) \<Otimes> x = pw (x#xs) (k+1)"
  sorry

definition(in qft) j_to_tensor_prod :: "complex Matrix.mat" ("[j]" 75) where (*Find better abbrev*)
"[j] = pow_tensor_list (rev (j_to_list n)) n"

(*Might not be needed*)
definition(in qft) j_to_tensor_prod_rest :: "nat\<Rightarrow>complex Matrix.mat" ("[j] _" 75) where (*Not good to overload?*)
"[j] k = pow_tensor_list (rev (j_to_list k)) k"

definition(in qft) binary_fraction::"nat \<Rightarrow> nat \<Rightarrow> complex" ("bf _ _") where
"binary_fraction l m \<equiv> (\<Sum>i\<in>{l..m}. ((bin_rep n j_dec)!i) /2^(i-l+1) )"

definition phase_shift:: "nat \<Rightarrow> complex Matrix.mat" ("R _") where (*Not needed*)
"R k \<equiv> Matrix.mat 2 2 (\<lambda>(i,j). if i = j then (if i = 0 then 1 else (exp (2*pi*\<i>/2^k))) else 0)"

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
proof -
  show "dim_row (SWAP_all k t) = 2^(k+2+t)"
    by (simp add: Id_def SWAP_all_def SWAP_def power_add)
next
  show "dim_col (SWAP_all k t) = 2^(k+2+t)"
    by (simp add: Id_def SWAP_all_def SWAP_def power_add)
qed


lemma(in qft) app_SWAP_all:
  assumes "k\<ge>1" and "t\<ge>1"
      and "dim_row v = 2" and "dim_row w = 2" 
      and "dim_col v = 1" and "dim_col w = 1" 
      and "length xs = k" and "length ys = t"
      and "\<forall>x \<in> set xs. dim_row x = 2" and "\<forall>y \<in> set ys. dim_row y = 2"
      and "\<forall>x \<in> set xs. dim_col x = 1" and "\<forall>y \<in> set ys. dim_col y = 1"
  shows "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) = ((pw xs k) \<Otimes> w \<Otimes> v \<Otimes> (pw ys t))"
proof-
  have "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) = ((Id k) \<Otimes> SWAP \<Otimes> (Id t)) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t))"
    using SWAP_all_def by auto
  then have "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) = ((Id k) \<Otimes> (SWAP \<Otimes> (Id t))) * ((pw xs k) \<Otimes> (v \<Otimes> w \<Otimes> (pw ys t)))"
    using tensor_mat_is_assoc by auto
  moreover have "dim_col (Id k) = dim_row (pw xs k)"  
    using Id_def pow_tensor_list_dim_row assms by (metis index_one_mat(3))
  moreover have "dim_col (SWAP \<Otimes> (Id t)) = dim_row (v \<Otimes> w \<Otimes> (pw ys t))" 
    using Id_def assms pow_tensor_list_dim_row'[of t ys 2] by (simp add: SWAP_def)
  moreover have "dim_col (Id k) > 0" and "dim_col (SWAP \<Otimes> (Id t)) > 0" and
                "dim_col (pw xs k) > 0" and "dim_col (v \<Otimes> w \<Otimes> (pw ys t)) > 0" 
    apply (auto simp: Id_def SWAP_def assms pow_tensor_list_dim_col'[of k xs] pow_tensor_list_dim_col'[of t ys])
    using assms(1) assms(11) assms(7) pow_tensor_list_dim_col apply auto[1]
    using assms(12) assms(2) assms(8) pow_tensor_list_dim_col by auto
  ultimately have "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) =
              ((Id k)*(pw xs k)) \<Otimes> ((SWAP \<Otimes> (Id t)) * (v \<Otimes> w \<Otimes> (pw ys t)))"
    using mult_distr_tensor by auto
  then have "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) =
             ((pw xs k)) \<Otimes> ((SWAP \<Otimes> (Id t)) * (v \<Otimes> w \<Otimes> (pw ys t)))" 
    using Id_def \<open>dim_col (Id k) = dim_row (pw xs k)\<close> by auto
  moreover have "dim_col SWAP = dim_row (v \<Otimes> w)" using assms by (simp add: SWAP_def)
  moreover have "dim_col (Id t) = dim_row (pw ys t)" using Id_def pow_tensor_list_dim_row'[of t ys] assms 
    by (metis index_one_mat(3) pow_tensor_list_dim_row)
  moreover have "dim_col SWAP > 0" and "dim_col (v \<Otimes> w) > 0" and "dim_col (Id t) > 0" and "dim_col (pw ys t) > 0" 
    apply (auto simp: SWAP_def assms Id_def pow_tensor_list_dim_col'[of t ys]) 
    using assms(12) assms(2) assms(8) pow_tensor_list_dim_col by auto
  ultimately have "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) =
                   ((pw xs k)) \<Otimes> ((SWAP * (v \<Otimes> w)) \<Otimes> ((Id t) * (pw ys t)))" 
    using mult_distr_tensor by auto
  then have "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) =
                   ((pw xs k)) \<Otimes> ((SWAP * (v \<Otimes> w)) \<Otimes> (pw ys t))" 
    using Id_def \<open>dim_col (Id t) = dim_row (pw ys t)\<close> by auto
  then have "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) =
                   ((pw xs k)) \<Otimes> ((w \<Otimes> v) \<Otimes> (pw ys t))" 
    using assms app_SWAP by auto
  then show "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) = ((pw xs k) \<Otimes> w \<Otimes> v \<Otimes> (pw ys t))"
    using tensor_mat_is_assoc by auto
qed


(*Could go into generic mult function would be more confusing to understand though*)
fun(in qft)pow_SWAP_front:: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("fSWAP _ _" 75)  where
  "(fSWAP (Suc 0) t) = SWAP_all (Suc 0) t"  
| "(fSWAP (Suc k) t) = (fSWAP k (t+1)) * (SWAP_all k t)"

lemma(in qft) pow_SWAP_front_dim:
  assumes "k\<ge>1" 
  shows "dim_row (fSWAP k t) = 2^(k+2+t)"
  and "dim_col (fSWAP k t) = 2^(k+2+t)" sorry
(*proof(rule ind_from_1[of k])
  show "k\<ge>1" using assms by auto
next
  fix k
  assume a0: "k\<ge>1"
  and IH: "dim_row (fSWAP k t) = 2^(k+2+t)"
  then have "dim_row (fSWAP (Suc k) t) = dim_row ((fSWAP k (t+1)) * (SWAP_all k t))" 
    by (metis One_nat_def Suc_le_D pow_SWAP_front.simps(2))
  moreover have "dim_col (SWAP_all k t) = 2^(k+2+t)" sorry
  ultimately have "dim_row (fSWAP (Suc k) t) = 2^(k+2+t)" using IH sorry*)


declare[[show_types]]
lemma(in qft) app_fSWAP:
  fixes k m::nat 
  assumes "k\<ge>1" and "m>k"
      and "dim_row v = 2" and "dim_col v = 1" 
      and "\<forall>x \<in> set xs. dim_row x = 2" and "\<forall>y \<in> set ys. dim_row y = 2" (*Need to go into show :( *)
      and "\<forall>x \<in> set xs. dim_col x = 1" and "\<forall>y \<in> set ys. dim_col y = 1"

  shows "\<forall>xs ys. length xs = k \<and> length ys = m-k\<longrightarrow> (fSWAP k (m-k)) * ((pw xs k) \<Otimes> v \<Otimes>(pw ys (m-k))) = v \<Otimes> (pw xs k) \<Otimes> (pw ys (m-k))"
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
      using app_SWAP_all assms a0 a1 by auto
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

(*Not quite sure if its not bf 0 (k-1) or something else but general idea should work*)


(*These are sometimes to specific and need to be generalized with current qubit and swapping target qubit. So they work on 
all qubits of j. *)

lemma(in qft) app_Id_fSWAP:
  assumes "length xs = k" and "k\<ge>1" and "m>k"
    and  "dim_row v = 2"  and "dim_col v = 1"
  shows "(Id 1 \<Otimes> (fSWAP k (m-k))) * ((qr k) \<Otimes> (pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k)))
= (qr k) \<Otimes> v \<Otimes> (pw xs k) \<Otimes> (pw ys (m-k))"
proof-
  have "dim_col (Id 1) = dim_row (qr k)" by (simp add: Id_def qr_def)
  moreover have "dim_col (fSWAP k (m-k)) = dim_row ((pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k)))" 
    using pow_SWAP_front_dim assms pow_tensor_list_dim_row[of xs k] pow_tensor_list_dim_row[of ys "m-k"] tensor_mat_is_assoc 
    by (smt app_fSWAP dim_row_tensor_mat index_mult_mat(2) mult.commute)
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



fun pow_mult :: "(complex Matrix.mat) list \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("pm _ _" 75)  where
  "(pm (Cons x []) 0) = x"  
| "(pm (Cons x xs) (Suc k)) = x * (pm xs k)"


value "[k . k<-[(0::nat),1]]"
(*How does list comprehension work?*)
(*Might need to rev this*)
abbreviation(in qft) \<psi>\<^sub>1 where 
  "\<psi>\<^sub>1 \<equiv> pow_tensor_list [qr (nat k). k<-[1..n] ] n"

lemma(in qft)
  shows "G k * ((pow_tensor_list [G (nat i). i<-[1..k]] k) \<Otimes> ([j] (n-k))) = ((pow_tensor_list [G (nat i). i<-[1..(k+1)]] (k+1)) \<Otimes> ([j] (n-k-1)))"
  sorry

lemma(in qft)
  shows "(aCR (Suc m) (n-(Suc m))) *
((pow_tensor_list [G (nat i). i<-[1..(m+1)]] (m+1)) 
\<Otimes> (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1/sqrt(2) else 1/sqrt(2)*exp(2*pi*\<i>*bf (m+1) (m+1))))  
\<Otimes> ([j] (n-m-1)))
= 
((pow_tensor_list [G (nat i). i<-[1..(m+1)]] (m+1)) 
\<Otimes> (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1/sqrt(2) else 1/sqrt(2)*exp(2*pi*\<i>*bf (m+1) (m+1))))  
\<Otimes> ([j] (n-m-1)))"






lemma(in qft)
  assumes "(bin_rep n j_dec)!m = 1" and "m<n" (*Change def of [j] n and extend to smaller equal*)
  shows "[j] (n-m) = zero \<Otimes> [j] (n-m-1)" 
proof-
 have "[j] (n-m) = pw (rev (j_to_list (n-m))) (n-m)" 
   by (simp add: j_to_tensor_prod_rest_def)
  have "last (rev (j_to_list (n-m))) = hd (j_to_list (n-m))" sorry
  have "(rev (j_to_list (n-m))) = butlast (rev (j_to_list (n-m))) @ [last (rev (j_to_list (n-m)))]" sorry
  then have "[j] (n-m) = hd (j_to_list (n-m)) \<Otimes> (pw (rev (j_to_list (n-m))) (n-m-1))" sorry
  moreover have "hd (j_to_list (n-m)) = one" sorry
  show "[j] (n-m) = zero \<Otimes> [j] (n-m-1)" sorry
qed

lemma(in qft)
  shows "(bin_rep n j_dec)!m = 0 \<longrightarrow> [j] (n-m) = zero \<Otimes> [j] (n-m-1)" sorry


lemma(in qft) h1:
  assumes "m\<ge>1"
  shows "m\<le>n \<longrightarrow> (pow_mult [G (nat k). k<-[1..m]] m) * [j] = ((pow_tensor_list [G (nat i). i<-[1..(m+1)]] (m+1)) \<Otimes> ([j] (n-m)))"
proof(rule ind_from_1[of m])
  fix m::nat
  assume "m\<ge>1"
  and IH:"(pow_mult [G (nat k). k<-[1..m]] m) * [j] = ((pow_tensor_list [G (nat i). i<-[1..(m+1)]] (m+1)) \<Otimes> ([j] (n-m)))"
  then have "(pow_mult [G (nat k). k<-[1..(Suc m)]] (Suc m)) * [j]
       = (G (Suc m) * (pow_mult [G (nat k). k<-[1..m]] m)) * [j]" sorry
  then have "(pow_mult [G (nat k). k<-[1..(Suc m)]] (Suc m)) * [j] 
       = G (Suc m) * ((pow_mult [G (nat k). k<-[1..m]] m) * [j])" sorry
  then have "(pow_mult [G (nat k). k<-[1..(Suc m)]] (Suc m)) * [j] 
       = G (Suc m) * ((pow_tensor_list [G (nat i). i<-[1..(m+1)]] (m+1)) \<Otimes> ([j] (n-m)))" sorry
  then have "(pow_mult [G (nat k). k<-[1..(Suc m)]] (Suc m)) * [j] 
       = ((aCR (Suc m) (n-(Suc m))) * (Id (Suc m) \<Otimes> H \<Otimes> Id (n-(Suc m)))) * ((pow_tensor_list [G (nat i). i<-[1..(m+1)]] (m+1)) \<Otimes> ([j] (n-m)))" sorry
  
  have "(pow_mult [G (nat k). k<-[1..m]] m) * [j] = ((pow_tensor_list [G (nat i). i<-[1..(m+1)]] (m+1)) \<Otimes> ([j] (n-m)))"
  proof(rule disjE)
    show "(bin_rep n j_dec)!m = 1 \<or> (bin_rep n j_dec)!m = 0" sorry
  next
    assume "(bin_rep n j_dec)!m = 1"
    then have "(pow_mult [G (nat k). k<-[1..(Suc m)]] (Suc m)) * [j] 
       = ((aCR (Suc m) (n-(Suc m))) * (Id (Suc m) \<Otimes> H \<Otimes> Id (n-(Suc m)))) * ((pow_tensor_list [G (nat i). i<-[1..(m+1)]] (m+1)) \<Otimes> zero \<Otimes> ([j] (n-m-1)))" sorry
    have "(Id (Suc m) \<Otimes> H \<Otimes> Id (n-(Suc m))) * ((pow_tensor_list [G (nat i). i<-[1..(m+1)]] (m+1)) \<Otimes> ([j] (n-m)))
      = ((pow_tensor_list [G (nat i). i<-[1..(m+1)]] (m+1)) \<Otimes> 
        (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1/sqrt(2) else 1/sqrt(2)*exp(2*pi*\<i>*bf (m+1) (m+1))))  \<Otimes> ([j] (n-m-1)))" sorry
have "(aCR (Suc m) (n-(Suc m))) *
        (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1/sqrt(2) else 1/sqrt(2)*exp(2*pi*\<i>*bf (m+1) (m+1))))  \<Otimes> ([j] (n-m-1)))" sorry








lemma(in qft)
  shows "(pow_mult [G (nat k). k<-[1..n]] n)* [j] = \<psi>\<^sub>1"
  using h1[of n] sorry






(*Make this more general, this will appear in the induction showing what the result of applying all necessary Ri is*)
lemma(in qft)
  shows "(R\<^sub>m (n-m) (n-k)) * (H \<Otimes> Id (n-k)) * ([j] k) 
= (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then (1::complex)/sqrt(2) else exp(complex_of_real (2*pi)*\<i>*(bf 0 (k+1))) * 1/sqrt(2))) \<Otimes> ([j] (k-1))"
  sorry

(*Will not be needed anymore*)
(*Gives the unit vector corresponding to |j\<^sub>sj\<^sub>s\<^sub>+\<^sub>1,..,j\<^sub>n> for given s. *)
(*E.g. n=3 j=5, 101 is shortened to 01 (start=1) or 1 (start=0)*)
definition(in qft) unit_vec_j:: "nat \<Rightarrow> complex Matrix.mat" ("UV _") where
"UV start \<equiv> Matrix.mat (2^(n-start)) 1 (\<lambda>(i,j). if (i = j mod 2^(n-start)) then 1 else 0)"

