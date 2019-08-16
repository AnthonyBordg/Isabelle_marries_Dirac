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

fun pow_mult :: "complex Matrix.mat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("pm _ _" 75)  where
  "(pm A 0) = A"  
| "(pm A (Suc k)) = A * (pm A k)"

(*TODO: Would exchanging the arguments help with induction problem?*)
fun pow_tensor_list :: "((complex Matrix.mat) list) \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("pw _ _" 75)  where
  "(pw (Cons x []) (Suc 0)) = x"  |
  "(pw (Cons x xs) (Suc k)) = (pw xs k) \<Otimes> x"

(*Missing: result is gate, state,... Easy to proof*)

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
"[j] = pow_tensor_list (j_to_list n) n"

(*Added rev on a whim look into it*)
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

(*I did this proof adhoc there is certainly a much nicer one*)
lemma(in qft) app_controlled_phase_shift_zero:
  fixes r::nat
  assumes "r < n" and "((bin_rep n j_dec)!(r+1)) = 1"
  defines "v \<equiv> (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then (1::complex)/sqrt(2) else (exp (complex_of_real (2*pi)*\<i>*(bf 0 r))) * 1/sqrt(2)))"
      and "w \<equiv> (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then (1::complex)/sqrt(2) else (exp (complex_of_real (2*pi)*\<i>*(bf 0 (r+1)))) * 1/sqrt(2)))"
  shows "(CR (r+2)) * (v \<Otimes> |zero\<rangle>) = w \<Otimes> |zero\<rangle>"
proof
  fix i j::nat
  assume "i < Matrix.dim_row (w \<Otimes> |zero\<rangle>)" and "j < Matrix.dim_col (w \<Otimes> |zero\<rangle>)" 
  then have f0: "i<4 \<and> j=0" using ket_vec_def v_def w_def by auto
  then have "((CR (r+2)) * (v \<Otimes> |zero\<rangle>)) $$ (i,j) 
           = (\<Sum>k\<in>{0,1,2,3}. ((CR (r+2)) $$ (i,k)) * ((v \<Otimes> |zero\<rangle>) $$ (k,j)))" 
    using f0 ket_vec_def v_def set_4 atLeast0LessThan controlled_phase_shift_def by auto
  then have f1: "((CR (r+2)) * (v \<Otimes> |zero\<rangle>)) $$ (i,j) 
           = ((CR (r+2)) $$ (i,0)) * (1::complex)/sqrt(2)
           + ((CR (r+2)) $$ (i,2)) * exp (complex_of_real (2*pi) *\<i>*(bf 0 r))*1/sqrt(2)" 
    using f0 ket_vec_def v_def by auto
  moreover have "i=0 \<longrightarrow> ((CR (r+2)) * (v \<Otimes> |zero\<rangle>)) $$ (i,j) = 1/sqrt(2)"
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=0 \<longrightarrow> (w \<Otimes> |zero\<rangle>) $$ (i,j) = 1/sqrt(2)" 
    using w_def ket_vec_def f0 by auto
  moreover have "i=1 \<longrightarrow> ((CR (r+2)) * (v \<Otimes> |zero\<rangle>)) $$ (i,j) = 0"
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=1 \<longrightarrow> (w \<Otimes> |zero\<rangle>) $$ (i,j) = 0" 
    using w_def ket_vec_def f0 by auto
  moreover have "i=2 \<longrightarrow> ((CR (r+2)) * (v \<Otimes> |zero\<rangle>)) $$ (i,j) 
           = (exp (complex_of_real (2*pi)*\<i>*(bf 0 (r+1)))) *1/sqrt(2)" 
  proof-
   have "i=2 \<longrightarrow> ((CR (r+2)) * (v \<Otimes> |zero\<rangle>)) $$ (i,j) 
           = (exp (complex_of_real (2*pi)*\<i>*(bf 0 r))) * (exp (complex_of_real (2*pi)*\<i>*1/2^(r+2))) * 1/sqrt(2)" 
      using controlled_phase_shift_def f1 by auto
   moreover have "exp (complex_of_real (2*pi)*\<i>*1/2^(r+2)*(bin_rep n j_dec)!(r+1)) = exp (complex_of_real (2*pi)*\<i>*1/2^(r+2)) " using assms by auto
   ultimately show "i=2 \<longrightarrow> ((CR (r+2)) * (v \<Otimes> |zero\<rangle>)) $$ (i,j) 
           = (exp (complex_of_real (2*pi)*\<i>*(bf 0 (r+1)))) * 1/sqrt(2)" using exp_mult by (smt assms(2) of_nat_1)
 qed
  moreover have "i=2 \<longrightarrow> (w \<Otimes> |zero\<rangle>) $$ (i,j) = exp (complex_of_real (2*pi)*\<i>*(bf 0 (r+1)))*1/sqrt(2)" 
    using w_def ket_vec_def f0 by auto
  moreover have "i=3 \<longrightarrow> ((CR (r+2)) * (v \<Otimes> |zero\<rangle>)) $$ (i,j) = 0"
    using controlled_phase_shift_def f1 by auto 
  moreover have "i=3 \<longrightarrow> (w \<Otimes> |zero\<rangle>) $$ (i,j) = 0" 
    using w_def ket_vec_def f0 by auto
  moreover have "i\<in>{0,1,2,3}" using f0 by auto
  ultimately show "((CR (r+2)) * (v \<Otimes> |zero\<rangle>)) $$ (i,j) = (w \<Otimes> |zero\<rangle>) $$ (i,j)" 
    using f0 ket_vec_def w_def by (smt set_four)
next
  show "dim_row ((CR (r+2)) * (v \<Otimes> |zero\<rangle>)) = dim_row (w \<Otimes> |zero\<rangle>)" 
    by (simp add: controlled_phase_shift_def ket_vec_def w_def)
next
  show "dim_col ((CR (r+2)) * (v \<Otimes> |zero\<rangle>)) = dim_col (w \<Otimes> |zero\<rangle>)"
    using ket_vec_def controlled_phase_shift_def v_def w_def by auto
qed

lemma(in qft) app_controlled_phase_shift_one: 
  fixes r::nat
  assumes "r < n" and "((bin_rep n j)!(r+1)) = 0"
  shows "(CR k) * ((Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then (1::complex)/sqrt(2) else exp (complex_of_real (2*pi)*\<i>*(bf 0 r))*1/sqrt(2))) \<Otimes> |one\<rangle>)
       = (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then (1::complex)/sqrt(2) else exp (complex_of_real (2*pi)*\<i>*(bf 0 r))*1/sqrt(2))) \<Otimes> |one\<rangle>"
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

lemma 
  assumes "dim_row v = 2" and "dim_col v = 1"
      and "dim_row w = 2" and "dim_col w = 1"
  shows "SWAP * (v \<Otimes> w) = w \<Otimes> v"
  sorry

definition(in qft) SWAP_all :: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" where
"SWAP_all k t \<equiv>  (Id k) \<Otimes> SWAP \<Otimes> (Id t)"


lemma(in qft) app_SWAP_all:
  shows "(SWAP_all k t) * ((pw xs k) \<Otimes> v \<Otimes> w \<Otimes> (pw ys t)) = ((pw xs k) \<Otimes> w \<Otimes> v \<Otimes> (pw ys t))"
  sorry



fun(in qft)pow_SWAP_front:: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("fSWAP _ _" 75)  where
  "(fSWAP (Suc 0) t) = SWAP_all (Suc 0) t"  
| "(fSWAP (Suc k) t) = (fSWAP k (t+1)) * (SWAP_all k t)"

declare[[show_types]]
lemma(in qft) app_fSWAP:
  fixes k m::nat 
  assumes "k\<ge>1"
  shows "\<forall>xs ys. length xs = k \<longrightarrow> (fSWAP k (m-k)) * ((pw xs k) \<Otimes> v \<Otimes>(pw ys (m-k))) = v \<Otimes> (pw xs k) \<Otimes> (pw ys (m-k))"
proof(rule ind_from_1[of k])
  show "k\<ge>1" using assms by auto
next
  show "\<forall>xs ys. length xs = 1 \<longrightarrow> (fSWAP 1 (m-1)) * ((pw xs 1) \<Otimes> v \<Otimes>(pw ys (m-1))) = v \<Otimes> (pw xs 1) \<Otimes> (pw ys (m-1))" sorry
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


lemma(in qft)
  assumes "length xs =k" and "k\<ge>1"
  shows "(Id 1 \<Otimes> (fSWAP k t)) * 
  ((Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then (1::complex)/sqrt(2) else (exp (complex_of_real (2*pi)*\<i>*(bf 0 k)))*1/sqrt(2))) \<Otimes> (pw xs k) \<Otimes> v \<Otimes> (pw ys (m-k)))
= (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then (1::complex)/sqrt(2) else exp(complex_of_real (2*pi)*\<i>*(bf 0 k)) * 1/sqrt(2)) ) \<Otimes> v \<Otimes> (pw xs k) \<Otimes> (pw ys (m-k))"
  sorry

(*Needs some assumptions abount bin_rep_values. Should already use j probably*)
lemma(in qft) 
  assumes "k < n" and "k\<ge>1" and "((bin_rep n j_dec)!(k+1)) = 1 \<or> ((bin_rep n j_dec)!(k+1)) = 0" (*Can be eliminated*)
  shows "(CR k * Id m) * 
   ((Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then (1::complex)/sqrt(2) else (exp (complex_of_real (2*pi)*\<i>*(bf 0 k)))*1/sqrt(2))) \<Otimes> v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k)))
=  (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then (1::complex)/sqrt(2) else exp(complex_of_real (2*pi)*\<i>*(bf 0 (k+1))) * 1/sqrt(2))) \<Otimes> v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k))"
sorry

lemma(in qft) 
  shows "(Id 1 \<Otimes> ((fSWAP k t)\<^sup>\<dagger>)) * ((Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then (1::complex)/sqrt(2) else (exp (complex_of_real (2*pi)*\<i>*(bf 0 (k+1))))*1/sqrt(2))) \<Otimes> v \<Otimes> (pw xs k) \<Otimes>(pw ys (m-k)))
  = (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then (1::complex)/sqrt(2) else exp(complex_of_real (2*pi)*\<i>*(bf 0 (k+1))) * 1/sqrt(2))) \<Otimes> (pw xs k)\<Otimes> v \<Otimes>(pw ys (m-k))"
  sorry

(*k is the index of the qubit that should be added to the binary fraction. c is the current qubit *)
definition(in qft) app_CR::"nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("R\<^sub>_ _" 75) where
"app_CR k c \<equiv> (Id c) \<Otimes> ((Id 1 \<Otimes> ((fSWAP k (n-c-k))\<^sup>\<dagger>)) *(CR k * Id (n-c)) * (Id 1 \<Otimes> (fSWAP k (n-c-k)))) "

(*Make this more general, this will appear in the induction showing what the result of applying all necessary Ri is*)
lemma(in qft)
  shows "(R\<^sub>m (n-m) (n-k)) * (H \<Otimes> Id (n-k)) * ([j] k) 
= (Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then (1::complex)/sqrt(2) else exp(complex_of_real (2*pi)*\<i>*(bf 0 (k+1))) * 1/sqrt(2))) \<Otimes> ([j] (k-1))"
  sorry

value "[k<-[0,1].true]"
(*How does list comprehension work?*)
(*Might need to rev this*)
abbreviation(in qft) \<psi>\<^sub>1 where "\<psi>\<^sub>1 \<equiv> pow_tensor_list [\<forall>k\<in>{1..n}.(Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then (1::complex)/sqrt(2) else exp (complex_of_real (2*pi)*\<i>*(bf 0 k))*1/sqrt(2) ))] n"








(*Will not be needed anymore*)
(*Gives the unit vector corresponding to |j\<^sub>sj\<^sub>s\<^sub>+\<^sub>1,..,j\<^sub>n> for given s. *)
(*E.g. n=3 j=5, 101 is shortened to 01 (start=1) or 1 (start=0)*)
definition(in qft) unit_vec_j:: "nat \<Rightarrow> complex Matrix.mat" ("UV _") where
"UV start \<equiv> Matrix.mat (2^(n-start)) 1 (\<lambda>(i,j). if (i = j mod 2^(n-start)) then 1 else 0)"

