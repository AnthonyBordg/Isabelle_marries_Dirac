(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk *)

theory Binary_Nat
imports
  HOL.Nat
  HOL.List
begin

primrec bin_rep_aux:: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "bin_rep_aux 0 m = [m]"
| "bin_rep_aux (Suc n) m = m div 2^n # bin_rep_aux n (m mod 2^n)"

lemma length_of_bin_rep_aux:
  fixes n m:: nat
  assumes "m < 2^n"
  shows "length (bin_rep_aux n m) = n+1" 
  using assms
proof(induction n arbitrary: m)
  case 0
  then show "length (bin_rep_aux 0 m) = 0 + 1" by simp
next
  case (Suc n)
  assume a0:"\<And>m. m < 2^n \<Longrightarrow> length (bin_rep_aux n m) = n + 1" and "m < 2^(Suc n)"
  then show "length (bin_rep_aux (Suc n) m) = Suc n + 1" using a0 by simp
qed

lemma last_of_bin_rep_aux:
  fixes n m:: nat
  assumes "m < 2^n"
  shows "last (bin_rep_aux n m) = 0" sorry

lemma bin_rep_aux_index:
  fixes n m i:: nat
  assumes "m < 2^n" and "i \<le> n"
  shows "bin_rep_aux n m ! i = (m mod 2^(n+1-i)) div 2^(n-i)" sorry

lemma bin_rep_aux_coeff:
  fixes n m i:: nat
  assumes "m < 2^n" and "i \<le> n"
  shows "bin_rep_aux n m ! i = 0 \<or> bin_rep_aux n m ! i = 1" 
  using assms
proof(induction n arbitrary: m)
  case 0
  assume "m < 2^0" and "i \<le> 0"
  then show "bin_rep_aux 0 m ! i = 0 \<or> bin_rep_aux 0 m ! i = 1" by simp
next
  case (Suc n)
  assume a0:"\<And>m. m < 2 ^ n \<Longrightarrow> i \<le> n \<Longrightarrow> bin_rep_aux n m ! i = 0 \<or> bin_rep_aux n m ! i = 1" 
and a1:"m < 2 ^ Suc n" and a2:"i \<le> Suc n"
  then show "bin_rep_aux (Suc n) m ! i = 0 \<or> bin_rep_aux (Suc n) m ! i = 1"
  proof-
    have "m div 2^n \<le> 1" 
      using a1 less_mult_imp_div_less by fastforce
    moreover have "m mod 2^n < 2^n" by simp
    ultimately show ?thesis using a0 a2 bin_rep_aux.simps(2) bin_rep_aux_index sorry
  qed
qed

definition bin_rep:: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
"bin_rep n m = butlast (bin_rep_aux n m)"

lemma bin_rep_eq:
  fixes n m:: nat
  assumes "m < 2^n"
  shows "m = (\<Sum>i<n. bin_rep n m ! i * 2^(n-1-i))" sorry

end