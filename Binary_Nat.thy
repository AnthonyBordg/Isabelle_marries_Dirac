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
  then show "length (bin_rep_aux (Suc n) m) = Suc n + 1" 
    using a0 by simp
qed

lemma bin_rep_aux_neq_nil:
  fixes n m:: nat
  shows "bin_rep_aux n m \<noteq> []" 
  using bin_rep_aux.simps by (metis list.distinct(1) old.nat.exhaust)

lemma last_of_bin_rep_aux:
  fixes n m:: nat
  assumes "m < 2^n"
  shows "last (bin_rep_aux n m) = 0"
  using assms
proof(induction n arbitrary: m)
  case 0
  assume "m < 2^0"
  then show "last (bin_rep_aux 0 m) = 0" by simp
next
  case (Suc n)
  assume a0:"\<And>m. m < 2^n \<Longrightarrow> last (bin_rep_aux n m) = 0" and "m < 2^(Suc n)"
  then show "last (bin_rep_aux (Suc n) m) = 0" 
    using bin_rep_aux_neq_nil by simp
qed

lemma mod_mod_power_cancel:
  fixes m n p:: nat
  assumes "m \<le> n"
  shows "p mod 2^n mod 2^m = p mod 2^m" 
  using assms by (simp add: dvd_power_le mod_mod_cancel)
    
lemma bin_rep_aux_index:
  fixes n m i:: nat
  assumes "n \<ge> 1" and "m < 2^n" and "i \<le> n"
  shows "bin_rep_aux n m ! i = (m mod 2^(n-i)) div 2^(n-1-i)"
  using assms
proof(induction n arbitrary: m i rule: nat_induct_at_least)
  case base
  assume "m < 2^1" and "i \<le> 1"
  then show "bin_rep_aux 1 m ! i = m mod 2^(1-i) div 2^(1-1-i)" 
    using bin_rep_aux.simps diff_is_0_eq' div_by_1 le_0_eq le_Suc_eq mod_less nth_Cons' 
numeral_1_eq_Suc_0 numeral_One power_0 zero_less_one by auto
next
  case (Suc n)
  assume a0:"\<And>m i. m < 2^n \<Longrightarrow> i \<le> n \<Longrightarrow> bin_rep_aux n m ! i = m mod 2 ^ (n-i) div 2^(n-1-i)"
and a1:"m < 2^(Suc n)" and a2:"i \<le> Suc n"
  then show "bin_rep_aux (Suc n) m ! i = m mod 2^(Suc n - i) div 2^(Suc n - 1 - i)"
  proof-
    have "bin_rep_aux (Suc n) m = m div 2^n # bin_rep_aux n (m mod 2^n)" by simp
    then have f0:"bin_rep_aux (Suc n) m ! i = (m div 2^n # bin_rep_aux n (m mod 2^n)) ! i" by simp
    then have "bin_rep_aux (Suc n) m ! i = m div 2^n" if "i = 0" using that by simp
    then have f1:"bin_rep_aux (Suc n) m ! i = m mod 2^(Suc n - i) div 2^(Suc n - 1 - i)" if "i = 0"
    proof-
      have "m mod 2^(Suc n - i) = m" 
        using that a1 by simp
      then have "m mod 2^(Suc n - i) div 2^(Suc n - 1 - i) = m div 2^n" 
        using that by simp
      thus ?thesis by (simp add: that)
    qed
    then have "bin_rep_aux (Suc n) m ! i = bin_rep_aux n (m mod 2^n) ! (i-1)" if "i \<ge> 1"
      using that f0 by simp
    then have f2:"bin_rep_aux (Suc n) m ! i = ((m mod 2^n) mod 2^(n - (i - 1))) div 2^(n - 1 - (i - 1))" if "i \<ge> 1"
      using that a0 Suc.prems(2) by simp
    then have f3:"bin_rep_aux (Suc n) m ! i = ((m mod 2^n) mod 2^(Suc n - i)) div 2^(Suc n - 1 - i)" if "i \<ge> 1"
      using that by simp
    then have "bin_rep_aux (Suc n) m ! i = m mod 2^(Suc n - i) div 2^(Suc n - 1 - i)" if "i \<ge> 1" 
    proof-
      have "Suc n - i \<le> n" using that by simp
      then have "m mod 2^n mod 2^(Suc n - i) = m mod 2^(Suc n - i)" 
        using that mod_mod_power_cancel[of "Suc n - i" "n" "m"] by simp
      thus ?thesis 
        using that f3 by simp
    qed
    thus ?thesis using f1 f2
      using linorder_not_less by blast
  qed
qed

lemma bin_rep_aux_coeff:
  fixes n m i:: nat
  assumes "m < 2^n" and "i \<le> n"
  shows "bin_rep_aux n m ! i = 0 \<or> bin_rep_aux n m ! i = 1" 
  using assms
proof(induction n arbitrary: m i)
  case 0
  assume "m < 2^0" and "i \<le> 0"
  then show "bin_rep_aux 0 m ! i = 0 \<or> bin_rep_aux 0 m ! i = 1" by simp
next
  case (Suc n)
  assume a0:"\<And>m i. m < 2 ^ n \<Longrightarrow> i \<le> n \<Longrightarrow> bin_rep_aux n m ! i = 0 \<or> bin_rep_aux n m ! i = 1" 
and a1:"m < 2^Suc n" and a2:"i \<le> Suc n"
  then show "bin_rep_aux (Suc n) m ! i = 0 \<or> bin_rep_aux (Suc n) m ! i = 1"
  proof-
    have "bin_rep_aux (Suc n) m ! i = (m div 2^n # bin_rep_aux n (m mod 2^n)) ! i" by simp
    moreover have "\<dots> = bin_rep_aux n (m mod 2^n) ! (i - 1)" if "i \<ge> 1"
      using that by simp
    moreover have "m mod 2^n < 2^n" by simp
    ultimately have "bin_rep_aux (Suc n) m ! i = 0 \<or> bin_rep_aux (Suc n) m ! i = 1" if "i\<ge>1"
      using that a0[of "m mod 2^n" "i-1"] a2 by simp
    moreover have "m div 2^n \<le> 1" 
      using a1 less_mult_imp_div_less by fastforce
    ultimately show ?thesis
      by (metis One_nat_def Suc_pred bin_rep_aux.simps(2) less_Suc_eq_le linorder_not_less neq0_conv 
nth_Cons_0)
  qed
qed

definition bin_rep:: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
"bin_rep n m = butlast (bin_rep_aux n m)"

lemma length_of_bin_rep:
  fixes n m:: nat
  assumes "m < 2^n"
  shows "length (bin_rep n m) = n"
  using assms length_of_bin_rep_aux bin_rep_def by simp

lemma bin_rep_index:
  fixes n m i:: nat
  assumes "n \<ge> 1" and "m < 2^n" and "i < n"
  shows "bin_rep n m ! i = (m mod 2^(n-i)) div 2^(n-1-i)"
proof-
  have "bin_rep n m ! i = bin_rep_aux n m ! i"
    using bin_rep_def length_of_bin_rep nth_butlast assms(3)
    by (simp add: nth_butlast assms(2))
  thus ?thesis
    using assms bin_rep_aux_index by simp
qed

lemma bin_rep_eq:
  fixes n m:: nat
  assumes "m < 2^n"
  shows "m = (\<Sum>i<n. bin_rep n m ! i * 2^(n-1-i))" sorry

end