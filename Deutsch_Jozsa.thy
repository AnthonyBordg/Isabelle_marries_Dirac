theory Deutsch_Jozsa
imports
  MoreTensor
  Quantum 
begin

declare [[show_abbrevs=true]]
declare [[names_short=true]]
(*There will probably be some lemmas going into Basic (maybe even Tensor) in here, 
I will transfer them when I am sure they are actually needed*)
section \<open>The Deutsch-Jozsa Algorithm\<close>


locale bob_fun =
  fixes f:: "nat \<Rightarrow> nat" and n:: "nat"
  assumes dom: "f \<in> ({(i::nat). i < 2^n} \<rightarrow>\<^sub>E {0,1})"
  assumes dim: "n \<ge> 1"

context bob_fun
begin

definition const:: "nat \<Rightarrow> bool" where 
"const c = (\<forall>x\<in>{i::nat. i < 2^n}. f x = c)"

definition is_const:: bool where 
"is_const \<equiv> const 0 \<or> const 1"

definition is_balanced:: bool where
"is_balanced \<equiv> \<exists>A B. A \<subseteq> {i::nat. i < 2^n} \<and> B \<subseteq> {i::nat. i < 2^n}
                   \<and> card A = (2^(n-1)) \<and> card B = (2^(n-1))  
                   \<and> (\<forall>x \<in> A. f(x) = 0)  \<and> (\<forall>x \<in> B. f(x) = 1)"

lemma is_balanced_inter: 
  fixes A B:: "nat set"
  assumes "\<forall>x \<in> A. f(x) = 0" and "\<forall>x \<in> B. f(x) = 1" 
  shows "A \<inter> B = {}" 
  using assms by auto

lemma is_balanced_union:
  fixes A B:: "nat set"
  assumes "A \<subseteq> {i::nat. i < 2^n}" and "B \<subseteq> {i::nat. i < 2^n}" 
      and "card A = (2^(n-1))" and "card B = (2^(n-1))" 
      and "A \<inter> B = {}"
  shows "A \<union> B = {i::nat. i < 2^n}"
proof-
  have "finite A" and "finite B" 
     apply (simp add: assms(3) card_ge_0_finite)
    apply (simp add: assms(4) card_ge_0_finite).
  then have "card(A \<union> B) = 2 * 2^(n-1)" 
    using assms(3-5) by (simp add: card_Un_disjoint)
  then have "card(A \<union> B) = 2^n"
    by (metis Nat.nat.simps(3) One_nat_def dim le_0_eq power_eq_if)
  moreover have "\<dots> = card({i::nat. i < 2^n})" by simp
  moreover have "A \<union> B \<subseteq> {i::nat. i < 2^n}" 
    using assms(1,2) by simp
  moreover have "finite ({i::nat. i < 2^n})" by simp
  ultimately show ?thesis 
    using card_subset_eq[of "{i::nat. i < 2^n}" "A \<union> B"] by simp
qed

lemma f_ge_0: "\<forall>x. (f x \<ge> 0)" by simp

lemma f_dom_not_zero: 
  shows "f \<in> ({i::nat. n \<ge> 1 \<and> i < 2^n} \<rightarrow>\<^sub>E {0,1})" 
  using dim dom by simp

lemma f_values: "\<forall>x \<in> {(i::nat). i < 2^n} .(f x = 0 \<or> f x = 1)" 
  using dom by auto


end (* bob_fun *)

locale jozsa = bob_fun +
  assumes const_or_balanced: "is_const \<or> is_balanced "

definition (in jozsa) jozsa_transform:: "complex Matrix.mat" ("U\<^sub>f") where 
"U\<^sub>f \<equiv> Matrix.mat (2^(n+1)) (2^(n+1)) (\<lambda>(i,j). if i = j then (1-f(i div 2)) else 
                                          if i = j + 1 \<and> odd i then f(i div 2) else
                                             if i = j - 1 \<and> even i \<and> j\<ge>1 then f(i div 2) else 0)"

lemma (in jozsa) jozsa_transform_dim [simp]:
  shows "dim_row U\<^sub>f = 2^(n+1)" and "dim_col U\<^sub>f = (2^(n+1))" 
  by (auto simp add: jozsa_transform_def)

lemma (in jozsa) jozsa_transform_coeff_is_zero [simp]:
  assumes "i < dim_row U\<^sub>f \<and> j < dim_col U\<^sub>f"
  shows "(i\<noteq>j \<and> \<not>(i=j+1 \<and> odd i) \<and> \<not> (i=j-1 \<and> even i \<and> j\<ge>1)) \<longrightarrow> U\<^sub>f $$ (i,j) = 0"
  using jozsa_transform_def assms by auto

lemma (in jozsa) jozsa_transform_coeff [simp]: 
  assumes "i < dim_row U\<^sub>f \<and> j < dim_col U\<^sub>f"
  shows "i = j \<longrightarrow> U\<^sub>f $$ (i,j) = 1 - f (i div 2)"
  and "i = j + 1 \<and> odd i \<longrightarrow> U\<^sub>f $$ (i,j) = f (i div 2)"
  and "j\<ge>1 \<and> i = j - 1 \<and> even i \<longrightarrow> U\<^sub>f $$ (i,j) = f (i div 2)" 
  using jozsa_transform_def assms by auto

(*Should this be a lemma on its own? could easily be integrated in main lemma (next one)*)
(*Is this version structured better than the next??? I am not sure*)
lemma (in jozsa) U\<^sub>f_mult_without_empty_summands_sum_even:  (*better name*)
  fixes i j A
  assumes "i < dim_row U\<^sub>f" and "j < dim_col A"
  and "even i" 
  and "dim_col U\<^sub>f = dim_row A"
  shows "(\<Sum>k\<in>{0..< dim_row A}. U\<^sub>f $$ (i, k) * A $$ (k, j)) =(\<Sum>k\<in>{i,i+1}. U\<^sub>f $$ (i, k) * A $$ (k, j)) "
proof-
  have "(\<Sum>k\<in>{0..< 2 ^ (n+1)}. U\<^sub>f $$ (i, k) * A $$ (k, j)) = 
             (\<Sum>k \<in> {0..<i}. U\<^sub>f $$ (i, k) * A $$ (k, j))+
             (\<Sum>k \<in> {i,i+1}. U\<^sub>f $$ (i, k) * A $$ (k, j))+
             (\<Sum>k \<in> {(i+2)..< 2^(n+1)}. U\<^sub>f $$ (i, k) * A $$ (k, j)) " 
  proof - 
    have "{0..< 2^(n+1)} = {0..<i} \<union> {i..< 2^(n+1)} 
          \<and> {i..< 2^(n+1)} = {i,i+1} \<union> {(i+2)..<2^(n+1)}" using assms(1-3) by auto
    moreover have "{0..<i} \<inter> {i,i+1} = {} 
                  \<and> {i,i+1} \<inter> {(i+2)..< 2^(n+1)} = {} 
                  \<and> {0..<i} \<inter> {(i+2)..< 2^(n+1)} = {}" using assms by auto
    ultimately show ?thesis
      using assms sum.union_disjoint  
      by (metis (no_types, lifting) finite_Un finite_atLeastLessThan is_num_normalize(1) ivl_disj_int_two(3))
  qed
  moreover have "(\<Sum>k \<in> {0..<i}. U\<^sub>f $$ (i, k) * A $$ (k, j)) = 0 " 
  proof-
    have "k \<in> {0..<i} \<longrightarrow> (i\<noteq>k \<and> \<not>(i=k+1 \<and> odd i) \<and> \<not> (i=k-1 \<and> even i \<and> k\<ge>1))" for k 
      using assms by auto
    then have "k \<in> {0..<i} \<longrightarrow> U\<^sub>f $$ (i, k) =0" for k
      by (metis assms(1) atLeastLessThan_iff jozsa_transform_coeff_is_zero jozsa_transform_dim 
          less_imp_add_positive trans_less_add1)
    then show ?thesis 
      by simp
  qed
  moreover have "(\<Sum>k \<in> {(i+2)..< 2^(n+1)}. U\<^sub>f $$ (i, k) * A $$ (k, j)) = 0 " 
  proof- 
    have  "k \<in> {(i+2)..< 2^(n+1)} \<longrightarrow> (i\<noteq>k \<and> \<not>(i=k+1 \<and> odd i) \<and> \<not> (i=k-1 \<and> even i \<and> k\<ge>1))" for k
      using assms by auto
    then have "k \<in> {(i+2)..< 2^(n+1)}\<longrightarrow> U\<^sub>f $$ (i, k) = 0" for k
      using jozsa_transform_coeff_is_zero assms  by auto
    then show ?thesis
      by simp
  qed
  moreover have  "dim_row A =  2^(n+1)" using assms by simp
  ultimately show "(\<Sum>k\<in>{0..< dim_row A}. U\<^sub>f $$ (i, k) * A $$ (k, j)) =(\<Sum>k\<in>{i,i+1}. U\<^sub>f $$ (i, k) * A $$ (k, j))"
    using assms 
    by (metis (no_types, lifting) add.left_neutral add.right_neutral)
qed

(*Second version with different structure*)
lemma (in jozsa) U\<^sub>f_mult_without_empty_summands_sum_even':  (*better name*)
  fixes i j A
  assumes "i < dim_row U\<^sub>f" and "j < dim_col A"
  and "even i" 
  and "dim_col U\<^sub>f = dim_row A"
  shows "(\<Sum>k\<in>{0..< dim_row A}. U\<^sub>f $$ (i, k) * A $$ (k, j)) =(\<Sum>k\<in>{i,i+1}. U\<^sub>f $$ (i, k) * A $$ (k, j)) "
proof-
  have "{0..< 2^(n+1)} = {0..<i} \<union> {i..< 2^(n+1)} 
        \<and> {i..< 2^(n+1)} = {i,i+1} \<union> {(i+2)..<2^(n+1)}" using assms(1-3) by auto
  moreover have "{0..<i} \<inter> {i,i+1} = {} 
        \<and> {i,i+1} \<inter> {(i+2)..< 2^(n+1)} = {} 
        \<and> {0..<i} \<inter> {(i+2)..< 2^(n+1)} = {}" using assms by auto
  ultimately have f0: "(\<Sum>k\<in>{0..< 2 ^ (n+1)}. U\<^sub>f $$ (i, k) * A $$ (k, j)) = 
             (\<Sum>k \<in> {0..<i}. U\<^sub>f $$ (i, k) * A $$ (k, j))+
             (\<Sum>k \<in> {i,i+1}. U\<^sub>f $$ (i, k) * A $$ (k, j))+
             (\<Sum>k \<in> {(i+2)..< 2^(n+1)}. U\<^sub>f $$ (i, k) * A $$ (k, j)) " 
    using assms sum.union_disjoint  
    by (metis (no_types, lifting) finite_Un finite_atLeastLessThan is_num_normalize(1) ivl_disj_int_two(3))

  have "k \<in> {0..<i} \<longrightarrow> (i\<noteq>k \<and> \<not>(i=k+1 \<and> odd i) \<and> \<not> (i=k-1 \<and> even i \<and> k\<ge>1))" for k 
    using assms by auto
  then have "k \<in> {0..<i} \<longrightarrow> U\<^sub>f $$ (i, k) =0" for k
    by (metis assms(1) atLeastLessThan_iff jozsa_transform_coeff_is_zero jozsa_transform_dim 
        less_imp_add_positive trans_less_add1)
  then have f1:"(\<Sum>k \<in> {0..<i}. U\<^sub>f $$ (i, k) * A $$ (k, j)) = 0 " 
    by simp

  have "k \<in> {(i+2)..< 2^(n+1)} \<longrightarrow> (i\<noteq>k \<and> \<not>(i=k+1 \<and> odd i) \<and> \<not> (i=k-1 \<and> even i \<and> k\<ge>1))" for k
    using assms by auto
  then have "k \<in> {(i+2)..< 2^(n+1)}\<longrightarrow> U\<^sub>f $$ (i, k) = 0" for k
    using jozsa_transform_coeff_is_zero assms  by auto
  then have f2: "(\<Sum>k \<in> {(i+2)..< 2^(n+1)}. U\<^sub>f $$ (i, k) * A $$ (k, j)) = 0 " 
    by simp

  have "dim_row A =  2^(n+1)" using assms by simp
  then show "(\<Sum>k\<in>{0..< dim_row A}. U\<^sub>f $$ (i, k) * A $$ (k, j)) =(\<Sum>k\<in>{i,i+1}. U\<^sub>f $$ (i, k) * A $$ (k, j))"
    using f0 f1 f2 assms 
    by (metis (no_types, lifting) add.left_neutral add.right_neutral)
qed

lemma (in jozsa) U\<^sub>f_mult_without_empty_summands_even: 
  fixes i j A
  assumes "i < dim_row U\<^sub>f" and "j < dim_col A"
  and "even i"
  and "dim_col U\<^sub>f = dim_row A"
  shows "(U\<^sub>f * A) $$ (i,j) = (\<Sum>k\<in>{i,i+1}. U\<^sub>f $$ (i, k) * A $$ (k, j)) "
proof -
  have "(U\<^sub>f * A) $$ (i,j) = (\<Sum> k \<in> {0 ..< dim_row A}. (U\<^sub>f $$ (i,k)) * (A $$ (k,j)))"
    using assms index_matrix_prod 
    by (simp add: atLeast0LessThan)
  then show "(U\<^sub>f * A) $$ (i,j) = (\<Sum>k\<in>{i,i+1}. U\<^sub>f $$ (i, k) * A $$ (k, j))" 
    using assms U\<^sub>f_mult_without_empty_summands_sum_even by auto
qed






lemma (in jozsa) U\<^sub>f_mult_without_empty_summands_sum_odd:  (*better name*)
  fixes i j A
  assumes "i < dim_row U\<^sub>f" and "j < dim_col A"
  and "odd i" 
  and "dim_col U\<^sub>f = dim_row A"
  shows "(\<Sum>k\<in>{0..< dim_row A}. U\<^sub>f $$ (i, k) * A $$ (k, j)) =(\<Sum>k\<in>{i-1,i}. U\<^sub>f $$ (i, k) * A $$ (k, j)) "
proof-
  have "{0..< 2^(n+1)} = {0..<(i-1)} \<union> {(i-1)..< 2^(n+1)}" using assms by auto
  moreover have "{(i-1)..< 2^(n+1)} = {i-1,i} \<union> {(i+1)..<2^(n+1)}" using assms(1-3) by auto
  moreover have "{0..<(i-1)} \<inter> {i-1,i} = {} 
                \<and> {i-1,i} \<inter> {(i+1)..< 2^(n+1)} = {} 
                \<and> {0..<(i-1)} \<inter> {(i-1)..< 2^(n+1)} = {}" 
    using assms by auto
  ultimately have f0: "(\<Sum>k \<in> {0..< 2^(n+1)}. U\<^sub>f $$ (i, k) * A $$ (k, j)) = 
             (\<Sum>k \<in> {0..<(i-1)}. U\<^sub>f $$ (i, k) * A $$ (k, j))+
             (\<Sum>k \<in> {i-1,i}. U\<^sub>f $$ (i, k) * A $$ (k, j))+
             (\<Sum>k \<in> {(i+1)..<2^(n+1)}. U\<^sub>f $$ (i, k) * A $$ (k, j)) " 
    using assms sum.union_disjoint  
    by (metis (no_types, lifting) finite_Un finite_atLeastLessThan is_num_normalize(1) ivl_disj_int_two(3))

  have "k \<in> {0..<(i-1)} \<longrightarrow> (i\<noteq>k \<and> \<not>(i=k+1 \<and> odd i) \<and> \<not> (i=k-1 \<and> even i \<and> k\<ge>1))" for k 
    using assms by auto
  then have "k \<in> {0..<(i-1)} \<longrightarrow> U\<^sub>f $$ (i, k) =0" for k
    by (metis assms(1) atLeastLessThan_iff jozsa_transform_coeff_is_zero jozsa_transform_dim 
        less_imp_add_positive less_imp_diff_less trans_less_add1)
  then have f1:"(\<Sum>k \<in> {0..<(i-1)}. U\<^sub>f $$ (i, k) * A $$ (k, j)) = 0 " 
    by simp

  have "k \<in> {(i+1)..<2^(n+1)} \<longrightarrow> (i\<noteq>k \<and> \<not>(i=k+1 \<and> odd i) \<and> \<not> (i=k-1 \<and> even i \<and> k\<ge>1))" for k
    using assms by auto
  then have "k \<in> {(i+1)..<2^(n+1)} \<longrightarrow> U\<^sub>f $$ (i, k) = 0" for k
    using jozsa_transform_coeff_is_zero assms by auto
  then have f2: "(\<Sum>k \<in> {(i+1)..<2^(n+1)}. U\<^sub>f $$ (i, k) * A $$ (k, j)) = 0 " 
    by simp

  have "dim_row A =  2^(n+1)" using assms by simp
  then show "(\<Sum>k\<in>{0..< dim_row A}. U\<^sub>f $$ (i, k) * A $$ (k, j)) =(\<Sum>k\<in>{i-1,i}. U\<^sub>f $$ (i, k) * A $$ (k, j))"
    using f0 f1 f2 assms 
    by (metis (no_types, lifting) add.left_neutral add.right_neutral)
qed








lemma (in jozsa) U\<^sub>f_mult_without_empty_summands_odd: 
  fixes i j A
  assumes "i < dim_row U\<^sub>f" and "j < dim_col A"
  and "odd i"
  and "dim_col U\<^sub>f = dim_row A"
  shows "(U\<^sub>f * A) $$ (i,j) = (\<Sum>k\<in>{i-1,i}. U\<^sub>f $$ (i, k) * A $$ (k, j)) "
proof-
  have "(U\<^sub>f * A) $$ (i,j) = (\<Sum> k \<in> {0 ..< dim_row A}. (U\<^sub>f $$ (i,k)) * (A $$ (k,j)))"
    using assms index_matrix_prod 
    by (simp add: atLeast0LessThan)
  then show "(U\<^sub>f * A) $$ (i,j) = (\<Sum>k\<in>{i-1,i}. U\<^sub>f $$ (i, k) * A $$ (k, j))" 
    using assms U\<^sub>f_mult_without_empty_summands_sum_odd by auto
qed









(*To deal with Uf it is often necessary to do a case distinction with four different cases.*)
(*TODO: until now this is only used for 
"i=j \<or> (i=j+1 \<and> odd i) \<or> (i=j-1 \<and> even i \<and> j\<ge>1) \<or> (i\<noteq>j \<and> \<not>(i=j+1 \<and> odd i) \<and> \<not> (i=j-1 \<and> even i \<and> j\<ge>1))"
should it be specialised more? I tend to keep the general one although it requires one step more in each proof*)
lemma disj_four_cases:
  assumes "A \<or> B \<or> C \<or> D"
  and "A \<Longrightarrow> P"
  and "B \<Longrightarrow> P"
  and "C \<Longrightarrow> P"
  and "D \<Longrightarrow> P"
  shows "P"
proof -
  from assms show ?thesis by blast
qed

lemma disj_four_cases':
  assumes  "i=j \<Longrightarrow> P"
  and "(i=j+1 \<and> odd i) \<Longrightarrow> P"
  and "(i=j-1 \<and> even i \<and> j\<ge>1) \<Longrightarrow> P"
  and "(i\<noteq>j \<and> \<not>(i=j+1 \<and> odd i) \<and> \<not> (i=j-1 \<and> even i \<and> j\<ge>1)) \<Longrightarrow> P"
  shows "P"
proof -
  have "i=j \<or> (i=j+1 \<and> odd i) \<or> (i=j-1 \<and> even i \<and> j\<ge>1) \<or> (i\<noteq>j \<and> \<not>(i=j+1 \<and> odd i) \<and> \<not> (i=j-1 \<and> even i \<and> j\<ge>1))"
    by linarith
  from assms show ?thesis by blast
qed




text \<open>@{text U\<^sub>f} is a gate.\<close>

lemma (in jozsa) transpose_of_jozsa_transform:
  shows "(U\<^sub>f)\<^sup>t = U\<^sub>f"
proof
  show "dim_row (U\<^sub>f\<^sup>t) = dim_row U\<^sub>f" by simp
next
  show "dim_col (U\<^sub>f\<^sup>t) = dim_col U\<^sub>f" by simp
next
  fix i j:: nat
  assume a0: "i < dim_row U\<^sub>f" and a1: "j < dim_col U\<^sub>f"
  thus "U\<^sub>f\<^sup>t $$ (i, j) = U\<^sub>f $$ (i, j)" 
  proof (induct rule: disj_four_cases)
    show "i=j \<or> (i=j+1 \<and> odd i) \<or> (i=j-1 \<and> even i \<and> j\<ge>1) \<or> (i\<noteq>j \<and> \<not>(i=j+1 \<and> odd i) \<and> \<not> (i=j-1 \<and> even i \<and> j\<ge>1))"
      by linarith
  next
    assume a2: "i=j"
    then show "U\<^sub>f\<^sup>t $$ (i, j) = U\<^sub>f $$ (i, j)" 
      using a0 by auto
  next
    assume a2: "(i=j+1 \<and> odd i)"
    then show "U\<^sub>f\<^sup>t $$ (i, j) = U\<^sub>f $$ (i, j)"
      using transpose_mat_def a0 a1 by auto
  next
    assume a2:"(i=j-1 \<and> even i \<and> j\<ge>1)"
    then have "U\<^sub>f $$ (i, j) = f (i div 2)" 
      using a0 a1 jozsa_transform_coeff by blast
    moreover have "U\<^sub>f $$ (j, i) = f (i div 2)" 
      using a0 a1 a2 jozsa_transform_coeff
      by (metis add_diff_assoc2 diff_add_inverse2 even_plus_one_iff even_succ_div_two jozsa_transform_dim)
    ultimately show "U\<^sub>f\<^sup>t $$ (i, j) = U\<^sub>f $$ (i, j)"
      using transpose_mat_def a0 a1 by auto
  next 
    assume a2: "(i\<noteq>j \<and> \<not>(i=j+1 \<and> odd i) \<and> \<not> (i=j-1 \<and> even i \<and> j\<ge>1))"
    then have "(j\<noteq>i \<and> \<not>(j=i+1 \<and> odd j) \<and> \<not> (j=i-1 \<and> even j \<and> i\<ge>1))" 
      by (metis le_imp_diff_is_add diff_add_inverse even_plus_one_iff le_add1)
    then have "U\<^sub>f $$ (j, i) = 0" 
      using jozsa_transform_coeff_is_zero a0 a1 by auto
    moreover have "U\<^sub>f $$ (i, j) = 0" 
      using jozsa_transform_coeff_is_zero a0 a1 a2 by auto
    ultimately show "U\<^sub>f\<^sup>t $$ (i, j) = U\<^sub>f $$ (i, j)"
      using transpose_mat_def a0 a1 by auto
  qed 
qed

lemma (in jozsa) adjoint_of_jozsa_transform: 
  shows "(U\<^sub>f)\<^sup>\<dagger> = U\<^sub>f"
proof
  show "dim_row (U\<^sub>f\<^sup>\<dagger>) = dim_row U\<^sub>f" by simp
next
  show "dim_col (U\<^sub>f\<^sup>\<dagger>) = dim_col U\<^sub>f" by simp
next
  fix i j:: nat
  assume a0: "i < dim_row U\<^sub>f" and a1: "j < dim_col U\<^sub>f"
  thus "U\<^sub>f\<^sup>\<dagger> $$ (i, j) = U\<^sub>f $$ (i, j)"
  proof (induct rule: disj_four_cases )
 show "i=j \<or> (i=j+1 \<and> odd i) \<or> (i=j-1 \<and> even i \<and> j\<ge>1) \<or> (i\<noteq>j \<and> \<not>(i=j+1 \<and> odd i) \<and> \<not> (i=j-1 \<and> even i \<and> j\<ge>1))"
      by linarith
  next
    assume a2: "i=j"
    then show "U\<^sub>f\<^sup>\<dagger> $$ (i, j) = U\<^sub>f $$ (i, j)" 
      using a0 hermite_cnj_def by auto
  next
    assume a2: "(i=j+1 \<and> odd i)"
    then show "U\<^sub>f\<^sup>\<dagger> $$ (i, j) = U\<^sub>f $$ (i, j)" 
      using a0 hermite_cnj_def by auto
  next
    assume a2:"(i=j-1 \<and> even i \<and> j\<ge>1)"
    then have "U\<^sub>f $$ (i, j) = f (i div 2)" 
      using a0 a1 jozsa_transform_coeff by auto
    moreover have "U\<^sub>f\<^sup>\<dagger>  $$ (j, i) = f (i div 2)" 
      using a1 a2 jozsa_transform_coeff hermite_cnj_def by auto 
    ultimately show "U\<^sub>f\<^sup>\<dagger> $$ (i, j) = U\<^sub>f $$ (i, j)" 
      by (metis a0 a1 cnj_transpose hermite_cnj_dim_row index_transpose_mat
          transpose_hermite_cnj transpose_of_jozsa_transform)
  next 
    assume a2: "(i\<noteq>j \<and> \<not>(i=j+1 \<and> odd i) \<and> \<not> (i=j-1 \<and> even i \<and> j\<ge>1))"
    then have f0:"(i\<noteq>j \<and> \<not>(j=i+1 \<and> odd j) \<and> \<not> (j=i-1 \<and> even j \<and> i\<ge>1))" 
      by (metis le_imp_diff_is_add diff_add_inverse even_plus_one_iff le_add1)
    then have "U\<^sub>f $$ (j,i) = 0" and "cnj 0 = 0"
      using jozsa_transform_coeff_is_zero a0 a1 a2 by auto
    then have "U\<^sub>f\<^sup>\<dagger> $$ (i,j) = 0" 
      using a0 a1 hermite_cnj_def by auto
    then show "U\<^sub>f\<^sup>\<dagger> $$ (i, j) = U\<^sub>f $$ (i, j)" 
      using a0 a1 a2 jozsa_transform_coeff_is_zero by auto
  qed 
qed

(*TODO: add line breaks if possible take out facts*)
lemma (in jozsa) jozsa_transform_is_unitary_index_even:
  fixes i j::nat
  assumes "i < dim_row U\<^sub>f" and "j < dim_col U\<^sub>f"
      and "even i"
  shows "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)"
proof-
  have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (\<Sum>k\<in>{i,i+1}. U\<^sub>f $$ (i, k) * U\<^sub>f $$ (k, j)) " 
    using U\<^sub>f_mult_without_empty_summands_even[of i j U\<^sub>f ] assms by auto
  moreover have "U\<^sub>f $$ (i, i) * U\<^sub>f $$ (i, j) = (1-f(i div 2))  * U\<^sub>f $$ (i, j)" 
    using assms by simp
  moreover have f0: "U\<^sub>f $$ (i, i+1) * U\<^sub>f $$ (i+1, j) = f(i div 2) * U\<^sub>f $$ (i+1, j)" 
    by (metis assms add.right_neutral One_nat_def Suc_leI add_Suc_right diff_add_inverse2 dvd_minus_add 
        even_add even_plus_one_iff even_succ_div_two index_transpose_mat(1) jozsa_transform_coeff(2) 
        jozsa_transform_dim nat_less_le power_add power_one_right transpose_of_jozsa_transform)
  ultimately have f1: "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (1-f(i div 2)) * U\<^sub>f $$ (i, j) +  f(i div 2) * U\<^sub>f $$ (i+1, j)" by auto
  thus "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)"
  proof (induct rule: disj_four_cases)
    show "j=i \<or> (j=i+1 \<and> odd j) \<or> (j=i-1 \<and> even j \<and> i\<ge>1) \<or> (j\<noteq>i \<and> \<not>(j=i+1 \<and> odd j) \<and> \<not> (j=i-1 \<and> even j \<and> i\<ge>1))"
      by linarith
  next
    assume a0: "j=i"
    then have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (1-f(i div 2))  *(1-f(i div 2)) +  f(i div 2) * f(i div 2)" 
      using f1 assms
      by (smt Groups.monoid_add_class.add.right_neutral One_nat_def Suc_leI add_Suc_right even_add even_mult_iff even_plus_one_iff even_succ_div_two jozsa_transform_coeff(1) jozsa_transform_coeff(2) jozsa_transform_dim(1) nat_less_le of_nat_add of_nat_mult one_add_one power_add power_one_right)
    moreover have "(1-f(i div 2))  *(1-f(i div 2)) +  f(i div 2) * f(i div 2) = 1" 
      using f_values assms
      by (metis (no_types, lifting) Nat.minus_nat.diff_0 diff_add_0 diff_add_inverse jozsa_transform_dim(1) less_power_add_imp_div_less mem_Collect_eq mult_eq_if one_power2 power2_eq_square power_one_right) 
    ultimately show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)" 
      by (metis assms(2) a0 index_one_mat(1) of_nat_1)
  next
    assume a0: "(j=i+1 \<and> odd j)"
    then have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (1-f(i div 2))  *f(i div 2) +  f(i div 2) *(1-f(i div 2))" 
      using f0 f1 assms
      by (smt jozsa_transform_coeff(1) Groups.ab_semigroup_mult_class.mult.commute even_succ_div_two 
          jozsa_transform_dim of_nat_add of_nat_mult)
    then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)" 
      using assms a0 by auto
  next
    assume a0:"(j=i-1 \<and> even j \<and> i\<ge>1)"
    then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)" 
      using a0 assms(3) dvd_diffD1 odd_one by blast
  next 
    assume a0: "(j\<noteq>i \<and> \<not>(j=i+1 \<and> odd j) \<and> \<not> (j=i-1 \<and> even j \<and> i\<ge>1))"
    then have "U\<^sub>f $$ (i, j) = 0" 
      by (metis assms index_transpose_mat(1) jozsa_transform_coeff_is_zero jozsa_transform_dim transpose_of_jozsa_transform)
    moreover have "U\<^sub>f $$ (i+1, j) = 0" 
      using assms a0
      by (smt add.right_neutral One_nat_def Suc_leI add_Suc_right add_diff_cancel_left' add_right_cancel 
          dvd_minus_add even_plus_one_iff jozsa_transform_coeff_is_zero jozsa_transform_dim(1) 
          less_imp_le_nat nat_less_le odd_one power_add power_one_right)
    ultimately have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (1-f(i div 2))  *0 +  f(i div 2) *0" 
      by (simp add: f1)
    then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)" 
      using a0 assms
      by (metis add.left_neutral index_one_mat(1) jozsa_transform_dim mult_0_right of_nat_0)
  qed
qed


lemma (in jozsa) jozsa_transform_is_unitary_index_odd:
  fixes i j::nat
  assumes "i < dim_row U\<^sub>f" and "j < dim_col U\<^sub>f"
      and "odd i"
  shows "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)"
proof-
  have f0: "i\<ge>1"  
    using linorder_not_less assms(3) by auto
  have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (\<Sum>k\<in>{i-1,i}. U\<^sub>f $$ (i, k) * U\<^sub>f $$ (k, j)) " 
    using U\<^sub>f_mult_without_empty_summands_odd[of i j U\<^sub>f ] assms by auto
  moreover have "(\<Sum>k\<in>{i-1,i}. U\<^sub>f $$ (i, k) * U\<^sub>f $$ (k, j)) 
                 = U\<^sub>f $$ (i, i-1) * U\<^sub>f $$ (i-1, j) +  U\<^sub>f $$ (i, i) * U\<^sub>f $$ (i, j)" 
    using assms f0 by auto
  moreover have "U\<^sub>f $$ (i, i) * U\<^sub>f $$ (i, j) = (1-f(i div 2))  * U\<^sub>f $$ (i, j)" 
    using assms jozsa_transform_coeff by simp
  moreover have f1: "U\<^sub>f $$ (i, i-1) * U\<^sub>f $$ (i-1, j) = f(i div 2) * U\<^sub>f $$ (i-1, j)" 
    using assms(1) assms(3) by auto
  ultimately have f2: "(U\<^sub>f * U\<^sub>f) $$ (i,j) = f(i div 2) * U\<^sub>f $$ (i-1, j) + (1-f(i div 2))  * U\<^sub>f $$ (i, j)" 
    using assms by auto
  show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)"
  proof (induct rule: disj_four_cases)
    show "j=i \<or> (j=i+1 \<and> odd j) \<or> (j=i-1 \<and> even j \<and> i\<ge>1) \<or> (j\<noteq>i \<and> \<not>(j=i+1 \<and> odd j) \<and> \<not> (j=i-1 \<and> even j \<and> i\<ge>1))"
      by linarith
  next
    assume a0: "j=i"
    then have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = f(i div 2) * f(i div 2) +  (1-f(i div 2)) *  (1-f(i div 2))" 
      using f2 assms 
      by (smt diff_less index_transpose_mat(1) jozsa_transform_coeff(1) jozsa_transform_coeff(2) 
          less_imp_add_positive less_numeral_extra(1) odd_pos odd_two_times_div_two_nat odd_two_times_div_two_succ 
          of_nat_add of_nat_mult trans_less_add1 transpose_of_jozsa_transform)
    moreover have "f(i div 2) * f(i div 2) +  (1-f(i div 2)) *  (1-f(i div 2)) = 1" 
      using f_values assms
      by (metis (no_types, lifting) Nat.minus_nat.diff_0 diff_add_0 diff_add_inverse jozsa_transform_dim(1) less_power_add_imp_div_less mem_Collect_eq mult_eq_if one_power2 power2_eq_square power_one_right) 
    ultimately show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)" 
      by (metis assms(2) a0 index_one_mat(1) of_nat_1)
  next
    assume a0: "(j=i+1 \<and> odd j)"
    then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)" 
      using assms(3) dvd_diffD1 odd_one even_plus_one_iff by blast
  next
    assume a0:"(j=i-1 \<and> even j \<and> i\<ge>1)"
    then have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = f(i div 2) * (1-f(i div 2)) +  (1-f(i div 2)) *  f(i div 2)" 
      using f0 f1 f2 assms
      by (smt jozsa_transform_coeff(1) Groups.ab_semigroup_mult_class.mult.commute even_succ_div_two f2 
          jozsa_transform_dim odd_two_times_div_two_nat odd_two_times_div_two_succ of_nat_add of_nat_mult)
    then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)" 
      using assms a0 by auto
  next 
    assume a0: "(j\<noteq>i \<and> \<not>(j=i+1 \<and> odd j) \<and> \<not> (j=i-1 \<and> even j \<and> i\<ge>1))"
    then have "U\<^sub>f $$ (i, j) = 0" 
      by (metis assms index_transpose_mat(1) jozsa_transform_coeff_is_zero jozsa_transform_dim transpose_of_jozsa_transform)
    moreover have "U\<^sub>f $$ (i-1, j) = 0" 
      using assms a0 f0 
      by (smt Groups.ordered_cancel_comm_monoid_diff_class.add_diff_inverse diff_less even_diff_nat 
          even_plus_one_iff  jozsa_transform_coeff_is_zero less_imp_add_positive less_numeral_extra(1) trans_less_add1)
    ultimately have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (1-f(i div 2))  *0 +  f(i div 2) *0" 
      using f2 by simp
    then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)" 
      using a0 assms
      by (metis add.left_neutral index_one_mat(1) jozsa_transform_dim mult_0_right of_nat_0)
  qed
qed

(*TODO: clean up,delete unused facts*)
lemma (in jozsa) jozsa_transform_is_gate:
  shows "gate (n+1) U\<^sub>f"
proof
  show "dim_row U\<^sub>f = 2^(n+1)" by simp
next
  show "square_mat U\<^sub>f" by simp
next
  show "unitary U\<^sub>f"
  proof-
    have "U\<^sub>f * U\<^sub>f = 1\<^sub>m (dim_col U\<^sub>f)"
    proof
      show "dim_row (U\<^sub>f * U\<^sub>f) = dim_row (1\<^sub>m (dim_col U\<^sub>f))" by simp
    next
      show "dim_col (U\<^sub>f * U\<^sub>f) = dim_col (1\<^sub>m (dim_col U\<^sub>f))" by simp
    next
      fix i j:: nat
      assume "i < dim_row (1\<^sub>m (dim_col U\<^sub>f))" and "j < dim_col (1\<^sub>m (dim_col U\<^sub>f))"
      then have "i < dim_row U\<^sub>f" and "j < dim_col U\<^sub>f" by auto
      then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)" 
        using jozsa_transform_is_unitary_index_odd jozsa_transform_is_unitary_index_even 
        by blast
    qed
  then show "unitary U\<^sub>f" 
    by (simp add: adjoint_of_jozsa_transform unitary_def)
  qed
qed

(*As n has to be at least 1 we introduce a modified introduction rule *)
lemma ind_from_1 [case_names n_ge_1 1 step]:
  assumes "n \<ge> 1"
  assumes "P(1)" 
  assumes "\<And>n. n \<ge> 1 \<Longrightarrow>  P n \<Longrightarrow> P (Suc n)"
  shows " P n"
  using nat_induct_at_least assms by auto

(*TODO: Better way then always assuming n\<ge>1?, for now just keep it a moment to try out what works*)

(*TODO: Think about binding of n and inductions. Should all lemmas be in jozsa? How to do induction then?
But first finish last step to see what requirements exist*)



fun pow_tensor :: "complex Matrix.mat \<Rightarrow> nat \<Rightarrow>  complex Matrix.mat" (infixr "^\<^sub>\<otimes>" 75) where
  "A ^\<^sub>\<otimes> (Suc 0) = A"  
| "A ^\<^sub>\<otimes> (Suc k) =  A \<Otimes> (A ^\<^sub>\<otimes> k)"

lemma pow_tensor_1_is_id [simp]:
  fixes A
  shows "A ^\<^sub>\<otimes> 1 = A"
  using one_mat_def by auto

lemma pow_tensor_n: 
  fixes n
  assumes "n \<ge> 1"
  shows " A ^\<^sub>\<otimes> (Suc n) = A  \<Otimes>  ( A ^\<^sub>\<otimes> n)" using assms 
  by (metis Deutsch_Jozsa.pow_tensor.simps(2) One_nat_def Suc_le_D)

lemma pow_tensor_dim_row [simp]:
  fixes A n
  assumes "n \<ge> 1"
  shows "dim_row(A ^\<^sub>\<otimes> n) = (dim_row A)^n"
proof (induction n rule: ind_from_1)
  show "n\<ge>1" using assms by auto 
next
  show "dim_row(A ^\<^sub>\<otimes> 1) = (dim_row A)^1" by simp
next
  fix n
  assume "dim_row(A ^\<^sub>\<otimes> n) = (dim_row A)^n"
  then show "dim_row(A ^\<^sub>\<otimes> (Suc n)) = (dim_row A)^(Suc n)" 
    by (metis One_nat_def Suc_inject Zero_not_Suc dim_row_tensor_mat pow_tensor.elims power_Suc power_one_right)
qed

lemma pow_tensor_dim_col [simp]:
  fixes A n
  assumes "n \<ge> 1"
  shows "dim_col(A ^\<^sub>\<otimes> n) = (dim_col A)^n"
proof (induction n rule: ind_from_1)
  show "n\<ge>1" using assms by auto 
next
  show "dim_col(A ^\<^sub>\<otimes> 1) = (dim_col A)^1" by simp
next
  fix n
  assume "dim_col(A ^\<^sub>\<otimes> n) = (dim_col A)^n"
  then show "dim_col(A ^\<^sub>\<otimes> (Suc n)) = (dim_col A)^(Suc n)" 
    by (metis dim_col_tensor_mat One_nat_def Suc_inject Zero_not_Suc pow_tensor.elims power_Suc power_one_right )
qed

lemma pow_tensor_values:
  fixes A n i j
  assumes "n \<ge> 1"
  assumes "i < dim_row ( A \<Otimes> ( A ^\<^sub>\<otimes> n))"
  and "j < dim_col ( A \<Otimes> ( A ^\<^sub>\<otimes> n))"
  shows "( A ^\<^sub>\<otimes> (Suc n)) $$ (i, j) = ( A \<Otimes> ( A ^\<^sub>\<otimes> n)) $$ (i, j)"
  using assms
  by (metis One_nat_def le_0_eq not0_implies_Suc pow_tensor.simps(2))

lemma pow_tensor_mult_distr:
  assumes "n \<ge> 1"
  and "dim_col A = dim_row B" and "0 < dim_row B" and "0 < dim_col B"
  shows "(A ^\<^sub>\<otimes> (Suc n))*(B ^\<^sub>\<otimes> (Suc n)) = (A * B) \<Otimes> ((A ^\<^sub>\<otimes> n)*(B ^\<^sub>\<otimes> n))" 
proof -
  have "(A ^\<^sub>\<otimes> (Suc n))*(B ^\<^sub>\<otimes> (Suc n)) = (A \<Otimes> (A ^\<^sub>\<otimes> n)) * (B  \<Otimes> (B ^\<^sub>\<otimes> n))" 
    using Suc_le_D assms(1) by fastforce
  then show "(A ^\<^sub>\<otimes> (Suc n))*(B ^\<^sub>\<otimes> (Suc n)) =  (A * B) \<Otimes> ((A ^\<^sub>\<otimes> n)*(B ^\<^sub>\<otimes> n))" 
    using mult_distr_tensor [of A B "(pow_tensor A n)" "(pow_tensor B n)"] assms
    by auto
qed

lemma index_tensor_mat_vec2_i_smaller_row_B: (*Better name would be welcome. index_tensor_mat_vec2_1? *)
  fixes A B:: "complex Matrix.mat" and i:: "nat" 
assumes "i < dim_row B" 
    and "dim_row A = 2"
    and "dim_col A = 1"
    and "0 < dim_col B" 
  shows "(A \<Otimes> B) $$ (i, 0) = (A  $$ (0, 0)) * (B $$ (i,0))" 
using index_tensor_mat assms by auto

lemma index_tensor_mat_vec2_i_greater_row_B:
  fixes A B:: "complex Matrix.mat" 
  and     i:: "nat" 
  assumes "i < (dim_row A) * (dim_row B)" 
      and "0 < (dim_col A) * (dim_col B)" 
      and "i \<ge> dim_row B"
      and "dim_row A = 2"
      and "dim_col A = 1"
  shows "(A \<Otimes> B) $$ (i, 0) = (A  $$ (1, 0)) * (B $$ ( i -dim_row B,0))"
proof -
  have "(A \<Otimes> B) $$ (i,0) = A $$ (i div (dim_row B), 0) * B $$ (i mod (dim_row B),0)"
    using assms index_tensor_mat[of A "dim_row A" "dim_col A" B "dim_row B" "dim_col B" i 0]
    by auto
  moreover have "i div (dim_row B) = 1" 
    using assms(1) assms(3) assms(4) 
    by simp
  then  have "i mod (dim_row B) = i - (dim_row B)" 
    by (simp add: modulo_nat_def)
  ultimately show "(A \<Otimes> B) $$ (i, 0) = (A  $$ (1, 0)) * (B $$ ( i -dim_row B,0))" 
    by (simp add: \<open>i div dim_row B = 1\<close>)
qed


abbreviation zero where "zero \<equiv> unit_vec 2 0"
abbreviation one where "one \<equiv> unit_vec 2 1"

lemma ket_zero_is_state: 
  shows "state 1 |zero\<rangle>"
  by (simp add: state_def ket_vec_def cpx_vec_length_def numerals(2))

lemma ket_one_is_state:
  shows "state 1 |one\<rangle>" 
  by (simp add: state_def ket_vec_def cpx_vec_length_def numerals(2))


abbreviation \<psi>\<^sub>1\<^sub>0:: "nat \<Rightarrow> complex Matrix.mat" where
"\<psi>\<^sub>1\<^sub>0 n \<equiv> Matrix.mat (2^n) 1 (\<lambda>(i,j). 1/(sqrt(2))^n)" (*start with 0 rather than 1? but then until 2^n-1*)

lemma \<psi>\<^sub>1\<^sub>0_values:
  fixes i j n
  assumes "i < dim_row (\<psi>\<^sub>1\<^sub>0 n)"
  and "j < dim_col (\<psi>\<^sub>1\<^sub>0 n)"
  and "n \<ge> 1"
  shows "(\<psi>\<^sub>1\<^sub>0 n) $$ (i,j) = 1/(sqrt(2)^n)" 
  using assms(1) assms(2) case_prod_conv by auto

lemma H_on_ket_zero: 
  shows "(H *  |zero\<rangle>) = (\<psi>\<^sub>1\<^sub>0 1)"
proof 
  fix i j:: nat
  assume a0: "i < dim_row (\<psi>\<^sub>1\<^sub>0 1)" 
     and a1: "j < dim_col (\<psi>\<^sub>1\<^sub>0 1)"
  then have f1: "i \<in> {0,1} \<and> j = 0" by (simp add: less_2_cases)
  then show "(H * |zero\<rangle>) $$ (i,j) = (\<psi>\<^sub>1\<^sub>0 1) $$ (i,j)"
    by (auto simp add: times_mat_def scalar_prod_def H_def ket_vec_def)
next
  show "dim_row (H * |zero\<rangle>) = dim_row (\<psi>\<^sub>1\<^sub>0 1)"  by (simp add: H_def)
next 
  show "dim_col (H * |zero\<rangle>) = dim_col (\<psi>\<^sub>1\<^sub>0 1)" using H_def  
    by (simp add: ket_vec_def)
qed

lemma H_on_ket_zero_is_state: 
  shows "state 1 (H * |zero\<rangle>)"
proof
  show "gate 1 H" 
    using H_is_gate by simp
next
  show "state 1 |zero\<rangle>" 
    using ket_zero_is_state by simp
qed

lemma \<psi>\<^sub>1\<^sub>0_tensor_n: 
  assumes "n \<ge> 1"
  shows "(\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n) = (\<psi>\<^sub>1\<^sub>0 (Suc n))"
proof
  have "dim_row (\<psi>\<^sub>1\<^sub>0 1) * dim_row (\<psi>\<^sub>1\<^sub>0 n)  =  2^(Suc n)" by simp 
  then show "dim_row ((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) = dim_row (\<psi>\<^sub>1\<^sub>0 (Suc n))" by auto
next
  have "dim_col (\<psi>\<^sub>1\<^sub>0 1) * dim_col (\<psi>\<^sub>1\<^sub>0 n)  =  1" by simp
  then show "dim_col ((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) = dim_col (\<psi>\<^sub>1\<^sub>0 (Suc n))" by auto
next
  fix i j:: nat
  assume a0: "i < dim_row (\<psi>\<^sub>1\<^sub>0 (Suc n))" and a1: "j < dim_col (\<psi>\<^sub>1\<^sub>0 (Suc n))"
  then have f0: "j = 0" and f1: "i< 2^(Suc n)" by auto
  then have f2: "(\<psi>\<^sub>1\<^sub>0 (Suc n)) $$ (i,j) = 1/(sqrt(2)^(Suc n))" 
    using  \<psi>\<^sub>1\<^sub>0_values[of i "(Suc n)" j] a0 a1 by auto
  show "((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) $$ (i,j) = (\<psi>\<^sub>1\<^sub>0 (Suc n)) $$ (i,j)" 
  proof (rule disjE) (*case distinction*)
    show "i < dim_row (\<psi>\<^sub>1\<^sub>0 n) \<or> i \<ge> dim_row (\<psi>\<^sub>1\<^sub>0 n)" by linarith
  next (* case i < dim_row (\<psi>\<^sub>1\<^sub>0 n) *)
    assume a2: "i < dim_row (\<psi>\<^sub>1\<^sub>0 n)"
    then have "((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) $$ (i,j) = (\<psi>\<^sub>1\<^sub>0 1) $$ (0,0) * (\<psi>\<^sub>1\<^sub>0 n) $$ (i,0)"
      using index_tensor_mat f0 assms by simp
    also have "... = 1/sqrt(2) * 1/(sqrt(2)^n)"
      using \<psi>\<^sub>1\<^sub>0_values a2 assms by auto
    finally show  "((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) $$ (i,j) = (\<psi>\<^sub>1\<^sub>0 (Suc n)) $$ (i,j)" 
      using f2  
      by (smt divide_divide_eq_left power_Suc)
  next (* case i \<ge> dim_row (\<psi>\<^sub>1\<^sub>0 n) *)
    assume "i \<ge> dim_row (\<psi>\<^sub>1\<^sub>0 n)"
    then have "((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) $$ (i,0) = ((\<psi>\<^sub>1\<^sub>0 1)  $$ (1, 0)) * ((\<psi>\<^sub>1\<^sub>0 n) $$ ( i -dim_row (\<psi>\<^sub>1\<^sub>0 n),0))"
      using index_tensor_mat_vec2_i_greater_row_B[of i "(\<psi>\<^sub>1\<^sub>0 1)" "(\<psi>\<^sub>1\<^sub>0 n)" ] a0 a1 f0  
      by auto
    then have "((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) $$ (i,0) = 1/sqrt(2) * 1/(sqrt(2)^n)"
      using \<psi>\<^sub>1\<^sub>0_values[of "i -dim_row (\<psi>\<^sub>1\<^sub>0 n)" n j] a0 a1 by auto
    then show  "((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) $$ (i,j) = (\<psi>\<^sub>1\<^sub>0 (Suc n)) $$ (i,j)" 
      using f0 f1 divide_divide_eq_left power_Suc 
      by auto
  qed
qed

lemma \<psi>\<^sub>1\<^sub>0_tensor_n_is_state:
  assumes "n \<ge> 1"
  shows "state n ( |zero\<rangle> ^\<^sub>\<otimes> n)"
proof (induction n rule: ind_from_1)
  show "n \<ge> 1" using assms by auto
next
  show "state 1 ( |zero\<rangle> ^\<^sub>\<otimes> 1)" using ket_zero_is_state by auto
next
  fix n
  assume a0: "state n ( |zero\<rangle> ^\<^sub>\<otimes> n)" and "n\<ge>1"
  then have "( |zero\<rangle>) ^\<^sub>\<otimes> (Suc n) = ( |zero\<rangle>)  \<Otimes>  ( |zero\<rangle> ^\<^sub>\<otimes> n)" 
    using assms pow_tensor_n[of n "|zero\<rangle>" ] by auto
  then show "state (Suc n) ( |zero\<rangle> ^\<^sub>\<otimes> (Suc n))" 
    using assms tensor_state a0 ket_zero_is_state by fastforce
qed


lemma H_tensor_n_is_gate:
  assumes "n \<ge> 1"
  shows "gate n (H ^\<^sub>\<otimes> n)" 
proof(induction n rule: ind_from_1)
  show "n \<ge> 1" using assms by auto
next
  show "gate 1 (H ^\<^sub>\<otimes> 1)" 
    using H_is_gate by auto
next
  fix n 
  assume a0: "gate n (H ^\<^sub>\<otimes> n)" and "n \<ge> 1"
  then have "(H ^\<^sub>\<otimes> (Suc n)) = H \<Otimes> (H ^\<^sub>\<otimes> n)" 
    using pow_tensor_n[of n H] by auto
  then show "gate (Suc n) (H ^\<^sub>\<otimes> (Suc n))" 
    using assms a0 tensor_gate H_is_gate by fastforce
qed



lemma H_tensor_n_on_zero_tensor_n: 
  assumes "n \<ge> 1"
  shows "(H ^\<^sub>\<otimes> n) * ( |zero\<rangle> ^\<^sub>\<otimes> n) = (\<psi>\<^sub>1\<^sub>0 n)"  
proof (induction n rule: ind_from_1)
  show "n\<ge>1" using assms by auto
next
  have "(H ^\<^sub>\<otimes> 1) * ( |zero\<rangle> ^\<^sub>\<otimes> 1) = H * |zero\<rangle>" by auto
  show "(H ^\<^sub>\<otimes> 1) * ( |zero\<rangle> ^\<^sub>\<otimes> 1) = (\<psi>\<^sub>1\<^sub>0 1)" using H_on_ket_zero by auto
next
  fix n
  assume a0: "1 \<le> n" and a1: "(H ^\<^sub>\<otimes> n) * ( |zero\<rangle> ^\<^sub>\<otimes> n) = (\<psi>\<^sub>1\<^sub>0 n)" 
  then have "(H ^\<^sub>\<otimes> (Suc n)) * ( |zero\<rangle> ^\<^sub>\<otimes> (Suc n)) = (H * |zero\<rangle>) \<Otimes> ((H ^\<^sub>\<otimes> n) * ( |zero\<rangle> ^\<^sub>\<otimes> n))" 
    using pow_tensor_mult_distr[of n "H" "|zero\<rangle>"] a0 ket_vec_def H_def
    by (simp add: H_def)
  also have  "... = (H * |zero\<rangle>) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)" using a1 by auto 
  also have "... = (\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)" using H_on_ket_zero by auto
  also have "... = (\<psi>\<^sub>1\<^sub>0 (Suc n))" using \<psi>\<^sub>1\<^sub>0_tensor_n a0 by auto
  finally show "(H ^\<^sub>\<otimes> (Suc n)) * ( |zero\<rangle> ^\<^sub>\<otimes> (Suc n)) = (\<psi>\<^sub>1\<^sub>0 (Suc n))" by auto
qed



lemma \<psi>\<^sub>1\<^sub>0_is_state:
  assumes "n \<ge> 1"
  shows "state n (\<psi>\<^sub>1\<^sub>0 n)"
  using H_tensor_n_is_gate \<psi>\<^sub>1\<^sub>0_tensor_n_is_state assms gate_on_state_is_state H_tensor_n_on_zero_tensor_n assms
  by metis


abbreviation \<psi>\<^sub>1\<^sub>1:: "complex Matrix.mat" where
"\<psi>\<^sub>1\<^sub>1 \<equiv> Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1/sqrt(2) else -1/sqrt(2))"


lemma H_on_ket_one_is_\<psi>\<^sub>1\<^sub>1: 
  shows "(H * |one\<rangle>) = \<psi>\<^sub>1\<^sub>1"
proof 
  fix i j:: nat
  assume "i < dim_row \<psi>\<^sub>1\<^sub>1" and "j < dim_col \<psi>\<^sub>1\<^sub>1"
  then have "i \<in> {0,1} \<and> j = 0" by (simp add: less_2_cases)
  then show "(H * |one\<rangle>) $$ (i,j) = \<psi>\<^sub>1\<^sub>1 $$ (i,j)"
    by (auto simp add: times_mat_def scalar_prod_def H_def ket_vec_def)
next
  show "dim_row (H * |one\<rangle>) = dim_row \<psi>\<^sub>1\<^sub>1" by (simp add: H_def)
next 
  show "dim_col (H * |one\<rangle>) = dim_col \<psi>\<^sub>1\<^sub>1" by (simp add: H_def ket_vec_def)
qed

lemma \<psi>\<^sub>1\<^sub>1_is_state: 
  shows "state 1 (H * |one\<rangle>)"
  using H_is_gate ket_one_is_state by simp



abbreviation \<psi>\<^sub>1:: "nat \<Rightarrow> complex Matrix.mat" where
"\<psi>\<^sub>1 n \<equiv> Matrix.mat (2^(n+1))  1 (\<lambda>(i,j). if (even i) then 1/(sqrt(2)^(n+1)) else -1/(sqrt(2)^(n+1)))"

lemma \<psi>\<^sub>1_values_even[simp]:
  fixes i j n
  assumes "i < dim_row (\<psi>\<^sub>1 n)"
  and "j < dim_col (\<psi>\<^sub>1 n)"
  and "n \<ge> 1"
  and "even i"
  shows "(\<psi>\<^sub>1 n) $$ (i,j) = 1/(sqrt(2)^(n+1))" 
  using assms case_prod_conv by auto

lemma \<psi>\<^sub>1_values_odd [simp]:
  fixes i j n
  assumes "i < dim_row (\<psi>\<^sub>1 n)"
  and "j < dim_col (\<psi>\<^sub>1 n)"
  and "n \<ge> 1"
  and "odd i"
  shows "(\<psi>\<^sub>1 n) $$ (i,j) = -1/(sqrt(2)^(n+1))" 
  using assms case_prod_conv by auto


lemma "\<psi>\<^sub>1\<^sub>0_tensor_\<psi>\<^sub>1\<^sub>1_is_\<psi>\<^sub>1":
  assumes "n \<ge> 1"
  shows "(\<psi>\<^sub>1\<^sub>0 n) \<Otimes> \<psi>\<^sub>1\<^sub>1 = (\<psi>\<^sub>1 n)" 
proof 
 show "dim_col ((\<psi>\<^sub>1\<^sub>0 n) \<Otimes> \<psi>\<^sub>1\<^sub>1) = dim_col (\<psi>\<^sub>1 n)" by auto
next
  show "dim_row ((\<psi>\<^sub>1\<^sub>0 n) \<Otimes> \<psi>\<^sub>1\<^sub>1) = dim_row (\<psi>\<^sub>1 n)" by auto
next
  fix i j::nat
  assume a0: "i < dim_row (\<psi>\<^sub>1 n)" and a1: "j < dim_col (\<psi>\<^sub>1 n)"
  then have "i < 2^(n+1)" and "j = 0" by auto 
  then have f0: "((\<psi>\<^sub>1\<^sub>0 n) \<Otimes> \<psi>\<^sub>1\<^sub>1) $$ (i,j) = 1/(sqrt(2)^n) * \<psi>\<^sub>1\<^sub>1 $$ (i mod 2, j)" 
    using \<psi>\<^sub>1\<^sub>0_values[of "i div 2" n "j div 1"] a0 a1 by auto
  show "((\<psi>\<^sub>1\<^sub>0 n) \<Otimes> \<psi>\<^sub>1\<^sub>1) $$ (i,j) = (\<psi>\<^sub>1 n) $$ (i,j)" using f0 \<psi>\<^sub>1_values_even \<psi>\<^sub>1_values_odd a0 a1 by auto 
(*I have a longer proof with case distinction even i \<or> odd i for this which one is nicer?*)
qed

lemma \<psi>\<^sub>1_is_state:
  assumes "n \<ge> 1"
  shows "state (n+1) (\<psi>\<^sub>1 n)" 
  using \<psi>\<^sub>1\<^sub>0_tensor_\<psi>\<^sub>1\<^sub>1_is_\<psi>\<^sub>1  \<psi>\<^sub>1\<^sub>0_is_state assms  \<psi>\<^sub>1\<^sub>1_is_state assms H_on_ket_one_is_\<psi>\<^sub>1\<^sub>1 tensor_state by metis


abbreviation (in jozsa) \<psi>\<^sub>2:: "complex Matrix.mat" where
"\<psi>\<^sub>2 \<equiv> Matrix.mat (2^(n+1)) 1 (\<lambda>(i,j). if (even i) then ((1-f(i div 2))+-f(i div 2)) * 1/(sqrt(2)^(n+1)) 
                                      else (-(1-f(i div 2))+(f(i div 2)))* 1/(sqrt(2)^(n+1)))"

(* Would this be much better?
"\<psi>\<^sub>2 \<equiv> Matrix.mat (2^(n+1)) 1 (\<lambda>(i,j). if (even i) then (1-2*f(i div 2))/(sqrt(2)^(n+1)) 
                                      else (-1+2*f(i div 2))/(sqrt(2)^(n+1)))"*)

(*Maybe just change it to  (1-f(i div 2))* 1/(sqrt(2)^(n+1)) + (-f(i div 2))* 1/(sqrt(2)^(n+1)) 
instead of f(i div 2)^n 
Is also correct saves a lot of work and we don't have to stick to the paper proof in all points
Edit: changed it there is some kind of integer problem, best solution right now proceed first and 
come back to it if it turns out to be important*)

lemma (in jozsa) \<psi>\<^sub>2_values_even[simp]:
  fixes i j 
  assumes "i < dim_row \<psi>\<^sub>2 "
  and "j < dim_col \<psi>\<^sub>2 "
  and "even i"
  shows "\<psi>\<^sub>2  $$ (i,j) = ((1-f(i div 2))+-f(i div 2)) * 1/(sqrt(2)^(n+1))" 
  using assms case_prod_conv by simp

lemma (in jozsa) \<psi>\<^sub>2_values_odd[simp]:
  fixes i j 
  assumes "i < dim_row \<psi>\<^sub>2 "
  and "j < dim_col \<psi>\<^sub>2 "
  and "odd i"
  shows "\<psi>\<^sub>2  $$ (i,j) = (-(1-f(i div 2))+(f(i div 2)))* 1/(sqrt(2)^(n+1))" 
  using assms case_prod_conv by simp


lemma (in jozsa) jozsa_transform_times_\<psi>\<^sub>1_is_\<psi>\<^sub>2:
  shows "U\<^sub>f * (\<psi>\<^sub>1 n) = \<psi>\<^sub>2 " 
proof 
  show "dim_row (U\<^sub>f * (\<psi>\<^sub>1 n)) = dim_row \<psi>\<^sub>2 " by simp
next
  show "dim_col (U\<^sub>f * (\<psi>\<^sub>1 n)) = dim_col \<psi>\<^sub>2 " by simp
next
  fix i j ::nat
  assume a0: "i < dim_row \<psi>\<^sub>2" and a1: "j < dim_col \<psi>\<^sub>2"
  then have f0:"i \<in> {0..2^(n+1)} \<and> j=0" by auto
  then have f1: "i < dim_row U\<^sub>f \<and> j < dim_col U\<^sub>f " using a0 by auto
  have f2: "i < dim_row (\<psi>\<^sub>1 n) \<and> j < dim_col (\<psi>\<^sub>1 n)" using a0 a1 by auto
  show "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = \<psi>\<^sub>2 $$ (i,j)"
  proof (rule disjE)
    show "even i \<or> odd i" by auto
  next
    assume a2: "even i"
    then have "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = (\<Sum>k\<in>{i,i+1}. U\<^sub>f $$ (i, k) * (\<psi>\<^sub>1 n)$$ (k, j))"
      using f1 f2 U\<^sub>f_mult_without_empty_summands_even[of i j "(\<psi>\<^sub>1 n)"] by auto 
    moreover have "U\<^sub>f $$ (i, i) * (\<psi>\<^sub>1 n)$$ (i, j) = (1-f(i div 2))* 1/(sqrt(2)^(n+1))" 
      using f0 f1 a2 by auto
    moreover have "U\<^sub>f $$ (i, i+1) * (\<psi>\<^sub>1 n)$$ (i+1, j) = (-f(i div 2))* 1/(sqrt(2)^(n+1))" 
      using f0 f1 a2 by auto
    ultimately have "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = (1-f(i div 2))* 1/(sqrt(2)^(n+1)) + (-f(i div 2))* 1/(sqrt(2)^(n+1))" 
      by auto
    also have "... = ((1-f(i div 2))+-f(i div 2)) * 1/(sqrt(2)^(n+1))" 
      using add_divide_distrib 
      by (metis (no_types, hide_lams) mult.right_neutral of_int_add of_int_of_nat_eq)
    also have "... =  \<psi>\<^sub>2 $$ (i,j)" 
      using a0 a1 a2 by auto
    finally show "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = \<psi>\<^sub>2 $$ (i,j)" by auto
  next 
    assume a2: "odd i"
    then have f6: "i\<ge>1"  
    using linorder_not_less by auto
    have "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = (\<Sum>k\<in>{i-1,i}. U\<^sub>f $$ (i, k) * (\<psi>\<^sub>1 n)$$ (k, j))"
      using f1 f2 a2 U\<^sub>f_mult_without_empty_summands_odd[of i j "(\<psi>\<^sub>1 n)"]  
      by (smt dim_row_mat(1) jozsa_transform_dim(2)) 
    moreover have "(\<Sum>k\<in>{i-1,i}. U\<^sub>f $$ (i, k) * (\<psi>\<^sub>1 n) $$ (k, j)) 
                 = U\<^sub>f $$ (i, i-1) * (\<psi>\<^sub>1 n) $$ (i-1, j) +  U\<^sub>f $$ (i, i) * (\<psi>\<^sub>1 n) $$ (i, j)" 
      using a2 f6 by auto
    moreover have  "U\<^sub>f $$ (i, i) * (\<psi>\<^sub>1 n)$$ (i, j) = (1-f(i div 2))* -1/(sqrt(2)^(n+1))" 
      using f1 f2 a2 by auto
    moreover have "U\<^sub>f $$ (i, i-1) * (\<psi>\<^sub>1 n)$$ (i-1, j) = f(i div 2)* 1/(sqrt(2)^(n+1))" 
      using a0 a1 a2 by auto
    ultimately have "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = (1-f(i div 2))* -1/(sqrt(2)^(n+1)) +(f(i div 2))* 1/(sqrt(2)^(n+1))" 
       by (smt of_real_add)
     also have "... = ( -(1-f(i div 2)) + (f(i div 2)))* 1/(sqrt(2)^(n+1))" 
       by (metis (no_types, hide_lams) mult.right_neutral add_divide_distrib mult_minus1_right 
           of_int_add of_int_of_nat_eq)
     finally show "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = \<psi>\<^sub>2 $$ (i,j)" 
       using a0 a1 a2 by auto
  qed
qed

lemma (in jozsa) \<psi>\<^sub>2_is_state:
  shows "state (n+1) \<psi>\<^sub>2" 
  using jozsa_transform_times_\<psi>\<^sub>1_is_\<psi>\<^sub>2 jozsa_transform_is_gate \<psi>\<^sub>1_is_state dim gate_on_state_is_state by fastforce


(*I need a representation of (H ^\<^sub>\<otimes> n) as matrix!!! Or at least I need to know what psi3 is!*)

lemma [simp]:
  fixes i j n
  shows "((\<langle>unit_vec (2^n) i| unit_vec (2^n) j\<rangle>))\<in>  \<nat>"
proof-
  have " Im z = 0 \<and> (\<exists>i. Re z = of_nat i)" sorry
  show ?thesis sorry
qed



(*Even does not work*)
lemma H_tensor_n:
  fixes n
  assumes "n\<ge>1"
shows "(H ^\<^sub>\<otimes> n) = Matrix.mat (2^n) (2^n) (\<lambda>(i,j). if ((\<langle>unit_vec (2^n) i| unit_vec (2^n) j\<rangle>)) = 1
                                                  then -1/(sqrt(2)^n) else 1/(sqrt(2)^n))" 
proof (induction n rule: ind_from_1)
  show "n\<ge>1" using assms by auto
next
  have "((\<langle>unit_vec (2^1) 0| unit_vec (2^1) 0\<rangle>)) = 1" by simp
  moreover have "((\<langle>unit_vec (2^1) 0| unit_vec (2^1) 1\<rangle>)) = 0" by simp
  moreover have "((\<langle>unit_vec (2^1) 1| unit_vec (2^1) 0\<rangle>)) = 0" by simp
  moreover have "((\<langle>unit_vec (2^1) 1| unit_vec (2^1) 1\<rangle>)) = 1" by simp
  ultimately have "H = Matrix.mat 2 2 (\<lambda>(i,j). if ((\<langle>unit_vec (2^1) i| unit_vec (2^1) j\<rangle>)) = 1
                                                  then -1/(sqrt(2)^1) else 1/(sqrt(2)^1))"
  show "(H ^\<^sub>\<otimes> 1) = Matrix.mat (2^1) (2^1) (\<lambda>(i,j). if ((\<langle>unit_vec (2^1) i| unit_vec (2^1) j\<rangle>)) = 1
                                                  then -1/(sqrt(2)^1) else 1/(sqrt(2)^1))"
  

qed



















(*Tryout a new thing: Pretty tiresome*)

fun dec_to_bin:: "nat \<Rightarrow> nat list" where
"dec_to_bin 0 = []"
|"dec_to_bin (Suc n) = (if ((Suc n) mod 2 = 0) then (dec_to_bin ((Suc n) div 2))@[0] 
                       else (dec_to_bin ((Suc n) div 2))@[1] ) "

fun pad_with_zero:: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
"pad_with_zero xs 0 = xs"
| "pad_with_zero xs (Suc n) = [0]@ (pad_with_zero xs n)"


value "(pad_with_zero (dec_to_bin 3) (2^2- length (dec_to_bin 3)))"

fun h ::"nat list \<Rightarrow> nat list \<Rightarrow> nat" where
"h [] ys = 0"
|"h (x#xs) (y#ys) = x*y + h xs ys"


abbreviation  Hn:: "nat \<Rightarrow> complex Matrix.mat" where
"Hn n \<equiv> Matrix.mat (2^n) (2^n) (\<lambda>(i,j). if even
(h  (pad_with_zero (dec_to_bin i) (2^n- length (dec_to_bin i))) 
    (pad_with_zero (dec_to_bin j) (2^n- length (dec_to_bin j))) ) 
then (1/sqrt(2)^n) else -1/sqrt(2)^n)"

lemma H_tensor_n:
  fixes n
  assumes "n\<ge>1"
  shows "(H ^\<^sub>\<otimes> n) = Hn n"
proof (induction n rule: ind_from_1)
  show "n\<ge>1" using assms by auto
next
  show "(H ^\<^sub>\<otimes> 1) = Hn 1"
  proof 
    show "dim_row (H ^\<^sub>\<otimes> 1) = dim_row (Hn 1)" 
      by (simp add:H_without_scalar_prod) 
    show "dim_col (H ^\<^sub>\<otimes> 1) = dim_col (Hn 1)"
      by (simp add:H_without_scalar_prod) 
    fix i j::nat
    assume a0:"i<dim_row (Hn 1)" and a1:" j<dim_col (Hn 1)"
    have f0: "(pad_with_zero (dec_to_bin 0) (2- length (dec_to_bin 0))) = [0,0]" 
      by (simp add: numeral_2_eq_2)
    then have "Hn 1 $$ (0, 0) = 1/sqrt(2)" using f0 by auto 
    moreover have " Hn 1 $$ (0, 1) = 1/sqrt(2)" using f0 by auto 
    moreover have " Hn 1 $$ (1, 0) = 1/sqrt(2)" using f0 by auto 
    moreover have " Hn 1 $$ (1, 1) = -1/sqrt(2)" using f0 by auto 
    ultimately show "(H ^\<^sub>\<otimes> 1) $$ (i, j) = Hn 1 $$ (i, j)" using a0 a1 
      by (smt H_without_scalar_prod Product_Type.old.prod.case dim_col_mat(1) dim_row_mat(1) 
          divide_minus_left index_mat(1) less_2_cases one_less_numeral_iff pow_tensor_1_is_id 
          power_one_right semiring_norm(76))
  qed
next
  fix n 
  assume "(H ^\<^sub>\<otimes> n) = Hn n"
  have "(H ^\<^sub>\<otimes> (Suc n)) = H \<Otimes> (H ^\<^sub>\<otimes> n)" using assms  sledgehammer

qed




(*What I tried
here is to separate psi2 in unit vectors multiplied with 1-2*f(i div 2) or -1+2*f(i div 2) and show 
what the result of multiplying (H ^\<^sub>\<otimes> n) with it is. Then, add all vectors up again.  *)
lemma H_on_unit_vec: (*Not even sure if this is true*)
  fixes k n::nat
  assumes "n\<ge>1"
    and "k<n"
  shows "(H ^\<^sub>\<otimes> n) * |unit_vec n k\<rangle> = Matrix.mat (2^n) 1 (\<lambda>(i,j). if even (i*k) then (1/sqrt(2)^n) else (-1/sqrt(2)^n))"
proof(induction n rule: ind_from_1)
  show "n\<ge>1" using assms by auto
next
  show "(H ^\<^sub>\<otimes> 1) * |unit_vec 1 k\<rangle> = Matrix.mat (2^1) 1 (\<lambda>(i,j). if even (i*k) then (1/sqrt(2)^1) else (-1/sqrt(2)^1))" 
    sorry
next 
  fix n
  assume "(H ^\<^sub>\<otimes> n) * |unit_vec n k\<rangle> = Matrix.mat (2^n) 1 (\<lambda>(i,j). if even (i*k) then (1/sqrt(2)^n) else (-1/sqrt(2)^n))"
  show "(H ^\<^sub>\<otimes> (Suc n)) * |unit_vec (Suc n) k\<rangle> = Matrix.mat (2^(Suc n)) 1 (\<lambda>(i,j). if even (i*k) 
                                                                then (1/sqrt(2)^(Suc n)) else (-1/sqrt(2)^(Suc n)))"
    sorry
qed

(*lemma "\<psi>\<^sub>2 = (\<Sum>k\<in>{0..<2^(n+1)}. (Matrix.mat (2^n) 1 (\<lambda>(i,j). if even k \<and> i=k then ((1-f(i div 2))+-f(i div 2)) * 1/(sqrt(2)^(n+1)) else 
(if odd k \<and> i=k then (-(1-f(i div 2))+(f(i div 2)))* 1/(sqrt(2)^(n+1)) else 0)) ))" 
This could be done with finsum_vec but seems very difficult to prove.*)



(*This needs to include all f(0) to f(2^n) in each row but how determine coefficients? Need (H ^\<^sub>\<otimes> n) for this*)
abbreviation (in jozsa) \<psi>\<^sub>3:: "complex Matrix.mat" where
"\<psi>\<^sub>3 \<equiv> Matrix.mat (2^(n+1)) 1 (\<lambda>(i,j). if (even i) then ((1-f(i div 2))+-f(i div 2)) * 1/(sqrt(2)^(n+1)) 
                                      else (-(1-f(i div 2))+(f(i div 2)))* 1/(sqrt(2)^(n+1)))"


lemma (in jozsa) H_tensor_n_on_\<psi>\<^sub>2_is_\<psi>\<^sub>3:
  shows "((H ^\<^sub>\<otimes> n) \<Otimes> Id 1)* \<psi>\<^sub>2 = \<psi>\<^sub>3" 
proof 
qed

end