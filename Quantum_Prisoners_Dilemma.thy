theory Quantum_Prisoners_Dilemma
imports
More_Tensor
begin


text \<open>
\<gamma> can be seen as a measure of the game's entanglement. In a restricted 
strategy space, the game behaves classically if \<gamma> = 0. But for \<gamma> = 2*$\pi$ the dilemma 
disappears.   
\<close>
locale prisoner =
  fixes \<gamma>:: "real" 
  assumes "\<gamma> \<le> (2*pi)"
      and "\<gamma> \<ge> 0"

(*I am not sure at all that J can be expressed like this. There are papers where it sounds as if this 
there are just some restrictions on J and that's all*)
abbreviation (in prisoner) J :: "complex Matrix.mat" where
"J \<equiv> mat_of_cols_list 4 [[cos(\<gamma>/2),0,0,\<i>*sin(\<gamma>/2)],
                          [0,cos(\<gamma>/2),-\<i>*sin(\<gamma>/2),0],
                          [0,-\<i>*sin(\<gamma>/2),cos(\<gamma>/2),0],
                          [\<i>*sin(\<gamma>/2),0,0,cos(\<gamma>/2)]]"

abbreviation (in prisoner) \<psi>\<^sub>1 :: "complex Matrix.mat" where
"\<psi>\<^sub>1 \<equiv> mat_of_cols_list 4 [[cos(\<gamma>/2),0,0,\<i>*sin(\<gamma>/2)]]"

lemma (in prisoner) 
  shows "J*|unit_vec 4 0\<rangle> = \<psi>\<^sub>1"
proof
  fix i j assume "i < dim_row \<psi>\<^sub>1" and "j < dim_col \<psi>\<^sub>1"
  then have f0: "i\<in>{0,1,2,3} \<and> j=0" using mat_of_cols_list_def by auto       
  then have  "(J*|unit_vec 4 0\<rangle>) $$ (i,j) = (\<Sum>k<4. (J $$ (i,k)) * ( |unit_vec 4 0\<rangle> $$ (k,j)))" 
    using mat_of_cols_list_def ket_vec_def 
    by auto
  also have "... = (\<Sum>k\<in>{0,1,2,3}. (J $$ (i,k)) * ( |unit_vec 4 0\<rangle> $$ (k,j)))" 
    using set_4 atLeast0LessThan by auto
  also have "... = \<psi>\<^sub>1 $$(i,j)" 
    using mat_of_cols_list_def f0 by auto
  finally show "(J*|unit_vec 4 0\<rangle>) $$ (i,j) = \<psi>\<^sub>1 $$(i,j)" by blast
next 
  show  "dim_row (J*|unit_vec 4 0\<rangle>) = dim_row \<psi>\<^sub>1"  
    using mat_of_cols_list_def by simp
next
  show  "dim_col (J*|unit_vec 4 0\<rangle>) = dim_col \<psi>\<^sub>1"  
    using mat_of_cols_list_def  
    by (simp add: ket_vec_def)
qed


locale restricted_strategic_space = prisoner+
  fixes \<theta>\<^sub>A:: "real"
    and \<psi>\<^sub>A:: "real" 
    and \<theta>\<^sub>B:: "real"
    and \<psi>\<^sub>B:: "real"
  assumes "0 \<le> \<theta>\<^sub>A \<and> \<theta>\<^sub>A \<le> 2*\<pi>"
      and "0 \<le> \<psi>\<^sub>A \<and> \<psi>\<^sub>A \<le> 2*\<pi>"
      and "0 \<le> \<theta>\<^sub>B \<and> \<theta>\<^sub>B \<le> 2*\<pi>"
      and "0 \<le> \<psi>\<^sub>B \<and> \<psi>\<^sub>B \<le> 2*\<pi>"

abbreviation (in restricted_strategic_space) U\<^sub>A :: "complex Matrix.mat" where
"U\<^sub>A \<equiv>  mat_of_cols_list 2 [[(exp(\<i>*\<psi>\<^sub>A))*cos(\<theta>\<^sub>A/2), sin (\<theta>\<^sub>A/2)],
                           [-sin(\<theta>\<^sub>A/2), (exp (-\<i>*\<psi>\<^sub>A))*cos(\<theta>\<^sub>A/2)]]"

abbreviation (in restricted_strategic_space) U\<^sub>B :: "complex Matrix.mat" where
"U\<^sub>B \<equiv>  mat_of_cols_list 2 [[exp(\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2), sin(\<theta>\<^sub>B/2)],
                           [-sin(\<theta>\<^sub>B/2), exp(-\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2)]]"

abbreviation (in restricted_strategic_space) \<psi>\<^sub>2 :: "complex Matrix.mat" where
"\<psi>\<^sub>2 \<equiv> mat_of_cols_list 4 [[exp(\<i>*\<psi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * exp(\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * cos(\<gamma>/2) + sin(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2),
                           exp(\<i>*\<psi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2) * cos(\<gamma>/2) - sin(\<theta>\<^sub>A/2) * exp(-\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2),
                           sin(\<theta>\<^sub>A/2) * exp (\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * cos(\<gamma>/2) - exp (-\<i>*\<psi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2),
                           sin(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2) * cos(\<gamma>/2) + exp (-\<i>*\<psi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * exp (-\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2)]]"

abbreviation (in restricted_strategic_space) U\<^sub>A\<^sub>B :: "complex Matrix.mat" where
"U\<^sub>A\<^sub>B \<equiv> mat_of_cols_list 4 [[exp(\<i>*\<psi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * exp(\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2), exp(\<i>*\<psi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2),
                            sin(\<theta>\<^sub>A/2) * exp(\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2), sin(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2)],
                           [exp(\<i>*\<psi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * -sin(\<theta>\<^sub>B/2), exp(\<i>*\<psi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * exp(-\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2),
                            sin(\<theta>\<^sub>A/2) * -sin(\<theta>\<^sub>B/2), sin(\<theta>\<^sub>A/2) * exp(-\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2)],
                           [-sin(\<theta>\<^sub>A/2) * exp(\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2), -sin(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2),
                            exp(-\<i>*\<psi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * exp (\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2), exp(-\<i>*\<psi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2)],
                           [-sin(\<theta>\<^sub>A/2) * -sin(\<theta>\<^sub>B/2), -sin(\<theta>\<^sub>A/2) * exp(-\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2),
                            exp(-\<i>*\<psi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * -sin(\<theta>\<^sub>B/2), exp (-\<i>*\<psi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * exp(-\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2)]]"


lemma two_div_two [simp]: 
  shows "2 div Suc (Suc 0) = 1" by auto
lemma two_mod_two [simp]: 
  shows "2 mod Suc (Suc 0) = 0" by (simp add: numeral_2_eq_2)
lemma three_div_two [simp]: 
  shows "3 div Suc (Suc 0) = 1" by (simp add: numeral_3_eq_3)
lemma three_mod_two [simp]: 
  shows "3 mod Suc (Suc 0) = 1" by (simp add: mod_Suc numeral_3_eq_3)

lemma (in restricted_strategic_space) U\<^sub>A_tensor_U\<^sub>B:
  shows "(U\<^sub>A \<Otimes> U\<^sub>B) = U\<^sub>A\<^sub>B"
proof
  fix i j assume a0: "i<dim_row U\<^sub>A\<^sub>B" and a1: "j<dim_col U\<^sub>A\<^sub>B"
  then have "i\<in>{0,1,2,3} \<and> j\<in>{0,1,2,3}"
    using mat_of_cols_list_def by auto
  then show "(U\<^sub>A \<Otimes> U\<^sub>B) $$ (i,j) = U\<^sub>A\<^sub>B $$ (i,j)"
    using mat_of_cols_list_def by auto
next
  show "dim_row (U\<^sub>A \<Otimes> U\<^sub>B) = dim_row U\<^sub>A\<^sub>B" using mat_of_cols_list_def by auto
next
  show "dim_col (U\<^sub>A \<Otimes> U\<^sub>B) = dim_col U\<^sub>A\<^sub>B" using mat_of_cols_list_def by auto
qed

lemma set_sub_4: "{..<4::nat} = {0,1,2,3}" by auto

lemma sum_4: 
  fixes f::"nat \<Rightarrow> complex"
  shows "(\<Sum>k<4::nat. f(k)) = f(0::nat)+f(1)+f(2)+f(3)"
  using set_sub_4 by auto

lemma (in restricted_strategic_space)
  shows "(U\<^sub>A \<Otimes> U\<^sub>B)*\<psi>\<^sub>1 = \<psi>\<^sub>2"
proof
  fix i j
  assume "i < dim_row \<psi>\<^sub>2" and "j < dim_col \<psi>\<^sub>2"
  then have "i\<in>{0,1,2,3} \<and> j=0" using mat_of_cols_list_def by auto 
  then show "((U\<^sub>A \<Otimes> U\<^sub>B)*\<psi>\<^sub>1) $$(i,j) = \<psi>\<^sub>2 $$(i,j)" 
    using mat_of_cols_list_def U\<^sub>A_tensor_U\<^sub>B sum_4 by auto
next
  show "dim_row ((U\<^sub>A \<Otimes> U\<^sub>B)*\<psi>\<^sub>1) = dim_row \<psi>\<^sub>2" using mat_of_cols_list_def by auto  
next
  show "dim_col ((U\<^sub>A \<Otimes> U\<^sub>B)*\<psi>\<^sub>1) = dim_col \<psi>\<^sub>2" using mat_of_cols_list_def by auto  
qed

abbreviation (in prisoner) J_cnj :: "complex Matrix.mat" where
"J_cnj \<equiv> mat_of_cols_list 4 [[cos(\<gamma>/2),0,0,-\<i>*sin(\<gamma>/2)],
                             [0,cos(\<gamma>/2),\<i>*sin(\<gamma>/2),0],
                             [0,\<i>*sin(\<gamma>/2),cos(\<gamma>/2),0],
                             [-\<i>*sin(\<gamma>/2),0,0,cos(\<gamma>/2)]]"

lemma (in prisoner) hermite_cnj_of_J [simp]:
  shows "J\<^sup>\<dagger> = J_cnj"
proof
  fix i j assume "i < dim_row J_cnj" and "j < dim_col J_cnj"
  then have "i\<in>{0,1,2,3} \<and> j\<in>{0,1,2,3}" using mat_of_cols_list_def by auto
  then show "J\<^sup>\<dagger> $$ (i,j) = J_cnj $$ (i,j)"
    using mat_of_cols_list_def hermite_cnj_def by auto
next
  show "dim_row (J\<^sup>\<dagger>) = dim_row J_cnj" using mat_of_cols_list_def by auto
next
  show "dim_col (J\<^sup>\<dagger>) = dim_col J_cnj" using mat_of_cols_list_def by auto
qed

abbreviation (in restricted_strategic_space) \<psi>\<^sub>f :: "complex Matrix.mat" where
"\<psi>\<^sub>f \<equiv> mat_of_cols_list 4 [[
cos(\<gamma>/2) * (exp(\<i>*\<psi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * exp(\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * cos(\<gamma>/2) + sin(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2))
+ (-\<i>*sin(\<gamma>/2)) * (-sin(\<theta>\<^sub>A/2) * -sin(\<theta>\<^sub>B/2) * cos(\<gamma>/2) + exp (-\<i>*\<psi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * exp (-\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2)),

cos(\<gamma>/2) * (exp(\<i>*\<psi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2) * cos(\<gamma>/2) - sin(\<theta>\<^sub>A/2) * exp(-\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2)) 
+ (\<i>*sin(\<gamma>/2)) * (sin(\<theta>\<^sub>A/2) * exp (\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * cos(\<gamma>/2) - exp (-\<i>*\<psi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2)),

(\<i>*sin(\<gamma>/2)) * (exp(\<i>*\<psi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2) * cos(\<gamma>/2) - sin(\<theta>\<^sub>A/2) * exp(-\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2))
+ cos(\<gamma>/2) * (sin(\<theta>\<^sub>A/2) * exp (\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * cos(\<gamma>/2) - exp (-\<i>*\<psi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2)),

(-\<i>*sin(\<gamma>/2)) * (exp(\<i>*\<psi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * exp(\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * cos(\<gamma>/2) + sin(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2)) 
+ cos(\<gamma>/2) * (-sin(\<theta>\<^sub>A/2) * -sin(\<theta>\<^sub>B/2) * cos(\<gamma>/2) + exp (-\<i>*\<psi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * exp (-\<i>*\<psi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2))
]]"


lemma (in restricted_strategic_space)
  shows "(J\<^sup>\<dagger>)*\<psi>\<^sub>2 = \<psi>\<^sub>f"
proof
  fix i j assume "i < dim_row \<psi>\<^sub>f" and "j < dim_col \<psi>\<^sub>f"
  then have "i\<in>{0,1,2,3} \<and> j=0" using mat_of_cols_list_def by auto 
  then show "((J\<^sup>\<dagger>)*\<psi>\<^sub>2) $$(i,j) = \<psi>\<^sub>f $$(i,j)" 
    using mat_of_cols_list_def sum_4 hermite_cnj_of_J by auto
next
  show "dim_row ((J\<^sup>\<dagger>)*\<psi>\<^sub>2) = dim_row \<psi>\<^sub>f" using mat_of_cols_list_def by auto  
next
  show "dim_col ((J\<^sup>\<dagger>)*\<psi>\<^sub>2) = dim_col \<psi>\<^sub>f" using mat_of_cols_list_def by auto  
qed 


abbreviation (in restricted_strategic_space) prob00 :: "complex Matrix.mat \<Rightarrow> real" where
"prob00 v \<equiv> (prob0 2 v 0) * (prob0 2 v 1)"

abbreviation (in restricted_strategic_space) prob01 :: "complex Matrix.mat \<Rightarrow> real" where
"prob01 v \<equiv> (prob0 2 v 0) * (prob1 2 v 1)"

abbreviation (in restricted_strategic_space) prob10 :: "complex Matrix.mat \<Rightarrow> real" where
"prob10 v \<equiv> (prob1 2 v 0) * (prob0 2 v 1)"

abbreviation (in restricted_strategic_space) prob11 :: "complex Matrix.mat \<Rightarrow> real" where
"prob11 v \<equiv> (prob1 2 v 0) * (prob1 2 v 1)"


definition (in restricted_strategic_space) alice_payoff ::"real" where
"alice_payoff \<equiv> 3*(prob00 \<psi>\<^sub>f) + 1*(prob11 \<psi>\<^sub>f) + 5*(prob01 \<psi>\<^sub>f) + 0*(prob10 \<psi>\<^sub>f)"


definition (in restricted_strategic_space)bob_payoff ::"real" where
"bob_payoff \<equiv> 3*(prob00 \<psi>\<^sub>f) + 1*(prob11 \<psi>\<^sub>f) + 0*(prob01 \<psi>\<^sub>f) + 5*(prob10 \<psi>\<^sub>f)"

lemma cos_pi_div_2: "cos(\<pi>/2) = 0" sorry

lemma (in restricted_strategic_space) classical_case:
  assumes "\<gamma> = 0"
  shows "\<psi>\<^sub>A = 0 \<and> \<theta>\<^sub>A = \<pi> \<and> \<psi>\<^sub>B = 0 \<and> \<theta>\<^sub>B = \<pi> \<longrightarrow> alice_payoff = 1 \<and> bob_payoff = 1"
proof-
  show ?thesis
    using alice_payoff_def bob_payoff_def apply auto
    sorry
qed

end