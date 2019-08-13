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
  assumes "0 \<le> \<theta>\<^sub>A \<and> \<theta>\<^sub>A \<le> 2*pi"
      and "0 \<le> \<psi>\<^sub>A \<and> \<psi>\<^sub>A \<le> 2*pi"
      and "0 \<le> \<theta>\<^sub>B \<and> \<theta>\<^sub>B \<le> 2*pi"
      and "0 \<le> \<psi>\<^sub>B \<and> \<psi>\<^sub>B \<le> 2*pi"

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
"prob00 v \<equiv> if state 2 v then (cmod (v $$ (0, 0)))\<^sup>2 else undefined"

abbreviation (in restricted_strategic_space) prob01 :: "complex Matrix.mat \<Rightarrow> real" where
"prob01 v \<equiv> if state 2 v then (cmod (v $$ (1, 0)))\<^sup>2 else undefined"

abbreviation (in restricted_strategic_space) prob10 :: "complex Matrix.mat \<Rightarrow> real" where
"prob10 v \<equiv> if state 2 v then (cmod (v $$ (2, 0)))\<^sup>2 else undefined"

abbreviation (in restricted_strategic_space) prob11 :: "complex Matrix.mat \<Rightarrow> real" where
"prob11 v \<equiv> if state 2 v then (cmod (v $$ (3, 0)))\<^sup>2 else undefined"


definition (in restricted_strategic_space) alice_payoff ::"real" where
"alice_payoff \<equiv> 3*(prob00 \<psi>\<^sub>f) + 1*(prob11 \<psi>\<^sub>f) + 0*(prob01 \<psi>\<^sub>f) + 5*(prob10 \<psi>\<^sub>f)"


definition (in restricted_strategic_space) bob_payoff ::"real" where
"bob_payoff \<equiv> 3*(prob00 \<psi>\<^sub>f) + 1*(prob11 \<psi>\<^sub>f) + 5*(prob01 \<psi>\<^sub>f) + 0*(prob10 \<psi>\<^sub>f)"

lemma select_index_2_0: "{x. select_index 2 0 x} = {2,3}"
  using select_index_def by auto
lemma select_index_2_0_inv: "{x. x < 4 \<and> \<not> select_index 2 0 x} = {0,1}"
  using select_index_def by auto
lemma select_index_2_1: "{x. select_index 2 (Suc 0) x} = {1,3}"
proof
  show "{1, 3} \<subseteq> {x. select_index 2 (Suc 0) x}" using select_index_def by auto
  show "{x. select_index 2 (Suc 0) x} \<subseteq> {1, 3}"
  proof
    fix x assume "x \<in> {x. select_index 2 (Suc 0) x}"
    then have "x \<in> {0,1,2,3} \<and> x mod 2 \<ge> 1" using select_index_def by auto
    then show "x \<in> {1,3}" by auto
  qed
qed
lemma select_index_2_1_inv: "{x. x < 4 \<and> \<not> select_index 2 (Suc 0) x} = {0,2}"
  using select_index_def select_index_2_1 by auto

lemma cos_sin_squared_add_cpx: 
  "complex_of_real (cos (\<gamma>/2)) * complex_of_real (cos (\<gamma>/2)) -
   \<i>*complex_of_real (sin (\<gamma>/2)) * (\<i>*complex_of_real (sin (\<gamma>/2))) = 1"
  apply (auto simp add: algebra_simps)
  by (metis of_real_add of_real_hom.hom_one of_real_mult sin_cos_squared_add3)

lemma sin_cos_squared_add_cpx:
  "\<i>*complex_of_real (sin (\<gamma> / 2)) * (\<i>*complex_of_real (sin (\<gamma> / 2))) -
   complex_of_real (cos (\<gamma> / 2)) * complex_of_real (cos (\<gamma> / 2)) = -1"
  apply (auto simp add: algebra_simps)
  by (metis of_real_add of_real_hom.hom_one of_real_mult sin_cos_squared_add3)

lemma unit_vec_4_is_state: "state 2 (Matrix.mat 4 (Suc 0) (\<lambda>(i, j). [[0, 0, 0, 1]] ! j ! i))"
  using state_def cpx_vec_length_def by (auto simp add: set_sub_4)

lemma minus_unit_vec_4_is_state: "state 2 (Matrix.mat 4 (Suc 0) (\<lambda>(i, j). [[- 1, 0, 0, 0]] ! j ! i))"
  using state_def cpx_vec_length_def by (auto simp add: set_sub_4)

lemma (in restricted_strategic_space) classical_case:
  assumes "\<gamma> = 0"
  shows "\<psi>\<^sub>A = 0 \<and> \<theta>\<^sub>A = pi \<and> \<psi>\<^sub>B = 0 \<and> \<theta>\<^sub>B = pi \<longrightarrow> alice_payoff = 1 \<and> bob_payoff = 1"
  using alice_payoff_def bob_payoff_def mat_of_cols_list_def cos_sin_squared_add_cpx 
        unit_vec_4_is_state
  by (auto simp add: select_index_2_0 select_index_2_0_inv select_index_2_1 select_index_2_1_inv)

lemma cmod_squared_of_rotated_real:
  fixes x y
  shows "(cmod (exp (\<i>*complex_of_real y) * complex_of_real x))\<^sup>2 = x\<^sup>2"
  by (simp add: norm_mult)

lemma sin_squared_le_one:
  fixes x::real
  shows "(sin x)\<^sup>2 \<le> 1"
  using abs_sin_le_one abs_square_le_1 by blast

lemma cos_squared_le_one:
  fixes x::real
  shows "(cos x)\<^sup>2 \<le> 1"
  using abs_cos_le_one abs_square_le_1 by blast

lemma alice_vec_is_state: "state 2 (Matrix.mat 4 (Suc 0) (\<lambda>(i, j). 
[[0, exp (\<i>*complex_of_real \<psi>\<^sub>A) * complex_of_real (cos (\<theta>\<^sub>A / 2)), 0, complex_of_real (sin (\<theta>\<^sub>A / 2))]] ! j ! i))"
  using state_def cpx_vec_length_def cmod_squared_of_rotated_real by (auto simp add: set_sub_4)

lemma bob_vec_is_state: "state 2 (Matrix.mat 4 (Suc 0) (\<lambda>(i, j). 
[[0, 0, exp (\<i>*complex_of_real \<psi>\<^sub>B) * complex_of_real (cos (\<theta>\<^sub>B / 2)), complex_of_real (sin (\<theta>\<^sub>B / 2))]] ! j ! i))"
  using state_def cpx_vec_length_def cmod_squared_of_rotated_real by (auto simp add: set_sub_4)

lemma (in restricted_strategic_space) classical_alice_optimal:
  assumes "\<gamma> = 0" and "\<psi>\<^sub>B = 0 \<and> \<theta>\<^sub>B = pi"
  shows "alice_payoff \<le> 1"
  using alice_payoff_def mat_of_cols_list_def assms cmod_squared_of_rotated_real 
        sin_squared_le_one alice_vec_is_state
  by (auto simp add: select_index_2_0 select_index_2_0_inv select_index_2_1 select_index_2_1_inv)

lemma (in restricted_strategic_space) classical_bob_optimal:
  assumes "\<gamma> = 0" and "\<psi>\<^sub>A = 0 \<and> \<theta>\<^sub>A = pi"
  shows "bob_payoff \<le> 1"
  using bob_payoff_def mat_of_cols_list_def assms cmod_squared_of_rotated_real 
        sin_squared_le_one bob_vec_is_state
  by (auto simp add: select_index_2_0 select_index_2_0_inv select_index_2_1 select_index_2_1_inv)

lemma exp_of_half_pi: 
  fixes x
  assumes "x = pi/2"
  shows "exp (\<i> * complex_of_real x) = \<i>"
  using assms cis_conv_exp cis_pi_half by fastforce

lemma exp_of_minus_half_pi: 
  fixes x
  assumes "x = pi/2"
  shows "exp (-(\<i> * complex_of_real x)) = -\<i>"
  using assms cis_conv_exp cis_minus_pi_half by fastforce

lemma sin_of_quarter_pi:
  fixes x
  assumes "x = pi/2"
  shows "sin (x/2) = (sqrt 2)/2"
  by (auto simp add: assms sin_45)

lemma cos_of_quarter_pi:
  fixes x
  assumes "x = pi/2"
  shows "cos (x/2) = (sqrt 2)/2"
  by (auto simp add: assms cos_45)

lemma exp_of_real:
  fixes x::real
  shows "exp (\<i> * x) = cos x + \<i> * (sin x)"
proof
  show "Re (exp (\<i> * x)) = Re ((cos x) + \<i> * (sin x))"
    using Re_exp by simp
  show "Im (exp (\<i> * x)) = Im ((cos x) + \<i> * (sin x))"
    using Im_exp by simp
qed

lemma exp_of_real_inv:
  fixes x::real
  shows "exp (-(\<i> * x)) = cos x - \<i> * (sin x)"
proof
  show "Re (exp (-(\<i> * x))) = Re ((cos x) - \<i> * (sin x))"
    using Re_exp by simp
  show "Im (exp (-(\<i> * x))) = Im ((cos x) - \<i> * (sin x))"
    using Im_exp by simp
qed

lemma exp_to_sin:
  fixes x::real
  shows "exp (\<i> * x) - exp (-(\<i> * x)) = 2*\<i>*(sin x)"
  using exp_of_real exp_of_real_inv by simp

lemma exp_to_cos:
  fixes x::real
  shows "exp (\<i> * x) + exp (-(\<i> * x)) = 2*(cos x)"
  using exp_of_real exp_of_real_inv by simp


lemma cmod_real_prod_squared: 
  fixes x y::real
  shows "(cmod (complex_of_real x * complex_of_real y))\<^sup>2 = x\<^sup>2 * y\<^sup>2"
  by (simp add: norm_mult power_mult_distrib)

lemma quantum_reward_simp:
  fixes x y::real
  shows "3 * (cmod (complex_of_real (sin x) * complex_of_real (cos y)))\<^sup>2 +
         (cmod (complex_of_real (cos x) * complex_of_real (cos y)))\<^sup>2 = 
         2 * (sin x)\<^sup>2 * (cos y)\<^sup>2 + (cos y)\<^sup>2"
proof-
  have "3 * (sin x)\<^sup>2 * (cos y)\<^sup>2 + (cos x)\<^sup>2 * (cos y)\<^sup>2 = 
        (2 * (sin x)\<^sup>2 * (cos y)\<^sup>2) + ((sin x)\<^sup>2 + (cos x)\<^sup>2) * (cos y)\<^sup>2" 
    by (auto simp add: algebra_simps simp del: sin_cos_squared_add2)
  then show ?thesis
    by (simp add: cmod_real_prod_squared power_mult_distrib)
qed

lemma quantum_reward_le_3: 
  fixes x y::real
  shows "2 * (sin x)\<^sup>2 * (cos y)\<^sup>2 + (cos y)\<^sup>2 \<le> 3"
proof-
  have "(sin x)\<^sup>2 * (cos y)\<^sup>2 \<le> 1" by (simp add: sin_squared_le_one cos_squared_le_one mult_le_one)
  then have "2 * (sin x)\<^sup>2 * (cos y)\<^sup>2 \<le> 2" by simp
  moreover have "(cos y)\<^sup>2 \<le> 1" using cos_squared_le_one[of "y"] by simp
  ultimately show ?thesis by simp
qed

lemma sqrt_two_squared_cpx: "complex_of_real (sqrt 2) * complex_of_real (sqrt 2) = 2"
  by (metis dbl_def dbl_simps(5) mult_2_right of_real_mult of_real_numeral real_sqrt_four real_sqrt_mult)

lemma hidden_sqrt_two_squared_cpx: "complex_of_real (sqrt 2) * (complex_of_real (sqrt 2) * x) / 4 = x/2"
  using sqrt_two_squared_cpx by (auto simp add: algebra_simps)

lemma (in restricted_strategic_space) quantum_case:
  assumes "\<gamma> = pi/2"
  shows "\<psi>\<^sub>A = pi*(1/2) \<and> \<theta>\<^sub>A = 0 \<and> \<psi>\<^sub>B = pi/2 \<and> \<theta>\<^sub>B = 0 \<longrightarrow> alice_payoff = 3 \<and> bob_payoff = 3"
  using alice_payoff_def bob_payoff_def mat_of_cols_list_def sin_cos_squared_add_cpx
        cmod_squared_of_rotated_real exp_of_half_pi exp_of_minus_half_pi minus_unit_vec_4_is_state
  by (auto simp add: select_index_2_0 select_index_2_0_inv select_index_2_1 select_index_2_1_inv)

lemma alice_quantum_vec_is_state: "state 2 (Matrix.mat 4 (Suc 0) (\<lambda>(i, j). 
[[-(complex_of_real (sin \<psi>\<^sub>A) * complex_of_real (cos (\<theta>\<^sub>A / 2))), 
  -complex_of_real (sin (\<theta>\<^sub>A / 2)), 
  0, 
  complex_of_real (cos \<psi>\<^sub>A) * complex_of_real (cos (\<theta>\<^sub>A / 2))]] ! j ! i))"
proof-
  have "(sin \<psi>\<^sub>A)\<^sup>2 * (cos (\<theta>\<^sub>A / 2))\<^sup>2 + ((sin (\<theta>\<^sub>A / 2))\<^sup>2 + (cos \<psi>\<^sub>A)\<^sup>2 * (cos (\<theta>\<^sub>A / 2))\<^sup>2) =
        ((sin \<psi>\<^sub>A)\<^sup>2 + (cos \<psi>\<^sub>A)\<^sup>2) * (cos (\<theta>\<^sub>A / 2))\<^sup>2 + (sin (\<theta>\<^sub>A / 2))\<^sup>2"
    by (auto simp add: algebra_simps simp del: sin_cos_squared_add2)
  then show ?thesis
    using state_def cpx_vec_length_def cmod_real_prod_squared sin_cos_squared_add 
    by (auto simp add: set_sub_4)
qed

lemma bob_quantum_vec_is_state: "state 2 (Matrix.mat 4 (Suc 0) (\<lambda>(i, j). 
[[-(complex_of_real (sin \<psi>\<^sub>A) * complex_of_real (cos (\<theta>\<^sub>A / 2))), 
  0, 
  -complex_of_real (sin (\<theta>\<^sub>A / 2)), 
  complex_of_real (cos \<psi>\<^sub>A) * complex_of_real (cos (\<theta>\<^sub>A / 2))]] ! j ! i))"
proof-
  have "(sin \<psi>\<^sub>A)\<^sup>2 * (cos (\<theta>\<^sub>A / 2))\<^sup>2 + ((sin (\<theta>\<^sub>A / 2))\<^sup>2 + (cos \<psi>\<^sub>A)\<^sup>2 * (cos (\<theta>\<^sub>A / 2))\<^sup>2) =
        ((sin \<psi>\<^sub>A)\<^sup>2 + (cos \<psi>\<^sub>A)\<^sup>2) * (cos (\<theta>\<^sub>A / 2))\<^sup>2 + (sin (\<theta>\<^sub>A / 2))\<^sup>2"
    by (auto simp add: algebra_simps simp del: sin_cos_squared_add2)
  then show ?thesis
    using state_def cpx_vec_length_def cmod_real_prod_squared sin_cos_squared_add 
    by (auto simp add: set_sub_4)
qed

lemma (in restricted_strategic_space) quantum_alice_optimal:
  assumes "\<gamma> = pi/2"
  shows "\<psi>\<^sub>B = pi/2 \<and> \<theta>\<^sub>B = 0 \<longrightarrow> alice_payoff \<le> 3"
proof
  assume asm:"\<psi>\<^sub>B = pi/2 \<and> \<theta>\<^sub>B = 0"
  have "\<psi>\<^sub>f $$ (0,0) = -(sin \<psi>\<^sub>A) * (cos (\<theta>\<^sub>A/2))"
  proof-
    have "\<psi>\<^sub>f $$ (0,0) = \<i> * (sqrt 2/2) * (sqrt 2/2) * (cos (\<theta>\<^sub>A/2)) * exp (\<i> * \<psi>\<^sub>A) +
                        \<i> * (sqrt 2/2) * (sqrt 2/2) * (cos (\<theta>\<^sub>A/2)) * -exp (-(\<i> * \<psi>\<^sub>A))"
      using mat_of_cols_list_def asm assms exp_of_half_pi exp_of_minus_half_pi
      by (auto simp add: sin_of_quarter_pi[of "\<gamma>"] cos_of_quarter_pi[of "\<gamma>"] algebra_simps)
    then have "\<psi>\<^sub>f $$ (0,0) = \<i> * (sqrt 2/2) * (sqrt 2/2) * (cos (\<theta>\<^sub>A/2)) * (exp (\<i> * \<psi>\<^sub>A) - exp (-(\<i> * \<psi>\<^sub>A)))"
      by (auto simp add: algebra_simps)
    then have "\<psi>\<^sub>f $$ (0,0) = \<i> * (cos (\<theta>\<^sub>A/2)) * (1/2) * (exp (\<i> * \<psi>\<^sub>A) - exp (-(\<i> * \<psi>\<^sub>A)))"
      using sqrt_two_squared_cpx by (auto simp add: algebra_simps)
    then show ?thesis
      using exp_to_sin by (simp add: algebra_simps)
  qed
  moreover have "\<psi>\<^sub>f $$ (1,0) = -(sin (\<theta>\<^sub>A/2))"
    using mat_of_cols_list_def asm assms exp_of_half_pi exp_of_minus_half_pi sqrt_two_squared_cpx
    by (auto simp add: sin_of_quarter_pi[of "\<gamma>"] cos_of_quarter_pi[of "\<gamma>"])
  moreover have "\<psi>\<^sub>f $$ (2,0) = 0"
    using mat_of_cols_list_def asm assms exp_of_half_pi exp_of_minus_half_pi sqrt_two_squared_cpx
    by (auto simp add: sin_of_quarter_pi[of "\<gamma>"] cos_of_quarter_pi[of "\<gamma>"] algebra_simps)
  moreover have "\<psi>\<^sub>f $$ (3,0) = (cos \<psi>\<^sub>A) * (cos (\<theta>\<^sub>A/2))"
  proof-
    have "\<psi>\<^sub>f $$ (3,0) = exp (\<i> * \<psi>\<^sub>A) * (cos (\<theta>\<^sub>A / 2)) * (sqrt 2/2) * (sqrt 2/2) +
                        exp (- (\<i> * \<psi>\<^sub>A)) * (cos (\<theta>\<^sub>A / 2)) * (sqrt 2/2) * (sqrt 2/2)"
      using mat_of_cols_list_def asm assms exp_of_half_pi exp_of_minus_half_pi
      by (auto simp add: sin_of_quarter_pi[of "\<gamma>"] cos_of_quarter_pi[of "\<gamma>"] algebra_simps)
    then have "\<psi>\<^sub>f $$ (3,0) = (exp (\<i> * \<psi>\<^sub>A) + exp (-(\<i> * \<psi>\<^sub>A))) * (cos (\<theta>\<^sub>A/2)) * (sqrt 2/2) * (sqrt 2/2)"
      by (auto simp add: algebra_simps)
    then have "\<psi>\<^sub>f $$ (3,0) = (exp (\<i> * \<psi>\<^sub>A) + exp (-(\<i> * \<psi>\<^sub>A))) * (cos (\<theta>\<^sub>A/2)) * (1/2)"
      using sqrt_two_squared_cpx hidden_sqrt_two_squared_cpx by (auto simp add: algebra_simps)
    then show ?thesis
      using exp_to_cos by (simp add: algebra_simps)
  qed
  ultimately show "alice_payoff \<le> 3"
  using alice_payoff_def mat_of_cols_list_def alice_quantum_vec_is_state quantum_reward_simp quantum_reward_le_3 
  by (auto simp add: select_index_2_0 select_index_2_0_inv select_index_2_1 select_index_2_1_inv)
qed

lemma (in restricted_strategic_space) quantum_bob_optimal:
  assumes "\<gamma> = pi/2"
  shows "\<psi>\<^sub>A = pi/2 \<and> \<theta>\<^sub>A = 0 \<longrightarrow> bob_payoff \<le> 3"
proof
  assume asm:"\<psi>\<^sub>A = pi/2 \<and> \<theta>\<^sub>A = 0"
  have "\<psi>\<^sub>f $$ (0,0) = -(sin \<psi>\<^sub>B) * (cos (\<theta>\<^sub>B/2))"
  proof-
    have "\<psi>\<^sub>f $$ (0,0) = \<i> * (sqrt 2/2) * (sqrt 2/2) * (cos (\<theta>\<^sub>B/2)) * exp (\<i> * \<psi>\<^sub>B) +
                        \<i> * (sqrt 2/2) * (sqrt 2/2) * (cos (\<theta>\<^sub>B/2)) * -exp (-(\<i> * \<psi>\<^sub>B))"
      using mat_of_cols_list_def asm assms exp_of_half_pi exp_of_minus_half_pi
      by (auto simp add: sin_of_quarter_pi[of "\<gamma>"] cos_of_quarter_pi[of "\<gamma>"] algebra_simps)
    then have "\<psi>\<^sub>f $$ (0,0) = \<i> * (sqrt 2/2) * (sqrt 2/2) * (cos (\<theta>\<^sub>B/2)) * (exp (\<i> * \<psi>\<^sub>B) - exp (-(\<i> * \<psi>\<^sub>B)))"
      by (auto simp add: algebra_simps)
    then have "\<psi>\<^sub>f $$ (0,0) = \<i> * (cos (\<theta>\<^sub>B/2)) * (1/2) * (exp (\<i> * \<psi>\<^sub>B) - exp (-(\<i> * \<psi>\<^sub>B)))"
      using sqrt_two_squared_cpx by (auto simp add: algebra_simps)
    then show ?thesis
      using exp_to_sin by (simp add: algebra_simps)
  qed
  moreover have "\<psi>\<^sub>f $$ (1,0) = 0"
    using mat_of_cols_list_def asm assms exp_of_half_pi exp_of_minus_half_pi sqrt_two_squared_cpx
    by (auto simp add: sin_of_quarter_pi[of "\<gamma>"] cos_of_quarter_pi[of "\<gamma>"] algebra_simps)
  moreover have "\<psi>\<^sub>f $$ (2,0) = -(sin (\<theta>\<^sub>B/2))"
    using mat_of_cols_list_def asm assms exp_of_half_pi exp_of_minus_half_pi sqrt_two_squared_cpx
    by (auto simp add: sin_of_quarter_pi[of "\<gamma>"] cos_of_quarter_pi[of "\<gamma>"] algebra_simps)
  moreover have "\<psi>\<^sub>f $$ (3,0) = (cos \<psi>\<^sub>B) * (cos (\<theta>\<^sub>B/2))"
  proof-
    have "\<psi>\<^sub>f $$ (3,0) = exp (\<i> * \<psi>\<^sub>B) * (cos (\<theta>\<^sub>B / 2)) * (sqrt 2/2) * (sqrt 2/2) +
                        exp (- (\<i> * \<psi>\<^sub>B)) * (cos (\<theta>\<^sub>B / 2)) * (sqrt 2/2) * (sqrt 2/2)"
      using mat_of_cols_list_def asm assms exp_of_half_pi exp_of_minus_half_pi
      by (auto simp add: sin_of_quarter_pi[of "\<gamma>"] cos_of_quarter_pi[of "\<gamma>"] algebra_simps)
    then have "\<psi>\<^sub>f $$ (3,0) = (exp (\<i> * \<psi>\<^sub>B) + exp (-(\<i> * \<psi>\<^sub>B))) * (cos (\<theta>\<^sub>B/2)) * (sqrt 2/2) * (sqrt 2/2)"
      by (auto simp add: algebra_simps)
    then have "\<psi>\<^sub>f $$ (3,0) = (exp (\<i> * \<psi>\<^sub>B) + exp (-(\<i> * \<psi>\<^sub>B))) * (cos (\<theta>\<^sub>B/2)) * (1/2)"
      using sqrt_two_squared_cpx hidden_sqrt_two_squared_cpx by (auto simp add: algebra_simps)
    then show ?thesis
      using exp_to_cos by (simp add: algebra_simps)
  qed
  ultimately show "bob_payoff \<le> 3"
  using bob_payoff_def mat_of_cols_list_def bob_quantum_vec_is_state quantum_reward_simp quantum_reward_le_3 
  by (auto simp add: select_index_2_0 select_index_2_0_inv select_index_2_1 select_index_2_1_inv)
qed

end