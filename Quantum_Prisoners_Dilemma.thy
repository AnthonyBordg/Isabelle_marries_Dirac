(*
authors:
  Yijun He, University of Cambridge, yh403@cam.ac.uk
  Hanna Lachnitt, TU Wien, lachnitt@student.tuwien.ac.at
*)

theory Quantum_Prisoners_Dilemma
imports
  More_Tensor
  Measurement
begin


text \<open>
Prisoner's dilemma ceases to pose a dilemma if quantum strategies are allowed for. Indeed, 
Alice and Bob both choosing to defect is no longer a Nash equilibrium. However, a new Nash 
equilibrium appears which is at the same time Pareto optimal. Moreover, there exists a 
quantum strategy which always gives reward if played against any classical strategy. 
Below the parameter \<gamma> can be seen as a measure of the game's entanglement. The game behaves 
classically if \<gamma> = 0, and for the maximally entangled case (\<gamma> = 2*$\pi$) the dilemma disappears
as pointed out above.   
\<close>


section \<open>The Set-Up\<close>

locale prisoner =
  fixes \<gamma>:: "real" 
  assumes "\<gamma> \<le> (2*pi)"
      and "\<gamma> \<ge> 0"

abbreviation (in prisoner) J :: "complex Matrix.mat" where
"J \<equiv> mat_of_cols_list 4  [[cos(\<gamma>/2), 0, 0, \<i>*sin(\<gamma>/2)],
                          [0, cos(\<gamma>/2), -\<i>*sin(\<gamma>/2), 0],
                          [0, -\<i>*sin(\<gamma>/2), cos(\<gamma>/2), 0],
                          [\<i>*sin(\<gamma>/2), 0, 0, cos(\<gamma>/2)]]"

abbreviation (in prisoner) \<psi>\<^sub>1 :: "complex Matrix.mat" where
"\<psi>\<^sub>1 \<equiv> mat_of_cols_list 4 [[cos(\<gamma>/2), 0, 0, \<i>*sin(\<gamma>/2)]]"

lemma (in prisoner) psi_one:
  shows "J * |unit_vec 4 0\<rangle> = \<psi>\<^sub>1"
proof
  fix i j assume a0:"i < dim_row \<psi>\<^sub>1" and a1:"j < dim_col \<psi>\<^sub>1"      
  then have "(J * |unit_vec 4 0\<rangle>) $$ (i,j) = (\<Sum>k<4. (J $$ (i,k)) * ( |unit_vec 4 0\<rangle> $$ (k,j)))" 
    using mat_of_cols_list_def ket_vec_def by auto
  also have "... = (\<Sum>k\<in>{0,1,2,3}. (J $$ (i,k)) * ( |unit_vec 4 0\<rangle> $$ (k,j)))" 
    using set_4 atLeast0LessThan by simp
  also have "... = \<psi>\<^sub>1 $$(i,j)"
  proof-
    have "i\<in>{0,1,2,3} \<and> j=0" 
      using a0 a1 mat_of_cols_list_def by auto
    thus ?thesis
      using mat_of_cols_list_def by auto
  qed
  finally show "(J * |unit_vec 4 0\<rangle>) $$ (i,j) = \<psi>\<^sub>1 $$ (i,j)" by simp
next 
  show  "dim_row (J * |unit_vec 4 0\<rangle>) = dim_row \<psi>\<^sub>1"  
    using mat_of_cols_list_def by simp
next
  show  "dim_col (J*|unit_vec 4 0\<rangle>) = dim_col \<psi>\<^sub>1"  
    using mat_of_cols_list_def by (simp add: ket_vec_def)
qed

locale restricted_strategic_space = prisoner +
  fixes \<theta>\<^sub>A:: "real"
    and \<phi>\<^sub>A:: "real" 
    and \<theta>\<^sub>B:: "real"
    and \<phi>\<^sub>B:: "real"
  assumes "0 \<le> \<theta>\<^sub>A \<and> \<theta>\<^sub>A \<le> pi"
      and "0 \<le> \<phi>\<^sub>A \<and> \<phi>\<^sub>A \<le> 2*pi"
      and "0 \<le> \<theta>\<^sub>B \<and> \<theta>\<^sub>B \<le> pi"
      and "0 \<le> \<phi>\<^sub>B \<and> \<phi>\<^sub>B \<le> 2*pi"

abbreviation (in restricted_strategic_space) U\<^sub>A :: "complex Matrix.mat" where
"U\<^sub>A \<equiv> mat_of_cols_list 2 [[exp(\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2), -sin(\<theta>\<^sub>A/2)],
                           [sin(\<theta>\<^sub>A/2), exp(-\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2)]]"

abbreviation (in restricted_strategic_space) U\<^sub>B :: "complex Matrix.mat" where
"U\<^sub>B \<equiv> mat_of_cols_list 2 [[exp(\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2), -sin(\<theta>\<^sub>B/2)],
                           [sin(\<theta>\<^sub>B/2), exp(-\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2)]]"

abbreviation (in restricted_strategic_space) \<psi>\<^sub>2 :: "complex Matrix.mat" where
"\<psi>\<^sub>2 \<equiv> 
mat_of_cols_list 4 [[exp(\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * exp(\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * cos(\<gamma>/2) + sin(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2),
                     exp(\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * -sin(\<theta>\<^sub>B/2) * cos(\<gamma>/2) + sin(\<theta>\<^sub>A/2) * exp(-\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2),
                     -sin(\<theta>\<^sub>A/2) * exp (\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * cos(\<gamma>/2) + exp (-\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2),
                     sin(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2) * cos(\<gamma>/2) + exp (-\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * exp (-\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2)]]"

abbreviation (in restricted_strategic_space) U\<^sub>A\<^sub>B :: "complex Matrix.mat" where
"U\<^sub>A\<^sub>B \<equiv> 
mat_of_cols_list 4 [[exp(\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * exp(\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2), exp(\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * -sin(\<theta>\<^sub>B/2),
                            -sin(\<theta>\<^sub>A/2) * exp(\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2), -sin(\<theta>\<^sub>A/2) * -sin(\<theta>\<^sub>B/2)],
                    [exp(\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2), exp(\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * exp(-\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2),
                            -sin(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2), -sin(\<theta>\<^sub>A/2) * exp(-\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2)],
                    [sin(\<theta>\<^sub>A/2) * exp(\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2), -sin(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2),
                            exp(-\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * exp (\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2), exp(-\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * -sin(\<theta>\<^sub>B/2)],
                    [sin(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2), sin(\<theta>\<^sub>A/2) * exp(-\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2),
                            exp(-\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2), exp (-\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * exp(-\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2)]]"

lemma set_4_lessThan: "{..<4::nat} = {0,1,2,3}" by auto (* idem *)
lemma set_2_lessThan: "{..<2::nat} = {0,1}" by auto

(* The 4 following lemmas should be moved in Basics.thy *)
lemma two_div_two [simp]: 
  shows "2 div Suc (Suc 0) = 1" by simp

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
  show "dim_row (U\<^sub>A \<Otimes> U\<^sub>B) = dim_row U\<^sub>A\<^sub>B" 
    using mat_of_cols_list_def by simp
next
  show "dim_col (U\<^sub>A \<Otimes> U\<^sub>B) = dim_col U\<^sub>A\<^sub>B" 
    using mat_of_cols_list_def by simp
qed

lemma (in restricted_strategic_space) psi_two:
  shows "(U\<^sub>A \<Otimes> U\<^sub>B) * \<psi>\<^sub>1 = \<psi>\<^sub>2"
proof
  fix i j
  assume a0:"i < dim_row \<psi>\<^sub>2" and a1:"j < dim_col \<psi>\<^sub>2"
  then show "((U\<^sub>A \<Otimes> U\<^sub>B) * \<psi>\<^sub>1) $$ (i,j) = \<psi>\<^sub>2 $$ (i,j)"
  proof-
    have "i\<in>{0,1,2,3} \<and> j=0" 
      using a0 a1 mat_of_cols_list_def by auto
    thus ?thesis
      using mat_of_cols_list_def U\<^sub>A_tensor_U\<^sub>B set_4_lessThan by auto
  qed
next
  show "dim_row ((U\<^sub>A \<Otimes> U\<^sub>B)*\<psi>\<^sub>1) = dim_row \<psi>\<^sub>2" 
    using mat_of_cols_list_def by simp 
next
  show "dim_col ((U\<^sub>A \<Otimes> U\<^sub>B)*\<psi>\<^sub>1) = dim_col \<psi>\<^sub>2" 
    using mat_of_cols_list_def by simp  
qed

abbreviation (in prisoner) J_cnj :: "complex Matrix.mat" where
"J_cnj \<equiv> mat_of_cols_list 4 [[cos(\<gamma>/2), 0, 0, -\<i>*sin(\<gamma>/2)],
                             [0, cos(\<gamma>/2), \<i>*sin(\<gamma>/2), 0],
                             [0, \<i>*sin(\<gamma>/2), cos(\<gamma>/2), 0],
                             [-\<i>*sin(\<gamma>/2), 0, 0, cos(\<gamma>/2)]]"

lemma (in prisoner) hermite_cnj_of_J [simp]:
  shows "J\<^sup>\<dagger> = J_cnj"
proof
  fix i j assume a0:"i < dim_row J_cnj" and a1:"j < dim_col J_cnj"
  then show "J\<^sup>\<dagger> $$ (i,j) = J_cnj $$ (i,j)"
  proof-
    have "i\<in>{0,1,2,3} \<and> j\<in>{0,1,2,3}" 
      using a0 a1 mat_of_cols_list_def by auto
    thus ?thesis
      using mat_of_cols_list_def hermite_cnj_def by auto
  qed
next
  show "dim_row (J\<^sup>\<dagger>) = dim_row J_cnj" 
    using mat_of_cols_list_def by simp
next
  show "dim_col (J\<^sup>\<dagger>) = dim_col J_cnj" 
    using mat_of_cols_list_def by simp
qed

abbreviation (in restricted_strategic_space) \<psi>\<^sub>f :: "complex Matrix.mat" where
"\<psi>\<^sub>f \<equiv> mat_of_cols_list 4 [[
cos(\<gamma>/2) * (exp(\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * exp(\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * cos(\<gamma>/2) + sin(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2))
+ (-\<i>*sin(\<gamma>/2)) * (sin(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2) * cos(\<gamma>/2) + exp (-\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * exp (-\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2)),

cos(\<gamma>/2) * (exp(\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * -sin(\<theta>\<^sub>B/2) * cos(\<gamma>/2) + sin(\<theta>\<^sub>A/2) * exp(-\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2)) 
+ (\<i>*sin(\<gamma>/2)) * (-sin(\<theta>\<^sub>A/2) * exp (\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * cos(\<gamma>/2) + exp (-\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2)),

(\<i>*sin(\<gamma>/2)) * (exp(\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * -sin(\<theta>\<^sub>B/2) * cos(\<gamma>/2) + sin(\<theta>\<^sub>A/2) * exp(-\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2))
+ cos(\<gamma>/2) * (-sin(\<theta>\<^sub>A/2) * exp (\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * cos(\<gamma>/2) + exp (-\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2)),

(-\<i>*sin(\<gamma>/2)) * (exp(\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * exp(\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * cos(\<gamma>/2) + sin(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2)) 
+ cos(\<gamma>/2) * (sin(\<theta>\<^sub>A/2) * sin(\<theta>\<^sub>B/2) * cos(\<gamma>/2) + exp (-\<i>*\<phi>\<^sub>A)*cos(\<theta>\<^sub>A/2) * exp (-\<i>*\<phi>\<^sub>B)*cos(\<theta>\<^sub>B/2) * \<i>*sin(\<gamma>/2))
]]"

lemma (in restricted_strategic_space) psi_f:
  shows "(J\<^sup>\<dagger>) * \<psi>\<^sub>2 = \<psi>\<^sub>f"
proof
  fix i j assume a0:"i < dim_row \<psi>\<^sub>f" and a1:"j < dim_col \<psi>\<^sub>f"
  then show "((J\<^sup>\<dagger>) * \<psi>\<^sub>2) $$ (i,j) = \<psi>\<^sub>f $$ (i,j)" 
  proof-
    have "i\<in>{0,1,2,3} \<and> j=0" 
      using a0 a1 mat_of_cols_list_def by auto
    thus ?thesis
      using mat_of_cols_list_def set_4_lessThan hermite_cnj_of_J by auto
  qed
next
  show "dim_row ((J\<^sup>\<dagger>) * \<psi>\<^sub>2) = dim_row \<psi>\<^sub>f" 
    using mat_of_cols_list_def by simp  
next
  show "dim_col ((J\<^sup>\<dagger>) * \<psi>\<^sub>2) = dim_col \<psi>\<^sub>f" 
    using mat_of_cols_list_def by simp  
qed

lemma (in prisoner) unit_vec_4_0_ket_is_state: 
  shows "state 2 |unit_vec 4 0\<rangle>"
  using state_def cpx_vec_length_def ket_vec_def unit_vec_def by (auto simp add: set_4_lessThan)

lemma cos_sin_squared_add_cpx: 
  "complex_of_real (cos (\<gamma>/2)) * complex_of_real (cos (\<gamma>/2)) -
   \<i>*complex_of_real (sin (\<gamma>/2)) * (\<i>*complex_of_real (sin (\<gamma>/2))) = 1"
  apply (auto simp add: algebra_simps)
  by (metis of_real_add of_real_hom.hom_one of_real_mult sin_cos_squared_add3)

lemma sin_cos_squared_add_cpx:
  "\<i>*complex_of_real (sin (\<gamma>/2)) * (\<i>*complex_of_real (sin (\<gamma>/2))) -
   complex_of_real (cos (\<gamma>/2)) * complex_of_real (cos (\<gamma>/2)) = -1"
  apply (auto simp add: algebra_simps)
  by (metis of_real_add of_real_hom.hom_one of_real_mult sin_cos_squared_add3)

lemma (in prisoner) J_cnj_times_J:
  shows "J\<^sup>\<dagger> * J = 1\<^sub>m 4"
proof
  fix i j assume a0:"i < dim_row (1\<^sub>m 4)" and a1:"j < dim_col (1\<^sub>m 4)"
  then show "(J\<^sup>\<dagger> * J) $$ (i,j) = 1\<^sub>m 4 $$ (i,j)"
  proof-
    have "i\<in>{0,1,2,3} \<and> j\<in>{0,1,2,3}" 
      using a0 a1 mat_of_cols_list_def by auto
    thus ?thesis
      using mat_of_cols_list_def hermite_cnj_of_J set_4_lessThan cos_sin_squared_add_cpx by auto
  qed
next
  show "dim_row (J\<^sup>\<dagger> * J) = dim_row (1\<^sub>m 4)"
    using mat_of_cols_list_def by simp
next
  show "dim_col (J\<^sup>\<dagger> * J) = dim_col (1\<^sub>m 4)" 
    using mat_of_cols_list_def by simp
qed

lemma (in prisoner) J_times_J_cnj:
  shows "J * (J\<^sup>\<dagger>) = 1\<^sub>m 4"
proof
  fix i j assume a0:"i < dim_row (1\<^sub>m 4)" and a1:"j < dim_col (1\<^sub>m 4)"
  then show "(J * (J\<^sup>\<dagger>)) $$ (i,j) = 1\<^sub>m 4 $$ (i,j)"
  proof-
    have "i\<in>{0,1,2,3} \<and> j\<in>{0,1,2,3}" 
      using a0 a1 mat_of_cols_list_def by auto
    thus ?thesis
      using mat_of_cols_list_def hermite_cnj_of_J set_4_lessThan cos_sin_squared_add_cpx by auto
  qed
next
  show "dim_row (J * (J\<^sup>\<dagger>)) = dim_row (1\<^sub>m 4)"
    using mat_of_cols_list_def by simp
next
  show "dim_col (J * (J\<^sup>\<dagger>)) = dim_col (1\<^sub>m 4)"
    using mat_of_cols_list_def by simp
qed

lemma (in prisoner) J_is_gate:
  shows "gate 2 J"
proof
  show "dim_row J = 2\<^sup>2"
    using mat_of_cols_list_def by simp
  moreover show "square_mat J"
    using mat_of_cols_list_def by simp
  ultimately show "unitary J"
    using mat_of_cols_list_def unitary_def J_cnj_times_J J_times_J_cnj by auto
qed

lemma (in restricted_strategic_space) psi_one_is_state: 
  shows "state 2 \<psi>\<^sub>1"
proof-
  have "state 2 (J * |unit_vec 4 0\<rangle>)"
    using unit_vec_4_0_ket_is_state J_is_gate by auto
  then show ?thesis
    using psi_one by simp
qed

abbreviation (in restricted_strategic_space) U\<^sub>A_cnj :: "complex Matrix.mat" where
"U\<^sub>A_cnj \<equiv> mat_of_cols_list 2 [[(exp(-\<i>*\<phi>\<^sub>A))*cos(\<theta>\<^sub>A/2), sin(\<theta>\<^sub>A/2)],
                              [-sin(\<theta>\<^sub>A/2), (exp (\<i>*\<phi>\<^sub>A))*cos(\<theta>\<^sub>A/2)]]"

abbreviation (in restricted_strategic_space) U\<^sub>B_cnj :: "complex Matrix.mat" where
"U\<^sub>B_cnj \<equiv> mat_of_cols_list 2 [[(exp(-\<i>*\<phi>\<^sub>B))*cos(\<theta>\<^sub>B/2), sin(\<theta>\<^sub>B/2)],
                              [-sin(\<theta>\<^sub>B/2), (exp(\<i>*\<phi>\<^sub>B))*cos(\<theta>\<^sub>B/2)]]"

lemma exp_of_real_cnj:
  fixes x ::real
  shows "cnj (exp (\<i> * x)) = exp (-(\<i> * x))"
proof
  show "Re (cnj (exp (\<i> * x))) = Re (exp (-(\<i> * x)))"
    using Re_exp by simp
  show "Im (cnj (exp (\<i> * x))) = Im (exp (-(\<i> * x)))"
    using Im_exp by simp
qed

lemma exp_of_real_cnj2:
  fixes x ::real
  shows "cnj (exp (-(\<i> * x))) = exp (\<i> * x)"
proof
  show "Re (cnj (exp (-(\<i> * x)))) = Re (exp (\<i> * x))"
    using Re_exp by simp
  show "Im (cnj (exp (-(\<i> * x)))) = Im (exp (\<i> * x))"
    using Im_exp by simp
qed

lemma (in restricted_strategic_space) hermite_cnj_of_U\<^sub>A:
  shows "U\<^sub>A\<^sup>\<dagger> = U\<^sub>A_cnj"
proof
  fix i j assume a0:"i < dim_row U\<^sub>A_cnj" and a1:"j < dim_col U\<^sub>A_cnj"
  then show "U\<^sub>A\<^sup>\<dagger> $$ (i,j) = U\<^sub>A_cnj $$ (i,j)"
  proof-
    have "i\<in>{0,1} \<and> j\<in>{0,1}"
      using a0 a1 mat_of_cols_list_def by auto
    thus ?thesis
      using mat_of_cols_list_def hermite_cnj_def exp_of_real_cnj exp_of_real_cnj2 by auto
  qed
next
  show "dim_row (U\<^sub>A\<^sup>\<dagger>) = dim_row U\<^sub>A_cnj"
    using mat_of_cols_list_def by simp
next
  show "dim_col (U\<^sub>A\<^sup>\<dagger>) = dim_col U\<^sub>A_cnj"
    using mat_of_cols_list_def by simp
qed

lemma (in restricted_strategic_space) hermite_cnj_of_U\<^sub>B:
  shows "U\<^sub>B\<^sup>\<dagger> = U\<^sub>B_cnj"
proof
  fix i j assume a0:"i < dim_row U\<^sub>B_cnj" and a1:"j < dim_col U\<^sub>B_cnj"
  then show "U\<^sub>B\<^sup>\<dagger> $$ (i,j) = U\<^sub>B_cnj $$ (i,j)"
  proof-
    have "i\<in>{0,1} \<and> j\<in>{0,1}"
      using a0 a1 mat_of_cols_list_def by auto
    thus ?thesis
      using mat_of_cols_list_def hermite_cnj_def exp_of_real_cnj exp_of_real_cnj2 by auto
  qed
next
  show "dim_row (U\<^sub>B\<^sup>\<dagger>) = dim_row U\<^sub>B_cnj"
    using mat_of_cols_list_def by simp
next
  show "dim_col (U\<^sub>B\<^sup>\<dagger>) = dim_col U\<^sub>B_cnj"
    using mat_of_cols_list_def by simp
qed

lemma exp_sin_cos_squared_add:
  fixes x y :: real
  shows "exp (- (\<i> * x)) * cos (y) * (exp (\<i> * x) * cos (y)) + sin(y) * sin(y) = 1"
proof-
  have "exp (- (\<i> * x)) * cos (y) * (exp (\<i> * x) * cos (y)) = cos(y) * cos(y)"
    using exp_minus_inverse by (auto simp add: algebra_simps)
  then show ?thesis
    by (metis of_real_add of_real_hom.hom_one sin_cos_squared_add3)
qed

lemma (in restricted_strategic_space) U\<^sub>A_cnj_times_U\<^sub>A:
  shows "U\<^sub>A\<^sup>\<dagger> * U\<^sub>A = 1\<^sub>m 2"
proof
  fix i j assume a0:"i < dim_row (1\<^sub>m 2)" and a1:"j < dim_col (1\<^sub>m 2)"
  then show "(U\<^sub>A\<^sup>\<dagger> * U\<^sub>A) $$ (i,j) = 1\<^sub>m 2 $$ (i,j)"
  proof-
    have "i\<in>{0,1} \<and> j\<in>{0,1}" 
      using a0 a1 mat_of_cols_list_def by auto
    thus ?thesis
      using mat_of_cols_list_def cos_sin_squared_add_cpx hermite_cnj_of_U\<^sub>A exp_sin_cos_squared_add[of "\<phi>\<^sub>A" "\<theta>\<^sub>A / 2"]
      by (auto simp add: set_2_lessThan algebra_simps)
  qed
next
  show "dim_row (U\<^sub>A\<^sup>\<dagger> * U\<^sub>A) = dim_row (1\<^sub>m 2)"
    using mat_of_cols_list_def by simp
next
  show "dim_col (U\<^sub>A\<^sup>\<dagger> * U\<^sub>A) = dim_col (1\<^sub>m 2)" 
    using mat_of_cols_list_def by simp
qed

lemma (in restricted_strategic_space) U\<^sub>A_times_U\<^sub>A_cnj:
  shows "U\<^sub>A * (U\<^sub>A\<^sup>\<dagger>) = 1\<^sub>m 2"
proof
  fix i j assume a0:"i < dim_row (1\<^sub>m 2)" and a1:"j < dim_col (1\<^sub>m 2)"
  then show "(U\<^sub>A * (U\<^sub>A\<^sup>\<dagger>)) $$ (i,j) = 1\<^sub>m 2 $$ (i,j)"
  proof-
    have "i\<in>{0,1} \<and> j\<in>{0,1}" 
      using a0 a1 mat_of_cols_list_def by auto
    thus ?thesis
      using mat_of_cols_list_def cos_sin_squared_add_cpx hermite_cnj_of_U\<^sub>A exp_sin_cos_squared_add[of "\<phi>\<^sub>A" "\<theta>\<^sub>A / 2"]
      by (auto simp add: set_2_lessThan algebra_simps)
  qed
next
  show "dim_row (U\<^sub>A * (U\<^sub>A\<^sup>\<dagger>)) = dim_row (1\<^sub>m 2)"
    using mat_of_cols_list_def by simp
next
  show "dim_col (U\<^sub>A * (U\<^sub>A\<^sup>\<dagger>)) = dim_col (1\<^sub>m 2)" 
    using mat_of_cols_list_def by simp
qed

lemma (in restricted_strategic_space) U\<^sub>B_cnj_times_U\<^sub>B:
  shows "U\<^sub>B\<^sup>\<dagger> * U\<^sub>B = 1\<^sub>m 2"
proof
  fix i j assume a0:"i < dim_row (1\<^sub>m 2)" and a1:"j < dim_col (1\<^sub>m 2)"
  then show "(U\<^sub>B\<^sup>\<dagger> * U\<^sub>B) $$ (i,j) = 1\<^sub>m 2 $$ (i,j)"
  proof-
    have "i\<in>{0,1} \<and> j\<in>{0,1}" 
      using a0 a1 mat_of_cols_list_def by auto
    thus ?thesis
      using mat_of_cols_list_def cos_sin_squared_add_cpx hermite_cnj_of_U\<^sub>B exp_sin_cos_squared_add[of "\<phi>\<^sub>B" "\<theta>\<^sub>B / 2"]
      by (auto simp add: set_2_lessThan algebra_simps)
  qed
next
  show "dim_row (U\<^sub>B\<^sup>\<dagger> * U\<^sub>B) = dim_row (1\<^sub>m 2)"
    using mat_of_cols_list_def by simp
next
  show "dim_col (U\<^sub>B\<^sup>\<dagger> * U\<^sub>B) = dim_col (1\<^sub>m 2)" 
    using mat_of_cols_list_def by simp
qed

lemma (in restricted_strategic_space) U\<^sub>B_times_U\<^sub>B_cnj:
  shows "U\<^sub>B * (U\<^sub>B\<^sup>\<dagger>) = 1\<^sub>m 2"
proof
  fix i j assume a0:"i < dim_row (1\<^sub>m 2)" and a1:"j < dim_col (1\<^sub>m 2)"
  then show "(U\<^sub>B * (U\<^sub>B\<^sup>\<dagger>)) $$ (i,j) = 1\<^sub>m 2 $$ (i,j)"
  proof-
    have "i\<in>{0,1} \<and> j\<in>{0,1}" 
      using a0 a1 mat_of_cols_list_def by auto
    thus ?thesis
      using mat_of_cols_list_def cos_sin_squared_add_cpx hermite_cnj_of_U\<^sub>B exp_sin_cos_squared_add[of "\<phi>\<^sub>B" "\<theta>\<^sub>B / 2"]
      by (auto simp add: set_2_lessThan algebra_simps)
  qed
next
  show "dim_row (U\<^sub>B * (U\<^sub>B\<^sup>\<dagger>)) = dim_row (1\<^sub>m 2)"
    using mat_of_cols_list_def by simp
next
  show "dim_col (U\<^sub>B * (U\<^sub>B\<^sup>\<dagger>)) = dim_col (1\<^sub>m 2)" 
    using mat_of_cols_list_def by simp
qed

lemma (in restricted_strategic_space) U\<^sub>A\<^sub>_is_gate:
  shows "gate 1 U\<^sub>A"
proof
  show "dim_row U\<^sub>A = 2^1"
    using mat_of_cols_list_def by simp
  moreover show "square_mat U\<^sub>A"
    using mat_of_cols_list_def by simp
  ultimately show "unitary U\<^sub>A"
    using mat_of_cols_list_def unitary_def U\<^sub>A_cnj_times_U\<^sub>A U\<^sub>A_times_U\<^sub>A_cnj by auto
qed

lemma (in restricted_strategic_space) U\<^sub>B_is_gate:
  shows "gate 1 U\<^sub>B"
proof
  show "dim_row U\<^sub>B = 2^1"
    using mat_of_cols_list_def by simp
  moreover show "square_mat U\<^sub>B"
    using mat_of_cols_list_def by simp
  ultimately show "unitary U\<^sub>B"
    using mat_of_cols_list_def unitary_def U\<^sub>B_cnj_times_U\<^sub>B U\<^sub>B_times_U\<^sub>B_cnj by auto
qed

lemma (in restricted_strategic_space) U\<^sub>A\<^sub>B_is_gate:
  shows "gate 2 (U\<^sub>A \<Otimes> U\<^sub>B)"
proof-
  have "gate (1+1) (U\<^sub>A \<Otimes> U\<^sub>B)"
    using U\<^sub>A\<^sub>_is_gate U\<^sub>B_is_gate tensor_gate[of "1" "U\<^sub>A" "1" "U\<^sub>B"] by auto
  then show ?thesis
    by (auto simp add: numeral_2_eq_2)
qed

lemma (in restricted_strategic_space) psi_two_is_state:
  shows "state 2 \<psi>\<^sub>2"
proof-
  have "state 2 ((U\<^sub>A \<Otimes> U\<^sub>B) * \<psi>\<^sub>1)"
    using psi_one_is_state U\<^sub>A\<^sub>B_is_gate by auto
  then show ?thesis
    using psi_two by simp
qed

(* This could be added to Quantum.thy *)
lemma hermite_cnj_of_hermite_cnj:
  fixes M :: "complex Matrix.mat"
  shows "(M\<^sup>\<dagger>)\<^sup>\<dagger> = M"
proof
  show "dim_row ((M\<^sup>\<dagger>)\<^sup>\<dagger>) = dim_row M" by simp
  show "dim_col ((M\<^sup>\<dagger>)\<^sup>\<dagger>) = dim_col M" by simp
  fix i j assume a0:"i < dim_row M" and a1:"j < dim_col M"
  then show "(M\<^sup>\<dagger>)\<^sup>\<dagger> $$ (i,j) = M $$ (i,j)"
  proof-
    show ?thesis
      using hermite_cnj_def a0 a1 by auto
  qed
qed

lemma (in restricted_strategic_space) J_cnj_is_gate:
  shows "gate 2 (J\<^sup>\<dagger>)"
proof
  show "dim_row (J\<^sup>\<dagger>) = 2\<^sup>2"
    using mat_of_cols_list_def by simp
  moreover show "square_mat (J\<^sup>\<dagger>)"
    using mat_of_cols_list_def by simp
  moreover have "(J\<^sup>\<dagger>)\<^sup>\<dagger> = J"
    using hermite_cnj_of_hermite_cnj by auto
  ultimately show "unitary (J\<^sup>\<dagger>)"
    using mat_of_cols_list_def unitary_def J_cnj_times_J J_times_J_cnj by auto
qed

lemma (in restricted_strategic_space) psi_f_is_state: 
  shows "state 2 \<psi>\<^sub>f"
proof-
  have "state 2 ((J\<^sup>\<dagger>) * \<psi>\<^sub>2)"
    using psi_two_is_state J_cnj_is_gate by auto
  then show ?thesis
    using psi_f by simp
qed

(* equation (1) in the paper *)
lemma (in restricted_strategic_space) equation_one:
  shows "(J\<^sup>\<dagger>) * ((U\<^sub>A \<Otimes> U\<^sub>B) * (J * |unit_vec 4 0\<rangle>)) = \<psi>\<^sub>f"
  using psi_one psi_two psi_f by auto

abbreviation (in restricted_strategic_space) prob00 :: "complex Matrix.mat \<Rightarrow> real" where
"prob00 v \<equiv> if state 2 v then (cmod (v $$ (0,0)))\<^sup>2 else undefined"

abbreviation (in restricted_strategic_space) prob01 :: "complex Matrix.mat \<Rightarrow> real" where
"prob01 v \<equiv> if state 2 v then (cmod (v $$ (1,0)))\<^sup>2 else undefined"

abbreviation (in restricted_strategic_space) prob10 :: "complex Matrix.mat \<Rightarrow> real" where
"prob10 v \<equiv> if state 2 v then (cmod (v $$ (2,0)))\<^sup>2 else undefined"

abbreviation (in restricted_strategic_space) prob11 :: "complex Matrix.mat \<Rightarrow> real" where
"prob11 v \<equiv> if state 2 v then (cmod (v $$ (3,0)))\<^sup>2 else undefined"

definition (in restricted_strategic_space) alice_payoff :: "real" where
"alice_payoff \<equiv> 3 * (prob00 \<psi>\<^sub>f) + 1 * (prob11 \<psi>\<^sub>f) + 0 * (prob01 \<psi>\<^sub>f) + 5 * (prob10 \<psi>\<^sub>f)"

definition (in restricted_strategic_space) bob_payoff :: "real" where
"bob_payoff \<equiv> 3 * (prob00 \<psi>\<^sub>f) + 1 * (prob11 \<psi>\<^sub>f) + 5 * (prob01 \<psi>\<^sub>f) + 0 * (prob10 \<psi>\<^sub>f)"

(* The variables represent values of \<gamma>, \<theta>\<^sub>A, \<phi>\<^sub>A, \<theta>\<^sub>B, \<phi>\<^sub>B respectively *)
definition (in restricted_strategic_space) alice_optimal :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
"alice_optimal c pa ta pb tb pay \<equiv> ((\<gamma> = c \<and> \<theta>\<^sub>A = ta \<and> \<phi>\<^sub>A = pa \<and> \<theta>\<^sub>B = tb \<and> \<phi>\<^sub>B = pb) \<longrightarrow> (alice_payoff = pay)) \<and>
                                   ((\<gamma> = c \<and> \<theta>\<^sub>B = tb \<and> \<phi>\<^sub>B = pb) \<longrightarrow> (alice_payoff \<le> pay))"

definition (in restricted_strategic_space) bob_optimal :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
"bob_optimal c pa ta pb tb pay \<equiv> ((\<gamma> = c \<and> \<theta>\<^sub>A = ta \<and> \<phi>\<^sub>A = pa \<and> \<theta>\<^sub>B = tb \<and> \<phi>\<^sub>B = pb) \<longrightarrow> (bob_payoff = pay)) \<and>
                                   ((\<gamma> = c \<and> \<theta>\<^sub>A = ta \<and> \<phi>\<^sub>A = pa) \<longrightarrow> (bob_payoff \<le> pay))"

definition (in restricted_strategic_space) is_nash_eq :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
"is_nash_eq c pa ta pb tb \<equiv> \<exists> p1 p2. alice_optimal c pa ta pb tb p1 \<and> bob_optimal c pa ta pb tb p2"

definition (in restricted_strategic_space) is_pareto_optimal :: 
"real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
"is_pareto_optimal c pa ta pb tb \<equiv> \<exists> p1 p2.
((\<gamma> = c \<and> \<theta>\<^sub>A = ta \<and> \<phi>\<^sub>A = pa \<and> \<theta>\<^sub>B = tb \<and> \<phi>\<^sub>B = pb) \<longrightarrow> (alice_payoff = p1 \<and> bob_payoff = p2)) \<and>
(\<gamma> = c) \<longrightarrow> ((alice_payoff > p1 \<longrightarrow> bob_payoff < p2) \<and> (bob_payoff > p2 \<longrightarrow> alice_payoff < p1))"

lemma (in restricted_strategic_space) sum_of_prob:
  fixes v :: "complex Matrix.mat"
  assumes "state 2 v"
  shows "(prob00 v) + (prob11 v) + (prob01 v) + (prob10 v) = 1"
proof-
  have "(prob00 v) + (prob11 v) + (prob01 v) + (prob10 v) = 
        (cmod (v $$ (0,0)))\<^sup>2 + (cmod (v $$ (1,0)))\<^sup>2 + (cmod (v $$ (2,0)))\<^sup>2 + (cmod (v $$ (3,0)))\<^sup>2"
    using assms by auto
  then show ?thesis
    using state_def assms cpx_vec_length_def by (auto simp add: set_4_lessThan)
qed

lemma (in restricted_strategic_space) sum_payoff_le_6:
  shows "alice_payoff + bob_payoff \<le> 6"
proof-
  have "alice_payoff + bob_payoff = 6 * (prob00 \<psi>\<^sub>f) + 2 * (prob11 \<psi>\<^sub>f) + 5 * (prob01 \<psi>\<^sub>f) + 5 * (prob10 \<psi>\<^sub>f)"
    using alice_payoff_def bob_payoff_def psi_f_is_state by auto
  then have "alice_payoff + bob_payoff \<le> 6 * ((prob00 \<psi>\<^sub>f) + (prob11 \<psi>\<^sub>f) + (prob01 \<psi>\<^sub>f) + (prob10 \<psi>\<^sub>f))"
    using psi_f_is_state by (auto simp add: algebra_simps)
  moreover have "(prob00 \<psi>\<^sub>f) + (prob11 \<psi>\<^sub>f) + (prob01 \<psi>\<^sub>f) + (prob10 \<psi>\<^sub>f) = 1"
    using sum_of_prob[of "\<psi>\<^sub>f"] psi_f_is_state by auto
  ultimately show ?thesis
    by auto
qed

lemma (in restricted_strategic_space) cooperate_is_pareto_optimal:
  fixes c pa ta pb tb :: real
  assumes "((\<gamma> = c \<and> \<theta>\<^sub>A = ta \<and> \<phi>\<^sub>A = pa \<and> \<theta>\<^sub>B = tb \<and> \<phi>\<^sub>B = pb) \<longrightarrow> (alice_payoff = 3 \<and> bob_payoff = 3))"
  shows "is_pareto_optimal c pa ta pb tb"
proof-
  have "(alice_payoff > 3 \<longrightarrow> bob_payoff < 3) \<and> (bob_payoff > 3 \<longrightarrow> alice_payoff < 3)"
    using sum_payoff_le_6 by auto
  then show ?thesis
    using assms is_pareto_optimal_def by auto
qed


section \<open>The Separable Case\<close>

lemma (in restricted_strategic_space) separable_case_CC: (* both player defect *)
  assumes "\<gamma> = 0"
  shows "\<phi>\<^sub>A = 0 \<and> \<theta>\<^sub>A = 0 \<and> \<phi>\<^sub>B = 0 \<and> \<theta>\<^sub>B = 0 \<longrightarrow> alice_payoff = 3 \<and> bob_payoff = 3"
  using alice_payoff_def bob_payoff_def cos_sin_squared_add_cpx psi_f_is_state by auto

lemma (in restricted_strategic_space) separable_case_DD: (* both player defect *)
  assumes "\<gamma> = 0"
  shows "\<phi>\<^sub>A = 0 \<and> \<theta>\<^sub>A = pi \<and> \<phi>\<^sub>B = 0 \<and> \<theta>\<^sub>B = pi \<longrightarrow> alice_payoff = 1 \<and> bob_payoff = 1"
  using alice_payoff_def bob_payoff_def cos_sin_squared_add_cpx psi_f_is_state by auto

lemma sin_squared_le_one:
  fixes x:: real
  shows "(sin x)\<^sup>2 \<le> 1"
  using abs_sin_le_one abs_square_le_1 by blast

lemma cos_squared_le_one:
  fixes x:: real
  shows "(cos x)\<^sup>2 \<le> 1"
  using abs_cos_le_one abs_square_le_1 by blast

lemma (in restricted_strategic_space) separable_alice_payoff_D\<^sub>B: 
(* Alice's payoff in the separable case given that Bob defects *)
  assumes "\<gamma> = 0" and "\<phi>\<^sub>B = 0 \<and> \<theta>\<^sub>B = pi"
  shows "alice_payoff \<le> 1"
  using alice_payoff_def assms sin_squared_le_one psi_f_is_state by auto

lemma (in restricted_strategic_space) separable_bob_payoff_D\<^sub>A:
(* Bob's payoff in the separable case given that Alice defects *)
  assumes "\<gamma> = 0" and "\<phi>\<^sub>A = 0 \<and> \<theta>\<^sub>A = pi"
  shows "bob_payoff \<le> 1"
  using bob_payoff_def assms sin_squared_le_one psi_f_is_state by auto

lemma (in restricted_strategic_space) separable_alice_optimal:
  shows "alice_optimal 0 0 pi 0 pi 1"
proof-
  have "\<gamma> = 0 \<and> \<theta>\<^sub>A = pi \<and> \<phi>\<^sub>A = 0 \<and> \<theta>\<^sub>B = pi \<and> \<phi>\<^sub>B = 0 \<longrightarrow> alice_payoff = 1"
    using separable_case_DD by simp
  moreover have "\<gamma> = 0 \<and> \<theta>\<^sub>B = pi \<and> \<phi>\<^sub>B = 0 \<longrightarrow> alice_payoff \<le> 1"
    using separable_alice_payoff_D\<^sub>B by simp
  ultimately show ?thesis
    using alice_optimal_def by simp
qed

lemma (in restricted_strategic_space) separable_bob_optimal:
  shows "bob_optimal 0 0 pi 0 pi 1"
proof-
  have "\<gamma> = 0 \<and> \<theta>\<^sub>A = pi \<and> \<phi>\<^sub>A = 0 \<and> \<theta>\<^sub>B = pi \<and> \<phi>\<^sub>B = 0 \<longrightarrow> bob_payoff = 1"
    using separable_case_DD by simp
  moreover have "\<gamma> = 0 \<and> \<theta>\<^sub>A = pi \<and> \<phi>\<^sub>A = 0 \<longrightarrow> bob_payoff \<le> 1"
    using separable_bob_payoff_D\<^sub>A by simp
  ultimately show ?thesis
    using bob_optimal_def by simp
qed

lemma (in restricted_strategic_space) separable_case_DD_is_nash_eq:
  shows "is_nash_eq 0 0 pi 0 pi"
  using separable_alice_optimal separable_bob_optimal is_nash_eq_def by auto

lemma (in restricted_strategic_space) separable_case_CC_is_pareto_optimal:
  shows "is_pareto_optimal 0 0 0 0 0"
  using cooperate_is_pareto_optimal separable_case_CC by auto


section \<open>The Maximally Entangled Case\<close>

lemma exp_of_half_pi: 
  fixes x:: real
  assumes "x = pi/2"
  shows "exp (\<i> * complex_of_real x) = \<i>"
  using assms cis_conv_exp cis_pi_half by fastforce

lemma exp_of_minus_half_pi: 
  fixes x:: real
  assumes "x = pi/2"
  shows "exp (-(\<i> * complex_of_real x)) = -\<i>"
  using assms cis_conv_exp cis_minus_pi_half by fastforce

lemma sin_of_quarter_pi:
  fixes x:: real
  assumes "x = pi/2"
  shows "sin (x/2) = (sqrt 2)/2"
  by (auto simp add: assms sin_45)

lemma cos_of_quarter_pi:
  fixes x:: real
  assumes "x = pi/2"
  shows "cos (x/2) = (sqrt 2)/2"
  by (auto simp add: assms cos_45)

lemma exp_of_real:
  fixes x:: real
  shows "exp (\<i> * x) = cos x + \<i> * (sin x)"
proof
  show "Re (exp (\<i> * x)) = Re ((cos x) + \<i> * (sin x))"
    using Re_exp by simp
  show "Im (exp (\<i> * x)) = Im ((cos x) + \<i> * (sin x))"
    using Im_exp by simp
qed

lemma exp_of_real_inv:
  fixes x:: real
  shows "exp (-(\<i> * x)) = cos x - \<i> * (sin x)"
proof
  show "Re (exp (-(\<i> * x))) = Re ((cos x) - \<i> * (sin x))"
    using Re_exp by simp
  show "Im (exp (-(\<i> * x))) = Im ((cos x) - \<i> * (sin x))"
    using Im_exp by simp
qed

lemma exp_to_sin:
  fixes x:: real
  shows "exp (\<i> * x) - exp (-(\<i> * x)) = 2 * \<i> * (sin x)"
  using exp_of_real exp_of_real_inv by simp

lemma exp_to_cos:
  fixes x:: real
  shows "exp (\<i> * x) + exp (-(\<i> * x)) = 2 * (cos x)"
  using exp_of_real exp_of_real_inv by simp

lemma cmod_real_prod_squared: 
  fixes x y:: real
  shows "(cmod (complex_of_real x * complex_of_real y))\<^sup>2 = x\<^sup>2 * y\<^sup>2"
  by (simp add: norm_mult power_mult_distrib)

lemma quantum_payoff_simp:
  fixes x y:: real
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

lemma quantum_payoff_le_3: 
  fixes x y:: real
  shows "2 * (sin x)\<^sup>2 * (cos y)\<^sup>2 + (cos y)\<^sup>2 \<le> 3"
proof-
  have "(sin x)\<^sup>2 * (cos y)\<^sup>2 \<le> 1" by (simp add: sin_squared_le_one cos_squared_le_one mult_le_one)
  then have "2 * (sin x)\<^sup>2 * (cos y)\<^sup>2 \<le> 2" by simp
  moreover have "(cos y)\<^sup>2 \<le> 1" 
    using cos_squared_le_one[of "y"] by simp
  ultimately show ?thesis by simp
qed

lemma sqrt_two_squared_cpx: "complex_of_real (sqrt 2) * complex_of_real (sqrt 2) = 2"
  by (metis dbl_def dbl_simps(5) mult_2_right of_real_mult of_real_numeral real_sqrt_four real_sqrt_mult)

lemma hidden_sqrt_two_squared_cpx: "complex_of_real (sqrt 2) * (complex_of_real (sqrt 2) * x) / 4 = x/2"
  using sqrt_two_squared_cpx by (auto simp add: algebra_simps)

lemma (in restricted_strategic_space) max_entangled_DD:
(* both players defects in the maximally entangled case *)
  assumes "\<gamma> = pi/2"
  shows "\<phi>\<^sub>A = 0 \<and> \<theta>\<^sub>A = pi \<and> \<phi>\<^sub>B = 0 \<and> \<theta>\<^sub>B = pi \<longrightarrow> alice_payoff = 1 \<and> bob_payoff = 1"
  using alice_payoff_def bob_payoff_def cos_sin_squared_add_cpx psi_f_is_state
  by auto

lemma (in restricted_strategic_space) max_entangled_QQ:
(* both players play the move Q in the maximally entangled case *)
  assumes "\<gamma> = pi/2"
  shows "\<phi>\<^sub>A = pi/2 \<and> \<theta>\<^sub>A = 0 \<and> \<phi>\<^sub>B = pi/2 \<and> \<theta>\<^sub>B = 0 \<longrightarrow> alice_payoff = 3 \<and> bob_payoff = 3"
  using alice_payoff_def bob_payoff_def sin_cos_squared_add_cpx exp_of_half_pi exp_of_minus_half_pi psi_f_is_state
  by auto

lemma (in restricted_strategic_space) max_entangled_DQ:
(* Alice defects, and Bob plays the move Q in the maximally entangled case *)
  assumes "\<gamma> = pi/2"
  shows "\<phi>\<^sub>A = 0 \<and> \<theta>\<^sub>A = pi \<and> \<phi>\<^sub>B = pi/2 \<and> \<theta>\<^sub>B = 0 \<longrightarrow> alice_payoff = 0 \<and> bob_payoff = 5"
  using alice_payoff_def bob_payoff_def cos_sin_squared_add_cpx exp_of_half_pi exp_of_minus_half_pi 
        psi_f_is_state sqrt_two_squared_cpx
  by (auto simp add: assms algebra_simps sin_45 cos_45)

lemma (in restricted_strategic_space) max_entangled_alice_payoff_Q\<^sub>B:
(* Alice's payoff in the maximally entangled case given that Bob plays the move Q *)
  assumes "\<gamma> = pi/2"
  shows "\<phi>\<^sub>B = pi/2 \<and> \<theta>\<^sub>B = 0 \<longrightarrow> alice_payoff \<le> 3"
proof
  assume asm:"\<phi>\<^sub>B = pi/2 \<and> \<theta>\<^sub>B = 0"
  have "\<psi>\<^sub>f $$ (0,0) = -(sin \<phi>\<^sub>A) * (cos (\<theta>\<^sub>A/2))"
  proof-
    have "\<psi>\<^sub>f $$ (0,0) = \<i> * (sqrt 2/2) * (sqrt 2/2) * (cos (\<theta>\<^sub>A/2)) * exp (\<i> * \<phi>\<^sub>A) +
                        \<i> * (sqrt 2/2) * (sqrt 2/2) * (cos (\<theta>\<^sub>A/2)) * -exp (-(\<i> * \<phi>\<^sub>A))"
      using mat_of_cols_list_def asm assms exp_of_half_pi exp_of_minus_half_pi
      by (auto simp add: sin_of_quarter_pi[of "\<gamma>"] cos_of_quarter_pi[of "\<gamma>"] algebra_simps)
    then have "\<psi>\<^sub>f $$ (0,0) = \<i> * (sqrt 2/2) * (sqrt 2/2) * (cos (\<theta>\<^sub>A/2)) * (exp (\<i> * \<phi>\<^sub>A) - exp (-(\<i> * \<phi>\<^sub>A)))"
      by (auto simp add: algebra_simps)
    then have "\<psi>\<^sub>f $$ (0,0) = \<i> * (cos (\<theta>\<^sub>A/2)) * (1/2) * (exp (\<i> * \<phi>\<^sub>A) - exp (-(\<i> * \<phi>\<^sub>A)))"
      using sqrt_two_squared_cpx by (auto simp add: algebra_simps)
    then show ?thesis
      using exp_to_sin by (simp add: algebra_simps)
  qed
  moreover have "\<psi>\<^sub>f $$ (1,0) = sin (\<theta>\<^sub>A/2)"
    using mat_of_cols_list_def asm assms exp_of_half_pi exp_of_minus_half_pi sqrt_two_squared_cpx
    by (auto simp add: sin_of_quarter_pi[of "\<gamma>"] cos_of_quarter_pi[of "\<gamma>"])
  moreover have "\<psi>\<^sub>f $$ (2,0) = 0"
    using mat_of_cols_list_def asm assms exp_of_half_pi exp_of_minus_half_pi sqrt_two_squared_cpx
    by (auto simp add: sin_of_quarter_pi[of "\<gamma>"] cos_of_quarter_pi[of "\<gamma>"] algebra_simps)
  moreover have "\<psi>\<^sub>f $$ (3,0) = (cos \<phi>\<^sub>A) * (cos (\<theta>\<^sub>A/2))"
  proof-
    have "\<psi>\<^sub>f $$ (3,0) = exp (\<i> * \<phi>\<^sub>A) * (cos (\<theta>\<^sub>A/2)) * (sqrt 2/2) * (sqrt 2/2) +
                        exp (- (\<i> * \<phi>\<^sub>A)) * (cos (\<theta>\<^sub>A/2)) * (sqrt 2/2) * (sqrt 2/2)"
      using mat_of_cols_list_def asm assms exp_of_half_pi exp_of_minus_half_pi
      by (auto simp add: sin_of_quarter_pi[of "\<gamma>"] cos_of_quarter_pi[of "\<gamma>"] algebra_simps)
    then have "\<psi>\<^sub>f $$ (3,0) = (exp (\<i> * \<phi>\<^sub>A) + exp (-(\<i> * \<phi>\<^sub>A))) * (cos (\<theta>\<^sub>A/2)) * (sqrt 2/2) * (sqrt 2/2)"
      by (auto simp add: algebra_simps)
    then have "\<psi>\<^sub>f $$ (3,0) = (exp (\<i> * \<phi>\<^sub>A) + exp (-(\<i> * \<phi>\<^sub>A))) * (cos (\<theta>\<^sub>A/2)) * (1/2)"
      using sqrt_two_squared_cpx hidden_sqrt_two_squared_cpx by (auto simp add: algebra_simps)
    then show ?thesis
      using exp_to_cos by (simp add: algebra_simps)
  qed
  ultimately show "alice_payoff \<le> 3"
  using alice_payoff_def psi_f_is_state quantum_payoff_simp quantum_payoff_le_3 
  by auto
qed

lemma (in restricted_strategic_space) max_entangled_bob_payoff_Q\<^sub>A:
(* Bob's payoff in the maximally entangled case given that Alice plays the move Q *)
  assumes "\<gamma> = pi/2"
  shows "\<phi>\<^sub>A = pi/2 \<and> \<theta>\<^sub>A = 0 \<longrightarrow> bob_payoff \<le> 3"
proof
  assume asm:"\<phi>\<^sub>A = pi/2 \<and> \<theta>\<^sub>A = 0"
  have "\<psi>\<^sub>f $$ (0,0) = -(sin \<phi>\<^sub>B) * (cos (\<theta>\<^sub>B/2))"
  proof-
    have "\<psi>\<^sub>f $$ (0,0) = \<i> * (sqrt 2/2) * (sqrt 2/2) * (cos (\<theta>\<^sub>B/2)) * exp (\<i> * \<phi>\<^sub>B) +
                        \<i> * (sqrt 2/2) * (sqrt 2/2) * (cos (\<theta>\<^sub>B/2)) * -exp (-(\<i> * \<phi>\<^sub>B))"
      using mat_of_cols_list_def asm assms exp_of_half_pi exp_of_minus_half_pi
      by (auto simp add: sin_of_quarter_pi[of "\<gamma>"] cos_of_quarter_pi[of "\<gamma>"] algebra_simps)
    then have "\<psi>\<^sub>f $$ (0,0) = \<i> * (sqrt 2/2) * (sqrt 2/2) * (cos (\<theta>\<^sub>B/2)) * (exp (\<i> * \<phi>\<^sub>B) - exp (-(\<i> * \<phi>\<^sub>B)))"
      by (auto simp add: algebra_simps)
    then have "\<psi>\<^sub>f $$ (0,0) = \<i> * (cos (\<theta>\<^sub>B/2)) * (1/2) * (exp (\<i> * \<phi>\<^sub>B) - exp (-(\<i> * \<phi>\<^sub>B)))"
      using sqrt_two_squared_cpx by (auto simp add: algebra_simps)
    then show ?thesis
      using exp_to_sin by (simp add: algebra_simps)
  qed
  moreover have "\<psi>\<^sub>f $$ (1,0) = 0"
    using mat_of_cols_list_def asm assms exp_of_half_pi exp_of_minus_half_pi sqrt_two_squared_cpx
    by (auto simp add: sin_of_quarter_pi[of "\<gamma>"] cos_of_quarter_pi[of "\<gamma>"] algebra_simps)
  moreover have "\<psi>\<^sub>f $$ (2,0) = sin (\<theta>\<^sub>B/2)"
    using mat_of_cols_list_def asm assms exp_of_half_pi exp_of_minus_half_pi sqrt_two_squared_cpx
    by (auto simp add: sin_of_quarter_pi[of "\<gamma>"] cos_of_quarter_pi[of "\<gamma>"] algebra_simps)
  moreover have "\<psi>\<^sub>f $$ (3,0) = (cos \<phi>\<^sub>B) * (cos (\<theta>\<^sub>B/2))"
  proof-
    have "\<psi>\<^sub>f $$ (3,0) = exp (\<i> * \<phi>\<^sub>B) * (cos (\<theta>\<^sub>B/2)) * (sqrt 2/2) * (sqrt 2/2) +
                        exp (- (\<i> * \<phi>\<^sub>B)) * (cos (\<theta>\<^sub>B/2)) * (sqrt 2/2) * (sqrt 2/2)"
      using mat_of_cols_list_def asm assms exp_of_half_pi exp_of_minus_half_pi
      by (auto simp add: sin_of_quarter_pi[of "\<gamma>"] cos_of_quarter_pi[of "\<gamma>"] algebra_simps)
    then have "\<psi>\<^sub>f $$ (3,0) = (exp (\<i> * \<phi>\<^sub>B) + exp (-(\<i> * \<phi>\<^sub>B))) * (cos (\<theta>\<^sub>B/2)) * (sqrt 2/2) * (sqrt 2/2)"
      by (auto simp add: algebra_simps)
    then have "\<psi>\<^sub>f $$ (3,0) = (exp (\<i> * \<phi>\<^sub>B) + exp (-(\<i> * \<phi>\<^sub>B))) * (cos (\<theta>\<^sub>B/2)) * (1/2)"
      using sqrt_two_squared_cpx hidden_sqrt_two_squared_cpx by (auto simp add: algebra_simps)
    then show ?thesis
      using exp_to_cos by (simp add: algebra_simps)
  qed
  ultimately show "bob_payoff \<le> 3"
  using bob_payoff_def psi_f_is_state quantum_payoff_simp quantum_payoff_le_3 
  by auto
qed

lemma (in restricted_strategic_space) max_entangled_DD_is_not_nash_eq:
  shows "\<not>is_nash_eq (pi/2) 0 pi 0 pi"
proof
  assume "is_nash_eq (pi/2) 0 pi 0 pi"
  then have "\<exists>p2. bob_optimal (pi/2) 0 pi 0 pi p2"
    using is_nash_eq_def by auto
  then obtain p2 where "bob_optimal (pi/2) 0 pi 0 pi p2"
    by blast
  then have f0:"(\<gamma> = (pi/2) \<and> \<theta>\<^sub>A = pi \<and> \<phi>\<^sub>A = 0 \<and> \<theta>\<^sub>B = pi \<and> \<phi>\<^sub>B = 0 \<longrightarrow> bob_payoff = p2) \<and>
                (\<gamma> = (pi/2) \<and> \<theta>\<^sub>A = pi \<and> \<phi>\<^sub>A = 0 \<longrightarrow> bob_payoff \<le> p2)"
    using bob_optimal_def by auto
  then have "\<gamma> = (pi/2) \<and> \<theta>\<^sub>A = pi \<and> \<phi>\<^sub>A = 0 \<and> \<theta>\<^sub>B = pi \<and> \<phi>\<^sub>B = 0 \<longrightarrow> p2 = 1"
    using max_entangled_DD by auto
  then have "\<gamma> = (pi/2) \<and> \<theta>\<^sub>A = pi \<and> \<phi>\<^sub>A = 0 \<longrightarrow> bob_payoff \<le> 1"
    using f0 sorry
  show False
    sorry
qed

lemma (in restricted_strategic_space) max_entangled_alice_optimal:
  shows "alice_optimal (pi/2) (pi/2) 0 (pi/2) 0 3"
proof-
  have "\<gamma> = (pi/2) \<and> \<theta>\<^sub>A = 0 \<and> \<phi>\<^sub>A = (pi/2) \<and> \<theta>\<^sub>B = 0 \<and> \<phi>\<^sub>B = (pi/2) \<longrightarrow> alice_payoff = 3"
    using max_entangled_QQ by simp
  moreover have "\<gamma> = (pi/2) \<and> \<theta>\<^sub>B = 0 \<and> \<phi>\<^sub>B = (pi/2) \<longrightarrow> alice_payoff \<le> 3"
    using max_entangled_alice_payoff_Q\<^sub>B by simp
  ultimately show ?thesis
    using alice_optimal_def[of "(pi/2)" "(pi/2)" "0" "(pi/2)" "0" "3"] by auto
qed

lemma (in restricted_strategic_space) max_entangled_bob_optimal:
  shows "bob_optimal (pi/2) (pi/2) 0 (pi/2) 0 3"
proof-
  have "\<gamma> = (pi/2) \<and> \<theta>\<^sub>A = 0 \<and> \<phi>\<^sub>A = (pi/2) \<and> \<theta>\<^sub>B = 0 \<and> \<phi>\<^sub>B = (pi/2) \<longrightarrow> bob_payoff = 3"
    using max_entangled_QQ by simp
  moreover have "\<gamma> = (pi/2) \<and> \<theta>\<^sub>A = 0 \<and> \<phi>\<^sub>A = (pi/2) \<longrightarrow> bob_payoff \<le> 3"
    using max_entangled_bob_payoff_Q\<^sub>A by simp
  ultimately show ?thesis
    using bob_optimal_def[of "(pi/2)" "(pi/2)" "0" "(pi/2)" "0" "3"] by auto
qed

lemma (in restricted_strategic_space) max_entangled_QQ_is_nash_eq:
  shows "is_nash_eq (pi/2) (pi/2) 0 (pi/2) 0"
  using max_entangled_alice_optimal max_entangled_bob_optimal is_nash_eq_def by auto

lemma (in restricted_strategic_space) max_entangled_QQ_is_pareto_optimal:
  shows "is_pareto_optimal (pi/2) (pi/2) 0 (pi/2) 0"
  using cooperate_is_pareto_optimal[of "(pi/2)" "0" "(pi/2)" "0" "(pi/2)"] max_entangled_QQ by auto


section \<open>The Unfair Strategy Case\<close>

lemma half_sqrt_two_squared: "2 * (sqrt 2 / 2)\<^sup>2 = 1"
  by (auto simp add: power2_eq_square)

lemma (in restricted_strategic_space) max_entangled_MD:
(* Alice plays the "miracle move", and Bob plays the classical defect move in the maximally entangled case *)
  assumes "\<gamma> = pi/2"
  shows "\<phi>\<^sub>A = pi/2 \<and> \<theta>\<^sub>A = pi/2 \<and> \<phi>\<^sub>B = 0 \<and> \<theta>\<^sub>B = pi \<longrightarrow> alice_payoff = 3 \<and> bob_payoff = 1/2"
proof
  assume asm:"\<phi>\<^sub>A = pi/2 \<and> \<theta>\<^sub>A = pi/2 \<and> \<phi>\<^sub>B = 0 \<and> \<theta>\<^sub>B = pi"
  show "alice_payoff = 3 \<and> bob_payoff = 1/2"
    using alice_payoff_def bob_payoff_def sqrt_two_squared_cpx half_sqrt_two_squared
          exp_of_half_pi[of "pi/2"] exp_of_minus_half_pi[of "pi/2"] psi_f_is_state
    by (auto simp add: asm assms sin_45 cos_45 algebra_simps)
qed

lemma (in restricted_strategic_space) max_entangled_MC:
(* Alice plays the "miracle move", and Bob plays the classical defect move in the maximally entangled case *)
  assumes "\<gamma> = pi/2"
  shows "\<phi>\<^sub>A = pi/2 \<and> \<theta>\<^sub>A = pi/2 \<and> \<phi>\<^sub>B = 0 \<and> \<theta>\<^sub>B = 0 \<longrightarrow> alice_payoff = 3 \<and> bob_payoff = 1/2"
proof
  assume asm:"\<phi>\<^sub>A = pi/2 \<and> \<theta>\<^sub>A = pi/2 \<and> \<phi>\<^sub>B = 0 \<and> \<theta>\<^sub>B = 0"
  show "alice_payoff = 3 \<and> bob_payoff = 1/2"
    using alice_payoff_def bob_payoff_def sqrt_two_squared_cpx half_sqrt_two_squared
          exp_of_half_pi[of "pi/2"] exp_of_minus_half_pi[of "pi/2"] psi_f_is_state
    by (auto simp add: asm assms sin_45 cos_45 algebra_simps)
qed

lemma (in restricted_strategic_space) max_entangled_MH:
(* Alice plays the "miracle move", and Bob plays the classical half move in the maximally entangled case *)
  assumes "\<gamma> = pi/2"
  shows "\<phi>\<^sub>A = pi/2 \<and> \<theta>\<^sub>A = pi/2 \<and> \<phi>\<^sub>B = 0 \<and> \<theta>\<^sub>B = pi/2 \<longrightarrow> alice_payoff = 1 \<and> bob_payoff = 1"
proof
  assume asm:"\<phi>\<^sub>A = pi/2 \<and> \<theta>\<^sub>A = pi/2 \<and> \<phi>\<^sub>B = 0 \<and> \<theta>\<^sub>B = pi/2"
  show "alice_payoff = 1 \<and> bob_payoff = 1"
    using alice_payoff_def bob_payoff_def sqrt_two_squared_cpx half_sqrt_two_squared
          exp_of_half_pi[of "pi/2"] exp_of_minus_half_pi[of "pi/2"] psi_f_is_state
    by (auto simp add: asm assms sin_45 cos_45 algebra_simps)
qed

(* This is the definition of M in equation (9) *)
abbreviation M :: "complex Matrix.mat" where
"M \<equiv> mat_of_cols_list 2 [[\<i> * sqrt(2)/2, -1 * sqrt(2)/2],
                          [1 * sqrt(2)/2, -\<i> * sqrt(2)/2]]"

lemma (in restricted_strategic_space) M_correct:
  assumes "\<phi>\<^sub>A = pi/2 \<and> \<theta>\<^sub>A = pi/2"
  shows "U\<^sub>A = M"
proof
  show "dim_row U\<^sub>A = dim_row M" using mat_of_cols_list_def by simp
  show "dim_col U\<^sub>A = dim_col M" using mat_of_cols_list_def by simp
  fix i j assume a0:"i < dim_row M" and a1:"j < dim_col M"
  then show "U\<^sub>A $$ (i,j) = M $$ (i,j)"
  proof-
    have "i\<in>{0,1} \<and> j\<in>{0,1}" 
      using a0 a1 mat_of_cols_list_def by auto
    thus ?thesis
      using mat_of_cols_list_def exp_of_half_pi[of "pi/2"] exp_of_minus_half_pi[of "pi/2"]
      by (auto simp add: assms sin_45 cos_45)
  qed
qed

lemma hidden_sqrt_two_squared_cpx2:
  fixes x y :: complex
  shows "(sqrt 2) * ((sqrt 2) * (x * y)) / 2 = x * y"
  using sqrt_two_squared_cpx by auto

lemma (in restricted_strategic_space) unfair_strategy_no_benefit:
(* Two players' payoffs in the maximally entangled case given that Alice plays a quantum move and Bob 
plays a classical move with the same \<theta> *)
  assumes "\<gamma> = pi/2"
  shows "\<phi>\<^sub>A = pi/2 \<and> \<phi>\<^sub>B = 0 \<and> \<theta>\<^sub>A = \<theta>\<^sub>B \<longrightarrow> alice_payoff = 1 \<and> bob_payoff = 1"
proof
  assume asm:"\<phi>\<^sub>A = pi/2 \<and> \<phi>\<^sub>B = 0 \<and> \<theta>\<^sub>A = \<theta>\<^sub>B"
  have "\<psi>\<^sub>f $$ (0,0) = 0"
    using exp_of_half_pi[of "pi/2"] exp_of_minus_half_pi[of "pi/2"]
    by (auto simp add: asm assms sin_45 cos_45 algebra_simps)
  moreover have "\<psi>\<^sub>f $$ (1,0) = 0"
    using exp_of_half_pi[of "pi/2"] exp_of_minus_half_pi[of "pi/2"]
    by (auto simp add: asm assms sin_45 cos_45 algebra_simps)
  moreover have "\<psi>\<^sub>f $$ (2,0) = 0"
    using exp_of_half_pi[of "pi/2"] exp_of_minus_half_pi[of "pi/2"]
    by (auto simp add: asm assms sin_45 cos_45 hidden_sqrt_two_squared_cpx2 algebra_simps)
  moreover have "\<psi>\<^sub>f $$ (3,0) = 1"
    using exp_of_half_pi[of "pi/2"] exp_of_minus_half_pi[of "pi/2"] cos_sin_squared_add_cpx
    by (auto simp add: asm assms sin_45 cos_45 hidden_sqrt_two_squared_cpx2 algebra_simps)
  ultimately show "alice_payoff = 1 \<and> bob_payoff = 1"
    using alice_payoff_def bob_payoff_def psi_f_is_state
    by auto
qed

(* The lemmas in the comments are not true *)
(* lemma (in restricted_strategic_space) unfair_strategy_alice_payoff: 
"3 \<le> (cos (\<theta>\<^sub>B/2 - pi/4))\<^sup>2 + 5 * (sin (\<theta>\<^sub>B/2 - pi/4))\<^sup>2"
  sorry

lemma (in restricted_strategic_space) unfair_strategy_bob_payoff: 
"(cos (\<theta>\<^sub>B/2 - pi/4))\<^sup>2 * 2 \<le> 1"
  sorry

lemma unfair_strategy_vec_is_state:"state 2 (Matrix.mat 4 (Suc 0) (\<lambda>(i,j).
[[0, 0, complex_of_real (sin (\<theta>\<^sub>B/2 - pi/4)), complex_of_real (cos (\<theta>\<^sub>B/2 - pi/4))]] ! j ! i))"
  using state_def cpx_vec_length_def by (auto simp add: set_4_lessThan)

lemma (in restricted_strategic_space) unfair_strategy_payoff_M\<^sub>A:
(* Two players' payoffs in the maximally entangled case given that Alice plays the "miracle move" and Bob 
only plays classical strategies*)
  assumes "\<gamma> = pi/2"
  shows "\<phi>\<^sub>A = pi/2 \<and> \<theta>\<^sub>A = pi/2 \<and> \<phi>\<^sub>B = 0 \<longrightarrow> alice_payoff \<ge> 3 \<and> bob_payoff \<le> 1/2"
proof
  assume asm:"\<phi>\<^sub>A = pi/2 \<and> \<theta>\<^sub>A = pi/2 \<and> \<phi>\<^sub>B = 0"
  have "\<psi>\<^sub>f $$ (0,0) = 0"
    using exp_of_half_pi[of "pi/2"] exp_of_minus_half_pi[of "pi/2"]
    by (auto simp add: asm assms sin_45 cos_45 algebra_simps)
  moreover have "\<psi>\<^sub>f $$ (1,0) = 0"
    using exp_of_half_pi[of "pi/2"] exp_of_minus_half_pi[of "pi/2"]
    by (auto simp add: asm assms sin_45 cos_45 algebra_simps)
  moreover have "\<psi>\<^sub>f $$ (2,0) = sin(\<theta>\<^sub>B/2 - pi/4)"
  proof-
    have "\<psi>\<^sub>f $$ (2,0) = cos(\<theta>\<^sub>A/2)*sin(\<theta>\<^sub>B/2) - sin(\<theta>\<^sub>A/2)*cos(\<theta>\<^sub>B/2)"
      using exp_of_half_pi[of "pi/2"] exp_of_minus_half_pi[of "pi/2"]
      by (auto simp add: asm assms sin_45 cos_45 hidden_sqrt_two_squared_cpx2 algebra_simps)
    then show ?thesis
      using sin_add[of "\<theta>\<^sub>B/2" "-\<theta>\<^sub>A/2"] sin_minus
      by (simp add: asm)
  qed
  moreover have "\<psi>\<^sub>f $$ (3,0) = cos(\<theta>\<^sub>B/2 - pi/4)"
  proof-
    have "\<psi>\<^sub>f $$ (3,0) = cos(\<theta>\<^sub>A/2)*cos(\<theta>\<^sub>B/2) + sin(\<theta>\<^sub>A/2)*sin(\<theta>\<^sub>B/2)"
      using exp_of_half_pi[of "pi/2"] exp_of_minus_half_pi[of "pi/2"]
      by (auto simp add: asm assms sin_45 cos_45 hidden_sqrt_two_squared_cpx2 algebra_simps)
    then show ?thesis
      using cos_add[of "\<theta>\<^sub>B/2" "-\<theta>\<^sub>A/2"] sin_minus
      by (simp add: asm)
  qed
  ultimately show "alice_payoff \<ge> 3 \<and> bob_payoff \<le> 1/2"
    using alice_payoff_def bob_payoff_def mat_of_cols_list_def unfair_strategy_vec_is_state
          unfair_strategy_alice_payoff unfair_strategy_bob_payoff
    by auto
qed *)


(*
Bibliography:

@ARTICLE{1999PhRvL..83.3077E,
   author = {{Eisert}, J. and {Wilkens}, M. and {Lewenstein}, M.},
    title = "{Quantum Games and Quantum Strategies}",
  journal = {Physical Review Letters},
   eprint = {quant-ph/9806088},
     year = 1999,
    month = oct,
   volume = 83,
    pages = {3077-3080},
      doi = {10.1103/PhysRevLett.83.3077},
   adsurl = {https://ui.adsabs.harvard.edu/abs/1999PhRvL..83.3077E},
  adsnote = {Provided by the SAO/NASA Astrophysics Data System}
}
*)

end