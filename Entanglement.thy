(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk, 

           with contributions from Yijun He, University of Cambridge, yh403@cam.ac.uk
*)

theory Entanglement
imports
  Main
  Jordan_Normal_Form.Matrix
  Quantum
  Tensor
begin


section\<open>Quantum Entanglement\<close>

subsection\<open>The Product States and Entangled States of a 2-qubits System\<close>

(* Here I added the condition that v, w \<in> state_qbit 1, otherwise u can always be represented by the
   tensor product of the 1-dimensional vector (1) and u itself *)

definition prod_state2 ::"complex Matrix.vec \<Rightarrow> bool" where
"prod_state2 u \<equiv> if u \<in> state_qbit 2 then \<exists>v \<in> state_qbit 1.\<exists>w \<in> state_qbit 1. u = v \<otimes> w else undefined"

definition entangled2 ::"complex Matrix.vec \<Rightarrow> bool" where
"entangled2 u \<equiv> \<not> prod_state2 u"

text\<open>The Bell states are entangled states\<close>

lemma tensor_prod_2:"mult.vec_vec_Tensor ( * ) [x1::complex,x2] [x3,x4] = [x1*x3,x1*x4,x2*x3,x2*x4]"
proof-
  have f0:"Matrix_Tensor.mult (1::complex) ( * )" 
  proof
    fix a::complex and b::complex and c::complex and x::complex
    show "a * b = b * a" by simp
    show "a * b * c = a * (b * c)" by simp
    show "1 * x = x" by simp
    show "x * 1 = x" by simp
  qed
  show "mult.vec_vec_Tensor ( * ) [x1::complex,x2] [x3,x4] = [x1*x3,x1*x4,x2*x3,x2*x4]"
    using mult.vec_vec_Tensor_def[of "(1::complex)" "( * )"] mult.times_def[of "(1::complex)" "( * )"]
  by(simp add: f0)
qed

lemma list_vec: 
  assumes "v \<in> state_qbit 1"
  shows "list_of_vec v = [v $ 0, v $ 1]"
proof-
  have a1:"Rep_vec v = (fst(Rep_vec v), snd(Rep_vec v))" 
    by auto
  have a2:"fst(Rep_vec v) = 2" 
    using state_qbit_def assms
    by(auto simp add: dim_vec.rep_eq)
  have a3:"Rep_vec v = (2, vec_index v)"
    using a1 a2 vec_index.rep_eq
    by(auto simp add: vec_index.rep_eq)
  have a4:"[0..<2::nat] = [0,1]"
    by(simp add: upt_rec) 
  show ?thesis
    using a3 a4
    by(auto simp add: list_of_vec_def)
qed

lemma vec_tensor_prod_2:
  assumes "v \<in> state_qbit 1" and "w \<in> state_qbit 1"
  shows "v \<otimes> w = vec_of_list [v $ 0 * w $ 0, v $ 0 * w $ 1, v $ 1 * w $ 0, v $ 1 * w $ 1]"
proof-
  have f1:"list_of_vec v = [v $ 0, v $ 1]"
    using list_vec assms
    by simp
  have f2:"list_of_vec w = [w $ 0, w $ 1]"
    using list_vec assms
    by simp
  show "v \<otimes> w = vec_of_list [v $ 0 * w $ 0, v $ 0 * w $ 1, v $ 1 * w $ 0, v $ 1 * w $ 1]"
    by(simp add: tensor_vec_def f1 f2 tensor_prod_2)
qed

lemma bell_00_is_entangled2:
  shows "entangled2 bell_00" 
proof-
  have "\<forall>v \<in> state_qbit 1. \<forall> w \<in> state_qbit 1. |\<beta>\<^sub>0\<^sub>0\<rangle> \<noteq> v \<otimes> w"
  proof-
    have "\<exists>v \<in> state_qbit 1. \<exists> w \<in> state_qbit 1. |\<beta>\<^sub>0\<^sub>0\<rangle> = v \<otimes> w \<Longrightarrow> False"
    proof-
      assume asm:"\<exists>v \<in> state_qbit 1. \<exists> w \<in> state_qbit 1. |\<beta>\<^sub>0\<^sub>0\<rangle> = v \<otimes> w"
      obtain v and w where a0:"v \<in> state_qbit 1" and a1:"w \<in> state_qbit 1" and a2:"|\<beta>\<^sub>0\<^sub>0\<rangle> = v \<otimes> w"
        using asm
        by blast
      have "|\<beta>\<^sub>0\<^sub>0\<rangle> $ 0 = (v \<otimes> w) $ 0"
        using a2
        by simp
      then have f1:"v $ 0 * w $ 0 = 1 / complex_of_real (sqrt 2)"
        using a0 a1
        by(auto simp add: vec_tensor_prod_2 mult.times.simps bell_00_def)
      have "|\<beta>\<^sub>0\<^sub>0\<rangle> $ 1 = (v \<otimes> w) $ 1"
        using a2
        by simp
      then have f2:"v $ 0 * w $ 1 = 0"
        using a0 a1
        by(auto simp add: vec_tensor_prod_2 mult.times.simps bell_00_def)
      have "|\<beta>\<^sub>0\<^sub>0\<rangle> $ 2 = (v \<otimes> w) $ 2"
        using a2
        by simp
      then have f3:"v $ 1 * w $ 0 = 0"
        using a0 a1
        by(auto simp add: vec_tensor_prod_2 mult.times.simps bell_00_def numeral_2_eq_2)
      have "|\<beta>\<^sub>0\<^sub>0\<rangle> $ 3 = (v \<otimes> w) $ 3"
        using a2
        by simp
      then have f4:"v $ 1 * w $ 1 = 1 / complex_of_real (sqrt 2)"
        using a0 a1
        by(auto simp add: vec_tensor_prod_2 mult.times.simps bell_00_def numeral_3_eq_3)
      have "1 / complex_of_real (sqrt 2) * 1 / complex_of_real (sqrt 2) = 0"
        using f1 f2 f3 f4
        by auto
      then show False
        by simp
    qed
    then show "\<forall>v \<in> state_qbit 1. \<forall> w \<in> state_qbit 1. |\<beta>\<^sub>0\<^sub>0\<rangle> \<noteq> v \<otimes> w"
      by blast
  qed
  then show ?thesis 
    by(simp add: entangled2_def prod_state2_def bell_00_is_state)
qed

lemma bell_01_is_entangled2:
  shows "entangled2 bell_01" 
proof-
  have "\<forall>v \<in> state_qbit 1. \<forall> w \<in> state_qbit 1. |\<beta>\<^sub>0\<^sub>1\<rangle> \<noteq> v \<otimes> w"
  proof-
    have "\<exists>v \<in> state_qbit 1. \<exists> w \<in> state_qbit 1. |\<beta>\<^sub>0\<^sub>1\<rangle> = v \<otimes> w \<Longrightarrow> False"
    proof-
      assume asm:"\<exists>v \<in> state_qbit 1. \<exists> w \<in> state_qbit 1. |\<beta>\<^sub>0\<^sub>1\<rangle> = v \<otimes> w"
      obtain v and w where a0:"v \<in> state_qbit 1" and a1:"w \<in> state_qbit 1" and a2:"|\<beta>\<^sub>0\<^sub>1\<rangle> = v \<otimes> w"
        using asm
        by blast
      have "|\<beta>\<^sub>0\<^sub>1\<rangle> $ 0 = (v \<otimes> w) $ 0"
        using a2
        by simp
      then have f1:"v $ 0 * w $ 0 = 0"
        using a0 a1
        by(auto simp add: vec_tensor_prod_2 mult.times.simps bell_01_def)
      have "|\<beta>\<^sub>0\<^sub>1\<rangle> $ 1 = (v \<otimes> w) $ 1"
        using a2
        by simp
      then have f2:"v $ 0 * w $ 1 = 1 / complex_of_real (sqrt 2)"
        using a0 a1
        by(auto simp add: vec_tensor_prod_2 mult.times.simps bell_01_def)
      have "|\<beta>\<^sub>0\<^sub>1\<rangle> $ 2 = (v \<otimes> w) $ 2"
        using a2
        by simp
      then have f3:"v $ 1 * w $ 0 = 1 / complex_of_real (sqrt 2)"
        using a0 a1
        by(auto simp add: vec_tensor_prod_2 mult.times.simps bell_01_def numeral_2_eq_2)
      have "|\<beta>\<^sub>0\<^sub>1\<rangle> $ 3 = (v \<otimes> w) $ 3"
        using a2
        by simp
      then have f4:"v $ 1 * w $ 1 = 0"
        using a0 a1
        by(auto simp add: vec_tensor_prod_2 mult.times.simps bell_01_def numeral_3_eq_3)
      have "1 / complex_of_real (sqrt 2) * 1 / complex_of_real (sqrt 2) = 0"
        using f1 f2 f3 f4
        by auto
      then show False
        by simp
    qed
    then show "\<forall>v \<in> state_qbit 1. \<forall> w \<in> state_qbit 1. |\<beta>\<^sub>0\<^sub>1\<rangle> \<noteq> v \<otimes> w"
      by blast
  qed
  then show ?thesis 
    by(simp add: entangled2_def prod_state2_def bell_01_is_state)
qed

lemma bell_10_is_entangled2:
  shows "entangled2 bell_10" 
proof-
  have "\<forall>v \<in> state_qbit 1. \<forall> w \<in> state_qbit 1. |\<beta>\<^sub>1\<^sub>0\<rangle> \<noteq> v \<otimes> w"
  proof-
    have "\<exists>v \<in> state_qbit 1. \<exists> w \<in> state_qbit 1. |\<beta>\<^sub>1\<^sub>0\<rangle> = v \<otimes> w \<Longrightarrow> False"
    proof-
      assume asm:"\<exists>v \<in> state_qbit 1. \<exists> w \<in> state_qbit 1. |\<beta>\<^sub>1\<^sub>0\<rangle> = v \<otimes> w"
      obtain v and w where a0:"v \<in> state_qbit 1" and a1:"w \<in> state_qbit 1" and a2:"|\<beta>\<^sub>1\<^sub>0\<rangle> = v \<otimes> w"
        using asm
        by blast
      have "|\<beta>\<^sub>1\<^sub>0\<rangle> $ 0 = (v \<otimes> w) $ 0"
        using a2
        by simp
      then have f1:"v $ 0 * w $ 0 = 1 / complex_of_real (sqrt 2)"
        using a0 a1
        by(auto simp add: vec_tensor_prod_2 mult.times.simps bell_10_def)
      have "|\<beta>\<^sub>1\<^sub>0\<rangle> $ 1 = (v \<otimes> w) $ 1"
        using a2
        by simp
      then have f2:"v $ 0 * w $ 1 = 0"
        using a0 a1
        by(auto simp add: vec_tensor_prod_2 mult.times.simps bell_10_def)
      have "|\<beta>\<^sub>1\<^sub>0\<rangle> $ 2 = (v \<otimes> w) $ 2"
        using a2
        by simp
      then have f3:"v $ 1 * w $ 0 = 0"
        using a0 a1
        by(auto simp add: vec_tensor_prod_2 mult.times.simps bell_10_def numeral_2_eq_2)
      have "|\<beta>\<^sub>1\<^sub>0\<rangle> $ 3 = (v \<otimes> w) $ 3"
        using a2
        by simp
      then have f4:"v $ 1 * w $ 1 = -1 / complex_of_real (sqrt 2)"
        using a0 a1
        by(auto simp add: vec_tensor_prod_2 mult.times.simps bell_10_def numeral_3_eq_3)
      have "1 / complex_of_real (sqrt 2) * 1 / complex_of_real (sqrt 2) = 0"
        using f1 f2 f3 f4
        by auto
      then show False
        by simp
    qed
    then show "\<forall>v \<in> state_qbit 1. \<forall> w \<in> state_qbit 1. |\<beta>\<^sub>1\<^sub>0\<rangle> \<noteq> v \<otimes> w"
      by blast
  qed
  then show ?thesis 
    by(simp add: entangled2_def prod_state2_def bell_10_is_state)
qed

lemma bell_11_is_entangled2:
  shows "entangled2 bell_11"
proof-
  have "\<forall>v \<in> state_qbit 1. \<forall> w \<in> state_qbit 1. |\<beta>\<^sub>1\<^sub>1\<rangle> \<noteq> v \<otimes> w"
  proof-
    have "\<exists>v \<in> state_qbit 1. \<exists> w \<in> state_qbit 1. |\<beta>\<^sub>1\<^sub>1\<rangle> = v \<otimes> w \<Longrightarrow> False"
    proof-
      assume asm:"\<exists>v \<in> state_qbit 1. \<exists> w \<in> state_qbit 1. |\<beta>\<^sub>1\<^sub>1\<rangle> = v \<otimes> w"
      obtain v and w where a0:"v \<in> state_qbit 1" and a1:"w \<in> state_qbit 1" and a2:"|\<beta>\<^sub>1\<^sub>1\<rangle> = v \<otimes> w"
        using asm
        by blast
      have "|\<beta>\<^sub>1\<^sub>1\<rangle> $ 0 = (v \<otimes> w) $ 0"
        using a2
        by simp
      then have f1:"v $ 0 * w $ 0 = 0"
        using a0 a1
        by(auto simp add: vec_tensor_prod_2 mult.times.simps bell_11_def)
      have "|\<beta>\<^sub>1\<^sub>1\<rangle> $ 1 = (v \<otimes> w) $ 1"
        using a2
        by simp
      then have f2:"v $ 0 * w $ 1 = 1 / complex_of_real (sqrt 2)"
        using a0 a1
        by(auto simp add: vec_tensor_prod_2 mult.times.simps bell_11_def)
      have "|\<beta>\<^sub>1\<^sub>1\<rangle> $ 2 = (v \<otimes> w) $ 2"
        using a2
        by simp
      then have f3:"v $ 1 * w $ 0 = -1 / complex_of_real (sqrt 2)"
        using a0 a1
        by(auto simp add: vec_tensor_prod_2 mult.times.simps bell_11_def numeral_2_eq_2)
      have "|\<beta>\<^sub>1\<^sub>1\<rangle> $ 3 = (v \<otimes> w) $ 3"
        using a2
        by simp
      then have f4:"v $ 1 * w $ 1 = 0"
        using a0 a1
        by(auto simp add: vec_tensor_prod_2 mult.times.simps bell_11_def numeral_3_eq_3)
      have "1 / complex_of_real (sqrt 2) * 1 / complex_of_real (sqrt 2) = 0"
        using f1 f2 f3 f4
        by auto
      then show False
        by simp
    qed
    then show "\<forall>v \<in> state_qbit 1. \<forall> w \<in> state_qbit 1. |\<beta>\<^sub>1\<^sub>1\<rangle> \<noteq> v \<otimes> w"
      by blast
  qed
  then show ?thesis 
    by(simp add: entangled2_def prod_state2_def bell_11_is_state)
qed


text \<open>An entangled state is a state that cannot be broken down as the tensor product of smaller states\<close>

definition prod_state ::"nat \<Rightarrow> complex Matrix.vec \<Rightarrow> bool" where
"prod_state m u \<equiv> if u \<in> state_qbit m then \<exists>n p::nat.\<exists>v \<in> state_qbit n.\<exists>w \<in> state_qbit p. 
  n < m \<and> p < m \<and>  u = v \<otimes> w else undefined"

definition entangled ::"nat \<Rightarrow> complex Matrix.vec \<Rightarrow> bool" where
"entangled n v \<equiv> \<not> (prod_state n v)"

(* To do: as an exercise prove the equivalence between entangled2 and (entangled 2) *)

lemma sanity_check: 
  shows "\<not>(entangled 2 (vec_of_list [1/sqrt(2), 1/sqrt(2)] \<otimes> vec_of_list [1/sqrt(2), 1/sqrt(2)]))" sorry



end