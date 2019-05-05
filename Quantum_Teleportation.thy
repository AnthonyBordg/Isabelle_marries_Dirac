(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk *)

theory Quantum_Teleportation
imports 
  Quantum 
  MoreTensor
begin


definition Alice:: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
"Alice \<phi> \<equiv> (H \<Otimes> id 2) * ((CNOT \<Otimes> id 1) * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>))"

lemma Alice_state [simp]:
  assumes "state 1 \<phi>"
  shows "state 3 (Alice \<phi>)"
proof -
  have "state 3 (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>)"
    using assms bell00_is_state tensor_state by(metis One_nat_def Suc_1 numeral_3_eq_3 plus_1_eq_Suc)
  moreover have "gate 3 (CNOT \<Otimes> id 1)"
    using CNOT_is_gate id_is_gate tensor_gate by(metis numeral_plus_one semiring_norm(5))
  ultimately have "state 3 ((CNOT \<Otimes> id 1) * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>))" by simp
  moreover have "gate 3 (H \<Otimes> id 2)"
    using tensor_gate id_is_gate H_is_gate
    by (metis eval_nat_numeral(3) plus_1_eq_Suc)
  ultimately show ?thesis by(simp add: Alice_def)
qed

text \<open>
An application of function Alice to a state \<phi> of a 1-qubit system results in the following cases.
\<close>

definition Alice_meas:: "complex Matrix.mat \<Rightarrow> _list" where
"Alice_meas \<phi> \<equiv> [
((prob0 3 (Alice \<phi>) 0) * (prob0 3 (post_meas0 3 (Alice \<phi>) 0) 1), post_meas0 3 (post_meas0 3 (Alice \<phi>) 0) 1)
, ((prob0 3 (Alice \<phi>) 0) * (prob1 3 (post_meas0 3 (Alice \<phi>) 0) 1), post_meas1 3 (post_meas0 3 (Alice \<phi>) 0) 1)
,((prob1 3 (Alice \<phi>) 0) * (prob0 3 (post_meas1 3 (Alice \<phi>) 0) 1), post_meas0 3 (post_meas1 3 (Alice \<phi>) 0) 1)
,((prob1 3 (Alice \<phi>) 0) * (prob1 3 (post_meas1 3 (Alice \<phi>) 0) 1), post_meas1 3 (post_meas1 3 (Alice \<phi>) 0) 1)
]"

definition Alice_pos:: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
"Alice_pos \<phi> q \<equiv>  q = mat_of_cols_list 8 [[\<phi> $$ (0,0), \<phi> $$ (1,0), 0, 0, 0, 0, 0, 0]] \<or>
                  q = mat_of_cols_list 8 [[0, 0, \<phi> $$ (1,0), \<phi> $$ (0,0), 0, 0, 0, 0]] \<or>
                  q = mat_of_cols_list 8 [[0, 0, 0, 0, \<phi> $$ (0,0), - \<phi> $$ (1,0), 0, 0]] \<or>
                  q = mat_of_cols_list 8 [[0, 0, 0, 0, 0, 0, - \<phi> $$ (1,0), \<phi> $$ (0,0)]]"

lemma Alice_case [simp]:
  assumes "state 1 \<phi>" and "state 3 q" and "List.member (Alice_meas \<phi>) (p, q)"
  shows "Alice_pos \<phi> q"  sorry
(*proof-
  fix \<phi>::"complex Matrix.mat"
  define \<alpha> \<beta> where "\<alpha> = \<phi> $$ (0,0)" and "\<beta> = \<phi> $$ (1,0)"
  then have "post_meas0 3 (post_meas0 3 (Alice \<phi>) 0) 1 = 
mat_of_cols_list 8 [[\<alpha>, \<beta>, 0, 0, 0, 0, 0, 0]]"
  proof-
    have f1:"{j |j::nat. select_index 3 0 j} = {4,5,6,7}"
      apply (auto simp: select_index_def).
    then have "{j | j::nat. j < 8 \<and> \<not> select_index 3 0 j} = {0,1,2,3}"
    proof-
      have "\<forall>j::nat. j < 8 \<and> j \<notin> {4,5,6,7} \<longrightarrow> j \<in> {0,1,2,3}" 
        by auto
      thus ?thesis
        apply (auto simp: f1 select_index_def).
    qed
*)

datatype bit = zero | one

definition Alice_out:: "complex Matrix.mat => complex Matrix.mat => bit \<times> bit" where
"Alice_out \<phi> q \<equiv> if q = mat_of_cols_list 8 [[\<phi> $$ (0,0), \<phi> $$ (1,0), 0, 0, 0, 0, 0, 0]] then (zero, zero) else
  if q = mat_of_cols_list 8 [[0, 0, \<phi> $$ (1,0), \<phi> $$ (0,0), 0, 0, 0, 0]] then (zero, one) else
    if q = mat_of_cols_list 8 [[0, 0, 0, 0, \<phi> $$ (0,0), - \<phi> $$ (1,0), 0, 0]] then (one, zero) else
      if q = mat_of_cols_list 8 [[0, 0, 0, 0, 0, 0, - \<phi> $$ (1,0), \<phi> $$ (0,0)]] then (one, one) else 
        undefined"

definition Bob:: "complex Matrix.mat => bit \<times> bit \<Rightarrow> complex Matrix.mat" where
"Bob q b \<equiv> if (fst b, snd b) = (zero, zero) then q else 
  if (fst b, snd b) = (zero, one) then (id 1 \<Otimes> id 1 \<Otimes> X) * q else
    if (fst b, snd b) = (one, zero) then (id 1 \<Otimes> id 1 \<Otimes> Z) * q else
      if (fst b, snd b) = (one, one) then (id 1 \<Otimes> id 1 \<Otimes> Y) * q else 
        undefined"

lemma teleportation:
  assumes "state 1 \<phi>" and "state 3 q" and "List.member (Alice_meas \<phi>) (p, q)"
  shows "\<exists>r. state 2 r \<and> Bob q (Alice_out \<phi> q) = r \<Otimes> \<phi>" sorry

(* 
Bibliography:

- Jaap Boender, Florian Kammüller, Rajagopal Nagarajan, Formalization of Quantum Protocols Using Coq, 
Proceedings QPL 2015, arXiv:1511.01181 
*)


end