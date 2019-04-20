(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk *)

theory Quantum_Teleportation
imports 
  Main
  Jordan_Normal_Form.Matrix
  Quantum
  Tensor
begin


definition Alice ::"complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
"Alice \<phi> \<equiv> app (H \<Otimes> id 4) (app (CNOT \<Otimes> id 2) (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>))"

lemma Alice_state:
  assumes "state 1 \<phi>"
  shows "state 3 (Alice \<phi>)" sorry

text \<open>An application of function Alice to a state \<phi> of a 1-qubit system results in the following 
cases.\<close>

definition Alice_meas :: "complex Matrix.mat \<Rightarrow> _list" where
"Alice_meas \<phi> \<equiv> [
((prob_0 3 (Alice \<phi>) 0) * (prob_0 3 (post_meas_0 3 (Alice \<phi>) 0) 1), post_meas_0 3 (post_meas_0 3 (Alice \<phi>) 0) 1)
, ((prob_0 3 (Alice \<phi>) 0) * (prob_1 3 (post_meas_0 3 (Alice \<phi>) 0) 1), post_meas_1 3 (post_meas_0 3 (Alice \<phi>) 0) 1)
,((prob_1 3 (Alice \<phi>) 0) * (prob_0 3 (post_meas_1 3 (Alice \<phi>) 0) 1), post_meas_0 3 (post_meas_1 3 (Alice \<phi>) 0) 1)
,((prob_1 3 (Alice \<phi>) 0) * (prob_1 3 (post_meas_1 3 (Alice \<phi>) 0) 1), post_meas_1 3 (post_meas_1 3 (Alice \<phi>) 0) 1)
]"


definition Alice_pos :: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
"Alice_pos \<phi> q \<equiv>  q = mat_of_cols_list 8 [[\<phi> $$ (0,0), \<phi> $$ (1,0), 0, 0, 0, 0, 0, 0]] \<or>
                  q = mat_of_cols_list 8 [[0, 0, \<phi> $$ (1,0), \<phi> $$ (0,0), 0, 0, 0, 0]] \<or>
                  q = mat_of_cols_list 8 [[0, 0, 0, 0, \<phi> $$ (0,0), - \<phi> $$ (1,0), 0, 0]] \<or>
                  q = mat_of_cols_list 8 [[0, 0, 0, 0, 0, 0, - \<phi> $$ (1,0), \<phi> $$ (0,0)]]"

lemma Alice_case :
  assumes "state 1 \<phi>" and "state 3 q" and "List.member (Alice_meas \<phi>) (p, q)"
  shows "Alice_pos \<phi> q" sorry

datatype bit = zero | one

definition Alice_out ::"complex Matrix.mat => complex Matrix.mat => bit \<times> bit" where
"Alice_out \<phi> q \<equiv> if q = mat_of_cols_list 8 [[\<phi> $$ (0,0), \<phi> $$ (1,0), 0, 0, 0, 0, 0, 0]] then (zero, zero) else
  if q = mat_of_cols_list 8 [[0, 0, \<phi> $$ (1,0), \<phi> $$ (0,0), 0, 0, 0, 0]] then (zero, one) else
    if q = mat_of_cols_list 8 [[0, 0, 0, 0, \<phi> $$ (0,0), - \<phi> $$ (1,0), 0, 0]] then (one, zero) else
      if q = mat_of_cols_list 8 [[0, 0, 0, 0, 0, 0, - \<phi> $$ (1,0), \<phi> $$ (0,0)]] then (one, one) else 
        undefined"

definition Bob :: "complex Matrix.mat => bit \<times> bit \<Rightarrow> complex Matrix.mat" where
"Bob q b \<equiv> if (fst b, snd b) = (zero, zero) then q else 
  if (fst b, snd b) = (zero, one) then app (id 1 \<Otimes> id 1 \<Otimes> X) q else
    if (fst b, snd b) = (one, zero) then app (id 1 \<Otimes> id 1 \<Otimes> Z) q else
      if (fst b, snd b) = (one, one) then app (id 1 \<Otimes> id 1 \<Otimes> Y) q else 
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