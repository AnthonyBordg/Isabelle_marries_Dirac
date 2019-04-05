(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk *)

theory Quantum_Teleportation
imports 
  Main
  Jordan_Normal_Form.Matrix
  Quantum
  Tensor
begin


definition Alice ::"complex Matrix.vec \<Rightarrow> complex Matrix.vec" where
"Alice \<phi> \<equiv> 
app (Abs_gate (H_gate \<Otimes> id_gate 4)) (app (Abs_gate (CNOT_gate \<Otimes> id_gate 2)) (Abs_state (\<phi> \<otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>)))"

lemma Alice_state:
  assumes "\<phi> \<in> state_qbit 1"
  shows "Alice \<phi> \<in> state_qbit 3" sorry

text \<open>An application of function Alice to a single qubit \<phi> results in the following cases\<close>

definition Alice_meas :: "complex Matrix.vec \<Rightarrow> _list" where
"Alice_meas \<phi> \<equiv> [
((prob_0 3 (Alice \<phi>) 0) * (prob_0 3 (post_meas_0 3 (Alice \<phi>) 0) 1), post_meas_0 3 (post_meas_0 3 (Alice \<phi>) 0) 1)
, ((prob_0 3 (Alice \<phi>) 0) * (prob_1 3 (post_meas_0 3 (Alice \<phi>) 0) 1), post_meas_1 3 (post_meas_0 3 (Alice \<phi>) 0) 1)
,((prob_1 3 (Alice \<phi>) 0) * (prob_0 3 (post_meas_1 3 (Alice \<phi>) 0) 1), post_meas_0 3 (post_meas_1 3 (Alice \<phi>) 0) 1)
,((prob_1 3 (Alice \<phi>) 0) * (prob_1 3 (post_meas_1 3 (Alice \<phi>) 0) 1), post_meas_1 3 (post_meas_1 3 (Alice \<phi>) 0) 1)
]"


definition Alice_pos :: "complex Matrix.vec \<Rightarrow> complex Matrix.vec \<Rightarrow> bool" where
"Alice_pos \<phi> q \<equiv>  q = vec_of_list [\<phi> $ 0, \<phi> $ 1, 0, 0, 0, 0, 0, 0] \<or>
                  q = vec_of_list [0, 0, \<phi> $ 1, \<phi> $ 0, 0, 0, 0, 0] \<or>
                  q = vec_of_list [0, 0, 0, 0, \<phi> $ 0, - \<phi> $ 1, 0, 0] \<or>
                  q = vec_of_list [0, 0, 0, 0, 0, 0, - \<phi> $ 1, \<phi> $ 0]"

lemma Alice_case :
  assumes "\<phi> \<in> state_qbit 1" and "q \<in> state_qbit 3" and "List.member (Alice_meas \<phi>) (p, q)"
  shows "Alice_pos \<phi> q" sorry

datatype bit = zero | one

definition Alice_out ::"complex Matrix.vec => complex Matrix.vec => bit \<times> bit" where
"Alice_out \<phi> q \<equiv> if q = vec_of_list [\<phi> $ 0, \<phi> $ 1, 0, 0, 0, 0, 0, 0] then (zero, zero) else
  if q = vec_of_list [0, 0, \<phi> $ 1, \<phi> $ 0, 0, 0, 0, 0] then (zero, one) else
    if q = vec_of_list [0, 0, 0, 0, \<phi> $ 0, - \<phi> $ 1, 0, 0] then (one, zero) else
      if q = vec_of_list [0, 0, 0, 0, 0, 0, - \<phi> $ 1, \<phi> $ 0] then (one, one) else undefined"

definition Bob :: "complex Matrix.vec => bit \<times> bit \<Rightarrow> complex Matrix.vec" where
"Bob q b \<equiv> if (fst b, snd b) = (zero, zero) then Abs_state q else 
  if (fst b, snd b) = (zero, one) then app (Abs_gate (id_gate 1 \<Otimes> id_gate 1 \<Otimes> X_gate)) (Abs_state q) else
    if (fst b, snd b) = (one, zero) then app (Abs_gate (id_gate 1 \<Otimes> id_gate 1 \<Otimes> Z_gate)) (Abs_state q) else
      if (fst b, snd b) = (one, one) then app (Abs_gate (id_gate 1 \<Otimes> id_gate 1 \<Otimes> Y_gate)) (Abs_state q) else 
        undefined"

lemma teleportation:
  assumes "\<phi> \<in> state_qbit 1" and "q \<in> state_qbit 3" and "List.member (Alice_meas \<phi>) (p, q)"
  shows "\<exists>r \<in> state_qbit 2. Bob q (Alice_out \<phi> q) = r \<otimes> \<phi>" sorry

(* 
Bibliography:

- Jaap Boender, Florian Kammüller, Rajagopal Nagarajan, Formalization of Quantum Protocols Using Coq, 
Proceedings QPL 2015, arXiv:1511.01181 
*)

end