(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk *)

theory Entanglement
imports
  Main
  Jordan_Normal_Form.Matrix
  Quantum
  Tensor
begin


section\<open>Quantum Entanglement\<close>

subsection\<open>The Product States and Entangled States of a 2-qubits System\<close>

definition prod_state ::"complex Matrix.vec \<Rightarrow> bool" where
"prod_state u \<equiv> if u \<in> state_qbit 2 then \<exists>v.\<exists>w. u = v \<otimes> w else undefined"

definition entangled2 ::"complex Matrix.vec \<Rightarrow> bool" where
"entangled2 u \<equiv> \<not> prod_state u"

text\<open>The Bell states are entangled states\<close>

lemma bell_00_is_entangled2:
  shows "entangled2 bell_00" sorry

lemma bell_01_is_entangled2:
  shows "entangled2 bell_01" sorry

lemma bell_10_is_entangled2:
  shows "entangled2 bell_10" sorry

lemma bell_11_is_entangled2:
  shows "entangled2 bell_11" sorry



end