Require Import List.


Inductive configuration := a | a' | b | b' | x.


Inductive trans : configuration -> configuration -> Prop
(* every A  is followed by B  (and every B  is preceeded by A)
   every B' is followed by A' (and every A' is preceeded by B) *)



Inductive execution : list configuration -> Prop :=
| exec_nil : execution nil
| exec_sing : forall c, execution (c :: nil)
| exec_trans : forall `(trans c c')
                 `(execution (c' :: e)),
                 execution (c' :: c :: e).


Fixpoint a_confs (e : list configuration) : list configuration :=
match e with
| nil => nil
| a  :: e' => a :: a_confs e'
| a' :: e' => a' :: a_confs e'
| _  :: e' => a_confs e'
end.


Fixpoint b_confs (e : list configuration) : list configuration :=
match e with
| nil => nil
| b  :: e' => b :: b_confs e'
| b' :: e' => b' :: b_confs e'
| _  :: e' => b_confs e'
end.


Lemma exists_exec_with_eq_bs :
  forall `(execution e), exists e', (execution e') /\ b_confs e = a_confs e'.
Proof.
Admitted.
