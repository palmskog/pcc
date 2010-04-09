Require Import List.
Require Import ssreflect.

Inductive configuration : Set :=
  | x : configuration
  | a : nat -> configuration
  | a' : nat -> configuration
  | b : nat -> configuration
  | b' : nat -> configuration.

Inductive execution : list configuration -> Prop :=
  | exec_nil : execution nil
  | exec_x : forall `(execution e), execution (x :: e)
  | exec_call : forall `(execution e) (n : nat), execution ((a n):: (b n) :: e)
  | exec_return : forall `(execution e) (n : nat), execution ((b' n) :: (a' n) :: e).

Fixpoint a_confs (e : list configuration) : list nat :=
match e with
| nil => nil
| a n :: e' => n :: a_confs e'
| a' n :: e' => n :: a_confs e'
| _ :: e' => a_confs e'
end.

Definition test_conf_list := (x :: x :: (a 1) :: (b 1) :: x :: x :: (b' 5) :: (a' 5) :: nil).

Lemma test_exec : execution test_conf_list.
Proof.
 rewrite /test_conf_list.
 apply exec_x.
 apply exec_x.
 apply exec_call.
 apply exec_x.
 apply exec_x.
 apply exec_return.
 apply exec_nil.
Qed.

Eval compute in a_confs test_conf_list.

Fixpoint b_confs (e : list configuration) : list nat :=
match e with
| nil => nil
| b n  :: e' => n :: b_confs e'
| b' n :: e' => n :: b_confs e'
| _  :: e' => b_confs e'
end.

Eval compute in b_confs test_conf_list.

Lemma test_conf_exists : exists e', (execution e') /\ b_confs test_conf_list = a_confs e'.
Proof.
 exists (test_conf_list).
 split.
 - by apply test_exec.
 - done.
Qed.
 
Lemma exists_exec_with_eq_bs :
  forall `(execution e), exists e', (execution e') /\ b_confs e = a_confs e'.
Proof.
Admitted.
