Require Import List.
Require Import ssreflect.

Inductive configuration : Set :=
  | x
  | a  (_: nat)
  | a' (_: nat)
  | b  (_: nat)
  | b' (_: nat).


Inductive trans : configuration -> configuration -> Prop :=
(* [x] can go to anything *)
| trans_xx    : trans x x
| trans_xa    : forall n, trans x (a n)
| trans_xb'   : forall n, trans x (b' n)
(* (a n) can only go to (b n)  *)
| trans_ab    : forall n, trans (a n) (b n)
(* (a' n) can go to x, (a m) or (b' m) *)
| trans_a'x   : forall n, trans (a' n) x
| trans_a'a   : forall n m, trans (a' n) (a m)
| trans_a'b'  : forall n m, trans (a' n) (b' m)
(* similarly, (b n) can go to x, (a m) or (b' m) *)
| trans_bx    : forall n, trans (b n) x
| trans_ba    : forall n m, trans (b n) (a m)
| trans_bb'   : forall n m, trans (b n) (b' m)
(* (b' n) can only go to (a' n). *)
| trans_b'a'  : forall n, trans (b' n) (a' n).


Hint Resolve trans_xx trans_xa trans_xb' trans_ab trans_a'x
  trans_a'a trans_a'b' trans_bx trans_ba trans_bb' trans_b'a' : transitions.


Inductive execution : list configuration -> Prop :=
| exec_nil : execution nil
| exec_sing : forall c, execution (c :: nil)
| exec_trans : forall `(trans c c')
                 `(execution (e ++ (c :: nil))),
	         execution (e ++ (c :: c' :: nil)).

Definition test_conf_list := (x :: x :: (a 1) :: (b 1) :: x :: x :: (b' 5) :: nil).


Lemma rearrange (A: Set) : forall (a b c : A), a :: b :: c :: nil = (a :: nil) ++ (b :: c :: nil).
  reflexivity.
Qed.

Lemma test_exec : execution test_conf_list.
Proof.
  unfold test_conf_list.
  repeat (
    rewrite rearrange;
    repeat rewrite app_comm_cons;
    apply exec_trans;
    auto with transitions;
    simpl).
  
  apply exec_trans with (e := nil).
  apply trans_xx.

  apply exec_sing.
Qed.


Fixpoint a_updates (e : list configuration) : list nat :=
match e with
| nil => nil
| a n :: e' => n :: a_updates e'
| a' n :: e' => n :: a_updates e'
| _ :: e' => a_updates e'
end.

Eval compute in a_updates test_conf_list.

Fixpoint b_updates (e : list configuration) : list nat :=
match e with
| nil => nil
| b n  :: e' => n :: b_updates e'
| b' n :: e' => n :: b_updates e'
| _  :: e' => b_updates e'
end.

Eval compute in b_updates test_conf_list.

Lemma test_conf_exists : exists e', (execution e') /\ b_updates test_conf_list = a_updates e'.
Proof.
Admitted.
 
Lemma exists_exec_with_eq_bs :
  forall `(execution e), exists e', (execution e') /\ b_updates e = a_updates e'.
Proof.
Admitted.
