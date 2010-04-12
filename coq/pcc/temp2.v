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

Hint Resolve trans_xx trans_xa trans_xb' : transitions.
Hint Resolve trans_ab trans_a'x trans_a'a trans_a'b' : transitions.
Hint Resolve trans_bx trans_ba trans_bb' trans_b'a' : transitions.

Inductive execution : list configuration -> Prop :=
| exec_nil : execution nil
| exec_a : forall n, execution (a n :: nil)
| exec_x : execution (x :: nil)
| exec_trans : forall `(trans c c')
                 `(execution (e ++ (c :: nil))),
	         execution (e ++ (c :: c' :: nil)).

Definition test_conf_list := x :: x :: (a 1) :: (b 1) :: x :: x :: (b' 5) :: nil.

Lemma rearrange (A: Set) : forall (a b c : A), a :: b :: c :: nil = (a :: nil) ++ (b :: c :: nil).
Proof. done. Qed.

Lemma test_exec : execution test_conf_list.
Proof.
  rewrite /test_conf_list.
  repeat (
    rewrite rearrange;
    repeat rewrite app_comm_cons;
    apply exec_trans;
    auto with transitions;
    simpl).  
  by apply exec_trans with (e := nil); [ apply trans_xx | apply exec_x ].
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
 exists (x :: x :: a 1 :: b 1 :: x :: x :: b' 5 :: a' 5 :: nil).
 split; last done.
 repeat (
   rewrite rearrange;
   repeat rewrite app_comm_cons;
   apply exec_trans;
   auto with transitions;
   rewrite /=).
 by apply exec_trans with (e := nil); [ apply trans_xx | apply exec_x ].
Qed.

Lemma rev_case : forall (e : list configuration), e = nil \/ (exists e', exists c, e = e' ++ (c :: nil)).
Proof.
 elim/rev_ind => [|c e H]; first by left. 
 elim: H => H.
 * by right; rewrite H; exists nil; exists c.
 * right.
   elim: H => e' H.
   elim: H => c' H.
   rewrite H {H}.
   by exists (e' ++ c' :: nil); exists c.
Qed.

Lemma b_updates_comp : forall (e : list configuration) (c : configuration), b_updates (e ++ c :: nil) = b_updates e ++ b_updates (c :: nil).
Proof.
 elim => [c|c e IH c']; first done.
 case: c => [|n|n|n|n]; case: c' => [|n0|n0|n0|n0]; (try rewrite /= IH -app_nil_end /=; try done); (try rewrite -IH /=; try done); (try rewrite /= IH; try done).
Qed.

Lemma a_updates_comp : forall (e : list configuration) (c : configuration), a_updates (e ++ c :: nil) = a_updates e ++ a_updates (c :: nil).
Proof.
 elim => [c|c e IH c']; first done.
 case: c => [|n|n|n|n]; case: c' => [|n0|n0|n0|n0]; (try rewrite /= IH -app_nil_end /=; try done); (try rewrite -IH /=; try done); (try rewrite /= IH; try done).
Qed.

Lemma coalesce_tail : forall (e : list configuration) (c c' : configuration), (e ++ c :: nil) ++ c' :: nil = e ++ c :: c' :: nil.
Proof. by move => e c c'; rewrite -ass_app -app_comm_cons. Qed.

Lemma coalesce_tail_long : forall (e : list configuration) (c c' c'' : configuration), (e ++ c :: c' :: nil) ++ c'' :: nil = e ++ c :: c' :: c'' :: nil.
Proof. by move => e c c' c''; rewrite -ass_app -app_comm_cons. Qed.

Lemma coalesce_long_tail : forall (e : list configuration) (c c' c'' : configuration), (e ++ c :: nil) ++ c' :: c'' :: nil = e ++ c :: c' :: c'' :: nil.
Proof. by move => e c c' c''; rewrite -ass_app -app_comm_cons. Qed.

Lemma exists_exec_n_remain : forall `(execution e) `(execution e') `(b_updates e = a_updates e') (n : nat), exists e0 : list configuration, execution e0 /\ b_updates e ++ n :: nil = a_updates e0.
Proof.
 move => e execution0 e' H H0 n.
 pose proof rev_case e' as H1.
 elim: H1 => H1; first by subst; exists (a n :: nil); split; [ apply exec_a | rewrite H0 ]. 
 elim: H1 => e0 H1; elim: H1.
 case => [|n'|n'|n'|n'] H1.
 - rewrite H1 {H1 e'} in H H0.
   exists (e0 ++ x :: a n :: nil). 
   split; first by apply exec_trans; [ apply trans_xa | done ].
   by rewrite H0 -coalesce_tail 3!a_updates_comp.
 - rewrite H1 {H1 e'} in H H0.
   exists (e0 ++ a n' :: b n' :: a n :: nil); split.
   * rewrite -coalesce_long_tail.
     apply exec_trans; first by apply trans_ba.
     by rewrite coalesce_tail; apply exec_trans; first by apply trans_ab.
   * by rewrite -coalesce_tail_long -coalesce_tail 2!a_updates_comp H0 -app_nil_end.
 - rewrite H1 {H1 e'} in H H0.
   exists (e0 ++ a' n' :: a n :: nil).
   split; first by apply exec_trans; [ apply trans_a'a | done ].
   by rewrite -coalesce_tail a_updates_comp H0.
 - rewrite H1 {H1 e'} in H H0.
   exists (e0 ++ b n' :: a n :: nil).
   split; first by apply exec_trans; [ apply trans_ba | done ].
   by rewrite -coalesce_tail a_updates_comp H0.
 - rewrite H1 {H1 e'} in H H0.
   rewrite a_updates_comp -app_nil_end in H0.
   exists (e0 ++ a n :: nil).
   inversion H; first by contradict H2; apply app_cons_not_nil.
   * change (a n0 :: nil) with (nil ++ a n0 :: nil) in H2.
     apply app_inj_tail in H2.
     by elim: H2 => H2 H3.
   * change (x :: nil) with (nil ++ x :: nil) in H2.
     apply app_inj_tail in H2.
     by elim: H2 => H2 H3.
   * rewrite -coalesce_tail in H2.
     apply app_inj_tail in H2.
     elim: H2 => H2 H3.
     rewrite H2 in execution1.
     rewrite H3 {H3} in trans0.
     split; last by rewrite a_updates_comp H0.
     move: H2 trans0.
     case: c => [|n0|n0|n0|n0] H2 H3.
     + rewrite -H2 coalesce_tail.
       apply exec_trans; first by apply trans_xa.
       by rewrite -H2 in execution1.
     + by inversion H3.
     + rewrite -H2 coalesce_tail.
       apply exec_trans; first by apply trans_a'a.
       by rewrite H2.
     + rewrite -H2 coalesce_tail. 
       apply exec_trans; first by apply trans_ba.
       by rewrite H2.
     + by inversion H3.
Qed.

Theorem exists_exec_with_eq_bs : forall `(execution e), exists e', (execution e') /\ b_updates e = a_updates e'.
Proof.
 elim/rev_ind => [H|c e IH H]; first by exists nil; split; [ apply exec_nil | done ].
 inversion H.
 - by exists nil; split; [ apply exec_nil | done ].
 - by exists nil; split; [ apply exec_nil | done ].
 - by exists (x :: nil); split; [ apply exec_x | done ].
 - rewrite -coalesce_tail in H1.     
   apply app_inj_tail in H1.
   elim: H1 => H1 H2.     
   move: execution0 trans0 H IH. 
   rewrite -coalesce_tail H1 H2 {H1 H2 c'} => execution0 trans0 H IH.
   pose proof execution0 as H0.
   apply IH in H0.
   elim: H0 => e' H0 {IH}.
   elim: H0 => H0 H1.
   move: H H1 trans0.
   case: c => [|n|n|n|n] H H1 trans0.
   * by exists e'; split; first done; rewrite b_updates_comp H1 -app_nil_end.
   * by exists e'; split; first done; rewrite b_updates_comp H1 -app_nil_end.
   * by exists e'; split; first done; rewrite b_updates_comp H1 -app_nil_end.
   * by rewrite b_updates_comp; apply (exists_exec_n_remain execution0 H0 H1 n).
   * by rewrite b_updates_comp; apply (exists_exec_n_remain execution0 H0 H1 n).
Qed.
