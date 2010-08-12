Require Import List.
Require Import Omega.
Require Import ssreflect.

Inductive configuration : Set :=
  | x
  | a  (_: nat)
  | a' (_: nat)
  | b  (_: nat)
  | b' (_: nat).

Inductive trans : configuration -> configuration -> Prop :=
| trans_xx    : trans x x
| trans_xa    : forall n, trans x (a n)
| trans_xb'   : forall n, trans x (b' n)
| trans_ab    : forall n, trans (a n) (b n)
| trans_a'x   : forall n, trans (a' n) x
| trans_a'a   : forall n m, trans (a' n) (a m)
| trans_a'b'  : forall n m, trans (a' n) (b' m)
| trans_bx    : forall n, trans (b n) x
| trans_ba    : forall n m, trans (b n) (a m)
| trans_bb'   : forall n m, trans (b n) (b' m)
| trans_b'a'  : forall n, trans (b' n) (a' n).

Hint Resolve trans_xx trans_xa trans_xb' : transitions.
Hint Resolve trans_ab trans_a'x trans_a'a trans_a'b' : transitions.
Hint Resolve trans_bx trans_ba trans_bb' trans_b'a' : transitions.

Inductive execution : list configuration -> Prop :=
| exec_nil : execution nil
| exec_a : forall n, execution (a n :: nil)
| exec_x : execution (x :: nil)
| exec_trans : forall `(trans c c')
                 `(execution (e ++ c :: nil)),
	         execution (e ++ c :: c' :: nil).

Definition test_conf_list := x :: x :: (a 1) :: (b 1) :: x :: x :: (b' 5) :: nil.

Lemma rearrange (A: Set) : forall (a b c : A), a :: b :: c :: nil = (a :: nil) ++ (b :: c :: nil).
Proof. by []. Qed.

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
split; rewrite //.
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
elim: H => H; first by right; rewrite H; exists nil; exists c.
right.
move: H => [ e' [ c' H]].
rewrite H {H}.
by exists (e' ++ c' :: nil); exists c.
Qed.

Lemma b_updates_comp : forall (e : list configuration) (c : configuration), 
  b_updates (e ++ c :: nil) = b_updates e ++ b_updates (c :: nil).
Proof.
elim => [c|c e IH c']; first done.
case: c => [|n|n|n|n]; case: c' => [|n0|n0|n0|n0]; (try rewrite /= IH -app_nil_end //=); (try rewrite -IH //=); (try rewrite /= IH //=).
Qed.

Lemma a_updates_comp : forall (e : list configuration) (c : configuration), 
  a_updates (e ++ c :: nil) = a_updates e ++ a_updates (c :: nil).
Proof.
elim => [c|c e IH c']; first done.
case: c => [|n|n|n|n]; case: c' => [|n0|n0|n0|n0]; (try rewrite /= IH -app_nil_end /=; try done); (try rewrite -IH /=; try done); (try rewrite /= IH; try done).
Qed.

Lemma coalesce_tail : forall (e : list configuration) (c c' : configuration),
  (e ++ c :: nil) ++ c' :: nil = e ++ c :: c' :: nil.
Proof. by move => e c c'; rewrite -ass_app -app_comm_cons. Qed.

Lemma coalesce_tail_long : forall (e : list configuration) (c c' c'' : configuration), 
  (e ++ c :: c' :: nil) ++ c'' :: nil = e ++ c :: c' :: c'' :: nil.
Proof. by move => e c c' c''; rewrite -ass_app -app_comm_cons. Qed.

Lemma coalesce_long_tail : forall (e : list configuration) (c c' c'' : configuration), 
  (e ++ c :: nil) ++ c' :: c'' :: nil = e ++ c :: c' :: c'' :: nil.
Proof. by move => e c c' c''; rewrite -ass_app -app_comm_cons. Qed.

Lemma exists_exec_n_remain : forall `(execution e) `(execution e') (n : nat), 
  b_updates e = a_updates e' -> exists e0 : list configuration, execution e0 /\ 
    b_updates e ++ n :: nil = a_updates e0.
Proof.
move => e execution0 e' H n H0.
pose proof rev_case e' as H1.
elim: H1 => H1; first by subst; exists (a n :: nil); split; [ apply exec_a | rewrite H0 ].
elim: H1 => e0 H1; elim: H1.
case => [|n'|n'|n'|n'] H1; rewrite H1 {H1 e'} in H H0.
- exists (e0 ++ x :: a n :: nil). 
  split; first by apply exec_trans; [ apply trans_xa | done ].
  by rewrite H0 -coalesce_tail 3!a_updates_comp.
- exists (e0 ++ a n' :: b n' :: a n :: nil); split.
  * rewrite -coalesce_long_tail.
    apply exec_trans; first by apply trans_ba.
    by rewrite coalesce_tail; apply exec_trans; first by apply trans_ab.
  * by rewrite -coalesce_tail_long -coalesce_tail 2!a_updates_comp H0 -app_nil_end.
- exists (e0 ++ a' n' :: a n :: nil).
  split; first by apply exec_trans; [ apply trans_a'a | done ].
  by rewrite -coalesce_tail a_updates_comp H0.
- exists (e0 ++ b n' :: a n :: nil).
  split; first by apply exec_trans; [ apply trans_ba | done ].
  by rewrite -coalesce_tail a_updates_comp H0.
- exists (e0 ++ a n :: nil).
  rewrite a_updates_comp -app_nil_end in H0.
  inversion H as [H1|n0 H1|H1|c c' H1 e' H2 H3].
  * by contradict H1; apply app_cons_not_nil.
  * change (a n0 :: nil) with (nil ++ a n0 :: nil) in H1.
    apply app_inj_tail in H1.
    by elim: H1 => H1 H2.
  * change (x :: nil) with (nil ++ x :: nil) in H1.
    apply app_inj_tail in H1.
    by elim: H1 => H1 H2.
  * rewrite -coalesce_tail in H3.
    apply app_inj_tail in H3.
    elim: H3 => H3 H4.
    rewrite H3 in H2.
    rewrite H4 {H4 c'} in H1.
    split; last by rewrite a_updates_comp H0.
    move: H1 H3.
    case: c => [|n0|n0|n0|n0] H1 H3.
    + rewrite -H3 coalesce_tail.
      by apply exec_trans; [ apply trans_xa | rewrite -H3 in H2 ].
    + by inversion H1.
    + rewrite -H3 coalesce_tail.
      by apply exec_trans; [ apply trans_a'a | rewrite H3 ].
    + rewrite -H3 coalesce_tail. 
      by apply exec_trans; [ apply trans_ba | rewrite H3 ].
    + by inversion H1.
Qed.

Theorem exists_exec_with_eq_bs : forall `(execution e), 
  exists e', (execution e') /\ b_updates e = a_updates e'.
Proof.
elim/rev_ind => [H|c e IH H]; first by exists nil; split; rewrite //; apply exec_nil.
inversion H as [H0|n H0|H0|c' c0 H0 e' H1 H2].
- by apply app_cons_not_nil in H0.
- by exists nil; split; rewrite //; apply exec_nil.
- by exists (x :: nil); split; rewrite //; apply exec_x.
- rewrite -coalesce_tail in H2.
  apply app_inj_tail in H2.
  move: H2 => [H2 [H3 ] ].
  move: H IH H0 H1; rewrite -coalesce_tail H2 H3 {H2 H3 c0 e'} => H IH H0 H1.
  pose proof H1 as H2.
  apply IH in H1.
  elim: H1 => e' H1 {IH}.
  elim: H1 => H1 H3.
  move: H H0.
  case: c => [|n|n|n|n] H H0.
  * by exists e'; split; rewrite // b_updates_comp H3 -app_nil_end.
  * by exists e'; split; rewrite // b_updates_comp H3 -app_nil_end.
  * by exists e'; split; rewrite // b_updates_comp H3 -app_nil_end.
  * by rewrite b_updates_comp; apply (exists_exec_n_remain H2 H1).
  * by rewrite b_updates_comp; apply (exists_exec_n_remain H2 H1).
Qed.

Lemma list_neq_length (A: Set) : forall l l': list A, length l <> length l' -> l <> l'.
intros.
contradict H.
subst.
reflexivity.
Qed.

Lemma sub_execution : forall `(execution (e ++ c :: nil)), execution e.
(* behöver ej induktion *)
destruct e using rev_ind; intros.
apply exec_nil.
inversion execution0.
contradict H0; apply app_cons_not_nil.
contradict H0.
apply list_neq_length.
rewrite app_length.
rewrite app_length.
simpl.
omega.
contradict H0.
apply list_neq_length.
rewrite app_length.
rewrite app_length.
simpl; omega.
rewrite -coalesce_tail in H0.
apply app_inj_tail in H0.
elim H0; intros.
apply app_inj_tail in H.
elim H; intros.
subst.
assumption.
Qed.

Lemma exec_impl_trans : forall `(execution (e ++ c :: c' :: nil)), trans c c'.
intros.
inversion execution0;
  try (contradict H0; apply list_neq_length; simpl; rewrite app_length; simpl; omega).
rewrite -2!coalesce_tail in H0.
apply app_inj_tail in H0; elim H0; intros.
apply app_inj_tail in H; elim H; intros.
subst.
assumption.
Qed.


Lemma exec_tail_cases : forall `(execution (e ++ c :: nil)),
  (exists n, c = a  n /\ (b_updates (e ++ c :: nil)) ++ n :: nil = a_updates (e ++ c :: nil)) \/
  (exists n, c = b  n /\ b_updates (e ++ c :: nil) = a_updates (e ++ c :: nil)) \/
  (exists n, c = b' n /\ b_updates (e ++ c :: nil) = (a_updates e) ++ n :: nil) \/
  (exists n, c = a' n /\ b_updates (e ++ c :: nil) = (a_updates e) ++ n :: nil) \/
  (c = x /\ b_updates (e ++ c :: nil) = a_updates (e ++ c :: nil)).
destruct e using rev_ind; intros.
destruct c.
right; right; right; right.
split; reflexivity.
left.
exists n.
split; reflexivity.
right; right; right; left.
simpl in execution0.
inversion execution0.
apply app_eq_unit in H0.
elim H0; intros.
elim H; intros.
inversion H2.
elim H; intros.
inversion H2.
simpl in execution0.
inversion execution0.
apply app_eq_unit in H0.
elim H0; intros.
elim H; intros.
inversion H2.
elim H; intros.
inversion H2.
simpl in execution0.
inversion execution0.
apply app_eq_unit in H0.
elim H0; intros.
elim H; intros.
inversion H2.
elim H; intros.
inversion H2.

(* inductive case *)
pose proof (IHe x0 (sub_execution execution0)).
clear IHe.
rewrite coalesce_tail in execution0.
apply exec_impl_trans in execution0.
inversion execution0; subst.

(* case x x *)
right; right; right; right.
split.
reflexivity.
move: H => [H | [ H | ]].
move: H => [H | [ H | [ H | [H | H]]]]; try by (elim: H => n H; elim: H).
elim: H => H_eq H.
rewrite b_updates_comp; rewrite a_updates_comp.
rewrite H.
reflexivity.

(* case x a *)
left.
exists n.
split; first by reflexivity.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim H; clear H; intros.
rewrite b_updates_comp a_updates_comp.
rewrite H0.
rewrite -app_nil_end.
reflexivity.

(* case x b' *)
right; right; left.
exists n.
split; first by reflexivity.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim H; clear H; intros.
rewrite b_updates_comp a_updates_comp.
rewrite H0.
rewrite a_updates_comp.
reflexivity.

(* case a b *)
right; left.
exists n.
split; first by reflexivity.
elim H; clear H; intros.
elim H; clear H; intros.
elim H; clear H; intros.
inversion H; subst.
rewrite a_updates_comp.
rewrite -H0.
simpl.
rewrite b_updates_comp.
auto with datatypes.

elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim: H => H. discriminate.

(* case a x *)
right; right; right; right.
split; first by reflexivity.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim H; clear H; intros.
elim H; clear H; intros.
elim H; clear H; intros.
inversion H; subst.
rewrite a_updates_comp b_updates_comp.
rewrite H0.
rewrite a_updates_comp.
reflexivity.
elim H; clear H; intros H; discriminate.

(* case a' a *)
left.
exists m.
split; first by reflexivity.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim H; clear H; intros.
elim H; clear H; intros.
elim H; clear H; intros.
inversion H; subst.
rewrite a_updates_comp.
rewrite a_updates_comp.
rewrite -H0.
rewrite b_updates_comp.
rewrite -app_nil_end.
reflexivity.
elim H; clear H; intros H; discriminate.

(* case a' b' *)
right; right; left.
exists m.
split; first by reflexivity.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim H; clear H; intros.
elim H; clear H; intros.
elim H; clear H; intros.
inversion H; subst.
rewrite a_updates_comp.
rewrite -H0.
rewrite b_updates_comp.
reflexivity.
elim H; clear H; intros H; discriminate.

(* case b x *)
right; right; right; right.
split; first by reflexivity.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim H; clear H; intros.
elim H; clear H; intros.
elim H; clear H; intros.
inversion H; subst.
rewrite a_updates_comp b_updates_comp.
rewrite -H0.
rewrite b_updates_comp.
reflexivity.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim H; clear H; intros H; discriminate.

(* case b a *)
left.
exists m.
split; first by reflexivity.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim H; clear H; intros.
elim H; clear H; intros.
elim H; clear H; intros.
inversion H; subst.
rewrite a_updates_comp b_updates_comp.
rewrite -H0.
rewrite b_updates_comp.
rewrite -app_nil_end.
reflexivity.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim H; clear H; intros H; discriminate.

(* case b b' *)
right; right; left.
exists m.
split; first by reflexivity.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim H; clear H; intros.
elim H; clear H; intros.
elim H; clear H; intros.
inversion H; subst.
rewrite b_updates_comp.
rewrite -H0.
rewrite b_updates_comp.
reflexivity.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim H; clear H; intros H; discriminate.

(* case b' a' *)
right; right; right; left.
exists n.
split; first by reflexivity.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim H; clear H; intros.
elim H; clear H; intros.
elim H; clear H; intros.
inversion H; subst.
rewrite b_updates_comp a_updates_comp.
simpl.
rewrite -2!app_nil_end.
rewrite -H0.
reflexivity.
elim: H => H. elim H; clear H; intros n' H; elim H; clear H; intros H_disc; discriminate.
elim H; clear H; intros H; discriminate.
Qed.

  Lemma list_neq_length (A: Set) : forall l l': list A, length l <> length l' -> l <> l'.
    intros.
    contradict H.
    subst.
    reflexivity.
  Qed.

Theorem exists_exec_with_eq_bs_2 : forall `(execution e), exists e', (execution e') /\ b_updates e = a_updates e'.
intros.
pose proof (rev_case e) as H_ecase.
elim H_ecase; clear H_ecase; intros; subst.
exists nil; split; [ apply exec_nil | reflexivity ].
elim H; clear H; intros e0 H.
elim H; clear H; intros c H.
subst.
pose proof (exec_tail_cases execution0).
elim H; clear H; intros.
(* FALL 1 *)
exists e0.
split.
apply sub_execution in execution0; assumption.
elim H; clear H; intros.
elim H; clear H; intros.
subst.
assert (forall l, a_updates (l ++ a x0 :: nil) = (a_updates l) ++ x0 :: nil).
  induction l.
  reflexivity.
  simpl.
  rewrite IHl.
  destruct a0; reflexivity.
rewrite H in H0.
apply app_inj_tail in H0.
elim H0; intros.
assumption.

(* FALL 2 *)
elim H; clear H; intros.
exists (e0 ++ c :: nil).
split.
assumption.
elim H; clear H; intros.
elim H; clear H; intros.
assumption.

(* FALL 3 *)
elim H; clear H; intros.
elim H; clear H; intros.
elim H; clear H; intros.
subst.
exists ((e0 ++ b' x0 :: nil) ++ (a' x0 :: nil)).
split.
rewrite app_ass.
simpl.
apply exec_trans.
apply trans_b'a'.
assumption.
rewrite H0.
rewrite a_updates_comp.
simpl.
rewrite a_updates_comp.
simpl.
rewrite -app_nil_end.
reflexivity.
(* FALL 4 *)
elim H; clear H; intros.
elim H; clear H; intros.
elim H; clear H; intros.
exists (e0 ++ c :: nil).
split.
assumption.
subst.
rewrite H0.
rewrite a_updates_comp.
reflexivity.
(* FALL 5 *)
elim H; clear H; intros.
exists (e0 ++ c :: nil).
split.
assumption.
assumption.
Qed.
