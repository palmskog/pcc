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
  apply exec_trans with (e := nil).
  apply trans_xx.
  apply exec_x.  
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
 split.
 - repeat (
    rewrite rearrange;
    repeat rewrite app_comm_cons;
    apply exec_trans;
    auto with transitions;
    simpl).  
   apply exec_trans with (e := nil).
   * by apply trans_xx.
   * by apply exec_x.
 - by done.
Qed.

Lemma rev_case : forall (e : list configuration), e = nil \/ (exists e', exists c, e = e' ++ (c :: nil)).
Proof.
 elim/rev_ind => [|c e].
 - by left.
 - move => H.
   elim: H => H.
   * right.
     rewrite H.
     exists nil.
     exists c.
     done.
   * right.
     elim: H => e' H.
     elim: H => c' H.
     rewrite H {H}.
     exists (e' ++ c' :: nil).
     exists c.
     by rewrite app_ass -app_comm_cons.
Qed.

Lemma b_updates_ignores_x : forall `(execution e), b_updates (e ++ x :: nil) = b_updates e.
Admitted.

Lemma b_updates_ignores_an : forall `(execution e) (n : nat), b_updates (e ++ a n :: nil) = b_updates e.
Admitted.

Lemma exists_exec_with_eq_bs :
  forall `(execution e), exists e', (execution e') /\ b_updates e = a_updates e'.
Proof.
 elim/rev_ind => [H|c e].
 - exists nil.
   split.
   * by apply exec_nil.
   * by done.
 - pose proof rev_case e.
   elim: H => H.
   * rewrite H {H}.
     case:c => [H0 H1|n H0 H1|n H0 H1|n H0 H1|n H0 H1].
     + by exists (x :: nil); split; [ apply exec_x | done].
     + by exists nil; split; [ apply exec_nil | done ].
     + by exists nil; split; [ apply exec_nil | done ].
     + exists (a n :: nil); split.
       - inversion H1.
         by apply exec_a.
       - by done.
     + exists (a n :: nil); split.
       - inversion H1.
         by apply exec_a.
       - by done.
   * elim: H => e' H.
     elim: H => c' H.
     rewrite H {H}.
     move => IH H.
     have H0: (e' ++ c' :: nil) ++ c :: nil = e' ++ (c' :: c :: nil) by rewrite app_ass -app_comm_cons.
     rewrite H0 in H.
     rewrite H0 {H0}.
     inversion H.
     + by exists nil; split; [ apply exec_nil | done ].
     + by exists nil; split; [ apply exec_nil | done ].
     + by exists (x :: nil); split; [ apply exec_x | done ].
     + have H2: (e0 ++ (c0 :: c'0 :: nil) = (e0 ++ c0 :: nil) ++ c'0 :: nil) by rewrite -ass_app -app_comm_cons.
       rewrite H2 {H2} in H1.
       have H2: (e' ++ (c' :: c :: nil) = (e' ++ c' :: nil) ++ c :: nil) by rewrite -ass_app -app_comm_cons.
       rewrite H2 {H2} in H1.
       apply app_inj_tail in H1.
       elim: H1 => H1 H2.
       apply app_inj_tail in H1.
       elim: H1 => H1 H3.
       rewrite H2 in trans0.
       rewrite H2 {H2 c'0}.
       rewrite H1 in execution0.
       rewrite H1 {H1 e0}.
       rewrite H3 in execution0.
       rewrite H3 in trans0.
       rewrite H3 {H3 c0}.
       have H0: execution (e' ++ c' :: nil) by apply execution0.
       apply IH in H0.
       elim: H0 => e0 H0 {IH}.
       elim: H0 => H0 H1.
       move: H H1 trans0.       
       case c => [H H1 trans0|n H H1 trans0|||].
       - exists e0; split; first done.
         have H2: e' ++ c' :: x :: nil = (e' ++ c' :: nil) ++ x :: nil by rewrite -ass_app -app_comm_cons.
         rewrite H2 {H2}.         
         by rewrite b_updates_ignores_x. 
       - exists e0; split; first done.
         rewrite -H1 {H1}.
         have H2: e' ++ c' :: a n :: nil = (e' ++ c' :: nil) ++ a n :: nil by rewrite -ass_app -app_comm_cons.
         rewrite H2 {H2}.
         


inversion trans0.
         subst.
         exists e0; split; first done.
         rewrite -H1 {H1}.
         Focus 2.
       - 
       
       rewrite 

       rew
       rewrite -ass_app.
       rewrite -app_comm_cons.

apply app_inj_tail in H1.
     + have H2: e' = e'.
       

move => IH.
     
     rewrite H {H} => H.
     
     
   
   
       exists (c :: nil).
   split; first by rewrite /= in H1; apply H1.
   

case H: e => [|c' e0].
   * 

Admitted.
