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


Lemma b_updates_compositional : forall (e : list configuration) (c : configuration), b_updates (e ++ c :: nil) = b_updates e ++ b_updates (c :: nil).
elim => [c|c e IH c']; first done.
case: c => [|n|n|n|n]; case: c' => [|n0|n0|n0|n0]; (try rewrite /= IH -app_nil_end /=); (try reflexivity); (try rewrite -IH /=); try reflexivity.
- by rewrite /= IH.
- by rewrite /= IH.
- by rewrite /= IH.
- by rewrite /= IH.
Qed.

Lemma a_updates_compositional : forall (e : list configuration) (c : configuration), a_updates (e ++ c :: nil) = a_updates e ++ a_updates (c :: nil).
elim => [c|c e IH c']; first done.
case: c => [|n|n|n|n]; case: c' => [|n0|n0|n0|n0]; (try rewrite /= IH -app_nil_end /=); (try reflexivity); (try rewrite -IH /=); try reflexivity.
- by rewrite /= IH.
- by rewrite /= IH.
- by rewrite /= IH.
- by rewrite /= IH.
Qed.


Lemma b_updates_ignores_x : forall `(execution e), b_updates (e ++ x :: nil) = b_updates e.
Proof.
Admitted.

Lemma b_updates_ignores_an : forall `(execution e) (n : nat), b_updates (e ++ a n :: nil) = b_updates e.
Admitted.

Lemma b_updates_ignores_a'n : forall `(execution e) (n : nat), b_updates (e ++ a' n :: nil) = b_updates e.
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
       case c => [H H1 trans0|n H H1 trans0|n H H1 trans0|n H H1 trans0|n H H1 trans0].
       - exists e0; split; first done.
         have H2: e' ++ c' :: x :: nil = (e' ++ c' :: nil) ++ x :: nil by rewrite -ass_app -app_comm_cons.
         rewrite H2 {H2}.         
         by rewrite b_updates_ignores_x. 
       - exists e0; split; first done.
         rewrite -H1 {H1}.
         have H2: e' ++ c' :: a n :: nil = (e' ++ c' :: nil) ++ a n :: nil by rewrite -ass_app -app_comm_cons.
         rewrite H2 {H2}.
         by rewrite b_updates_ignores_an.
       - exists e0; split; first done.
         rewrite -H1 {H1}.
         have H2: e' ++ c' :: a' n :: nil = (e' ++ c' :: nil) ++ a' n :: nil by rewrite -ass_app -app_comm_cons.
         rewrite H2 {H2}.
         by rewrite b_updates_ignores_a'n.
       - inversion trans0; subst.
         pose proof rev_case e0.
         elim: H2 => H2.
         * rewrite H2 /= in H1.          
           exists (a n :: nil).
           split; first by apply exec_a.
           rewrite /=.
           have H4: e' ++ a n :: b n :: nil = (e' ++ a n :: nil) ++ (b n :: nil) by rewrite -ass_app -app_comm_cons.
           by rewrite H4 b_updates_compositional H1.
         * elim: H2 => e1 H2.
           elim: H2.
           case => [H2|n0 H2|n0 H2|n0 H2|n0 H2].
           + rewrite H2 in H0.
             rewrite H2 {H2 e0} in H1.
             exists (e1 ++ x :: a n :: nil).
             split; first by apply exec_trans; [ apply trans_xa | done ].
             have H2: e' ++ a n :: b n :: nil = (e' ++ a n :: nil) ++ b n :: nil by rewrite -ass_app -app_comm_cons.
             rewrite H2 {H2}.
             rewrite b_updates_compositional H1 /=.
             have H2: e1 ++ x :: a n :: nil = (e1 ++ x :: nil) ++ a n :: nil by rewrite -ass_app -app_comm_cons.
             rewrite H2 {H2}.
             rewrite a_updates_compositional.
             rewrite a_updates_compositional.
             rewrite a_updates_compositional.
             done.
           + rewrite H2 in H0.
             rewrite H2 {H2 e0} in H1.
             exists (e1 ++ a n0 :: b n0 :: a n :: nil).
             have H2: e1 ++ a n0 :: b n0 :: a n :: nil = (e1 ++ a n0 :: nil) ++ b n0 :: a n :: nil by rewrite -ass_app -app_comm_cons.
             rewrite H2 {H2}. 
             split.
             - apply exec_trans.
               apply trans_ba.
               have H3: (e1 ++ a n0 :: nil) ++ b n0 :: nil = e1 ++ a n0 :: b n0 :: nil by rewrite -ass_app -app_comm_cons.
               rewrite H3 {H3}.
               by apply exec_trans; first by apply trans_ab.
             - have H2: (e1 ++ a n0 :: nil) ++ b n0 :: a n :: nil = (e1 ++ a n0 :: b n0 :: nil) ++ a n :: nil.
               rewrite -ass_app.
               rewrite -ass_app.
               rewrite -app_comm_cons.
               rewrite -app_comm_cons.
               rewrite -app_comm_cons.               
               by rewrite app_comm_cons.
               rewrite H2 {H2}.
               have H2: e' ++ a n :: b n :: nil = (e' ++ a n :: nil) ++ b n :: nil by rewrite -ass_app -app_comm_cons.
               rewrite H2 {H2}.
               rewrite b_updates_compositional a_updates_compositional /=.
               have H2: e1 ++ a n0 :: b n0 :: nil = (e1 ++ a n0 :: nil) ++ b n0 :: nil by rewrite -ass_app -app_comm_cons.
               by rewrite H2 a_updates_compositional {H2} H1 /= -app_nil_end.
           + rewrite H2 in H0.
             rewrite H2 {H2 e0} in H1.
             exists (e1 ++ a' n0 :: a n :: nil).
             split; first by apply exec_trans; [ apply trans_a'a | done ].
             have H2: e' ++ a n :: b n :: nil = (e' ++ a n :: nil) ++ b n :: nil by rewrite -ass_app -app_comm_cons.
             rewrite H2 {H2}.
             rewrite b_updates_compositional /= H1.
             have H2: e1 ++ a' n0 :: a n :: nil = (e1 ++ a' n0 :: nil) ++ a n :: nil by rewrite -ass_app -app_comm_cons.
             rewrite H2 {H2}.
             by rewrite a_updates_compositional a_updates_compositional a_updates_compositional /=.
           + rewrite H2 in H0.
             rewrite H2 {H2 e0} in H1.
             exists (e1 ++ b n0 :: a n :: nil).
             split; first by apply exec_trans; [ apply trans_ba | done ].
             have H2: e' ++ a n :: b n :: nil = (e' ++ a n :: nil) ++ b n :: nil by rewrite -ass_app -app_comm_cons.
             rewrite H2 {H2}.
             rewrite b_updates_compositional /= H1.
             have H2: e1 ++ b n0 :: a n :: nil = (e1 ++ b n0 :: nil) ++ a n :: nil by rewrite -ass_app -app_comm_cons.
             rewrite H2 {H2}.
             by rewrite a_updates_compositional a_updates_compositional a_updates_compositional /=.
           + rewrite H2 in H0.
             rewrite H2 {H2 e0} in H1.
             rewrite b_updates_compositional a_updates_compositional /= -app_nil_end -app_nil_end in H1.
             exists (e1 ++ a n :: b n :: nil).
             inversion H0; first by contradict H3; apply app_cons_not_nil.
             have H4: a n1 :: nil = nil ++ a n1 :: nil by done.
             rewrite H4 {H4} in H3.
             apply app_inj_tail in H3.
             by elim: H3 => H3 H4.
             have H4: x :: nil = nil ++ x :: nil by done.
             rewrite H4 {H4} in H3.
             apply app_inj_tail in H3.
             by elim: H3 => H3 H4.
             have H4: e0 ++ c0 :: c' :: nil = (e0 ++ c0 :: nil) ++ c' :: nil by rewrite -ass_app -app_comm_cons.
             rewrite H4 {H4} in H3.
             apply app_inj_tail in H3.
             elim: H3 => H3 H4.
             rewrite H3 in execution1.
             rewrite H4 {H4} in trans1.             
             split.
             - apply exec_trans; first by apply trans_ab.
               move: H3 trans1.
               case c0 => [H2 H3|n1 H2 H3|n1 H2 H3|n1 H2 H3|n1 H2 H3].
               * rewrite -H2.
                 have H4: (e0 ++ x :: nil) ++ a n :: nil = e0 ++ x :: a n :: nil by rewrite -ass_app -app_comm_cons.
                 rewrite H4 {H4}.
                 apply exec_trans; first by apply trans_xa.
                 by rewrite -H2 in execution1.
               * by inversion H3.
               * rewrite -H2.
                 have H4: (e0 ++ a' n1 :: nil) ++ a n :: nil = e0 ++ a' n1 :: a n :: nil by rewrite -ass_app -app_comm_cons.
                 rewrite H4 {H4}.
                 apply exec_trans; first by apply trans_a'a.
                 by rewrite H2.
               * rewrite -H2.
                 have H4: (e0 ++ b n1 :: nil) ++ a n :: nil = e0 ++ b n1 :: a n :: nil by rewrite -ass_app -app_comm_cons.
                 rewrite H4 {H4}.
                 inversion H3; subst.
                 by apply exec_trans; first by apply trans_ba.
               * by inversion H3.
            - have H4: e' ++ a n :: b n :: nil = (e' ++ a n :: nil) ++ b n :: nil by rewrite -ass_app -app_comm_cons.
              rewrite H4 {H4} b_updates_compositional b_updates_compositional /= -app_nil_end.
              have H4: e1 ++ a n :: b n :: nil = (e1 ++ a n :: nil) ++ b n :: nil by rewrite -ass_app -app_comm_cons.
              by rewrite H4 {H4} a_updates_compositional a_updates_compositional /= -app_nil_end H1.
       - inversion trans0; subst.
         pose proof rev_case e0.
         elim: H2 => H2.
         * rewrite H2 /= in H1.
           exists (a n :: nil).
           split; first by apply exec_a.
           have H3: e' ++ x :: b' n :: nil = (e' ++ x :: nil) ++ b' n :: nil by rewrite -ass_app -app_comm_cons.
           rewrite H3 {H3}.                     
           by rewrite b_updates_compositional /= H1.
         * elim: H2 => e1 H2.
           elim: H2.
           case => [H2|n0 H2|n0 H2|n0 H2|n0 H2].
           + rewrite H2 in H1.
             rewrite b_updates_compositional a_updates_compositional /= -app_nil_end -app_nil_end in H1.
             rewrite H2 in H0.
             exists (e1 ++ x :: a n :: nil).
             split; first by apply exec_trans; [ apply trans_xa | done ].
             have H3: e' ++ x :: b' n :: nil = (e' ++ x :: nil) ++ b' n :: nil by rewrite -ass_app -app_comm_cons.
             rewrite H3 {H3}.
             have H3: e1 ++ x :: a n :: nil = (e1 ++ x :: nil) ++ a n :: nil by rewrite -ass_app -app_comm_cons.
             rewrite H3 {H3}.
             by rewrite b_updates_compositional b_updates_compositional a_updates_compositional a_updates_compositional H1.
           + rewrite H2 in H1.
             exists (e1 ++ a n0 :: b n0 :: a n :: nil).
             split.
             - have H3: e1 ++ a n0 :: b n0 :: a n :: nil = (e1 ++ a n0 :: nil) ++ b n0 :: a n :: nil by rewrite -ass_app -app_comm_cons.
               rewrite H3 {H3}.
               apply exec_trans.
               apply trans_ba.
               have H3: (e1 ++ a n0 :: nil) ++ b n0 :: nil = (e1 ++ a n0 :: b n0 :: nil) by rewrite app_ass -app_comm_cons.
               rewrite H3 {H3}.
               rewrite H2 in H0.
               by apply exec_trans; [ apply trans_ab | done ].
             - have H3: e' ++ x :: b' n :: nil = (e' ++ x :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
               rewrite H3 {H3} b_updates_compositional /=.
               have H3: e1 ++ a n0 :: b n0 :: a n :: nil = (e1 ++ a n0 :: b n0 :: nil) ++ a n :: nil  by rewrite app_ass -app_comm_cons.
               rewrite H3 a_updates_compositional /= {H3}.
               have H3: e1 ++ a n0 :: b n0 :: nil = (e1 ++ a n0 :: nil) ++ b n0 :: nil by rewrite app_ass -app_comm_cons.         
               by rewrite H3 a_updates_compositional /= -app_nil_end H1 {H3}.
           + rewrite H2 in H1.
             rewrite H2 in H0.
             exists (e1 ++ a' n0 :: a n :: nil).
             split; first by apply exec_trans; [ apply trans_a'a | done ].
             have H3: e' ++ x :: b' n :: nil = (e' ++ x :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
             rewrite H3 b_updates_compositional /= {H3}.
             have H3: e1 ++ a' n0 :: a n :: nil = (e1 ++ a' n0 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.
             by rewrite H3 a_updates_compositional H1.
           + rewrite H2 in H1.
             rewrite H2 in H0.
             exists (e1 ++ b n0 :: a n :: nil).
             split; first by apply exec_trans; [ apply trans_ba | done ].
             have H3: e' ++ x :: b' n :: nil = (e' ++ x :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
             rewrite H3 b_updates_compositional /= {H3}.
             have H3: e1 ++ b n0 :: a n :: nil = (e1 ++ b n0 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.
             by rewrite H3 a_updates_compositional H1.
           + rewrite H2 in H1.
             rewrite H2 in H0.
             rewrite b_updates_compositional a_updates_compositional /= -app_nil_end -app_nil_end in H1.
             exists (e1 ++ a n :: nil).
             inversion H0.
             - by contradict H4; apply app_cons_not_nil.
             - have H5: a n1 :: nil = nil ++ a n1 :: nil by done.
               rewrite H5 {H5} in H4.
               apply app_inj_tail in H4.
               by elim: H4 => H4 H5.
             - have H5: x :: nil = nil ++ x :: nil by done.
               rewrite H5 {H5} in H4.
               apply app_inj_tail in H4.
               by elim: H4 => H4 H5.
               have H5: e2 ++ c0 :: c' :: nil = (e2 ++ c0 :: nil) ++ c' :: nil by rewrite app_ass -app_comm_cons.
               rewrite H5 {H5} in H4.
               apply app_inj_tail in H4.
               elim: H4 => H4 H5.
               rewrite H5 in trans1.
               rewrite -H4 in H1.
               move: H4 execution1 trans1 H1.
               case c0 => [H3 H4 H6 H7|n1 H3 H4 H6 H7|n1 H3 H4 H6 H7|n1 H3 H4 H6 H7|n1 H3 H4 H6 H7].
               * rewrite -H3.
                 split.
                 + have H8: (e2 ++ x :: nil) ++ a n :: nil = e2 ++ x :: a n :: nil by rewrite app_ass -app_comm_cons.
                   rewrite H8 {H8}.
                   by apply exec_trans; first by apply trans_xa.
                 + have H8: e' ++ x :: b' n :: nil = (e' ++ x :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
                   rewrite H8 {H8}.
                   by rewrite b_updates_compositional b_updates_compositional a_updates_compositional -app_nil_end H7.
               * by inversion H6.
               * rewrite -H3.
                 split.
                 + have H8: (e2 ++ a' n1 :: nil) ++ a n :: nil = e2 ++ a' n1 :: a n :: nil by rewrite app_ass -app_comm_cons.
                   rewrite H8 {H8}.
                   by apply exec_trans; first by apply trans_a'a.
                 + have H8: e' ++ x :: b' n :: nil = (e' ++ x :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
                   rewrite H8 {H8}.
                   by rewrite b_updates_compositional b_updates_compositional a_updates_compositional -app_nil_end H7.
               * rewrite -H3.
                 split.
                 + have H8: (e2 ++ b n1 :: nil) ++ a n :: nil = e2 ++ b n1 :: a n :: nil by rewrite app_ass -app_comm_cons.
                   rewrite H8 {H8}.
                   by apply exec_trans; first by apply trans_ba.
                 + have H8: e' ++ x :: b' n :: nil = (e' ++ x :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
                   rewrite H8 {H8}.
                   by rewrite b_updates_compositional b_updates_compositional a_updates_compositional -app_nil_end H7.
               * by inversion H6.
       - pose proof rev_case e0.
         elim: H2 => H2.
         * rewrite H2 /= in H1.
           exists (a n :: nil).
           split; first by apply exec_a.
           have H3: e' ++ a' n0 :: b' n :: nil = (e' ++ a' n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
           rewrite H3 {H3}.
           by rewrite b_updates_compositional H1.
        * elim: H2 => e1 H2.
          elim: H2.
          case => [H2|n1 H2|n1 H2|n1 H2|n1 H2].
          + exists (e1 ++ x :: a n :: nil).
            rewrite H2 in H0.
            rewrite H2 in H1.
            split; first by apply exec_trans; [ apply trans_xa | done ].
            have H3: e' ++ a' n0 :: b' n :: nil = (e' ++ a' n0 :: nil) ++ b' n :: nil by  rewrite app_ass -app_comm_cons.
            rewrite H3 {H3}.
            have H3: e1 ++ x :: a n :: nil = (e1 ++ x :: nil) ++ a n :: nil by  rewrite app_ass -app_comm_cons.
            rewrite H3 {H3}.
            by rewrite b_updates_compositional a_updates_compositional H1.
          + rewrite H2 in H0.
            rewrite H2 in H1.
            inversion H0.
            * by contradict H4; apply app_cons_not_nil.
            * have H5: a n2 :: nil = nil ++ a n2 :: nil by done.
              rewrite H5 {H5} in H4.
              apply app_inj_tail in H4.
              elim: H4 => H4 H5.
              inversion H5.
              rewrite -H4 /= in H1.
              exists (a n1 :: b n1 :: a n :: nil).               
              split.
              - have H7: a n1 :: b n1 :: a n :: nil = (a n1 :: nil) ++ (b n1 :: a n :: nil) by done.
                rewrite H7 {H7}.               
                apply exec_trans.
                apply trans_ba.
                have H7: (a n1 :: nil) ++ b n1 :: nil = nil ++ (a n1 :: b n1 :: nil) by done.
                rewrite H7 {H7}.               
                apply exec_trans.
                apply trans_ab.
                by apply exec_a.
              - have H7: e' ++ a' n0 :: b' n :: nil = (e' ++ a' n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
                by rewrite H7 b_updates_compositional H1 {H7}.
            * have H5: x :: nil = nil ++ x :: nil by done.
              rewrite H5 {H5} in H4.   
              apply app_inj_tail in H4.
              by elim: H4 => H4 H5. 
            * have H5: e2 ++ c0 :: c' :: nil = (e2 ++ c0 :: nil) ++ c' :: nil by rewrite app_ass -app_comm_cons.
              rewrite H5 {H5} in H4.
              apply app_inj_tail in H4.
              elim: H4 => H4 H5.
              rewrite H5 {H5 c'} in trans1.
              rewrite  b_updates_compositional -app_nil_end /= in H1.
              exists (e1 ++ a n1 :: b n1 :: a n :: nil).
              
              split.
              have H3: e1 ++ a n1 :: b n1 :: a n :: nil = (e1 ++ a n1 :: nil) ++ b n1 :: a n :: nil by rewrite app_ass -app_comm_cons.
              rewrite H3 {H3}.
              apply exec_trans.
              apply trans_ba.
              have H3: (e1 ++ a n1 :: nil) ++ b n1 :: nil = e1 ++ a n1 :: b n1 :: nil by rewrite app_ass -app_comm_cons.
              rewrite H3 {H3}.
              apply exec_trans.
              by apply trans_ab.
              done.
              
              have H3: e' ++ a' n0 :: b' n :: nil = (e' ++ a' n0 :: nil) ++  b' n :: nil by rewrite app_ass -app_comm_cons.
              rewrite H3 b_updates_compositional b_updates_compositional -app_nil_end /= {H3}.
              have H3: e1 ++ a n1 :: b n1 :: a n :: nil = (e1 ++ a n1 :: b n1 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.
              rewrite H3 a_updates_compositional /= {H3}.
              have H3: e1 ++ a n1 :: b n1 :: nil = (e1 ++ a n1 :: nil) ++ b n1 :: nil by rewrite app_ass -app_comm_cons.
              rewrite H3 a_updates_compositional -app_nil_end /= {H3}.
              by rewrite H1.                          
            
            rewrite H2 in H0.
            rewrite H2 in H1.
            rewrite b_updates_compositional -app_nil_end /= in H1.
            exists (e1 ++ a' n1 :: a n :: nil).
            split.
            by apply exec_trans; first by apply trans_a'a.
            have H3: e' ++ a' n0 :: b' n :: nil = (e' ++ a' n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
            rewrite H3 b_updates_compositional b_updates_compositional -app_nil_end /= {H3}.
            have H3: e1 ++ a' n1 :: a n :: nil = (e1 ++ a' n1 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.
            rewrite H3 {H3}.
            by rewrite a_updates_compositional H1.
            
            rewrite H2 in H1.
            rewrite H2 in H0.
            exists (e1 ++ b n1 :: a n :: nil).
            rewrite a_updates_compositional -app_nil_end /= in H1.
            split.
            apply exec_trans.
            apply trans_ba.
            done.
            
            have H3: e' ++ a' n0 :: b' n :: nil = (e' ++ a' n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
            rewrite H3 b_updates_compositional /= {H3}.
            have H3: e1 ++ b n1 :: a n :: nil = (e1 ++ b n1 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.       
            rewrite H3 a_updates_compositional a_updates_compositional -app_nil_end /= {H3}.
            by rewrite H1.
                        
            rewrite H2 in H0.
            rewrite H2 in H1.
            inversion H0; first by contradict H4; apply app_cons_not_nil.
            have H5: a n2 :: nil = nil ++ a n2 :: nil by done.
            rewrite H5 {H5} in H4.
            apply app_inj_tail in H4.
            by elim: H4 => H4 H5.
            have H5: x :: nil = nil ++ x :: nil by done.
            rewrite H5 {H5} in H4.
            apply app_inj_tail in H4.
            by elim: H4 => H4 H5.
            have H5: e2 ++ c0 :: c' :: nil = (e2 ++ c0 :: nil) ++ c' :: nil by rewrite app_ass -app_comm_cons.
            rewrite H5 {H5} in H4.            
            apply app_inj_tail in H4.
            elim: H4 => H4 H5.
            rewrite H5 {H5 c'} in trans1.
            move: execution1 H4 trans1.
            case c0 => [H3 H4 H5|n2 H3 H4 H5|n2 H3 H4 H5|n2 H3 H4 H5|n2 H3 H4 H5].
            - exists (e2 ++ x :: a n :: nil).
              split.
              apply exec_trans.
              apply trans_xa.
              done.
              have H6: e2 ++ x :: a n :: nil = (e2 ++ x :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.
              rewrite H6 H4 {H6}.
              rewrite a_updates_compositional -app_nil_end in H1.
              rewrite a_updates_compositional /=.
              have H6: e' ++ a' n0 :: b' n :: nil = (e' ++ a' n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
              by rewrite H6 b_updates_compositional H1.
              
              by inversion H5.

              exists (e2 ++ a' n2 :: a n :: nil).
              split.
              apply exec_trans.
              apply trans_a'a.
              done.
              have H6: e' ++ a' n0 :: b' n :: nil = (e' ++ a' n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
              rewrite H6 b_updates_compositional /= {H6}.
              have H6: e2 ++ a' n2 :: a n :: nil = (e2 ++ a' n2 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons. 
              rewrite H6 a_updates_compositional H4 /= {H6}.
              by rewrite H1 a_updates_compositional -app_nil_end.
              
              exists (e2 ++ b n2 :: a n :: nil).
              split.
              apply exec_trans.
              apply trans_ba.
              done.
              
              have H6: e' ++ a' n0 :: b' n :: nil = (e' ++ a' n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
              rewrite H6 b_updates_compositional /= {H6}.
              have H6: e2 ++ b n2 :: a n :: nil = (e2 ++ b n2 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.
              rewrite H6 H4 a_updates_compositional /=.
              by rewrite H1 a_updates_compositional -app_nil_end.
              
              by inversion H5.

         - pose proof rev_case e0.
         elim: H2 => H2.
         * rewrite H2 /= in H1.
           exists (a n :: nil).
           split; first by apply exec_a.
           have H3: e' ++ b n0 :: b' n :: nil = (e' ++ b n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
           rewrite H3 {H3}.
           by rewrite b_updates_compositional H1.
        * elim: H2 => e1 H2.
          elim: H2.
          case => [H2|n1 H2|n1 H2|n1 H2|n1 H2].
          + exists (e1 ++ x :: a n :: nil).
            rewrite H2 in H0.
            rewrite H2 in H1.
            split; first by apply exec_trans; [ apply trans_xa | done ].
            have H3: e' ++ b n0 :: b' n :: nil = (e' ++ b n0 :: nil) ++ b' n :: nil by  rewrite app_ass -app_comm_cons.
            rewrite H3 {H3}.
            have H3: e1 ++ x :: a n :: nil = (e1 ++ x :: nil) ++ a n :: nil by  rewrite app_ass -app_comm_cons.
            rewrite H3 {H3}.
            by rewrite b_updates_compositional a_updates_compositional H1.
          + rewrite H2 in H0.
            rewrite H2 in H1.
            inversion H0.
            * by contradict H4; apply app_cons_not_nil.
            * have H5: a n2 :: nil = nil ++ a n2 :: nil by done.
              rewrite H5 {H5} in H4.
              apply app_inj_tail in H4.
              elim: H4 => H4 H5.
              inversion H5.
              rewrite -H4 /= in H1.
              exists (a n1 :: b n1 :: a n :: nil).               
              split.
              - have H7: a n1 :: b n1 :: a n :: nil = (a n1 :: nil) ++ (b n1 :: a n :: nil) by done.
                rewrite H7 {H7}.               
                apply exec_trans.
                apply trans_ba.
                have H7: (a n1 :: nil) ++ b n1 :: nil = nil ++ (a n1 :: b n1 :: nil) by done.
                rewrite H7 {H7}.               
                apply exec_trans.
                apply trans_ab.
                by apply exec_a.
              - have H7: e' ++ b n0 :: b' n :: nil = (e' ++ b n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
                by rewrite H7 b_updates_compositional H1 {H7}.
            * have H5: x :: nil = nil ++ x :: nil by done.
              rewrite H5 {H5} in H4.   
              apply app_inj_tail in H4.
              by elim: H4 => H4 H5. 
            * have H5: e2 ++ c0 :: c' :: nil = (e2 ++ c0 :: nil) ++ c' :: nil by rewrite app_ass -app_comm_cons.
              rewrite H5 {H5} in H4.
              apply app_inj_tail in H4.
              elim: H4 => H4 H5.
              rewrite H5 {H5 c'} in trans1.
              rewrite  b_updates_compositional /= in H1.
              exists (e1 ++ a n1 :: b n1 :: a n :: nil).
              
              split.
              have H3: e1 ++ a n1 :: b n1 :: a n :: nil = (e1 ++ a n1 :: nil) ++ b n1 :: a n :: nil by rewrite app_ass -app_comm_cons.
              rewrite H3 {H3}.
              apply exec_trans.
              apply trans_ba.
              have H3: (e1 ++ a n1 :: nil) ++ b n1 :: nil = e1 ++ a n1 :: b n1 :: nil by rewrite app_ass -app_comm_cons.
              rewrite H3 {H3}.
              apply exec_trans.
              by apply trans_ab.
              done.
              
              have H3: e' ++ b n0 :: b' n :: nil = (e' ++ b n0 :: nil) ++  b' n :: nil by rewrite app_ass -app_comm_cons.
              rewrite H3 b_updates_compositional b_updates_compositional /= {H3}.
              have H3: e1 ++ a n1 :: b n1 :: a n :: nil = (e1 ++ a n1 :: b n1 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.
              rewrite H3 a_updates_compositional /= {H3}.
              have H3: e1 ++ a n1 :: b n1 :: nil = (e1 ++ a n1 :: nil) ++ b n1 :: nil by rewrite app_ass -app_comm_cons.
              rewrite H3 a_updates_compositional -app_nil_end /= {H3}.
              by rewrite H1.                          
            
            rewrite H2 in H0.
            rewrite H2 in H1.
            rewrite b_updates_compositional /= in H1.
            exists (e1 ++ a' n1 :: a n :: nil).
            split.
            by apply exec_trans; first by apply trans_a'a.
            have H3: e' ++ b n0 :: b' n :: nil = (e' ++ b n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
            rewrite H3 b_updates_compositional b_updates_compositional  /= {H3}.
            have H3: e1 ++ a' n1 :: a n :: nil = (e1 ++ a' n1 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.
            rewrite H3 {H3}.
            by rewrite a_updates_compositional H1.
            
            rewrite H2 in H1.
            rewrite H2 in H0.
            exists (e1 ++ b n1 :: a n :: nil).
            rewrite a_updates_compositional -app_nil_end /= in H1.
            split.
            apply exec_trans.
            apply trans_ba.
            done.
            
            have H3: e' ++ b n0 :: b' n :: nil = (e' ++ b n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
            rewrite H3 b_updates_compositional /= {H3}.
            have H3: e1 ++ b n1 :: a n :: nil = (e1 ++ b n1 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.       
            rewrite H3 a_updates_compositional a_updates_compositional -app_nil_end /= {H3}.
            by rewrite H1.
                        
            rewrite H2 in H0.
            rewrite H2 in H1.
            inversion H0; first by contradict H4; apply app_cons_not_nil.
            have H5: a n2 :: nil = nil ++ a n2 :: nil by done.
            rewrite H5 {H5} in H4.
            apply app_inj_tail in H4.
            by elim: H4 => H4 H5.
            have H5: x :: nil = nil ++ x :: nil by done.
            rewrite H5 {H5} in H4.
            apply app_inj_tail in H4.
            by elim: H4 => H4 H5.
            have H5: e2 ++ c0 :: c' :: nil = (e2 ++ c0 :: nil) ++ c' :: nil by rewrite app_ass -app_comm_cons.
            rewrite H5 {H5} in H4.            
            apply app_inj_tail in H4.
            elim: H4 => H4 H5.
            rewrite H5 {H5 c'} in trans1.
            move: execution1 H4 trans1.
            case c0 => [H3 H4 H5|n2 H3 H4 H5|n2 H3 H4 H5|n2 H3 H4 H5|n2 H3 H4 H5].
            - exists (e2 ++ x :: a n :: nil).
              split.
              apply exec_trans.
              apply trans_xa.
              done.
              have H6: e2 ++ x :: a n :: nil = (e2 ++ x :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.
              rewrite H6 H4 {H6}.
              rewrite a_updates_compositional -app_nil_end in H1.
              rewrite a_updates_compositional /=.
              have H6: e' ++ b n0 :: b' n :: nil = (e' ++ b n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
              by rewrite H6 b_updates_compositional H1.
              
              by inversion H5.

              exists (e2 ++ a' n2 :: a n :: nil).
              split.
              apply exec_trans.
              apply trans_a'a.
              done.
              have H6: e' ++ b n0 :: b' n :: nil = (e' ++ b n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
              rewrite H6 b_updates_compositional /= {H6}.
              have H6: e2 ++ a' n2 :: a n :: nil = (e2 ++ a' n2 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons. 
              rewrite H6 a_updates_compositional H4 /= {H6}.
              by rewrite H1 a_updates_compositional -app_nil_end.
              
              exists (e2 ++ b n2 :: a n :: nil).
              split.
              apply exec_trans.
              apply trans_ba.
              done.
              
              have H6: e' ++ b n0 :: b' n :: nil = (e' ++ b n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
              rewrite H6 b_updates_compositional /= {H6}.
              have H6: e2 ++ b n2 :: a n :: nil = (e2 ++ b n2 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.
              rewrite H6 H4 a_updates_compositional /=.
              by rewrite H1 a_updates_compositional -app_nil_end.
              
              by inversion H5.
Qed.
              
            
