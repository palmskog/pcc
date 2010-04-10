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
elim => [c|c e IH c']; first done.
case: c => [|n|n|n|n]; case: c' => [|n0|n0|n0|n0]; (try rewrite /= IH -app_nil_end /=); (try reflexivity); (try rewrite -IH /=); try reflexivity.
- by rewrite /= IH.
- by rewrite /= IH.
- by rewrite /= IH.
- by rewrite /= IH.
Qed.

Lemma a_updates_comp : forall (e : list configuration) (c : configuration), a_updates (e ++ c :: nil) = a_updates e ++ a_updates (c :: nil).
elim => [c|c e IH c']; first done.
case: c => [|n|n|n|n]; case: c' => [|n0|n0|n0|n0]; (try rewrite /= IH -app_nil_end /=); (try reflexivity); (try rewrite -IH /=); try reflexivity.
- by rewrite /= IH.
- by rewrite /= IH.
- by rewrite /= IH.
- by rewrite /= IH.
Qed.

Lemma coalesce_tail : forall (e : list configuration) (c c' : configuration), (e ++ c :: nil) ++ c' :: nil = e ++ c :: c' :: nil.
Proof. by move => e c c'; rewrite -ass_app -app_comm_cons. Qed.

Lemma coalesce_tail_long : forall (e : list configuration) (c c' c'' : configuration), (e ++ c :: c' :: nil) ++ c'' :: nil = e ++ c :: c' :: c'' :: nil.
Proof. by move => e c c' c''; rewrite -ass_app -app_comm_cons. Qed.

Lemma coalesce_long_tail : forall (e : list configuration) (c c' c'' : configuration), (e ++ c :: nil) ++ c' :: c'' :: nil = e ++ c :: c' :: c'' :: nil.
Proof. by move => e c c' c''; rewrite -ass_app -app_comm_cons. Qed.

Lemma nil_front : forall (e : list configuration), e = nil ++ e.
Proof. done. Qed.

Lemma exists_exec_with_eq_bs : forall `(execution e), exists e', (execution e') /\ b_updates e = a_updates e'.
Proof.
 elim/rev_ind => [H|c e]; first by exists nil; split; [ apply exec_nil | done ].
 pose proof rev_case e as H; elim: H => H.
 - rewrite H {H}.
   case: c => [|n|n|n|n] H0 H1.
   * by exists (x :: nil); split; [ apply exec_x | done ].
   * by exists nil; split; [ apply exec_nil | done ].
   * by exists nil; split; [ apply exec_nil | done ].
   * by exists (a n :: nil); split; last done; inversion H1; apply exec_a.
   * by exists (a n :: nil); split; last done; inversion H1; apply exec_a.
 - elim: H => e' H.
   elim: H => c' H.
   rewrite H {H} => IH.
   rewrite coalesce_tail => H.
   inversion H.
   * by exists nil; split; [ apply exec_nil | done ].
   * by exists nil; split; [ apply exec_nil | done ].
   * by exists (x :: nil); split; [ apply exec_x | done ].
   * do 2!rewrite -coalesce_tail in H1.     
     apply app_inj_tail in H1.
     elim: H1 => H1 H2.
     apply app_inj_tail in H1.
     elim: H1 => H1 H3.
     move: execution0 trans0. 
     rewrite H1 H2 H3 {H1 H2 H3 e e0 c'0 c0} => execution0 trans0.
     pose proof execution0 as H0.
     apply IH in H0.
     elim: H0 => e0 H0 {IH}.
     elim: H0 => H0 H1.
     move: H H1 trans0.
     case: c => [|n|n|n|n] H H1 trans0.
     + exists e0; split; first done. 
       by rewrite -coalesce_tail b_updates_comp -app_nil_end.
     + exists e0; split; first done.
       by rewrite -H1 -coalesce_tail b_updates_comp -app_nil_end.
     + exists e0; split; first done. 
       by rewrite -H1 -coalesce_tail b_updates_comp -app_nil_end.
     + inversion trans0; subst.
       pose proof rev_case e0 as H2.
       elim: H2 => H2.
       - subst; exists (a n :: nil); split; first by apply exec_a. 
         by rewrite -coalesce_tail b_updates_comp H1.
       - elim: H2 => e1 H2.
         elim: H2.
         case => [|n0|n0|n0|n0] H2.
         * rewrite H2 {H2 e0} in H0 H1.
           exists (e1 ++ x :: a n :: nil). 
           split; first by apply exec_trans; [ apply trans_xa | done ].
           do 2!rewrite -coalesce_tail; rewrite b_updates_comp H1.
           by do 3!rewrite a_updates_comp.
         * rewrite H2 {H2 e0} in H0 H1.
           exists (e1 ++ a n0 :: b n0 :: a n :: nil); split.
           + rewrite -coalesce_long_tail.
             apply exec_trans; first by apply trans_ba.             
             by rewrite coalesce_tail; apply exec_trans; first by apply trans_ab.
           + rewrite -coalesce_tail_long -coalesce_tail.
             rewrite a_updates_comp b_updates_comp -coalesce_tail.
             by rewrite a_updates_comp H1 -app_nil_end.
         * rewrite H2 {H2 e0} in H0 H1.
           exists (e1 ++ a' n0 :: a n :: nil).
           split; first by apply exec_trans; [ apply trans_a'a | done ].
           do 2!rewrite -coalesce_tail.
           by rewrite a_updates_comp b_updates_comp H1.           
         * rewrite H2 {H2 e0} in H0 H1.
           exists (e1 ++ b n0 :: a n :: nil).
           split; first by apply exec_trans; [ apply trans_ba | done ].
           do 2!rewrite -coalesce_tail.
           by rewrite a_updates_comp b_updates_comp H1.
         * rewrite H2 {H2 e0} in H0 H1.                     
           rewrite b_updates_comp a_updates_comp -app_nil_end -app_nil_end in H1.
           exists (e1 ++ a n :: b n :: nil).
           inversion H0; first by contradict H3; apply app_cons_not_nil.
           + change (a n1 :: nil) with (nil ++ a n1 :: nil) in H3.
             apply app_inj_tail in H3.
             by elim: H3 => H3 H4.
           + change (x :: nil) with (nil ++ x :: nil) in H3.
             apply app_inj_tail in H3.
             by elim: H3 => H3 H4.
           + rewrite -coalesce_tail in H3.                        
             apply app_inj_tail in H3.
             elim: H3 => H3 H4.
             rewrite H3 in execution1.
             rewrite H4 {H4} in trans1.
             split.
             - apply exec_trans; first by apply trans_ab.
               move: H3 trans1.
               case: c => [|n1|n1|n1|n1] H2 H3.
               * rewrite -H2 coalesce_tail.
                 apply exec_trans; first by apply trans_xa.
                 by rewrite -H2 in execution1.               
               * by inversion H3.
               * rewrite -H2 coalesce_tail.
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
            rewrite H4 {H4} b_updates_comp b_updates_comp /= -app_nil_end.
            have H4: e1 ++ a n :: b n :: nil = (e1 ++ a n :: nil) ++ b n :: nil by rewrite -ass_app -app_comm_cons.
            by rewrite H4 {H4} a_updates_comp a_updates_comp /= -app_nil_end H1.
     - inversion trans0; subst.
       pose proof rev_case e0.
       elim: H2 => H2.
       * rewrite H2 /= in H1.
         exists (a n :: nil).
         split; first by apply exec_a.
         have H3: e' ++ x :: b' n :: nil = (e' ++ x :: nil) ++ b' n :: nil by rewrite -ass_app -app_comm_cons.
         rewrite H3 {H3}.                     
         by rewrite b_updates_comp /= H1.
       * elim: H2 => e1 H2.
         elim: H2.
         case => [H2|n0 H2|n0 H2|n0 H2|n0 H2].
         + rewrite H2 in H1.
           rewrite b_updates_comp a_updates_comp /= -app_nil_end -app_nil_end in H1.
           rewrite H2 in H0.
           exists (e1 ++ x :: a n :: nil).
           split; first by apply exec_trans; [ apply trans_xa | done ].
           have H3: e' ++ x :: b' n :: nil = (e' ++ x :: nil) ++ b' n :: nil by rewrite -ass_app -app_comm_cons.
           rewrite H3 {H3}.
           have H3: e1 ++ x :: a n :: nil = (e1 ++ x :: nil) ++ a n :: nil by rewrite -ass_app -app_comm_cons.
           rewrite H3 {H3}.
           by rewrite b_updates_comp b_updates_comp a_updates_comp a_updates_comp H1.
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
             rewrite H3 {H3} b_updates_comp /=.
             have H3: e1 ++ a n0 :: b n0 :: a n :: nil = (e1 ++ a n0 :: b n0 :: nil) ++ a n :: nil  by rewrite app_ass -app_comm_cons.
             rewrite H3 a_updates_comp /= {H3}.
             have H3: e1 ++ a n0 :: b n0 :: nil = (e1 ++ a n0 :: nil) ++ b n0 :: nil by rewrite app_ass -app_comm_cons.         
             by rewrite H3 a_updates_comp /= -app_nil_end H1 {H3}.
         + rewrite H2 in H1.
           rewrite H2 in H0.
           exists (e1 ++ a' n0 :: a n :: nil).
           split; first by apply exec_trans; [ apply trans_a'a | done ].
           have H3: e' ++ x :: b' n :: nil = (e' ++ x :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
           rewrite H3 b_updates_comp /= {H3}.
           have H3: e1 ++ a' n0 :: a n :: nil = (e1 ++ a' n0 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.
           by rewrite H3 a_updates_comp H1.
         + rewrite H2 in H1.
           rewrite H2 in H0.
           exists (e1 ++ b n0 :: a n :: nil).
           split; first by apply exec_trans; [ apply trans_ba | done ].
           have H3: e' ++ x :: b' n :: nil = (e' ++ x :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
           rewrite H3 b_updates_comp /= {H3}.
           have H3: e1 ++ b n0 :: a n :: nil = (e1 ++ b n0 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.
           by rewrite H3 a_updates_comp H1.
         + rewrite H2 in H1.
           rewrite H2 in H0.
           rewrite b_updates_comp a_updates_comp /= -app_nil_end -app_nil_end in H1.
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
                 by rewrite b_updates_comp b_updates_comp a_updates_comp -app_nil_end H7.
             * by inversion H6.
             * rewrite -H3.
               split.
               + have H8: (e2 ++ a' n1 :: nil) ++ a n :: nil = e2 ++ a' n1 :: a n :: nil by rewrite app_ass -app_comm_cons.
                 rewrite H8 {H8}.
                 by apply exec_trans; first by apply trans_a'a.
               + have H8: e' ++ x :: b' n :: nil = (e' ++ x :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
                 rewrite H8 {H8}.
                 by rewrite b_updates_comp b_updates_comp a_updates_comp -app_nil_end H7.
             * rewrite -H3.
               split.
               + have H8: (e2 ++ b n1 :: nil) ++ a n :: nil = e2 ++ b n1 :: a n :: nil by rewrite app_ass -app_comm_cons.
                 rewrite H8 {H8}.
                 by apply exec_trans; first by apply trans_ba.
               + have H8: e' ++ x :: b' n :: nil = (e' ++ x :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
                 rewrite H8 {H8}.
                 by rewrite b_updates_comp b_updates_comp a_updates_comp -app_nil_end H7.
             * by inversion H6.
     - pose proof rev_case e0.
       elim: H2 => H2.
       * rewrite H2 /= in H1.
         exists (a n :: nil).
         split; first by apply exec_a.
         have H3: e' ++ a' n0 :: b' n :: nil = (e' ++ a' n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
         rewrite H3 {H3}.
         by rewrite b_updates_comp H1.
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
          by rewrite b_updates_comp a_updates_comp H1.
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
              by rewrite H7 b_updates_comp H1 {H7}.
          * have H5: x :: nil = nil ++ x :: nil by done.
            rewrite H5 {H5} in H4.   
            apply app_inj_tail in H4.
            by elim: H4 => H4 H5. 
          * have H5: e2 ++ c0 :: c' :: nil = (e2 ++ c0 :: nil) ++ c' :: nil by rewrite app_ass -app_comm_cons.
            rewrite H5 {H5} in H4.
            apply app_inj_tail in H4.
            elim: H4 => H4 H5.
            rewrite H5 {H5 c'} in trans1.
            rewrite  b_updates_comp -app_nil_end /= in H1.
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
            rewrite H3 b_updates_comp b_updates_comp -app_nil_end /= {H3}.
            have H3: e1 ++ a n1 :: b n1 :: a n :: nil = (e1 ++ a n1 :: b n1 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.
            rewrite H3 a_updates_comp /= {H3}.
            have H3: e1 ++ a n1 :: b n1 :: nil = (e1 ++ a n1 :: nil) ++ b n1 :: nil by rewrite app_ass -app_comm_cons.
            rewrite H3 a_updates_comp -app_nil_end /= {H3}.
            by rewrite H1.                          
          
          rewrite H2 in H0.
          rewrite H2 in H1.
          rewrite b_updates_comp -app_nil_end /= in H1.
          exists (e1 ++ a' n1 :: a n :: nil).
          split.
          by apply exec_trans; first by apply trans_a'a.
          have H3: e' ++ a' n0 :: b' n :: nil = (e' ++ a' n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
          rewrite H3 b_updates_comp b_updates_comp -app_nil_end /= {H3}.
          have H3: e1 ++ a' n1 :: a n :: nil = (e1 ++ a' n1 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.
          rewrite H3 {H3}.
          by rewrite a_updates_comp H1.
          
          rewrite H2 in H1.
          rewrite H2 in H0.
          exists (e1 ++ b n1 :: a n :: nil).
          rewrite a_updates_comp -app_nil_end /= in H1.
          split.
          apply exec_trans.
          apply trans_ba.
          done.
          
          have H3: e' ++ a' n0 :: b' n :: nil = (e' ++ a' n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
          rewrite H3 b_updates_comp /= {H3}.
          have H3: e1 ++ b n1 :: a n :: nil = (e1 ++ b n1 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.       
          rewrite H3 a_updates_comp a_updates_comp -app_nil_end /= {H3}.
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
            rewrite a_updates_comp -app_nil_end in H1.
            rewrite a_updates_comp /=.
            have H6: e' ++ a' n0 :: b' n :: nil = (e' ++ a' n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
            by rewrite H6 b_updates_comp H1.
            
            by inversion H5.

            exists (e2 ++ a' n2 :: a n :: nil).
            split.
            apply exec_trans.
            apply trans_a'a.
            done.
            have H6: e' ++ a' n0 :: b' n :: nil = (e' ++ a' n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
            rewrite H6 b_updates_comp /= {H6}.
            have H6: e2 ++ a' n2 :: a n :: nil = (e2 ++ a' n2 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons. 
            rewrite H6 a_updates_comp H4 /= {H6}.
            by rewrite H1 a_updates_comp -app_nil_end.
            
            exists (e2 ++ b n2 :: a n :: nil).
            split.
            apply exec_trans.
            apply trans_ba.
            done.
            
            have H6: e' ++ a' n0 :: b' n :: nil = (e' ++ a' n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
            rewrite H6 b_updates_comp /= {H6}.
            have H6: e2 ++ b n2 :: a n :: nil = (e2 ++ b n2 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.
            rewrite H6 H4 a_updates_comp /=.
            by rewrite H1 a_updates_comp -app_nil_end.
            
            by inversion H5.

       - pose proof rev_case e0.
       elim: H2 => H2.
       * rewrite H2 /= in H1.
         exists (a n :: nil).
         split; first by apply exec_a.
         have H3: e' ++ b n0 :: b' n :: nil = (e' ++ b n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
         rewrite H3 {H3}.
         by rewrite b_updates_comp H1.
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
          by rewrite b_updates_comp a_updates_comp H1.
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
              by rewrite H7 b_updates_comp H1 {H7}.
          * have H5: x :: nil = nil ++ x :: nil by done.
            rewrite H5 {H5} in H4.   
            apply app_inj_tail in H4.
            by elim: H4 => H4 H5. 
          * have H5: e2 ++ c0 :: c' :: nil = (e2 ++ c0 :: nil) ++ c' :: nil by rewrite app_ass -app_comm_cons.
            rewrite H5 {H5} in H4.
            apply app_inj_tail in H4.
            elim: H4 => H4 H5.
            rewrite H5 {H5 c'} in trans1.
            rewrite  b_updates_comp /= in H1.
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
            rewrite H3 b_updates_comp b_updates_comp /= {H3}.
            have H3: e1 ++ a n1 :: b n1 :: a n :: nil = (e1 ++ a n1 :: b n1 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.
            rewrite H3 a_updates_comp /= {H3}.
            have H3: e1 ++ a n1 :: b n1 :: nil = (e1 ++ a n1 :: nil) ++ b n1 :: nil by rewrite app_ass -app_comm_cons.
            rewrite H3 a_updates_comp -app_nil_end /= {H3}.
            by rewrite H1.                          
          
          rewrite H2 in H0.
          rewrite H2 in H1.
          rewrite b_updates_comp /= in H1.
          exists (e1 ++ a' n1 :: a n :: nil).
          split.
          by apply exec_trans; first by apply trans_a'a.
          have H3: e' ++ b n0 :: b' n :: nil = (e' ++ b n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
          rewrite H3 b_updates_comp b_updates_comp  /= {H3}.
          have H3: e1 ++ a' n1 :: a n :: nil = (e1 ++ a' n1 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.
          rewrite H3 {H3}.
          by rewrite a_updates_comp H1.
          
          rewrite H2 in H1.
          rewrite H2 in H0.
          exists (e1 ++ b n1 :: a n :: nil).
          rewrite a_updates_comp -app_nil_end /= in H1.
          split.
          apply exec_trans.
          apply trans_ba.
          done.
          
          have H3: e' ++ b n0 :: b' n :: nil = (e' ++ b n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
          rewrite H3 b_updates_comp /= {H3}.
          have H3: e1 ++ b n1 :: a n :: nil = (e1 ++ b n1 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.       
          rewrite H3 a_updates_comp a_updates_comp -app_nil_end /= {H3}.
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
            rewrite a_updates_comp -app_nil_end in H1.
            rewrite a_updates_comp /=.
            have H6: e' ++ b n0 :: b' n :: nil = (e' ++ b n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
            by rewrite H6 b_updates_comp H1.
            
            by inversion H5.

            exists (e2 ++ a' n2 :: a n :: nil).
            split.
            apply exec_trans.
            apply trans_a'a.
            done.
            have H6: e' ++ b n0 :: b' n :: nil = (e' ++ b n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
            rewrite H6 b_updates_comp /= {H6}.
            have H6: e2 ++ a' n2 :: a n :: nil = (e2 ++ a' n2 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons. 
            rewrite H6 a_updates_comp H4 /= {H6}.
            by rewrite H1 a_updates_comp -app_nil_end.
            
            exists (e2 ++ b n2 :: a n :: nil).
            split.
            apply exec_trans.
            apply trans_ba.
            done.
            
            have H6: e' ++ b n0 :: b' n :: nil = (e' ++ b n0 :: nil) ++ b' n :: nil by rewrite app_ass -app_comm_cons.
            rewrite H6 b_updates_comp /= {H6}.
            have H6: e2 ++ b n2 :: a n :: nil = (e2 ++ b n2 :: nil) ++ a n :: nil by rewrite app_ass -app_comm_cons.
            rewrite H6 H4 a_updates_comp /=.
            by rewrite H1 a_updates_comp -app_nil_end.
            
            by inversion H5.
Qed.
              
            
