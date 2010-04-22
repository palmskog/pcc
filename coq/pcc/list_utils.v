
Set Implicit Arguments.

Require Export List.
Require Import Arith.
Require Import Omega.

Section list_utils.

  Variable A : Set.
  
  Lemma app_cons_has_head : forall (a : A) l l', exists a', exists l'', l ++ a :: l' = a' :: l''.
  Proof.
    intros.
    destruct l.
    exists a; exists l'.
    reflexivity.
    exists a0; exists (l ++ a :: l').
    reflexivity.
  Qed.
  
  
  Lemma nil_or_app : forall l, l = nil \/ exists l', exists a: A, l = l' ++ a :: nil.
    intros.
    induction l.
    left; reflexivity.
    right.
    elim IHl; intros.
    exists nil.
    exists a.
    subst; reflexivity.
    elim H; intros.
    elim H0; intros.
    subst.
    exists (a::x).
    exists x0.
    reflexivity.
  Qed.
  
  
  Lemma in_but_not_last : forall l (a b: A), In a (l ++ b :: nil) -> a = b \/ In a l.
    intros.
    apply In_rev in H.
    rewrite distr_rev in H.
    simpl in H.
    elim H; intros.
    left.
    auto.
    right.
    apply In_rev in H0.
    assumption.
  Qed.
  

  Lemma list_rearrange : forall l l' (a:A), l ++ a :: l' = (l ++ a :: nil) ++ l'.
    intros.
    induction l.
    induction l'; simpl; auto.
    rewrite app_ass.
    trivial.
  Qed.
  
  
  Lemma list_rearrange2 : forall l (a b: A), l ++ a :: b :: nil = (l ++ a :: nil) ++ b :: nil.
    intros.
    rewrite app_ass.
    auto with datatypes.
  Qed.
  

  Lemma list_rearrange3 : forall l l' (a : A), (a :: l) ++ l' = a :: l ++ l'.
    reflexivity.
  Qed.

  
  Lemma list_neq_length : forall l l': list A, length l <> length l' -> l <> l'.
    intros.
    contradict H.
    subst.
    reflexivity.
  Qed.

  
  Inductive prefix : list A -> list A -> Prop :=
  | prefix_nil : forall l, prefix nil l
  | prefix_next : forall (a: A) l l', prefix l l' -> prefix (a :: l) (a :: l').
  

  Lemma prefix_firstn : forall n (l : list A), n <= length l -> prefix (firstn n l) l.
    induction n; intros.
    apply prefix_nil.
    destruct l.
    inversion H.
    simpl.
    apply prefix_next.
    apply IHn.
    apply le_S_n; assumption.
  Qed.
  
  
  Inductive proper_prefix : list A -> list A -> Prop :=
  | proper_prefix_nil : forall (l: list A) a, proper_prefix nil (a :: l)
  | proper_prefix_next : forall a l l', proper_prefix l l' -> proper_prefix (a :: l) (a :: l').
  
  
  Lemma proper_prefix_app : forall (l l' l'': list A), proper_prefix l l' -> proper_prefix (l''++l) (l''++l').
    intros.
    induction l''.
    assumption.
    repeat rewrite <- app_comm_cons.
    apply proper_prefix_next.
    assumption.
  Qed.
  
  
  Lemma proper_prefix_last : forall l (a: A), proper_prefix l (l ++ a :: nil).
    intros.
    induction l.
    apply proper_prefix_nil.
    rewrite <- app_comm_cons.
    apply proper_prefix_next.
    assumption.
  Qed.
  
  
  Lemma proper_prefix_split : forall (l l': list A), proper_prefix l' l -> exists x, exists l'', l = l' ++ (x :: l'').
    induction l; intros.
    inversion H.
    destruct l'.
    exists a.
    exists l.
    auto.
    inversion H; subst.
    apply IHl in H1.
    inversion H1.
    inversion H0.
    subst.
    exists x.
    exists x0.
    auto.
  Qed.
  

  Lemma proper_prefix_shorter : forall (l' l: list A), proper_prefix l' l -> length l' < length l.
    intros.
    apply proper_prefix_split in H.
    inversion H; subst.
    inversion H0; subst.
    rewrite app_length.
    simpl.
    omega.
  Qed.
  
  
  Theorem proper_prefix_well_founded : well_founded (@proper_prefix).
    apply well_founded_lt_compat with (f := @length A).
    apply proper_prefix_shorter.
  Qed.
  
  
  Theorem strong_list_ind (P: list A -> Prop) :
    (forall l, (forall l', proper_prefix l' l -> P l') -> P l) -> forall l, P l.
    intros P H.
    apply well_founded_ind with (R := @proper_prefix).
    apply proper_prefix_well_founded.
    intros.
    apply H.
    intros.
    apply H0.
    assumption.
  Qed.
  
  
  Lemma in_list_in_prefix : forall l l' (a: A), proper_prefix l' l -> In a l' -> In a l.
    intros.
    apply proper_prefix_split in H.
    elim H; intros.
    elim H1; intros.
    rewrite H2.
    apply in_or_app.
    left.
    assumption.
  Qed.
  
  
  Lemma nil_or_last : forall l, l = nil \/ exists l', exists a : A, l = l' ++ a :: nil.
    intros.
    destruct l using rev_ind.
    left; reflexivity.
    right.
    exists l.
    exists x.
    reflexivity.
  Qed.
  
  
  Inductive suffix : list A -> list A -> Prop :=
  | suffix_here : forall (l: list A), suffix l l
  | suffix_next : forall a suff l, suffix suff l -> suffix suff (a::l).
  
  
  Lemma suffix_split :
    forall l suff: list A, suffix suff l -> exists pref, l = pref ++ suff.
  Proof.
    intros l.
    induction l; intros.
    inversion H; subst.
    exists nil.
    reflexivity.
    inversion H; subst.
    exists nil.
    reflexivity.
    apply IHl in H2.
    elim H2; intros.
    subst.
    exists (a::x).
    reflexivity.
  Qed.
  
  
  Lemma suffix_app :
    forall l l' l'': list A, suffix l l' -> suffix l (l'' ++ l').
  Proof.
    intros.
    induction l''.
    assumption.
    simpl.
    apply suffix_next.
    assumption.
  Qed.
  
  
  Lemma suffix_transitive :
    forall c bc abc: list A, suffix bc abc -> suffix c bc -> suffix c abc.
  Proof.
    intros.
    apply suffix_split in H.
    apply suffix_split in H0.
    elim H; intros.
    elim H0; intros.
    subst.
    apply suffix_app.
    apply suffix_app.
    apply suffix_here.
  Qed.
  
  
  Inductive last : list A -> A -> Prop :=
  | last_base : forall a, last (a :: nil) a
  | last_cons : forall l a b, last l a -> last (b::l) a.


  Lemma last_exists : forall l (c : A), exists c', last (c :: l) c'.
  Proof.
    intros.
    induction l.
    exists c.
    apply last_base.
    elim IHl; intros.
    inversion H; subst.
    exists a.
    apply last_cons.
    apply last_base.
    exists x.
    apply last_cons.
    apply last_cons.
    assumption.
  Qed.


  Lemma single_last : forall l (a b: A), last l a -> last l b -> a = b.
    intros.
    induction l.
    inversion H.
    inversion H; subst.
    inversion H0; subst.
    reflexivity.
    inversion H4.
    apply IHl.
    assumption.
    inversion H0; subst.
    inversion H4.
    assumption.
  Qed.

  
  Lemma last_app : forall l l' (a: A), last l' a -> last (l++l') a.
    intros.
    induction l.
    simpl.
    assumption.
    simpl.
    apply last_cons.
    assumption.
  Qed.
  
  
  Lemma app_last : forall l (a: A), last (l ++ a :: nil) a.
  Proof.
    intros.
    induction l.
    apply last_base.
    rewrite list_rearrange3.
    apply last_cons.
    assumption.
  Qed.

  
  Lemma last_app_prefix :
    forall (l l': list A) a, last l a -> exists l', l = l' ++ a::nil.
  Proof.
    intros l l'.
    induction l; intros.
    inversion H.
    
    inversion H; subst.
    exists nil.
    auto with datatypes.
    
    apply IHl in H3.
    elim H3; intros.
    rewrite H0.
    exists (a::x).
    auto with datatypes.
  Qed.
  
  
  Lemma last_app_cons :
    forall l (a b: A), last (l ++ a::nil) b -> a = b.
  Proof.
    intros.
    apply last_app_prefix in H.
    elim H; intros.
    apply app_inj_tail in H0.
    elim H0; intros; assumption.
    auto.
  Qed.
  
  
  Lemma list_same_head :
    forall l (a b: A), head (l ++ a :: nil) = head (l ++ a :: b :: nil).
    induction l; intros; reflexivity.
  Qed.

End list_utils.
