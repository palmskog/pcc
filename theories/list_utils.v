Require Export List.
Require Import Arith.
Require Import Omega.
Require Import ssreflect.

Set Implicit Arguments.

Section ListUtils.

Variable A : Set.

Lemma app_cons_has_head : forall (a : A) l l', exists a', exists l'', l ++ a :: l' = a' :: l''.
Proof. 
move => a; case => [l'|a' l l']; first by exists a; exists l'. 
by exists a'; exists (l ++ a :: l'). 
Qed.

Lemma nil_or_app : forall l, l = nil \/ exists l', exists a: A, l = l' ++ a :: nil.
Proof.
elim => [|a l IHl]; first by left.
right; elim: IHl => H; first by exists nil; exists a; rewrite H.
by move: H => [l' [a' H]]; exists (a :: l'); exists a'; rewrite H.
Qed.

Lemma in_but_not_last : forall l (a b: A), In a (l ++ b :: nil) -> a = b \/ In a l.
Proof.
move => l a b H.
apply In_rev in H.
rewrite distr_rev /= in H.
by elim: H => H; [ left | right; apply In_rev in H ].
Qed.

Lemma list_rearrange : forall l l' (a:A), l ++ a :: l' = (l ++ a :: nil) ++ l'.
Proof. by elim => [|a l IH l' a']; [ case | rewrite app_ass ]. Qed.

Lemma list_rearrange2 : forall l (a b: A), l ++ a :: b :: nil = (l ++ a :: nil) ++ b :: nil.
Proof. by move => l a b; rewrite app_ass. Qed.

Lemma list_rearrange3 : forall l l' (a : A), (a :: l) ++ l' = a :: l ++ l'.
Proof. by []. Qed.

Lemma list_neq_length : forall l l': list A, length l <> length l' -> l <> l'.
Proof. by move => l l' H; contradict H; rewrite H. Qed.

Inductive prefix : list A -> list A -> Prop :=
| prefix_nil : forall l, prefix nil l
| prefix_next : forall (a: A) l l', prefix l l' -> prefix (a :: l) (a :: l').

Lemma prefix_firstn : forall n (l : list A), n <= length l -> prefix (firstn n l) l.
Proof.
elim => [l H|n IHn]; first by apply prefix_nil.
case => [|a l] H; first by inversion H.
by apply prefix_next; apply IHn; apply le_S_n.
Qed.

Inductive proper_prefix : list A -> list A -> Prop :=
| proper_prefix_nil : forall (l: list A) a, proper_prefix nil (a :: l)
| proper_prefix_next : forall a l l', proper_prefix l l' -> proper_prefix (a :: l) (a :: l').

Lemma proper_prefix_app : forall (l l' l'': list A), 
  proper_prefix l l' -> proper_prefix (l'' ++ l) (l'' ++ l').
Proof.
move => l l'.
elim => [|a l'' IH H]; first by [].
rewrite -2!app_comm_cons.
by apply proper_prefix_next; apply IH.
Qed.

Lemma proper_prefix_last : forall l (a: A), proper_prefix l (l ++ a :: nil).
Proof.
elim => [|a l IH a']; first by apply proper_prefix_nil.
by rewrite -app_comm_cons; apply proper_prefix_next.
Qed.

Lemma proper_prefix_split : forall (l l': list A), 
  proper_prefix l' l -> exists x, exists l'', l = l' ++ (x :: l'').
Proof.
elim => [l' H|a l IH]; first by inversion H.
case => [|a' l'] H; first by exists a; exists l.
have ->: a = a' by inversion H.
have H0: proper_prefix l' l by inversion H.
apply IH in H0.
move: H0 => [x [l'' H0]].
by exists x; exists l''; rewrite H0.
Qed.

Lemma proper_prefix_shorter : forall (l' l: list A), proper_prefix l' l -> length l' < length l.
Proof.
move => l' l H.
apply proper_prefix_split in H.
move: H => [a' [l'' H]].
rewrite H app_length /=.
by omega.
Qed.

Theorem proper_prefix_well_founded : well_founded (@proper_prefix).
Proof. 
apply well_founded_lt_compat with (f := @length A). 
by apply proper_prefix_shorter. 
Qed.

Theorem strong_list_ind (P: list A -> Prop) :
  (forall l, (forall l', proper_prefix l' l -> P l') -> P l) -> forall l, P l.
Proof.
move => P H.
apply well_founded_ind with (R := @proper_prefix).
apply proper_prefix_well_founded.
move => x H0.
apply H => l' H1.
by apply H0.
Qed.

Lemma in_list_in_prefix : forall l l' (a: A), proper_prefix l' l -> In a l' -> In a l.
Proof.
move => l l' a H H0.
apply proper_prefix_split in H.
move: H => [a' [l'' H]].
rewrite H.
by apply in_or_app; left.
Qed.

Lemma nil_or_last : forall l, l = nil \/ exists l', exists a : A, l = l' ++ a :: nil.
Proof. by elim/rev_ind => [|a l IH]; [ left | right; exists l; exists a ]. Qed.

Inductive suffix : list A -> list A -> Prop :=
| suffix_here : forall (l: list A), suffix l l
| suffix_next : forall a suffx l, suffix suffx l -> suffix suffx (a::l).

Lemma suffix_split : forall l suffx: list A, 
  suffix suffx l -> exists pref, l = pref ++ suffx.
Proof.
elim => [|a l IH] suffx H; first by inversion H; exists nil.
inversion H; subst; first by exists nil.
apply IH in H2.
move: H2 => [l' H2].
by exists (a :: l'); rewrite H2.
Qed.

Lemma suffix_app : forall l l' l'': list A, 
  suffix l l' -> suffix l (l'' ++ l').
Proof.
move => l l'.
elim => [|a l'' IH H]; first by [].
rewrite /=; 
by apply suffix_next; apply IH.
Qed.

Lemma suffix_transitive : forall c bc abc: list A, 
  suffix bc abc -> suffix c bc -> suffix c abc.
Proof.
move => c bc abc H H0. 
apply suffix_split in H.
apply suffix_split in H0.
move: H => [pref H]; move: H0 => [pref' H0].
rewrite H H0.
by do 2!apply suffix_app; apply suffix_here.
Qed.

Inductive last : list A -> A -> Prop :=
| last_base : forall a, last (a :: nil) a
| last_cons : forall l a b, last l a -> last (b::l) a.

Lemma last_exists : forall l (c : A), exists c', last (c :: l) c'.
Proof.
elim => [|a l IH] c; first by exists c; apply last_base.
have H: exists c', last (c :: l) c' by apply IH.
move: H => [c' H] {IH}.
inversion H; first by exists a; apply last_cons; apply last_base.
by exists c'; apply last_cons; apply last_cons.
Qed.

Lemma single_last : forall l (a b: A), last l a -> last l b -> a = b.
Proof.
elim => [|a' l IH] a b H H0; first by inversion H.
inversion H; subst; first by inversion H0; subst; last by inversion H4.
apply IH; first by [].
by inversion H0; subst; first by inversion H4.
Qed.

Lemma last_app : forall l l' (a: A), last l' a -> last (l++l') a.
Proof.
elim => [|a' l IH l' a H]; first by [].
by apply last_cons; apply IH.
Qed.

Lemma app_last : forall l (a: A), last (l ++ a :: nil) a.
Proof.
elim => [|a' l IH] a; first by apply last_base.
by rewrite list_rearrange3; apply last_cons.
Qed.

Lemma last_app_prefix : forall (l : list A) (a : A), 
  last l a -> exists l', l = l' ++ a::nil.
Proof.
elim => [|a' l IH] a H; first by inversion H.
inversion H; subst; first by exists nil.
apply IH in H3.
move: H3 => [l'' H3]; rewrite H3 {H3}.
by exists (a' :: l'').
Qed.

Lemma last_app_cons :forall l (a b: A), last (l ++ a::nil) b -> a = b.
Proof.
move => l a b H.
apply last_app_prefix in H.
move: H => [l' H].
apply app_inj_tail in H.
by move: H => [H H0].
Qed.

Lemma list_same_head : forall l (a b: A), 
  head (l ++ a :: nil) = head (l ++ a :: b :: nil).
Proof. by case. Qed.

End ListUtils.
