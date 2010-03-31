Require Import List.
Require Import ssreflect.

Variable A : Set.
Variable f : A -> bool.

Inductive prefix : list A -> list A -> Prop :=
| prefix_nil : forall l, prefix nil l
| prefix_next : forall (a: A) l l', prefix l l' -> prefix (a :: l) (a :: l').

Fixpoint filter (l : list A) : list A :=
  match l with
    | nil => nil
    | h :: t  => if (f h) then (h :: (filter t)) else (filter t)
  end.

Lemma filter_prefix : forall l l', prefix l (filter l') -> exists l0, prefix l0 l' /\ filter l0 = l.
Proof.
 move => l l'; move: l' l.
 elim => [l' H|a l' IH].
 - by exists nil; rewrite /= in H; inversion H; split; [ apply prefix_nil | done ].
 - case => [|a' l].
   * by exists nil; split; [ apply prefix_nil | done ].
   * rewrite /=; case H: (f a) => H0.
     + inversion H0 as [|a0 l0 l'0 H1 [H2 H4] [H3 H5]].
       pose proof (IH l) as H6.
       apply H6 in H1.
       elim: H1 => l1 H1 {H6}.
       elim: H1 => H1 H6.
       exists (a :: l1); split.
       - by apply prefix_next.
       - by rewrite /=; case H7: (f a); [ rewrite H6 | rewrite H in H7 ].
     + pose proof (IH (a' :: l)) as H1.
       apply H1 in H0.
       elim: H0 => l0 H2 {H1}.
       elim: H2 => H2 H3.
       exists (a :: l0); split.
       - by apply prefix_next.
       - by rewrite /=; case H4: (f a); [ rewrite H in H4 | rewrite H3 ].
Qed.
