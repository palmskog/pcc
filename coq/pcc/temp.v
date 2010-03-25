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

Lemma filter_prefix : forall l l',
  prefix l (filter l') -> exists l0, prefix l0 l' /\ filter l0 = l.
Proof.
move => l l'.
move: l' l.
elim => [l' H|a l' IH].
- exists nil.
  rewrite /= in H.
  inversion H.
  by split; [ apply prefix_nil | done ].
- case => [|a' l].
  * exists nil.
    by split; [ apply prefix_nil | done ].
  * rewrite /=.
    case H: (f a) => H0.
    + inversion H0.
      pose proof (IH l).
      apply H6 in H2.
      elim: H2 => l1 H2.
      elim: H2 => H2 H7.
      exists (a :: l1).
      split.
      - by apply prefix_next.
      - rewrite /=.
        case H8: (f a).
        * by rewrite H7.
        * by rewrite H in H8.
    + pose proof (IH (a' :: l)).
      apply H1 in H0.
      elim: H0 => l0 H2.
      elim: H2 => H2 H3.
      exists (a :: l0).
      split.
      - by apply prefix_next.
      - rewrite /=.
        case H4: (f a).
        * by rewrite H in H4.
        * by rewrite H3.
Qed.
