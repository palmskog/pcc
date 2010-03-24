Require Import List.

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

Lemma filter_prefix : forall f_pref l,
  prefix f_pref (filter l) -> exists l_pref, prefix l_pref l /\ filter l_pref = f_pref.
