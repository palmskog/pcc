From PCC Require Import java_basic_defs expressions_assertions program_model.
From Coq Require Import ZArith Lia.
From PCC Require Import ssrexport.

Section SemanticsAssertions.
  
Lemma int_or_other : forall v, is_intval v \/ ~is_intval v.
Proof.
case; last by right => H_int; inversion H_int.
case; try (intros; right; unfold is_intval; intro; elim H; intros; discriminate).
by move => z; left; exists z.
Qed.

Lemma complete_geeval : forall e gv, exists v, g_eeval e gv v.
Proof.
case => [v gv|g gv|e f gv| c f gv| n gv| n gv|e e' gv|e e' e0 gv].
- by exists v; apply ge_val.
- by exists (gv g); apply ge_gv.
- by exists undefval; apply ge_nsfield.
- by exists undefval; apply ge_sfield.
- by exists undefval; apply ge_stackexp.
- by exists undefval; apply ge_local.
- by exists undefval; apply ge_plus.
- by exists undefval; apply ge_guarded.
Qed.

Set Printing Coercions.

Lemma deterministic_geeval : forall e c v1 v2, g_eeval e c v1 -> g_eeval e c v2 -> v1 = v2.
Proof.
move => e c v1 v2 H_geeval1 H_geeval2.
inversion H_geeval1; inversion H_geeval2; subst; rewrite //; first by injection H2.
by inversion H_geeval1; inversion H_geeval2.
Qed.

Lemma complete_eeval : forall e c, normal_conf c -> exists v, eeval e c v.
Proof.
elim => [|g c H_norm|e IH f c H_norm|c f c0|n c|||].
- case => [j c H_norm|c H_norm].
  * by exists j; apply e_val.
  * by exists ghost_errval; apply e_ghosterr.
- inversion H_norm; subst.
  by exists (gv g); apply e_ghostvar.
- case (IH c H_norm).
  case; last by exists undefval; eapply e_nsfield_err1; eauto.
  case => [z|b|l H|].
  * by exists undefval; apply e_nsfield_err1 with (v := intval z).
  * by exists undefval; apply e_nsfield_err1 with (v := boolval b).
  * have Hc: exists gv dh sh ars, c = (gv, (dh, sh), ars).
     destruct c; destruct p; destruct h.
     by exists g, d, s, l0.
    case: Hc => [ gv [dh [sh [ars Hc] ] ] ].
    case_eq (dh l) => [obj|] Hdh; first by exists (jval (obj f)); eapply e_nsfield; eauto.
    by exists undefval; eapply e_nsfield_err2; eauto.
  * by exists undefval; eapply e_nsfield_err1; eauto.
- move => H; inversion H; intros.
  destruct h as (dh, sh).
  case Hf: (sh c f) => [v|]; last by exists undefval; eapply e_sfield_err; eauto.
  by exists (jval v); eapply e_sfield; eauto.
- move => H; inversion H; subst.
  exists (s[[n]]).
  by apply e_stack.
- move => n c H; inversion H; subst.
  exists (ls n).
  by apply e_local.
- move => e1 IHe1 e2 IHe2 c H.
  have [v1 Hv1] := IHe1 _ H.
  have [v2 Hv2] := IHe2 _ H.
  case (int_or_other v1); case (int_or_other v2) => H1 H2.
  * inversion H1; subst.
    inversion H2; subst.
    exists (intval (x0 + x)).
    by apply e_plus.
  * by exists undefval; eapply e_plus_err; eauto.
  * by exists undefval; eapply e_plus_err; eauto.
  * by exists undefval; eapply e_plus_err; eauto.
- move => e1 IHe1 e2 IHe2 e3 IHe3 c Hc.
  have [v1 Hv1] := IHe1 _ Hc.
  have [v2 Hv2] := IHe2 _ Hc.
  have [v3 Hv3] := IHe3 _ Hc.
  have Hb_dec: (forall v, (exists b, v = boolval b) \/ forall b, v <> boolval b).
    case => [z|b|l|].
    * by right.
    * by left; exists b.
    * by right.
    * by right.
  destruct v1; last by exists undefval; eapply e_guard_err; eauto.
  case (Hb_dec j) => [ [b Hb]|Hb].
    subst.
    destruct b; first by exists v2; apply e_guard_true.
    by exists v3; apply e_guard_other.
  exists undefval; eapply e_guard_err; eauto.
  move => b Hj.
  by inversion Hj; congruence.
Qed.

Open Scope Z_scope.


  Inductive aeval : ast -> conf -> Prop :=
  | e_tt       : forall c, aeval tt c
  | e_conj     : forall c a1 a2, aeval a1 c /\ aeval a2 c -> aeval (and a1 a2) c
  | e_disj     : forall c a1 a2, aeval a1 c \/ aeval a2 c -> aeval (or  a1 a2) c
  | e_neg      : forall c a, aeval_f a c -> aeval (neg a) c
  | e_le       : forall c e1 e2 i j, eeval e1 c (intval i) -> eeval e2 c (intval j) -> i <= j -> aeval (le e1 e2) c
  | e_eq       : forall c e1 e2 v, eeval e1 c v -> eeval e2 c v -> aeval (eq e1 e2) c
  | e_if_true  : forall c a1 a2 a3, aeval a1 c -> aeval a2 c -> aeval (ifelse a1 a2 a3) c
  | e_if_false : forall c a1 a2 a3, aeval_f a1 c -> aeval a3 c -> aeval (ifelse a1 a2 a3) c
  with aeval_f : ast -> conf -> Prop :=
  | e_ff_f       : forall c, aeval_f ff c
  | e_conj_f     : forall c a1 a2, aeval_f a1 c \/ aeval_f a2 c -> aeval_f (and a1 a2) c
  | e_disj_f     : forall c a1 a2, aeval_f a1 c /\ aeval_f a2 c -> aeval_f (or  a1 a2) c
  | e_neg_f      : forall c a, aeval a c -> aeval_f (neg a) c
  | e_le_f       : forall c e1 e2 i j, eeval e1 c (intval i) -> eeval e2 c (intval j) -> i > j -> aeval_f (le e1 e2) c 
(*  | e_eq_f       : forall c e1 e2 i j, eeval e1 c (intval i) -> eeval e2 c (intval j) -> i <> j -> aeval_f (eq e1 e2) c *)
  | e_eq_f       : forall c e1 e2 v1 v2, eeval e1 c v1 -> eeval e2 c v2 -> v1 <> v2 -> aeval_f (eq e1 e2) c 
  | e_if_true_f  : forall c a1 a2 a3, aeval a1 c -> aeval_f a2 c -> aeval_f (ifelse a1 a2 a3) c
  | e_if_false_f : forall c a1 a2 a3, aeval_f a1 c -> aeval_f a3 c -> aeval_f (ifelse a1 a2 a3) c
(*  | e_eq_f_err   : forall c e1 e2 v1 v2, eeval e1 c v1 -> eeval e2 c v2 -> ~is_intval v1 \/ ~is_intval v2 -> aeval_f (eq e1 e2) c*)
  | e_le_f_err   : forall c e1 e2 v1 v2, eeval e1 c v1 -> eeval e2 c v2 -> ~is_intval v1 \/ ~is_intval v2 -> aeval_f (le e1 e2) c.


  Lemma same_or_diff_type : forall v1 v2: value, v1 = v2 \/ v1 <> v2.
  Proof.
    intros.
    destruct v1; destruct v2; try (right; intro; discriminate).
    destruct j; destruct j0; try (right; intro; discriminate).
    assert (z = z0 \/ z <> z0).
      lia.
    elim H; intros.
    subst.
    left; reflexivity.
    right.
    intro.
    inversion H1.
    contradict H0.
    assumption.
    destruct b; destruct b0;
      try (left; reflexivity);
        try (right; discriminate).
    unfold loc in l.
    unfold loc in l0.
    assert (l = l0 \/ l <> l0).
      lia.
    elim H; intros.
    subst.
    left; reflexivity.
    right; intro.
    elim H0.
    inversion H1.
    reflexivity.
    left; reflexivity.
    left; reflexivity.
  Qed.
  

  Lemma deterministic_eeval : forall e c v1 v2, eeval e c v1 -> eeval e c v2 -> v1 = v2.
  Proof.
intros e c.
induction e; intros; inversion H; subst; inversion H0; subst; try reflexivity.
assert (jval (refval l) = jval (refval l0)).
  apply IHe.
  assumption.
  assumption.
inversion H1; subst.
inversion H3; subst.
rewrite H7 in H9.
inversion H9; subst.
reflexivity.

assert (jval (refval l) = v).
  apply IHe.
  assumption.
  assumption.
rewrite <- H1 in H8.
elim (H8 l).
reflexivity.

assert (jval (refval l) = jval (refval l0)).
  apply IHe; assumption.
inversion H1; subst.
inversion H3; subst.
rewrite H9 in H7.
discriminate.

assert (v = refval l).
  apply IHe; assumption.
rewrite H1 in H6.
elim (H6 l).
reflexivity.

assert (jval (refval l) = jval (refval l0)).
  apply IHe; assumption.
inversion H1; subst.
inversion H3; subst.
rewrite H7 in H9; discriminate.

inversion H3; subst.
rewrite H7 in H6.
inversion H6.
reflexivity.

inversion H3; subst.
rewrite H7 in H6; discriminate.

inversion H3; subst.
rewrite H7 in H6; discriminate.

rewrite H3 in H2.
inversion H2.
reflexivity.

rewrite H2 in H3.
inversion H3; reflexivity.

assert (jval (intval i) = jval (intval i0)). apply IHe1; assumption.
assert (jval (intval j) = jval (intval j0)). apply IHe2; assumption.
inversion H1; inversion H2.
reflexivity.

assert (jval (intval i) = v1). apply IHe1; assumption.
assert (jval (intval j) = v0). apply IHe2; assumption.
rewrite <- H1 in H9.
rewrite <- H2 in H9.
elim H9; intros; elim H7.
exists i; reflexivity.
exists j; reflexivity.

assert (jval (intval i) = v0). apply IHe1; assumption.
assert (jval (intval j) = v3). apply IHe2; assumption.
rewrite <- H1 in H7.
rewrite <- H2 in H7.
elim H7; intros; elim H6.
exists i; reflexivity.
exists j; reflexivity.

apply IHe2; assumption.

assert (jval (boolval true) = boolval false). apply IHe1; assumption.
discriminate.

assert (jval (boolval true) = v). apply IHe1; assumption.
rewrite <- H1 in H9.
elim (H9 true).
reflexivity.

assert (jval (boolval false) = boolval true). apply IHe1; assumption.
discriminate.

apply IHe3; assumption.

assert (v = boolval false). apply IHe1; assumption.
rewrite H1 in H9.
elim (H9 false); reflexivity.

assert (jval (boolval true) = v). apply IHe1; assumption.
rewrite <- H1 in H7.
elim (H7 true); reflexivity.
assert (v = boolval false). apply IHe1; assumption.
rewrite H1 in H7.
elim (H7 false); reflexivity.
Qed.


(* Correctness of aeval vs aeval_f. *)
Theorem eval_or : forall a c, normal_conf c -> aeval a c \/ aeval_f a c.
  intros.
  induction a.
  left; apply e_tt.
  right; apply e_ff_f.
  
  (* le *)
  assert (exists z1, eeval e  c z1). apply complete_eeval; assumption.
  assert (exists z2, eeval e0 c z2). apply complete_eeval; assumption.
  elim H0; intros v.
  elim H1; intros v0.
  intros.
  
  assert (is_intval v \/ ~is_intval v). apply int_or_other.
  assert (is_intval v0 \/ ~is_intval v0). apply int_or_other.
  
  elim H4; elim H5; intros.
  elim H6; elim H7; intros; subst.
  assert (x <= x0 \/ x > x0). lia.
  elim H8; intros.
  left; apply e_le with (i := x) (j := x0); assumption.
  right; apply e_le_f with (i := x) (j := x0); assumption.
  right; apply e_le_f_err with (v1 := v) (v2 := v0); try assumption.
    right.
    assumption.
  
  right; apply e_le_f_err with (v1 := v) (v2 := v0); try assumption.
    left.
    assumption.
  
  right; apply e_le_f_err with (v1 := v) (v2 := v0); try assumption.
    left.
    assumption.
  
  (* eq *)
  assert (exists z1, eeval e  c z1). apply complete_eeval; assumption.
  assert (exists z2, eeval e0 c z2). apply complete_eeval; assumption.
  
  elim H0; intros v.
  elim H1; intros v0.
  intros.
  
  pose proof (same_or_diff_type v v0).
  elim H4; intros.
  subst.
  left.
  apply e_eq with (v := v0); assumption.
  right.
  apply e_eq_f with (v1 := v) (v2 := v0); try assumption.


  (* or *)
  elim IHa1; intros.
  left.
  apply e_disj.
  left.
  assumption.
  elim IHa2; intros.
  left.
  apply e_disj.
  right.
  assumption.
  right.
  apply e_disj_f.
  split; assumption.
  
  (* and *)
  elim IHa1; intros.
  elim IHa2; intros.
  left.
  apply e_conj.
  split; assumption.
  right.
  apply e_conj_f.
  right.
  assumption.
  right.
  apply e_conj_f.
  left.
  assumption.
  
  (* neg *)
  elim IHa; intros.
  right; apply e_neg_f; assumption.
  left;  apply e_neg; assumption.
  
  (* ifelse *)
  elim IHa1; intros.
  elim IHa2; intros.
  left; apply e_if_true; assumption.
  right; apply e_if_true_f; assumption.
  elim IHa3; intros.
  left; apply e_if_false; assumption.
  right; apply e_if_false_f; assumption.
Qed.



Theorem eval_nand : forall a c, ~(aeval a c /\ aeval_f a c).
Proof.
  intros.
  intro.
  elim H; intros.
  
  induction a; inversion H0; inversion H1; subst; try discriminate.
  
  (* le *)
  assert (jval (intval i) = intval i0). apply deterministic_eeval with (e := e)  (c := c); assumption.
  assert (jval (intval j) = intval j0). apply deterministic_eeval with (e := e0) (c := c); assumption.
  inversion H2; inversion H3; subst.
  lia.
  
  assert (v1 = intval i). apply deterministic_eeval with (e := e)  (c := c); assumption.
  assert (v2 = intval j). apply deterministic_eeval with (e := e0) (c := c); assumption.
  
  elim H13; intros; unfold is_intval in H6.
  elim H6; exists i; assumption.
  elim H6; exists j; assumption.
  
  (* eq *)
  assert (v1 = v). apply (deterministic_eeval e c); assumption.
  assert (v2 = v). apply (deterministic_eeval e0 c); assumption.
  subst.
  elim H12; reflexivity.
  
  (* or *)
  elim H9; intros.
  elim H5; intros.
  apply IHa1; try assumption.
  split; assumption.
  apply IHa2; try assumption.
  split; assumption.
  
  (* and *)
  elim H5; intros.
  elim H9; intros.
  apply IHa1; try assumption.
  split; assumption.
  apply IHa2; try assumption.
  split; assumption.
  
  (* neg *)
  apply IHa; try assumption. split; assumption.
  
                             (* if else *)
  apply IHa2; try assumption. split; assumption.
  apply IHa1; try assumption. split; assumption.
  apply IHa1; try assumption. split; assumption.
  apply IHa3; try assumption. split; assumption.
Qed.



Theorem invert_aeval :
  forall a c a' c', 
    normal_conf c ->
    normal_conf c' ->
    (aeval a c <-> aeval a' c') ->
    (aeval_f a c <-> aeval_f a' c').
  intros.
  split; intros.
  assert (aeval a' c' \/ aeval_f a' c').
    apply eval_or.
    assumption.
  elim H3; intros.
  apply H1 in H4.
  assert (aeval a c /\ aeval_f a c).
    split; assumption.
  assert (~(aeval a c /\ aeval_f a c)).
    apply eval_nand.
  contradiction.
  assumption.
  
  assert (aeval a c \/ aeval_f a c).
    apply eval_or.
    assumption.
  elim H3; intros.
  apply H1 in H4.
  assert (aeval a' c' /\ aeval_f a' c').
    split; assumption.
  assert (~(aeval a' c' /\ aeval_f a' c')).
    apply eval_nand.
  contradiction.
  assumption.
Qed.


End SemanticsAssertions.

Notation "'∥' a '∥' c" := (aeval a c) (at level 90).
(* Notation "'∥' e '∥' c" := (eeval e c) (at level 90). *)
