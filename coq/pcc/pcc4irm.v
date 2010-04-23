
Require Import list_utils.
Require Export validity.
Require Export security_defs.
Require Import ssreflect.



Section contracts.

  (* For simplicity: The ghost state is represented by a single fixed ghost variable 'gs'. *)
  (* We still have a notion of ghost valuations to be able to handle local ghost variables
     used for storing arguments and return values. *)
  Variable gs : ghostid.
  
  
  Lemma seen_ghost_updates_of_distr p :
    forall e1 e2, seen_ghost_updates_of p (e1 ++ e2) = seen_ghost_updates_of p e1 ++ seen_ghost_updates_of p e2. 
    induction e1; intros.
    repeat rewrite <- app_nil_end.
    reflexivity.
    rewrite list_rearrange3.
    simpl.
    destruct (ghost_update_of p a).
    rewrite list_rearrange3.
    rewrite IHe1.
    reflexivity.
    apply IHe1.
  Qed.
  
  Lemma gus_eq_seen_gus : forall p e c, 
    ghost_updates_of p (e ++ c :: nil) = seen_ghost_updates_of p e.
    induction e.
    reflexivity.
    intros.
    simpl.
    destruct (ghost_update_of p a).
    rewrite IHe.
    destruct e; [ | rewrite <- app_comm_cons ]; reflexivity.
    rewrite IHe.
    destruct e; [ | rewrite <- app_comm_cons ]; reflexivity.
  Qed.
  
  Lemma gu_impl_normal : forall `(ghost_update_of p c = Some gu), normal_conf c.
    intros.
    unfold ghost_update_of in H.
    assert (exists oi, current_instr p c = oi).
      exists (current_instr p c); reflexivity.
    elim H0; clear H0; intros.
    rewrite H0 in H.
    destruct x.
    destruct i; try discriminate.
    unfold current_instr in H0.
    destruct c.
    destruct l.
    destruct p0.
    discriminate.
    destruct a.
    destruct p0.
    apply is_norm_conf.
    destruct p0.
    discriminate.
    discriminate.
  Qed.
  
Lemma ghost_update_impl_ghost_instr :
  forall `(ghost_update_of p (gv, h, normal c m pc s ls :: ars0) = Some gu),
    instr_at p c m pc = ghost_instr gu.
Proof.
  intros.
  unfold ghost_update_of in H.
  assert (exists oi, current_instr p (gv, h, normal c m pc s ls :: ars0) = oi).
    exists (current_instr p (gv, h, normal c m pc s ls :: ars0)); reflexivity.
  elim H0; clear H0; intros.
  rewrite H0 in H.
  destruct x.
  destruct i; try discriminate.
  apply current_to_instr_at in H0.
  inversion H; subst.
  assumption.
  discriminate.
Qed.


  Lemma ex_seen_gus_impl_ex_gus : forall `(execution_of p e) `(seen_ghost_updates_of p e = gus),
    exists e', execution_of p e' /\ ghost_updates_of p e' = gus.
    destruct e using rev_ind; intros.
    exists nil.
    split; [apply exec_nil | ].
    rewrite <- H; reflexivity.
rename x into c.
generalize execution_of0; intros.
apply sub_execution in execution_of1.
pose proof (IHe execution_of1).
assert (exists ogu, ghost_update_of p c = ogu).
  exists (ghost_update_of p c); reflexivity.
elim H1; clear H1; intros.
destruct x.
(* last *is* a ghost update. e' needs to be an extended version of e. *)
destruct g as (gid, gexpr).
destruct c as (p0, ars).
destruct p0 as (gv, h).
pose proof (complete_geeval gexpr gv).
elim H2; intros v H_geeval.

pose proof (gu_impl_normal H1) as H_norm.
inversion H_norm; subst.
exists (e ++ (gv, h, normal c m pc s ls :: ars0) ::
      (upd_gv gv gid v, h, (normal c m (successor p c m pc) s ls) :: ars0) :: nil).
split.
(**)
apply exec_append; [assumption |].
apply tr_ghost.
apply tr_ghost_upd with (e := gexpr).
apply ghost_update_impl_ghost_instr in H1.
assumption.
assumption.

rewrite list_rearrange.
rewrite -app_nil_end.

have H3: (e ++ (gv, h, normal c m pc s ls :: ars0)
  :: (upd_gv gv gid v, h, normal c m (successor p c m pc) s ls :: ars0) :: nil 
  =
((e ++ (gv, h, normal c m pc s ls :: ars0)::nil) ++
  (upd_gv gv gid v, h, normal c m (successor p c m pc) s ls :: ars0) :: nil)) by rewrite app_ass -app_comm_cons.
rewrite H3 gus_eq_seen_gus {H3}.
reflexivity.

(* last is not a gu *)
rewrite seen_ghost_updates_of_distr in H.
simpl in H.
rewrite H1 in H.
rewrite <- app_nil_end in H.
apply (H0 gus).
assumption.
Qed.
    

  Inductive ss_after : sec_state -> list ghost_update -> sec_state -> Prop :=
  | ssaft_done : forall ss, ss_after ss nil ss
  | ssaft_step : forall ss ss' ss'' gvar exp v ssus,
        g_eeval exp ss v -> 
        ss' = (upd_gv ss gvar v) ->
        ss_after ss' ssus ss'' ->
        ss_after ss ((gvar, exp) :: ssus) ss''.


Lemma prefix_split : forall (l l' : list conf), prefix l l' -> exists l'', l' = l ++ l''.
induction l; intros.
exists l'; reflexivity.
inversion H; subst.
apply (IHl l'0) in H3.
elim H3; clear H3; intros.
subst.
exists x.
reflexivity.
Qed.


Lemma last_trans_app :  forall `(execution_of p (e ++ c :: c' :: nil)), trans p c c'.
intros.
inversion execution_of0.
apply (H0 e c c' nil).
reflexivity.
Qed.


Corollary last_trans : forall `(execution_of p (e ++ c' :: nil)) `(last e c), trans p c c'.
intros.
apply last_app_prefix in last0; try assumption.
elim last0; intros.
subst.
rewrite <- list_rearrange in execution_of0.
apply (last_trans_app execution_of0).
Qed.


Lemma non_ghost_instr_preservs_gv :
  forall `(trans p (gv, h, ar :: ars) (gv', h', ars')),
    (forall gu, current_instr p (gv, h, ar :: ars) <> Some (ghost_instr gu)) -> gv = gv'.
intros.
inversion trans0; subst.
inversion H2; subst; try (inversion H0; inversion H1; subst; reflexivity).
inversion H0; subst.
apply instr_at_to_current with (p := (gv, h')) (s := s) (l1 := ls) (l := ars) in H3.
pose proof (H (gvar, e)).
rewrite H3 in H1.
elim H1; reflexivity.
Qed.


(* To do; Find out if we're better of with ss_after as a fixpoint. *)
Lemma ss_after_total : forall ssus ss, exists ss'', ss_after ss ssus ss''.
induction ssus.
intros.
exists ss.
apply ssaft_done.

intros.

destruct a.
pose proof (complete_geeval e ss).
elim H; clear H; intros.
elim (IHssus (upd_gv ss g x)); intros ss''; intros.
exists ss''.

apply ssaft_step with (ss' := upd_gv ss g x) (v := x); try assumption.
reflexivity.
Qed.


Lemma ss_after_deterministic : forall ssus ss' ss'' ss,  ss_after ss ssus ss' -> ss_after ss ssus ss'' -> ss' = ss''.
intros until ss''.
induction ssus; intros ss ss_after0 ss_after1.
inversion ss_after0; inversion ss_after1; repeat subst.
reflexivity.
inversion ss_after0; inversion ss_after1; subst.
inversion H6; subst.
pose proof (deterministic_geeval H1 H8); subst.
apply (IHssus (upd_gv ss gvar v0) H5 H12).
Qed.



Lemma ghost_update_extension :
  forall x gv' h' ars' `(current_instr p (gv, h, ars) = Some (ghost_instr gu)),
    (ghost_updates_of p (x ++ (gv,h,ars) :: nil)) ++ gu :: nil =
        ghost_updates_of p (x ++ (gv,h,ars) :: (gv',h',ars') :: nil).
intros.
induction x.

assert (ghost_update_of p (gv, h, ars) = Some gu).
  unfold ghost_update_of.
  rewrite H.
  reflexivity.

simpl.
destruct ars.
inversion H.
destruct a.
rewrite H0.
reflexivity.
inversion H.

repeat rewrite list_rearrange3.

simpl.
rewrite <- IHx.

pose proof (app_cons_has_head (gv, h, ars) x nil) as H_eq1.
elim H_eq1; clear H_eq1; intros c1 H_eq1.
elim H_eq1; clear H_eq1; intros x1 H_eq1.

pose proof (app_cons_has_head (gv, h, ars) x ((gv', h', ars') :: nil)) as H_eq2.
elim H_eq2; clear H_eq2; intros c2 H_eq2.
elim H_eq2; clear H_eq2; intros x2 H_eq2.

rewrite H_eq1.
rewrite H_eq2.

destruct (ghost_update_of p a).
reflexivity.
reflexivity.
Qed.


Lemma ghost_update_noextension :
  forall p x gv h ars gv' h' ars',
    (forall gu, current_instr p (gv, h, ars) <> Some (ghost_instr gu)) ->
    ghost_updates_of p (x ++ (gv,h,ars) :: nil) =
        ghost_updates_of p (x ++ (gv,h,ars) :: (gv',h',ars') :: nil).
intros.
induction x.

assert (ghost_update_of p (gv, h, ars) = None).
  unfold ghost_update_of.
  destruct ars; try reflexivity.
  destruct a; intros; try reflexivity.
  
  assert (H_tmp : exists oi, instr_at p c m l = oi).
    exists (instr_at p c m l); reflexivity.
  elim H_tmp; clear H_tmp; intros i H_tmp.
  apply instr_at_to_current with (p := (gv, h)) (s := s) (l1 := l0) (l := ars) in H_tmp.
  rewrite H_tmp in H |- *.
  (* rewrite H_tmp in * |- *. *)
  destruct i; try reflexivity.
  pose proof (H g).
  
  contradict H0.
  simpl.
  reflexivity.

simpl.
destruct ars.
reflexivity.
destruct a; try reflexivity.
assert (exists oi, instr_at p c m l = oi).
  exists (instr_at p c m l); reflexivity.
elim H1; clear H1; intros i H1.
rewrite H0 in H |- *.
reflexivity.

repeat rewrite list_rearrange3.

simpl.
rewrite <- IHx.

pose proof (app_cons_has_head (gv, h, ars) x nil) as H_eq1.
elim H_eq1; clear H_eq1; intros c1 H_eq1.
elim H_eq1; clear H_eq1; intros x1 H_eq1.

pose proof (app_cons_has_head (gv, h, ars) x ((gv', h', ars') :: nil)) as H_eq2.
elim H_eq2; clear H_eq2; intros c2 H_eq2.
elim H_eq2; clear H_eq2; intros x2 H_eq2.

rewrite H_eq1.
rewrite H_eq2.
reflexivity.
Qed.


(* EXISTS_EXEC_WITH_EQ_GUS Begin *)
Section conf_classes.
  
  Variable (contr: contract) (p: program) (c: conf).
  
  Definition before_gu_conf cid mid : Prop :=
    current_instr p c = Some (ghost_instr (contr (before, cid, mid))).
  
  Definition before_ssu_conf cid mid : Prop :=
    current_instr p c = Some (invoke cid mid).
  
  Definition after_gu_conf cid mid : Prop :=
    current_instr p c = Some (ghost_instr (contr (after, cid, mid))).

  Definition after_ssu_conf cid mid : Prop :=
    class_of c = Some cid /\ meth_of c = Some mid /\ current_instr p c = Some ret.

  Definition non_sra_conf : Prop :=
    forall cid mid,
      ~ before_gu_conf  cid mid /\ ~ after_gu_conf  cid mid /\
      ~ before_ssu_conf cid mid /\ ~ after_ssu_conf cid mid.

  Lemma conf_cases_exhaustive :
    (exists cid, exists mid, before_gu_conf cid mid) \/
    (exists cid, exists mid, before_ssu_conf cid mid) \/
    (exists cid, exists mid, after_ssu_conf cid mid) \/
    (exists cid, exists mid, after_gu_conf cid mid) \/
    non_sra_conf.
  Admitted.

End conf_classes.

Lemma befgu_prec_befssu :
  forall contr `(execution_of p e) `(In c' e),
    (exists cid, exists mid, before_ssu_conf p c' cid mid) ->
    exists c, (exists cid, exists mid, before_gu_conf contr p c cid mid) /\
      exists pref, exists suff, e = pref ++ c :: c' :: suff.
Admitted.


Lemma aftssu_prec_aftgu :
  forall contr `(execution_of p e) `(In c' e),
    (exists cid, exists mid, after_gu_conf contr p c' cid mid) ->
    exists c, (exists cid, exists mid, after_ssu_conf p c cid mid) /\
      exists pref, exists suff, e = pref ++ c :: c' :: suff.
Admitted.


Lemma exec_tail_cases :
  forall contr
    `(ghost_inlined contr p pg)
    `(execution_of pg (e ++ c :: nil))
    `(ss_updates_of contr (event_trace_of pg (e ++ c :: nil)) ssus),
    let gus := seen_ghost_updates_of pg (e ++ c :: nil) in 
      (exists cid, exists mid, before_gu_conf contr pg c cid mid /\ ssus ++ (contr (before, cid, mid)) :: nil = gus) \/
      (exists cid, exists mid, before_ssu_conf pg c cid mid /\ ssus = gus) \/
      (exists cid, exists mid, after_ssu_conf pg c cid mid /\ ssus = gus ++ (contr (after, cid, mid)) :: nil) \/
      (exists cid, exists mid, after_gu_conf contr pg c cid mid /\ ssus = gus) \/
      (non_sra_conf contr pg c /\ ssus = gus).
move => contr p pg H.
elim/rev_ind => [c|c e].
(* base case *)
- pose proof (conf_cases_exhaustive contr pg c) as H0.
  move: H0 => 
    [ [cid [mid H_befgus] ]|
        [ [cid [mid H_befssu] ]|
          [ [cid [mid H_aftssu] ]|
            [ [cid [mid H_aftgu] ]|
              H_nonsra] ] ] ] H0 sus H1 gus.
  (* befgus *)
  * left; exists cid; exists mid.
    split; first done.
    rewrite /= in H1.
    have H2: sus = nil.
     inversion H1; first done.
     + rewrite /observed_event in H2.
       rewrite /before_gu_conf /current_instr in H_befgus.
       destruct c.
       destruct p0.
       destruct l; first done.
       destruct a; last done.
       inversion H_befgus.
       by rewrite H6 in H2.
     + rewrite /observed_event in H2.
       rewrite /before_gu_conf /current_instr in H_befgus.
       destruct c.
       destruct p0.
       destruct l; first done.
       destruct a; last done.
       inversion H_befgus.
       by rewrite H6 in H2.
    move: H1; rewrite H2 /gus /= /ghost_update_of {H2 gus} => H1.
    rewrite /before_gu_conf in H_befgus.
    by rewrite H_befgus.
  (* befssu *)
  * right; left; exists cid; exists mid.
    split; first done.
    have H2: In c (nil ++ c :: nil) by auto with datatypes.
    have H3: (exists cid, exists mid, before_ssu_conf pg c cid mid) by exists cid; exists mid.
    pose proof (befgu_prec_befssu contr H0 H2 H3) as H4.
    elim: H4 => c0 H4.
    elim: H4 => H4 H5.
    elim: H5 => pref H5.
    elim: H5 => suff H5.
    apply list_neq_length in H5; first by contradict H5.
    rewrite 2!app_length /= => H_eq.
    by omega.
  (* aftssu *)
  * right; right; left; exists cid; exists mid.
    split; first done.

(**)
have H_gusnil : gus = nil.
rewrite /gus.
rewrite /seen_ghost_updates_of.
simpl.
rewrite /ghost_update_of.
rewrite /after_ssu_conf in H_aftssu.
elim: H_aftssu => H_cid [H_mid H_ret].
by rewrite H_ret.
rewrite H_gusnil {H_gusnil gus} /=.

destruct c.
destruct l.
- destruct p0 as (gv, h).
  apply no_empty_ar_stack with (h := h) (gv := gv) in H0; first done.
  by auto with datatypes.
- destruct a.
  have H_aft: event_trace_of pg (nil ++ (p0, normal c m l0 s l1 :: l) :: nil) = (aft_event c m (s[[0]])) :: nil.
  rewrite /event_trace_of /observed_event.
  simpl.
  rewrite /after_ssu_conf in H_aftssu.
  elim: H_aftssu => [H_cid [H_mid H_ret] ].
  apply current_to_instr_at in H_ret.
  rewrite H_ret.
  by destruct p0.
rewrite H_aft in H1.
inversion H1.
inversion H7.
rewrite /after_ssu_conf in H_aftssu.
elim: H_aftssu => [H_cid [H_mid H_ret] ].
simpl in H_cid.
destruct p0.
simpl in H_mid.
inversion H_cid.
inversion H_mid.
by done.
apply exec_sing_impl_initial in H0.
by inversion H0.
      
  (* aftgu *)
  * right; right; right; left; exists cid; exists mid.
    split; first done.
    have H2: In c (nil ++ c :: nil) by auto with datatypes.
    have H3: (exists cid, exists mid, after_gu_conf contr pg c cid mid) by exists cid; exists mid.
    pose proof (aftssu_prec_aftgu contr H0 H2 H3) as H4.
    elim: H4 => c0 H4.
    elim: H4 => H4 H5.
    elim: H5 => pref H5.
    elim: H5 => suff H5.
    apply list_neq_length in H5; first by contradict H5.
    rewrite 2!app_length /= => H_eq.
    by omega.
  (* nonsra *)
  * right; right; right; right.
    split; first done.
    rewrite /non_sra_conf in H_nonsra.
    have H_gusnil : gus = nil.
      rewrite /gus /= /seen_ghost_updates_of /ghost_update_of {gus}.
      apply exec_sing_impl_initial in H0.
      (* kalle, hur gör man detta snyggt? *)
      have H_tmp : exists oi, oi = current_instr pg c.
        by exists (current_instr pg c).
      elim: H_tmp => oi H_eq.
      rewrite -H_eq.
      destruct oi.
      destruct i; try done.
      inversion H_eq.
      (* follows from H3 and H_nonsra (since c can't point at a ghost instr). *)
      (* I realize now that we may need an extra assumption for this lemma.
         (An assumption that anyway hold at the call site.) *)
      admit.
      done.
    
    have H_ssunil : sus = nil.
      (* should follow from the fact that c is neigther a call nor a ret (according to H_nonsra). *)
      admit.
    by rewrite H_gusnil H_ssunil.

(* inductive case *)

Admitted.

(* Work in progress. *)
Lemma exists_exec_with_eq_seen_gus :
    forall contr
      `(ghost_inlined contr p pg)
      `(execution_of pg eg)
      `(ss_updates_of contr (event_trace_of pg eg) ssus),
      exists e'g,
        execution_of pg e'g /\ seen_ghost_updates_of pg e'g = ssus.
Proof.
  intros.
  destruct eg using rev_ind; [| clear IHeg].
  exists nil.
  split; [apply exec_nil |].
  inversion ss_updates_of0.
  reflexivity.
  pose proof (exec_tail_cases contr ghost_inlined0 execution_of0 ss_updates_of0).
  rename eg into e0, x into c.
  elim H; clear H; intros H_tmp.
  
  (* case 1 *)
  elim H_tmp; clear H_tmp; intros cid H_tmp.
  elim H_tmp; clear H_tmp; intros mid H_tmp.
  elim H_tmp; clear H_tmp; intros.
  exists e0.
  split; [ apply sub_execution with (suff := c :: nil); assumption |].
  unfold before_gu_conf in H.
  rewrite seen_ghost_updates_of_distr in H0.
  simpl in H0.
  unfold ghost_update_of in H0.
  rewrite H in H0.
  apply app_inj_tail in H0.
  elim H0; intros.
  rewrite H1; reflexivity.
  
  (* case 2 *)
  elim H_tmp; clear H_tmp; intros H_tmp.
  elim H_tmp; clear H_tmp; intros cid H_tmp.
  elim H_tmp; clear H_tmp; intros mid H_tmp.
  elim H_tmp; clear H_tmp; intros.
  exists (e0 ++ c :: nil).
  split; [assumption |].
  rewrite H0; reflexivity.
  
  
  (* case 3 *)
  elim H_tmp; clear H_tmp; intros H_tmp.
  elim H_tmp; clear H_tmp; intros cid H_tmp.
  elim H_tmp; clear H_tmp; intros mid H_tmp.
  elim H_tmp; clear H_tmp; intros.
  destruct c.
  destruct p0 as (gv, h).
  destruct l.
  apply no_empty_ar_stack with (gv := gv) (h := h) in execution_of0.
  contradict execution_of0.
  auto with datatypes.
  
  exists (e0 ++ (gv, h, a :: l) :: (gv, h, l) :: nil).
  split.
  apply exec_append.
  assumption.
  
(**)
(* tr_ret *)
(**)
  admit.
  rewrite list_rearrange.
  rewrite seen_ghost_updates_of_distr.
  simpl.
  (* a ghost-after-update conf follows after a ret conf. *)
  assert (current_instr pg (gv, h, l) = Some (ghost_instr (contr (after, cid, mid)))).
  admit.
  unfold ghost_update_of.
  rewrite H1.
  rewrite H0.
  reflexivity.
  
  (* Case 4 *)
  elim H_tmp; clear H_tmp; intros H_tmp.
  elim H_tmp; clear H_tmp; intros cid H_tmp.
  elim H_tmp; clear H_tmp; intros mid H_tmp.
  elim H_tmp; clear H_tmp; intros.
  exists (e0 ++ c :: nil).
  split; subst; [assumption | reflexivity].
  
  (* Case 5 *)
  elim H_tmp; clear H_tmp; intros.
  exists (e0 ++ c :: nil).
  split; subst; [assumption | reflexivity].
Qed.


Corollary exists_exec_with_eq_gus :
    forall contr
      `(ghost_inlined contr p pg)
      `(execution_of pg eg)
      `(ss_updates_of contr (event_trace_of pg eg) ssus),
      exists e'g,
        execution_of pg e'g /\ ghost_updates_of pg e'g = ssus.
Proof.
intros.
pose proof (exists_exec_with_eq_seen_gus contr ghost_inlined0 execution_of0 ss_updates_of0).
elim H; clear H; intros.
elim H; clear H; intros.
apply (ex_seen_gus_impl_ex_gus H H0).
Qed.


(* EXISTS_EXEC_WITH_EQ_GUS End *)


Lemma len_sst_eq_S_len_ssus : forall `(sst_tail ssus sst), length sst = S (length ssus).
Proof.
induction ssus; intros.
inversion sst_tail0.
inversion H0.
reflexivity.
inversion sst_tail0.
inversion H0; subst.
assert (H_tmp : forall (a: ghost_valuation) l n, length l = n -> length (a :: l) = S n). simpl; auto.
apply (H_tmp ss (upd_gv ss gvar v :: sst0) (length ((gvar, exp) :: ssus))); clear H_tmp.
assert (H_tmp : length ((gvar, exp) :: ssus) = S (length ssus)). auto.
rewrite H_tmp; clear H_tmp.
apply IHssus.
assumption.
Qed.


Definition dummy_ss : sec_state := initial_gv.
Definition dummy_su : ghost_update := (O, valexp (ghost_errval)).


Lemma sst_follows_ssus :
  forall `(n < length (ss :: sst))
    `(sst_tail ssus (ss :: sst)),
    ss_after ss (firstn n ssus) (nth n (ss :: sst) dummy_ss).
Proof.
  induction n; intros.
  simpl.
  apply ssaft_done.
  destruct ssus.
  simpl.
  simpl in H.
  apply lt_S_n in H.
  inversion sst_tail0; subst.
  inversion H.
  simpl.
  destruct g.
  pose proof (complete_geeval e ss).
  elim H0; clear H0; intros v H_geeval.
  pose (upd_gv ss g v) as ss'.
  apply ssaft_step with (ss' := ss') (v := v).
  assumption.
  reflexivity.
  destruct sst.
  inversion H.
  inversion H1.
  assert (s = ss').
    inversion sst_tail0; subst.
    pose proof (deterministic_geeval H_geeval H4).
    rewrite <- H0 in *; clear H0.
    reflexivity.
  subst.
  apply IHn.
  simpl in H.
  apply lt_S_n in H.
  assumption.
  inversion sst_tail0.
  assumption.
Qed.


Lemma exists_ssus_prefix :
  forall `(is_sec_state_trace ssus sst),
    (forall ss, In ss sst ->
      exists ssus_pref, prefix ssus_pref ssus /\ ss_after initial_gv ssus_pref ss).
intros.
apply In_split in H.
elim H; clear H; intros pref H.
elim H; clear H; intros suff H.
subst.

exists (firstn (length pref) ssus).
split.
assert (length pref <= length ssus).
  inversion is_sec_state_trace0.
  apply len_sst_eq_S_len_ssus in H0.
  rewrite app_length in H0.
  simpl in H0.
  rewrite <- plus_Snm_nSm in H0.
  inversion H0.
  assert (H_tmp : forall n m, n <= n + m). intros; omega.
  apply H_tmp.

apply prefix_firstn; assumption.

assert (forall l l' (x : sec_state), nth (length l) (l ++ x :: l') dummy_ss = x).
  intros.
  induction l.
  reflexivity.
  assumption.

inversion is_sec_state_trace0.
assert (length pref < length (pref ++ ss :: suff)).
  rewrite app_length.
  assert (H_tmp : forall n m, n < n + (S m)). intros; omega.
  apply H_tmp.

destruct pref.

pose proof (sst_follows_ssus H2 H1).
simpl.
inversion is_sec_state_trace0.
inversion H4; subst.
apply ssaft_done.

rewrite list_rearrange3 in is_sec_state_trace0.
pose proof (sst_follows_ssus H2 H1).
rewrite <- list_rearrange3 in H3.
rewrite (H (s :: pref) suff ss) in H3.
inversion is_sec_state_trace0.
inversion H4; subst.
assumption.
Qed.


Lemma gus_pref_impl_exec_pref : forall p e gus_pref `(prefix gus_pref (ghost_updates_of p e)),
    exists e_pref, prefix e_pref e /\ ghost_updates_of p e_pref = gus_pref.
Proof.
 move => p.
 elim => [gus_pref prefix0|a l IH].
 - by exists nil; inversion prefix0; split; [ apply prefix_nil | done ].
 - case => [|g gus_pref].
   * by exists nil; split; [ apply prefix_nil | done ].
   * case H: (ghost_update_of p a) => [g0|] prefix0.
     + inversion prefix0 as [|g1 l' l0 H0 [H1 H2] H3].
       move: IH prefix0 H3.
       case: l => [|a' l] IH prefix0 H3; first done.
       pose proof (IH gus_pref) as H4.
       rewrite H {IH} in H3.
       move: H0; have -> : l0 = ghost_updates_of p (a' :: l) by inversion H3.       
       move => H0; apply H4 in H0.
       elim: H0. 
       case => [H0|a0 l1 H0]; elim: H0 => H0 H5.
       - exists (a :: a' :: nil); split; first by do 2!apply prefix_next; apply prefix_nil.
         by rewrite /= H -H5; inversion H3.
       - exists (a :: a0 :: l1); split; first by apply prefix_next.
         have H7: g = g0 by inversion H3.
         by rewrite -H5 H7 {1}/ghost_updates_of H.
     + pose proof (IH (g :: gus_pref)) as H0.
       move: IH prefix0 H0.
       case: l => [IH prefix0|a' l IH]; first by inversion prefix0.
       have -> : ghost_updates_of p (a :: a' :: l) = ghost_updates_of p (a' :: l) by rewrite {1}/ghost_updates_of H.
       move => prefix0 H0.
       apply H0 in prefix0.              
       elim: prefix0 => l' H1.
       elim: H1 => H1 H2.
       exists (a :: l'); split; first by apply prefix_next.           
       move: H1 H2.
       case: l' => [|a0 l'] H1 H2; first by inversion H2.
       by have -> : ghost_updates_of p (a :: a0 :: l') = ghost_updates_of p (a0 :: l') by rewrite {1}/ghost_updates_of H.
Qed.

Lemma to_be_or_not_to_be_ghost :
  forall p c, (exists gu, current_instr p c = Some (ghost_instr gu)) \/
    (forall gu, current_instr p c <> Some (ghost_instr gu)).
intros.
destruct c.
destruct l.
right.
intros.
compute.
intros.
destruct p0.
discriminate.
destruct a.
assert (exists oi, current_instr p (p0, normal c m l0 s l1 :: l) = oi).
  exists (current_instr p (p0, normal c m l0 s l1 :: l)); reflexivity.
elim H; clear H; intros.
destruct x.

destruct i; try (right; intros; rewrite H; discriminate).
left; exists g; rewrite H; reflexivity.

right.
intros.
rewrite H.
discriminate.
right.
intros.
simpl.
destruct p0.
discriminate.
Qed.


Lemma ss_after_update :
  forall ssus ss gv gid gexpr ss' v,
    ss_after ss ssus gv ->
    ss_after ss (ssus ++ (gid, gexpr) :: nil) ss' ->
    g_eeval gexpr gv v ->
    ss' = upd_gv gv gid v.
Proof.
induction ssus; intros.
inversion H; inversion H0; subst.
pose proof (deterministic_geeval H1 H8); subst.
inversion H11; subst.
reflexivity.

rewrite list_rearrange3 in H0.
destruct a.
pose proof (complete_geeval e ss) as H_geeval.
elim H_geeval; clear H_geeval; intros v2 H_geeval.
apply IHssus with (ss := upd_gv ss g v2) (gexpr := gexpr).
inversion H; subst.
pose proof (deterministic_geeval H_geeval H6); subst.
assumption.
inversion H0; subst.
pose proof (deterministic_geeval H_geeval H6); subst.
assumption.
assumption.
Qed.



Lemma trans_ghost_update :
  forall `(g_eeval gexpr gv v)
    `(trans p (gv, h, ars) (gv', h', ars'))
    `(current_instr p (gv, h, ars) = Some (ghost_instr (gid, gexpr))),
    gv' = upd_gv gv gid v.

intros.
inversion trans0; inversion H2; subst; try (
  inversion H1; inversion H0; subst; inversion H; rewrite H6 in H4 |- *; subst; done).

inversion H0; subst.

apply current_to_instr_at in H.
rewrite H in H3.
inversion H3.
subst.
rewrite (deterministic_geeval g_eeval0 g_eeval1).
reflexivity.
Qed.


(* ss_AFTER means after the su of the last conf. gv_last is the gv AT the last conf.
   This poses an off-by-one problem that may be resolved by taking the ssus of only e.
   Let's try it out and see if the lemma still fits.

   EDIT: This has now been fixed with a more appropriate definition of ghost_updates_of. *)
Lemma ss_after_equals_gv_last :
  forall `(last e (gv, h, ars))
    `(execution_of p e)
     `(ss_after initial_gv (ghost_updates_of p e) ss),
    ss = gv.
Proof.

  destruct e using rev_ind.
  intros.
  inversion last0.
  
  intros.
  apply last_app_cons in last0; subst.
  
  (* In order to make use of IHe, we need [last e (gv', h', ars')]. That is, we need to know that
     e <> nil. *)
  destruct (nil_or_app e).
  (* Case e = nil *)
  subst.
  simpl in *.
  inversion ss_after0; subst.
  inversion execution_of0; subst.
  assert (initial_conf (gv, h, ars)).
    apply H; auto.
  inversion H1; subst.
  reflexivity.
  
  (* Case e = x ++ c :: nil *)
  rename ss into ss', gv into gv', h into h', ars into ars'.
  elim H; clear H; intros.
  elim H; clear H; intros.
  subst.
  destruct x0 as (p0, ars).
  destruct p0 as (gv, h).
  
  pose proof (sub_execution p (x ++ (gv, h, ars) :: nil) ((gv', h', ars') :: nil) execution_of0).
  pose proof (IHe gv h ars (app_last x (gv, h, ars)) p H).
  
  
  pose proof (ss_after_total (ghost_updates_of p (x ++ (gv, h, ars) :: nil)) initial_gv) as H_tmp.
  elim H_tmp; clear H_tmp; intros ss2 H_ssaft.
  pose proof (H0 ss2 H_ssaft).
  subst.

  (* Case-split on the type of instruction in (gv, h, ars). *)
  pose proof (to_be_or_not_to_be_ghost p (gv, h, ars)).
  elim H1; clear H1; intros.
  
  (* if (gv, h, ars) *does* point at a ghost instruction (with update "gu"), then
     (ghost_updates_of p (x ++ (gv,h,ars)                  :: nil)) ++ gu  equals
      ghost_updates_of p (x ++ (gv,h,ars) :: (gv',h',ars') :: nil)
      
      Since H_ssaft says
      ss_after initial_gv (ghost_updates_of p (x ++ (gv, h, ars) :: nil)) gv
      and ss_after0 says
      ss_after initial_gv
      (ghost_updates_of p ((x ++ (gv, h, ars) :: nil) ++ (gv', h', ars') :: nil)) ss'
      we know that the last update (gu) updates gv to ss'.
      And since execution_of0 says that (gv,h,ars)->(gv',h',ars') we have that gu updates gv to gv'
      Since ghost-updates are deterministic, ss' = gv'.
  *)
  elim H1; clear H1; intros gu H1.
  pose proof (ghost_update_extension x gv' h' ars' H1) as H_eq.
  
  destruct gu as (gid, gexpr).
  pose proof (complete_geeval gexpr gv).
  elim H2; clear H2; intros v H2.

  rewrite <- list_rearrange in ss_after0.
  rewrite <- H_eq in ss_after0.
  pose proof (ss_after_update _ _ _ _ _ _ _ H_ssaft ss_after0 H2) as H_gv_upd.
  
  (* From execution_of0 *)
  assert (H_trans : trans p (gv, h, ars) (gv', h', ars')).
    inversion execution_of0.
    apply H4 with (pref := x) (suff := nil).
    rewrite <- list_rearrange; reflexivity.
  pose proof (trans_ghost_update H2 H_trans H1).
  
  subst.
  reflexivity.

  (* if (gv, h, ars) *does not* point at a ghost instruction, then
     ghost_updates_of p (x ++ (gv,h,ars)                  :: nil)  =
     ghost_updates_of p (x ++ (gv,h,ars) :: (gv',h',ars') :: nil)
     
     Rewriting ss_after0 using the above equality yields 
     ss_after initial_gv (ghost_updates_of p (x ++ (gv, h, ars) :: nil)) ss'
     and H_ssaft says
     ss_after initial_gv (ghost_updates_of p (x ++ (gv, h, ars) :: nil)) gv
     Since ss_after is deterministic, we have ss' = gv.
     execution_of0 says that (gv,h,ars) -> (gv',h',ar's) and since (gv,h,ars) does not point
     at a ghost-update, gv = gv'.
     Thus, ss' = gv'.
  *)
  
  assert (H_eq : ghost_updates_of p (x ++ (gv,h,ars) :: nil) =
                 ghost_updates_of p (x ++ (gv,h,ars) :: (gv',h',ars') :: nil)).

  rewrite <- list_rearrange in execution_of0.
  apply (ghost_update_noextension _ _ _ _ _ _ _ _ H1).
  
  rewrite <- list_rearrange in ss_after0.
  rewrite <- H_eq in ss_after0.
  pose proof (ss_after_deterministic _ _ _ _ ss_after0 H_ssaft).
  
  rewrite <- list_rearrange in execution_of0.
  destruct ars.
  apply no_empty_ar_stack with (gv:= gv) (h := h) in H.
  contradict H.
  auto with datatypes.
  pose proof (non_ghost_instr_preservs_gv (last_trans_app execution_of0) H1).
  subst.
  reflexivity.
Qed.


  Lemma non_empty_exec_has_initial_gv :
    forall `(execution_of p e), e <> nil -> exists h, exists ars, In (initial_gv, h, ars) e.
  Proof.
    intros.
    inversion execution_of0.
    destruct e; subst.
    contradict H; reflexivity.
    exists empty_heap; exists (normal maincid mainmid O emptystack (fun n => undefval) :: nil).
    assert (initial_conf c).
    apply H0.
    reflexivity.
    rewrite H2.
    apply in_eq.
  Qed.
  
  
Lemma ssus_eq_gus_impl_sst_subset_gvs :
  forall contr
    `(execution_of p e)
    `(execution_of p (e' ++ c' :: nil))
    `(ss_updates_of contr (event_trace_of p e) ssus)
    `(is_sec_state_trace ssus sst),
    ghost_updates_of p (e' ++ c' :: nil) = ssus ->
    (forall ss, In ss sst -> exists h, exists ars, In (ss, h, ars) (e' ++ c' :: nil)).
Proof.
(* 1. Pick an arbitrary ss in sst (and then show that (ss, _, _) in e'++c' *)
intros.

(* 2. Let pref denote the prefix of ssus(E) which takes the initial sec-state to ss. *)
pose proof (exists_ssus_prefix is_sec_state_trace0 ss H0) as H_tmp.
elim H_tmp; clear H_tmp; intros pref H_tmp.
elim H_tmp; clear H_tmp; intros H_pref H_ssaft.

(* 3. pref is also a prefix of gus(e' ++ c') *)
rewrite <- H in H_pref.

(* 4. There exizts an e_pref such that gus(e_pref) = pref. *)
apply gus_pref_impl_exec_pref in H_pref.
elim H_pref; clear H_pref; intros e_pref H_pref.
elim H_pref; clear H_pref; intros H_pref H_gus_eq_pref.

rewrite <- H_gus_eq_pref in H_ssaft.

(* To apply ss_after_equals_gv_last, we need e_pref <> nil. *)
(* Get rid of e_pref = nil case. *)
destruct (nil_or_app e_pref); subst.
  (* case e_pref = nil *)
  inversion H_ssaft; subst.
  apply (non_empty_exec_has_initial_gv execution_of1).
  apply list_neq_length; rewrite app_length; simpl; omega.

  (* case e_pref = l' ++ a *)
  apply prefix_split in H_pref.
  elim H_pref; intros e_suff H.
  assert (H_exec_pref : execution_of p e_pref).
    rewrite H in execution_of1.
    apply sub_execution with (suff := e_suff); assumption.
  elim H1; clear H1; intros l' H1.
  elim H1; clear H1; intros.
  subst.
  destruct x as (gv_h, ars); destruct gv_h as (gv, h).
  pose proof (ss_after_equals_gv_last (app_last l' (gv, h, ars)) H_exec_pref H_ssaft).
  subst.
  rewrite H.
  exists h; exists ars.
  auto with datatypes.
Qed.



(* For an inlined program with sec-state trace SST, there exist an execution
     of the same program for which SST is a subset of the gvs. *)
(* The alternative succedent [\/ ss = initial_gv] is due to the fact that the
   empty execution may have the same gus as ssus, which yields an empty gv-trace.
   The sst however, will always at least contain the initial_gv. *)
  Lemma sst_subset_gvs :
    forall contr
      `(ghost_inlined contr p pg)
      `(execution_of pg eg)
      `(ss_updates_of contr (event_trace_of pg eg) ssus)
      `(is_sec_state_trace ssus sst),
      exists e'g,
        execution_of pg e'g /\
        (forall ss, In ss sst -> (exists h, exists ars, In (ss, h, ars) e'g) \/ ss = initial_gv).
  Proof.
    
    intros.
    
    pose proof (exists_exec_with_eq_gus contr ghost_inlined0
      execution_of0 ss_updates_of0).
    elim H; clear H; intros e'g H.
    elim H; clear H; intros.
    exists e'g.
    split; [ assumption | ].
    
    (* We need to have an e'g <> nil, otherwise we run into the situation in which ssus = nil,
       gvs = nil, but sst = initial_gv :: nil. *)

    (* Get rid of the case in which e'g = nil. *)
    destruct (nil_or_app e'g).
    subst.
    inversion ss_updates_of0.
    rewrite <- H1 in *.
    inversion is_sec_state_trace0.
    inversion H2; subst.
    intros; right.
    inversion H0.
    inversion H3; subst; try contradiction.
    rewrite H4; reflexivity.

    (* Case e'g = l' ++ a. *)
    elim H1; clear H1; intros e'g_pref H1.
    elim H1; clear H1; intros c' H1.
    rewrite H1 in H H0 |- *.
    
    intros.
    left.
    
    apply (ssus_eq_gus_impl_sst_subset_gvs contr execution_of0 H
      ss_updates_of0 is_sec_state_trace0 H0 ss H2).
  Qed.
  
  
  Theorem never_wrong_impl_ghost_adherence p contr `(ghost_inlined contr p pg) :
    (forall eg,
      execution_of pg eg ->
      exec_never_goes_wrong gs eg) ->
    adheres_to gs pg contr.
  Proof.
    unfold adheres_to.
    unfold accepted_by.
    intros.
    
    pose proof sst_subset_gvs.
    
    elim (H4 contr p pg ghost_inlined0 e execution_of0 gus H0 sec_tr H1); try assumption.
    intros e'g H_tmp.
    elim H_tmp; clear H_tmp; intros.
    
    apply H6 in H3.
    
    elim H3; clear H3; intros H3.
    
    (* case ss in e'g *)
    elim H3; intros h H_tmp.
    elim H_tmp; clear H_tmp; intros ars H'.
    apply H in H5.
    unfold exec_never_goes_wrong in H5.
    apply H5 in H'.
    auto.
    
    (* case ss = initial_gv *)
    subst.
    unfold violating_sec_state.
    unfold initial_gv.
    intro.
    discriminate H3.
  Qed.
  
  
  Section ghost_simulation.
    
    Variable contr: contract.
    Variable p pg: program.
    Hypothesis gi_p_pg : ghost_inlined contr p pg.
    
    (* Why do we need a pg (ghost inlined version of p) as a variable / param
       in this section?
       Otherwise we wouldn't know which labels to expect in the simulated
       execution. (The ghost inliner is formalized as a relation (not a
       function), and instructions are arbitrarily labeled by a labeling
       function. *)
    
    Inductive ars_sim_head : option act_record -> option act_record -> Prop :=
    | ars_exc : forall o, ars_sim_head (Some (exceptional o)) (Some (exceptional o))
    | ars_inv : forall c m pc s l slg,
          (exists c', exists m', instr_at p c m pc = invoke c' m') ->
          slg = label_function_of (classes pg c m) ->
          ars_sim_head (Some (normal c m pc s l)) (Some (normal c m (slg pc) s l))
    | ars_non_inv : forall c m pc s l,
          (forall c' m', instr_at p c m pc <> invoke c' m') ->
          ars_sim_head (Some (normal c m pc s l)) (Some (normal c m pc s l)).
    
    Inductive ars_sim_tail : (list act_record) -> (list act_record) -> Prop :=
    | ars_base : ars_sim_tail nil nil
    | ars_subst : forall c m s l ars ars' sl slg pc,
          ars_sim_tail ars ars' ->
          (exists c', exists m', instr_at p c m pc = invoke c' m') ->
          sl = label_function_of (classes p c m) ->
          slg = label_function_of (classes pg c m) ->
          ars_sim_tail ((normal c m (sl pc) s l) :: ars) ((normal c m (slg (slg pc)) s l) :: ars')
    | ars_skip : forall c m s l ars ars' pc sl,
          ars_sim_tail ars ars' ->
          (forall c' m', instr_at p c m pc <> invoke c' m') ->
          sl = label_function_of (classes p c m) ->
          ars_sim_tail ((normal c m (sl pc) s l) :: ars) ((normal c m (sl pc) s l) :: ars').
    
    
    Definition sim_p (c cg: conf) := heap_of c = heap_of cg /\
      ars_sim_head (head (ars_of c)) (head (ars_of c)) /\
      ars_sim_tail (ars_of c) (ars_of cg).

    Notation "c1 'sim' c2 " := (sim_p c1 c2) (at level 90).
    
    
    (* Work in progress. 2010-04-16. *)
    (* See notes for a proof on paper. *)
    Lemma pg_simulates_p_base :
      forall `(initial_conf c0),
        exists eg,
          execution_of pg eg /\
          event_trace_of p (c0 :: nil) = event_trace_of pg eg /\
          (exists c'g, last eg c'g /\ (c0 sim c'g)).
    Admitted.
    Lemma pg_simulates_p_step :
      forall c cg c',
        c sim cg ->
        trans p c c' ->
        (exists eg, exists c'g, trans_star pg (cg :: eg ++ c'g :: nil) /\
          (c' sim c'g) /\
          event_trace_of p (c' :: nil) = event_trace_of pg (eg ++ c'g :: nil)).
    Admitted.
  
  End ghost_simulation.
  
  
  Lemma ghost_inl_preservs_obs_trace_strong :
    forall p `(execution_of p e) contr `(ghost_inlined contr p pg),
      exists eg, execution_of pg eg /\ event_trace_of pg eg = event_trace_of p e /\
        (forall lc, last e lc -> exists lcg, last eg lcg /\ sim_p p pg lc lcg).
  Proof.
    intros.
    destruct e using rev_ind.
    
    (* Base case: e = nil *)
    exists nil.
    split; [| split].
    apply exec_nil.
    reflexivity.
    intros.
    inversion H.
    
    (* Inductive step: e = e' ++ x *)
    (* Let's figure out if we should apply "initial conf" step, or inductive step of simulation. *)
    assert (H_tmp: e = nil \/ exists e', exists c, e = e' ++ c :: nil).
      apply nil_or_last.
    
    elim H_tmp; clear H_tmp; intros; subst.
    
    (* e = nil  =>  initial-conf step *)
    pose proof (pg_simulates_p_base).
    elim (H p pg x); intros.
    exists x0.
    elim H0; clear H0; intros.
    elim H1; clear H1; intros.
    elim H2; clear H2; intros.
    elim H2; clear H2; intros.
    split; [| split].
    assumption.
    rewrite <- H1.
    reflexivity.
    intros.
    exists x1.
    split.
    assumption.
    apply last_app_cons in H4.
    subst.
    assumption.
    inversion execution_of0.
    apply H0.
    auto.
    
    (* e = (c :: e) ++ x *)
    elim H; clear H; intros e' H.
    elim H; clear H; intros c H.
    subst.
    assert (execution_of p (e' ++ c :: nil)).
      apply sub_execution2 with (c' := x).
      rewrite app_ass in execution_of0.
      assumption.
    apply IHe in H.
    elim H; clear H; intros.
    elim H; clear H; intros.
    elim H0; clear H0; intros.
    
    pose proof (H1 c).
    clear H1.
    assert (last (e' ++ c :: nil) c).
      apply last_app.
      apply last_base.
    apply H2 in H1.
    clear H2.
    elim H1.
    intros.
    elim H2; clear H2; intros.
    
    pose proof (pg_simulates_p_step).
    elim (H4 p pg c x1 x); clear H4.
    intros egPref H_tmp.
    elim H_tmp; clear H_tmp; intros c'g H_tmp.
    elim H_tmp; clear H_tmp; intros H_trans_star H_tmp.
    elim H_tmp; clear H_tmp; intros.
    
    exists (x0 ++ egPref ++ c'g :: nil).
    split; [| split].

    apply exec_intros.
    inversion H.
    intros.
    apply H6.
    inversion H2.
    rewrite <- H9.
    rewrite <- H10.
    simpl.
    subst.
    reflexivity.
    rewrite <- H9.
    rewrite <- H11.
    simpl.
    reflexivity.

    intros.
    apply exec_impl_trans_star in H.
    apply last_app_prefix in H2.
    elim H2; intros.
    subst.
    rewrite <- list_rearrange in H6.
    apply trans_star_seq with (e2 := egPref ++ c'g :: nil) in H; try assumption.
    rewrite H6 in H.
    apply trans_star_suff in H.
    inversion H.
    assumption.
    assumption.
    
    rewrite (event_trace_distr pg x0).
    rewrite (event_trace_distr _ (e' ++ c :: nil) (x :: nil)).
    rewrite H5.
    rewrite H0.
    reflexivity.
    
    intros.
    exists c'g.
    split.
    apply last_app; apply last_app; apply last_base.
    
    apply last_app_prefix in H6.
    elim H6; intros.
    apply app_inj_tail in H7.
    elim H7; intros; subst.
    assumption.
    assumption.
    
    assumption.
    inversion execution_of0.
    apply H5 with (pref := e') (suff := nil).
    rewrite app_ass.
    reflexivity.
  Qed.
  
  
  Corollary ghost_inl_preservs_obs_trace :
    forall p `(execution_of p e) contr `(ghost_inlined contr p pg),
      exists eg, execution_of pg eg /\ event_trace_of pg eg = event_trace_of p e.
  Proof.
    intros.
    pose proof (ghost_inl_preservs_obs_trace_strong p (execution_of0) contr ghost_inlined0).
    elim: H => x H.
    elim: H => H H0.
    elim: H0 => H0.
    by exists x.
  Qed.
  
  Lemma ghost_adherence_impl_actual_adherence :
    forall p contr, (exists pg, ghost_inlined contr p pg /\ adheres_to gs pg contr) -> adheres_to gs p contr.
  Proof.
    intros p contr H.
    unfold adheres_to.
    intros.
    elim H; clear H; intros pg H_g_inad.
    elim H_g_inad; clear H_g_inad; intros H_g_in H_g_ad.
    
    assert (H_sim: exists eg, execution_of pg eg /\ event_trace_of pg eg = event_trace_of p e).
      apply ghost_inl_preservs_obs_trace with (p := p) (e := e) (contr := contr); assumption.
    
    elim H_sim.
    intros eg [H_exg H_trg].
    apply H_g_ad in H_exg.
    rewrite H_trg in H_exg.
    assumption.
  Qed.
  
  
  Corollary never_wrong_impl_adherence p contr :
    (exists pg,
      ghost_inlined contr p pg /\
      forall `(execution_of pg gexec), exec_never_goes_wrong gs gexec) ->
      adheres_to gs p contr.
  Proof.
    intros.
    elim H; intros pg H_gadh.
    elim H_gadh; intros.
    apply ghost_adherence_impl_actual_adherence.
    exists pg.
    split.
    assumption.
    apply never_wrong_impl_ghost_adherence with (p := p) (pg := pg).
    assumption.
    intros.
    apply H1.
    assumption.
  Qed.
  
  
  Definition stronger_ast a a' := forall c, ∥ a ∥ c -> ∥ a' ∥ c.
  

Lemma ghostid_neq_false : forall g1 g2 : ghostid, g1 <> g2 -> beq_nat g1 g2 = false.
  induction g1; intros.
  destruct g2.
  elim H; reflexivity.
  reflexivity.
  destruct g2.
  reflexivity.
  simpl.
  assert (g1 <> g2).
    intro; elim H; intros; rewrite H0; reflexivity.
  apply (IHg1 _ H0).
Qed.
  

Lemma ghostid_eq_dec : forall g1 g2: ghostid, g1 = g2 \/ g1 <> g2.
  induction g1; intros.
  destruct g2.
  left; reflexivity.
  right; auto.
  destruct g2.
  right; auto.
  elim (IHg1 g2); intros.
  left; rewrite H; reflexivity.
  right.
  intro.
  contradict H.
  inversion H0.
  reflexivity.
Qed.


(* Lemma: only way to go from non-violating conf to violating conf is to execute a ghost instr with rhs evaluating to \bot *)
Lemma non_vio_to_vio_impl_ghost_err :
  forall p c c',
    ~ violating_sec_state gs (ghost_valuation_of c) ->
    trans p c c' ->
    violating_sec_state gs (ghost_valuation_of c') ->
    exists gexpr,
      current_instr p c = Some (ghost_instr (gs, gexpr)) /\
      g_eeval gexpr (ghost_valuation_of c) ghost_errval.
intros.
assert (H_gv: ghost_valuation_of c <> ghost_valuation_of c').
  intro.
  elim H.
  rewrite H2.
  assumption.
inversion H0; subst.
inversion H4; subst; try (elim H_gv; reflexivity).
inversion H2; subst.

assert (H_tmp : ghost_valuation_of (upd_gv gv gvar v, h, normal c0 m (successor p c0 m pc) s ls :: ars) = upd_gv gv gvar v).
  reflexivity.
rewrite H_tmp in H1; clear H_tmp.
assert (H_tmp : ghost_valuation_of (gv, h, normal c0 m pc s ls :: ars) = gv).
  reflexivity.
rewrite H_tmp in H; clear H_tmp.



exists e.
split.
apply instr_at_to_current.

pose proof ghostid_eq_dec.
pose proof (H4 gvar gs).
elim H5; intros; subst.
(* case gvar = gs *)
assumption.

(* case gvar <> gs *)
contradict H.
unfold violating_sec_state in H1.
unfold violating_sec_state.
unfold upd_gv in H1.
pose proof (ghostid_neq_false).
rewrite H in H1.
assumption.

intro.
elim H6.
rewrite H1; reflexivity.

unfold violating_sec_state in H1.
unfold violating_sec_state in H.
assert (H_tmp : ghost_valuation_of (gv, h, normal c0 m pc s ls :: ars) = gv).
  reflexivity.
rewrite H_tmp; clear H_tmp.

pose proof ghostid_eq_dec.
pose proof (H4 gvar gs).
elim H5; clear H5; intros.
unfold upd_gv in H1.
assert (beq_nat gs gvar = true).
  rewrite H5.
  rewrite (beq_nat_refl gs).
  reflexivity.
rewrite H6 in H1.
subst.
assumption.

pose proof ghostid_neq_false.

unfold upd_gv in H1.
rewrite H6 in H1.
elim H; assumption.
intro; elim H5; subst; reflexivity.
Qed.


  Lemma eval_gv_neq_undefex_impl_gs_neq_ghost_errval : forall c gs,
    ∥ neg (eq (ghost_var gs) ghost_errval) ∥ c ->
    ~ eeval (ghost_var gs) c ghost_errval.
  Proof.
    intros.
    intro.
    inversion H0; subst.
    inversion H; subst.
    inversion H2; subst.
    inversion H5; subst.
    inversion H6; subst.
    elim H8; assumption.
    elim H8; assumption.
  Qed.
  
  
  Lemma initial_not_violating :
    forall c, initial_conf c -> ~ violating_sec_state gs (ghost_valuation_of c).
  Proof.
    intros.
    intro.
    inversion H; subst.
    unfold ghost_valuation_of in H0.
    simpl in H0.
    inversion H0.
  Qed.
  
  
  (* Given a locally valid (ghost) program pg,
       if the instruction at label l is a ghost instruction
         and the successor of l is l'
         and the annotation of l' is something stronger than [gs != \bot]
       then forall executions ex of pg, ex never goes wrong. *)
  Lemma sufficient_never_go_wrong_annos pg :
    locally_valid pg ->
    (forall c m l l' gu a,
      instr_at pg c m l = ghost_instr gu ->
      label_function_of (classes pg c m) l = l' ->
      annotations_of (classes pg c m) l' = a ->
      stronger_ast a (neg (eq (ghost_var gs) ghost_errval))) ->
    forall `(execution_of pg exec), exec_never_goes_wrong gs exec.
  Proof.
intros.
destruct exec using rev_ind.

(* Base case: exec = nil *)
unfold exec_never_goes_wrong.
intros.
auto.

(* Inductive case: exec = exec ++ c' *)
rename x into c'.

unfold exec_never_goes_wrong.
intros.
apply in_app_or in H1.
elim H1; intros.
apply IHexec.
apply sub_execution with (suff := c' :: nil); assumption.
assumption.
inversion H2; subst; auto.

rename c into c'.

clear H1 H2.

pose proof (nil_or_app exec) as H_tmp.
elim H_tmp; intros; clear H_tmp.

(* Case exec = c c'*)
subst.

inversion execution_of0.
apply initial_not_violating.
apply H1.
auto.

(* Case exec = exec' c c' *)
elim H1; clear H1; intros exec' H_tmp.
elim H_tmp; clear H_tmp; intros.
subst.

rename x into c.

pose proof (non_vio_to_vio_impl_ghost_err pg c c').

generalize execution_of0; intro H_exec.
apply sub_execution in H_exec.
apply IHexec in H_exec.
unfold exec_never_goes_wrong in H_exec.
pose proof (H_exec c).
assert (H_1 : ~ violating_sec_state gs (ghost_valuation_of c)).
  apply H2; auto with datatypes.

intro.

apply H1 in H_1.

elim H_1; clear H_1; intros x H_tmp.
elim H_tmp; clear H_tmp; intros H_curr_inst H_geval.

destruct c.
destruct l.

unfold current_instr in H_curr_inst.
contradict H_curr_inst.
destruct p; discriminate.

destruct a.

(* top ar is normal *)
pose proof (H0 c m l0 (label_function_of (classes pg c m) l0) (gs, x) (annotations_of (classes pg c m) (label_function_of (classes pg c m) l0))).
clear H0.

apply current_to_instr_at in H_curr_inst.
rewrite H_curr_inst in H4.

assert (H_tmp : ghost_instr (gs, x) = ghost_instr (gs, x)).
  reflexivity.
apply H4 in H_tmp; try reflexivity.
unfold stronger_ast in H_tmp.

apply local_impl_global in H.
unfold globally_valid in H.
generalize execution_of0; intros.
apply H in execution_of1.
apply valid_exec_last in execution_of1.
inversion execution_of1.

(* since previous conf is normal, and instr at prev conf is a ghost instr, last conf (c') is normal too. *)
assert (normal_conf c').
  (* the exact shape of c' can be determined through the shape of c, and instr_at.
     This is also needed elsewhere so it should be extracted to right after we conclude that
     the current instr is a ghost instr. *)
  assert (H_trans : trans pg (p, normal c m l0 s l1 :: l) c').
    generalize execution_of0; intros.
    inversion execution_of2.
    apply H7 with (pref := exec') (suff := nil).
    rewrite <- list_rearrange.
    reflexivity.
    inversion H_trans; subst.
    
   inversion H8; subst;
      injection H6; try rewrite H_curr_inst; done.

    inversion H6; subst.
    apply is_norm_conf.


apply H5 with (a := annotations_of (classes pg c m) (label_function_of (classes pg c m) l0)) in H6.
apply H_tmp in H6.
assert (∥neg (eq (ghost_var gs) ghost_errval) ∥ c' -> ~ eeval (ghost_var gs) c' ghost_errval).
  apply eval_gv_neq_undefex_impl_gs_neq_ghost_errval.

apply H7 in H6.
elim H6.
unfold violating_sec_state in H3.
destruct c'.
destruct p0.
rewrite <- H3.
apply e_ghostvar.


assert (H_trans : trans pg (p, normal c m l0 s l1 :: l) c').
  generalize execution_of0; intros.
inversion execution_of2.
apply H8 with (pref := exec') (suff := nil).
rewrite <- list_rearrange.
reflexivity.
inversion H_trans; subst.

inversion H9; subst;
injection H7; intros; subst; rewrite H_curr_inst in H4 H8 |-; try done.

(*--*)
(*
inversion H9; subst;
injection H7; intros; subst;
rewrite H_curr_inst in * |-; try discriminate.
*)

(**)
inversion H7; subst.
(* according to H_curr_inst and H17, gvar=gs and x=e*)
simpl.
unfold ast_at.
unfold successor.
reflexivity.
inversion H_curr_inst.
destruct p.
discriminate.

inversion execution_of0. 
apply H5 with (pref := exec') (suff := nil). 
rewrite <- list_rearrange. 
reflexivity.

assumption.
Qed.


Lemma tmp7 : forall c e, ~ ghost_expr e -> ~ eeval e c ghost_errval.
intros.
intro.
elim H.
induction e; try (inversion H0; subst).
left; apply sub_base.
left; apply sub_base.
unfold ghost_expr.
right.
exists g.
apply sub_base.
assert (~ ghost_expr e2).
  intro.
  elim H.
  elim H1; intros.
  unfold ghost_expr.
  left.
  apply sub_guarded.
  right; left.
  assumption.
  right.
  elim H2; intros.
  exists x.
  apply sub_guarded.
  right; left.
  assumption.

generalize H1; intros.
apply IHe2 in H1.
elim H2; assumption.
assumption.

assert (~ ghost_expr e3).
  intro.
  elim H.
  elim H1; intros.
  unfold ghost_expr.
  left.
  apply sub_guarded.
  right; right.
  assumption.
  right.
  elim H2; intros.
  exists x.
  apply sub_guarded.
  right; right.
  assumption.

generalize H1; intros.
apply IHe3 in H1.
elim H2; assumption.
assumption.
Qed.

(* ~ ghost_expr e ->  gs = e  STRONGER THAN  gs <> ghost_errexp *)
  Lemma non_ghost_stronger_than_non_err :
    forall e, ~ ghost_expr e ->
              stronger_ast (eq (ghost_var gs) e) (neg (eq (ghost_var gs) ghost_errval)).
intros.
unfold stronger_ast.
intros.
apply e_neg.
inversion H0; subst.
apply e_eq_f with (v1 := v) (v2 := ghost_errval).
assumption.
apply e_ghosterr.
intro.
subst.
apply (tmp7 c e) in H.
elim H.
assumption.
Qed.
  
  
  Definition prog_annotations := classid -> methid -> label -> ast.
  
  
  Definition annotated_with p annos : Prop :=
    forall c m l, annotations_of (classes p c m) l = annos c m l.


  (* For a given p, contr: annos is a proof outline if
       there exists a ghost inlined version pg,
         which is annotated with annos, and locally valid
         such that
           forall labels, l, pointing at a ghost-update
           the successor label l'
           should be annotated with [gs = e] where e is a non-ghost expression *)
  Definition is_proof_outline (p: program) (contr: contract) (annos : prog_annotations) :=
    exists pg,
      ghost_inlined contr p pg /\
      annotated_with pg annos /\
      locally_valid pg /\
      forall c m l l' gu,
        instr_at pg c m l = ghost_instr gu ->
        label_function_of (classes pg c m) l = l' ->
        exists e, annos c m l' = (eq (ghost_var gs) e) /\ ~ghost_expr e.
  
  
  Theorem proof_outline_existence_impl_adherence :
    forall p contr,
      (exists annos, is_proof_outline p contr annos) ->
      adheres_to gs p contr.
    Proof.
      intros.
      elim H; intros annos H_po.
      unfold is_proof_outline in H_po.
      elim H_po => pg H0.
      elim: H0 => H_gi H0.
      elim: H0 => H_annotated H0.
      elim: H0 => H_lvpg H0.
      apply never_wrong_impl_adherence.
      exists pg.
      split.
      assumption.
      intros.
      apply sufficient_never_go_wrong_annos with (pg := pg).
      assumption.
      intros.
      subst.
      elim (H0 c m l (label_function_of (classes pg c m) l) gu); intros.
      elim H2; intros.
      unfold annotated_with in H_annotated.
      pose proof (H_annotated c m (label_function_of (classes pg c m) l)).
      rewrite H5.
      pose proof (H0 c m l (label_function_of (classes pg c m) l)).
      pose proof (H6 gu).
      apply H7 in H1.
      elim H1; intros e H'.
      elim H'; intros.
      rewrite H8.
      apply (non_ghost_stronger_than_non_err e).
      assumption.
      reflexivity.
      assumption.
      reflexivity.
      assumption.
    Qed.
  
End contracts.

