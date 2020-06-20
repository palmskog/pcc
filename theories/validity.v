From Coq Require Import List Lia.
From PCC Require Import list_utils java_basic_defs program_model expressions_assertions semantics_assertions weakest_precondition.
From mathcomp Require Import ssreflect.

(* The default variable denotes an assertion that expresses that
   all variables have their default values. *)
Variable default : ast.

Hypothesis initial_default : forall c, initial_conf c -> ∥ default ∥ c.


Section validity.
  
  Variable p: program.
  
  (* An execution is valid if each config satisfies the assertion of the current
     program point and inv holds whenever a config is calling or returning. *)
  Inductive valid_conf c : Prop :=
  | v_conf : (* TODO: change into a def. *)
      (visible_conf p c -> ∥ inv p ∥ c) ->
      (normal_conf c -> forall a, current_ast p c = Some a -> ∥ a ∥ c) ->
      valid_conf c.
  
  
  Inductive valid_exec : execution -> Prop :=
  | ve_nil : valid_exec nil
  | ve_cons : 
    forall c cs,
      valid_conf c ->
      valid_exec cs ->
      valid_exec (cs++c::nil).
  
  Lemma all_valid : forall e, valid_exec e <-> forall c, In c e -> valid_conf c.
    split.
    
    (* -> *)
    intros.
    destruct e using rev_ind.
    inversion H0.
    inversion H.
    apply app_cons_not_nil in H2.
    contradiction.
    
    apply in_but_not_last in H0.
    elim H0; intros.
    
    apply app_inj_tail in H1.
    elim H1; intros; subst.
    assumption.
    
    apply IHe.
    apply app_inj_tail in H1.
    elim H1; intros; subst.
    assumption.
    assumption.
    
    (* <- *)
    intros.
    destruct e using rev_ind.
    apply ve_nil.
    apply ve_cons.
    apply H.
    apply in_or_app.
    right.
    auto with datatypes.
    apply IHe.
    intros.
    apply H.
    apply in_or_app.
    left.
    assumption.
  Qed.
  
  
  Definition globally_valid : Prop := forall e, execution_of p e -> valid_exec e.
  
  
  Definition locally_valid_meth cid mid : Prop :=
    (forall c, ∥ inv p ∥ c -> ∥ ast_at p cid mid O ∥ c) /\
    (forall c l, ∥ ast_at p cid mid l ∥ c -> ∥ wp p cid mid l ∥ c).
  
  
  Definition locally_valid : Prop :=
    (forall cid mid, locally_valid_meth cid mid) /\
    (forall c, ∥ default ∥ c -> ∥ ast_at p maincid mainmid O ∥ c) /\
    (forall c, ∥ default ∥ c -> ∥ inv p ∥ c).

(* aload n *)
Lemma wp_correct_normal_aload : forall c m pc s ls h n ars gv,
  instr_at p c m pc = aload n ->
  (∥wp p c m pc ∥ (gv, h, normal c m pc s ls :: ars) <->
  ∥ast_at p c m (successor p c m pc) ∥ (gv, h, normal c m (successor p c m pc) (ls n :: s) ls :: ars)).
Proof.
  intros.
  unfold wp.
  rewrite H.
  set (a := ast_at p c m (successor p c m pc)) in * |- *.
  set (cnf := (gv, h, normal c m pc s ls :: ars)) in * |- *.
  set (cnf' := (gv, h, normal c m (successor p c m pc) (ls n::s) ls :: ars)) in * |- *.
  
  assert (expr_lemma: forall e val, eeval (eunshift (subste e (local n) (stackexp 0))) cnf val <-> (eeval e cnf' val)).
    intros e.
    induction e; intros.
    (* v *)
    split; intros.
    simpl in H0.
    inversion H0; subst.
    apply e_val.
    inversion H0; subst.
    simpl.
    apply e_val.
    apply e_ghosterr.
    inversion H0; subst.
    simpl.
    apply e_val.
    simpl.
    apply e_ghosterr.
    
    (* ghost var *)
    assert (H_gv: ghost_valuation_of cnf = ghost_valuation_of cnf'). auto.
    split; intros.
    inversion H0; subst.
    rewrite H_gv.
    apply e_ghostvar.
    simpl.
    inversion H0; subst.
    rewrite <- H_gv.
    apply e_ghostvar.

    (* nsfield *) split; intros. simpl in H0.
    inversion H0; subst.
    apply IHe in H4. Check e_nsfield.
    apply (e_nsfield gv cnf' e dh sh (normal c m (successor p c m pc) (ls n::s) ls :: ars) f l obj).
    inversion H3.
    rewrite <- H2.
    rewrite <- H5.
    reflexivity.
    assumption.
    assumption.
    
    apply e_nsfield_err1 with (v := v).
    apply (IHe v).
    assumption.
    assumption.
    
    
    apply e_nsfield_err2 with (c := cnf') (gv := gv) (dh := dh) (sh := sh) (l := l) (ars := normal c m (successor p c m pc) (ls n :: s) ls :: ars).
    inversion H3.
    rewrite <- H2.
    rewrite <- H5.
    reflexivity.
    apply IHe in H4.
    assumption.
    assumption.
    

    inversion H0; subst.
    simpl.
    apply e_nsfield with (gv := gv) (dh := dh) (sh := sh) (ars := normal c m pc s ls :: ars) (l := l).
    inversion H3.
    rewrite <- H2.
    rewrite <- H5.
    reflexivity.
    apply (IHe (refval l)).
    assumption.
    assumption.
    
    inversion H0; subst.
    simpl.
    apply e_nsfield with (gv := gv) (dh := dh) (sh := sh) (ars := normal c m pc s ls :: ars) (l := l).
    inversion H5.
    rewrite <- H7.
    rewrite <- H2.
    reflexivity.
    apply (IHe (refval l)).
    assumption.
    assumption.
    
    simpl.
    apply e_nsfield_err1 with (v := v0).
    apply (IHe v0).
    assumption.
    assumption.

    simpl.
    apply e_nsfield_err2 with (c := cnf) (gv := gv) (dh := dh) (sh := sh) (l := l) (ars := normal c m pc s ls :: ars).
    inversion H4.
    rewrite <- H2.
    rewrite <- H7.
    reflexivity.
    apply (IHe (refval l)).
    assumption.
    assumption.
    
    simpl.
    apply e_nsfield_err2 with (c := cnf) (gv := gv) (dh := dh) (sh := sh) (l := l) (ars := normal c m pc s ls :: ars).
    inversion H3.
    rewrite <- H2.
    rewrite <- H5.
    reflexivity.
    apply (IHe (refval l)).
    assumption.
    assumption.
    
    
    (* sfield *) split; intros.
    inversion H0; subst.
    apply (e_sfield gv cnf' dh sh (normal c m (successor p c m pc) (ls n :: s) ls :: ars) c0 f v).
    inversion H3.
    rewrite <- H2.
    rewrite <- H4.
    reflexivity.
    assumption.
    
    apply e_sfield_err with (gv := gv) (dh := dh) (sh := sh) (ars := normal c m (successor p c m pc) (ls n :: s) ls :: ars).
    inversion H3.
    rewrite <- H2.
    rewrite <- H4.
    reflexivity.
    assumption.
    
    simpl.
    inversion H0; subst.
    apply e_sfield with (gv := gv) (dh := dh) (sh := sh) (ars := normal c m pc s ls :: ars).
    inversion H3.
    rewrite <- H4.
    rewrite <- H2.
    reflexivity.
    assumption.
    
    apply e_sfield_err with (gv := gv) (dh := dh) (sh := sh) (ars := normal c m pc s ls :: ars).
    inversion H3.
    rewrite <- H2.
    rewrite <- H4.
    reflexivity.
    assumption.
    
    (* stackexp *) split; intros.
    destruct n0.
    (* subcase: n0 = 0 *)
    simpl in H0.
    inversion H0; subst.
    assert ((ls0 n::s)[[0]] = ls0 n).
      simpl.
      reflexivity.
    rewrite <- H1.
    apply (e_stack cnf' 0 (ls0 n :: s)).
    simpl.
    inversion H2.
    reflexivity.
    (* subcase: n0 = S n0 *)
    simpl in H0.
    inversion H0; subst.
    inversion H2.
    rewrite <- H3 in * |- *.
    assert (s[[n0]] = ((ls n :: s)[[S n0]])).
      simpl.
      reflexivity.
    rewrite H1.
    
    apply (e_stack cnf' (S n0) (ls n :: s)).
    simpl.
    reflexivity.
    destruct n0.
    (* subcase n0 = 0 *)
    simpl.
    inversion H0; subst.
    inversion H2.
    simpl.
    apply e_local.
    reflexivity.
    (* subcase n0 = S n0' *)
    inversion H0; subst.
    inversion H2; subst.
    simpl.
    apply e_stack.
    reflexivity.
    (* local n0 *)
    split; intros.
    simpl in H0.
    inversion H0; subst.
    inversion H2.
    apply e_local.
    rewrite <- H3.
    reflexivity.
    inversion H0; subst.
    inversion H2.
    rewrite <- H3.
    simpl.
    apply e_local.
    reflexivity.
    (* plus *)
    split; intros.
    simpl in H0.
    inversion H0; subst.
    apply IHe1 in H3.
    apply IHe2 in H6.
    apply e_plus; assumption.
    
    apply e_plus_err with (v1 := v1) (v2 := v2).
    apply (IHe1 v1) in H3; assumption.
    apply (IHe2 v2) in H4; assumption.
    assumption.

    simpl.
    inversion H0; subst.
    apply e_plus.
    apply IHe1 in H3; assumption.
    apply IHe2 in H6; assumption.
    
    inversion H0; subst.
    apply e_plus_err with (v1 := v1) (v2 := v2).
    apply (IHe1 v1); assumption.
    apply (IHe2 v2); assumption.
    assumption.
    
    (* guarded *)
    split; intros.
    simpl in H0.
    inversion H0; subst.
    apply IHe1 in H6.
    apply IHe2 in H7.
    apply e_guard_true; assumption.
    apply IHe1 in H6.
    apply IHe3 in H7.
    apply e_guard_other; assumption.
    
    apply e_guard_err with (v := v).
    apply IHe1 in H6.
    assumption.
    assumption.
    
    simpl.
    inversion H0; subst.
    apply e_guard_true.
    apply IHe1 in H6; assumption.
    apply IHe2 in H7; assumption.
    apply e_guard_other.
    apply IHe1 in H6; assumption.
    apply IHe3 in H7; assumption.
    
    apply e_guard_err with (v := v).
    apply (IHe1 v).
    assumption.
    assumption.

induction a; inversion H.
(* tt *)
split; intros; apply e_tt.
(* ff *)
split; intros; inversion H0.
(* le *)
split; intros.
inversion H0.
apply expr_lemma in H4.
apply expr_lemma in H5.
apply e_le with (i := i) (j := j); assumption.
simpl.
inversion H0; subst.
apply e_le with (i := i) (j := j).
apply expr_lemma in H4; assumption.
apply expr_lemma in H5; assumption.
assumption.
(* eq *)
split; intros.
inversion H0; subst.
apply expr_lemma in H4.
apply expr_lemma in H6.
apply e_eq with (v := v); assumption.
simpl.
inversion H0; subst.
apply e_eq with (v := v).
apply expr_lemma in H4; assumption.
apply expr_lemma in H6; assumption.
(* or *)
split; intros.
inversion H0; subst.
elim H5; intros.
apply IHa1 in H2.
apply e_disj.
left; assumption.
apply IHa2 in H2.
apply e_disj.
right; assumption.
simpl.
apply e_disj.
inversion H0; subst.
elim H5; intros.
apply IHa1 in H2.
left; assumption.
apply IHa2 in H2.
right; assumption.
(* and *)
split; intros.
inversion H0; subst.
elim H5; intros.
apply IHa1 in H2.
apply IHa2 in H3.
apply e_conj.
split; assumption.
simpl.
apply e_conj.
inversion H0; subst.
elim H5; intros.
apply IHa1 in H2.
apply IHa2 in H3.
split; assumption.
(* neg *)
split; intros.
inversion H0; subst.
apply e_neg.
apply invert_aeval in IHa.
apply IHa in H3.
assumption.
apply is_norm_conf.
apply is_norm_conf.
simpl.
apply e_neg.
apply invert_aeval in IHa.
apply IHa.
inversion H0; subst.
assumption.
apply is_norm_conf.
apply is_norm_conf.

(* if else *)
split; intros.
simpl in H0.
inversion H0; subst.
apply e_if_true.
apply IHa1 in H6; assumption.
apply IHa2 in H7; assumption.
inversion H0; subst.
apply e_if_false.
apply invert_aeval in IHa1.
apply IHa1 in H6; assumption.
apply is_norm_conf.
apply is_norm_conf.
apply IHa3 in H7; assumption.
apply e_if_false.
apply invert_aeval in IHa1.
apply IHa1 in H6; assumption.
apply is_norm_conf.
apply is_norm_conf.
apply IHa3 in H7; assumption.

simpl.
inversion H0; subst.
apply e_if_true.
apply IHa1; assumption.
apply IHa2; assumption.
apply e_if_false.
apply invert_aeval in IHa1.
apply IHa1 in H6; assumption.
apply is_norm_conf.
apply is_norm_conf.
apply IHa3 in H7; assumption.
Qed.

Lemma wp_correct_normal_astore: forall c m pc s ls h n v ars gv,
 instr_at p c m pc = astore n ->
 (∥wp p c m pc ∥ (gv, h, normal c m pc (v :: s) ls :: ars) <->
   ∥ast_at p c m (successor p c m pc) ∥ (gv, h, normal c m (successor p c m pc) s (upd ls n v) :: ars)).
Proof.
Admitted.

Lemma wp_correct_normal_dup: forall c m pc s ls h v ars gv,
 instr_at p c m pc = dup ->
 (∥wp p c m pc ∥ (gv, h, normal c m pc (v :: s) ls :: ars) <->
   ∥ast_at p c m (successor p c m pc) ∥ (gv, h, normal c m (successor p c m pc) (v :: v :: s) ls :: ars)).
Proof.
Admitted.

Lemma wp_correct_normal_goto: forall c m pc s ls h l ars gv,
 instr_at p c m pc = goto l ->
  (∥ wp p c m pc ∥ (gv, h, normal c m pc s ls :: ars) <->
  ∥ ast_at p c m l ∥ (gv, h, normal c m l s ls :: ars)).
Proof.
Admitted.

Lemma wp_correct_normal : forall h cid mid pc s ls ars c' a,
  let c := (h, (normal cid mid pc s ls)::ars) in
    trans p c c' ->
    normal_conf c' ->
    current_ast p c' = Some a ->
    (∥ wp p cid mid pc ∥ c <->
    ∥ a ∥ c').
Proof.
intros.
inversion H; subst; last first.
  (* trans *)
  by admit.
inversion H0; subst.
inversion H1; subst.
inversion H2; subst.
inversion H4; subst.
- (* aload n *)
  inversion H6; subst.
  inversion H5; subst.
  by apply wp_correct_normal_aload.
- (* astore n *)
  inversion H6; subst.
  inversion H5; subst.
  by apply wp_correct_normal_astore.
- (* dup *)
  inversion H6; subst.
  inversion H5; subst.
  rewrite H2.
  by apply wp_correct_normal_dup.
- (* goto *)
  inversion H6; subst.
  inversion H5; subst.
  rewrite H2.
  by apply wp_correct_normal_goto.
- (* iconst *)
  by admit.
- (* ldc *)
  by admit.
- (* ifeq true *)
  by admit.
- (* ifeq false *)
  by admit.
(* The other instructions can be treated similarly and are proved correct when the
   remaining of the proof script is completed and the definitions more stable. *)

(* This whole lemma could probably be solved with some proof search
   automation and/or ssreflect. Consult Karl. *)
Admitted.
  
  Lemma wp_correct_exceptional :
    forall gv h o cid mid pc s ls ars gv'' h'' c' a,
      let c := (gv, h, (exceptional o) :: (normal cid mid pc s ls) :: ars) in
      let c'' := (gv'', h'', (normal cid mid pc s ls) :: ars) in
        trans p c c' ->
        normal_conf c' ->
        current_ast p c' = Some a ->
        (∥ wp p cid mid pc ∥ c'') ->
        (∥ a ∥ c').
(* The other instructions can be treated similarly and are proved correct when the
   remaining of the proof script is completed and the definitions more stable. *)
  Admitted.
  
  
  Lemma sub_execution : forall pref suff, execution_of p (pref ++ suff) ->
                                          execution_of p pref.
    intros.
    apply exec_intros.
    destruct pref.
    intros.
    inversion H0.
    intros.
    inversion H0; subst.
    inversion H; subst.
    apply H1.
    simpl.
    reflexivity.
    intros.
    subst.
    inversion H; subst.
    apply H1 with (pref := pref0) (suff1 := suff0 ++ suff).
    rewrite app_ass.
    rewrite app_comm_cons.
    reflexivity.
  Qed.
  
  Corollary sub_execution2 : forall exec c c',
      execution_of p (exec ++ c::c'::nil) -> execution_of p (exec ++ c :: nil).
    
    intros.
    apply sub_execution with (suff := c' :: nil).
    rewrite app_ass.
    simpl.
    assumption.
  Qed.
  
  Theorem strong_exec_ind (P: execution -> Prop) :
    P nil ->
    (forall c, execution_of p (c :: nil) -> P (c :: nil)) ->
    (forall exec c c', execution_of p (exec ++ c :: c' :: nil) ->
      (forall exec', execution_of p exec' ->
                     proper_prefix exec' (exec ++ c :: c' :: nil) ->
                     P exec') ->
      P (exec ++ c :: c' :: nil)) ->
    forall exec, execution_of p exec -> P exec.
    
    destruct exec using strong_list_ind.
    intros.
    destruct exec using rev_ind.
    assumption.
    destruct exec using rev_ind.
    apply (H0 x).
    assumption.
    rewrite <- list_rearrange.
    apply H1.
    rewrite <- list_rearrange in H3.
    assumption.
    intros.
    apply H2.
    rewrite <- list_rearrange.
    assumption.
    assumption.
  Qed.
  
  
  Lemma valid_exec_last : forall exec c, valid_exec (exec ++ c :: nil) -> valid_conf c.
    intros.
    apply (all_valid (exec ++ c::nil)).
    assumption.
    apply in_or_app.
    right.
    auto with datatypes.
  Qed.
  
  
  Lemma valid_exec_prefix :
    forall pref exec, proper_prefix pref exec -> valid_exec exec -> valid_exec pref.
    intros pref ex H.
    
    assert (H_tmp: forall a a' b b': Prop, (a' -> b') -> (a <-> a') -> (b <-> b') -> (a -> b)).
      intros a a' b b' H_t0 H_t1 H_t2 H_t3.
      apply H_t2.
      apply H_t0.
      apply H_t1.
      assumption.
    
    apply (H_tmp (valid_exec ex) (forall c, In c ex -> valid_conf c) (valid_exec pref) (forall c, In c pref -> valid_conf c)).
    intros.
    apply H0.
    apply proper_prefix_split in H.
    elim H; intros.
    elim H2; intros.
    rewrite H3.
    apply in_or_app.
    left.
    assumption.
    apply (all_valid ex).
    apply (all_valid pref).
  Qed.
  
  
  Corollary valid_exec_last_norm :
    forall exec c, valid_exec (exec ++ c :: nil) -> normal_conf c ->
      forall a, current_ast p c = Some a -> (∥ a ∥ c).
  Proof.
    intros exec c H.
    apply valid_exec_last in H.
    inversion H.
    assumption.
  Qed.
  
  
  Lemma exec_impl_trans :
    forall exec c c', execution_of p (exec ++ c :: c' :: nil) -> trans p c c'.
  Proof.
    intros.
    inversion H; subst.
    apply H1 with (pref := exec) (suff := nil).
    reflexivity.
  Qed.
  
  
  Lemma act_rec_suffixes :
    forall gv gv' h ars h' ar ars', trans p (gv, h, ars) (gv', h', ar::ars') -> suffix ars' ars.
    intros.
    inversion H.
    inversion H2; inversion H0; inversion H1; subst; try apply suffix_next; try apply suffix_here.
    inversion H0; inversion H5; inversion H7; subst; apply suffix_next; apply suffix_here.
Qed.
  
  Lemma all_ars_has_been_on_top :
    forall exec,
      execution_of p exec ->
      forall gv h ars suff,
        last exec (gv, h, ars) ->
        suffix suff ars ->
        suff <> nil ->
        exists gv', exists h', In (gv', h', suff) exec.
    
    apply (strong_exec_ind (fun exec => forall gv h ars suff,
      last exec (gv, h, ars) ->
      suffix suff ars ->
      suff <> nil ->
      exists gv', exists h', In (gv', h', suff) exec)).
    
    intros.
    inversion H.
    
    (* Base case *)
    intros.
    inversion H; subst.
    assert (initial_conf c).
      apply H3.
      simpl; reflexivity.
    inversion H5; subst.
    inversion H0.
    exists gv.
    exists h.
    subst.
    inversion H1.
    subst.
    apply in_eq.
    subst.
    inversion H8.
    contradiction H2.
    inversion H9.
    
    (* Inductive step *)
    intros.
    rewrite list_rearrange in H1.
    apply last_app_cons in H1.
    subst.
    (* rewrite H1 in * |- *. *)

    inversion H2; subst.
    
      (* suff = ars   "non-proper" prefix *)
      exists gv.
      exists h.
      auto with datatypes.
      
      (* suff = proper suffix *)
      assert (exists gv', exists h', In (gv', h', suff) (exec ++ c :: nil)).
        destruct c as ((gv', h'), ars').
        apply H0 with (gv := gv') (h := h') (ars := ars').
        apply sub_execution2 with (c' := (gv, h, a::l)).
        assumption.
        apply proper_prefix_app.
        apply proper_prefix_next.
        apply proper_prefix_nil.
        apply last_app.
        apply last_base.
        apply exec_impl_trans in H.
        apply act_rec_suffixes in H.
        apply suffix_transitive with (bc := l); assumption.
        assumption.
        
      elim H4; intros gv' H_ex_h.
      elim H_ex_h; intros h'; intros.
      exists gv'.
      exists h'.
      rewrite list_rearrange.
      apply in_or_app.
      left.
      assumption.
  Qed.
  
  
  Lemma no_empty_ar_stack_trans : forall gv h ar ars gv' h', trans p (gv, h, ar :: ars) (gv', h', nil) -> False.
    intros.
    inversion H; subst.
    inversion H1; subst.
    inversion H0; subst.
  Qed.
  
  
  Lemma no_empty_ar_stack : forall exec gv h, execution_of p exec ->
                                              In (gv, h, nil) exec -> False.
    destruct exec using rev_ind; intros.
    inversion H0.
rename x into c'.
apply (IHexec gv h).
apply (sub_execution exec (c' :: nil) H).
destruct exec using rev_ind; [| clear IHexec0].
inversion H0; subst.
inversion H.
pose proof (H1 (gv, h, nil)).
assert (H_tmp : forall (A: Set) (a : A), head (nil ++ a :: nil) = Some a).
  reflexivity.
apply H4 in H_tmp.
inversion H_tmp.
contradict H1.
rename x into c.
apply in_app_or in H0.
elim H0; clear H0; intros.
rewrite <- list_rearrange in H.
apply sub_execution2 in H.
contradict (IHexec gv h H H0).
inversion H0; [| contradiction]; subst.
rewrite <- list_rearrange in H.
destruct c.
destruct p0.
destruct l.
apply sub_execution2 in H.
apply (IHexec g h0) in H; [contradiction |].
apply in_or_app.
right.
auto with datatypes.
apply exec_impl_trans in H.
contradict (no_empty_ar_stack_trans _ _ _ _ _ _ H).
Qed.
  
  
  Lemma calling_only_invoke :
    forall gv h c m pc s ls ars0 gv' h' c' m' pc' s' ls',
      let ars := normal c  m  pc  s  ls :: ars0 in
      let ars':= normal c' m' pc' s' ls':: ars  in
        calling_conf p (gv, h, ars) ->
        trans p (gv, h, ars) (gv', h', ars') ->
        instr_at p c m pc = invoke c' m'.
    intros until ars'.
    intros H_calling H_trans.
    inversion H_calling as [gv0 h0 c0 m0 pc0 l ls0 ars1 H_trans']; subst.
    inversion H_trans'; subst.
    rename H1 into H_atrans.
    inversion H0.
    subst.
    inversion H_atrans; subst; inversion H; contradict H9; apply list_neq_length; simpl; lia.
    inversion H.
    contradict H16; apply list_neq_length; simpl; lia.
  Qed.
  
  
  Lemma calling_conf_inv : forall gv h c m pc s ls ars,
    let cnf := (gv, h, normal c m pc s ls::ars) in
      locally_valid -> calling_conf p cnf -> ∥ ast_at p c m pc ∥ cnf -> ∥inv p ∥ cnf.
    intros.
    inversion H0; subst.
    assert (instr_at p c m pc = invoke c0 m0).
      apply (calling_only_invoke gv h c m pc s ls ars gv h c0 m0 pc0 l ls0); assumption.
    
    inversion H.
    elim (H4 c m); intros.
    assert ((∥ast_at p c m pc ∥ cnf) -> ∥wp p c m pc ∥ cnf).
      apply H7.
    unfold wp in H8.
    rewrite H2 in H8.
    apply H8.
    assumption.
  Qed.
  
  
  Lemma returning_conf_inv : forall gv h c m pc s ls ars,
    let cnf  := (gv, h, normal c m pc s ls::ars) in
      locally_valid -> ∥ast_at p c m pc ∥ cnf -> returning_conf p cnf -> ∥inv p ∥ cnf.
  Proof.
    intros.
    assert (H_curr_inst_ret: current_instr p cnf = Some ret).
    inversion H1; subst.
    inversion H3; subst.
    
    (* ar-trans *)
    inversion H5; subst; subst cnf; (try
      inversion H2; inversion H4; subst;
        inversion H4; contradict H8;
          apply list_neq_length; simpl; lia).
    
    (* ghost-trans *)
    subst cnf.
    inversion H2.
    contradict H15.
    apply list_neq_length; simpl; lia.
    
    inversion H.
    pose proof (H2 c m).
    inversion H4.
    apply current_to_instr_at in H_curr_inst_ret.
    pose proof (H6 cnf pc).
    unfold wp in H7.
    rewrite H_curr_inst_ret in H7.
    apply H7.
    assumption.
  Qed.
  
  
  Lemma returning_conf_inv_exc : forall gv h o ars,
    let cnf := (gv, h, exceptional o :: ars) in
      locally_valid -> returning_conf p cnf -> ∥inv p ∥ cnf.
  Proof.
    intros.
    inversion H0; subst.
    inversion H2.
    inversion H4; subst; inversion H3; inversion H1.
    subst.
    inversion H1; subst.
  Qed.
  
  
  Lemma no_double_exc_trans : forall c gv h o1 o2 ars, trans p c (gv, h, exceptional o1 :: exceptional o2 :: ars) -> exists gv', exists h', c = (gv', h', exceptional o1 :: exceptional o2 :: ars).
    intros.
    inversion H; subst.
    inversion H2; subst; try (inversion H1; inversion H1; subst).
  inversion H0; subst.
  Qed.
  
  
  Corollary no_double_exceptional : forall exec gv h o1 o2 ars,
      execution_of p (exec ++ (gv, h, exceptional o1 :: exceptional o2 :: ars) :: nil) -> False.
    destruct exec using rev_ind; intros.
    inversion H; subst.
    assert (initial_conf (gv, h, exceptional o1 :: exceptional o2 :: ars)).
      apply H0.
      reflexivity.
    inversion H2.
    rewrite <- list_rearrange in H.
    generalize H; intros H_exec.
    apply exec_impl_trans in H.
    apply no_double_exc_trans in H.
    elim H; clear H; intros.
    elim H; clear H; intros.
    subst.
    apply sub_execution2 in H_exec.
    apply IHexec in H_exec.
    contradict H_exec.
  Qed.
  
  
  Lemma initial_conf_valid :
    forall c,
      locally_valid ->
      execution_of p (c::nil) ->
      valid_exec (c::nil).
    
    intros.
    destruct c as ((gv, h), ars).
    destruct ars.
    contradict H0.
    intro.
    apply (no_empty_ar_stack ((gv, h, nil)::nil) gv h); auto with datatypes.
    assert (∥inv p ∥ (gv, h, a::ars)).
      inversion H.
      inversion H0.
      elim H2; intros.
      apply (H7 (gv, h, a::ars)).
      apply initial_default.
      apply H3.
      reflexivity.
    destruct a.
    set (c0 := (gv, h, normal c m l s l0 :: ars)) in * |- *.
    apply (ve_cons c0 nil).
    apply v_conf.
    intros.
    assumption.
    intros.
    inversion H.
    elim H5; intros.
    inversion H0.
    subst.
    assert (initial_conf c0).
      apply H8; reflexivity.
    inversion H10.
    inversion H3.
    rewrite H14.
    rewrite H15.
    rewrite H16.
    apply (H6 c0).
    apply initial_default.
    assumption.
    apply ve_nil.
    inversion H0.
    subst.
    assert (initial_conf (gv, h, exceptional l :: ars)).
      apply H2; reflexivity.
    inversion H4.
  Qed.
  
  

  Lemma local_impl_global_prev_normal_then_ast_holds :
    forall cnf cnf' exec a,
        locally_valid ->
        execution_of p (exec ++ cnf :: cnf' :: nil) ->
        (forall exec' : execution,
          execution_of p exec' ->
          proper_prefix exec' (exec ++ cnf :: cnf' :: nil) ->
          valid_exec exec') ->
        normal_conf cnf' ->
        current_ast p cnf' = Some a ->
        ∥a ∥ cnf'.
      intros until a.
      intros H_p_lv H_exec IH.
      intros.
      destruct cnf as ((gv, h), ars). (* would like to be able to destruct .. using .. so I don't have to take care of the case where ar-stack is empty all the time. *)
      destruct ars.
      contradict H_exec.
      intro.
      apply no_empty_ar_stack with (gv := gv) (h := h) in H1.
      assumption.
      auto with datatypes.
      
      destruct a0.
      set (cnf := (gv, h, normal c m l s l0 :: ars)) in * |- *.
      
      (* Normal predecessor *)
        assert (H_wp: ∥ wp p c m l ∥ cnf -> ∥ a ∥ cnf').
          assert (H_tmp: ∥ wp p c m l ∥ cnf <-> ∥ a ∥ cnf').
            apply wp_correct_normal.
            apply (exec_impl_trans exec cnf cnf').
            assumption.
            assumption.
            assumption.
          elim H_tmp; intros H' H''.
          assumption.
        
        apply H_wp.
        inversion H_p_lv as [H_all_lv].
        elim (H_all_lv c m); intros H_inv_imp_pre H_proof_obl.
        apply (H_proof_obl cnf).
        apply (valid_exec_last_norm exec cnf).
        apply IH.
        apply sub_execution2 with (c' := cnf').
        assumption.
        apply proper_prefix_app.
        apply proper_prefix_next.
        apply proper_prefix_nil.
        apply is_norm_conf.
        reflexivity.
        
        
        (* Exceptional predecessor *)
        (* Show that l <> nil *)
        destruct ars.
        apply exec_impl_trans in H_exec.
        inversion H_exec; subst.
        inversion H3; subst; inversion H1.
        inversion H1; subst.

        (* a0 must be normal. *)
        destruct a0.
        
        (* Case: it is normal. *)
        set (ar := normal c m l0 s l1) in * |- *.
        assert (H_ex_thrower : exists gv', exists h', In (gv', h', ar :: ars) (exec ++ (gv, h, exceptional l :: ar :: ars) :: nil)).
          apply (all_ars_has_been_on_top) with (gv := gv) (h := h) (ars := exceptional l :: ar :: ars).
          apply sub_execution2 with (c' := cnf').
          assumption.
          apply last_app.
          apply last_base.
          apply suffix_next.
          apply suffix_here.
          auto with datatypes.
        
        elim H_ex_thrower; intros gv' H_in_tmp.
        elim H_in_tmp; intros h' H_in.
        
        apply in_but_not_last in H_in.
        elim H_in; intros H_thrower.
        inversion H_thrower.
        assert (H_ex_pref_suff : exists ex_pref, exists ex_suff, exec = ex_pref ++ (gv', h', ar :: ars) :: ex_suff).
          apply (In_split (gv', h', ar :: ars) exec).
          assumption.
        
        elim H_ex_pref_suff; intros x H_ex_suff.
        elim H_ex_suff; intros x0 H_ex.
        set (cnfT := (gv', h', ar :: ars)) in * |- *.
        
        assert (valid_exec (x ++ cnfT::nil)).
          apply IH.
          assert (H_sub_exec : execution_of p exec).
            destruct exec.
            contradict H_ex.
            auto with datatypes.
            apply sub_execution with (suff := (gv, h, exceptional l :: ar :: ars) :: cnf' :: nil).
            assumption.
            subst.
          (* rewrite H_ex in * |- *. *)
          rewrite list_rearrange in H_sub_exec.
          apply sub_execution with (suff := x0).
          auto with datatypes.
          rewrite H_ex.
          rewrite app_ass.
          apply proper_prefix_app.
          rewrite <- app_comm_cons.
          apply proper_prefix_next.
          case x0.
          apply proper_prefix_nil.
          intros.
          rewrite <- app_comm_cons.
          apply proper_prefix_nil.
        
        assert (H_ast_cnft : ∥ ast_at p c m l0 ∥ cnfT).
          apply (valid_exec_last x cnfT).
          assumption.
          apply is_norm_conf.
          auto.
        
        inversion H_p_lv as [H_all_lv].
        elim (H_all_lv c m); intros H_lv_ast H_lv_wp.
        apply (H_lv_wp cnfT l0) in H_ast_cnft.
        apply (wp_correct_exceptional gv h l c m l0 s l1 ars gv' h' cnf' a); auto.
        apply (exec_impl_trans exec (gv, h, exceptional l :: ar :: ars) cnf').
        assumption.
        
        (* Case: it is exceptional. *)
        assert (execution_of p (exec ++ (gv, h, exceptional l :: exceptional l0 :: ars) :: nil)).
          apply sub_execution2 with (c' := cnf').
          assumption.
        apply no_double_exceptional in H1.
        contradiction.
  Qed.

  
  
  Lemma calling_conf_normal_conf : forall c, calling_conf p c -> normal_conf c.
    intros.
    inversion H; subst.
    destruct ars.
    inversion H0; subst.
    inversion H1.
    inversion H1.
    destruct a.
    apply is_norm_conf.
    inversion H0; subst.
    inversion H1; subst.
    inversion H3; discriminate.
    inversion H1.
  Qed.
  
  
  Theorem local_impl_global : locally_valid -> globally_valid.
    intros.
    unfold globally_valid.
    intros exec H0.
    apply (strong_exec_ind valid_exec).
    apply ve_nil.
    intros.
    apply initial_conf_valid; assumption.
    clear H0 exec.
    intros exec c c' H0 IH.
    
    (* Inductive step. *)
    destruct c' as ((gv', h'), ars').
    destruct ars'.
    contradict H0; intro.
    apply (no_empty_ar_stack (exec ++ c :: (gv', h', nil) :: nil) gv' h'); auto with datatypes.
    destruct a.
    
    (* Last conf: normal *)
      rewrite list_rearrange.
      apply ve_cons.
      apply v_conf.
      
      (* Visible => Inv *)
      intro H_visconf.
      unfold visible_conf in H_visconf.
      elim H_visconf.
      (* Calling *)
        intros H_c.
        assert (∥ast_at p c0 m l ∥ (gv', h', normal c0 m l s l0 :: ars')).
          apply local_impl_global_prev_normal_then_ast_holds with (cnf := c) (exec := exec); auto.
          apply is_norm_conf.
        
        apply calling_conf_inv.
        assumption.
        assumption.
        assumption.
    
      (* Returning *)
        apply (returning_conf_inv gv' h' c0 m l s l0 ars').
        assumption.
        apply local_impl_global_prev_normal_then_ast_holds with (cnf := c) (exec := exec); auto.
        apply is_norm_conf.
        
      (* C_i normal => ∥ast at C_i∥ C_i  holds. *)
      intros H_normal a H_currast.
      apply local_impl_global_prev_normal_then_ast_holds with (cnf := c) (exec := exec); auto.
      apply IH.
      apply sub_execution2 with (c' := (gv', h', normal c0 m l s l0 :: ars')).
      assumption.
      apply proper_prefix_app.
      apply proper_prefix_next.
      apply proper_prefix_nil.
      
    (* Last conf: exceptional *)
      rewrite list_rearrange.
      apply (ve_cons (gv', h', exceptional l :: ars') (exec ++ c :: nil)).
      apply v_conf.
      
      (* Visible => Inv *)
      intro H_visconf.
      unfold visible_conf in H_visconf.
      elim H_visconf.
      intros.
      inversion H1; subst.
      inversion H3; subst.
      inversion H5; subst; try inversion H2.
      inversion H2.
      intros.
      apply (returning_conf_inv_exc gv' h' l ars').
      assumption.
      assumption.
      intros.
      inversion H1.
      apply IH.
      apply (sub_execution2 exec c (gv', h', exceptional l :: ars')).
      assumption.
      apply proper_prefix_app.
      apply proper_prefix_next.
      apply proper_prefix_nil.
      assumption.
    Qed.

End validity.
