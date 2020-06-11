From PCC Require Import list_utils java_basic_defs expressions_assertions.
From Coq Require Import List Bool ZArith.
From mathcomp Require Import ssreflect.

Section ProgramModel.
  
Open Scope type_scope.

Definition ghost_update := ghostid * expr.

Inductive instr : Set :=
| aload (_: nat)
| astore (_: nat)
| athrow
| dup
| getfield (_: fieldid)
| getstatic (_: classid) (_: fieldid)
| goto (_: label)
| iadd
| iconst (_: Z)
| ifeq (_: label)
| invoke (_: classid) (_: methid)
| putstatic (_: classid) (_: fieldid)
| ldc (_: jvalue)
| exit
| ret
| nop
| ghost_instr (_: ghost_update).

(* Exception handler records (rows in the exception handler table) *)
Record eh_record : Set := {
  start_label  : label;
  end_label    : label;
  target_label : label;
  handled_classes : classid
}.

Definition eh_table := list eh_record.

(* 
   A label function is used to look up successor-labels. It used to 
   be 'S' (the nat successor-funciotn) but that quickly became insufficient 
   when inserting ghost-instructions.
*)
Definition label_function := label -> label.

(* 
   We're skipping the regular method definition and jump straight to the
   extended version which includes assertions. 
*)
Record method := {
  code_of: label -> instr;
  annotations_of : label -> ast;
  eh_table_of: eh_table;
  label_function_of: label_function
}.

(* 
   No field declarations at this point. Wi simply assume that all fields 
   accessed by the program has been properly declared. 
 *)
Definition class := methid -> method.

(* Local variables store. *)
Definition lstore := nat -> jvalue.

Definition emptylstore : lstore := fun x => undefval.

Definition upd (ls:lstore) (n:nat) (v:jvalue) : lstore :=
  fun x => if beq_nat x n then v else ls x.

(* A heap consists of a dynamic part (dheap) and static part (sheap). *)
Definition dheap := loc -> option object.

Definition sheap := classid -> fieldid -> option jvalue.

Definition heap := dheap * sheap.

Definition empty_heap : heap := (fun l => None, fun c f => None).

Definition upd_sheap (h:heap) (cid:classid) (fid:fieldid) (v:jvalue) : heap :=
  (fst h, fun c f => if beq_nat c cid && beq_nat f fid then Some v else (snd h) c f).

Notation "ls '[[' n '⟼' v ']]'" := (upd ls n v) (at level 90).

(* Activation records. *)
Inductive act_record : Set :=
| normal (_: classid) (_: methid) (_: label) (_: stack) (_: lstore)
| exceptional (_: loc).

Record program := {
  classes: classid -> class;
  inv: ast
}.

(* Main class and main method are assumed to be these constants. *)
Definition maincid : classid := O.

Definition mainmid : methid := O.

Definition ghost_valuation := ghostid -> value.

(* We assume that the default value for ghost variables is 0. (Since the undefval is
   reserved for the notion of "going wrong".) *)
Definition initial_gv : ghost_valuation := fun l => intval 0. 

Definition upd_gv (gv: ghost_valuation) (var: ghostid) (val: value) : ghost_valuation :=
  (fun v => if beq_nat v var then val else gv v).

(* We go straight to extended configurations. *)
Definition conf := ghost_valuation * heap * (list act_record).

Definition execution := list conf.

(* Convenience access methods  *)
Definition instr_at (p: program) c m l : instr := code_of (classes p c m) l.

Definition minstr_at (m: method) l : instr := code_of m l.

Definition ast_at   (p: program) c m l : ast   := annotations_of (classes p c m) l.

Definition successor (p: program) c m l := label_function_of (classes p c m) l.

Definition stack_of (c: conf) : option stack :=
  match c with (_, _, (normal _ _ _ s _)::_) => Some s | _ => None end.

Definition lstore_of (c: conf) : option lstore :=
  match c with (_, _, (normal _ _ _ _ ls)::_) => Some ls | _ => None end.

Definition class_of (c: conf) : option classid :=
  match c with (_, _, (normal c _ _ _ _)::_) => Some c | _ => None end.

Definition meth_of (c: conf) : option methid :=
  match c with (_, _, (normal _ m _ _ _)::_) => Some m | _ => None end.

Definition heap_of (c: conf) : heap := snd (fst c).

Definition ars_of (c: conf) : (list act_record) := snd c.

Definition ghost_valuation_of (c: conf) : ghost_valuation := fst (fst c).

Definition current_instr (p: program) (cnf: conf) : option instr :=
  match cnf with (_, _, (normal c m pc _ _)::_) => 
    Some (instr_at p c m pc) | _ => None end.

Definition current_ast (p: program) (cnf: conf) : option ast :=
  match cnf with (_, _, (normal c m pc _ _)::_) => 
    Some (ast_at p c m pc) | _ => None end.

Definition current_label (cnf: conf) : option label :=
  match cnf with (_, _, (normal _ _ pc _ _)::_) => Some pc | _ => None end.

Lemma current_to_instr_at : forall pg p c m pc s l1 l i, 
  current_instr pg (p, normal c m pc s l1 :: l) = Some i ->
  instr_at pg c m pc = i.
Proof.
move => pg p c m pc s l1 l i H.
inversion H as [H0].
move: p H H0; case => g h H H0.
by inversion H0.
Qed.

Lemma instr_at_to_current : forall pg p c m pc s l1 l i, 
  instr_at pg c m pc = i -> current_instr pg (p, normal c m pc s l1 :: l) = Some i.
Proof.
move => pg p c m pc s l1 l i H.
rewrite /current_instr.
case: p => g h.
by rewrite H.
Qed.

(*
  To  show ∥wp(A)∥ C <-> ∥A∥ C' later on, we need a lemma (in the neg case) 
  relating aeval and aeval_f in the following way:

  (aeval a c <-> aeval a' c') -> (aeval_f a c <-> aeval_f a' c')       (1)

  This fact requires more than just [aeval a c -> ~aeval_f a c] and vice versa,
  since if there is an undefined expression (s.t. [~aeval undef c] and 
  [~ aeval_f undef c]) we get the following counter example:

  (aeval ff c <-> aeval undef c') -> (aeval_f ff c <-> aeval_f undef c')

  Fact (1) relies on a stronger fact that

  ~ (aeval a c <-> aeval_f a c)      (2)

  Showing (2) requires that aeval_f is true/defined for all cases in which
  aeval is not true/defined. For example, if the heap is ill-typed, this has 
  to be taken into account in aeval_f.

  This in turn requires that all expressions can be evaluated to a value, no
  matter the context.
*)

Definition is_intval (v: value) : Prop := exists i, v = intval i.

Inductive eeval : expr -> conf -> value -> Prop :=
| e_val : forall c v, eeval (valexp v) c v
| e_nsfield : forall gv c e dh sh ars f l obj, c = (gv, (dh, sh), ars) -> 
    eeval e c (refval l) -> dh l = Some obj -> eeval (nsfield e f) c (obj f)
| e_sfield : forall gv c dh sh ars cid f v, c = (gv, (dh, sh), ars) -> 
    sh cid f = Some v -> eeval (sfield cid f) c v
| e_ghosterr : forall c, eeval ghost_errval c ghost_errval
| e_plus : forall c e1 e2 i j, eeval e1 c (intval i) -> 
    eeval e2 c (intval j) -> eeval (plus e1 e2) c (intval (i + j))
| e_guard_true : forall c eg et ef v, eeval eg c (boolval true ) -> 
    eeval et c v -> eeval (guarded eg et ef) c v
| e_guard_other : forall c eg et ef v, eeval eg c (boolval false) -> 
    eeval ef c v -> eeval (guarded eg et ef) c v
| e_stack : forall c n s, stack_of c = Some s -> eeval (stackexp n) c (s[[n]])
| e_local : forall c n ls, lstore_of c = Some ls -> eeval (local n) c (ls n)
| e_ghostvar : forall c gvarid, eeval (ghost_var gvarid) c ((ghost_valuation_of c) gvarid)
| e_nsfield_err1 : forall c e v f, eeval e c v -> (forall l, v <> refval l) -> 
    eeval (nsfield e f) c undefval
| e_nsfield_err2 : forall gv c e dh sh ars f l, c = (gv, (dh, sh), ars) -> 
    eeval e c (refval l) -> dh l = None -> eeval (nsfield e f) c undefval
| e_sfield_err : forall gv c dh sh ars cid f, c = (gv, (dh, sh), ars) -> 
    sh cid f = None -> eeval (sfield cid f) c undefval
| e_plus_err : forall c e1 e2 v1 v2, eeval e1 c v1 -> eeval e2 c v2 -> 
    ~ is_intval v1 \/ ~ is_intval v2 -> eeval (plus e1 e2) c undefval
| e_guard_err : forall c eg et ef v, eeval eg c v -> (forall b, v <> boolval b) -> 
    eeval (guarded eg et ef) c undefval.

(* Transitions (activation record related) *)
Inductive artrans : program -> act_record -> act_record -> Prop :=
| tr_aload : forall p c m pc n s ls ar1 ar2,
    instr_at p c m pc = aload n ->
    ar1 = normal c m pc s ls ->
    ar2 = normal c m (successor p c m pc) (ls n::s) ls ->
    artrans p ar1 ar2
| tr_astore : forall p c m pc s n ls v ar1 ar2,
    instr_at p c m pc = astore n ->
    ar1 = normal c m pc (v::s) ls ->
    ar2 = normal c m (successor p c m pc) s (ls[[n ⟼ v]]) ->
    artrans p ar1 ar2
| tr_dup : forall p c m pc s ls v ar1 ar2,
    instr_at p c m pc = dup ->
    ar1 = normal c m pc (v::s) ls ->
    ar2 = normal c m (successor p c m pc) (v::v::s) ls ->
    artrans p ar1 ar2
| tr_goto : forall p c m l pc s ls ar1 ar2,
    instr_at p c m pc = goto l ->
    ar1 = normal c m pc s ls ->
    ar2 = normal c m l  s ls ->
    artrans p ar1 ar2
| tr_iconst : forall p c m pc n ls s ar1 ar2,
    instr_at p c m pc = iconst n ->
    ar1 = normal c m pc s ls ->
    ar2 = normal c m (successor p c m pc) ((intval n)::s) ls ->
    artrans p ar1 ar2
| tr_ldc : forall p c m pc s ls v ar1 ar2,
    instr_at p c m pc = ldc v ->
    ar1 = normal c m pc s ls ->
    ar2 = normal c m (successor p c m pc) (v::s) ls ->
    artrans p ar1 ar2
| tr_ifeq_true : forall p c m pc s ls l v ar1 ar2,
    instr_at p c m pc = ifeq l ->
    v = boolval true ->
    ar1 = normal c m pc (v::s) ls ->
    ar2 = normal c m l s ls ->
    artrans p ar1 ar2
| tr_ifeq_false : forall p c m pc s ls l v ar1 ar2,
    instr_at p c m pc = ifeq l ->
    v = boolval false ->
    ar1 = normal c m pc (v::s) ls ->
    ar2 = normal c m l s ls ->
    artrans p ar1 ar2.
    
(* Transitions (heap releated) *)
Inductive htrans : program -> conf -> conf -> Prop :=
| tr_putstatic : forall p c cid fid ars m pc v s ls h c1 c2 ar1 ar2 gv,
    instr_at p c m pc = putstatic cid fid ->
    ar1 = normal c m pc (v::s) ls ->
    ar2 = normal c m (successor p c m pc) (v::s) ls ->
    c1 = (gv, h, ar1::ars) ->
    c2 = (gv, upd_sheap h cid fid v, ar2::ars) ->
    htrans p c1 c2
| tr_getstatic : forall p c cid fid ars m pc v s ls h c1 c2 ar1 ar2 gv,
    instr_at p c m pc = getstatic cid fid ->
    ar1 = normal c m pc s ls ->
    ar2 = normal c m (successor p c m pc) (v::s) ls ->
    c1 = (gv, h, ar1::ars) ->
    c2 = (gv, h, ar2::ars) ->
    htrans p c1 c2.
  
(* Ghost instruction transitions *)
(* Just a stub as of now. *)
Inductive g_eeval : expr -> ghost_valuation -> value -> Prop :=
| ge_val : forall s v, g_eeval (valexp v) s v
| ge_gv : forall gv gid, g_eeval (ghost_var gid) gv (gv gid)
| ge_nsfield : forall e f gv, g_eeval (nsfield e f) gv undefval
| ge_sfield : forall gv cid f, g_eeval (sfield cid f) gv undefval
| ge_stackexp : forall gv n, g_eeval (stackexp n) gv undefval
| ge_local : forall gv l, g_eeval (local l) gv undefval
| ge_plus : forall gv e1 e2, g_eeval (plus e1 e2) gv undefval
| ge_guarded : forall gv e1 e2 e3, g_eeval (guarded e1 e2 e3) gv undefval.
    
Inductive ghosttrans : program -> conf -> conf -> Prop :=
| tr_ghost_upd :
    forall h ars s ls p c m pc gvar e gv v,
      instr_at p c m pc = ghost_instr (gvar, e) -> g_eeval e gv v ->
    ghosttrans p (gv, h, (normal c m pc s ls) :: ars)
      (upd_gv gv gvar v, h, (normal c m (successor p c m pc) s ls) :: ars).
    
(* Transitions (invoke-related) *)
Inductive invtrans : program -> conf -> conf -> Prop :=
| tr_invoke : forall p c m pc cid mid s ls c1 c2 h ar1 ar2 ars gv,
    instr_at p c m pc = invoke cid mid ->
    ar1 = normal c m pc s ls ->
    ar2 = normal c m (successor p c m pc) s ls ->
    c1 = (gv, h, ar1::ars) ->
    c2 = (gv, h, (normal cid mid O emptystack emptylstore)::ar2::ars) ->
    invtrans p c1 c2.
    
(* Transitions (exceptional) *)
(* Not implemented as of now. *)  
  
(* Transitions Combined (Only activation record related as of now.) *)
Inductive trans : program -> conf -> conf -> Prop :=
| tr_ar : forall prog ar1 ar2 ars h c1 c2 gv,
    c1 = (gv, h, ar1::ars) ->
    c2 = (gv, h, ar2::ars) ->
    artrans prog ar1 ar2 ->
    trans prog c1 c2
| tr_ghost : forall p c c', ghosttrans p c c' -> trans p c c'.
  
Inductive trans_star : program -> execution -> Prop :=
| tr_star_nil : forall p, trans_star p nil
| tr_star_sing : forall p c, trans_star p (c :: nil)
| tr_star_step : forall p c c' e, trans p c c' ->
    trans_star p (c' :: e) ->
    trans_star p (c :: c' :: e).
  
Lemma trans_star_seq : forall p c e1 e2,
  trans_star p (e1 ++ c :: nil) -> trans_star p (c :: e2) ->
  trans_star p (e1 ++ c :: e2).
Proof.
move => p c.
elim => [|c']; first by [].
case => [|c0 l] IH e2 H0 H1; rewrite -app_comm_cons /=.
- by apply tr_star_step; inversion H0.
- apply tr_star_step; first by inversion H0.
  rewrite /= in IH; apply IH; last by [].
  by inversion H0.
Qed.

Lemma trans_star_suff : forall p e e', trans_star p (e ++ e') -> trans_star p e'.
Proof.
move => p.
elim => [|c e IH e' H]; first by [].
by apply IH; inversion H; first by apply tr_star_nil.
Qed.

Definition initial_conf (c: conf) : Prop := 
  c = (initial_gv, empty_heap, 
    (normal maincid mainmid O emptystack (fun n => undefval))::nil).

Inductive execution_of p : execution -> Prop :=
| exec_intros : forall exec,
    (forall c, head exec = Some c -> initial_conf c) ->
    (forall pref c c' suff, exec = pref ++ c :: c' :: suff -> trans p c c') ->
    execution_of p exec.

(* 
   An alternative approach would have been to define execution as a dependent
   inductive type directly based on initial_conf and trans. Such approach,
   would be cleaner in many ways, but would unfortunately prevent us from
   using all the nice list lemmas and induction principles in the coq
   library.
   
   Same goes for the approach { ex : list conf | execution_of p ex } since
   elements of this type are not lists either. 
*)

Definition max_execution_of p e : Prop :=
  execution_of p e /\ ~ exists c, execution_of p (e ++ c :: nil).

Lemma exec_nil : forall p, execution_of p nil.
Proof.
move => p.
apply exec_intros; first by [].
move => pref c c' suffx H.
by contradict H; auto with datatypes.
Qed.

Lemma exec_sing_impl_initial : forall p c, execution_of p (c :: nil) -> initial_conf c.
Proof.
move => p c H_exec.
inversion H_exec as [exec H_init H_trans H_eq].
by apply H_init.
Qed.

Lemma exec_append : forall p e c c', execution_of p (e ++ c :: nil) -> trans p c c' ->
  execution_of p (e ++ c :: c' :: nil).
Proof.
move => p e c c' H_exec H_trans.
inversion H_exec as [e' H_init H_suff H_eq].
apply exec_intros.
- pose proof (list_same_head e c c') as H_head.
  move => c0 H_some.
  rewrite -H_head in H_some.
  by apply H_init.
- move => pref c0 c1.
  case => [|c2 suffx] H_pref.
  * rewrite list_rearrange in H_pref.
    have H_re: pref ++ c0 :: c1 :: nil = (pref ++ c0 :: nil) ++ c1 :: nil.
      by rewrite list_rearrange.
    rewrite H_re {H_re} in H_pref.
    apply app_inj_tail in H_pref.
    move: H_pref => [H_pref H_cc'].
    apply app_inj_tail in H_pref.
    move: H_pref => [H_e H_c].
    by rewrite -H_cc' -H_c.
  * apply (H_suff pref c0 c1 (removelast (c2 :: suffx))).
    have H_rl : removelast (e ++ c :: c' :: nil) = removelast (pref ++ c0 :: c1 :: c2 :: suffx).
      by rewrite H_pref.
    have H_neq : c :: c' :: nil <> nil by [].    
    rewrite (removelast_app e H_neq) /= {H_neq} in H_rl.
    have H_re: pref ++ c0 :: c1 :: c2 :: suffx = (pref ++ c0 :: c1 :: nil) ++ c2 :: suffx.
      by rewrite app_ass -app_comm_cons.
    rewrite H_re {H_re} in H_rl.
    have H_nnil: c2 :: suffx <> nil by [].
    rewrite (removelast_app (pref ++ c0 :: c1 :: nil) H_nnil) {H_nnil} in H_rl.
    by rewrite H_rl app_ass -app_comm_cons.
Qed.
  
Lemma exec_impl_trans_star : forall p e, execution_of p e -> trans_star p e.
Proof.
move => p e H_exec.
inversion H_exec as [e' H_init H_suff H_eq].
move: e H_suff {H_exec H_init H_eq e'}. 
elim => [H_suff|c]; first by apply tr_star_nil.
case => [|c' l] H_suff H_pref; first by apply tr_star_sing.
apply tr_star_step; first by apply (H_pref nil c c' l). 
apply H_suff => pref c0 c1 suffx H_eq.
apply H_pref with (pref := c :: pref) (suff := suffx).
by rewrite H_eq.
Qed.

Definition complete_execution_of p ex : Prop :=
  execution_of p ex /\ ~exists c', execution_of p (ex ++ c' :: nil).

Inductive normal_conf : conf -> Prop :=
| is_norm_conf : forall h c m pc s ls ars gv, 
    normal_conf (gv, h, (normal c m pc s ls)::ars).

Inductive exceptional_conf : conf -> Prop :=
| is_exc_conf : forall h o ars gv, exceptional_conf (gv, h, (exceptional o)::ars).

Inductive calling_conf p : conf -> Prop :=
| call_conf : forall gv h c m pc l ls ars,
  trans p (gv, h, ars) (gv, h, (normal c m pc l ls)::ars) ->
  calling_conf p (gv, h, ars).

Inductive returning_conf p : conf -> Prop :=
| ret_norm_conf : forall h ar ars,
  trans p (h, ar::ars) (h, ars) ->
  returning_conf p (h, ar::ars).

Definition visible_conf p c : Prop :=
  calling_conf p c \/ returning_conf p c.

End ProgramModel.
