(* SS_Reflect tutorial: http://inria.ccsd.cnrs.fr/docs/00/25/94/78/PDF/RR-6455.pdf *)

(******************************************************************************)
(*                                                                            *)
(*    IMPORTS                                                                 *)
(*                                                                            *)
(******************************************************************************)
Require Import List.
Require Import ZArith.
Require Import Bool.
Require Import Omega.
Require Import Wf.
Require Import Wellfounded.
Require Import ssreflect.

(******************************************************************************)
(*                                                                            *)
(*    AUXILIARY LIST LEMMAS                                                   *)
(*                                                                            *)
(******************************************************************************)
Section list_aux.
  
  Set Implicit Arguments.
  
  Lemma app_cons_has_head (A: Set) : forall (a : A) l l', exists a', exists l'', l ++ a :: l' = a' :: l''.
  Proof.
    intros.
    destruct l.
    exists a; exists l'.
    reflexivity.
    exists a0; exists (l ++ a :: l').
    reflexivity.
  Qed.
  
  
  Lemma nil_or_app (A: Set) : forall l, l = nil \/ exists l', exists a: A, l = l' ++ a :: nil.
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
  
  
  Lemma in_but_not_last (A: Set) : forall l (a b: A), In a (l ++ b :: nil) -> a = b \/ In a l.
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
  
(*  Lemma head_non_nil (A: Set): forall l l', l <> nil -> head (l ++ l') = head l. *)
    


  Lemma list_rearrange : forall (A: Set) l l' (a:A), l ++ a :: l' = (l ++ a :: nil) ++ l'.
    intros.
    induction l.
    induction l'; simpl; auto.
    rewrite app_ass.
    trivial.
  Qed.
  
  
  Lemma list_rearrange2 (A: Set) : forall l (a b: A), l ++ a :: b :: nil = (l ++ a :: nil) ++ b :: nil.
    intros.
    rewrite app_ass.
    auto with datatypes.
  Qed.
  
  Lemma list_rearrange3 (A: Set) : forall l l' (a : A), (a :: l) ++ l' = a :: l ++ l'.
    reflexivity.
  Qed.
  
  Lemma list_neq_length (A: Set) : forall l l': list A, length l <> length l' -> l <> l'.
    intros.
    contradict H.
    subst.
    reflexivity.
  Qed.
  
  Inductive prefix (A: Set) : list A -> list A -> Prop :=
  | prefix_nil : forall l, prefix nil l
  | prefix_next : forall (a: A) l l', prefix l l' -> prefix (a :: l) (a :: l').
  

  Lemma prefix_firstn (A: Set) : forall n (l : list A), n <= length l -> prefix (firstn n l) l.
    induction n; intros.
    apply prefix_nil.
    destruct l.
    inversion H.
    simpl.
    apply prefix_next.
    apply IHn.
    apply le_S_n; assumption.
  Qed.
  
  
  Inductive proper_prefix (A:Set) : list A -> list A -> Prop :=
  | proper_prefix_nil : forall (l: list A) a, proper_prefix nil (a :: l)
  | proper_prefix_next : forall a l l', proper_prefix l l' -> proper_prefix (a :: l) (a :: l').
  
  
  Lemma proper_prefix_app (A:Set) : forall (l l' l'': list A), proper_prefix l l' -> proper_prefix (l''++l) (l''++l').
    intros.
    induction l''.
    assumption.
    repeat rewrite <- app_comm_cons.
    apply proper_prefix_next.
    assumption.
  Qed.
  
  
  Lemma proper_prefix_last (A: Set) : forall l (a: A), proper_prefix l (l ++ a :: nil).
    intros.
    induction l.
    apply proper_prefix_nil.
    rewrite <- app_comm_cons.
    apply proper_prefix_next.
    assumption.
  Qed.
  
  
  Lemma proper_prefix_split (A: Set) : forall (l l': list A), proper_prefix l' l -> exists x, exists l'', l = l' ++ (x :: l'').
    intros A.
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
  

  Lemma proper_prefix_shorter (A: Set) : forall (l' l: list A), proper_prefix l' l -> length l' < length l.
    intros.
    apply proper_prefix_split in H.
    inversion H; subst.
    inversion H0; subst.
    rewrite app_length.
    simpl.
    omega.
  Qed.
  
  
  Theorem proper_prefix_well_founded (A: Set) : well_founded (@proper_prefix A).
    intros A.
    apply well_founded_lt_compat with (f := @length A).
    apply proper_prefix_shorter.
  Qed.
  
  
  Theorem strong_list_ind (A:Set) (P: list A -> Prop) :
    (forall l, (forall l', proper_prefix l' l -> P l') -> P l) -> forall l, P l.
    intros A P H.
    apply well_founded_ind with (R := @proper_prefix A).
    apply proper_prefix_well_founded.
    intros.
    apply H.
    intros.
    apply H0.
    assumption.
  Qed.
  
  
  Lemma in_list_in_prefix (A: Set) : forall l l' (a: A), proper_prefix l' l -> In a l' -> In a l.
    intros.
    apply proper_prefix_split in H.
    elim H; intros.
    elim H1; intros.
    rewrite H2.
    apply in_or_app.
    left.
    assumption.
  Qed.
  
  
  Lemma nil_or_last (A: Set) : forall l, l = nil \/ exists l', exists a : A, l = l' ++ a :: nil.
    intros.
    destruct l using rev_ind.
    left; reflexivity.
    right.
    exists l.
    exists x.
    reflexivity.
  Qed.
  
  
  Inductive suffix (A:Set) : list A -> list A -> Prop :=
  | suffix_here : forall (l: list A), suffix l l
  | suffix_next : forall a suff l, suffix suff l -> suffix suff (a::l).
  
  
  Lemma suffix_split (A: Set) :
    forall l suff: list A, suffix suff l -> exists pref, l = pref ++ suff.
  Proof.
    intros A l.
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
  
  
  Lemma suffix_app (A: Set) :
    forall l l' l'': list A, suffix l l' -> suffix l (l'' ++ l').
  Proof.
    intros.
    induction l''.
    assumption.
    simpl.
    apply suffix_next.
    assumption.
  Qed.
  
  
  Lemma suffix_transitive (A: Set) :
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
  
  
  Inductive last (A: Set) : list A -> A -> Prop :=
  | last_base : forall a, last (a :: nil) a
  | last_cons : forall l a b, last l a -> last (b::l) a.


  Lemma last_exists (A: Set) : forall l (c : A), exists c', last (c :: l) c'.
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


  Lemma single_last (A: Set) : forall l (a b: A), last l a -> last l b -> a = b.
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
  
  Lemma last_app (A: Set) : forall l l' (a: A), last l' a -> last (l++l') a.
    intros.
    induction l.
    simpl.
    assumption.
    simpl.
    apply last_cons.
    assumption.
  Qed.
  
  
  Lemma app_last (A: Set) : forall l (a: A), last (l ++ a :: nil) a.
  Proof.
    intros.
    induction l.
    apply last_base.
    rewrite list_rearrange3.
    apply last_cons.
    assumption.
  Qed.

  
  Lemma last_app_prefix (A: Set) :
    forall (l l': list A) a, last l a -> exists l', l = l' ++ a::nil.
  Proof.
    intros A l l'.
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
  
  
  Lemma last_app_cons (A: Set) :
    forall l (a b: A), last (l ++ a::nil) b -> a = b.
  Proof.
    intros.
    apply last_app_prefix in H.
    elim H; intros.
    apply app_inj_tail in H0.
    elim H0; intros; assumption.
    auto.
  Qed.
  
  
  Lemma list_same_head (A: Set) :
    forall l (a b: A), head (l ++ a :: nil) = head (l ++ a :: b :: nil).
    induction l; intros; reflexivity.
  Qed.

  Unset Implicit Arguments.
  
End list_aux.




(******************************************************************************)
(*                                                                            *)
(*    BASIC DEFINITIONS                                                       *)
(*                                                                            *)
(******************************************************************************)
Section basic_defs.
  
  Definition classid := nat.
  Definition methid := nat.
  Definition fieldid := nat.
  Definition label := nat.
  Definition loc := nat.
  
  
  Inductive jvalue :=
  | intval  (_: Z)
  | boolval (_: bool)
  | refval  (_: loc)
  | undefval.           (* used for, say 5 = true *)
  
  Inductive value :=
  | jval (_: jvalue)
  | ghost_errval.       (* represents \bot *)
  
  Coercion jval : jvalue >-> value.
  
  Definition object := fieldid -> jvalue.
  Definition stack := list jvalue.
  Definition emptystack : stack := nil.
  
End basic_defs.

Notation "s '[[' n ']]'" := (nth n s undefval) (at level 90).




(******************************************************************************)
(*                                                                            *)
(*    EXPRESSIONS AND ASSERTIONS                                              *)
(*                                                                            *)
(******************************************************************************)
Section expressions_assertions.
  
  Definition ghostid := nat.
  
  (* Assertions *)
  Inductive ast :=
  | tt
  | ff
  | le (_ _: expr)
  | eq (_ _: expr)
  | or (_ _: ast)
  | and (_ _: ast)
  | neg (_: ast)
  | ifelse (_ _ _: ast)
  with expr :=
  | valexp (_: value)
  | ghost_var (_: ghostid)
  | nsfield (_: expr) (_: fieldid)
  | sfield (_: classid) (_: fieldid)
  | stackexp (_: nat)
  | local (_: nat)
  | plus (_ _: expr)
  | guarded (_ _ _: expr).
  
  
  Coercion valexp : value >-> expr.
  
  
  Inductive sub_exp : expr -> expr -> Prop :=
  | sub_base : forall e, sub_exp e e
  | sub_nsfield : forall e e0 fid, sub_exp e e0 -> sub_exp e (nsfield e0 fid)
  | sub_plus : forall e e0 e1, sub_exp e e0 \/ sub_exp e e1 -> sub_exp e (plus e0 e1)
  | sub_guarded : forall e e0 e1 e2, sub_exp e e0 \/ sub_exp e e1 \/ sub_exp e e2 -> sub_exp e (guarded e0 e1 e2).
  
  
  Definition ghost_expr e := sub_exp ghost_errval e \/ exists gid, sub_exp (ghost_var gid) e.
  
  
End expressions_assertions.



(******************************************************************************)
(*                                                                            *)
(*    PROGRAM MODEL                                                           *)
(*                                                                            *)
(******************************************************************************)
Section program_model.
  
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
  
  
  (* Exception handler records (Rows in the exception handler table) *)
  Record eh_record : Set := {
    start_label  : label;
    end_label    : label;
    target_label : label;
    handled_classes : classid
  }.
  Definition eh_table := list eh_record.
  
  
  (* A label function is used to look up successor-labels.
     It used to be 'S' (the nat successor-funciotn) but that quickly became
     insufficient when inserting ghost-instructions.
  *)
  Definition label_function := label -> label.
  
  
  (* We're skipping the regular method definition and jump straight to the
     extended version which includes assertions. *)
  Record method := {
    code_of: label -> instr;
    annotations_of : label -> ast;
    eh_table_of: eh_table;
    label_function_of: label_function
  }.
  
  
  (* No field declarations at this point. Wi simply assume that all fields accessed
     by the program has been properly declared. *)
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
    match cnf with (_, _, (normal c m pc _ _)::_) => Some (instr_at p c m pc) | _ => None end.
  Definition current_ast (p: program) (cnf: conf) : option ast :=
    match cnf with (_, _, (normal c m pc _ _)::_) => Some (ast_at p c m pc) | _ => None end.
  Definition current_label (cnf: conf) : option label :=
    match cnf with (_, _, (normal _ _ pc _ _)::_) => Some pc | _ => None end.
  
  Lemma current_to_instr_at :
    forall pg p c m pc s l1 l i, current_instr pg (p, normal c m pc s l1 :: l) = Some i ->
      instr_at pg c m pc = i.
  Proof.
    intros.
    inversion H.
    destruct p.
    inversion H1; subst.
    reflexivity.
  Qed.

  Lemma instr_at_to_current :
    forall pg p c m pc s l1 l i, instr_at pg c m pc = i -> current_instr pg (p, normal c m pc s l1 :: l) = Some i.
  Proof.
    intros.
    unfold current_instr.
    destruct p.
    rewrite H.
    reflexivity.
  Qed.


(*
To  show ∥wp(A)∥ C <-> ∥A∥ C' later on, we need a lemma (in the neg case) relating aeval and aeval_f in the following way:

(aeval a c <-> aeval a' c') -> (aeval_f a c <-> aeval_f a' c')       (1)

This fact requires more than just [aeval a c -> ~aeval_f a c] and vice versa,
since if there is an undefined expression (s.t. [~aeval undef c] and [~aeval_f undef c]) we get the following counter example:

(aeval ff c <-> aeval undef c') -> (aeval_f ff c <-> aeval_f undef c')

Fact (1) relies on a stronger fact that

~(aeval a c <-> aeval_f a c)      (2)

Showing (2) requires that aeval_f is true/defined for all cases in which aeval is not true/defined.
for example, if the heap is ill-typed, this has to be taken into account in aeval_f.

This in turn requires that all expressions can be evaluated to a value, no matter the context.
*)

Definition is_intval (v: value) : Prop := exists i, v = intval i.

Inductive eeval : expr -> conf -> value -> Prop :=
  | e_val          : forall c v, eeval (valexp v) c v
  | e_nsfield      : forall gv c e dh sh ars f l obj, c = (gv, (dh, sh), ars) -> eeval e c (refval l) -> dh l = Some obj -> eeval (nsfield e f) c (obj f)
  | e_sfield       : forall gv c dh sh ars cid f v, c = (gv, (dh, sh), ars) -> sh cid f = Some v -> eeval (sfield cid f) c v
  | e_ghosterr        : forall c, eeval ghost_errval c ghost_errval
  | e_plus         : forall c e1 e2 i j, eeval e1 c (intval i) -> eeval e2 c (intval j) -> eeval (plus e1 e2) c (intval (i + j))
  | e_guard_true   : forall c eg et ef v, eeval eg c (boolval true ) -> eeval et c v -> eeval (guarded eg et ef) c v
  | e_guard_other  : forall c eg et ef v, eeval eg c (boolval false) -> eeval ef c v -> eeval (guarded eg et ef) c v
  | e_stack        : forall c n s, stack_of c = Some s -> eeval (stackexp n) c (s[[n]])
  | e_local        : forall c n ls, lstore_of c = Some ls -> eeval (local n) c (ls n)
  | e_ghostvar     : forall c gvarid, eeval (ghost_var gvarid) c ((ghost_valuation_of c) gvarid)
  | e_nsfield_err1 : forall c e v f, eeval e c v -> (forall l, v <> refval l) -> eeval (nsfield e f) c undefval
  | e_nsfield_err2 : forall gv c e dh sh ars f l, c = (gv, (dh, sh), ars) -> eeval e c (refval l) -> dh l = None -> eeval (nsfield e f) c undefval
  | e_sfield_err   : forall gv c dh sh ars cid f, c = (gv, (dh, sh), ars) -> sh cid f = None -> eeval (sfield cid f) c undefval
  | e_plus_err     : forall c e1 e2 v1 v2, eeval e1 c v1 -> eeval e2 c v2 -> ~is_intval v1 \/ ~is_intval v2 -> eeval (plus e1 e2) c undefval
  | e_guard_err    : forall c eg et ef v, eeval eg c v -> (forall b, v <> boolval b) -> eeval (guarded eg et ef) c undefval.





  
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
      forall h ars s ls
        `(instr_at p c m pc = ghost_instr (gvar, e))
        `(g_eeval e gv v),
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
  

  Lemma trans_star_seq : forall p c `(trans_star p (e1 ++ c :: nil)) `(trans_star p (c :: e2)),
    trans_star p (e1 ++ c :: e2).
  Proof.
intros.
induction e1.
assumption.
rewrite <- app_comm_cons.
induction e1.
simpl.
apply tr_star_step.
simpl in trans_star0.
inversion trans_star0.
assumption.
assumption.
simpl in * |- *.
apply tr_star_step.
inversion trans_star0.
assumption.
apply IHe1.
inversion trans_star0.
assumption.
Qed.


Lemma trans_star_suff : forall p e e', trans_star p (e ++ e') -> trans_star p e'.
intros.
induction e.
assumption.
apply IHe.
simpl in H.
inversion H.
apply tr_star_nil.
assumption.
Qed.






  Definition initial_conf (c: conf) : Prop :=
    c = (initial_gv, empty_heap, (normal maincid mainmid O emptystack (fun n => undefval))::nil).
  
  
  Inductive execution_of p : execution -> Prop :=
  | exec_intros : forall exec,
                      (forall c, head exec = Some c -> initial_conf c) ->
                      (forall pref c c' suff, exec = pref ++ c :: c' :: suff -> trans p c c') ->
                      execution_of p exec.

  (* An alternative approach would have been to define execution as a dependent
     inductive type directly based on initial_conf and trans. Such approach,
     would be cleaner in many ways, but would unfortunately prevent us from
     using all the nice list lemmas and induction principles in the coq
     library.
     
     Same goes for the approach { ex : list conf | execution_of p ex } since
     elements of this type are not lists either. *)

  Definition max_execution_of p e : Prop :=
    execution_of p e /\ ~ exists c, execution_of p (e ++ c :: nil).

  Lemma exec_nil : forall p, execution_of p nil.
    intros.
    apply exec_intros.
    intros.
    inversion H.
    intros.
    contradict H.
    auto with datatypes.
  Qed.
  

Lemma exec_append : forall `(execution_of p (e ++ c :: nil)) `(trans p c c'),
  execution_of p (e ++ c :: c' :: nil).
intros.
inversion execution_of0.
apply exec_intros.

pose proof (list_same_head e c c').
rewrite H2 in H.
assumption.

destruct suff.
intros.
rewrite list_rearrange in H2.
assert (pref ++ c0 :: c'0 :: nil = (pref ++ c0 :: nil) ++ c'0 :: nil).
  rewrite list_rearrange.
  reflexivity.
rewrite H3 in H2.
apply app_inj_tail in H2.
elim H2; clear H2; intros.
apply app_inj_tail in H2.
elim H2; clear H2; intros.
subst.
assumption.

intros.
apply (H0 pref c0 c'0 (removelast (c1 :: suff))).

assert (forall (A: Set) (l l': list A), l = l' -> removelast l = removelast l').
  intros; subst; reflexivity.

apply H3 in H2.
assert (H_tmp : c :: c' :: nil <> nil).
  intro; discriminate.
rewrite (removelast_app e H_tmp) in H2; clear H_tmp.
simpl in H2.
assert (pref ++ c0 :: c'0 :: c1 :: suff = (pref ++ c0 :: c'0 :: nil) ++ c1 :: suff).
  rewrite app_ass.
  rewrite <- app_comm_cons.
  reflexivity.
rewrite H4 in H2.
assert (H_nnil : c1 :: suff <> nil).
  intro; discriminate.
rewrite (removelast_app (pref ++ c0 :: c'0 :: nil) H_nnil) in H2.
rewrite H2.
rewrite app_ass.
rewrite <- app_comm_cons.
rewrite list_rearrange3.
assert (forall (A: Set) (l : list A), nil ++ l = l).
  reflexivity.
rewrite H5.
reflexivity.
Qed.


  
  Lemma exec_impl_trans_star : forall p `(execution_of p e), trans_star p e.
  Proof.
    intros.
    inversion execution_of0; subst.
    clear execution_of0 H.
    induction e.
    apply tr_star_nil.
    induction e.
    apply tr_star_sing.
    apply tr_star_step.
    apply H0 with (pref := nil) (suff := e).
    reflexivity.
    apply IHe.
    intros.
    apply H0 with (pref := a :: pref) (suff := suff).
    rewrite <- app_comm_cons.
    rewrite H.
    reflexivity.
  Qed.
  
  
  Definition complete_execution_of p ex : Prop :=
    execution_of p ex /\ ~exists c', execution_of p (ex ++ c' :: nil).
  
  
  Inductive normal_conf : conf -> Prop :=
  | is_norm_conf : forall h c m pc s ls ars gv, normal_conf (gv, h, (normal c m pc s ls)::ars).
  
  
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

End program_model.


(******************************************************************************)
(*                                                                            *)
(*    SEMANTICS OF ASSERTIONS                                                 *)
(*                                                                            *)
(******************************************************************************)
Section semantics_assertions.
  
  
  
  Lemma int_or_other : forall v, is_intval v \/ ~is_intval v.
  Proof.
    intro.
    case v.
    intro; case j; try (intros; right; unfold is_intval; intro; elim H; intros; discriminate).
    left; exists z; reflexivity.
    right.
    intro.
    inversion H.
    discriminate.
  Qed.

  
  Lemma complete_geeval : forall e gv, exists v, g_eeval e gv v.
    intros.
    destruct e.
    exists v; apply ge_val.
    exists (gv g); apply ge_gv.
    exists undefval; apply ge_nsfield.
    exists undefval; apply ge_sfield.
    exists undefval; apply ge_stackexp.
    exists undefval; apply ge_local.
    exists undefval; apply ge_plus.
    exists undefval; apply ge_guarded.
  Qed.


Set Printing Coercions.
Lemma deterministic_geeval : forall `(g_eeval e c v1) `(g_eeval e c v2), v1 = v2.
intros.
inversion g_eeval0; inversion g_eeval1; subst; try (inversion g_eeval1; discriminate); try reflexivity.
inversion H2.
reflexivity.
inversion g_eeval0; inversion g_eeval1.
subst.
reflexivity.
Qed.

Lemma complete_eeval : forall e c, normal_conf c -> exists v, eeval e c v.

  intros.
  induction e.

  destruct v.

  (* value *)
  exists j.
  apply e_val.
  
  (* ghost_errval *)
  exists ghost_errval.
  apply e_ghosterr.
  
  (* ghost var *)
  inversion H; subst.
  exists (gv g).
  apply e_ghostvar.

  (* ns field *)
  elim IHe; intros.
  destruct x.
  destruct j.
  
  exists undefval; apply e_nsfield_err1 with (v := intval z); [assumption | intros; discriminate].
  exists undefval; apply e_nsfield_err1 with (v := boolval b); [assumption | intros; discriminate].

  inversion H; subst.
  elim IHe; intros.

  assert ((exists l, x = refval l) \/ (forall l, x <> refval l)).
    destruct x.
    destruct j.
    right; intros; intro; discriminate.
    right; intros; intro; discriminate.
    left; exists l0; reflexivity.
    right; intros; intro; discriminate.
    right; intros; intro; discriminate.
  
  elim H2; intros.
elim H3; intros.
destruct h as (dh, sh).

assert (dh x0 = None \/ exists obj, dh x0 = Some obj).
  destruct (dh x0).
  right; exists o; reflexivity.
  left; reflexivity.

elim H5; intros.
exists undefval.
apply e_nsfield_err2 with (gv := gv) (dh := dh) (sh := sh) (ars := normal c0 m pc s ls :: ars) (l := x0).
reflexivity.
rewrite <- H4; assumption.
assumption.

elim H6; intros obj.
exists (obj f).
apply e_nsfield with (gv := gv) (dh := dh) (sh := sh) (ars := normal c0 m pc s ls :: ars) (l := x0).
reflexivity.
rewrite <- H4; assumption.
assumption.

exists undefval.
apply e_nsfield_err1 with (v := x).
assumption.
assumption.

exists undefval.
apply e_nsfield_err1 with (v := undefval).
assumption.
intros.
intro; discriminate.

exists undefval.
apply e_nsfield_err1 with (v := ghost_errval).
assumption.
intros.
intro; discriminate.

(* sfield *)
inversion H; intros.
destruct h as (dh, sh).
assert ((sh c0) f = None \/ exists v, (sh c0) f = Some v).
  destruct (sh c0).
  right; exists j; reflexivity.
  left; reflexivity.
elim H1; intros.
exists undefval.
apply e_sfield_err with (gv := gv) (dh := dh) (sh := sh) (ars := normal c1 m pc s ls :: ars).
reflexivity.
assumption.
elim H2; intros.
exists x.
apply e_sfield with (gv := gv) (dh := dh) (sh := sh) (ars := normal c1 m pc s ls :: ars).
reflexivity.
assumption.

(* stackexp *)
inversion H; subst.
exists (s[[n]]).
apply e_stack.
reflexivity.

(* local n *)
inversion H; subst.
exists (ls n).
apply e_local.
reflexivity.

(* plus *)
elim IHe1; intros.
assert (is_intval x \/ ~is_intval x).
  apply int_or_other.
elim H1; intros.

elim IHe2; intros.
assert (is_intval x0 \/ ~is_intval x0).
  apply int_or_other.
elim H4; intros.
inversion H2; inversion H5; subst.
exists (intval (x1 + x2)).
apply e_plus.
assumption.
assumption.

exists undefval.
apply e_plus_err with (v1 := x) (v2 := x0).
assumption.
assumption.
right; assumption.

exists undefval.
elim IHe2; intros.
apply e_plus_err with (v1 := x) (v2 := x0).
assumption.
assumption.
left; assumption.

(* guarded *)
elim IHe1; elim IHe2; elim IHe3; intros.
assert (forall v, (exists b, v = boolval b) \/ forall b, v <> boolval b).
  intros.
  destruct v.
  right; intros; discriminate.
  left; exists b; reflexivity.
  right; intros; discriminate.
  right; intros; discriminate.
destruct x1.
elim (H3 j); intros.
elim H4; intros.
destruct x1.
exists x0.
apply e_guard_true.
rewrite H5 in H2.
assumption.
assumption.
exists x.
apply e_guard_other.
rewrite H5 in H2.
assumption.
assumption.
Set Printing Coercions.
exists undefval.
apply e_guard_err with (v := jval j).
assumption.
intro.
intro.
inversion H5.
contradict H7.
apply H4.

exists undefval.
apply e_guard_err with (v := ghost_errval).
assumption.
intros.
discriminate.
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
      omega.
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
      omega.
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
  assert (x <= x0 \/ x > x0). omega.
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
  omega.
  
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


End semantics_assertions.

Notation "'∥' a '∥' c" := (aeval a c) (at level 90).
(* Notation "'∥' e '∥' c" := (eeval e c) (at level 90). *)

(* The default variable denotes an assertion that expresses that
   all variables have their default values. *)
Variable default : ast.




(******************************************************************************)
(*                                                                            *)
(*    WEAKEST PRECONDITIONS                                                   *)
(*                                                                            *)
(******************************************************************************)
Section weakest_precondition.
  
  Fixpoint unshift (a:ast) : ast :=
    match a with
      | le e0 e1   => le (eunshift e0) (eunshift e1)
      | eq e0 e1   => eq (eunshift e0) (eunshift e1)
      | and a0 a1  => and (unshift a0) (unshift a1)
      | or a0 a1   => or (unshift a0) (unshift a1)
      | neg a0     => neg (unshift a0)
      | ifelse a0 a1 a2 => ifelse (unshift a0) (unshift a1) (unshift a2)
      | other      => a
    end
  with eunshift (e:expr) : expr :=
    match e with
      | nsfield e0 fid     => nsfield (eunshift e0) fid
      | stackexp (S n)     => stackexp n
      | plus e0 e1         => plus (eunshift e0) (eunshift e1)
      | guarded e0 e1 e2   => guarded (eunshift e0) (eunshift e1) (eunshift e2)
      | other              => e
    end.
  
  
  Fixpoint shift (a:ast) : ast :=
    match a with
      | le e0 e1  => le (eshift e0) (eshift e1)
      | eq e0 e1  => eq (eshift e0) (eshift e1)
      | and a0 a1 => and (shift a0) (shift a1)
      | or a0 a1  => or (shift a0) (shift a1)
      | neg a0    => neg (shift a0)
      | ifelse a0 a1 a2 => ifelse (shift a0) (shift a1) (shift a2)
      | other     => a
    end
  with eshift (e:expr) : expr :=
    match e with
      | nsfield e0 fid     => nsfield (eshift e0) fid
      | stackexp n         => stackexp (S n)
      | plus e0 e1         => plus (eshift e0) (eshift e1)
      | guarded e0 e1 e2   => guarded (eshift e0) (eshift e1) (eshift e2)
      | other              => e
    end.
  
  
  Definition substitute_eq (expr0 expr1: expr) : bool :=
    match expr0, expr1 with
      | sfield c f, sfield c' f' => beq_nat c c' && beq_nat f f'
      | stackexp n, stackexp n' => beq_nat n n'
      | local n, local n' => beq_nat n n'
      | _, _ => false
    end.
  
  
  Fixpoint subste (e n o:expr) : expr :=
    if substitute_eq e o then n else
      match e with
        | nsfield e0 fid  => nsfield (subste e0 n o) fid
        | plus e0 e1 => plus (subste e0 n o) (subste e1 n o)
        | guarded e0 e1 e2 => guarded (subste e0 n o) (subste e1 n o) (subste e2 n o)
        | other => e
      end.
  
  
  Fixpoint subst (a: ast) (n o: expr) : ast :=
    match a with
      | le e0 e1  => le (subste e0 n o) (subste e1 n o)
      | eq e0 e1  => eq (subste e0 n o) (subste e1 n o)
      | and a0 a1 => and (subst a0 n o) (subst a1 n o)
      | or a0 a1  => or (subst a0 n o) (subst a1 n o)
      | neg a0    => neg (subst a0 n o)
      | ifelse a0 a1 a2 => ifelse (subst a0 n o) (subst a1 n o) (subst a2 n o)
      | other     => a
    end.
  
  Notation "c1 '[[' c2 '∕' c3 ']]'" := (subst  c1 c2 c3) (at level 90).
  
  
  (* Only non-exceptional WP as of now. *)
  Definition wp (p:program) (c:classid) (m:methid) (l:label) : ast := 
    let a' := ast_at p c m (successor p c m l) in
    match (instr_at p c m l) with
      | aload n        => unshift (a' [[local n ∕ stackexp 0]])
      | astore n       => and (shift a') (eq (stackexp 0) (local n))
      | athrow         => tt
      | dup            => unshift (a' [[stackexp 1 ∕ stackexp 0]])
      | iadd           => (shift a') [[plus (stackexp 0) (stackexp 1)  ∕  (stackexp 1)]]
      | getfield f     => unshift (a' [[nsfield (stackexp 0) f ∕ stackexp 0]])
      | getstatic c f  => unshift (a' [[sfield c f ∕ stackexp 0]])
      | goto l'        => ast_at p c m l'
      | iconst n       => unshift (a' [[valexp (intval n) ∕ stackexp 0]])
      | ifeq l'        => ifelse (eq (stackexp 0) (valexp (intval 0))) (shift (ast_at p c m l')) (shift (a'))
      | putstatic c f  => (shift (a'))[[stackexp 0 ∕ sfield c f]]
      | ldc v          => unshift (a' [[valexp v ∕ stackexp 0]])
      | ret            => inv p
      | invoke c m     => inv p
      | exit           => tt
      | nop            => a'
      | ghost_instr (g, e) => a' [[e ∕ ghost_var g]]
    end.

End weakest_precondition.




(******************************************************************************)
(*                                                                            *)
(*    VALIDITY                                                                *)
(*                                                                            *)
(******************************************************************************)
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
  
  
  Definition globally_valid : Prop := forall `(execution_of p e), valid_exec e.
  
  
  Definition locally_valid_meth cid mid : Prop :=
    (forall c, ∥ inv p ∥ c -> ∥ ast_at p cid mid O ∥ c) /\
    (forall c l, ∥ ast_at p cid mid l ∥ c -> ∥ wp p cid mid l ∥ c).
  
  
  Definition locally_valid : Prop :=
    (forall cid mid, locally_valid_meth cid mid) /\
    (forall c, ∥ default ∥ c -> ∥ ast_at p maincid mainmid O ∥ c) /\
    (forall c, ∥ default ∥ c -> ∥ inv p ∥ c).
  
  
  Lemma initial_default : forall c, initial_conf c -> ∥ default ∥ c.
  (* Should probably be encoded as Hypothesis. *)
  Admitted.
  
  
  Lemma wp_correct_normal :
    forall h cid mid pc s ls ars c' a,
      let c := (h, (normal cid mid pc s ls)::ars) in
        trans p c c' ->
        normal_conf c' ->
        current_ast p c' = Some a ->
        (∥ wp p cid mid pc ∥ c <->
        ∥ a ∥ c').

intros.
inversion H; subst.

(* aload n *)
Lemma wp_correct_normal_aload : forall c m pc s ls h n ars gv,
  instr_at p c m pc = aload n ->
  (∥wp p c m pc ∥ (gv, h, normal c m pc s ls :: ars) <->
  ∥ast_at p c m (successor p c m pc) ∥ (gv, h, normal c m (successor p c m pc) (ls n :: s) ls :: ars)).
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



inversion H0; subst.
inversion H1; subst.
inversion H2; subst.
inversion H4; subst.
inversion H6; subst.
inversion H5; subst.

(* aload n *)
apply wp_correct_normal_aload; assumption.

(* astore n *)
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
  
  
  Lemma no_empty_ar_stack_trans : forall `(trans p (gv, h, ar :: ars) (gv', h', nil)), False.
    intros.
    inversion trans0; subst.
    inversion H0; subst.
    inversion H; subst.
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
contradict (no_empty_ar_stack_trans H).
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
    inversion H_atrans; subst; inversion H; contradict H9; apply list_neq_length; simpl; omega.
    inversion H.
    contradict H16; apply list_neq_length; simpl; omega.
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
          apply list_neq_length; simpl; omega).
    
    (* ghost-trans *)
    subst cnf.
    inversion H2.
    contradict H15.
    apply list_neq_length; simpl; omega.
    
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
  
  
  Lemma no_double_exc_trans : forall `(trans p c (gv, h, exceptional o1 :: exceptional o2 :: ars)), exists gv', exists h', c = (gv', h', exceptional o1 :: exceptional o2 :: ars).
    intros.
    inversion trans0; subst.
    inversion H1; subst; try (inversion H0; inversion H0; subst).
inversion H; subst.
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



(******************************************************************************)
(*                                                                            *)
(*    CONTRACTS                                                               *)
(*                                                                            *)
(******************************************************************************)
Section contracts.

  Open Scope type_scope.
  
  Inductive event :=
  | bef_event (_: classid) (_: methid) (arg: value)
  | aft_event (_: classid) (_: methid) (ret: value)
  | exc_event (_: classid) (_: methid).
  
  Definition event_trace := list event.
  
  (* The following definition is not distributive under ++ operations.
     That is, trace_of (exec1 ++ exec2) <> (trace_of exec1) ++ (trace_of exec2) *)
  Definition observed_event (p: program) (c: conf) : option event :=
    match c with
      | (gv, h, normal c m pc s ls :: ars) =>
        match (instr_at p c m pc) with
          | invoke c' m' => Some (bef_event c' m' (s[[0]]))
          | ret => Some (aft_event c m (s[[0]]))
          | _ => None
        end
      | (gv, h, exceptional o :: ars) => None (* add exc_event *)
      | (gv, h, nil) => None
    end.
  
  Fixpoint event_trace_of (p: program) (e: execution) : event_trace :=
    match e with
      | nil => nil
      | c :: e' => match observed_event p c with
                    | Some evt => evt :: event_trace_of p e'
                    | None => event_trace_of p e'
                  end
    end.
  
  
  Lemma event_trace_distr : forall p l l', event_trace_of p (l ++ l') =
                                      event_trace_of p l ++ event_trace_of p l'.
    intros.
    induction l.
    reflexivity.
    rewrite <- app_comm_cons.
    simpl.
    destruct (observed_event p a).
    rewrite IHl.
    reflexivity.
    rewrite IHl.
    reflexivity.
  Qed.
  
  
  Inductive event_modifier := before | after  | exception.
  
  Definition contract := (event_modifier * classid * methid) -> ghost_update.
  
  Definition sec_state := ghost_valuation.
  
  Definition sec_state_trace := list sec_state.
  
  
  Inductive ss_updates_of (contr : contract) : event_trace -> list ghost_update -> Prop :=
  | ssu_done : ss_updates_of contr nil nil
  | ssu_bef  : forall c m arg t' gus', ss_updates_of contr t' gus' ->
                                  ss_updates_of contr (bef_event c m arg :: t') (contr (before, c, m) :: gus')
  | ssu_aft  : forall c m ret t' gus', ss_updates_of contr t' gus' ->
                                  ss_updates_of contr (aft_event c m ret :: t') (contr (after, c, m) :: gus').
  
  Inductive sst_tail : list ghost_update -> sec_state_trace -> Prop :=
  | sst_done : forall ss, sst_tail nil (ss :: nil)
  | sst_step : forall ss ss' gvar exp v sst gus, 
        g_eeval exp ss v -> 
        ss' = (upd_gv ss gvar v) ->
        sst_tail gus (ss' :: sst) ->
        sst_tail ((gvar, exp) :: gus) (ss :: ss' :: sst).
  
  Definition is_sec_state_trace (ssus : list ghost_update) (sst : sec_state_trace) : Prop :=
    head sst = Some initial_gv /\ sst_tail ssus sst.
  
  
  (* For simplicity: The ghost state is represented by a single fixed ghost variable 'gs'. *)
  (* We still have a notion of ghost valuations to be able to handle local ghost variables
     used for storing arguments and return values. *)
  Variable gs : ghostid.
  
  
  Definition violating_sec_state (gv: ghost_valuation) := gv gs = ghost_errval.
  
  
  Definition accepted_by contr (event_tr: event_trace) :=
    forall gus sec_tr, 
      ss_updates_of contr event_tr gus ->
      is_sec_state_trace gus sec_tr ->
      hd initial_gv sec_tr = initial_gv ->
      (forall ss, In ss sec_tr -> ~ violating_sec_state ss).
  
  
  Definition adheres_to p contr : Prop :=
    forall `(execution_of p e), accepted_by contr (event_trace_of p e).
  
  
  (*
  The original definition of "Ghost Instruction Goes Wrong" is, 
  "no guards of the ghost instruction hold".
  If all inserted ghost instructions has the shape
  
    x := g_1 -> v_1 | g_2 -> v_2 | ... | g_n -> v_n | ghost_errval
  
  the notion of going wrong is equivalent to "no ghost var equals ghost_errval".
  This is the reason why initial_gv has all vars initialized to 0 instead of ghost_errval.
  *)
  
  
  Definition exec_never_goes_wrong e :=
    forall c, In c e -> ~ violating_sec_state (ghost_valuation_of c).
  
  
  Section ghost_inliner.
    
    (* Note that assertions are irrelevant in this section. *)
    
    Variable contr: contract.
    
    (* My initial attempt encoded the ghost_inliner as a function. That approach
       ran into the following problem:
       
       If a ghost instruction is to be inserted, it needs a label. Since method
       bodies are total mappings from lables to instructions, it is impossible
       to dig out a fresh label.
       
       The obvious fix would be to let method bodies be partial ("option")
       mappings. Unfortunately the option-type spreads like a plague in the defs
       and all proofs needs splitting on Some/None.
       
       This is why it is currently encoded as a proposition over programs. *)
    
    Definition ghost_inlined_meth (m gm: method) : Prop :=
      forall l,
        let l'   := label_function_of gm l in
        let l''  := label_function_of gm l' in
        let l''' := label_function_of gm l'' in
          
        forall (c: classid) (m': methid),
          match minstr_at m l with
          | invoke c m' => minstr_at gm l   = ghost_instr (contr (before, c, m')) /\
                           minstr_at gm l'  = invoke c m' /\
                           minstr_at gm l'' = ghost_instr (contr (after, c, m')) /\
                           label_function_of m l = l'''
          | i => minstr_at gm l = i /\
                 label_function_of m l = l
          end.
    
    
    Definition ghost_inlined_class (c gc: class) : Prop :=
      forall mid, ghost_inlined_meth (c mid) (gc mid).

    Definition ghost_inlined (p pg: program) : Prop :=
      forall cid, ghost_inlined_class (classes pg cid) (classes p cid).
  
  End ghost_inliner.
  
  (*
  Definition ghost_update_of pg (c : conf) : option ghost_update :=
    match c with
      | (_, _, normal c m pc s l :: _) =>
        match instr_at pg c m pc with
          | ghost_instr gu => Some gu
          | otherwise => None
        end
      | otherwise => None
    end.
  *)
  Definition ghost_update_of pg (c : conf) : option ghost_update :=
    match current_instr pg c with
      | Some (ghost_instr gu) => Some gu
      | _ => None
    end.

  (* Returns ghost updates that *have been carried out* (to be compatible with ss_after). *)
  Fixpoint ghost_updates_of pg (eg : execution) : list ghost_update :=
    match eg with
      | nil => nil
      | c :: eg' =>
        match eg' with
          | nil => nil
          | c' :: eg'' =>
            match ghost_update_of pg c with
              | Some gu => gu :: ghost_updates_of pg eg'
              | None => ghost_updates_of pg eg'
            end
        end
    end.
  
  Fixpoint seen_ghost_updates_of pg (eg : execution) : list ghost_update :=
    match eg with
      | nil => nil
      | c :: eg' =>
        match ghost_update_of pg c with
          | Some gu => gu :: seen_ghost_updates_of pg eg'
          | None => seen_ghost_updates_of pg eg'
        end
    end.
  
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

Check gus_eq_seen_gus.

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

End conf_classes.


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
(* Work in progress *)
(* See temp2.v in repository for a sketch proof. *)
(* It's a straigt forward induction over the length of the execution and
   a case split on the type of the last configuration *)
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
intros p e.
elim e; intros.
exists nil.
split.
apply prefix_nil.
inversion prefix0.
reflexivity.

destruct gus_pref.
exists nil; split.
apply prefix_nil.
reflexivity.

case_eq (ghost_update_of p a).
intros.
inversion prefix0.
destruct l.
inversion H4.
pose proof (H gus_pref).
rewrite H0 in H4.
assert (H_listeq : l' = ghost_updates_of p (c :: l)).
  inversion H4; subst; reflexivity.
rewrite H_listeq in H2.
apply H5 in H2.
elim H2; intros.
elim H6; intros.

(* clear case in which x is nil *)
destruct x.
subst.
exists (a :: c :: nil).
split.
repeat apply prefix_next.
apply prefix_nil.
simpl.
rewrite H0.
inversion H4; subst; reflexivity.

exists (a :: c0 :: x).
split.
apply prefix_next.
assumption.

rewrite <- H8.

assert (H_tmp : g = g0).
  inversion H4; subst; reflexivity.
subst.

unfold ghost_updates_of.
rewrite H0.
reflexivity.

pose proof (H (g :: gus_pref)).
intros.

destruct l.
simpl in prefix0.
inversion prefix0.
assert (ghost_updates_of p (a :: c :: l) = ghost_updates_of p (c :: l)).
  unfold ghost_updates_of at 1.
rewrite H1.
reflexivity.
rewrite H2 in prefix0.

apply H0 in prefix0.
elim prefix0; intros.
elim H3; intros.
exists (a :: x).
split.
apply prefix_next.
assumption.

destruct x.
inversion H5.
assert (ghost_updates_of p (a :: c0 :: x) = ghost_updates_of p (c0 :: x)).
  unfold ghost_updates_of at 1.
  rewrite H1.
  reflexivity.
rewrite H6.
assumption.
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
      exec_never_goes_wrong eg) ->
    adheres_to pg contr.
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
    forall p contr, (exists pg, ghost_inlined contr p pg /\ adheres_to pg contr) -> adheres_to p contr.
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
      forall `(execution_of pg gexec), exec_never_goes_wrong gexec) ->
      adheres_to p contr.
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
    ~ violating_sec_state (ghost_valuation_of c) ->
    trans p c c' ->
    violating_sec_state (ghost_valuation_of c') ->
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
    forall c, initial_conf c -> ~ violating_sec_state (ghost_valuation_of c).
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
    forall `(execution_of pg exec), exec_never_goes_wrong exec.
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
assert (H_1 : ~ violating_sec_state (ghost_valuation_of c)).
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

(*::*)
inversion H9; subst;
injection H7; try rewrite H_curr_inst //=.
rewrite H_curr_inst in * |-; try discriminate.

(*--*)
inversion H9; subst;
injection H7; intros; subst;
rewrite H_curr_inst in * |-; try discriminate.

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
      adheres_to p contr.
    Proof.
      intros.
      elim H; intros annos H_po.
      unfold is_proof_outline in H_po.
      elim H_po; intros pg.
      intros [H_gi [H_annotated [H_lvpg]]].
      intros.
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

