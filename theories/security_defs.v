From Coq Require Import List.
From PCC Require Import java_basic_defs program_model expressions_assertions.
From PCC Require Import ssrexport.

Section SecurityDefs.
  
Open Scope type_scope.

Inductive event :=
| bef_event (_: classid) (_: methid) (arg: value)
| aft_event (_: classid) (_: methid) (ret: value)
| exc_event (_: classid) (_: methid).

Definition event_trace := list event.

(* 
   The following definition is not distributive under ++ operations.
   That is, trace_of (exec1 ++ exec2) <> (trace_of exec1) ++ (trace_of exec2) 
*)
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
  | c :: e' => 
    match observed_event p c with
    | Some evt => evt :: event_trace_of p e'
    | None => event_trace_of p e'
    end
  end.

Lemma event_trace_distr : forall p l l', 
  event_trace_of p (l ++ l') = event_trace_of p l ++ event_trace_of p l'.
Proof.
move => p.
elim => [|a l IH l']; first by [].
rewrite -app_comm_cons /=.
by case (observed_event p a); rewrite IH.
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


(* 
   For simplicity: The ghost state is represented by a single fixed ghost variable 'gs'.
   We still have a notion of ghost valuations to be able to handle local ghost variables
   used for storing arguments and return values. 
*)
Variable gs : ghostid.

Definition violating_sec_state (gv: ghost_valuation) := gv gs = ghost_errval.

Definition accepted_by contr (event_tr: event_trace) :=
  forall gus sec_tr, 
    ss_updates_of contr event_tr gus ->
    is_sec_state_trace gus sec_tr ->
    hd initial_gv sec_tr = initial_gv ->
    (forall ss, In ss sec_tr -> ~ violating_sec_state ss).

Definition adheres_to p contr : Prop :=
  forall e, execution_of p e -> accepted_by contr (event_trace_of p e).

(*
   The original definition of "Ghost Instruction Goes Wrong" is, 
   "no guards of the ghost instruction hold".
   If all inserted ghost instructions has the shape
   
   x := g_1 -> v_1 | g_2 -> v_2 | ... | g_n -> v_n | ghost_errval
   
   the notion of going wrong is equivalent to "no ghost var equals ghost_errval".
   This is the reason why initial_gv has all vars initialized to 0 instead of ghost_errval.
*)

Definition exec_never_goes_wrong (e: execution) :=
  forall c, In c e -> ~ violating_sec_state (ghost_valuation_of c).

Section GhostInliner.
  
(* Note that assertions are irrelevant in this section. *)
  
Variable contr : contract.

(* 
   My initial attempt encoded the ghost_inliner as a function. That approach
   ran into the following problem:
   
   If a ghost instruction is to be inserted, it needs a label. Since method
   bodies are total mappings from lables to instructions, it is impossible
   to dig out a fresh label.
   
   The obvious fix would be to let method bodies be partial ("option")
   mappings. Unfortunately the option-type spreads like a plague in the defs
   and all proofs needs splitting on Some/None.
   
   This is why it is currently encoded as a proposition over programs. 
*)
  
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

End GhostInliner.

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

End SecurityDefs.
