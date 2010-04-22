
Require Export java_basic_defs.

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



