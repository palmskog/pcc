
Require Export program_model.
Require Export Bool.

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
