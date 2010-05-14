Require Export ZArith.
Require Export List.

Section JavaBasicDefs.
  
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
  
End JavaBasicDefs.

Notation "s '[[' n ']]'" := (nth n s undefval) (at level 90).


