Module Type ABELIAN_GROUP.
  Parameter T : Type.

  Parameter zero : T.
  Parameter add : T -> T -> T.
  Parameter sub : T -> T -> T.
  Parameter neg : T -> T.

  Notation "0" := zero.
  Notation "x + y" := (add x y).
  Notation "x - y" := (sub x y).
  Notation "- x" := (neg x).

  Axiom zero_add : forall x : T, x + 0 = x.
  Axiom add_comm : forall x y : T, x + y = y + x.
  Axiom add_assoc : forall x y z : T, (x + y) + z = x + (y + z).
  Axiom sub_def : forall x y : T, x - y = x + (-y).
  Axiom sub_zero : forall x : T, x - x = 0.
  Axiom neg_ext : forall x y : T, - x = - y -> x = y.
  Axiom add_ext : forall x y z : T, x + z = y + z -> x = y.
End ABELIAN_GROUP.