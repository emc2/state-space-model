Module Type ORDER.
  Parameter T : Type.
  Parameter leq : T -> T -> Prop.

  Definition lt (x y : T) := leq x y /\ not (x = y).
  Definition geq (x y : T) := not (lt x y).
  Definition gt (x y : T) := not (leq x y).

  Infix "<=" := leq (at level 70, no associativity).
  Infix "<" := lt (at level 70, no associativity).
  Infix ">=" := geq (at level 70, no associativity).
  Infix ">" := gt (at level 70, no associativity).

  Axiom eq_sub_order : forall x y : T, x = y -> x <= y.
  Axiom order_refl : forall x : T, x <= x.
  Axiom order_trans : forall x y z : T, x <= y -> y <= z -> x <= z.
  Axiom order_antisym : forall x y : T, x <= y -> y <= x -> x = y.
End ORDER.