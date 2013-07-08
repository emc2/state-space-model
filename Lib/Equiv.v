Module Type EQUIV.
  Parameter T : Type.
  Parameter equiv : T -> T -> Prop.

  Infix "==" := eq (at level 70, no associativity).

  Axiom equiv_refl : forall x : T, x == x.
  Axiom equiv_comm : forall x y : T, x == y -> y == x.
  Axiom equiv_trans : forall x y z : T, x == y -> y == z -> x == z.
End EQUIV.