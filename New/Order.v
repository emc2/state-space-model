Require Import New.Equiv.

Class OrderOp A := le : A -> A -> Prop.

Infix "<=" := le (at level 70, no associativity).

Class PartialOrder A
  {equiv : Equiv A} := {
  order_op :> OrderOp A;
  order_refl :> forall a : A, a <= a;
  order_trans :> forall a b c : A, a <= b -> b <= c -> a <= c;
  order_antisymm :> forall a b : A, a <= b -> b <= a -> a == b;
  eq_sub_ord : forall x y : A, x == y -> x <= y
}.

Class TotalOrder A
  {equiv : Equiv A} := {
  partial_ord :> PartialOrder A;
  total_ord : forall x y : A, x <= y \/ y <= x
}.
