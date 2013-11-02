Require Import New.Properties.
Require Import New.Equiv.

Class OrderOp A := le : A -> A -> Prop.

Infix "<=" := le (at level 70, no associativity).

Class PartialOrder A := {
  order_equiv :> Equiv A;
  order_op :> OrderOp A;
  order_refl :> Reflexive le;
  order_trans :> Transitive le;
  order_antisymm :> Antisymmetric le eq;
  eq_sub_ord : forall x y : A, x == y -> x <= y
}.

Class TotalOrder A := {
  partial_ord :> PartialOrder A;
  total_ord : forall x y : A, x <= y \/ y <= x
}.

Class PositiveSemiDefinite {A} {po : PartialOrder A} (op : A -> A) (zero : A) := {
  positive : forall a : A, zero <= op a;
  strict : op zero == zero
}.

Class PositiveDefinite {A} {po : PartialOrder A} (op : A -> A) (zero : A) := {
  pos_semidef_pd :> PositiveSemiDefinite op zero;
  zero_exclusive : forall a : A, op a == zero -> a == zero
}.

