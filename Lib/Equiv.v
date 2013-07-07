Require Import Lib.Base.

Class EquivOp A := eq : A -> A -> Prop.

Class Equiv A := {
  equiv_op :> EquivOp A;
  equiv_refl :> Reflexive eq;
  equiv_comm :> Commutative eq;
  equiv_trans :> Transitive eq
}.

Infix "==" := eq (at level 70, no associativity).
