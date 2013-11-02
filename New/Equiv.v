Require Import New.Properties.

Class EquivOp A := eq : A -> A -> Prop.

Class Equiv A := {
  equiv_op :> EquivOp A;
  equiv_refl :> Reflexive eq;
  equiv_comm :> Symmetric eq;
  equiv_trans :> Transitive eq
}.

Infix "==" := equiv_op (at level 70, no associativity).
