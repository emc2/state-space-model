Class EquivOp A := eq : A -> A -> Prop.

Infix "==" := eq (at level 70, no associativity).

Class Equiv A := {
  equiv_op :> EquivOp A;
  equiv_refl :> forall a : A, a == a;
  equiv_sym :> forall a b : A, a == b -> b == a;
  equiv_trans :> forall a b c : A, a == b -> b == c -> a == c
}.

(*
Ltac rewrite_eqn P :=
  match goal with
    | |- ?A ==
*)

Ltac solve_equation :=
  match goal with
    | x : ?A == ?B |- ?A == ?B => apply x
    | |- ?A == ?A => apply equiv_refl
  end.