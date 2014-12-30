Require Import New.Complex.
Require Import New.Ring.
Require Import New.Field.
Require Import New.Order.
Require Import Scalars.
Require Import States.

Class NormOp Scalar Elem := {
  norm : Elem -> Scalar
}.

Class SemiNorm Scalar Elem
  {scops : ScalarOps Scalar}
  {elem_sops : StateOps Scalar Elem}
  {norm_ops : NormOp Scalar Elem} := {
  norm_positive : forall s : Elem, 0 <= norm s;
  norm_zero : norm null = 0;
  norm_homogeneous :
    forall (s : Elem) (a : Scalar), norm (scalar_prod a s) = a * (norm s);
  norm_triangle_ineq :
    forall (s1 s2 : Elem), norm (join s1 s2) <= (norm s1) + (norm s2);
  norm_volume_ineq :
    forall (s1 s2 : Elem), norm (meet s1 s2) <= (norm s1) * (norm s2)
}.

Class Norm Scalar Elem
  {scops : ScalarOps Scalar}
  {elem_sops : StateOps Scalar Elem}
  {norm_ops : NormOp Scalar Elem} := {
  seminorm_n :> SemiNorm Scalar Elem;
  norm_definite : forall s : Elem, ((norm s) = 0) -> (s = null)
}.