Require Import New.Equiv.
Require Import New.Complex.
Require Import New.Ring.
Require Import New.Field.
Require Import New.Order.
Require Import Scalars.
Require Import States.
Require Import InnerProd.

(* The master class containing everything *)
Class StateSpace E S := {
  scalarops_ss :> ScalarOps S;
  stateops_ss :> StateOps E S;
  innerprodop_ss :> InnerProdOp E S;
  innerprod_ss :> InnerProd E S;
  inner_prod_extensional_eq :
    forall s1 s2 : E, s1 == s2 <-> (forall s : E, <| s | s1 |> == <| s | s2 |>)
}.