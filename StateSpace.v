Require Import New.Complex.
Require Import New.Ring.
Require Import New.Field.
Require Import New.Order.
Require Import Scalars.
Require Import States.
Require Import InnerProd.

(* The master class containing everything *)
Class StateSpace Scalar State := {
  scalarops_ss :> ScalarOps Scalar;
  stateops_ss :> StateOps Scalar State;
  innerprod_ss :> InnerProd Scalar State;
  innerprodop_ss :> InnerProdOp Scalar State;
  inner_prod_ext_eq :
    forall (S1 S2 : State),
      (forall (S0 : State), <| S0 | S1 |> = <| S0 | S2 |>) -> S1 = S2
}.