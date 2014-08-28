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
  innerprodop_ss :> InnerProdOp Scalar State;
  innerprod_ss :> InnerProd Scalar State;
  inner_prod_ext_ind_eq :
    forall s1 s2 : State,
      (forall s3 s4 : State,
        (<| s3 | s1 |> = <| s3 | s2 |>) ->
        (<| s4 | s1 |> = <| s4 | s2 |>) ->
        <| join s3 s4 | s1 |> = <| join s3 s4 | s2 |>) ->
      (forall s3 s4 : State,
        (<| s3 | s1 |> = <| s3 | s2 |>) ->
        (<| s4 | s1 |> = <| s4 | s2 |>) ->
        <| meet s3 s4 | s1 |> = <| meet s3 s4 | s2 |>) ->
      (forall s0 : State,
        (<| s0 | s1 |> = <| s0 | s2 |>) ->
        <| ~ s0 | s1 |> = <| ~ s0 | s2 |>) ->
      s1 = s2
}.