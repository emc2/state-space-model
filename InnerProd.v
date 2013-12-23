Require Import New.Properties.
Require Import New.Equiv.
Require Import New.Complex.
Require Import New.Ring.
Require Import New.Field.
Require Import New.Order.
Require Import Scalars.
Require Import States.

Class InnerProdOp E S := {
  inner_prod : E -> E -> S
}.

Notation "<| x | y |>" := (inner_prod x y).

Class InnerProd E S {scalar_cops : ComplexOps S} {scalar_fops : FieldOps S}
                    {elem_sops : StateOps E S}
                    {inner_prod_ops : InnerProdOp E S} := {
  ipop :> InnerProdOp E S;
  scalars_ip :> Scalars S;
  states_ip :> States E S;
  conjugate_sym : forall s1 s2 : E, <| s1 | s2 |> == ~<| s2 | s1 |>;
  positive : forall s : E, 0 <= <| s | s |>;
  strict : <| null | null |> == 0
}.