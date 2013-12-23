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

Class InnerProd E S
  {scops : ScalarOps S}
  {elem_sops : StateOps E S}
  {inner_prod_ops : InnerProdOp E S} := {
  scalars_ip :> Scalars S;
  states_ip :> States E S;
  conjugate_sym : forall s1 s2 : E, <| s1 | s2 |> == ~<| s2 | s1 |>;
  positive : forall s : E, 0 <= <| s | s |>;
  inner_prod_left_strict : forall s : E, <| s | null |> == 0;
  inner_prod_conj : forall s1 s2 : E, <| ~s1 | ~s2 |> == ~<| s2 | s1 |>;
  inner_prod_right_homogeneous :
    forall (s1 s2 : E) (a : S),
      <| s1 | scalar_prod a s2 |> == a * <| s1 | s2 |>
}.
