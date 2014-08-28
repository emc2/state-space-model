Require Import New.Complex.
Require Import New.Ring.
Require Import New.Field.
Require Import New.Order.
Require Import Scalars.
Require Import States.

Class InnerProdOp Scalar Elem := {
  inner_prod : Elem -> Elem -> Scalar
}.

Notation "<| x | y |>" := (inner_prod x y).

(* Basic properties of inner products.  Note: this axiomatization is
 * slightly more fine-grained than those found in traditional textbooks,
 * as is necessary for mechanical proving.
 *)
Class InnerProd Scalar Elem
  {scops : ScalarOps Scalar}
  {elem_sops : StateOps Scalar Elem}
  {inner_prod_ops : InnerProdOp Scalar Elem} := {
  scalars_ip :> ScalarsNoAssoc Scalar;
  states_ip :> States Scalar Elem;

  (* Conjugate Symmetry of inner products *)
  inner_prod_conj_sym : forall s1 s2 : Elem, <| s1 | s2 |> = ~<| s2 | s1 |>;

  (* Positivity of inner products *)
  inner_prod_pos : forall s : Elem, 0 <= <| s | s |>;

  (* Strictness of inner products (inner product with null is 0).
   * Left-side strictness is provable as a theorem
   *)
  inner_prod_right_strict : forall s : Elem, <| s | null |> = 0;

  (* Conjugate distribution of inner products *)
  inner_prod_conj_dist : forall s1 s2 : Elem, <| ~s1 | ~s2 |> = ~<| s2 | s1 |>;

  (* Homogeneity of inner products *)
  inner_prod_right_homogeneous :
    forall (s1 s2 : Elem) (a : Scalar),
      <| s1 | scalar_prod a s2 |> = a * <| s1 | s2 |>;

  (* Right meet-multiply correspondance *)
  inner_prod_right_meet :
    forall s s1 s2 : Elem, <| s | meet s1 s2 |> = <| s | s1 |> * <| s | s2 |>;

  (* Join-join property *)
  inner_prod_join :
    forall s1 s2 s3 s4 : Elem,
      <| join s1 s2 | join s3 s4 |> =
      <| s1 | s3 |> + <| s1 | s4 |> + <| s2 | s3 |> + <| s2 | s4 |>;

  (* One-sided Join-join property *)
  inner_prod_join_right :
    forall s1 s2 s3 s4 : Elem,
      <| join s1 s2 | join s3 s4 |> = <| join s1 s2 | s3 |> + <| join s1 s2 | s4 |>;

  (* Join-meet property *)
  inner_prod_join_meet :
    forall s1 s2 s3 s4 : Elem,
      <| join s1 s2 | meet s3 s4 |> =
      (<| s1 | s3 |> + <| s2 | s3 |>) * (<| s1 | s4 |> + <| s2 | s4 |>)
}.
