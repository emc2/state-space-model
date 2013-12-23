Module InnerProdTheorems.

Require Import New.Properties.
Require Import New.Equiv.
Require Import New.Complex.
Require Import New.Ring.
Require Import Scalars.
Require Import States.
Require Import InnerProd.

Theorem inner_prod_left_homogeneous Scalar State
  {scalarops : ScalarOps Scalar}
  {stateops : StateOps State Scalar}
  {innerprodop : InnerProdOp State Scalar}
  {innerprod : InnerProd State Scalar} :
  forall (s1 s2 : State) (a : Scalar),
    <| scalar_prod a s1 | s2 |> == ((~ a) * <| s1 | s2 |>).
Proof.
  intros.
  apply equiv_trans with (~<| s2 | scalar_prod a s1 |>).
  apply conjugate_sym.
  apply equiv_trans with (~ (a * <| s2 | s1 |>)).
  cut (<| s2 | scalar_prod a s1 |> == a * <| s2 | s1 |>).
  apply conj_ext.
  apply inner_prod_right_homogeneous.  
  apply equiv_trans with ((~a) * (~<| s2 | s1 |>)).
  generalize (<| s2 | s1 |>).
  intro s.
  apply equiv_trans with ((~s) * (~a)).
  apply conj_mul.
  apply mul_comm.
  apply mul_extensional.
  apply equiv_refl.
  apply equiv_sym.
  apply conjugate_sym.
Qed.

End InnerProdTheorems.