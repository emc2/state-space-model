Module InnerProdTheorems.

Require Import New.Equiv.
Require Import New.Complex.
Require Import New.Ring.
Require Import Scalars.
Require Import States.
Require Import InnerProd.

(* Left homogeneity from right homogeneity and conjugate symmetry *)
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
  apply inner_prod_conj_sym.
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
  apply inner_prod_conj_sym.
Qed.

(* Left strictness from right strictness and conjugate symmetry *)
Theorem inner_prod_left_strict Scalar State
  {scalarops : ScalarOps Scalar}
  {stateops : StateOps State Scalar}
  {innerprodop : InnerProdOp State Scalar}
  {innerprod : InnerProd State Scalar} :
  forall s : State, <| null | s |> == 0.
Proof.
  intro.
  apply equiv_trans with (<| s | null |>).
  apply equiv_trans with (~<| s | null |>).
  apply inner_prod_conj_sym.
  apply equiv_sym.
  apply equiv_trans with 0.
  apply inner_prod_right_strict.
  apply equiv_trans with (~0).
  apply equiv_sym.
  apply zero_self_conj.
  apply equiv_sym.
  cut (<| s | null |> == 0).
  apply conj_ext.
  apply inner_prod_right_strict.
  apply inner_prod_right_strict.
Qed.

(* Left meet-multiply correspondance from right meet and conjugate symmetry *)
Theorem inner_prod_left_meet Scalar State
  {scalarops : ScalarOps Scalar}
  {stateops : StateOps State Scalar}
  {innerprodop : InnerProdOp State Scalar}
  {innerprod : InnerProd State Scalar} :
  forall (s s1 s2 : State), <| meet s1 s2 | s |> == <| s1 | s |> * <| s2 | s |>.
Proof.
  intros.
  apply equiv_trans with (~ <| s | meet s1 s2 |>).
  apply inner_prod_conj_sym.
  apply equiv_trans with (~(<| s | s1 |> * <| s | s2 |>)).
  cut (<| s | meet s1 s2 |> == <| s | s1 |> * <| s | s2 |>).
  apply conj_ext.
  apply inner_prod_right_meet.
  apply equiv_trans with ((~<| s | s2 |>) * (~<| s | s1 |>)).
  apply conj_mul.
  apply equiv_sym.
  apply equiv_trans with ((~<| s | s1 |>) * (~<| s | s2 |>)).
  apply mul_extensional.
  apply inner_prod_conj_sym.
  apply inner_prod_conj_sym.
  apply mul_comm.
Qed.

Theorem inner_prod_meet_join Scalar State
  {scalarops : ScalarOps Scalar}
  {stateops : StateOps State Scalar}
  {innerprodop : InnerProdOp State Scalar}
  {innerprod : InnerProd State Scalar} :
  forall s1 s2 s3 s4 : State,
    <| meet s1 s2 | join s3 s4 |> ==
    (<| s1 | s3 |> + <| s1 | s4 |>) * (<| s2 | s3 |> + <| s2 | s4 |>).
Proof.
  intros.
  apply equiv_trans with (~<| join s3 s4 | meet s1 s2 |>).
  apply inner_prod_conj_sym.
  apply equiv_trans with (~((<| s3 | s1 |> + <| s4 | s1 |>) *
                           (<|s3 | s2 |> + <| s4 | s2 |>))).
  apply conj_ext.
  apply equiv_trans with (<| join s3 s4 | meet s1 s2 |>).
  apply equiv_sym.
  apply conj_inv.
  apply equiv_trans with ((<| s3 | s1 |> + <| s4 | s1 |>) *
                          (<| s3 | s2 |> + <| s4 | s2 |>)).
  apply inner_prod_join_meet.
  apply conj_inv.
  apply equiv_trans with ((~(<| s3 | s2 |> + <| s4 | s2 |>)) *
                          (~(<| s3 | s1 |> + <| s4 | s1 |>))).
  apply conj_mul.
  apply equiv_trans with ((~ <| s3 | s1 |> + <| s4 | s1 |>) *
                          (~ <| s3 | s2 |> + <| s4 | s2 |>)).
  apply mul_comm.
  apply equiv_trans with (((~ <| s3 | s1 |>) + (~ <| s4 | s1 |>)) *
                          (~(<| s3 | s2 |> + <| s4 | s2 |>))).
  apply mul_extensional.
  apply conj_sum.
  apply equiv_refl.
  apply equiv_trans with (((~ <| s3 | s1 |>) + (~ <| s4 | s1 |>)) *
                          ((~ <| s3 | s2 |>) + (~ <| s4 | s2 |>))).
  apply mul_extensional.
  apply equiv_refl.
  apply conj_sum.
  apply equiv_trans with ((<| s1 | s3 |> + (~ <| s4 | s1 |>)) *
                          ((~ <| s3 | s2 |>) + (~ <| s4 | s2 |>))).
  apply mul_extensional.
  apply add_extensional.
  apply equiv_sym.
  apply inner_prod_conj_sym.
  apply equiv_refl.
  apply equiv_refl.
  apply equiv_trans with ((<| s1 | s3 |> + <| s1 | s4 |>) *
                          ((~ <| s3 | s2 |>) + (~ <| s4 | s2 |>))).
  apply mul_extensional.
  apply add_extensional.
  apply equiv_refl.
  apply equiv_sym.
  apply inner_prod_conj_sym.
  apply equiv_refl.
  apply equiv_trans with ((<| s1 | s3 |> + <| s1 | s4 |>) *
                          (<| s2 | s3 |> + (~ <| s4 | s2 |>))).
  apply mul_extensional.
  apply equiv_refl.
  apply add_extensional.
  apply equiv_sym.
  apply inner_prod_conj_sym.
  apply equiv_refl.
  apply equiv_trans with ((<| s1 | s3 |> + <| s1 | s4 |>) *
                          (<| s2 | s3 |> + <| s2 | s4 |>)).
  apply mul_extensional.
  apply equiv_refl.
  apply add_extensional.
  apply equiv_refl.
  apply equiv_sym.
  apply inner_prod_conj_sym.
  apply equiv_refl.
Qed.

End InnerProdTheorems.