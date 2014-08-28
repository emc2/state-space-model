Module InnerProdTheorems.

Require Import New.Complex.
Require Import New.Ring.
Require Import Scalars.
Require Import States.
Require Import InnerProd.

(* Left homogeneity from right homogeneity and conjugate symmetry *)
Lemma inner_prod_left_homogeneous Scalar State
  {scalarops : ScalarOps Scalar}
  {stateops : StateOps Scalar State}
  {innerprodop : InnerProdOp Scalar State}
  {innerprod : InnerProd Scalar State} :
  forall (s1 s2 : State) (a : Scalar),
    <| scalar_prod a s1 | s2 |> = ((~ a) * <| s1 | s2 |>).
Proof.
  intros.
  rewrite inner_prod_conj_sym.
  rewrite inner_prod_right_homogeneous.
  rewrite conj_mul.
  rewrite mul_comm.
  rewrite <- inner_prod_conj_sym.
  reflexivity.
Qed.

(* Left strictness from right strictness and conjugate symmetry *)
Lemma inner_prod_left_strict Scalar State
  {scalarops : ScalarOps Scalar}
  {stateops : StateOps Scalar State}
  {innerprodop : InnerProdOp Scalar State}
  {innerprod : InnerProd Scalar State} :
  forall s : State, <| null | s |> = 0.
Proof.
  intro.
  rewrite inner_prod_conj_sym.
  rewrite inner_prod_right_strict.
  apply zero_self_conj.
Qed.

(* Left meet-multiply correspondance from right meet and conjugate symmetry *)
Lemma inner_prod_left_meet Scalar State
  {scalarops : ScalarOps Scalar}
  {stateops : StateOps Scalar State}
  {innerprodop : InnerProdOp Scalar State}
  {innerprod : InnerProd Scalar State} :
  forall (s s1 s2 : State), <| meet s1 s2 | s |> = <| s1 | s |> * <| s2 | s |>.
Proof.
  intros.
  rewrite inner_prod_conj_sym.
  rewrite inner_prod_right_meet.
  rewrite conj_mul.
  rewrite mul_comm.
  rewrite <- 2! inner_prod_conj_sym.
  reflexivity.
Qed.

Lemma inner_prod_meet_join Scalar State
  {scalarops : ScalarOps Scalar}
  {stateops : StateOps Scalar State}
  {innerprodop : InnerProdOp Scalar State}
  {innerprod : InnerProd Scalar State} :
  forall s1 s2 s3 s4 : State,
    <| meet s1 s2 | join s3 s4 |> =
    (<| s1 | s3 |> + <| s1 | s4 |>) * (<| s2 | s3 |> + <| s2 | s4 |>).
Proof.
  intros.
  rewrite inner_prod_conj_sym.
  rewrite inner_prod_join_meet.
  rewrite conj_mul.
  rewrite mul_comm.
  rewrite 2! conj_sum.
  rewrite <- 4! inner_prod_conj_sym.
  reflexivity.
Qed.

Lemma inner_prod_join_left Scalar State
  {scalarops : ScalarOps Scalar}
  {stateops : StateOps Scalar State}
  {innerprodop : InnerProdOp Scalar State}
  {innerprod : InnerProd Scalar State} :
    forall s1 s2 s3 s4 : State,
      <| join s1 s2 | join s3 s4 |> = <| s1 | join s3 s4 |> + <| s2 | join s3 s4 |>.
Proof.
  intros.
  rewrite inner_prod_conj_sym.
  rewrite inner_prod_join_right.
  rewrite conj_sum.
  rewrite <- 2! inner_prod_conj_sym.
  reflexivity.
Qed.

End InnerProdTheorems.