Module StateSpaceTheorems.

Require Import Setoid.
Require Import New.Complex.
Require Import New.Equiv.
Require Import New.Ring.
Require Import New.RingTheorems.
Require Import New.Field.
Require Import InnerProd.
Require Import Scalars.
Require Import States.
Require Import StateSpace.


Lemma state_join_bot Scalar State
  {statespace : StateSpace Scalar State} :
  forall (s : State), join null s = s.
Proof.
  intros.
  apply inner_prod_ext_ind_eq.
  intros.
  rewrite inner_prod_join.
  rewrite 2! inner_prod_right_strict.
  rewrite add_zero_right.
  rewrite add_zero_left.
  rewrite <- inner_prod_join.
  rewrite add_comm at 1.
  intro.
Qed.

End StateSpaceTheorems.