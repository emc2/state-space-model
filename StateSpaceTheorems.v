Module StateSpaceTheorems.

Require Import Setoid.
Require Import New.Complex.
Require Import New.Equiv.
Require Import New.Ring.
Require Import New.RingTheorems.
Require Import New.Field.
Require Import InnerProd.
Require Import InnerProdTheorems.
Require Import Scalars.
Require Import States.
Require Import StateTheorems.
Require Import StateSpace.
Require Import Coq.Sets.Ensembles.

Variable Scalar : Type.
Variable State : Type.

Definition equal_inner_prod_forall
 {statespace : StateSpace Scalar State}
 (S1 S2 : State) (S0 : State) := <| S0 | S1 |> = <| S0 | S2 |>.

Definition state_join_bot
  {statespace : StateSpace Scalar State}
  (s : State) := join null s = s.

Lemma state_join_bot_inductive
  {statespace : StateSpace Scalar State} :
  state_pred_inductive state_join_bot.
Proof.
  unfold state_pred_inductive.
  unfold state_join_bot.
  split.
  intros.
  apply inner_prod_ext_eq.
  intros.
  rewrite inner_prod_left_join.
  apply inner_prod_ext_eq.
  intros.
  rewrite inner_prod_join_right.
  rewrite inner_prod_right_strict.
  rewrite add_zero_left.
  reflexivity.
Qed.

End StateSpaceTheorems.