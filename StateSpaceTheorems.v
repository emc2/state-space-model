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

(* Inductive equality for meets and joins.  This, combined with a
 * basis equality lemma, will become the primary proof goal for showing
 * equality. *)
Definition state_meet_join_ind_eq
  {statespace : StateSpace Scalar State}
  (S1 S2 : State) : Prop :=
  (forall (S3 S4 : State),
    <| S3 | S1 |> = <| S3 | S2 |> -> <| S4 | S1 |> = <| S4 | S2 |> ->
      <| join S3 S4 | S1 |> = <| join S3 S4 | S2 |>) /\
  (forall (S3 S4 : State),
    <| S3 | S1 |> = <| S3 | S2 |> -> <| S4 | S1 |> = <| S4 | S2 |> ->
      <| meet S3 S4 | S1 |> = <| meet S3 S4 | S2 |>).

(* Helper for proving that extensional equality on inner products is
 * inductive *)
Definition state_inner_prod_eq
  {statespace : StateSpace Scalar State}
  (S1 S2 : State) (S : State) :=
   <| S | S1 |> = <| S | S2 |>.

(* If we have meet-join inductive equality, we can show that full
 * extensional equality is inductive *)
Lemma state_inner_prod_eq_ind
  {statespace : StateSpace Scalar State}
  (S1 S2 : State) :
  state_meet_join_ind_eq S1 S2 ->
  state_pred_inductive (state_inner_prod_eq S1 S2).
Proof.
  unfold state_meet_join_ind_eq.
  intros (join_ind & meet_ind).
  unfold state_pred_inductive.
  unfold state_inner_prod_eq.
  split.
  assumption.
  split.
  assumption.
  split.
  intros.
  rewrite 2! inner_prod_left_homogeneous.
  apply mul_extensional.
  reflexivity.
  assumption.
  exact innerprod_ss.
  exact innerprod_ss.
  split.
  intros.
  (* Appeal to actual definitions of complex numbers, which I haven't
   * developed here yet.  Eventually develop them, come back, and get rid
   * of this. *)
  admit.
  rewrite 2! inner_prod_left_strict.
  reflexivity.
  exact innerprod_ss.
  exact innerprod_ss.
Qed.

(* Basis equality: Are these two states equal in an inner product with
 * any basis element? *)
Definition state_basis_eq
  {statespace : StateSpace Scalar State}
  (B : Ensemble State) (S1 S2 : State) : Prop :=
  forall (S : State), In State B S -> <| S | S1 |> = <| S | S2 |>.

(* If we have a basis for the entire state space, then meet-join
 * equality and basis equality proves general equality. *)
Lemma state_meet_join_eq_induction_with_basis
  {statespace : StateSpace Scalar State}
  (B : Ensemble State) (S1 S2 : State) :
  (forall (S : State), state_basis B S) ->
  state_meet_join_ind_eq S1 S2 ->
  state_pred_forall_basis B (state_inner_prod_eq S1 S2) ->
  S1 = S2.
Proof.
  intros.
  apply inner_prod_ext_eq.
  intro.
  apply (state_inner_prod_eq_ind S1 S2) in H0.
  apply (state_basis_induction B (state_inner_prod_eq S1 S2)).
  assumption.
  assumption.
  apply H.
Qed.

(* join S1 S2 = join S2 S1 *)
Lemma state_join_comm_meet_join_eq
  {statespace : StateSpace Scalar State} :
  forall (S1 S2 : State), state_meet_join_ind_eq (join S1 S2) (join S2 S1).
Proof.
  intro.
  unfold state_meet_join_ind_eq.
  split.
  intros.
  rewrite 2! inner_prod_join_right.
  rewrite add_comm.
  reflexivity.
  intros.
  rewrite 2! inner_prod_meet_join.
  apply mul_extensional.
  rewrite add_comm.
  reflexivity.
  rewrite add_comm.
  reflexivity.
  exact innerprod_ss.
  exact innerprod_ss.
Qed.

Lemma state_meet_comm_meet_join_eq
  {statespace : StateSpace Scalar State} :
  forall (S1 S2 : State), state_meet_join_ind_eq (meet S1 S2) (meet S2 S1).
Proof.
  intro.
  unfold state_meet_join_ind_eq.
  split.
  intros.
  rewrite 2! inner_prod_right_meet.
  apply mul_comm.
  intros.
  rewrite 2! inner_prod_right_meet.
  apply mul_comm.
Qed.

(*
Lemma state_join_assoc_meet_join_eq
  {statespace : StateSpace Scalar State} :
  forall (S1 S2 S3 : State),
    state_meet_join_ind_eq (join (join S1 S2) S3) (join S1 (join S2 S3)).
Proof.
  intro.
  unfold state_meet_join_ind_eq.
  split.
  intros.
  rewrite 4! inner_prod_join_right.
  rewrite add_assoc.
  reflexivity.
  intros.
  rewrite 2! inner_prod_meet_join.

Lemma state_meet_assoc_meet_join_eq
  {statespace : StateSpace Scalar State} :
  forall (S1 S2 S3 : State),
    state_meet_join_ind_eq (meet (meet S1 S2) S3) (meet S1 (meet S2 S3)).
Proof.
  intro.
  unfold state_meet_join_ind_eq.
  split.
  intros.
*)

(* join null S = S *)
Lemma state_join_bot_meet_join_eq
  {statespace : StateSpace Scalar State} :
  forall (S : State), state_meet_join_ind_eq (join null S) S.
Proof.
  intro.
  unfold state_meet_join_ind_eq.
  split.
  intros.
  rewrite inner_prod_join_right.
  rewrite inner_prod_right_strict.
  rewrite add_comm.
  rewrite add_zero_right.
  reflexivity.
  intros.
  rewrite inner_prod_meet_join.
  rewrite 2! inner_prod_right_strict.
  rewrite add_comm.
  rewrite add_zero_right.
  rewrite add_comm.
  rewrite add_zero_right.
  rewrite inner_prod_left_meet.
  reflexivity.
  exact innerprod_ss.
  exact innerprod_ss.
Qed.

(* meet null S = null *)
Lemma state_meet_bot_meet_join_eq
  {statespace : StateSpace Scalar State} :
  forall (S : State), state_meet_join_ind_eq (meet null S) null.
Proof.
  intro.
  unfold state_meet_join_ind_eq.
  split.
  intros.
  rewrite inner_prod_join_meet.
  rewrite 3! inner_prod_right_strict.
  rewrite add_zero_right.
  rewrite mul_comm.
  rewrite mul_zero_right.
  reflexivity.
  intros.
  rewrite inner_prod_right_meet.
  rewrite inner_prod_right_strict.
  rewrite mul_comm.
  rewrite mul_zero_right.
  reflexivity.
Qed.
(*
Lemma state_join_scalar_meet_join_eq
  {statespace : StateSpace Scalar State} :
  forall (S : State) (a b : Scalar),
    state_meet_join_ind_eq (join (scalar_prod a S) (scalar_prod b S))
                           (scalar_prod (a + b) S).
Proof.
  intro.
  unfold state_meet_join_ind_eq.
  split.
  intros.
  rewrite inner_prod_join_right.
  rewrite 3! inner_prod_right_homogeneous.
  rewrite mul_comm.
  replace (b * <| join S3 S4 | S |>) with (<| join S3 S4 | S |> * b).
  rewrite <- add_mul_dist.
  apply mul_comm.
  apply mul_comm.
  intros.
  rewrite inner_prod_meet_join.
  rewrite 5! inner_prod_right_homogeneous.
*)
End StateSpaceTheorems.