Require Import New.Complex.
Require Import New.Field.
Require Import Scalars.
Require Import States.
Require Import Coq.Sets.Ensembles.

(* Induction theorem with basis sets.  Any inductive predicate P over
 * a basis B holds for all elements of any state S such that B is a
 * basis for S.
 *)
Theorem state_basis_induction
  {Scalar} {State}
  {sops : ScalarOps Scalar}
  {state_ops : StateOps Scalar State}
  (B : Ensemble State) (P : State -> Prop) :
  state_pred_inductive P -> state_pred_forall_basis B P ->
  (forall (S : State), state_basis B S -> P S).
Proof.
  unfold state_pred_inductive.
  intros (join_P & meet_P & scalar_P & conj_P & null_P).
  unfold state_pred_forall_basis.
  intro basis_P.
  intros.
  apply (state_basis_ind Scalar State sops state_ops B).
  assumption.
  intros.
  apply basis_P.
  assumption.
  intros.
  apply join_P.
  assumption.
  assumption.
  intros.
  apply meet_P.
  assumption.
  assumption.
  intros.
  apply scalar_P.
  assumption.
  intros.
  apply conj_P.
  assumption.
  assumption.
Qed.

(* Is B a basis for all states in set SS? *)
Definition state_set_basis
  {Scalar} {State}
  {sops : ScalarOps Scalar}
  {state_ops : StateOps Scalar State}
  (B : Ensemble State) (SS : Ensemble State) :=
  forall (S : State), In State SS S -> state_basis B S.

(* A version of the basis induction theorem for sets of states. *)
Lemma state_set_basis_induction
  {Scalar} {State}
  {sops : ScalarOps Scalar}
  {state_ops : StateOps Scalar State}
  (B : Ensemble State) (SS : Ensemble State) (P : State -> Prop) :
  state_pred_inductive P -> state_pred_forall_basis B P ->
  state_set_basis B SS -> (forall (S : State), In State SS S -> P S).
Proof.
  unfold state_set_basis.
  intros.
  apply H1 in H2.
  apply (state_basis_induction B).
  assumption.
  assumption.
  assumption.
Qed.
