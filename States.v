Require Import New.Complex.
Require Import New.Field.
Require Import Scalars.
Require Import Coq.Sets.Ensembles.

(* Fundamental operations on states. *)
Class StateOps Scalar State
  {scalar_cops : ComplexOps Scalar}
  {scalar_fops : FieldOps Scalar} := {
  cops :> ComplexOps State;
  (* Null state *)
  null : State;
  meet : State -> State -> State;
  join : State -> State -> State;
  scalar_prod : Scalar -> State -> State
}.

(* All properties of states will be theorems *)
Class States Scalar State
  {sops : ScalarOps Scalar}
  {state_ops : StateOps Scalar State} := {
  complex_st :> Complex State
}.

(* Is a set of states B a basis for state S, the inductive version *)
Inductive state_basis
  {Scalar} {State}
  {sops : ScalarOps Scalar}
  {state_ops : StateOps Scalar State}
  (B : Ensemble State) :
  State -> Prop :=
  (* Everything is a basis for null *)
  | state_null : state_basis B null
  (* B is a basis for S if it contains S *)
  | state_in_basis : forall (S : State),
                       In State B S -> state_basis B S
  (* B is a basis for a join if it's a basis for the components *)
  | state_join_basis : forall (S1 S2 : State),
                         state_basis B S1 ->
                         state_basis B S2 ->
                         state_basis B (join S1 S2)
  (* B is a basis for a meet if it's a basis for the components *)
  | state_meet_basis : forall (S1 S2 : State),
                              state_basis B S1 ->
                              state_basis B S2 ->
                              state_basis B (meet S1 S2)
  (* B is a basis for a scalar product if it's a basis for the inner state *)
  | state_scalar_basis : forall (a : Scalar) (S : State),
                                state_basis B S ->
                                state_basis B (scalar_prod a S)
  (* B is a basis for a complex conjugate if it's a basis for the inner state *)
  | state_conj_basis : forall (S : State),
                              state_basis B S ->
                              state_basis B (~ S).

(* Inductive predicates on states.  Basically, predicates that behave
 * nicely in induction. *)
Definition state_pred_inductive
  {Scalar} {State}
  {sops : ScalarOps Scalar}
  {state_ops : StateOps Scalar State}
  (B : Ensemble State) (P : State -> Prop) : Prop :=
  (forall (S : State), In State B S -> P S) /\
  (forall (S1 S2 : State), P S1 -> P S2 -> P (join S1 S2)) /\
  (forall (S1 S2 : State), P S1 -> P S2 -> P (meet S1 S2)) /\
  (forall (S : State) (a : Scalar), P S -> P (scalar_prod a S)) /\
  (forall (S : State), P S -> P (~ S)) /\
  P null.

(* Helper used in proof of the induction principle over a basis. *)
Definition P_if_basis
  {Scalar} {State}
  {sops : ScalarOps Scalar}
  {state_ops : StateOps Scalar State}
  (P : State -> Prop) (B : Ensemble State) (S : State) :=
  state_basis B S -> P S.

(* Induction theorem with basis sets.  Any inductive predicate P over
 * a basis B holds for all elements of any state S such that B is a
 * basis for S.
 *)
Theorem state_basis_induction
  {Scalar} {State}
  {sops : ScalarOps Scalar}
  {state_ops : StateOps Scalar State}
  (B : Ensemble State) (P : State -> Prop) :
  state_pred_inductive B P -> (forall (S : State), state_basis B S -> P S).
Proof.
  unfold state_pred_inductive.
  intros (basis_P & join_P & meet_P & scalar_P & conj_P & null_P).
  intros.
  cut (state_basis B S).
  revert H.
  replace (state_basis B S -> P S) with (P_if_basis P B S).
  apply (state_basis_ind Scalar State sops state_ops B).
  unfold P_if_basis.
  intro.
  assumption.
  intros.
  unfold P_if_basis.
  intro.
  apply basis_P.
  assumption.
  unfold P_if_basis.
  intros.
  apply join_P.
  apply H0.
  assumption.
  apply H2.
  assumption.
  unfold P_if_basis.
  intros.
  apply meet_P.
  apply H0.
  assumption.
  apply H2.
  assumption.
  unfold P_if_basis.
  intros.
  apply scalar_P.
  apply H0.
  assumption.
  unfold P_if_basis.
  intros.
  apply conj_P.
  apply H0.
  assumption.
  unfold P_if_basis.
  reflexivity.
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
  state_pred_inductive B P -> state_set_basis B SS ->
  (forall (S : State), In State SS S -> P S).
Proof.
  intro.
  unfold state_set_basis.
  intros.
  apply H0 in H1.
  apply (state_basis_induction B).
  assumption.
  assumption.
Qed.
