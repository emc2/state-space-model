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
  (P : State -> Prop) : Prop :=
  (forall (S1 S2 : State), P S1 -> P S2 -> P (join S1 S2)) /\
  (forall (S1 S2 : State), P S1 -> P S2 -> P (meet S1 S2)) /\
  (forall (S : State) (a : Scalar), P S -> P (scalar_prod a S)) /\
  (forall (S : State), P S -> P (~ S)) /\
  P null.

Definition state_pred_forall_basis
  {Scalar} {State}
  {sops : ScalarOps Scalar}
  {state_ops : StateOps Scalar State}
  (B : Ensemble State) (P : State -> Prop) : Prop :=
  forall (S : State), In State B S -> P S.
