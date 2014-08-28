Require Import New.Complex.
Require Import New.Field.
Require Import Scalars.

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