Require Import New.Properties.
Require Import New.Equiv.
Require Import New.Complex.
Require Import New.Field.
Require Import Scalars.

Class StateOps E S {scalar_cops : ComplexOps S} {scalar_fops : FieldOps S} := {
  equiv :> Equiv E;
  cops :> ComplexOps E;
  null : E;
  meet : E -> E -> E;
  join : E -> E -> E;
  scalar_prod : S -> E -> E
}.

(* All properties of states will be theorems *)
Class States E S {sops : ScalarOps S}
                 {state_ops : StateOps E S} := {
  complex_st :> Complex E
}.