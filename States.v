Require Import New.Properties.
Require Import New.Equiv.
Require Import New.Complex.
Require Import New.Field.
Require Import Scalars.

Class StateOps E S {scalar_cops : ComplexOps S} {scalar_fops : FieldOps S}
                   {elem_cops : ComplexOps E} := {
  equiv :> Equiv E;
  null : E;
  meet : E -> E -> E;
  join : E -> E -> E;
  scalar_prod : S -> E -> E
}.