Require Import New.Complex.
Require Import New.Equiv.
Require Import New.Field.
Require Import New.Ring.

(* Scalar values, assume a complex field for most general
 * construction, but don't necessarily define i.
 *)

Class ScalarsNoAssoc A {cops : ComplexOps A} {fops : FieldOps A} := {
  complex_scna :> Complex A;
  field_no_assoc_scna : FieldNoAssoc A
}.

Class Scalars A {cops : ComplexOps A} {fops : FieldOps A} := {
  complex_sc :> Complex A;
  field_sc : Field A
}.
