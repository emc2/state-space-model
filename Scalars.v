Require Import New.Complex.
Require Import New.Equiv.
Require Import New.Field.
Require Import New.Ring.
Require Import New.Order.

(* Scalar values, assume a complex field for most general
 * construction, but don't necessarily define i.
 *)
Class ScalarOps A := {
  equiv :> Equiv A;
  pord :> PartialOrder A;
  cops :> ComplexOps A;
  fops :> FieldOps A
}.

Class ScalarsNoAssoc A {scops : ScalarOps A} := {
  complex_scna :> ComplexRing A;
  field_no_assoc_scna :> FieldNoAssoc A
}.

Class Scalars A {scops : ScalarOps A} := {
  complex_sc :> ComplexRing A;
  field_sc :> Field A
}.
