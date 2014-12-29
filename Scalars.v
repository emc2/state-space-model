Require Import New.Complex.
Require Import New.Field.
Require Import New.Ring.
Require Import New.Order.

(* Scalar values, assume a complex field for most general
 * construction, but don't necessarily define i.
 *)
Class ScalarOps A := {
  pord :> PartialOrder A;
  cops :> ComplexOps A;
  fops :> FieldOps A
}.

Class ScalarsNoAssoc A
  {scops : ScalarOps A} := {
  ring_scna :> Ring A;
  cprops_scna :> ComplexProps A;
  csrprops_scna :> ComplexSemiRingProps A;
  field_no_assoc_scna :> FieldNoAssoc A
}.

Class Scalars A
  {scops : ScalarOps A} := {
  ring_sc :> Ring A;
  cprops_sc :> ComplexProps A;
  csrprops_sc :> ComplexSemiRingProps A;
  field_sc :> Field A
}.
