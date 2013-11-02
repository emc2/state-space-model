Require Import New.Properties.
Require Import New.Equiv.
Require Import New.Ring.

Class ComplexOps A := {
  complex_conj : A -> A
}.

Notation "~ x" := (complex_conj x).

Class Complex A {cops : ComplexOps A} {rops : RingOps A} := {
  conj_inv :> Involution complex_conj equiv_op;
  conj_sum : forall a b : A, ~(a + b) == (~a) + (~b);
  conj_mul : forall a b : A, ~(a * b) = (~b) * (~a)
}.