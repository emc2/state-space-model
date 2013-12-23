Require Import New.Properties.
Require Import New.Equiv.
Require Import New.Ring.

Class ComplexOps A := {
  complex_conj : A -> A
}.

(* Unorthodox notation *)
Notation "~ x" := (complex_conj x).

Class Complex A {cops : ComplexOps A} := {
  equiv_c :> Equiv A;
  conj_inv :> Involution complex_conj equiv_op
}.

Class ComplexRing A {cops : ComplexOps A} {rops : RingOps A} := {
  complex_cr :> Complex A;
  conj_sum_cr : forall a b : A, ~(a + b) == (~a) + (~b);
  conj_mul : forall a b : A, ~(a * b) = (~b) * (~a)
}.