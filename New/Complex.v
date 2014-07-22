Require Import New.Ring.

Class ComplexOps A := {
  complex_conj : A -> A
}.

(* Unorthodox notation *)
Notation "~ x" := (complex_conj x).

Class Complex A
  {cops : ComplexOps A} := {
  conj_inv : forall a : A, a = ~ (~ a);
  conj_ext : forall a b : A, a = b <-> (~a) = (~b)
}.

Class ComplexRing A
  {cops : ComplexOps A}
  {rops : RingOps A} := {
  complex_cr :> Complex A;
  zero_self_conj : (~ 0) = 0;
  conj_sum : forall a b : A, (~(a + b)) = (~a) + (~b);
  conj_mul : forall a b : A, (~(a * b)) = (~b) * (~a)
}.