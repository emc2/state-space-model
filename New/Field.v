Require Import New.Properties.
Require Import New.Equiv.
Require Import New.Ring.

Class FieldOps A := {
  rops :> RingOps A;
  div : A -> A -> A;
  recip : A -> A
}.

Class FieldAxioms A {fops : FieldOps A} := {
  div_def : forall x y, div x y == mul x (recip y)
}.

Notation "x / y" := (div x y).
Notation "/ x" := (recip x).

Class FieldNoAssoc A {fops : FieldOps A} := {
  ring_no_assoc_fna :> RingNoAssoc A;
  axioms_fna :> FieldAxioms A
}.

Class Field A {fops : FieldOps A} := {
  ring_f :> Ring A;
  axioms_f :> FieldAxioms A
}.
