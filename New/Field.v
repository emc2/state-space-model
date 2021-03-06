Require Import New.Ring.

Class FieldOps A := {
  rops :> RingOps A;
  div : A -> A -> A;
  recip : A -> A
}.

Notation "x / y" := (div x y).
Notation "/ x" := (recip x).

Class FieldAxioms A
  {fops : FieldOps A} := {
  div_def : forall x y, div x y = mul x (recip y);
  recip_mul_inv : forall a : A, (/ a) * a = 1
}.

Class FieldNoAssoc A
  {fops : FieldOps A} := {
  ring_no_assoc_fna :> RingNoAssoc A;
  axioms_fna :> FieldAxioms A
}.

Class Field A
  {fops : FieldOps A} := {
  ring_f :> Ring A;
  axioms_f :> FieldAxioms A
}.
