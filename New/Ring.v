Require Import New.Properties.
Require Import New.Equiv.

Class SemiRingOps A := {
  equiv :> Equiv A;
  zero : A;
  one : A;
  add : A -> A -> A;
  sub : A -> A -> A;
  mul : A -> A -> A;
  neg : A -> A
}.

Notation "0" := zero.
Notation "1" := one.
Notation "x + y" := (add x y).
Notation "x - y" := (sub x y).
Notation "x * y" := (mul x y).
Notation "- x" := (neg x).
Infix "==" := equiv_op (at level 70, no associativity).

Class RingOps A := {
  rops :> SemiRingOps A;
  sub_def : forall x y, x - y == x + (-y);
  sub_zero : forall x, x - x == 0
}.

Class SemiRingNoAssoc A {rops : SemiRingOps A} := {
  add_extensional :
    forall x1 x2 y1 y2: A, x1 == x2 -> y1 == y2 -> x1 + y1 == x2 + y2;
  mul_extensional :
    forall x1 x2 y1 y2: A, x1 == x2 -> y1 == y2 -> x1 * y1 == x2 * y2;
  add_comm : Commutative add equiv_op;
  mul_comm : Commutative add equiv_op;
  add_mul_dist : Distributive add mul equiv_op
}.

Class RingNoAssoc A {rops : RingOps A} := {
  semiring_no_assoc_r :> SemiRingNoAssoc A
}.

Class SemiRing A {rops : SemiRingOps A} := {
  semiring_no_assoc_s :> SemiRingNoAssoc A;
  add_assoc : Associative add equiv_op;
  mul_assoc : Associative add equiv_op
}.

Class Ring A {rops : RingOps A} := {
  semiring :> SemiRing A;
  ring_noassoc :> RingNoAssoc A
}.