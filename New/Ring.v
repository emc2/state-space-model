Require Import New.Properties.
Require Import New.Equiv.

Class SemiRingOps A := {
  zero : A;
  one : A;
  add : A -> A -> A;
  mul : A -> A -> A
}.

Class RingOps A {equiv : Equiv A} := {
  rops :> SemiRingOps A;
  sub : A -> A -> A;
  neg : A -> A;
  sub_def : forall x y, sub x y == add x (neg y);
  sub_zero : forall x, sub x x == zero
}.

Notation "0" := zero.
Notation "1" := one.
Notation "x + y" := (add x y).
Notation "x - y" := (sub x y).
Notation "x * y" := (mul x y).
Notation "- x" := (neg x).

Class SemiRingNoAssoc A {equiv : Equiv A} {rops : SemiRingOps A} := {
  add_extensional :
    forall x1 x2 y1 y2 : A, x1 == x2 -> y1 == y2 -> x1 + y1 == x2 + y2;
  mul_extensional :
    forall x1 x2 y1 y2 : A, x1 == x2 -> y1 == y2 -> x1 * y1 == x2 * y2;
  add_comm : forall a b : A, a + b == b + a;
  mul_comm : forall a b : A, a * b == b * a;
  add_mul_dist : forall a b c : A, a * (b + c) == (a * b) + (a * c);
  add_zero : forall a : A, a + 0 == a;
  mul_zero : forall a : A, a * 0 == 0;
  mul_one : forall a : A, a * 1 == a
}.

Class RingNoAssoc A {equiv : Equiv A} {rops : RingOps A} := {
  semiring_no_assoc_r :> SemiRingNoAssoc A;
  neg_add_inv : forall a : A, (- a) + a == 0
}.

Class SemiRing A {equiv : Equiv A} {rops : SemiRingOps A} := {
  semiring_no_assoc_s :> SemiRingNoAssoc A;
  add_assoc : Associative add equiv_op;
  mul_assoc : Associative add equiv_op
}.

Class Ring A {equiv : Equiv A} {rops : RingOps A} := {
  semiring_r :> SemiRing A;
  ring_noassoc :> RingNoAssoc A
}.