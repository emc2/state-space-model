Require Import Coq.Setoids.Setoid.
Require Import New.Ring.
Require Import New.RingTheorems.

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

Function complex_conj_impl {A} {rops : RingOps A} (x : (A * A)) :=
  let (x_r, x_i) := x in (x_r, - x_i).

Instance ComplexOpsImpl A {rops : RingOps A} : ComplexOps (A * A) := {
  complex_conj := complex_conj_impl
}.

Lemma complex_conj_inv {A} {rops : RingOps A} {ra : Ring A} :
  forall a : (A * A), a = complex_conj_impl (complex_conj_impl a).
Proof.
  intros.
  unfold complex_conj_impl.
  elim a.
  intros.
  rewrite (neg_inv A).
  reflexivity.
Qed.

Lemma complex_conj_ext {A} {cops : ComplexOps A} {rops : RingOps A} {ra : Ring A} :
  forall a b : (A * A), a = b <-> (complex_conj_impl a) = (complex_conj_impl b).
Proof.
  intros.
  unfold complex_conj_impl.
  elim a.
  elim b.
  intros.
  unfold iff.
  split.
  intro.
  injection H.
  intros.
  f_equal.
  assumption.
  f_equal.
  assumption.
  intro.
  injection H.
  intros.
  f_equal.
  assumption.
  rewrite <- (neg_inv A).
  rewrite <- (neg_inv A) at 1.
  f_equal.
  assumption.
Qed.

Instance ComplexImpl A {cops : ComplexOps A} {rops : RingOps A} {ra : Ring A} :
  Complex (A * A) := {
  conj_inv := complex_conj_inv;
  conj_ext := complex_conj_ext
}.

Function complex_add {A} {rops : SemiRingOps A} (x y : (A * A)) :=
  let (x_r, x_i) := x in
    let (y_r, y_i) := y in
      (x_r + y_r, x_i + y_i).

Function complex_mul {A} {rops : RingOps A} (x y : (A * A)) :=
  let (x_r, x_i) := x in
    let (y_r, y_i) := y in
      ((x_r * y_r) - (x_i * y_i), (x_r * y_i) + (x_i * y_r)).

Instance ComplexSemiRingOps A {rops : RingOps A} : SemiRingOps (A * A) := {
  zero := (zero, zero);
  one := (one, zero);
  add := complex_add;
  mul := complex_mul
}.

Function complex_sub {A} {rops : RingOps A} (x y : (A * A)) :=
  let (x_r, x_i) := x in
    let (y_r, y_i) := y in (x_r - y_r, x_i - y_i).

Function complex_neg {A} {rops : RingOps A} (x : (A * A)) :=
  let (x_r, x_i) := x in (neg x_r, neg x_i).

Lemma complex_sub_def {A} {rops : RingOps A} :
  forall x y, complex_sub x y = complex_add x (complex_neg y).
Proof.
  intros.
  unfold complex_add.
  unfold complex_neg.
  unfold complex_sub.
  elim x.
  elim y.
  intros.
  f_equal.
  apply sub_def.
  apply sub_def.
Qed.

Lemma complex_sub_zero {A} {rops : RingOps A} :
  forall x, complex_sub x x = zero.
Proof.
  intro.
  unfold complex_sub.
  elim x.
  intros.
  rewrite 2! sub_zero.
  reflexivity.
Qed.

Instance ComplexRingOps A {rops : RingOps A} : RingOps (A * A) := {
  rops := ComplexSemiRingOps A;
  sub := complex_sub;
  neg := complex_neg;
  sub_def := complex_sub_def;
  sub_zero := complex_sub_zero
}.

Lemma complex_add_extensional {A} {rops : RingOps A} :
  forall x1 x2 y1 y2 : (A * A),
    x1 = x2 -> y1 = y2 -> complex_add x1 y1 = complex_add x2 y2.
Proof.
  intros.
  unfold complex_add.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Lemma complex_mul_extensional {A} {rops : RingOps A} :
  forall x1 x2 y1 y2 : (A * A),
    x1 = x2 -> y1 = y2 -> complex_mul x1 y1 = complex_mul x2 y2.
Proof.
  intros.
  unfold complex_mul.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Lemma complex_add_comm {A} {rops : RingOps A} {sring : SemiRingNoAssoc A} :
  forall a b : (A * A), complex_add a b = complex_add b a.
Proof.
  intros.
  unfold complex_add.
  elim a.
  elim b.
  intros.
  f_equal.
  apply add_comm.
  apply add_comm.
Qed.

Lemma complex_mul_comm {A} {rops : RingOps A} {sring : SemiRingNoAssoc A} :
  forall a b : (A * A), complex_mul a b = complex_mul b a.
Proof.
  intros.
  unfold complex_mul.
  elim a.
  elim b.
  intros.
  f_equal.
  rewrite 2! sub_def.
  apply add_extensional.
  apply mul_comm.
  rewrite mul_comm.
  reflexivity.
  rewrite add_comm.
  apply add_extensional.
  apply mul_comm.
  apply mul_comm.
Qed.

Lemma complex_add_mul_dist {A} {rops : RingOps A} {ring : Ring A} :
  forall a b c : (A * A),
    complex_mul a (complex_add b c) =
    complex_add (complex_mul a b) (complex_mul a c).
Proof.
  intros.
  unfold complex_mul.
  unfold complex_add.
  elim a.
  elim b.
  elim c.
  intros.
  f_equal.
  replace (a2 * a1 - b2 * b1 + (a2 * a0 - b2 * b0)) with
          (a2 * a1 + a2 * a0 - (b2 * b1 + b2 * b0)).
  rewrite 2! sub_def.
  apply add_extensional.
  rewrite add_mul_dist.
  reflexivity.
  rewrite add_mul_dist.
  reflexivity.
  rewrite 3! sub_def.
  rewrite <- 2! add_assoc.
  apply add_extensional.
  reflexivity.
  rewrite neg_add.
  rewrite 2! add_assoc.
  apply add_extensional.
  apply add_comm.
  reflexivity.
  replace (a2 * b1 + b2 * a1 + (a2 * b0 + b2 * a0)) with
          (a2 * b1 + a2 * b0 + (b2 * a1 + b2 * a0)).
  apply add_extensional.
  rewrite add_mul_dist.
  reflexivity.
  rewrite add_mul_dist.
  reflexivity.
  rewrite <- 2! add_assoc.
  apply add_extensional.
  reflexivity.
  rewrite 2! add_assoc.
  apply add_extensional.
  apply add_comm.
  reflexivity.
Qed.

Lemma complex_add_zero {A} {rops : RingOps A} {sring : SemiRingNoAssoc A} :
  forall a : (A * A), complex_add a (0, 0) = a.
Proof.
  intros.
  unfold complex_add.
  elim a.
  elim (0, 0).
  intros.
  f_equal.
  apply add_zero_right.
  apply add_zero_right.
Qed.

Lemma complex_mul_zero {A} {rops : RingOps A} {sring : SemiRingNoAssoc A} :
  forall a : (A * A), complex_mul a (0, 0) = (0, 0).
Proof.
  intros.
  unfold complex_mul.
  elim a.
  intros.
  f_equal.
  rewrite 2! mul_zero_right.
  apply sub_zero.
  rewrite 2! mul_zero_right.
  apply add_zero_right.
Qed.

Lemma complex_mul_one {A} {rops : RingOps A} {ring : RingNoAssoc A} :
  forall a : (A * A), complex_mul a (1, 0) = a.
Proof.
  intros.
  unfold complex_mul.
  elim a.
  elim (1, 0).
  intros.
  f_equal.
  rewrite mul_zero_right.
  rewrite sub_def.
  rewrite zero_self_inv.
  rewrite add_zero_right.
  apply mul_one_right.
  rewrite mul_zero_right.
  rewrite add_comm.
  rewrite add_zero_right.
  apply mul_one_right.
Qed.

Instance ComplexSemiRingNoAssoc A
  {rops : RingOps A}
  {ring : Ring A} :
  SemiRingNoAssoc (A * A) := {
  add_extensional := complex_add_extensional;
  mul_extensional := complex_mul_extensional;
  add_comm := complex_add_comm;
  mul_comm := complex_mul_comm;
  add_mul_dist := complex_add_mul_dist;
  add_zero_right := complex_add_zero;
  mul_zero_right := complex_mul_zero;
  mul_one_right := complex_mul_one
}.

Lemma complex_neg_add {A}
  {rops : RingOps A}
  {ring : RingNoAssoc A} :
    forall a b : (A * A),
      complex_neg (complex_add a b) = complex_add (complex_neg a) (complex_neg b).
Proof.
  intros.
  unfold complex_neg.
  unfold complex_add.
  elim a.
  elim b.
  intros.
  f_equal.
  apply neg_add.
  apply neg_add.
Qed.

Lemma complex_neg_mul {A}
  {rops : RingOps A}
  {ring : RingNoAssoc A} :
    forall a b : (A * A),
      complex_neg (complex_mul a b) = complex_mul a (complex_neg b).
Proof.
  intros.
  unfold complex_neg.
  unfold complex_mul.
  elim a.
  elim b.
  intros.
  f_equal.
  rewrite <- 2! neg_mul.
  apply neg_sub.
  rewrite <- 2! neg_mul.
  apply neg_add.
Qed.

Lemma complex_neg_add_inv {A} {rops : RingOps A} {ring : RingNoAssoc A} :
  forall a : (A * A), complex_add (complex_neg a) a = (0, 0).
Proof.
  intro.
  unfold complex_add.
  unfold complex_neg.
  elim a.
  intros.
  f_equal.
  rewrite add_comm.
  rewrite <- sub_def.
  apply sub_zero.
  rewrite add_comm.
  rewrite <- sub_def.
  apply sub_zero.
Qed.


Instance ComplexRingNoAssoc A
  {rops : RingOps A}
  {ring : Ring A} :
  RingNoAssoc (A * A) := {
  semiring_no_assoc_r := ComplexSemiRingNoAssoc A;
  neg_add := complex_neg_add;
  neg_mul := complex_neg_mul;
  neg_add_inv := complex_neg_add_inv
}.

Lemma complex_add_assoc {A} {rops : RingOps A} {sring : SemiRing A} :
  forall a b c : (A * A),
    complex_add a (complex_add b c) = complex_add (complex_add a b) c.
Proof.
  intros.
  unfold complex_add.
  elim a.
  elim b.
  elim c.
  intros.
  f_equal.
  apply add_assoc.
  apply add_assoc.
Qed.

Lemma complex_mul_assoc {A} {rops : RingOps A} {ring : Ring A} :
  forall a b c : (A * A),
    complex_mul a (complex_mul b c) = complex_mul (complex_mul a b) c.
Proof.
  intros.
  unfold complex_mul.
  elim a.
  elim b.
  elim c.
  intros.
  f_equal.
  rewrite add_mul_dist.
  rewrite sub_mul_dist.
  rewrite 4! mul_assoc at 1.
  rewrite 2! sub_def at 1.
  rewrite neg_add.
  rewrite add_assoc.
  rewrite add_comm.
  rewrite <- add_assoc.
  rewrite <- neg_add.
  rewrite <- add_mul_dist_right.
  rewrite add_assoc.
  rewrite <- sub_def.
  rewrite add_comm.
  rewrite <- sub_def.
  rewrite <- sub_mul_dist_right.
  reflexivity.
  rewrite add_mul_dist.
  rewrite sub_mul_dist.
  rewrite 4! mul_assoc at 1.
  rewrite sub_def at 1.
  rewrite add_assoc.
  rewrite add_comm.
  rewrite <- add_assoc.
  rewrite <- add_mul_dist_right.
  rewrite add_assoc.
  apply add_extensional.
  rewrite add_comm.
  rewrite <- sub_def.
  rewrite <- sub_mul_dist_right.
  reflexivity.
  reflexivity.
Qed.

Instance ComplexSemiRing A
  {rops : RingOps A}
  {ring : Ring A} :
  SemiRing (A * A) := {
  semiring_no_assoc_s := ComplexSemiRingNoAssoc A;
  add_assoc := complex_add_assoc;
  mul_assoc := complex_mul_assoc
}.

Instance ComplexRing A
  {rops : RingOps A}
  {ring : Ring A} :
  Ring (A * A) := {
  semiring_r := ComplexSemiRing A;
  ring_noassoc := ComplexRingNoAssoc A
}.