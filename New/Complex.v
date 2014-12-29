Require Import Coq.Setoids.Setoid.
Require Import New.Ring.
Require Import New.RingTheorems.
Require Import New.Field.

(* Basic complex operations *)
Class ComplexOps A := {
  complex_conj : A -> A
}.

(* Unorthodox notation *)
Notation "~ x" := (complex_conj x).

Class ComplexProps A {cops : ComplexOps A} := {
  complex_conj_inv : forall (x : A), (~ (~ x)) = x;
  complex_conj_ext : forall a b : A, a = b <-> (~ a) = (~ b)
}.

Class ComplexSemiRingProps A {cops : ComplexOps A} {srops : SemiRingOps A} := {
  conj_sum : forall a b : A, (~ (a + b)) = (~ a) + (~ b);
  conj_mul : forall a b : A, (~ (a * b)) = (~ b) * (~ a);
  zero_self_conj : (~ 0) = 0
}.


(* Type which builds complex numbers out of an underlying type *)
Record Complex A := {
  real_part : A;
  imaginary_part : A
}.

Function complex_conj_impl {A} {rops : RingOps A} (x : Complex A) :=
  {| real_part := real_part A x; imaginary_part := - imaginary_part A x |}.

Instance ComplexImplOps A {rops : RingOps A} {ra : Ring A} :
  ComplexOps (Complex A) := {
  complex_conj := complex_conj_impl
}.

Lemma complex_conj_impl_inv {A} {rops : RingOps A} {ra : Ring A} :
  forall a : Complex A, complex_conj_impl (complex_conj_impl a) = a.
Proof.
  intros.
  unfold complex_conj_impl.
  elim a.
  intros.
  f_equal.
  unfold imaginary_part.
  rewrite neg_inv.
  reflexivity.
Qed.

Lemma complex_conj_impl_ext {A} {rops : RingOps A} {ra : Ring A} :
  forall a b : Complex A, a = b <-> (complex_conj_impl a) = (complex_conj_impl b).
Proof.
  intros.
  unfold complex_conj_impl.
  elim a.
  elim b.
  unfold real_part.
  unfold imaginary_part.
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
  rewrite <- neg_inv.
  rewrite <- neg_inv at 1.
  f_equal.
  assumption.
Qed.

Instance ComplexImplProps A {rops : RingOps A} {ra : Ring A} :
  ComplexProps (Complex A) := {
  complex_conj_inv := complex_conj_impl_inv;
  complex_conj_ext := complex_conj_impl_ext
}.

Definition complex_zero {A} {rops : RingOps A} : Complex A :=
  {| real_part := 0; imaginary_part := 0 |}.

Definition complex_one {A} {rops : RingOps A} : Complex A :=
  {| real_part := 1; imaginary_part := 0 |}.

Lemma complex_zero_self_conj {A} {rops : RingOps A} {rna : Ring A} :
  (complex_conj_impl complex_zero) = complex_zero.
Proof.
  unfold complex_conj_impl.
  unfold complex_zero.
  unfold imaginary_part.
  f_equal.
  apply zero_self_inv.
Qed.

Function complex_add {A} {rops : SemiRingOps A} (x y : Complex A) :=
  {| real_part := real_part A x + real_part A y;
     imaginary_part := imaginary_part A x + imaginary_part A y |}.

Lemma conj_impl_sum {A} {rops : RingOps A} {rna : Ring A} :
  forall a b : Complex A, complex_conj_impl (complex_add a b) =
                          complex_add (complex_conj_impl a) (complex_conj_impl b).
Proof.
  intros.
  unfold complex_conj_impl.
  unfold complex_add.
  elim a.
  elim b.
  unfold real_part.
  unfold imaginary_part.
  intros.
  f_equal.
  apply neg_add.
Qed.

Function complex_mul {A} {rops : RingOps A} (x y : Complex A) :=
  {| real_part := real_part A x * real_part A y -
                  imaginary_part A x * imaginary_part A y;
     imaginary_part := real_part A x * imaginary_part A y +
                       imaginary_part A x * real_part A y |}.

Lemma conj_impl_mul {A} {rops : RingOps A} {rna : Ring A} :
  forall a b : Complex A, (complex_conj_impl (complex_mul a b)) =
                          complex_mul (complex_conj_impl b) (complex_conj_impl a).
Proof.
  intros.
  unfold complex_conj_impl.
  unfold complex_mul.
  elim a.
  elim b.
  unfold real_part.
  unfold imaginary_part.
  intros.
  f_equal.
  rewrite mul_comm.
  rewrite 2! sub_def.
  apply add_extensional.
  reflexivity.
  rewrite <- neg_mul.
  rewrite neg_inv.
  rewrite mul_comm.
  apply neg_mul_left.
  rewrite <- neg_mul.
  rewrite <- neg_mul_left.
  rewrite neg_add.
  rewrite add_comm.
  rewrite mul_comm.
  apply add_extensional.
  reflexivity.
  rewrite mul_comm.
  reflexivity.
Qed.

Instance ComplexSemiRingOps A {rops : RingOps A} : SemiRingOps (Complex A) := {
  zero := complex_zero;
  one := complex_one;
  add := complex_add;
  mul := complex_mul
}.

Instance ComplexImplSemiRingProps {A}
  {rops : RingOps A}
  {rna : Ring A} :
  ComplexSemiRingProps (Complex A) := {
  conj_sum := conj_impl_sum;
  conj_mul := conj_impl_mul;
  zero_self_conj := complex_zero_self_conj
}.

Function complex_sub {A} {rops : RingOps A} (x y : Complex A) :=
  {| real_part := real_part A x - real_part A y;
     imaginary_part := imaginary_part A x - imaginary_part A y |}.

Function complex_neg {A} {rops : RingOps A} (x : Complex A) :=
  {| real_part := - real_part A x; imaginary_part := - imaginary_part A x |}.

Lemma complex_sub_def {A} {rops : RingOps A} :
  forall (x y : Complex A), complex_sub x y = complex_add x (complex_neg y).
Proof.
  intros.
  unfold complex_add.
  unfold complex_neg.
  unfold complex_sub.
  elim x.
  elim y.
  unfold real_part.
  unfold imaginary_part.
  intros.
  f_equal.
  apply sub_def.
  apply sub_def.
Qed.

Lemma complex_sub_zero {A} {rops : RingOps A} :
  forall (x : Complex A), complex_sub x x = zero.
Proof.
  intro.
  unfold complex_sub.
  elim x.
  unfold real_part.
  unfold imaginary_part.
  intros.
  rewrite 2! sub_zero.
  reflexivity.
Qed.

Instance ComplexRingOps A {rops : RingOps A} : RingOps (Complex A) := {
  rops := ComplexSemiRingOps A;
  sub := complex_sub;
  neg := complex_neg;
  sub_def := complex_sub_def;
  sub_zero := complex_sub_zero
}.

Lemma complex_add_extensional {A} {rops : RingOps A} :
  forall x1 x2 y1 y2 : (Complex A),
    x1 = x2 -> y1 = y2 -> complex_add x1 y1 = complex_add x2 y2.
Proof.
  intros.
  unfold complex_add.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Lemma complex_mul_extensional {A} {rops : RingOps A} :
  forall x1 x2 y1 y2 : (Complex A),
    x1 = x2 -> y1 = y2 -> complex_mul x1 y1 = complex_mul x2 y2.
Proof.
  intros.
  unfold complex_mul.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Lemma complex_add_comm {A} {rops : RingOps A} {sring : SemiRingNoAssoc A} :
  forall a b : (Complex A), complex_add a b = complex_add b a.
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
  forall a b : (Complex A), complex_mul a b = complex_mul b a.
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
  forall a b c : (Complex A),
    complex_mul a (complex_add b c) =
    complex_add (complex_mul a b) (complex_mul a c).
Proof.
  intros.
  unfold complex_mul.
  unfold complex_add.
  elim a.
  elim b.
  elim c.
  unfold real_part.
  unfold imaginary_part.
  intros.
  f_equal.
  rewrite 2! add_mul_dist.
  rewrite 3! sub_def.
  rewrite neg_add.
  rewrite 2! add_assoc.
  apply add_extensional.
  rewrite add_comm.
  rewrite add_assoc.
  apply add_extensional.
  apply add_comm.
  reflexivity.
  reflexivity.
  rewrite 2! add_mul_dist.
  rewrite 2! add_assoc.
  apply add_extensional.
  rewrite add_comm.
  rewrite add_assoc.
  apply add_extensional.
  apply add_comm.
  reflexivity.
  reflexivity.
Qed.

Lemma complex_add_zero {A} {rops : RingOps A} {sring : SemiRingNoAssoc A} :
  forall a : (Complex A), complex_add a complex_zero = a.
Proof.
  intros.
  unfold complex_add.
  unfold complex_zero.
  elim a.
  unfold real_part.
  unfold imaginary_part.
  intros.
  f_equal.
  apply add_zero_right.
  apply add_zero_right.
Qed.

Lemma complex_mul_zero {A} {rops : RingOps A} {sring : SemiRingNoAssoc A} :
  forall a : (Complex A), complex_mul a complex_zero = complex_zero.
Proof.
  intros.
  unfold complex_mul.
  unfold complex_zero.
  elim a.
  unfold real_part.
  unfold imaginary_part.
  intros.
  f_equal.
  rewrite 2! mul_zero_right.
  apply sub_zero.
  rewrite 2! mul_zero_right.
  apply add_zero_right.
Qed.

Lemma complex_mul_one {A} {rops : RingOps A} {ring : RingNoAssoc A} :
  forall a : (Complex A), complex_mul a complex_one = a.
Proof.
  intros.
  unfold complex_mul.
  unfold complex_one.
  elim a.
  unfold real_part.
  unfold imaginary_part.
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
  SemiRingNoAssoc (Complex A) := {
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
    forall a b : (Complex A),
      complex_neg (complex_add a b) = complex_add (complex_neg a) (complex_neg b).
Proof.
  intros.
  unfold complex_neg.
  unfold complex_add.
  elim a.
  elim b.
  unfold real_part.
  unfold imaginary_part.
  intros.
  f_equal.
  apply neg_add.
  apply neg_add.
Qed.

Lemma complex_neg_mul {A}
  {rops : RingOps A}
  {ring : RingNoAssoc A} :
    forall a b : (Complex A),
      complex_neg (complex_mul a b) = complex_mul a (complex_neg b).
Proof.
  intros.
  unfold complex_neg.
  unfold complex_mul.
  elim a.
  elim b.
  unfold real_part.
  unfold imaginary_part.
  intros.
  f_equal.
  rewrite <- 2! neg_mul.
  apply neg_sub.
  rewrite <- 2! neg_mul.
  apply neg_add.
Qed.

Lemma complex_neg_add_inv {A} {rops : RingOps A} {ring : RingNoAssoc A} :
  forall a : (Complex A), complex_add (complex_neg a) a = complex_zero.
Proof.
  intro.
  unfold complex_add.
  unfold complex_neg.
  unfold complex_zero.
  elim a.
  unfold real_part.
  unfold imaginary_part.
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
  RingNoAssoc (Complex A) := {
  semiring_no_assoc_r := ComplexSemiRingNoAssoc A;
  neg_add := complex_neg_add;
  neg_mul := complex_neg_mul;
  neg_add_inv := complex_neg_add_inv
}.

Lemma complex_add_assoc {A} {rops : RingOps A} {sring : SemiRing A} :
  forall a b c : (Complex A),
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
  forall a b c : (Complex A),
    complex_mul a (complex_mul b c) = complex_mul (complex_mul a b) c.
Proof.
  intros.
  unfold complex_mul.
  elim a.
  elim b.
  elim c.
  unfold real_part.
  unfold imaginary_part.
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
  SemiRing (Complex A) := {
  semiring_no_assoc_s := ComplexSemiRingNoAssoc A;
  add_assoc := complex_add_assoc;
  mul_assoc := complex_mul_assoc
}.

Instance ComplexRing A
  {rops : RingOps A}
  {ring : Ring A} :
  Ring (Complex A) := {
  semiring_r := ComplexSemiRing A;
  ring_noassoc := ComplexRingNoAssoc A
}.

Function complex_recip {A} {rops : FieldOps A} (x : (Complex A)) :=
  {| real_part :=
       real_part A x / (real_part A x * real_part A x +
                        imaginary_part A x *imaginary_part A x);
     imaginary_part :=
       - imaginary_part A x / (real_part A x * real_part A x +
                               imaginary_part A x *imaginary_part A x) |}.

Function complex_div {A} {rops : FieldOps A} (x y : (Complex A)) :=
  {| real_part :=
       (real_part A x * real_part A y +
        imaginary_part A x * imaginary_part A y) /
       (real_part A y * real_part A y +
        imaginary_part A y *imaginary_part A y);
     imaginary_part :=
       (real_part A y * imaginary_part A x -
        real_part A x * imaginary_part A y) /
       (real_part A y * real_part A y +
        imaginary_part A y *imaginary_part A y) |}.

Instance ComplexFieldOps A
  {rops : FieldOps A} :
  FieldOps (Complex A) := {
  rops := ComplexRingOps A;
  div := complex_div;
  recip := complex_recip
}.

Lemma complex_div_def {A} {rops : FieldOps A} {field : Field A} :
  forall (x y : Complex A), complex_div x y = complex_mul x (complex_recip y).
Proof.
  intros.
  unfold complex_div.
  unfold complex_recip.
  unfold complex_mul.
  elim x.
  elim y.
  unfold real_part.
  unfold imaginary_part.
  intros.
  f_equal.
  rewrite 3! div_def.
  rewrite 2! mul_assoc.
  rewrite <- sub_mul_dist_right.
  rewrite <- neg_mul.
  rewrite sub_def.
  rewrite neg_inv.
  reflexivity.
  rewrite 3! div_def.
  rewrite 2! mul_assoc.
  rewrite <- add_mul_dist_right.
  f_equal.
  rewrite add_comm.
  rewrite <- neg_mul.
  rewrite mul_comm at 1.
  apply sub_def.
Qed.

Lemma complex_recip_mul_inv {A} {rops : FieldOps A} {field : Field A} :
  forall a : (Complex A), complex_mul (complex_recip a) a = complex_one.
Proof.
  intros.
  rewrite complex_mul_comm.
  rewrite <- complex_div_def.
  unfold complex_div.
  unfold complex_one.
  elim a.
  unfold real_part.
  unfold imaginary_part.
  intros.
  f_equal.
  rewrite div_def.
  rewrite mul_comm.
  apply recip_mul_inv.
  rewrite sub_zero.
  rewrite div_def.
  apply mul_zero_left.
Qed.

Instance ComplexFieldAxioms A
  {rops : FieldOps A}
  {field : Field A} :
  FieldAxioms (Complex A) := {
  div_def := complex_div_def;
  recip_mul_inv := complex_recip_mul_inv
}.

Instance ComplexFieldNoAssoc A
  {fops : FieldOps A}
  {field : Field A} :
  FieldNoAssoc (Complex A) := {
  ring_no_assoc_fna := ComplexRingNoAssoc A;
  axioms_fna := ComplexFieldAxioms A
}.

Instance ComplexField A
  {fops : FieldOps A}
  {field : Field A} :
  Field (Complex A) := {
  ring_f := ComplexRing A;
  axioms_f := ComplexFieldAxioms A
}.
