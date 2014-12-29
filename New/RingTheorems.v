Require Import Coq.Setoids.Setoid.
Require Import New.Ring.

Lemma add_zero_left {A}
  {srops : SemiRingOps A}
  {sra : SemiRingNoAssoc A} :
    forall a : A, 0 + a = a.
Proof.
  intro.
  rewrite add_comm.
  apply add_zero_right.
Qed.

Lemma mul_zero_left {A}
  {srops : SemiRingOps A}
  {sra : SemiRingNoAssoc A} :
    forall a : A, 0 * a = 0.
Proof.
  intro.
  rewrite mul_comm.
  apply mul_zero_right.
Qed.

Lemma mul_one_left {A}
  {srops : SemiRingOps A}
  {sra : SemiRingNoAssoc A} :
    forall a : A, 1 * a = a.
Proof.
  intro.
  rewrite mul_comm.
  apply mul_one_right.
Qed.

Lemma neg_inv {A}
  {rops : RingOps A}
  {ra : Ring A} :
    forall a : A, - -a = a.
Proof.
  intro.
  rewrite <- add_zero_right at 1.
  rewrite <- (sub_zero a).
  rewrite sub_def.
  rewrite add_comm.
  rewrite <- add_assoc.
  rewrite <- sub_def.
  rewrite sub_zero.
  apply add_zero_right.
Qed.

Lemma zero_self_inv {A} {rops : RingOps A} {rna : RingNoAssoc A} : -0 = 0.
Proof.
  rewrite <- add_zero_right at 1.
  rewrite add_comm.
  rewrite <- sub_def.
  apply sub_zero.
Qed.

Lemma neg_sub {A} {rops : RingOps A} {rna : RingNoAssoc A} :
  forall a b : A, -(a - b) = (-a) - (-b).
Proof.
  intros.
  rewrite 2 sub_def.
  apply neg_add.
Qed.

Lemma sub_mul_dist {A} {rops : RingOps A} {rna : RingNoAssoc A} :
  forall a b c : A, a * (b - c) = (a * b) - (a * c).
Proof.
  intros.
  rewrite 2! sub_def.
  rewrite add_mul_dist.
  rewrite neg_mul.
  reflexivity.
Qed.

Lemma add_mul_dist_right {A} {srops : SemiRingOps A} {sra : SemiRingNoAssoc A} :
  forall a b c : A, (b + c) * a = (b * a) + (c * a).
Proof.
  intros.
  rewrite mul_comm at 1.
  rewrite add_mul_dist.
  f_equal.
  apply mul_comm.
  apply mul_comm.
Qed.

Lemma sub_mul_dist_right {A} {srops : RingOps A} {sra : RingNoAssoc A} :
  forall a b c : A, (b - c) * a = (b * a) - (c * a).
Proof.
  intros.
  rewrite mul_comm at 1.
  rewrite sub_mul_dist.
  f_equal.
  apply mul_comm.
  apply mul_comm.
Qed.

Lemma neg_mul_left {A} {srops : RingOps A} {sra : RingNoAssoc A} :
  forall a b : A, -(a * b) = (-a) * b.
Proof.
  intros.
  rewrite mul_comm.
  rewrite neg_mul.
  apply mul_comm.
Qed.