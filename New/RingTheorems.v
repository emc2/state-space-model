Module RingTheorems.

Require Import New.Ring.

Lemma add_zero_left A
  {srops : SemiRingOps A}
  {sra : SemiRingNoAssoc A} :
    forall a : A, 0 + a = a.
Proof.
  intro.
  rewrite add_comm.
  apply add_zero_right.
Qed.

Lemma mul_zero_left A
  {srops : SemiRingOps A}
  {sra : SemiRingNoAssoc A} :
    forall a : A, 0 * a = 0.
Proof.
  intro.
  rewrite mul_comm.
  apply mul_zero_right.
Qed.

Lemma mul_one_left A
  {srops : SemiRingOps A}
  {sra : SemiRingNoAssoc A} :
    forall a : A, 1 * a = a.
Proof.
  intro.
  rewrite mul_comm.
  apply mul_one_right.
Qed.

End RingTheorems.