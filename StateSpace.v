Require Import Field Scalars.

(* Definition of a state *)
Inductive State : Set :=
  | ScalarProd : Scalar -> State -> State
  | Join : State -> State -> State
  | Meet : State -> State -> State
  | Conj : State -> State.

(* Null state *)
Parameter Null : State.
Axiom null_zero_scalar_prod : forall s : State, ScalarProd ScalarZero s = Null.

(* Inner products *)
Parameter InnerProd : State -> State -> Scalar.

(* Extensional equality of states by inner products *)
Axiom inner_prod_extensional_eq :
  forall s1 s2 : State, s1 = s2 <->
    (forall s0 : State, InnerProd s0 s1 = InnerProd s0 s2).

(* Inner product laws *)

(* Conjugate symmetry *)
Axiom inner_prod_conj_sym :
  forall x y : State, InnerProd x y = ScalarConj (InnerProd y x).

(* Full continuity *)

(* Homogeneity *)
Axiom inner_prod_homogenous2 :
  forall (s1 s2: State) (a : Scalar),
    InnerProd s1 (ScalarProd a s2) = ScalarMult a (InnerProd s1 s2).

Lemma inner_prod_homogenous1 :
  forall (x y: State) (a : Scalar),
    InnerProd (ScalarProd a x) y = ScalarMult (ScalarConj a) (InnerProd x y).
Proof.
  intros x y a.
  rewrite inner_prod_conj_sym.
  rewrite inner_prod_homogenous2.
  rewrite scalar_conj_mult.
  rewrite <- inner_prod_conj_sym.
  apply scalar_extensional.
  field.
Qed.

(* Positive Semidefiniteness *)

(* Zero *)
Lemma inner_prod_zero2 : forall s : State, InnerProd s Null = ScalarZero.
Proof.
  intro s.
  erewrite <- null_zero_scalar_prod.
  rewrite inner_prod_homogenous2.
  apply scalar_extensional.
  instantiate (1 := s).
  field.
Qed.

Lemma inner_prod_zero1 : forall s : State, InnerProd Null s = ScalarZero.
Proof.
  intro s.
  erewrite <- null_zero_scalar_prod.
  rewrite inner_prod_homogenous1.
  apply scalar_extensional.
  rewrite scalar_zero_self_conj.
  instantiate (1 := s).
  field.
Qed.

(* Non-zero *)


(* Meet preservation *)
Axiom inner_prod_meet2 :
  forall s s1 s2 : State,
    InnerProd s (Meet s1 s2) = ScalarMult (InnerProd s s1) (InnerProd s s2).

Lemma inner_prod_meet1 :
  forall s1 s2 s : State,
    InnerProd (Meet s1 s2) s = ScalarMult (InnerProd s1 s) (InnerProd s2 s).
Proof.
  intros s1 s2 s.
  rewrite inner_prod_conj_sym.
  rewrite inner_prod_meet2.
  rewrite scalar_conj_mult.
  rewrite <- 2! inner_prod_conj_sym.
  apply scalar_extensional.
  field.
Qed.

(* Join preservation *)
Axiom inner_prod_join :
  forall s1 s2 s3 s4 : State,
    InnerProd (Join s1 s2) (Join s3 s4) =
    ScalarAdd (ScalarAdd (InnerProd s1 s3) (InnerProd s1 s4))
              (ScalarAdd (InnerProd s2 s3) (InnerProd s2 s4)).

(* Basic identities *)

(* 0 S = _|_ *)
Lemma scalar_prod_zero : forall s : State, ScalarProd ScalarZero s = Null.
Proof.
  intro s.
  apply inner_prod_extensional_eq.
  intro s0.
  rewrite inner_prod_homogenous2.
  rewrite inner_prod_zero2.
  apply scalar_extensional.
  field.
Qed.

(* a S meet b S = (ab)S *)
Lemma meet_scalar_prod :
  forall (s : State) (a b : Scalar),
    Meet (ScalarProd a s) (ScalarProd b s) =
    ScalarProd (ScalarMult a b) (Meet s s).
Proof.
  intros s a b.
  apply inner_prod_extensional_eq.
  intro s0.
  rewrite inner_prod_meet2, !inner_prod_homogenous2, inner_prod_meet2.
  apply scalar_extensional.
  field.
Qed.

(* S meet _|_ = _|_ *)
Lemma meet_null : forall s : State, Meet s Null = Null.
Proof.
  intro s.
  apply inner_prod_extensional_eq.
  intro s0.
  rewrite inner_prod_meet2, inner_prod_zero2.
  apply scalar_extensional.
  field.
Qed.

(* S1 meet S2 = S2 meet S1 *)
Lemma meet_commute : forall s1 s2 : State, Meet s1 s2 = Meet s2 s1.
Proof.
  intros s1 s2.
  apply inner_prod_extensional_eq.
  intro s0.
  rewrite !inner_prod_meet2.
  apply scalar_extensional.
  field.
Qed.

(* S1 meet (S2 meet S3) = (S1 meet S2) meet S3 *)
Lemma meet_assoc :
  forall s1 s2 s3 : State, Meet s1 (Meet s2 s3) = Meet (Meet s1 s2) s3.
Proof.
  intros s1 s2 s3.
  apply inner_prod_extensional_eq.
  intro s0.
  rewrite !inner_prod_meet2.
  apply scalar_extensional.
  field.
Qed.

(* S join _|_ = S *)
Lemma join_null2 : forall s : State, Join s Null = Null.
Proof.
  intro s.
  apply inner_prod_extensional_eq.
  intro s0.
  rewrite inner_prod_meet2, inner_prod_zero2.
  apply scalar_extensional.
  field.

(* S1 join S2 = S2 join S1 *)
Lemma join_commute : forall s1 s2 : State, Join s1 s2 = Join s2 s1.
Proof.
  intros s1 s2.
  apply inner_prod_extensional_eq.
  intro s0.
  induction s0.
  rewrite !inner_prod_homogenous1.
  rewrite IHs0.
  reflexivity.
  rewrite !inner_prod_join.
  apply scalar_extensional.
  field.
  rewrite !inner_prod_meet1.
  rewrite IHs0_1, IHs0_2.
  reflexivity.
  
  rewrite !inner_prod_join_preserve; apply scalar_extensional; field.
  rewrite !inner_prod_meet_join; apply scalar_extensional; field.
  rewrite !inner_prod_join_conj; apply scalar_extensional; field.
  rewrite !inner_prod_zero1; reflexivity.
Qed.

(*
Lemma null_self_conj : forall s : State, Conj Null = Null.
Proof.
  intro s.
  apply inner_prod_extensional_eq.
  intro s0.
  rewrite inner_prod_zero2.
  rewrite inner_prod_conj_sym.
  rewrite inner_prod_zero1.
  reflexivity.
Qed.
*)

Definition Orthogonal (s1 s2 : State) : Prop :=
  InnerProd s1 s2 = ScalarZero.

Definition Normal (s : State) : Prop :=
  InnerProd s s = ScalarOne

Definition Orthonormal (s1 s2 : State) : Prop :=
  Normal s1 /\ Normal s2 /\ Orthogonal s1 s2.

Definition Degenerate (s : State) : Prop :=
  ~ s = Null /\ InnerProd s s = ScalarZero.