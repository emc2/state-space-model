Require Import Field Scalars.

(* Definition of a state *)
Inductive State : Set :=
  | ScalarProd : Scalar -> State -> State
  | Join : State -> State -> State
  | Meet : State -> State -> State
  | Conj : State -> State
  | Null : State.

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

(* Positive Semidefiniteness *)

(* Zero *)
Axiom inner_prod_zero2 : forall s : State, InnerProd s Null = ScalarZero.

Lemma inner_prod_zero1 : forall s : State, InnerProd Null s = ScalarZero.
Proof.
  intro s.
  rewrite inner_prod_conj_sym.
  rewrite inner_prod_zero2.
  rewrite scalar_zero_self_conj.
  reflexivity.
Qed.

(* Non-zero *)

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

(* Meet preservation *)
Axiom inner_prod_meet_preserve :
  forall s1 s2 s3 s4 : State,
    InnerProd (Meet s1 s2) (Meet s3 s4) =
    ScalarMult (ScalarMult (InnerProd s1 s3) (InnerProd s1 s4))
               (ScalarMult (InnerProd s2 s3) (InnerProd s2 s4)).

(* Join preservation *)
Axiom inner_prod_join_preserve :
  forall s1 s2 s3 s4 : State,
    InnerProd (Join s1 s2) (Join s3 s4) =
    ScalarAdd (ScalarAdd (InnerProd s1 s3) (InnerProd s1 s4))
              (ScalarAdd (InnerProd s2 s3) (InnerProd s2 s4)).

(* Meet-join preservation *)
Axiom inner_prod_meet_join :
  forall s1 s2 s3 s4 : State,
    InnerProd (Meet s1 s2) (Join s3 s4) =
    ScalarMult (ScalarAdd (InnerProd s1 s3) (InnerProd s1 s4))
               (ScalarAdd (InnerProd s2 s3) (InnerProd s2 s4)).

Lemma inner_prod_join_meet :
  forall s1 s2 s3 s4 : State,
    InnerProd (Join s1 s2) (Meet s3 s4) =
    ScalarMult (ScalarAdd (InnerProd s1 s3) (InnerProd s2 s3))
               (ScalarAdd (InnerProd s1 s4) (InnerProd s2 s4)).
Proof.
  intros s1 s2 s3 s4.
  rewrite inner_prod_conj_sym.
  rewrite inner_prod_meet_join.
  rewrite scalar_conj_mult.
  rewrite scalar_conj_add.
  rewrite <- !inner_prod_conj_sym.
  rewrite scalar_conj_add.
  rewrite <- !inner_prod_conj_sym.
  apply scalar_extensional.
  field.
Qed.

Axiom inner_prod_meet_scalar_prod :
  forall (s1 s2 s3 : State) (a : Scalar),
    InnerProd (ScalarProd a s1) (Meet s2 s3) =
      ScalarMult (InnerProd (ScalarProd a s1) s2)
                 (InnerProd (ScalarProd a s1) s3).

Axiom inner_prod_join_scalar_prod :
  forall (s1 s2 s3 : State) (a : Scalar),
    InnerProd (ScalarProd a s1) (Join s2 s3) =
      ScalarAdd (InnerProd (ScalarProd a s1) s2)
                (InnerProd (ScalarProd a s1) s3).

Axiom inner_prod_meet_conj :
  forall s1 s2 s3 : State,
    InnerProd (Conj s1) (Meet s2 s3) =
      ScalarMult (InnerProd (Conj s1) s2) (InnerProd (Conj s1) s3).

Axiom inner_prod_join_conj :
  forall s1 s2 s3 : State,
    InnerProd (Conj s1) (Join s2 s3) =
      ScalarAdd (InnerProd (Conj s1) s2) (InnerProd (Conj s1) s3).


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

(* S1 meet S2 = S2 meet S1 *)
Lemma meet_commute : forall s1 s2 : State, Meet s1 s2 = Meet s2 s1.
Proof.
  intros s1 s2.
  apply inner_prod_extensional_eq.
  intro s0.
  destruct s0.
  rewrite !inner_prod_meet_scalar_prod.
  apply scalar_extensional.
  field.
  rewrite !inner_prod_join_meet.
  apply scalar_extensional.
  field.
  rewrite !inner_prod_meet_preserve.
  apply scalar_extensional.
  field.
  rewrite !inner_prod_meet_conj.
  apply scalar_extensional.
  field.
  rewrite !inner_prod_zero1.
  reflexivity.
Qed.

(* S1 join S2 = S2 join S1 *)
Lemma join_commute : forall s1 s2 : State, Join s1 s2 = Join s2 s1.
Proof.
  intros s1 s2.
  apply inner_prod_extensional_eq.
  intro s0.
  destruct s0.
  rewrite !inner_prod_join_scalar_prod.
  apply scalar_extensional.
  field.
  rewrite !inner_prod_join_preserve.
  apply scalar_extensional.
  field.
  rewrite !inner_prod_meet_join.
  apply scalar_extensional.
  field.
  rewrite !inner_prod_join_conj.
  apply scalar_extensional.
  field.
  rewrite !inner_prod_zero1.
  reflexivity.
Qed.

(* (S1 meet S2) meet S3 = S1 meet (S2 meet S3) *)
(*
Lemma meet_assoc : forall s1 s2 s3 : State,
  Meet (Meet s1 s2) s3 = Meet s1 (Meet s2 s3).
Proof.
Qed.
*)

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