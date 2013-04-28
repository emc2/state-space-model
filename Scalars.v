Require Import Relation_Definitions Setoid.
Require Import Field.

Parameter Scalar : Set.

(* Field operations *)
Parameter ScalarOne : Scalar.
Parameter ScalarZero : Scalar.
Parameter ScalarAdd : Scalar -> Scalar -> Scalar.
Parameter ScalarSub : Scalar -> Scalar -> Scalar.
Parameter ScalarMult : Scalar -> Scalar -> Scalar.
Parameter ScalarNeg : Scalar -> Scalar.
Parameter ScalarDiv : Scalar -> Scalar -> Scalar.
Parameter ScalarRecip : Scalar -> Scalar.
Parameter ScalarEq : Scalar -> Scalar -> Prop.

(* Complex conjugates *)
Parameter ScalarConj : Scalar -> Scalar.

(* Order *)
Parameter ScalarLe : Scalar -> Scalar -> Prop.

(* Extensional equality *)
Axiom scalar_extensional : forall x y : Scalar, x = y <-> ScalarEq x y.

(* Field laws *)
Axiom scalar_field_theory :
  field_theory ScalarZero ScalarOne ScalarAdd ScalarMult ScalarSub
               ScalarNeg ScalarDiv ScalarRecip ScalarEq.

(* Stuff required to get the field tactic *)
Definition morphism1 f :=
  forall x y : Scalar, ScalarEq x y -> ScalarEq (f x) (f y).

Definition morphism2 f := 
  forall x y : Scalar,
     ScalarEq x y ->
       forall x0 y0 : Scalar,
         ScalarEq x0 y0 -> ScalarEq (f x x0) (f y y0).

Axiom scalar_setoid_theory : Setoid_Theory Scalar ScalarEq.
Axiom scalar_add_morphism : morphism2 ScalarAdd.
Axiom scalar_mult_morphism : morphism2 ScalarMult.
Axiom scalar_neg_morphism : morphism1 ScalarNeg.
Axiom scalar_recip_morphism : morphism1 ScalarRecip.

Add Setoid Scalar ScalarEq scalar_setoid_theory as scalar_setoid.

Add Morphism ScalarAdd : scalar_add.
Proof. apply scalar_add_morphism. Qed.

Add Morphism ScalarMult : scalar_mult.
Proof. apply scalar_mult_morphism. Qed.

Add Morphism ScalarNeg : scalar_neg.
Proof. apply scalar_neg_morphism. Qed.

Add Morphism ScalarRecip : scalar_recip.
Proof. apply scalar_recip_morphism. Qed.

Add Field scalar_field : scalar_field_theory.

(* Conjugate properties *)
Axiom scalar_conj :
  forall x : Scalar, ScalarMult x (ScalarConj x) = ScalarMult x x.

Axiom scalar_conj_involution :
  forall x : Scalar, ScalarConj (ScalarConj x) = x.

Axiom scalar_conj_add :
  forall x y : Scalar,
    ScalarConj (ScalarAdd x y) = ScalarAdd (ScalarConj x) (ScalarConj y).

Axiom scalar_conj_mult :
  forall x y : Scalar,
    ScalarConj (ScalarMult x y) = ScalarMult (ScalarConj y) (ScalarConj x).

Axiom scalar_zero_self_conj : ScalarConj ScalarZero = ScalarZero.
Axiom scalar_one_self_conj : ScalarConj ScalarOne = ScalarOne.

(* Order properties *)

Axiom scalar_ord_reflexive : forall x : Scalar, ScalarLe x x.
Axiom scalar_ord_antisymmetric :
  forall x y : Scalar, ScalarLe x y -> ScalarLe y x -> ScalarEq x y.
Axiom scalar_ord_transitive :
  forall x y z : Scalar, ScalarLe x y -> ScalarLe y z -> ScalarLe x z.

Axiom scalar_ord_zero_one : ScalarLe ScalarZero ScalarOne.

Definition ScalarPos : forall x : Scalar, ScalarLe ScalarZero x.
Definition ScalarNeg : forall x : Scalar, ScalarLe x ScalarZero.

Axiom scalar_ord_add1 :
  forall x y : Scalar, ScalarPos x -> ScalarPos y -> ScalarLt x (ScalarAdd x y).

Axiom scalar_ord_add2 :
  forall x y : Scalar, ScalarPos x -> ScalarPos y -> ScalarLt y (ScalarAdd x y).