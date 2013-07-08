Module Type SCALAR.
  Require Import Lib.Equiv Lib.Order Lib.Field Lib.Complex.

  Declare Module Order : ORDER.
  Declare Module Field : FIELD with Definition AbelianGroup.T := Order.T.
  Declare Module Complex : COMPLEX with Definition T := Order.T.

  Export Order.
  Export Field.
  Export Complex.

  Definition T := Order.T.

  Definition real (x : T) := conj x = x.
  Definition negative (x : T) := x < 0.
  Definition positive (x : T) := x > 0.

  Axiom zero_real : real 0.
  Axiom one_real : real 1.
  Axiom conj_add : forall x y : T, conj (x + y) = (conj x) + (conj y).
  Axiom conj_mul : forall x y : T, conj (x * y) = (conj x) * (conj y).

  Axiom add_monotone_leq :
    forall w x y z : T, w <= y -> x <= z -> w + x <= y + z.
  Axiom zero_leq_one : zero <= one.
  Axiom neg_antitone_1 : forall x : T, x > 0 -> neg x < x.
  Axiom neg_antitone_2 : forall x : T, x < 0 -> neg x > x.
  Axiom pos_mul_preserve :
    forall x y : T, positive x -> positive y -> positive (x * y).
  Axiom double_neg_mul :
    forall x y : T, negative x -> negative y -> positive (x * y).
  Axiom neg_pos_mul :
    forall x y : T, negative x -> positive y -> negative (x * y).
End SCALAR.
