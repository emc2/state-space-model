(* Actually these are complex fields *)
Module Type FIELD.
  Require Import Lib.AbelianGroup.

  Declare Module AbelianGroup : ABELIAN_GROUP.
  Export AbelianGroup.

  Definition T : Type := AbelianGroup.T.

  Parameter one : T.
  Parameter mul : T -> T -> T.
  Parameter div : T -> T -> T.
  Parameter inv : T -> T.

  Notation "1" := one.
  Notation "x * y" := (mul x y).
  Notation "x / y" := (div x y).
  Notation "/ x" := (inv x).

  Axiom mul_zero : forall x : T, x * 0 = 0.
  Axiom mul_one : forall x : T, x * 1 = x.
  Axiom mul_comm : forall x y : T, x * y = y * x.
  Axiom mul_assoc : forall x y z : T, (x * y) * z = x * (y * z).
  Axiom add_mul_dist : forall x y z : T, (x + y) * z = (x * z) + (y * z).
  Axiom one_neq_zero : not (1 = 0).
  Axiom div_def : forall x y : T, x / y = x * / y.
  Axiom inv_one : forall x : T, x * / x = 1.
  Axiom mul_ext : forall x y z : T, x * z = y * z -> x = y.
  Axiom inv_ext : forall x y : T, / x = / y -> x = y.
End FIELD.