Module Type STATE.
  Require Import Lib.Vector.

  Declare Module Vector : VECTOR.

  Module Scalar := Vector.Scalar.

  Definition S := Vector.V.

  Definition null := Vector.null.
  Definition scalar := Vector.scalar.
  Definition compliment := Vector.compliment.
  Definition join := Vector.sum.
  Definition dual := Vector.dual.

  Parameter meet : S -> S -> S.
End STATE.