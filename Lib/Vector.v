Module Type VECTOR.
  Require Import Lib.Scalar.

  Declare Module Scalar : SCALAR.

  Parameter V : Type.

  Parameter null : V.
  Parameter dual : V -> V.
  Parameter compliment : V -> V.
  Parameter scalar : Scalar.T -> V -> V.
  Parameter sum : V -> V -> V.
End VECTOR.