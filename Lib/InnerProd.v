Module Type INNER_PROD.
  Require Import Lib.Vector.

  Declare Module Vector : VECTOR.

  Module Scalar := Vector.Scalar.

  Export Vector.
  Export Scalar.

  Parameter inner_prod : V -> V -> T.

  Notation "<| x , y |>" := (inner_prod x y).

  Axiom inner_prod_pos : forall x : V, 0 <= <|x,x|>.
  Axiom inner_prod_zero : forall x : V, <|x,x|> = 0 -> x = null.
  Axiom inner_prod_null : forall x : V, <|x,null|> = 0.
  Axiom inner_prod_conj_sym : forall x y : V, <|x,y|> = <|dual y, dual x|>.
  Axiom inner_prod_superpose2 :
    forall x y z: V, <|sum x y,z|> = <|x,z|> + <|y,z|>.
  Axiom inner_prod_homogenous2 :
    forall (x y : V) (a : T), <|x, scalar a y|> = a * <|x,y|>.
  Axiom inner_prod_conj_dist :
    forall x y : V, conj <|x,y|> = <|dual x, dual y|>.
End INNER_PROD.