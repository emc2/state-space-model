Module Type INNER_PROD.
  Require Import Lib.Vector.

  Declare Module Vector : VECTOR.

  Module Scalar := Vector.Scalar.

  Export Vector.
  Export Scalar.

  Parameter inner_prod : V -> V -> T.

  Notation "<| x , y |>" := (inner_prod x y).

  Axiom inner_prod_pos_def1 : forall x : V, not (x = null) -> 0 < <|x,x|>.
  Axiom inner_prod_pos_def2 : <|null,null|> = 0.
  Axiom inner_prod_conj_sym : forall x y : V, <|x,y|> = <|dual y, dual x|>.
  Axiom inner_prod_superpose :
    forall x y z: V, <|sum x y,z|> = <|x,z|> + <|y,z|>.
  Axiom inner_prod_homogenous :
    forall (x y : V) (a : T), <|x, scalar a y|> = a * <|x,y|>.
End INNER_PROD.