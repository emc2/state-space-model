Require Import Lib.Equiv.

(* Most basic definitions for complex conjugates.  True complex
 * numbers require ring or field axioms.
 *)
Class ComplexOp A := conj : A -> A.

Class Complex A := {
  complex_equiv :> Equiv A;
  complex_op :> ComplexOp A;
  involution : forall x : A, conj (conj x) == x
}.