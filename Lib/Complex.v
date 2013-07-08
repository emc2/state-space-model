Module Type COMPLEX.
  (* Most basic definitions for complex conjugates.  True complex
   * numbers require ring or field axioms.
   *)
  Parameter T : Type.
  Parameter conj : T -> T.

  Axiom involution : forall x : T, conj (conj x) = x.
  Axiom conj_ext : forall x y : T, conj x = conj y -> x = y.
End COMPLEX.