Class Reflexive {A} (r : A -> A -> Prop) := refl : forall a : A, r a a.
Class Commutative {A} (r : A -> A -> Prop) :=
  comm : forall a b : A, r a b -> r b a.
Class Transitive {A} (r : A -> A -> Prop) := 
  trans : forall a b c : A, r a b -> r b c -> r a c.
