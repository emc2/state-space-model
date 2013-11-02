Class Reflexive {A} (r : A -> A -> Prop) := reflexive : forall a : A, r a a.

Class Transitive {A} (r : A -> A -> Prop) := 
  transitive : forall a b c : A, r a b -> r b c -> r a c.

Class Antisymmetric {A} (r : A -> A -> Prop) (eq : A -> A -> Prop) :=
  antisymmetry : forall a b, r a b -> r b a -> eq a b.

Class Symmetric {A} (r : A -> A -> Prop) :=
  symmetry : forall a b : A, r a b -> r b a.

Class Involution {A} (op : A -> A) (eq : A -> A -> Prop) :=
  involution : forall a : A, eq a (op (op a)).

Class Commutative {A} (op : A -> A -> A) (eq : A -> A -> Prop) :=
  commutative : forall a b : A, eq (op a b) (op b a).

Class Associative {A} (op : A -> A -> A) (eq : A -> A -> Prop) :=
  associative : forall a b c : A, eq (op a (op b c)) (op (op a b) c).

Class Distributive {A} (op1 : A -> A -> A) (op2 : A -> A -> A)
                       (eq : A -> A -> Prop) := {
  left_distributive : forall a b c : A,
    eq (op1 a (op2 b c)) (op2 (op1 a b) (op1 a c));
  right_distributive : forall a b c : A,
    eq (op1 (op2 a b) c) (op2 (op1 a c) (op1 b c))
}.