Require Export Base.


Module hfset.

  Delimit Scope set_scope with set.
  Open Scope set_scope.

  Inductive set : Type :=
  | empty : set
  | adj (a b : set) : set.

  Implicit Types (a b c x y z : set).

  Inductive element : set -> set -> Prop :=
  | el_adj (a b x : set) : (a = x \/ element x b) -> element x (adj a b).

  Notation "x 'el' y" := (element x y) (at level 70) : set_scope.
  Notation "x ⊆ y" := (forall z, z el x -> z el y) (at level 70) : set_scope.
  Notation "x ≡ y" := (x ⊆ y /\ y ⊆ x) (at level 70) : set_scope.


  (* TODO *)
  Axiom set_dec_el : forall x y, dec (x el y).
  

End hfset.