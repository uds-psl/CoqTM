(* Inhabited types *)
Require Import Coq.Vectors.Vector Coq.Vectors.Fin.

Class inhabitedC (X : Type) :=
  Inhabited
    {
      default : X
    }.

Structure inhabitedType :=
  InhabitedType
    {
      type :> Type;
      class : inhabitedC type
    }.

Arguments InhabitedType type {class}.
Existing Instance class | 0.

Canonical Structure inhabitedType_CS (X : Type) {class : inhabitedC X} : inhabitedType := @InhabitedType X class.

(*
Section Test.
  Variable x : inhabitedType.
  Set Printing All.
  Check default : x.
  Unset Printing All.
End Test.
*)

Instance inhabited_unit : inhabitedC unit.
Proof. do 2 constructor. Defined.


Instance inhabited_inl (a b : Type) (inh_a : inhabitedC a) : inhabitedC (a + b).
Proof. constructor. left. apply default. Defined.

Instance inhabited_inr (a b : Type) (inh_b : inhabitedC b) : inhabitedC (a + b).
Proof. constructor. right. apply default. Defined.

Instance inhabited_option (a : Type) : inhabitedC (option a).
Proof. constructor. right. Defined.

Instance inhabited_bool : inhabitedC bool.
Proof. do 2 constructor. Defined.

Instance inhabited_list (a : Type) : inhabitedC (list a).
Proof. do 2 constructor. Defined.

Instance inhabited_vector (a : Type) (n : nat) (inh_a : inhabitedC a) : inhabitedC (Vector.t a n).
Proof. constructor. eapply VectorDef.const. apply default. Defined.

Instance inhabited_fin (a : Type) (n : nat) : inhabitedC (Fin.t (S n)).
Proof. do 2 constructor. Defined.

Instance inhabited_nat : inhabitedC nat.
Proof. do 2 constructor. Defined.


(*
Section Test2.
  Compute default : bool + bool.
  Compute default : bool + nat.

  Variable someFunction : inhabitedType -> inhabitedType.
  Check someFunction (InhabitedType nat).

  (* Check, that inl and inr work *)
  Variable (A : inhabitedType) (B : Type).
  Check someFunction A.

  Check someFunction (InhabitedType (A + B)).
  Check someFunction (InhabitedType (B + A)).
End Test2.
*)



Require Import Shared.FiniteTypes.

Print FinType.

Record finInhabitedType :=
  FinInhabitedType
    {
      type_finInhabit :> inhabitedType;
      class_dec : eq_dec type_finInhabit;
      class_finite : finTypeC (EqType type_finInhabit);
      class_inhabited : inhabitedC type_finInhabit
    }.

Print finType_CS.

Canonical Structure finInhabitedType_CS (X : Type) {p : eq_dec X} {class1 : finTypeC (EqType X)} {class2 : inhabitedC X} :=
  @FinInhabitedType (InhabitedType X) _ class1 class2.

Print Implicit finInhabitedType_CS.

Section Tes3.
  Variable F : finInhabitedType.

  Check default : F.
  Variable f1 f2 : F.
  Check Dec (f1 = f2).