Require Import Shared.Base Shared.FiniteTypes TM.Prelim.
Require Import Shared.Vectors.Vectors.

(** * Equality *)
(** Introduce some Haskell style like notations. *)
Notation "(=)" := eq (only parsing).
Notation "( x =)" := (eq x) (only parsing).
Notation "(= x )" := (fun y => eq y x) (only parsing).
Notation "(<>)" := (fun x y => x <> y) (only parsing).
Notation "( x <>)" := (fun y => x <> y) (only parsing).
Notation "(<> x )" := (fun y => y <> x) (only parsing). 

(** * Relations *)

Definition Rel (X : Type) (Y : Type) := X -> Y -> Prop.

Definition Rel3 X Y Z := X -> Y -> Z -> Prop.
Definition Rel3_is_Rel X Y Z (R : Rel3 X Y Z) : Rel X (Y * Z) := fun x1 p => let (y, x2) := p in R x1 y x2.
Coercion Rel3_is_Rel : Rel3 >-> Rel.

Definition fun_to_Rel F B Z  (R : F -> Rel B Z) : Rel (F * B) Z := fun p z => let (f,b) := p in R f b z.
Notation "'⇑' R" := (fun_to_Rel R) (at level 30, format "'⇑' R").

Definition rcomp X Y Z (R : Rel X Y) (S : Rel Y Z) : Rel X Z :=
  fun x z => exists y, R x y /\ S y z.
Notation "R1 '∘' R2" := (rcomp R1 R2) (at level 40, left associativity).
Arguments rcomp {X Y Z} (R S) x y /.

Definition runion X Y (R : Rel X Y) (S : Rel X Y) : Rel X Y := fun x y => R x y \/ S x y.
Notation "R '∪' S" := (runion R S) (at level 42).
Arguments runion { X Y } ( R S ) x y /.

Definition rintersection X Y (R : Rel X Y) (S : Rel X Y) : Rel X Y := fun x y => R x y /\ S x y.
Notation "R '∩' S" := (rintersection R S) (at level 41).
Arguments rintersection { X Y } ( R S ) x y /.


Definition rimplication X Y (R : Rel X Y) (S : Rel X Y) : Rel X Y := fun x y => R x y -> S x y.
Notation "R '⊂' S" := (rimplication R S) (at level 41).
Arguments rimplication { X Y } ( R S ) x y /.

Definition ignoreParam X Y Z (R : Rel X Z) : Rel X (Y * Z)  := fun x '(y,z) => R x z.
Arguments ignoreParam {X Y Z} ( R ) x y /.

Definition rUnion (X Y : Type) (F : Type) (R : F -> Rel X Y) : Rel X Y := 
  fun x y => exists f, R f x y.
Notation "'⋃_' f R" := (rUnion (fun f => R)) (at level 50, f at level 9, R at next level, format "'⋃_' f  R"). (* Todo: This does not work if f is higher than 9. Why? *)
Arguments rUnion { X Y F } ( R ) x y /.

Definition rIntersection (X Y : Type) (F : Type) (R : F -> Rel X Y) : Rel X Y := 
  fun x y => forall f, R f x y.
Notation "'⋂_' f R" := (rIntersection (fun f => R)) (at level 50, f at level 9, R at next level, format "'⋂_' f  R"). (* Todo: This does not work if f is higher than 9. Why? *)
Arguments rIntersection { X Y F } ( R ) x y /.


Definition surjective X Z (R : Rel X Z) :=
  forall x, exists y, R x y.

Definition functional X Z (R : Rel X Z) :=
  forall x z1 z2, R x z1 -> R x z2 -> z1 = z2.


Definition ignoreFirst X P1 P2 Z (R : Rel X (P2 * Z)) : Rel X ((P1*P2)*Z) := fun x '((p1, p2), z) => R x (p2, z).
Arguments ignoreFirst { X P1 P2 Z } ( R ) x y /.

Definition ignoreSecond X P1 P2 Z (R : Rel X (P1 * Z)) : Rel X ((P1*P2)*Z) := fun x '((p1, p2), z) => R x (p1, z).
Arguments ignoreSecond { X P1 P2 Z } ( R ) x y /.

Definition rprod X Y Z (R : Rel X Y) (S : Rel X Z) : Rel X (Y * Z) := fun x '(y,z) =>  R x y /\ S x z.
Notation "R '⊗' S" := (rprod R S) (at level 41).
Arguments rprod { X Y Z } ( R S ) x y /.

Definition subrel X Y (R S: Rel X Y) := (forall x y, R x y -> S x y).

Notation "R1 <<=2 R2" := (subrel R1 R2) (at level 60).
Notation "R1 <<=3 R2" := (forall x y z, R1 x y z -> R2 x y z) (at level 60).

Lemma subrel_and X Y (R1 R2 R3 : Rel X Y) :
  R1 <<=2 R3 \/ R2 <<=2 R3 -> R1 ∩ R2 <<=2 R3.
Proof. firstorder. Qed.

Lemma subrel_or X Y (R1 R2 R3 : Rel X Y) :
  R1 <<=2 R3 /\ R2 <<=2 R3 -> R1 ∪ R2 <<=2 R3.
Proof. firstorder. Qed.

Lemma subrel_and2 X Y (R1 R2 R3 R4 : Rel X Y) :
  R1 <<=2 R3 /\ R2 <<=2 R4 -> R1 ∩ R2 <<=2 R3 ∩ R4.
Proof. firstorder. Qed.

Lemma subrel_or2 X Y (R1 R2 R3 R4 : Rel X Y) :
  R1 <<=2 R3 /\ R2 <<=2 R4 -> R1 ∪ R2 <<=2 R3 ∪ R4.
Proof. firstorder. Qed.

Definition eqrel X Y (R S: Rel X Y) := (R <<=2 S /\ S <<=2 R) .

Notation "R '=2' S"  := (eqrel R S) (at level 70).


Definition restrict X Y Z (R : Rel X (Y * Z)) f : Rel X Z := (fun x1 x2 => R x1 (f, x2)).
Notation "R '|_' f" := (restrict R f) (at level 30, format "R '|_' f").
Arguments restrict { X Y Z } ( R f ) x y /.

Lemma rintersect_restrict X Y (R1 R2 : Rel X (bool * Y)) b : (R1 ∩ R2) |_ b = (R1 |_ b) ∩ (R2 |_ b).
Proof.
  destruct b; firstorder.
Qed.

Lemma rimplication_restrict X Y (R1 R2 : Rel X (bool * Y)) b : (R1 ⊂ R2) |_ b = (R1 |_ b) ⊂ (R2 |_ b).
Proof.
  destruct b; firstorder.
Qed.

Lemma runion_restrict X Y (R1 R2 : Rel X (bool * Y)) b : (R1 ∪ R2) |_ b = (R1 |_ b) ∪ (R2 |_ b).
Proof.
  destruct b; firstorder.
Qed.

Lemma rcomp_restrict X Y Z (R1 : Rel X Y) (R2 : Rel Y (bool * Z)) b :
  (R1 ∘ R2) |_ b = R1 ∘ (R2 |_ b).
Proof.
  destruct b; firstorder.
Qed.



(** * Relations over Vectors *)

Section Fix_X2.

  Variable X Y Z : Type.
  Variable n : nat.

  Local Notation "'V' Z" := (Vector.t Z n) (at level 10).

  Definition Eq_in (f : Fin.t n -> Prop) : Rel (V X) (V X) :=
    fun vx vy => forall i : Fin.t n, f i -> vy[@i] = vx[@i].

  Instance Eq_in_equivalence X (f : Fin.t n -> Prop) :
    Equivalence (@Eq_in X).
  Proof.
    econstructor.
    - econstructor.
    - hnf. intros. hnf in *. intros. rewrite <- H; eauto.
    - hnf. intros. hnf in *. intros. rewrite <- H, <- H0; eauto.
  Qed.

End Fix_X2.

Arguments Eq_in { X n } P x y / : rename.





Definition pow X R n : Rel X X := it (rcomp R) n eq.

(** Reflexive transitive closure *)

Inductive star X (R: Rel X X) : Rel X X :=
| starR x : star R x x
| starC x y z : R x y -> star R y z -> star R x z.

(* Making first argument a non-uniform parameter doesn't simplify the induction principle. *)

Lemma star_simpl_ind X (R: Rel X X) (p : X -> Prop) y :
  p y ->
  (forall x x', R x x' -> star R x' y -> p x' -> p x) -> 
  forall x, star R x y -> p x.
Proof.
  intros A B. induction 1; eauto.
Qed.

Lemma star_trans X (R:Rel X X):
  forall x y z, star R x y -> star R y z -> star R x z.
Proof.
  induction 1; eauto using star.
Qed.

(** Power characterization *)
Lemma star_pow X (R:Rel X X) x y :
  star R x y <-> exists n, pow R n x y.
Proof.
  split; intros A.
  - induction A as [ |x x' y B _ [n IH]].
    + exists 0. reflexivity.
    + exists (S n), x'. auto.
  - destruct A as [n A].
    revert x A. induction n; intros x A.
    + destruct A. constructor.
    + destruct A as [x' [A B]]. econstructor; eauto.
Qed.

Lemma pow_star X (R:Rel X X) x y n:
  pow R n x y -> star R x y.
Proof.
  intros A. erewrite star_pow. eauto.
Qed.

(*(** Equivalence closure *)

  Inductive ecl R : X -> X -> Prop :=
  | eclR x : ecl R x x
  | eclC x y z : R x y -> ecl R y z -> ecl R x z
  | eclS x y z : R y x -> ecl R y z -> ecl R x z.

  Lemma ecl_trans R :
    transitive (ecl R).
  Proof.
    induction 1; eauto using ecl.
  Qed.

  Lemma ecl_sym R :
    symmetric (ecl R).
  Proof.
    induction 1; eauto using ecl, (@ecl_trans R).
  Qed.

  Lemma star_ecl R :
    star R <=2 ecl R.
  Proof.
    induction 1; eauto using ecl.
  Qed.
 *)

Lemma pow_add X (R: Rel X X) n m (s t : X) : pow R (n + m) s t <-> rcomp (pow R n) (pow R m) s t.
Proof.
  revert m s t; induction n; intros m s t.
  - simpl. split; intros. econstructor. split. unfold pow. simpl. reflexivity. eassumption.
    destruct H as [u [H1 H2]]. unfold pow in H1. simpl in *. subst s. eassumption.
  - simpl in *; split; intros.
    + destruct H as [u [H1 H2]].
      change (it (rcomp R) (n + m) eq) with (pow R (n+m)) in H2.
      rewrite IHn in H2.
      destruct H2 as [u' [A B]]. unfold pow in A.
      econstructor. 
      split. econstructor. repeat split; repeat eassumption. eassumption.
    + destruct H as [u [H1 H2]].
      destruct H1 as [u' [A B]].
      econstructor.  split. eassumption. change (it (rcomp R) (n + m) eq) with (pow R (n + m)).
      rewrite IHn. econstructor. split; eassumption.
Qed.

Lemma rcomp_eq X (R S R' S' : Rel X X) (s t : X) : (R =2 R') -> (S =2 S') -> (rcomp R S s t <-> rcomp R' S' s t).
Proof.
  intros A B.
  split; intros H; destruct H as [u [H1 H2]];
    eapply A in H1; eapply B in H2;
      econstructor; split; eassumption.
Qed.

Lemma eq_ref X (R : X -> X -> Prop) : R =2 R.
Proof.
  split; intros s t; tauto.
Qed.

Lemma rcomp_1 X (R : X -> X -> Prop): R =2 pow R 1.
Proof.
  split; intros s t; unfold pow in *; simpl in *; intros H.
  - econstructor. split; eauto.
  - destruct H as [u [H1 H2]]; subst u; eassumption.
Qed.

Instance eqrel_equiv X Y: Equivalence (@eqrel X Y).
Proof.
  constructor;firstorder.
Qed.

(* Instance subrel_rcomp_proper X Y Z: *)
(*   Proper (@subrel X Y ==> @subrel Y Z ==> @subrel X Z) (@rcomp X Y Z). *)
(* Proof. *)
(*   firstorder. *)
(* Qed. *)

Instance eqrel_subrel_subrel X Y:
  subrelation (@eqrel X Y) (@subrel X Y).
Proof.
  firstorder.
Qed.

Instance subrel_preorder X Y: PreOrder (@subrel X Y).
Proof.
  constructor;firstorder.
Qed.

Instance subrel_subrel X Y: subrelation (@subrel X Y) (pointwise_relation X (pointwise_relation Y Basics.impl)).
Proof.
  firstorder.
Qed.

Instance equiv_subrel X Y: subrelation (@eqrel X Y) (pointwise_relation X (pointwise_relation Y iff)).
Proof.
  firstorder.
Qed.

Lemma use_subrel X Y (R1 R2 : Rel X Y) s t: subrel R1 R2 -> R1 s t -> R2 s t.
  firstorder.
Qed.


Instance subrel_eqrel_proper X Y:
  Proper (@eqrel X Y ==> @eqrel X Y ==> Basics.impl) (@subrel X Y).
Proof.
  firstorder.
Qed.

Lemma star_rcomp_idem X (R: Rel X X):
  star R ∘ star R =2 star R.
Proof.
  unfold rcomp. 
  firstorder eauto using star_trans, starR.
Qed.

Lemma R_in_star X (R: Rel X X):
  R <<=2 star R.
Proof.
  hnf. eauto using star.
Qed.

Lemma rcomp_assoc X Y Z W (R1: Rel X Y) (R2: Rel Y Z) (R3: Rel Z W):
  R1 ∘ R2 ∘ R3 =2 R1 ∘ (R2 ∘ R3).
Proof.
  firstorder.
Qed.

Instance eqrel_rcomp_proper X Y Z:
  Proper (@eqrel X Y ==> @eqrel Y Z ==> @eqrel X Z) (@rcomp X Y Z).
Proof.
  constructor;firstorder.
Qed.

Instance eqrel_star_proper X :
  Proper (@eqrel X X ==> @eqrel X X) (@star X).
Proof.
  hnf. intros. split.
  - induction 1.
    + econstructor.
    + econstructor. rewrite <- H. eauto. eauto.
  - induction 1.
    + econstructor.
    + econstructor. rewrite H. eauto. eauto.
Qed.

Instance eqrel_union_proper X Y :
  Proper (@eqrel X Y ==> @eqrel X Y ==> @eqrel X Y) (@runion X Y).
Proof.
  cbv. intuition.
Qed.

Instance eqrel_rintersection_proper X Y :
  Proper (@eqrel X Y ==> @eqrel X Y ==> @eqrel X Y) (@rintersection X Y).
Proof.
  cbv. intuition.
Qed.

Instance eqrel_rimplication_proper X Y :
  Proper (@eqrel X Y ==> @eqrel X Y ==> @eqrel X Y) (@rimplication X Y).
Proof.
  cbv. intuition.
Qed.

Instance eqrel_restrict_proper X Y Z :
  Proper (@eqrel X (Y * Z) ==> @eq Y ==> @eqrel X Z) (@restrict X Y Z).
Proof.
  cbv. intuition; subst; intuition.
Qed.


Instance eqrel_rprod_proper X Y Z :
  Proper (@eqrel X Y ==> @eqrel X Z ==> @eqrel X (Y * Z)) (@rprod X Y Z).
Proof.
  cbv. firstorder; destruct *; firstorder.
Qed.

Instance eqrel_ignoreParam_proper X Y Z :
  Proper (@eqrel X Z ==> @eqrel X (Y * Z)) (@ignoreParam X Y Z).
Proof.
  cbv. firstorder; destruct *; firstorder.
Qed.


(* Introduce a param that is fixed to a value *)
Definition rfix X Y Z (R : Rel X Z) (p : Y) : Rel X (Y*Z) := (fun x '(y, z) =>
y = p /\ R x z).
Notation "R '||_' f" := (rfix R f) (at level 30, format "R '||_' f").
Arguments rfix { X Y Z } ( R p ) x y /.