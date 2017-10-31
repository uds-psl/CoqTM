Require Import Shared.Base Shared.FiniteTypes Prelim.

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

Definition Univ_rel {X Y : Type} : X -> Y -> Prop := fun x y => True.
Definition Empty_rel {X Y : Type} : X -> Y -> Prop := fun x y => False.

Definition rcomp X Y Z (R : Rel X Y) (S : Rel Y Z) : Rel X Z :=
  fun x z => exists y, R x y /\ S y z.
Notation "R1 '∘' R2" := (rcomp R1 R2) (at level 40, left associativity).

Definition runion X Y (R : Rel X Y) (S : Rel X Y) : Rel X Y := fun x y => R x y \/ S x y.
Notation "R '∪' S" := (runion R S) (at level 42).

Definition rintersection X Y (R : Rel X Y) (S : Rel X Y) : Rel X Y := fun x y => R x y /\ S x y.
Notation "R '∩' S" := (rintersection R S) (at level 41).

Definition rimplication X Y (R : Rel X Y) (S : Rel X Y) : Rel X Y := fun x y => R x y -> S x y.
Notation "R '⊂' S" := (rimplication R S) (at level 41).

Definition Rsnd1 {X Y} : Rel (Y * X) X := fun p x2 => snd p = x2.
Definition Rsnd2 {X Y} : Rel X (Y * X) := fun x1 p => x1 = snd p.

Definition ignoreParam X Y Z (R : Rel X Z) : Rel X (Y * Z)  := fun x '(y,z) => R x z.
Definition hideParam X Y Z (R : Rel X Z) : Rel (Y * X) Z := fun '(_,x) z => R x z.

Definition finite_rel_union (X Y : Type) (F : Type) (R : F -> Rel X Y) : Rel X Y := 
  fun x y => exists f, R f x y.

Definition functionalOn X Y Z (T : Rel X Y) (R : Rel X Z) :=
  forall x i, T x i -> forall z1 z2, R x z1 -> R x z2 -> z1 = z2.
Notation "'⋃_' f R" := (finite_rel_union (fun f => R)) (at level 50, f at level 9, R at next level, format "'⋃_' f  R"). (* Todo: This does not work if f is higher than 9. Why? *)

Definition ignoreFirst X Y (R : Y -> Prop) : Rel X Y  := fun x y => R y.
Notation "'↑' R" := (ignoreFirst R) (at level 40, format "'↑' R").

Definition rprod X Y Z (R : Rel X Y) (S : Rel X Z) : Rel X (Y * Z) := fun x '(y,z) =>  R x y /\ S x z.
Notation "R '⊗' S" := (rprod R S) (at level 41).

Definition subrel X Y (R S: Rel X Y) := (forall x y, R x y -> S x y).

Notation "R1 <<=2 R2" := (subrel R1 R2) (at level 60).
Notation "R1 <<=3 R2" := (forall x y z, R1 x y z -> R2 x y z) (at level 60).

Definition eqrel X Y (R S: Rel X Y) := (R <<=2 S /\ S <<=2 R) .

Notation "R '=2' S"  := (eqrel R S) (at level 70).

Definition rif X Y (R1 R2 : Rel X Y) : Rel X (bool * Y) := ((fun x p => let (b,z) := p in if b : bool  then R1 x z else R2 x z)).
Notation "'if?' R1 '!' R2" := (rif R1 R2) (at level 60).

Definition restrict X Y Z (R : Rel X (Y * Z)) f : Rel X Z := (fun x1 x2 => R x1 (f, x2)).
Notation "R '|_' f" := (restrict R f) (at level 30, format "R '|_' f").

Lemma rif_restrict X Y (R1 R2 : Rel X Y) b : (if? R1 ! R2) |_b =2 if b then R1 else R2.
Proof.
  destruct b; firstorder.
Qed.

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

Definition pow X R n : Rel X X := it (rcomp R) n eq.

(** Reflexive transitive closure *)

(** * Relations over Vectors *)

Section Fix_X2.

  Variable X Y Z : Type.
  Variable n : nat.

  Local Notation "'V' Z" := (Vector.t Z n) (at level 10).

  Definition Eq_in (f : nat -> Prop) : Rel (V X) (V X) :=
    fun vx vy => forall i (iv : i < n), f i -> get_at iv vx = get_at iv vy.

End Fix_X2.


Definition project (i : nat) (m : nat) (H : i < m) := i.

Definition IdR (X : Type) : Rel X X := eq.

Lemma ignore_hideParam X Y Z A (R1 : Rel X Y) (R2 : Rel Y Z) (a : A):
  ignoreParam (Y := A) R1 ∘ hideParam R2 =2 R1 ∘ R2.
Proof.
  split; intros ? ?; cbn; firstorder; try destruct x0; firstorder.
  exists (a, x0). firstorder.
Qed.

Hint Unfold project Eq_in.

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


Instance eqrel_rif_proper X Y :
  Proper (@eqrel X Y ==> @eqrel X Y ==> @eqrel X (bool * Y)) (@rif X Y).
Proof.
  cbv. firstorder; destruct *; firstorder.
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


Instance eqrel_hideParam_proper X Y Z :
  Proper (@eqrel X Z ==> @eqrel (Y * X) Z) (@hideParam X Y Z).
Proof.
  cbv. firstorder; destruct *; firstorder.
Qed.

Instance functionalOn_eqrel_proper X Y Z :
  Proper (@eqrel X Y ==> @eqrel X Z ==> Basics.impl) (@functionalOn X Y Z).
Proof.
  cbv. intuition. eauto. 
Qed.

Instance Eq_in_equivalence X (f : nat -> Prop) n :
  Equivalence (@Eq_in X n f).
Proof.
  econstructor.
  - econstructor.
  - hnf. intros. hnf in *. intros. rewrite H; eauto.
  - hnf. intros. hnf in *. intros. rewrite H, H0; eauto.
Qed.


Lemma tapes_eq_iff (X : Type)  (n : nat) (t t' : Vector.t X n) (i : nat) (itape itape' : i < n) : (Eq_in (<> i) t t') -> (get_at itape t = get_at itape' t') -> t = t'.
Proof.
  intros. eapply get_at_eq_iff.
  intros. decide (m = i).
  - subst. erewrite get_at_ext. rewrite H0. eapply get_at_ext.
  - rewrite H; eauto. eapply get_at_ext.
Qed.



Lemma function_restrict X Y (R : Rel X X) c :
  (↑ (fun y : Y => y = c) ⊗ R)|_c =2 R.
Proof.
  split; intros ? ? ?; firstorder.
Qed.

Lemma function_restrict2 X Y (R : Rel X X) c c' : c <> c' ->
  (↑ (fun y : Y => y = c') ⊗ R)|_c =2 Empty_rel.
Proof.
  split; intros ? ? ?; firstorder.
Qed.
                
Lemma compose_id X Y (R : Rel X Y) :
  R ∘ (@IdR _) =2 R.
Proof.
  split; intros ? ? ?; hnf in *; firstorder congruence.
Qed.

Definition finite_rel_intersection (X Y : Type) (F : finType) (R : F -> Rel X Y) : Rel X Y := 
  List.fold_right (fun f R' => rintersection (R f) R' ) (fun x y => True) (elem F).
Notation "'⋂_' f R" := (finite_rel_intersection (fun f => R)) (at level 50, f at level 9, R at next level, format "'⋂_' f  R"). (* Todo: This does not work if f is higher than 9. Why? *)

Lemma finite_rel_intersection_spec' (F : finType) (X Y : Type)  (R : F -> Rel X Y) x y A :
  (forall f, f el A -> R f x y) <-> List.fold_right (fun f R' => rintersection (R f) R' ) (fun x y => True) A x y.
Proof.
  induction A; firstorder congruence.
Qed.

Lemma finite_rel_intersection_spec (F : finType) (X Y : Type)  (R : F -> X -> Y -> Prop) x y :
  (forall f, R f x y) <-> finite_rel_intersection R x y.
Proof.
  unfold finite_rel_union. split.
  intros ?.
  - unfold finite_rel_intersection. rewrite <- finite_rel_intersection_spec'. firstorder.
  - intros. unfold finite_rel_intersection in H. rewrite <- finite_rel_intersection_spec' in H.
    eapply H. eauto.
Qed.

Definition reorder m n Z (indices : Vector.t (Fin.t n) m) (V : Vector.t Z n) : Vector.t Z m :=
  Vector.map (Vector.nth V) indices.

Lemma reorder_nth m n Z (indices : Vector.t (Fin.t n) m) (V : Vector.t Z n) (k : Fin.t m) :
  (reorder indices V) [@ k] = V [@ (indices [@ k])].
Proof. now apply Vector.nth_map. Qed.



Fixpoint permute m n (indices : Vector.t (Fin.t m) n) (i : Fin.t m) : option (Fin.t n).
Proof.
  destruct indices.
  - now econstructor.
  - decide (i = h).
    + econstructor. now econstructor.
    + eapply permute in indices. Focus 2. eassumption.
      edestruct indices.
      * econstructor. eapply Fin.FS. eassumption.
      * now econstructor.
Defined.

Lemma reorder_permute X m n (I : Vector.t (Fin.t m) n) ni (i : ni < n) ni2 (i2 : ni2 < m) (V : Vector.t X _) e :
  permute I (Fin.of_nat_lt i2) = Some e ->
  get_at (proj2_sig (Fin.to_nat e)) (reorder I V) = get_at i2 V.
Proof.
  unfold get_at.
Abort.
  
Section lift_gen.

  Variable n : nat.
  Variable X Y Z : Type.

  Variable m : nat.
  Variable indices : Vector.t (Fin.t m) n.
  
  Definition lift_gen (R : Rel (Vector.t X n) (Vector.t Y n)) : Rel (Vector.t X m) (Vector.t Y m) :=
    fun x y => R (reorder indices x) (reorder indices y).

  Definition lift_gen_p (R : Rel (Vector.t X n) (Z * Vector.t Y n)) : Rel (Vector.t X m) (Z * Vector.t Y m) :=
    fun x p => let (z,y) := p in R (reorder indices x) (z, reorder indices y).    

End lift_gen.

Section lift_gen_eq.

  Variable n : nat.
  Variable X Z : Type.

  Variable m : nat.
  Variable I : Vector.t (Fin.t m) n.

  Definition not_indices :=
    (fun x : nat => ~ Vector.In x (Vector.map (proj1_sig (P:=fun i : nat => i < m)) (Vector.map Fin.to_nat I))).

  Definition lift_gen_eq (R : Rel (Vector.t X n) (Vector.t X n)) : Rel (Vector.t X m) (Vector.t X m) :=
    lift_gen I R ∩ Eq_in (not_indices).
  
  Definition lift_gen_eq_p (R : Rel (Vector.t X n) (Z * Vector.t X n)) : Rel (Vector.t X m) (Z * Vector.t X m) :=
    lift_gen_p I R ∩ ignoreParam (Eq_in not_indices).
  
End lift_gen_eq.  

Notation "'↑↑(' x ; .. ; z ')' R" := (lift_gen (Vector.cons _ (Fin.of_nat_lt x) _ .. (Vector.cons _ (Fin.of_nat_lt z) _ (Vector.nil _)) ..) R) (at level 40).
Notation "'↑↑[' x ; .. ; z ']' R" := (lift_gen_p (Vector.cons _ (Fin.of_nat_lt x) _ .. (Vector.cons _ (Fin.of_nat_lt z) _ (Vector.nil _)) ..) R) (at level 40).

Notation "'⇑⇑(' x ; .. ; z ')' R" := (lift_gen_eq (Vector.cons _ (Fin.of_nat_lt x) _ .. (Vector.cons _ (Fin.of_nat_lt z) _ (Vector.nil _)) ..) R) (at level 40).
Notation "'⇑⇑[' x ; .. ; z ']' R" := (lift_gen_eq_p (Vector.cons _ (Fin.of_nat_lt x) _ .. (Vector.cons _ (Fin.of_nat_lt z) _ (Vector.nil _)) ..) R) (at level 40).

Notation "π[ x ; y ; .. ; z ] V" := (reorder (Vector.cons _ (Fin.of_nat_lt x) _ (Vector.cons _ (Fin.of_nat_lt y) _ .. (Vector.cons _ (Fin.of_nat_lt z) _ (Vector.nil _)) ..)) V) (at level 30).

Coercion Fin.of_nat_lt : lt >-> Fin.t.


Lemma Eq_in_monotone n X (P Q : nat -> Prop) x y :
  Eq_in (n := n) (X := X) P x y -> (forall x, Q x -> P x) -> Eq_in Q x y.
Proof.
  intros H ? ? ? ?.
  rewrite H; eauto.
Qed.  
  
Lemma Eq_in_not_indices X n m (I : Vector.t (Fin.t m) n) ni (i : ni < m) x y :
  Eq_in (X := X) (n := m) (<> ni) x y ->
  Vector.In ni (Vector.map (proj1_sig (P:=fun i : nat => i < m)) (Vector.map Fin.to_nat I)) ->
  Eq_in (not_indices I) x y.
Proof.
  intros. eapply Eq_in_monotone; eauto.
  intros ? ? ?. subst. eauto.
Qed.

Lemma Eq_in_replace X P n i (l : i < n) (v v' : Vector.t X n) (x : X) :
  ~ P i -> Eq_in P v v' -> Eq_in P v (Vector.replace v' l x).
Proof.
  unfold Eq_in in *. intros H H'. firstorder. rewrite H'; trivial.
  apply vec_replace_nth_nochange; contradict H; rewrite !Fin.to_nat_of_nat in H; congruence.
Qed.

Lemma rif_lift_gen X Y n (R1 R2 : Rel (Vector.t X n) (Vector.t Y n)) m (I : Vector.t (Fin.t m) n) :
  lift_gen_p I (if? R1 ! R2) =2 if? lift_gen I R1 ! lift_gen I R2.
Proof.
  firstorder.
Qed.

Lemma rintersect_lift_gen X Y n (R1 R2 : Rel (Vector.t X n) (Vector.t Y n)) m (I : Vector.t (Fin.t m) n) :
  lift_gen I (R1 ∩ R2) =2 lift_gen I R1 ∩ lift_gen I R2.
Proof.
  firstorder.
Qed.

Lemma rintersect_lift_gen_eq X n (R1 R2 : Rel (Vector.t X n) (Vector.t X n)) m (I : Vector.t (Fin.t m) n) :
  lift_gen_eq I (R1 ∩ R2) =2 lift_gen_eq I R1 ∩ lift_gen_eq I R2.
Proof.
  firstorder.
Qed.

Lemma rimplication_lift_gen X Y n (R1 R2 : Rel (Vector.t X n) (Vector.t Y n)) m (I : Vector.t (Fin.t m) n) :
  lift_gen I (R1 ⊂ R2) =2 lift_gen I R1 ⊂ lift_gen I R2.
Proof.
  firstorder.
Qed.

(* Lemma rimplication_lift_gen_eq X n (R1 R2 : Rel (Vector.t X n) (Vector.t X n)) m (I : Vector.t (Fin.t m) n) : *)
(*   lift_gen_eq I (R1 ⊂ R2) =2 lift_gen_eq I R1 ⊂ lift_gen_eq I R2. *)
(* Proof. *)
(*   firstorder. *)
(* Qed. *)

Lemma rintersect_lift_gen_eq2 X Z n (R1 R2 : Rel (Vector.t X n) (Z * Vector.t X n)) m (I : Vector.t (Fin.t m) n) :
  lift_gen_eq_p I (R1 ∩ R2) =2 lift_gen_eq_p I R1 ∩ lift_gen_eq_p I R2.
Proof.
  split; intros ? (? & ?); firstorder.
Qed.

Lemma rimplication_lift_gen_eq2 X Z n (R1 R2 : Rel (Vector.t X n) (Z * Vector.t X n)) m (I : Vector.t (Fin.t m) n) :
  lift_gen_eq_p I (R1 ⊂ R2) =2 lift_gen_p I R1 ⊂ lift_gen_eq_p I R2.
Proof.
  split.
  - intros ? (? & ?) ?. firstorder.
  - intros ? (? & ?) ?.
    unfold lift_gen_eq_p, lift_gen_p.
    split.
    + intros ?. admit.
    + unfold ignoreParam, not_indices, Eq_in. intros ? ? ?.
      admit.
Admitted.

Lemma runion_lift_gen X Y n (R1 R2 : Rel (Vector.t X n) (Vector.t Y n)) m (I : Vector.t (Fin.t m) n) :
  lift_gen I (R1 ∪ R2) =2 lift_gen I R1 ∪ lift_gen I R2.
Proof.
  firstorder.
Qed.

Lemma runion_lift_gen_eq X n (R1 R2 : Rel (Vector.t X n) (Vector.t X n)) m (I : Vector.t (Fin.t m) n) :
  lift_gen_eq I (R1 ∪ R2) =2 lift_gen_eq I R1 ∪ lift_gen_eq I R2.
Proof.
  firstorder.
Qed.

Lemma runion_lift_gen_eq2 X Z n (R1 R2 : Rel (Vector.t X n) (Z * Vector.t X n)) m (I : Vector.t (Fin.t m) n) :
  lift_gen_eq_p I (R1 ∪ R2) =2 lift_gen_eq_p I R1 ∪ lift_gen_eq_p I R2.
Proof.
  split; intros ? (? & ?); firstorder.
Qed.

Lemma ignoreParam_lift_gen_eq X Z m n (R : Rel (Vector.t X n) (Vector.t X n)) (I : Vector.t (Fin.t m) n) :
  lift_gen_eq_p (Z := Z) I (ignoreParam R) =2 ignoreParam (lift_gen_eq I R).
Proof.
  split; intros ? (? & ?); firstorder.
Qed.

Lemma restrict_lift_gen_eq X Y n (R : Rel (Vector.t X n) (Y * Vector.t X n)) m (I : Vector.t (Fin.t m) n) f :
  lift_gen_eq I ( R |_ f) =2 ( lift_gen_eq_p I R ) |_ f.
Proof.
  firstorder.
Qed.

Lemma id_lift_gen_eq X n m (I : Vector.t (Fin.t m) n) :
  lift_gen_eq I (@IdR (Vector.t X n)) =2 @IdR _.
Proof.
Admitted.

Instance eqrel_lift_gen_proper X Y n m (I : Vector.t (Fin.t m) n) :
  Proper (@eqrel (Vector.t X n) (Vector.t Y n) ==> @eqrel (Vector.t X m) (Vector.t Y m)) (@lift_gen n X Y m I).
Proof.
  cbv. intuition.
Qed.

Instance eqrel_lift_gen_p_proper X Y Z n m (I : Vector.t (Fin.t m) n) :
  Proper (@eqrel (Vector.t X n) (Z * Vector.t Y n) ==> @eqrel (Vector.t X m) (Z * Vector.t Y m)) (@lift_gen_p n X Y  Z m I).
Proof.
  split; intros ? (? & ?); firstorder.
Qed.

Instance eqrel_lift_gen_eq_proper X n m (I : Vector.t (Fin.t m) n) :
  Proper (@eqrel (Vector.t X n) (Vector.t X n) ==> @eqrel (Vector.t X m) (Vector.t X m)) (@lift_gen_eq n X m I).
Proof.
  split; intros ? ?; firstorder.
Qed.

Instance eqrel_lift_gen_eq_p_proper X Y n m (I : Vector.t (Fin.t m) n) :
  Proper (@eqrel (Vector.t X n) (Y * Vector.t X n) ==> @eqrel (Vector.t X m) (Y * Vector.t X m)) (@lift_gen_eq_p n X Y m I).
Proof.
    split; intros ? (? & ?); firstorder.
Qed.

Lemma compose_lift_gen_eq X n (R S : Rel (Vector.t X n) (Vector.t X n)) m (I : Vector.t (Fin.t m) n) :
  lift_gen_eq I (R ∘ S) =2 (lift_gen_eq I R ∘ lift_gen_eq I S).
Proof.
Admitted.

Lemma compose_lift_gen_eq2 X Z n (R: Rel (Vector.t X n) (Vector.t X n)) (S : Rel (Vector.t X n) (Z * Vector.t X n)) m (I : Vector.t (Fin.t m) n) :
  lift_gen_eq_p I (R ∘ S) =2 (lift_gen_eq I R ∘ lift_gen_eq_p I S).
Proof.
Admitted.

Lemma star_lift_gen_eq X n (R : Rel (Vector.t X n) (Vector.t X n)) m (I : Vector.t (Fin.t m) n) :
  lift_gen_eq I (star R) =2 star (lift_gen_eq I R).
Proof.
  split; intros ? ? ?.
  - econstructor. admit. admit.
  - induction H.
    + econstructor. econstructor. econstructor.
    + econstructor. econstructor. destruct H. admit.
      admit. admit.  
Admitted.

(* Lemma function_vector_lift_eq X Y (R : Rel X X) ni n (i : ni < n) c : *)
(*   (⇑[ i ] (↑ (fun y : Y => y = c) ⊗ R)) =2 (↑ (fun y : Y => y = c) ⊗ ⇑( i ) R). *)
(* Proof. *)
(*   split; intros ? (? & ?) ?; firstorder. *)
(* Qed. *)

Lemma lift_gen_eq_subrel X n (R S : Rel (Vector.t X n) (Vector.t X n)) m (I : Vector.t (Fin.t m) n) :
  R <<=2 S -> lift_gen_eq I R <<=2 lift_gen_eq I S.
Proof.
  intros H ? ? ?; firstorder.
Qed.

Lemma lift_gen_eq_p_subrel X Z n (R S : Rel (Vector.t X n) (Z * Vector.t X n)) m (I : Vector.t (Fin.t m) n) :
  R <<=2 S -> lift_gen_eq_p I R <<=2 lift_gen_eq_p I S.
Proof.
  intros H ? (? & ?) (? & ?); firstorder.
Qed.

Definition functional X Y (R : Rel X Y) := forall x y1 y2, R x y1 -> R x y2 -> y1 = y2. 

Lemma tapes_eq_iff_gen (X : Type) n m (I : Vector.t (Fin.t m) n) (t t' : Vector.t X m) :
  (Eq_in (not_indices I) t t') -> reorder I t = reorder I t' -> t = t'.
Proof.
  intros. eapply get_at_eq_iff.
  intros. 
Admitted.

Lemma functional_lift_gen_eq_p X Z n (R: Rel (Vector.t X n) (Z * Vector.t X n)) m (I : Vector.t (Fin.t m) n) :
  functional R -> functional (lift_gen_eq_p I R).
Proof.
  intros ? ? (? & ?) (? & ?) ? ?.
  destruct H0, H1; cbn in *. eapply H in H0. eapply H0 in H1. inv H1.
  f_equal. eapply tapes_eq_iff_gen; eauto. etransitivity. symmetry. eauto. eauto.
Qed.

Lemma ignoreParam_restrict X Y Z (R : Rel X Z) c :
  (ignoreParam (Y := Y) R) |_c =2 R.
Proof.
  split; intros ? ? ?; firstorder.
Qed.

Lemma function_lift_gen_eq  X Y n (R: Rel (Vector.t X n) (Vector.t X n)) m (I : Vector.t (Fin.t m) n) c :
      (lift_gen_eq_p I (↑ (fun y : Y => y = c) ⊗ R)) =2 (↑ (fun y : Y => y = c) ⊗ lift_gen_eq I R).
Proof.
  split; intros ? (? & ?) ?; firstorder.
Qed.

Definition tape_0 : 0 < 2 := ltac:(omega).
Definition tape_1 : 1 < 2 := ltac:(omega).

Section extend.

  Variable tapes_no : nat.

  Variable tape_i : nat.
  Hypothesis i_is_a_tape : tape_i < S tapes_no.

  Variable tape_j : nat.
  Hypothesis j_is_a_tape : tape_j < S tapes_no.

  Hypothesis neq : tape_i <> tape_j.

  Lemma lift_gen_eq_extend_1 X (R : Rel (Vector.t X 1) (Vector.t X 1)) : ⇑⇑(i_is_a_tape) R =2 ⇑⇑(j_is_a_tape; i_is_a_tape ) (fun t t' => R [|get_at tape_1 t|] [|get_at tape_1 t'|] /\ (get_at tape_0 t = get_at tape_0 t'))%vector_scope.
  Proof.
    split; intros ? ? []; cbn; repeat split.
    - cbn. exact H. 
    - cbn in *. unfold Eq_in, get_at in H0. rewrite H0. reflexivity.
      intros ?. cbn in H1. rewrite Fin.to_nat_of_nat in H1. cbn in H1.
      inversion H1. subst. omega. subst. inv H4.
    - eapply Eq_in_monotone. eassumption. intros. unfold not_indices in *. cbn in *.
      rewrite !Fin.to_nat_of_nat in *. rewrite Fin.to_nat_of_nat in H1.
      intros ?. eapply H1. cbn in *. cbn. econstructor. eassumption.
    - cbn in *. unfold lift_gen. cbn. unfold lift_gen in H. cbn in H. firstorder.
    - unfold lift_gen in H. cbn in H. destruct H.
      intros ? ? ?.
      unfold not_indices in H2. cbn in H2.
      rewrite !Fin.to_nat_of_nat in H2. cbn in H2.
      decide (i = tape_j).
      + subst. erewrite get_at_ext. unfold get_at.
        rewrite H1. eapply eq_nth_iff. reflexivity.
        eapply Fin.of_nat_ext.        
      + rewrite H0. reflexivity.
        intros. unfold not_indices in *. cbn in *.
        rewrite !Fin.to_nat_of_nat in *. cbn.
        intros ?. cbn in *.
        inv H3. omega.
        replace v with ([| tape_i |]%vector_scope) in H6. firstorder.
        eapply Eqdep_dec.inj_pair2_eq_dec in H7. congruence.
        intros. decide equality.
  Qed.

  
  Lemma lift_gen_eq_p_extend_1 X Y (R : Rel (Vector.t X 1) (Y * Vector.t X 1)) : ⇑⇑[i_is_a_tape] R =2 ⇑⇑[j_is_a_tape; i_is_a_tape ] (fun t t' => let (z, t') := t' in R [|get_at tape_1 t|] (z,[|get_at tape_1 t'|]) /\ (get_at tape_0 t = get_at tape_0 t'))%vector_scope.
  Proof.
    split; intros ? (? & ?) []; cbn; repeat split.
    - cbn. exact H. 
    - cbn in *. unfold Eq_in, get_at in H0. rewrite H0. reflexivity.
      intros ?. cbn in H1. rewrite Fin.to_nat_of_nat in H1. cbn in H1.
      inversion H1. subst. omega. subst. inv H4.
    - eapply Eq_in_monotone. eassumption. intros. unfold not_indices in *. cbn in *.
      rewrite !Fin.to_nat_of_nat in *. rewrite Fin.to_nat_of_nat in H1.
      intros ?. eapply H1. cbn in *. cbn. econstructor. eassumption.
    - cbn in *. unfold lift_gen. cbn. unfold lift_gen in H. cbn in H. firstorder.
    - unfold lift_gen in H. cbn in H. destruct H.
      intros ? ? ?.
      unfold not_indices in H2. cbn in H2.
      rewrite !Fin.to_nat_of_nat in H2. cbn in H2.
      decide (i = tape_j).
      + subst. erewrite get_at_ext. unfold get_at.
        rewrite H1. eapply eq_nth_iff. reflexivity.
        eapply Fin.of_nat_ext.        
      + rewrite H0. reflexivity.
        intros. unfold not_indices in *. cbn in *.
        rewrite !Fin.to_nat_of_nat in *. cbn.
        intros ?. cbn in *.
        inv H3. omega.
        replace v with ([| tape_i |]%vector_scope) in H6. firstorder.
        eapply Eqdep_dec.inj_pair2_eq_dec in H7. congruence.
        intros. decide equality.
  Qed.
  
  Lemma lift_gen_eq_extend X (R : Rel (Vector.t X 1) (Vector.t X 1)) : ⇑⇑(i_is_a_tape) R =2 ⇑⇑(i_is_a_tape; j_is_a_tape) (fun t t' => R [|get_at tape_0 t|] [|get_at tape_0 t'|] /\ (get_at tape_1 t = get_at tape_1 t'))%vector_scope.
  Proof.
    split; intros ? ? []; cbn; repeat split.
    - cbn. exact H. 
    - cbn in *. unfold Eq_in, get_at in H0. rewrite H0. reflexivity.
      intros ?. cbn in H1. rewrite Fin.to_nat_of_nat in H1. cbn in H1.
      inversion H1. subst. omega. subst. inv H4.
    - eapply Eq_in_monotone. eassumption. intros. unfold not_indices in *. cbn in *.
      rewrite !Fin.to_nat_of_nat in *. rewrite Fin.to_nat_of_nat in H1.
      intros ?. eapply H1. cbn in *. inv H2. repeat econstructor. inv H5.
    - cbn in *. unfold lift_gen. cbn. unfold lift_gen in H. cbn in H. firstorder.
    - unfold lift_gen in H. cbn in H. destruct H.
      intros ? ? ?.
      decide (i = tape_j).
      + subst. erewrite get_at_ext. unfold get_at at 1. rewrite H1.
        eapply get_at_ext.
      + rewrite H0. reflexivity.
        intros. unfold not_indices in *. cbn in *.
        rewrite !Fin.to_nat_of_nat in *.
        intros ?. cbn in *. eapply H2. cbn in *. inv H3. repeat econstructor.
        replace v with ([| tape_j |]%vector_scope) in H6.
        inv H6. omega. inv H5.
        eapply Eqdep_dec.inj_pair2_eq_dec in H7. congruence.
        intros. decide equality.
  Qed.

  
  Lemma lift_gen_eq_p_extend X Y (R : Rel (Vector.t X 1) (Y * Vector.t X 1)) : ⇑⇑[i_is_a_tape] R =2 ⇑⇑[i_is_a_tape; j_is_a_tape] (fun t t' => let (y,t') := t' in R [|get_at tape_0 t|] (y, [|get_at tape_0 t'|]) /\ (get_at tape_1 t = get_at tape_1 t'))%vector_scope.
  Proof.
    split; intros ? (? & ?) []; cbn; repeat split.
    - cbn. exact H. 
    - cbn in *. unfold Eq_in, get_at in H0. rewrite H0. reflexivity.
      intros ?. cbn in H1. rewrite Fin.to_nat_of_nat in H1. cbn in H1.
      inversion H1. subst. omega. subst. inv H4.
    - eapply Eq_in_monotone. eassumption. intros. unfold not_indices in *. cbn in *.
      rewrite !Fin.to_nat_of_nat in *. rewrite Fin.to_nat_of_nat in H1.
      intros ?. eapply H1. cbn in *. inv H2. repeat econstructor. inv H5.
    - cbn in *. unfold lift_gen. cbn. unfold lift_gen in H. cbn in H. firstorder.
    - unfold lift_gen in H. cbn in H. destruct H.
      intros ? ? ?.
      decide (i = tape_j).
      + subst. erewrite get_at_ext. unfold get_at at 1. rewrite H1.
        eapply get_at_ext.
      + rewrite H0. reflexivity.
        intros. unfold not_indices in *. cbn in *.
        rewrite !Fin.to_nat_of_nat in *. 
        intros ?. cbn in *. eapply H2. cbn in *. inv H3. repeat econstructor.
        replace v with ([| tape_j |]%vector_scope) in H6.
        inv H6. omega. inv H5.
        eapply Eqdep_dec.inj_pair2_eq_dec in H7. congruence.
        intros. decide equality.
  Qed.

End extend.

Instance finite_rel_union_proper (X Y : Type) (F : finType) :
  Proper (pointwise_relation F (@eqrel X Y) ==> @eqrel X Y) (@finite_rel_union X Y F). 
Proof.
  hnf. split; intros ? ? ?; firstorder.
Qed.


Definition rifb (b : bool) X Y (R1 R2 : Rel X Y) := if b then R1 else R2.

Definition update_R X Y (Z : eqType) e (R1: Rel X Y) (R2 : Z -> Rel X Y) :=
  fun z : Z => rifb ( Dec (e = z) )  R1  (R2 z).

Lemma update_sem X Y (Z : eqType) (R1 : Rel X Y) (R2 : Z -> Rel X Y) (z : Z) : R1 <<=2 update_R z R1 R2 z.
Proof. 
  intros ? ? ?. unfold update_R, rifb. dec; cbn; firstorder. 
Qed.

Lemma update_sem2 X Y (Z : eqType) (R1 : Rel X Y) (R2 : Z -> Rel X Y) (z1 z2 : Z) :
  z1 <> z2 ->
  R2 z2 <<=2 update_R z1 R1 R2 z2.
Proof.
  (* split; *) intros ? ?; firstorder. unfold update_R. dec; cbn; firstorder. 
Qed.

Instance rifb_proper (b : bool) X Y :
  Proper (@eqrel X Y ==> @eqrel X Y ==> @eqrel X Y) (@rifb b X Y).
Proof.
  intros ? ? ? ? ? ?. split; intros ? ? ?; unfold rifb;
                        destruct b; firstorder. 
Qed.      

Lemma hideParam_restrict X Y Z I F (R1 : Rel X Y) (R2 : Rel Y Z) f (y' : I):
  ignoreParam (Y := I) R1 ∘ hideParam (↑ (fun y : F => y = f) ⊗ R2) =2 ↑ (fun y : F => y = f) ⊗ (R1 ∘ R2).
Proof.                                                                
  split; intros ? ? ?.
  - firstorder. destruct y, x0. cbn in *. firstorder. 
  - cbv in H. destruct y. firstorder. subst. cbv.
    eexists (_, x0). firstorder.
    Unshelve. eassumption.
Qed.

Section liftT_gen.

  Variable n : nat.
  Variable X Y Z : Type.

  Variable m : nat.
  Variable indices : Vector.t (Fin.t m) n.
  
  Definition liftT_gen (R : Rel (Vector.t X n) Y) : Rel (Vector.t X m) Y :=
    fun x y => R (reorder indices x) y.
  
  Lemma functionalOn_lift_gen (R :  Rel _ Y) (R2 : Rel _ (Z * _)) :
    functionalOn R R2 ->
    functionalOn
      (liftT_gen R)
      (lift_gen_eq_p indices R2).
  Proof.
    intros. hnf in *. intros.
    destruct H1, H2. cbn in *.
    destruct z1 as (z1, t1), z2 as (z2, t2).
    eapply H in H0.
    Focus 2. exact H1. Focus 2. exact H2.
    inv H0.
    f_equal.
    eapply tapes_eq_iff_gen; eauto.
    cbn in *. etransitivity. symmetry. eauto. eauto.
  Qed.

  Definition lift_option X Y E (D : Rel X Y) (R : E -> Rel X Y) : option E -> Rel X Y :=
    fun e => match e with None => D | Some e => R e end.

  Instance lift_option_proper X Y E :
    Proper (@eqrel X Y ==> pointwise_relation _ (@eqrel X Y) ==> pointwise_relation _ (@eqrel X Y)) (@lift_option X Y E).
  Proof.
    hnf. intros. hnf. intros. hnf in *. intros.
    subst. split; intros ? ? ?; firstorder; destruct a; firstorder.
  Qed.

  Lemma lift_option_subrel E (D : Rel X Y) (R : E -> Rel X Y) e :
    lift_option D R (Some e) =2 R e.
  Proof.
    split; intros ? ?; firstorder.
  Qed.

End liftT_gen.