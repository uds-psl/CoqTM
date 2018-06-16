Require Export Shared.FiniteTypes.FinTypes Shared.FiniteTypes.BasicFinTypes Shared.FiniteTypes.CompoundFinTypes Shared.FiniteTypes.VectorFin.
Require Export Shared.Vectors.FinNotation.
Require Export Shared.Retracts.
Require Export Shared.Inhabited.
Require Export Shared.Base.
Require Export Shared.Vectors.Vectors Shared.Vectors.VectorDupfree.

Require Export smpl.Smpl.

Global Open Scope vector_scope.


(* Instance fin_eq_dec (A: finType) : eq_dec A. *)
(* Proof. *)
(*   now destruct A, type.  *)
(* Qed. *)

(* Definition graph_of := fun A B => fun (f:A -> B) => { p: A * B & f (fst p) = snd p}. *)
(* Definition graph_enum := fun (A B : finType) => fun (f : A -> B) => filter (fun (p : A * B) => Dec (f (fst p) = snd p)) (elem (A (x) B)). *)

Fixpoint loop (A:Type) n (f:A -> A) (p : A -> bool) a {struct n}:=
  if p a then Some a  else
    match n with
      O => None
    | S m => loop m f p (f a)
    end.

Lemma loop_functional A n1 n2 f p (a : A) c1 c2 : loop n1 f p a = Some c1 -> loop n2 f p a = Some c2 -> c1 = c2.
Proof.
  revert n2 c1 c2 a. induction n1; intros; cbn in *.
  - destruct (p a) eqn:E; inv H.
    destruct n2; cbn in H0; rewrite E in H0; now inv H0.
  - destruct (p a) eqn:E.
    + inv H. destruct n2; cbn in H0; rewrite E in H0; now inv H0.
    + destruct n2; cbn in H0; rewrite E in H0; try now inv H0.
      eauto.
Qed.
  
Lemma loop_fulfills_p A n f p (a : A) c : loop n f p a = Some c -> p c.
Proof.
  revert a; induction n; intros; inv H; destruct (p a) eqn:E; inv H1; eauto.
Qed.

Lemma loop_fulfills_p_0 A n f p (a : A) : p a = true -> loop n f p a = Some a.
Proof.
  intros. destruct n; cbn; now rewrite H.
Qed.

Fixpoint loop_informative (A : Type) (n : nat) (f : A -> A) (p : A -> bool) a : A + A :=
  if p a then inr a else
    match n with
    | 0 => inl a
    | S n => loop_informative n f p (f a)
    end.

Lemma loop_informative_spec A n f p (a : A) r : loop_informative n f p a = inr r <-> loop n f p a = Some r.
Proof.
  revert a r. induction n; intros; cbn in *.
  - destruct (p a) eqn:E; firstorder congruence.
  - destruct (p a) eqn:E.
    + firstorder congruence.
    + now rewrite IHn.
Qed.

Lemma loop_ext A f f' p p' (a : A) k :
  (forall a, p a = false -> f a = f' a) ->
  (forall a, p a = p' a) ->
  loop k f p a = loop k f' p a.
Proof.
  intros H. revert a. induction k; intros a; cbn; auto. destruct (p a) eqn:E; auto. rewrite H; auto.
Qed.

Lemma loop_ge A f p (a c : A) k1 k2 : k2 >= k1 -> loop k1 f p a = Some c -> loop k2 f p a = Some c.
Proof.
  revert a k2; induction k1; intros; cbn in *.
  - destruct k2; cbn; destruct (p a); now inv H0.
  - destruct (p a) eqn:E; inv H0.
    + destruct k2; cbn; rewrite E; reflexivity.
    + rewrite H2. destruct k2; [omega | ].
      cbn. rewrite E. rewrite IHk1; eauto. omega.
Qed.


Lemma loop_lift A B k lift f g h hlift (c1 c2 : A):
  (forall x , hlift (lift x) = h x) ->
  (forall x, h x = false -> lift (f x) = g (lift x)) ->
  loop k f h c1 = Some c2 ->
  loop (A := B) k g hlift (lift c1) = Some (lift c2).
Proof.
  revert c1; induction k; intros; cbn in *; rewrite H; destruct h eqn:E; inv H1; rewrite <- ?H0; eauto.
Qed.

Lemma loop_merge A f p q k1 k2 (a1 a2 a3 : A):
  (forall b, p b = false -> q b = false) ->
  loop k1 f p a1 = Some a2 ->
  loop k2 f q a2 = Some a3 ->
  loop (k1+k2) f q a1 = Some a3.
Proof.
  revert a1 a2 a3 k2. induction k1; intros; cbn in *.
  - now destruct p eqn:E; inv H0.
  - destruct (p a1) eqn:E.
    + inv H0. eapply (loop_ge (k2 := S (k1 + k2))) in H1. now rewrite <- H1. omega.
    + destruct (q a1) eqn:E1; try firstorder congruence. erewrite IHk1; eauto.
Qed.

Lemma loop_split A f p q k (a1 a3 : A):
  (forall b, p b = false -> q b = false) ->
  loop k f q a1 = Some a3 -> 
  exists k1 a2 k2, loop k1 f p a1 = Some a2 /\
              loop k2 f q a2 = Some a3 /\ k=k1+k2.  
Proof.
  intros weakens. revert a1. apply complete_induction with (x:=k);clear k; intros k IH a1 E.
  destruct k.
  -simpl in *.
   eexists 0,a1,0. cbn. destruct q eqn:Eq; inv E.
   destruct (p a3) eqn:E1.
   +auto.
   +apply weakens in E1. congruence.
  -cbn in E. destruct (p a1) eqn:Eq.
   +exists 0 ,a1,(1+k). now rewrite loop_fulfills_p_0.
   +rewrite (weakens _ Eq) in E.
    eapply IH in E as (k1&a2&k2&Eq1&Eq2&->);[ |omega].
    exists (1+k1), a2, k2; intuition.
    cbn. now rewrite Eq.
Qed.

Lemma loop_unlift A B f p f' p' (unlift : B -> option A):
  (forall a b, unlift b = Some a -> p a = false -> unlift (f' b) = Some (f a)) ->
  (forall a b, unlift b = Some a -> p a = p' b) ->
  forall a b,
  unlift b = Some a -> 
  forall i x',
  loop i f' p' b = Some x' ->
  exists x, loop i f p a = Some x /\ Some x = unlift x'.
Proof.
  intros Hf Hp a b Ha i x'. revert a b Ha x'. induction i; intros a b Ha x' Hl; cbn in *.
  - destruct (p' b) eqn:E; rewrite (Hp _ _ Ha) in *; inv Hl. rewrite E. eauto.
  - destruct (p' b) eqn:E; rewrite (Hp _ _ Ha) in *; inv Hl.
    + rewrite E. eauto.
    + rewrite E. eapply IHi; eauto.
Qed.

Section Fix_X.

  Variable X : Type.
  Fixpoint inb eqb (x:X) (A: list X) :=
    match A with
      List.nil => false
    | a::A' => orb (eqb a x) (inb eqb x A')
    end.

  Lemma inb_spec eqb: (forall (x y:X), Bool.reflect (x=y) (eqb x y)) -> forall x A, Bool.reflect (List.In x A) (inb eqb x A).
  Proof.
    intros R x A. induction A; firstorder; cbn.
    destruct (R a x); inv IHA; cbn; firstorder.
    constructor; tauto.
  Qed.

End Fix_X.


(* Apply functions in typles, options, etc. *)
Section Map.
  Variable X Y Z : Type.
  Definition map_opt : (X -> Y) -> option X -> option Y :=
    fun f a =>
      match a with
      | Some x => Some (f x)
      | None => None
      end.

  Definition map_inl : (X -> Y) -> X + Z -> Y + Z :=
    fun f a =>
      match a with
      | inl x => inl (f x)
      | inr y => inr y
      end.

  Definition map_inr : (Y -> Z) -> X + Y -> X + Z :=
    fun f a =>
      match a with
      | inl y => inl y
      | inr x => inr (f x)
      end.

  Definition map_left  : (X -> Z) -> X * Y -> Z * Y := fun f '(x,y) => (f x, y).
  Definition map_right : (Y -> Z) -> X * Y -> X * Z := fun f '(x,y) => (x, f y).
End Map.



(** We often use
<<
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
>>
in runtime proofs. However, if we then use [Fin.R], this can brake proofs, since the [plus] in the type of [Fin.R] doesn't simplify with [cbn] any more. To avoid this problem, we simply have a copy of [Fin.R] and [plus], that isn't affected by these commands.
*)
Fixpoint plus' (n m : nat) { struct n } : nat :=
  match n with
  | 0 => m
  | S p => S (plus' p m)
  end.

Fixpoint FinR {m} n (p : Fin.t m) : Fin.t (plus' n m) :=
  match n with
  | 0 => p
  | S n' => Fin.FS (FinR n' p)
  end.