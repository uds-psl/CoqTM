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
  if p a then Some a else
    match n with
    | O => None
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

Lemma loop_fulfills_p A n f p (a : A) c : loop n f p a = Some c -> p c = true.
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


Section LoopLift.

  Variable A B : Type. (* Abstract states *)
  (* Variable I : Retract A B. (* Lifting between states *) *)
  Variable lift : A -> B.
  Variable (f : A -> A) (f' : B -> B). (* Abstract steps *)
  Variable (h : A -> bool) (h' : B -> bool). (* Abstract halting states *)

  (*
  Notation lift := (Retr_f (Retract := I)).
  Notation unlift := (Retr_g (Retract := I)).
   *)

  Hypothesis halt_lift_comp : forall x:A, h' (lift x) = h x.
  Hypothesis step_lift_comp : forall x:A, h x = false -> f' (lift x) = lift (f x).

  Lemma loop_lift (k : nat) (c1 c2 : A) :
    loop (A := A) k f  h  c1        = Some c2 ->
    loop (A := B) k f' h' (lift c1) = Some (lift c2).
  Proof.
    revert c1. induction k as [ | k']; intros; cbn in *.
    - rewrite halt_lift_comp. destruct (h c1); now inv H.
    - rewrite halt_lift_comp. destruct (h c1) eqn:E.
      + now inv H.
      + rewrite step_lift_comp by auto. now apply IHk'.
  Qed.



  Lemma loop_unlift (k : nat) (a : A) (b' : B) :
    loop k f' h' (lift a) = Some b' ->
    exists b : A, loop k f h a = Some b /\ b' = lift b.
  Proof.
    revert a b'. induction k as [ | k']; intros; cbn in *.
    - rewrite halt_lift_comp in H.
      exists a. destruct (h a) eqn:E; now inv H.
    - rewrite halt_lift_comp in H.
      destruct (h a) eqn:E.
      + exists a. now inv H.
      + rewrite step_lift_comp in H by assumption.
        specialize IHk' with (1 := H) as (x&IH&->). now exists x.
  Qed.
    
End LoopLift.


Section LoopMerge.

  Variable A : Type. (** abstract states *)
  Variable f : A -> A. (** abstract step function *)
  Variable (h h' : A -> bool). (** abstract halting functions *)

  (** Every halting state w.r.t. [h] is also a halting state w.r.t. [h'] *)
  Hypothesis halt_comp : forall a, h a = false -> h' a = false.
    
  Lemma loop_merge (k1 k2 : nat) (c1 c2 c3 : A) :
    loop k1 f h  c1 = Some c2 ->
    loop k2 f h' c2 = Some c3 ->
    loop (k1+k2) f h' c1 = Some c3.
  Proof.
    revert c1 c2 c3. induction k1 as [ | k1' IH]; intros c1 c2 c3 HLoop1 HLoop2; cbn in HLoop1.
    - now destruct (h c1); inv HLoop1.
    - destruct (h c1) eqn:E.
      + inv HLoop1. eapply loop_ge. 2: eauto. omega.
      + cbn. rewrite (halt_comp E). eapply IH; eauto.
  Qed.

  Lemma loop_split (k : nat) (c1 c3 : A) :
    loop k f h' c1 = Some c3 ->
    exists k1 c2 k2,
      loop k1 f h  c1 = Some c2 /\
      loop k2 f h' c2 = Some c3 /\
      k <= k1 + k2.
  Proof.
    revert c1 c3. revert k; refine (size_recursion id _); intros k IH. intros c1 c3 HLoop. cbv [id] in *.
    destruct k as [ | k']; cbn in *.
    - destruct (h' c1) eqn:E; inv HLoop.
      exists 0, c3, 0. cbn. rewrite E.
      destruct (h c3) eqn:E'.
      + auto.
      + apply halt_comp in E'. congruence.
    - destruct (h c1) eqn:E.
      + exists 0, c1, (S k'). cbn. rewrite E. auto.
      + rewrite (halt_comp E) in HLoop.
        apply IH in HLoop as (k1&c2&k2&IH1&IH2&IH3); [ | omega].
        exists (S k1), c2, k2. cbn. rewrite E. repeat split; auto. omega.
  Qed.
  
End LoopMerge.



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