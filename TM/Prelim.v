Require Export Shared.FiniteTypes.FinTypes Shared.FiniteTypes.BasicFinTypes Shared.FiniteTypes.CompoundFinTypes Shared.FiniteTypes.VectorFin Shared.Tactics.AutoIndTac.
Require Export Shared.Extra Shared.Base.
Require Export Program.Equality.

Require Export smpl.Smpl.


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

Require Import Vector.

Fixpoint repeatVector (m : nat) (X : Type) (x : X) : Vector.t X m :=
  match m with
  | 0 => Vector.nil X
  | S m0 => Vector.cons X x m0 (repeatVector m0 x)
  end.

(** * Functions *)

Definition compose {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

Hint Unfold compose.

(*Notation " g ∘ f " := (compose g f) (at level 40, left associativity).*)


(** * Some missing Vector functions *)

Tactic Notation "dependent" "destruct'" constr(V) :=
  match type of V with
  | Vector.t ?Z 0 =>
    revert all except V;
    pattern V; revert V;
    eapply case0; intros
  | Vector.t ?Z (S ?n) =>
    revert all except V;
    pattern V; revert n V;
    eapply caseS; intros
  | Fin.t 0 => inv V
  | Fin.t (S ?n) =>
    let pos := V in
    revert all except pos;
    pattern pos; revert n pos;
    eapply Fin.caseS; intros
  | _ => fail "Wrong type"
  end.

Tactic Notation "dependent" "destruct" constr(V) :=
  match type of V with
  | Vector.t ?Z (S ?n) =>
    revert all except V;
    pattern V; revert n V;
    eapply caseS; intros
  | Fin.t 0 => inv V
  | Fin.t (S ?n) =>
    let pos := V in
    revert all except pos;
    pattern pos; revert n pos;
    eapply Fin.caseS; intros
  | _ => fail "Wrong type"
  end.


Lemma destruct_vector_nil (X : Type) :
  forall v : Vector.t X 0, v = [||]%vector_scope.
Proof.
  intros H. dependent destruction H. reflexivity.
Qed.

Lemma destruct_vector_cons (X : Type) (n : nat) :
  forall v : Vector.t X (S n), { h : X & { v' : Vector.t X n | v = h ::: v' }} % vector_scope.
Proof.
  intros H. dependent destruction H. eauto.
Qed.

(* Destruct a vector of known size *)
Ltac destruct_vector :=
  repeat match goal with
         | [ v : Vector.t ?X 0 |- _ ] =>
           let H  := fresh "Hvect" in
           pose proof (@destruct_vector_nil X v) as H;
           subst v
         | [ v : Vector.t ?X (S ?n) |- _ ] =>
           let h  := fresh "h" in
           let v' := fresh "v'" in
           let H  := fresh "Hvect" in
           pose proof (@destruct_vector_cons X n v) as (h&v'&H);
           subst v; rename v' into v
         end.

Goal True. (* test *)
Proof.
  pose proof (([|1;2;3;4;5;6|]%vector_scope)) as v.
  destruct_vector.
  pose proof (([| [ 1;2;3] ; [ 4;5;6] |]%vector_scope)) as v'.
  destruct_vector.
  pose proof (([| [ 1;2;3] |]%vector_scope)) as v''.
  destruct_vector.
Abort.

Section In_nth.
  Variable (A : Type) (n : nat).

  Lemma vect_nth_In (v : Vector.t A n) (i : Fin.t n) (x : A) :
    Vector.nth v i = x -> Vector.In x v.
  Proof.
    induction n; cbn in *.
    - inv i.
    - dependent destruct v. dependent destruct i; cbn in *; subst; econstructor; eauto.
  Qed.

  Lemma vect_nth_In' (v : Vector.t A n) (x : A) :
    Vector.In x v -> exists i : Fin.t n, Vector.nth v i = x.
  Proof.
    induction n; cbn in *.
    - inversion 1.
    - dependent destruct v. inv H.
      + apply EqdepFacts.eq_sigT_eq_dep in H3. induction H3. exists Fin.F1. auto.
      + apply EqdepFacts.eq_sigT_eq_dep in H3. induction H3. specialize (IHn0 _ H2) as (i&<-). exists (Fin.FS i). auto.
  Qed.

End In_nth.


Section tabulate_vec.

  Variable X : Type.

  Fixpoint tabulate_vec (n : nat) (f : Fin.t n -> X) {struct n} : Vector.t X n.
  Proof.
    destruct n.
    - apply Vector.nil.
    - apply Vector.cons.
      + apply f, Fin.F1.
      + apply tabulate_vec. intros m. apply f, Fin.FS, m.
  Defined.

  Lemma nth_tabulate n (f : Fin.t n -> X) (m : Fin.t n) :
    Vector.nth (tabulate_vec f) m = f m.
  Proof.
    induction m.
    - cbn. reflexivity.
    - cbn. rewrite IHm. reflexivity.
  Qed.
  
  Lemma in_tabulate n (f : Fin.t n -> X) (x : X) :
    In x (tabulate_vec (n := n) f) <-> exists i : Fin.t n, x = f i.
  Proof.
    split.
    {
      revert f x. induction n; intros f x H.
      - cbn in *. inv H.
      - cbn in *. dependent induction H.
        + eauto.
        + specialize (IHn (fun m => f (Fin.FS m)) _ H) as (i&IH). eauto.
    }
    {
      intros (i&Hi). induction i; cbn in *; subst; econstructor; eauto.
    }
  Qed.

End tabulate_vec.

Lemma vec_replace_nth X x n (t : Vector.t X n) (i : Fin.t n) :
  x = Vector.nth (Vector.replace t i x) i.
Proof.
  induction i; dependent destruct t; simpl; auto.
Qed.

Lemma vec_replace_nth_nochange X x n (t : Vector.t X n) (i j : Fin.t n) :
  Fin.to_nat i <> Fin.to_nat j -> Vector.nth t i = Vector.nth (Vector.replace t j x) i.
Proof.
  revert j. induction i; dependent destruct t; dependent destruct j; simpl; try tauto.
  apply IHi. contradict H. cbn. now rewrite !H.
Qed.

Instance Fin_eq_dec n : eq_dec (Fin.t n).
Proof.
  intros; hnf.
  destruct (Fin.eqb x y) eqn:E.
  - left. now eapply Fin.eqb_eq.
  - right. intros H. eapply Fin.eqb_eq in H. congruence.
Defined.


Ltac getFin i j := apply (Fin.of_nat_lt (ltac:(omega) : i < j)).
Definition bool2nat := fun b : bool => if b then 1 else 0.
Coercion bool2nat : bool >-> nat.




(* Apply functions in typles, options, etc. *)
Section Translate.
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
End Translate.

(* Show the non-dependent hypothesis of a hypothesis that is a implication and specialize it *)
Tactic Notation "spec_assert" hyp(H) :=
  let H' := fresh in
  match type of H with
  | ?A -> _ =>
    assert A as H'; [ | specialize (H H'); clear H']
  end.

Tactic Notation "spec_assert" hyp(H) "by" tactic(T) :=
  let H' := fresh in
  match type of H with
  | ?A -> _ =>
    assert A as H' by T; specialize (H H'); clear H'
  end.


(* Dupfree vector *)

Global Open Scope vector_scope.

Inductive dupfree X : forall n, Vector.t X n -> Prop :=
  dupfreeVN :
    dupfree (@Vector.nil X)
| dupfreeVC n (x : X) (V : Vector.t X n) :
    ~ Vector.In x V -> dupfree V -> dupfree (x ::: V).
  

Ltac existT_eq :=
  match goal with
  | [ H: existT ?X1 ?Y1 ?Z1 = existT ?X2 ?Y2 ?Z2 |- _] =>
    apply EqdepFacts.eq_sigT_iff_eq_dep in H; inv H
  end.

Ltac existT_eq' :=
  match goal with
  | [ H: existT ?X1 ?Y1 ?Z1 = existT ?X2 ?Y2 ?Z2 |- _] =>
    apply EqdepFacts.eq_sigT_iff_eq_dep in H; induction H
  end.


Ltac vector_not_in_step :=
  match goal with
  | _ => progress destruct_vector
  | [ H: Vector.In ?X ?Y |- _ ] => inv H
  | _ => existT_eq
  end.

Ltac vector_not_in := repeat intro; repeat vector_not_in_step.

Goal ~ Vector.In 10 [|1;2;4|].
Proof.
  vector_not_in.
Qed.

Ltac vector_dupfree :=
  match goal with
  | [ |- dupfree (Vector.nil _) ] =>
    constructor
  | [ |- dupfree (?a ::: ?bs)%vector_scope ] =>
    constructor; [vector_not_in | vector_dupfree]
  end.

Goal dupfree [| 4; 8; 15; 16; 23; 42 |].
Proof. vector_dupfree. Qed.

Goal dupfree [| Fin.F1 (n := 1) |].
Proof. vector_dupfree. Qed.

Lemma dupfree_cons (X : Type) (n : nat) (x : X) (xs : Vector.t X n) :
  dupfree (x ::: xs) -> dupfree xs /\ ~ In x xs.
Proof.
  intros H1. inv H1. now existT_eq'.
Qed.

Lemma dupfree_tabulate_functional (X : Type) (n : nat) (f : Fin.t n -> X) :
  (forall x y, f x = f y -> x = y) ->
  dupfree (tabulate_vec f).
Proof.
  intros H. revert f H. induction n; intros; cbn.
  - constructor.
  - constructor.
    + intros (x & H2 % H) % in_tabulate. congruence.
    + eapply IHn. now intros x y -> % H % Fin.FS_inj.
Qed.

Lemma In_cons (X : Type) (n : nat) (x y : X) (xs : Vector.t X n) :
  In y (x ::: xs) -> x = y \/ In y xs.
Proof.
  intros H. inv H; existT_eq'; tauto.
Qed.

Lemma In_replace (X : Type) (n : nat) (xs : Vector.t X n) (i : Fin.t n) (x y : X) :
  In y (replace xs i x) -> (x = y \/ In y xs).
Proof.
  revert i x y. induction xs; intros; cbn in *.
  - inv i.
  - dependent destruct i; cbn in *; apply In_cons in H as [-> | H]; auto; try now (right; constructor).
    specialize (IHxs _ _ _ H) as [-> | IH]; [ now left | right; now constructor ].
Qed.

Lemma In_replace' (X : Type) (n : nat) (xs : Vector.t X n) (i : Fin.t n) (x y : X) :
  In y (replace xs i x) -> x = y \/ exists j, i <> j /\ xs[@j] = y.
Proof.
  revert i x y. induction xs; intros; cbn -[nth] in *.
  - inv i.
  - dependent destruct i; cbn -[nth] in *.
    + apply In_cons in H as [->|H].
      * tauto.
      * apply vect_nth_In' in H as (j&H). right. exists (Fin.FS j). split. discriminate. cbn. assumption.
    + apply In_cons in H as [->|H].
      * right. exists Fin.F1. split. discriminate. cbn. reflexivity.
      * specialize (IHxs _ _ _ H) as [-> | (j&IH1&IH2)]; [ tauto | ].
        right. exists (Fin.FS j). split. now intros -> % Fin.FS_inj. cbn. assumption.
Qed.

Lemma dupfree_replace (X : Type) (n : nat) (xs : Vector.t X n) (x : X) :
  dupfree xs -> ~ In x xs -> forall i, dupfree (replace  xs i x).
Proof.
  revert x. induction xs; intros; cbn.
  - inv i.
  - dependent destruct i; cbn.
    + constructor; auto.
      * intros H1. contradict H0. now econstructor.
      * inv H. existT_eq'. assumption.
    + apply dupfree_cons in H as (H&H').
      assert (~In x xs).
      {
        intros H1. contradict H0. now constructor.
      }
      specialize (IHxs x H H1 p). constructor.
      * intros [ -> | H2] % In_replace. contradict H0. constructor. tauto.
      * tauto.
Qed.

Coercion Vector.to_list : Vector.t >-> list.

Lemma tolist_In (X : Type) (n : nat) (xs : Vector.t X n) (x : X) :
  Vector.In x xs <-> List.In x xs.
Proof.
  split; intros H.
  - induction H; cbn; auto.
  - induction xs; cbn in *; auto. destruct H as [-> | H]; econstructor; eauto.
Qed.

Lemma tolist_dupfree (X : Type) (n : nat) (xs : Vector.t X n) :
  dupfree xs -> Dupfree.dupfree xs.
Proof.
  induction 1.
  - cbn. constructor.
  - cbn. constructor; auto. intros H1. contradict H. now apply tolist_In.
Qed.


Instance Fin_finTypeC n : finTypeC (EqType (Fin.t n)).
Proof.
  pose (enum := tabulate_vec (fun i : Fin.t n => i)).
  pose (enum' := Vector.to_list enum).
  constructor 1 with (enum := enum').
  intros x. cbn in x.
  eapply dupfreeCount.
  - subst enum'. eapply tolist_dupfree. eapply dupfree_tabulate_functional; eauto.
  - eapply tolist_In. subst enum. eapply in_tabulate. eauto.
Qed.

Section Count.
  Variable (X : eqType).

  Definition count (n : nat) (x : X) (xs : t X n) :=
    fold_right (fun y c => if Dec (x = y) then S c else c) xs 0.

  Lemma count0_notIn (n : nat) (x : X) (xs : t X n) :
    count x xs = 0 -> ~ In x xs.
  Proof.
    revert x. induction xs; intros; cbn in *.
    - vector_not_in.
    - intros H1. decide (x=h); try congruence.
      apply In_cons in H1 as [-> | H1]; try tauto.
      eapply IHxs; eauto.
  Qed.

  Lemma count0_notIn' (n : nat) (x : X) (xs : t X n) :
    ~ In x xs -> count x xs = 0.
  Proof.
    induction xs; intros; cbn in *.
    - reflexivity.
    - decide (x = h) as [ -> | D ].
      + contradict H. constructor.
      + apply IHxs. intros H2. contradict H. now constructor.
  Qed.

  Lemma countDupfree (n : nat) (xs : t X n) :
    (forall x : X, In x xs -> count x xs = 1) <-> dupfree xs.
  Proof.
    split; intros H.
    {
      induction xs; cbn -[count] in *.
      - constructor.
      - constructor.
        + intros H2. specialize (H h ltac:(now constructor)). cbn in H.
          decide (h = h); try tauto. inv H.
          contradict H2. now eapply count0_notIn.
        + apply IHxs. intros x Hx. specialize (H x ltac:(now constructor)).
          cbn in H. decide (x = h); inv H; auto. rewrite H1.
          contradict Hx. now eapply count0_notIn.
    }
    {
      induction H as [ | n x' xs HIn HDup IH ]; intros; cbn in *.
      - inv H.
      - decide (x = x') as [ -> | D].
        + f_equal. exact (count0_notIn' HIn).
        + apply (IH x). now apply In_cons in H as [ -> | H].
    }
  Qed.


(* (* Test *)
End Count.
Compute let xs := [|1;2;3;4;5;6|] in
        let x  := 2 in
        let y  := 1 in
        let i  := Fin.F1 in
        Dec (x = y) + count x xs = Dec (x = xs[@i]) + count x (replace xs i y).
*)

  Lemma replace_nth (n : nat) (xs : Vector.t X n) (p : Fin.t n) :
    replace xs p xs[@p] = xs.
  Proof.
    eapply eq_nth_iff. intros ? ? <-.
    decide (p = p1) as [ -> | D].
    - now rewrite Vector_replace_nth.
    - now rewrite Vector_replace_nth2.
  Qed.
  
  Lemma count_replace (n : nat) (xs : t X n) (x y : X) (i : Fin.t n) :
    Dec (x = y) + count x xs = Dec (x = xs[@i]) + count x (replace xs i y).
  Proof.
    induction xs; intros; cbn -[nth count] in *.
    - inv i.
    - dependent destruct i; cbn -[nth count] in *.
      + decide (x = y) as [ D | D ]; cbn -[nth count] in *; cbn -[bool2nat dec2bool count].
        * rewrite <- D in *. decide (x = h) as [ -> | D2]; cbn [dec2bool bool2nat plus]; auto.
          cbv [count]. cbn. rewrite D. decide (y = y); try tauto. decide (y = h); congruence.
        * decide (x = h); subst; cbn [bool2nat dec2bool plus]; cbv [count]; try reflexivity.
          -- cbn. decide (h = h); try tauto. decide (h = y); tauto.
          -- cbn. decide (x = h); try tauto. decide (x = y); tauto.
      + cbn. decide (x = y); cbn.
        * decide (x = h); cbn; f_equal.
          -- decide (x = xs[@p]); cbn; repeat f_equal; subst.
             ++ symmetry. now apply replace_nth.
             ++ cbn in *. specialize (IHxs p). decide (h = xs[@p]); tauto.
          -- decide (x = xs[@p]); cbn; repeat f_equal; subst.
             ++ symmetry. now apply replace_nth.
             ++ cbn in *. specialize (IHxs p). decide (y = xs[@p]); tauto.
        * decide (x = h); cbn; f_equal.
          -- decide (x = xs[@p]); cbn; f_equal; subst.
             ++ cbn in *. specialize (IHxs p). decide (xs[@p] = xs[@p]); cbn in *; try tauto.
             ++ specialize (IHxs p). cbn in *. decide (h = xs[@p]); cbn in *; tauto.
          -- decide (x = xs[@p]); cbn; auto.
             ++ specialize (IHxs p). cbn in *. decide (x = xs[@p]); cbn in *; tauto.
             ++ specialize (IHxs p). cbn in *. decide (x = xs[@p]); cbn in *; tauto.
  Qed.
  
End Count.

Lemma dupfree_nth_injective (X : Type) (n : nat) (xs : Vector.t X n) :
  dupfree xs -> forall (i j : Fin.t n), xs[@i] = xs[@j] -> i = j.
Proof.
  induction 1; intros; cbn -[nth] in *.
  - inv i.
  - dependent destruct i; dependent destruct j; cbn -[nth] in *; auto.
    + cbn in *. contradict H. eapply vect_nth_In; eauto.
    + cbn in *. contradict H. eapply vect_nth_In; eauto.
    + f_equal. now apply IHdupfree.
Qed.