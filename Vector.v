Require Import Eqdep_dec.
Require Export Shared.Base.

Delimit Scope vector_scope with vector.
Open Scope vector_scope.

(** ** Vector **)

Module Vector.
  Structure vector (A:Type) (size:nat) : Type := Vector
    {
      Vector_vec  :> list A;
      Vector_size : length Vector_vec = size
    }.
  Arguments Vector {A} size enum _ : rename.

  (* Record member (A : Type) (size : nat) (Vec : vector A size) :=
    {
      member_element :> A;
      member_element_in : member_element el Vector_vec Vec
    }. *)


  (* Interesting :) *)
  Theorem vector_eq {X: Type} {size:nat} (A B : vector X size) :
    Vector_vec (size := size) A = Vector_vec (size := size) B -> A = B.
  Proof.
    intros H. destruct A as [vecA HsizeA], B as [vecB HsizeB].
    cbn in H. subst.
    enough (eq_refl = HsizeB) by congruence.
    pose proof Eqdep_dec.eq_proofs_unicity as PI.
    apply PI with (p2 := HsizeB).
    intros x y. omega.
  Qed.

  Definition make_vector {A:Type} (xs:list A) := @Vector A (length xs) xs eq_refl.


  Section Map.
    Definition vector_map {A B : Type} {size: nat} (f: A -> B) (vec : vector A size) : vector B size.
    Proof.
      destruct vec as [xs Hsize]. apply (@Vector B size (map f xs)). destruct Hsize. apply map_length.
    Defined.

    Lemma vector_map_eq_id {A : Type} {size: nat} (f : A -> A) (vec : vector A size) :
      (forall x, f x = x) -> vector_map f vec = vec.
    Proof.
      intros H. apply vector_eq.
      destruct vec as [vect Hsize].
      unfold vector_map.
      cbn.
      clear Hsize. clear size. 
      induction vect; cbn; auto.
      rewrite H. f_equal. assumption.
    Qed.

    Lemma map_map { A B C : Type } (f : B -> C) (g : A -> B) (xs : list A) :
      map f (map g xs) = map (fun x => f (g x)) xs.
    Proof.
      induction xs as [|x xs' IH].
      - reflexivity.
      - cbn. f_equal. congruence.
    Qed.

    Lemma vector_map_map_eq { A B C : Type } {size: nat} (f : B -> C) (g : A -> B) (vec : vector A size) :
      vector_map f (vector_map g vec) = vector_map (fun x => f (g x)) vec.
    Proof.
      destruct vec as [xs HsizeA]. apply vector_eq. cbn. unfold Vector_vec; cbn. apply map_map.
    Qed.

    Lemma vector_in_map_iff {A B : Type} {size : nat} (f : A -> B) (vec : vector A size) (y : B) :
      y el vector_map f vec <-> (exists x : A, f x = y /\ x el vec).
    Proof.
      destruct vec as [xs HsizeA]. unfold Vector_vec; cbn. apply in_map_iff.
    Qed.

    Lemma in_doublemap_iff {A B C : Type} (f : B -> C) (g : A -> B) (xs : list A) (z : C) :
      z el map f (map g xs) <-> (exists y, f y = z /\ exists x, g x = y /\ x el xs).
    Proof.
      split.
      - induction xs as [|x xs' IH]; cbn; [tauto|].
        intros [H|H].
        + exists (g x). eauto.
        + specialize (IH H). destruct IH as (y&H'&x'&H''&H'''). exists (y). eauto.
      - induction xs as [|x xs' IH]; cbn; [now intros (y&_&x&_&H)|].
        intros (y&H&x'&H'&[->|H'']).
        + left. congruence.
        + right. apply IH. eauto.
    Qed.

    Lemma vector_in_double_map_iff {A B C : Type} {size : nat} (f : B -> C) (g : A -> B)  (vec : vector A size) (z : C) :
      z el vector_map f (vector_map g vec) <-> (exists y : B, f y = z /\ exists x : A, g x = y /\ x el vec).
    Proof.
      destruct vec as [xs HsizeA]. unfold Vector_vec; cbn. apply in_doublemap_iff.
    Qed.


  End Map.

  Section Map2.
      Fixpoint map2 {A B C : Type} (f : A -> B -> C) xs ys :=
          match xs, ys with
          | nil, _ => nil
          | _, nil => nil
          | (x::xs'), (y::ys') => f x y :: map2 f xs' ys'
          end.

      Lemma map2_size_min {A B C : Type} (f : A -> B -> C) (xs : list A) (ys : list B) :
        length (map2 f xs ys) = Nat.min (length xs) (length ys).
      Proof.
        revert ys; induction xs as [|x xs' IH]; intros ys; cbn.
        - reflexivity.
        - destruct ys as [|y ys']; cbn.
          + reflexivity.
          + f_equal. apply IH.
      Qed.

      Lemma map2_size_same {A B C : Type} (f : A -> B -> C) (xs : list A) (ys : list B) :
        length xs = length ys -> length xs = length (map2 f xs ys).
      Proof. intros H. rewrite map2_size_min. rewrite H. now rewrite Nat.min_id. Qed.

      Definition vector_map2 {A B C : Type} {size:nat} (f : A -> B -> C) (vec1 : vector A size) (vec2 : vector B size) :
        vector C size.
      Proof.
        destruct vec1 as [xs Hs1], vec2 as [ys Hs2]. apply (@Vector C size (map2 f xs ys)).
        destruct Hs1. symmetry. apply map2_size_same. symmetry. assumption.
      Defined.

      Lemma vector_map2_eq_id {A B : Type} (f : A -> B -> A) (size : nat) (vec1 : vector A size) (vec2 : vector B size) :
        (forall x y, x el vec1 -> y el vec2 -> f x y = x) -> vector_map2 f vec1 vec2 = vec1.
      Proof.
        intros H.
        destruct vec1 as [xs Hsize1], vec2 as [ys Hsize2].
        apply vector_eq; cbn.
        subst. revert H. revert Hsize2. revert ys. induction xs as [|x xs' IH]; intros ys Hsize H.
        - reflexivity.
        - cbn. destruct ys; cbn in *; auto; [omega|].
          injection Hsize. intros Hsize'.
          specialize (IH ys). rewrite IH.
          + f_equal. apply H; auto.
          + congruence.
          + intros x' y' Hx' Hy'. apply H; auto.
      Qed.

      Lemma vector_map2_eq_id' {A B : Type} (size : nat) (f : A -> B -> B) (vec1 : vector A size) (vec2 : vector B size) :
        (forall x y, x el vec1 -> y el vec2 -> f x y = y) -> vector_map2 f vec1 vec2 = vec2.
      Proof.
        intros H.
        destruct vec1 as [xs Hsize1], vec2 as [ys Hsize2].
        apply vector_eq; cbn.
        subst. revert H. revert Hsize2. revert xs. induction ys as [|y ys' IH]; intros xs Hsize H.
        - destruct xs; reflexivity.
        - cbn. destruct xs; cbn in *; auto; [omega|].
          injection Hsize. intros Hsize'.
          specialize (IH xs). rewrite IH.
          + f_equal. apply H; auto.
          + congruence.
          + intros x' y' Hx' Hy'. apply H; auto.
      Qed.

      Lemma vector_map2_map_eq_id {A B C : Type} (size : nat) (f : A -> C -> A) (g : B -> C) (vec1 : vector A size) (vec2 : vector B size) :
        (forall x y, x el vec1 -> y el vec2 -> f x (g y) = x) -> vector_map2 f vec1 (vector_map g vec2) = vec1.
      Proof.
        intros H.
        destruct vec1 as [xs Hsize1], vec2 as [ys Hsize2].
        apply vector_eq; cbn.
        subst. revert H. revert Hsize2. revert ys. induction xs as [|x xs' IH]; intros ys Hsize H.
        - reflexivity.
        - cbn. destruct ys; cbn in *; auto; [omega|].
          injection Hsize. intros Hsize'.
          specialize (IH ys). rewrite IH.
          + f_equal. apply H; auto.
          + congruence.
          + intros x' y' Hx' Hy'. apply H; auto.
      Qed.

      Lemma map2_map__L { A B C D : Type} (f : B -> C -> D) (g : A -> B) (xs : list A) (ys : list C) :
        map2 f (map g xs) ys = map2 (fun b => fun c => f (g b) c) xs ys.
      Proof.
        revert ys; induction xs as [|x xs' IH]; intros ys; cbn.
        - reflexivity.
        - destruct ys as [|y ys']; cbn; congruence.
      Qed.

      Lemma map2_map__R { A B C D : Type} (f : B -> C -> D) (g : A -> C) (xs : list B) (ys : list A) :
        map2 f xs (map g ys) = map2 (fun b => fun c => f b (g c)) xs ys.
      Proof.
        revert ys; induction xs as [|x xs' IH]; intros ys; cbn.
        - reflexivity.
        - destruct ys as [|y ys']; cbn; congruence.
      Qed.

      Lemma vector_map2_mapL_eq_id { A B C D : Type } {size : nat} (f : B -> C -> D) (g : A -> B)
            (vec__x : vector A size) (vec__y : vector C size) :
        vector_map2 f (vector_map g vec__x) vec__y = vector_map2 (fun b => fun c => f (g b) c) vec__x vec__y.
      Proof.
        destruct vec__x as [xs Hsize1], vec__y as [ys Hsize2]. apply vector_eq; cbn. subst. apply map2_map__L.
      Qed.
      
      Lemma vector_map2_mapR_eq_id { A B C D : Type } {size : nat} (f : B -> C -> D) (g : A -> C)
            (vec__x : vector B size) (vec__y : vector A size) :
        vector_map2 f vec__x (vector_map g vec__y) = vector_map2 (fun b => fun c => f b (g c)) vec__x vec__y.
      Proof.
        destruct vec__x as [xs Hsize1], vec__y as [ys Hsize2]. apply vector_eq; cbn. subst. apply map2_map__R.
      Qed.


      Lemma map2_simple_map { A B : Type } (f : A -> A -> B) (xs : list A) :
        map2 f xs xs = map (fun a => f a a) xs.
      Proof. induction xs; cbn; congruence. Qed.

      Lemma vector_map2_simple_map { A B : Type } {size : nat} (f : A -> A -> B) (vec : vector A size) :
        vector_map2 f vec vec = vector_map (fun a => f a a) vec.
      Proof. destruct vec as [xs Hsize]. apply vector_eq; cbn. subst. apply map2_simple_map. Qed.
      

  End Map2.



  Section Tabulate.
    Variables (A : Type) (f : nat -> A).
    
    Fixpoint tabulate n :=
      match n with
      | O => nil
      | S n' => f n' :: tabulate n'
      end.

    (* Compute tabulate 3. *)

    Lemma tabulate_length n : | tabulate n | = n.
    Proof. induction n; cbn; omega. Qed.
    
  End Tabulate.

  Definition vector_tabulate {A : Type} (f : nat -> A) (size : nat) : vector A size.
  Proof. apply (Vector size (tabulate f size)), tabulate_length. Defined.


  (** Decidability **)
  Instance vec_dec_eq {X : eqType} {size : nat} : eq_dec (vector X size).
  Proof.
    intros [xs sizeXs] [ys siezYs]. decide (xs = ys); [left|right].
    - apply vector_eq. assumption.
    - intros H. injection H. auto.
  Qed.

  
End Vector.