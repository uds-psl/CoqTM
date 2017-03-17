Require Export Base.

(* This is a kind of a set that supports subsets. But it turns out that it is not easy to handle and we don't even need subsets *)
Module SigmaSet.

  Structure sigmaSet := SigmaSet
    {
      sigmaSet_carr : eqType; (* don't coerce this, since it could contain more *)
      sigmaSet_sub  : sigmaSet_carr -> Prop;
      sigmaSet_enum : list sigmaSet_carr;
      sigmaSet_enumeration : forall x, sigmaSet_sub x <-> x el sigmaSet_enum;
      sigmaSet_dupfree : dupfree sigmaSet_enum
    }.
  Arguments SigmaSet {X} sub enum enumeration dupfree : rename.

  Coercion sigmaSet_el {A : sigmaSet} := { a : (sigmaSet_carr A) | @sigmaSet_sub A a }.
  Coercion sigmaSet_el_impl {A: sigmaSet} {a : sigmaSet_carr A} {H : @sigmaSet_sub A a} : sigmaSet_el := exist (@sigmaSet_sub A) a H.

  Canonical Structure sigmaSet_CS car sub enum enumeration dupfree := @SigmaSet car sub enum enumeration dupfree.

  Section Test.
    (* Coercion seems to work as expected. Nice!!! :-) *)
    Variable A : sigmaSet.
    Variable a : A.
    Goal let (b,s) := a in @sigmaSet_sub A b.
      destruct a. assumption.
    Abort.
  End Test.


  (* Disjoint Union *)
  Section Union.

    Definition intersect_type (A B : sigmaSet) := sum (sigmaSet_carr A) (sigmaSet_carr B).

    Instance decide_sum (A B : sigmaSet) : eq_dec (intersect_type A B).
    Proof.
      destruct A, B. unfold intersect_type; cbn.
      intros [x|x] [y|y].
      - unfold dec. decide (x=y) as [->|H]; eauto. right. intros H'. apply H. now inversion H'.
      - right. discriminate.
      - right. discriminate.
      - unfold dec. decide (x=y) as [->|H]; eauto. right. intros H'. apply H. now inversion H'.
    Qed.
    
    Definition union_enum (A B : sigmaSet) :=
      let xs := sigmaSet_enum A in
      let ys := sigmaSet_enum B in
      map inl xs ++ map inr ys.


    Lemma union_enum_dupfree A B :
      dupfree (union_enum A B).
    Proof.
     destruct A, B. unfold union_enum. cbn. apply dupfree_app.
     + intros ([x|y] & (z1&Hz11&Hz12) % in_map_iff & (z2&Hz21&Hz22) % in_map_iff); discriminate.
     + apply dupfree_map; intuition; try congruence. 
     + apply dupfree_map; intuition; congruence.
    Qed.
    
    Definition sigmaSet_union (A B : sigmaSet) : sigmaSet.
    Proof.
      apply (SigmaSet (fun C => match C with inl a => sigmaSet_sub a | inr b => sigmaSet_sub b end) (union_enum A B)).
      - Lemma union_enum_enumeration A B :
          forall x : eqType_CS (decide_sum (B:=B)),
          match x with
          | inl a => sigmaSet_sub a
          | inr b => sigmaSet_sub b
          end <-> x el union_enum A B.
        Proof.
          split.
          - destruct x as [x|x]; intros H; apply in_app_iff; [left|right]; apply in_map_iff; exists x;
              split; auto; [apply A|apply B]; exact H.
          - destruct x as [x|x]; intros H; [apply A|apply B]; apply in_app_iff in H as [(y&H1&H2)%in_map_iff|(y&H1&H2)%in_map_iff];
              congruence; injection H1; intros ->; try assumption.
        Qed. apply union_enum_enumeration.
      - apply union_enum_dupfree.
    Defined.
    Notation "a ⊕ b" := (sigmaSet_union a b) (at level 70) : set_scope.

    (* Instanciate a value of a ⊕ b from a *)
    Definition fromLeft {sigma1 sigma2 : sigmaSet} (s : sigma1) : (sigmaSet_union sigma1 sigma2).
    Proof.
      unfold sigmaSet_union. cbn in *.
      destruct s.
      pose (y := inl x : (sigmaSet_carr sigma1 + sigmaSet_carr sigma2)).
      apply exist with (x := y). apply sigma1. apply sigma1. assumption.
    Defined.

    (* Instanciate a value of a ⊕ b from b *)
    Definition fromRight {sigma1 sigma2 : sigmaSet} (s : sigma2) : (sigmaSet_union sigma1 sigma2).
    Proof.
      unfold sigmaSet_union. cbn in *.
      destruct s.
      pose (y := inr x : (sigmaSet_carr sigma1 + sigmaSet_carr sigma2)).
      apply exist with (x := y). apply sigma2. apply sigma2. assumption.
    Defined.
    
  End Union.

  (* Product Set *)
  Section Product.
    Definition product_type (A B : sigmaSet) := prod (sigmaSet_carr A) (sigmaSet_carr B).

    Definition product_list (X Y : Type) : list X -> list Y -> list (X*Y) :=
      fix product xs ys :=
        match xs with
        | nil => nil
        | x::xs' => map (pair x) ys ++ product xs' ys
        end.

    Definition product_enum (A B : sigmaSet) :=
      let xs := sigmaSet_enum A in
      let ys := sigmaSet_enum B in
      (* undup *) (product_list xs ys). (* undup is not needed any more :-) *)

    Lemma product_list_enumeration (X Y : Type) (xs : list X) (ys : list Y) :
      forall x, forall y, x el xs -> y el ys -> (x, y) el product_list xs ys.
    Proof.
      revert ys. induction xs as [|x' xs IHx]; intros ys; induction ys as [|y' ys IHy]; cbn; auto.
      (* intros x y [->|Hx] [->|Hy]; auto. right. apply in_app_iff. left. apply IHx; auto. *)
      intros x y [->|Hx] [->|Hy]; auto; right; apply in_app_iff. auto.
      - left.  apply in_map_iff. eauto.
      - right. apply IHx; auto.
    Qed.

    Lemma product_list_nil_iff (X Y : Type) (xs : list X) (ys : list Y) :
      (xs = nil \/ ys = nil) <-> product_list xs ys = nil.
    Proof.
      split.
      - intros [->| ->]; cbn; [reflexivity|]. induction xs; cbn; auto.
      - revert ys. induction xs as [|x xs' IHx]; cbn; auto.
        intros ys. intros (H1&H2) % app_eq_nil. right.
        destruct (IHx ys H2) as [->|H]; [|assumption].
        destruct ys; cbn in *; auto. discriminate.
    Qed.

    Lemma product_list_el (X Y : Type) (xs : list X) (ys : list Y) (x : X) (y : Y) :
      (x, y) el product_list xs ys -> x el xs /\ y el ys.
    Proof.
      revert x y ys; induction xs as [|x xs' IHx]; cbn; auto.
      intros x' y ys. intros [(z&H0&H1) % in_map_iff | H] % in_app_iff.
      - injection H0. intros -> ->; auto.
      - specialize (IHx x' y ys H) as [IH1 IH2]. intuition.
    Qed.

    Lemma product_list_dupfree (X Y : Type) (xs : list X) (ys : list Y) :
      dupfree xs -> dupfree ys -> dupfree (product_list xs ys).
    Proof.
      intros H1; revert ys. induction H1 as [|x xs' H1 H2 IH1]; intros ys;
                            induction  1 as [|y ys' H3 H4 IH2]; cbn.
      - constructor. - constructor.
      - apply IH1. constructor.
      - constructor.
        + intros [(z&H5&H6)%in_map_iff|H5]%in_app_iff.
          * injection H5. intros ->. tauto.
          * specialize (IH1 ys' H4). inv IH1.
            -- symmetry in H0. apply product_list_nil_iff in H0. destruct H0 as [-> | ->]; auto.
               apply product_list_el in H5. intuition.
            -- destruct x0 as [a b]. apply product_list_el in H5 as [H7 H8]. auto.
        + apply dupfree_app.
          * intros (a & (b&<-&HbHb) % in_map_iff & (HaHa & [-> | HaHaHa]) % product_list_el); auto.
          * apply dupfree_map. intros y1 y2 Hy1 Hy2. inversion 1; auto. auto.
          * apply IH1. constructor; auto.
    Qed.
    (* That was a verry interesting proof :-) *)


    Definition sigmaSet_product (A B : sigmaSet) : sigmaSet.
    Proof.
      apply (SigmaSet (fun C => match C with (a, b) => sigmaSet_sub a /\ sigmaSet_sub b end) (product_enum A B)).
      - Lemma product_enum_enumeration A B :
          forall x : eqType_CS (prod_eq_dec (eqType_dec (e:=sigmaSet_carr A)) (eqType_dec (e:=sigmaSet_carr B))),
            (let (a, b) := x in sigmaSet_sub a /\ sigmaSet_sub b) <-> x el product_enum A B.
        Proof.
          destruct A, B; unfold product_enum; cbn. split.
          - destruct x as (x&y); intros (H1&H2).
            (* rewrite undup_id_equi. *)
            apply product_list_enumeration; auto; [now apply sigmaSet_enumeration0|now apply sigmaSet_enumeration1].
          - destruct x as (x&y). intros (H1&H2) % product_list_el. split; [now apply sigmaSet_enumeration0|now apply sigmaSet_enumeration1].
        Qed. apply product_enum_enumeration.
      - Lemma product_enum_dupfree: forall A B : sigmaSet, dupfree (product_enum A B).
        Proof.
          intros A B. destruct A, B; unfold product_enum; cbn.
          (* apply dupfree_undup. *) now apply product_list_dupfree.
        Qed. apply product_enum_dupfree.
    Defined.
    Notation "A × B" := (sigmaSet_product A B) (at level 60) : set_scope.
  End Product.

  (* Sets of options of Sets *)
  Section Option.
    Definition option_type (A : sigmaSet) := option (sigmaSet_carr A).
    Definition option_enum (A : sigmaSet) := None :: map Some (sigmaSet_enum A).

    Instance decide_option (A : sigmaSet) : eq_dec (option_type A).
    Proof. unfold dec. decide equality. decide (a=e); auto. Qed.

    Definition sigmaSet_option (A : sigmaSet) : sigmaSet.
    Proof.
      apply (SigmaSet (fun x => match x with None => True | Some y => sigmaSet_sub y end) (option_enum A)).
      - Lemma sigmaSet_enum_enumeration A :
          forall x : eqType_CS (decide_option (A:=A)),
            match x with
            | Some y => sigmaSet_sub y
            | None => True
            end <-> x el option_enum A.
        Proof.
          split.
          - destruct A. unfold option_enum. cbn. destruct x as [x|]; [right; apply in_map_iff|now left].
            exists x. split; [reflexivity|]. now apply sigmaSet_enumeration0.
          - destruct A. unfold option_enum. cbn. destruct x as [x|]. intros [H|(y&Hy&Hy2)%in_map_iff]; [discriminate|].
            injection Hy. intros ->. now apply sigmaSet_enumeration0. auto.
        Qed. apply sigmaSet_enum_enumeration.
      - Lemma sigmaSet_enum_dupfree: forall A : sigmaSet, dupfree (option_enum A).
        Proof.
          intros A. destruct A. unfold option_enum. cbn. constructor.
          - intros (x&H&_) % in_map_iff; discriminate.
          - apply dupfree_map; [intros; congruence|assumption].
        Qed. apply sigmaSet_enum_dupfree.
    Defined.
  End Option.

  (* Subset of Sets *)
  Section SubSet.
    Definition sigmaSet_subset (A : sigmaSet) (f : (sigmaSet_carr A) -> bool) : sigmaSet.
    Proof.
      apply (SigmaSet (fun a => f a /\ sigmaSet_sub a) (filter f (sigmaSet_enum A))).
      - Lemma sigmaSet_subset_enum_enumeration (A : sigmaSet) (f : sigmaSet_carr A -> bool) (x : sigmaSet_carr A) :
          f x /\ sigmaSet_sub x <-> x el filter f (sigmaSet_enum A).
        Proof.
          intuition. apply in_filter_iff. intuition. now apply A. now apply in_filter_iff in H. apply in_filter_iff in H. intuition.
          now apply A. Qed. apply sigmaSet_subset_enum_enumeration.
      - Lemma sigmaSet_subset_dupfree (A : sigmaSet) (f : sigmaSet_carr A -> bool) :
          dupfree (filter f (sigmaSet_enum A)).
        Proof. apply dupfree_filter. apply A. Qed. apply sigmaSet_subset_dupfree.
    Defined.
  End SubSet.

  (* Natural Number Initial intervalls [0; ⋯; n] *)
  Section NatEnum.

    Fixpoint nat_enum n :=
      match n with
      | O => 0 :: nil
      | S n => S n :: nat_enum n
      end.

    Lemma nat_enum_iff x n :
      x el nat_enum n <-> x <= n.
    Proof.
      split.
      - induction n; cbn; intuition. 
      - induction 1; cbn; intuition.
        induction x; cbn; intuition.
    Qed.

    Lemma nat_enum_length n : |nat_enum n| = S n.
    Proof. induction n; cbn; omega. Qed.

    Lemma nat_enum_dupfree n : dupfree (nat_enum n).
    Proof.
      induction n as [|n' IH].
      - cbn. repeat constructor; auto.
      - cbn. constructor.
        + intros H % nat_enum_iff. omega.
        + assumption.
    Qed.

    Definition sigmaSet_natEnum (m : nat) : sigmaSet.
    Proof.
      apply (SigmaSet (fun n => n <= m) (nat_enum m)).
      - Lemma sigmaSet_natEnum_enumeration:
          forall (m : nat) (x : eqType_CS nat_eq_dec),
            x <= m <-> x el nat_enum m.
        Proof. intros m. intros x. split; intros; now apply nat_enum_iff. Qed. apply sigmaSet_natEnum_enumeration.
      - apply nat_enum_dupfree.
    Defined.

  End NatEnum.

  
  (* Functions between sets *)
  Section Func.
    Definition sigmaSet_function (A B : sigmaSet) (f : sigmaSet_carr A -> sigmaSet_carr B) : sigmaSet.
    Proof.
      apply (@sigmaSet_subset (sigmaSet_product A B)).
      destruct A, B. unfold sigmaSet_product. cbn. intros (x&y).
      decide (f x = y); [exact true|exact false].
    Defined.
  End Func.

  (* Empty Set *)
  Section Empty.
    Inductive null := .
    Instance null_eq_dec : eq_dec null.
    Proof. unfold dec. decide equality. Qed.
    Definition null_enum : list null := nil.

    Definition sigmaSet_empty : sigmaSet.
    Proof. apply (SigmaSet (fun _ => False) null_enum); [intros [] | constructor]. Defined.
    Notation "'∅'" := (sigmaSet_empty) : set_scope.
  End Empty.

  (* Section fromList *)
  Section FromList.
    Definition sigmaSet_fromList {X : eqType} (A : list X) {H : dupfree A} : sigmaSet.
    Proof. now apply (SigmaSet (fun x => x el A) A). Defined.

    Lemma sigmaSet_fromList_el (X : eqType) (A : list X) { H : dupfree A} (B : @sigmaSet_fromList X A H) :
      let (x,_) := B in x el A.
    Proof. destruct B. unfold sigmaSet_fromList in *. cbn in *. assumption. Qed.
  End FromList.

  (* Singleton Set *)
  Section SingleTon.
    Definition sigmaSet_singleTon {X: eqType} (A : X) : sigmaSet.
    Proof. apply (@sigmaSet_fromList X [A]). repeat constructor; auto. Defined.

    Lemma sigmaSet_singleTon_el (X : eqType) (A : X) (B : sigmaSet_singleTon A) :
      let (x,_) := B in A=x.
    Proof. destruct B. unfold sigmaSet_singleTon, sigmaSet_fromList in *. cbn in *. destruct s; tauto. Qed.
  End SingleTon.

  (* Section Test2.
    Compute sigmaSet_empty.
    Compute sigmaSet_singleTon 42.
    Compute sigmaSet_natEnum 3.
    Compute sigmaSet_union (sigmaSet_natEnum 2) (sigmaSet_natEnum 3).
    Compute sigmaSet_option (sigmaSet_union (sigmaSet_natEnum 2) (sigmaSet_natEnum 3)).
    Compute sigmaSet_product (sigmaSet_natEnum 0) sigmaSet_empty.
    Compute sigmaSet_product (sigmaSet_natEnum 10) (sigmaSet_natEnum 3). (* now computeable because of no undup *)
  End Test2. *)
  

End SigmaSet.



(** ** Vector **)

Module Vector.
  Structure vector (A:Type) (size:nat) : Type := Vector
    {
      Vector_vec  :> list A;
      Vector_size : length Vector_vec = size
    }.
  Arguments Vector {A} size enum _ : rename.

  Record member (A : eqType) (size : nat) (Vec : vector A size) :=
    {
      member_element :> A;
      member_element_in : member_element el Vector_vec Vec
    }.
  
  
  Definition make_vector {A:Type} (xs:list A) := @Vector A (length xs) xs eq_refl.

  Definition vector_map {A B : Type} {size:nat} (f : A -> B) (vec : vector A size) : vector B size.
  Proof.
    destruct vec as [xs Hsize]. apply (@Vector B size (map f xs)). destruct Hsize. apply map_length.
  Defined.

  Section Map2.
    Variables (A B C : Type) (f : A -> B -> C).
      Fixpoint map2 xs ys :=
          match xs, ys with
          | nil, _ => nil
          | _, nil => nil
          | (x::xs'), (y::ys') => f x y :: map2 xs' ys'
          end.

      Lemma map2_size_min xs ys : length (map2 xs ys) = Nat.min (length xs) (length ys).
      Proof.
        revert ys; induction xs as [|x xs' IH]; intros ys; cbn.
        - reflexivity.
        - destruct ys as [|y ys']; cbn.
          + reflexivity.
          + f_equal. apply IH.
      Qed.

      Lemma map2_size_same xs ys : length xs = length ys -> length xs = length (map2 xs ys).
      Proof. intros H. rewrite map2_size_min. rewrite H. now rewrite Nat.min_id. Qed.
  End Map2.

  Definition vector_map2 {A B C : Type} {size:nat} (f : A -> B -> C) (vec1 : vector A size) (vec2 : vector B size) :
    vector C size.
  Proof.
    destruct vec1 as [xs Hs1], vec2 as [ys Hs2]. apply (@Vector C size (map2 f xs ys)).
    destruct Hs1. now rewrite <- map2_size_same.
  Defined.

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
  
End Vector.