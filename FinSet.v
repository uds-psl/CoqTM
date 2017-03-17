(** ** Finite Sets **)

Require Export Base.
Require Import Eqdep_dec.

Delimit Scope finSet_scope with finSet.
Open Scope finSet_scope.

(* We cannot build "subsets" of these finSet's
 * We would need sets with sum types { x | P x }, but we cannot show the enumeration
 * property, because we don't have proof irrelevance (Propositional extensionality). *)

Delimit Scope set_scope with set.

Module FinSet.

  Structure finSet := FinSet
    {
      finSet_carr :> eqType;
      finSet_enum : list finSet_carr;
      finSet_enumeration : forall x : finSet_carr, x el finSet_enum;
      finSet_dupfree : dupfree finSet_enum
    }.
  Arguments FinSet {X} enum _ _ : rename.

  Notation "A == B" := (finSet_carr A = finSet_carr B) (at level 70) : finSet_scope.

  (* Disjoint Union *)
  Section Union.

    Definition intersect_type (A B : finSet) := sum (finSet_carr A) (finSet_carr B).

    Instance decide_sum (A B : finSet) : eq_dec (intersect_type A B).
    Proof.
      destruct A, B; unfold intersect_type; cbn.
      intros [x|x] [y|y].
      - unfold dec. decide (x=y) as [->|H]; eauto. right. intros H'. apply H. now inversion H'.
      - right. discriminate.
      - right. discriminate.
      - unfold dec. decide (x=y) as [->|H]; eauto. right. intros H'. apply H. now inversion H'.
    Qed.
    
    Definition union_enum (A B : finSet) :=
      let xs := finSet_enum A in
      let ys := finSet_enum B in
      map inl xs ++ map inr ys.


    Lemma union_enum_enumeration A B :
      forall x : eqType_CS (decide_sum (B:=B)), x el union_enum A B.
    Proof.
      intros [x|x]; apply in_app_iff; [left|right]; apply in_map_iff; exists x; split; auto; [apply A|apply B].
    Qed.
    
    Lemma union_enum_dupfree A B :
      dupfree (union_enum A B).
    Proof.
     destruct A, B. unfold union_enum. cbn. apply dupfree_app.
     + intros ([x|y] & (z1&Hz11&Hz12) % in_map_iff & (z2&Hz21&Hz22) % in_map_iff); discriminate.
     + apply dupfree_map; intuition; congruence.
     + apply dupfree_map; intuition; congruence.
    Qed.
    
    Definition finSet_union (A B : finSet) : finSet.
    Proof.
      apply (FinSet (union_enum A B)).
      - apply union_enum_enumeration.
      - apply union_enum_dupfree.
    Defined.
    Notation "a ⊕ b" := (finSet_union a b) (at level 70) : set_scope.
  End Union.

  (* Product Set *)
  Section Product.
    Definition product_type (A B : finSet) := prod (finSet_carr A) (finSet_carr B).

    (* This creates all tuples (x,y); and duplication free *)
    Definition product_list (X Y : Type) : list X -> list Y -> list (X*Y) :=
      fix product xs ys :=
        match xs with
        | nil => nil
        | x::xs' => map (pair x) ys ++ product xs' ys
        end.

    Definition product_enum (A B : finSet) :=
      let xs := finSet_enum A in
      let ys := finSet_enum B in
      (* undup *) (product_list xs ys).

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


    Definition finSet_product (A B : finSet) : finSet.
    Proof.
      apply (FinSet (product_enum A B)).
      - Lemma product_enum_enumeration:
          forall (A B : finSet) (x : eqType_CS (prod_eq_dec (eqType_dec (e:=A)) (eqType_dec (e:=B)))),
            x el product_enum A B.
        Proof.
          intros A B. destruct A, B; unfold product_enum; cbn. intros (x&y).
          apply product_list_enumeration; auto.
        Qed. apply product_enum_enumeration.
      - Lemma product_enum_dupfree:
          forall A B : finSet, dupfree (product_enum A B).
        Proof.
          intros A B. destruct A, B; unfold product_enum; cbn. now apply product_list_dupfree.
        Qed. apply product_enum_dupfree.
    Defined.

    Notation "a '×' b" := (finSet_product a b) (at level 70) : set_scope.

    
  End Product.

  (* Sets of options of Sets *)
  Section Option.
    Definition option_type (A : finSet) := option (finSet_carr A).
    Definition option_enum (A : finSet) := None :: map Some (finSet_enum A).

    Instance decide_option (A : finSet) : eq_dec (option_type A).
    Proof. unfold dec. decide equality. decide (a=e); auto. Qed.

    Definition finSet_option (A : finSet) : finSet.
    Proof.
      apply (FinSet (option_enum A)).
      - Lemma finalSet_enum_enumeration: forall (A : finSet) (x : eqType_CS (decide_option (A:=A))), x el option_enum A.
        Proof. intros A. destruct A. unfold option_enum. cbn. intros [x|]; [right; apply in_map_iff; eauto|now left]. Qed.
        apply finalSet_enum_enumeration.
      - Lemma finalSet_enum_dupfree: forall A : finSet, dupfree (option_enum A).
        Proof.
          intros A. destruct A. unfold option_enum. cbn. constructor.
          - intros (x&H&_) % in_map_iff; discriminate.
          - apply dupfree_map; [intros; congruence|assumption].
        Qed. apply finalSet_enum_dupfree.
    Defined.
  End Option.

  (* Sets of numbers *)
  Section NatEnum.

    (*
     * The following procedures / Lemmas are not enough, because they handle with lists of nats.
     * We would need { m | m <= n } as carrier type, but we cannot show enumeration without Propositional extensionality
     *)

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

    Fixpoint nat_enum' n :=
      match n with
      | O => nil
      | S n => n :: nat_enum' n
      end.

    Lemma nat_enum'_iff x n :
      x el nat_enum' n <-> x < n.
    Proof.
      split.

      - induction n; cbn; intuition; omega.
      - induction 1; cbn; intuition.
    Qed.

    Lemma nat_enum'_length n : |nat_enum' n| = n.
    Proof. induction n; cbn; omega. Qed.

    Lemma nat_enum'_dupfree n : dupfree (nat_enum' n).
    Proof.
      induction n as [|n' IH].
      - cbn. repeat constructor; auto.
      - cbn. constructor.
        + intros H % nat_enum'_iff. omega.
        + assumption.
    Qed.
  End NatEnum.

  Section Empty.
    Inductive null := . Instance null_eq_dec : eq_dec null. Proof. unfold dec. decide equality. Qed. Definition null_enum : list null := nil.
    Definition finSet_empty : finSet. Proof. apply (FinSet null_enum); [intros [] | constructor]. Defined.
  End Empty.

  Section ABC.
    (* Example of a finit Set with constructors *)
    Inductive enumABC := A | B | C.
    Instance enumABC_eq_dec : eq_dec enumABC. Proof. unfold dec. decide equality. Qed.
    Definition abc_enum := [A;B;C].
    Lemma abc_enum_enumeration : forall x : eqType_CS enumABC_eq_dec, x el abc_enum. Proof. intros x. destruct x; cbn; auto. Qed.
    Lemma abc_enum_dupfree : dupfree abc_enum. Proof. unfold abc_enum. repeat constructor; cbn; auto; intuition; discriminate. Qed.
    Definition finSet_abc : finSet. Proof. apply (FinSet abc_enum); [apply abc_enum_enumeration| apply abc_enum_dupfree]. Defined.
  End ABC.


  Section Test.
    (* Works good. *)
    (* Compute finSet_empty.
    Compute finSet_product finSet_abc finSet_abc.
    Compute finSet_product finSet_abc (finSet_product finSet_abc FinSet.finSet_empty). *)
  End Test.

End FinSet.