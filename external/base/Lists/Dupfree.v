Require Export BaseLists Filter Lists.Cardinality.

(** *** Duplicate-free lists *)

Inductive dupfree (X : Type) : list X -> Prop :=
| dupfreeN : dupfree nil
| dupfreeC x A : ~ x el A -> dupfree A -> dupfree (x::A).

Section Dupfree.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma dupfree_cons x A :
    dupfree (x::A) <-> ~ x el A /\ dupfree A.
  Proof. 
    split; intros D.
    - inv D; auto.
    - apply dupfreeC; tauto.
  Qed.

  Lemma dupfree_app A B :
    disjoint A B -> dupfree A -> dupfree B -> dupfree (A++B).
  Proof.
    intros D E F. induction E as [|x A E' E]; cbn.
    - exact F.
    - apply disjoint_cons in D as [D D'].
      constructor; [|exact (IHE D')].
      intros G. apply in_app_iff in G; tauto.
  Qed.

  Lemma dupfree_map Y A (f : X -> Y) :
    (forall x y, x el A -> y el A -> f x = f y -> x=y) -> 
    dupfree A -> dupfree (map f A).
  Proof.
    intros D E. induction E as [|x A E' E]; cbn.
    - constructor.
    - constructor; [|now auto].
      intros F. apply in_map_iff in F as [y [F F']].
      rewrite (D y x) in F'; auto.
  Qed.

  Lemma dupfree_filter p A :
    dupfree A -> dupfree (filter p A).
  Proof.
    intros D. induction D as [|x A C D]; cbn.
    - left.
    - destruct (p x) eqn:E; [|exact IHD].
      right; [|exact IHD].
      rewrite in_filter_iff, E. intuition.
  Qed.

End Dupfree.

Section Undup.
  Variable X : eqType.
  Implicit Types A B : list X.

  Lemma dupfree_dec A :
    dec (dupfree A).
  Proof.
    induction A as [|x A].
    - left. left.
    - decide (x el A) as [E|E].
      + right. intros F. inv F; tauto.
      + destruct (IHA) as [F|F].
        * unfold dec. auto using dupfree.
        * right. intros G. inv G; tauto.
  Qed.

  Lemma dupfree_card A :
    dupfree A -> card A = |A|.
  Proof.
    induction 1 as [|x A D _ IH]; cbn.
    - reflexivity.
    - decide (x el A) as [G|].
      + exfalso; auto.
      + omega.
  Qed.

  Fixpoint undup (A : list X) : list X :=
    match A with
      | nil => nil
      | x::A' => if Dec (x el A') then undup A' else  x :: undup A'
    end.

  Lemma undup_id_equi A :
    undup A === A.
  Proof.
    induction A as [|x A]; cbn.
    - reflexivity.
    - decide (x el A) as [E|E]; rewrite IHA; auto.
  Qed.

  Lemma dupfree_undup A :
    dupfree (undup A).
  Proof.
    induction A as [|x A]; cbn.
    - left.
    - decide (x el A) as [E|E]; auto.
      right; auto. now rewrite undup_id_equi. 
  Qed.

  Lemma undup_incl A B :
    A <<= B <-> undup A <<= undup B.
  Proof.
    now rewrite !undup_id_equi.
  Qed.

  Lemma undup_equi A B :
    A === B <-> undup A === undup B.
  Proof.
    now rewrite !undup_id_equi.
  Qed.

  Lemma undup_id A :
    dupfree A -> undup A = A.
  Proof.
    intros E. induction E as [|x A E F]; cbn.
    - reflexivity.
    - rewrite IHF. decide (x el A) as [G|G]; tauto.
  Qed.

  Lemma undup_idempotent A :
    undup (undup A) = undup A.

  Proof. apply undup_id, dupfree_undup. Qed.

End Undup.
