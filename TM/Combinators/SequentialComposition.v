Require Import Match.

Section Composition.
  
  Variable n : nat.
  Variable sig : finType.

  
  Variable F : finType.
  Variable pM1 : {M1 : mTM sig n & states M1 -> F}.

  Variable F2 : finType.
  Variable pM2 : { M2 : mTM sig n & states M2 -> F2}.
  
  Definition Seq := MATCH pM1 (fun _ => pM2).

  Lemma Seq_WRealise (R1 : Rel _ (_ * _)) (R2 : Rel _ (F2 * _)) :
    pM1 ⊫ R1 ->
    pM2 ⊫ R2 ->
    Seq ⊫ (R1 ∘ hideParam R2).
  Proof.
    intros.
    eapply WRealise_monotone.
    eapply (Match_WRealise (R1 := R1) (R2 := (fun _ => R2))); eauto.
    firstorder.
  Qed.

  Lemma Seq_Terminates' t conf1 k1 conf2 k2 :
    (projT1 pM1) ↓↓ (t, (conf1, k1)) ->
    projT1 pM2 ↓↓ (ctapes conf1, (conf2, k2)) ->
    (projT1 Seq) ↓ t.
  Proof.
    intros H1 H2. eapply Match_Terminates'; eauto.
  Qed.

  Section Seq_Terminates.

    Variable (T1 : (tapes sig n) -> nat -> Type).
    Variable (T2 : (tapes sig n) -> nat -> Type).

    Hypothesis (Term1 : projT1 pM1 ⇓ T1).
    Hypothesis (Term2 : projT1 pM2 ⇓ T2).

    Record Seq_Terminates_Rel (t : tapes sig n) (k'' : nat) : Type :=
      {
        term_k : nat;
        term_k' : nat;
        term_In : term_k + term_k' < k'';
        term_m1 : T1 t term_k;
        term_m2 : T2 (ctapes (proj1_sig (Term1 term_m1))) term_k';
      }.

    Lemma Seq_Terminates :
      projT1 Seq ⇓ Seq_Terminates_Rel.
    Proof.
      unfold Seq, MATCH. cbn.
      eapply TerminatesIn_monotone.
      - apply Match_Terminates. instantiate (1 := fun _ => T2). auto. Unshelve. apply T1. apply Term1.
      - intros t k''. intros [k k' H1 H2 H3]. econstructor; eauto.
    Qed.

  End Seq_Terminates.

  Lemma Seq_RealiseIn (R1 : Rel _ _) (R2 : Rel _ (F2 * _)) k1 k2:
    pM1 ⊨c(k1) R1 ->
    pM2 ⊨c(k2) R2 ->
    Seq ⊨c(1 + k1 + k2) (R1 ∘ hideParam R2).
  Proof.
    intros H1 H2.
    eapply RealiseIn_monotone.
    eapply (Match_RealiseIn).
    - eapply H1.
    - intros f.  eapply H2.
    - omega.
    - firstorder.
  Qed.

  Lemma Seq_Realise (R1 : Rel _ _) (R2 : Rel _ (F2 * _)) :
    pM1 ⊨ R1 ->
    pM2 ⊨ R2 ->
    Seq ⊨ R1 ∘ (hideParam R2).
  Proof.
    intros H1 H2. 
    eapply Realise_monotone.
    eapply (Match_Realise).
    - eapply H1.
    - intros f.  eapply H2.
    - firstorder.
  Qed.

End Composition.

Notation "A ;; B" := (Seq A B) (right associativity, at level 65).