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
    Seq ⊫ ⋃_y ((R1 |_ y) ∘ R2).
  Proof.
    intros.
    eapply WRealise_monotone.
    eapply (Match_WRealise (R1 := R1) (R2 := (fun _ => R2))); eauto.
    firstorder.
  Qed.

  Lemma Seq_TerminatesIn (R1 : Rel (tapes sig n) (F * tapes sig n)) (T1 T2 : Rel (tapes sig n) nat) :
    pM1 ⊫ R1 ->
    projT1 pM1 ↓ T1 ->
    projT1 pM2 ↓ T2 ->
    projT1 Seq ↓ (fun tin i => exists i1 i2, i1 + S i2 <= i /\ T1 tin i1 /\
                                    forall tout yout, R1 tin (yout, tout) -> T2 tout i2).
  Proof.
    intros HRealise HTerm1 HTerm2.
    eapply TerminatesIn_monotone.
    - eapply Match_TerminatesIn; eauto. instantiate (1 := fun _ => T2). auto.
    - intros tin i (i1&i2&Hi&HT1&HT2). exists i1, i2; repeat split; auto.
  Qed.


  Lemma Seq_terminatesIn (R1 : Rel _ (F * _)) T1 T2:
    functionalOn T1 R1 ->
    pM1 ⊫ R1 ->
    projT1 pM1 ↓(T1) ->
    projT1 pM2 ↓(T2) ->
    projT1 Seq ↓(fun (x : tapes sig n) (i : nat) =>
            exists (j k : nat) (y : tapes sig n) (f : F),
              R1 x (f, y) /\ T1 x j /\ T2 y k /\ j + k < i).
  Proof.
    intros.
    eapply TerminatesIn_monotone. eapply (Match_TerminatesIn' (R1 := R1) (T := fun _ => T2) ); eauto.
    intros ? ? (? & ? & ? & ? & ? & ? & ? & ?). eexists _, _, _, _. eauto.
  Qed.

  Lemma Seq_RealiseIn (R1 : Rel _ _) (R2 : Rel _ (F2 * _)) k1 k2:
    pM1 ⊨c(k1) R1 ->
    pM2 ⊨c(k2) R2 ->
    Seq ⊨c(1 + k1 + k2) ⋃_y ((R1 |_y) ∘ R2).
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
    Seq ⊨ ⋃_y ((R1 |_y) ∘ R2).
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

Arguments Seq : simpl never.