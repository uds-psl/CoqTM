Require Import Match.

Section Composition.

  Variable n : nat.
  Variable sig : finType.

  Variable pM1 : { M1 : mTM sig n & states M1 -> bool}.

  Variable F2 : finType.
  
  Variable pM2 : { M2 : mTM sig n & states M2 -> F2}.
  Variable pM3 : { M3 : mTM sig n & states M3 -> F2}.

  Definition If := MATCH pM1 (fun b => if b then pM2 else pM3).

  Lemma If_WRealsie (R1 : Rel _ _) (R2 : Rel _ (F2 * _)) (R3 : Rel _ (F2 * _)) :
    pM1 ⊫ R1 ->
    pM2 ⊫ R2 ->
    pM3 ⊫ R3 ->
    If ⊫ (R1 |_true) ∘ R2 ∪ (R1 |_false) ∘ R3.
  Proof.
    intros.
    eapply WRealise_monotone.
    - eapply (Match_WRealise (R1 := R1) (R2 := (fun b => if b then R2 else R3))); eauto.
      now intros [].
    - hnf. intros H2 (f& t). intros ([ | ]& (y & H3&H3')). left. hnf. eauto. right. hnf. eauto.
  Qed.

  Lemma If_Terminates_True t conf1 k1 conf2 k2 :
    (projT1 pM1) ↓↓ (t, (conf1, k1)) ->
    projT2 pM1 (cstate conf1) = true ->
    (projT1 pM2) ↓↓ (ctapes conf1, (conf2, k2)) ->
    (projT1 If) ↓ t.
  Proof.
    intros H1 H2 H3.
    pose proof @Match_Terminates' n sig (FinType (EqType bool)) pM1 F2 (fun b => if b then pM2 else pM3) t conf1 k1 as L.
    cbn in L. rewrite H2 in L. specialize (L conf2 k2 ). unfold If, MATCH. cbn [projT1]. eapply L; eauto.
  Qed.
    
  Lemma If_Terminates_False t conf1 k1 conf2 k2 :
    (projT1 pM1) ↓↓ (t, (conf1, k1)) ->
    projT2 pM1 (cstate conf1) = false ->
    (projT1 pM3) ↓↓ (ctapes conf1, (conf2, k2)) ->
    (projT1 If) ↓ t.
  Proof.
    intros H1 H2 H3.
    pose proof @Match_Terminates' n sig (FinType (EqType bool)) pM1 F2 (fun b => if b then pM2 else pM3) t conf1 k1 as L.
    cbn in L. rewrite H2 in L. specialize (L conf2 k2 ). unfold If, MATCH. cbn [projT1]. eapply L; eauto.
  Qed.

  Lemma Match_Terminates T1 T2 T3 :
    pM1 ⇓ T1 ->
    pM2 ⇓ T2 ->
    pM3 ⇓ T3 ->
    If ⇓ (fun t '(y'', t'', k'') =>
            exists f k1 k2 t', T1 t (f, t', k1) /\ (f = true /\ T2 t' (y'', t'', k2) \/ f = false /\ T3 t' (y'', t'', k2)) /\ k1 + k2 < k'').
  Proof.
    intros H1 H2 H3. eapply TerminatesIn_monotone.
    - unfold If. apply Match_Terminates with (T__f := fun f : bool => if f then T2 else T3). apply H1. intros [ | ]; cbn; assumption.
    - hnf. intros t ((y&t2)&k2). intros (f&k1&k3&t'&H&H'&H''). destruct H' as [ (-> & H') | (-> & H')]; [exists true | exists false]; firstorder.
  Qed.
  

  Lemma If_RealiseIn (R1 : Rel _ _) (R2 : Rel _ (F2 * _)) (R3 : Rel _ (F2 * _)) k1 k2 k3:
    pM1 ⊨c(k1) R1 ->
    pM2 ⊨c(k2) R2 ->
    pM3 ⊨c(k3) R3 ->
    If ⊨c(1 + k1 + Nat.max k2 k3)
       (R1 |_true) ∘ R2 ∪ (R1 |_false) ∘ R3.
  Proof.
    intros.
    eapply RealiseIn_monotone.
    eapply Match_RealiseIn; eauto.
    - intros. cbn in f. destruct f.
      + eapply RealiseIn_monotone. destruct pM2. eassumption. instantiate (1 := Nat.max k2 k3); firstorder.
        instantiate (1 := fun t => match t with true => R2 | _ => R3 end). reflexivity.
      + eapply RealiseIn_monotone. destruct pM3. eassumption. firstorder. reflexivity.
    - omega.
    - hnf. intros H2 (f& t). intros ([ | ]& (y & H3&H3')). left. hnf. eauto. right. hnf. eauto.
  Qed.

  Lemma If_Realise (R1 : Rel _ _) (R2 : Rel _ (F2 * _)) (R3 : Rel _ (F2 * _)) :
    pM1 ⊨ R1 ->
    pM2 ⊨ R2 ->
    pM3 ⊨ R3 ->
    If ⊨ (R1 |_true) ∘ R2 ∪ (R1 |_false) ∘ R3.
  Proof.
    intros.
    eapply Realise_monotone.
    eapply Match_Realise; eauto.
    - intros. cbn in f. destruct f.
      + eapply Realise_monotone. eassumption.
        instantiate (1 := fun t => match t with true => R2 | _ => R3 end). reflexivity.
      + eapply Realise_monotone. destruct pM3. eassumption. firstorder.
    - hnf. intros H2 (f& t). intros ([ | ]& (y & H3&H3')). left. hnf. eauto. right. hnf. eauto.
  Qed.
    
End Composition.