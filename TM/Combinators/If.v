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


  Lemma If_terminatesIn (R1 : Rel _ (bool * _)) T1 T2 T3 :
    functionalOn T1 R1 ->
    pM1 ⊫ R1 ->
    projT1 pM1 ↓ T1 ->
    projT1 pM2 ↓ T2 ->
    projT1 pM3 ↓ T3 ->
    projT1 If ↓ (fun (t : tapes sig n) (i : nat) =>
            exists (i1 i2 : nat) (b : bool) (y : tapes sig n),
              i > i1 + i2 /\
              (R1 t (b, y) /\ b = true /\ T1 t i1 /\ T2 y i2 \/
                                                  R1 t (b, y) /\ b = false /\ T1 t i1 /\ T3 y i2)).
  Proof.
    intros. eapply TerminatesIn_monotone.
    - eapply (Match_TerminatesIn (R1 := R1) (T := fun b => if b then T2 else T3) ); eauto.
      now destruct f.
    - intros t i (i1 & i2 & b & y & Hi & [(? & ? & ? & ?) | (? & ? & ? & ?)]); cbv -[plus];
        repeat eexists; eauto;
          destruct b; eauto.
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