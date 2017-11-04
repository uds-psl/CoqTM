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

  Lemma If_Terminates_True' t conf1 k1 conf2 k2 :
    (projT1 pM1) ↓↓ (t, k1, conf1) ->
    projT2 pM1 (cstate conf1) = true ->
    (projT1 pM2) ↓↓ (ctapes conf1, k2, conf2) ->
    (projT1 If) ↓ (t, k1 + S k2).
  Proof.
    intros H1 H2 H3.
    pose proof @Match_Terminates' n sig (FinType (EqType bool)) pM1 F2 (fun b => if b then pM2 else pM3) t conf1 k1 as L.
    cbn in L. rewrite H2 in L. specialize (L conf2 k2 ). unfold If, MATCH. cbn [projT1]. eapply L; eauto.
  Qed.
    
  Lemma If_Terminates_False' t conf1 k1 conf2 k2 :
    (projT1 pM1) ↓↓ (t, k1, conf1) ->
    projT2 pM1 (cstate conf1) = false ->
    (projT1 pM3) ↓↓ (ctapes conf1, k2, conf2) ->
    (projT1 If) ↓ (t, k1 + S k2).
  Proof.
    intros H1 H2 H3.
    pose proof @Match_Terminates' n sig (FinType (EqType bool)) pM1 F2 (fun b => if b then pM2 else pM3) t conf1 k1 as L.
    cbn in L. rewrite H2 in L. specialize (L conf2 k2 ). unfold If, MATCH. cbn [projT1]. eapply L; eauto.
  Qed.

  
  Section If_Terminates.

    Inductive If_Terminates_Rel (t : tapes sig n) (k'' : nat) : Prop :=
    | If_Terminates_True
        (k k' : nat) (In : k + k' < k'')
        (midconf   : mconfig sig (states (projT1 pM1)) n)
        (exec1     : projT1 pM1 ↓↓ (t, k, midconf))
        (exec1True : projT2 pM1 (cstate midconf) = true)
        (endconf   : mconfig sig (states (projT1 pM2)) n)
        (exec1     :  projT1 pM2 ↓↓ (ctapes midconf, k', endconf)) :
           If_Terminates_Rel t k''
    | If_Terminates_False
        (k k' : nat) (In : k + k' < k'')
        (midconf   : mconfig sig (states (projT1 pM1)) n)
        (exec1     : projT1 pM1 ↓↓ (t, k, midconf))
        (exec1True : projT2 pM1 (cstate midconf) = false)
        (endconf   : mconfig sig (states (projT1 pM3)) n)
        (exec2     : projT1 pM3 ↓↓ (ctapes midconf, k', endconf)) :
           If_Terminates_Rel t k''.
                                                
    Lemma If_Terminates :
      projT1 If ⇓ If_Terminates_Rel.
    Proof.
      intros t k''. intros [k k' H1 midconf H2 H3 endconf H4 | k k' H1 midconf H2 H3 endconf H4].
      - pose proof @Match_Terminates' n sig (FinType (EqType bool)) pM1 F2 (fun b => if b then pM2 else pM3) t midconf as L.
        cbn in L. rewrite H3 in L. specialize (L k endconf k' H2 H4). hnf in *.
        destruct L as (econf'&H5). hnf in H5. exists econf'. unfold If. unfold MATCH. cbn in *.
        unfold loopM in *. eapply loop_ge with (k1 := k + S k'). omega. assumption.
      - pose proof @Match_Terminates' n sig (FinType (EqType bool)) pM1 F2 (fun b => if b then pM2 else pM3) t midconf as L.
        cbn in L. rewrite H3 in L. specialize (L k endconf k' H2 H4). hnf in *.
        destruct L as (econf'&H5). hnf in H5. exists econf'. unfold If. unfold MATCH. cbn in *.
        unfold loopM in *. eapply loop_ge with (k1 := k + S k'). omega. assumption.
    Qed.

  End If_Terminates.
  
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