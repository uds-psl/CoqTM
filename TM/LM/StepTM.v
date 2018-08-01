Require Import TM.Code.ProgrammingTools.
Require Import TM.LM.Semantics TM.LM.Alphabets.
Require Import TM.LM.MatchTok TM.LM.LookupTM TM.LM.JumpTargetTM.
Require Import TM.Code.ListTM TM.Code.MatchList TM.Code.MatchPair TM.Code.MatchSum.


(** * Step Machine *)

Local Arguments plus : simpl never.
Local Arguments mult : simpl never.

Section StepMachine.

  Implicit Types H : Heap.
  Implicit Types T V : list HClos.
  Implicit Types a b c : HAd.
  Implicit Types g : HClos.
  Implicit Types (P Q : Pro).

  

  (** Here we compose the [Lookup] and [JumpTarget] machines, together with additional some matches.
The semantics of the step machine are only defined, similarly to [Lookup] and [JumpTarget], when the simulated heap machine steps.

The machine operates on lists of closures and on a heap, so we need a closure-list alphabet and a heap alphabet.
   *)

  Variable sigStep : finType.
  Variable retr_closures_step : Retract (sigList sigHClos) sigStep.
  Variable retr_heap_step : Retract sigHeap sigStep.


  (** Retracts *)
  (* Closures *)
  Local Definition retr_clos_step : Retract sigHClos sigStep := ComposeRetract _ retr_closures_step.

  (* Closure addresses *)

  Definition retr_pro_clos : Retract sigPro sigHClos := _.
  Local Definition retr_pro_step : Retract sigPro sigStep := ComposeRetract retr_pro_clos retr_clos_step.
  Local Definition retr_tok_step : Retract sigTok sigStep := ComposeRetract _ retr_pro_step.

  Local Definition retr_nat_clos_ad : Retract sigNat sigHClos := Retract_sigPair_X _ (Retract_id _).
  Local Definition retr_nat_step_clos_ad : Retract sigNat sigStep := ComposeRetract retr_nat_clos_ad retr_clos_step.

  Local Definition retr_nat_clos_var : Retract sigNat sigHClos := Retract_sigPair_Y _ _.
  Local Definition retr_nat_step_clos_var : Retract sigNat sigStep := ComposeRetract retr_nat_clos_var retr_clos_step.

  (** Instance of the [Lookup] and [JumpTarget] machine *)
  Local Definition Step_Lookup := Lookup retr_clos_step retr_heap_step.



  (** Cons a closure to a closure list, if the programm of the closure is not empty, and reset the program but not the address of the closure *)

  Definition TailRec_Rel : pRel sigStep^+ unit 3 :=
    ignoreParam (
        fun tin tout =>
          forall T P a,
            tin[@Fin0] ≃ T ->
            tin[@Fin1] ≃(Encode_map Encode_Prog retr_pro_step) P ->
            tin[@Fin2] ≃(Encode_map Encode_nat retr_nat_step_clos_ad) a ->
            tout[@Fin0] ≃ tailRecursion (a, P) T /\
            isRight tout[@Fin1] /\
            tout[@Fin2] ≃(Encode_map Encode_nat retr_nat_step_clos_ad) a
      ).
  
  
  Definition TailRec : pTM sigStep^+ unit 3 :=
    If (IsNil sigTok_fin ⇑ retr_pro_step @ [|Fin1|])
       (Reset _ @ [|Fin1|])
       (Constr_pair sigHAd_fin sigPro_fin ⇑ retr_clos_step @ [|Fin2; Fin1|];;
        Constr_cons sigHClos_fin ⇑ _ @ [|Fin0; Fin1|];;
        Reset _ @ [|Fin1|]).

  Lemma TailRec_Realise : TailRec ⊨ TailRec_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold TailRec. repeat TM_Correct.
      - apply Reset_Realise with (cX := Encode_map Encode_Prog retr_pro_step).
      - apply Reset_Realise with (cX := Encode_map Encode_HClos retr_clos_step).
    }
    {
      intros tin ((), tout) H. intros T P a HEncT HEncP HEncA.
      destruct H; TMSimp.
      - modpon H. destruct P; auto; modpon H. modpon H0. repeat split; auto.
      - modpon H. destruct P; auto; modpon H.
        specialize (H0 a (t :: P)). modpon H0.
        specialize (H1 T (a, t :: P)). modpon H1.
        specialize (H2 (a, t :: P)). modpon H2.
        repeat split; auto. contains_ext.
    }
  Qed.

  Local Arguments tailRecursion : simpl never.

  Definition TailRec_steps P a :=
    match P with
    | nil => 1 + IsNil_steps + Reset_steps _ nil
    | t::P => 1 + IsNil_steps + 1 + Constr_pair_steps _ a + 1 + Constr_cons_steps _ (a,t::P) + Reset_steps _ (a, t :: P)
    end.

  Definition TailRec_T : tRel sigStep^+ 3 :=
    fun tin k =>
      exists T P a, tin[@Fin0] ≃ T /\
               tin[@Fin1] ≃(Encode_map Encode_Prog retr_pro_step) P /\
               tin[@Fin2] ≃(Encode_map Encode_nat retr_nat_step_clos_ad) a /\
               TailRec_steps P a <= k.

  Lemma TailRec_Terminates : projT1 TailRec ↓ TailRec_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold TailRec. repeat TM_Correct.
      - apply Reset_Terminates with (cX := Encode_map Encode_Prog retr_pro_step).
      - apply Reset_Terminates with (cX := Encode_map Encode_HClos retr_clos_step).
    }
    {
      intros tin k (T&P&a&HEncT&HEncP&HEncA&Hk). unfold TailRec_steps in Hk.
      destruct P as [ | t P]; cbn.
      - exists (IsNil_steps), (Reset_steps _ nil). repeat split; try omega.
        intros tmid b (HIsNil&IsNilInj); TMSimp. modpon HIsNil. destruct b; auto; modpon HIsNil. eauto.
      - exists (IsNil_steps), (1 + Constr_pair_steps _ a + 1 + Constr_cons_steps _ (a,t::P) + Reset_steps _ (a, (t::P))).
        repeat split; try omega.
        intros tmid b (HIsNil&IsNilInj); TMSimp. modpon HIsNil. destruct b; auto; modpon HIsNil.
        exists (Constr_pair_steps _ a), (1 + Constr_cons_steps _ (a,t::P) + Reset_steps _ (a,t::P)). repeat split; try omega.
        { hnf; cbn. eexists; split. simpl_surject; contains_ext. reflexivity. } now rewrite !Nat.add_assoc.
        intros tmid0 () (HPair&HPairInj); TMSimp.
        specialize (HPair a (t::P)); modpon HPair.
        exists (Constr_cons_steps _ (a,t::P)), (Reset_steps _ (a,t::P)). repeat split; try omega.
        { hnf; cbn. do 2 eexists; repeat split; simpl_surject; eauto. contains_ext. } reflexivity.
        intros tmid1 () (HCons&HConsInj); TMSimp. specialize (HCons T (a,t::P)). modpon HCons.
        exists (a, t :: P). split; eauto. contains_ext. now setoid_rewrite Reset_steps_comp.
    }
  Qed. 


  (** Like [TailRec], but doesn't check whether the program is empty, and resets [a] and [Q] *)
  Definition ConsClos_Rel : pRel sigStep^+ unit 3 :=
    ignoreParam (
        fun tin tout =>
          forall T Q a,
            tin[@Fin0] ≃ T ->
            tin[@Fin1] ≃(Encode_map Encode_nat retr_nat_step_clos_ad) a ->
            tin[@Fin2] ≃(Encode_map Encode_Prog retr_pro_step) Q ->
            tout[@Fin0] ≃ (a, Q) :: T /\
            isRight tout[@Fin1] /\
            isRight tout[@Fin2]
      ).
  
  
  Definition ConsClos : pTM sigStep^+ unit 3 :=
    Constr_pair sigHAd_fin sigPro_fin ⇑ retr_clos_step @ [|Fin1; Fin2|];;
    Constr_cons sigHClos_fin ⇑ _ @ [|Fin0; Fin2|];;
    Reset _ @ [|Fin2|];;
    Reset _ @ [|Fin1|].

  Lemma ConsClos_Realise : ConsClos ⊨ ConsClos_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold ConsClos. repeat TM_Correct.
      - apply Reset_Realise with (cX := Encode_map Encode_HClos retr_clos_step).
      - apply Reset_Realise with (cX := Encode_map Encode_nat retr_nat_step_clos_ad).
    }
    {
      intros tin ((), tout) H. intros T Q a HEncT HEncA HEncQ.
      TMSimp.
      specialize (H a Q). modpon H. (* Constr_pair *)
      specialize (H0 T (a, Q)). modpon H0. (* Constr_cons *)
      specialize (H1 (a, Q)). modpon H1. (* Reset HClos *)
      modpon H2. (* Reset HAd *) auto.
    }
  Qed.


  Definition ConsClos_steps Q a :=
    3 + Constr_pair_steps _ a + Constr_cons_steps _ (a,Q) + Reset_steps _ (a,Q) + Reset_steps _ a.
    
  Definition ConsClos_T : tRel sigStep^+ 3 :=
    fun tin k =>
          exists T Q a,
            tin[@Fin0] ≃ T /\
            tin[@Fin1] ≃(Encode_map Encode_nat retr_nat_step_clos_ad) a /\
            tin[@Fin2] ≃(Encode_map Encode_Prog retr_pro_step) Q /\
            ConsClos_steps Q a <= k.

  Lemma ConsClos_Terminates : projT1 ConsClos ↓ ConsClos_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold ConsClos. repeat TM_Correct.
      - apply Reset_Realise with (cX := Encode_map Encode_HClos retr_clos_step).
      - apply Reset_Terminates with (cX := Encode_map Encode_HClos retr_clos_step).
      - apply Reset_Terminates with (cX := Encode_map Encode_nat retr_nat_step_clos_ad).
    }
    {
      intros tin k. intros (T&Q&a&HEncT&HEnca&HEncQ&Hk). unfold ConsClos_steps in Hk.
      exists (Constr_pair_steps _ a), (1 + Constr_cons_steps _ (a,Q) + 1 + Reset_steps _ (a,Q) + Reset_steps _ a).
      cbn; repeat split; try omega.
      { hnf; cbn. exists a. repeat split; simpl_surject; eauto. contains_ext. }
      intros tmid () (HPair&HPairInj); TMSimp. modpon HPair.
      exists (Constr_cons_steps _ (a,Q)), (1 + Reset_steps _ (a,Q) + Reset_steps _ a).
      cbn; repeat split; try omega.
      { hnf; cbn. exists T, (a, Q). repeat split; simpl_surject; eauto. contains_ext. } now rewrite !Nat.add_assoc.
      intros tmid0 () (HCons&HConsInj); TMSimp. specialize (HCons T (a,Q)); modpon HCons.
      exists (Reset_steps _ (a,Q)), (Reset_steps _ a).
      cbn; repeat split; try omega; eauto.
      { hnf; cbn. exists (a, Q). repeat split; simpl_surject; eauto. contains_ext. now setoid_rewrite Reset_steps_comp. }
      intros tmid1 () (HReset&HResetInj); TMSimp. clear HReset.
      exists a. split; eauto. contains_ext. now setoid_rewrite Reset_steps_comp.
    }
  Qed.


  Definition Step_lam_Rel : pRel sigStep^+ bool 10 :=
    fun tin '(yout, tout) =>
      forall (T V : list HClos) (H : Heap) (a : HAd) (P : Pro),
        tin[@Fin0] ≃ T ->
        tin[@Fin1] ≃ V ->
        tin[@Fin2] ≃ H ->
        tin[@Fin3] ≃(Encode_map Encode_Prog retr_pro_step) P ->
        tin[@Fin4] ≃(Encode_map Encode_nat retr_nat_step_clos_ad) a ->
        (forall i : Fin.t 5, isRight tin[@FinR 5 i]) ->
        match yout with
        | true =>
          exists (P' Q : Pro),
          jumpTarget 0 [] P = Some (Q, P') /\
          tout[@Fin0] ≃ tailRecursion (a, P') T /\
          tout[@Fin1] ≃ (a, Q) :: V /\
          tout[@Fin2] ≃ H /\
          (forall i : Fin.t 7, isRight tout[@FinR 3 i])
        | false => jumpTarget 0 [] P = None
        end.

  Definition Step_lam : pTM sigStep^+ bool 10 :=
    If (JumpTarget ⇑ retr_pro_step @ [|Fin3; Fin6; Fin7; Fin8; Fin9|])
       (Return (TailRec @ [|Fin0; Fin3; Fin4|];;
                ConsClos @ [|Fin1; Fin4; Fin6|])
               true)
       (Return Nop false).
  

  Lemma Step_lam_Realise : Step_lam ⊨ Step_lam_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Step_lam. repeat TM_Correct.
      - apply JumpTarget_Realise.
      - apply TailRec_Realise.
      - apply ConsClos_Realise.
    }
    {
      intros tin (yout, tout) H. cbn. intros T V heap a P HEncT HEncV HEncHeap HEncP HEncA HInt.
      destruct H; TMSimp.
      { (* Then, i.e. [jumpTarget 0 [] = Some (Q', P')] *) rename H into HJumpTarget, H0 into HTailRec, H1 into HConsClos.
        modpon HJumpTarget.
        { intros i; destruct_fin i; cbn; simpl_surject; auto. }
        destruct HJumpTarget as (P'&Q'&HJumpTarget); modpon HJumpTarget.
        modpon HTailRec.
        modpon HConsClos.
        do 2 eexists; repeat split; eauto.
        generalize (HJumpTarget2 Fin0); generalize (HJumpTarget2 Fin1); generalize (HJumpTarget2 Fin2); cbn; TMSimp_goal.
        intros; simpl_surject; destruct_fin i; TMSimp_goal; auto.
      }
      { (* Else, i.e. [jumpTarget 0 [] = None] *)
        modpon H.
        { intros i; destruct_fin i; cbn; simpl_surject; auto. }
        assumption.
      }
    }
  Qed.

  (* Steps depending on the result of [JumpTarget] *)
  Definition Step_lam_steps_JumpTarget P a :=
    match jumpTarget 0 [] P with
    | Some (Q', P') =>
      1 + TailRec_steps P' a + ConsClos_steps Q' a
    | None => 0
    end.
  
  Definition Step_lam_steps P a := 1 + JumpTarget_steps P + Step_lam_steps_JumpTarget P a.

  Definition Step_lam_T : tRel sigStep^+ 10 :=
    fun tin k =>
      exists (T V : list HClos) (H : Heap) (a : HAd) (P : Pro),
        tin[@Fin0] ≃ T /\
        tin[@Fin1] ≃ V /\
        tin[@Fin2] ≃ H /\
        tin[@Fin3] ≃(Encode_map Encode_Prog retr_pro_step) P /\
        tin[@Fin4] ≃(Encode_map Encode_nat retr_nat_step_clos_ad) a /\
        (forall i : Fin.t 5, isRight tin[@FinR 5 i]) /\
        Step_lam_steps P a <= k.

  Lemma Step_lam_Terminates : projT1 Step_lam ↓ Step_lam_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Step_lam. repeat TM_Correct.
      - apply JumpTarget_Realise.
      - apply JumpTarget_Terminates.
      - apply TailRec_Realise.
      - apply TailRec_Terminates.
      - apply ConsClos_Terminates.
    }
    {
      intros tin k. intros (T&V&H&a&P&HEncT&HEncV&HEncH&HEncP&HEncA&HInt&Hk). unfold Step_lam_steps in Hk.
      exists (JumpTarget_steps P), (Step_lam_steps_JumpTarget P a). cbn; repeat split; try omega.
      { hnf; cbn. do 1 eexists; repeat split; simpl_surject; eauto.
        - apply HInt.
        - intros i; destruct_fin i; cbn; simpl_surject; TMSimp_goal; eauto; apply HInt. }
      intros tmid ymid (HJump&HJumpInj); TMSimp. modpon HJump.
      { intros i; destruct_fin i; cbn; simpl_surject; TMSimp_goal; eauto; apply HInt. }
      destruct ymid.
      {
        destruct HJump as (P'&Q'&HJump); modpon HJump.
        unfold Step_lam_steps_JumpTarget. rewrite HJump.
        exists (TailRec_steps P' a), (ConsClos_steps Q' a). cbn; repeat split; try omega. hnf; cbn; eauto 7.
        intros tmid0 () (HTailRec&HTailRecInj); TMSimp. modpon HTailRec.
        hnf; cbn. eauto 7.
      }
      { omega. }
    }
  Qed.
  


  Definition Put_Rel : pRel sigStep^+ unit 6 :=
    ignoreParam (
        fun tin tout =>
          forall (H : Heap) (g : HClos) (b : HAd),
            tin[@Fin0] ≃ H ->
            tin[@Fin1] ≃(Encode_map Encode_HClos retr_clos_step) g ->
            tin[@Fin2] ≃(Encode_map Encode_nat retr_nat_step_clos_ad) b ->
            isRight tin[@Fin3] -> isRight tin[@Fin4] -> isRight tin[@Fin5] ->
            tout[@Fin0] ≃ H ++ [Some (g,b)] /\
            isRight tout[@Fin1] /\
            isRight tout[@Fin2] /\
            tout[@Fin3] ≃(Encode_map Encode_nat retr_nat_step_clos_ad) length H /\
            isRight tout[@Fin4] /\
            isRight tout[@Fin5]
      ).



  Local Definition retr_nat_step_hent : Retract sigNat sigStep := ComposeRetract retr_nat_heap_entry retr_heap_step.

  Local Definition retr_clos_step_hent : Retract sigHClos sigStep := ComposeRetract retr_clos_heap retr_heap_step.

  Local Definition retr_hent'_step : Retract sigHEnt' sigStep := ComposeRetract retr_hent'_heap retr_heap_step.

  Local Definition retr_hent_step : Retract sigHEnt sigStep := ComposeRetract retr_hent_heap retr_heap_step.
  
  Definition Put : pTM sigStep^+ unit 6 :=
    Length retr_heap_step retr_nat_step_clos_ad @ [|Fin0; Fin3; Fin4; Fin5|];;
    Constr_nil sigHEnt_fin ⇑ _ @ [|Fin4|];;
    Translate retr_nat_step_clos_ad retr_nat_step_hent @ [|Fin2|];;
    Translate retr_clos_step retr_clos_step_hent @ [|Fin1|];;
    Constr_pair sigHClos_fin sigHAd_fin ⇑ retr_hent'_step @ [|Fin1; Fin2|];;
    Constr_Some sigHEnt'_fin ⇑ retr_hent_step @ [|Fin2|];;
    Constr_cons sigHEnt_fin ⇑ _ @ [|Fin4; Fin2|];;
    App' sigHEnt_fin ⇑ _ @ [|Fin0; Fin4|];;
    MoveValue _ @ [|Fin4; Fin0|];;
    Reset _ @ [|Fin2|];;
    Reset _ @ [|Fin1|].


  Lemma Put_Realise : Put ⊨ Put_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Put. repeat TM_Correct.
      - apply Length_Computes with (X := HEnt).
      - apply Translate_Realise with (X := nat).
      - apply Translate_Realise with (X := HClos).
      - apply App'_Realise with (X := HEnt).
      - apply MoveValue_Realise with (X := Heap) (Y := Heap).
      - apply Reset_Realise with (cX := Encode_map Encode_HEnt retr_hent_step).
      - apply Reset_Realise with (cX := Encode_map Encode_HClos retr_clos_step_hent).
    }
    {
      intros tin ((), tout) H. cbn. intros heap g b HEncHeap HEncG HEncB HRigh3 HRight4 HRight5.
      TMSimp. (* This takes long *)
      rename H into HLength; rename H0 into HNil; rename H1 into HTranslate; rename H2 into HTranslate'; rename H3 into HPair; rename H4 into HSome; rename H5 into HCons; rename H6 into HApp; rename H7 into HMove; rename H8 into HReset; rename H9 into HReset'.
      modpon HLength.
      { intros i; destruct_fin i; TMSimp_goal; auto. }
      specialize (HLength1 Fin1) as HLength2; specialize (HLength1 Fin0).
      modpon HNil.
      modpon HTranslate.
      modpon HTranslate'.
      modpon HPair.
      specialize (HSome (g, b)). modpon HSome. cbn in *.
      specialize (HCons [] (Some (g, b))). modpon HCons.
      modpon HApp.
      modpon HMove.
      specialize (HReset (Some (g, b))). modpon HReset.
      modpon HReset'.
      repeat split; auto.
    }
  Qed.

  Definition Put_steps H g b :=
    10 + Length_steps _ H + Constr_nil_steps + Translate_steps _ b + Translate_steps _ g + Constr_pair_steps _ g + Constr_Some_steps +
    Constr_cons_steps _ (Some (g, b)) + App'_steps _ H + MoveValue_steps _ _ (H++[Some(g,b)]) H + Reset_steps _ (Some (g, b)) + Reset_steps _ g.

  Definition Put_T : tRel sigStep ^+ 6 :=
    fun tin k =>
      exists (H : Heap) (g : HClos) (b : HAd),
        tin[@Fin0] ≃ H /\
        tin[@Fin1] ≃(Encode_map Encode_HClos retr_clos_step) g /\
        tin[@Fin2] ≃(Encode_map Encode_nat retr_nat_step_clos_ad) b /\
        isRight tin[@Fin3] /\ isRight tin[@Fin4] /\ isRight tin[@Fin5] /\
        Put_steps H g b <= k.
            
  Lemma Put_Terminates : projT1 Put ↓ Put_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Put. repeat TM_Correct.
      - apply Length_Computes with (X := HEnt).
      - apply Length_Terminates with (X := HEnt).
      - apply Translate_Realise with (X := nat).
      - apply Translate_Terminates with (X := nat).
      - apply Translate_Realise with (X := HClos).
      - apply Translate_Terminates with (X := HClos).
      - apply App'_Realise with (X := HEnt).
      - apply App'_Terminates with (X := HEnt).
      - apply MoveValue_Realise with (X := Heap) (Y := Heap).
      - apply MoveValue_Terminates with (X := Heap) (Y := Heap).
      - apply Reset_Realise with (cX := Encode_map Encode_HEnt retr_hent_step).
      - apply Reset_Terminates with (cX := Encode_map Encode_HEnt retr_hent_step).
      - apply Reset_Terminates with (cX := Encode_map Encode_HClos retr_clos_step_hent).
    }
    {
      intros tin k. intros (H&g&b&HEncH&HEncG&HEncB&HRight3&HRight4&HRight5&Hk). unfold Put_steps in Hk.
      exists (Length_steps _ H),
      (1 + Constr_nil_steps + 1 + Translate_steps _ b + 1 + Translate_steps _ g + 1 + Constr_pair_steps _ g + 1 + Constr_Some_steps +
       1 + Constr_cons_steps _ (Some (g, b)) + 1 + App'_steps _ H + 1 + MoveValue_steps _ _ (H++[Some(g,b)]) H + 1 + Reset_steps _ (Some (g, b)) +
       Reset_steps _ g).
      cbn; repeat split; try omega. now hnf; cbn; eauto 10.
      intros tmid () (HLength&HLengthInj); TMSimp. modpon HLength. 1: now intros i; destruct_fin i; cbn; auto.
      exists (Constr_nil_steps),
      (1 + Translate_steps _ b + 1 + Translate_steps _ g + 1 + Constr_pair_steps _ g + 1 + Constr_Some_steps +
       1 + Constr_cons_steps _ (Some (g, b)) + 1 + App'_steps _ H + 1 + MoveValue_steps _ _ (H++[Some(g,b)]) H + 1 + Reset_steps _ (Some (g, b)) +
       Reset_steps _ g).
      cbn; repeat split; try omega. now rewrite !Nat.add_assoc.
      intros tmid0 () (HNil&HNilInj); TMSimp. modpon HNil. simpl_surject. exact (HLength1 Fin0).
      exists (Translate_steps _ b),
      (1 + Translate_steps _ g + 1 + Constr_pair_steps _ g + 1 + Constr_Some_steps + 1 + Constr_cons_steps _ (Some (g, b)) +
       1 + App'_steps _ H + 1 + MoveValue_steps _ _ (H++[Some(g,b)]) H + 1 + Reset_steps _ (Some (g, b)) + Reset_steps _ g).
      cbn; repeat split; try omega. now hnf; cbn; eexists; split; eauto. now rewrite !Nat.add_assoc.
      intros tmid1 () (HTranslate&HTranslateInj); TMSimp. modpon HTranslate.
      exists (Translate_steps _ g),
      (1 + Constr_pair_steps _ g + 1 + Constr_Some_steps + 1 + Constr_cons_steps _ (Some (g, b)) +
       1 + App'_steps _ H + 1 + MoveValue_steps _ _ (H++[Some(g,b)]) H + 1 + Reset_steps _ (Some (g, b)) + Reset_steps _ g).
      cbn; repeat split; try omega. now hnf; cbn; eauto. now rewrite !Nat.add_assoc.
      intros tmid2 () (HTranslate'&HTranslateInj'); TMSimp. modpon HTranslate'.
      exists (Constr_pair_steps _ g),
      (1 + Constr_Some_steps + 1 + Constr_cons_steps _ (Some (g, b)) +
       1 + App'_steps _ H + 1 + MoveValue_steps _ _ (H++[Some(g,b)]) H + 1 + Reset_steps _ (Some (g, b)) + Reset_steps _ g).
      cbn; repeat split; try omega. 2: now rewrite !Nat.add_assoc.
      { hnf; cbn; eexists; split; simpl_surject; eauto; contains_ext. }
      intros tmid3 () (HPair&HPairInj); TMSimp. modpon HPair.
      exists (Constr_Some_steps),
      (1 + Constr_cons_steps _ (Some (g, b)) + 1 + App'_steps _ H + 1 + MoveValue_steps _ _ (H++[Some(g,b)]) H + 1 +
       Reset_steps _ (Some (g, b)) + Reset_steps _ g).
      cbn; repeat split; try omega. now rewrite !Nat.add_assoc.
      intros tmid4 () (HSome&HSomeInj); TMSimp. specialize (HSome (g,b)); modpon HSome.
      exists (Constr_cons_steps _ (Some (g, b))),
         (1 + App'_steps _ H + 1 + MoveValue_steps _ _ (H++[Some(g,b)]) H + 1 + Reset_steps _ (Some (g, b)) + Reset_steps _ g).
      cbn; repeat split; try omega. 2: now rewrite !Nat.add_assoc.
      { do 2 eexists; repeat split; simpl_surject; eauto. contains_ext. }
      intros tmid5 () (HCons&HConsInj); TMSimp. specialize (HCons [] (Some (g,b))); modpon HCons.
      exists (App'_steps _ H), (1 + MoveValue_steps _ _ (H++[Some(g,b)]) H + 1 + Reset_steps _ (Some (g, b)) + Reset_steps _ g).
      cbn; repeat split; try omega. 2: now rewrite !Nat.add_assoc.
      { hnf; cbn. do 2 eexists; repeat split; simpl_surject; eauto. }
      intros tmid6 () (HApp&HAppInj); TMSimp. modpon HApp.
      exists (MoveValue_steps _ _ (H++[Some(g,b)]) H), (1 + Reset_steps _ (Some (g, b)) + Reset_steps _ g).
      cbn; repeat split; try omega. 2: now rewrite !Nat.add_assoc.
      { hnf; cbn. do 2 eexists; repeat split; simpl_surject; eauto.
        now rewrite (MoveValue_steps_comp Encode_Heap Encode_Heap retr_heap_step retr_heap_step). }
      intros tmid7 () (HMove&HMoveInj); TMSimp. modpon HMove.
      exists (Reset_steps _ (Some (g, b))), (Reset_steps _ g).
      cbn; repeat split; try omega.
      { hnf; cbn. exists (Some (g, b)). split; eauto. contains_ext. now setoid_rewrite Reset_steps_comp. } reflexivity. (* oh omega... *)
      intros tmid8 () (HReset&HResetInj); TMSimp. specialize (HReset (Some (g,b))); modpon HReset.
      { hnf; cbn. exists g. repeat split; eauto. contains_ext. now setoid_rewrite Reset_steps_comp. }
    }
  Qed.


  Definition Step_app_Rel : pRel sigStep^+ bool 11 :=
    fun tin '(yout, tout) =>
      forall (T V : list HClos) (H : Heap) (a : HAd) (P : Pro),
        tin[@Fin0] ≃ T ->
        tin[@Fin1] ≃ V ->
        tin[@Fin2] ≃ H ->
        tin[@Fin3] ≃(Encode_map Encode_Prog retr_pro_step) P ->
        tin[@Fin4] ≃(Encode_map Encode_nat retr_nat_step_clos_ad) a ->
        (forall i : Fin.t 6, isRight tin[@FinR 5 i]) ->

        match yout, V with
        | true, g :: (b, Q) :: V =>
          let (c, H') := put H (Some (g, b)) in (* This simplifys immediatly by computation *)
          tout[@Fin0] ≃ (c, Q) :: tailRecursion (a, P) T /\
          tout[@Fin1] ≃ V /\
          tout[@Fin2] ≃ H' /\
          (forall i : Fin.t 8, isRight tout[@FinR 3 i])
        | false, [] => True
        | false, [_] => True
        | _, _ => False
        end.

  
  Definition Step_app : pTM sigStep^+ bool 11 :=
    If (MatchList sigHClos_fin ⇑ _ @ [|Fin1; Fin5|])
       (If (MatchList sigHClos_fin ⇑ _ @ [|Fin1; Fin6|])
           (Return (MatchPair sigHAd_fin sigPro_fin ⇑ retr_clos_step @ [|Fin6; Fin7|];;
                    TailRec @ [|Fin0; Fin3; Fin4|];;
                    Reset _ @ [|Fin4|];;
                    Put @ [|Fin2; Fin5; Fin7; Fin8; Fin9; Fin10|];;
                    ConsClos @ [|Fin0; Fin8; Fin6|])
                   (true))
           (Return Nop false))
       (Return Nop false)
  .


  Lemma Step_app_Realise : Step_app ⊨ Step_app_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Step_app. repeat TM_Correct.
      - apply TailRec_Realise.
      - apply Reset_Realise with (cX := Encode_map Encode_nat retr_nat_step_clos_ad).
      - apply Put_Realise.
      - apply ConsClos_Realise.
    }
    {
      intros tin (yout, tout) H. cbn. intros T V heap a P HEncT HEncV HEncH HEncP HEncA HInt.
      TMSimp. rename H into HIf.
      destruct HIf; TMSimp.
      { (* Then of first [MatchList], i.e. [V = g :: V'] *) rename H into HMatchList, H0 into HIf'.
        modpon HMatchList. destruct V as [ | g V']; auto; modpon HMatchList.
        destruct HIf'; TMSimp. (* This takes long *)
        {
          rename H into HMatchList'; rename H0 into HMatchPair; rename H1 into HTailRec; rename H2 into HReset; rename H3 into HPut; rename H4 into HConsClos.
          modpon HMatchList'. destruct V' as [ | (b, Q) V'']; auto. modpon HMatchList'.
          specialize (HMatchPair (b,Q)). modpon HMatchPair. cbn in *.
          modpon HTailRec.
          modpon HReset.
          modpon HPut.
          modpon HConsClos.
          repeat split; auto.
          intros i; destruct_fin i; auto; TMSimp_goal; auto.
        }
        { modpon H. destruct V'; auto. }
      }
      { modpon H. destruct V; auto. }
    }
  Qed.


  Definition Step_app_steps_MatchList' T g V' H P a :=
    match V' with
    | nil => 0 (* Nop *)
    | (b, Q) :: V'' =>
      4 + MatchPair_steps _ b + TailRec_steps P a + Reset_steps _ a + Put_steps H g b + ConsClos_steps Q (length H)
    end.

  Definition Step_app_steps_MatchList T V H P a :=
    match V with
    | nil => 0 (* Nop *)
    | g :: V' => 1 + MatchList_steps _ V' + Step_app_steps_MatchList' T g V' H P a
    end.
  
  Definition Step_app_steps T V H a P := 1 + MatchList_steps _ V + Step_app_steps_MatchList T V H P a.

  Definition Step_app_T : tRel sigStep^+ 11 :=
    fun tin k =>
      exists (T V : list HClos) (H : Heap) (P : Pro) (a : HAd),
        tin[@Fin0] ≃ T /\
        tin[@Fin1] ≃ V /\
        tin[@Fin2] ≃ H /\
        tin[@Fin3] ≃(Encode_map Encode_Prog retr_pro_step) P /\
        tin[@Fin4] ≃(Encode_map Encode_nat retr_nat_step_clos_ad) a /\
        (forall i : Fin.t 6, isRight tin[@FinR 5 i]) /\
        Step_app_steps T V H a P <= k.

  Lemma Step_app_Terminates : projT1 Step_app ↓ Step_app_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Step_app. repeat TM_Correct.
      - apply TailRec_Realise.
      - apply TailRec_Terminates.
      - apply Reset_Realise with (cX := Encode_map Encode_nat retr_nat_step_clos_ad).
      - apply Reset_Terminates with (cX := Encode_map Encode_nat retr_nat_step_clos_ad).
      - apply Put_Realise.
      - apply Put_Terminates.
      - apply ConsClos_Terminates.
    }
    {
      intros tin k. intros (T&V&H&P&a&HEncT&HEncV&HEncH&HEncP&HEncA&HInt&Hk). unfold Step_app_steps in Hk.
      exists (MatchList_steps _ V), (Step_app_steps_MatchList T V H P a).
      cbn; repeat split; try omega.
      { exists V. repeat split; simpl_surject; eauto. apply HInt. }
      intros tmid bml1 (HMatchList&HMatchListInj); TMSimp. modpon HMatchList.
      destruct bml1, V as [ | g V']; auto; modpon HMatchList.
      {
        unfold Step_app_steps_MatchList.
        exists (MatchList_steps _ V'), (Step_app_steps_MatchList' T g V' H P a).
        cbn; repeat split; try omega.
        { exists V'. repeat split; simpl_surject; eauto. }
        intros tmid1 bml2 (HMatchList'&HMatchListInj'); TMSimp. modpon HMatchList'.
        destruct bml2, V' as [ | (b, Q) V'']; auto; modpon HMatchList'.
        {
          unfold Step_app_steps_MatchList'.
          exists (MatchPair_steps _ b), (1 + TailRec_steps P a + 1 + Reset_steps _ a + 1 + Put_steps H g b + ConsClos_steps Q (length H)).
          cbn; repeat split; try omega.
          { hnf; cbn. exists (b, Q). repeat split; simpl_surject; eauto. contains_ext. }
          intros tmid2 () (HMatchPair&HMatchPairInj); TMSimp. specialize (HMatchPair (b,Q)); modpon HMatchPair.
          exists (TailRec_steps P a), (1 + Reset_steps _ a + 1 + Put_steps H g b + ConsClos_steps Q (length H)).
          cbn; repeat split; try omega. 2: now rewrite !Nat.add_assoc.
          { hnf; cbn. do 3 eexists. repeat split; simpl_surject; eauto. }
          intros tmid3 () (HTailRec&HTailRecInj); TMSimp. modpon HTailRec.
          exists (Reset_steps _ a), (1 + Put_steps H g b + ConsClos_steps Q (length H)).
          cbn; repeat split; try omega. 2: now rewrite !Nat.add_assoc.
          { hnf; cbn. do 1 eexists. repeat split; simpl_surject; eauto. now setoid_rewrite Reset_steps_comp. }
          intros tmid4 () (HReset&HResetInj); TMSimp. modpon HReset.
          exists (Put_steps H g b), (ConsClos_steps Q (length H)).
          cbn; repeat split; try omega.
          { hnf; cbn. do 3 eexists. repeat split; simpl_surject; eauto; contains_ext. }
          intros tmid5 () (HPut&HInjPut); TMSimp. modpon HPut.
          { hnf; cbn. do 3 eexists. repeat split; simpl_surject; eauto; contains_ext. }
        }
      }
    }
  Qed.


  Definition Step_var_Rel : pRel sigStep^+ bool 8 :=
    fun tin '(yout, tout) =>
      forall (T V : list HClos) (H : Heap) (a : HAd) (n : nat) (P : Pro),
        tin[@Fin0] ≃ T ->
        tin[@Fin1] ≃ V ->
        tin[@Fin2] ≃ H ->
        tin[@Fin3] ≃(Encode_map Encode_Prog retr_pro_step) P ->
        tin[@Fin4] ≃(Encode_map Encode_nat retr_nat_step_clos_ad) a ->
        tin[@Fin5] ≃(Encode_map Encode_nat retr_nat_step_clos_var) n ->
        isRight tin[@Fin6] -> isRight tin[@Fin7] ->
        match yout with
        | true =>
          exists (g : HClos),
          lookup H a n = Some g /\
          tout[@Fin0] ≃ tailRecursion (a, P) T /\
          tout[@Fin1] ≃ g :: V /\
          tout[@Fin2] ≃ H /\
          (forall i : Fin.t 5, isRight tout[@FinR 3 i])
        | false => lookup H a n = None
        end
  .
  
  Definition Step_var : pTM sigStep^+ bool 8 :=
    TailRec @ [|Fin0; Fin3; Fin4|];;
    If (Step_Lookup @ [|Fin2; Fin4; Fin5; Fin6; Fin7|])
       (Return (Constr_cons sigHClos_fin ⇑ _ @ [|Fin1; Fin6|];;
                Reset _ @ [|Fin6|])
               (true))
       (Return Nop false).

  Local Definition retr_closure_step : Retract sigHClos sigStep := ComposeRetract _ retr_closures_step.

  Lemma Step_var_Realise : Step_var ⊨ Step_var_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Step_var. repeat TM_Correct.
      - apply TailRec_Realise.
      - apply Lookup_Realise.
      - apply Reset_Realise with (cX := Encode_map Encode_HClos retr_closure_step).
    }
    {
      intros tin (yout, tout) H. cbn. intros T V heap a n P HEncT HEncV HEncHeap HEncP HEncA HEncN HRight6 HRight7.
      TMSimp. rename H into HTailRec, H0 into HIf.
      modpon HTailRec.
      destruct HIf; TMSimp.
      { rename H into HLookup, H0 into HCons, H1 into HReset. 
        modpon HLookup. destruct HLookup as (g&HLookup); modpon HLookup.
        modpon HCons. modpon HReset.
        eexists; repeat split; eauto. intros i; destruct_fin i; auto; TMSimp_goal; auto.
      }
      { now modpon H. }
    }
  Qed.


  Definition Step_var_steps_Lookup P V H a n :=
    match lookup H a n with
    | None => 0 (* Nop *)
    | Some g => 1 + Constr_cons_steps _ g + Reset_steps _ g
    end.
    

  Definition Step_var_steps P V H a n := 2 + TailRec_steps P a + Lookup_steps H a n + Step_var_steps_Lookup P V H a n.

  Definition Step_var_T : tRel sigStep^+ 8 :=
    fun tin k =>
      exists (T V : list HClos) (H : Heap) (a : HAd) (n : nat) (P : Pro),
        tin[@Fin0] ≃ T /\
        tin[@Fin1] ≃ V /\
        tin[@Fin2] ≃ H /\
        tin[@Fin3] ≃(Encode_map Encode_Prog retr_pro_step) P /\
        tin[@Fin4] ≃(Encode_map Encode_nat retr_nat_step_clos_ad) a /\
        tin[@Fin5] ≃(Encode_map Encode_nat retr_nat_step_clos_var) n /\
        isRight tin[@Fin6] /\ isRight tin[@Fin7] /\
        Step_var_steps P V H a n <= k.

  Lemma Step_var_Terminates : projT1 Step_var ↓ Step_var_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Step_var. repeat TM_Correct.
      - apply TailRec_Realise.
      - apply TailRec_Terminates.
      - apply Lookup_Realise.
      - apply Lookup_Terminates.
      - apply Reset_Terminates with (cX := Encode_map Encode_HClos retr_closure_step).
    }
    {
      intros tin k. intros (T&V&H&a&n&P&HEncT&HEncV&HEncH&HEncP&HEncA&HEncN&HRight6&HRigth7&Hk). unfold Step_var_steps in Hk.
      exists (TailRec_steps P a), (1 + Lookup_steps H a n + Step_var_steps_Lookup P V H a n).
      cbn; repeat split; try omega.
      { hnf; cbn. do 3 eexists; repeat split; eauto. }
      intros tmid () (HTailRec&HTailRecInj); TMSimp. modpon HTailRec.
      exists (Lookup_steps H a n), (Step_var_steps_Lookup P V H a n).
      cbn; repeat split; try omega.
      { hnf; cbn. do 3 eexists; repeat split; eauto. }
      intros tmid0 ymid (HLookup&HLookupInj); TMSimp. modpon HLookup.
      destruct ymid.
      {
        destruct HLookup as (g&HLookup); modpon HLookup.
        unfold Step_var_steps_Lookup. rewrite HLookup.
        exists (Constr_cons_steps _ g), (Reset_steps _ g).
        cbn; repeat split; try omega.
        { hnf; cbn. do 2 eexists; repeat split; simpl_surject; eauto. contains_ext. }
        intros tmid1 () (HCons&HConsInj); TMSimp. modpon HCons.
        { hnf; cbn. do 1 eexists; repeat split; simpl_surject; eauto. contains_ext. now setoid_rewrite Reset_steps_comp. }
      }
      { omega. }
    }
  Qed.


  (* I forgot that [WHILE] takes a machine over [option unit] instead of [bool]. But that's no problem since we have [ChangePartition]. *)
  Coercion bool2optunit := fun b : bool => if b then None else Some tt.

  Definition Step : pTM sigStep^+ (option unit) 11 :=
    ChangePartition
      (If (MatchList sigHClos_fin ⇑ _ @ [|Fin0; Fin3|])
          (MatchPair sigHAd_fin sigPro_fin ⇑ retr_clos_step @ [|Fin3; Fin4|];;
           If (MatchList sigTok_fin ⇑ retr_pro_step @ [|Fin3; Fin5|])
              (MATCH (MatchTok ⇑ retr_tok_step @ [|Fin5|])
                     (fun t : option ATok =>
                        match t with
                        | Some lamAT =>
                          Step_lam @ [|Fin0; Fin1; Fin2; Fin3; Fin4; Fin5; Fin6; Fin7; Fin8; Fin9|]
                        | Some appAT =>
                          Step_app
                        | Some retAT =>
                          Return Nop false
                        | None (* Variable *) =>
                          Step_var @ [|Fin0; Fin1; Fin2; Fin3; Fin4; Fin5; Fin6; Fin7|]
                        end))
              (Return Nop false))
          (Return Nop false)
        ) bool2optunit.


  Definition Step_Rel : pRel sigStep^+ (option unit) 11 :=
    fun tin '(yout, tout) =>
      forall (T V : list HClos) (H: Heap),
        tin[@Fin0] ≃ T ->
        tin[@Fin1] ≃ V ->
        tin[@Fin2] ≃ H ->
        (forall i : Fin.t 8, isRight tin[@FinR 3 i]) ->
        match yout with
        | None =>
          exists T' V' H',
          step (T,V,H) (T',V',H') /\
          tout[@Fin0] ≃ T' /\
          tout[@Fin1] ≃ V' /\
          tout[@Fin2] ≃ H' /\
          (forall i : Fin.t 8, isRight tout[@FinR 3 i])
        | Some tt =>
          halt_state (T,V,H) /\
          match T with
          | nil => 
            tout[@Fin0] ≃ (@nil HClos) /\
            tout[@Fin1] ≃ V /\
            tout[@Fin2] ≃ H /\
            (forall i : Fin.t 8, isRight tout[@FinR 3 i])
          | _ => True
          end
        end.

  Lemma Step_Realise : Step ⊨ Step_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Step. repeat TM_Correct.
      - eapply RealiseIn_Realise. apply MatchTok_Sem.
      - apply Step_lam_Realise.
      - apply Step_app_Realise.
      - apply Step_var_Realise.
    }
    {
      intros tin (yout, tout) H. cbn. intros T V Heap HEncT HEncV HEncHeap HInt.
      TMSimp. rename H0 into HIf.
      destruct HIf; TMSimp.
      { (* Then of [MatchList], i.e. [T = (a, P) :: T'] *) rename H into HMatchList, H0 into HMatchPair, H1 into HIf'.
        modpon HMatchList. destruct T as [ | (a, P) T' ]; auto; modpon HMatchList.
        specialize (HMatchPair (a, P)); modpon HMatchPair.
        destruct HIf'; TMSimp.
        { (* Then of second [MatchList], i.e [P = t :: P'] *) rename H into HMatchList', H0 into HMatchTok, H1 into HCase.
          modpon HMatchList'. destruct P as [ | t P']; auto; modpon HMatchList'.
          modpon HMatchTok. destruct ymid0 as [ [ | | ] | ], t; auto; simpl_surject; cbn in *.
          { (* retT *)
            destruct HCase as (->&(?&->)); cbn. split; auto. hnf. intros s HStep. inv HStep.
          }
          { (* lamT *)
            rename HCase into HStepLam. modpon HStepLam; TMSimp_goal; eauto; try contains_ext.
            intros i; destruct_fin i; auto; TMSimp_goal; cbn; auto.
            destruct ymid.
            - cbn. destruct HStepLam as (jump_P&jump_Q&HStepLam); modpon HStepLam.
              do 3 eexists. repeat split; eauto.
              + econstructor. eauto.
              + generalize (HStepLam4 Fin0); generalize (HStepLam4 Fin1); generalize (HStepLam4 Fin2); generalize (HStepLam4 Fin3); generalize (HStepLam4 Fin4); generalize (HStepLam4 Fin5); generalize (HStepLam4 Fin6); cbn; TMSimp_goal; intros.
                destruct_fin i; TMSimp_goal; auto. rewrite HStepLam0 by vector_not_in. now TMSimp_goal.
            - cbn. split; auto. intros s' HStep. inv HStep. congruence.
          }
          { (* appT *)
            rename HCase into HStepApp. cbn in HStepApp.
            cbv [put] in *. modpon HStepApp; TMSimp_goal; eauto; try contains_ext.
            { intros i; destruct_fin i; auto; TMSimp_goal; auto. }
            destruct ymid; cbn.
            - destruct V as [ | g V']; auto.
              destruct V' as [ | (b, Q) V'']; auto. modpon HStepApp.
              do 3 eexists. repeat split; eauto.
              + econstructor. reflexivity.
            - split; auto. intros s' HStep. now inv HStep.
          }
          { (* varT *)
            rename HCase into HStepVar. modpon HStepVar; TMSimp_goal; eauto; try contains_ext.
            destruct ymid; cbn.
            - destruct HStepVar as (g&HStepVar); modpon HStepVar.
              do 3 eexists; repeat split; eauto.
              + econstructor; eauto.
              + generalize (HStepVar4 Fin0); generalize (HStepVar4 Fin1); generalize (HStepVar4 Fin2); generalize (HStepVar4 Fin3); generalize (HStepVar4 Fin4); cbn; TMSimp_goal; intros.
                simpl_not_in. destruct_fin i; auto; TMSimp_goal; auto.
            - split; auto. intros s' HStep. inv HStep. congruence.
          }
        }
        { (* Else of the second [MatchList], i.e [P = nil] *)
          modpon H. destruct P; auto. split; auto. intros s HStep. now inv HStep.
        }
      }
      { (* Else of the first [MatchList], i.e. [T = nil] *)
        modpon H. destruct T; auto. modpon H. split; auto. intros s HStep. now inv HStep.
        repeat split; eauto. intros i; destruct_fin i; TMSimp_goal; auto.
      }
    }
  Qed.



  Definition Step_steps_MatchTok a t P' T' V H :=
    match t with
    | varT n => Step_var_steps P' V H a n
    | appT => Step_app_steps T' V H a P'
    | lamT => Step_lam_steps P' a
    | retT => 0 (* Nop *)
    end.

  Definition Step_steps_MatchList' a P T' V H :=
    match P with
    | nil => 0
    | t :: P' => 1 + MatchTok_steps + Step_steps_MatchTok a t P' T' V H
    end.

  Definition Step_steps_MatchList T V H :=
    match T with
    | nil => 0
    | (a,P) :: T' => 2 + MatchPair_steps _ a + MatchList_steps _ P + Step_steps_MatchList' a P T' V H
    end.

  Definition Step_steps T V H :=
    1 + MatchList_steps _ T + Step_steps_MatchList T V H.

  
  Definition Step_T : tRel sigStep^+ 11 :=
    fun tin k =>
      exists (T V : list HClos) (H: Heap),
        tin[@Fin0] ≃ T /\
        tin[@Fin1] ≃ V /\
        tin[@Fin2] ≃ H /\
        (forall i : Fin.t 8, isRight tin[@FinR 3 i]) /\
        Step_steps T V H <= k.


  Lemma Step_Terminates : projT1 Step ↓ Step_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Step. repeat TM_Correct.
      - eapply RealiseIn_Realise. apply MatchTok_Sem.
      - eapply RealiseIn_TerminatesIn. apply MatchTok_Sem.
      - apply Step_lam_Terminates.
      - apply Step_app_Terminates.
      - apply Step_var_Terminates.
    }
    {
      intros tin k (T&V&H&HEncT&HEncV&HEncH&HInt&Hk). unfold Step_steps in Hk.
      exists (MatchList_steps _ T), (Step_steps_MatchList T V H). cbn; repeat split; try omega.
      { do 1 eexists; repeat split; simpl_surject; eauto. apply HInt. }
      intros tmid bif (HMatchList&HMatchListInj); TMSimp. modpon HMatchList.
      destruct bif, T as [ | (a,P) T']; cbn; auto; modpon HMatchList.
      exists (MatchPair_steps _ a), (1 + MatchList_steps _ P + Step_steps_MatchList' a P T' V H). cbn; repeat split; try omega.
      { hnf; cbn. exists (a, P); repeat split; simpl_surject; eauto. contains_ext. }
      intros tmid0 () (HMatchPair&HMatchPairInj); TMSimp. specialize (HMatchPair (a,P)). modpon HMatchPair. cbn in *.
      exists (MatchList_steps _ P), (Step_steps_MatchList' a P T' V H). cbn; repeat split; try omega. 2: reflexivity.
      { hnf; cbn. exists P; repeat split; simpl_surject; eauto. contains_ext. }
      intros tmid1 bif (HMatchList'&HMatchListInj'); TMSimp. modpon HMatchList'.
      destruct bif, P as [ | t P']; auto; modpon HMatchList'. cbn.
      exists (MatchTok_steps), (Step_steps_MatchTok a t P' T' V H). cbn; repeat split; try omega.
      intros tmid2 ymid (HMatchTok&HMatchTokInj); TMSimp. modpon HMatchTok.
      destruct ymid as [ [ | | ] | ]; destruct t; cbn; auto; simpl_surject.
      - hnf; cbn. do 5 eexists; repeat split; TMSimp_goal; eauto. contains_ext. intros i; destruct_fin i; cbn; TMSimp_goal; auto.
      - hnf; cbn. do 5 eexists; repeat split; TMSimp_goal; eauto. contains_ext. intros i; destruct_fin i; cbn; TMSimp_goal; auto.
      - hnf; cbn. do 6 eexists; repeat split; TMSimp_goal; eauto. contains_ext. contains_ext.
    }
  Qed.
  


End StepMachine.