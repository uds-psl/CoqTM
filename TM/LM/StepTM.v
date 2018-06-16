Require Import HeapTM.
Require Import LookupTM JumpTargetTM.
Require Import MatchList TokTM.
Require Import ListTM.


(** ** Step semantics *)


(** ** Step Machine *)


Section StepMachine.

  Implicit Types H : Heap.
  Implicit Types T V : list HClos.
  Implicit Types a b c : HAd.
  Implicit Types g : HClos.
  Implicit Types (P Q : Pro).

  Section Semantics.

    Definition put H e : HAd * Heap := (|H|, H++[e]).

    Definition tailRecursion : HClos -> list HClos -> list HClos :=
      fun '(a, P) T =>
        match P with
        | [] => T
        | _ => (a, P) :: T
        end.


    Definition state : Type := list HClos * list HClos * Heap.
    
    Inductive step : state -> state -> Prop :=
    | step_pushVal P P' Q a T V H :
        jumpTarget O [] P = Some (Q, P') ->
        step ((a, (lamT :: P)) :: T, V, H) (tailRecursion (a, P') T, (a, Q) :: V, H)
    | step_beta a b g P Q H H' c T V :
        put H (Some (g, b)) = (c, H') ->
        step ((a, (appT :: P)) :: T, g :: (b, Q) :: V, H) ((c, Q) :: tailRecursion (a, P) T, V, H')
    | step_load P a x g T V H :
        lookup H a x = Some g ->
        step ((a, (varT x :: P)) :: T, V, H) (tailRecursion (a, P) T, g :: V, H)
    .

    Definition steps : state -> state -> Prop := star step.

    Definition step_fun : state -> option state :=
      fun '(T, V, H) =>
        match T with
        | (a, (lamT :: P)) :: T =>
          match jumpTarget O [] P with
          | Some (Q, P') =>
            Some (tailRecursion (a, P') T, (a, Q) :: V, H)
          | _ => None
          end
        | (a, (appT :: P)) :: T =>
          match V with
          | g :: (b, Q) :: V =>
            let (c, H') := put H (Some (g, b)) in
            Some ((c, Q) :: tailRecursion (a, P) T, V, H')
          | _ => None
          end
        | (a, (varT x :: P)) :: T =>
          match lookup H a x with
          | Some g => Some (tailRecursion (a, P) T, g :: V, H)
          | _ => None
          end
        | _ => None
        end.

    Goal forall s s', step s s' -> step_fun s = Some s'.
    Proof.
      induction 1; cbn; TMSimp; auto.
      unfold put in *. now inv_pair.
    Qed.

  End Semantics.
  

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

  Definition Step_lam_Rel : pRel sigStep^+ unit 10 :=
    ignoreParam (
        fun tin tout =>
          forall (T V : list HClos) (H : Heap) (a : HAd) (P : Pro) (Q P' : Pro),
            jumpTarget 0 [] P = Some (Q, P') ->
            tin[@Fin0] ≃ T ->
            tin[@Fin1] ≃ V ->
            tin[@Fin2] ≃ H ->
            tin[@Fin3] ≃(Encode_map Encode_Prog retr_pro_step) P ->
            tin[@Fin4] ≃(Encode_map Encode_nat retr_nat_step_clos_ad) a ->
            (forall i : Fin.t 5, isRight tin[@Fin.R 5 i]) ->
            tout[@Fin0] ≃ tailRecursion (a, P') T /\
            tout[@Fin1] ≃ (a, Q) :: V /\
            tout[@Fin2] ≃ H /\
            (forall i : Fin.t 7, isRight tout[@Fin.R 3 i])
      ).


  Definition Step_lam : pTM sigStep^+ unit 10 :=
    JumpTarget ⇑ retr_pro_step @ [|Fin3; Fin6; Fin7; Fin8; Fin9|];;
    TailRec @ [|Fin0; Fin3; Fin4|];;
    ConsClos @ [|Fin1; Fin4; Fin6|].
  

  Lemma Step_lam_Realise : Step_lam ⊨ Step_lam_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Step_lam. repeat TM_Correct.
      - apply JumpTarget_Realise.
      - apply TailRec_Realise.
      - apply ConsClos_Realise.
    }
    {
      intros tin ((), tout) H. cbn. intros T V heap a P Q P' HJump HEncT HEncV HEncHeap HEncP HEncA HInt.
      TMSimp. modpon H. (* JumpTarget *)
      { intros i; destruct_fin i; cbn; simpl_surject; auto. }
      modpon H0. (* TailRec *)
      specialize (H1 V Q a). modpon H1. (* ConsClos *)
      repeat split; auto.
      generalize (H3 Fin0); generalize (H3 Fin1); generalize (H3 Fin2); cbn; TMSimp_goal; intros; simpl_surject; destruct_fin i; TMSimp_goal; auto.
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
      TMSimp.
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
  

  Definition Step_app_Rel : pRel sigStep^+ unit 11 :=
    ignoreParam (
        fun tin tout =>
          forall (T V : list HClos) (H : Heap) (a : HAd) (P : Pro)
            (g : HClos) (b : HAd) (Q : Pro),
            let (c, H') := put H (Some (g, b)) in
            tin[@Fin0] ≃ T ->
            tin[@Fin1] ≃ g :: (b, Q) :: V ->
            tin[@Fin2] ≃ H ->
            tin[@Fin3] ≃(Encode_map Encode_Prog retr_pro_step) P ->
            tin[@Fin4] ≃(Encode_map Encode_nat retr_nat_step_clos_ad) a ->
            (forall i : Fin.t 6, isRight tin[@Fin.R 5 i]) ->
            tout[@Fin0] ≃ (c, Q) :: tailRecursion (a, P) T /\
            tout[@Fin1] ≃ V /\
            tout[@Fin2] ≃ H' /\
            (forall i : Fin.t 8, isRight tout[@Fin.R 3 i])
      ).

  
  Definition Step_app : pTM sigStep^+ unit 11 :=
    MatchList sigHClos_fin ⇑ _ @ [|Fin1; Fin5|];;
    MatchList sigHClos_fin ⇑ _ @ [|Fin1; Fin6|];;
    MatchPair sigHAd_fin sigPro_fin ⇑ retr_clos_step @ [|Fin6; Fin7|];;
    TailRec @ [|Fin0; Fin3; Fin4|];;
    Reset _ @ [|Fin4|];;
    Put @ [|Fin2; Fin5; Fin7; Fin8; Fin9; Fin10|];;
    ConsClos @ [|Fin0; Fin8; Fin6|].


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
      intros tin ((), tout) H. cbn. intros T V heap a P g b Q HEncT HEncV HEncH HEncP HEncA HInt.
      TMSimp.
      rename H into HMatchList; rename H0 into HMatchList'; rename H1 into HMatchPair; rename H2 into HTailRec; rename H3 into HReset; rename H4 into HPut; rename H5 into HConsClos.
      modpon HMatchList. destruct ymid; auto; modpon HMatchList.
      modpon HMatchList'. destruct ymid0; auto; modpon HMatchList'.
      specialize (HMatchPair (b,Q)). modpon HMatchPair. cbn in *.
      modpon HTailRec.
      modpon HReset.
      modpon HPut.
      modpon HConsClos.
      repeat split; auto.
      intros i; destruct_fin i; auto; TMSimp_goal; auto.
    }
  Qed.


  Definition Step_var_Rel : pRel sigStep^+ unit 8 :=
    ignoreParam (
        fun tin tout =>
          forall (T V : list HClos) (H : Heap) (a : HAd) (n : nat) (P : Pro) (g : HClos),
            lookup H a n = Some g ->
            tin[@Fin0] ≃ T ->
            tin[@Fin1] ≃ V ->
            tin[@Fin2] ≃ H ->
            tin[@Fin3] ≃(Encode_map Encode_Prog retr_pro_step) P ->
            tin[@Fin4] ≃(Encode_map Encode_nat retr_nat_step_clos_ad) a ->
            tin[@Fin5] ≃(Encode_map Encode_nat retr_nat_step_clos_var) n ->
            isRight tin[@Fin6] -> isRight tin[@Fin7] ->
            tout[@Fin0] ≃ tailRecursion (a, P) T /\
            tout[@Fin1] ≃ g :: V /\
            tout[@Fin2] ≃ H /\
            (forall i : Fin.t 5, isRight tout[@Fin.R 3 i])
      ).
  
  Definition Step_var : pTM sigStep^+ unit 8 :=
    TailRec @ [|Fin0; Fin3; Fin4|];;
    Step_Lookup @ [|Fin2; Fin4; Fin5; Fin6; Fin7|];;
    Constr_cons sigHClos_fin ⇑ _ @ [|Fin1; Fin6|];;
    Reset _ @ [|Fin6|].

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
      intros tin ((), tout) H. cbn. intros T V heap a n P g HLook HEncT HEncV HEncHeap HEncP HEncA HEncN HRight6 HRight7.
      TMSimp. rename H into HTailRec; rename H0 into HLookup; rename H1 into HCons; rename H2 into HReset.
      modpon HTailRec. modpon HLookup. modpon HCons. modpon HReset.
      repeat split; auto. intros i; destruct_fin i; auto; TMSimp_goal; auto.
    }
  Qed.


  Definition Step : pTM sigStep^+ unit 11 :=
    MatchList sigHClos_fin ⇑ _ @ [|Fin0; Fin3|];;
    MatchPair sigHAd_fin sigPro_fin ⇑ retr_clos_step @ [|Fin3; Fin4|];;
    MatchList sigTok_fin ⇑ retr_pro_step @ [|Fin3; Fin5|];;
    MATCH (MatchTok ⇑ retr_tok_step @ [|Fin5|])
          (fun t : option ATok =>
             match t with
             | Some lamAT =>
               Step_lam
             | Some appAT =>
               Step_app
             | Some retAT =>
               Nop default
             | None (* Variable *) =>
               Step_var @ [|Fin0; Fin1; Fin2; Fin3; Fin4; Fin5; Fin6; Fin7|]
             end). 

  Definition Step_Rel : pRel sigStep^+ unit 11 :=
    ignoreParam (
        fun tin tout =>
          forall (T : list HClos) (V : list HClos) (H : Heap) (T' : list HClos) (V' : list HClos) (H' : Heap),
            step (T, V, H) (T', V', H') ->
            tin[@Fin0] ≃ T ->
            tin[@Fin1] ≃ V ->
            tin[@Fin2] ≃ H ->
            (forall i : Fin.t 8, isRight tin[@Fin.R 3 i]) ->
            tout[@Fin0] ≃ T' /\
            tout[@Fin1] ≃ V' /\
            tout[@Fin2] ≃ H' /\
            (forall i : Fin.t 8, isRight tout[@Fin.R 3 i])
      ).


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
      intros tin ((), tout) H. cbn. intros T V heap T' V' heap' HStep HEncT HEncV HEncHeap HInt.
      TMSimp. (* This takes long *)
      rename H into HMatchList; rename H0 into HMatchPair; rename H1 into HMatchList'; rename H2 into HMatchTok.
      modpon HMatchList. destruct ymid, T as [ | (a, P) T]; auto. 2: now inv HStep. modpon HMatchList.
      specialize (HMatchPair (a, P)). modpon HMatchPair.
      modpon HMatchList'. destruct ymid0, P as [ | t P]; auto; modpon HMatchList'. 2: now inv HStep.
      modpon HMatchTok. destruct ymid1 as [ [ | | ] | ], t; auto; simpl_surject; inv HStep; cbn in *.
      - (* lamT *)
        rename H3 into HStepLam. modpon HStepLam; TMSimp_goal; eauto; try contains_ext.
        intros i; destruct_fin i; auto; TMSimp_goal; auto.
      - (* appT *)
        rename H3 into HStepApp. cbn in HStepApp. move HStepApp at bottom. (* for less scrolling... *)
        cbv [put] in *. inv H1.
        modpon HStepApp; TMSimp_goal; eauto; try contains_ext.
        intros i; destruct_fin i; auto; TMSimp_goal; auto.
      - (* varT *)
        rename H3 into HStepVar. modpon HStepVar; TMSimp_goal; eauto; try contains_ext.
        generalize (HStepVar3 Fin0); generalize (HStepVar3 Fin1); generalize (HStepVar3 Fin2); generalize (HStepVar3 Fin3); generalize (HStepVar3 Fin4); cbn; TMSimp_goal; intros.
        simpl_not_in. repeat split; auto. intros i; destruct_fin i; auto; TMSimp_goal; auto.
    }
  Qed.


End StepMachine.