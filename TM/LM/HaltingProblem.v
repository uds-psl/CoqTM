Require Import ProgrammingTools.
Require Import LM.Semantics LM.Alphabets LM.StepTM.


Local Arguments plus : simpl never.
Local Arguments mult : simpl never.


(** Initialise the alphabet of the [Step] Machine *)
Definition sigStep : Type := sigList sigHClos + sigHeap.
Definition retr_heap_step : Retract sigHeap sigStep := _.
Definition retr_closures_step : Retract (sigList sigHClos) sigStep := _.


Definition Loop := WHILE (Step retr_closures_step retr_heap_step).

Definition Loop_Rel : pRel sigStep^+ unit 11 :=
  ignoreParam (
      fun tin tout =>
        forall (T V : list HClos) (H: Heap),
          tin[@Fin0] ≃ T ->
          tin[@Fin1] ≃ V ->
          tin[@Fin2] ≃ H ->
          (forall i : Fin.t 8, isRight tin[@FinR 3 i]) ->
          exists T' V' H',
            steps (T,V,H) (T',V',H') /\
            halt_state (T',V',H') /\
            match T' with
            | nil => 
              tout[@Fin0] ≃ @nil HClos /\
              tout[@Fin1] ≃ V' /\
              tout[@Fin2] ≃ H' /\
              (forall i : Fin.t 8, isRight tout[@FinR 3 i])
            | _ => True
            end
    ).

Lemma Loop_Realise : Loop ⊨ Loop_Rel.
Proof.
  eapply Realise_monotone.
  { unfold Loop. TM_Correct.
    - apply Step_Realise.
  }
  {
    apply WhileInduction; intros; intros T V heap HEncT HEncV HEncHep HInt; cbn in *.
    {
      modpon HLastStep. destruct_unit; cbn in *. modpon HLastStep.
      exists T, V, heap. repeat split; auto. constructor.
    }
    {
      modpon HStar. destruct HStar as (T1&V1&heap1&HStar); modpon HStar.
      modpon HLastStep. destruct HLastStep as (T2&V2&heap2&HLastStep); modpon HLastStep.
      do 3 eexists. repeat split. econstructor 2. all: eauto.
    }
  }
Qed.



Fixpoint Loop_steps T V H k :=
  match k with
  | 0 => Step_steps T V H
  | S k' =>
    match step_fun (T, V, H) with
    | Some (T',V',H') =>
      if is_halt_state (T',V',H')
      then 1 + Step_steps T V H + Step_steps T' V' H'
      else 1 + Step_steps T V H + Loop_steps T' V' H' k'
    | None => Step_steps T V H
    end
  end.


Definition Loop_T : tRel sigStep^+ 11 :=
  fun tin i => exists T V H k,
      halts_k (T,V,H) k /\
      tin[@Fin0] ≃ T /\
      tin[@Fin1] ≃ V /\
      tin[@Fin2] ≃ H /\
      (forall i : Fin.t 8, isRight tin[@FinR 3 i]) /\
      Loop_steps T V H k <= i.


Lemma Loop_Terminates : projT1 Loop ↓ Loop_T.
Proof.
  eapply TerminatesIn_monotone.
  { unfold Loop. TM_Correct.
    - apply Step_Realise.
    - apply Step_Terminates. }
  {
    eapply WhileCoInduction. intros tin i. intros (T&V&Heap&k&Halt&HEncT&HEncV&HEncH&HInt&Hi).
    exists (Step_steps T V Heap). repeat split.
    { hnf. do 3 eexists; repeat split; eauto. }
    intros ymid tmid HStep. cbn in HStep. modpon HStep. destruct ymid as [ () | ].
    - destruct HStep as (HStep&_).
      destruct Halt as (((T'&V')&H')&HSteps&HTerm). pose proof (halt_state_steps_k HStep HSteps) as (H&->); inv H. cbn in *. assumption.
    - destruct HStep as (T1&V1&Heap1&HStep); modpon HStep.
      destruct Halt as (((T2&V2)&H2)&HSteps&HTerm).
      unfold Loop_T; cbn. 

      inv HSteps.
      + exfalso. eapply HTerm; eauto.
      + pose proof (step_functional HStep H) as <-. cbn -[step_fun] in *.
        rewrite (step_step_fun HStep) in Hi. rename k0 into k. move HTerm at bottom. clear H. rename H0 into HSteps.
        destruct (is_halt_state (T1, V1, Heap1)) eqn:EHalt.
        * apply is_halt_state_correct in EHalt. pose proof (halt_state_steps_k EHalt HSteps) as (H&->); inv H.
          exists (Step_steps T1 V1 Heap1). split.
          -- do 3 eexists. eexists 0. cbn -[step_fun]. repeat split; hnf; eauto.
          -- omega.
        * exists (Loop_steps T1 V1 Heap1 k). split.
          -- do 3 eexists. exists k. repeat split; hnf; eauto.
          -- omega.
  }
Qed.



Definition initTapes : state -> tapes sigStep^+ 11 :=
  fun '(T,V,H) => initValue T ::: initValue V ::: initValue H ::: Vector.const (initRight _) 8.


Definition Halts {sig: finType} {n: nat} (M : mTM sig n) (t : tapes sig n) :=
  exists outc k, loopM (initc M t) k = Some outc.


Theorem HaltingProblem s :
  halts s <-> Halts (projT1 Loop) (initTapes s).
Proof.
  destruct s as ((T&V)&Heap). split.
  {
    intros (s'&HSteps&HHalt).
    apply steps_steps_k in HSteps as (k&HSteps).
    destruct (@Loop_Terminates (initTapes (T,V,Heap)) (Loop_steps T V Heap k)) as (outc&Term).
    { cbn. hnf. do 4 eexists; repeat split; cbn; eauto.
      1: hnf; eauto.
      1-3: apply initValue_contains.
      intros i; destruct_fin i; cbn; apply initRight_isRight.
    }
    hnf. eauto.
  }
  {
    intros (tout&k&HLoop).
    pose proof Loop_Realise HLoop as HLoopRel. hnf in HLoopRel. modpon HLoopRel.
    1-3: apply initValue_contains.
    intros i; destruct_fin i; cbn; apply initRight_isRight.
    destruct HLoopRel as (T'&V'&H'&HStep&HTerm&_). cbn in *. hnf. eauto.
  }
Qed.


Print Assumptions HaltingProblem.