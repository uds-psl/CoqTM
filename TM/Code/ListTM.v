(** * Machines that compute list functions *)

Require Import ProgrammingTools.
Require Import MatchNat MatchList MatchSum. (* [TM.Code.MatchSum] contains [Constr_Some] and [Constr_None]. *)


Local Arguments skipn { A } !n !l.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.


Local Arguments Encode_list : simpl never.
Local Arguments Encode_nat : simpl never.


(** ** Implementation of [nth_error] *)

Section Nth.

  Variable (sig sigX : finType) (X : Type) (cX : codable sigX X).

  Variable (retr1 : Retract (sigList sigX) sig) (retr2 : Retract sigNat sig) (retr3 : Retract (sigOption sigX ) sig).
  Local Instance retr_X_list : Retract sigX sig := ComposeRetract (Retract_sigList_X _) retr1.
  Local Instance retr_X_opt : Retract sigX sig := ComposeRetract (Retract_sigOption_X _) retr3.

  (*
  Check _ : codable sig (list X).
  Check _ : codable sig nat.
  Check _ : codable sig (option X).
  *)

  (*
   * Nth_Step:
   * if ∃n'. n = S n'; n' -> n {
   *   if ∃x l'. l == x::l'; l' -> l {
   *     reset x
   *     continue
   *   } else {
   *     x = None
   *     return
   *   }
   * } else {
   *   if ∃x l'. l == x::l'; l' -> l {
   *     x = Some x
   *     return
   *   } else {
   *     x = None
   *     return
   *   }
   * }
   *
   * t0: l (copy)
   * t1: n (copy)
   * t2: x (output)
   *)

  Definition Nth_Step_Rel : Rel (tapes sig^+ 3) (option unit * tapes sig^+ 3) :=
    fun tin '(yout, tout) =>
      forall (l : list X) (n : nat),
        tin[@Fin0] ≃ l ->
        tin[@Fin1] ≃ n ->
        isRight tin[@Fin2] ->
        match yout, n, l with
        | None, S n', x :: l' => (* Recursion case *)
          tout[@Fin0] ≃ l' /\
          tout[@Fin1] ≃ n' /\
          isRight tout[@Fin2] (* continue *)
        | Some tt, S n', nil => (* list to short *)
          tout[@Fin0] ≃ l /\
          tout[@Fin1] ≃ n' /\
          tout[@Fin2] ≃ None (* return None *)
        | Some tt, 0, x::l' => (* return value *)
          tout[@Fin0] ≃ l' /\
          tout[@Fin1] ≃ 0 /\
          tout[@Fin2] ≃ Some x (* return Some x *)
        | Some tt, 0, nil => (* list to short *)
          tout[@Fin0] ≃ l /\
          tout[@Fin1] ≃ n /\
          tout[@Fin2] ≃ None (* return None *)
        | _, _, _ => False
        end.


  Definition Nth_Step : { M : mTM sig^+ 3 & states M -> option unit } :=
    If (LiftTapes (ChangeAlphabet MatchNat _) [|Fin1|])
       (If (LiftTapes (ChangeAlphabet (MatchList sigX) _) [|Fin0; Fin2|])
           (Return (LiftTapes (Reset _) [|Fin2|]) (None))
           (Return (LiftTapes (ChangeAlphabet (Constr_None _) _) [|Fin2|]) (Some tt)))
       (If (LiftTapes (ChangeAlphabet (MatchList sigX) _) [|Fin0; Fin2|])
           (Return (LiftTapes (Translate retr_X_list retr_X_opt;;
                            ChangeAlphabet (Constr_Some sigX) _) [|Fin2|]) (Some tt))
           (Return (LiftTapes (ChangeAlphabet (Constr_None _) _) [|Fin2|]) (Some tt)))
  .

  Lemma Nth_Step_Realise : Nth_Step ⊨ Nth_Step_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Nth_Step. TM_Correct.
      - eapply Reset_Realise with (cX := Encode_map cX retr_X_list).
      - apply Translate_Realise with (X := X).
    }
    {
      intros tin (yout, tout) H.
      intros l n HEncL HEncN HRight.
      destruct H; TMSimp.
      { (* First "Then" case *)
        modpon H.
        destruct n as [ | n']; auto; simpl_surject.
        (* We know that n = S n' *)

        destruct H0; TMSimp.
        { (* Second "Then" case *)
          modpon H0. destruct l as [ | x l']; auto; simpl_surject. modpon H0.
          modpon H1.
          (* We know that l = x :: l' *)
          modpon H2. repeat split; auto.
        }
        { (* Second "Else" case *)
          modpon H0. destruct l as [ | x l']; auto; modpon H0; auto; simpl_surject.
          (* We know that l = nil *)
          modpon H1.
          modpon H2. repeat split; eauto.
        }
      }
      { (* The first "Else" case *)
        modpon H.
        destruct n as [ | n']; auto.
        (* We know that n = 0 *)

        destruct H0; TMSimp.
        { (* Second "Then" case *)
          modpon H0.
          destruct l as [ | x l']; auto. destruct H0 as (H0&H0'); simpl_surject.
          (* We know that l = x :: l' *)
          modpon H1.
          simpl_tape in H2. modpon H2. repeat split; auto.
        }
        { (* Second "Else" case *)
          modpon H0.
          destruct l as [ | x l']; auto; destruct H0 as (H0 & H0'); simpl_surject.
          (* We know that l = nil *)
          modpon H1. repeat split; eauto.
        }
      }
    }
  Qed.


  Definition Nth_Loop_Rel : Rel (tapes sig^+ 3) (unit * tapes sig^+ 3) :=
    ignoreParam
      (fun tin tout =>
         forall l (n : nat),
           tin[@Fin0] ≃ l ->
           tin[@Fin1] ≃ n ->
           isRight tin[@Fin2] ->
           tout[@Fin0] ≃ skipn (S n) l /\
           tout[@Fin1] ≃ n - (S (length l)) /\
           tout[@Fin2] ≃ nth_error l n).


  Definition Nth_Loop := While Nth_Step.


  Lemma Nth_Loop_Realise : Nth_Loop ⊨ Nth_Loop_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Nth_Loop. TM_Correct. eapply Nth_Step_Realise. }
    {
      apply WhileInduction; intros; intros l n HEncL HEncN HRight.
      - TMSimp. modpon HLastStep.
        destruct n as [ | n'], l as [ | x l']; auto; destruct HLastStep as (H1&H2&H3); cbn; repeat split; eauto.
        now rewrite Nat.sub_0_r.
      - TMSimp. modpon HStar.
        destruct n as [ | n'], l as [ | x l']; auto; destruct HStar as (H1&H2&H3); cbn in *.
        modpon HLastStep. auto.
    }
  Qed.


  Definition Nth : { M : mTM sig^+ 5 & states M -> unit } :=
    LiftTapes (CopyValue _) [|Fin0; Fin3|];; (* Save l (on t0) to t3 and n (on t1) to t4 *)
    LiftTapes (CopyValue _) [|Fin1; Fin4|];;
    LiftTapes (Nth_Loop) [|Fin3; Fin4; Fin2|];; (* Execute the loop with the copy of n and l *)
    LiftTapes (Reset _) [|Fin3|];; (* Reset the copies *)
    LiftTapes (Reset _) [|Fin4|]
  .


  Lemma Nth_Computes : Nth ⊨ Computes2_Rel (@nth_error _).
  Proof.
    eapply Realise_monotone.
    { unfold Nth. TM_Correct.
      - apply CopyValue_Realise with (X := list X).
      - apply CopyValue_Realise with (X := nat).
      - apply Nth_Loop_Realise.
      - apply Reset_Realise with (X := list X).
      - apply Reset_Realise with (X := nat).
    }
    {
      intros tin ((), tout) H. cbn. intros l n HEncL HEncN HOut HInt.
      specialize (HInt Fin0) as HInt1. specialize (HInt Fin1) as HInt2. clear HInt.
      TMSimp.
      modpon H. modpon H0. modpon H1. modpon H2. modpon H3.
      repeat split; eauto.
      - intros i. destruct_fin i; TMSimp_goal; auto.
    }
  Qed.


End Nth.

  
(** ** Other Implementation of [nth_error] *)

Section Nth'.

  (** In this implementation of [nth_error], instead of encoding an option to the output tape, we use the finite parameter to indicate whether the result is [Some] or [None]. The advantage is that the client doesn't have to add the option to its alphabet. *)

  Variable (sig sigX : finType) (X : Type) (cX : codable sigX X).
  (* Hypothesis (defX: inhabitedC sigX). *)

  Variable (retr1 : Retract (sigList sigX) sig) (retr2 : Retract sigNat sig).
  Local Instance retr_X_list' : Retract sigX sig := ComposeRetract (Retract_sigList_X _) retr1.

  Check _ : codable sig (list X).
  Check _ : codable sig nat.

  Definition Nth'_Step_Rel : Rel (tapes sig^+ 3) (option bool * tapes sig^+ 3) :=
    fun tin '(yout, tout) =>
      forall (l : list X) (n : nat),
        tin[@Fin0] ≃ l ->
        tin[@Fin1] ≃ n ->
        isRight tin[@Fin2] ->
        match yout, n, l with
        | None, S n', x :: l' => (* Recursion case *)
          tout[@Fin0] ≃ l' /\
          tout[@Fin1] ≃ n' /\
          isRight tout[@Fin2] (* continue *)
        | Some true, 0, x::l' => (* return value *)
          tout[@Fin0] ≃ l' /\
          tout[@Fin1] ≃ 0 /\
          tout[@Fin2] ≃ x
        | Some false, 0, nil => (* list to short *)
          tout[@Fin0] ≃ nil /\
          tout[@Fin1] ≃ 0 /\
          isRight tout[@Fin2]
        | Some false, S n', nil => (* list to short *)
          tout[@Fin0] ≃ nil /\
          tout[@Fin1] ≃ n' /\
          isRight tout[@Fin2]
        | _, _, _ => False
        end.


  Definition Nth'_Step : { M : mTM sig^+ 3 & states M -> option bool } :=
    If (LiftTapes (ChangeAlphabet MatchNat _) [|Fin1|])
       (If (LiftTapes (ChangeAlphabet (MatchList sigX) _) [|Fin0; Fin2|]) (* n = S n' *)
           (Return (LiftTapes (Reset _) [|Fin2|]) None) (* l = x :: l'; continue *)
           (Return Nop (Some false))) (* l = nil; return false *)
       (ChangePartition (LiftTapes (ChangeAlphabet (MatchList sigX) _) [|Fin0; Fin2|]) Some) (* n = 0 *)
  .

  Lemma Nth'_Step_Realise : Nth'_Step ⊨ Nth'_Step_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Nth'_Step. TM_Correct.
      - eapply Reset_Realise with (X := X).
    }
    {
      intros tin (yout, tout) H.
      intros l n HEncL HEncN HRight.
      destruct H; TMSimp.
      { (* First "Then"; n = S n' *) rename H into HMatchNat, H0 into HIf.
        modpon HMatchNat. destruct n as [ | n']; auto; simpl_surject.
        destruct HIf; TMSimp.
        { (* Second "Then"; l = x :: l' *) rename H into HMatchList, H0 into HReset.
          modpon HMatchList. destruct l as [ | x l']; auto. modpon HMatchList.
          modpon HReset. repeat split; auto.
        }
        { (* Second "Else"; l = nil *) rename H into HMatchList.
          modpon HMatchList. destruct l as [ | x l']; auto. modpon HMatchList. repeat split; auto.
        }
      }
      { (* The first "Else"; n = 0 *) rename H into HMatchNat, H0 into HMatchList.
        modpon HMatchNat. destruct n as [ | n']; auto; simpl_surject.
        modpon HMatchList. destruct ymid, l; auto; modpon HMatchList; repeat split; auto. contains_ext.
      }
    }
  Qed.

  Definition Nth'_Step_steps (l : list X) (n : nat) :=
    match n, l with
    | S n', x :: l' =>
      2 + MatchNat_steps + MatchList_steps_cons _ x + Reset_steps _ x
    | S n', nil =>
      2 + MatchNat_steps + MatchList_steps_nil
    | O, x :: l' =>
      1 + MatchNat_steps + MatchList_steps_cons _ x
    | O, nil =>
      1 + MatchNat_steps + MatchList_steps_nil
    end.

  Definition Nth'_Step_T : tRel sig^+ 3 :=
    fun tin k => exists (l : list X) (n : nat),
        tin[@Fin0] ≃ l /\ tin[@Fin1] ≃ n /\ isRight tin[@Fin2] /\
        Nth'_Step_steps l n <= k.


  Lemma Nth'_Step_Terminates : projT1 Nth'_Step ↓ Nth'_Step_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Nth'_Step. TM_Correct.
      - apply Reset_Terminates with (X := X).
    }
    {
      intros tin k. intros (l&n&HEncL&HEncN&HRight2&Hk). unfold Nth'_Step_steps in Hk.
      destruct n as [ | n'] eqn:E1, l as [ | x l'] eqn:E2; cbn.
      - (* [n = 0] and [l = nil] *)
        exists (MatchNat_steps), (MatchList_steps_nil). repeat split; auto; try omega.
        intros tmid b (HMatchNat&HMatchNatInj); TMSimp. modpon HMatchNat. destruct b; auto; simpl_surject.
        { eexists; repeat split; simpl_surject; eauto. }
      - (* [n = 0] and [l = x :: l'] *)
        exists MatchNat_steps, (MatchList_steps_cons _ x). repeat split; cbn; auto.
        intros tmid b (H&HInj1); TMSimp. modpon H. destruct b; cbn in *; auto; simpl_surject.
        { eexists; repeat split; simpl_surject; eauto. }
      - (* [n = S n'] and [l = nil] *) 
        exists (MatchNat_steps), (S (MatchList_steps_nil)). repeat split; try omega.
        intros tmid b (HMatchNat&HMatchNatInj); TMSimp. modpon HMatchNat. destruct b; auto. simpl_surject.
        exists (MatchList_steps_nil), 0. repeat split; try omega.
        { eexists; repeat split; simpl_surject; eauto. }
        intros tmid0 b (HMatchList&HMatchListInj); TMSimp. modpon HMatchList. destruct b; auto.
      - (* [n = S n'] and [l = x :: l'] *)
        exists MatchNat_steps, (S (MatchList_steps_cons _ x + Reset_steps _ x)). repeat split; cbn; auto.
        intros tmid b (H&HInj1); TMSimp. modpon H. destruct b; cbn in *; auto; simpl_surject.
        exists (MatchList_steps_cons _ x), (Reset_steps _ x). repeat split; cbn; try omega.
        { exists (x :: l'). repeat split; simpl_surject; auto. }
        intros tmid2 b (H2&HInj2); TMSimp. modpon H2. destruct b; cbn in *; auto; simpl_surject; modpon H2.
        exists x. repeat split; eauto. contains_ext. unfold Reset_steps. now rewrite Encode_map_hasSize.
    }
  Qed.


  Definition Nth'_Loop_Rel : Rel (tapes sig^+ 3) (bool * tapes sig^+ 3) :=
    fun tin '(yout, tout) =>
      forall (l:list X) (n : nat),
          tin[@Fin0] ≃ l ->
          tin[@Fin1] ≃ n ->
          isRight tin[@Fin2] ->
          match yout with
          | true =>
            exists (x : X),
            nth_error l n = Some x /\
            tout[@Fin0] ≃ skipn (S n) l /\
            tout[@Fin1] ≃ n - (S (length l)) /\
            tout[@Fin2] ≃ x
          | false =>
            nth_error l n = None /\
            tout[@Fin0] ≃ skipn (S n) l /\
            tout[@Fin1] ≃ n - (S (length l)) /\
            isRight tout[@Fin2]
          end.


  Definition Nth'_Loop := While Nth'_Step.


  Lemma Nth'_Loop_Realise : Nth'_Loop ⊨ Nth'_Loop_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Nth'_Loop. TM_Correct. eapply Nth'_Step_Realise. }
    {
      apply WhileInduction; intros; intros l n HEncL HEncN HRight; cbn in *.
      - modpon HLastStep. destruct yout.
        + destruct n; auto. destruct l as [ | x l']; auto. modpon HLastStep.
          cbn. exists x. tauto.
        + destruct n; auto.
          * destruct l as [ | x l']; auto.
          * destruct l as [ | x l']; auto. modpon HLastStep.
            cbn. now rewrite Nat.sub_0_r.
      - modpon HStar. destruct n as [ | n']; auto. destruct l as [ | x l']; auto. modpon HStar.
        modpon HLastStep. destruct yout.
        + destruct HLastStep as (y&HLastStep); modpon HLastStep. cbn. exists y. eauto.
        + modpon HLastStep. cbn. eauto.
    }
  Qed.


  Fixpoint Nth'_Loop_steps (l : list X) (n : nat) { struct l } :=
    match n, l with
    | S n', x :: l'  => S (Nth'_Step_steps l n) + Nth'_Loop_steps l' n' (* continue *)
    | S n', nil => Nth'_Step_steps l n (* return *)
    | O, x :: l' => Nth'_Step_steps l n (* return *)
    | O, nil => Nth'_Step_steps l n (* only [MatchNat] and [If] *)
    end.
  

  Definition Nth'_Loop_T : tRel sig^+ 3 :=
    fun tin k => exists (l : list X) (n : nat),
        tin[@Fin0] ≃ l /\
        tin[@Fin1] ≃ n /\
        isRight tin[@Fin2] /\
        Nth'_Loop_steps l n <= k.

  
  Lemma Nth'_Loop_Terminates : projT1 Nth'_Loop ↓ Nth'_Loop_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Nth'_Loop. TM_Correct.
      - apply Nth'_Step_Realise.
      - apply Nth'_Step_Terminates. }
    {
      apply WhileCoInduction. intros tin k (l&n&HEncL&HEncN&HRight&Hk).
      destruct l as [ | x l'] eqn:E1, n as [ | n'] eqn:E2; cbn in *; auto; TMSimp.
      - (* [n=0] and [l=0]; return *)
        exists (Nth'_Step_steps nil 0). split.
        { hnf; cbn. exists nil, 0. repeat split; auto. }
        intros b ymid H. modpon H. destruct b; auto.
      - (* [n=S n'] and [l=nil]; return *)
        exists (Nth'_Step_steps nil (S n')). split.
        { hnf; cbn. exists nil, (S n'). repeat split; auto. }
        intros b ymid H. modpon H. destruct b as [ [ | ] | ]; auto.
      - (* [n=0] and [l = x :: l']; return *)
        exists (Nth'_Step_steps (x::l') 0). split.
        { hnf. exists (x :: l'), 0. repeat split; auto. }
        intros b tmid H1; TMSimp. modpon H1. destruct b; auto; modpon H1.
      - (* [n=S n'] and [l = x :: l']; continue *)
        exists (Nth'_Step_steps (x::l') (S n')). repeat split.
        { hnf. exists (x :: l'), (S n'). auto. }
        intros b tmid H1. modpon H1. destruct b; auto; modpon H1. now destruct b.
        exists (Nth'_Loop_steps l' n'). repeat split; auto; try omega.
        hnf. exists l', n'. auto.
    }
  Qed.


  (** We don't want to save, but reset, [n]. *)
  Definition Nth' : { M : mTM sig^+ 4 & states M -> bool } :=
    LiftTapes (CopyValue _) [|Fin0; Fin3|];; (* Save l (on t0) to t3 *)
    If (LiftTapes (Nth'_Loop) [|Fin3; Fin1; Fin2|]) (* Execute the loop with the copy of l *)
       (Return (LiftTapes (Reset _) [|Fin3|];; (* Reset the copy of [l] *)
                LiftTapes (Reset _) [|Fin1|] (* Reset [n] *)
               ) true)
       (Return (LiftTapes (Reset _) [|Fin3|];; (* Reset the copy of [l] *)
                LiftTapes (Reset _) [|Fin1|] (* Reset [n] *)
               ) false)
  .

  Definition Nth'_Rel : pRel sig^+ bool 4 :=
    fun tin '(yout, tout) =>
      forall (l : list X) (n : nat),
        tin[@Fin0] ≃ l ->
        tin[@Fin1] ≃ n ->
        isRight tin[@Fin2] ->
        isRight tin[@Fin3] ->
        match yout with
        | true =>
          exists (x : X),
          nth_error l n = Some x /\
          tout[@Fin0] ≃ l /\
          isRight tout[@Fin1] /\
          tout[@Fin2] ≃ x /\
          isRight tout[@Fin3]
        | false =>
          nth_error l n = None /\
          tout[@Fin0] ≃ l /\
          isRight tout[@Fin1] /\
          isRight tout[@Fin2] /\
          isRight tout[@Fin3]
        end.

  Lemma Nth'_Realise : Nth' ⊨ Nth'_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Nth'. TM_Correct.
      - apply CopyValue_Realise with (X := list X).
      - apply Nth'_Loop_Realise.
      - apply Reset_Realise with (X := list X).
      - apply Reset_Realise with (X := nat).
      - apply Reset_Realise with (X := list X).
      - apply Reset_Realise with (X := nat).
    }
    {
      intros tin (yout, tout) H. cbn. intros l n HEncL HEncN HRight2 HRight3.
      TMSimp. rename H into HCopy, H0 into HIf.
      destruct HIf; TMSimp.
      { rename H into HLoop, H0 into HReset, H1 into HReset'.
        modpon HCopy. modpon HLoop. destruct HLoop as (HLoop1&HLoop2&HLoop3&HLoop4&HLoop5).
        modpon HReset. eexists; repeat split; eauto.
      }
      { rename H into HLoop, H0 into HReset, H1 into HReset'.
        modpon HCopy. modpon HLoop.
        modpon HReset. eexists; repeat split; eauto.
      }
    }
  Qed.


  Definition Nth'_steps (l : list X) (n : nat) :=
    3 + CopyValue_steps _ l + Nth'_Loop_steps l n + Reset_steps _ (skipn (S n) l) + Reset_steps _ (n - S (length l)).

  Definition Nth'_T : tRel sig^+ 4 :=
    fun tin k => exists (l : list X) (n : nat),
        tin[@Fin0] ≃ l /\
        tin[@Fin1] ≃ n /\
        isRight tin[@Fin2] /\ isRight tin[@Fin3] /\
        Nth'_steps l n <= k.

  Lemma Nth'_Terminates : projT1 Nth' ↓ Nth'_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Nth'. TM_Correct.
      - apply CopyValue_Realise with (X := list X).
      - apply CopyValue_Terminates with (X := list X).
      - apply Nth'_Loop_Realise.
      - apply Nth'_Loop_Terminates.
      - apply Reset_Realise with (X := list X).
      - apply Reset_Terminates with (X := list X).
      - apply Reset_Terminates with (X := nat).
      - apply Reset_Realise with (X := list X).
      - apply Reset_Terminates with (X := list X).
      - apply Reset_Terminates with (X := nat).
    }
    {
      intros tin k (l&n&HEncL&HEncN&HRigh2&HRight3&Hk). unfold Nth'_steps in *.
      exists (CopyValue_steps _ l), (1 + Nth'_Loop_steps l n + 1 + Reset_steps _ (skipn (S n) l) + Reset_steps _ (n - S (length l))).
      repeat split; cbn; try omega.
      exists l. repeat split; eauto. unfold CopyValue_steps. now rewrite Encode_map_hasSize.
      intros tmid () (HCopy&HInjCopy); TMSimp. modpon HCopy.
      exists (Nth'_Loop_steps l n), (1 + Reset_steps _ (skipn (S n) l) + Reset_steps _ (n - S (length l))).
      repeat split; cbn; try omega. 2: now rewrite !Nat.add_assoc.
      { hnf; cbn. eauto 6. }
      intros tmid2 b (HLoop&HInjLoop); TMSimp. modpon HLoop. destruct b.
      {
        destruct HLoop as (x&HLoop); modpon HLoop.
        exists (Reset_steps _ (skipn (S n) l)), (Reset_steps _ (n - S (length l))).
        repeat split; cbn; try omega. 2: reflexivity.
        do 1 eexists. repeat split; eauto. unfold Reset_steps. now rewrite Encode_map_hasSize.
        intros tmid3 () (HReset&HInjReset); TMSimp. modpon HReset.
        do 1 eexists. repeat split; eauto. unfold Reset_steps. now rewrite Encode_map_hasSize.
      }
      {
        modpon HLoop.
        exists (Reset_steps _ (skipn (S n) l)), (Reset_steps _ (n - S (length l))).
        repeat split; cbn; try omega. 2: reflexivity.
        do 1 eexists. repeat split; eauto. unfold Reset_steps. now rewrite Encode_map_hasSize.
        intros tmid3 () (HReset&HInjReset); TMSimp. modpon HReset.
        eexists; repeat split; eauto. now setoid_rewrite Reset_steps_comp.
      }
    }
  Qed.
  

End Nth'.



Require Import TM.Basic.Mono TM.Code.Copy.



Lemma pair_eq (A B : Type) (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) ->
  a1 = a2 /\ b1 = b2.
Proof. intros H. now inv H. Qed.


Section ListStuff.
  Variable X : Type.

  (* TODO: -> base *)
  Lemma app_or_nil (xs : list X) :
    xs = nil \/ exists ys y, xs = ys ++ [y].
  Proof.
    induction xs as [ | x xs IH]; cbn in *.
    - now left.
    - destruct IH as [ -> | (ys&y&->) ].
      + right. exists nil, x. cbn. reflexivity.
      + right. exists (x :: ys), y. cbn. reflexivity.
  Qed.

  (* TODO: -> base *)
  Lemma map_removelast (A B : Type) (f : A -> B) (l : list A) :
    map f (removelast l) = removelast (map f l).
  Proof.
    induction l as [ | a l IH]; cbn in *; auto.
    destruct l as [ | a' l]; cbn in *; auto.
    f_equal. auto.
  Qed.

  (* TODO: -> base *)
  Corollary removelast_app_singleton (xs : list X) (x : X) :
    removelast (xs ++ [x]) = xs.
  Proof. destruct xs. reflexivity. rewrite removelast_app. cbn. rewrite app_nil_r. reflexivity. congruence. Qed.
    

  (* TODO: -> base *)
  Corollary removelast_length (xs : list X) :
    length (removelast xs) = length xs - 1.
  Proof.
    destruct (app_or_nil xs) as [ -> | (x&xs'&->)].
    - cbn. reflexivity.
    - rewrite removelast_app_singleton. rewrite app_length. cbn. omega.
  Qed.

End ListStuff.

  
(** ** Append *)

(** I simply copy memory instead of using constructors/deconstructors. The former approach is maybe easier, but I want to use fewer internal tapes. *)
Section Append.

  Variable (sigX : finType) (X : Type) (cX : codable sigX X).
  Hypothesis (defX: inhabitedC sigX).

  Notation sigList := (FinType (EqType (sigList sigX))) (only parsing).

  Let stop : sigList^+ -> bool :=
    fun x => match x with
          | inl (START) => true (* halt at the start symbol *)
          | _ => false
          end.

  Definition App'_Rel : Rel (tapes sigList^+ 2) (unit * tapes sigList^+ 2) :=
    ignoreParam (fun tin tout =>
                   forall (xs ys : list X),
                     tin[@Fin0] ≃ xs ->
                     tin[@Fin1] ≃ ys ->
                     tout[@Fin0] ≃ xs /\
                     tout[@Fin1] ≃ xs ++ ys).


  Definition App' : { M : mTM sigList^+ 2 & states M -> unit } :=
    LiftTapes (MoveRight _;; Move L;; Move L) [|Fin0|];;
    CopySymbols_L stop.
  Lemma App'_Realise : App' ⊨ App'_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold App'. TM_Correct.
      - apply MoveRight_Realise with (X := list X).
    }
    {
      intros tin ((), tout) H. cbn. intros xs ys HEncXs HEncYs.
      destruct HEncXs as (ls1&HEncXs), HEncYs as (ls2&HEncYs). TMSimp; clear_trivial_eqs.
      rename H into HMoveRight; rename H0 into HCopy.
      specialize (HMoveRight xs ltac:(repeat econstructor)) as (ls3&HEncXs'). TMSimp.

      pose proof app_or_nil xs as [ -> | (xs'&x&->) ]; cbn in *; auto.
      - rewrite CopySymbols_L_Fun_equation in HCopy; cbn in *. inv HCopy; TMSimp. repeat econstructor.
      - cbv [Encode_list] in *; cbn in *.
        rewrite encode_list_app in HCopy. cbn in *.
        rewrite rev_app_distr in HCopy. rewrite <- tl_rev in HCopy. rewrite map_app, <- !app_assoc in HCopy.
        rewrite <- tl_map in HCopy. rewrite map_rev in HCopy. cbn in *. rewrite <- app_assoc in HCopy. cbn in *.
        rewrite !List.map_app, !List.map_map in HCopy. rewrite rev_app_distr in HCopy. cbn in *.
        rewrite map_rev, tl_rev in HCopy.

        rewrite app_comm_cons, app_assoc in HCopy. rewrite CopySymbols_L_correct_moveleft in HCopy; cbn in *; auto.
        + rewrite rev_app_distr, rev_involutive, <- app_assoc in HCopy. inv HCopy; TMSimp.
          * rewrite <- app_assoc. cbn. repeat econstructor.
            -- f_equal. cbn. rewrite encode_list_app. rewrite map_app, <- app_assoc.
               cbn.
               f_equal.
               ++ now rewrite rev_involutive, map_removelast.
               ++ f_equal. now rewrite map_app, List.map_map, <- app_assoc.
            -- f_equal. cbn. rewrite !encode_list_app. rewrite rev_involutive, <- app_assoc.
               cbn. rewrite <- app_assoc. cbn.
               rewrite removelast_app, !map_app, <- !app_assoc, map_removelast. 2: congruence. f_equal.
               setoid_rewrite app_assoc at 2. rewrite app_comm_cons. rewrite app_assoc. f_equal. f_equal.
               rewrite map_removelast. cbn -[removelast]. rewrite map_app. cbn -[removelast].
               rewrite app_comm_cons. rewrite removelast_app. 2: congruence. cbn. now rewrite List.map_map, app_nil_r.
        + cbn.
          intros ? [ (?&<-&?) % in_rev % in_map_iff | H % in_rev ] % in_app_iff. cbn. auto. cbn in *.
          rewrite rev_involutive, <- map_removelast in H.
          apply in_app_iff in H as [ (?&<-&?) % in_map_iff | [ <- | [] ] ]. all: auto.
    }
  Qed.

  Definition App'_steps (xs : list X) :=
    29 + 12 * size _ xs.

  Definition App'_T : tRel sigList^+ 2 :=
    fun tin k => exists (xs ys : list X), tin[@Fin0] ≃ xs /\ tin[@Fin1] ≃ ys /\ App'_steps xs <= k.

  Lemma App'_Terminates : projT1 App' ↓ App'_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold App'. TM_Correct. (* This is a bit strange, because [App'] is a sequence of two sequences. *)
      - apply MoveRight_Realise with (X := list X).
      - apply MoveRight_Realise with (X := list X).
      - apply MoveRight_Terminates with (X := list X).
    }
    {
      intros tin k (xs&ys&HEncXS&HEncYs&Hk). unfold App'_steps in *.
      exists (12+4*size _ xs), (16+8*size _ xs). repeat split; cbn; try omega.
      exists (8+4*size _ xs), 3. repeat split; cbn; try omega. eauto.
      intros tmid1 () H. modpon H.
      exists 1, 1. repeat split; try omega. eauto.
      intros tmid (). intros H; TMSimp; clear_trivial_eqs. modpon H.
      destruct H as (ls&HEncXs); TMSimp.
      cbv [Encode_list]; cbn in *.

      destruct (app_or_nil xs) as [-> | (xs'&x&->)]; cbn in *.
      { (* [xs = nil] *)
        rewrite CopySymbols_L_steps_equation. cbn. omega.
      }
      { (* [xs = xs' ++ [x]] *)
        rewrite encode_list_app. rewrite rev_app_distr. cbn. rewrite <- app_assoc, rev_app_distr, <- app_assoc. cbn.
        rewrite CopySymbols_L_steps_moveleft; cbn; auto.
        rewrite map_length, !app_length, rev_length. cbn. rewrite map_length, rev_length, !app_length, !map_length. cbn.
        rewrite removelast_length. omega.
      }
    }
  Qed.
    
    
  Definition App : { M : mTM sigList^+ 3 & states M -> unit } :=
    LiftTapes (CopyValue _) [|Fin1; Fin2|];;
    LiftTapes (App') [|Fin0; Fin2|].


  Lemma App_Computes : App ⊨ Computes2_Rel (@app X).
  Proof.
    eapply Realise_monotone.
    { unfold App. TM_Correct.
      - apply CopyValue_Realise with (X := list X).
      - apply App'_Realise.
    }
    {
      intros tin ((), tout) H. cbn. intros xs ys HEncXs HEncYs HOut _.
      TMSimp. rename H into HCopy; rename H0 into HComp.
      specialize HCopy with (1 := HEncYs) (2 := HOut) as (HCopy1&HCopy2).
      specialize HComp with (1 := HEncXs) (2 := HCopy2) as (HComp1&HComp2).
      repeat split; auto.
      - intros i; destruct_fin i.
    }
  Qed.


  Definition App_steps (xs ys : list X) :=
    55 + 12 * size _ xs + 12 * size _ ys.
    

  Definition App_T : tRel sigList^+ 3 :=
    fun tin k => exists (xs ys : list X), tin[@Fin0] ≃ xs /\ tin[@Fin1] ≃ ys /\ isRight tin[@Fin2] /\ App_steps xs ys <= k.
  
  Lemma App_Terminates : projT1 App ↓ App_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold App. TM_Correct.
      - apply CopyValue_Realise with (X := list X).
      - apply CopyValue_Terminates with (X := list X).
      - apply App'_Terminates.
    }
    {
      intros tin k (xs&ys&HEncXs&HEnYs&HRigh2&Hk).
      exists (25 + 12 * size _ ys), (App'_steps xs). repeat split; cbn; eauto.
      unfold App'_steps, App_steps in *. omega.
      intros tmid () (HApp'&HInjApp'); TMSimp. modpon HApp'.
      hnf. cbn. do 2 eexists. repeat split; eauto.
    }
  Qed.
        
End Append.



(** ** Length *)

Section Lenght.

  (** Instead of defining [Length] on the alphabet [sigList sigX + sigNat], we can define Length on any alphabet [sig] and assume a retracts from [sigList sigX] to [tau] and from [sigNat] to [tau]. This makes the invocation of the machine more flexible for a client. *)

  Variable sig sigX : finType.
  Variable (X : Type) (cX : codable sigX X).
  Variable (retr1 : Retract (sigList sigX) sig) (retr2 : Retract sigNat sig).


  Definition Length_Step : pTM sig^+ (option unit) 3 :=
    If (LiftTapes (ChangeAlphabet (MatchList _) _) [|Fin0; Fin2|])
       (Return (LiftTapes (Reset _) [|Fin2|];;
                LiftTapes (ChangeAlphabet (Constr_S) _) [|Fin1|])
               (None)) (* continue *)
       (Return Nop (Some tt)) (* break *)
  .

  Definition Length_Step_Rel : pRel sig^+ (option unit) 3 :=
    fun tin '(yout, tout) =>
      forall (xs : list X) (n : nat),
        tin[@Fin0] ≃ xs ->
        tin[@Fin1] ≃ n ->
        isRight tin[@Fin2] ->
        match yout, xs with
        | (Some tt), nil => (* break *)
          tout[@Fin0] ≃ nil /\
          tout[@Fin1] ≃ n /\
          isRight tout[@Fin2]
        | None, _ :: xs' => (* continue *)
          tout[@Fin0] ≃ xs' /\
          tout[@Fin1] ≃ S n /\
          isRight tout[@Fin2]
        | _, _ => False
        end.


  Lemma Length_Step_Realise : Length_Step ⊨ Length_Step_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Length_Step. TM_Correct.
      - apply Reset_Realise with (X := X).
    }
    {
      intros tin (yout, tout) H. cbn. intros xs n HEncXS HEncN HRight.
      destruct H; TMSimp.
      { (* Then *) rename H into HMatchList, H0 into HReset, H1 into HS.
        modpon HMatchList. destruct xs as [ | x xs']; cbn in *; auto; modpon HMatchList.
        modpon HReset. modpon HS. repeat split; auto.
      }
      { (* Then *) rename H into HMatchList.
        modpon HMatchList. destruct xs as [ | x xs']; cbn in *; auto; modpon HMatchList. repeat split; auto.
      }
    }
  Qed.


  Definition Length_Step_steps (xs : list X) :=
    match xs with
    | nil => 1 + MatchList_steps_nil
    | x :: xs' => 2 + MatchList_steps_cons _ x + Reset_steps _ x + Constr_S_steps
    end.

  Definition Length_Step_T : tRel sig^+ 3 :=
    fun tin k => exists (xs : list X) (n : nat), tin[@Fin0] ≃ xs /\ tin[@Fin1] ≃ n /\ isRight tin[@Fin2] /\ Length_Step_steps xs <= k.

  Lemma Length_Step_Terminates : projT1 Length_Step ↓ Length_Step_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Length_Step. TM_Correct.
      - apply Reset_Realise with (X := X).
      - apply Reset_Terminates with (X := X).
    }
    {
      intros tin k (xs&n&HEncXs&HEncN&HRight2&Hk). unfold Length_Step_steps in Hk.
      destruct xs as [ | x xs'].
      - exists MatchList_steps_nil, 0. repeat split; cbn in *; try omega.
        eexists; repeat split; simpl_surject; eauto; cbn; eauto.
        intros tmid b (HMatchList&HInjMatchList); TMSimp. modpon HMatchList. destruct b; cbn in *; auto.
      - exists (MatchList_steps_cons _ x), (1 + Reset_steps _ x + Constr_S_steps). repeat split; cbn in *; try omega.
        eexists; repeat split; simpl_surject; eauto; cbn; eauto.
        intros tmid b (HMatchList&HInjMatchList); TMSimp. modpon HMatchList. destruct b; cbn in *; auto; modpon HMatchList.
        exists (Reset_steps _ x), Constr_S_steps. repeat split; cbn; try omega.
        eexists; repeat split; simpl_surject; eauto; cbn; eauto. unfold Reset_steps. now rewrite !Encode_map_hasSize.
        now intros _ _ _.
    }
  Qed.
  

  Definition Length_Loop := While Length_Step.

  Definition Length_Loop_Rel : pRel sig^+ unit 3 :=
    ignoreParam (
        fun tin tout =>
          forall (xs : list X) (n : nat),
            tin[@Fin0] ≃ xs ->
            tin[@Fin1] ≃ n ->
            isRight tin[@Fin2] ->
            tout[@Fin0] ≃ nil /\
            tout[@Fin1] ≃ n + length xs /\
            isRight tout[@Fin2]
      ).


  Lemma Length_Loop_Realise : Length_Loop ⊨ Length_Loop_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Length_Loop. TM_Correct.
      - apply Length_Step_Realise.
    }
    {
      apply WhileInduction; intros; intros xs n HEncXS HEncN HRight; TMSimp.
      {
        modpon HLastStep.
        destruct xs as [ | x xs']; auto; TMSimp.
        cbn. rewrite Nat.add_0_r. repeat split; auto.
      }
      {
        modpon HStar.
        destruct xs as [ | x xs']; auto; TMSimp.
        modpon HLastStep.
        rewrite Nat.add_succ_r.
        repeat split; auto.
      }
    }
  Qed.


  Fixpoint Length_Loop_steps (xs : list X) : nat :=
    match xs with
    | nil => Length_Step_steps xs
    | x :: xs' => S (Length_Step_steps xs) + Length_Loop_steps xs'
    end.

  Definition Length_Loop_T : tRel sig^+ 3 :=
    fun tin k => exists (xs : list X) (n : nat), tin[@Fin0] ≃ xs /\ tin[@Fin1] ≃ n /\ isRight tin[@Fin2] /\ Length_Loop_steps xs <= k.

  Lemma Length_Loop_Terminates : projT1 Length_Loop ↓ Length_Loop_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Length_Loop. TM_Correct.
      - apply Length_Step_Realise.
      - apply Length_Step_Terminates. }
    {
      apply WhileCoInduction. intros tin k (xs&n&HEncXs&HEncN&HRight2&Hk). exists (Length_Step_steps xs). repeat split.
      - hnf. do 2 eexists. repeat split; eauto.
      - intros b tmid HStep. hnf in HStep. modpon HStep. destruct b as [ () | ], xs as [ | x xs']; cbn in *; auto; modpon HStep.
        eexists (Length_Loop_steps xs'). repeat split; try omega. hnf. exists xs', (S n). repeat split; eauto.
    }
  Qed.
  

  Definition Length : pTM sig^+ unit 4 :=
    LiftTapes (CopyValue _) [|Fin0; Fin3|];;
    LiftTapes (ChangeAlphabet Constr_O _) [|Fin1|];;
    LiftTapes (Length_Loop) [|Fin3; Fin1; Fin2|];;
    LiftTapes (ResetEmpty1 _) [|Fin3|].


  Lemma Length_Computes : Length ⊨ Computes_Rel (@length X).
  Proof.
    eapply Realise_monotone.
    { unfold Length. TM_Correct.
      - apply CopyValue_Realise with (X := list X).
      - apply Length_Loop_Realise.
      - eapply RealiseIn_Realise. apply ResetEmpty1_Sem with (X := list X).
    }
    {
      intros tin ((), tout) H. intros xs HEncXs Hout HInt2. specialize (HInt2 Fin1) as HInt3; specialize (HInt2 Fin0).
      TMSimp. modpon H. modpon H0. modpon H1. modpon H2. modpon H3.
      repeat split; auto. intros i; destruct_fin i; auto. now TMSimp.
    }
  Qed.


  Definition Length_steps (xs : list X) := 36 + 12 * size _ xs + Length_Loop_steps xs.

  Definition Length_T : tRel sig^+ 4 :=
    fun tin k => exists (xs : list X), tin[@Fin0] ≃ xs /\ isRight tin[@Fin1] /\ isRight tin[@Fin2] /\ isRight tin[@Fin3] /\ Length_steps xs <= k.
  
  Lemma Length_Terminates : projT1 Length ↓ Length_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Length. TM_Correct.
      - apply CopyValue_Realise with (X := list X).
      - apply CopyValue_Terminates with (X := list X).
      - apply Length_Loop_Realise.
      - apply Length_Loop_Terminates.
      - eapply RealiseIn_TerminatesIn. apply ResetEmpty1_Sem.
    }
    {
      intros tin k (xs&HEncXs&HRight1&HRight2&HRigth3&Hk). unfold Length_steps in *.
      exists (25 + 12 * size _ xs), (10 + Length_Loop_steps xs). repeat split; cbn; try omega.
      eexists. repeat split; eauto. unfold CopyValue_steps. now rewrite Encode_map_hasSize.
      intros tmid () (HO&HOInj); TMSimp. modpon HO.
      exists 5, (4 + Length_Loop_steps xs). unfold Constr_O_steps. repeat split; cbn; try omega.
      intros tmid0 () (HLoop&HLoopInj); TMSimp. modpon HLoop.
      exists (Length_Loop_steps xs), 3. repeat split; cbn; try omega.
      hnf. cbn. do 2 eexists. repeat split; eauto.
      now intros _ _ _.
    }
  Qed.

End Lenght.