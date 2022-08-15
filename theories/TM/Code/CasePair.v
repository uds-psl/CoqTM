(** * Constructors and Deconstructors for Pair Types *)

Require Import ProgrammingTools.

(* TODO: ~> base *)
Lemma pair_eq (A B : Type) (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) ->
  a1 = a2 /\ b1 = b2.
Proof. intros H. now inv H. Qed.

Local Arguments skipn { A } !n !l.

Section CasePair.

  (** ** Deconstructor *)

  Variable (sigX sigY: finType) (X Y: Type) (cX: codable sigX X) (cY: codable sigY Y).

  Local Notation sigPair := (sigPair sigX sigY).

  Definition stopAfterFirst : sigPair^+ -> bool :=
    fun x => match x with
          | inr (sigPair_Y y) => true
          | inl STOP => true
          | _ => false
          end.

  
  Definition stopAtStart : sigPair^+ -> bool :=
    fun x => match x with
          | inl START => true
          | _ => false
          end.


  Definition CasePair_Rel : pRel sigPair^+ unit 2 :=
    ignoreParam (
        fun tin tout =>
          forall p : X * Y,
            tin[@Fin0] ≃ p ->
            isRight tin[@Fin1] ->
            tout[@Fin0] ≃ snd p /\
            tout[@Fin1] ≃ fst p
      ).

  Definition CasePair : pTM sigPair^+ unit 2 :=
    LiftTapes (WriteMove (inl STOP) L) [|Fin1|];;
    LiftTapes (MoveToSymbol stopAfterFirst id;; Move L) [|Fin0|];;
    CopySymbols_L stopAtStart;;
    LiftTapes (MoveToSymbol stopAfterFirst id;; Move L;; Write (inl START)) [|Fin0|].

  Lemma CasePair_Realise : CasePair ⊨ CasePair_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold CasePair. TM_Correct. }
    {
      intros tin ((), tout) H.
      intros (x,y) HEncXY HRight.
      destruct HEncXY as (ls&HEncXY).
      TMSimp; clear_trivial_eqs. rename H1 into HCopy.
      rewrite map_app, <- app_assoc in HCopy.
      (* We need a case distinction, whether the encoding of [y] is empty, because [MoveToSymbol] either stops in a symbol of [cY y] or on [inl STOP]. However, both parts of the proof have identical proof scripts. *)
      destruct (cY y) eqn:EY; cbn in *.
      - rewrite MoveToSymbol_correct_midtape in HCopy; cbn in *; auto.
        erewrite CopySymbols_L_correct_moveleft in HCopy; cbn; auto.
        + apply pair_eq in HCopy as (HCopy1, HCopy2). TMSimp.
          * repeat econstructor. f_equal.
            rewrite MoveToSymbol_correct_midtape; cbn; auto.
            -- simpl_tape. now rewrite EY.
            -- rewrite map_id, rev_involutive, List.map_map. now intros ? (?&<-&?) % in_map_iff.
            -- cbn. rewrite !map_id, rev_involutive, !List.map_map.
               f_equal. f_equal. setoid_rewrite isRight_right at 2; auto. now simpl_tape.
        + rewrite List.map_map. now intros ? (?&<-&?) % in_rev % in_map_iff.
        + rewrite List.map_map. now intros ? (?&<-&?) % in_map_iff.
      - rewrite MoveToSymbol_correct_midtape in HCopy; cbn in *; auto.
        erewrite CopySymbols_L_correct_moveleft in HCopy; cbn; auto.
        + apply pair_eq in HCopy as (HCopy1, HCopy2). TMSimp.
          * repeat econstructor. f_equal.
            rewrite MoveToSymbol_correct_midtape; cbn; auto.
            -- simpl_tape. now rewrite EY.
            -- rewrite map_id, rev_involutive, List.map_map. now intros ? (?&<-&?) % in_map_iff.
            -- cbn. rewrite !map_id, rev_involutive, !List.map_map.
               f_equal. f_equal. setoid_rewrite isRight_right at 2; auto. now simpl_tape.
        + rewrite List.map_map. now intros ? (?&<-&?) % in_rev % in_map_iff.
        + rewrite List.map_map. now intros ? (?&<-&?) % in_map_iff.
    }
  Qed.

  Local Arguments plus : simpl never. Local Arguments mult : simpl never.
  Local Arguments size : simpl never.

  Definition CasePair_steps (x : X) :=
    34 + 16 * size _ x.

  Definition CasePair_T : tRel sigPair^+ 2 :=
    fun tin k => exists (p : X * Y), tin[@Fin0] ≃ p /\ CasePair_steps (fst p) <= k.
      
  Lemma CasePair_Terminates : projT1 CasePair ↓ CasePair_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold CasePair. TM_Correct. }
    {
      intros tin k ((x&y)&HEncP&Hk). unfold CasePair_steps in *. cbn in *.
      exists 1, (32 + 16 * size _ x). repeat split; try lia.
      intros tmid () ?; TMSimp.
      exists (10 + 4 * size _ x), (21 + 12 * size _ x). repeat split; try lia.
      {
        exists (8 + 4 * size _ x), 1. repeat split; try lia.
        destruct HEncP as (ls&->). cbn. destruct (cY y) eqn:EY.
        - rewrite app_nil_r. rewrite MoveToSymbol_steps_midtape; cbn; auto. now rewrite !map_length.
        - rewrite map_app, <- app_assoc. cbn.
          rewrite MoveToSymbol_steps_midtape; cbn; auto. now rewrite !map_length.
      }
      intros tmid1 (). intros ?; TMSimp.
      exists (8 + 8 * size _ x), (12 + 4 * size _ x). repeat split; try lia.
      {
        destruct HEncP as (ls&->). cbn. destruct (cY y) eqn:EY.
        - rewrite app_nil_r. rewrite MoveToSymbol_correct_midtape; cbn; auto.
          + rewrite CopySymbols_L_steps_moveleft; cbn; auto. now rewrite rev_length, !map_length.
          + rewrite List.map_map. now intros ? (?&<-&?) % in_map_iff.
        - rewrite map_app, <- app_assoc. cbn.
          rewrite MoveToSymbol_correct_midtape; cbn; auto.
          + rewrite CopySymbols_L_steps_moveleft; cbn; auto. now rewrite rev_length, !map_length.
          + rewrite List.map_map. now intros ? (?&<-&?) % in_map_iff.
      }
      intros tmid2 () HCopy.
      exists (8 + 4 * size _ x), 3. repeat split; try lia.
      {
        destruct HEncP as (ls&HEncP); TMSimp. cbn in *. destruct (cY y) eqn:EY.
        - rewrite app_nil_r in HCopy. rewrite MoveToSymbol_correct_midtape in HCopy; cbn in *; auto.
          + rewrite CopySymbols_L_correct_moveleft in HCopy; cbn; auto.
            * inv HCopy; TMSimp. rewrite MoveToSymbol_steps_midtape; cbn; auto. now rewrite !rev_length, !map_length.
            * rewrite List.map_map. now intros ? (?&<-&?) % in_rev % in_map_iff.
          + rewrite List.map_map. now intros ? (?&<-&?) % in_map_iff.
        - rewrite map_app, <- app_assoc in HCopy. cbn in *. rewrite MoveToSymbol_correct_midtape in HCopy; cbn in *; auto.
          + rewrite CopySymbols_L_correct_moveleft in HCopy; cbn; auto. 
            * inv HCopy; TMSimp. rewrite MoveToSymbol_steps_midtape; cbn; auto. now rewrite !rev_length, !map_length.
            * rewrite List.map_map. now intros ? (?&<-&?) % in_rev % in_map_iff.
          + rewrite List.map_map. now intros ? (?&<-&?) % in_map_iff.
      }
      intros tmid3 _ _. exists 1, 1. split. lia. split. lia. intros _ _ _. lia.
    }
  Qed.

  (** ** Constructor *)
  
  Definition Constr_pair_Rel : pRel sigPair^+ unit 2 :=
    ignoreParam (
        fun tin tout =>
          forall (x : X) (y : Y),
            tin[@Fin0] ≃ x ->
            tin[@Fin1] ≃ y ->
            tout[@Fin0] ≃ x /\
            tout[@Fin1] ≃ (x, y)
      ).


  Definition Constr_pair : pTM sigPair^+ unit 2 :=
    LiftTapes (MoveRight _;; Move L) [|Fin0|];;
    CopySymbols_L stopAtStart.


  Lemma Constr_pair_Realise : Constr_pair ⊨ Constr_pair_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Constr_pair. TM_Correct.
      - apply MoveRight_Realise with (X := X).
    }
    {
      intros tin ((), tout) H. intros x y HEncX HEncY.
      TMSimp; clear_trivial_eqs. rename H into HMoveRight; rename H0 into HCopy.
      modpon HMoveRight. destruct HMoveRight as (ls&HMoveRight); TMSimp.
      rewrite CopySymbols_L_correct_moveleft in HCopy; cbn in *; auto.
      - apply pair_eq in HCopy as (HCopy1&HCopy2). TMSimp. split.
        + repeat econstructor. cbn. f_equal. now rewrite map_rev, rev_involutive.
        + repeat econstructor. cbn. f_equal. simpl_tape.
          destruct HEncY as (ls'&HEncY); TMSimp_goal.
          rewrite map_rev, rev_involutive. cbn. now rewrite map_app, <- app_assoc. 
      - rewrite map_rev, List.map_map. now intros ? (?&<-&?) % in_rev % in_map_iff.
    }
  Qed.


  Definition Constr_pair_steps (x : X) : nat := 19 + 12 * size _ x.

  Definition Constr_pair_T : tRel sigPair^+ 2 :=
    fun tin k => exists (x : X), tin[@Fin0] ≃ x /\ Constr_pair_steps x <= k.
      
  Lemma Constr_pair_Terminates : projT1 Constr_pair ↓ Constr_pair_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Constr_pair. TM_Correct.
      - apply MoveRight_Realise with (X := X).
      - apply MoveRight_Realise with (X := X).
      - apply MoveRight_Terminates with (X := X).
    }
    {
      intros tin k (x & HEncX & Hk). unfold Constr_pair_steps in *. cbn in *.
      exists (10 + 4 * size _ x), (8 + 8 * size _ x). repeat split; try lia.
      {
        exists (8 + 4 * size _ x), 1. repeat split; try lia.
        eexists. repeat split; eauto. unfold MoveRight_steps. now rewrite Encode_map_hasSize.
      }
      intros tmid () ?; TMSimp. modpon H. destruct H as (ls&->). cbn.
      rewrite CopySymbols_L_steps_moveleft; cbn; auto. now rewrite map_length, rev_length, map_length.
    }
  Qed.


  (** [Snd] simply discard the first element *)

  Definition Snd_Rel : pRel sigPair^+ unit 1 :=
    ignoreParam (fun tin tout => forall p : X*Y, tin[@Fin0] ≃ p -> tout[@Fin0] ≃ snd p).

  Definition Snd : pTM sigPair^+ unit 1 :=
    MoveToSymbol stopAfterFirst id;;
    Move L;;
    Write (inl START).


  Lemma Snd_Realise : Snd ⊨ Snd_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Snd. TM_Correct. }
    {
      intros tin ((), tout) H. intros (x,y) HEncXY.
      destruct HEncXY as (ls&HEncXY).
      TMSimp; clear_trivial_eqs.
      destruct (cY y) eqn:EY.
      - rewrite app_nil_r.
        rewrite MoveToSymbol_correct_midtape; cbn; auto.
        + cbn. simpl_tape. repeat econstructor. cbn. rewrite EY. cbn. f_equal.
        + rewrite List.map_map. now intros ? (?&<-&?) % in_map_iff.
      - cbn. rewrite map_app, <- app_assoc; cbn.
        rewrite MoveToSymbol_correct_midtape; cbn; auto.
        + simpl_tape. repeat econstructor. f_equal. cbn. now rewrite EY.
        + rewrite List.map_map. now intros ? (?&<-&?) % in_map_iff.
    }
  Qed.


  Definition Snd_steps (x : X) := 12 + 4 * size _ x.

  Definition Snd_T : tRel sigPair^+ 1 :=
    fun tin k => exists p : X*Y, tin[@Fin0] ≃ p /\ Snd_steps (fst p) <= k.

  Lemma Snd_Terminates : projT1 Snd ↓ Snd_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Snd. TM_Correct. }
    {
      intros tin k ((x,y)&HEncP&Hk). unfold Snd_steps in *; cbn in *.
      exists (8+4*size _ x), 3. repeat split; try lia.
      {
        destruct HEncP as (ls&->). destruct (cY y) eqn:EY; cbn in *.
        - rewrite MoveToSymbol_steps_midtape; cbn; auto. rewrite EY. cbn.
          rewrite map_length, app_length, map_length. cbn. unfold size. lia.
        - rewrite map_app, <- app_assoc, EY. cbn.
          rewrite MoveToSymbol_steps_midtape; cbn; auto. now rewrite !map_length.
      }
      intros ? _ _. exists 1, 1. split. reflexivity. split. reflexivity. intros _ _ _. reflexivity.
    }
  Qed.


End CasePair.

(** ** Compatibility of running time functions with mapping of encodings *)

Section Steps_comp.
  Variable (sig tau: finType) (X Y:Type) (cX: codable sig X).
  Variable (I : Retract sig tau).

  Lemma CasePair_steps_comp l :
    CasePair_steps (Encode_map cX I) l = CasePair_steps cX l.
  Proof. unfold CasePair_steps. now rewrite Encode_map_hasSize. Qed.

  Lemma Constr_pair_steps_comp l :
    Constr_pair_steps (Encode_map cX I) l = Constr_pair_steps cX l.
  Proof. unfold Constr_pair_steps. now rewrite Encode_map_hasSize. Qed.

  Lemma Snd_steps_comp l :
    Snd_steps (Encode_map cX I) l = Snd_steps cX l.
  Proof. unfold Snd_steps. now rewrite Encode_map_hasSize. Qed.

End Steps_comp.


(** ** Tactic Support *)

Ltac smpl_TM_CasePair :=
  lazymatch goal with
  | [ |- CasePair _ _ ⊨ _ ] => apply CasePair_Realise
  | [ |- projT1 (CasePair _ _) ↓ _ ] => apply CasePair_Terminates

  | [ |- Constr_pair _ _ ⊨ _ ] => apply Constr_pair_Realise
  | [ |- projT1 (Constr_pair _ _) ↓ _] => apply Constr_pair_Terminates

  | [ |- Snd _ _ ⊨ _ ] => apply Snd_Realise
  | [ |- projT1 (Snd _ _) ↓ _] => apply Snd_Terminates
  end.

Smpl Add smpl_TM_CasePair : TM_Correct.
