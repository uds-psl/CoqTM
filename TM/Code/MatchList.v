(* List destruct and construction *)

Require Import TM.Code.CodeTM.
Require Import TM.Basic.Mono TM.Basic.Nop TM.Basic.Multi.
Require Import TM.Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.
Require Import TM.Compound.CopySymbols TM.Compound.MoveToSymbol.
Require Import TM.Code.Copy.


Section MatchList.

  (** ** Definition *)


  Variable X : Type.
  Variable (sigX : finType).
  Hypothesis (cX : codable sigX X).

  Definition stop (s: (sigList sigX)^+) :=
    match s with
    | inr (sigList_cons) => true
    | inr (sigList_nil) => true
    | inl _ => true
    | _ => false
    end.
  

  Definition Skip_cons : { M : mTM (sigList sigX)^+ 1 & states M -> unit } :=
    Move R tt;;
    Return (MoveToSymbol stop id) tt.


  Definition M1 : { M : mTM (sigList sigX)^+ 2 & states M -> unit } :=
    Inject Skip_cons [|Fin0|];;
    Inject (Write (inl STOP) tt) [|Fin1|];;
    MovePar L L tt;;
    CopySymbols_L stop id;;
    Inject (Write (inl START) tt) [|Fin1|].

  Definition MatchList : { M : mTM (sigList sigX)^+ 2 & states M -> bool } :=
    Inject (Move R tt) [|Fin0|];;
    MATCH (Inject (Read_char) [|Fin0|])
          (fun s => match s with
                 | Some (inr sigList_nil) => (* nil *)
                   Inject (Move L false) [|Fin0|]
                 | Some (inr sigList_cons) => (* cons *)
                   M1;; 
                   Inject Skip_cons [|Fin0|];;
                   Inject (Move L tt;; Write (inl START) true) [|Fin0|]
                 | _ => Nop true (* invalid input *)
                 end).


  (** ** Corectness *)

  Definition Skip_cons_Rel : Rel (tapes (sigList sigX)^+ 1) (unit * tapes (sigList sigX)^+ 1) :=
    Mk_R_p (
        ignoreParam (
            fun tin tout =>
              forall ls rs (x : X) (l : list X),
                tin = midtape (inl START :: ls) (inr sigList_cons)
                              (map inr (encode x) ++ map inr (encode l) ++ inl STOP :: rs) ->
                match l with
                | nil =>
                  tout = midtape (rev (map inr (encode x)) ++ inr sigList_cons :: inl START :: ls)
                                 (inr sigList_nil) (inl STOP :: rs)
                | x'::l' =>
                  tout = midtape (rev (map inr (encode x)) ++ inr sigList_cons :: inl START :: ls)
                                 (inr sigList_cons) (map inr (encode x') ++ map inr (encode l') ++ inl STOP :: rs)
                end)).

  
  Lemma stop_lemma x :
    forall s : (sigList sigX)^+, s el map inr (map sigList_X (encode x)) -> stop s = false.
  Proof.
    rewrite List.map_map. intros ? (?&<-&?) % in_map_iff. cbn. reflexivity.
  Qed.


  Lemma Skip_cons_Realise : Skip_cons ⊨ Skip_cons_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Skip_cons. repeat TM_Correct. }
    {
      intros tin ((), tout) H. intros ls rs x l HTin. TMSimp. clear_trivial_eqs. clear HTin H1 H2.
      destruct l as [ | x' l']; cbn.
      - rewrite MoveToSymbol_correct_moveright; cbn; auto.
        + now rewrite map_id.
        + apply stop_lemma.
      - rewrite MoveToSymbol_correct_moveright; cbn; auto.
        + rewrite map_id, map_app, <- app_assoc. reflexivity.
        + apply stop_lemma.
    }
  Qed.
  

  Definition M1_Rel : Rel (tapes (sigList sigX)^+ 2) (unit * tapes (sigList sigX)^+ 2) :=
    ignoreParam (
        fun tin tout =>
          forall ls rs (x : X) (l : list X),
            isRight tin[@Fin1] ->
            tin[@Fin0] = midtape (inl START :: ls) (inr sigList_cons)
                                 (map inr (encode x) ++ map inr (encode l) ++ inl STOP :: rs) ->
            tout[@Fin0] = tin[@Fin0] /\
            tout[@Fin1] ≃ x).
            

  Lemma M1_Realise : M1 ⊨ M1_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold M1. repeat TM_Correct. eapply Skip_cons_Realise. }
    {
      intros tin ((), tout) H. intros ls rs x l HRight HTin0. TMSimp; clear_trivial_eqs.
      rename H3 into HCopy.
      destruct HRight as (r1&r2&HRight). TMSimp. clear HRight.

      specialize H with (1 := eq_refl).
      destruct l as [ | x' l']; TMSimp.
      - rewrite CopySymbols_L_correct_moveleft in HCopy; cbn; auto.
        2: setoid_rewrite <- in_rev; apply stop_lemma.
        inv HCopy. TMSimp.
        cbn. rewrite !map_id, !rev_involutive. repeat econstructor. cbn. f_equal. simpl_tape. reflexivity.
      - rewrite CopySymbols_L_correct_moveleft in HCopy; cbn; auto.
        2: setoid_rewrite <- in_rev; apply stop_lemma.
        inv HCopy. TMSimp.
        cbn. rewrite !map_id, !rev_involutive. repeat econstructor.
        + f_equal. rewrite map_app, <- app_assoc. reflexivity.
        + cbn. f_equal. simpl_tape. reflexivity.
    }
  Qed.


  Definition MatchList_Rel : Rel (tapes (sigList sigX)^+ 2) (bool * tapes (sigList sigX)^+ 2) :=
    fun tin '(yout, tout) =>
      forall (l : list X),
        tin[@Fin0] ≃ l ->
        isRight tin[@Fin1] ->
        match yout, l with
        | false, nil =>
          tout[@Fin0] ≃ nil /\
          isRight tout[@Fin1]
        | true, x :: l' =>
          tout[@Fin0] ≃ l' /\
          tout[@Fin1] ≃ x
        | _, _ => False
        end.


  Lemma MatchList_Realise : MatchList ⊨ MatchList_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold MatchList. repeat TM_Correct. eapply M1_Realise. eapply Skip_cons_Realise. }
    {
      intros tin (yout, tout) H. intros l HEncL HRight.
      destruct HEncL as (ls&HEncL). destruct HRight as (ls'&rs'&HRight). TMSimp; clear_trivial_eqs.
      destruct l as [ | x l'] in *; cbn in *; TMSimp; clear_trivial_eqs.
      { (* nil *)
        split; auto.
        - repeat econstructor; cbn; simpl_tape.
        - repeat econstructor.
      }
      { (* cons *)
        rewrite map_app, <- app_assoc in H0. symmetry in H0.
        TMSimp.
        rewrite map_app, <- app_assoc in H.
        specialize H with (1 := ltac:(now repeat econstructor) : isRight _) (2 := eq_refl).
        TMSimp. symmetry in H0. specialize H2 with (1 := H0).
        destruct l' as [ | x' l'']; TMSimp.
        - repeat split; auto. repeat econstructor. f_equal. simpl_tape. cbn. reflexivity.
        - repeat split; auto. repeat econstructor. f_equal. simpl_tape. cbn. now rewrite map_app, <- app_assoc.
      }
    }
  Qed.


  (** ** Termination *)


  Local Arguments plus : simpl never. Local Arguments mult : simpl never.


  Lemma Skip_cons_Terminates :
    projT1 (Skip_cons) ↓
           (fun tin k =>
              exists ls rs (x : X) (l : list X),
                tin[@Fin0] = midtape (inl START :: ls) (inr sigList_cons)
                                     (map inr (encode x) ++ map inr (encode l) ++ inl STOP :: rs) /\
                 6 + 4 * size cX x <= k).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Skip_cons. repeat TM_Correct. }
    {
      intros tin k (ls&rs&x&l&HTin&Hk). TMSimp. clear HTin.
      exists 1, (4 + 4 * size cX x). repeat split. 1-2: omega.
      intros tmid () (_&H). TMSimp. clear H.
      destruct l as [ | x' l]; cbn.
      - rewrite MoveToSymbol_TermTime_moveright; cbn; auto. now rewrite !map_length.
      - rewrite MoveToSymbol_TermTime_moveright; cbn; auto. now rewrite !map_length.
    }
  Qed.


  Lemma M1_Terminates :
    projT1 M1 ↓
           (fun tin k =>
              exists ls rs (x : X) (l : list X),
                tin[@Fin0] = midtape (inl START :: ls) (inr sigList_cons)
                                     (map inr (encode x) ++ map inr (encode l) ++ inl STOP :: rs) /\
                 23 + 12 * size cX x <= k).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold M1. repeat TM_Correct. eapply Skip_cons_Realise. eapply Skip_cons_Terminates. }
    {
      intros tin k (ls&rs&x&l&HTin&Hk). TMSimp. clear HTin.
      exists (6 + 4 * size cX x), (16 + 8 * size cX x). repeat split; try omega. eauto 6.
      intros tmid (). intros (H&HInj); TMSimp. specialize H with (1 := eq_refl).
      destruct l as [ | x' l']; TMSimp. (* Both cases are identical *)
      1-2: exists 1, (14 + 8 * size cX x); repeat split; try omega.
      - intros tmid2 (). intros (_&HInj2); TMSimp.
        exists 3, (10 + 8 * size cX x). repeat split; try omega.
        intros tmid3 (). intros (_&H3&H3'); TMSimp.
        exists (8+8*size cX x), 1. repeat split; cbn; try omega.
        + rewrite CopySymbols_L_TermTime_moveleft; auto.
          now rewrite rev_length, !map_length.
        + intros tmid4 () _. omega.
      - intros tmid2 (). intros (_&HInj2); TMSimp.
        exists 3, (10 + 8 * size cX x). repeat split; try omega.
        intros tmid3 (). intros (_&H3&H3'); TMSimp.
        exists (8+8*size cX x), 1. repeat split; cbn; try omega.
        + rewrite CopySymbols_L_TermTime_moveleft; auto.
          now rewrite rev_length, !map_length.
        + intros tmid4 () _. omega.
    }
  Qed.


  Definition MatchList_steps l :=
    match l with
    | nil => 5
    | x::l' => 42 + 16 * size cX x
    end.

  Lemma MatchList_Terminates :
    projT1 MatchList ↓
           (fun tin k =>
              exists l : list X,
                tin[@Fin0] ≃ l /\
                isRight tin[@Fin1] /\
                MatchList_steps l <= k).
  Proof.
    unfold MatchList_steps. eapply TerminatesIn_monotone.
    { unfold MatchList. repeat TM_Correct.
      - eapply M1_Realise.
      - eapply M1_Terminates.
      - eapply Skip_cons_Realise.
      - eapply Skip_cons_Terminates.
    }
    {
      cbn. intros tin k (l&HEncL&HRight&Hk).
      destruct HEncL as (ls&HEncL); TMSimp.
      destruct l as [ | x l']; cbn.
      {
        exists 1, 3. repeat split; try omega.
        intros tmid (). intros ((_&H1)&HInj1); TMSimp.
        exists 1, 1. repeat split; try omega.
        intros tmid2 ymid2 ((H2&H2')&HInj2). apply Vector.cons_inj in H2' as (H2'&_). TMSimp.
        omega.
      }
      {
        exists 1, (40 + 16 * size cX x). repeat split; try omega.
        intros tmid (). intros ((_&H1)&HInj1); TMSimp.
        exists 1, (38 + 16 * size cX x). repeat split; try omega.
        intros tmid2 ymid2 ((H2&H2')&HInj2). apply Vector.cons_inj in H2' as (H2'&_). TMSimp. rewrite <- H2'.
        exists (23 + 12 * size cX x), (14 + 4 * size cX x). repeat split; try omega.
        { rewrite map_app, <- app_assoc. eauto 6. }
        intros tmid3 () H3'. 
        rewrite map_app, <- app_assoc in H3'. specialize H3' with (1 := HRight) (2 := eq_refl). TMSimp.
        exists (6 + 4 * size cX x), 3. repeat split; try omega. eauto 6.
        intros tmid4 () (H4&HInj4); TMSimp. specialize H4 with (1 := eq_refl).
        destruct l' as [ | x' l'']; TMSimp. (* both cases are equal *)
        - exists 1, 1. repeat split; try omega. intros ? _ _. omega.
        - exists 1, 1. repeat split; try omega. intros ? _ _. omega.
      }
    }
  Qed.



  (** *** [IsNil] *)

  Definition IsNil : pTM (sigList sigX)^+ bool 1 :=
    Move R tt;;
    MATCH Read_char
    (fun s =>
       match s with
       | Some (inr sigList_nil) =>
         Move L true
       | _ => Move L false
       end).
  
  Definition IsNil_Rel : pRel (sigList sigX)^+ bool 1 :=
    Mk_R_p (
        fun tin '(yout, tout) =>
          forall (xs : list X),
            tin ≃ xs ->
            match yout, xs with
            | true, nil => tout ≃ xs
            | false, _ :: _ => tout ≃ xs
            | _, _ => False
            end). 

  Lemma IsNil_Sem : IsNil ⊨c(5) IsNil_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold IsNil. repeat TM_Correct. }
    { Unshelve. 4-11: reflexivity. omega. }
    {
      intros tin (yout, tout) H. cbn. intros xs HEncXs.
      destruct HEncXs as (ls & HEncXs). TMSimp.
      destruct xs as [ | x xs' ]; TMSimp.
      - repeat econstructor.
      - repeat econstructor.
    }
  Qed.



  (** ** Constructors *)


  (** *** [nil] *)
  
  Definition Constr_nil : { M : mTM (sigList sigX)^+ 1 & states M -> unit } :=
    WriteMove (inl STOP) L tt;; WriteMove (inr sigList_nil) L tt;; Write (inl START) tt.


  Definition Constr_nil_Rel : Rel (tapes (sigList sigX)^+ 1) (unit * tapes (sigList sigX)^+ 1) :=
    Mk_R_p (ignoreParam (fun tin tout => isRight tin -> tout ≃ nil)).


  Lemma Constr_nil_Sem : Constr_nil ⊨c(5) Constr_nil_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold Constr_nil. repeat TM_Correct. }
    { reflexivity. }
    {
      intros tin ((), tout) H. intros HRight. TMSimp.
      repeat econstructor. f_equal. simpl_tape. cbn. rewrite isRight_right; auto.
    }
  Qed.
  

  (** *** [cons] *)

  

  Definition Constr_cons : { M : mTM (sigList sigX)^+ 2 & states M -> unit } :=
    Inject (MoveRight _;; Move L tt) [|Fin1|];;
    Inject (CopySymbols_L stop id) [|Fin1;Fin0|];;
    Inject (WriteMove (inr sigList_cons) L tt;; Write (inl START) tt) [|Fin0|].

  Definition Constr_cons_Rel : Rel (tapes (sigList sigX)^+ 2) (unit * tapes (sigList sigX)^+ 2) :=
    ignoreParam (
        fun tin tout =>
          forall l y,
            tin[@Fin0] ≃ l ->
            tin[@Fin1] ≃ y ->
            tout[@Fin0] ≃ y :: l /\
            tout[@Fin1] ≃ y
      ).

  
  Lemma Constr_cons_Realise : Constr_cons ⊨ Constr_cons_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Constr_cons. repeat TM_Correct. apply MoveRight_Realise with (X := X). }
    {
      intros tin ((), tout) H. intros l y HEncL HEncY.
      TMSimp; clear_trivial_eqs.
      specialize (H y HEncY) as (ls&H). TMSimp.
      destruct HEncL as (ls2&HEncL). TMSimp.
      rewrite CopySymbols_L_correct_moveleft in H0; swap 1 2; auto.
      { intros ? (?&<-& (?&<-&?) % in_rev % in_map_iff) % in_map_iff. cbn. reflexivity. }
      inv H0. TMSimp.
      repeat econstructor.
      - cbn. f_equal. simpl_tape. rewrite map_id. rewrite !map_rev, rev_involutive. f_equal.
        now rewrite !List.map_map, map_app, <- app_assoc, List.map_map.
      - f_equal. now rewrite !map_rev, rev_involutive.
    }
  Qed.

  Definition Constr_cons_steps (x : X) := 23 + 12 * size _ x.

  Lemma Constr_cons_Terminates :
    projT1 Constr_cons ↓
           (fun tin k =>
              exists (l: list X) (y: X),
                tin[@Fin0] ≃ l /\
                tin[@Fin1] ≃ y /\
                Constr_cons_steps y <= k).
  Proof.
    unfold Constr_cons_steps. eapply TerminatesIn_monotone.
    { unfold Constr_cons. repeat TM_Correct.
      - apply MoveRight_Realise with (X := X).
      - apply MoveRight_Realise with (X := X).
      - apply MoveRight_Terminates with (X := X).
    }
    {
      intros tin k (l&y&HEncL&HEncY&Hk). cbn.
      exists (10 + 4 * size _ y), (12 + 8 * size _ y). repeat split; try omega.
      - cbn. exists (8 + 4 * size _ y), 1. repeat split; try omega.
        + eexists. split. eauto. unfold MoveRight_steps. now rewrite Encode_map_hasSize.
        + now intros _ _ _.
      - intros tmid () (H&HInj). TMSimp.
        specialize (H _ HEncY) as (ls&HEncY'). TMSimp.
        exists (8 + 8 * size _ y), 3. repeat split; try omega.
        + erewrite CopySymbols_L_TermTime_moveleft; eauto. now rewrite map_length, rev_length, map_length.
        + intros tmid2 (). intros (H2&HInj2). TMSimp.
          exists 1, 1. repeat split; try omega. intros ? _ _. omega.
    }
  Qed.

End MatchList.


Section Steps_comp.
  Variable (sig tau: finType) (X:Type) (cX: codable sig X).
  Variable (I : Retract sig tau).

  Lemma MatchList_steps_comp l :
    MatchList_steps (Encode_map cX I) l = MatchList_steps cX l.
  Proof. unfold MatchList_steps. destruct l; auto. now rewrite Encode_map_hasSize. Qed.

  Lemma Constr_cons_steps_comp l :
    Constr_cons_steps (Encode_map cX I) l = Constr_cons_steps cX l.
  Proof. unfold Constr_cons_steps. now rewrite Encode_map_hasSize. Qed.
  
End Steps_comp.


Arguments MatchList : simpl never.
Arguments IsNil : simpl never.
Arguments Constr_nil : simpl never.
Arguments Constr_cons : simpl never.

Ltac smpl_TM_MatchList :=
  match goal with
  | [ |- MatchList _ ⊨ _ ] => apply MatchList_Realise
  | [ |- projT1 (MatchList _) ↓ _ ] => apply MatchList_Terminates

  | [ |- IsNil _ ⊨ _ ] => eapply RealiseIn_Realise; apply IsNil_Sem
  | [ |- IsNil _ ⊨c(_) _ ] => apply IsNil_Sem
  | [ |- projT1 (IsNil _ ) ↓ _ ] => eapply RealiseIn_Realise; apply IsNil_Sem
                                  
  | [ |- Constr_nil _ ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_nil_Sem
  | [ |- Constr_nil _ ⊨c(_) _ ] => apply Constr_nil_Sem
  | [ |- projT1 (Constr_nil _) ↓ _ ] => eapply RealiseIn_terminatesIn; apply Constr_nil_Sem

  | [ |- Constr_cons _ ⊨ _ ] => apply Constr_cons_Realise
  | [ |- projT1 (Constr_cons _) ↓ _ ] => apply Constr_cons_Terminates
  end.

Smpl Add smpl_TM_MatchList : TM_Correct.
