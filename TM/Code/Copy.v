(* Helper functions for verifying machines using CopySymbols and MoveToSymbol *)

Require Import TM.Code.CodeTM.
Require Import TM.Compound.CopySymbols TM.Compound.MoveToSymbol.

Require Import TM.Combinators.Combinators.
Require Import TM.Basic.Mono.
Require Import TM.Compound.TMTac.
Require Import TM.Mirror.

Section Copy.

  (*
  Section Test.

    Let inputX := encode (4, 3).
    Compute inputX.

    Let t : tape (Bool_Fin + Bool_Fin)^+ :=
      midtape [inr START] (inl (inl true))
              (map inl [inl true; inl true; inl true; inl false; 
                          inr true; inr true; inr true; inr false] ++ [inr STOP; inl (inl true)]).

    Compute tape_local t.
    Let stop_X :=
      fun (x : (Bool_Fin+Bool_Fin)^+) =>
        match x with
        | (inl (inl _)) => false
        | _ => true (* Stop at symbol from Y or halt/stop symbol *)
        end.

    Ltac re x := assert (x = x) by reflexivity.

    (* CopySymbols_Fun is not computable!  Use the equational rewriting to "execute"
     * (CopSymbols_Fun can be made computable by changing the termination proof to Qed.)
     *)
    Goal True.
      re (tape_local (fst (CopySymbols_Fun stop_X id (t, rightof (inr START) [])))).
      re (snd (CopySymbols_Fun stop_X id (t, rightof (inr START) []))).
      re ((left (snd (CopySymbols_Fun stop_X id (t, rightof (inr START) []))))).
      subst t; repeat ( rewrite CopySymbols_Fun_equation in *; cbn in * ); cbv [id] in *.
    Abort.


    Goal True.
      re (right (MoveToSymbol_Fun stop_X t)).
      re (left (MoveToSymbol_Fun stop_X t)).
      re (current (MoveToSymbol_Fun stop_X t)).
      re (tape_local (MoveToSymbol_Fun stop_X t)).
      Compute t.
      subst t; repeat ( rewrite MoveToSymbol_Fun_equation in *; cbn in * ).
    Abort.
    
  End Test.
   *)
  
  Variable sig : finType.
  Variable stop : sig -> bool.

  Lemma CopySymbols_pair_first tltr str1 x str2 tl' tr':
    (forall x, List.In x str1 -> stop x = false) ->
    (stop x = true) ->
    tape_local (fst tltr) = str1 ++ x :: str2 ->
    (tl', tr') = CopySymbols_Fun stop id tltr ->
    tape_local tl' = x :: str2 /\
    left tl' = rev str1 ++ left (fst tltr).
  Proof.
    intros H H0. destruct tltr as [tl tr]. intros H1 E0.
    destruct tl as [ | r rs | l ls | ls m rs]; cbn in *.
    1-3: rewrite CopySymbols_Fun_equation in E0; inv H1; exfalso; destruct str1; cbn in *; congruence.
    revert rs tr ls H ls m H1 tl' tr' E0. revert str1; intros str1.
    induction str1 as [ | s' str1' IHstr1]; (* cbn in *; *) intros.
    - cbn in *. inv H1. rewrite CopySymbols_Fun_equation in E0. rewrite H0 in E0. inv E0. cbn. auto.
    - rewrite CopySymbols_Fun_equation in E0. destruct (stop m) eqn:E1.
      + inv E0. cbn in *. inv H1. enough (stop s' = false)  by congruence; eauto.
      + cbn in H1. inv H1. cbn in *. simpl_list. destruct str1'; cbn in *; eapply IHstr1; eauto.
  Qed.

  Lemma CopySymbols_pair_second tltr str1 x str2 tl' tr':
    (forall x, List.In x str1 -> stop x = false) ->
    (stop x = true) ->
    tape_local (fst tltr) = str1 ++ x :: str2 ->
    (tl', tr') = CopySymbols_Fun stop id tltr ->
    left tr' = rev str1 ++ left (snd tltr).
  Proof.
    intros H H0. destruct tltr as [tl tr]. intros H1 E0.
    destruct tl as [ | r rs | l ls | ls m rs]; cbn in *.
    1-3: rewrite CopySymbols_Fun_equation in E0; inv H1; exfalso; destruct str1; cbn in *; congruence.
    revert rs tr ls H ls m H1 tl' tr' E0. revert str1; intros str1.
    induction str1 as [ | s' str1' IHstr1]; (* cbn in *; *) intros.
    - cbn in *. inv H1. rewrite CopySymbols_Fun_equation in E0. rewrite H0 in E0. inv E0. cbn. auto.
    - rewrite CopySymbols_Fun_equation in E0. destruct (stop m) eqn:E1.
      + inv E0. cbn in *. inv H1. enough (stop s' = false)  by congruence; eauto.
      + cbn in H1. inv H1. cbn in *.
        simpl_list; cbn.
        destruct str1'; cbn in *.
        * clear H. erewrite IHstr1; eauto. destruct tr; cbn; eauto. destruct l0; cbn; auto.
        * simpl_list; cbn.
          erewrite IHstr1; eauto. destruct tr; simpl_list; cbn; eauto. destruct l0; cbn; auto.
  Qed.


  Lemma MoveToSymbol_correct t str1 str2 x :
    (forall x, List.In x str1 -> stop x = false) ->
    (stop x = true) ->
    tape_local t = str1 ++ x :: str2 ->
    tape_local (MoveToSymbol_Fun stop t) = x :: str2 /\
    left (MoveToSymbol_Fun stop t) = rev str1 ++ left t.
  Proof.
    intros H H0. destruct t as [ | r rs | l ls | ls m rs]; cbn in *.
    1,3: rewrite MoveToSymbol_Fun_equation; cbn; destruct str1; cbn in *; try congruence.
    1: destruct str1; cbn in *; congruence.
    revert m ls str1 H. revert rs.
    refine (@size_induction _ (@length sig) _ _); intros [ | s rs'] IH; intros.
    - rewrite MoveToSymbol_Fun_equation; cbn. destruct str1; cbn in *; inv H1.
      + rewrite H0. cbn. auto.
      + destruct str1; cbn in *; congruence.
    - rewrite MoveToSymbol_Fun_equation; cbn.
      destruct (stop m) eqn:E1.
      + cbn. destruct str1; cbn in *; inv H1; eauto. specialize (H _ ltac:(eauto)). congruence.
      + destruct str1; cbn in *; inv H1.
        * congruence.
        * simpl_list. eapply IH; cbn; eauto.
  Qed.

  Corollary MoveToSymbol_L_correct t str1 str2 x :
    (forall x, List.In x str1 -> stop x = false) ->
    (stop x = true) ->
    tape_local_l t = str1 ++ x :: str2 ->
    tape_local_l (MoveToSymbol_L_Fun stop t) = x :: str2 /\
    right (MoveToSymbol_L_Fun stop t) = rev str1 ++ right t.
  Proof.
    intros. pose proof (@MoveToSymbol_correct (mirror_tape t) str1 str2 x) as L.
    simpl_tape in L. repeat spec_assert L by auto. destruct L as (L1,L2).
    simpl_tape in *. split; auto.
    erewrite (MoveToSymbol_mirror' (t' := mirror_tape (MoveToSymbol_L_Fun stop t))) in L1, L2; simpl_tape in *; eauto.
    erewrite MoveToSymbol_mirror' in L2; eauto. 2: symmetry; eapply mirror_tape_involution. now simpl_tape in *.
  Qed.

  (* Termination times *)

  (* The termination times of CopySymbols and MoveTosymbol only differ in the factors *)

  Lemma CopySymbols_TermTime_local t r1 sym r2 :
    tape_local t = r1 ++ sym :: r2 ->
    stop sym = true ->
    CopySymbols_TermTime stop t <= 8 + 8 * length r1.
  Proof.
    revert t sym r2. induction r1; intros t sym r2 HEnc HStop; cbn -[plus mult] in *.
    - destruct t; cbn in HEnc; inv HEnc. rewrite CopySymbols_TermTime_equation. rewrite HStop. cbn. omega.
    - destruct t; cbn in HEnc; try congruence. inv HEnc.
      rewrite CopySymbols_TermTime_equation. destruct (stop a).
      + omega.
      + apply Nat.add_le_mono_l. replace (8 * S (|r1|)) with (8 + 8 * |r1|) by omega.
        eapply IHr1; eauto. cbn. now simpl_tape.
  Qed.

  Lemma MoveToSymbols_TermTime_local t r1 sym r2 :
    tape_local t = r1 ++ sym :: r2 ->
    stop sym = true ->
    MoveToSymbol_TermTime stop t <= 4 + 4 * length r1.
  Proof.
    revert t sym r2. induction r1; intros t sym r2 HEnc HStop; cbn -[plus mult] in *.
    - destruct t; cbn in HEnc; inv HEnc. rewrite MoveToSymbol_TermTime_equation. rewrite HStop. cbn. omega.
    - destruct t; cbn in HEnc; try congruence. inv HEnc.
      rewrite MoveToSymbol_TermTime_equation. destruct (stop a).
      + omega.
      + apply Nat.add_le_mono_l. replace (4 * S (|r1|)) with (4 + 4 * |r1|) by omega.
        eapply IHr1; eauto. cbn. now simpl_tape.
  Qed.


  Lemma MoveToSymbols_TermTime_local_l t r1 sym r2 :
    tape_local_l t = r1 ++ sym :: r2 ->
    stop sym = true ->
    MoveToSymbol_L_TermTime stop t <= 4 + 4 * length r1.
  Proof.
    revert t sym r2. induction r1; intros t sym r2 HEnc HStop; cbn -[plus mult] in *.
    - destruct t; cbn in HEnc; inv HEnc. rewrite MoveToSymbol_L_TermTime_equation. rewrite HStop. cbn. omega.
    - destruct t; cbn in HEnc; try congruence. inv HEnc.
      rewrite MoveToSymbol_L_TermTime_equation. destruct (stop a).
      + omega.
      + apply Nat.add_le_mono_l. replace (4 * S (|r1|)) with (4 + 4 * |r1|) by omega.
        eapply IHr1; eauto. cbn. now simpl_tape.
  Qed.
  
End Copy.

Section Copy_code.
  Variable sig : finType.
  Variable X : Type.
  Variable encX : codeable sig X.


  Variable stop_X : sig -> bool.
  Hypothesis stop_X_notInX : forall x : X, forall s : sig, List.In s (encode x) -> stop_X s = false.

  Definition stop : (sig^+) -> bool :=
    fun s => match s with
          | inl _ => true
          | inr x => stop_X x
          end.

  
  Lemma stop_notInX (x : X) (s : (sig^+)) :
    List.In s (encode x) -> stop s = false.
  Proof. cbn. intros (?&<-&?) % in_map_iff. cbn. eapply stop_X_notInX; eauto. Qed.



  Definition MoveToSymbol_Code := Return (MoveToSymbol stop) tt.

  Definition MoveToSymbol_Code_Rel : Rel (tapes (sig^+) 1) (unit * tapes (sig^+) 1) :=
    Mono.Mk_R_p (
        ignoreParam (
            fun tin tout =>
              forall (x : X) r1 r2,
                tape_encodes_l _ tin x r1 r2 ->
                tape_local_l tout = inl STOP :: rev (encode x) ++ inl START :: r1 /\
                right tout = r2
          )
      ).


  
  (*
  Definition MoveToSymbol_Code :=
    MoveToSymbol stop;;
    MATCH (Read_char _)
    (fun s => match s with
           | Some (inl true) => mono_Nop _ tt (* encoding is empty *)
           | Some (inl false) => Move _ L tt (* encoding is not empty *)
           | _ => mono_Nop _ tt (* this can't happen *)
           end).
   *)


  Lemma MoveToSymbol_Code_WRealise :
    MoveToSymbol_Code ⊫ MoveToSymbol_Code_Rel.
  Proof.
    eapply WRealise_monotone.
    { unfold MoveToSymbol_Code. repeat TM_Correct. }
    {
      intros tin ((), tout). TMSimp. clear_trivial_eqs. clear H2.
      destruct H0 as (HE1&HE2).
      unfold finType_CS in *.
      destruct (encode x) eqn:E1.
      - eapply (MoveToSymbol_correct (stop := stop)) in HE2 as (L1&L2); eauto.
        split; eauto. cbn in *.
        + eapply tape_local_cons_iff in L1 as (L1&L1').
          eapply tape_local_l_cons_iff. split; eauto.
          rewrite E1. cbn. unfold finType_CS in *. rewrite HE1 in L2. congruence.
        + eapply tape_local_cons_iff in L1 as (L1&L1'). eauto.
      - eapply (MoveToSymbol_correct (stop := stop)) in HE2 as (L1&L2); eauto.
        split; eauto. cbn in *.
        + eapply tape_local_cons_iff in L1 as (L1&L1').
          eapply tape_local_l_cons_iff. split; eauto.
          rewrite E1. cbn. unfold finType_CS in *. rewrite HE1 in L2. congruence.
        + eapply tape_local_cons_iff in L1 as (L1&L1'). eauto.
        + intros ? [-> | ?]; eapply (@stop_notInX x); unfold finType_CS in *; rewrite E1; eauto.
    }
  Qed.

  Lemma MoveToSymbol_Code_Terminates :
    projT1 MoveToSymbol_Code ↓
           (fun tin k => exists x : X, tin[@Fin.F1] ≂ x /\ 4 + 4 * length (encode x) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold MoveToSymbol_Code. repeat TM_Correct. }
    {
      intros tin k. intros (x&HEncX&HTx).
      destruct HEncX as (r1&r2&HE1&HE2).
      pose proof MoveToSymbols_TermTime_local (stop := stop) HE2 ltac:(trivial).
      rewrite <- HTx. progress unfold finType_CS in *. rewrite H.
      eapply Nat.add_le_mono. omega. cbn. simpl_list. omega.
    }
  Qed.



  Definition MoveToSymbol_Code_L := Return (MoveToSymbol_L stop) tt.

  (*
  Definition MoveToSymbol_Code_L := Mirror MoveToSymbol_Code.

  Lemma MoveToSymbol_Code_L_WRealise :
    MoveToSymbol_Code_L ⊫ MoveToSymbol_Code_L_Rel.
  Proof.
    eapply WRealise_monotone.
    { unfold MoveToSymbol_Code_L. repeat TM_Correct. eapply MoveToSymbol_Code_WRealise. }
    {
      intros tin (yout, tout) H. hnf in *.
      intros x r1 r2 (HE1&HE2).
      specialize (H x r1 r2). spec_assert H.
      { hnf. simpl_tape. split; auto. 

      specialize H with (1 := HE2).
    }
   *)

  Definition MoveToSymbol_Code_L_Rel : Rel (tapes (sig^+) 1) (unit * tapes (sig^+) 1) :=
    Mono.Mk_R_p (
        ignoreParam (
            fun tin tout =>
              forall (x : X) r1 r2,
                tape_encodes_r _ tin x r1 r2 ->
                left tout = r1 /\
                tape_local tout = inl START :: encode x ++ inl STOP :: r2
          )
      ).

    
  Lemma MoveToSymbol_Code_L_WRealise :
    MoveToSymbol_Code_L ⊫ MoveToSymbol_Code_L_Rel.
  Proof.
    eapply WRealise_monotone.
    { unfold MoveToSymbol_Code_L. repeat TM_Correct. }
    {
      intros tin ((), tout). TMSimp. clear_trivial_eqs. clear H2.
      destruct H0 as (HE1&HE2).
      unfold finType_CS in *.
      destruct (encode x) eqn:E1.
      - eapply (MoveToSymbol_L_correct (stop := stop)) in HE2 as (L1&L2); eauto.
        split; eauto. cbn in *.
        + eapply tape_local_l_cons_iff in L1 as (L1&L1'). eauto.
        + eapply tape_local_l_cons_iff in L1 as (L1&L1'). unfold finType_CS in *. cbn in *. rewrite E1. cbn.
          eapply tape_local_cons_iff. split; auto. unfold finType_CS in *. congruence.
        + cbn. auto.
      - eapply (MoveToSymbol_L_correct (stop := stop)) in HE2 as (L1&L2); eauto.
        split; eauto. cbn in *.
        + eapply tape_local_l_cons_iff in L1 as (L1&L1'). eauto.
        + eapply tape_local_l_cons_iff in L1 as (L1&L1'). unfold finType_CS in *. cbn in *. rewrite E1. cbn.
          eapply tape_local_cons_iff. split; auto. unfold finType_CS in *.
          rewrite rev_app_distr, rev_involutive in L2. cbn in L2. rewrite L2. congruence.
        + intros ? [ -> | ? ] % in_rev; eapply (@stop_notInX x); unfold finType_CS; rewrite E1; auto.
    }
  Qed.

  Lemma MoveToSymbol_Code_L_Terminates :
    projT1 MoveToSymbol_Code ↓
           (fun tin k => exists x : X, tin[@Fin.F1] ≂ x /\ 4 + 4 * length (encode x) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold MoveToSymbol_Code. repeat TM_Correct. }
    {
      intros tin k. intros (x&HEncX&HTx).
      destruct HEncX as (r1&r2&HE1&HE2).
      pose proof MoveToSymbols_TermTime_local (stop := stop) HE2 ltac:(trivial).
      rewrite <- HTx. progress unfold finType_CS in *. rewrite H.
      eapply Nat.add_le_mono. omega. cbn. simpl_list. omega.
    }
  Qed.


  


  Definition CopySymbols_Code := CopySymbols stop id.

  Definition CopySymbols_Code_Rel : Rel (tapes (sig^+) 2) (unit * tapes (sig^+) 2) :=
    ignoreParam (
        fun tin tout =>
          forall x r1 r2,
            tape_encodes_l _ tin[@Fin.F1] x r1 r2 ->
            left tout[@Fin.F1] = rev (encode x) ++ inl START :: r1 /\
            tape_local tout[@Fin.F1] = inl STOP :: r2 /\
            left tout[@Fin.FS Fin.F1] = rev (encode x) ++ left tin[@Fin.FS Fin.F1]
      ).

  Lemma CopySymbols_Code_WRealise :
    CopySymbols_Code ⊫ CopySymbols_Code_Rel.
  Proof.
    eapply WRealise_monotone.
    { unfold CopySymbols_Code. repeat TM_Correct. }
    {
      intros tin ((), tout). TMSimp. clear_trivial_eqs.
      destruct H0 as (HE1&HE2).
      destruct (encode x) eqn:E1.
      - unshelve epose proof CopySymbols_pair_first (stop := stop) as L.
        specialize L with (4 := H). cbn in L. specialize L with (3 := HE2).
        spec_assert L by eauto. spec_assert L as (L1&L2) by eauto.

        unshelve epose proof CopySymbols_pair_second (stop := stop) as L.
        specialize L with (4 := H). cbn in L. specialize L with (3 := HE2).
        spec_assert L by eauto. spec_assert L by eauto.
        cbn in *. rewrite E1 in *. cbn. split; auto.
        rewrite HE1 in *. auto.
      - unshelve epose proof CopySymbols_pair_first (stop := stop) as L.
        specialize L with (4 := H). cbn in L. specialize L with (3 := HE2).
        spec_assert L.
        { intros ? [-> | ?]; eapply (@stop_notInX x); unfold finType_CS in *; rewrite E1; eauto. }
        spec_assert L as (L1&L2) by eauto.

        unshelve epose proof CopySymbols_pair_second (stop := stop) as L.
        specialize L with (4 := H). cbn in L. specialize L with (3 := HE2).
        spec_assert L.
        { intros ? [-> | ?]; eapply (@stop_notInX x); unfold finType_CS in *; rewrite E1; eauto. }
        spec_assert L by eauto.
        cbn in *. rewrite E1 in *. cbn. split; auto.
        rewrite HE1 in *. auto.
    }
  Qed.

  (* TODO: Termination *)

  (* TODO: Gespiegelte Variante *)
                 
End Copy_code.

Arguments MoveToSymbol_Code : simpl never.
Arguments CopySymbols_Code : simpl never.

Arguments MoveToSymbol_Code_Rel { sig X encX } x y /.
Arguments CopySymbols_Code_Rel { sig X encX } x y /.

Ltac smpl_TM_CopyMoveCode :=
  match goal with
  | [ |- MoveToSymbol_Code    _ ⊫ _ ] => eapply MoveToSymbol_Code_WRealise
  | [ |- MoveToSymbol_Code_L  _ ⊫ _ ] => eapply MoveToSymbol_Code_L_WRealise
  | [ |- CopySymbols_Code     _ ⊫ _ ] => eapply CopySymbols_Code_WRealise
  end.

Smpl Add smpl_TM_CopyMoveCode : TM_Correct.