(* Helper functions for verifying machines using CopySymbols and MoveToSymbol *)

Require Import TM.Code.CodeTM.
Require Export TM.Compound.CopySymbols TM.Compound.MoveToSymbol.

Require Import TM.Basic.Mono TM.Basic.Multi.
Require Import TM.Combinators.Combinators.
Require Import TM.Compound.TMTac.
Require Import TM.Mirror.
Require Import TM.LiftMN.

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
    tl' = midtape (rev str1 ++ left (fst tltr)) x str2.
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
    tape_local_l tr' = x :: rev str1 ++ left (snd tltr).
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

  Lemma CopySymbols_pair_correct tltr str1 x str2 tl' tr':
    (forall x, List.In x str1 -> stop x = false) ->
    (stop x = true) ->
    tape_local (fst tltr) = str1 ++ x :: str2 ->
    (tl', tr') = CopySymbols_Fun stop id tltr ->
    tl' = midtape (rev str1 ++ left (fst tltr)) x str2 /\
    tape_local_l tr' = x :: rev str1 ++ left (snd tltr).
  Proof. eauto using CopySymbols_pair_first, CopySymbols_pair_second. Qed.

  Lemma MoveToSymbol_correct t str1 str2 x :
    (forall x, List.In x str1 -> stop x = false) ->
    (stop x = true) ->
    tape_local t = str1 ++ x :: str2 ->
    MoveToSymbol_Fun stop t = midtape (rev str1 ++ left t) x str2.
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
    MoveToSymbol_L_Fun stop t = midtape str2 x (rev str1 ++ right t).
  Proof.
    intros. pose proof (@MoveToSymbol_correct (mirror_tape t) str1 str2 x) as L.
    simpl_tape in L. repeat spec_assert L by auto.
    erewrite (MoveToSymbol_mirror' (t' := mirror_tape (MoveToSymbol_L_Fun stop t))) in L; simpl_tape in *; eauto.
    now apply mirror_tape_inv_midtape in L.
  Qed.

  Require Import FunInd.

  Lemma MoveToSymbol_correct_toRight' (t : tape sig) x str :
    tape_local t = x :: str ->
    right (tape_move_left (MoveToSymbol_Fun (fun _ => false) t)) = nil /\
    tape_local_l (tape_move_left (MoveToSymbol_Fun (fun _ => false) t)) = rev (tapeToList t).
  Proof.
    revert x str.
    functional induction (MoveToSymbol_Fun (fun (_ : sig) => false) t); intros; try congruence.
    - cbn in *. inv H. simpl_tape in *.
      destruct str; cbn.
      + rewrite MoveToSymbol_Fun_equation; cbn. simpl_list. cbn. auto.
      + specialize (IHt0 _ _ ltac:(eauto)).
      destruct IHt0 as (IH1&IH2). rewrite IH1, IH2. split; auto.
      destruct str; cbn; simpl_list; cbn; simpl_list; auto.
    - destruct t eqn:E; cbn in *; auto; congruence.
  Qed.

  Lemma MoveToSymbol_correct_toRight ls (x : sig) rs :
    right (tape_move_left (MoveToSymbol_Fun (fun _ => false) (midtape ls x rs))) = nil /\
    tape_local_l (tape_move_left (MoveToSymbol_Fun (fun _ => false) (midtape ls x rs))) = rev rs ++ x :: ls.
  Proof.
    pose proof @MoveToSymbol_correct_toRight' (midtape ls x rs) _ _ ltac:(cbn; eauto) as (L1&L2).
    rewrite L1, L2. cbn. simpl_list. cbn. simpl_list. cbn. auto.
  Qed.
  
  Corollary MoveToSymbol_L_correct_toLeft ls (x : sig) rs :
    left (tape_move_right (MoveToSymbol_L_Fun (fun _ => false) (midtape ls x rs))) = nil /\
    tape_local (tape_move_right (MoveToSymbol_L_Fun (fun _ => false) (midtape ls x rs))) = rev ls ++ x :: rs.
  Proof.
    intros. pose proof (@MoveToSymbol_correct_toRight rs x ls) as L.
    simpl_tape in L. repeat spec_assert L by auto.
    erewrite (MoveToSymbol_mirror' (t' := mirror_tape (MoveToSymbol_L_Fun _ _))) in L; simpl_tape in *; eauto.
    cbn in L. rewrite <- !mirror_tape_move_right in L. rewrite mirror_tape_right in L. rewrite tape_local_mirror in L.
    auto.
  Qed.



  (** Termination times *)

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
                tout = midtape (rev (encode x) ++ inl START :: r1) (inl STOP) r2
          )
      ).


  
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
      - eapply (MoveToSymbol_correct (stop := stop)) in HE2; eauto. unfold finType_CS in *. rewrite HE2.
        cbn in *. rewrite HE1, E1. cbn. trivial.
      - eapply (MoveToSymbol_correct (stop := stop)) in HE2; eauto. unfold finType_CS in *. rewrite HE2.
        + cbn in *. rewrite HE1, E1. cbn. trivial.
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

  Definition MoveToSymbol_Code_L_Rel : Rel (tapes (sig^+) 1) (unit * tapes (sig^+) 1) :=
    Mono.Mk_R_p (
        ignoreParam (
            fun tin tout =>
              forall (x : X) r1 r2,
                tape_encodes_r _ tin x r1 r2 ->
                tout = midtape r1 (inl START) (encode x ++ inl STOP :: r2)
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
      - eapply (MoveToSymbol_L_correct (stop := stop)) in HE2; eauto.
        + unfold finType_CS in *. rewrite HE2. cbn in *. rewrite E1, HE1. cbn. trivial.
        + cbn. auto.
      - eapply (MoveToSymbol_L_correct (stop := stop)) in HE2; eauto.
        + unfold finType_CS in *. rewrite HE2. cbn in *. rewrite E1, HE1. cbn. simpl_list. cbn. trivial.
        + intros ? [ -> | ? ] % in_rev; eapply (@stop_notInX x); unfold finType_CS; rewrite E1; auto.
    }
  Qed.

  Lemma MoveToSymbol_Code_L_Terminates :
    projT1 MoveToSymbol_Code_L ↓
           (fun tin k => exists x : X, tape_encodes' _ tin[@Fin.F1] x /\ 4 + 4 * length (encode x) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold MoveToSymbol_Code_L. repeat TM_Correct. }
    {
      intros tin k. intros (x&HEncX&HTx).
      destruct HEncX as (r1&r2&HE1&HE2).
      pose proof MoveToSymbols_TermTime_local_l (stop := stop) HE2 ltac:(trivial).
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
            tout[@Fin.F1] = midtape (rev (encode x) ++ inl START :: r1) (inl STOP) r2 /\
            tape_local_l tout[@Fin.FS Fin.F1] = inl STOP :: rev (encode x) ++ left tin[@Fin.FS Fin.F1]
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
      - unshelve epose proof CopySymbols_pair_correct (stop := stop) as L.
        specialize L with (4 := H). cbn in L. specialize L with (3 := HE2).
        spec_assert L by eauto. spec_assert L as (->&L) by eauto.
        cbn. unfold finType_CS in *. cbn in *.
        rewrite E1, HE1. cbn. split; auto.
      - unshelve epose proof CopySymbols_pair_correct (stop := stop) as L.
        specialize L with (4 := H). cbn in L. specialize L with (3 := HE2).
        spec_assert L.
        { intros ? [-> | ?]; eapply (@stop_notInX x); unfold finType_CS in *; rewrite E1; eauto. }
        spec_assert L as (->&L) by eauto.
        cbn. unfold finType_CS in *. cbn in *.
        rewrite E1, HE1. cbn. split; auto.
    }
  Qed.

  Lemma CopySymbols_Code_Terminates :
    projT1 CopySymbols_Code ↓ (fun tin k => exists x : X, tin[@Fin.F1] ≂ x /\ 8 + 8 * length (encode x) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold CopySymbols_Code. repeat TM_Correct. }
    {
      intros tin k (x&HencX&Hk). rewrite <- Hk.
      destruct HencX as (r1&r2&HEnc1&HEnc2).
      epose proof CopySymbols_TermTime_local (stop := stop) HEnc2 ltac:(trivial) as L.
      rewrite L.
      eapply Nat.add_le_mono. omega. cbn. simpl_list. omega.
    }
  Qed.
  
  (* TODO: Gespiegelte Variante *)
                 
End Copy_code.


Arguments MoveToSymbol_Code : simpl never.
Arguments MoveToSymbol_Code_L : simpl never.
Arguments CopySymbols_Code : simpl never.

Arguments MoveToSymbol_Code_Rel { sig X encX } x y /.
Arguments MoveToSymbol_Code_L_Rel { sig X encX } x y /.
Arguments CopySymbols_Code_Rel { sig X encX } x y /.




Section MoveToOtherSideOfTheEncoding.

  Variable sig : finType.
  Variable X : Type.
  Variable encX : codeable sig X.

  Definition dontStop : sig -> bool := fun _ => false.

  Definition MoveToRightCode :=
    MoveToSymbol_Code dontStop;;
    Move _ L tt.

  Definition MoveToRightCode_Rel : Rel (tapes (sig^+) 1) (unit * tapes (sig^+) 1) :=
    Mk_R_p (
        ignoreParam (
        fun tin tout =>
          forall (x : X) r1 r2,
            tape_encodes_l _ tin x r1 r2 ->
            tape_encodes_r _ tout x r1 r2
          )
      ).

  Lemma MoveToRightCode_WRealse :
    MoveToRightCode ⊫ MoveToRightCode_Rel.
  Proof.
    eapply WRealise_monotone.
    { unfold MoveToRightCode. repeat TM_Correct. eapply MoveToSymbol_Code_WRealise. eauto. }
    {
      intros tin ((), tout) H. TMSimp. clear_trivial_eqs.
      specialize (H _ _ _ H0) as ->. cbn.
      hnf. hnf in H0. destruct H0 as (HE1&HE2).
      simpl_tape; auto.
    }
  Qed.

  Lemma MoveToRightCode_Terminates :
    projT1 MoveToRightCode ↓
           (fun tin k => exists x : X, tin[@Fin.F1] ≂ x /\ 6 + 4 * length (encode x) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    {
      unfold MoveToRightCode. repeat TM_Correct. 
      - apply MoveToSymbol_Code_WRealise; auto.
      - apply MoveToSymbol_Code_Terminates; auto.
    }
    {
      intros tin k (x&HEncX&Hk).
      exists (4 + 4 * length (encode x)), 1. repeat split.
      - omega.
      - exists x. split. auto. omega.
      - auto.
    }
  Qed.
  
    

  Definition MoveToLeftCode :=
    MoveToSymbol_Code_L dontStop;;
    Move _ R tt.

  Definition MoveToLeftCode_Rel : Rel (tapes (sig^+) 1) (unit * tapes (sig^+) 1) :=
    Mk_R_p (
        ignoreParam (
        fun tin tout =>
          forall (x : X) r1 r2,
            tape_encodes_r _ tin x r1 r2 ->
            tape_encodes_l _ tout x r1 r2
          )
      ).

  Lemma MoveToLeftCode_WRealse :
    MoveToLeftCode ⊫ MoveToLeftCode_Rel.
  Proof.
    eapply WRealise_monotone.
    { unfold MoveToLeftCode. repeat TM_Correct. eapply MoveToSymbol_Code_L_WRealise. eauto. }
    {
      intros tin ((), tout) H. TMSimp. clear_trivial_eqs.
      specialize (H _ _ _ H0) as ->. cbn.
      hnf. hnf in H0. destruct H0 as (HE1&HE2).
      simpl_tape; auto.
    }
  Qed.

  
  Lemma MoveToLeftCode_Terminates :
    projT1 MoveToLeftCode ↓
           (fun tin k => exists x : X, tape_encodes' _ tin[@Fin.F1] x /\ 6 + 4 * length (encode x) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    {
      unfold MoveToLeftCode. repeat TM_Correct. 
      - apply MoveToSymbol_Code_L_WRealise; auto.
      - apply MoveToSymbol_Code_L_Terminates.
    }
    {
      intros tin k (x&HEncX&Hk).
      exists (4 + 4 * length (encode x)), 1. repeat split.
      - omega.
      - exists x. split. auto. omega.
      - auto.
    }
  Qed.



  (** Copy values from one tape to another tape *)

  Local Definition CopyValue :=
    Inject (WriteMove (Some (inl START), R) tt) [|Fin.FS Fin.F1|];;
    CopySymbols_Code dontStop;;
    MovePar _ L L tt.

  Definition CopyValue_Rel : Rel (tapes (sig^+) 2) (unit * tapes (sig^+) 2) :=
    ignoreParam (
        fun tin tout =>
          forall (x : X) r1 r2,
            tape_encodes_l _ tin [@Fin.F1       ] x r1 r2 ->
            tape_encodes_r _ tout[@Fin.F1       ] x r1 r2 /\
            tape_encodes'  _ tout[@Fin.FS Fin.F1] x
      ).

  Lemma CopyValue_WRealise :
    CopyValue ⊫ CopyValue_Rel.
  Proof.
    eapply WRealise_monotone.
    { unfold CopyValue. repeat TM_Correct. eapply CopySymbols_Code_WRealise; auto. }
    {
      intros tin ((), tout) H. TMSimp. clear_trivial_eqs.
      specialize (H1 _ _ _ H0) as (-> & (L1&L2) % tape_local_l_cons_iff). cbn.
      destruct H0 as (HE1&HE2).
      simpl_tape in *. split.
      - hnf. split.
        + subst. simpl_tape. auto.
        + simpl_tape. auto.
      - hnf. do 2 eexists. split.
        + erewrite tape_right_move_left; eauto.
        + erewrite tape_local_l_move_left; eauto. eapply tape_local_l_cons_iff; eauto.
    }
  Qed.

  Lemma CopyValue_Terminates :
    projT1 CopyValue ↓ (fun tin k => exists x, tin[@Fin.F1] ≂ x /\ 14 + 8 * length (encode x) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    {
      unfold CopyValue. repeat TM_Correct. 
      - apply CopySymbols_Code_WRealise; auto.
      - apply CopySymbols_Code_Terminates.
    }
    {
      intros tin k. intros (x&HEnc&Hk).
      exists 1, (12 + 8 * length (encode x)). repeat split.
      - omega.
      - hnf. omega.
      - intros tout () (H1&H2). hnf in H1, H2. simpl_not_in.
        exists (8 + 8 * length (encode x)), 3. repeat split.
        + omega.
        + exists x. repeat split; eauto. unfold finType_CS in *. rewrite <- H2. auto.
        + intros ? ? ?. omega.
    }
  Qed.


  Definition CopyValue' :=
    CopyValue;; (* 14 + 8 * length (encode x) *)
    Inject MoveToLeftCode [|Fin.F1|];; (* 6 + 4 * length (encode x) *)
    Inject MoveToLeftCode [|Fin.FS Fin.F1|]. (* 6 + 4 * length (encode x) *)

  Definition CopyValue'_Rel : Rel (tapes (sig^+) 2) (unit * tapes (sig^+) 2) :=
    ignoreParam (
        fun tin tout =>
          forall (x : X),
            tape_encodes _ tin [@Fin.F1       ] x ->
            tout[@Fin.F1] = tin[@Fin.F1] /\
            tape_encodes _ tout[@Fin.FS Fin.F1] x
      ).

  Lemma CopyValue'_WRealise :
    CopyValue' ⊫ CopyValue'_Rel.
  Proof.
    eapply WRealise_monotone.
    {
      unfold CopyValue'. repeat TM_Correct.
      - eapply CopyValue_WRealise.
      - eapply MoveToLeftCode_WRealse.
      - eapply MoveToLeftCode_WRealse.
    }
    {
      intros tin ((), yout). TMSimp.
      destruct H0 as (r1&r2&HE).
      specialize (H _ _ _ HE) as (H&H').
      destruct H' as (r1'&r2'&HE').
      specialize (H1 _ _ _ H).
      specialize (H2 _ _ _ HE').
      split.
      - eapply tape_encodes_l_injective; eauto.
      - hnf; eauto.
    }
  Qed.
  
  Lemma CopyValue'_Terminates :
    projT1 CopyValue' ↓ (fun tin k => exists x, tin[@Fin.F1] ≂ x /\ 28 + 16 * length (encode x) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    {
      unfold CopyValue'. repeat TM_Correct.
      - eapply CopyValue_WRealise.
      - eapply CopyValue_Terminates.
      - eapply MoveToLeftCode_WRealse.
      - eapply MoveToLeftCode_Terminates.
      - eapply MoveToLeftCode_Terminates.
    }
    {
      intros tin k (x&HEncX&Hk).
      exists (14 + 8 * length (encode x)), (13 + 8 * length (encode x)). repeat split.
      - omega.
      - eauto.
      - intros tout () H.
        destruct HEncX as (r1&r2&HE).
        hnf in H. specialize (H _ _ _ HE) as (L1&L2).
        exists (6 + 4 * length (encode x)), (6 + 4 * length (encode x)). repeat split.
        + omega.
        + hnf. exists x. split. cbn. do 2 eexists. eauto. omega.
        + intros tout' () (H1&H2).
          hnf in H1, H2. simpl_not_in. cbn in H1.
          specialize (H1 _ _ _ L1). hnf.
          exists x. split. cbn. rewrite <- H2. eauto. omega.
    }
  Qed.
  

End MoveToOtherSideOfTheEncoding.

Arguments MoveToRightCode : simpl never.
Arguments MoveToLeftCode : simpl never.
Arguments CopyValue : simpl never.
Arguments CopyValue' : simpl never.




Section RestoreValue.

  Variable sig : finType.
  Variable (X : Type) (codX : codeable sig X).

  Definition MoveToLeft_Rel : Rel (tapes (sig^+) 1) (unit * tapes (sig^+) 1) :=
    Mk_R_p (
        ignoreParam (
            fun tin tout =>
              forall x, tin ≂ x ->
                   exists x rs, tout = midtape nil x rs
          )
      ).

  Definition MoveToLeft :=
    MoveToSymbol_L (fun _ : (sig^+) => false);;
    Move _ R tt.

  Lemma MoveToLeft_WRealsie : MoveToLeft ⊫ MoveToLeft_Rel.
  Proof.
    eapply WRealise_monotone.
    { unfold MoveToLeft. repeat TM_Correct. }
    {
      intros tin ((), tout) H. intros x HEncX.
      destruct H as ((ymid&tmid)&(H1&_)&_&H3). cbn in *. clear ymid. rewrite H1 in *. rewrite H3 in *. clear H1 H3.
      destruct HEncX as (r1 & r2 & HE1 & HE2).
      destruct (encode x) eqn:E1; cbn in *.
      - apply midtape_tape_local_cons in HE2. unfold finType_CS in *. rewrite HE1 in HE2. rewrite HE2.
        pose proof MoveToSymbol_L_correct_toLeft (inl START :: r1) (inl STOP) r2 as (L1&L2).
        cbn in L1, L2. rewrite <- app_assoc in L2. cbn in *.
        destruct (tape_move_right _) eqn:E2; cbn in *; subst; try now apply app_cons_not_nil in L2. eauto.
      - apply midtape_tape_local_cons in HE2. unfold finType_CS in *. rewrite HE1 in HE2. rewrite HE2.
        pose proof MoveToSymbol_L_correct_toLeft (inl START :: r1) e (l ++ inl STOP :: r2) as (L1&L2).
        cbn in L1, L2. rewrite <- app_assoc in L2. cbn in *.
        destruct (tape_move_right _) eqn:E2; cbn in *; subst; try now apply app_cons_not_nil in L2. eauto.
    }
  Qed.

End RestoreValue.




(* todo: Arguments, smpl, etc. *)


(*
Ltac smpl_TM_CopyMoveCode :=
  match goal with
  | [ |- MoveToSymbol_Code    _ ⊫ _ ] => eapply MoveToSymbol_Code_WRealise
  | [ |- MoveToSymbol_Code_L  _ ⊫ _ ] => eapply MoveToSymbol_Code_L_WRealise
  | [ |- CopySymbols_Code     _ ⊫ _ ] => eapply CopySymbols_Code_WRealise
  end.

Smpl Add smpl_TM_CopyMoveCode : TM_Correct.
*)
