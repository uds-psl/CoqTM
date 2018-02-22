(* Product destruct and construction *)

Require Import TM.Code.CodeTM.
Require Import TM.Basic.Mono TM.Basic.Nop TM.Basic.Multi.
Require Import TM.Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.
Require Import TM.Compound.CopySymbols TM.Compound.MoveToSymbol.
Require Import TM.Code.Copy.

Section Projection.

  Variable X Y : Type.
  Variable (sigX sigY : finType).
  Hypothesis (codX : codeable sigX X) (codY : codeable sigY Y).


  Definition stop_X :=
    fun (x : (sigX+sigY)^+) =>
      match x with
      | (inr (inl _)) => false
      | _ => true (* Stop at symbol from Y or halt/stop symbol *)
      end.

  Definition stop_Y :=
    fun (x : (sigX+sigY)^+) =>
      match x with
        inr (inr _) => false
      | _ => true (* Stop at symbol from X or halt/stop symbol *)
      end.


  Lemma CopySymbols_pair_first' (inputX : list sigX) (inputY : list sigY) tltr tl' tr' rs' :
    tape_local (fst tltr) = map inr (map inl inputX ++ map inr inputY) ++ (inl STOP :: rs') ->
    (tl', tr') = CopySymbols_Fun stop_X id tltr ->
    tape_local (tl') = map inr (map inr inputY) ++ (inl STOP :: rs').
  Proof.
    intros. destruct inputY as [ | csy inputY'] eqn:E1; cbn in *.
    - eapply CopySymbols_pair_first; cbn; eauto.
      + rewrite app_nil_r. intuition. eapply in_map_iff in H1 as (?&<-& (?&<-&?)%in_map_iff). trivial.
      + trivial.
    - eapply CopySymbols_pair_first with (str1 := map inr (map inl inputX)); cbn; eauto.
      + intros x. rewrite !List.map_map. intros (?&<-&?) % in_map_iff. cbn. trivial.
      + simpl_list. intuition.
      + now rewrite map_app, <- app_assoc in H.
  Qed.

  Lemma CopySymbols_pair_first'' (inputX : list sigX) (inputY : list sigY) ls m rs tr tl' tr' rs' :
    m :: rs = map inr (map inl inputX ++ map inr inputY) ++ inl STOP :: rs' ->
    (tl', tr') = CopySymbols_Fun stop_X id (midtape ls m rs, tr) ->
    tape_local tl' = map inr (map inr inputY) ++ inl STOP :: rs'.
  Proof.
    intros H1 H2. apply (CopySymbols_pair_first' (tltr := (midtape ls m rs, tr)) ltac:(cbn; eapply H1) H2).
  Qed.

  Lemma CopySymbols_pair_second' (inputX : list sigX) (inputY : list sigY) tltr tl' tr' rs' :
    tape_local (fst tltr) = map inr (map inl inputX ++ map inr inputY) ++ (inl STOP :: rs') ->
    (tl', tr') = CopySymbols_Fun stop_X id tltr ->
    left tr' = map inr (map inl (rev inputX)) ++ left (snd tltr).
  Proof.
    intros. rewrite !map_rev. destruct inputY as [ | csy inputY'] eqn:E1; cbn in *.
    - rewrite app_nil_r in H.
      eapply CopySymbols_pair_second; cbn; eauto.
      + intros ? (? & <- & (? & <- & ?) % in_map_iff) % in_map_iff. cbn. trivial.
      + cbn. trivial.
    - eapply CopySymbols_pair_second with (str1 := map inr (map inl inputX)); cbn; eauto; swap 2 3.
      + intros x. rewrite !List.map_map. intros (?&<-&?) % in_map_iff. cbn. trivial.
      + rewrite map_app, <- app_assoc in H. eapply H.
      + trivial.
  Qed.
  
  Lemma CopySymbols_pair_second'' (inputX : list sigX) (inputY : list sigY) ls m rs tr tl' tr' rs' :
    m :: rs = map inr (map inl inputX ++ map inr inputY) ++ inl STOP :: rs' ->
    (tl', tr') = CopySymbols_Fun stop_X id (midtape ls m rs, tr) ->
    left tr' = map inr (map inl (rev inputX)) ++ left tr.
  Proof.
    intros H1 H2. apply (CopySymbols_pair_second' (tltr := (midtape ls m rs, tr)) ltac:(cbn; eapply H1) H2).
  Qed.


  Let M1 : { M : mTM (sigX+sigY)^+ 2 & states M -> unit } :=
    CopySymbols stop_X id;;
    Inject (
      (Move _ L tt);;
      WriteMove (Some (inl START), R) tt
    ) [|Fin.F1|].

  
  (* Copy the symbols from tape 0 to tape 1, finish tape 0 but not don't initialise tape 1 *)
  Let R1 : Rel (tapes (sigX+sigY)^+ 2) (unit * tapes (sigX+sigY)^+ 2) :=
    ignoreParam (
        fun (tin tout : tapes (sigX+sigY)^+ 2) =>
          forall (xy : X * Y),
            tin [@Fin.F1] ≂ xy ->
            tout[@Fin.F1] ≂ snd xy /\
            left (tout[@Fin.FS Fin.F1]) = rev (map inr (map inl (encode (fst xy)))) ++ left (tin[@Fin.FS Fin.F1])
      ).

  
  Lemma M1_WRealise : M1 ⊫ R1.
  Proof.
    subst M1 R1.
    eapply WRealise_monotone.
    {
      do 1 try eapply Seq_WRealise.
      all: try (eapply Inject_WRealise; [vector_dupfree| ]).
      2: eapply Seq_WRealise.
      all: try (eapply Realise_WRealise, RealiseIn_Realise;
                first [ eapply Move_Sem | eapply WriteMove_Sem | eapply Write_Sem ]).
      - eapply CopySymbols_WRealise.
    }
    {
      hnf. intros tin ((),tout) H. cbn in *. intros (inputX, inputY). TMSimp.
      destruct H0 as (r1&r2&HE1&HE2).
      destruct h1; cbn in *; inv HE1; [ do 2 destruct (encode _); cbn in HE2; congruence | ]. clear H0.
      split.
      - pose proof CopySymbols_pair_first'' HE2 H as L1.
        destruct h3; cbn in *; try (destruct (encode inputY); cbn in L1; congruence).
        destruct l; cbn in *.
        + hnf. do 2 eexists. split; cbn; eauto.
        + hnf. do 2 eexists. split; cbn; eauto.
      - pose proof (CopySymbols_pair_second'' HE2 H) as ->. now rewrite !map_rev.
    }
  Qed.


  Definition Proj : { M : mTM (sigX+sigY)^+ 2 & states M -> unit } :=
    Inject (WriteMove (Some (inl START), R) tt) [|Fin.FS Fin.F1|];;
    M1;;
    Inject (
      WriteMove (Some (inl STOP), L) tt;;
      MoveToSymbol_L stop_X;;
      Move _ R tt
    ) [|Fin.FS Fin.F1|].

  
  Definition Proj_Rel : Rel (tapes (sigX+sigY)^+ 2) (unit * tapes (sigX+sigY)^+ 2) :=
    ignoreParam (
        fun (tin tout : tapes (sigX+sigY)^+ 2) =>
          forall (xy : X * Y),
            tin [@Fin.F1] ≂ xy ->
            tout[@Fin.F1] ≂ snd xy /\
            tout[@Fin.FS Fin.F1] ≂ fst xy
      ).

  Lemma Proj_WRealise : Proj ⊫ Proj_Rel.
  Proof.
    eapply WRealise_monotone.
    {
      unfold Proj. do 2 try eapply Seq_WRealise.
      all: try (eapply Inject_WRealise; [vector_dupfree| ]).
      3: repeat eapply Seq_WRealise.
      all: try (eapply Realise_WRealise, RealiseIn_Realise;
                first [ eapply Move_Sem | eapply WriteMove_Sem | eapply Write_Sem ]).
      - eapply M1_WRealise.
      - eapply MoveToSymbol_L_WRealise.
    }
    {
      hnf. intros tin ((), tout) H. intros (inputX, inputY).
      TMSimp. clear H4 H5. clear_trivial_eqs. specialize (H1 _ H0) as (H1&H2). simpl_tape in H2. cbn in *.
      split; eauto.
      
      destruct (encode inputX) as [ | cs cX'] eqn:E1; cbn in *.
      - unfold finType_CS in *. do 2 eexists; hnf; split; cbn; hnf.
        rewrite H2. cbn. 
        rewrite MoveToSymbol_L_Fun_equation; cbn; eauto.
        rewrite H2, E1. cbn. 
        rewrite MoveToSymbol_L_Fun_equation; cbn; eauto.
      - repeat ( rewrite <- !app_assoc in *; cbn in H2 ).

        assert (tape_local_l (tape_move_mono h4 (Some (inl STOP), L)) =
                (rev (map inr (map inl cX')) ++ [inr (inl cs)]) ++ inl START :: left h2) as L1.
        {
          repeat ( rewrite <- !app_assoc in *; cbn in * ).
          destruct h4; cbn in *; rewrite H2; cbn; auto.
          subst. now simpl_tape.
        }
        
        unshelve epose proof MoveToSymbol_L_correct (stop := stop_X) _ _ L1 as (L2&L3); eauto.
        + rewrite <- !map_rev, List.map_map. intros x [ (?&<-&?) % in_map_iff | [ <- | H]] % in_app_iff; cbn; auto.
        + rewrite !List.map_map, List.rev_app_distr, <- List.app_assoc, !List.rev_involutive in L3. cbn in *.
          rewrite H2 in L1, L2, L3.
          rewrite <- !tape_local_mirror' in L1, L2.
          do 2 eexists; split; cbn.
          * unfold finType_CS in *. rewrite H2. erewrite tape_left_move_right; eauto.
            eapply tape_local_current_cons in L2. now simpl_tape in L2.
          * unfold finType_CS in *. rewrite H2. erewrite tape_local_move_right; eauto.
            eapply tape_local_cons_iff. split; eauto.
            eapply tape_local_current_cons in L2; simpl_tape in L2. eauto.
            rewrite L3. simpl_tape. rewrite E1. cbn. f_equal. now rewrite List.map_map.
    }
  Qed.


  (** * Constructor *)

  (* TODO *)


  (** * Termination *)

  Lemma CopySymbols_TermTime_pair (x : X) (y : Y) (t : tape _) :
    t ≂ (x, y) ->
    CopySymbols_TermTime stop_X t <= 8 + 8 * length (encode x).
  Proof.
    intros (r1&r2&HE1&HE2). cbn -[plus mult] in *.
    rewrite !map_app, <- app_assoc in HE2.
    destruct (encode y) eqn:E1; cbn in HE2.
    - pose proof CopySymbols_TermTime_local (stop := stop_X) HE2 ltac:(eauto). now rewrite !map_length in H.
    - pose proof CopySymbols_TermTime_local (stop := stop_X) HE2 ltac:(eauto). now rewrite !map_length in H.
  Qed.

  
  Lemma M1_Terminates :
    projT1 M1 ↓ (fun tin k => 
                   exists (xy : X * Y),
                     tin [@Fin.F1] ≂ xy /\
                     12 + 8 * length (encode (fst xy)) <= k).
  Proof.
    unfold M1. eapply TerminatesIn_monotone.
    {
      repeat TM_Correct.
    }
    {
      cbn -[plus mult]. intros tin k. intros ((x&y)&HEncXY&Ht).
      eexists. exists 3. repeat split.
      - hnf in Ht. rewrite <- Ht. rewrite Nat.add_comm.
        replace 11 with (3+8) by omega. replace (S (3 + 8)) with (4 + 8) by omega.
        rewrite <- Nat.add_assoc. apply Nat.add_le_mono_l. cbn [fst].
        eapply CopySymbols_TermTime_pair. eauto.
      - intros tout (). intros H. hnf.
        exists 1, 1. repeat split.
        + omega.
        + omega.
        + intros tout' (). intros (?&?). clear_trivial_eqs. omega.
    }
  Qed.


  Lemma Proj_Terminats :
    projT1 Proj ↓ (fun tin k =>
                   exists (xy : X * Y),
                     tin [@Fin.F1] ≂ xy /\
                     24 + 12 * length (encode (fst xy)) <= k).
  Proof.
    unfold Proj. eapply TerminatesIn_monotone.
    {
      repeat TM_Correct.
      - apply M1_WRealise.
      - apply M1_Terminates.
    }
    {
      cbn -[plus mult]. intros tin k. intros ((x&y)&HEncXY&Ht). cbn -[plus mult].
      exists 1, (22 + 12 * length (encode x)). repeat split.
      - assumption.
      - hnf. omega.
      - intros tout () ((_&H1)&H2). hnf in H1, H2. simpl_not_in. unfold finType_CS in *. rewrite <- !H2.
        exists (12 + 8 * length (encode x)), (9 + 4 * length (encode x)). repeat split.
        + omega.
        + exists (x,y). split; eauto.
        + intros tout2 () H3. specialize (H3 (x,y) ltac:(eauto)) as (H3&H4).
          hnf. exists 1, (7 + 4 * length (encode x)). repeat split.
          * omega.
          * omega.
          * intros tout3 () (_&H5). exists (4 + 4 * length (encode x)), 1. repeat split.
            -- omega.
            -- destruct H3 as (r1&r2&He1&He2). cbn -[plus mult] in *.
               rewrite H4, H1 in H5. simpl_tape in H5.
               assert (tape_local_l tout3[@Fin.F1] = rev (map inr (map inl (encode x))) ++ inl START :: left tin[@Fin.FS Fin.F1])
                 as L by (rewrite H5; now simpl_tape).
               pose proof MoveToSymbols_TermTime_local_l (stop := stop_X) L ltac:(eauto) as L2.
               now rewrite rev_length, !map_length in L2.
            -- intros tout4 [ | ]; intros; omega.
    }
  Qed.


End Projection.