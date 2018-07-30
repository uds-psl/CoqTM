(* Helper functions for verifying machines using CopySymbols and MoveToSymbol *)

Require Import FunInd.

Require Import TM.Code.CodeTM.
Require Export TM.Compound.CopySymbols TM.Compound.MoveToSymbol.

Require Import TM.Basic.Mono.
Require Import TM.Combinators.Combinators.
Require Import TM.Compound.TMTac TM.Compound.Multi.
Require Import TM.Lifting.LiftAlphabet.


Generalizable All Variables.


Lemma skipn_0 (A:Type) (xs : list A) : skipn 0 xs = xs. Proof. reflexivity. Qed.

Lemma skipn_tl (A:Type) (xs : list A) (n : nat) : skipn (S n) xs = skipn n (tl xs).
Proof. induction n; cbn; destruct xs; auto. Qed.


(* Don't simplify [skipn (S n) xs]; only, if the number and the lists are constructors *)
Local Arguments skipn { A } !n !l.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.



Section Copy.

  Variable sig : finType.
  Variable stop : sig -> bool.

  Lemma CopySymbols_correct (t : tape sig * tape sig) str1 x str2 :
    (forall x, List.In x str1 -> stop x = false) ->
    (stop x = true) ->
    tape_local (fst t) = str1 ++ x :: str2 ->
    CopySymbols_Fun stop t =
    (midtape (rev str1 ++ left (fst t)) x str2,
     midtape (rev str1 ++ left (snd t)) x (skipn (|str1|) (right (snd t)))).
  Proof.
    intros HStop1 HStop2. intros HEnc.
    revert str1 x str2 HEnc HStop1 HStop2.
    functional induction (CopySymbols_Fun stop t); cbn in *; intros.
    - destruct str1; cbn in *.
      * rewrite skipn_0.
        pose proof tape_local_current_cons HEnc as HEnc'. assert (s = x) as -> by congruence. clear HEnc'.
        f_equal. now apply midtape_tape_local_cons.
      * apply tape_local_cons_iff in HEnc as (HEnc'&HEnc). assert (s = e1) as -> by congruence. clear HEnc'.
        specialize (HStop1 _ ltac:(eauto)). congruence.
    - destruct str1; cbn in *.
      + apply tape_local_cons_iff in HEnc as (HEnc'&HEnc). assert (s = x) as -> by congruence. clear HEnc'.
        congruence.
      + apply tape_local_cons_iff in HEnc as (HEnc'&HEnc). assert (s = e1) as -> by congruence. clear HEnc'.
        apply (tape_midtape_current_right e) in HEnc. rewrite HEnc in *. cbn in *.
        rewrite <- !app_assoc. erewrite IHp; eauto. rewrite HEnc. cbn. f_equal.
        * now simpl_tape.
        * f_equal; simpl_tape. reflexivity. now rewrite skipn_tl.
        * now simpl_tape.
    - destruct (current (fst tin)) eqn:E; auto.
      apply tape_local_nil in E. rewrite E in HEnc. now apply app_cons_not_nil in HEnc.
  Qed.


  Corollary CopySymbols_correct_midtape ls m rs x rs' t2 :
    stop m = false ->
    (forall x, List.In x rs -> stop x = false) ->
    stop x = true ->
    CopySymbols_Fun stop (midtape ls m (rs ++ x :: rs'), t2) =
    (midtape (rev rs ++ m :: ls) x rs',
     midtape (rev rs ++ m :: left (t2)) x (skipn (S (|rs|)) (right t2))).
  Proof.
    intros HStopM HStopRs HStopX.
    unshelve epose proof @CopySymbols_correct (midtape ls m (rs ++ x :: rs'), t2) (m::rs) x rs' _ _ _ as L; cbn in *; eauto.
    - intros ? [->|?]; auto.
    - now rewrite <- !app_assoc in L.
  Qed.

  Corollary CopySymbols_correct_moveright ls m rs x rs' t2:
    (forall x, List.In x rs -> stop x = false) ->
    stop x = true ->
    CopySymbols_Fun stop (tape_move_right' ls m (rs ++ x :: rs'), t2) =
   (midtape (rev rs ++ m :: ls) x rs',
      midtape (rev rs ++ left t2) x (skipn (|rs|) (right t2))).
  Proof.
    intros HStopLs HStopX.
    cbv [tape_move_left']. destruct rs as [ | s s'] eqn:E; cbn in *.
    - rewrite CopySymbols_Fun_equation. cbn. rewrite HStopX; cbn. reflexivity.
    - rewrite CopySymbols_correct_midtape; auto. subst. rewrite <- !app_assoc; cbn. reflexivity.
  Qed.
  

  Corollary CopySymbols_L_correct t str1 x str2 :
    (forall x, List.In x str1 -> stop x = false) ->
    (stop x = true) ->
    tape_local_l (fst t) = str1 ++ x :: str2 ->
    CopySymbols_L_Fun stop t =
    (midtape str2 x (rev str1 ++ right (fst t)),
     midtape (skipn (|str1|) (left (snd t))) x (rev str1 ++ right (snd t))).
  Proof.
    intros HStop1 HStop2. intros HEnc.
    pose proof @CopySymbols_correct (mirror_tape (fst t), mirror_tape (snd t)) str1 x str2 HStop1 HStop2 as L.
    spec_assert L by now (cbn; simpl_tape).
    apply CopySymbols_mirror. rewrite L. unfold mirror_tapes; cbn. f_equal; [ | f_equal]; now simpl_tape.
  Qed.

  Corollary CopySymbols_L_correct_midtape ls ls' m rs x t2 :
    stop m = false ->
    (forall x, List.In x ls -> stop x = false) ->
    stop x = true ->
    CopySymbols_L_Fun stop (midtape (ls ++ x :: ls') m rs, t2) =
    (midtape ls' x (rev ls ++ m :: rs),
     midtape (skipn (S (|ls|)) (left t2)) x (rev ls ++ m :: right t2)).
  Proof.
    intros HStopM HStopRs HStopX.
    unshelve epose proof @CopySymbols_L_correct (midtape (ls ++ x :: ls') m rs, t2) (m::ls) x ls' _ _ _ as L; cbn in *; eauto.
    - intros ? [->|?]; auto.
    - now rewrite <- !app_assoc in L.
  Qed.

  Corollary CopySymbols_L_correct_moveleft ls x ls' m rs t2 :
    (forall x, List.In x ls -> stop x = false) ->
    stop x = true ->
    CopySymbols_L_Fun stop (tape_move_left' (ls ++ x :: ls') m rs, t2) =
    (midtape ls' x (rev ls ++ m :: rs),
     midtape (skipn (|ls|) (left t2)) x (rev ls ++ right t2)).
  Proof.
    intros HStopLs HStopX.
    cbv [tape_move_left']. destruct ls as [ | s s'] eqn:E; cbn in *.
    - rewrite CopySymbols_L_Fun_equation. cbn. rewrite HStopX; cbn. reflexivity.
    - rewrite CopySymbols_L_correct_midtape; auto. subst. rewrite <- !app_assoc; cbn. reflexivity.
  Qed.
  

  Variable f : sig -> sig.

  Lemma MoveToSymbol_correct t str1 str2 x :
    (forall x, List.In x str1 -> stop x = false) ->
    (stop x = true) ->
    tape_local t = str1 ++ x :: str2 ->
    MoveToSymbol_Fun stop f t = midtape (rev (map f str1) ++ left t) (f x) str2.
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

  Corollary MoveToSymbol_correct_midtape ls rs rs' m x :
    stop m = false ->
    (forall x, List.In x rs -> stop x = false) ->
    stop x = true ->
    MoveToSymbol_Fun stop f (midtape ls m (rs ++ x :: rs')) =
    midtape (rev (map f rs) ++ (f m) :: ls) (f x) rs'.
  Proof.
    intros HStopM HStopRs HStopX.
    unshelve epose proof (@MoveToSymbol_correct (midtape ls m (rs ++ x :: rs')) (m::rs) rs' x _ HStopX eq_refl) as L.
    { intros ? [->|?]; auto. }
    cbn in *. now rewrite <- app_assoc in L.
  Qed.

  Corollary MoveToSymbol_correct_moveright ls m rs x rs' :
    (forall x, List.In x rs -> stop x = false) ->
    stop x = true ->
    MoveToSymbol_Fun stop f (tape_move_right' ls m (rs ++ x :: rs')) =
    midtape (rev (map f rs) ++ m :: ls) (f x) rs'.
  Proof.
    intros HStopR HStopX.
    destruct rs as [ | s s'] eqn:E; cbn.
    - rewrite MoveToSymbol_Fun_equation. cbn. rewrite HStopX. reflexivity.
    - rewrite MoveToSymbol_correct_midtape; auto. rewrite <- !app_assoc. reflexivity.
  Qed.

  Corollary MoveToSymbol_L_correct t str1 str2 x :
    (forall x, List.In x str1 -> stop x = false) ->
    (stop x = true) ->
    tape_local_l t = str1 ++ x :: str2 ->
    MoveToSymbol_L_Fun stop f t = midtape str2 (f x) (rev (map f str1) ++ right t).
  Proof.
    intros. pose proof (@MoveToSymbol_correct (mirror_tape t) str1 str2 x) as L.
    simpl_tape in L. repeat spec_assert L by auto.
    erewrite (MoveToSymbol_mirror' (t' := mirror_tape (MoveToSymbol_L_Fun stop f t))) in L; simpl_tape in *; eauto.
    now apply mirror_tape_inv_midtape in L.
  Qed.

  Corollary MoveToSymbol_L_correct_midtape ls ls' rs m x :
    stop m = false ->
    (forall x, List.In x ls -> stop x = false) ->
    stop x = true ->
    MoveToSymbol_L_Fun stop f (midtape (ls ++ x :: ls') m rs) =
    midtape ls' (f x) (rev (map f ls) ++ (f m) :: rs).
  Proof.
    intros HStopM HStopRs HStopX.
    unshelve epose proof (@MoveToSymbol_L_correct (midtape (ls ++ x :: ls') m rs) (m::ls) ls' x _ HStopX eq_refl) as L.
    { intros ? [->|?]; auto. }
    cbn in *. now rewrite <- app_assoc in L.
  Qed.

  Corollary MoveToSymbol_L_correct_moveleft ls x ls' m rs :
    (forall x, List.In x ls -> stop x = false) ->
    stop x = true ->
    MoveToSymbol_L_Fun stop f (tape_move_left' (ls ++ x :: ls') m rs) =
    midtape ls' (f x) (rev (map f ls) ++ m :: rs).
  Proof.
    intros HStopL HStopX.
    destruct ls as [ | s s'] eqn:E; cbn.
    - rewrite MoveToSymbol_L_Fun_equation. cbn. rewrite HStopX. reflexivity.
    - rewrite MoveToSymbol_L_correct_midtape; auto. rewrite <- !app_assoc. reflexivity.
  Qed.


  (** Termination times *)

  (* The termination times of CopySymbols and MoveTosymbol only differ in the factors *)

  Lemma MoveToSymbol_steps_local t r1 sym r2 :
    tape_local t = r1 ++ sym :: r2 ->
    stop sym = true ->
    MoveToSymbol_steps stop f t <= 4 + 4 * length r1.
  Proof.
    revert t sym r2. induction r1; intros t sym r2 HEnc HStop; cbn -[plus mult] in *.
    - destruct t; cbn in HEnc; inv HEnc. rewrite MoveToSymbol_steps_equation. cbn. rewrite HStop. cbn. omega.
    - destruct t; cbn in HEnc; try congruence. inv HEnc.
      rewrite MoveToSymbol_steps_equation. cbn. destruct (stop a).
      + omega.
      + apply Nat.add_le_mono_l. replace (4 * S (|r1|)) with (4 + 4 * |r1|) by omega.
        eapply IHr1; eauto. cbn. now simpl_tape.
  Qed.

  Corollary MoveToSymbol_steps_midtape ls x m rs rs' :
    stop x = true ->
    MoveToSymbol_steps stop f (midtape ls m (rs ++ x :: rs')) <= 8 + 4 * length rs.
  Proof.
    intros.
    rewrite MoveToSymbol_steps_local with (r1 := m::rs) (sym := x) (r2 := rs'); auto.
    cbn [length]. omega.
  Qed.

  Corollary MoveToSymbol_steps_moveright ls m rs x rs' :
    stop x = true ->
    MoveToSymbol_steps stop f (tape_move_right' ls m (rs ++ x :: rs')) <= 4 + 4 * length rs.
  Proof.
    intros HStop. destruct rs as [ | s s'] eqn:E; cbn.
    - rewrite MoveToSymbol_steps_equation. cbn. rewrite HStop; cbn. omega.
    - rewrite MoveToSymbol_steps_midtape; auto. omega.
  Qed.


  Lemma MoveToSymbol_L_steps_local t r1 sym r2 :
    tape_local_l t = r1 ++ sym :: r2 ->
    stop sym = true ->
    MoveToSymbol_L_steps stop f t <= 4 + 4 * length r1.
  Proof.
    revert t sym r2. induction r1; intros t sym r2 HEnc HStop; cbn -[plus mult] in *.
    - destruct t; cbn in HEnc; inv HEnc. rewrite MoveToSymbol_L_steps_equation. cbn. rewrite HStop. cbn. omega.
    - destruct t; cbn in HEnc; try congruence. inv HEnc.
      rewrite MoveToSymbol_L_steps_equation. cbn. destruct (stop a).
      + omega.
      + apply Nat.add_le_mono_l. replace (4 * S (|r1|)) with (4 + 4 * |r1|) by omega.
        eapply IHr1; eauto. cbn. now simpl_tape.
  Qed.

  Corollary MoveToSymbol_L_steps_midtape ls ls' x m rs :
    stop x = true ->
    MoveToSymbol_L_steps stop f (midtape (ls ++ x :: ls') m rs) <= 8 + 4 * length ls.
  Proof.
    intros.
    rewrite MoveToSymbol_L_steps_local with (r1 := m::ls) (sym := x) (r2 := ls'); auto.
    cbn [length]. omega.
  Qed.

  Corollary MoveToSymbol_L_steps_moveleft ls ls' x m rs :
    stop x = true ->
    MoveToSymbol_L_steps stop f (tape_move_left' (ls ++ x :: ls') m rs) <= 4 + 4 * length ls.
  Proof.
    intros HStop. destruct ls as [ | s s'] eqn:E; cbn.
    - rewrite MoveToSymbol_L_steps_equation. cbn. rewrite HStop; cbn. omega.
    - rewrite MoveToSymbol_L_steps_midtape; auto. omega.
  Qed.


  Lemma CopySymbols_steps_local t r1 sym r2 :
    tape_local t = r1 ++ sym :: r2 ->
    stop sym = true ->
    CopySymbols_steps stop t <= 8 + 8 * length r1.
  Proof.
    revert t sym r2. induction r1; intros t sym r2 HEnc HStop; cbn -[plus mult] in *.
    - destruct t; cbn in HEnc; inv HEnc. rewrite CopySymbols_steps_equation. cbn. rewrite HStop. cbn. omega.
    - destruct t; cbn in HEnc; try congruence. inv HEnc.
      rewrite CopySymbols_steps_equation. cbn. destruct (stop a).
      + omega.
      + apply Nat.add_le_mono_l. replace (8 * S (|r1|)) with (8 + 8 * |r1|) by omega.
        eapply IHr1; eauto. cbn. now simpl_tape.
  Qed.

  Corollary CopySymbols_steps_midtape ls m rs x rs' :
    stop x = true ->
    CopySymbols_steps stop (midtape ls m (rs ++ x :: rs')) <= 16 + 8 * length rs.
  Proof.
    intros. erewrite CopySymbols_steps_local with (r1 := m :: rs); cbn -[plus mult]; eauto. omega.
  Qed.

  Corollary CopySymbols_steps_moveright ls m rs x rs' :
    stop x = true ->
    CopySymbols_steps stop (tape_move_right' ls m (rs ++ x :: rs')) <= 8 + 8 * length rs.
  Proof.
    intros HStop. destruct rs as [ | s s'] eqn:E; cbn.
    - rewrite CopySymbols_steps_equation. cbn. rewrite HStop; cbn. omega.
    - rewrite CopySymbols_steps_midtape; auto. omega.
  Qed.

  Lemma CopySymbols_L_steps_local t r1 sym r2 :
    tape_local_l t = r1 ++ sym :: r2 ->
    stop sym = true ->
    CopySymbols_L_steps stop t <= 8 + 8 * length r1.
  Proof.
    revert t sym r2. induction r1; intros t sym r2 HEnc HStop; cbn -[plus mult] in *.
    - destruct t; cbn in HEnc; inv HEnc. rewrite CopySymbols_L_steps_equation. cbn. rewrite HStop. cbn. omega.
    - destruct t; cbn in HEnc; try congruence. inv HEnc.
      rewrite CopySymbols_L_steps_equation. cbn. destruct (stop a).
      + omega.
      + apply Nat.add_le_mono_l. replace (8 * S (|r1|)) with (8 + 8 * |r1|) by omega.
        eapply IHr1; eauto. cbn. now simpl_tape.
  Qed.

  Corollary CopySymbols_L_steps_midtape ls x ls' m rs :
    stop x = true ->
    CopySymbols_L_steps stop (midtape (ls ++ x :: ls') m rs) <= 16 + 8 * length ls.
  Proof.
    intros. erewrite CopySymbols_L_steps_local with (r1 := m :: ls); cbn -[plus mult]; eauto. omega.
  Qed.

  Corollary CopySymbols_L_steps_moveleft ls ls' x m rs :
    stop x = true ->
    CopySymbols_L_steps stop (tape_move_left' (ls ++ x :: ls') m rs) <= 8 + 8 * length ls.
  Proof.
    intros HStop. destruct ls as [ | s s'] eqn:E; cbn.
    - rewrite CopySymbols_L_steps_equation. cbn. rewrite HStop; cbn. omega.
    - rewrite CopySymbols_L_steps_midtape; auto. omega.
  Qed.
  

End Copy.



(** Move between the start and the end symbol *)
Section Move.
  Variable (sig: finType) (X:Type) (cX: codable sig X).


  Definition isStop  (s: sig^+) := match s with inl STOP => true | _ => false end.
  Definition isStart (s: sig^+) := match s with inl START => true | _ => false end.

  (* Note, that [encode] maps implicitely here *)
  Lemma stop_not_in (x : X) (s : (sig^+)) :
    List.In s (encode x) -> isStop s = false.
  Proof. cbn. intros (?&<-&?) % in_map_iff. reflexivity. Qed.

  Lemma start_not_in (x : X) (s : (sig^+)) :
    List.In s (encode x) -> isStart s = false.
  Proof. cbn. intros (?&<-&?) % in_map_iff. reflexivity. Qed.


  Definition MoveRight := Return (MoveToSymbol isStop id) tt.
  Definition MoveLeft := Return (MoveToSymbol_L isStart id) tt.
  Definition Reset := MoveRight.

  Definition MoveRight_Rel : Rel (tapes (sig^+) 1) (unit * tapes (sig^+) 1) :=
    Mk_R_p (ignoreParam (fun tin tout => forall x:X, tin ≃ x -> tout ≂ x)).
  Definition MoveLeft_Rel : Rel (tapes (sig^+) 1) (unit * tapes (sig^+) 1) :=
    Mk_R_p (ignoreParam (fun tin tout => forall x:X, tin ≂ x -> tout ≃ x)).
  Definition Reset_Rel : Rel (tapes (sig^+) 1) (unit * tapes (sig^+) 1) :=
    Mk_R_p (ignoreParam (fun tin tout => forall x:X, tin ≃ x -> isRight tout)).

  Lemma MoveRight_Realise : MoveRight ⊨ MoveRight_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold MoveRight. repeat TM_Correct. }
    {
      intros tin ((), tout) H. intros x HEncX.
      TMSimp; clear_trivial_eqs. clear H0.
      destruct HEncX as (r1&->).
      erewrite MoveToSymbol_correct_midtape; eauto.
      - repeat econstructor. now rewrite map_id, map_rev.
      - apply stop_not_in.
    }
  Qed.

  Lemma MoveLeft_Realise : MoveLeft ⊨ MoveLeft_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold MoveLeft. repeat TM_Correct. }
    {
      intros tin ((), tout) H. intros x HEncX.
      TMSimp; clear_trivial_eqs. clear H0.
      destruct HEncX as (r1&->).
      erewrite MoveToSymbol_L_correct_midtape; eauto.
      - repeat econstructor. now rewrite map_id, <- map_rev, rev_involutive.
      - intros ? (?&<-&?) % in_map_iff. reflexivity.
    }
  Qed.

  Lemma Reset_Realise : Reset ⊨ Reset_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Reset. eapply MoveRight_Realise. }
    {
      intros tin ((), tout) H. intros x HEncX.
      TMSimp. eapply tape_contains_rev_isRight; eauto.
    }
  Qed.

  Definition MoveRight_steps x := 8 + 4 * size cX x.

  Lemma MoveRight_Terminates :
    projT1 MoveRight ↓ (fun tin k => exists x, tin[@Fin0] ≃ x /\ MoveRight_steps x <= k).
  Proof.
    unfold MoveRight_steps. eapply TerminatesIn_monotone.
    { unfold MoveRight. repeat TM_Correct. }
    {
      intros tin k (x&HEncX&Hk).
      destruct HEncX as (r1&->).
      rewrite MoveToSymbol_steps_midtape; auto. now rewrite map_length.
    }
  Qed.

  Definition MoveLeft_steps x := 8 + 4 * size cX x.

  Lemma MoveLeft_Terminates :
    projT1 MoveLeft ↓ (fun tin k => exists x, tin[@Fin0] ≂ x /\ MoveLeft_steps x <= k).
  Proof.
    unfold MoveLeft_steps. eapply TerminatesIn_monotone.
    { unfold MoveLeft. repeat TM_Correct. }
    {
      intros tin k (x&HEncX&Hk).
      destruct HEncX as (r1&->).
      rewrite MoveToSymbol_L_steps_midtape; auto. now rewrite map_length, rev_length.
    }
  Qed.

  Definition Reset_steps x := 8 + 4 * size cX x.

  Definition Reset_Terminates :
    projT1 Reset ↓ (fun tin k => exists x, tin[@Fin0] ≃ x /\ Reset_steps x <= k).
  Proof. exact MoveRight_Terminates. Qed.

  Definition ResetEmpty : pTM sig^+ unit 1 := Move R.

  Definition ResetEmpty_Rel : pRel sig^+ unit 1 :=
    ignoreParam (
        fun tin tout =>
          forall (x : X),
            tin[@Fin0] ≃ x ->
            cX x = nil ->
            isRight tout[@Fin0]
        ).

  Definition ResetEmpty_steps := 1.

  Lemma ResetEmpty_Sem : ResetEmpty ⊨c(ResetEmpty_steps) ResetEmpty_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold ResetEmpty. repeat TM_Correct. }
    { reflexivity. }
    {
      intros tin ((), tout) H. cbn. intros x HEncX HCod.
      destruct HEncX as (ls&HEncX). TMSimp; clear_trivial_eqs.
      destruct (cX x); cbn in *; inv HCod. cbn. repeat econstructor.
    }
  Qed.

  Definition ResetEmpty1 : pTM sig^+ (FinType(EqType unit)) 1 := Move R;; Move R.

  Definition ResetEmpty1_Rel : pRel sig^+ (FinType(EqType unit)) 1 :=
    ignoreParam (
        fun tin tout =>
          forall (x : X),
            tin[@Fin0] ≃ x ->
            size cX x = 1 ->
            isRight tout[@Fin0]
        ).

  Definition ResetEmpty1_steps := 3.

  Lemma ResetEmpty1_Sem : ResetEmpty1 ⊨c(ResetEmpty1_steps) ResetEmpty1_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold ResetEmpty1. repeat TM_Correct. }
    { reflexivity. }
    {
      intros tin ((), tout) H. cbn. intros x HEncX HCod.
      destruct HEncX as (ls&HEncX). unfold size in *. TMSimp; clear_trivial_eqs.
      destruct (cX x); cbn in *; inv HCod. destruct l; inv H2.
      cbn. repeat econstructor.
    }
  Qed.

End Move.


Section Move_steps_comp.
  Variable (sig tau: finType) (X:Type) (cX: codable sig X).
  Variable (I : Retract sig tau).

  Lemma MoveRight_steps_comp (x : X):
    MoveRight_steps (Encode_map cX I) x = MoveRight_steps cX x.
  Proof. unfold MoveRight_steps. now rewrite Encode_map_hasSize. Qed.

  Lemma MoveLeft_steps_comp (x : X):
    MoveLeft_steps (Encode_map cX I) x = MoveLeft_steps cX x.
  Proof. unfold MoveLeft_steps. now rewrite Encode_map_hasSize. Qed.
  
  Lemma Reset_steps_comp (x : X):
    Reset_steps (Encode_map cX I) x = Reset_steps cX x.
  Proof. unfold Reset_steps. now rewrite Encode_map_hasSize. Qed.

End Move_steps_comp.




(** Copy a value from to an internal (right) tape *)
Section CopyValue.
  Variable (sig: finType) (X:Type) (cX : codable sig X).

  Definition CopyValue :=
    LiftTapes (MoveRight _) [|Fin0|];; CopySymbols_L (@isStart sig).

  Definition CopyValue_Rel : Rel (tapes (sig^+) 2) (unit * tapes (sig^+) 2) :=
    ignoreParam (
        fun tin tout =>
          forall x:X,
            tin[@Fin0] ≃ x ->
            isRight tin[@Fin1] ->
            tout[@Fin0] ≃ x /\
            tout[@Fin1] ≃ x
      ).


  Lemma CopyValue_Realise : CopyValue ⊨ CopyValue_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold CopyValue. repeat TM_Correct. eapply MoveRight_Realise with (X := X). }
    {
      intros tin ((), tout) H.
      intros x HEncX HRight.
      TMSimp.
      apply H in HEncX. clear H. destruct HEncX as (r3&HEncX). TMSimp.
      cbn. erewrite CopySymbols_L_correct_midtape in H0; eauto.
      - inv H0. TMSimp. repeat econstructor; f_equal; rewrite map_rev, rev_involutive; repeat f_equal. now apply isRight_right.
      - intros ? (?&<-&?) % in_map_iff. reflexivity.
    }
  Qed.

  Definition CopyValue_steps x := 25 + 12 * size cX x.

  Lemma CopyValue_Terminates :
    projT1 CopyValue ↓ (fun tin k => exists x:X, tin[@Fin0] ≃ x /\ CopyValue_steps x <= k).
  Proof.
    unfold CopyValue_steps. eapply TerminatesIn_monotone.
    { unfold CopyValue. repeat TM_Correct.
      - eapply MoveRight_Realise.
      - eapply MoveRight_Terminates. }
    {
      intros tin k (x&HEncX&Hk).
      exists (8 + 4 * length (encode x : list sig)), (16 + 8 * length (encode x : list sig)). repeat split; cbn; eauto.
      - unfold size in *. omega.
      - intros tmid () (H1&HInj). TMSimp.
        apply H1 in HEncX as (r1&->).
        rewrite CopySymbols_L_steps_midtape; eauto.
        now rewrite map_length, rev_length.
    }
  Qed.

End CopyValue.


Section CopyValue_steps_comp.
  Variable (sig tau: finType) (X:Type) (cX: codable sig X).
  Variable (I : Retract sig tau).

  Lemma CopyValue_steps_comp (x : X):
    CopyValue_steps (Encode_map cX I) x = CopyValue_steps cX x.
  Proof. unfold CopyValue_steps. now rewrite Encode_map_hasSize. Qed.

End CopyValue_steps_comp.



(** Copy and overwrite a value *)
Section MoveValue.
  Variable sig : finType.
  Variable (X Y : Type) (cX : codable sig X) (cY : codable sig Y).

  Definition MoveValue : pTM sig^+ unit 2 :=
    LiftTapes (Reset _) [|Fin1|];;
    CopyValue _;;
    LiftTapes (Reset _) [|Fin0|].

  Definition MoveValue_Rel : pRel sig^+ unit 2 :=
    ignoreParam (
        fun tin tout =>
          forall (x : X) (y : Y),
            tin[@Fin0] ≃ x ->
            tin[@Fin1] ≃ y ->
            isRight tout[@Fin0] /\
            tout[@Fin1] ≃ x
      ).

  Lemma MoveValue_Realise : MoveValue ⊨ MoveValue_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold MoveValue. repeat TM_Correct.
      - apply Reset_Realise with (X := Y).
      - apply CopyValue_Realise with (X := X).
      - apply Reset_Realise with (X := X).
    }
    {
      intros tin ((), tout) H. cbn. intros x y HEncX HEncY.
      TMSimp.
      specialize H with (1 := HEncY).
      specialize H0 with (1 := HEncX) (2 := H) as (H0&H0').
      specialize H1 with (1 := H0).
      repeat split; auto.
    }
  Qed.

  Definition MoveValue_steps x y := 43 + 16 * size cX x + 4 * size cY y.

  Lemma MoveValue_Terminates :
    projT1 MoveValue ↓ (fun tin k => exists (x : X) (y : Y), tin[@Fin0] ≃ x /\ tin[@Fin1] ≃ y /\ MoveValue_steps x y <= k).
  Proof.
    unfold MoveValue_steps. eapply TerminatesIn_monotone.
    { unfold MoveValue. repeat TM_Correct.
      - apply Reset_Realise with (X := Y).
      - apply Reset_Terminates with (X := Y).
      - apply CopyValue_Realise with (X := X).
      - apply CopyValue_Terminates with (X := X).
      - apply Reset_Terminates with (X := X).
    }
    {
      intros tin k (x&y&HEncX&HEncY&Hk).
      exists (8 + 4 * length (cY y)), (34 + 16 * length (cX x)). repeat split; cbn; eauto.
      - unfold size in *. omega.
      - intros tmid1 () (H1&HInj1). TMSimp.
        specialize H1 with (1 := HEncY).
        exists (25 + 12 * length (cX x)), (8 + 4 * length (cX x)). repeat split; cbn; eauto.
        + omega.
        + intros tmid2 () H2.
          specialize H2 with (1 := HEncX) (2 := H1) as (H2&H2').
          exists x. split; eauto.
    }
  Qed.

  
End MoveValue.


Section MoveValue_steps_comp.
  Variable (sig tau: finType) (X Y:Type) (cX: codable sig X) (cY : codable sig Y).
  Variable (I1 I2 : Retract sig tau).

  Lemma MoveValue_steps_comp (x : X) (y: Y):
    MoveValue_steps (Encode_map cX I1) (Encode_map cY I2) x y = MoveValue_steps cX cY x y.
  Proof. unfold MoveValue_steps. now rewrite !Encode_map_hasSize. Qed.

End MoveValue_steps_comp.


Section Translate.

  Variable (tau sig : finType).
  Variable (X: Type) (cX : codable sig X).
  Variable (retr1 : Retract sig tau) (retr2 : Retract sig tau).

  Definition translate : tau^+ -> tau^+ :=
    fun t => match t with
          | inl _ => t
          | inr x => match Retr_g (Retract := retr1) x with
                    | Some y => inr (Retr_f (Retract := retr2) y)
                    | None => inl UNKNOWN
                    end
          end.

  Definition Translate' := MoveToSymbol (@isStop tau) translate.

  Definition Translate'_Rel : Rel (tapes (tau^+) 1) (unit * tapes (tau^+) 1) :=
    ignoreParam (
        fun tin tout =>
          forall x : X,
            tin[@Fin0] ≃(Encode_map cX retr1) x ->
            tout[@Fin0] ≂(Encode_map cX retr2) x
      ).

  Lemma Translate'_Realise : Translate' ⊨ Translate'_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Translate'. repeat TM_Correct. }
    {
      intros tin ((), tout) H. intros x HEncX.
      destruct HEncX as (ls&HEncX). TMSimp.
      rewrite MoveToSymbol_correct_midtape; cbn; auto.
      - repeat econstructor. cbn. f_equal. f_equal. rewrite map_rev, !List.map_map. f_equal.
        apply map_ext. cbn. intros. now retract_adjoint.
      - rewrite List.map_map. now intros ? (?&<-&?) % in_map_iff.
    }
  Qed.

  Definition Translate'_steps x := 8 + 4 * size cX x.

  Lemma Translate'_Terminates :
    projT1 Translate' ↓ (fun tin k => exists x, tin[@Fin0] ≃(Encode_map cX retr1) x /\ Translate'_steps x <= k).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Translate'. repeat TM_Correct. }
    {
      intros tin k (x&HEncX&Hk). unfold size in *.
      destruct HEncX as (r1&->).
      rewrite MoveToSymbol_steps_midtape; auto. cbn. now rewrite !map_length.
    }
  Qed.


  Definition Translate := Translate';; MoveLeft _.

  Definition Translate_Rel : Rel (tapes (tau^+) 1) (unit * tapes (tau^+) 1) :=
    ignoreParam (
        fun tin tout =>
          forall x : X,
            tin[@Fin0] ≃(Encode_map cX retr1) x ->
            tout[@Fin0] ≃(Encode_map cX retr2) x
      ).

  Lemma Translate_Realise : Translate ⊨ Translate_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Translate. repeat TM_Correct.
      - apply Translate'_Realise.
      - apply MoveLeft_Realise with (cX := Encode_map cX retr2).
    }
    {
      intros tin ((), tout) H. intros x HEncX.
      TMSimp. apply H0. apply H. apply HEncX.
    }
  Qed.


  Definition Translate_steps (x : X) := 17 + 8 * size cX x.

  Definition Translate_T : tRel tau^+ 1 :=
    fun tin k => exists x, tin[@Fin0] ≃(Encode_map cX retr1) x /\ Translate_steps x <= k.

  Lemma Translate_Terminates :
    projT1 Translate ↓ Translate_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Translate. repeat TM_Correct.
      - apply Translate'_Realise.
      - apply Translate'_Terminates.
      - apply MoveLeft_Terminates.
    }
    {
      intros tin k (x&HEncX&Hk). unfold Translate_steps in *.
      exists (8 + 4 * size cX x), (8 + 4 * size cX x). repeat split; try omega.
      eexists. repeat split; eauto.
      intros tmid () H. cbn in H. specialize H with (1 := HEncX). 
      exists x. split. eauto. unfold MoveLeft_steps. now rewrite Encode_map_hasSize.
    }
  Qed.


End Translate.

Section Translate_steps_comp.
  Variable (sig tau: finType) (X:Type) (cX: codable sig X).
  Variable (I : Retract sig tau).

  Lemma Translate_steps_comp (x : X):
    Translate_steps (Encode_map cX I) x = Translate_steps cX x.
  Proof. unfold Translate_steps. now rewrite Encode_map_hasSize. Qed.

End Translate_steps_comp.