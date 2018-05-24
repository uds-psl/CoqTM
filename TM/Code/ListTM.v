Require Import TM.Code.CodeTM Code.Copy.
Require Import MatchNat MatchList MatchSum. (* [TM.Code.MatchSum] contains [Constr_Some] and [Constr_None]. *)
Require Import TM.LiftMN TM.LiftSigmaTau TM.Combinators.Combinators.
Require Import ChangeAlphabet.
Require Import TM.Compound.TMTac.


Local Arguments skipn { A } !n !l.


(** * Implementation of [nth_error] *)

Section Nth.

  Variable (sigX : finType) (X : Type) (cX : codable sigX X).
  Hypothesis (defX: inhabitedC sigX).

  Let tau := FinType (EqType (bool + sigX)).

  Check _ : codable tau nat.
  Check _ : codable tau X.
  Check _ : codable tau (list X).


  Print nth_error.

  (*
   * Nth_Step:
   * if ∃n'. n = S n'; n' -> n {
   *   if ∃x l'. l == x::l'; l' -> l {
   *     reset x
   *     continue
   *   } else {
   *     reset x
   *     x = None
   *     return
   *   }
   * } else {
   *   if ∃x l'. l == x::l'; l' -> l {
   *     x = Some x
   *     return
   *   } else {
   *     reset x
   *     x = None
   *     return
   *   }
   * }
   *
   * t0: l (copy)
   * t1: n (copy)
   * t2: x (output)
   *)

  Definition Nth_Step_Rel : Rel (tapes tau^+ 3) ((bool*unit) * tapes tau^+ 3) :=
    fun tin '(yout, tout) =>
      forall (l : list X) (n : nat),
        tin[@Fin0] ≃ l ->
        tin[@Fin1] ≃ n ->
        isRight tin[@Fin2] ->
        match n, l with
        | S n', x :: l' => (* Recursion case *)
          tout[@Fin0] ≃ l' /\
          tout[@Fin1] ≃ n' /\
          isRight tout[@Fin2] /\
          yout = (true, tt) (* continue *)
        | S n', nil => (* list to short *)
          tout[@Fin0] ≃ l /\
          tout[@Fin1] ≃ n' /\
          tout[@Fin2] ≃ None /\
          yout = (false, tt) (* return None *)
        | 0, x::l' => (* return value *)
          tout[@Fin0] ≃ l' /\
          tout[@Fin1] ≃ 0 /\
          tout[@Fin2] ≃ Some x /\
          yout = (false, tt) (* return Some x *)
        | 0, nil => (* list to short *)
          tout[@Fin0] ≃ l /\
          tout[@Fin1] ≃ n /\
          tout[@Fin2] ≃ None /\
          yout = (false, tt) (* return None *)
        end.


  Definition Nth_Step : { M : mTM tau^+ 3 & states M -> bool*unit } :=
    If (Inject (ChangeAlphabet MatchNat _) [|Fin1|])
       (If (Inject (MatchList sigX) [|Fin0; Fin2|])
           (Return (Inject (Reset _) [|Fin2|]) (true, tt))
           (Return (Inject (Constr_None _) [|Fin2|]) (false, tt)))
       (If (Inject (MatchList sigX) [|Fin0; Fin2|])
           (Return (Inject (Constr_Some _) [|Fin2|]) (false, tt))
           (Return (Inject (Constr_None _) [|Fin2|]) (false, tt)))
  .


  Lemma Nth_Step_Realise : Nth_Step ⊨ Nth_Step_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Nth_Step. repeat TM_Correct.
      - unfold ChangeAlphabet. repeat TM_Correct. eapply RealiseIn_Realise. eapply MatchNat_Sem.
      - eapply MatchList_Realise with (X := X).
      - eapply Reset_Realise with (X := X).
      - eapply RealiseIn_Realise. apply Constr_None_Sem with (X := X).
      - eapply MatchList_Realise with (X := X).
      - eapply RealiseIn_Realise. apply Constr_Some_Sem with (X := X).
      - eapply RealiseIn_Realise. apply Constr_None_Sem with (X := X).
    }
    {
      intros tin ((yout, ()), tout) H.
      intros l n HEncL HEncN HRight.
      subst tau. destruct H; TMSimp.
      { (* First "Then" case *)
        specialize (H n). spec_assert H by now eapply contains_translate_tau1.
        destruct n as [ | n']; destruct H as (H&H'); inv H'.
        (* We know that n = S n' *)

        destruct H0; TMSimp; inv_pair.
        { (* Second "Then" case *)
          specialize (H0 l). spec_assert H0.
          { unfold tape_contains. unfold tape_contains in HEncL. eapply tape_contains_ext with (1 := HEncL).
            cbn. now rewrite map_id. }
          specialize (H0 HRight).

          destruct l as [ | x l']; destruct H0 as (H0&H0'&H0''); inv H0''.
          (* We know that l = x :: l' *)
          repeat split; eauto.
          - eapply tape_contains_ext with (1 := H0). cbn. now rewrite map_id.
          - now eapply contains_translate_tau2 in H.
        }
        { (* Second "Else" case *)
          specialize (H0 l). spec_assert H0.
          { unfold tape_contains. unfold tape_contains in HEncL. eapply tape_contains_ext with (1 := HEncL).
            cbn. now rewrite map_id. }
          specialize (H0 HRight).

          destruct l as [ | x l']; destruct H0 as (H0&H0'&H0''); inv H0''.
          TMSimp; clear_trivial_eqs.
          (* We know that l = nil *)
          repeat split; eauto.
          - now eapply contains_translate_tau2 in H.
        }
      }
      { (* The first "Else" case *)
        specialize (H n). spec_assert H by now eapply contains_translate_tau1.
        destruct n as [ | n']; destruct H as (H&H'); inv H'.
        (* We know that n = 0 *)

        destruct H0; TMSimp; inv_pair.
        { (* Second "Then" case *)
          specialize (H0 l). spec_assert H0.
          { unfold tape_contains. unfold tape_contains in HEncL. eapply tape_contains_ext with (1 := HEncL).
            cbn. now rewrite map_id. }
          specialize (H0 HRight).

          destruct l as [ | x l']; destruct H0 as (H0&H0'&H0''); inv H0''.
          (* We know that l = x :: l' *)
          repeat split; eauto.
          - eapply tape_contains_ext with (1 := H0). cbn. now rewrite map_id.
          - now eapply contains_translate_tau2 in H.
        }
        { (* Second "Else" case *)
          specialize (H0 l). spec_assert H0.
          { unfold tape_contains. unfold tape_contains in HEncL. eapply tape_contains_ext with (1 := HEncL).
            cbn. now rewrite map_id. }
          specialize (H0 HRight).

          destruct l as [ | x l']; destruct H0 as (H0&H0'&H0''); inv H0''.
          (* We know that l = nil *)
          repeat split; eauto.
          - now eapply contains_translate_tau2 in H.
        }
      }
    }
  Qed.


  Definition Nth_Loop_Rel : Rel (tapes tau^+ 3) (unit * tapes tau^+ 3) :=
    ignoreParam
      (fun tin tout =>
         forall l (n : nat),
           tin[@Fin0] ≃ l ->
           tin[@Fin1] ≃ n ->
           isRight tin[@Fin2] ->
           tout[@Fin0] ≃ skipn (S n) l /\
           tout[@Fin1] ≃ n - (S (length l)) /\
           tout[@Fin2] ≃ nth_error l n).


  Definition Nth_Loop := WHILE Nth_Step.


  Lemma Nth_Loop_Realise : Nth_Loop ⊨ Nth_Loop_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Nth_Loop. repeat TM_Correct. eapply Nth_Step_Realise. }
    {
      apply WhileInduction; intros; intros l n HEncL HEncN HRight.
      - TMSimp. specialize (HLastStep _ _ HEncL HEncN HRight).
        destruct n as [ | n'], l as [ | x l']; destruct HLastStep as (H1&H2&H3&H4); inv H4; cbn; repeat split; eauto.
        now rewrite Nat.sub_0_r.
      - TMSimp. specialize (HStar _ _ HEncL HEncN HRight).
        destruct n as [ | n'], l as [ | x l']; destruct HStar as (H1&H2&H3&H4); inv H4; cbn in *;
          specialize (HLastStep _ _ H1 H2 H3) as (H4&H5&H6); auto.
    }
  Qed.


  Definition Nth : { M : mTM tau^+ 5 & states M -> unit } :=
    Inject (CopyValue _) [|Fin0; Fin3|];; (* Save l (on t0) to t3 and n (on t1) to t4 *)
    Inject (CopyValue _) [|Fin1; Fin4|];;
    Inject (Nth_Loop) [|Fin3; Fin4; Fin2|];; (* Execute the loop with the copy of n and l *)
    Inject (Reset _) [|Fin3|];; (* Reset the copies *)
    Inject (Reset _) [|Fin4|]
  .


  Lemma Nth_Computes : Nth ⊨ Computes2_Rel (@nth_error _).
  Proof.
    eapply Realise_monotone.
    { unfold Nth. repeat TM_Correct.
      - apply CopyValue_Realise with (X := list X).
      - apply CopyValue_Realise with (X := nat).
      - apply Nth_Loop_Realise.
      - apply Reset_Realise with (X := list X).
      - apply Reset_Realise with (X := nat).
    }
    {
      intros tin ((), tout) H. cbn. intros l n HEncL HEncN HOut HInt.
      specialize (HInt Fin0) as HInt1. specialize (HInt Fin1) as HInt2. clear HInt.
      TMSimp. (* This can take a while *)
      specialize H with (1 := HEncL) (2 := HInt1) as (H&H').
      specialize H0 with (1 := HEncN) (2 := HInt2) as (H0&H0').
      specialize H1 with (1 := H') (2 := H0') (3 := HOut) as (H1&H1'&H1'').
      specialize H2 with (1 := H1).
      specialize H3 with (1 := H1').
      repeat split; eauto.
      - intros i. destruct_fin i; TMSimp; auto.
    }
  Qed.


  (** ** Runtime *)


  Arguments plus : simpl never. Arguments mult : simpl never.

  Definition Nth_Step_steps l n :=
    6 + (* [5] for [MatchNat], [1] for first [If] *)
    match n, l with
    | S n, x :: l' =>
      51 + 20 * length (cX x) (* [1] for [If], [42+16*|x|] for [MatchList], [8+4*|x|] for Reset *)
    | S n, nil =>
      11 (* [1] for [If], [5] for [MatchList], [5] for [Constr_None] *)
    | O, x :: l =>
      46 + 16 * length (cX x) (* [1] for [42+16*|x|] for [MatchList], [3] for [Constr_Some] *)
    | 0, nil =>
      11 (* [1] for [If], [5] for [MatchList], [5] for [Constr_None] *)
    end.

  Definition Nth_Step_T : tRel tau^+ 3 :=
    fun tin k =>
      exists (l : list X) (n : nat),
        tin[@Fin0] ≃ l /\
        tin[@Fin1] ≃ n /\
        isRight tin[@Fin2] /\
        Nth_Step_steps l n <= k.

  Lemma Nth_Step_Terminates : projT1 Nth_Step ↓ Nth_Step_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Nth_Step. repeat TM_Correct.
      - unfold ChangeAlphabet. TM_Correct. eapply RealiseIn_Realise. apply MatchNat_Sem.
      - unfold ChangeAlphabet. TM_Correct. eapply RealiseIn_terminatesIn. apply MatchNat_Sem.
      - apply MatchList_Realise with (X := X).
      - apply MatchList_Terminates with (X := X).
      - unfold Reset. apply MoveRight_Terminates with (X := X).
      - eapply RealiseIn_terminatesIn. apply Constr_None_Sem with (X := X).
      - apply MatchList_Realise with (X := X).
      - apply MatchList_Terminates with (X := X).
      - eapply RealiseIn_terminatesIn. apply Constr_Some_Sem with (X := X).
      - eapply RealiseIn_terminatesIn. apply Constr_None_Sem with (X := X).
    }
    {
      unfold Nth_Step_T, Nth_Step_steps. intros tin k (l&n&HEncL&HEncN&HRight&Hk).
      destruct n as [ | n'], l as [ | x l']; exists 5.
      { (* n = 0, l = nil *)
        exists 11. repeat split; cbn; try omega.
        intros tmid ymid (H&HInj); TMSimp.
        specialize (H _ (contains_translate_tau1 HEncN)) as (H % contains_translate_tau2 & ->).
        exists 5, 5. repeat split. omega.
        - exists nil. repeat split; eauto.
        - intros tmid2 ymid2 (H2&HInj2). TMSimp. specialize (H2 nil) with (1 := HEncL) (2 := HRight) as (H2&H2'&->). omega.
      }
      { (* n = 0, l = x :: l' *)
        exists (46 + 16 * length (cX x)). repeat split; cbn; try omega.
        intros tmid ymid (H&HInj); TMSimp.
        specialize (H _ (contains_translate_tau1 HEncN)) as (H % contains_translate_tau2 & ->).
        exists (42+16*length(cX x)), 3. repeat split; try omega.
        - exists (x :: l'). repeat split; auto.
          apply tape_contains_ext with (1 := HEncL). cbn. f_equal. now rewrite !List.map_app, !List.map_map, map_id.
        - intros tmid2 ymid2 (H2&HInj2). TMSimp.
          specialize (H2 (x :: l')) with (2 := HRight) as (H2&H2'&->); try omega.
          apply tape_contains_ext with (1 := HEncL). cbn. f_equal. now rewrite !List.map_app, !List.map_map, map_id.
      }
      { (* n = S n'; l = nil *)
        exists 11. repeat split; cbn; try omega.
        intros tmid ymid (H&HInj); TMSimp.
        specialize (H _ (contains_translate_tau1 HEncN)) as (H % contains_translate_tau2 & ->).
        exists 5, 5. repeat split; cbn; try omega.
        - exists nil. auto.
        - intros tmid2 ymid2 (H2&HInj2). TMSimp. specialize (H2 nil) with (1 := HEncL) (2 := HRight) as (H2&H2'&->). omega.
      }
      { (* n = S n; l = x :: l' *)
        exists (51 + 20 * length (cX x)). repeat split; cbn; try omega.
        intros tmid ymid (H&HInj); TMSimp.
        specialize (H _ (contains_translate_tau1 HEncN)) as (H % contains_translate_tau2 & ->).
        exists (42+16*length (cX x)), (8+4*length (cX x)). repeat split; try omega.
        - exists (x :: l'). repeat split; auto.
          apply tape_contains_ext with (1 := HEncL). cbn. f_equal. now rewrite !List.map_app, !List.map_map, map_id.
        - intros tmid2 ymid2 (H2&HInj2). TMSimp.
          specialize (H2 (x :: l')) with (2 := HRight) as (H2&H2'&->).
          + apply tape_contains_ext with (1 := HEncL). cbn. f_equal. now rewrite !List.map_app, !List.map_map, map_id.
          + exists x. repeat split; auto. rewrite map_length. omega.
      }
    }
  Qed.


  Fixpoint Nth_Loop_steps l n :=
    match n, l with
    | S n', x :: l' => S (Nth_Step_steps l n) + Nth_Loop_steps l' n' (* Only recursion case *)
    | _, _ => S (Nth_Step_steps l n)
    end.


  Definition Nth_Loop_T : tRel tau^+ 3 :=
    fun tin k =>
      exists (l : list X) (n : nat),
        tin[@Fin0] ≃ l /\
        tin[@Fin1] ≃ n /\
        isRight tin[@Fin2] /\
        Nth_Loop_steps l n <= k.

  Lemma Nth_Loop_Terminates : projT1 Nth_Loop ↓ Nth_Loop_T.
  Proof.
    unfold Nth_Loop. repeat TM_Correct.
    { apply Nth_Step_Realise. }
    { apply Nth_Step_Terminates. }
    {
      unfold Nth_Loop_T. intros tin k (l&n&HEncL&HEncN&HRight&Hk).
      destruct n as [ | n'] eqn:E1, l as [ | x l'] eqn:E2; exists (Nth_Step_steps l n); subst.
      {
        split. hnf. do 2 eexists. repeat split; eauto.
        intros b ymid tmid H. cbn in H.
        specialize H with (1 := HEncL) (2 := HEncN) (3 := HRight); destruct H as (H1&H2&H3&H4); inv H4.
        cbv in Hk; cbv. omega.
      }
      {
        split. hnf. do 2 eexists. repeat split; eauto.
        intros b ymid tmid H. cbn in H.
        specialize H with (1 := HEncL) (2 := HEncN) (3 := HRight); destruct H as (H1&H2&H3&H4); inv H4.
        cbv in Hk; cbv. omega.
      }
      {
        split. hnf. do 2 eexists. repeat split; eauto.
        intros b ymid tmid H. cbn in H.
        specialize H with (1 := HEncL) (2 := HEncN) (3 := HRight); destruct H as (H1&H2&H3&H4); inv H4.
        cbv in Hk; cbv. omega.
      }
      {
        split. hnf. do 2 eexists. repeat split; eauto.
        intros b ymid tmid H. cbn in H.
        specialize H with (1 := HEncL) (2 := HEncN) (3 := HRight); destruct H as (H1&H2&H3&H4); inv H4.
        cbn in *.
        exists (Nth_Loop_steps l' n'). repeat split.
        - exists l', n'. eauto.
        - rewrite <- Hk. cbv [Nth_Step_steps]. omega.
      }
    }
  Qed.

  Arguments Encode_list : simpl never.
  Arguments Encode_nat : simpl never.

  (* 25 + 12 * | encode l | for Copy l *)
  (* 25 + 12 * | encode n| for Copy n *)
  (* [Nth_Loop_steps l n] for the Loop *)
  (* 8 + 4 * | encode (skipn (S n)) | for Reset l *)
  (* 8 + 4 * | encode (n - (S (length l))) | for Reset n *)
  Definition Nth_steps l n :=
    70 +
    Nth_Loop_steps l n +
    4 * length (Encode_list cX (skipn (S n) l)) +
    4 * length (Encode_nat (n - (S (length l)))) +
    12 * length (Encode_list cX l) +
    12 * length (Encode_nat n).

  Definition Nth_T : tRel tau^+ 5 :=
    fun tin k =>
      exists (l : list X) (n : nat),
        tin[@Fin0] ≃ l /\
        tin[@Fin1] ≃ n /\
        isRight tin[@Fin2] /\
        isRight tin[@Fin3] /\
        isRight tin[@Fin4] /\
        Nth_steps l n <= k.

  Lemma Nth_Terminates : projT1 Nth ↓ Nth_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Nth. repeat TM_Correct.
      - apply CopyValue_Realise with (X := list X).
      - apply CopyValue_Terminats with (X := list X).
      - apply CopyValue_Realise with (X := nat).
      - apply CopyValue_Terminats with (X := nat).
      - apply Nth_Loop_Realise.
      - apply Nth_Loop_Terminates.
      - apply Reset_Realise with (X := list X).
      - apply MoveRight_Terminates with (X := list X).
      - apply MoveRight_Terminates with (X := nat).
    }
    {
      intros tin k (l&n&HEncL&HEncN&HRight2&HRight3&HRight4&Hk). unfold Nth_steps in Hk.
      exists (25 + 12 * length (Encode_list cX (l))).
      exists (44 + Nth_Loop_steps l n +
         4 * length (Encode_list cX (skipn (S n) l)) + 4 * length (Encode_nat (n - (S (length l)))) +
         12 * length (Encode_nat n)).
      repeat split; cbn.
      - rewrite <- Hk.
        subst tau.
        (* Somehow, [generalize] doesn't work here as exspected. *)
        enough (forall a b c d,
                   25 + 12 * a +
                   S (44 + Nth_Loop_steps l n + 4 * b + 4 * c + 12 * d) <=
                   70 + Nth_Loop_steps l n + 4 * b + 4 * c +
                   12 * a + 12 * d
               ) by auto; intros. omega.
      - exists l. repeat split. cbn. eauto. rewrite map_length. omega.
      - intros tmid () (H1&HInj1). TMSimp.
        exists (25 + 12 * length (Encode_nat n)).
        exists (18 + Nth_Loop_steps l n + 4 * length (Encode_list cX (skipn (S n) l)) + 4 * length (Encode_nat (n - (S (length l))))).
        repeat split.
        + enough (forall a b c,
                     25 + 12 * a +
                     S (18 + Nth_Loop_steps l n + 4 * b + 4 * c) <=
                     44 + Nth_Loop_steps l n + 4 * b + 4 * c + 12 * a
                 ) as H by auto; intros. omega.
        + exists n. repeat split. auto. rewrite map_length. reflexivity. (* [omega] doesn't work, but [reflexivity] ? *)
        + intros tmid2 () (H2&HInj2); TMSimp.
          specialize H2 with (1 := HEncN) (2 := HRight4) as (H2&H2').
          specialize H1 with (x := l). destruct H1 as (H1&H1'); auto.
          exists (Nth_Loop_steps l n).
          exists (17 + 4 * length (Encode_list cX (skipn (S n) l)) + 4 * length (Encode_nat (n - (S (length l))))).
          repeat split.
          * enough (forall a b,
                       Nth_Loop_steps l n + S (17 + 4 * a + 4 * b) <=
                       18 + Nth_Loop_steps l n + 4 * a + 4 * b) by auto; intros; omega.
          * hnf. cbn. exists l, n. auto.
          * intros tmid3 () (H3&HInj3).
            specialize H3 with (1 := H1') (2 := H2') (3 := HRight2) as (H3&H3'&H3'').
            exists (8 + 4 * length (Encode_list cX (skipn (S n) l))).
            exists (8 + 4 * length (Encode_nat (n - S (length l)))).
            repeat split.
            -- omega.
            -- eexists. repeat split. eauto. rewrite map_length. auto.
            -- intros tmid4 () (H4&HInj4); TMSimp. specialize H4 with (1 := H3).
               eexists. repeat split. eauto. rewrite map_length. auto.
    }
  Qed.

End Nth.