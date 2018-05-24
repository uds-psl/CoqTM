Require Import TM.Code.CodeTM Code.Copy.
Require Import MatchNat MatchList MatchSum. (* [TM.Code.MatchSum] contains [Constr_Some] and [Constr_None]. *)
Require Import TM.LiftMN TM.LiftSigmaTau TM.Combinators.Combinators.
Require Import ChangeAlphabet.
Require Import TM.Compound.TMTac.


Local Arguments skipn { A } !n !l.


(** * Implementation of [nth_error] *)

Section Nth.

  Variable (sigX : finType) (X : Type) (encX : codable sigX X).
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
      
  
End Nth.