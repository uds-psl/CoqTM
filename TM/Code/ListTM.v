Require Import TM.Code.CodeTM Code.Copy.
Require Import MatchNat MatchList MatchSum. (* [TM.Code.MatchSum] contains [Constr_Some] and [Constr_None]. *)
Require Import TM.LiftMN TM.LiftSigmaTau TM.Combinators.Combinators.
Require Import ChangeAlphabet.
Require Import TM.Compound.TMTac.


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
   * t0: n (copy)
   * t1: l (copy)
   * t2: x (output)
   *)

  Definition Nth_Step_Rel : Rel (tapes tau^+ 3) ((bool*unit) * tapes tau^+ 3) :=
    fun tin '(yout, tout) =>
      forall (n : nat) (l : list X),
        tin[@Fin0] ≃ n ->
        tin[@Fin1] ≃ l ->
        isRight tin[@Fin2] ->
        match n, l with
        | S n', x :: l' => (* Recursion case *)
          tout[@Fin0] ≃ n' /\
          tout[@Fin1] ≃ l' /\
          isRight tout[@Fin2] /\
          yout = (true, tt) (* continue *)
        | S n', nil => (* list to short *)
          tout[@Fin0] ≃ n' /\
          tout[@Fin1] ≃ l /\
          tout[@Fin2] ≃ None /\
          yout = (false, tt) (* return None *)
        | 0, x::l' => (* return value *)
          tout[@Fin0] ≃ 0 /\
          tout[@Fin1] ≃ l' /\
          tout[@Fin2] ≃ Some x /\
          yout = (false, tt) (* return Some x *)
        | 0, nil => (* list to short *)
          tout[@Fin0] ≃ n /\
          tout[@Fin1] ≃ l /\
          tout[@Fin2] ≃ None /\
          yout = (false, tt) (* return None *)
        end.


  Definition Nth_Step : { M : mTM tau^+ 3 & states M -> bool*unit } :=
    If (Inject (ChangeAlphabet MatchNat _) [|Fin0|])
       (If (Inject (MatchList sigX) [|Fin1; Fin2|])
           (Return (Inject (Reset _) [|Fin2|]) (true, tt))
           (Return (Inject (Constr_None _) [|Fin2|]) (false, tt)))
       (If (Inject (MatchList sigX) [|Fin1; Fin2|])
           (Return (Inject (Constr_Some _) [|Fin2|]) (false, tt))
           (Return (Inject (Constr_None _) [|Fin2|]) (false, tt)))
  .


  Lemma Nth_Step_WRealise : Nth_Step ⊫ Nth_Step_Rel.
  Proof.
    eapply WRealise_monotone.
    { unfold Nth_Step. repeat TM_Correct.
      - unfold ChangeAlphabet. repeat TM_Correct. eapply RealiseIn_WRealise. eapply MatchNat_Sem.
      - eapply MatchList_WRealise with (X := X).
      - eapply Reset_WRealise with (X := X).
      - eapply RealiseIn_WRealise. apply Constr_None_Sem with (X := X).
      - eapply MatchList_WRealise with (X := X).
      - eapply RealiseIn_WRealise. apply Constr_Some_Sem with (X := X).
      - eapply RealiseIn_WRealise. apply Constr_None_Sem with (X := X).
    }
    {
      intros tin ((yout, ()), tout) H.
      intros n l HEncN HEncL HRight.
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
          - now eapply contains_translate_tau2 in H.
          - eapply tape_contains_ext with (1 := H0). cbn. now rewrite map_id.
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
          - now eapply contains_translate_tau2 in H.
          - eapply tape_contains_ext with (1 := H0). cbn. now rewrite map_id.
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



End Nth.