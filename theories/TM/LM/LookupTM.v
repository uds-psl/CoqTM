(** * Heap Lookup *)

Require Import TM.Code.ProgrammingTools.
Require Import TM.LM.Semantics TM.LM.Alphabets.
Require Import TM.Code.ListTM TM.Code.CasePair TM.Code.CaseSum TM.Code.CaseNat.

Local Arguments plus : simpl never.
Local Arguments mult : simpl never.

Section Lookup.

  (** There is no need to save [n]. [H] must be saved. We use the [Nth'] machine, because we don't want to introduce an additional [sigOption sigHEnt] to the alphabet. [Nth'] also doesn't save [a] (which is the parameter of [Nth'] here, not [n]). [Lookup] will overwrite and reset the variables [a] and [n], but save [H] (which is saved by [Nth']). *)

(** We could define [Lookup] over the alphabet [sigHeap], however, in the step machine, we want to read [a] and [n] from a different closure alphabet (sigList sigHClos). [a] is read from an address of a closure and [n] from a variable of this closure, and the output closure will also be copied to this alphabet. *)


  Variable sigLookup : finType.
  
  Variable retr_clos_lookup : Retract sigHClos sigLookup.
  Variable retr_heap_lookup : Retract sigHeap sigLookup.


  (**
There are (more than) three possible ways how to encode [nat] on the [Heap] alphabet [sigLookup]:

- 1: as a heap address of a closure on the stack alphabet
- 2: as a variable of a command inside a closure of the closure input alphabet
- 3: as a "next" address of an heap entry

[a] is stored in the second way and [n] in the third way.
*)

  (** No 1 *)
  Definition retr_nat_clos_ad : Retract sigNat sigHClos :=
    Retract_sigPair_X _ _.
  Definition retr_nat_lookup_clos_ad : Retract sigNat sigLookup :=
    ComposeRetract retr_clos_lookup retr_nat_clos_ad.

  (** No 2 *)
  Definition retr_nat_clos_var : Retract sigNat sigHClos :=
    Retract_sigPair_Y _ _.
  Definition retr_nat_lookup_clos_var : Retract sigNat sigLookup :=
    ComposeRetract retr_clos_lookup retr_nat_clos_var.

  (** No 3 *)
  Definition retr_nat_heap_entry : Retract sigNat sigHeap :=
    Retract_sigList_X (Retract_sigOption_X (Retract_sigPair_Y _ (Retract_id _))).
  Local Definition retr_nat_lookup_entry : Retract sigNat sigLookup :=
    ComposeRetract retr_heap_lookup retr_nat_heap_entry.

  
  (** Encoding of a closure on the heap alphabet *)
  Definition retr_clos_heap : Retract sigHClos sigHeap := _.
  Definition retr_clos_lookup_heap : Retract sigHClos sigLookup := ComposeRetract retr_heap_lookup retr_clos_heap.

  Definition retr_hent_heap : Retract sigHEntr sigHeap := _.
  Local Definition retr_hent_lookup : Retract sigHEntr sigLookup := ComposeRetract retr_heap_lookup retr_hent_heap.

  Definition retr_hent'_heap : Retract sigHEntr' sigHeap := _.
  Local Definition retr_hent'_lookup : Retract sigHEntr' sigLookup := ComposeRetract retr_heap_lookup retr_hent'_heap.
  
  (*
  Tapes:
  t0: H
  t1: a
  t2: n
  t3: out
  t4: internal tape
  *)

  Definition Lookup_Step : pTM sigLookup^+ (option bool) 5 :=
    If (Nth' retr_heap_lookup retr_nat_lookup_clos_ad @ [|Fin0; Fin1; Fin4; Fin3|])
       (If (CaseOption sigHEntr'_fin ⇑ retr_hent_lookup @ [|Fin4|])
           (CasePair sigHClos_fin sigHAdd_fin ⇑ retr_hent'_lookup @ [|Fin4; Fin3|];;
            If (CaseNat ⇑ retr_nat_lookup_clos_var @ [|Fin2|])
               (Return (CopyValue _ @ [|Fin4; Fin1|];; (* n = S n' *)
                        Translate retr_nat_lookup_entry retr_nat_lookup_clos_ad @ [|Fin1|];;
                        Reset _ @ [|Fin4|];;
                        Reset _ @ [|Fin3 |])
                       None) (* continue *)
               (Return (Reset _ @ [|Fin4|];; (* n = 0 *)
                        Reset _ @ [|Fin2|];;
                        Translate retr_clos_lookup_heap retr_clos_lookup @ [|Fin3|])
                       (Some true))) (* return true *)
           (Return Nop (Some false))) (* return false *)
       (Return Nop (Some false)) (* return false *)
  .

  Definition Lookup_Step_Rel : pRel sigLookup^+ (option bool) 5 :=
    fun tin '(yout, tout) =>
      forall (H: Heap) (a n: nat),
        tin[@Fin0] ≃ H ->
        tin[@Fin1] ≃(Encode_map Encode_nat retr_nat_lookup_clos_ad ) a ->
        tin[@Fin2] ≃(Encode_map Encode_nat retr_nat_lookup_clos_var) n ->
        isRight tin[@Fin3] -> isRight tin[@Fin4] ->
        match yout, n with
        | Some true, O => (* return true *)
          exists g b,
          nth_error H a = Some (Some (g, b)) /\
          tout[@Fin0] ≃ H /\
          isRight tout[@Fin1] /\
          isRight tout[@Fin2] /\
          tout[@Fin3] ≃(Encode_map Encode_HClos retr_clos_lookup) g /\
          isRight tout[@Fin4]
        | None, S n' => (* continue *)
          exists g b,
          nth_error H a = Some (Some (g, b)) /\
          tout[@Fin0] ≃ H /\
          tout[@Fin1] ≃(Encode_map Encode_nat retr_nat_lookup_clos_ad ) b /\
          tout[@Fin2] ≃(Encode_map Encode_nat retr_nat_lookup_clos_var) n' /\
          isRight tout[@Fin3] /\
          isRight tout[@Fin4]
        | Some false, _ =>
          lookup H a n = None (* Tapes are not specified *)
        | _, _ => False (* Unreachable *)
        end.



  Lemma Lookup_Step_Realise : Lookup_Step ⊨ Lookup_Step_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Lookup_Step. TM_Correct.
      - apply Nth'_Realise.
      - apply CopyValue_Realise with (cX := Encode_map Encode_nat retr_nat_lookup_entry).
      - apply Translate_Realise with (X := nat).
      - apply Reset_Realise with (cX := Encode_map Encode_nat retr_nat_lookup_entry).
      - apply Reset_Realise with (cX := Encode_map Encode_HClos retr_clos_lookup_heap).
      - apply Reset_Realise with (cX := Encode_map Encode_nat retr_nat_lookup_entry).
      - apply Reset_Realise with (cX := Encode_map Encode_nat retr_nat_lookup_clos_var).
      - apply Translate_Realise with (X := HClos).
    }
    {
      intros tin (yout, tout) H. cbn. intros heap a n HEncHeap HEncA HEncN HRight3 HRight4.
      destruct H; TMSimp.
      { (* Then of [Nth'], i.e. nth_error H a = Some e *) rename H into HNth, H0 into HCaseOption.
        modpon HNth. destruct HNth as (e&HNth); modpon HNth.
        destruct HCaseOption; TMSimp.
        { (* Then of [CaseOption], i.e. e = Some e', where e' = (g, b) *) rename H into HCaseOption, H0 into HCasePair, H1 into HCaseNat.
          modpon HCaseOption. destruct e as [ e' | ]; auto; simpl_surject.
          modpon HCasePair.
          destruct HCaseNat; TMSimp.
          { (* Then of [CaseNat], i.e. n = S n' *)
            rename H into HCaseNat, H0 into HCopy, H1 into HTranslate, H2 into HReset, H3 into HReset'.
            modpon HCaseNat. destruct n as [ | n']; auto; simpl_surject.
            modpon HCopy.
            modpon HTranslate.
            modpon HReset.
            modpon HReset'.
            eauto 9.
          }
          { (* Else of [CaseNat], i.e. n = 0 *)
            rename H into HCaseNat, H0 into HReset, H1 into HReset', H2 into HTranslate.
            modpon HCaseNat. destruct n as [ | n']; auto; simpl_surject.
            modpon HReset.
            modpon HReset'.
            modpon HTranslate.
            eauto 8.
          }
        }
        { (* Else of [CaseOption], i.e. e = None *) rename H into HCaseOption.
          modpon HCaseOption. destruct e; auto; simpl_surject. rewrite lookup_eq, HNth. auto.
        }
      }
      { (* Else of [Nth'], i.e. nth_error H a = None *) rename H into HNth.
        modpon HNth. rewrite lookup_eq, HNth. auto.
      }
    }
  Qed.

  
  Local Definition Lookup_Step_steps_CaseNat (n: nat) (e': HClos * HAdd) :=
    let (g,b) := (fst e', snd e') in
    match n with
    | S _ => 1 + CopyValue_steps _ b + 1 + Translate_steps _ b + 1 + Reset_steps _ b + Reset_steps _ g
    | O => 1 + Reset_steps _ b + 1 + Reset_steps _ 0 + Translate_steps _ g
    end.

  Local Definition Lookup_Step_steps_CaseOption (n:nat) (e: HEntr) :=
    match e with
    | Some ((g, b) as e') => 1 + CasePair_steps _ g + 1 + CaseNat_steps + Lookup_Step_steps_CaseNat n e'
    | None => 0
    end.

  Local Definition Lookup_Step_steps_Nth' H a n :=
    match nth_error H a with
    | Some e => 1 + CaseOption_steps + Lookup_Step_steps_CaseOption n e
    | None => 0
    end.

  Definition Lookup_Step_steps (H: Heap) (a: HAdd) (n: nat) :=
    1 + Nth'_steps _ H a + Lookup_Step_steps_Nth' H a n.

    
  Definition Lookup_Step_T : tRel sigLookup^+ 5 :=
    fun tin k =>
      exists (H: Heap) (a n: nat),
        tin[@Fin0] ≃ H /\
        tin[@Fin1] ≃(Encode_map Encode_nat retr_nat_lookup_clos_ad ) a /\
        tin[@Fin2] ≃(Encode_map Encode_nat retr_nat_lookup_clos_var) n /\
        isRight tin[@Fin3] /\ isRight tin[@Fin4] /\
        Lookup_Step_steps H a n <= k.


  Lemma Lookup_Step_Terminates : projT1 Lookup_Step ↓ Lookup_Step_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Lookup_Step. TM_Correct.
      - apply Nth'_Realise.
      - apply Nth'_Terminates.
      - apply CopyValue_Realise with (cX := Encode_map Encode_nat retr_nat_lookup_entry).
      - apply CopyValue_Terminates with (cX := Encode_map Encode_nat retr_nat_lookup_entry).
      - apply Translate_Realise with (X := nat).
      - apply Translate_Terminates with (X := nat).
      - apply Reset_Realise with (cX := Encode_map Encode_nat retr_nat_lookup_entry).
      - apply Reset_Terminates with (cX := Encode_map Encode_nat retr_nat_lookup_entry).
      - apply Reset_Terminates with (cX := Encode_map Encode_HClos retr_clos_lookup_heap).
      - apply Reset_Realise with (cX := Encode_map Encode_nat retr_nat_lookup_entry).
      - apply Reset_Terminates with (cX := Encode_map Encode_nat retr_nat_lookup_entry).
      - apply Reset_Realise with (cX := Encode_map Encode_nat retr_nat_lookup_clos_var).
      - apply Reset_Terminates with (cX := Encode_map Encode_nat retr_nat_lookup_clos_var).
      - apply Translate_Terminates with (X := HClos).
    }
    {
      intros tin k. cbn. intros (H&a&n&HEncH&HEncA&HEncN&HRight3&HRight4&Hk). unfold Lookup_Step_steps in Hk.
      exists (Nth'_steps _ H a), (Lookup_Step_steps_Nth' H a n).
      repeat split; try lia.
      { hnf; cbn; eauto 7. }
      unfold Lookup_Step_steps_Nth' in *.
      intros tmid b (HNth&HNthInj); TMSimp. modpon HNth. destruct b; modpon HNth.
      { (* nth_error H a = Some e *) destruct HNth as (e&HNth); modpon HNth. rewrite HNth in *.
        exists (CaseOption_steps), (Lookup_Step_steps_CaseOption n e).
        repeat split; try lia. unfold Lookup_Step_steps_CaseOption in *.
        intros tmid0 b (HCaseOption&HCaseOptionInj); TMSimp. modpon HCaseOption. destruct b; auto.
        { (* e = Some e', where e' = (g,b) *) destruct e as [ e' | ]; auto; simpl_surject.
          destruct e' as [g b] eqn:Ee'.
          exists (CasePair_steps _ g), (1 + CaseNat_steps + Lookup_Step_steps_CaseNat n e'); subst.
          repeat split; try lia. 2: now rewrite !Nat.add_assoc.
          { hnf; cbn. exists (g,b). repeat split; simpl_surject; eauto. contains_ext. }
          intros tmid1 () (HCasePair&HCasePairInj). specialize (HCasePair (g,b)); modpon HCasePair.
          exists (CaseNat_steps), (Lookup_Step_steps_CaseNat n (g,b)).
          repeat split; try lia.
          intros tmid2 bif (HCaseNat&HCaseNatInj); TMSimp. modpon HCaseNat. destruct bif, n as [ | n']; auto; simpl_surject.
          { (* n = S n' *)
            exists (CopyValue_steps _ b), (1 + Translate_steps _ b + 1 + Reset_steps _ b + Reset_steps _ g).
            repeat split; try lia. 2: now rewrite !Nat.add_assoc.
            { eexists; repeat split; eauto. contains_ext. now setoid_rewrite CopyValue_steps_comp. }
            intros tmid3 () (HCopyValue&HCopyValueInj); TMSimp. modpon HCopyValue.
            exists (Translate_steps _ b), (1 + Reset_steps _ b + Reset_steps _ g).
            repeat split; try lia. 2: now rewrite !Nat.add_assoc.
            { hnf; cbn. eauto. }
            intros tmid4 () (HTranslate&HTranslateInj); TMSimp. modpon HTranslate.
            exists (Reset_steps _ b), (Reset_steps _ g).
            repeat split; try lia. 2: reflexivity.
            { hnf; cbn. eexists; repeat split; eauto. now setoid_rewrite Reset_steps_comp. }
            intros tmid5 () (HReset&HResetInj); TMSimp. modpon HReset.
            { hnf; cbn. eexists; repeat split; eauto. contains_ext. now setoid_rewrite Reset_steps_comp. }
          }
          { (* n = 0 *)
            exists (Reset_steps _ b), (1 + Reset_steps _ 0 + Translate_steps _ g).
            repeat split; try lia. 2: now rewrite !Nat.add_assoc.
            { eexists; split; eauto. contains_ext. now setoid_rewrite Reset_steps_comp. }
            intros tmid3 () (HReset&HResetInj); TMSimp. modpon HReset.
            exists (Reset_steps _ 0), (Translate_steps _ g).
            repeat split; try lia. 2: reflexivity.
            { eexists; split; eauto. }
            intros tmid4 () (HReset'&HResetInj'); TMSimp. modpon HReset'.
            { hnf; cbn. eexists; split; eauto. contains_ext. }
          }
        }
        { (* e = None *) destruct e; auto. }
      }
      { (* nth_error H a = None *) now rewrite HNth. }
    }
  Qed.
    

  Definition Lookup := While Lookup_Step.

  Definition Lookup_Rel : pRel sigLookup^+ bool 5 :=
    fun tin '(yout, tout) =>
      forall (H: Heap) (a n: nat),
        tin[@Fin0] ≃ H ->
        tin[@Fin1] ≃(Encode_map Encode_nat retr_nat_lookup_clos_ad) a ->
        tin[@Fin2] ≃(Encode_map Encode_nat retr_nat_lookup_clos_var) n ->
        isRight tin[@Fin3] -> isRight tin[@Fin4] ->
        match yout with
        | true =>
          exists g,
          lookup H a n = Some g /\
          tout[@Fin0] ≃ H /\ (* [H] is saved *)
          isRight tout[@Fin1] /\ (* [a] is discarded *)
          isRight tout[@Fin2] /\ (* [n] is discarded *)
          tout[@Fin3] ≃(Encode_map Encode_HClos retr_clos_lookup) g /\ (* result *)
          isRight tout[@Fin4] (* internal tape *)
        | false =>
          lookup H a n = None (* Tapes are not specified *)
        end.


  Lemma Lookup_Realise : Lookup ⊨ Lookup_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Lookup. TM_Correct.
      - apply Lookup_Step_Realise.
    }
    {
      apply WhileInduction; intros; intros heap a n HEncHeap HEncA HEncN HRight3 HRight4; cbn in *.
      - modpon HLastStep. destruct yout, n as [ | n']; auto.
        destruct HLastStep as (g&b&HLastStep); modpon HLastStep.
        eexists. rewrite lookup_eq, HLastStep. eauto 10.
      - modpon HStar. destruct n as [ | n']; auto.
        destruct HStar as (g&b&HStar); modpon HStar.
        modpon HLastStep. destruct yout.
        + destruct HLastStep as (g'&HLastStep); modpon HLastStep.
          eexists. rewrite lookup_eq, HStar. eauto 10.
        + modpon HLastStep. cbn. rewrite HStar. repeat split; auto.
    }
  Qed.

  Fixpoint Lookup_steps (H : Heap) (a : HAdd) (n : nat) : nat :=
    match nth_error H a with
    | Some (Some (g, b)) =>
      match n with
      | 0 => Lookup_Step_steps H a n
      | S n' => 1 + Lookup_Step_steps H a n + Lookup_steps H b n'
      end
    | _ => Lookup_Step_steps H a n
    end.

  Definition Lookup_T : tRel sigLookup^+ 5 :=
    fun tin k =>
      exists (H: Heap) (a n: nat),
        tin[@Fin0] ≃ H /\
        tin[@Fin1] ≃(Encode_map Encode_nat retr_nat_lookup_clos_ad) a /\
        tin[@Fin2] ≃(Encode_map Encode_nat retr_nat_lookup_clos_var) n /\
        isRight tin[@Fin3] /\ isRight tin[@Fin4] /\
        Lookup_steps H a n <= k.

  Lemma Lookup_Terminates : projT1 Lookup ↓ Lookup_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Lookup. TM_Correct.
      - apply Lookup_Step_Realise.
      - apply Lookup_Step_Terminates. }
    {
      apply WhileCoInduction. intros tin k (Heap&a&n&HEncHeap&HEncA&HEncN&HRight3&HRight4&Hk).
      exists (Lookup_Step_steps Heap a n). split.
      - hnf. do 3 eexists; repeat split; eauto.
      - intros ymid tmid HStep. cbn in *. modpon HStep. destruct ymid as [ [ | ] | ], n as [ | n']; cbn in *; auto.
        + destruct HStep as (g&b&HStep); modpon HStep. rewrite HStep in Hk. auto.
        + destruct (nth_error Heap a) as [ [ (g&b) | ] | ] eqn:E; auto.
        + destruct (nth_error Heap a) as [ [ (g&b) | ] | ] eqn:E; auto. lia.
        + destruct HStep as (g&b&HStep); modpon HStep. rewrite HStep in Hk.
          eexists; repeat split; eauto. hnf. do 3 eexists; repeat split; eauto.
    }
  Qed.

End Lookup.
