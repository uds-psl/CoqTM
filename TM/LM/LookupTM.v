Require Import HeapTM.
Require Import ListTM.

(** ** Lookup *)

Local Arguments plus : simpl never.
Local Arguments mult : simpl never.

Section Lookup.


  Fixpoint lookup (H:Heap) (a:nat) (n:nat) : option HClos :=
    match nth_error H a with
    | Some (Some (g, b)) =>
      match n with
      | 0 => Some g
      | S n' => lookup H b n'
      end
    | _ => None
    end.

  Lemma lookup_eq H a n :
    lookup H a n =
    match nth_error H a with
    | Some (Some (g, b)) =>
      match n with
      | 0 => Some g
      | S n' => lookup H b n'
      end
    | _ => None
    end.
  Proof. destruct n; auto. Qed.

    


  (**
There is no need to save [n], however [H] must be saved. We use the [Nth'] machine, because we don't want to introduce an additional [sigOption sigHEnt] to the alphabet. [Nth'] also doesn't save [a] (which is the parameter of [Nth'] here, not [n]).
[Lookup] will overwrite and reset the variables [a] and [n], but save [H] (which is saved by [Nth']).

Instead of encoding the optional output of the machine with [sigOption sigHClos], our machine will only be specified if the result of [lookup] is [Some]. We can make this assumption because all heap machines we will consider never get stuck. We use the machine [Nth'], which is also only specified, if [nth_error = Some].

We could define [Lookup] over the alphabet [sigHeap], however, in the step machine, we want to read [a] and [n] from a different closure alphabet (sigList sigHClos). [a] is read from an address of a closure and [n] from a variable of this closure, and the output closure will also be copied to this alphabet.
   *)


  Variable sigLookup : finType.
  
  Variable retr_clos_lookup : Retract sigHClos sigLookup.
  Variable retr_heap_lookup : Retract sigHeap sigLookup.


  (**
There are (more than) three possible ways how to encode [nat] on the [Heap] alphabet [sigLookup]:

- 1: as an adress of a closure in an entry
- 2: as the "next" address of an entry
- 3: as a variable of a token inside a closure of the closure input alphabet

[a] is stored in the second way and [n] in the third way.
*)

  (* No 1 *)
  Definition retr_nat_clos_ad : Retract sigNat sigHClos :=
    Retract_sigPair_X _ _.
  Definition retr_nat_lookup_clos_ad : Retract sigNat sigLookup :=
    ComposeRetract retr_nat_clos_ad retr_clos_lookup.

  (* No 2 *)
  Definition retr_nat_heap_entry : Retract sigNat sigHeap :=
    Retract_sigList_X (Retract_sigOption_X (Retract_sigPair_Y _ (Retract_id _))).
  Local Definition retr_nat_lookup_entry : Retract sigNat sigLookup :=
    ComposeRetract retr_nat_heap_entry retr_heap_lookup.

  (* No 3 *)
  Definition retr_nat_clos_var : Retract sigNat sigHClos :=
    Retract_sigPair_Y _ _.
  Definition retr_nat_lookup_clos_var : Retract sigNat sigLookup :=
    ComposeRetract retr_nat_clos_var retr_clos_lookup.

  
  (** Encoding of a closure on the heap alphabet *)
  Definition retr_clos_heap : Retract sigHClos sigHeap := _.
  Definition retr_clos_lookup_heap : Retract sigHClos sigLookup := ComposeRetract retr_clos_heap retr_heap_lookup.

  Definition retr_hent_heap : Retract sigHEnt sigHeap := _.
  Local Definition retr_hent_lookup : Retract sigHEnt sigLookup := ComposeRetract retr_hent_heap retr_heap_lookup.

  Definition retr_hent'_heap : Retract sigHEnt' sigHeap := _.
  Local Definition retr_hent'_lookup : Retract sigHEnt' sigLookup := ComposeRetract retr_hent'_heap retr_heap_lookup.
  
(*
Tapes:
t0: H
t1: a
t2: n
t3: out
t4: internal tape
*)

  Definition Lookup_Step : pTM sigLookup^+ (bool*unit) 5 :=
    Nth' retr_heap_lookup retr_nat_lookup_clos_ad @ [|Fin0; Fin1; Fin4; Fin3|];;
    MatchOption sigHEnt'_fin ⇑ retr_hent_lookup @ [|Fin4|];;
    MatchPair sigHClos_fin sigHAd_fin ⇑ retr_hent'_lookup @ [|Fin4; Fin3|];;
    If (MatchNat ⇑ retr_nat_lookup_clos_var @ [|Fin2|])
       (Return (CopyValue _ @ [|Fin4; Fin1|];;
                Translate retr_nat_lookup_entry retr_nat_lookup_clos_ad @ [|Fin1|];;
                Reset _ @ [|Fin4|];;
                Reset _ @ [|Fin3|]) (true, tt))
       (Return (Reset _ @ [|Fin4|];;
                Reset _ @ [|Fin2|];;
                Translate retr_clos_lookup_heap retr_clos_lookup @ [|Fin3|]) (false, tt))
  .

  Definition Lookup_Step_Rel : pRel sigLookup^+ (bool*unit) 5 :=
    fun tin '(yout, tout) =>
      forall (H: Heap) (a n: nat) (g : HClos) (b : HAd),
        nth_error H a = Some (Some (g, b)) ->
        tin[@Fin0] ≃ H ->
        tin[@Fin1] ≃(Encode_map Encode_nat retr_nat_lookup_clos_ad ) a ->
        tin[@Fin2] ≃(Encode_map Encode_nat retr_nat_lookup_clos_var) n ->
        isRight tin[@Fin3] -> isRight tin[@Fin4] ->
        match yout, n with
        | (false, tt), O => (* return *)
          tout[@Fin0] ≃ H /\
          isRight tout[@Fin1] /\
          isRight tout[@Fin2] /\
          tout[@Fin3] ≃(Encode_map Encode_HClos retr_clos_lookup) g /\
          isRight tout[@Fin4]
        | (true, tt), S n' => (* continue *)
          tout[@Fin0] ≃ H /\
          tout[@Fin1] ≃(Encode_map Encode_nat retr_nat_lookup_clos_ad ) b /\
          tout[@Fin2] ≃(Encode_map Encode_nat retr_nat_lookup_clos_var) n' /\
          isRight tout[@Fin3] /\
          isRight tout[@Fin4]
        | _, _ => False (* Unreachable *)
        end.


  Lemma Lookup_Step_Realise : Lookup_Step ⊨ Lookup_Step_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Lookup_Step. repeat TM_Correct.
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
      intros tin ((yout, ()), tout) H. cbn. intros heap a n g b HNthSome HEncHeap HEncA HEncN HRight3 HRight4.
      TMSimp. rename H into HNth, H0 into HMatchOption, H1 into HMatchPair, H2 into HIf.
      modpon HNth.
      modpon HMatchOption. destruct ymid; auto; modpon HMatchOption.
      specialize (HMatchPair (g, b)). modpon HMatchPair. cbn in *.
      destruct HIf; TMSimp.
      { (* If of [MatchNat] (n = S n') *)
        rename H into HMatchNat, H0 into HRet, H1 into HCopyValue, H2 into HTranslate, H3 into HReset, H4 into HReset'.
        inv HRet.
        modpon HMatchNat. destruct n as [ | n']; auto; simpl_surject.
        modpon HCopyValue.
        modpon HTranslate.
        modpon HReset.
        modpon HReset'.
        repeat split; auto.
      }
      { (* Else of [MatchNat] *)
        rename H into HMatchNat, H0 into HRet, H1 into HReset, H2 into HReset', H3 into HTranslate.
        modpon HMatchNat. destruct n as [ | n']; auto.
        inv HRet.
        modpon HReset.
        modpon HReset'.
        modpon HTranslate.
        repeat split; auto.
      }
    }
  Qed.
  
  Definition Lookup_steps_MatchNat (n: nat) (g: HClos) (b: HAd) :=
    match n with
    | O => 2 + Reset_steps _ b + Reset_steps _ 0 + Translate_steps _ g
    | S _ => 3 + CopyValue_steps _ b + Translate_steps _ b + Reset_steps _ b + Reset_steps _ g
    end.

  Definition Lookup_Step_steps (H: Heap) (a: HAd) (n: nat) (g: HClos) (b: HAd) :=
    4 + Nth'_steps _ H a + MatchOption_steps + MatchPair_steps _ g + MatchNat_steps + Lookup_steps_MatchNat n g b.

  Definition Lookup_Step_T : tRel sigLookup^+ 5 :=
    fun tin k =>
      exists (H: Heap) (a n: nat) (g : HClos) (b : HAd),
        nth_error H a = Some (Some (g, b)) /\
        tin[@Fin0] ≃ H /\
        tin[@Fin1] ≃(Encode_map Encode_nat retr_nat_lookup_clos_ad ) a /\
        tin[@Fin2] ≃(Encode_map Encode_nat retr_nat_lookup_clos_var) n /\
        isRight tin[@Fin3] /\ isRight tin[@Fin4] /\
        Lookup_Step_steps H a n g b <= k.


  Lemma Lookup_Step_Terminates : projT1 Lookup_Step ↓ Lookup_Step_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Lookup_Step. repeat TM_Correct.
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
      intros tin k. cbn. intros (H&a&n&g&b&NthSome&HEncH&HEncA&HEncN&HRight3&HRight4&Hk). unfold Lookup_Step_steps in Hk.
      exists (Nth'_steps _ H a), (1 + MatchOption_steps + 1 + MatchPair_steps _ g + 1 + MatchNat_steps + Lookup_steps_MatchNat n g b).
      repeat split; try omega.
      hnf; cbn; eauto 9.
      intros tmid () (HNth&HNthInj); TMSimp. modpon HNth.
      exists (MatchOption_steps), (1 + MatchPair_steps _ g + 1 + MatchNat_steps + Lookup_steps_MatchNat n g b).
      repeat split; try omega.
      now rewrite !Nat.add_assoc.
      intros tmid0 bif (HMatchOpt&HMatchOptInj). modpon HMatchOpt. destruct bif; cbn in *; auto; modpon HMatchOpt; TMSimp.
      exists (MatchPair_steps _ g), (1 + MatchNat_steps + Lookup_steps_MatchNat n g b).
      repeat split; try omega.
      hnf; cbn. exists (g, b); repeat split; simpl_surject; eauto. contains_ext. now rewrite !Nat.add_assoc.
      intros tmid1 () (HMatchPair&HMatchPairInj); TMSimp. specialize (HMatchPair (g,b)). modpon HMatchPair. cbn in *.
      exists (MatchNat_steps), (Lookup_steps_MatchNat n g b).
      repeat split; try omega.
      intros tmid2 bif (HMatchNat&HMatchNatInj); TMSimp. modpon HMatchNat. destruct bif, n as [ | n']; auto; modpon HMatchNat; cbn.
      { (* Then of [MatchNat] *)
        exists (CopyValue_steps _ b), (1 + Translate_steps _ b + 1 + Reset_steps _ b + Reset_steps _ g).
        repeat split; try omega.
        do 1 eexists. repeat split; eauto. contains_ext. now setoid_rewrite CopyValue_steps_comp.
        intros tmid3 () (HCopyValue&HCopyValueInj); TMSimp. modpon HCopyValue.
        exists (Translate_steps _ b), (1 + Reset_steps _ b + Reset_steps _ g). repeat split; try omega.
        hnf. cbn. eauto.
        now rewrite !Nat.add_assoc.
        intros tmid4 () (HTranslate&HTranslateInj); TMSimp. modpon HTranslate.
        exists (Reset_steps _ b), (Reset_steps _ g). repeat split; try omega.
        eexists. split. eauto. now setoid_rewrite Reset_steps_comp.
        reflexivity.
        intros tmid5 () (HReset&HResetInj); TMSimp. modpon HReset.
        eexists. split. contains_ext. now setoid_rewrite Reset_steps_comp.
      }
      {
        exists (Reset_steps _ b), (1 + Reset_steps _ 0 + Translate_steps _ g). repeat split; try omega.
        exists b. repeat split; eauto. contains_ext. now setoid_rewrite Reset_steps_comp.
        intros tmid3 () (HReset&HResetInj); TMSimp. modpon HReset.
        exists (Reset_steps _ 0), (Translate_steps _ g). repeat split; try omega.
        exists 0. split; eauto. reflexivity.
        intros tmid4 () (HReset'&HResetInj'); TMSimp. modpon HReset'.
        hnf; cbn. exists g. split. contains_ext. reflexivity.
      }
    }
  Qed.
    

  Definition Lookup := WHILE Lookup_Step.

  Definition Lookup_Rel : pRel sigLookup^+ unit 5 :=
    ignoreParam (
        fun tin tout =>
          forall (H: Heap) (a n: nat) (g : HClos),
            lookup H a n = Some g ->
            tin[@Fin0] ≃ H ->
            tin[@Fin1] ≃(Encode_map Encode_nat retr_nat_lookup_clos_ad) a ->
            tin[@Fin2] ≃(Encode_map Encode_nat retr_nat_lookup_clos_var) n ->
            isRight tin[@Fin3] -> isRight tin[@Fin4] ->
            tout[@Fin0] ≃ H /\ (* [H] is saved *)
            isRight tout[@Fin1] /\ (* [a] is discarded *)
            isRight tout[@Fin2] /\ (* [n] is discarded *)
            tout[@Fin3] ≃(Encode_map Encode_HClos retr_clos_lookup) g /\ (* result *)
            isRight tout[@Fin4] (* internal tape *)
      ).


  Lemma Lookup_Realise : Lookup ⊨ Lookup_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Lookup. repeat TM_Correct.
      - apply Lookup_Step_Realise.
    }
    {
      apply WhileInduction; intros; intros heap a n g HLookup HEncHeap HEncA HEncN HRight3 HRight4; TMSimp.
      - rewrite lookup_eq in HLookup. destruct (nth_error heap a) as [ [ (g'&b) | ] | ] eqn:E; cbn in *; try congruence.
        modpon HLastStep. destruct n; auto. inv HLookup. modpon HLastStep. repeat split; auto.
      - rewrite lookup_eq in HLookup. destruct (nth_error heap a) as [ [ (g'&b) | ] | ] eqn:E; cbn in *; try congruence.
        modpon HStar. destruct n; auto. modpon HStar. modpon HLastStep. repeat split; auto.
    }
  Qed.

  Fixpoint Lookup_steps (H : Heap) (a : HAd) (n : nat) : nat :=
    match nth_error H a with
    | Some (Some (g, b)) =>
      match n with
      | 0 => Lookup_Step_steps H a n g b
      | S n' => 1 + Lookup_Step_steps H a n g b + Lookup_steps H b n'
      end
    | _ => 0 (* runtime not specified *)
    end.

  Definition Lookup_T : tRel sigLookup^+ 5 :=
    fun tin k =>
      exists (H: Heap) (a n: nat) (g : HClos),
        lookup H a n = Some g /\
        tin[@Fin0] ≃ H /\
        tin[@Fin1] ≃(Encode_map Encode_nat retr_nat_lookup_clos_ad) a /\
        tin[@Fin2] ≃(Encode_map Encode_nat retr_nat_lookup_clos_var) n /\
        isRight tin[@Fin3] /\ isRight tin[@Fin4] /\
        Lookup_steps H a n <= k.

  Lemma Lookup_Terminates : projT1 Lookup ↓ Lookup_T.
  Proof.
    unfold Lookup. repeat TM_Correct.
    { apply Lookup_Step_Realise. }
    { apply Lookup_Step_Terminates. }
    {
      intros tin k (H&a&n&g&HLookupSome&HEncH&HEncA&HEncN&HRight3&HRight4&Hk).
      rewrite lookup_eq in HLookupSome. destruct (nth_error H a) eqn:HNthSome; try congruence.
      destruct h as [ (g',b) | ]; cbn in *; try congruence.
      exists (Lookup_Step_steps H a n g' b). split.
      - hnf. do 5 eexists. repeat split; eauto.
      - intros bwhile () tmid HStep. cbn in *. modpon HStep.
        destruct bwhile, n as [ | n']; auto; modpon HStep; cbn in *.
        + eexists (Lookup_steps H b n'). split. do 4 eexists; repeat split; eauto.
          rewrite <- Hk. cbn. now rewrite HNthSome.
        + now rewrite HNthSome in Hk.
    }
  Qed.

End Lookup.