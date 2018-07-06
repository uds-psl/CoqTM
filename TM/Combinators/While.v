Require Export TM.TM.
Require Import Shared.FiniteTypes.DepPairs EqdepFacts.

Section While.

  Variable n : nat.
  Variable sig : finType.

  Variable F : finType.
  (** Parameter [None] indicates continueing, [Some f] means breaking out of the loop and terminating in the partition [f]. *)
  Variable pM : { M : mTM sig n & states M -> option F }.

  Definition While_trans :
    (TM.states (projT1 pM)) * Vector.t (option sig) n ->
    (TM.states (projT1 pM)) * Vector.t (option sig * move) n :=
    fun '(q,s) =>
      if halt q
      then match projT2 pM q with
           | Some y => (q, null_action)
           | None => (start (projT1 pM), null_action)
           end
      else trans (q,s).

  Definition While : mTM sig n :=
    Build_mTM While_trans (start (projT1 pM))
              (fun q => halt q && match projT2 pM q with
                               | Some _ => true
                               | None => false
                               end).

  Hypothesis (defF : inhabitedC F).

  Definition WHILE : pTM sig F n :=
    (While; fun q =>
              match projT2 pM q with
              | Some y => y
              | None => default
              end).

  Local Arguments loopM {_ _} _ _ _.
  Local Arguments halt {_ _} _ _.
  Local Arguments step {_ _} _ _.

  Lemma step_comp (c : mconfig sig (states (projT1 pM)) n) :
    haltConf c = false ->
    step (projT1 pM) c = step While c.
  Proof.
    intros HHalt. unfold haltConf in HHalt.
    destruct c as [q t]. cbn in *.
    cbv [step]. cbn. rewrite HHalt. reflexivity.
  Qed.

  Lemma halt_comp (c : mconfig sig (states (projT1 pM)) n) :
    haltConf (M := projT1 pM) c = false ->
    haltConf (M := While)     c = false.
  Proof.
    intros HHalt. cbn in *.
    destruct c as [q t]. cbn in *.
    apply andb_false_iff. now left.
  Qed.

  Lemma While_trans_repeat (c : mconfig sig (states While) n) :
    haltConf (M := projT1 pM) c = true ->
    projT2 pM (cstate c) = None ->
    step While c = initc (While) (ctapes c).
  Proof.
    intros HHalt HRepeat. unfold haltConf in HHalt.
    destruct c as [q t]; cbn in *.
    unfold step. cbn -[tape_move_multi] in *. rewrite HHalt, HRepeat. unfold initc. f_equal. apply tape_move_null_action.
  Qed.

  Lemma While_split k (c1 c3 : mconfig sig (states (projT1 pM)) n) :
    loopM While k c1 = Some c3 ->
    exists k1 k2 c2,
      loopM (projT1 pM) k1 c1 = Some c2 /\
      loopM While k2 c2 = Some c3 /\
      k1 + k2 <= k.
  Proof.
    unfold loopM. intros HLoop.
    apply loop_split with (h := haltConf (M := projT1 pM)) in HLoop as (k1&c2&k2&HLoop&HLoop'&Hk).
    - exists k1, k2, c2. repeat split; eauto.
      apply loop_lift with (lift := id) (f' := step (projT1 pM)) (h' := haltConf (M := projT1 pM)) in HLoop.
      + apply HLoop.
      + auto.
      + apply step_comp.
    - apply halt_comp.
  Qed.

  Lemma While_split_repeat k (c1 c2 : mconfig sig (states While) n) :
    loopM While k c1 = Some c2 ->
    haltConf (M := projT1 pM) c1 = true ->
    projT2 pM (cstate c1) = None ->
    exists k' : nat,
      k = S k' /\
      loopM While k' (initc While (ctapes c1)) = Some c2.
  Proof.
    intros HLoop HHalt HRepeat. unfold haltConf in HHalt.
    destruct k as [ | k']; cbn in *.
    - rewrite HHalt, HRepeat in HLoop. cbn in HLoop. inv HLoop.
    - rewrite HHalt, HRepeat in HLoop. cbn in HLoop. exists k'. split. reflexivity.
      now rewrite While_trans_repeat in HLoop by auto.
  Qed.

  Lemma While_split_term k (c1 c2 : mconfig sig (states While) n) (f : F) :
    loopM While k c1 = Some c2 ->
    haltConf (M := projT1 pM) c1 = true ->
    projT2 pM (cstate c1) = Some f ->
    c2 = c1.
  Proof.
    intros HLoop HHalt HTerm. unfold loopM in *.
    eapply loop_eq_0. 2: apply HLoop. unfold haltConf in *. cbn in *. now rewrite HHalt, HTerm.
  Qed.

  Lemma While_merge_repeat k1 k2 (c1 c2 c3 : mconfig sig (states While) n) :
    loopM (projT1 pM) k1 c1 = Some c2 ->
    (projT2 pM) (cstate c2) = None ->
    loopM While k2 (initc While (ctapes c2)) = Some c3 ->
    loopM While (k1+(1+k2)) c1 = Some c3.
  Proof.
    intros HLoop1 HRepeat HLoop2. unfold loopM in *.
    eapply loop_lift with (lift := id) (f' := step (While)) (h' := haltConf (M := projT1 pM)) in HLoop1; cbv [id] in *; cbn; auto; cycle 1.
    { intros. symmetry. now apply step_comp. }
    apply loop_merge with (h := haltConf (M := projT1 pM)) (c2 := c2).
    - apply halt_comp.
    - apply HLoop1.
    - cbn [loop plus]. rewrite While_trans_repeat; auto. 2: apply (loop_fulfills HLoop1).
      cbn in *. setoid_rewrite (loop_fulfills HLoop1). now rewrite HRepeat.
  Qed.

  Lemma While_merge_term k1 (c1 c2 : mconfig sig (states While) n) (f : F) :
    loopM (projT1 pM) k1 c1 = Some c2 ->
    (projT2 pM) (cstate c2) = Some f ->
    loopM While k1 c1 = Some c2.
  Proof.
    intros HLoop HTerm. unfold loopM in *.
    eapply loop_lift with (lift := id) (f' := step (While)) (h' := haltConf (M := projT1 pM)) in HLoop; cbv [id] in *; cbn; auto; cycle 1.
    { intros. symmetry. now apply step_comp. }
    unfold loopM.
    replace k1 with (k1 + 0) by omega.
    apply loop_merge with (h := haltConf (M := projT1 pM)) (c2 := c2).
    - apply halt_comp.
    - apply HLoop.
    - cbn in *. setoid_rewrite (loop_fulfills HLoop). rewrite HTerm. cbn. reflexivity.
  Qed.
  

  Variable R : pRel sig (option F) n.

  Inductive While_Rel : pRel sig F n :=
  | While_Rel''_one :
      forall tin yout tout, R tin (Some yout, tout) -> While_Rel tin (yout, tout)
  | While_Rel''_loop :
      forall tin tmid yout tout,
        R tin (None, tmid) ->
        While_Rel tmid (yout, tout) ->
        While_Rel tin (yout, tout).

  Lemma While_Realise :
    pM ⊨ R -> WHILE ⊨ While_Rel.
  Proof.
    intros HRel. hnf in HRel; hnf. intros t k; revert t. apply complete_induction with (x := k); clear k; intros k IH. intros tin c3 HLoop.
    apply While_split in HLoop as (k1&k2&c2&HLoop1&HLoop2&Hk).
    destruct (projT2 pM (cstate c2)) as [ f | ] eqn:E; cbn in *; [ clear IH | ].
    - apply While_split_term with (f := f) in HLoop2 as ->; auto. 2: apply (loop_fulfills HLoop1). rewrite E.
      constructor 1. specialize HRel with (1 := HLoop1). now rewrite E in HRel.
    - apply While_split_repeat in HLoop2 as (k2'&->&HLoop2); auto. 2: apply (loop_fulfills HLoop1).
      specialize IH with (2 := HLoop2); spec_assert IH by omega.
      econstructor 2.
      + specialize HRel with (1 := HLoop1). rewrite E in HRel. eassumption.
      + apply IH.
  Qed.


  Section While_TerminatesIn.
    Variable (T T' : Rel (tapes sig n) nat).

    Lemma While_TerminatesIn :
      pM ⊨ R ->
      projT1 pM ↓ T ->
      (forall (tin : tapes sig n) (i : nat),
          T' tin i ->
          exists i1,
            T tin i1 /\
            forall (ymid : option F) tmid,
              R tin (ymid, tmid) ->
              match ymid with
              | Some _ => i1 <= i
              | None => exists i2, T' tmid i2 /\ 1 + i1 + i2 <= i
              end) ->
      While ↓T'.
    Proof.
      intros Realise_M Term_M Hyp tin i. revert tin. apply complete_induction with (x:=i); clear i; intros i IH tin.
      intros HT1. specialize (Hyp _ _ HT1) as (i1&Ht1&HT2).
      pose proof (Term_M _ _ Ht1) as (oconf&Hloop).
      specialize (Realise_M _ _ _ Hloop).
      specialize (HT2 (projT2 pM (cstate oconf)) (ctapes oconf) Realise_M).
      destruct (projT2 pM (cstate oconf)) as [ ymid | ] eqn:E1.
      - exists oconf. eapply loop_monotone; eauto. eapply While_merge_term; eauto.
      - destruct HT2 as (i2&HT2&Hi).
        specialize (IH i2 ltac:(omega) _ HT2) as (oconf2&Hloop2).
        exists oconf2. apply loop_monotone with (k1 := i1 + (1 + i2)). 2: omega.
        eapply While_merge_repeat; eauto.
    Qed.

  End While_TerminatesIn.

End While.
(* Arguments While {n} {sig} M _. *)

Arguments WHILE : simpl never.
Arguments WHILE {n sig F} pM {defF}.


Section WhileInduction.

  Variable (sig : finType) (n : nat) (F : finType).

  Variable R1 : Rel (tapes sig n) (option F * tapes sig n).
  Variable R2 : Rel (tapes sig n) (F * tapes sig n).

  Lemma WhileInduction :
    (forall tin yout tout (HLastStep: (R1 |_(Some yout)) tin tout), R2 tin (yout, tout)) ->
    (forall tin tmid tout yout
       (HStar : (R1 |_None) tin tmid) (HLastStep : R2 tmid (yout, tout)), R2 tin (yout, tout)) ->
    While_Rel R1 <<=2 R2.
  Proof. intros H1 H2. intros tin tout. induction 1; eauto. Qed.

End WhileInduction.


(** Alternative definition of [While_Rel] *)
Section OtherWhileRel.

  Variable (sig : finType) (n : nat) (F : finType).

  Variable R : Rel (tapes sig n) (option F * tapes sig n).

  Definition While_Rel' : pRel sig F n :=
    (star (R |_ None)) ∘ ⋃_y (R |_(Some y)) ||_y.

  Goal While_Rel R =2 While_Rel'.
  Proof.
    unfold While_Rel'. split.
    {
      apply WhileInduction; intros; cbn in *.
      - eexists. split. constructor. exists yout. auto.
      - destruct HLastStep as (y&IH1&?&<-&IH2); cbn in *.
        eexists. split; eauto. econstructor; eauto.
    }
    {
      intros tin (yout, tout) H.  cbn in H. destruct H as (tmid&HStar&HLastStep).
      induction HStar as [ tin | tin tmid tmid2 HS1 HS2 IH].
      - destruct HLastStep as (?&<-&H). now constructor.
      - spec_assert IH by assumption.
        destruct HLastStep as (?&<-&H).
        econstructor 2.
        + apply HS1.
        + apply IH.
    }
  Qed.

End OtherWhileRel.