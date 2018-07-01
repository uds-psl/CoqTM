(* FIXME: TM.Basic.Nop is deprecated *)
Require Export TM.TM TM.Basic.Nop.
Require Import Shared.FiniteTypes.DepPairs EqdepFacts.

Require Import Wellfounded.

Section While.

  Variable n : nat.
  Variable sig : finType.

  Variable F : finType.
  (** Parameter [None] indicates continueing, [Some f] means breaking out of the loop and terminating in the partition [f]. *)
  Variable pM : { M : mTM sig n & states M -> option F }.

  Definition while_trans :
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
    Build_mTM while_trans (start (projT1 pM))
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


  Definition unlift_1 : mconfig sig (states While) n -> option (mconfig sig (states (projT1 pM)) n).
  Proof.
    intros s. exact (if (halt (projT1 pM) (cstate s)) then Some s else None).
  Defined.

  Lemma While_split i res c:
    loopM While i c = Some res ->
    exists i1 x1 i2,
      loopM (projT1 pM) i1 c = Some x1 /\
      loopM While i2 x1 = Some res /\ i = i1 + i2.
  Proof.
    intros.
    unfold loopM, haltConf in H.
    eapply loop_split with (p := fun c=> halt (projT1 pM) (cstate c)) in H.
    destruct H as (i1 & x1 & i2 & H1 & H2 & ->).
    - exists i1,x1,i2. split;[ |split;[exact H2|reflexivity]].
      eapply loop_lift with (lift:=id) in H1.
      + exact H1.
      + reflexivity.
      + unfold id.  intros. destruct x. unfold step. cbn in *. now rewrite H.
    - intros b. unfold halt at 2. cbn. now intros ->.
  Qed.

  Lemma While_true_split i (x : mconfig _ (states While) _) oenc :
    halt (projT1 pM) (cstate x) = true -> projT2 pM (cstate x) = None ->
    loopM While i x = Some oenc ->
    exists i', i = 1+i' /\ loopM While i' (initc While (ctapes x)) = Some oenc.
  Proof.
    intros hx px Eq.
    destruct i as [ |i'];cbn in Eq;cbn in Eq; change (states (projT1 pM)) with (states While) in Eq; rewrite hx,px in Eq;cbn in Eq; inv Eq.
    exists i'. split;[omega| ].
    destruct x. cbn in *. rewrite <- H0. unfold loopM. f_equal.
    unfold step. cbn -[tape_move_multi null_action].
    rewrite hx,px. cbn -[tape_move_multi null_action]. now rewrite tape_move_null_action.
  Qed.

  Lemma While_true_merge i1 i2 (t x1 : mconfig _ (states While) _) oenc :
    loopM (projT1 pM) i1 t = Some x1 ->
    loopM While i2 (initc While (ctapes x1)) = Some oenc ->
    (projT2 pM) (cstate x1) = None ->
    loopM While (i1+(1+i2)) t = Some oenc.
  Proof.
    intros Eq1 Eq2 px1.
    eapply loop_merge with
    (p:= fun c => halt (projT1 pM) (cstate c)) (a2:=x1).
    {unfold While. cbn. intros. now destruct halt. }
    {change (states While) with (states (projT1 pM)) in *.
     eapply loop_lift with (g:= step While) in Eq1;[exact Eq1|reflexivity| ].
     intros. unfold step,While,while_trans. cbn. unfold haltConf in H. now rewrite H.
    }
    cbn. assert (hx1:halt (projT1 pM) (cstate x1)=true) by now apply loop_fulfills_p in Eq1.
    change (states While) with (states (projT1 pM)) in *.
    rewrite hx1;cbn.
    -rewrite <- Eq2. unfold loopM. cbn. f_equal. unfold step. cbn -[tape_move_multi null_action].
     rewrite hx1,px1;cbn -[tape_move_multi null_action]. now rewrite tape_move_null_action.
  Qed.

   Lemma While_false_merge i1 (t : mconfig _ (states While) _) oenc (f : F) :
    loopM (projT1 pM) i1 t = Some oenc ->
    projT2 pM (cstate oenc) = Some f ->
    loopM While i1 t = Some oenc.
  Proof.
    intros Eq px1.
    eapply (loop_unlift (unlift := fun (x:mconfig sig (states While) n) => Some x))
      in Eq. destruct Eq as (?&H'&H1). inv H1.
    Focus 3. intros ? ? H. inv H. reflexivity.
    replace i1 with (i1+0) by omega.
    eapply (loop_merge (p:= fun c => halt (projT1 pM) (cstate c))). cbn.
    now intros ? ->. exact H'.
    apply loop_fulfills_p_0. unfold halt. cbv [haltConf]. cbn. rewrite px1.
    apply loop_fulfills_p in H'. unfold haltConf in H'. rewrite H'. auto.
    intros ? ? H ?. inv H. all: auto.
    cbn in H0. f_equal. unfold step at 2;cbn. unfold haltConf in H0. now rewrite H0.
  Qed.


  Variable R : pRel sig (option F) n.

  Definition While_Rel : pRel sig F n := star (R |_ None) ∘ (fun (t : tapes sig n) '(y,t') => R t (Some y,t')).


  Lemma While_Realise :
    pM ⊨ R -> WHILE ⊨ While_Rel.
  Proof.
    unfold While_Rel.
    intros HR t1 i1 oenc2 eq. unfold initc in eq.
    revert t1 eq; apply complete_induction with (x := i1); clear i1; intros i1 IH t1 eq.
    eapply While_split in eq as (i2&x0&i3&Eq1&Eq2&->).
    assert (halt (projT1 pM) (cstate x0) = true) as hx0.
    {
      eapply loop_fulfills_p in Eq1. unfold haltConf in Eq1. destruct halt; auto.
    }
    assert (halt While (cstate oenc2) = true) as Hoenc2.
    {
      eapply loop_fulfills_p in Eq2. destruct halt; auto.
    }
    apply andb_true_iff in Hoenc2 as (Hoenc2&Hoenc2').
    destruct (projT2 pM (cstate oenc2)) as [ f | ] eqn:Eoenc2; inv Hoenc2'.
    destruct (projT2 pM (cstate x0)) as [ fx0 | ] eqn:px0.
    - hnf. exists t1. split; [now apply starR | ]. hnf.
      unfold  loopM in Eq2. rewrite loop_fulfills_p_0 in Eq2; [ | cbn; now rewrite px0, hx0]. inv Eq2.
      apply HR in Eq1. cbn in Eq1. cbn. rewrite px0. cbn. auto. rewrite px0 in Eq1. auto.
    - eapply While_true_split in Eq2 as (i' & -> & Eq2); eauto.
      apply IH in Eq2; [ | omega]. hnf in Eq2.
      destruct Eq2 as (y&Eq2&Eq2'). hnf in Eq2, Eq2'.
      eapply use_subrel.
      rewrite <- star_rcomp_idem. rewrite rcomp_assoc. reflexivity.
      hnf. exists (ctapes x0). split.
      + apply R_in_star. apply HR in Eq1. cbn in *. rewrite px0 in Eq1. rewrite Eoenc2 in Eq2'. eauto.
      + repeat (econstructor; hnf; eauto).
  Qed.


  Section While_terminatesIn.
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
      - exists oconf. eapply loop_ge with (k1 := i1); eauto.
        eapply While_false_merge; eauto.
      - destruct HT2 as (i2&HT2&Hi).
        specialize (IH i2 ltac:(omega) _ HT2) as (oconf2&Hloop2).
        exists oconf2. apply loop_ge with (k1 := i1 + (1 + i2)). omega.
        eapply While_true_merge; eauto.
    Qed.

  End While_terminatesIn.

End While.
(* Arguments While {n} {sig} M _. *)

Arguments While_Rel {n sig F} R x y/.
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
  Proof.
    unfold While_Rel.
    intros H1 H2. intros tin (yout, tout) H.  cbn in H. destruct H as (tmid&HStar&HLastStep).
    induction HStar as [ tin | tin tmid tmid2 HS1 HS2 IH].
    - apply H1. cbn. apply HLastStep.
    - cbn in HS1. eauto.
  Qed.


End WhileInduction.


Section OtherWhileRel.

  Variable (sig : finType) (n : nat) (F : finType).

  Variable R : Rel (tapes sig n) (option F * tapes sig n).
  
  Definition While_Rel' : pRel sig F n :=
    ⋃_y ((star (R |_ None) ∘ R|_(Some y)) ||_ y).

  Goal While_Rel R =2 While_Rel'.
  Proof.
    unfold While_Rel'. split.
    - apply WhileInduction; intros; cbn in *.
      + eexists. split. reflexivity. eexists. split; eauto. constructor.
      + eexists. split. reflexivity. destruct HLastStep as (?&<-&(y&HLastStep1&HLastStep2)).
        eexists. split; eauto. econstructor; cbn; eauto.
    - intros tin (yout, tout) H. destruct H as (?&H); cbn in *. destruct H as (<-&(tmid&H&H1)).
      revert tout H1. induction H; intros.
      + eexists. split; eauto. constructor.
      + apply IHstar in H1 as (tmid&H2&H3).
        eexists. split; eauto. econstructor; cbn; eauto.
  Qed.

  Inductive While_Rel'' : pRel sig F n :=
  | While_Rel''_one :
      forall tin yout tout, R tin (Some yout, tout) -> While_Rel'' tin (yout, tout)
  | While_Rel''_loop :
      forall tin tmid yout tout,
        R tin (None, tmid) ->
        While_Rel'' tmid (yout, tout) ->
        While_Rel'' tin (yout, tout).

  Goal While_Rel R =2 While_Rel''.
  Proof.
    split.
    - apply WhileInduction; intros; cbn in *.
      + now constructor 1.
      + now econstructor 2; eauto.
    - intros tin yout H. induction H; cbn.
      + eexists. split; eauto. constructor.
      + cbn in IHWhile_Rel''. destruct IHWhile_Rel'' as (tmid'&IH1&IH2).
        eexists. split; eauto. econstructor; eauto.
  Qed.


  Check While_Rel''_ind.
  

End OtherWhileRel.