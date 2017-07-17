Require Import Prelim TM.TM TM.Code.Code TM.Code.CodeTM.
Require Import Program.Equality.


Open Scope vector_scope.

(* Read boolean from tape 1, negate it and write it back to tape 1 *)
Section Neg_TM.

  Variable (F : finType) (def : bool_fin -> F).

  Definition neg_TM_trans :
    bool_fin * (Vector.t (option bool_fin) 1) ->
    bool_fin * (Vector.t (option bool_fin * move) 1).
  Proof.
    intros ([ | ], rd).
    - constructor. apply true. constructor. apply (None, N). constructor.
    - destruct (rd[@Fin.F1]) as [[ | ] | ].
      + (* Some true  *) constructor. apply true. constructor. apply (Some false, N). constructor.
      + (* Some false *) constructor. apply true. constructor. apply (Some true,  N). constructor.
      + (* None       *) constructor. apply true. constructor. apply (None,       N). constructor.
  Defined.

  Definition neg_TM : mTM bool_fin 0.
  Proof.
    split with (states := bool_fin).
    - apply neg_TM_trans.
    - apply false.
    - apply id.
  Defined.

  Definition neg_mTM : { M : mTM bool_fin 0 & states M -> F} := (neg_TM; def).

  Lemma neg_TM_onestep (inittapes : tapes bool_fin 1) :
    cstate (step (M := neg_TM) (initc neg_TM inittapes)) = true.
  Proof.
    unfold initc, step, neg_TM in *. cbn in *.
    dependent induction inittapes. dependent induction inittapes. cbn in *. clear IHinittapes.
    destruct (current h); cbn; auto. destruct e; cbn; auto.
  Qed.

  Lemma neg_TM_computes_sem :
    neg_mTM ⊫ computes_locally_R_p (F := F) Fin.F1 Fin.F1 _ _ negb.
  Proof.
    hnf. intros inittapes i (b, outt) HLoop. cbn in *.
    assert (i >= 1).
    {
      destruct i; cbn in *; try discriminate. cbn in *. omega.
    }
    pose proof loop_fulfills_p HLoop as H_Stop. cbn in *. destruct b; auto.
    unfold loopM in *.
    erewrite (loop_ge (k1 := 1) (k2 := i)) in HLoop. Focus 2. omega. Focus 2.
    cbn. unfold id. unfold neg_TM. cbn. rewrite neg_TM_onestep. reflexivity. inv HLoop.
    apply computes_locally_R_iff. hnf. intros x (rest1&E1).
    unfold initc, step, neg_TM in *. cbn in *.
    dependent induction inittapes. dependent induction inittapes. cbn in *. clear IHinittapes.
    hnf.
    destruct x; cbn in *;
      erewrite !tape_local_current_cons in H1; eauto; cbn in *; inv H1; cbn in *; now eauto.
  Qed.

  Lemma neg_TM_computes_terminates_in :
    neg_TM ↓ (fun _ => fun t => t = 1).
  Proof.
    hnf. intros inittape i ->. cbn. unfold id. rewrite neg_TM_onestep. eauto.
  Qed.

  Lemma neq_TM_computes_total :
    neg_mTM ⊨(1) computes_locally_R_p (F := F) Fin.F1 Fin.F1 _ _ negb.
  Proof.
    hnf. intros inittape.
    dependent induction inittape. dependent induction inittape. clear IHinittape; cbn in *.
    unfold id. rewrite neg_TM_onestep. econstructor. split. eauto.
    hnf. intros x.
    rewrite !tape_encodes_locally_iff. unfold tape_encodes_locally'. intros (tape&bl). cbn in *.
    destruct x; cbn in *; exists tape;
      cbn; unfold neg_TM, step; cbn;
        erewrite tape_local_current_cons; eauto; cbn; f_equal; eapply tape_local_right; eauto.
  Qed.
  
End Neg_TM.


(* Copy boolean from tape 1 to tape 2. *)
Section Copy.

  Variable (F : finType) (def : bool_fin -> F).

  Definition copy_TM_trans :
    bool_fin * (Vector.t (option bool_fin) 2) ->
    bool_fin * (Vector.t (option bool_fin * move) 2).
  Proof.
    intros ([ | ], rd).
    - apply (true, [| (None, N); (None, N)|]).
    - destruct (rd[@Fin.F1]) as [ | ].
      + (* Some *) apply (true, [| (None, N); (Some e, N)|]).
      + (* None *) apply (true, [| (None, N); (None, N)|]).
  Defined.

  Definition copy_TM : mTM bool_fin 1.
  Proof.
    split with (states := bool_fin).
    - apply copy_TM_trans.
    - apply false.
    - apply id.
  Defined.

  Definition copy_mTM : { M : mTM bool_fin 1 & states M -> F} := (copy_TM; def).

  Lemma copy_TM_onestep (inittapes : tapes bool_fin 2) :
    cstate (step (M := copy_TM) (initc copy_TM inittapes)) = true.
  Proof.
    unfold initc, step, neg_TM in *. cbn in *.
    dependent induction inittapes. dependent induction inittapes. cbn in *. clear IHinittapes.
    destruct (current h); cbn; auto.
  Qed.

  Lemma copy_TM_computes_sem :
    copy_mTM ⊫ computes_locally_R_p (F := F) Fin.F1 Fin.F1 _ _ id.
  Proof.
    hnf. intros inittapes i (b, outt) HLoop. cbn in *.
    assert (i >= 1).
    {
      destruct i; cbn in *; try discriminate. cbn in *. omega.
    }
    pose proof loop_fulfills_p HLoop as H_Stop. cbn in *. destruct b; auto.
    unfold loopM in *.
    erewrite (loop_ge (k1 := 1) (k2 := i)) in HLoop. Focus 2. omega. Focus 2.
    cbn. unfold id. unfold neg_TM. cbn. rewrite copy_TM_onestep. reflexivity. inv HLoop.
    apply computes_locally_R_iff. hnf. intros x (rest1&E1).
    unfold initc, step, neg_TM in *. cbn in *.
    dependent induction inittapes. dependent induction inittapes. cbn in *. clear IHinittapes.
    hnf.
    destruct x; cbn in *;
      erewrite !tape_local_current_cons in H1; eauto; cbn in *; inv H1; cbn in *; now eauto.
  Qed.

  Lemma copy_TM_computes_terminates_in :
    copy_TM ↓ (fun _ => fun t => t = 1).
  Proof.
    hnf. intros inittape i ->. cbn. unfold id. rewrite copy_TM_onestep. eauto.
  Qed.

  Lemma copy_TM_computes_total :
    copy_mTM ⊨(1) computes_locally_R_p (F := F) Fin.F1 Fin.F1 _ _ id.
  Proof.
    hnf. intros inittape.
    dependent induction inittape. dependent induction inittape. clear IHinittape; cbn in *.
    unfold id. rewrite copy_TM_onestep. econstructor. split. eauto.
    hnf. intros x.
    rewrite !tape_encodes_locally_iff. unfold tape_encodes_locally'. intros (tape&bl). cbn in *.
    destruct x; cbn in *; exists tape;
      cbn; unfold copy_TM, step; cbn;
        erewrite tape_local_current_cons; eauto; cbn; f_equal; eapply tape_local_right; eauto.
  Qed.

End Copy.


Section Dual.

  Variable (F : finType) (def : bool_fin -> F).
  Variable (f : bool * bool -> bool).

  Definition dual_TM_trans :
    bool_fin * (Vector.t (option bool_fin) 2) ->
    bool_fin * (Vector.t (option bool_fin * move) 2).
  Proof.
    intros ([ | ], rd).
    - apply (true, [| (None, N); (None, N)|]).
    - destruct (rd[@Fin.F1])          as [ b1 | ]; [ | apply (true, [| (None, N); (None, N)|])].
      destruct (rd[@(Fin.FS Fin.F1)]) as [ b2 | ]; [ | apply (true, [| (None, N); (None, N)|])].
      apply (true, [| (Some (f (b1, b2)), N); (None, N) |]).
  Defined.

  Definition dual_TM : mTM bool_fin 1.
  Proof.
    split with (states := bool_fin).
    - apply dual_TM_trans.
    - apply false.
    - apply id.
  Defined.

  Definition dual_mTM : { M : mTM bool_fin 1 & states M -> F} := (dual_TM; def).

  Lemma dual_TM_onestep (inittapes : tapes bool_fin 2) :
    cstate (step (M := dual_TM) (initc dual_TM inittapes)) = true.
  Proof.
    unfold initc, step, neg_TM in *. cbn in *.
    dependent induction inittapes. clear IHinittapes. dependent induction inittapes. clear IHinittapes. cbn in *.
    (destruct (current _); cbn; auto); (destruct (current _); cbn; auto).
  Qed.

  Lemma dual_TM_computes_sem :
    dual_mTM ⊫ computes2_locally_R_p (F := F) Fin.F1 (Fin.FS Fin.F1) Fin.F1 _ _ _ f.
  Proof.
    hnf. intros inittapes i (b, outt) HLoop. cbn in *.
    assert (i >= 1).
    {
      destruct i; cbn in *; try discriminate. cbn in *. omega.
    }
    pose proof loop_fulfills_p HLoop as H_Stop. cbn in *. destruct b; auto.
    unfold loopM in *.
    erewrite (loop_ge (k1 := 1) (k2 := i)) in HLoop. Focus 2. omega. Focus 2.
    cbn. unfold id. unfold dual_TM. cbn. rewrite dual_TM_onestep. reflexivity. inv HLoop.
    apply computes2_locally_R_iff. hnf. intros x y (rest1&E1) (rest2&E2).
    unfold initc, step, neg_TM in *. cbn in *.
    dependent induction inittapes. clear IHinittapes.
    dependent induction inittapes. clear IHinittapes.
    dependent induction inittapes. cbn in *.
    hnf.
    destruct x, y;
      (
        cbn in *;
        (erewrite tape_local_current_cons in H1; eauto);
        (erewrite tape_local_current_cons in H1; eauto);
        cbn in *; inv H1;
        unfold encode_sum, encode_unit, tape_local; cbn in *;
        destruct (f (_, _)); now (eexists; cbn; eauto)
      ).
  Qed.

  Lemma dual_TM_computes_terminates_in :
    dual_TM ↓ (fun _ => fun t => t = 1).
  Proof.
    hnf. intros inittape i ->. cbn. unfold id. rewrite dual_TM_onestep. eauto.
  Qed.

  Lemma dual_TM_computes_total :
    dual_mTM ⊨(1) computes2_locally_R_p (F := F) Fin.F1 (Fin.FS Fin.F1) Fin.F1 _ _ _ f.
  Proof.
    hnf. intros inittapes.
    dependent induction inittapes. clear IHinittapes.
    dependent induction inittapes. clear IHinittapes.
    dependent induction inittapes. cbn in *.
    unfold id. rewrite dual_TM_onestep. econstructor. split. eauto.
    hnf. intros x y.
    rewrite !tape_encodes_locally_iff. unfold tape_encodes_locally'. intros (rest1&bl1) (rest2&bl2). cbn in *.
    destruct x, y;
      (
        cbn in *; eexists;
        unfold dual_TM, step; cbn;
        (erewrite tape_local_current_cons; eauto);
        (erewrite tape_local_current_cons; eauto);
        unfold encode_sum, encode_unit, tape_local; cbn in *;
        destruct (f (_, _)); (eexists; cbn; eauto)
      ).
  Qed.
  
End Dual.