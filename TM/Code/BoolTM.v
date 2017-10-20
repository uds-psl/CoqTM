Require Import TM.Prelim TM.TM TM.Code.Code TM.Code.CodeTM.
Require Import TM.Combinators.SequentialComposition TM.Basic.Mono.

Open Scope vector_scope.

(* Read boolean from tape 1, negate it and write it back to tape 1 *)
Section Neg_TM.

  Variable (F : finType) (def : Bool_Fin -> F).

  Definition bool_neg_TM_trans :
    Bool_Fin * (Vector.t (option Bool_Fin) 1) ->
    Bool_Fin * (Vector.t (option Bool_Fin * move) 1).
  Proof.
    intros ([ | ], rd).
    - constructor. apply true. constructor. apply (None, N). constructor.
    - destruct (rd[@Fin.F1]) as [[ | ] | ].
      + (* Some true  *) constructor. apply true. constructor. apply (Some false, N). constructor.
      + (* Some false *) constructor. apply true. constructor. apply (Some true,  N). constructor.
      + (* None       *) constructor. apply true. constructor. apply (None,       N). constructor.
  Defined.

  Definition bool_neg_TM : mTM Bool_Fin 1.
  Proof.
    split with (states := Bool_Fin).
    - apply bool_neg_TM_trans.
    - apply false.
    - apply id.
  Defined.

  Definition bool_neg_mTM : { M : mTM Bool_Fin 1 & states M -> F} := (bool_neg_TM; def).

  Lemma bool_neg_TM_onestep (inittapes : tapes Bool_Fin 1) :
    cstate (step (M := bool_neg_TM) (initc bool_neg_TM inittapes)) = true.
  Proof.
    destruct_tapes.
    unfold initc, step, bool_neg_TM in *. cbn in *.
    destruct (current h); cbn; auto. destruct e; cbn; auto.
  Qed.

  Lemma bool_neg_TM_computes_sem :
    bool_neg_mTM ⊫ computes_locally_R_p (F := F) Fin.F1 Fin.F1 _ _ negb.
  Proof.
    hnf. intros inittapes i (b, outt) HLoop. cbn in *.
    assert (i >= 1).
    {
      destruct i; cbn in *; try discriminate. cbn in *. omega.
    }
    pose proof loop_fulfills_p HLoop as H_Stop. cbn in *. destruct b; auto.
    unfold loopM in *.
    erewrite (loop_ge (k1 := 1) (k2 := i)) in HLoop. Focus 2. omega. Focus 2.
    cbn. unfold id. unfold bool_neg_TM. cbn. rewrite bool_neg_TM_onestep. reflexivity. inv HLoop.
    hnf. intros x (rest1&E1).
    unfold initc, step, bool_neg_TM in *. cbn in *.
    destruct_tapes.
    hnf in *. unfold tape_encodes_locally_rest in *.
    destruct x; cbn in *;
      erewrite !tape_local_current_cons in H1; eauto; cbn in *; inv H1; cbn in *; now eauto.
  Qed.

  Lemma bool_neg_TM_computes_terminates_in :
    bool_neg_TM ↓ (fun _ => fun t => t = 1).
  Proof.
    hnf. intros inittape i ->. cbn. unfold id. rewrite bool_neg_TM_onestep. eauto.
  Qed.

  Lemma bool_neq_TM_computes_total :
    bool_neg_mTM ⊨(1) computes_locally_R_p (F := F) Fin.F1 Fin.F1 _ _ negb.
  Proof.
    hnf. intros inittape.
    destruct_tapes. cbn in *.
    rewrite bool_neg_TM_onestep. econstructor. split. cbn. eauto.
    hnf. intros x.
    unfold tape_encodes_locally, tape_encodes_locally_rest in *. intros (tape&bl). cbn in *.
    destruct x; cbn in *; exists tape;
      cbn; unfold bool_neg_TM, step; cbn;
        erewrite tape_local_current_cons; eauto; cbn; f_equal; eapply tape_local_right; eauto.
  Qed.
  
End Neg_TM.


(* Copy boolean from tape 1 to tape 2. *)
Section Copy.

  Variable (F : finType) (def : Bool_Fin -> F).

  Definition bool_copy_TM_trans :
    Bool_Fin * (Vector.t (option Bool_Fin) 2) ->
    Bool_Fin * (Vector.t (option Bool_Fin * move) 2).
  Proof.
    intros ([ | ], rd).
    - apply (true, [| (None, N); (None, N)|]).
    - destruct (rd[@Fin.F1]) as [ | ].
      + (* Some *) apply (true, [| (None, N); (Some e, N)|]).
      + (* None *) apply (true, [| (None, N); (None, N)|]).
  Defined.

  Definition bool_copy_TM : mTM Bool_Fin 2.
  Proof.
    split with (states := Bool_Fin).
    - apply bool_copy_TM_trans.
    - apply false.
    - apply id.
  Defined.

  Definition bool_copy_mTM : { M : mTM Bool_Fin 2 & states M -> F} := (bool_copy_TM; def).

  Lemma bool_copy_TM_onestep (inittapes : tapes Bool_Fin 2) :
    cstate (step (M := bool_copy_TM) (initc bool_copy_TM inittapes)) = true.
  Proof.
    unfold initc, step, bool_neg_TM in *. destruct_tapes. cbn in *. destruct (current h); cbn; auto.
  Qed.

  Lemma bool_copy_TM_computes_sem :
    bool_copy_mTM ⊫
             (computes_locally_R_p (F := F) Fin.F1 (Fin.FS Fin.F1) _ _ (@id bool)) ∩
             (stay_locally_R_p (X := Bool_Fin) (F := F) Fin.F1 _).
  Proof.
    hnf. intros inittapes i (b, outt) HLoop. cbn in *.
    assert (i >= 1).
    {
      destruct i; cbn in *; try discriminate. cbn in *. omega.
    }
    pose proof loop_fulfills_p HLoop as H_Stop. cbn in *. destruct b; auto.
    unfold loopM in *.
    erewrite (loop_ge (k1 := 1) (k2 := i)) in HLoop. Focus 2. omega. Focus 2.
    cbn. unfold id. unfold bool_neg_TM. cbn. rewrite bool_copy_TM_onestep. reflexivity. inv HLoop.
    unfold initc, step, bool_neg_TM in *. cbn in *.
    destruct_tapes.
    unfold computes_locally_R_p, computes_locally_R, tape_encodes_locally, tape_encodes_locally_rest in *.
    split; cbn.
    - hnf. intros x (rest1&E1).
      hnf.
      destruct x; cbn in *;
        (erewrite !tape_local_current_cons in H1; eauto); cbn in *; inv H1; cbn in *; now eauto.
    - hnf. intros x. intros rest1 E1. hnf in *.
      destruct x; cbn in *;
        (erewrite !tape_local_current_cons in H1; eauto); cbn in *; inv H1; cbn in *; eauto.
  Qed.

  Lemma bool_copy_TM_computes_terminates_in :
    bool_copy_TM ↓ (fun _ => fun t => t = 1).
  Proof.
    hnf. intros inittape i ->. cbn. unfold id. rewrite bool_copy_TM_onestep. eauto.
  Qed.

  Lemma bool_copy_TM_computes_total :
    bool_copy_mTM ⊨(1)
             (computes_locally_R_p (F := F) Fin.F1 (Fin.FS Fin.F1) _ _ (@id bool)) ∩
             (stay_locally_R_p (X := Bool_Fin) (F := F) Fin.F1 _).
  Proof.
    hnf. intros inittapes.
    destruct_tapes; cbn in *.
    unfold id. rewrite bool_copy_TM_onestep. econstructor. split. eauto.
    eapply bool_copy_TM_computes_sem. instantiate (1 := 1). cbn. now rewrite bool_copy_TM_onestep.
  Qed.

End Copy.


Section Dual.

  Variable (F : finType) (def : Bool_Fin -> F).
  Variable (f : bool * bool -> bool).

  Definition bool_dual_TM_trans :
    Bool_Fin * (Vector.t (option Bool_Fin) 2) ->
    Bool_Fin * (Vector.t (option Bool_Fin * move) 2).
  Proof.
    intros ([ | ], rd).
    - apply (true, [| (None, N); (None, N)|]).
    - destruct (rd[@Fin.F1])          as [ b1 | ]; [ | apply (true, [| (None, N); (None, N)|])].
      destruct (rd[@(Fin.FS Fin.F1)]) as [ b2 | ]; [ | apply (true, [| (None, N); (None, N)|])].
      apply (true, [| (Some (f (b1, b2)), N); (None, N) |]).
  Defined.

  Definition bool_dual_TM : mTM Bool_Fin 2.
  Proof.
    split with (states := Bool_Fin).
    - apply bool_dual_TM_trans.
    - apply false.
    - apply id.
  Defined.

  Definition bool_dual_mTM : { M : mTM Bool_Fin 2 & states M -> F} := (bool_dual_TM; def).

  Lemma bool_dual_TM_onestep (inittapes : tapes Bool_Fin 2) :
    cstate (step (M := bool_dual_TM) (initc bool_dual_TM inittapes)) = true.
  Proof.
    unfold initc, step, bool_dual_TM in *. destruct_tapes. cbn in *.
    (destruct (current _); cbn; auto); (destruct (current _); cbn; auto).
  Qed.

  Lemma bool_dual_TM_computes_sem :
    bool_dual_mTM ⊫
             (stay_locally_R_p (F := F) (Fin.FS Fin.F1) _) ∩
             computes2_locally_R_p (F := F) Fin.F1 (Fin.FS Fin.F1) Fin.F1 _ _ _ f.
  Proof.
    hnf. intros inittapes i (b, outt) HLoop. cbn in *.
    assert (i >= 1).
    {
      destruct i; cbn in *; try discriminate. cbn in *. omega.
    }
    pose proof loop_fulfills_p HLoop as H_Stop. cbn in *. destruct b; auto.
    unfold id, loopM in *.
    erewrite (loop_ge (k1 := 1) (k2 := i)) in HLoop. Focus 2. omega. Focus 2.
    cbn. unfold id. unfold bool_dual_TM. cbn. rewrite bool_dual_TM_onestep. reflexivity. inv HLoop.
    destruct_tapes; cbn in *.
    split; cbn; hnf.
    - intros x. intros rest1 E1. hnf in *.
      unfold initc, step, bool_neg_TM in *. cbn in *. hnf in *.
      destruct (current h), x;
        (
          unfold encode_sum, encode_unit, tape_local; cbn in *;
          repeat (erewrite tape_local_current_cons in H1; eauto);
          cbn in *; inv H1; eauto
        ).
    - hnf. intros x y (rest1&E1) (rest2&E2).
      unfold initc, step, bool_neg_TM in *. cbn in *. hnf in *.
      destruct x, y;
        (
          cbn in *;
          repeat (erewrite tape_local_current_cons in H1; eauto);
          cbn in *; inv H1;
          unfold encode_sum, encode_unit, tape_local; cbn in *;
          destruct (f (_, _)); now (eexists; cbn; eauto)
        ).
  Qed.

  Lemma bool_dual_TM_computes_terminates_in :
    bool_dual_TM ↓ (fun _ => fun t => t = 1).
  Proof.
    hnf. intros inittape i ->. cbn. unfold id. rewrite bool_dual_TM_onestep. eauto.
  Qed.

  Lemma bool_dual_TM_computes_total :
    bool_dual_mTM ⊨(1)
             (stay_locally_R_p (F := F) (Fin.FS Fin.F1) _) ∩
             computes2_locally_R_p (F := F) Fin.F1 (Fin.FS Fin.F1) Fin.F1 _ _ _ f.
  Proof.
    hnf. intros inittapes. destruct_tapes. cbn in *.
    unfold id. rewrite bool_dual_TM_onestep. econstructor. split. eauto.
    eapply bool_dual_TM_computes_sem. instantiate (1 := 1). cbn. now rewrite bool_dual_TM_onestep.
  Qed.
  
End Dual.

Require Import TM.Basic.Mono.
Require Import LiftNM.

Section CopyMove.

  Variable (F : finType) (def : Bool_Fin -> F).

  Local Definition Move_at_1 := Inject (n := 2) (Move Bool_Fin R) [| Fin.F1 |] .
  Definition bool_copy_move_mTM := (bool_copy_mTM def ;; Move_at_1).


  (* TODO: Make dupfree and In computeable *)
  Local Lemma dupfree : Injection.dupfree [| Fin.F1 (n := 1) |].
  Proof. constructor. inversion 1. constructor. Qed.

  Local Lemma Inj_1_helper : (1 < 2 /\ ~ Vector.In 1 [|0|]).
  Proof.
    split.
    - omega.
    - inversion 1; subst.
      apply EqdepFacts.eq_sigT_iff_eq_dep in H3. induction H3. inv H.
      apply EqdepFacts.eq_sigT_iff_eq_dep in H4. induction H4. destruct_vector. inv H3.
  Qed.

  Lemma bool_copy_move_TM_Sem :
    bool_copy_move_mTM ⊨(3) copy_Move_locally_R_p (X := Bool_Fin) (F := Bool_Fin) Fin.F1 (Fin.FS Fin.F1) _.
  Proof.
    eapply RealiseIn_monotone with (k1 := 3); try omega.
    - replace 3 with (1+1+1) by reflexivity. eapply Seq_total.
      + eapply bool_copy_TM_computes_total.
      + eapply Inject_total. apply dupfree. apply Move_Sem.
    - intros intapes (fstate, ftapes). destruct_tapes. cbn. intros ((f, fstate')&(H1&H2)&H3&H4). hnf in *. split.
      + intros x rest henc. hnf in *. cbn in *. clear H4.
        assert (tape_encodes_locally Encode_Bool h x) as lh1 by (eexists; apply henc).
        specialize (H1 _ lh1). clear lh1. hnf in H1.
        destruct fstate; cbn in *.
        * destruct H3 as (->&H3).
          destruct x; cbn in henc.
          -- erewrite tape_local_move_right; eauto. specialize (H2 true rest henc).  hnf in H2. cbn in H2. eauto.
          -- erewrite tape_local_move_right; eauto. specialize (H2 false rest henc). hnf in H2. cbn in H2. eauto.
        * hnf in H3. destruct H3 as (H3&<-).
          destruct x; cbn in henc.
          -- specialize (H2 true rest henc).  hnf in H2. cbn in H2. clear henc. exfalso.
             enough (current fstate'[@Fin.F1] = Some true) by congruence.
             eapply tape_local_current_cons; eauto.
          -- specialize (H2 false rest henc). hnf in H2. cbn in H2. clear henc. exfalso.
             enough (current fstate'[@Fin.F1] = Some false) by congruence.
             eapply tape_local_current_cons; eauto.
      + intros x HEnc. cbn in *. hnf in *. destruct HEnc as (rest&HEnc).
        assert (tape_encodes_locally _ h x) as L1 by eauto. specialize (H1 _ L1). clear L1. (* XXX *)
        specialize (H2 _ _ HEnc).
        assert (1 < 2 /\ ~ Vector.In 1 [|0|]) as (L1&L2) by now apply Inj_1_helper.
        specialize (H4 1 L1 L2). cbn in *. subst. eauto.
  Qed.
  
End CopyMove.