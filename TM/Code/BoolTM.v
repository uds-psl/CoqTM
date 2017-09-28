Require Import TM.Prelim TM.TM TM.Code.Code TM.Code.CodeTM.
Require Import TM.Combinators.SequentialComposition TM.Basic.Mono.

Open Scope vector_scope.

(* Read boolean from tape 1, negate it and write it back to tape 1 *)
Section Neg_TM.

  Variable (F : finType) (def : bool_fin -> F).

  Definition bool_neg_TM_trans :
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

  Definition bool_neg_TM : mTM bool_fin 0.
  Proof.
    split with (states := bool_fin).
    - apply bool_neg_TM_trans.
    - apply false.
    - apply id.
  Defined.

  Definition bool_neg_mTM : { M : mTM bool_fin 0 & states M -> F} := (bool_neg_TM; def).

  Lemma bool_neg_TM_onestep (inittapes : tapes bool_fin 1) :
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

  Variable (F : finType) (def : bool_fin -> F).

  Definition bool_copy_TM_trans :
    bool_fin * (Vector.t (option bool_fin) 2) ->
    bool_fin * (Vector.t (option bool_fin * move) 2).
  Proof.
    intros ([ | ], rd).
    - apply (true, [| (None, N); (None, N)|]).
    - destruct (rd[@Fin.F1]) as [ | ].
      + (* Some *) apply (true, [| (None, N); (Some e, N)|]).
      + (* None *) apply (true, [| (None, N); (None, N)|]).
  Defined.

  Definition bool_copy_TM : mTM bool_fin 1.
  Proof.
    split with (states := bool_fin).
    - apply bool_copy_TM_trans.
    - apply false.
    - apply id.
  Defined.

  Definition bool_copy_mTM : { M : mTM bool_fin 1 & states M -> F} := (bool_copy_TM; def).

  Lemma bool_copy_TM_onestep (inittapes : tapes bool_fin 2) :
    cstate (step (M := bool_copy_TM) (initc bool_copy_TM inittapes)) = true.
  Proof.
    unfold initc, step, bool_neg_TM in *. destruct_tapes. cbn in *. destruct (current h); cbn; auto.
  Qed.

  Lemma bool_copy_TM_computes_sem :
    bool_copy_mTM ⊫
             (computes_locally_R_p (F := F) Fin.F1 (Fin.FS Fin.F1) _ _ (@id bool)) ∩
             (stay_locally_R_p (X := bool_fin) (F := F) Fin.F1 _).
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
             (stay_locally_R_p (X := bool_fin) (F := F) Fin.F1 _).
  Proof.
    hnf. intros inittapes.
    destruct_tapes; cbn in *.
    unfold id. rewrite bool_copy_TM_onestep. econstructor. split. eauto.
    eapply bool_copy_TM_computes_sem. instantiate (1 := 1). cbn. now rewrite bool_copy_TM_onestep.
  Qed.

End Copy.


Section Dual.

  Variable (F : finType) (def : bool_fin -> F).
  Variable (f : bool * bool -> bool).

  Definition bool_dual_TM_trans :
    bool_fin * (Vector.t (option bool_fin) 2) ->
    bool_fin * (Vector.t (option bool_fin * move) 2).
  Proof.
    intros ([ | ], rd).
    - apply (true, [| (None, N); (None, N)|]).
    - destruct (rd[@Fin.F1])          as [ b1 | ]; [ | apply (true, [| (None, N); (None, N)|])].
      destruct (rd[@(Fin.FS Fin.F1)]) as [ b2 | ]; [ | apply (true, [| (None, N); (None, N)|])].
      apply (true, [| (Some (f (b1, b2)), N); (None, N) |]).
  Defined.

  Definition bool_dual_TM : mTM bool_fin 1.
  Proof.
    split with (states := bool_fin).
    - apply bool_dual_TM_trans.
    - apply false.
    - apply id.
  Defined.

  Definition bool_dual_mTM : { M : mTM bool_fin 1 & states M -> F} := (bool_dual_TM; def).

  Lemma bool_dual_TM_onestep (inittapes : tapes bool_fin 2) :
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

  Variable (F : finType) (def : bool_fin -> F).

  Local Definition Move_at_1 := Inject (n := 1) (Move bool_fin R) [| Fin.F1 |] .
  Definition bool_copy_move_mTM := (bool_copy_mTM def ;; Move_at_1).


  (* TODO: Automaticate this kind of lemmas *)
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
    bool_copy_move_mTM ⊨(3) copy_Move_locally_R_p (X := bool_fin) (F := bool_fin) Fin.F1 (Fin.FS Fin.F1) _.
  Proof.
    eapply RealiseIn_monotone with (k1 := 3); try omega.
    - replace 3 with (1+1+1) by reflexivity. eapply Seq_total.
      + eapply bool_copy_TM_computes_total.
      + eapply Inject_total. apply dupfree. apply Move_Sem.
    - intros intapes (fstate, ftapes). destruct_tapes. cbn. intros ((f, fstate')&(H1&H2)&H3&H4). hnf in *. split.
      + intros x rest henc. hnf in *. cbn in *. clear H4.
        assert (tape_encodes_locally I_bool h x) as lh1 by eauto. specialize (H1 _ lh1). clear lh1. hnf in H1.
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
        assert (tape_encodes_locally I_bool h x) as L1 by eauto. specialize (H1 _ L1). clear L1. (* XXX *)
        specialize (H2 _ _ HEnc).
        assert (1 < 2 /\ ~ Vector.In 1 [|0|]) as (L1&L2) by now apply Inj_1_helper.
        specialize (H4 1 L1 L2). cbn in *. subst. eauto.
  Qed.
  
    
  (*
  Lemma bool_copy_move_TM_Sem :
    bool_copy_move_mTM ⊫ copy_Move_locally_R_p (X := bool_fin) (F := bool_fin) Fin.F1 (Fin.FS Fin.F1) _.
  Proof.
    unfold bool_copy_move_mTM, Move_at_1.
    pose proof (Move_Sem (sig := bool_fin) R).
    apply WRealise_total in H. cbn in H.
    pose proof (@Inject_sem bool_fin 0 1 bool_fin (Move bool_fin R) [| Fin.F1 |] dupfree _ H).
    pose proof (bool_copy_TM_computes_sem (F := F) (def := def)).
    pose proof (Seq_sem H1 H0).
    hnf in *. cbn in *. clear H H0 H1. intros t i outc HLoop.
    specialize (H2 t i outc HLoop). hnf in *.
    destruct H2 as ((f&midtapes)&(H1&H1')&(H2&H2')). hnf in *. cbn in *.
    destruct outc.
    destruct_tapes. cbn in *.
    unfold id in *. cbn in *.
    unfold reorder, not_indices in *. unfold Vector.map in *. cbn in *.
    unfold Match.Match_p in *. cbn in *.
    split; hnf.
    - intros x rest henc. hnf in *. cbn in *. clear h2'.
      assert (tape_encodes_locally i_bool h x) as l1 by eauto. specialize (h1 _ l1). clear l1. (* xxx *)
      destruct cstate as [state | (state & state') ]; cbn in *.
      + hnf in h2. destruct h2 as (h2&->). hnf in *. subst.
        enough (rest = nil) as -> by now apply tape_local_nil.
        unfold tape_encodes_locally_rest in h1'.
        pose proof (tape_local_nil h1) as (l1&l2).
        rewrite l2 in h1'; eauto.
        specialize (h1' x rest henc).
        eapply appendnil; eauto.
      + destruct (fin.eqb state' m_true) eqn:e1.
        * apply fin.eqb_eq in e1. subst.
          destruct h2 as (->&(b&h2)).
          specialize (h1' x rest henc). hnf in h1'.
          eapply tape_local_move_right.
          destruct x; cbn in *; eauto.
        * hnf in *. destruct h2 as (h2&h22). hnf in *. subst.
          enough (rest = nil) as -> by now apply tape_local_nil.
          pose proof (tape_local_nil h1) as (l1&l2).
          specialize (h1' x rest henc). hnf in h1'.
          rewrite l2 in h1'; auto.
          eapply appendnil; eauto.
    - intros x HEnc. cbn in *. hnf in *. destruct HEnc as (rest&HEnc).
      assert (tape_encodes_locally I_bool h x) as L1 by eauto. specialize (H1 _ L1). clear L1. (* XXX *)
      specialize (H1' _ _ HEnc).
      assert (1 < 2 /\ ~ Vector.In 1 [|0|]) as (L1&L2) by now apply Inj_1_helper.
      specialize (H2' 1 L1 L2). cbn in *. subst. eauto.
  Qed.
  *)
  
End CopyMove.