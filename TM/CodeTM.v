Require Import Prelim TM LiftNM LiftSigmaTau Code.
(* Require Import Basic.Mono Compound. *)
Require Import Combinators.If Combinators.While Combinators.SequentialComposition.
Require Import TM.Relations.

Definition bool_fin : finType := FinType (EqType bool).

Section Tape_Local.
  Variable (sig : finType).

  Definition tape_local (t : tape sig) : list sig :=
    match t with
    | niltape _ => nil
    | leftof a l => nil (* XXX *)
    | rightof _ _ => nil
    | midtape _ a l => a :: l
    end.

  Lemma tape_local_current_cons (x : sig) (xs : list sig) (t : tape sig) :
    tape_local t = x :: xs -> current t = Some x.
  Proof. destruct t eqn:E; cbn; congruence. Qed.

  Lemma tape_local_right (x : sig) (xs : list sig) (t : tape sig) :
    tape_local t = x :: xs -> right t = xs.
  Proof. destruct t eqn:E; cbn; congruence. Qed.

  Lemma tape_local_iff (t : tape sig) (xs : list sig) :
    (tape_local t = xs /\ xs <> nil) <-> (exists x xs', xs = x :: xs' /\ current t = Some x /\ right t = xs').
  Proof.
    split.
    - intros (H1&H2). destruct t eqn:E; cbn in *; try congruence. eauto.
    - intros (x&xs'&->&H1&<-). split. destruct t eqn:E; cbn in *; congruence. discriminate.
  Qed.

End Tape_Local.
    
Section Tape_Encodes.

  Variable (X : Type) (cX : codeable X).

  Definition tape_encodes_locally (t : tape bool_fin) (x : X) : Prop :=
    match decoding_output_project (decode (tape_local t)) with
    | Some (cod, rest) => x = cod
    | None => False
    end.

  Definition tape_encodes_locally' (t : tape bool_fin) (x : X) : Prop :=
    exists rest, tape_local t = encode x ++ rest.
  
  Lemma tape_encodes_locally_iff (t : tape bool_fin) (x : X) :
    tape_encodes_locally t x <-> tape_encodes_locally' t x.
  Proof.
    unfold tape_encodes_locally, decoding_output_project, tape_encodes_locally'. split.
    - intros H. destruct (decode (tape_local t)) as [(cod&Rest)| ] eqn:E; auto. subst.
      pose proof (@encode_decode _ _ (tape_local t) cod Rest E). eauto.
    - intros (rest, ->).
      pose proof (@decode_encode _ _ x rest).
      pose proof (@encode_decode _ _ (tape_local t) x) as L.
      destruct (decode (encode x ++ rest)) as [(dec,Rest)| ] eqn:E; auto.
      intuition; auto.
  Qed.
  
  Definition tape_encodes_locally_rest (t : tape bool_fin) (x_rest : X * list bool) : Prop :=
    match decoding_output_project (decode (tape_local t)) with
    | Some out => x_rest = out
    | None => False
    end.

  Definition tape_encodes_global (t : tape bool_fin) (x : X) : Prop :=
    match decoding_output_project (decode (tapeToList t)) with
    | Some (cod, rest) => x = cod
    | None => False
    end.

  Definition tape_encodes_global' (t : tape bool_fin) (x : X) : Prop :=
    exists rest, tapeToList t = encode x ++ rest.
  
  Lemma tape_encodes_global_iff (t : tape bool_fin) (x : X) :
    tape_encodes_global t x <-> tape_encodes_global' t x.
  Proof.
    unfold tape_encodes_global, decoding_output_project, tape_encodes_global'. split.
    - intros H. destruct (decode (tapeToList t)) as [(cod&Rest)| ] eqn:E; auto. subst.
      pose proof (@encode_decode _ _ (tapeToList t) cod Rest E). eauto.
    - intros (rest, ->).
      pose proof (@decode_encode _ _ x rest).
      pose proof (@encode_decode _ _ (tapeToList t) x) as L.
      destruct (decode (encode x ++ rest)) as [(dec,Rest)| ] eqn:E; auto.
      intuition; auto.
  Qed.
  
  Definition tape_encodes_global_rest (t : tape bool_fin) (x_rest : X * list bool) : Prop :=
    match decoding_output_project (decode (tapeToList t)) with
    | Some out => x_rest = out
    | None => False
    end.

End Tape_Encodes.

Section Computes.
  Variable n_tapes : nat.
  Variable (i j : Fin.t n_tapes).
  Variable (X Y : Type) (cX : codeable X) (cY : codeable Y).
  Variable f : X -> Y.
  Variable F : finType.

  Definition computes_locally_R : relation (tapes bool_fin n_tapes) :=
    fun tin tout =>
      forall (x : X),
        tape_encodes_locally _ ( tin[@i]) x ->
        tape_encodes_locally _ (tout[@j]) (f x).

  Definition computes_locally_R' : relation (tapes bool_fin n_tapes) :=
    fun tin tout =>
      forall (x : X),
        tape_encodes_locally' _ ( tin[@i]) x ->
        tape_encodes_locally' _ (tout[@j]) (f x).

  Lemma computes_locally_R_iff (tin tout : tapes bool_fin n_tapes) :
    computes_locally_R tin tout <-> computes_locally_R' tin tout.
  Proof.
    unfold computes_locally_R, computes_locally_R'; intuition.
    rewrite <- tape_encodes_locally_iff in *; auto.
    rewrite -> tape_encodes_locally_iff in *; auto.
  Qed.

  Definition computes_locally_R_p : Rel (tapes bool_fin n_tapes) (F * tapes bool_fin n_tapes) :=
    ignoreParam (computes_locally_R).

  Definition computes_global_R : relation (tapes bool_fin n_tapes) :=
    fun tin tout =>
      forall (x : X),
        tape_encodes_global _ ( tin[@i]) x ->
        tape_encodes_global _ (tout[@j]) (f x).
  
  Definition computes_global_R' : relation (tapes bool_fin n_tapes) :=
    fun tin tout =>
      forall (x : X),
        tape_encodes_global' _ ( tin[@i]) x ->
        tape_encodes_global' _ (tout[@j]) (f x).

  Lemma computes_global_R_iff (tin tout : tapes bool_fin n_tapes) :
    computes_global_R tin tout <-> computes_global_R' tin tout.
  Proof.
    unfold computes_global_R, computes_global_R'; intuition.
    rewrite <- tape_encodes_global_iff in *; auto.
    rewrite -> tape_encodes_global_iff in *; auto.
  Qed.

  Definition computes_global_R_p : Rel (tapes bool_fin n_tapes) (F * tapes bool_fin n_tapes) :=
    ignoreParam (computes_global_R).

End Computes.

Section Computes_Composes.

  Variable (X Y Z : Type) (cX : codeable X) (cY : codeable Y) (cZ : codeable Z).
  Variable (f : X -> Y) (g : Y -> Z).
  Variable (n_tapes : nat).
  Variable (i1 i2 i3 : Fin.t (S n_tapes)).
  Variable (F1 F2 : finType).
  Variable (pM : {M : mTM bool_fin n_tapes & states M -> F1}).
  Variable (pN : {N : mTM bool_fin n_tapes & states N -> F2}).

  Lemma compose_computes_sem (iin iout : Fin.t (S n_tapes)) :
    pM ⊫ computes_locally_R_p (F := F1) i1 i2 _ _ f ->
    pN ⊫ computes_locally_R_p (F := F2) i2 i3 _ _ g ->
    (pM ;; pN) ⊫ computes_locally_R_p (F := F2) i1 i3 _ _ (fun x => g (f x)).
  Proof.
    intros H1 H2.
    pose proof (SequentialComposition.Seq_sem H1 H2) as HComp.
    hnf. intros intape i outc HLoop.
    hnf. intros x Hx. cbn in outc.
    specialize (HComp intape i outc HLoop).
    unfold rcomp in HComp.
    destruct HComp as ((exectape_p&exectape)&HComp&HComp'); cbn in HComp, HComp'.
    unfold computes_locally_R in *.
    apply HComp'. apply HComp. assumption.
  Qed.

  Lemma compose_computes_total (iin iout : Fin.t (S n_tapes)) (k1 k2 : nat) :
    pM ⊨(k1) computes_locally_R_p (F := F1) i1 i2 _ _ f ->
    pN ⊨(k2) computes_locally_R_p (F := F2) i2 i3 _ _ g ->
    (pM ;; pN) ⊨(1+k1+k2) computes_locally_R_p (F := F2) i1 i3 _ _ (fun x => g (f x)).
  Proof.
    intros H1 H2.
    pose proof (SequentialComposition.Seq_total H1 H2) as HComp.
    intros intape.
    specialize (HComp intape) as (outtape&HLoop&HComp).
    unfold computes_locally_R_p in HComp. cbn in HComp.
    unfold rcomp in HComp.
    destruct HComp as ((exectape_p&exectape)&HComp&HComp'); cbn in HComp, HComp'.
    unfold computes_locally_R in *. clear exectape_p.
    exists outtape. split.
    - apply HLoop.
    - cbn. hnf. intros x Hx. apply HComp'. apply HComp. apply Hx.
  Qed.

End Computes_Composes.


Section Neg_TM.

  Variable (F : finType) (def : bool_fin -> F).

  Definition neg_TM_trans_mono :
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
    - apply neg_TM_trans_mono.
    - apply false.
    - apply id.
  Defined.

  Definition neg_mTM : { M : mTM bool_fin 0 & states M -> F}.
  Proof.
    exists neg_TM. apply def.
  Defined.

  Require Import Program.Equality.
    
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