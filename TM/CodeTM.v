Require Import Prelim TM LiftNM LiftSigmaTau Code.
(* Require Import Basic.Mono Compound. *)
Require Import Combinators.If Combinators.While.
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
  Proof. destruct t eqn:E; cbn; try congruence. Qed.

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
      forall (x : X) (y : Y),
        tape_encodes_locally _ ( tin[@i]) x ->
        tape_encodes_locally _ (tout[@j]) y ->
        f x = y.

  Definition computes_locally_R' : relation (tapes bool_fin n_tapes) :=
    fun tin tout =>
      forall (x : X) (y : Y),
        tape_encodes_locally' _ ( tin[@i]) x ->
        tape_encodes_locally' _ (tout[@j]) y ->
        f x = y.

  Lemma computes_locally_R_iff (tin tout : tapes bool_fin n_tapes) :
    computes_locally_R tin tout <-> computes_locally_R' tin tout.
  Proof. unfold computes_locally_R, computes_locally_R'; intuition; apply H; now rewrite tape_encodes_locally_iff in *. Qed.

  Definition computes_locally_R_p : Rel (tapes bool_fin n_tapes) (F * tapes bool_fin n_tapes) :=
    ignoreParam (computes_locally_R).

  Definition computes_global_R : relation (tapes bool_fin n_tapes) :=
    fun tin tout =>
      forall (x : X) (y : Y),
        tape_encodes_global _ ( tin[@i]) x ->
        tape_encodes_global _ (tout[@j]) y ->
        f x = y.
  
  Definition computes_global_R' : relation (tapes bool_fin n_tapes) :=
    fun tin tout =>
      forall (x : X) (y : Y),
        tape_encodes_global' _ ( tin[@i]) x ->
        tape_encodes_global' _ (tout[@j]) y ->
        f x = y.

  Lemma computes_global_R_iff (tin tout : tapes bool_fin n_tapes) :
    computes_global_R tin tout <-> computes_global_R' tin tout.
  Proof. unfold computes_global_R, computes_global_R'; intuition; apply H; now rewrite tape_encodes_global_iff in *. Qed.

  Definition computes_global_R_p : Rel (tapes bool_fin n_tapes) (F * tapes bool_fin n_tapes) :=
    ignoreParam (computes_global_R).

End Computes.


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
    apply computes_locally_R_iff. hnf. intros x y (rest1&E1) (rest2&E2).
    unfold initc, step, neg_TM in *. cbn in *.
    dependent induction inittapes. dependent induction inittapes. cbn in *. clear IHinittapes.
    dependent induction outt. dependent induction outt. cbn in *. clear IHoutt.
    destruct x, y; cbn in *;
      erewrite !tape_local_current_cons in H1; eauto; cbn in *; inv H1; cbn in *; congruence.
  Qed.

  Lemma neg_TM_computes_terminates_in :
    neg_TM ↓ (fun _ => fun t => t = 1).
  Proof.
    hnf. intros inittape i ->. cbn. unfold id. rewrite neg_TM_onestep. eauto.
  Qed.
  
End Neg_TM.