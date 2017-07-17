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


Section Computes2.
  Variable n_tapes : nat.
  Variable (i j k : Fin.t n_tapes).
  Variable (X Y Z : Type) (cX : codeable X) (cY : codeable Y) (cZ : codeable Z).
  Variable f : X * Y -> Z.
  Variable F : finType.

  Definition computes2_locally_R : relation (tapes bool_fin n_tapes) :=
    fun tin tout =>
      forall (x : X) (y : Y),
        tape_encodes_locally cX ( tin[@i]) x ->
        tape_encodes_locally cY ( tin[@j]) y ->
        tape_encodes_locally cZ (tout[@k]) (f (x, y)).

  Definition computes2_locally_R' : relation (tapes bool_fin n_tapes) :=
    fun tin tout =>
      forall (x : X) (y : Y),
        tape_encodes_locally' cX ( tin[@i]) x ->
        tape_encodes_locally' cY ( tin[@j]) y ->
        tape_encodes_locally' cZ (tout[@k]) (f (x, y)).

  Lemma computes2_locally_R_iff (tin tout : tapes bool_fin n_tapes) :
    computes2_locally_R tin tout <-> computes2_locally_R' tin tout.
  Proof.
    unfold computes2_locally_R, computes2_locally_R'; intuition.
    rewrite <- tape_encodes_locally_iff in *; auto.
    rewrite -> tape_encodes_locally_iff in *; auto.
  Qed.

  Definition computes2_locally_R_p : Rel (tapes bool_fin n_tapes) (F * tapes bool_fin n_tapes) :=
    ignoreParam (computes2_locally_R).

  Definition computes2_global_R : relation (tapes bool_fin n_tapes) :=
    fun tin tout =>
      forall (x : X) (y : Y),
        tape_encodes_global cX ( tin[@i]) x ->
        tape_encodes_global cY ( tin[@j]) y ->
        tape_encodes_global cZ (tout[@j]) (f (x, y)).

  Definition computes2_global_R' : relation (tapes bool_fin n_tapes) :=
    fun tin tout =>
      forall (x : X) (y : Y),
        tape_encodes_global' cX ( tin[@i]) x ->
        tape_encodes_global' cY ( tin[@j]) y ->
        tape_encodes_global' cZ (tout[@j]) (f (x, y)).

  Lemma computes2_global_R_iff (tin tout : tapes bool_fin n_tapes) :
    computes2_global_R tin tout <-> computes2_global_R' tin tout.
  Proof.
    unfold computes2_global_R, computes2_global_R'; intuition.
    rewrite <- tape_encodes_global_iff in *; auto.
    rewrite -> tape_encodes_global_iff in *; auto.
  Qed.

  Definition computes2_global_R_p : Rel (tapes bool_fin n_tapes) (F * tapes bool_fin n_tapes) :=
    ignoreParam (computes2_global_R).

End Computes2.