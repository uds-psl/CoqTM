Require Import Prelim TM Code.
Require Import Combinators.SequentialComposition.
Require Import TM.Relations.

Section Tape_Local.
  Variable (sig : finType).

  Definition tape_local (t : tape sig) : list sig :=
    match t with
    | niltape _ => nil
    | leftof a l => nil
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

  Lemma tape_local_nil (t : tape sig) :
    tape_local t = nil <-> current t = None.
  Proof.
    destruct t; cbn; intuition; auto; congruence.
  Qed.

  Lemma tape_local_move_right (t : tape sig) (x : sig) (xs : list sig) :
    tape_local t = x :: xs -> tape_local (tape_move_right t) = xs.
  Proof.
    intro H. destruct t eqn:E; cbn in *; try congruence.
    inv H. destruct xs; cbn; auto.
  Qed.

End Tape_Local.

Section Tape_Encodes.

  Variable (sig : finType) (X : Type) (cX : codeable sig X).

  Definition tape_encodes_locally_rest (t : tape sig) (x : X) (rest : list sig) : Prop :=
    tape_local t = encode x ++ rest.

  Definition tape_encodes_locally (t : tape sig) (x : X) : Prop :=
    exists rest, tape_encodes_locally_rest t x rest.
  
  Definition tape_encodes_global_rest (t : tape sig) (x : X) (rest : list sig) : Prop :=
    exists rest, tapeToList t = encode x ++ rest.

  Definition tape_encodes_global (t : tape sig) (x : X) : Prop :=
    exists rest, tape_encodes_global_rest t x rest.
  
End Tape_Encodes.

Hint Unfold tape_encodes_locally tape_encodes_locally_rest tape_encodes_global tape_encodes_global_rest.

(*
(* TODO *)
(* Set X and cX as implict and maximally inserted *)
Arguments tape_encodes_locally {_} {_}.
Arguments tape_encodes_locally_rest {_} {_}.
Arguments tape_encodes_global {_} {_}.
Arguments tape_encodes_global_rest {_} {_}.
*)

Section Computes.
  Variable n_tapes : nat.
  Variable (i j : Fin.t n_tapes).
  Variable (sig : finType).
  Variable (X Y : Type) (cX : codeable sig X) (cY : codeable sig Y).
  Variable f : X -> Y.
  Variable F : finType.

  Definition computes_locally_R : relation (tapes sig n_tapes) :=
    fun tin tout =>
      forall (x : X),
        tape_encodes_locally _ ( tin[@i]) x ->
        tape_encodes_locally _ (tout[@j]) (f x).

  Definition computes_locally_R_p : Rel (tapes sig n_tapes) (F * tapes sig n_tapes) :=
    ignoreParam (computes_locally_R).

    Definition computes_global_R : relation (tapes sig n_tapes) :=
        fun tin tout =>
        forall (x : X),
            tape_encodes_global _ ( tin[@i]) x ->
            tape_encodes_global _ (tout[@j]) (f x).

    Definition computes_global_R_p : Rel (tapes sig n_tapes) (F * tapes sig n_tapes) :=
        ignoreParam (computes_global_R).

End Computes.
Hint Unfold computes_locally_R computes_locally_R computes_locally_R_p computes_global_R computes_global_R_p.

Section Computes_Composes.
  Variable sig : finType.
  Variable (X Y Z : Type) (cX : codeable sig X) (cY : codeable sig Y) (cZ : codeable sig Z).
  Variable (f : X -> Y) (g : Y -> Z).
  Variable (n_tapes : nat).
  Variable (i1 i2 i3 : Fin.t n_tapes).
  Variable (F1 F2 : finType).
  Variable (pM : {M : mTM sig n_tapes & states M -> F1}).
  Variable (pN : {N : mTM sig n_tapes & states N -> F2}).

  Lemma compose_computes_sem (iin iout : Fin.t n_tapes) :
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
  Variable (sig : finType).
  Variable (i j k : Fin.t n_tapes).
  Variable (X Y Z : Type) (cX : codeable sig X) (cY : codeable sig Y) (cZ : codeable sig Z).
  Variable f : X * Y -> Z.
  Variable F : finType.

  Definition computes2_locally_R : relation (tapes sig n_tapes) :=
    fun tin tout =>
      forall (x : X) (y : Y),
        tape_encodes_locally cX ( tin[@i]) x ->
        tape_encodes_locally cY ( tin[@j]) y ->
        tape_encodes_locally cZ (tout[@k]) (f (x, y)).

  Definition computes2_locally_R_p : Rel (tapes sig n_tapes) (F * tapes sig n_tapes) :=
    ignoreParam (computes2_locally_R).

  Definition computes2_global_R : relation (tapes sig n_tapes) :=
    fun tin tout =>
      forall (x : X) (y : Y),
        tape_encodes_global cX ( tin[@i]) x ->
        tape_encodes_global cY ( tin[@j]) y ->
        tape_encodes_global cZ (tout[@j]) (f (x, y)).

  Definition computes2_global_R_p : Rel (tapes sig n_tapes) (F * tapes sig n_tapes) :=
    ignoreParam (computes2_global_R).

End Computes2.

(* Copy the current data to the second tape and the first tape reamains locally the same (same rest). *)
Section Copy_Stay.
  Variable n_tapes : nat.
  Variable (i j : Fin.t n_tapes).
  Variable (sig : finType).
  Variable (X : Type) (cX : codeable sig X).
  Variable F : finType.

  Definition stay_locally_R1 : Rel (tape sig) (tape sig) :=
    fun tp1 tp2 =>
      forall (x : X) rest,
        tape_encodes_locally_rest cX tp1 x rest ->
        tape_encodes_locally_rest cX tp2 x rest.

  Definition stay_locally_R :=
    fun tps1 tps2 => stay_locally_R1 (tps1[@i]) (tps2[@i]).

  Definition stay_locally_R_p : Rel (tapes sig n_tapes) (F * tapes sig n_tapes) :=
    ignoreParam stay_locally_R.

  Lemma stay_locally_R_computes_id :
    stay_locally_R <<=2 computes_locally_R i i _ _ (@id X).
  Proof.
    unfold stay_locally_R, stay_locally_R1,
    computes_locally_R, tape_encodes_locally, tape_encodes_global_rest.
    firstorder.
  Qed.

End Copy_Stay.
Hint Unfold stay_locally_R1 stay_locally_R stay_locally_R stay_locally_R_p.

(* Copy the current data to the second tape and stop after the word on the first tape *)
Section Copy_Move.
  Variable n_tapes : nat.
  Variable (i j : Fin.t n_tapes).
  Variable (sig : finType).
  Variable (X : Type) (cX : codeable sig X).
  Variable F : finType.

  Definition skip_locally_R1 : Rel (tape sig) (tape sig) :=
    fun tp1 tp2 =>
      forall (x : X) rest,
        tape_encodes_locally_rest _ tp1 x rest ->
        tape_local tp2 = rest.

  Definition skip_locally_R :=
    fun tps1 tps2 => skip_locally_R1 (tps1[@i]) (tps2[@i]).

  Definition copy_Move_locally_R : Rel (tapes sig n_tapes) (tapes sig n_tapes) :=
    skip_locally_R ∩ computes_locally_R i j _ _ (@id X).

  Definition copy_Move_locally_R_p : Rel (tapes sig n_tapes) (F * tapes sig n_tapes) :=
    ignoreParam copy_Move_locally_R.

End Copy_Move.
Hint Unfold skip_locally_R skip_locally_R1 copy_Move_locally_R copy_Move_locally_R_p.