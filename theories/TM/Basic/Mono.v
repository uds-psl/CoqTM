Require Import TM.TM.

(** * Basic 1-Tape Machines *)


(** ** Helper functions *)
Section Mk_Mono.
  Variable (sig states : finType).
  Variable mono_trans : states -> option sig -> states * (option sig * move).
  Variable (init : states) (fin : states -> bool).

  Definition Mk_Mono_TM : mTM sig 1.
  Proof.
    split with (states := states).
    - intros (q&tape).
      pose proof (mono_trans q (tape[@Fin0])) as (q', act).
      apply (q', [| act |]).
    - apply init.
    - apply fin.
  Defined.

  Variable (F : finType) (R : Rel (tape sig) (F * tape sig)).

  Definition Mk_R_p : Rel (tapes sig 1) (F * tapes sig 1) :=
      fun tps1 '(p, tps2) => R (tps1[@Fin0]) (p, tps2[@Fin0]).

End Mk_Mono.

Arguments Mk_R_p { sig F } ( R ) x y /.



(** ** Do a single action *)
Section DoAct.
  Variable sig : finType.
  Variable c : sig.

  Variable act : option sig * move.

  Definition DoAct_TM :=
    {|
      trans := fun '(q, sym) => (true, [| act |]);
      start := false;
      halt x := x;
    |}.

  Definition DoAct : pTM sig unit 1 := (DoAct_TM; fun _ => tt).

  Definition DoAct_Rel : pRel sig unit 1 :=
    Mk_R_p (ignoreParam (fun t t' => t' = doAct t act)).

  Lemma DoAct_Sem : DoAct ⊨c(1) DoAct_Rel.
  Proof. intros t. destruct_tapes. cbn. unfold initc; cbn. eexists (mk_mconfig _ _); cbn; eauto. Qed.

End DoAct.

Arguments DoAct : simpl never.
Arguments DoAct_Rel { sig } act x y /.


(** *** Derived Machines *)

Section DoAct_Derived.
  Variable sig : finType.
  Variable c : sig. (* for Write *)
  Variable (D : move). (* for Move *)

  Definition Write : pTM sig unit 1 := DoAct (Some c, N).

  Definition Write_Rel : pRel sig unit 1 :=
    Mk_R_p (ignoreParam (fun t t' => t' = midtape (left t) c (right t))).

  Lemma Write_Sem :
    Write ⊨c(1) Write_Rel.
  Proof.
    eapply RealiseIn_monotone.
    - apply DoAct_Sem.
    - reflexivity.
    - hnf. firstorder.
  Qed.

  Definition Move : pTM sig unit 1 := DoAct (None, D).

  Definition Move_Rel : pRel sig unit 1 :=
    Mk_R_p (ignoreParam (fun t t' => t' = tape_move (sig := sig) t D)).

  Lemma Move_Sem :
    Move ⊨c(1) Move_Rel.
  Proof.
    eapply RealiseIn_monotone.
    - apply DoAct_Sem.
    - reflexivity.
    - hnf. firstorder.
  Qed.

  Definition WriteMove : pTM sig unit 1 := DoAct (Some c, D).

  Definition WriteMove_Rel : pRel sig unit 1 :=
    Mk_R_p (ignoreParam (fun t t' => t' = tape_move (tape_write t (Some c)) D)).

  Lemma WriteMove_Sem :
    WriteMove ⊨c(1) WriteMove_Rel.
  Proof.
    eapply RealiseIn_monotone.
    - apply DoAct_Sem.
    - reflexivity.
    - hnf. firstorder.
  Qed.

End DoAct_Derived.

Arguments Write : simpl never.
Arguments Write_Rel { sig } c x y / : rename.

Arguments Move : simpl never.
Arguments Move { sig } D.
Arguments Move_Rel { sig } ( D ) x y /.

Arguments WriteMove : simpl never.
Arguments WriteMove_Rel { sig } (w D) x y / : rename.


(** ** Read a symbol *)

Section ReadChar.

  Variable sig : finType.

  Definition ReadChar_TM : mTM sig 1 :=
    {|
      trans := fun '(_, sym) =>
                 match sym[@Fin0] with
                 | None => (inl true, [|(None, N)|])
                 | Some c => (inr c, [|(None, N)|])
                 end;
      start := inl false;
      halt := fun s => match s with
                    | inl b => b
                    | inr _ => true
                    end;
    |}.

  Definition ReadChar := (ReadChar_TM; fun s => match s with inl _ => None | inr s => Some s end).

  Definition ReadChar_Rel : pRel sig (option sig) 1 :=
    fun t '(y, t') =>
      y = current t[@Fin0] /\
      t' = t.

  Definition ReadChar_Sem : ReadChar ⊨c(1) ReadChar_Rel.
  Proof.
    intros t. destruct_tapes. cbn. unfold initc; cbn. cbv [step]; cbn. unfold current_chars; cbn.
    destruct (current h) eqn:E.
    - eexists (mk_mconfig _ _); cbv [step]; cbn. split; eauto.
    - eexists (mk_mconfig _ _); cbv [step]; cbn. split; eauto.
  Qed.

End ReadChar.

Arguments ReadChar : simpl never.
Arguments ReadChar {sig}.
Arguments ReadChar_Rel sig x y /.


(** ** Tactic Support *)

Ltac smpl_TM_Mono :=
  lazymatch goal with
  | [ |- DoAct _ ⊨ _] => eapply RealiseIn_Realise; eapply DoAct_Sem
  | [ |- DoAct _ ⊨c(_) _] => eapply DoAct_Sem
  | [ |- projT1 (DoAct _) ↓ _] => eapply RealiseIn_TerminatesIn; eapply DoAct_Sem
  | [ |- Write _ ⊨ _] => eapply RealiseIn_Realise; eapply Write_Sem
  | [ |- Write _ ⊨c(_) _] => eapply Write_Sem
  | [ |- projT1 (Write _) ↓ _] => eapply RealiseIn_TerminatesIn; eapply Write_Sem
  | [ |- Move _ ⊨ _] => eapply RealiseIn_Realise; eapply Move_Sem
  | [ |- Move _ ⊨c(_) _] => eapply Move_Sem
  | [ |- projT1 (Move _) ↓ _] => eapply RealiseIn_TerminatesIn; eapply Move_Sem
  | [ |- WriteMove _ _ ⊨ _] => eapply RealiseIn_Realise; eapply WriteMove_Sem
  | [ |- WriteMove _ _ ⊨c(_) _] => eapply WriteMove_Sem
  | [ |- projT1 (WriteMove _ _) ↓ _] => eapply RealiseIn_TerminatesIn; eapply WriteMove_Sem
  | [ |- ReadChar ⊨ _] => eapply RealiseIn_Realise; eapply ReadChar_Sem
  | [ |- ReadChar ⊨c(_) _] => eapply ReadChar_Sem
  | [ |- projT1 (ReadChar) ↓ _] => eapply RealiseIn_TerminatesIn; eapply ReadChar_Sem
  end.

Smpl Add smpl_TM_Mono : TM_Correct.