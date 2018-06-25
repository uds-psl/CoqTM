Require Import TM.TM.

Open Scope vector_scope.

Definition threeStates := FinType (EqType (Fin.t 3)).
Definition fourStates := FinType (EqType (Fin.t 4)).

Section Mk_Mono.
  Variable (sig states : finType).
  Variable mono_trans : states -> option sig -> states * (option sig * move).
  Variable (init : states) (fin : states -> bool).

  Definition Mk_Mono_TM : mTM sig 1.
  Proof.
    split with (states := states).
    - intros (q&tape).
      pose proof (mono_trans q (tape[@Fin.F1])) as (q', act).
      apply (q', [| act |]).
    - apply init.
    - apply fin.
  Defined.

  Variable (F : finType) (R : Rel (tape sig) (F * tape sig)).

  Definition Mk_R_p : Rel (tapes sig 1) (F * tapes sig 1) :=
      fun tps1 '(p, tps2) => R (tps1[@Fin.F1]) (p, tps2[@Fin.F1]).

End Mk_Mono.

Arguments Mk_R_p { sig F } ( R ) x y /.



Section DoAct.
  Variable sig : finType.
  Variable c : sig.

  Variable act : option sig * move.

  Variable (F : finType) (f : F).

  Definition DoAct_TM :=
    {|
      trans := fun '(q, sym) => (true, [| act |]);
      start := false;
      halt x := x;
    |}.

  Definition DoAct := (DoAct_TM; fun _ => f).

  Definition DoAct_Rel :=
    Mk_R_p (fun t '(y, t') => y = f /\ t' = tape_move_mono t act).

  Lemma DoAct_Sem : DoAct ⊨c(1) DoAct_Rel.
  Proof. intros t. destruct_tapes. cbn. unfold initc; cbn. eexists (mk_mconfig _ _); cbn; eauto. Qed.

End DoAct.

Arguments DoAct : simpl never.
Arguments DoAct_Rel { sig } act { F } f x y /.


Section Write.

  Variable sig : finType.
  Variable c : sig. (* for Write *)
  Variable (D : move). (* for Move *)
  Variable (F : finType) (f : F).

  Definition Write : pTM sig F 1 := DoAct (Some c, N) f.

  Definition Write_Rel :=
    Mk_R_p (fun t '(y, t') => y = f /\ t' = midtape (left t) c (right t)).

  Lemma Write_Sem :
    Write ⊨c(1) Write_Rel.
  Proof.
    eapply RealiseIn_monotone.
    - apply DoAct_Sem.
    - reflexivity.
    - hnf. firstorder.
  Qed.


  Definition Move : pTM sig F 1 := DoAct (None, D) f.

  Definition Move_Rel :=
    Mk_R_p (F := F)
           (fun t '(y, t') => y = f /\ t' = tape_move (sig := sig) t D).

  Lemma Move_Sem :
    Move ⊨c(1) Move_Rel.
  Proof.
    eapply RealiseIn_monotone.
    - apply DoAct_Sem.
    - reflexivity.
    - hnf. firstorder.
  Qed.

  Definition WriteMove := DoAct (Some c, D) f.

  Definition WriteMove_Rel :=
    Mk_R_p (fun t '(y, t') => y = f /\ t' = tape_move (tape_write t (Some c)) D).

  Lemma WriteMove_Sem :
    WriteMove ⊨c(1) WriteMove_Rel.
  Proof.
    eapply RealiseIn_monotone.
    - apply DoAct_Sem.
    - reflexivity.
    - hnf. firstorder.
  Qed.

End Write.

Arguments Write : simpl never.
Arguments Write_Rel { sig } c { F } p x y / : rename.

Arguments Move : simpl never.
Arguments Move { sig } D { F } f.
Arguments Move_Rel { sig } ( D ) { F } ( f ) x y /.

Arguments WriteMove : simpl never.
Arguments WriteMove_Rel { sig } (w D) { F } p x y / : rename.


Section ReadChar.

  Variable sig : finType.
  Definition rc_states : finType := FinType (EqType ((bool + sig)%type)).

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


Section Mono_Nop.

  Variable sig : finType.

  Definition mono_nop_trans : unit -> option sig -> unit * (option sig * move) :=
    fun u s => (u, (None, N)).

  Definition mono_nop : mTM sig 1 := Mk_Mono_TM mono_nop_trans tt (fun _ => true).

  Variable F : finType.
  Variable f : F.

  Definition mono_Nop := (mono_nop; fun _ => f).

  Definition mono_Nop_R := (fun (t : tapes sig 1) '(y, t') => y = f /\ t = t').

  Lemma mono_Nop_Sem: mono_Nop ⊨c(0) mono_Nop_R.
  Proof. intros t. cbn. unfold initc; cbn. eexists (mk_mconfig _ _); cbn; eauto. Qed.

End Mono_Nop.

Arguments mono_Nop : simpl never.
Arguments mono_Nop {sig F} f.
Arguments mono_Nop_R { sig F } ( p ) x y / : rename.


Ltac smpl_TM_Mono :=
  match goal with
  | [ |- DoAct _ _ ⊨ _] => eapply RealiseIn_Realise; eapply DoAct_Sem
  | [ |- DoAct _ _ ⊨c(_) _] => eapply DoAct_Sem
  | [ |- projT1 (DoAct _ _) ↓ _] => eapply RealiseIn_terminatesIn; eapply DoAct_Sem
  | [ |- Write _ _ ⊨ _] => eapply RealiseIn_Realise; eapply Write_Sem
  | [ |- Write _ _ ⊨c(_) _] => eapply Write_Sem
  | [ |- projT1 (Write _ _) ↓ _] => eapply RealiseIn_terminatesIn; eapply Write_Sem
  | [ |- Move _ _ ⊨ _] => eapply RealiseIn_Realise; eapply Move_Sem
  | [ |- Move _ _ ⊨c(_) _] => eapply Move_Sem
  | [ |- projT1 (Move _ _) ↓ _] => eapply RealiseIn_terminatesIn; eapply Move_Sem
  | [ |- WriteMove _ _ _ ⊨ _] => eapply RealiseIn_Realise; eapply WriteMove_Sem
  | [ |- WriteMove _ _ _ ⊨c(_) _] => eapply WriteMove_Sem
  | [ |- projT1 (WriteMove _ _ _) ↓ _] => eapply RealiseIn_terminatesIn; eapply WriteMove_Sem
  | [ |- ReadChar ⊨ _] => eapply RealiseIn_Realise; eapply ReadChar_Sem
  | [ |- ReadChar ⊨c(_) _] => eapply ReadChar_Sem
  | [ |- projT1 (ReadChar) ↓ _] => eapply RealiseIn_terminatesIn; eapply ReadChar_Sem
  | [ |- mono_Nop _ ⊨ _] => eapply RealiseIn_Realise; eapply mono_Nop_Sem
  | [ |- mono_Nop _ ⊨c(_) _] => eapply mono_Nop_Sem
  | [ |- projT1 (mono_Nop _) ↓ _] => eapply RealiseIn_terminatesIn; eapply mono_Nop_Sem
  end.

Smpl Add smpl_TM_Mono : TM_Correct.