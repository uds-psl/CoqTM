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


Section Write.

  Variable sig : finType.
  Variable c : sig.
  Variable (F : finType) (f : F).

  Definition Write_TM : mTM sig 1.
  Proof.
    apply Mk_Mono_TM with (states := FinType (EqType bool)).
    - intros [ | ] _.
      + (* final state *)
        apply (true, (None, N)).
      + (* write c *)
        apply (true, (Some c, N)).
    - apply false.
    - apply id.
  Defined.
  
  Definition Write := (Write_TM; fun _ => f).

  Definition Write_R :=
    Mk_R_p (F := F)
           (fun t '(y, t') => y = f /\ t' = midtape (left t) c (right t)).

  Lemma Write_Sem :
    Write ⊨c(1) Write_R.
  Proof.
    intros t. destruct_tapes. cbn in *. eauto.
  Qed.

End Write.

Arguments Write : simpl never.
Arguments Write_R { sig } c { F } p x y / : rename.



Section Move.

  Variable sig : finType.
  Variable D : TM.move.
  Variable (F : finType) (f : F).

  Definition move_trans : bool -> option sig -> bool * (option sig * move) := fun _ _ => (true, (None, D)).
  
  Definition Move_TM : mTM sig 1 :=
    Mk_Mono_TM move_trans false (fun q => q).

  Definition Move := (Move_TM; (fun x => f)).

  Definition Move_R :=
    Mk_R_p (F := F)
           (fun t '(y, t') => y = f /\ t' = tape_move (sig := sig) t D).
  
  Lemma Move_Sem :
    Move ⊨c(1) Move_R.
  Proof.
    unfold Mk_R_p, Move_R. hnf. intros tapes. destruct_tapes. cbn in *. eauto.
  Qed.

End Move.

Arguments Move : simpl never.
Arguments Move { sig } D { F } f.
Arguments Move_R { sig } ( D ) { F } ( f ) x y /.



(* write and move *)
Section WriteMove.

  Variable sig : finType.
  Variable w : sig.
  Variable D : move.
  Variable (F : finType) (f : F).

  Definition write_move_trans : bool -> option sig -> bool * (option sig * move) :=
    fun _ _ => (true, (Some w, D)).
  
  Definition WriteMove_TM : mTM sig 1 :=
    Mk_Mono_TM write_move_trans false (fun q => q).

  Definition WriteMove := (WriteMove_TM; (fun x => f)).

  Definition WriteMove_R :=
    Mk_R_p (F := F)
           (fun t '(y, t') => y = f /\ t' = tape_move (tape_write t (Some w)) D).
  
  Lemma WriteMove_Sem :
    WriteMove ⊨c(1) WriteMove_R.
  Proof.
    unfold Mk_R_p, Move_R. hnf. intros tapes. destruct_tapes. cbn in *. eauto.
  Qed.

End WriteMove.

Arguments WriteMove : simpl never.
Arguments WriteMove_R { sig } (w D) { F } p x y / : rename.


Section Read_char.

  Variable sig : finType.
  Definition rc_states : finType := FinType (EqType ((bool + sig)%type)).

  Definition read_char : mTM sig 1 :=
    Mk_Mono_TM
      (fun _ sym =>
         match sym with
         | None => (inl false, (None, TM.N))
         | Some c => (inr c, (None,TM.N))
         end)
      (inl true) (fun s => match s with inl true => false | _ => true end).

  Definition read_char_R :=
    Mk_R_p (fun (t : tape sig) '(s,t') => s = current t) ∩ ignoreParam (@IdR _).

  Definition Read_char := (read_char; fun s : rc_states => match s with inl _ => None | inr s => Some s end).

  Lemma read_char_sem :
    Read_char ⊨c(1) read_char_R.
  Proof.
    intros t. destruct_tapes. cbn. destruct (current h) eqn:E.
    - exists (mk_mconfig (inr e) [|h|]). unfold step. cbn; autounfold with tape; cbn. rewrite E. cbn. repeat (try split; auto; hnf).
    - exists (mk_mconfig (inl false) [|h|]). unfold step. cbn; autounfold with tape; cbn. rewrite E. cbn. repeat (try split; auto; hnf).
  Qed.

End Read_char.

Arguments Read_char : simpl never.
Arguments Read_char {sig}.
Arguments read_char_R sig x y /.


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
  Proof.
    intros ?. exists (initc mono_nop input). cbn. firstorder.
  Qed.

End Mono_Nop.

Arguments mono_Nop : simpl never.
Arguments mono_Nop {sig F} f.
Arguments mono_Nop_R { sig F } ( p ) x y / : rename.


Ltac smpl_TM_Mono :=
  match goal with
  | [ |- Write _ _ ⊨ _] => eapply RealiseIn_Realise; eapply Write_Sem
  | [ |- Write _ _ ⊨c(_) _] => eapply Write_Sem
  | [ |- projT1 (Write _ _) ↓ _] => eapply RealiseIn_terminatesIn; eapply Write_Sem
  | [ |- Move _ _ ⊨ _] => eapply RealiseIn_Realise; eapply Move_Sem
  | [ |- Move _ _ ⊨c(_) _] => eapply Move_Sem
  | [ |- projT1 (Move _ _) ↓ _] => eapply RealiseIn_terminatesIn; eapply Move_Sem
  | [ |- WriteMove _ _ _ ⊨ _] => eapply RealiseIn_Realise; eapply WriteMove_Sem
  | [ |- WriteMove _ _ _ ⊨c(_) _] => eapply WriteMove_Sem
  | [ |- projT1 (WriteMove _ _ _) ↓ _] => eapply RealiseIn_terminatesIn; eapply WriteMove_Sem
  | [ |- Read_char ⊨ _] => eapply RealiseIn_Realise; eapply read_char_sem
  | [ |- Read_char ⊨c(_) _] => eapply read_char_sem
  | [ |- projT1 (Read_char) ↓ _] => eapply RealiseIn_terminatesIn; eapply read_char_sem
  | [ |- mono_Nop _ ⊨ _] => eapply RealiseIn_Realise; eapply mono_Nop_Sem
  | [ |- mono_Nop _ ⊨c(_) _] => eapply mono_Nop_Sem
  | [ |- projT1 (mono_Nop _) ↓ _] => eapply RealiseIn_terminatesIn; eapply mono_Nop_Sem
  end.

Smpl Add smpl_TM_Mono : TM_Correct.