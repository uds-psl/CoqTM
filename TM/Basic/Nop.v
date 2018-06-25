Require Import TM.

Section Nop.

  Variable n : nat.
  Variable sig : finType.

  Definition null_action := Vector.const (@None sig, N) n.

  Lemma tape_move_null_action tapes :
    tape_move_multi tapes null_action = tapes.
  Proof.
    unfold null_action, tape_move_multi.
    apply Vector.eq_nth_iff; intros ? i <-.
    erewrite Vector.nth_map2; eauto.
    rewrite Vector.const_nth.
    cbn. reflexivity.
  Qed.


  Definition Nop_TM : mTM sig n :=
    {|
      trans := fun _ => (tt, null_action);
      start := tt;
      halt := fun _ => true
    |}.

  Variable F : finType.
  Variable f : F.

  Definition Nop := (Nop_TM; fun _ => f).

  Definition Nop_Rel : pRel sig F n :=
    fun tin '(yout, tout) =>
      yout = f /\
      tout = tin.

  Definition Nop_Sem : Nop ⊨c(0) Nop_Rel.
  Proof. hnf. intros t. exists (mk_mconfig tt t). cbn. auto. Qed.
    
End Nop.

Arguments null_action {_ _}.
Arguments Nop {n sig F} f.
Arguments Nop : simpl never.

Arguments Nop_Rel {n sig F} (f) x y/.

Ltac smpl_TM_Nop :=
  match goal with
  | [ |- Nop _ ⊨ _] => eapply RealiseIn_Realise; apply Nop_Sem
  | [ |- Nop _ ⊨c(_) _] => apply Nop_Sem
  | [ |- projT1 (Nop _) ↓ _] => eapply RealiseIn_terminatesIn, Nop_Sem
  end.

Smpl Add smpl_TM_Nop : TM_Correct.