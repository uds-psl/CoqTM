Require Import TM.

Section Nop.

  Variable n : nat.
  Variable sig : finType.

  Definition null_action m := Vector.const (@None sig, N) m.

  Lemma tape_move_null_action m tapes :
    tape_move_multi tapes (null_action m) = tapes.
  Proof.
    induction tapes; cbn in *; eauto using f_equal.
  Qed.

  Definition nop_trans := fun (p : (FinType (EqType unit)) * Vector.t (option sig) n)  => let (q,a) := p in (q, null_action n).

  Definition nop : mTM sig n :=
    Build_mTM nop_trans tt (fun _ => true).

  Variable F : finType.
  Variable f : F.

  Definition Nop := (nop; fun _ => f).

  Definition Nop_Rel : Rel (tapes sig n) (F * tapes sig n) := (@IdR _) ||_ f.

  Lemma Nop_total : Nop ⊨c(0) Nop_Rel.
  Proof.
    intros ?. exists (initc nop input). cbn. firstorder.
  Qed.

  Lemma Nop_sem: Nop ⊫ Nop_Rel.
  Proof.
    intros ? ? ? ?. hnf. destruct i; cbn in *; now inv H.
  Qed.

End Nop.

Arguments null_action {_ _}.
Arguments Nop : simpl never.

Arguments Nop_Rel {n sig F} (f) x y/.

Ltac smpl_TM_Nop :=
  match goal with
  | [ |- Nop _ _ _ ⊫ _] => eapply Nop_sem
  | [ |- Nop _ _ _ ⊨c(_) _] => eapply Nop_total
  | [ |- projT1 (Nop _ _ _) ↓ _] => eapply RealiseIn_terminatesIn, Nop_total
  end.

Smpl Add smpl_TM_Nop : TM_Correct.