Require Import CodeTM.
Require Import Basic.Mono.
Require Import TM.Compound.WriteString.
Require Import TMTac.


Lemma WriteString_L_right (sig : Type) (str : list sig) t :
  right (WriteString_Fun L t str) = rev str ++ right t.
Proof.
  revert t. induction str; intros; cbn in *.
  - reflexivity.
  - rewrite IHstr. simpl_tape. rewrite <- app_assoc. reflexivity.
Qed.

Arguments WriteString_Fun : simpl never.

Section WriteValue.

  Variable (sig: finType) (X: Type) (cX: codable sig X).

  Definition WriteValue (x:X) : { M : mTM sig^+ 1 & states M -> unit } :=
    WriteString L (inl STOP :: rev (encode x));; Write (inl START) tt.

  Definition WriteValue_Rel (x : X) : Rel (tapes sig^+ 1) (unit * tapes sig^+ 1) :=
    Mk_R_p (ignoreParam (fun tin tout => isRight tin -> tout ≃ x)).


  Definition WriteValue_steps (x : X) := 5 + 3 * size cX x.
  
  Lemma WriteValue_Sem (x : X) :
    WriteValue x ⊨c(WriteValue_steps x) WriteValue_Rel x.
  Proof.
    unfold WriteValue_steps. eapply RealiseIn_monotone.
    { unfold WriteValue. repeat TM_Correct. eapply WriteString_Sem. }
    { cbn. rewrite rev_length, map_length. apply Nat.eq_le_incl. unfold size. omega. }
    {
      intros tin ((), tout) H. intros HRight.
      TMSimp; clear_trivial_eqs.
      repeat econstructor. f_equal. rewrite WriteString_L_right. cbn.
      rewrite <- app_assoc. rewrite rev_involutive. rewrite isRight_right; auto.
    }
  Qed.

End WriteValue.


Section Steps_comp.
  Variable (sig tau: finType) (X:Type) (cX: codable sig X).
  Variable (I : Retract sig tau).

  Lemma WriteValue_steps_comp l :
    WriteValue_steps (Encode_map cX I) l = WriteValue_steps cX l.
  Proof. unfold WriteValue_steps. now rewrite Encode_map_hasSize. Qed.

End Steps_comp.



Ltac smpl_TM_WriteValue :=
  match goal with
  | [ |- WriteValue _ _ ⊨ _ ] => eapply RealiseIn_Realise; apply WriteValue_Sem
  | [ |- WriteValue _ _ ⊨c(_) _ ] => apply WriteValue_Sem
  | [ |- projT1 (WriteValue _ _) ↓ _ ] => eapply RealiseIn_terminatesIn; apply WriteValue_Sem
  end.

Smpl Add smpl_TM_WriteValue : TM_Correct.
