Require Import CodeTM.
Require Import Basic.Mono.
Require Import TM.Compound.WriteString.
Require Import TMTac.


Lemma WriteString_L_local (sig : Type) (str : list sig) t :
  str <> nil ->
  tape_local (WriteString_Fun L t str) = rev str ++ right t.
Proof.
  revert t. induction str as [ | s [ | s' str'] IH]; intros; cbn in *.
  - tauto.
  - reflexivity.
  - rewrite IH. 2: congruence. simpl_tape. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma tape_local_contains (sig : Type) (X : Type) (cX : codable sig X) (x : X) t :
  tape_local t = inl START :: encode x ++ [inl STOP] ->
  t ≃ x.
Proof. intros -> % midtape_tape_local_cons. repeat econstructor. Qed.


Arguments WriteString_Fun : simpl never.

Section WriteValue.

  Variable (sig: finType) (X: Type) (cX: codable sig X).

  Definition WriteValue (str : list sig) : pTM sig^+ unit 1 :=
    WriteString L (rev (inl START :: map inr str ++ [inl STOP])).

  Definition WriteValue_Rel (str : list sig) : Rel (tapes sig^+ 1) (unit * tapes sig^+ 1) :=
    Mk_R_p (ignoreParam (fun tin tout => forall (x:X), encode x = str -> isRight tin -> tout ≃ x)).

  Definition WriteValue_steps (l : nat) := 3 + 2 * l.
  
  Lemma WriteValue_Sem (str : list sig) :
    WriteValue str ⊨c(WriteValue_steps (length str)) WriteValue_Rel str.
  Proof.
    unfold WriteValue_steps. eapply RealiseIn_monotone.
    { unfold WriteValue. eapply WriteString_Sem. }
    { unfold WriteString_steps. rewrite !rev_length. cbn [length]. rewrite app_length.
      unfold size. cbn. rewrite map_length. lia. }
    {
      intros tin ((), tout) H. intros x <- HRight.
      TMSimp; clear_trivial_eqs. eapply tape_local_contains. rewrite WriteString_L_local.
      - rewrite rev_app_distr, <- !app_assoc, rev_involutive, <- !app_assoc. cbn. f_equal. f_equal. f_equal. now apply isRight_right.
      - rewrite rev_app_distr, <- !app_assoc. cbn. congruence.
    }
  Qed.

End WriteValue.


Ltac smpl_TM_WriteValue :=
  lazymatch goal with
  | [ |- WriteValue _ ⊨ _ ] => eapply RealiseIn_Realise; apply WriteValue_Sem
  | [ |- WriteValue _ ⊨c(_) _ ] => apply WriteValue_Sem
  | [ |- projT1 (WriteValue _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply WriteValue_Sem
  end.

Smpl Add smpl_TM_WriteValue : TM_Correct.
