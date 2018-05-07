Require Import CodeTM.
Require Import TM.Basic.Mono TM.Basic.WriteString.
Require Import TMTac.
Require Import TM.Combinators.Combinators.


(* Write a value to a tape *)
Section WriteValue.

  Section Write_String_Rev.
    Variable sig : finType.

    Definition WriteStr_Rev_Rel (str:list sig) : Rel (tapes sig 1) (unit * tapes sig 1) :=
      Mk_R_p (ignoreParam (fun tin tout => right tout = str ++ right tin)).

    (*
    Section Test.
      Let t : tape (FinType(EqType(move))) := midtape [N;N;N;N;N] N [N;N;N;N;N].
      Let str := [R;R;R;R;R;R;N].
      Compute rev str ++ right t.
      Compute right (Tape_Write_String L t str).
      Compute right (Tape_Write_String L t (str ++ [L;R])).
      Compute Tape_Write_String L t (rev str).
      Compute Tape_Write_String L (Tape_Write_String L t [L;R]) str.
      Compute Tape_Write_String L t ([L;R] ++ str).
    End Test.
     *)

    Lemma Tape_Write_String_L_cont (str str' : list sig) (t : tape sig) :
      Tape_Write_String L t (str ++ str') = Tape_Write_String L (Tape_Write_String L t str) str'.
    Proof. revert t str'. induction str; intros; cbn in *; auto. Qed.

    Lemma Tape_Write_String_L_right' (str : list sig) : forall t : tape sig,
        right (Tape_Write_String L t str) = List.rev str ++ right t.
    Proof.
      induction str; intros; cbn in *; auto.
      destruct t; cbn; simpl_list; rewrite IHstr; cbn; auto.
      destruct l; cbn; auto.
    Qed.

    Lemma Tape_Write_String_L_right (str : list sig) : forall t : tape sig,
        right (Tape_Write_String L t (List.rev str)) = str ++ right t.
    Proof. intros. rewrite <- (rev_involutive str) at 2. apply Tape_Write_String_L_right'. Qed.

    Lemma WriteStr_Rev_Sem (str:list sig) :
      Write_String L tt (List.rev str) ⊨c(4 * |str|) WriteStr_Rev_Rel str.
    Proof.
      eapply RealiseIn_monotone.
      - eapply Write_string_Sem.
      - simpl_list. omega.
      - intros tin (()&tout); TMSimp; subst. clear H0. apply Tape_Write_String_L_right.
    Qed.

  End Write_String_Rev.


  Variable sig : finType.
  Variable X : Type.
  Hypothesis codX : codeable sig X.

  Definition WriteValue_Rel (x : X) : Rel (tapes (sig^+) 1) (unit * tapes (sig^+) 1) :=
    Mk_R_p (ignoreParam (fun tin tout => isRight tin -> tout ≃ x)).


  Definition WriteValue (x : X) : { M : mTM (sig^+) 1 & states M -> unit } :=
    Write_String L tt (List.rev (inl START :: List.map inr (encode (codeable := codX) x)));;
    Move _ R tt;; Move _ R tt.


  Lemma WriteValue_Sem (x : X) (y : sig) (ys : list sig) :
    encode x = y :: ys ->
    WriteValue x ⊨c(12 + 4 * |encode x|) WriteValue_Rel x.
  Proof.
    Arguments plus : simpl never. Arguments mult : simpl never.
    intros HEncX. eapply RealiseIn_monotone.
    - eapply Seq_RealiseIn. eapply WriteStr_Rev_Sem.
      eapply Seq_RealiseIn; eapply Move_Sem.
    - cbn. simpl_list. cbn. omega.
    - intros tin (()&tout) H HRight. TMSimp; clear_trivial_eqs; subst.
      apply isRight_right in HRight. rewrite HRight in H. rewrite app_nil_r in H.
      destruct (tmid[@Fin0]); cbn in *; inv H; cbn in *.
      + hnf. repeat eexists; eauto.
      + hnf. repeat eexists; eauto.
  Qed.

End WriteValue.