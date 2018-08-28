Require Import TM.Code.ProgrammingTools.

(** * Constructor and Deconstructor Machines for Natural Numbers *)

Section MatchNat.

  (** ** Deconstructor *)

  Definition MatchNat_Rel : Rel (tapes sigNat^+ 1) (bool * tapes sigNat^+ 1) :=
    Mk_R_p
      (fun tin '(yout, tout) =>
         forall (n : nat),
           tin ≃ n ->
           match yout, n with
           | false, O => tout ≃ 0
           | true, S n' => tout ≃ n'
           | _, _ => False
           end).

  Definition MatchNat : { M : mTM sigNat^+ 1 & states M -> bool } :=
    Move R;;
    Match (ReadChar)
          (fun o => match o with
                 | Some (inr sigNat_S) => Return (Write (inl START)) true (* S *)
                 | Some (inr sigNat_O) => Return (Move L) false (* O *)
                 | _ => Return (Nop) default (* invalid input *)
                 end).

  Definition MatchNat_steps := 5.

  Lemma MatchNat_Sem : MatchNat ⊨c(MatchNat_steps) MatchNat_Rel.
  Proof.
    unfold MatchNat_steps. eapply RealiseIn_monotone.
    { unfold MatchNat. TM_Correct. }
    { Unshelve. 4,8: reflexivity. all: omega. }
    {
      intros tin (yout&tout) H. intros n HEncN. TMSimp.
      destruct HEncN as (r1&HEncN). TMSimp.
      destruct n; cbn in *; TMSimp.
      - repeat econstructor.
      - repeat econstructor.
    }
  Qed.


  (** ** Constructors *)
  Section NatConstructor.

    Definition S_Rel : Rel (tapes sigNat^+ 1) (unit * tapes sigNat^+ 1) :=
      Mk_R_p (ignoreParam (fun tin tout => forall n : nat, tin ≃ n -> tout ≃ S n)).

    Definition Constr_S : { M : mTM sigNat^+ 1 & states M -> unit } :=
      WriteMove (inr sigNat_S) L;; Write (inl START).


    Definition Constr_S_steps := 3.

    Lemma Constr_S_Sem : Constr_S ⊨c(Constr_S_steps) S_Rel.
    Proof.
      unfold Constr_S_steps. eapply RealiseIn_monotone.
      { unfold Constr_S. TM_Correct. }
      { cbn. omega. }
      {
        intros tin (yout, tout) H. intros n HEncN.
        TMSimp. clear all except HEncN.
        destruct HEncN as (r1&->). cbn. simpl_tape.
        repeat econstructor.
      }
    Qed.


    Definition O_Rel : Rel (tapes sigNat^+ 1) (unit * tapes sigNat^+ 1) :=
      Mk_R_p (ignoreParam (fun tin tout => isRight tin -> tout ≃ O)).

    Definition Constr_O : pTM sigNat^+ unit 1 := WriteValue [ sigNat_O ].

    Goal Constr_O = WriteMove (inl STOP) L;; WriteMove (inr sigNat_O) L;; Write (inl START).
    Proof. unfold Constr_O, WriteValue, WriteString.WriteString, encode, Encode_map, map, rev, Encode_nat, encode, repeat, app. reflexivity. Qed.
    Definition Constr_O_steps := 5.

    Lemma Constr_O_Sem : Constr_O ⊨c(Constr_O_steps) O_Rel.
    Proof.
      unfold Constr_O_steps. eapply RealiseIn_monotone.
      { unfold Constr_O. TM_Correct. }
      { cbn. reflexivity. }
      { intros tin (yout, tout) H. cbn in *. auto. }
    Qed.

  End NatConstructor.

End MatchNat.


(** ** Tactical Support *)

Ltac smpl_TM_MatchNat :=
  lazymatch goal with
  | [ |- MatchNat ⊨ _ ] => eapply RealiseIn_Realise; apply MatchNat_Sem
  | [ |- MatchNat ⊨c(_) _ ] => apply MatchNat_Sem
  | [ |- projT1 (MatchNat) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply MatchNat_Sem
  | [ |- Constr_O ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_O_Sem
  | [ |- Constr_O ⊨c(_) _ ] => apply Constr_O_Sem
  | [ |- projT1 (Constr_O) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Constr_O_Sem
  | [ |- Constr_S ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_S_Sem
  | [ |- Constr_S ⊨c(_) _ ] => apply Constr_S_Sem
  | [ |- projT1 (Constr_S) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Constr_S_Sem
  end.

Smpl Add smpl_TM_MatchNat : TM_Correct.