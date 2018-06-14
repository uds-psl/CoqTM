Require Import TM.Code.CodeTM.
Require Import TM.Basic.Mono TM.Basic.Nop TM.Basic.Multi.
Require Import TM.Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.



(* Basic pattern matching *)
Section MatchNat.

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
    Move R tt;;
    MATCH (Read_char)
          (fun o => match o with
                 | Some (inr sigNat_S)  => Write (inl START) true (* S *)
                 | Some (inr sigNat_O) => Move L false (* O *)
                 | _ => mono_Nop true (* invalid input *)
                 end).

  Lemma MatchNat_Sem : MatchNat ⊨c(5) MatchNat_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold MatchNat. repeat TM_Correct. }
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
      WriteMove (inr sigNat_S) L tt;; Write (inl START) tt.


    Definition Constr_S_steps := 3.

    Lemma Constr_S_Sem : Constr_S ⊨c(Constr_S_steps) S_Rel.
    Proof.
      unfold Constr_S_steps. eapply RealiseIn_monotone.
      { unfold Constr_S. repeat TM_Correct. }
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

    Definition Constr_O : { M : mTM sigNat^+ 1 & states M -> unit } :=
      WriteMove (inl STOP) L tt;;
      WriteMove (inr sigNat_O) L tt;;
      Write (inl START) tt.

    Definition Constr_O_steps := 5.

    Lemma Constr_O_Sem : Constr_O ⊨c(Constr_O_steps) O_Rel.
    Proof.
      unfold Constr_O_steps. eapply RealiseIn_monotone.
      { unfold Constr_O. repeat TM_Correct. }
      { cbn. omega. }
      {
        intros tin (yout, tout) H.
        intros HRight. destruct HRight as (r1&r2&?). TMSimp. clear_all.
        simpl_tape. repeat econstructor.
      }
    Qed.

  End NatConstructor.

End MatchNat.


Ltac smpl_TM_MatchNat :=
  match goal with
  | [ |- MatchNat ⊨ _ ] => eapply RealiseIn_Realise; apply MatchNat_Sem
  | [ |- MatchNat ⊨c(_) _ ] => apply MatchNat_Sem
  | [ |- projT1 (MatchNat) ↓ _ ] => eapply RealiseIn_terminatesIn; apply MatchNat_Sem
  | [ |- Constr_O ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_O_Sem
  | [ |- Constr_O ⊨c(_) _ ] => apply Constr_O_Sem
  | [ |- projT1 (Constr_O) ↓ _ ] => eapply RealiseIn_terminatesIn; apply Constr_O_Sem
  | [ |- Constr_S ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_S_Sem
  | [ |- Constr_S ⊨c(_) _ ] => apply Constr_S_Sem
  | [ |- projT1 (Constr_S) ↓ _ ] => eapply RealiseIn_terminatesIn; apply Constr_S_Sem
  end.

Smpl Add smpl_TM_MatchNat : TM_Correct.
