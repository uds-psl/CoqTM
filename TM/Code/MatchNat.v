Require Import TM.Code.CodeTM.
Require Import TM.Basic.Mono TM.Basic.Nop TM.Basic.Multi.
Require Import TM.Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.


Lemma encode_nat_correct (n : nat) :
  encode n = repeat true n ++ [false].
Proof. induction n; cbn in *; f_equal; auto. Qed.

Local Arguments Encode_Nat : simpl never.



(* Basic pattern matching *)
Section MatchNat.

  Definition MatchNat_Rel : Rel (tapes (bool^+) 1) (bool * tapes (bool^+) 1) :=
    Mk_R_p
      (fun tin '(yout, tout) =>
         forall (n : nat),
           tin ≃ n ->
           match n with
           | O =>
             tout ≃ O /\ yout = false
           | S n' =>
             tout ≃ n' /\ yout = true
           end).

  Definition MatchNat : { M : mTM (bool^+) 1 & states M -> bool } :=
    Move _ R tt;;
    MATCH (Read_char _)
          (fun o => match o with
                 | Some (inr true)  => Write (inl START) true (* S *)
                 | Some (inr false) => Move _ L false (* O *)
                 | _ => mono_Nop _ true (* invalid input *)
                 end).

  Lemma MatchNat_Sem : MatchNat ⊨c(5) MatchNat_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold MatchNat. repeat TM_Correct. }
    { Unshelve. 4,6: reflexivity. all: omega. }
    {
      intros tin (yout&tout) H. intros n HEncN. TMSimp.
      destruct HEncN as (r1&HEncN). rewrite encode_nat_correct in HEncN. TMSimp.
      destruct n; cbn in *; TMSimp.
      - repeat econstructor.
      - repeat econstructor. now rewrite encode_nat_correct.
    }
  Qed.


  (** ** Constructors *)
  Section NatConstructor.

    Definition S_Rel : Rel (tapes (bool^+) 1) (unit * tapes (bool^+) 1) :=
      Mk_R_p (ignoreParam (fun tin tout => forall n : nat, tin ≃ n -> tout ≃ S n)).

    Definition Constr_S : { M : mTM (bool^+) 1 & states M -> unit } :=
      WriteMove (Some (inr true), L) tt;; Write (inl START) tt.


    Lemma Constr_S_Sem : Constr_S ⊨c(3) S_Rel.
    Proof.
      eapply RealiseIn_monotone.
      { unfold Constr_S. repeat TM_Correct. }
      { cbn. omega. }
      {
        intros tin (yout, tout) H. intros n HEncN.
        TMSimp. clear all except HEncN. simpl_tape.
        destruct HEncN as (r1&->). rewrite encode_nat_correct. cbn.
        repeat econstructor. now rewrite encode_nat_correct.
      }
    Qed.


    Definition O_Rel : Rel (tapes (bool^+) 1) (unit * tapes (bool^+) 1) :=
      Mk_R_p (ignoreParam (fun tin tout => isRight tin -> tout ≃ O)).


    Definition Constr_O : { M : mTM (bool^+) 1 & states M -> unit } :=
        WriteMove (Some (inl STOP), L) tt;;
        WriteMove (Some (inr false), L) tt;;
        Write (inl START) tt.

    Lemma Constr_O_Sem : Constr_O ⊨c(5) O_Rel.
    Proof.
      eapply RealiseIn_monotone.
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