Require Import TM.Code.CodeTM.
Require Import TM.Basic.Mono TM.Basic.Nop TM.Basic.Multi.
Require Import TM.Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.



(* Basic pattern matching *)
Section MatchNat.

  Definition MatchNat_Rel : Rel (tapes (bool^+) 1) (bool * tapes (bool^+) 1) :=
    Mk_R_p
      (fun tin '(yout, tout) =>
         forall (n : nat),
           tin ≃ n ->
           match n with
           | O =>
             tout ≃ 0 /\ yout = false
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
      destruct HEncN as (r1&HEncN). TMSimp.
      destruct n; cbn in *; TMSimp.
      - repeat econstructor.
      - repeat econstructor.
    }
  Qed.


  (** ** Constructors *)
  Section NatConstructor.

    Definition S_Rel : Rel (tapes (bool^+) 1) (unit * tapes (bool^+) 1) :=
      Mk_R_p (ignoreParam (fun tin tout => forall n : nat, tin ≃ n -> tout ≃ S n)).

    Definition Constr_S : { M : mTM (bool^+) 1 & states M -> unit } :=
      WriteMove (Some (inr true), L) tt;; Write (inl START) tt.


    (*
    Lemma tape_right_move_left' (sig : finType) rs (x:sig) ls :
      right (tape_move_left' rs x ls) = x :: ls.
    Proof. destruct rs; cbn; reflexivity. Qed.

    Hint Rewrite tape_right_move_left' : tape.
    *)


    Lemma Constr_S_Sem : Constr_S ⊨c(3) S_Rel.
    Proof.
      eapply RealiseIn_monotone.
      { unfold Constr_S. repeat TM_Correct. }
      { cbn. omega. }
      {
        intros tin (yout, tout) H. intros n HEncN.
        TMSimp. clear all except HEncN.
        destruct HEncN as (r1&->). cbn. simpl_tape.
        repeat econstructor.
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