Require Import TM.Code.CodeTM.
Require Import TM.Basic.Mono TM.Basic.Nop TM.Basic.Multi.
Require Import TM.Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.


Lemma encode_nat_correct (n : nat) :
  encode n = repeat true n ++ [false].
Proof. induction n; cbn in *; f_equal; auto. Qed.



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
    MATCH (Read_char _)
          (fun o => match o with
                 | Some (inr true)  => Write (inl START) tt;; Move _ R true  (* S *)
                 | Some (inr false) => mono_Nop _ false (* O *)
                 | _ => mono_Nop _ true (* invalid input *)
                 end).

  Lemma MatchNat_Sem : MatchNat ⊨c(5) MatchNat_Rel.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold MatchNat. eapply Match_RealiseIn. cbn. eapply read_char_sem.
      instantiate (2 := fun o : option (bool^+) =>
                          match o with Some (inr true) => _ | Some (inr false) => _ | _ => _ end).
      cbn. intros [ s | ]; cbn.
      - destruct s as [ start | s]; cbn.
        + eapply RealiseIn_monotone'. eapply mono_Nop_Sem. omega.
        + destruct s.
          * eapply Seq_RealiseIn; [eapply Write_Sem | eapply Move_Sem].
          * eapply mono_Nop_Sem.
      - eapply RealiseIn_monotone'. eapply mono_Nop_Sem. omega.
    }
    { cbn. omega. }
    {
      intros tin (yout&tout) H. intros n HEncN. TMSimp.
      destruct HEncN as (x&ys&r1&HE1&HE2).
      rewrite encode_nat_correct in HE1.
      rewrite HE2 in H0. cbn in *.
      destruct n; cbn in *; inv HE1; TMSimp; cbn.
      - repeat econstructor.
      - destruct n; cbn.
        + repeat econstructor.
        + split; auto. hnf. do 3 eexists. split. rewrite encode_nat_correct. cbn. all: eauto.
    }
  Qed.


  (* More accurate termination time *)
  (* This lemma demonstrates how to show termination of the [Match] operator, in case each case-machine has different/not constant run time. *)
  Lemma MatchNat_Terminates :
    projT1 MatchNat ↓
           (fun tin k =>
              exists m, tin[@Fin0] ≃ m /\
                   match m with
                   | O => 2 <= k
                   | _ => 5 <= k
                   end).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold MatchNat. repeat TM_Correct. }
    {
      intros tin i. intros (m&HEncM&Hi).
      destruct HEncM as (y&ys&r1&HE1&HE2).
      rewrite encode_nat_correct in HE1.
      destruct m eqn:Em; cbn in *.
      - exists 1, 0. repeat split.
        + omega.
        + omega.
        + TMSimp. omega.
      - exists 1, 3. repeat split.
        + omega.
        + omega.
        + TMSimp. exists 1, 1. repeat split.
          * omega.
          * omega.
          * TMSimp. omega.
    }
  Qed.

  
  (* Constructors *)
  Section NatConstructor.

    Definition S_Rel : Rel (tapes (bool^+) 1) (unit * tapes (bool^+) 1) :=
      Mk_R_p (ignoreParam (fun tin tout => forall n : nat, tin ≃ n -> tout ≃ S n)).

    Definition Constr_S : { M : mTM (bool^+) 1 & states M -> unit } :=
      Move _ L tt;; WriteMove (Some (inr true), L) tt;; WriteMove (Some (inl START), R) tt.

    Lemma Constr_S_Sem : Constr_S ⊨c(5) S_Rel.
    Proof.
      eapply RealiseIn_monotone.
      {
        repeat eapply Seq_RealiseIn.
        - eapply Move_Sem.
        - eapply WriteMove_Sem.
        - eapply WriteMove_Sem.
      }
      { cbn. omega. }
      {
        intros tin (yout, tout) H. intros n HEncN.
        TMSimp. clear H0 H4 H2 H3. simpl_tape.
        destruct HEncN as (y&ys&r1&HE1&HE2).
        rewrite encode_nat_correct in HE1.
        destruct n as [ | n']; cbn in *; inv HE1.
        - hnf. do 3 eexists. split.
          + rewrite encode_nat_correct. cbn. reflexivity.
          + cbn. f_equal. rewrite HE2. cbn. reflexivity.
        - hnf. do 3 eexists. split.
          + rewrite encode_nat_correct. cbn. reflexivity.
          + cbn. f_equal. rewrite HE2. cbn. reflexivity.
      }
    Qed.


    Definition O_Rel : Rel (tapes (bool^+) 1) (unit * tapes (bool^+) 1) :=
      Mk_R_p (ignoreParam (fun tin tout => isRight tin -> tout ≃ O)).


    Definition Constr_O : { M : mTM (bool^+) 1 & states M -> unit } :=
      WriteMove (Some (inr false), L) tt;;
      WriteMove (Some (inl START), R) tt.


    Lemma Constr_O_Sem : Constr_O ⊨c(3) O_Rel.
    Proof.
      eapply RealiseIn_monotone.
      { unfold Constr_O. repeat TM_Correct. }
      { cbn. omega. }
      {
        intros tin (yout, tout) H.
        intros HRight. TMSimp.
        clear H H1 H2.
        simpl_tape.
        destruct HRight as (m&ls&HRight). rewrite HRight. cbn.
        hnf. rewrite encode_nat_correct. cbn. repeat econstructor.
      }
    Qed.

  End NatConstructor.

End MatchNat.