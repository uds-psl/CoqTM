Require Import TM.Code.CodeTM.
Require Import TM.Basic.Mono TM.Basic.Nop TM.Basic.Multi.
Require Import TM.Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.

(* Basic pattern matching *)
Section MatchNat.

  Definition MatchNat_Rel : Rel (tapes bool^+ 1) (bool * tapes bool^+ 1) :=
    Mk_R_p
      (fun tin '(yout, tout) =>
         forall (n : nat) r1 r2,
           tin ≂[r1;r2] n ->
           match n with
           | O =>
             tout ≂[r1;r2] O /\ yout = false
           | S n' =>
             tout ≂[inl START :: r1; r2] n' /\ yout = true
           end).

  Definition MatchNat : { M : mTM bool^+ 1 & states M -> bool } :=
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
      instantiate (2 := fun o : option bool^+ =>
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
      intros tin (yout&tout) H. intros n r1 r2 HEncN. TMSimp.
      destruct HEncN as (HE1&HE2).
      destruct n; cbn in *.
      - pose proof (proj1 (midtape_tape_local_cons_left _ _ _ _) ltac:(eauto)) as L. rewrite L in H0. clear L.
        TMSimp. repeat split; auto.
      - pose proof (proj1 (midtape_tape_local_cons_left _ _ _ _) ltac:(eauto)) as L. rewrite L in H0. clear L.
        TMSimp. split; auto. split.
        + simpl_tape. auto.
        + try rewrite L. simpl_tape. cbn. apply tape_local_cons_iff in HE2 as (HE2&HE3). unfold finType_CS in *. rewrite HE3. auto.
    }
  Qed.


  (* More accurate termination time *)
  (* Note that this Lemma is not at all useful, but it shows how to show termination of the [Match] operator. *)
  Lemma MatchNat_Terminates :
    projT1 MatchNat ↓
           (fun tin k =>
              exists m, tin[@Fin0] ≂ m /\
                   match m with
                   | O => 2 <= k
                   | _ => 5 <= k
                   end).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold MatchNat. repeat TM_Correct. }
    {
      intros tin i. intros (m&HEncM&Hi).
      destruct HEncM as (r1&r2&HE1&HE2).
      destruct m eqn:Em; cbn in *.
      - pose proof (proj1 (midtape_tape_local_cons_left _ _ _ _) ltac:(eauto)) as L. TMSimp.
        exists 1, 0. repeat split.
        + omega.
        + omega.
        + TMSimp. omega.
      - pose proof (proj1 (midtape_tape_local_cons_left _ _ _ _) ltac:(eauto)) as L. TMSimp.
        exists 1, 3. repeat split.
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

    Definition S_Rel : Rel (tapes bool^+ 1) (unit * tapes bool^+ 1) :=
      Mk_R_p (ignoreParam (fun tin tout => forall n : nat, tin ≂ n -> tout ≂ S n)).

    Definition Constr_S : { M : mTM bool^+ 1 & states M -> unit } :=
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
        destruct HEncN as (r1&r2&HE1&HE2).
        destruct n as [ | n']; cbn in *.
        - pose proof (proj1 (midtape_tape_local_cons_left _ _ _ _) ltac:(eauto)) as ->.
          cbn. hnf. do 2 eexists. split.
          + cbn. reflexivity.
          + cbn. reflexivity.
        - pose proof (proj1 (midtape_tape_local_cons_left _ _ _ _) ltac:(split; eauto)) as ->.
          cbn. hnf. do 2 eexists. split.
          + cbn. reflexivity.
          + cbn. reflexivity.
      }
    Qed.

    Definition O_Rel : Rel (tapes bool^+ 1) (unit * tapes bool^+ 1) :=
      Mk_R_p (ignoreParam (fun tin tout => forall n, tin ≂ n -> tout ≂ O)).

    Definition Constr_O : { M : mTM bool^+ 1 & states M -> unit } :=
      WriteMove (Some (inl STOP), L) tt;; WriteMove (Some (inr false), L) tt;; WriteMove (Some (inl START), R) tt.


    Lemma Constr_O_Sem : Constr_O ⊨c(5) O_Rel.
    Proof.
      eapply RealiseIn_monotone.
      {
        repeat eapply Seq_RealiseIn.
        - eapply WriteMove_Sem.
        - eapply WriteMove_Sem.
        - eapply WriteMove_Sem.
      }
      { cbn. omega. }
      {
        intros tin (yout, tout). TMSimp. simpl_tape.
        destruct H0 as (r1&r2&HE1&HE2). cbn in *.
        do 2 eexists; split; cbn; eauto.
      }
    Qed.

  End NatConstructor.

End MatchNat.