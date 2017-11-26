(* This file is a case-study.  All machines here are instances of UnaryFinTM or DualFinTM. *)

Require Import TM.Code.CodeTM TM.Code.FinTM.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Combinators.SequentialComposition.
Require Import TM.Code.ChangeAlphabet.

(* First we derive ID and NOT and AND from FinTM *)
Section ID.
  (* Note that Nop does this as well *)
  Definition ID := UnaryFinTM (@id bool).

  Lemma ID_Computes :
    ID ⊨c(3) Computes_Rel Fin.F1 Fin.F1 _ _ (@id bool).
  Proof.
    eapply RealiseIn_monotone.
    - eapply UnaryFinTM_Computes.
    - omega.
    - intros tin (yout&tout) H. auto.
  Qed.
End ID.

Section NOT.
  (* Note that Nop does this as well *)
  Definition NOT := UnaryFinTM (negb).

  Lemma NOT_Computes :
    NOT ⊨c(3) Computes_Rel Fin.F1 Fin.F1 _ _ (negb).
  Proof.
    eapply RealiseIn_monotone.
    - eapply UnaryFinTM_Computes.
    - omega.
    - intros tin (yout&tout) H. auto.
  Qed.
End NOT.

Section AND.
  Definition AND := DualFinTM andb.

  Lemma AND_Computes :
    AND ⊨c(5)
        Computes_Rel Fin.F1 Fin.F1 _ _ (@id bool) ∩
        Computes2_Rel (F := FinType (EqType unit)) Fin.F1 (Fin.FS Fin.F1) (Fin.FS Fin.F1) _ _ _  andb.
  Proof.
    eapply RealiseIn_monotone.
    - eapply DualFinTM_Computes.
    - omega.
    - intros tin (yout&tout) H. auto.
  Qed.
End AND.


(* Now we use the Sigma-Tau-Lift, we can build another version of ID *)
Section ID'.

  (* First we define the retract between [ bool ] and [ bool ], by using the involution [ negb ] *)
  Let retr : TRetract bool bool.
  Proof.
    econstructor. eapply inversion_retract. eapply inverse_involutive. eapply negb_involutive.
  Defined.

  (* We have to give a default value, even if the retract is an inversion *)
  Definition ID' := ChangeAlphabet (@TRetr_inv _ _ retr) false ID.

  (*
  Compute (@TRetr_f _ _ retr true).
  Compute (@TRetr_f _ _ retr false).
  Compute (@TRetr_g _ _ retr true).
  Compute (@TRetr_g _ _ retr false).
   *)

  Lemma ID'_Computes :
    ID' ⊨c(3) Computes_Rel Fin.F1 Fin.F1 _ _ (@id bool).
  Proof.
    eapply RealiseIn_monotone.
    - unfold ID'.
      apply (ChangeAlphabet_Computes_RealiseIn (@TRetr_inv _ _ retr) false (@id bool)); cbn; eauto.
      eapply ID_Computes.
    - omega.
    - intros tin (yout&tout) H. hnf in *. intros x HEnc. specialize (H (negb x)).
      unfold id in H.
      spec_assert H.
      {
        cbn. destruct x; cbn; cbv [ Encode_Map ]; hnf; cbn; eauto.
      }
      destruct x; cbn in H; cbv [ Encode_Map ] in H; hnf in *;
        (destruct H as (r1&r2&H1&H2); exists r1, r2; hnf in H1, H2; cbn in H1, H2; hnf; split; cbn; auto).
  Qed.
  
End ID'.


(* Because [ negb ] is involutive, we can concatinate to [ NOT ] machines and get another [ ID ] machine. *)
Section NOT_NOT.

  Definition NOT_NOT := NOT ;; NOT.

  Lemma NOT_NOT_Computes :
    NOT_NOT ⊨c(7) Computes_Rel Fin.F1 Fin.F1 _ _ (@id bool).
  Proof.
    eapply RealiseIn_monotone.
    - eapply (compose_computes_RealiseIn (f := negb) (g := negb)). apply Fin.F1. apply Fin.F1. 1-2: eapply NOT_Computes.
    - cbn. omega.
    - hnf. intros tin (yout&tout) H. hnf in *. intros x Cx. specialize (H x Cx). now rewrite negb_involutive in H. 
  Qed.
  
End NOT_NOT.


(* Using [ NOT ], [ AND ], and the DeMorgan law, we construct an [ OR ] machine. *)
Section DeMorgan.

  (* We use this equality *)
  Lemma deMorgan (b1 b2 : bool) :
    orb b1 b2 = negb (andb (negb b1) (negb b2)).
  Proof. destruct b1, b2; cbn; reflexivity. Qed.

  (* First we run [ NOT ] on tape 1 and 2. *)
  Definition NOT2 := UnaryParallelTM negb negb.

  Lemma NOT2_Computes :
    NOT2 ⊨c(7)
         Computes_Rel (F := FinType (EqType unit)) (Fin.F1       ) (Fin.F1       ) _ _ negb ∩
         Computes_Rel (F := FinType (EqType unit)) (Fin.FS Fin.F1) (Fin.FS Fin.F1) _ _ negb.
  Proof.
    eapply RealiseIn_monotone.
    - eapply UnaryParallelTM_Computes.
    - cbn. omega.
    - hnf. auto.
  Qed.
        
  (* Then we run [ AND ]. The result will be stored on tape 2.
   * After that we run [ NOT ] on this tape. *)
  Definition OR :=
    NOT2 ;; AND ;; Inject NOT [|Fin.FS Fin.F1|].

  Lemma OR_Computes :
    OR ⊨c(17) Computes2_Rel (F := FinType (EqType unit)) Fin.F1 (Fin.FS Fin.F1) (Fin.FS Fin.F1) _ _ _ orb.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold OR. eapply Seq_RealiseIn; [ | eapply Seq_RealiseIn].
      - apply NOT2_Computes.
      - apply AND_Computes.
      - apply Inject_RealisesIn. vector_dupfree. apply NOT_Computes.
    }
    {
      cbn. omega.
    }
    {
      hnf. intros tin (yout&tout) H1. hnf in *.
      destruct H1 as ((()&t1)&(H1&H2)&(()&t2)&(H3&H4)&H5&H6); hnf in *. intros x y HE1 HE2. destruct_tapes.
      specialize (H6 Fin.F1 ltac:(vector_not_in)). subst. cbn in *.
      specialize (H1 x HE1). specialize (H2 y HE2). subst. rewrite deMorgan. auto.
    }
  Qed.
  
End DeMorgan.

(* Finally, we employ commutativity of [ andb ].  We swap the tapes 1 and 2 using the M-N-Lift. *)
Section AndComm.

  Definition AND' := Inject AND [| Fin.FS Fin.F1 (n := 1); Fin.F1 |].

  Lemma AND'_Computes :
    AND' ⊨c(5)
         Computes_Rel (Fin.FS Fin.F1) (Fin.FS Fin.F1) _ _ (@id bool) ∩
         Computes2_Rel (F := FinType (EqType unit)) Fin.F1 (Fin.FS Fin.F1) Fin.F1 _ _ _  andb.
  Proof.
    eapply RealiseIn_monotone.
    - unfold AND'. eapply Inject_RealisesIn. vector_dupfree. eapply AND_Computes.
    - omega.
    - intros tin (yout&tout) H; hnf in *.
      destruct H as ((H1&H2)&_); hnf in *. destruct_tapes; cbn in *. split; cbn in *.
      + intros x HE1. cbn in *. eapply H1. auto.
      + intros x y HE1 HE2. specialize (H1 y HE2). specialize (H2 _ _ HE2 HE1). rewrite andb_comm. auto.
  Qed.

End AndComm.