Require Import TM.Prelim.
Require Import TM.TM.
Require Import TM.Basic.Mono.
Require Import TM.LiftMN.
Require Import TM.Combinators.SequentialComposition TM.Combinators.Match.

Require Import TM.Compound.TMTac.


(* Simple 2-tape Turing machines *)


(* Let both tapes move *)
Section MovePar.
  Variable sig : finType.
  Variable (D1 D2 : move).

  Definition MovePar_R : pRel sig unit 2 :=
    ignoreParam(fun (t t' : tapes sig 2) =>
                  t'[@Fin.F1] = tape_move t[@Fin.F1] D1 /\
                  t'[@Fin.FS Fin.F1] = tape_move t[@Fin.FS Fin.F1] D2).

  Definition MovePar : pTM sig unit 2 :=
    Inject (Move D1) [|Fin.F1|];; Inject (Move D2) [|Fin.FS Fin.F1|].

  Lemma MovePar_Sem : MovePar ⊨c(3) MovePar_R.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold MovePar.
      eapply Seq_RealiseIn; (eapply Inject_RealisesIn; [vector_dupfree | eapply Move_Sem ]).
    }
    {
      omega.
    }
    {
      hnf in *. intros tin (yout&tout) H. destruct_tapes. cbn -[Vector.nth] in *.
      TMSimp; clear_trivial_eqs. auto.
    }
  Qed.
  
End MovePar.

Arguments MovePar_R { sig } ( D1 D2 ) x y /.
Arguments MovePar {sig} (D1 D2).
Arguments MovePar : simpl never.


(* Copy the current symbol from tape 0 to tape 1 *)
Section Copy.
  Variable sig : finType.

  Variable f : sig -> sig.

  Definition CopyChar : pTM sig unit 2 :=
    MATCH (Inject ReadChar [|Fin.F1|])
          (fun s : option sig =>
             match s with
             | None =>  Nop
             | Some s => Inject (Write (f s)) [|Fin1|]
             end).

  Definition CopyChar_Rel : pRel sig unit 2 :=
    ignoreParam (
        fun tin tout =>
          tout[@Fin0] = tin[@Fin0] /\
          tout[@Fin1] = tape_write tin[@Fin1] (map_opt f (current tin[@Fin0]))
      ).

  Lemma CopyChar_Sem : CopyChar ⊨c(3) CopyChar_Rel.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold CopyChar. eapply Match_RealiseIn; cbn.
      - apply Inject_RealisesIn. vector_dupfree. apply ReadChar_Sem.
      - instantiate (2 := fun o : option sig => match o with Some s => _ | None => _ end).
        intros [ s | ]; cbn.
        + eapply Inject_RealisesIn. vector_dupfree. apply Write_Sem.
        + eapply RealiseIn_monotone'. apply Nop_Sem. omega.
    }
    { omega. }
    {
      intros tin ((), tout) H. cbn in *. TMSimp.
      destruct (current tin[@Fin0]) eqn:E; TMSimp; auto.
    }
  Qed.

End Copy.

Arguments CopyChar_Rel { sig } ( f ) x y /.
Arguments CopyChar { sig }.
Arguments CopyChar : simpl never.


(* Read a char at an arbitrary tape *)
Section ReadChar.

  Variable sig : finType.
  Variable (n : nat) (k : Fin.t n).

  Definition ReadChar_at : pTM sig (option sig) n :=
    Inject ReadChar [|k|].

  Definition ReadChar_at_Rel : pRel sig (option sig) n :=
    fun tin '(yout, tout) =>
      yout = current tin[@k] /\
      tout = tin.

  Lemma ReadChar_at_Sem :
    ReadChar_at ⊨c(1) ReadChar_at_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold ReadChar_at. repeat TM_Correct. }
    { cbn. reflexivity. }
    {
      intros tin (yout, tout) H.
      hnf. TMSimp; clear_trivial_eqs. split; auto.
      eapply VectorSpec.eq_nth_iff; intros p ? <-.
      decide (p = k) as [->|HnEq]; TMSimp; auto.
      - apply H0. vector_not_in.
    }
  Qed.

End ReadChar.

Arguments ReadChar_at : simpl never.
Arguments ReadChar_at {sig n} k.
Arguments ReadChar_at_Rel { sig n } ( k ) x y /.


Ltac smpl_TM_Multi :=
  match goal with
  | [ |- MovePar _ _ ⊨ _ ] => eapply RealiseIn_Realise; eapply MovePar_Sem
  | [ |- MovePar _ _ ⊨c(_) _ ] => eapply MovePar_Sem
  | [ |- projT1 (MovePar _ _) ↓ _ ] => eapply RealiseIn_terminatesIn; eapply MovePar_Sem
  | [ |- CopyChar _ ⊨ _ ] => eapply RealiseIn_Realise; eapply CopyChar_Sem
  | [ |- CopyChar _ ⊨c(_) _ ] => eapply CopyChar_Sem
  | [ |- projT1 (CopyChar _) ↓ _ ] => eapply RealiseIn_terminatesIn; eapply CopyChar_Sem
  | [ |- ReadChar_at _ ⊨ _ ] => eapply RealiseIn_Realise; eapply ReadChar_at_Sem
  | [ |- ReadChar_at _ ⊨c(_) _ ] => eapply ReadChar_at_Sem
  | [ |- projT1 (ReadChar_at _) ↓ _ ] => eapply RealiseIn_terminatesIn; eapply ReadChar_at_Sem
  end.

Smpl Add smpl_TM_Multi : TM_Correct.