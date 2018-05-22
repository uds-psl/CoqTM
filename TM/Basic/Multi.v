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
  Variable (F : finType) (def : F).

  Definition MovePar_R : Rel (tapes sig 2) (F * tapes sig 2) :=
    (fun (t t' : tapes sig 2) => t'[@Fin.F1] = tape_move t[@Fin.F1] D1 /\
                              t'[@Fin.FS Fin.F1] = tape_move t[@Fin.FS Fin.F1] D2) ||_ def.

  Definition MovePar : { M : mTM sig 2 & states M -> F} :=
    Inject (Move _ D1 tt) [|Fin.F1|];; Inject (Move _ D2 def) [|Fin.FS Fin.F1|].

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
      hnf in *. intros tin (yout&tout). destruct_tapes. cbn -[Vector.nth] in *.
      intros ((()&t1)&((_&H1)&H2)&(H3&H4)&H5); hnf in *; subst; split; auto; destruct_tapes.
      specialize (H5 Fin.F1 ltac:(vector_not_in)); cbn in H5; subst. cbn in H1, H4; subst.
      specialize (H2 (Fin.FS Fin.F1) ltac:(vector_not_in)); cbn in H2; subst. auto.
    }
  Qed.
  
End MovePar.

Arguments MovePar_R { sig } ( D1 D2 ) { F } ( def ) x y /.
Arguments MovePar : simpl never.


(* Copy the current symbol from tape 0 to tape 1 *)
Section Copy.
  Variable sig : finType.

  Variable f : sig -> sig.

  Definition Copy_char : { M : mTM sig 2 & states M -> bool} :=
    MATCH (Inject (Read_char sig) [|Fin.F1|])
          (fun s : option sig =>
             match s with
               None =>  Nop _ _ false
             | Some s => Inject (Write (f s) true) [|Fin.FS Fin.F1|]
             end).

  Definition Copy_char_R :=
    (if? (fun t t' : tapes sig 2 =>
            exists c, current t[@Fin.F1] = Some c /\
                 t'[@Fin.FS Fin.F1] = tape_write t[@Fin.FS Fin.F1] (Some (f c)) /\
                 t[@Fin.F1] = t'[@Fin.F1])
         ! (fun t t' => current t[@Fin.F1] = None) ∩ (@IdR _)).

  Lemma Copy_char_Sem : Copy_char ⊨c(3) Copy_char_R.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold Copy_char. eapply Match_RealiseIn. cbn.
      eapply Inject_RealisesIn; [ vector_dupfree| eapply read_char_sem].
      instantiate (2 := fun o : option sig => match o with Some s => _ | None => _ end).
      intros [ s | ]; cbn.
      eapply Inject_RealisesIn; [ vector_dupfree| eapply Write_Sem].
      eapply RealiseIn_monotone'. eapply Nop_total. omega.
    }
    {
      cbn. omega.
    }
    {
      hnf. intros tin (yout&tout). intros (o&t&((H1&H2)&H3)&H4); hnf in *; subst.
      cbn in H2. destruct_tapes. cbn -[Vector.nth] in *. cbn in H2. inv H2. cbn in H4.
      specialize (H3 (Fin.FS Fin.F1) ltac:(vector_not_in)); cbn in H3; subst.
      destruct h; cbn [current] in *.
      - destruct H4 as (H4&H5); hnf in *; subst. inv H5. now cbv.
      - destruct H4 as (H4&H5); hnf in *; subst. inv H5. now cbv.
      - destruct H4 as (H4&H5); hnf in *; subst. inv H5. now cbv.
      - destruct H4 as ((H4&H5)&H6); hnf in *; subst. cbn in H5; subst.
        specialize (H6 Fin.F1 ltac:(vector_not_in)); cbn in H6; subst. cbn. eauto.
    }
  Qed.

End Copy.

Arguments Copy_char_R { sig } ( f ) x y /.
Arguments Copy_char : simpl never.


(* Read a char at an arbitrary tape *)
Section ReadChar.

  Variable sig : finType.
  Variable (n : nat) (k : Fin.t n).

  Definition ReadChar_multi : { M : mTM sig n & states M -> option sig} :=
    Inject (Read_char _) [|k|].

  Definition ReadChar_multi_R  : Rel (tapes sig n) (option sig * tapes sig n) :=
    (fun (t : tapes sig n) '(s,t') => s = current t[@k]) ∩ ignoreParam (@IdR _).

  Lemma ReadChar_multi_Sem :
    ReadChar_multi ⊨c(1) ReadChar_multi_R.
  Proof.
    eapply RealiseIn_monotone.
    { unfold ReadChar_multi. repeat TM_Correct. }
    { cbn. reflexivity. }
    {
      intros tin (yout, tout) H.
      hnf. TMSimp; clear_trivial_eqs. split; auto.
      eapply VectorSpec.eq_nth_iff; intros p ? <-.
      decide (p = k) as [->|HnEq].
      - apply H.
      - symmetry. apply H0. vector_not_in.
    }
  Qed.

End ReadChar.

Arguments ReadChar_multi : simpl never.
Arguments ReadChar_multi_R { sig n } ( k ) x y /.


Ltac smpl_TM_Multi :=
  match goal with
  | [ |- MovePar _ _ _ _ ⊫ _ ] => eapply RealiseIn_WRealise; eapply MovePar_Sem
  | [ |- MovePar _ _ _ _ ⊨c(_) _ ] => eapply MovePar_Sem
  | [ |- projT1 (MovePar _ _ _ _) ↓ _ ] => eapply RealiseIn_terminatesIn; eapply MovePar_Sem
  | [ |- Copy_char _ ⊫ _ ] => eapply RealiseIn_WRealise; eapply Copy_char_Sem
  | [ |- Copy_char _ ⊨c(_) _ ] => eapply Copy_char_Sem
  | [ |- projT1 (Copy_char _) ↓ _ ] => eapply RealiseIn_terminatesIn; eapply Copy_char_Sem
  | [ |- ReadChar_multi _ _ ⊫ _ ] => eapply RealiseIn_WRealise; eapply ReadChar_multi_Sem
  | [ |- ReadChar_multi _ _ ⊨c(_) _ ] => eapply ReadChar_multi_Sem
  | [ |- projT1 (ReadChar_multi _ _) ↓ _ ] => eapply RealiseIn_terminatesIn; eapply ReadChar_multi_Sem
  end.

Smpl Add smpl_TM_Multi : TM_Correct.