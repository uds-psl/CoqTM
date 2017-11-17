Require Import TM.Prelim TM.TM TM.Code.Code TM.Code.CodeTM.
Require Import TM.Basic.Mono.
Require Import TM.Combinators.SequentialComposition TM.Combinators.Match.

Section FinTM1.
  Variable sig : finType.
  Variable f : sig -> sig.

  Let cX := Encode_Finite sig.
  Let codeX := codeX cX.
  Let sig' := sig' sig.

  Definition UnaryFinTM : { M : mTM sig' 1 & states M -> unit } :=
    MATCH (Read_char _)
          (fun r1 =>
             match r1 with
             | Some (inl r1') => Write (inl (f r1')) tt
             | _ => mono_Nop _ tt
             end).
  
  Lemma UnaryFinTM_Computes :
    UnaryFinTM ⊨c(3) Computes_Rel Fin.F1 Fin.F1 cX cX f.
  Proof.
    eapply RealiseIn_monotone.
    - unfold UnaryFinTM. eapply Match_RealiseIn.
      + eapply read_char_sem.
      + instantiate (2 := fun r1 => match r1 with Some (inl r1') => _ | _ => _ end).
        intros y. cbn in y. destruct y as [ [ | ] | ]; cbn in *.
        * eapply Write_Sem.
        * eapply mono_Nop_Sem.
        * eapply mono_Nop_Sem.
    - cbn. omega.
    - hnf. intros tin (yout, tout) H x (r1&r2&H3&H4). hnf in H.
      destruct H as (y&t2&H1&H2). hnf in *. destruct y as [ [ | ] | ]; hnf in *.
      + (* valid input *) destruct H1 as (H&H'). hnf in *. destruct H2 as (->&H2). subst.
        destruct_tapes. cbn in *. subst. cbn.
        pose proof tape_local_current_cons H4 as H4'; rewrite H4' in H; inv H; clear H4'.
        do 2 eexists. hnf; cbn. split; eauto. f_equal. eapply tape_local_right; eauto.
      + (* invalid input *) destruct H1 as (H&H'). hnf in *. destruct H2 as (->&->). subst. cbn in *.
        apply tape_local_current_cons in H4. destruct_tapes. cbn in *. congruence.
      + (* invalid input *) destruct H1 as (H&H'). hnf in *. destruct H2 as (->&->). subst. cbn in *.
        apply tape_local_current_cons in H4. destruct_tapes. cbn in *. congruence.
  Qed.
  
End FinTM1.