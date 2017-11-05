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
    TapeInit sig ;;
             MATCH (Read_char _)
             (fun r1 =>
                match r1 with
                | Some (inl r1') => Write (inl (f r1')) tt
                | _ => mono_Nop _ tt
                end).
  
  Lemma UnaryFinTM_Computes :
    UnaryFinTM ⊨ Computes_Rel Fin.F1 Fin.F1 cX cX f.
  Proof.
    eapply Realise_monotone.
    - unfold UnaryFinTM. eapply Seq_Realise.
      + eapply TapeInit_Realise with (X := sig) (cX := cX).
      + eapply Match_Realise.
        * eapply RealiseIn_Realise. eapply read_char_sem.
        * instantiate (1 := fun r1 => match r1 with Some (inl r1') => _ | _ => _ end).
          intros y. cbn in y. destruct y as [ [ | ] | ]; cbn in *.
          -- eapply RealiseIn_Realise. eapply Write_Sem.
          -- eapply RealiseIn_Realise. eapply mono_Nop_Sem.
          -- eapply RealiseIn_Realise. eapply mono_Nop_Sem.
    - hnf. intros tin (yout, tout). intros H. hnf in H. destruct H as ((y1&t1)&H1&H2). hnf in *.
      destruct H2 as (r1&t2&(He1&He2)&H3); hnf in *; subst. intros x (r1&r2&EncX). specialize (H1 _ _ _ EncX) as (H1&H2).
      cbn in *. pose proof tape_local_current_cons H2 as H2'. destruct_tapes. cbn in *. rewrite H2' in H3. hnf in H3.
      destruct H3 as (_&H3). cbn in *. subst. destruct yout, y1.
      unfold sig', CodeTM.sig', finType_CS in *. cbn in *. hnf in EncX.
      rewrite H1. hnf. do 2 eexists. hnf. cbn. simpl_list.
      instantiate (1 := r2). instantiate (1 := r1). f_equal. cbn. f_equal. f_equal. 
      erewrite tape_local_right; eauto.
  Qed.
  
End FinTM1.