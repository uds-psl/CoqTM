Require Import Prelim.
Require Import TM.Combinators.If TM.Combinators.SequentialComposition.
Require Import TM.TM TM.Basic.Mono.
Require Import TM.Compound.MoveToSymbol.


Section FindSymbol.
  
  Variable sig : finType.
  Variable f : sig -> bool.

  Definition FindSymbol : { M : mTM sig 1 & states M -> FinType (EqType bool)} :=
    If (MoveToSymbol f L)
       (mono_Nop _ true)
       (Move _ R tt ;; MoveToSymbol f R).

  Definition to_symbol t :=
    match to_symbol_l f t with
    | (true,  t') => (true, t')
    | (false, t') => to_symbol_r f (tape_move_mono t' (None, R))
    end.

  Definition R_FindSymbol := Mk_R_p (fun t t' => t' = to_symbol t).

  Lemma FindSymbol_Realise :
    FindSymbol ⊨ R_FindSymbol.
  Proof.
    eapply Realise_monotone.
    - unfold FindSymbol. eapply If_Realise.
      + eapply MoveToSymbol_L_Realise.
      + eapply RealiseIn_Realise. eapply mono_Nop_Sem.
      + eapply Seq_Realise.
        * eapply RealiseIn_Realise. eapply Move_Sem.
        * eapply MoveToSymbol_R_Realise.
    - hnf. intros tin (yout, tout). intros H. hnf in H.
      destruct H as [H | H]; hnf in *.
      + destruct H as (t1&H1&->&->). unfold to_symbol. cbn in H1. now rewrite <- H1.
      + destruct H as(t1&H1&((b&t2)&H2&H3)); hnf in *. destruct b. destruct H2 as (_&H2).
        unfold to_symbol. cbn in H1. rewrite <- H1. cbn. rewrite H2 in *; clear H2. destruct_tapes. now cbn in *.
  Qed.

End FindSymbol.