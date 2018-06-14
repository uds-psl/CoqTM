Require Import ProgrammingTools MatchSum.



(**
If there are two function [f1 : X -> Z] and [f2 : Y -> Z], then there is only one canonical way to define a function [map_sum : X + Y -> Z]. This machine operator takes machines [M1] and [M2] that compute the functions [f] and [g]; and defines a machine [Map_sum] that computes [map_sum]. Alphabets have to be handled with care, to define this machine as general as possible.
One way would be to let [M1] be a machine over [sigX + sigZ] and [M2] over the alphabet [sigY+sigZ]; and to define [Map_sum] over [sigSum sigX sigY + sigZ], but this is not general enough, as a "client" with an alphabet [sig] would had to give a retract from [sigSum sigX sigY + sigZ] to [sig], but this is in general not possible or to complicated. (Counterexample: there is no retract from [unit+unit] to [unit])
*)

Section MapSum.

  Variable n : nat.
  Variable (sigX sigY sigZ : finType) (defX : sigX) (defY : sigY) (defZ : sigZ).
  Variable (X Y Z : Type) (codX : codable sigX X) (codY : codable sigY Y) (codZ : codable sigZ Z).

  (** The alphabet of the first machine contains [sigX] for the input and [sigZ] for the output, so assume retracts from said alphabets to the alphabet of [sigM1]. *)
  Variable (sigM1 : finType) (retr_sigX_sigM1 : Retract sigX sigM1) (retr_sigZ_sigM1 : Retract sigZ sigM1).
  Variable (sigM2 : finType) (retr_sigY_sigM2 : Retract sigY sigM2) (retr_sigZ_sigM2 : Retract sigZ sigM2).


  (** We assume an alphabet [sig] of the "mapped" machine. It should at least contain the alphabets of [M1] and [M2]. *)
  Variable (sig : finType) (retr_sigM1_sig : Retract sigM1 sig) (retr_sigM2_sig : Retract sigM2 sig).

  (** Note that there are now two possible ways how to encode [Z] on [sig]: over the retract from [sigZ] to [sigM1] to [sig], and from [sigZ] to [sigM2] to [sig]. To solve this problem, we assume another retract from [sigZ] to [sig] and copy the result of [M1] or [M2] to this encoding. *)
  Variable (retr_sigZ_sig : Retract sigZ sig).

  (** The other two retracts from [sigZ] to [sig]: *)
  Definition retr_sigZ_sig_M1 : Retract sigZ sig := ComposeRetract retr_sigZ_sigM1 retr_sigM1_sig.
  Definition retr_sigZ_sig_M2 : Retract sigZ sig := ComposeRetract retr_sigZ_sigM2 retr_sigM2_sig.

  (** The input of the "mapped" machine is on [sigSum sigX sigY], which we have to add to the alphabet [sig]. *)
  Variable (retr_sigSum_sig : Retract (sigSum sigX sigY) sig).

  (** Note that we now have the same problem like above for [sigX] and [sigY]: There are multiple ways how to encode [X] and [Y] on [sig]. We simply have to translate from the alphabet [sigX], which is in [sigSum sigX sigY], to the corresponding alphabet [sigX] by [M1], before calling [M1]. *)

  Definition retr_sigX_sig : Retract sigX sig := ComposeRetract (Retract_sigSum_X _ _) retr_sigSum_sig.
  Definition retr_sigX_sig_M1 : Retract sigX sig := ComposeRetract retr_sigX_sigM1 retr_sigM1_sig.

  Definition retr_sigY_sig : Retract sigY sig := ComposeRetract (Retract_sigSum_Y _ _) retr_sigSum_sig.
  Definition retr_sigY_sig_M2 : Retract sigY sig := ComposeRetract retr_sigY_sigM2 retr_sigM2_sig.
  

  (** The Machines [M1] and [M2] that compute the functions [f1] and [f2]. *)
  Variable M1 : { M : mTM sigM1^+ (S (S n)) & states M -> unit }.
  Variable M2 : { M : mTM sigM2^+ (S (S n)) & states M -> unit }.

  Variable f : X -> Z.
  Variable g : Y -> Z.

  Hypothesis M1_Computes : M1 ⊨ Computes_Rel f.
  Hypothesis M2_Computes : M2 ⊨ Computes_Rel g.

  (** The mapped function *)
  Definition map_sum : X + Y -> Z :=
    fun s => match s with
          | inl x => f x
          | inr y => g y
          end.

  
  (** I use [Id] here to prevent [TM_Correct] unfolding [ChangeAlphabet], because we want to apply [ChangeAlphabet_Computes] instead. *)
  Definition MapSum : { M : mTM sig^+ (S (S n)) & states M -> unit } :=
    If (MatchSum sigX sigY ⇑ _ @ [|Fin0|])
       (Translate retr_sigX_sig retr_sigX_sig_M1 @ [|Fin0|];; (* Translate [x] to the alphabet of [M1] *)
        Id (M1 ⇑ _);; (* Call [M1] *)
        Translate retr_sigX_sig_M1 retr_sigX_sig @ [|Fin0|];; (* Translate [x] back to the "choosen" [sigX] on [sig] *)
        Translate retr_sigZ_sig_M1 retr_sigZ_sig @ [|Fin1|];; (* Translate the result [z] to the "choosen" [sigZ] on [sig] *)
        Constr_inl sigX sigY ⇑ _ @ [|Fin0|]) (* Apply the [inl] constructor again to [x], which has been removed by [MatchSum] *)
       (Translate retr_sigY_sig retr_sigY_sig_M2 @ [|Fin0|];; (* Translate [y] to the alphabet of [M2] *)
        Id (M2 ⇑ _);; (* Call [M2] *)
        Translate retr_sigY_sig_M2 retr_sigY_sig @ [|Fin0|];; (* Translate [y] back to the "choosen" [sigY] on [sig] *)
        Translate retr_sigZ_sig_M2 retr_sigZ_sig @ [|Fin1|];; (* Translate the result [z] to the "choosen" [sigZ] on [sig] *)
        Constr_inr sigX sigY ⇑ _ @ [|Fin0|]) (* Apply the [inr] constructor again to [y], which has been removed by [MatchSum] *)
  .


  (* TODO: [Translate_Realise] maybe could be registered to [TM_Correct]. *)
  Lemma MapSum_Computes : MapSum ⊨ Computes_Rel map_sum.
  Proof.
    eapply Realise_monotone.
    { unfold MapSum. repeat TM_Correct.
      - apply Translate_Realise with (X := X).
      - apply (ChangeAlphabet_Computes (M1_Computes)).
      - apply Translate_Realise with (X := X).
      - apply Translate_Realise with (X := Z).
      - apply Translate_Realise with (X := Y).
      - apply (ChangeAlphabet_Computes (M2_Computes)).
      - apply Translate_Realise with (X := Y).
      - apply Translate_Realise with (X := Z).
    }
    {
      intros tin ((), tout) H. cbn. intros s HEncS HOut HInt.
      destruct H; TMSimp. (* Both cases of the [If] are symmetric. *)
      { (* Then case, i.e. [s = inl x] *)
        (* give better names... *)
        rename H into HMatchSum, H1 into HInj1, H0 into HTranslate, H3 into HInj2, H2 into HCompM, H4 into HTranslate'.
        rename H6 into HInj3, H5 into HTranslate'', H9 into HInj4, H7 into HConstr, H8 into HInj5.
        (* instantiate the hypothesises.. *)
        modpon HMatchSum. destruct s as [x|y]; auto. simpl_surject. (* We now know that [s = inl x]. *)
        modpon HTranslate.
        modpon HCompM. (* If [modpon] can't solve a premise of a hypothesis, it opens a goal to let the user prove it. *)
        (* This normally happens automatically, however, [TMSimp] can't handle quantified hypothesises. *)
        { rewrite HInj2, HInj1; auto; vector_not_in. }
        { intros i. now rewrite HInj2, HInj1 by vector_not_in. }
        (* If you want to show the encoding instance somewhere, just [unfold tape_contains] to see it. *)
        unfold tape_contains in HCompM0, HConstr, HCompM0.
        (* Instead of the automatic tactic [modpon], you can also specialize the hypothesis manually and call [spec_assert] *)
        specialize (HTranslate' x); spec_assert HTranslate' by now contains_ext.
        modpon HTranslate''.
        { rewrite HInj3 by vector_not_in. contains_ext. }
        specialize (HConstr x). modpon HConstr.
        { eapply contains_translate_tau1. rewrite HInj4 by vector_not_in. contains_ext. }
        (* Now we have solved all hypothesises, time to call [repeat split; eauto]. *)
        repeat split; cbn; eauto.
        - now rewrite HInj5 by vector_not_in.
        - intros i. now rewrite HInj5, HInj4, HInj3 by vector_not_in.
      }
      { (* Then case, i.e. [s = iny y], completely symmetric *)
        (* give better names... *)
        rename H into HMatchSum, H1 into HInj1, H0 into HTranslate, H3 into HInj2, H2 into HCompM, H4 into HTranslate'.
        rename H6 into HInj3, H5 into HTranslate'', H9 into HInj4, H7 into HConstr, H8 into HInj5.
        (* instantiate the hypothesises.. *)
        modpon HMatchSum. destruct s as [x|y]; auto. simpl_surject. (* We now know that [s = inr y]. *)
        modpon HTranslate.
        modpon HCompM. (* If [modpon] can't solve a premise of a hypothesis, it opens a goal to let the user prove it. *)
        (* This normally happens automatically, however, [TMSimp] can't handle quantified hypothesises. *)
        { rewrite HInj2, HInj1; auto; vector_not_in. }
        { intros i. now rewrite HInj2, HInj1 by vector_not_in. }
        (* If you want to show the encoding instance somewhere, just [unfold tape_contains] to see it. *)
        unfold tape_contains in HCompM0, HConstr, HCompM0.
        (* Instead of the automatic tactic [modpon], you can also specialize the hypothesis manually and call [spec_assert] *)
        specialize (HTranslate' y); spec_assert HTranslate' by now contains_ext.
        modpon HTranslate''.
        { rewrite HInj3 by vector_not_in. contains_ext. }
        specialize (HConstr y). modpon HConstr.
        { eapply contains_translate_tau1. rewrite HInj4 by vector_not_in. contains_ext. }
        (* Now we have solved all hypothesises, time to call [repeat split; eauto]. *)
        repeat split; cbn; eauto.
        - now rewrite HInj5 by vector_not_in.
        - intros i. now rewrite HInj5, HInj4, HInj3 by vector_not_in.
      }
    }
    (* Done. *)
  Qed.

  (* TODO: Runtime. *)

End MapSum.