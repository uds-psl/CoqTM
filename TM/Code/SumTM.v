Require Import ProgrammingTools MatchSum.



(**
If there are two function [f1 : X -> Z] and [f2 : Y -> Z], then there is only one canonical way to define a function [map_sum : X + Y -> Z]. This machine operator takes machines [M1] and [M2] that compute the functions [f] and [g]; and defines a machine [Map_sum] that computes [map_sum].
Because this is a machine combinator, we assume that [M1] and [M2] have the same number of tapes [n] and the same alphabet [sigM]. If the numbers of tapes or alphabets don't match, as usual for combinators, the machines have to be lifted, using the n-lift and the Σ-Lift.
*)

Section MapSum.

  Variable n : nat.
  Variable (sigX sigY sigZ : finType).
  Variable (X Y Z : Type) (codX : codable sigX X) (codY : codable sigY Y) (codZ : codable sigZ Z).


  (** The alphabets of the machines [M1] and [M2], and the retracts to the alphabets of the encodings. *)
  Variable (sigM : finType).
  Variable (retr_sigX_sigM : Retract sigX sigM) (retr_sigY_sigM : Retract sigY sigM) (retr_sigZ_sigM : Retract sigZ sigM).

  (** The Machines [M1] and [M2] that compute the functions [f1] and [f2]. *)
  Variable M1 : { M : mTM sigM^+ (S (S n)) & states M -> unit }.
  Variable M2 : { M : mTM sigM^+ (S (S n)) & states M -> unit }.

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


  (** We don't know weather the alphabet of [M1] and [M2] contains [sigSum sigX sigY], so we have to extend the alphabet. We do this in the usual way, by assuming a alphabet [sigMap], which contains [sigSum sigX sigY] in addition to the alphabet of [M1] and [M2]. *)
  Variable sigMap : finType.
  Variable (retr_sigM_sigMap : Retract sigM sigMap).
  Variable (retr_sigSum_sigMap : Retract (sigSum sigX sigY) sigMap).


  (** Now we observe that there a two possible ways how to encode [X] and [Y] on [sigM], by composing retracts. *)
  Local Definition retr_sigX_sigMap  : Retract sigX sigMap := ComposeRetract retr_sigX_sigM retr_sigM_sigMap.
  Local Definition retr_sigX_sigMap' : Retract sigX sigMap := ComposeRetract (Retract_sigSum_X _ _) retr_sigSum_sigMap.

  Local Definition retr_sigY_sigMap  : Retract sigY sigMap := ComposeRetract retr_sigY_sigM retr_sigM_sigMap.
  Local Definition retr_sigY_sigMap' : Retract sigY sigMap := ComposeRetract (Retract_sigSum_Y _ _) retr_sigSum_sigMap.
  

  
  (** I use [Id] here to prevent [TM_Correct] to unfold [ChangeAlphabet], because we want to apply [ChangeAlphabet_Computes] instead. *)
  Definition MapSum : { M : mTM sigMap^+ (S (S n)) & states M -> unit } :=
    If (MatchSum sigX sigY ⇑ _ @ [|Fin0|])
       (Translate retr_sigX_sigMap' retr_sigX_sigMap @ [|Fin0|];; (* Translate the value [x] from the [sigSum] alphabet to the direct [sigX] alphabet *)
         Id (M1 ⇑ _);; (* Call [M1] *)
         Translate retr_sigX_sigMap retr_sigX_sigMap' @ [|Fin0|];; (* Translate [x] back to the alphabet [sigSum sigX sigY] *)
        Constr_inl sigX sigY ⇑ _ @ [|Fin0|]) (* Apply the [inl] constructor again to [x], which has been removed by [MatchSum] *)
       (Translate retr_sigY_sigMap' retr_sigY_sigMap @ [|Fin0|];; (* Translate the value [y] from the [sigSum] alphabet to the direct [sigY] alphabet *)
         Id (M2 ⇑ _);; (* Call [M2] *)
         Translate retr_sigY_sigMap retr_sigY_sigMap' @ [|Fin0|];; (* Translate [y] back to the alphabet [sigSum sigY sigY] *)
        Constr_inr sigX sigY ⇑ _ @ [|Fin0|]) (* Apply the [inr] constructor again to [y], which has been removed by [MatchSum] *)
  .


  Lemma MapSum_Computes : MapSum ⊨ Computes_Rel map_sum.
  Proof.
    eapply Realise_monotone.
    { unfold MapSum. repeat TM_Correct.
      - apply Translate_Realise with (X := X).
      - apply (ChangeAlphabet_Computes (M1_Computes)).
      - apply Translate_Realise with (X := X).
      - apply Translate_Realise with (X := Y).
      - apply (ChangeAlphabet_Computes (M2_Computes)).
      - apply Translate_Realise with (X := Y).
    }
    {
      intros tin ((), tout) H. cbn. intros s HEncS HOut HInt.
      destruct H; TMSimp. (* Both cases of the [If] are symmetric. *)
      { (* Then case, i.e. [s = inl x] *)
        (* First, give better names... *)
        rename H into HMatchSum, H1 into HInject, H0 into HTranslate, H3 into HInject', H2 into HM, H4 into HTranslate', H7 into HInject'', H5 into HConstr, H6 into HInject'''.
        (* The [simpl_not_in], which instantiates index-quantified tape-rewriting hypothesises like [HInject], works better for a fixed number of tapes, so we have to do some manual work here. *)

        modpon HMatchSum. destruct s as [ x | y ]; auto; simpl_surject.

        modpon HTranslate.

        modpon HM.
        { now rewrite HInject', HInject by vector_not_in. } (* This normally happens automatically *)
        { intros i. now rewrite HInject', HInject by vector_not_in. }

        modpon HTranslate'.

        modpon HConstr.

        repeat split; auto.
        { cbn. now rewrite HInject''', HInject'' by vector_not_in. }
        { intros i. now rewrite HInject''', HInject'' by vector_not_in. }
      }
      { (* Then case, i.e. [s = iny y], completely symmetric *)
        (* First, give better names... *)
        rename H into HMatchSum, H1 into HInject, H0 into HTranslate, H3 into HInject', H2 into HM, H4 into HTranslate', H7 into HInject'', H5 into HConstr, H6 into HInject'''.
        (* The [simpl_not_in], which instantiates index-quantified tape-rewriting hypothesises like [HInject], works better for a fixed number of tapes, so we have to do some manual work here. *)

        modpon HMatchSum. destruct s as [ x | y ]; auto; simpl_surject.

        modpon HTranslate.

        modpon HM.
        { now rewrite HInject', HInject by vector_not_in. } (* This normally happens automatically *)
        { intros i. now rewrite HInject', HInject by vector_not_in. }

        modpon HTranslate'.

        modpon HConstr.

        repeat split; auto.
        { cbn. now rewrite HInject''', HInject'' by vector_not_in. }
        { intros i. now rewrite HInject''', HInject'' by vector_not_in. }
      }
    }
  Qed.

  (* TODO: Runtime. *)

End MapSum.