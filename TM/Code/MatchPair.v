Require Import TM.Code.CodeTM.
Require Import TM.Basic.Mono TM.Basic.Nop TM.Basic.Multi.
Require Import TM.Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.
Require Import TM.Compound.CopySymbols TM.Compound.MoveToSymbol TM.Code.Copy.


(* TODO: ~> base *)
Lemma pair_eq (A B : Type) (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) ->
  a1 = a2 /\ b1 = b2.
Proof. intros H. now inv H. Qed.

Local Arguments skipn { A } !n !l.


Section MatchSum.

  Variable (sigX sigY: finType) (X Y: Type) (cX: codable sigX X) (cY: codable sigY Y).

  Definition sigPair := (FinType(EqType(sigX+sigY))).


  Definition stopAfterFirst : sigPair^+ -> bool :=
    fun x => match x with
          | inr (inr y) => true
          | inl STOP => true
          | _ => false
          end.

  
  Definition stopAtStart : sigPair^+ -> bool :=
    fun x => match x with
          | inl START => true
          | _ => false
          end.


  Definition MatchPair_Rel : Rel (tapes sigPair^+ 2) (unit * tapes sigPair^+ 2) :=
    ignoreParam (
        fun tin tout =>
          forall p : X * Y,
            tin[@Fin0] ≃ p ->
            isRight tin[@Fin1] ->
            tout[@Fin0] ≃ snd p /\
            tout[@Fin1] ≃ fst p
      ).

  Definition MatchPair : { M : mTM sigPair^+ 2 & states M -> unit } :=
    Inject (WriteMove (inl STOP) L tt) [|Fin1|];;
    Inject (MoveToSymbol stopAfterFirst;; Move L tt) [|Fin0|];;
    CopySymbols_L stopAtStart id;;
    Inject (MoveToSymbol stopAfterFirst;; Move L tt;; Write (inl START) tt) [|Fin0|].



  Lemma MatchPair_Realise : MatchPair ⊨ MatchPair_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold MatchPair. repeat TM_Correct. }
    {
      intros tin ((), tout) H.
      intros (x,y) HEncXY HRight.
      destruct HEncXY as (ls&HEncXY).
      TMSimp; clear_trivial_eqs. rename H2 into HCopy.
      rewrite map_app, <- app_assoc in HCopy.

      (* We need a case distinction, whether the encoding of [y] is empty or. However, both parts of the proof are identical. *)
      destruct (cY y) eqn:EY; cbn in *.
      - rewrite MoveToSymbol_correct_midtape in HCopy; cbn in *; auto.
        erewrite CopySymbols_L_correct_moveleft in HCopy; cbn; auto.
        + apply pair_eq in HCopy as (HCopy1, HCopy2). TMSimp.
          * repeat econstructor. f_equal.
            rewrite MoveToSymbol_correct_midtape; cbn; auto.
            -- simpl_tape. now rewrite EY.
            -- rewrite rev_involutive, List.map_map. now intros ? (?&<-&?) % in_map_iff.
            -- cbn. rewrite map_id, rev_involutive, !List.map_map.
               f_equal. f_equal. setoid_rewrite isRight_right at 2; auto. now simpl_tape.
        + rewrite List.map_map. now intros ? (?&<-&?) % in_rev % in_map_iff.
        + rewrite List.map_map. now intros ? (?&<-&?) % in_map_iff.
      - rewrite MoveToSymbol_correct_midtape in HCopy; cbn in *; auto.
        erewrite CopySymbols_L_correct_moveleft in HCopy; cbn; auto.
        + apply pair_eq in HCopy as (HCopy1, HCopy2). TMSimp.
          * repeat econstructor. f_equal.
            rewrite MoveToSymbol_correct_midtape; cbn; auto.
            -- simpl_tape. now rewrite EY.
            -- rewrite rev_involutive, List.map_map. now intros ? (?&<-&?) % in_map_iff.
            -- cbn. rewrite map_id, rev_involutive, !List.map_map.
               f_equal. f_equal. setoid_rewrite isRight_right at 2; auto. now simpl_tape.
        + rewrite List.map_map. now intros ? (?&<-&?) % in_rev % in_map_iff.
        + rewrite List.map_map. now intros ? (?&<-&?) % in_map_iff.
    }
  Qed.




  (** Constructor *)

  
  Definition Constr_pair_Rel : Rel (tapes sigPair^+ 2) (unit * tapes sigPair^+ 2) :=
    ignoreParam (
        fun tin tout =>
          forall (x : X) (y : Y),
            tin[@Fin0] ≃ x ->
            tin[@Fin1] ≃ y ->
            tout[@Fin0] ≃ x /\
            tout[@Fin1] ≃ (x, y)
      ).


  Definition Constr_pair : { M : mTM sigPair^+ 2 & states M -> unit } :=
    Inject (MoveToSymbol stopAfterFirst;; Move L tt) [|Fin0|];;
    CopySymbols_L stopAtStart id.


  Lemma Constr_pair_Realise : Constr_pair ⊨ Constr_pair_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold Constr_pair. repeat TM_Correct. }
    {
      intros tin ((), tout) H. intros x y HEncX HEncY.
      destruct HEncX as (ls1&HEncX), HEncY as (ls2&HEncY).
      TMSimp; clear_trivial_eqs. rename H0 into HCopy.
      rewrite MoveToSymbol_correct_midtape in HCopy; cbn in *; auto.
      - rewrite CopySymbols_L_correct_moveleft in HCopy; cbn in *; auto.
        + apply pair_eq in HCopy as (HCopy1&HCopy2). TMSimp.
          split.
          * repeat econstructor. cbn. f_equal. now rewrite rev_involutive.
          * repeat econstructor. cbn. f_equal. simpl_tape. now rewrite map_id, rev_involutive, !List.map_app, <- app_assoc.
        + rewrite List.map_map. now intros ? (?&<-&?) % in_rev % in_map_iff.
      - rewrite List.map_map. now intros ? (?&<-&?) % in_map_iff.
    }
  Qed.


End MatchSum.