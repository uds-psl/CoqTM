Require Import ProgrammingTools.

(* Basic pattern matching *)
Section MatchSum.

  Variable X Y : Type.

  Variable (sigX sigY : finType).
  Hypothesis (codX : codable sigX X) (codY : codable sigY Y).

  Definition MatchSum_Rel : Rel (tapes (sigSum sigX sigY)^+ 1) (bool * tapes ((sigSum sigX sigY)^+) 1) :=
    Mk_R_p (
        fun tin '(yout, tout) =>
          forall s : X + Y,
            tin ≃ s ->
            match yout, s with
            | true, inl x => tout ≃ x
            | false, inr y => tout ≃ y
            | _, _ => False
            end).


  Definition MatchSum : { M : mTM (sigSum sigX sigY)^+ 1 & states M -> bool } :=
    Move R;; (* skip the [START] symbol *)
    MATCH (ReadChar) (* read the "constructor" symbol *)
          (fun o => match o with (* Write a new [START] symbol and terminate in the corresponding partition *)
                 | Some (inr sigSum_inl) => Return (Write (inl START)) true  (* inl *)
                 | Some (inr sigSum_inr) => Return (Write (inl START)) false (* inr *)
                 | _ => Return (Nop) true (* invalid input *)
                 end).

  Definition MatchSum_steps := 5.

  Lemma MatchSum_Sem : MatchSum ⊨c(MatchSum_steps) MatchSum_Rel.
  Proof.
    unfold MatchSum_steps. eapply RealiseIn_monotone.
    { unfold MatchSum. repeat TM_Correct. }
    { Unshelve. 4,10,11: constructor. all: cbn. all: omega. }
    {
      intros tin (yout&tout) H.
      intros s HEncS. destruct HEncS as (ls&HEncS). TMSimp; clear_trivial_eqs. clear HEncS tin.
      destruct s as [x|y]; cbn in *; TMSimp.
      - (* s = inl x *) now repeat econstructor.
      - (* s = inr y *) now repeat econstructor.
    }
  Qed.

  (* Constructors *)
  Section SumConstr.


    Definition Constr_inl_Rel : Rel (tapes (sigSum sigX sigY)^+ 1) (unit * tapes (sigSum sigX sigY)^+ 1) :=
      Mk_R_p (ignoreParam (fun tin tout => forall x:X, tin ≃ x -> tout ≃ inl x)).

    Definition Constr_inr_Rel : Rel (tapes (sigSum sigX sigY)^+ 1) (unit * tapes (sigSum sigX sigY)^+ 1) :=
      Mk_R_p (ignoreParam (fun tin tout => forall y:Y, tin ≃ y -> tout ≃ inr y)).

    Definition Constr_inl : { M : mTM (sigSum sigX sigY)^+ 1 & states M -> unit } :=
      WriteMove (inr sigSum_inl) L;; Write (inl START).

    Definition Constr_inr : { M : mTM (sigSum sigX sigY)^+ 1 & states M -> unit } :=
      WriteMove (inr sigSum_inr) L;; Write (inl START).


    Lemma Constr_inl_Sem : Constr_inl ⊨c(3) Constr_inl_Rel.
    Proof.
      eapply RealiseIn_monotone.
      { unfold Constr_inl. repeat TM_Correct. }
      { cbn. reflexivity. }
      {
        intros tin (()&tout) H.
        cbn. intros x HEncX. destruct HEncX as (ls&HEncX). TMSimp; clear_trivial_eqs.
        repeat econstructor. f_equal. simpl_tape. cbn. reflexivity.
      }
    Qed.

    Lemma Constr_inr_Sem : Constr_inr ⊨c(3) Constr_inr_Rel.
    Proof.
      eapply RealiseIn_monotone.
      { unfold Constr_inr. repeat TM_Correct. }
      { cbn. reflexivity. }
      {
        intros tin (()&tout) H.
        cbn. intros y HEncY. destruct HEncY as (ls&HEncY). TMSimp; clear_trivial_eqs.
        repeat econstructor. f_equal. simpl_tape. cbn. reflexivity.
      }
    Qed.

  End SumConstr.

End MatchSum.

Arguments MatchSum : simpl never.
Arguments Constr_inl : simpl never.
Arguments Constr_inr : simpl never.

Ltac smpl_TM_MatchSum :=
  match goal with
  | [ |- MatchSum _ _ ⊨ _ ] => eapply RealiseIn_Realise; apply MatchSum_Sem
  | [ |- MatchSum _ _ ⊨c(_) _ ] => apply MatchSum_Sem
  | [ |- projT1 (MatchSum _ _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply MatchSum_Sem
  | [ |- Constr_inr _ _ ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_inr_Sem
  | [ |- Constr_inr _ _ ⊨c(_) _ ] => apply Constr_inr_Sem
  | [ |- projT1 (Constr_inr _ _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Constr_inr_Sem
  | [ |- Constr_inl _ _ ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_inl_Sem
  | [ |- Constr_inl _ _ ⊨c(_) _ ] => apply Constr_inl_Sem
  | [ |- projT1 (Constr_inl _ _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Constr_inl_Sem
  end.

Smpl Add smpl_TM_MatchSum : TM_Correct.







(** ** Reductions *)

Section MatchOption.

  (* Matching of option reduces to matching of sums with [Empty_set] *)

  Variable X : Type.
  Variable (sigX : finType).
  Hypothesis (codX : codable sigX X).

  Compute encode (None : option nat).
  Compute encode (Some 42).

  Let sig := FinType (EqType (sigSum sigX (FinType(EqType Empty_set)))).
  Let tau := FinType (EqType (sigOption sigX)).

  Check _ : codable sig X.
  Check _ : codable sig^+ X.
  Check _ : codable tau X.
  Check _ : codable tau^+ X.
  Check _ : codable tau (option X).
  Check _ : codable tau^+ (option X).

  Definition MatchOption_Rel : Rel (tapes tau^+ 1) (bool * tapes tau^+ 1) :=
    Mk_R_p (fun tin '(yout, tout) =>
              forall o : option X,
                tin ≃ o ->
                match yout, o with
                | true, Some x => tout ≃ x
                | false, None => isRight tout
                | _, _ => False
                end).

  Local Instance Retract_sigOption_sigSum :
    Retract (sigSum sigX Empty_set) (sigOption sigX) :=
    {|
      Retr_f x := match x : (sigSum sigX (FinType (EqType Empty_set))) with
                  | sigSum_X a => sigOption_X a
                  | sigSum_Y b => match b with end
                  | sigSum_inl => sigOption_Some
                  | sigSum_inr => sigOption_None
                  end;
      Retr_g y := match y with
                  | sigOption_X a => Some (sigSum_X a)
                  | sigOption_Some => Some (sigSum_inl)
                  | sigOption_None => Some (sigSum_inr)
                  end;
      |}.
  Proof.
    abstract now intros x y; split;
      [ now destruct y; intros H; inv H
      | intros ->; now destruct x as [ a | [] | | ]
      ].
  Defined.


  Definition MatchOption : { M : mTM tau^+ 1 & states M -> bool } :=
    If (ChangeAlphabet (MatchSum (sigX) (FinType (EqType Empty_set))) _)
       (Return Nop true)
       (Return (ResetEmpty _) false).

  Definition opt_to_sum (o : option X) : X + unit :=
    match o with
    | Some x => inl x
    | None => inr tt
    end.

  Definition MatchOption_steps := 7.
  
  Lemma MatchOption_Sem :
    MatchOption ⊨c(MatchOption_steps) MatchOption_Rel.
  Proof.
    unfold MatchOption_steps. eapply RealiseIn_monotone.
    { unfold MatchOption. repeat TM_Correct. unfold ChangeAlphabet. repeat TM_Correct.
      - apply ResetEmpty_Sem with (X := unit).
    }
    { cbn. reflexivity. }
    {
      intros tin (yout&tout) H. intros o HEncO.
      unfold tape_contains in HEncO. (* This makes the (otherwise implicit) encoding visible *)
      cbn in *.

      destruct H; TMSimp; unfold tau in *.
      { (* "Then" case *)
        (* This part is the same for both branches *)
        simpl_tape in H. cbn in *.
        specialize (H (opt_to_sum o)). spec_assert H.
        { 
          simpl_surject.
          eapply tape_contains_ext with (1 := HEncO).
          destruct o; cbn; f_equal. rewrite !List.map_map. apply map_ext. cbv; auto.
        }
        destruct o as [ x | ]; cbn in *; auto.
        simpl_tape in H; cbn in *; simpl_surject.

        (* We know now that o = Some x *)
        unfold tape_contains in H. unfold tape_contains.
        eapply tape_contains_ext with (1 := H). cbn. rewrite List.map_map. apply map_ext. auto.
      }
      { (* "Else" case *)
        simpl_tape in H. cbn in *.
        specialize (H (opt_to_sum o)). spec_assert H.
        { 
          simpl_surject.
          eapply tape_contains_ext with (1 := HEncO).
          destruct o; cbn; f_equal. rewrite !List.map_map. apply map_ext. cbv; auto.
        }
        destruct o as [ x | ]; cbn in *; auto.
        simpl_tape in H; cbn in *; simpl_surject.
        modpon H1.
        (* We know now that o = None *)
        eapply H1; eauto.
      }
    }
  Qed.


  Definition Constr_Some_Rel : Rel (tapes tau^+ 1) (unit * tapes tau^+ 1) :=
    Mk_R_p (ignoreParam(
                fun tin tout =>
                  forall x : X,
                    tin ≃ x ->
                    tout ≃ Some x)).

  Definition Constr_Some : { M : mTM tau^+ 1 & states M -> unit } :=
    ChangeAlphabet (Constr_inl sigX (FinType (EqType Empty_set))) _.

  Definition Constr_Some_steps := 3.

  Lemma Constr_Some_Sem : Constr_Some ⊨c(Constr_Some_steps) Constr_Some_Rel.
  Proof.
    unfold Constr_Some_steps. eapply RealiseIn_monotone.
    { unfold Constr_Some. unfold ChangeAlphabet. repeat TM_Correct. }
    { cbn. reflexivity. }
    {
      intros tin ((), tout) H.
      intros x HEncX. TMSimp.
      simpl_tape in H. cbn in H.
      unfold tape_contains in *.
      specialize (H x). spec_assert H.
      { eapply contains_translate_tau1. unfold tape_contains. eapply tape_contains_ext with (1 := HEncX).
        cbn. rewrite !List.map_map. apply map_ext. cbv. auto. }
      apply contains_translate_tau2 in H. unfold tape_contains in H.
      eapply tape_contains_ext with (1 := H). cbn. now rewrite !List.map_map.
    }
  Qed.

  
  Definition Constr_None_Rel : Rel (tapes tau^+ 1) (unit * tapes tau^+ 1) :=
    Mk_R_p (ignoreParam(
                fun tin tout =>
                    isRight tin ->
                    tout ≃ None)).

  Definition Constr_None : { M : mTM tau^+ 1 & states M -> unit } :=
    WriteMove (inl STOP) L;; WriteMove (inr sigOption_None) L;; Write (inl START).

  Lemma Constr_None_Sem : Constr_None ⊨c(5) Constr_None_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold Constr_None. repeat TM_Correct. }
    { cbn. reflexivity. }
    {
      intros tin ((), tout) H.
      intros HRight.
      subst sig tau.
      TMSimp; clear_trivial_eqs.
      repeat econstructor. cbn. f_equal. simpl_tape. cbn. f_equal. f_equal. now apply isRight_right.
    }
  Qed.

End MatchOption.

Arguments MatchOption : simpl never.
Arguments Constr_None : simpl never.
Arguments Constr_Some : simpl never.


Ltac smpl_TM_MatchOption :=
  match goal with
  | [ |- MatchOption _ ⊨ _ ] => eapply RealiseIn_Realise; apply MatchOption_Sem
  | [ |- MatchOption _ ⊨c(_) _ ] => apply MatchOption_Sem
  | [ |- projT1 (MatchOption _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply MatchOption_Sem
  | [ |- Constr_None _ ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_None_Sem
  | [ |- Constr_None _ ⊨c(_) _ ] => apply Constr_None_Sem
  | [ |- projT1 (Constr_None _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Constr_None_Sem
  | [ |- Constr_Some _ ⊨ _ ] => eapply RealiseIn_Realise; apply Constr_Some_Sem
  | [ |- Constr_Some _ ⊨c(_) _ ] => apply Constr_Some_Sem
  | [ |- projT1 (Constr_Some _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply Constr_Some_Sem
  end.

Smpl Add smpl_TM_MatchOption : TM_Correct.
