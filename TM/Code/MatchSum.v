Require Import TM.Code.CodeTM.
Require Import TM.Basic.Mono TM.Basic.Nop TM.Basic.Multi.
Require Import TM.Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.
Require Import TM.Compound.CopySymbols TM.Compound.MoveToSymbol.


(* Basic pattern matching *)
Section MatchSum.

  Variable X Y : Type.

  Variable (sigX sigY : finType).
  Hypothesis (codX : codable sigX X) (codY : codable sigY Y).

  Definition MatchSum_Rel : Rel (tapes ((bool + (sigX+sigY))^+) 1) (bool * tapes ((bool + (sigX+sigY))^+) 1) :=
    Mk_R_p (fun tin '(yout, tout) =>
              forall s : X + Y, tin ≃ s ->
                           match s with
                           | inl x => tout ≃ x /\ yout = true
                           | inr y => tout ≃ y /\ yout = false
                           end).


  Definition MatchSum : { M : mTM (bool + (sigX+sigY))^+ 1 & states M -> bool } :=
    Move _ R tt;; (* skip the [START] symbol *)
    MATCH (Read_char _) (* read the "constructor" symbol *)
          (fun o => match o with (* Write a new [START] symbol and terminate in the corresponding partition *)
                 | Some (inr (inl true))  => Write (inl START) true  (* inl *)
                 | Some (inr (inl false)) => Write (inl START) false (* inr *)
                 | _ => mono_Nop _ true (* invalid input *)
                 end).

  Lemma MatchSum_Sem : MatchSum ⊨c(5) MatchSum_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold MatchSum. repeat TM_Correct. }
    { Unshelve. 4,6: constructor. all: cbn. all: omega. }
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


    Definition Constr_inl_Rel : Rel (tapes (bool + (sigX+sigY))^+ 1) (unit * tapes (bool + (sigX+sigY))^+ 1) :=
      Mk_R_p (ignoreParam (fun tin tout => forall x:X, tin ≃ x -> tout ≃ inl x)).

    Definition Constr_inr_Rel : Rel (tapes (bool + (sigX+sigY))^+ 1) (unit * tapes (bool + (sigX+sigY))^+ 1) :=
      Mk_R_p (ignoreParam (fun tin tout => forall y:Y, tin ≃ y -> tout ≃ inr y)).

    Definition Constr_inl : { M : mTM (bool + (sigX+sigY))^+ 1 & states M -> unit } :=
      WriteMove (Some (inr (inl true)), L) tt;; Write (inl START) tt.

    Definition Constr_inr : { M : mTM (bool + (sigX+sigY))^+ 1 & states M -> unit } :=
      WriteMove (Some (inr (inl false)), L) tt;; Write (inl START) tt.


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

(** ** Reductions *)

Require Import ChangeAlphabet LiftSigmaTau.

Section MatchOption.

  (* Matching of option reduces to matching of sums with [Empty_set] *)

  Variable X : Type.
  Variable (sigX : finType).
  Hypothesis (codX : codable sigX X).

  Compute encode (None : option nat).
  Compute encode (Some 42).

  Let sig := FinType (EqType (bool + (sigX + Empty_set))).
  Let tau := FinType (EqType (bool + sigX)).

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
                match o with
                | Some x => tout ≃ x /\ yout = true
                | None => isRight tout /\ yout = false
                end).

  Definition MatchOption : { M : mTM tau^+ 1 & states M -> bool } :=
    If (ChangeAlphabet (MatchSum (sigX) (FinType (EqType Empty_set))) _)
       (Nop _ _ true)
       (Move _ R false).

  Definition opt_to_sum (o : option X) : X + unit :=
    match o with
    | Some x => inl x
    | None => inr tt
    end.
  
  
  Lemma MatchOption_Sem :
    MatchOption ⊨c(7) MatchOption_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold MatchOption. repeat TM_Correct. unfold ChangeAlphabet. repeat TM_Correct.
      - eapply MatchSum_Sem with (X := X) (Y := unit).
    }
    { cbn. reflexivity. }
    {
      intros tin (yout&tout) H. intros o HEncO.
      unfold tape_contains in HEncO. (* This makes the (otherwise implicit) encoding visible *)
      cbn in *.

      destruct H; TMSimp.
      { (* "Then" case *)
        (* This part is the same for both branches *)
        specialize (H (opt_to_sum o)). spec_assert H.
        { autounfold with tape. cbn. erewrite nth_map2'. cbn. 
          eapply contains_translate_tau1.
          eapply tape_contains_ext with (X := option X); eauto.
          destruct o; cbn; f_equal. rewrite !List.map_map. apply map_ext. cbn. auto.
        }
        destruct o as [ x | ]; cbn in *; destruct H as (H&H'); inv H'. split; auto.
        (* We know now that o = Some x *)

        autounfold with tape in H. cbn in H. rewrite nth_map2' in H. cbn in H.
        unfold tape_contains in H. unfold tape_contains.

        apply contains_translate_tau2 in H; unfold tape_contains in H.
        eapply tape_contains_ext with (1 := H). cbn. rewrite List.map_map. apply map_ext. auto.
      }
      { (* "Else" case *)
        specialize (H (opt_to_sum o)). spec_assert H.
        { autounfold with tape. cbn. erewrite nth_map2'. cbn. 
          eapply contains_translate_tau1.
          eapply tape_contains_ext with (X := option X); eauto.
          destruct o; cbn; f_equal. rewrite !List.map_map. apply map_ext. cbn. auto.
        }
        destruct o as [ x | ]; cbn in *; destruct H as (H&H'); inv H'. split; auto.
        (* We know now that o = None *)

        autounfold with tape in H. cbn in H. rewrite nth_map2' in H. cbn in H.
        unfold tape_contains in H.
        apply contains_translate_tau2 in H; unfold tape_contains in H.
        destruct H as (ls&->). cbn. repeat econstructor.
      }
    }
  Qed.

End MatchOption.


Section MapSum.

  Variable n : nat.
  Variable (sigX sigY sigZ : finType) (defX : sigX) (defY : sigY) (defZ : sigZ).
  Variable (X Y Z : Type) (codX : codable sigX X) (codY : codable sigY Y) (codZ : codable sigZ Z).

  Let sig_match := FinType(EqType (bool+(sigX+sigY))).
  Let sig_M1 := FinType(EqType (sigX+sigZ)).
  Let sig_M2 := FinType(EqType (sigY+sigZ)).
  Let tau := FinType(EqType ((bool + (sigX + sigY)) + sigZ)).

  Variable f : X -> Z.
  Variable g : Y -> Z.

  Variable M1 : { M : mTM sig_M1^+ (S (S n)) & states M -> unit }.
  Variable M2 : { M : mTM sig_M2^+ (S (S n)) & states M -> unit }.

  Hypothesis M1_Computes : M1 ⊫ Computes_Rel f.
  Hypothesis M2_Computes : M2 ⊫ Computes_Rel g.

  Definition map_sum : X + Y -> Z :=
    fun s => match s with
          | inl x => f x
          | inr y => g y
          end.

  
  (* This kind of retracts can only be infered semi-automatically, because [Retract_sum] is no typeclass instance. *)
  (* In this case, we map [inl x] to [inl (inr (inl x))] and [inr z] to [inr z]. *)
  Local Instance retr_M1 : Retract sig_M1 tau := Retract_sum _ _.
  Local Instance retr_M2 : Retract sig_M2 tau := Retract_sum _ _.


  Definition MapSum : { M : mTM tau^+ (S (S n)) & states M -> unit } :=
    If (Inject (ChangeAlphabet (MatchSum sigX sigY) _) [|Fin0|])
       (ChangeAlphabet M1 _;;
        Inject (ChangeAlphabet (Constr_inl sigX sigY) _) [|Fin0|])
       (ChangeAlphabet M2 _;;
        Inject (ChangeAlphabet (Constr_inr sigX sigY) _) [|Fin0|]).


  Lemma MapSum_Computes : MapSum ⊫ Computes_Rel map_sum.
  Proof.
    eapply WRealise_monotone.
    { unfold MapSum. repeat TM_Correct.
      - unfold ChangeAlphabet. eapply RealiseIn_WRealise. TM_Correct. apply MatchSum_Sem with (X := X) (Y := Y).
      - eapply ChangeAlphabet_Computes with (X := X) (Y := Z). apply M1_Computes.
      - unfold ChangeAlphabet. eapply RealiseIn_WRealise. TM_Correct. apply Constr_inl_Sem.
      - eapply ChangeAlphabet_Computes with (X := Y) (Y := Z). apply M2_Computes.
      - unfold ChangeAlphabet. eapply RealiseIn_WRealise. TM_Correct. apply Constr_inr_Sem.
    }
    {
      intros tin ((), tout) H.
      intros s HEncS HOut HInt.
      destruct H; TMSimp.
      { (* "Then" branche ([s = inl x]) *)
        specialize (H s). spec_assert H.
        { eapply contains_translate_tau1; auto. }
        destruct s as [ x | y]; destruct H as (H&H'); inv H'.
        rewrite (H1 Fin1 ltac:(vector_not_in)) in *.
        apply contains_translate_tau2 in H.
        unfold tape_contains in H, H0.
        specialize (H0 x). spec_assert H0.
        { eapply tape_contains_ext with (1 := H). cbn. rewrite !List.map_map. apply map_ext. cbn. cbv. auto. }
        specialize (H0 HOut). spec_assert H0 as (HCompIn&HCompOut&HCompInt).
        { intros i. rewrite <- H1; auto. vector_not_in. }
        specialize (H2 x). spec_assert H2.
        { apply contains_translate_tau1. eapply tape_contains_ext with (1 := HCompIn).
          cbn. rewrite !List.map_map. apply map_ext. cbv. auto. }
        apply contains_translate_tau2 in H2; swap 1 2.
        repeat split; cbn; auto.
        + rewrite H3 in HCompOut. 2: vector_not_in. eapply tape_contains_ext with (1 := HCompOut).
          cbn. rewrite List.map_map. apply map_ext. cbv. auto.
        + intros i. specialize (HCompInt i). rewrite H3 in HCompInt. 2: vector_not_in. auto.
      }
      { (* "Else" branche ([s = inr y]) *)
        specialize (H s). spec_assert H.
        { eapply contains_translate_tau1; auto. }
        destruct s as [ x | y]; destruct H as (H&H'); inv H'.
        rewrite (H1 Fin1 ltac:(vector_not_in)) in *.
        apply contains_translate_tau2 in H; swap 1 2.
        unfold tape_contains in H, H0.
        specialize (H0 y). spec_assert H0.
        { eapply tape_contains_ext with (1 := H). cbn. rewrite !List.map_map. apply map_ext. cbn. cbv. auto. }
        specialize (H0 HOut). spec_assert H0 as (HCompIn&HCompOut&HCompInt).
        { intros i. rewrite <- H1; auto. vector_not_in. }
        specialize (H2 y). spec_assert H2.
        { apply contains_translate_tau1. eapply tape_contains_ext with (1 := HCompIn).
          cbn. rewrite !List.map_map. apply map_ext. cbv. auto. }
        apply contains_translate_tau2 in H2; swap 1 2.
        repeat split; cbn; auto.
        + rewrite H3 in HCompOut. 2: vector_not_in. eapply tape_contains_ext with (1 := HCompOut).
          cbn. rewrite List.map_map. apply map_ext. cbv. auto.
        + intros i. specialize (HCompInt i). rewrite H3 in HCompInt. 2: vector_not_in. auto.
      }
    }
  Qed.

End MapSum.