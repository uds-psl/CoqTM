Require Import TM.Code.CodeTM.
Require Import TM.Code.MatchNat TM.Code.MatchSum TM.Code.MatchFin TM.Code.WriteValue.
Require Import TM.Code.ChangeAlphabet TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Basic.Mono.


Inductive Tok := varT (n :nat) | appT | lamT | retT.
Notation Pro := (list Tok) (only parsing).


Definition sigTok := (FinType (EqType (bool + (bool + Fin.t 3)))).

Coercion Tok_to_sum (t : Tok) : (nat + Fin.t 3) :=
  match t with
  | varT x => inl x
  | appT => inr Fin0
  | lamT => inr Fin1
  | retT => inr Fin2
  end.


Instance Encode_Tok : codable sigTok Tok :=
  {|
    encode x := encode (Tok_to_sum x)
  |}.

(** This makes sure that the numbers are encoded with the "inner" [bool], so we don't have to annotate the encoding in [MatchTok_Rel] explicitely. *)
Instance Encode_Tok_nat : codable sigTok nat := (Encode_map Encode_nat (Retract_inr _ _)).


Definition MatchTok : { M : mTM sigTok^+ 1 & states M -> Fin.t 4 } :=
  If (MatchSum _ _)
     (mono_Nop Fin3)
     (ChangePartition
        (ChangeAlphabet (MatchFin (FinType(EqType(Fin.t 3)))) _)
        (Fin.L 1))
.

Definition MatchTok_Rel : pRel sigTok^+ (FinType (EqType (Fin.t 4))) 1 :=
  fun tin '(yout, tout) =>
    forall t : Tok, tin[@Fin0] ≃ t ->
               match t with
               | appT => tout[@Fin0] ≃ Fin0 /\ yout = Fin0
               | lamT => tout[@Fin0] ≃ Fin1 /\ yout = Fin1
               | retT => tout[@Fin0] ≃ Fin2 /\ yout = Fin2
               | varT n => tout[@Fin0] ≃ n /\ yout = Fin3
               end
.


Lemma MatchTok_Sem : MatchTok ⊨c(11) MatchTok_Rel.
Proof.
  eapply RealiseIn_monotone.
  { unfold MatchTok. repeat TM_Correct.
    - apply MatchSum_Sem with (X := nat) (Y := Fin.t 3).
    - unfold ChangeAlphabet. apply Lift_RealiseIn. apply MatchFin_Sem.
  }
  { cbn. omega. }
  {
    intros tin (yout, tout) H. intros t HEncT. TMSimp.
    destruct H; TMSimp.
    { (* "Then" branche *)
      specialize (H t HEncT).
      destruct t; cbn in *; destruct H as (H&H'); inv H'.
      split; auto.
    }
    { (* "Else" branche *)
      specialize (H t HEncT). simpl_tape in H1.
      destruct t; cbn in *; destruct H as (H&H'); inv H'.
      - specialize (H1 Fin0).
        destruct H1 as (H1 % contains_translate_tau2 &->); auto.
        apply contains_translate_tau1. eapply tape_contains_ext with (1 := H). cbn; auto.
      - specialize (H1 Fin1).
        destruct H1 as (H1 % contains_translate_tau2 &->); auto.
        apply contains_translate_tau1. eapply tape_contains_ext with (1 := H). cbn; auto.
      - specialize (H1 Fin2).
        destruct H1 as (H1 % contains_translate_tau2 &->); auto.
        apply contains_translate_tau1. eapply tape_contains_ext with (1 := H). cbn; auto.
    }
  }
Qed.


(** Constructors *)

(** Use [WriteValue] for [appT], [lamT], and [retT] *)
Definition Constr_appT : { M : mTM sigTok^+ 1 & states M -> unit } := WriteValue _ appT.
Definition Constr_lamT : { M : mTM sigTok^+ 1 & states M -> unit } := WriteValue _ lamT.
Definition Constr_retT : { M : mTM sigTok^+ 1 & states M -> unit } := WriteValue _ retT.


Definition Constr_varT : { M : mTM sigTok^+ 1 & states M -> unit } := Constr_inl _ _.

Definition Constr_varT_Rel : pRel sigTok^+ (FinType (EqType unit)) 1 :=
  Mk_R_p (ignoreParam (fun tin tout => forall x : nat, tin ≃ x -> tout ≃ varT x)).

Lemma Constr_varT_Sem : Constr_varT ⊨c(3) Constr_varT_Rel.
Proof.
  eapply RealiseIn_monotone.
  - unfold Constr_varT. apply Constr_inl_Sem.
  - reflexivity.
  - intros tin ((), tout) H. intros n HEncN. TMSimp. now apply tape_contains_ext with (1 := H n HEncN).
Qed.