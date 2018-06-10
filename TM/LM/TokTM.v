Require Import ProgrammingTools.
Require Import TM.Code.MatchNat TM.Code.MatchSum TM.Code.MatchFin.

Require Import TM.LM.Definitions.

Inductive ATok : Type := retAT | lamAT | appAT.

Coercion ATok2Tok (a : ATok) : Tok :=
  match a with
  | retAT => retT
  | lamAT => lamT
  | appAT => appT
  end.


Instance ATok_dec : eq_dec ATok.
Proof. intros x y; hnf. decide equality. Defined.

Instance ATok_fin : finTypeC (EqType ATok).
Proof. split with (enum := [retAT; lamAT; appAT]). intros [ | | ]; cbn; reflexivity. Defined.

Instance ATok_inhab : inhabitedC ATok := ltac:(repeat constructor).

Instance Encode_ATok : codable (FinType(EqType ATok)) ATok := Encode_Fin (FinType(EqType(ATok))).


Coercion Tok_to_sum (t : Tok) : (nat + ATok) :=
  match t with
  | varT x => inl x
  | appT => inr appAT
  | lamT => inr lamAT
  | retT => inr retAT
  end.

(*
Coercion Tok_to_sum (t : Tok) : (nat + Fin.t 3) :=
  match t with
  | varT x => inl x
  | appT => inr Fin0
  | lamT => inr Fin1
  | retT => inr Fin2
  end.
*)

(*
Definition sigTok := FinType (EqType (sigSum (FinType (EqType (sigNat))) (FinType(EqType(Fin.t 3))))).
*)
Definition sigTok := FinType (EqType (sigSum (FinType (EqType (sigNat))) (FinType(EqType(ATok))))).
Arguments sigTok : simpl never.

Instance Encode_Tok : codable sigTok Tok :=
  {|
    encode x := encode (Tok_to_sum x)
  |}.



Definition MatchTok : { M : mTM sigTok^+ 1 & states M -> option ATok } :=
  If (MatchSum _ _)
     (mono_Nop None)
     (MATCH (ChangeAlphabet (MatchFin (FinType(EqType(ATok)))) _)
            (fun (i:ATok) => Return (ResetEmpty1 _) (Some i))).


Definition MatchTok_Rel : pRel sigTok^+ (FinType (EqType (option ATok))) 1 :=
  fun tin '(yout, tout) =>
    forall t : Tok, tin[@Fin0] ≃ t ->
               match t with
               | appT => isRight tout[@Fin0] /\ yout = Some appAT
               | lamT => isRight tout[@Fin0] /\ yout = Some lamAT
               | retT => isRight tout[@Fin0] /\ yout = Some retAT
               | varT n => tout[@Fin0] ≃ n /\ yout = None
               end
.


Lemma MatchTok_Sem : MatchTok ⊨c(15) MatchTok_Rel.
Proof.
  eapply RealiseIn_monotone.
  { unfold MatchTok. repeat TM_Correct.
    - apply Lift_RealiseIn. apply MatchFin_Sem.
    - apply ResetEmpty1_Sem with (X := ATok).
    - apply ResetEmpty1_Sem with (X := ATok).
    - apply ResetEmpty1_Sem with (X := ATok).
  }
  { cbn. Unshelve. 4,5,7: reflexivity. cbv. all: omega. }
  {
    intros tin (yout, tout) H. intros t HEncT. TMSimp.
    destruct H; TMSimp.
    { (* "Then" branche *)
      specialize (H t HEncT).
      destruct t; cbn in *; destruct H as (H&H'); inv H'.
      split; auto.
    }
    { (* "Else" branche *)
      rename H into HMatchSum; rename H0 into HMatchFin; rename H1 into HMove1. simpl_tape in HMatchFin. 
      specialize (HMatchSum t HEncT).
      unfold sigTok in *.
      destruct t; cbn in *; destruct HMatchSum as (HMatchSum&HMatchSum'); inv HMatchSum';
        specialize (HMatchFin _ (contains_translate_tau1 HMatchSum)) as (HMatchFin % contains_translate_tau2 & ->);
        TMSimp; eauto.
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


Arguments MatchTok : simpl never.
Arguments Constr_appT : simpl never.
Arguments Constr_lamT : simpl never.
Arguments Constr_retT : simpl never.
Arguments Constr_varT : simpl never.

(* TODO: TM_Correct *)