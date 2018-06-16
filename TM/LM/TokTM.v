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
Definition sigTok := sigSum sigNat ATok.
Definition sigTok_fin := FinType (EqType sigTok).

Instance Encode_Tok : codable sigTok Tok :=
  {|
    encode x := encode (Tok_to_sum x)
  |}.


Definition MatchTok : { M : mTM sigTok^+ 1 & states M -> option ATok } :=
  If (MatchSum _ _)
     (mono_Nop None)
     (ChangePartition (ChangeAlphabet (MatchFin (FinType(EqType(ATok))) ) _) Some)
.
     

Definition MatchTok_Rel : pRel sigTok^+ (FinType (EqType (option ATok))) 1 :=
  fun tin '(yout, tout) =>
    forall t : Tok,
      tin[@Fin0] ≃ t ->
      match yout, t with
      | Some appAT, appT => isRight tout[@Fin0]
      | Some lamAT, lamT => isRight tout[@Fin0]
      | Some retAT, retT => isRight tout[@Fin0]
      | None, varT n => tout[@Fin0] ≃ n
      | _, _ => False
      end
.

Definition MatchTok_steps := 11.

Lemma MatchTok_Sem : MatchTok ⊨c(MatchTok_steps) MatchTok_Rel.
Proof.
  unfold MatchTok_steps. eapply RealiseIn_monotone.
  { unfold MatchTok. repeat TM_Correct.
    - apply Lift_RealiseIn. apply MatchFin_Sem.
  }
  { cbn. Unshelve. reflexivity. }
  {
    intros tin (yout, tout) H. intros t HEncT. TMSimp.
    unfold sigTok in *.
    destruct H; TMSimp.
    { (* "Then" branche *)
      specialize (H t HEncT).
      destruct t; auto.
    }
    { (* "Else" branche *)
      rename H into HMatchSum.
      simpl_tape in *; cbn in *.
      specialize (HMatchSum t HEncT).
      destruct t; cbn in *; auto; modpon H1; subst; auto.
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

Definition Constr_varT_steps := 3.

Lemma Constr_varT_Sem : Constr_varT ⊨c(Constr_varT_steps) Constr_varT_Rel.
Proof.
  unfold Constr_varT_steps. eapply RealiseIn_monotone.
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