(** * Constructors and Deconstructors for Comens *)

Require Import ProgrammingTools.
Require Import TM.Code.CaseNat TM.Code.CaseSum TM.Code.CaseFin.
Require Import TM.LM.Semantics TM.LM.Alphabets.

Definition CaseCom : { M : mTM sigCom^+ 1 & states M -> option ACom } :=
  If (CaseSum _ _)
     (Return Nop None)
     (Relabel (ChangeAlphabet (CaseFin (FinType(EqType(ACom))) ) _) Some)
.
     

Definition CaseCom_Rel : pRel sigCom^+ (FinType (EqType (option ACom))) 1 :=
  fun tin '(yout, tout) =>
    forall t : Com,
      tin[@Fin0] ≃ t ->
      match yout, t with
      | Some appAT, appT => isRight tout[@Fin0]
      | Some lamAT, lamT => isRight tout[@Fin0]
      | Some retAT, retT => isRight tout[@Fin0]
      | None, varT n => tout[@Fin0] ≃ n
      | _, _ => False
      end
.

Definition CaseCom_steps := 11.

Lemma CaseCom_Sem : CaseCom ⊨c(CaseCom_steps) CaseCom_Rel.
Proof.
  unfold CaseCom_steps. eapply RealiseIn_monotone.
  { unfold CaseCom. TM_Correct.
    - apply LiftAlphabet_RealiseIn. apply CaseFin_Sem.
  }
  { cbn. reflexivity. }
  {
    intros tin (yout, tout) H. intros t HEncT. TMSimp.
    unfold sigCom in *.
    destruct H; TMSimp.
    { (* "Then" branche *)
      specialize (H t HEncT).
      destruct t; auto.
    }
    { (* "Else" branche *)
      rename H into HCaseSum.
      simpl_tape in *; cbn in *.
      specialize (HCaseSum t HEncT).
      destruct t; cbn in *; eauto; modpon H1; subst; eauto.
    }
  }
Qed.


(** Constructors *)

(** Use [WriteValue] for [appT], [lamT], and [retT] *)

Definition Constr_ACom (t : ACom) : pTM sigCom^+ unit 1 := WriteValue (encode (ACom2Com t)).
Definition Constr_ACom_Rel (t : ACom) : pRel sigCom^+ unit 1 :=
  Mk_R_p (ignoreParam (fun tin tout => isRight tin -> tout ≃ ACom2Com t)).
Definition Constr_ACom_steps := 7.
Lemma Constr_ACom_Sem t : Constr_ACom t ⊨c(Constr_ACom_steps)Constr_ACom_Rel t.
Proof.
  unfold Constr_ACom_steps. eapply RealiseIn_monotone.
  - unfold Constr_ACom. apply WriteValue_Sem.
  - cbn. destruct t; cbn; reflexivity.
  - intros tin ((), tout) H. cbn in *. auto.
Qed.



Definition Constr_varT : pTM sigCom^+ unit 1 := Constr_inl _ _.
Definition Constr_varT_Rel : pRel sigCom^+ (FinType (EqType unit)) 1 :=
  Mk_R_p (ignoreParam (fun tin tout => forall x : nat, tin ≃ x -> tout ≃ varT x)).
Definition Constr_varT_steps := 3.
Lemma Constr_varT_Sem : Constr_varT ⊨c(Constr_varT_steps) Constr_varT_Rel.
Proof.
  unfold Constr_varT_steps. eapply RealiseIn_monotone.
  - unfold Constr_varT. apply Constr_inl_Sem.
  - reflexivity.
  - intros tin ((), tout) H. intros n HEncN. TMSimp. now apply tape_contains_ext with (1 := H n HEncN).
Qed.


Arguments CaseCom : simpl never.
Arguments Constr_ACom : simpl never.
Arguments Constr_varT : simpl never.