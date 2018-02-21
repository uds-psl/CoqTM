(* Export the submodules *)
Require Export Match If SequentialComposition While.


(* Simple operator to fix the parameter *)

Section Return.

  Variable (sig : finType) (n : nat).
  Variable F : finType.
  Variable pM : { M : mTM sig n & states M -> F }.
  Variable F' : finType.
  Variable p : F'.

  Definition Return := (projT1 pM; fun _ => p).

  Lemma Return_WRealise R :
    pM ⊫ R ->
    Return ⊫ (⋃_f (R |_ f)) ||_ p.
  Proof. intros. intros tin k outc HLoop. hnf. split; hnf; eauto. exists (projT2 pM (cstate outc)). hnf. eauto. Qed.

  Lemma Return_RealiseIn R k :
    pM ⊨c(k) R ->
    Return ⊨c(k) (⋃_f (R |_ f)) ||_ p.
  Proof. firstorder. Qed.

  Lemma Return_Terminates T :
    projT1 pM ↓ T ->
    projT1 Return ↓ T.
  Proof. firstorder. Qed.

End Return.

Arguments Return : simpl never.



(** * Tactical support *)


(** Helper tactics for match *)

(* Database for additional one-parameter tactics that destruct the given arguments and shelves the
 * sub-goals *)
Smpl Create smpl_destruct_shelve.

Ltac destruct_shelve e :=
  cbn in e;
  idtac "Input:";
  print_type e;
  idtac "Output:";
  print_goal_cbn; 
  match type of e with
  | bool => destruct e; shelve; idtac "tam"
  | move => destruct e; shelve
  | (_ + _) % type =>
    idtac "I am sum!";
    (* ALWAYS use fresh, ****NEVER EVER**** do something like destruct e as [?X | ?Y] !!!!!!! *)
    let X := fresh "X" in
    let Y := fresh "Y" in
    destruct e as [X | Y]; [destruct_shelve X | destruct_shelve Y]
  | @option _ =>
    idtac "I am optional!";
    let X := fresh "X" in
    let Y := fresh "Y" in
    destruct e as [X | ]; [print_type X; destruct_shelve X | shelve]
  | _ * _ =>
    let X := fresh "X" in
    let Y := fresh "Y" in
    destruct e as (X, Y); destruct_shelve X; destruct_shelve Y
  | _ => smpl smpl_destruct_shelve e
  | _ => idtac "Could not destruct any more"; shelve
  end.

Eval simpl in ltac:(intros ?e; destruct_shelve e) : (option (bool + (bool + (nat + nat)))) -> nat.


Ltac smpl_match_case_solve_RealiseIn :=
  eapply RealiseIn_monotone'; [ | shelve].

Ltac smpl_match_RealiseIn :=
  match goal with
  | [ |- MATCH ?M1 ?M2 ⊨c(?k1) ?R] =>
    is_evar R;
    let tM2 := type of M2 in
    match tM2 with
    | ?F -> _ =>
      eapply (Match_RealiseIn
                (F := FinType(EqType F))
                (R2 := ltac:(now (intros ?e; destruct_shelve e))));
      [
        smpl_match_case_solve_RealiseIn
      | intros ?e; repeat destruct _; smpl_match_case_solve_RealiseIn
      ]
    end
  end.


Ltac smpl_match_WRealise :=
  match goal with
  | [ |- MATCH ?M1 ?M2 ⊫ ?R] =>
    is_evar R;
    let tM2 := type of M2 in
    match tM2 with
    | ?F -> _ =>
      eapply (Match_WRealise
                (F := FinType(EqType F))
                (R2 := ltac:(now (intros ?e; destruct_shelve e))));
      [
      | intros ?e; repeat destruct _
      ]
    end
  end.


(** Put stuff together *)

Ltac smpl_TM_Combinators :=
  match goal with
  | [ |- MATCH _ _ ⊫ _] => smpl_match_WRealise
  | [ |- MATCH _ _ ⊨c(_) _] => smpl_match_RealiseIn
  | [ |- projT1 (MATCH _ _) ↓ _] => eapply Match_TerminatesIn
  | [ |- If _ _ _ ⊫ _] => eapply If_WRealise
  | [ |- If _ _ _ ⊨c(_) _] => eapply If_RealiseIn
  | [ |- projT1 (If _ _ _) ↓ _] => eapply If_TerminatesIn
  | [ |- Seq _ _ ⊫ _] => eapply Seq_WRealise
  | [ |- Seq _ _ ⊨c(_) _] => eapply Seq_RealiseIn
  | [ |- projT1 (Seq _ _) ↓ _] => eapply Seq_TerminatesIn
  | [ |- WHILE _ ⊫ _] => eapply While_WRealise
  | [ |- projT1 (WHILE _) ↓ _] => eapply While_TerminatesIn
  | [ |- Return _ _ ⊫ _] => eapply Return_WRealise
  | [ |- Return _ _ ⊨c(_) _] => eapply Return_RealiseIn
  | [ |- projT1 (Return _ _) ↓ _] => eapply Return_Terminates
  end.

Smpl Add smpl_TM_Combinators : TM_Correct.