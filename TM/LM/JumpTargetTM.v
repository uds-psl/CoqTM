Require Import HeapTM.
Require Import MatchList.
Require Import ListTM.

Local Arguments plus : simpl never.
Local Arguments mult : simpl never.

Fixpoint jumpTarget (k:nat) (Q:Pro) (P:Pro) : option (Pro*Pro) :=
  match P with
  | retT :: P' => match k with
                 | 0 => Some (Q,P')
                 | S k' => jumpTarget k' (Q++[retT]) P'
                 end
  | lamT :: P' => jumpTarget (S k) (Q++[lamT]) P'
  | t :: P' => jumpTarget k (Q++[t]) P' (* either [varT n] or [appT] *)
  | [] => None
  end.


(** The [JumpTarget] machine only operates on programs. Consequently, the alphabet of [JumpTarget] is just [sigPro]. [JumpTarget] will also assume, that the result of [jumpTarget] is [Some]. *)


(** This is the only way we can encode [nat] on [sigPro]: as a variable token. *)
Definition retr_nat_prog : Retract sigNat sigPro := Retract_sigList_X _.


(** append a token to the token list *)
Definition App_Tokens : pTM sigPro^+ (FinType(EqType unit)) 2 :=
  App' _ @ [|Fin0; Fin1|];;
  MoveValue _ @ [|Fin1; Fin0|].

Definition App_Tokens_Rel : pRel sigPro^+ (FinType(EqType unit)) 2 :=
  ignoreParam (
      fun tin tout =>
        forall (Q Q' : list Tok),
          tin[@Fin0] ≃ Q ->
          tin[@Fin1] ≃ Q' ->
          tout[@Fin0] ≃ Q ++ Q' /\
          isRight tout[@Fin1]
    ).

Lemma App_Tokens_Realise : App_Tokens ⊨ App_Tokens_Rel.
Proof.
  eapply Realise_monotone.
  { unfold App_Tokens. repeat TM_Correct.
    - apply App'_Realise with (X := Tok).
    - apply MoveValue_Realise with (X := Pro).
  }
  {
    intros tin ((), tout) H. intros Q Q' HEncQ HEncQ'.
    TMSimp. modpon H. modpon H0. auto.
  }
Qed.


Definition App_Tokens_steps (Q Q': Pro) := 1 + App'_steps _ Q + MoveValue_steps _ _ (Q ++ Q') Q.

Definition App_Tokens_T : tRel sigPro^+ 2 :=
  fun tin k => exists (Q Q' : list Tok), tin[@Fin0] ≃ Q /\ tin[@Fin1] ≃ Q' /\ App_Tokens_steps Q Q' <= k.

Lemma App_Tokens_Terminates : projT1 App_Tokens ↓ App_Tokens_T.
Proof.
  eapply TerminatesIn_monotone.
  { unfold App_Tokens. repeat TM_Correct.
    - apply App'_Realise with (X := Tok).
    - apply App'_Terminates with (X := Tok).
    - apply MoveValue_Terminates with (X := Pro) (Y := Pro).
  }
  {
    intros tin k (Q&Q'&HEncQ&HEncQ'&Hk).
    exists (App'_steps _ Q), (MoveValue_steps _ _ (Q++Q') Q); cbn; repeat split; try omega.
    hnf; cbn. eauto. now rewrite Hk.
    intros tmid () (HApp&HInjApp); TMSimp. modpon HApp.
    exists (Q++Q'), Q. repeat split; eauto.
  }
Qed.
    

(** append a token to the token list *)
Definition App_ATok (t : ATok) : pTM sigPro^+ (FinType(EqType unit)) 2 :=
  WriteValue _ [ATok2Tok t] @ [|Fin1|];;
  App_Tokens.

Definition App_ATok_Rel (t : ATok) : pRel sigPro^+ (FinType(EqType unit)) 2 :=
  ignoreParam (
      fun tin tout =>
        forall (Q : list Tok),
          tin[@Fin0] ≃ Q ->
          isRight tin[@Fin1] ->
          tout[@Fin0] ≃ Q ++ [ATok2Tok t] /\
          isRight tout[@Fin1]
    ).

Lemma App_ATok_Realise t : App_ATok t ⊨ App_ATok_Rel t.
Proof.
  eapply Realise_monotone.
  { unfold App_ATok. repeat TM_Correct.
    - apply App_Tokens_Realise.
  }
  {
    intros tin ((), tout) H. intros Q HENcQ HRight1.
    TMSimp. modpon H0. auto.
  }
Qed.

Definition App_ATok_steps (Q: Pro) (t: ATok) := 1 + WriteValue_steps _ [ATok2Tok t] + App_Tokens_steps Q [ATok2Tok t].

Definition App_ATok_T (t: ATok) : tRel sigPro^+ 2 :=
  fun tin k => exists (Q: list Tok), tin[@Fin0] ≃ Q /\ isRight tin[@Fin1] /\ App_ATok_steps Q t <= k.

Lemma App_ATok_Terminates (t: ATok) : projT1 (App_ATok t) ↓ App_ATok_T t.
Proof.
  eapply TerminatesIn_monotone.
  { unfold App_ATok. repeat TM_Correct.
    - apply App_Tokens_Terminates.
  }
  {
    intros tin k. intros (Q&HEncQ&HRight&Hk).
    exists (WriteValue_steps _ [ATok2Tok t]), (App_Tokens_steps Q [ATok2Tok t]). cbn; repeat split; try omega.
    now rewrite Hk.
    intros tmid () (HWrite&HInjWrite); hnf; cbn; TMSimp. modpon HWrite. eauto.
  }
Qed.



(** Add a singleton list of tokes to [Q] *)
Definition App_Tok : pTM sigPro^+ (FinType(EqType unit)) 3 :=
  Constr_nil _ @ [|Fin2|];;
  Constr_cons _@ [|Fin2; Fin1|];;
  App_Tokens @ [|Fin0; Fin2|];;
  Reset _ @ [|Fin1|].

Definition App_Tok_Rel : pRel sigPro^+ (FinType(EqType unit)) 3 :=
  ignoreParam (
      fun tin tout =>
        forall (Q : list Tok) (t : Tok),
          tin[@Fin0] ≃ Q ->
          tin[@Fin1] ≃ t ->
          isRight tin[@Fin2] ->
          tout[@Fin0] ≃ Q ++ [t] /\
          isRight tout[@Fin1] /\
          isRight tout[@Fin2]
    ).


Lemma App_Tok_Realise : App_Tok ⊨ App_Tok_Rel.
Proof.
  eapply Realise_monotone.
  { unfold App_Tok. repeat TM_Correct.
    - apply App_Tokens_Realise.
    - apply Reset_Realise with (X := Tok).
  }
  { intros tin ((), tout) H. cbn. intros Q t HEncQ HEncT HRight.
    unfold sigPro, sigTok in *. TMSimp.
    rename H into HNil, H0 into HCons, H1 into HApp, H2 into HReset.
    modpon HNil. modpon HCons. modpon HApp. modpon HReset. repeat split; auto.
  }
Qed.

Definition App_Tok_steps (Q: Pro) (t:Tok) :=
  3 + Constr_nil_steps + Constr_cons_steps _ t + App_Tokens_steps Q [t] + Reset_steps _ t.

Definition App_Tok_T : tRel sigPro^+ 3 :=
  fun tin k => exists (Q: list Tok) (t: Tok), tin[@Fin0] ≃ Q /\ tin[@Fin1] ≃ t /\ isRight tin[@Fin2] /\ App_Tok_steps Q t <= k.

Lemma App_Tok_Terminates : projT1 App_Tok ↓ App_Tok_T.
Proof.
  eapply TerminatesIn_monotone.
  { unfold App_Tok. repeat TM_Correct.
    - apply App_Tokens_Realise.
    - apply App_Tokens_Terminates.
    - apply Reset_Terminates with (X := Tok).
  }
  {
    intros tin k (Q&t&HEncQ&HEncT&HRight&Hk). unfold App_Tok_steps in Hk. 
    exists (Constr_nil_steps), (1 + Constr_cons_steps _ t + 1 + App_Tokens_steps Q [t] + Reset_steps _ t). cbn. repeat split; try omega.
    intros tmid () (HNil&HInjNil); TMSimp. modpon HNil.
    exists (Constr_cons_steps _ t), (1 + App_Tokens_steps Q [t] + Reset_steps _ t). cbn. repeat split; try omega.
    eauto. now rewrite !Nat.add_assoc.
    unfold sigPro in *. intros tmid0 () (HCons&HInjCons); TMSimp. modpon HCons.
    exists (App_Tokens_steps Q [t]), (Reset_steps _ t). cbn. repeat split; try omega.
    hnf; cbn. do 2 eexists; repeat split; eauto. reflexivity.
    intros tmid1 _ (HApp&HInjApp); TMSimp. modpon HApp.
    eexists. split; eauto. now setoid_rewrite Reset_steps_comp.
  }
Qed.



Definition JumpTarget_Step : pTM sigPro^+ (FinType(EqType (bool*unit))) 5 :=
  Inject (MatchList sigTok_fin) [|Fin0; Fin3|];;
  MATCH (Inject (ChangeAlphabet MatchTok _) [|Fin3|])
         (fun t : option ATok =>
            match t with
            | Some retAT =>
              If (MatchNat ⇑ retr_nat_prog @ [|Fin2|])
                 (Return (App_ATok retAT @ [|Fin1; Fin4|]) (true, tt)) (* continue *)
                 (Nop (false, tt)) (* return *)
            | Some lamAT =>
              Return (Constr_S ⇑ retr_nat_prog @ [|Fin2|];;
                      App_ATok lamAT @ [|Fin1; Fin4|])
                     (true,default) (* continue *)
            | Some appAT =>
              Return (App_ATok appAT @ [|Fin1;Fin4|])
                     (true,default) (* continue *)
            | None => (* Variable *)
              Return (Constr_varT ⇑ _ @ [|Fin3|];;
                      App_Tok @ [|Fin1; Fin3; Fin4|])
                     (true,default) (* continue *)
            end)
.


Definition JumpTarget_Step_Rel : pRel sigPro^+ (FinType(EqType(bool*unit))) 5 :=
  ignoreSecond (
      fun tin '(yout, tout) =>
        forall (P Q : Pro) (k : nat) (t : Tok),
          tin[@Fin0] ≃ t :: P ->
          tin[@Fin1] ≃ Q ->
          tin[@Fin2] ≃ k ->
          isRight tin[@Fin3] -> isRight tin[@Fin4] ->
          match yout, t with
          | _, retT =>
            match yout, k with
            | false, O => (* return *)
              tout[@Fin0] ≃ P /\
              tout[@Fin1] ≃ Q /\
              tout[@Fin2] ≃ 0
            | true, S k' => (* continue *)
              tout[@Fin0] ≃ P /\
              tout[@Fin1] ≃ Q ++ [retT] /\
              tout[@Fin2] ≃ k'
            | _, _ => False (* not the case *)
            end
          | true, lamT => (* continue *)
            tout[@Fin0] ≃ P /\
            tout[@Fin1] ≃ Q ++ [lamT] /\
            tout[@Fin2] ≃ S k
          | true, t => (* continue *)
            tout[@Fin0] ≃ P /\
            tout[@Fin1] ≃ Q ++ [t] /\
            tout[@Fin2] ≃ k
          | _, _ => False (* not the case *)
          end /\
          isRight tout[@Fin3] /\
          isRight tout[@Fin4]
    ).


Lemma JumpTarget_Step_Realise : JumpTarget_Step ⊨ JumpTarget_Step_Rel.
Proof.
  eapply Realise_monotone.
  { unfold JumpTarget_Step. repeat TM_Correct.
    - eapply RealiseIn_Realise. apply MatchTok_Sem.
    - apply App_ATok_Realise.
    - apply App_ATok_Realise.
    - apply App_ATok_Realise.
    - eapply RealiseIn_Realise. apply Constr_varT_Sem.
    - apply App_Tok_Realise.
  }
  {
    intros tin ((yout, ()), tout) H. cbn. intros P Q k t HEncP HEncQ HEncK HInt3 HInt4.
    unfold sigPro in *. TMSimp. rename H into HMatchList, H0 into HMatchTok, H1 into HCase.
    modpon HMatchList. destruct ymid; auto; modpon HMatchList.
    modpon HMatchTok.
    destruct ymid0 as [ [ | | ] | ]; try destruct t; auto; simpl_surject; TMSimp.
    { (* t = retT *)
      destruct HCase; TMSimp.
      { (* k = S k' *) rename H into HMatchNat, H0 into HReturn, H1 into HApp.
        modpon HMatchNat. destruct k as [ | k']; auto; modpon HMatchNat.
        inv HReturn.
        modpon HApp.
        repeat split; auto.
      }
      { (* k = 0 *) rename H into HMatchNat, H0 into HReturn.
        modpon HMatchNat. destruct k as [ | k']; auto; modpon HMatchNat.
        inv HReturn.
        repeat split; auto.
      }
    }
    { (* t = lamT *) rename H into HReturn, H0 into HS, H1 into HApp.
      inv HReturn.
      modpon HS.
      modpon HApp.
      repeat split; auto.
    }
    { (* t = appT *) rename H into HReturn, H0 into HApp.
      inv HReturn.
      modpon HApp.
      repeat split; auto.
    }
    { (* t = varT *) rename H into HReturn, H0 into HVar, H1 into HApp.
      inv HReturn.
      modpon HVar.
      modpon HApp.
      repeat split; auto.
    }
  }
Qed.


Definition JumpTarget_Step_steps' (Q: Pro) (k: nat) (t: Tok) :=
  match t with
  | retT =>
    match k with
    | S _ => 1 + MatchNat_steps + App_ATok_steps Q retAT
    | 0 => 1 + MatchNat_steps
    end
  | lamT => 1 + Constr_S_steps + App_ATok_steps Q lamAT
  | appT => App_ATok_steps Q appAT
  | varT n => 1 + Constr_varT_steps + App_Tok_steps Q t
  end.

Definition JumpTarget_Step_steps (Q: Pro) (k: nat) (t: Tok) :=
  2 + MatchList_steps_cons _ t + MatchTok_steps + JumpTarget_Step_steps' Q k t.

Definition JumpTarget_Step_T : tRel sigPro^+ 5 :=
  fun tin steps => (* Warning: I have to use another variable for the steps, since [k] is used. *)
    exists (P Q : Pro) (k : nat) (t : Tok),
      tin[@Fin0] ≃ t :: P /\
      tin[@Fin1] ≃ Q /\
      tin[@Fin2] ≃ k /\
      isRight tin[@Fin3] /\ isRight tin[@Fin4] /\
      JumpTarget_Step_steps Q k t <= steps.

Lemma JumpTarget_Step_Terminates : projT1 JumpTarget_Step ↓ JumpTarget_Step_T.
Proof.
  eapply TerminatesIn_monotone.
  { unfold JumpTarget_Step. repeat TM_Correct.
    - eapply RealiseIn_Realise. apply MatchTok_Sem.
    - eapply RealiseIn_terminatesIn. apply MatchTok_Sem.
    - apply App_ATok_Terminates.
    - apply App_ATok_Terminates.
    - apply App_ATok_Terminates.
    - eapply RealiseIn_Realise. apply Constr_varT_Sem.
    - eapply RealiseIn_terminatesIn. apply Constr_varT_Sem.
    - apply App_Tok_Terminates.
  }
  {
    intros tin steps (P&Q&k&t&HEncP&HEncQ&HEncK&HRight3&HRight4&Hk). unfold JumpTarget_Step_steps in Hk. cbn in *.
    unfold sigPro in *.
    exists (MatchList_steps _ (t::P)), (1 + MatchTok_steps + JumpTarget_Step_steps' Q k t). cbn; repeat split; try omega. eauto.
    intros tmid bmatchlist (HMatchList&HMatchListInj); TMSimp. modpon HMatchList. destruct bmatchlist; auto; modpon HMatchList.
    exists (MatchTok_steps), (JumpTarget_Step_steps' Q k t). cbn; repeat split; try omega.
    intros tmid1 ytok (HMatchTok&HMatchTokInj); TMSimp. modpon HMatchTok.
    destruct ytok as [ [ | | ] | ]; destruct t; auto; simpl_surject; TMSimp.
    { (* t = retT *)
      exists MatchNat_steps.
      destruct k as [ | k'].
      - (* k = 0 *)
        exists 0. repeat split; try omega.
        intros tmid2 bMatchNat (HMatchNat&HMatchNatInj); TMSimp. modpon HMatchNat. destruct bMatchNat; auto.
      - (* k = S k' *)
        exists (App_ATok_steps Q retAT). repeat split; try omega.
        intros tmid2 bMatchNat (HMatchNat&HMatchNatInj); TMSimp. modpon HMatchNat. destruct bMatchNat; auto. hnf; cbn. eauto.
    }
    { (* t = lamT *)
      exists (Constr_S_steps), (App_ATok_steps Q lamAT). repeat split; try omega.
      intros tmid2 () (HS&HSInj); TMSimp. modpon HS. hnf; cbn. eauto.
    }
    { (* t = appT *) hnf; cbn; eauto. }
    { (* t = varT n *)
      exists (Constr_varT_steps), (App_Tok_steps Q (varT n)). repeat split; try omega.
      intros tmid2 H (HVarT&HVarTInj); TMSimp. modpon HVarT. hnf; cbn. eauto 6.
    }
  }
Qed.



Fixpoint jumpTarget_k (k:nat) (Q:Pro) (P:Pro) : nat :=
  match P with
  | retT :: P' => match k with
                 | 0 => 0
                 | S k' => jumpTarget_k k' (Q++[retT]) P'
                 end
  | lamT :: P' => jumpTarget_k (S k) (Q++[lamT]) P'
  | t :: P'    => jumpTarget_k k (Q++[t]) P' (* either [varT n] or [appT] *)
  | []         => k
  end.


Definition JumpTarget_Loop := WHILE JumpTarget_Step.


Definition JumpTarget_Loop_Rel : pRel sigPro^+ (FinType(EqType unit)) 5 :=
  fun tin '(yout, tout) =>
    forall (P Q : Pro) (k : nat) (P' Q' : Pro),
      jumpTarget k Q P = Some (Q', P') ->
      tin[@Fin0] ≃ P ->
      tin[@Fin1] ≃ Q ->
      tin[@Fin2] ≃ k ->
      isRight tin[@Fin3] -> isRight tin[@Fin4] ->
      tout[@Fin0] ≃ P' /\
      tout[@Fin1] ≃ Q' /\
      tout[@Fin2] ≃ jumpTarget_k k Q P /\
      isRight tout[@Fin3] /\ isRight tout[@Fin4].



Lemma JumpTarget_Loop_Realise : JumpTarget_Loop ⊨ JumpTarget_Loop_Rel.
Proof.
  eapply Realise_monotone.
  { unfold JumpTarget_Loop. repeat TM_Correct.
    - apply JumpTarget_Step_Realise.
  }
  {
    apply WhileInduction; intros; intros P Q k P' Q' HJumpSome HEncP HEncQ HEncK HRight3 HRight4; cbn in *.
    {
      destruct P as [ | t P]; cbn in *; try congruence.
      modpon HLastStep.
      destruct t; auto. destruct k; auto; modpon HLastStep. inv HJumpSome.
      repeat split; auto.
    }
    {
      destruct P as [ | t P]; cbn in *; try congruence.
      modpon HStar.
      destruct t; modpon HStar.
      - (* t = varT *) modpon HLastStep. repeat split; auto.
      - (* t = appT *) modpon HLastStep. repeat split; auto.
      - (* t = lamT *) modpon HLastStep. repeat split; auto.
      - (* t = varT k, k must be S k'*)
        destruct k as [ | k']; auto; modpon HStar.
        modpon HLastStep.
        repeat split; auto.
    }
  }
Qed.

(*
  match t with
  | retT =>
    match k with
    | S _ => 1 + MatchNat_steps + App_ATok_steps Q retAT
    | 0 => 1 + MatchNat_steps
    end
  | lamT => 1 + Constr_S_steps + App_ATok_steps Q lamAT
  | appT => App_ATok_steps Q appAT
  | varT n => 1 + Constr_varT_steps + App_Tok_steps Q t
  end.
*)


Fixpoint JumpTarget_Loop_steps (P Q: Pro) (k: nat) : nat :=
  match P with
  | nil => 0 (* underspecified *)
  | t :: P' =>
    match t with
    | retT =>
      match k with
      | S k' => 1 + JumpTarget_Step_steps Q k t + JumpTarget_Loop_steps P' (Q++[t]) k'
      | 0 =>        JumpTarget_Step_steps Q k retT (* terminal case *)
      end
    | lamT =>   1 + JumpTarget_Step_steps Q k t + JumpTarget_Loop_steps P' (Q++[t]) (S k)
    | appT =>   1 + JumpTarget_Step_steps Q k t + JumpTarget_Loop_steps P' (Q++[t]) k
    | varT n => 1 + JumpTarget_Step_steps Q k t + JumpTarget_Loop_steps P' (Q++[t]) k
    end
  end.

Definition JumpTarget_Loop_T : tRel sigPro^+ 5 :=
  fun tin steps =>
    exists (P Q : Pro) (k : nat) (P' Q' : Pro),
      jumpTarget k Q P = Some (Q', P') /\
      tin[@Fin0] ≃ P /\
      tin[@Fin1] ≃ Q /\
      tin[@Fin2] ≃ k /\
      isRight tin[@Fin3] /\ isRight tin[@Fin4] /\
      JumpTarget_Loop_steps P Q k <= steps.


Lemma JumpTarget_Loop_Terminates : projT1 JumpTarget_Loop ↓ JumpTarget_Loop_T.
Proof.
  unfold JumpTarget_Loop. repeat TM_Correct.
  { apply JumpTarget_Step_Realise. }
  { apply JumpTarget_Step_Terminates. }
  {
    intros tin steps. intros (P&Q&k&P'&Q'&HJump&HEncP&HEncQ&HEncK&HRight3&HRight4&Hk).
    destruct P as [ | t P]; cbn in *. now inv HJump.
    exists (JumpTarget_Step_steps Q k t). repeat split. hnf; cbn; eauto 10.
    intros b () tmid HStep. modpon HStep. destruct b.
    { (* recursion cases *)
      destruct t; modpon HStep.
      - (* t = varT n *)
        exists (JumpTarget_Loop_steps P (Q++[varT n]) k). split.
        + hnf. do 5 eexists; repeat split; eauto.
        + assumption.
      - (* t = appT *)
        exists (JumpTarget_Loop_steps P (Q++[appT]) k). split.
        + hnf. do 5 eexists; repeat split; eauto.
        + assumption.
      - (* t = lamT *)
        exists (JumpTarget_Loop_steps P (Q++[lamT]) (S k)). split.
        + hnf. do 5 eexists; repeat split; eauto.
        + assumption.
      - (* t = retT, k = S k' *)
        destruct k as [ | k']; auto; modpon HStep.
        exists (JumpTarget_Loop_steps P (Q++[retT]) k'). split.
        + hnf. do 5 eexists; repeat split; eauto.
        + assumption.
    }
    { (* termination case, i.e. t=retT and k=0 *)
      destruct t; auto. destruct k; auto.
    }
  }
Qed.

                            
Definition JumpTarget : pTM sigPro^+ unit 5 :=
  WriteValue _ (@nil Tok) @ [|Fin1|];;
  WriteValue _ 0 @ [|Fin2|];;
  JumpTarget_Loop;;
  Reset _ @ [|Fin2|].


Definition JumpTarget_Rel : pRel sigPro^+ unit 5 :=
  fun tin '(yout, tout) =>
    forall (P : Pro) (P' Q' : Pro),
      jumpTarget 0 nil P = Some (Q', P') ->
      tin[@Fin0] ≃ P ->
      isRight tin[@Fin1] ->
      (forall i : Fin.t 3, isRight tin[@FinR 2 i : Fin.t 5]) ->
      tout[@Fin0] ≃ P' /\
      tout[@Fin1] ≃ Q' /\
      (forall i : Fin.t 3, isRight tout[@FinR 2 i : Fin.t 5]).

Lemma JumpTarget_Realise : JumpTarget ⊨ JumpTarget_Rel.
Proof.
  eapply Realise_monotone.
  { unfold JumpTarget. repeat TM_Correct.
    - apply JumpTarget_Loop_Realise.
    - apply Reset_Realise with (X := nat).
  }
  {
    intros tin ((), tout) H. cbn. intros P P' Q' HJump HEncP HOut HInt.
    TMSimp ( unfold sigPro, sigTok in * ).
    rename H into HWriteNil, H0 into HWriteO, H1 into HLoop, H2 into HReset.
    modpon HWriteNil.
    modpon HWriteO.
    modpon HLoop.
    modpon HReset.
    repeat split; auto. intros i; destruct_fin i; TMSimp_goal; auto.
  }
Qed.


Definition JumpTarget_steps (P : Pro) :=
  3 + WriteValue_steps _ (@nil Tok) + WriteValue_steps _ 0 + JumpTarget_Loop_steps P nil 0 + Reset_steps _ (jumpTarget_k 0 nil P).


Definition JumpTarget_T : tRel sigPro^+ 5 :=
  fun tin k =>
    exists (P : Pro) (P' Q' : Pro),
      jumpTarget 0 nil P = Some (Q', P') /\
      tin[@Fin0] ≃ P /\
      isRight tin[@Fin1] /\
      (forall i : Fin.t 3, isRight tin[@Fin.R 2 i]) /\
      JumpTarget_steps P <= k.


Lemma JumpTarget_Terminates : projT1 JumpTarget ↓ JumpTarget_T.
Proof.
  eapply TerminatesIn_monotone.
  { unfold JumpTarget. repeat TM_Correct.
    - apply JumpTarget_Loop_Realise.
    - apply JumpTarget_Loop_Terminates.
    - apply Reset_Terminates with (X := nat).
  }
  {
    intros tin k (P&P'&Q'&HJumpSome&HEncP&Hout&HInt&Hk). unfold JumpTarget_steps in Hk.
    exists (WriteValue_steps _ (@nil Tok)), (1 + WriteValue_steps _ 0 + 1 + JumpTarget_Loop_steps P nil 0 + Reset_steps _ (jumpTarget_k 0 nil P)).
    cbn; repeat split; try omega.
    intros tmid () (HWrite&HWriteInj); TMSimp. modpon HWrite.
    exists (WriteValue_steps _ 0), (1 + JumpTarget_Loop_steps P nil 0 + Reset_steps _ (jumpTarget_k 0 nil P)).
    cbn; repeat split; try omega. now setoid_rewrite WriteValue_steps_comp. now rewrite Nat.add_assoc.
    unfold sigPro in *. intros tmid1 () (HWrite'&HWriteInj'); TMSimp. modpon HWrite'.
    exists (JumpTarget_Loop_steps P nil 0), (Reset_steps _ (jumpTarget_k 0 nil P)).
    TMSimp. cbn; repeat split; try omega. cbn in *.
    { hnf. do 5 eexists; repeat split; unfold sigPro in *; unfold eqType_X in *; cbn in *; TMSimp_goal; eauto. }
    intros tmid2 () HLoop. modpon HLoop.
    eexists; repeat split; eauto. now setoid_rewrite Reset_steps_comp.
  }
Qed.
