Require Import HeapTM.
Require Import MatchList.


Fixpoint jumpTarget (k:nat) (Q:Pro) (P:Pro) : option (Pro*Pro) :=
  match P with
  | retT :: P' => match k with
                | 0 => Some (Q,P')
                | S k' => jumpTarget k' (Q++[retT]) P'
                end
  | lamT :: P' => jumpTarget (S k) (Q++[lamT]) P'
  | t :: P'    => jumpTarget k (Q++[t]) P' (* either [varT n] or [appT] *)
  | []        => None
  end.





(* This is the only way we can encode [nat] on [sigPro]: as a variable token. *)
Definition retr_nat_prog : Retract sigNat sigPro := Retract_sigList_X _.


(** append a token to the token list *)
Definition App_Tokens : pTM sigPro^+ (FinType(EqType unit)) 3 :=
  Inject (App _) [|Fin0; Fin1; Fin2|];;
  Inject (Reset _) [|Fin0|];;
  Inject (CopyValue _) [|Fin2; Fin0|];;
  Inject (Reset _) [|Fin1|];;
  Inject (Reset _) [|Fin2|].

(** append a token to the token list *)
Definition App_Tokens_Rel : pRel sigPro^+ (FinType(EqType unit)) 3 :=
  ignoreParam (
      fun tin tout =>
        forall (Q Q' : list Tok),
          tin[@Fin0] ≃ Q ->
          tin[@Fin1] ≃ Q' ->
          isRight tin[@Fin2] ->
          tout[@Fin0] ≃ Q ++ Q' /\
          isRight tout[@Fin1] /\
          isRight tout[@Fin2]
    ).


(** append a token to the token list *)
Definition App_ATok (t : ATok) : pTM sigPro^+ (FinType(EqType unit)) 3 :=
  Inject (WriteValue _ [ATok2Tok t]) [|Fin1|];;
  App_Tokens.

Definition App_ATok_Rel (t : ATok) : pRel sigPro^+ (FinType(EqType unit)) 3 :=
  ignoreParam (
      fun tin tout =>
        forall (Q : list Tok),
          tin[@Fin0] ≃ Q ->
          isRight tin[@Fin1] ->
          isRight tin[@Fin2] ->
          tout[@Fin0] ≃ Q ++ [ATok2Tok t] /\
          isRight tout[@Fin1] /\
          isRight tout[@Fin2]
    ).


(** Add a singleton list of tokes to [Q] *)
Definition App_Tok : pTM sigPro^+ (FinType(EqType unit)) 4 :=
  Inject (Constr_nil _) [|Fin3|];;
  Inject (Constr_cons _) [|Fin3; Fin1|];;
  Inject (App_Tokens) [|Fin0; Fin3; Fin2|];;
  Inject (ChangeAlphabet (Reset sigTok) _) [|Fin1|].
  

Definition App_Tok_Rel : pRel sigPro^+ (FinType(EqType unit)) 4 :=
  ignoreParam (
      fun tin tout =>
        forall (Q : list Tok) (t : Tok),
          tin[@Fin0] ≃ Q ->
          tin[@Fin1] ≃ t ->
          isRight tin[@Fin2] ->
          isRight tin[@Fin3] ->
          tout[@Fin0] ≃ Q ++ [t] /\
          isRight tout[@Fin1] /\
          isRight tout[@Fin2] /\
          isRight tout[@Fin3]
    ).


Lemma App_Tokens_Realise : App_Tokens ⊨ App_Tokens_Rel.
Proof.
  eapply Realise_monotone.
  { unfold App_Tokens. repeat TM_Correct.
    - apply App_Computes with (X := Tok).
    - apply Reset_Realise with (X := list Tok).
    - apply CopyValue_Realise with (X := list Tok).
    - apply Reset_Realise with (X := list Tok).
    - apply Reset_Realise with (X := list Tok).
  }
  {
    intros tin ((), tout) H. intros Q Q' HENcQ HEncQ' HRight2.
    unfold sigPro, sigTok in *. TMSimp.
    specialize (H _ _ ltac:(eauto) ltac:(eauto) ltac:(eauto) ltac:(intros i; destruct_fin i)) as (HComp1&HComp2&HComp3&_).
    specialize (H0 _ ltac:(eauto)).
    specialize (H1 _ ltac:(eauto) ltac:(eauto)) as (H1&H1').
    specialize (H2 _ ltac:(eauto)).
    specialize (H3 _ ltac:(eauto)).
    repeat split; eauto.
  }
Qed.

Lemma App_ATok_Realise t : App_ATok t ⊨ App_ATok_Rel t.
Proof.
  eapply Realise_monotone.
  { unfold App_ATok. repeat TM_Correct.
    - eapply RealiseIn_Realise. apply WriteValue_Sem.
    - apply App_Tokens_Realise.
  }
  {
    intros tin ((), tout) H. intros Q HENcQ HRight1 HRight2.
    TMSimp.
    spec_assert H by eauto.
    specialize (H0 _ _ ltac:(eauto) ltac:(eauto) ltac:(eauto)) as (H0&H0'&H0'').
    split; auto.
  }
Qed.
  


Lemma App_Tok_Realise : App_Tok ⊨ App_Tok_Rel.
Proof.
  eapply Realise_monotone.
  { unfold App_Tok. repeat TM_Correct.
    - eapply RealiseIn_Realise. apply Constr_nil_Sem.
    - apply Constr_cons_Realise.
    - apply App_Tokens_Realise.
    - apply Lift_Realise. apply Reset_Realise with (X := Tok).
  }
  { intros tin ((), tout) H. cbn. intros Q t HEncQ HEncT HRight2 HRight3.
    unfold sigPro, sigTok in *. TMSimp.
    spec_assert H by auto.
    specialize (H0 [] t ltac:(eauto) ltac:(eauto)) as (H0&H0').
    specialize (H1 Q [t]). repeat spec_assert H1 by auto. destruct H1 as (H1&H1'&H1'').
    specialize (H2 t). spec_assert H2 as H2 % surjectTape_isRight'. apply contains_translate_tau1. auto.
    repeat split; auto.
  }
Qed.



Definition JumpToTarget_Step : pTM sigPro^+ (FinType(EqType (bool*bool))) 6 :=
  If (Inject (MatchList sigTok) [|Fin0; Fin3|])
     (MATCH (Inject (ChangeAlphabet MatchTok _) [|Fin3|])
            (fun t : option ATok =>
               match t with
               | Some retAT =>
                 If (Inject (ChangeAlphabet MatchNat retr_nat_prog) [|Fin2|])
                    (Return (Inject (App_ATok retAT) [|Fin1;Fin4;Fin5|]) (true,default)) (* continue *)
                    (Nop (false, true)) (* return Some *)
               | Some lamAT =>
                 Return (Inject (ChangeAlphabet Constr_S retr_nat_prog) [|Fin2|];;
                         Inject (App_ATok lamAT) [|Fin1;Fin4;Fin5|])
                        (true,default) (* continue *)
               | Some appAT => (* either [appT] or [retT] *)
                 Return (Inject (App_ATok appAT) [|Fin1;Fin4;Fin5|])
                        (true,default) (* continue *)
               | None => (* Variable *)
                 Return (Inject (ChangeAlphabet Constr_varT _) [|Fin3|];;
                         Inject (App_Tok) [|Fin1;Fin3;Fin4;Fin5|])
                        (true,default) (* continue *)
               end))
     (Nop (false, false))
.


Definition JumpToTarget_Step_Rel : pRel sigPro^+ (FinType(EqType(bool*bool))) 6 :=
  fun tin '(yout, tout) =>
    forall (P Q : Pro) (k : nat),
      tin[@Fin0] ≃ P ->
      tin[@Fin1] ≃ Q ->
      tin[@Fin2] ≃ k ->
      (forall i : Fin.t 3, isRight tin[@Fin.R 3 i]) ->
      match P with
      | retT :: P' =>
        match k with
        | O =>
          tout[@Fin0] ≃ P' /\
          tout[@Fin1] ≃ Q /\
          tout[@Fin2] ≃ 0 /\
          yout = (false, true) (* return Some *)
        | S k' =>
          tout[@Fin0] ≃ P' /\
          tout[@Fin1] ≃ Q ++ [retT] /\
          tout[@Fin2] ≃ k' /\
          yout = (true, default) (* continue *)
        end
      | lamT :: P' =>
        tout[@Fin0] ≃ P' /\
        tout[@Fin1] ≃ Q ++ [lamT] /\
        tout[@Fin2] ≃ S k /\
        yout = (true, default) (* continue *)
      | t :: P' =>
        tout[@Fin0] ≃ P' /\
        tout[@Fin1] ≃ Q ++ [t] /\
        tout[@Fin2] ≃ k /\
        yout = (true, default) (* continue *)
      | nil =>
        tout[@Fin0] ≃ nil /\
        tout[@Fin1] ≃ Q /\
        tout[@Fin2] ≃ k /\
        yout = (false, false) (* return None *)
      end /\
      (forall i : Fin.t 3, isRight tout[@Fin.R 3 i])
.


Lemma JumpToTarget_Step_Realise : JumpToTarget_Step ⊨ JumpToTarget_Step_Rel.
Proof.
  eapply Realise_monotone.
  { unfold JumpToTarget_Step. repeat TM_Correct.
    - apply MatchList_Realise.
    - apply Lift_Realise. eapply RealiseIn_Realise. apply MatchTok_Sem.
    - apply Lift_Realise. eapply RealiseIn_Realise. apply MatchNat_Sem.
    - apply App_ATok_Realise.
    - apply Lift_Realise. eapply RealiseIn_Realise. apply Constr_S_Sem.
    - apply App_ATok_Realise.
    - apply App_ATok_Realise.
    - apply Lift_Realise. eapply RealiseIn_Realise. apply Constr_varT_Sem.
    - apply App_Tok_Realise.
  }
  {
    intros tin (yout, tout) H. cbn. intros P Q k HEncP HEncQ HEncK HInt.
    unfold sigPro, sigTok in *.
    destruct H; TMSimp.
    { (* Then of [MatchList] *)
      rename H into HMatchList; rename H0 into HMatchTok; rename H1 into HCase.
      specialize HMatchList with (1 := HEncP) (2 := HInt _).
      destruct P as [ | t P']; destruct HMatchList as (HMatchList&HMatchList'&HMatchList''); inv HMatchList''.

      specialize HMatchTok with (1 := contains_translate_tau1 HMatchList').
      destruct t as [ n | | | ]; destruct HMatchTok as [HMatchTok ->]; try apply surjectTape_isRight' in HMatchTok; try apply contains_translate_tau2 in HMatchTok.
      - (* t = varT n *) TMSimp.
        idtac.
        specialize H0 with (1 := contains_translate_tau1 HMatchTok) as H0 % contains_translate_tau2.
        specialize H1 with (1 := HEncQ) (2 := H0). repeat spec_assert H1 by auto. destruct H1 as (H1&H1'&H1''&H''').
        repeat split; auto. intros i; destruct_fin i; TMSimp. all: auto.
      - (* t = appT *) TMSimp. specialize H0 with (1 := HEncQ). repeat spec_assert H0 by auto. destruct H0 as (H0&H0'&H0'').
        split; auto. intros i; destruct_fin i; auto. now setoid_rewrite H1_6.
      - (* t = lamT *) TMSimp.
        specialize H0 with (1 := contains_translate_tau1 HEncK) as H0 % contains_translate_tau2.
        specialize H1 with (1 := HEncQ). repeat spec_assert H1 by auto. destruct H1 as (H1&H1'&H1'').
        split; auto. intros i; destruct_fin i; auto. now setoid_rewrite H2_7.
      - (* t = retT *)
        cbn in *. destruct HCase as [HMatchNat | HMatchNat]; TMSimp.
        { (* Then of [MatchNat]: k = S k' *)
          specialize H with (1 := contains_translate_tau1 HEncK).
          destruct k as [ | k']; destruct H as [ HMatchNat HMatchNat']; inv HMatchNat'; apply contains_translate_tau2 in HMatchNat.
          specialize H1 with (1 := HEncQ). repeat spec_assert H1 by auto. destruct H1 as (H1&H1'&H1'').
          repeat split; auto. intros i; destruct_fin i; auto. now setoid_rewrite H2_12.
        }
        { (* Else case of [MatchNat]: k = O *)
          specialize H with (1 := contains_translate_tau1 HEncK).
          destruct k as [ | k']; destruct H as [ HMatchNat HMatchNat']; inv HMatchNat'; apply contains_translate_tau2 in HMatchNat.
          repeat split; auto. intros i; destruct_fin i. now setoid_rewrite H1_8. now setoid_rewrite H1_7. now setoid_rewrite H1_6.
        }
    }
    { (* Else of [MatchList] *)
      rename H into HMatchList.
      specialize HMatchList with (1 := HEncP) (2 := HInt _).
      destruct P as [ | t P']; destruct HMatchList as (HMatchList&HMatchList'&HMatchList''); inv HMatchList''.
      repeat split; auto. intros i; destruct_fin i; auto. now setoid_rewrite H0_3. now setoid_rewrite H0_2.
    }
  }
Qed.



Fixpoint jumpTarget_accus (k:nat) (Q:Pro) (P:Pro) : (nat*(Pro*Pro)) :=
  match P with
  | retT :: P' => match k with
                 | 0 => (0, (Q, P'))
                 | S k' => jumpTarget_accus k' (Q++[retT]) P'
                 end
  | lamT :: P' => jumpTarget_accus (S k) (Q++[lamT]) P'
  | t :: P'    => jumpTarget_accus k (Q++[t]) P' (* either [varT n] or [appT] *)
  | []         => (k, (Q, nil))
  end.

Lemma jumpTarget_accus_correct k Q P Q' P' :
  jumpTarget k Q P = Some (Q', P') -> snd (jumpTarget_accus k Q P) = (Q', P').
Proof.
  revert k Q. induction P as [ | t P IH]; intros; cbn in *.
  - inv H.
  - destruct t; cbn; try now rewrite IH.
    destruct k; cbn; auto. now inv H.
Qed.



Definition JumpToTarget_Loop := WHILE JumpToTarget_Step.


Definition JumpTarget_Loop_Rel : pRel sigPro^+ (FinType(EqType bool)) 6 :=
  fun tin '(yout, tout) =>
    forall (P Q : Pro) (k : nat),
      tin[@Fin0] ≃ P ->
      tin[@Fin1] ≃ Q ->
      tin[@Fin2] ≃ k ->
      (forall i : Fin.t 3, isRight tin[@Fin.R 3 i]) ->
      tout[@Fin0] ≃ snd (snd (jumpTarget_accus k Q P)) /\
      tout[@Fin1] ≃ fst (snd (jumpTarget_accus k Q P)) /\
      tout[@Fin2] ≃ fst (jumpTarget_accus k Q P) /\
      match jumpTarget k Q P with
      | Some (Q', P') =>
        yout = true
      | None =>
        yout = false
      end /\
      (forall i : Fin.t 3, isRight tout[@Fin.R 3 i]).


(* TODO: We are actually not interested in the cases, where [jumpTarget] yields [None]. *)

(* TODO *)
