Require Import TM.Prelim TM.Code.CodeTM.
Require Import TM.LiftSigmaTau.


Generalizable All Variables.


Section SurjectInject.
  Variable (sig tau : finType).
  Variable def : sig.
  Variable retr : Retract sig tau.

  Definition injectSymbols : list sig -> list tau := map Retr_f.
  Definition surjectSymbols : list tau -> list sig := map (surject Retr_g def).

  (* This can be easyly proven without induction. *)
  Lemma surject_inject (str : list sig) (str' : list tau) :
    injectSymbols str = str' ->
    str = surjectSymbols str'.
  Proof.
    intros <-. induction str as [ | s str IH ]; cbn.
    - reflexivity.
    - unfold surject. retract_adjoint. f_equal. auto.
  Qed.

  Lemma inject_surject (str : list tau) (str' : list sig) :
    (forall t, t el str -> exists s, Retr_g t = Some s) ->
    surjectSymbols str = str' ->
    str = injectSymbols str'.
  Proof.
    intros H <-. unfold injectSymbols, surjectSymbols. rewrite map_map. erewrite map_ext_in. symmetry. eapply map_id.
    intros t Ht. specialize (H _ Ht) as (s&Hs).
    erewrite retract_g_inv; eauto.
    unfold surject. rewrite Hs. reflexivity.
  Qed.

  Lemma surject_cons (str : list tau) (str2 : list sig) (s : sig) :
    surjectSymbols str = s :: str2 ->
    exists (t : tau) (str' : list tau),
      str = t :: str' /\
      surject Retr_g def t = s /\
      surjectSymbols str' = str2.
  Proof.
    destruct str as [ | t str ]; cbn in *; intros; inv H; eauto.
  Qed.

  Lemma surject_app (str : list tau) (str2 str3 : list sig) :
    surjectSymbols str = str2 ++ str3 ->
    exists (str' str'' : list tau),
      str = str' ++ str'' /\
      surjectSymbols str'  = str2 /\
      surjectSymbols str'' = str3.
  Proof.
    revert str str3. induction str2 as [ | s str2 IH]; intros str str3 H; cbn in *.
    - exists nil, str. cbn. auto.
    - pose proof surject_cons H as (t&str'&->&L1&L2). cbn in *. specialize (IH _ _ L2) as (Str&Str'&->&IH1&IH2).
      inv H. repeat eexists. instantiate (1 := t :: Str). reflexivity. cbn. reflexivity.
  Qed.

End SurjectInject.


Corollary map_length_eq : forall (A B C : Type) (f : A -> C) (g : B -> C) (l1 : list A) (l2 : list B), map f l1 = map g l2 -> |l1| = |l2|.
Proof.
  intros. erewrite <- map_length. symmetry. erewrite <- map_length. symmetry. rewrite H. reflexivity.
Qed.


Section MapCode.
  Variable sig tau : finType.
  Variable retr : Retract sig tau.

  (* [Retract_sum] isn't declared as instance *)
  Global Instance Retract_plus : Retract (sig^+) (tau^+) := Retract_sum _ _.
  Notation "'f''" := (@Retr_f (sig^+) (tau^+) Retract_plus).
  Notation "'g''" := (@Retr_g (sig^+) (tau^+) Retract_plus).

  Context `{cX : codable sig X}.

  Check _ : codable sig^+ X.

  

  (* Translation Functions *)
  Definition injectTape : tape (sig^+) -> tape (tau^+) := mapTape f'.
  Definition surjectTape : tape (tau^+) -> tape (sig^+) := surjectTape g' (inl UNKNOWN).

  (* The other direction does not hold *)
  Lemma surjectTape_injectTape t :
    surjectTape (injectTape t) = t.
  Proof.
    unfold injectTape, surjectTape. unfold LiftSigmaTau.surjectTape. unfold surject. simpl_tape.
    erewrite mapTape_ext. apply mapTape_id. intros a. retract_adjoint. reflexivity.
  Qed.



  Lemma contains_translate_sig (x : X) (t : tape (sig^+)) :
    t ≃ x <-> (injectTape t) ≃ x.
  Proof.
    split; intros (r1&HCode); subst; cbn in *; hnf.
    - repeat eexists. cbn. f_equal. rewrite map_app, !List.map_map. cbn. reflexivity.
    - unfold injectTape in HCode.
      exists (surjectSymbols (inl UNKNOWN) _ r1).
      apply mapTape_inv_midtape in HCode as (ls'&m'&rs'&->&->&HCode1&HCode2).
      rewrite map_map in HCode2.
      destruct m'; cbn in *; inv HCode1.
      f_equal.
      + unfold surjectSymbols. rewrite map_map. rewrite <- map_id at 1. eapply map_ext.
        intros [ | ]; cbn. reflexivity. unfold surject. cbn. retract_adjoint. reflexivity.
      + symmetry. eapply map_injective with (f := retract_sum_f id Retr_f); eauto.
        { intros. eapply retract_f_injective; eauto. }
        now rewrite map_app, !map_map.
  Qed.

  Lemma contains_translate_tau1 (x : X) (t : tape (tau^+)) :
    t ≃ x -> surjectTape t ≃ x.
  Proof.
    intros (ls&HCode). cbn in *. subst. cbn. rewrite !map_map.
    repeat econstructor. f_equal. rewrite map_app, !map_map. f_equal.
    eapply map_ext. intros. unfold surject. cbn. retract_adjoint. reflexivity.
  Qed.

  Lemma surject_inject_inr (x : boundary) (str : list tau^+) (code : list sig) :
    surjectSymbols (inl x) Retract_plus str = map inr code ->
    exists str' : list tau, str = map inr str' /\ map Retr_g str' = map Some code.
  Proof.
    revert x code. induction str as [ | s str' IH]; intros; cbn in *.
    - apply map_eq_nil' in H as ->. exists nil. cbn. tauto.
    - destruct code as [ | c code']; cbn in *; inv H.
      destruct s; cbn in *; inv H1.
      specialize (IH _ _ H2) as (str''&->&IH). rewrite <- IH.
      exists (e :: str''). cbn. split. auto. f_equal.
      unfold surject, retract_sum_g in H0. destruct (Retr_g e) eqn:E; inv H0; auto.
  Qed.

  Lemma in_encode_retract (x : X) :
    forall t' : tau, t' el encode x -> exists s' : sig, Retr_g t' = Some s'.
  Proof. cbn. intros t' (?&<-&?) % in_map_iff. retract_adjoint. eauto. Qed.

  Lemma contains_translate_tau2 (x : X) (t : tape (tau^+)) :
    surjectTape t ≃ x ->
    t ≃ x.
  Proof.
    intros (r1&HCode). cbn in *.
    eapply mapTape_inv_midtape in HCode as (ls'&m'&rs'&->&->&HCode1&HCode2).
    repeat econstructor; cbn in *. f_equal.
    - unfold surject in HCode1. destruct m'; cbn in *. cbv [id] in *. now inv HCode1.
      destruct (Retr_g e); inv HCode1.
    - symmetry in HCode2.
      change (surjectSymbols (inl UNKNOWN) Retract_plus rs' = map inr (cX x) ++ [inl STOP]) in HCode2.
      eapply surject_app in HCode2 as (str1&str2&->&L1&L2).
      eapply inject_surject in L1 as ->; eauto.
      eapply inject_surject in L2 as ->; eauto.
      + f_equal. unfold injectSymbols. rewrite !map_map. eapply map_ext. intros. cbn. reflexivity.
      + unfold surjectSymbols in L2. eapply map_eq_cons in L2 as (t & ? & -> & ? & -> % map_eq_nil').
        unfold surject in H. destruct t; cbn in *; swap 1 2. destruct (Retr_g e); inv H. inv H.
        intros [ | ]; intros [ | ]; try congruence; auto. inv H. eexists. cbn. reflexivity.
      + intros [ | ]; intros He; cbn; eauto.
        destruct (Retr_g e) eqn:E1; cbn; eauto. exfalso.
        pose proof surject_inject_inr L1 as (str1'&->&L3).
        apply in_map_iff in He as (?&HETmp&HE); inv HETmp.
        enough (e el encode x) as L4.
        {
          pose proof in_encode_retract L4 as (?&?). congruence.
        }
        assert (None el map Retr_g str1') as L5.
        {
          rewrite <- E1. eapply in_map_iff; eauto.
        }
        rewrite L3 in L5. apply in_map_iff in L5 as (?&?&?). congruence.
  Qed.

  Corollary contains_translate_eq (t1 t2 : tape (tau^+)) (x : X) :
    surjectTape t1 = surjectTape t2 ->
    t1 ≃ x -> t2 ≃ x.
  Proof.
    intros HEq HEnc.
    eapply contains_translate_tau2; auto.
    rewrite <- HEq. now eapply contains_translate_tau1 in HEnc.
  Qed.


  Lemma surjectTape_isRight (t : tape (tau^+)) :
    isRight t -> isRight (surjectTape t).
  Proof. unfold surjectTape, LiftSigmaTau.surjectTape. apply mapTape_isRight. Qed.

  Lemma surjectTape_isRight' (t : tape (tau^+)) :
    isRight (surjectTape t) -> isRight t.
  Proof. unfold surjectTape, LiftSigmaTau.surjectTape. apply mapTape_isRight. Qed.

End MapCode.

Hint Unfold surjectTape surjectTapes injectTape : tape.

(** This makes sure that we can apply the above lemmas ([contains_translate_sig], [contains_translate_tau1], [contains_translate_tau2]), even after [cbn] *)
Arguments Retract_plus : simpl never.
Arguments injectTape : simpl never.
Arguments surjectTape : simpl never.




Section ChangeAlphabet.
  Variable (sig tau : finType).
  Variable (n : nat) (F : finType).
  Variable pM : {M : mTM sig^+ n & states M -> F}.
  Variable (retr : Retract sig tau).

  Definition ChangeAlphabet : {M : mTM tau^+ n & states M -> F} :=
    Lift pM (Retract_plus retr) (Vector.const (inl UNKNOWN) n).

End ChangeAlphabet.



Section Computes_Change_Alphabet.

  Variable (sig tau : finType).
  Variable retr : Retract sig tau.

  Context `{cX : codable sig X} `{cY : codable sig Y}.
  Variable (func : X -> Y).

  Variable (n_tapes : nat).
  Variable F : finType.
  Variable (pM : {M : mTM (sig^+) (S (S n_tapes)) & states M -> F}).

  Notation f' := (@Retr_f _ _ retr).
  Notation g' := (@Retr_g _ _ retr).
  Check (f', g').


  Lemma ChangeAlphabet_Computes :
    pM ⊨ Computes_Rel func ->
    ChangeAlphabet pM _ ⊨ Computes_Rel func.
  Proof.
    intros H. eapply Realise_monotone.
    {
      unfold ChangeAlphabet. eapply Lift_Realise; eauto.
    }
    {
      hnf. intros tin (yout&tout) HComp.
      cbn. intros x HEncX HOut HIntern.
      cbn in HComp. repeat autounfold with tape in HComp. simpl_vector in HComp. cbn in HComp.

      unshelve eapply contains_translate_tau1 in HEncX; eauto.
      specialize (HComp x HEncX).
      destruct HComp as (HComp1&HComp2&HComp3); cbn in *.
      { now eapply surjectTape_isRight. }
      { intros. simpl_tape. cbn. rewrite Vector.const_nth. eapply surjectTape_isRight. eauto. }
      repeat split.
      + eapply contains_translate_tau2; eauto.
      + eapply contains_translate_tau2; eauto.
      + intros i. specialize (HComp3 i).
        erewrite VectorSpec.nth_map2 in HComp3; eauto. cbn in HComp3. rewrite VectorSpec.const_nth in HComp3.
        now eapply surjectTape_isRight' in HComp3.
    }
  Qed.


  (*
  Lemma ChangeAlphabet_Computes_RealiseIn (k : nat) :
    pM ⊨c(k) Computes_Rel i1 i2 cX cY func ->
    GoodCode ->
    ChangeAlphabet ⊨c(k) Computes_Rel i1 i2 _ _ func.
  Proof.
    intros H HDef. eapply RealiseIn_monotone.
    - unfold ChangeAlphabet. eapply Lift_RealiseIn. apply tight_retract_strong. eapply retr'. eassumption.
    - omega.
    - hnf. intros tin (yout&tout) HComp. hnf in *. intros x. specialize (HComp x). intros HEnc1.
      unfold surjectTapes, mapTapes in *. erewrite !Vector.nth_map in HComp; eauto.
      eapply encodeTranslate_tau1 in HEnc1; eauto.
      specialize (HComp HEnc1) as HEnc2. eapply encodeTranslate_tau2; eauto.
      destruct HDef as [HDef | HDef]; auto.
  Qed.

  Lemma ChangeAlphabet_Computes_RealiseIn_p (k : nat) :
    pM ⊨c(k) Computes_Rel_p i1 i2 cX cY func param ->
    GoodCode ->
    ChangeAlphabet ⊨c(k) Computes_Rel_p i1 i2 _ _ func param.
  Proof.
    intros H HDef. eapply RealiseIn_monotone.
    - unfold ChangeAlphabet. eapply Lift_RealiseIn. apply tight_retract_strong. eapply retr'. eassumption.
    - omega.
    - hnf. intros tin (yout&tout) HComp. hnf in *. intros x. specialize (HComp x). intros HEnc1.
      unfold surjectTapes, mapTapes in *. erewrite !Vector.nth_map in HComp; eauto.
      eapply encodeTranslate_tau1 in HEnc1; eauto.
      specialize (HComp HEnc1) as (HEnc2&HEnc2'). split; auto. eapply encodeTranslate_tau2; eauto.
      destruct HDef as [HDef | HDef]; auto.
  Qed.
   *)

End Computes_Change_Alphabet.

(*
Arguments ChangeAlphabet_Computes_Realise
          {sig} {tau} (default) {f} {g} retr
          {X} {Y} {cX} {cY} func {F}
          {n_tapes} {i1} {i2} {pM} /.

Arguments ChangeAlphabet_Computes_RealiseIn
          {sig} {tau} (default) {f} {g} retr
          {X} {Y} {cX} {cY} func {F}
          {n_tapes} {i1} {i2} {pM} /.

Arguments ChangeAlphabet_Computes_Realise_p
          {sig} {tau} (default) {f} {g} retr
          {X} {Y} {cX} {cY} func {F} param
          {n_tapes} {i1} {i2} {pM} /.

Arguments ChangeAlphabet_Computes_RealiseIn_p
          {sig} {tau} (default) {f} {g} retr
          {X} {Y} {cX} {cY} func {F} param
          {n_tapes} {i1} {i2} {pM} /.


Section Computes2_Change_Alphabet.

  Variable sig tau : finType.
  Variable default : sig.

  Variable (f : sig -> tau) (g : tau -> option sig).
  Hypothesis retr : tight_retract f g.

  Variable (X Y Z : Type) (cX : codable sig X) (cY : codable sig Y) (cZ : codable sig Z).
  Variable (func : X -> Y -> Z).
  Variable (F : finType).
  Variable (param : X -> Y -> F).

  Variable (n_tapes : nat).
  Variable (i1 i2 i3 : Fin.t n_tapes).
  Variable (pM : {M : mTM (sig^+) n_tapes & states M -> F}).


  Definition GoodCode2 := (forall (x: X) (y : Y), ~ default el encode (sigma := sig) (func x y)) \/ (forall t' : tau, exists s', g t' = Some s').

  Lemma ChangeAlphabet_Computes2_Realise :
    pM ⊨ Computes2_Rel i1 i2 i3 cX cY cZ func ->
    GoodCode2 ->
    ChangeAlphabet default retr pM ⊨ Computes2_Rel i1 i2 i3 _ _ _ func.
  Proof.
    intros H HDef. eapply Realise_monotone.
    - unfold ChangeAlphabet. eapply Lift_Realise. apply tight_retract_strong. eapply retr'. eassumption.
    - hnf. intros tin (yout&tout) HComp. hnf in *. intros x y. specialize (HComp x). intros HEnc1 HEnc2.
      unfold surjectTapes, mapTapes in *. erewrite !Vector.nth_map in HComp; eauto.
      apply encodeTranslate_tau1 with (def := default) in HEnc1. apply encodeTranslate_tau1 with (def := default) in HEnc2.
      specialize (HComp y HEnc1 HEnc2). eapply encodeTranslate_tau2; eauto. destruct HDef; auto.
  Qed.

  Lemma ChangeAlphabet_Computes2_Realise_p :
    pM ⊨ Computes2_Rel_p i1 i2 i3 cX cY cZ func param ->
    GoodCode2 ->
    ChangeAlphabet default retr pM ⊨ Computes2_Rel_p i1 i2 i3 _ _ _ func param.
  Proof.
    intros H HDef. eapply Realise_monotone.
    - unfold ChangeAlphabet. eapply Lift_Realise. apply tight_retract_strong. eapply retr'. eassumption.
    - hnf. intros tin (yout&tout) HComp. hnf in *. intros x y. specialize (HComp x). intros HEnc1 HEnc2.
      unfold surjectTapes, mapTapes in *. erewrite !Vector.nth_map in HComp; eauto.
      apply encodeTranslate_tau1 with (def := default) in HEnc1. apply encodeTranslate_tau1 with (def := default) in HEnc2.
      specialize (HComp y HEnc1 HEnc2) as (?&?). split; auto. eapply encodeTranslate_tau2; eauto. destruct HDef; auto.
  Qed.

  Lemma ChangeAlphabet_Computes2_RealiseIn (k : nat) :
    pM ⊨c(k) Computes2_Rel i1 i2 i3 cX cY cZ func ->
    GoodCode2 ->
    ChangeAlphabet default retr pM ⊨c(k) Computes2_Rel i1 i2 i3 _ _ _ func.
  Proof.
    intros H HDef. eapply RealiseIn_monotone.
    - unfold ChangeAlphabet. eapply Lift_RealiseIn. apply tight_retract_strong. eapply retr'. eassumption.
    - omega.
    - hnf. intros tin (yout&tout) HComp. hnf in *. intros x y. specialize (HComp x). intros HEnc1 HEnc2.
      unfold surjectTapes, mapTapes in *. erewrite !Vector.nth_map in HComp; eauto.
      apply encodeTranslate_tau1 with (def := default) in HEnc1. apply encodeTranslate_tau1 with (def := default) in HEnc2.
      specialize (HComp y HEnc1 HEnc2). eapply encodeTranslate_tau2; eauto. destruct HDef; auto.
  Qed.

  Lemma ChangeAlphabet_Computes2_RealiseIn_p (k : nat) :
    pM ⊨c(k) Computes2_Rel_p i1 i2 i3 cX cY cZ func param ->
    GoodCode2 ->
    ChangeAlphabet default retr pM ⊨c(k) Computes2_Rel_p i1 i2 i3 _ _ _ func param.
  Proof.
    intros H HDef. eapply RealiseIn_monotone.
    - unfold ChangeAlphabet. eapply Lift_RealiseIn. apply tight_retract_strong. eapply retr'. eassumption.
    - omega.
    - hnf. intros tin (yout&tout) HComp. hnf in *. intros x y. specialize (HComp x). intros HEnc1 HEnc2.
      unfold surjectTapes, mapTapes in *. erewrite !Vector.nth_map in HComp; eauto.
      apply encodeTranslate_tau1 with (def := default) in HEnc1. apply encodeTranslate_tau1 with (def := default) in HEnc2.
      specialize (HComp y HEnc1 HEnc2) as (?&?). split; auto. eapply encodeTranslate_tau2; eauto. destruct HDef; auto.
  Qed.

End Computes2_Change_Alphabet.


Arguments ChangeAlphabet_Computes2_Realise
          {sig} {tau} (default) {f} {g} retr
          {X} {Y} {Z} {cX} {cY} {cZ} func {F}
          {n_tapes} {i1} {i2} {i3} {pM} /.

Arguments ChangeAlphabet_Computes2_RealiseIn
          {sig} {tau} (default) {f} {g} retr
          {X} {Y} {Z} {cX} {cY} {cZ} func {F}
          {n_tapes} {i1} {i2} {i3} {pM} /.

Arguments ChangeAlphabet_Computes2_Realise_p
          {sig} {tau} (default) {f} {g} retr
          {X} {Y} {Z} {cX} {cY} {cZ} func {F} param
          {n_tapes} {i1} {i2} {i3} {pM} /.

Arguments ChangeAlphabet_Computes_RealiseIn_p
          {sig} {tau} (default) {f} {g} retr
          {X} {Y} {cX} {cY} func {F} param
          {n_tapes} {i1} {i2} {pM} /.
*)