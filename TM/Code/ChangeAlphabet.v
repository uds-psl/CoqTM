Require Import TM.Prelim TM.Code.CodeTM.
Require Import TM.LiftSigmaTau.

Section SurjectInject.
  Variable (sig tau : finType).
  Variable (f : sig -> tau) (g : tau -> option sig).
  Variable def : sig.
  Hypothesis retr : tight_retract f g.
  
  Definition injectSymbols : list sig -> list tau := map f.
  Definition surjectSymbols : list tau -> list sig := map (surject g def).
  
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
    (forall t, t el str -> exists s, g t = Some s) ->
    surjectSymbols str = str' ->
    str = injectSymbols str'.
  Proof.
    intros H <-. unfold injectSymbols, surjectSymbols. rewrite map_map. erewrite map_ext_in. symmetry. eapply map_id.
    intros t Ht. specialize (H _ Ht) as (s&Hs).
    erewrite tretract_g_inv'; eauto.
    unfold surject. rewrite Hs. reflexivity.
  Qed.

  Lemma surject_cons (str : list tau) (str2 : list sig) (s : sig) :
    surjectSymbols str = s :: str2 ->
    exists (t : tau) (str' : list tau),
      str = t :: str' /\
      surject g def t = s /\
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
  Variable (f : sig -> tau) (g : tau -> option sig).
  Variable def : sig.
  Hypothesis retr : tight_retract f g.

  Global Instance retr' : TRetract (sig^+) (tau^+) := Build_TRetract _.
  Notation "'f''" := (@TRetr_f (sig^+) (tau^+) retr').
  Notation "'g''" := (@TRetr_g (sig^+) (tau^+) retr').

  Variable X : Type.
  Hypothesis enc_X : codeable sig X.

  (* Translation Functions *)
  Definition injectTape : tape (sig^+) -> tape (tau^+) := mapTape f'.
  Definition surjectTape : tape (tau^+) -> tape (sig^+) := surjectTape g' (inr def).

  (* The other direction does not hold *)
  Lemma surjectTape_injectTape t :
    surjectTape (injectTape t) = t.
  Proof.
    unfold injectTape, surjectTape. unfold LiftSigmaTau.surjectTape. unfold surject. simpl_tape. 
    erewrite mapTape_ext. apply mapTape_id. intros a. retract_adjoint. reflexivity.
  Qed.



  Lemma encodeTranslate_sig (x : X) (t : tape (sig^+)) :
    tape_encodes _ t x <-> tape_encodes _ (injectTape t) x.
  Proof.
    split; intros (r1&r2&H1&H2); hnf in *; cbn in *.
    - exists (injectSymbols f' r1), (injectSymbols f' r2). hnf. cbn. split; [ clear H2 | clear H1 ].
      + unfold injectTape, injectSymbols. simpl_tape. rewrite H1. cbn in *. reflexivity.
      + unfold injectTape, injectSymbols. simpl_tape. rewrite H2. cbn in *.
        rewrite map_app, !map_map. cbn. reflexivity.
    - exists (surjectSymbols g' (inr def) r1), (surjectSymbols g' (inr def) r2). hnf. cbn. split; [ clear H2 | clear H1 ].
      + unfold injectTape in H1. simpl_tape in H1. 
        replace (map f' (left t)) with (injectSymbols f' (left t)) in H1 by reflexivity.
        pose proof (surject_inject (inr def) _ H1) as ->. cbn. reflexivity.
      + unfold injectTape in H2. simpl_tape in H2. 
        replace (map f' (tape_local t)) with (injectSymbols f' (tape_local t)) in H2 by reflexivity.
        pose proof (surject_inject (inr def) _ H2) as ->.
        cbn. f_equal. unfold surjectSymbols. rewrite !map_map. rewrite map_app. rewrite !map_map. cbn.
        f_equal. apply map_ext. intros a. cbn. unfold surject, retract_sum_g. retract_adjoint. reflexivity.
  Qed.

  Lemma encodeTranslate_tau1 (x : X) (t : tape (tau^+)) :
    tape_encodes _ t x -> tape_encodes _ (surjectTape t) x.
  Proof.
    intros (r1&r2&H1&H2); hnf in *; cbn in *.
    - exists (surjectSymbols g' (inr def) r1), (surjectSymbols g' (inr def) r2). hnf. cbn. split; [ clear H2 | clear H1 ].
      + unfold surjectTape. unfold LiftSigmaTau.surjectTape. simpl_tape. rewrite H1. cbn. reflexivity.
      + unfold surjectTape. unfold LiftSigmaTau.surjectTape. simpl_tape. rewrite H2. cbn.
        rewrite !map_map, map_app, !map_map. cbn. f_equal.
        eapply map_ext. intros a. unfold surject, retract_sum_g. retract_adjoint. reflexivity.
  Qed.

  
  Lemma encodeTranslate_tau2 (x : X) (t : tape (tau^+)) :
    (~ def el encode x) \/ (forall t' : tau, exists s', g t' = Some s') ->
    tape_encodes _ (surjectTape t) x -> tape_encodes _ t x.
  Proof.
    intros HDef (r1&r2&H1&H2). hnf.
    unfold surjectTape, LiftSigmaTau.surjectTape in *. simpl_tape in *. cbn in *.
    
    exists (skipn 1 (left t)). exists (skipn (S (| (encode x) |)) (tape_local t)). hnf. cbn -[skipn]. split; [clear H2 | clear H1].
    - apply surject_cons in H1 as (s1&s2&H1&H2&H3). cbn in *. unfold surjectSymbols in *. unfold surject in *. cbn in *.
      unfold retract_sum_g in H2. destruct s1. rewrite H1. cbn. congruence. destruct (g e); inv H2. 
    - apply surject_app in H2 as (str1&str2&->&L1&L2). apply surject_cons in L2 as (t'&str3&->&L3&L4).
      rewrite map_map.
      unfold surject, retract_sum_g in L3. destruct t'; swap 1 2. destruct (g e); inv L3. inversion L3. rewrite H0 in *. clear H0 L3.
      f_equal; [ | f_equal].
      + apply (inject_surject (f := f')) in L1 as ->; cbn.
        * unfold injectSymbols. cbn. unfold retract_sum_f. rewrite map_map. reflexivity.
        * auto_inj.
        * intros [s' | t'] Hin; swap 1 2.
          -- unfold surjectSymbols in L1.
             enough (exists s' : sig, g t' = Some s') as (s'&L5).
             {
               exists (inr s'). cbn. rewrite L5. reflexivity.
             }
             assert (exists x' : sig, inr x' = inr (A := bool) ((surject g def t')) /\ x' el (encode (codeable := enc_X) x)) as (x'&LH1&LH2).
             {
               eapply in_map_iff. rewrite <- L1. eapply in_map_iff.
               eexists. split; eauto. unfold surject, retract_sum_g. destruct (g t'); auto.
             }
             inv LH1. unfold surject in LH2.
             destruct HDef as [HDef | HDef].
             {
               destruct (g t').
               - eauto.
               - exfalso; eauto.
             }
             {
               pose proof (HDef t') as (s'&?). eauto.
             }
          -- cbn. eauto.
      + enough (str3 = skipn (S (| encode x |)) (str1 ++ [ inl STOP ] ++ str3)) as L by assumption.
        rewrite app_assoc. rewrite skipn_app. reflexivity. simpl_list. cbn. rewrite Nat.add_1_r. f_equal.
        unfold surjectSymbols in L1. apply map_length_eq in L1. auto.
  Qed.


  Corollary surjectTapes_sameEnc (t1 t2 : tape (sig^+)) (x : X) :
    (~ def el encode x) \/ (forall t' : tau, exists s', g t' = Some s') ->
    surjectTape (injectTape t1) = surjectTape (injectTape t2) ->
    tape_encodes _ t1 x -> tape_encodes _ t2 x.
  Proof.
    intros HDef HEq HEnc; cbn in *.
    eapply encodeTranslate_sig. eapply encodeTranslate_tau2; auto. rewrite <- HEq.
    eapply encodeTranslate_tau1. eapply encodeTranslate_sig. assumption.
  Qed.

  Corollary surjectTapes_sameEnc' (t1 t2 : tape (tau^+)) (x : X) :
    (~ def el encode x) \/ (forall t' : tau, exists s', g t' = Some s') ->
    surjectTape t1 = surjectTape t2 ->
    tape_encodes _ t1 x -> tape_encodes _ t2 x.
  Proof.
    intros HDef HEq HEnc.
    eapply encodeTranslate_tau2; auto.
    rewrite <- HEq. now eapply encodeTranslate_tau1 in HEnc.
  Qed.

End MapCode.


Hint Unfold surjectTape injectTape : tape.


Section Computes_Change_Alphabet.

  Variable (sig tau : finType).
  Variable (default : sig).
  Variable (f : sig -> tau) (g : tau -> option sig).
  Hypothesis retr : tight_retract f g.

  Variable (X Y : Type) (cX : codeable sig X) (cY : codeable sig Y).
  Variable (func : X -> Y).
  Variable (F : finType).
  Variable (param : X -> F).

  Variable (n_tapes : nat).
  Variable (i1 i2 : Fin.t n_tapes).
  Variable (pM : {M : mTM (sig^+) n_tapes & states M -> F}).

  Let retr' := retr' retr. 

  Notation "'f''" := (@TRetr_f _ _ retr').
  Notation "'g''" := (@TRetr_g _ _ retr').


  Definition ChangeAlphabet : { M : mTM (tau^+) n_tapes & states M -> F } :=
    LiftSigmaTau.Lift pM (f') (g') (inr default).


  Definition GoodCode := (forall x : X, ~ default el encode (sigma := sig) (func x)) \/ (forall t' : tau, exists s', g t' = Some s').


  Lemma ChangeAlphabet_Computes_WRealise :
    pM ⊫ Computes_Rel i1 i2 cX cY func ->
    GoodCode ->
    ChangeAlphabet ⊫ Computes_Rel i1 i2 _ _ func.
  Proof.
    intros H HDef. eapply WRealise_monotone.
    - unfold ChangeAlphabet. eapply Lift_WRealise. apply tight_retract_strong. eapply retr'. eassumption.
    - hnf. intros tin (yout&tout) HComp. hnf in *. intros x. specialize (HComp x). intros HEnc1.
      unfold surjectTapes, mapTapes in *. erewrite !Vector.nth_map in HComp; eauto.
      eapply encodeTranslate_tau1 in HEnc1; eauto.
      specialize (HComp HEnc1) as Henc2. eapply encodeTranslate_tau2; eauto.
      destruct HDef as [HDef | HDef]; auto.
  Qed.
  

  Lemma ChangeAlphabet_Computes_WRealise_p :
    pM ⊫ Computes_Rel_p i1 i2 cX cY func param ->
    GoodCode ->
    ChangeAlphabet ⊫ Computes_Rel_p i1 i2 _ _ func param.
  Proof.
    intros H HDef. eapply WRealise_monotone.
    - unfold ChangeAlphabet. eapply Lift_WRealise. apply tight_retract_strong. eapply retr'. eassumption.
    - hnf. intros tin (yout&tout) HComp. hnf in *. intros x. specialize (HComp x). intros HEnc1.
      unfold surjectTapes, mapTapes in *. erewrite !Vector.nth_map in HComp; eauto.
      eapply encodeTranslate_tau1 in HEnc1; eauto.
      specialize (HComp HEnc1) as (HEnc2&HEnc2'). split; auto. eapply encodeTranslate_tau2; eauto.
      destruct HDef as [HDef | HDef]; auto.
  Qed.

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

End Computes_Change_Alphabet.

Arguments ChangeAlphabet_Computes_WRealise
          {sig} {tau} (default) {f} {g} retr
          {X} {Y} {cX} {cY} func {F}
          {n_tapes} {i1} {i2} {pM} /.

Arguments ChangeAlphabet_Computes_RealiseIn
          {sig} {tau} (default) {f} {g} retr
          {X} {Y} {cX} {cY} func {F}
          {n_tapes} {i1} {i2} {pM} /.

Arguments ChangeAlphabet_Computes_WRealise_p
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

  Variable (X Y Z : Type) (cX : codeable sig X) (cY : codeable sig Y) (cZ : codeable sig Z).
  Variable (func : X -> Y -> Z).
  Variable (F : finType).
  Variable (param : X -> Y -> F).

  Variable (n_tapes : nat).
  Variable (i1 i2 i3 : Fin.t n_tapes).
  Variable (pM : {M : mTM (sig^+) n_tapes & states M -> F}).

  
  Definition GoodCode2 := (forall (x: X) (y : Y), ~ default el encode (sigma := sig) (func x y)) \/ (forall t' : tau, exists s', g t' = Some s').

  Lemma ChangeAlphabet_Computes2_WRealise :
    pM ⊫ Computes2_Rel i1 i2 i3 cX cY cZ func ->
    GoodCode2 ->
    ChangeAlphabet default retr pM ⊫ Computes2_Rel i1 i2 i3 _ _ _ func.
  Proof.
    intros H HDef. eapply WRealise_monotone.
    - unfold ChangeAlphabet. eapply Lift_WRealise. apply tight_retract_strong. eapply retr'. eassumption.
    - hnf. intros tin (yout&tout) HComp. hnf in *. intros x y. specialize (HComp x). intros HEnc1 HEnc2.
      unfold surjectTapes, mapTapes in *. erewrite !Vector.nth_map in HComp; eauto.
      apply encodeTranslate_tau1 with (def := default) in HEnc1. apply encodeTranslate_tau1 with (def := default) in HEnc2.
      specialize (HComp y HEnc1 HEnc2). eapply encodeTranslate_tau2; eauto. destruct HDef; auto.
  Qed.

  Lemma ChangeAlphabet_Computes2_WRealise_p :
    pM ⊫ Computes2_Rel_p i1 i2 i3 cX cY cZ func param ->
    GoodCode2 ->
    ChangeAlphabet default retr pM ⊫ Computes2_Rel_p i1 i2 i3 _ _ _ func param.
  Proof.
    intros H HDef. eapply WRealise_monotone.
    - unfold ChangeAlphabet. eapply Lift_WRealise. apply tight_retract_strong. eapply retr'. eassumption.
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


Arguments ChangeAlphabet_Computes2_WRealise
          {sig} {tau} (default) {f} {g} retr
          {X} {Y} {Z} {cX} {cY} {cZ} func {F}
          {n_tapes} {i1} {i2} {i3} {pM} /.

Arguments ChangeAlphabet_Computes2_RealiseIn
          {sig} {tau} (default) {f} {g} retr
          {X} {Y} {Z} {cX} {cY} {cZ} func {F}
          {n_tapes} {i1} {i2} {i3} {pM} /.

Arguments ChangeAlphabet_Computes2_WRealise_p
          {sig} {tau} (default) {f} {g} retr
          {X} {Y} {Z} {cX} {cY} {cZ} func {F} param
          {n_tapes} {i1} {i2} {i3} {pM} /.

Arguments ChangeAlphabet_Computes_RealiseIn_p
          {sig} {tau} (default) {f} {g} retr
          {X} {Y} {cX} {cY} func {F} param
          {n_tapes} {i1} {i2} {pM} /.