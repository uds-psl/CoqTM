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


Lemma map_cons' (A B: Type) (f: A->B) (ls: list A) (y: B) (ys: list B) :
  map f ls = y :: ys ->
  exists x xs, ls = x :: xs /\
          y = f x /\
          ys = map f xs.
Proof. induction ls; intros H; cbn in *; inv H; eauto. Qed.


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



  Lemma contains_translate_sig (x : X) (t : tape (sig^+)) :
    t ≃ x <-> (injectTape t) ≃ x.
  Proof.
    split; intros (y&ys&r1&HCode&HC); subst; cbn in *; hnf.
    - repeat eexists. cbn. rewrite HCode. cbn. eauto.
      f_equal. rewrite !map_map. cbn. now eapply map_ext.
    - eapply map_cons' in HCode as (y'&ys'&HCode&->&->); rename y' into y; rename ys' into ys.
      do 2 eexists. exists (surjectSymbols g' (inr def) r1). split.
      + rewrite HCode. eauto.
      + enough (midtape (inl START :: surjectSymbols TRetr_g (inr def) r1) 
                        (inr y) (map inr ys) =
                surjectTape (midtape (inl START :: r1) (inr (f y)) (map inr (map f ys)))) as L.
        { unfold finType_CS in *. rewrite L. rewrite <- HC. symmetry. now apply surjectTape_injectTape. }
        { cbn. f_equal.
          - unfold surject. cbn. retract_adjoint. reflexivity.
          - rewrite !map_map. apply map_ext. intros. unfold surject. cbn. retract_adjoint. reflexivity.
        }
  Qed.

  Lemma contains_translate_tau1 (x : X) (t : tape (tau^+)) :
    t ≃ x -> surjectTape t ≃ x.
  Proof.
    intros (y&ys&r1&HCode&->). cbn in *.
    eapply map_cons' in HCode as (y'&ys'&HCode&->&->); rename y' into y; rename ys' into ys.
    cbn. hnf. repeat econstructor; cbn; eauto.
    f_equal.
    - unfold surject. cbn. retract_adjoint. reflexivity.
    - rewrite !map_map. apply map_ext. intros. unfold surject. cbn. retract_adjoint. reflexivity.
  Qed.

  
  Lemma contains_translate_tau2 (x : X) (t : tape (tau^+)) :
    (~ def el encode x) \/ (forall t' : tau, exists s', g t' = Some s') ->
    surjectTape t ≃ x -> t ≃ x.
  Proof.
    intros HDef. intros (y&ys&rs&HCode&H). cbn in *.
    hnf. do 2 eexists. exists (skipn 1 (left t)). split. cbn. rewrite HCode. cbn. reflexivity.
    unfold surjectTape, LiftSigmaTau.surjectTape in H.

    destruct t; cbn -[skipn] in *; inv H.
    f_equal.
    - eapply map_cons' in H1 as (y'&ys'H1&->&H1'&->). cbn in *. f_equal.
      destruct y'; cbn in *; eauto. now destruct s.
      unfold surject in H1'. cbn in H1'. destruct (g e0) eqn:E1; inv H1'.
    - unfold surject in H2. unfold retract_sum_g in H2. destruct e; inv H2.
      destruct (g e) eqn:E2; inv H0.
      eapply tretract_g_inv' in E2 as ->; eauto.
      edestruct HDef as [HDef1|HDef2].
      { contradict HDef1. rewrite HCode. cbn. tauto. }
      { specialize (HDef2 e) as (s'&HDef2). congruence. }
    - rewrite map_map. 
      change (surjectSymbols (retract_sum_g Some g) (inr def) l0 = map inr ys) in H3.
      eapply inject_surject in H3 as ->; eauto.
      { unfold injectSymbols. rewrite map_map. apply map_ext. intros. cbn. reflexivity. }
      { intros. destruct HDef as [HDef1|HDef2].
        { (* def ∉ encode x *)
          unfold retract_sum_g. destruct t; cbn. eauto.
          destruct (g e0) eqn:E1; cbn; eauto. 
          contradict HDef1. rewrite HCode. cbn. right.
          eenough (List.In (inr def) (map inr ys)) as (?&L1&L2)%in_map_iff by now inv L1.
          rewrite <- H3. eapply in_map_iff. unfold surject. unfold retract_sum_g. cbn.
          exists (inr e0). rewrite E1. eauto.
        }
        { (* retract is full *)
          unfold retract_sum_g. destruct t; cbn; eauto.
          destruct (g e0) eqn:E1; eauto.
          specialize (HDef2 e0) as (?&?). congruence.
        }
      }
  Qed.


  Corollary contains_surjectTapes_sameEnc (t1 t2 : tape (sig^+)) (x : X) :
    (~ def el encode x) \/ (forall t' : tau, exists s', g t' = Some s') ->
    surjectTape (injectTape t1) = surjectTape (injectTape t2) ->
    t1 ≃ x -> t2 ≃ x.
  Proof.
    intros HDef HEq HEnc; cbn in *.
    eapply contains_translate_sig. eapply contains_translate_tau2; auto. rewrite <- HEq.
    eapply contains_translate_tau1. eapply contains_translate_sig; eauto.
  Qed.

  Corollary contains_surjectTapes_sameEnc' (t1 t2 : tape (tau^+)) (x : X) :
    (~ def el encode x) \/ (forall t' : tau, exists s', g t' = Some s') ->
    surjectTape t1 = surjectTape t2 ->
    t1 ≃ x -> t2 ≃ x.
  Proof.
    intros HDef HEq HEnc.
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


(* TODO: Where to put this? *)
Definition TRetract_Retract A B : TRetract A B -> Retract A B :=
  fun tretr => {|
      Retr_g := TRetr_g;
      Retr_f := TRetr_f;
      Retr_adj := ltac:(eauto);
    |}.

Coercion TRetract_Retract : TRetract >-> Retract.


Section Computes_Change_Alphabet.

  Variable (sig tau : finType).
  Variable retr : TRetract sig tau.

  Variable (X Y : Type) (cX : codeable sig X) (cY : codeable sig Y).
  Variable (defX defY : sig).
  Variable (func : X -> Y).

  Variable (n_tapes : nat).
  Variable (i1 i2 : Fin.t n_tapes).
  Variable F : finType.
  Variable (pM : {M : mTM (sig^+) (S (S n_tapes)) & states M -> F}).

  Let retr' := retr' retr. 

  Notation "'f''" := TRetr_f.
  Notation "'g''" := TRetr_g.
  

  Definition ChangeAlphabet : { M : mTM (tau^+) (S (S n_tapes)) & states M -> F } :=
    LiftSigmaTau.Lift pM retr' (inr defX ::: inr defY ::: Vector.const (inr defX) n_tapes).

  Definition GoodCode :=
    ((forall x : X, ~ defX el encode (sigma := sig) x) /\
     (forall x : X, ~ defY el encode (sigma := sig) (func x))) \/
    (forall t' : tau, exists s', g' t' = Some s').



  Lemma ChangeAlphabet_Computes_WRealise :
    pM ⊫ Computes_Rel func ->
    GoodCode ->
    ChangeAlphabet ⊫ Computes_Rel func.
  Proof.
    unfold GoodCode.
    intros H HDef. eapply WRealise_monotone.
    {
      unfold ChangeAlphabet. eapply Lift_WRealise; eauto.
    }
    {
      
      hnf. intros tin (yout&tout) HComp.
      cbn. intros x HEncX HOut HIntern.
      cbn in HComp. repeat autounfold with tape in HComp. simpl_vector in HComp. cbn in HComp.

      unshelve eapply contains_translate_tau1 with (def := defX) in HEncX; eauto.
      specialize (HComp x HEncX).
      destruct HComp as (HComp1&HComp2&HComp3); cbn in *.
      { now eapply surjectTape_isRight. }
      { intros. simpl_tape. cbn. rewrite Vector.const_nth. eapply surjectTape_isRight. eauto. }
      repeat split.
      + eapply contains_translate_tau2; eauto.
        destruct HDef as [[HDef1 HDef2] | HDef1]; eauto.
      + eapply contains_translate_tau2; eauto.
        destruct HDef as [[HDef1 HDef2] | HDef1]; eauto.
      + intros i. specialize (HComp3 i).
        erewrite VectorSpec.nth_map2 in HComp3; eauto. cbn in HComp3. rewrite VectorSpec.const_nth in HComp3.
        change (isRight (surjectTape defX retr tout[@Fin.FS (Fin.FS i)])) in HComp3.
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
*)