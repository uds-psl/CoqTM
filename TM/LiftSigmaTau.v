Require Import TM.Prelim TM.Relations TM.TM.


Section SujectTape.
  Variable sig tau : Type.
  Variable g : tau -> option sig.
  Variable def : sig.

  Definition surject : tau -> sig := fun t => match (g t) with Some s => s | None => def end.

  Definition surjectTape := mapTape surject.

End SujectTape.

Hint Unfold surjectTape : tape.


Section lift_sigma_tau.
  Variable n : nat.
  Variable sig tau : Type.
  Variable g : tau -> option sig.
  Variable def : Vector.t sig n.
  Variable F : Type.

  Definition surjectTapes : tapes tau n -> tapes sig n :=
     Vector.map2 (fun d t => surjectTape g d t) def.
  
  Definition lift_sigma_tau_Rel (R : Rel (tapes sig n) (F * tapes sig n)) :
    Rel (tapes tau n) (F * tapes tau n) :=
    fun tin '(yout,tout) => R (surjectTapes tin) (yout, surjectTapes tout).

  Definition lift_sigma_tau_T (T : Rel (Vector.t (tape sig) n) nat) :
    Rel (Vector.t (tape tau) n) nat :=
    fun tin k => T (surjectTapes tin) k.

End lift_sigma_tau.


Arguments lift_sigma_tau_Rel {n sig tau} (g def) {F} (R) x y /.
Arguments lift_sigma_tau_T {n sig tau} (g def T) x y /.


Section InjectTape.

  Variable sig tau : Type.
  Variable f : sig -> tau.

  Definition injectTape := mapTape f.
  Definition injectTapes {n: nat} := mapTapes (n := n) f.
End InjectTape.

Section InjectSurject.
  Variable sig tau : Type.
  Variable inj : Retract sig tau.
  Variable def : sig.

  Lemma surject_inject' (l : list sig) :
    List.map (fun t : tau => match Retr_g t with
                          | Some s => s
                          | None => def
                          end) (List.map Retr_f l) = l.
  Proof.
    induction l; cbn.
    - reflexivity.
    - retract_adjoint. f_equal. assumption.
  Qed.
  
  Lemma surject_inject_tape (t : tape sig) :
    surjectTape Retr_g def (injectTape Retr_f t) = t.
  Proof.
    unfold surjectTape, injectTape, surject.
    destruct t; cbn; f_equal; try rewrite retract_g_adjoint; auto; apply surject_inject'.
  Qed.

  (*
  Lemma surject_inject_tapes {n : nat} (t : Vector.t (tape sig) n) :
    surjectTapes g def (injectTapes f t) = t.
  Proof.
    unfold surjectTapes, injectTapes, mapTapes.
    apply Vector.eq_nth_iff. intros p ? <-. 
    erewrite !Vector.nth_map; eauto.
    apply surject_inject_tape.
  Qed.
*)
  
End InjectSurject.

Section TranslateAct.
  Variable X Y : Type.
  Definition map_act : (X -> Y) -> option X * move -> option Y * move := fun f => map_left (map_opt f).
End TranslateAct.


Section LiftSigmaTau.
  Variable sig tau : finType.
  Variable n : nat.
  Variable F : finType.
  Variable pMSig : { M : mTM sig n & states M -> F}.

  Variable Inj : Retract sig  tau.

  Variable def : Vector.t sig n.

  Definition surjectReadSymbols : Vector.t (option tau) n -> Vector.t (option sig) n :=
    fun sym =>
      Vector.map2 (fun d => map_opt (surject Retr_g d)) def sym.

  Definition lift_trans :=
    fun '(q, sym) =>
      let (q', act) := trans (m := projT1 pMSig) (q, surjectReadSymbols sym) in
      (q', Vector.map (map_act Retr_f) act).

  Definition liftM : mTM tau n :=
    {| trans := lift_trans;
       start := start (projT1 pMSig);
       halt := halt (m := projT1 pMSig) |}.

  Definition Lift := (liftM; projT2 pMSig).

  
  Definition surjectConf : (mconfig tau (states liftM) n) -> (mconfig sig (states (projT1 pMSig)) n) :=
    fun c => mk_mconfig (cstate c) (surjectTapes Retr_g def (ctapes c)).

  Definition injectConf : (mconfig sig (states (projT1 pMSig)) n) -> (mconfig tau (states liftM) n) :=
    fun c => mk_mconfig (cstate c) (injectTapes Retr_f (ctapes c)).


  (* End definition *)

  Lemma surject_step :
    forall (tape : tape tau) (act : option sig * move) (d : sig),
      tape_move_mono (surjectTape Retr_g d tape) act =
      surjectTape Retr_g d (tape_move_mono tape (map_act Retr_f act)).
  Proof.
    intros tape. intros (w,m) d; cbn.
    unfold surjectTape, tape_move_mono, tape_move, tape_write, surject; cbn.
    destruct tape, m, w; cbn; f_equal; try retract_adjoint; auto.
    - destruct l; cbn; f_equal; now retract_adjoint.
    - destruct l; cbn; f_equal; now retract_adjoint.
    - destruct l0; cbn; f_equal; now retract_adjoint.
    - destruct l0; cbn; f_equal; now retract_adjoint.
  Qed.


  Lemma sim_step (c1 c2 : mconfig tau (states (projT1 pMSig)) n) :
    step (M := liftM) c1 = c2 ->
    step (M := projT1 pMSig) (surjectConf c1) = surjectConf c2.
  Proof.
    unfold surjectConf. intros H. cbn. 
    destruct c1 as [state1 tapes1] eqn:E1, c2 as [state2 tapes2] eqn:E2.
    cbv [step] in *. cbn -[map step] in *.
    destruct (trans (state1, surjectReadSymbols (current_chars tapes1))) as (q, act) eqn:E3.
    inv H.
    destruct (trans (state1, current_chars _)) as (q', act') eqn:E4.
    enough ((state2, act) = (q', act')) as X.
    {
      inv X. f_equal.
      unfold surjectTapes, mapTapes. apply Vector.eq_nth_iff. intros p ? <-.
      erewrite !Vector.nth_map2, !Vector.nth_map; eauto.
      apply surject_step.
    }
    rewrite <- E3, <- E4. do 2 f_equal.

    unfold surjectReadSymbols, current_chars.
    apply Vector.eq_nth_iff; intros p ? <-.
    unfold surjectTapes, mapTapes, surject. autounfold with tape.
    erewrite !Vector.nth_map2, !Vector.nth_map; eauto. cbn.
    simpl_tape. destruct (tapes1[@p]) eqn:E5; cbn; auto.
  Qed.

  Lemma sim_loop (c1 c2 : mconfig tau (states liftM) n) (i : nat) :
    loopM (M := liftM) i c1 = Some c2 ->
    loopM (M := projT1 pMSig) i (surjectConf c1) = Some (surjectConf c2).
  Proof.
    unfold loopM, haltConf in *. revert c2 c1. induction i; intros c2 c1 H; cbn in *.
    - destruct (halt _) eqn:E; now inv H.
    - destruct (halt _) eqn:E; inv H; auto.
      rewrite sim_step with (c1 := c1) (c2 := step (M := liftM) c1); [ | reflexivity]. apply IHi. apply H1.
  Qed.


  Lemma Lift_Realise (R : Rel (tapes sig n) (F * tapes sig n)) :
    pMSig ⊨ R ->
    Lift ⊨ lift_sigma_tau_Rel Retr_g def R.
  Proof.
    intros H. intros t i outc Hloop. unfold lift_sigma_tau_Rel. hnf in H.
    specialize (H (surjectTapes Retr_g def t) i (mk_mconfig (cstate outc) (surjectTapes Retr_g def (ctapes outc)))).
    cbn in H. apply H.
    now apply (@sim_loop (initc liftM t) outc i).
  Qed.


  Lemma propagate_step (conf : (mconfig tau (states (projT1 pMSig)) n)) :
    surjectConf (step (M := liftM) conf) = step (surjectConf conf).
  Proof.
    cbv [surjectConf]. cbv [step]. cbn.
    replace (surjectReadSymbols (current_chars (ctapes conf))) with
        (current_chars (surjectTapes Retr_g def (ctapes conf))).
    - destruct (trans (cstate conf, current_chars (surjectTapes Retr_g def (ctapes conf)))) eqn:E1; cbn.
      f_equal. unfold surjectTapes, mapTapes. apply Vector.eq_nth_iff. intros ? ? <-.
      unfold tape_move_multi.
      repeat first [erewrite !Vector.nth_map2; eauto | erewrite !Vector.nth_map; eauto].
      cbv [surject]. cbn.
      destruct (t[@p1]) eqn:E2; cbn. generalize ((ctapes conf)[@p1]) as t1. intros t1. cbn.
      symmetry. apply surject_step.
    - eapply Vector.eq_nth_iff. intros ? ? <-.
      unfold current_chars, surjectTapes, mapTapes, surjectReadSymbols, surjectTape.
      now repeat simpl_tape.
  Qed.

  Lemma propagate_loop (k : nat) iconf (oconf : mconfig sig (states (projT1 pMSig)) n) :
    loopM k (surjectConf iconf) = Some oconf ->
    exists oconf' : mconfig tau (states liftM) n,
      loopM k iconf = Some oconf'.
  Proof.
    revert iconf. unfold loopM, haltConf. induction k as [ | k IH ]; intros iconf HLoop; cbn in *.
    - destruct (halt _); inv HLoop. unfold injectConf. cbn. eauto.
    - destruct (halt _) eqn:E1; eauto.
      replace (step (surjectConf iconf)) with (surjectConf (step (M := liftM) iconf)) in HLoop.
      + specialize (IH _ HLoop) as (oconf'&IH). eauto.
      + apply propagate_step.
  Qed.

  Lemma Lift_TerminatesIn (T : Rel (tapes sig n) nat) :
    projT1 pMSig ↓ T ->
    liftM ↓ lift_sigma_tau_T Retr_g def T.
  Proof.
    intros H. hnf. intros tin k HTerm. hnf in HTerm, H. specialize (H _ _ HTerm) as (oconf&HLoop).
    eapply propagate_loop; eauto.
  Qed.

  Lemma Lift_RealiseIn (R : Rel (tapes sig n) (F * tapes sig n)) (k : nat) :
    pMSig ⊨c(k) R ->
    Lift ⊨c(k) lift_sigma_tau_Rel Retr_g def R.
  Proof.
    intros [H1 H2] % Realise_total. eapply Realise_total. split; cbn in *.
    - now eapply Lift_Realise.
    - eapply Lift_TerminatesIn in H2. auto.
  Qed.

End LiftSigmaTau.

Arguments Lift : simpl never.

Ltac smpl_TM_LiftSigma :=
  match goal with
  | [ |- Lift _ _ _ ⊨ _] => eapply Lift_Realise; swap 1 2
  | [ |- Lift _ _ _ ⊨c(_) _] => eapply Lift_RealiseIn; swap 1 2
  | [ |- projT1 (Lift _ _ _) ↓ _] => eapply Lift_TerminatesIn; swap 1 2
  end.
Smpl Add smpl_TM_LiftSigma : TM_Correct.