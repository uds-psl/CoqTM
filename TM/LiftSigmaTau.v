Require Import TM.Prelim TM.Relations TM.TM.


Section SujectTape.
  Variable sig tau : finType.
  Variable g : tau -> option sig.
  Variable def : sig.

  Definition surject : tau -> sig := fun t => match (g t) with Some s => s | None => def end.

  Definition surjectTape := mapTape surject.
  Definition surjectTapes {n : nat} := mapTapes (n := n) surject.

  (*
  Lemma surjectTapes_nth {n : nat} (k : Fin.t n) (ts : tapes tau n) :
    (surjectTapes ts)[@k] = surjectTape(ts[@k]).
  Proof. unfold surjectTapes. now simpl_tape. Qed.
   *)

End SujectTape.

Arguments surjectTapes : simpl never.
(*
Hint Rewrite surjectTapes_nth : tape.
*)
Hint Unfold surjectTape surjectTapes : tape.

Section lift_sigma_tau.
  Variable n : nat.
  Variable sig tau : finType.
  Variable g : tau -> option sig.
  Variable def : sig.
  Variable Z : Type.
  
  Definition lift_sigma_tau (R : Rel (Vector.t (tape sig) n) (Vector.t (tape sig) n)) :
    Rel (Vector.t (tape tau) n) (Vector.t (tape tau) n) :=
    fun x y => R (surjectTapes g def x) (surjectTapes g def y).

  Definition lift_sigma_tau_p (R : Rel (Vector.t (tape sig) n) (Z * Vector.t (tape sig) n)) :
    Rel (Vector.t (tape tau) n) (Z * Vector.t (tape tau) n) :=
    fun x '(z,y) => R (surjectTapes g def x) (z, surjectTapes g def y).

  Definition lift_sigma_tau_T (T : Rel (Vector.t (tape sig) n) nat) :
    Rel (Vector.t (tape tau) n) nat :=
    fun x k => T (surjectTapes g def x) k.

End lift_sigma_tau.

Arguments lift_sigma_tau { n sig tau } ( g def R ) x y /.
Arguments lift_sigma_tau_p { n sig tau } ( g def ) { Z } ( R ) x y /.
Arguments lift_sigma_tau_T { n sig tau } ( g def T ) x y /.


Section InjectTape.

  Variable sig tau : finType.
  Variable f : sig -> tau.

  Definition injectTape := mapTape f.
  Definition injectTapes {n: nat} := mapTapes (n := n) f.
End InjectTape.

Section InjectSurject.
  Variable sig tau : finType.
  Variable (f : sig -> tau) (g : tau -> option sig).
  Hypothesis I : retract f g.
  Variable def : sig.

  Lemma surject_inject' (l : list sig) :
    List.map (fun t : tau => match g t with
                          | Some s => s
                          | None => def
                          end) (List.map f l) = l.
  Proof.
    induction l; cbn.
    - reflexivity.
    - retract_adjoint. f_equal. assumption.
  Qed.
  
  Lemma surject_inject_tape (t : tape sig) :
    surjectTape g def (injectTape f t) = t.
  Proof.
    unfold surjectTape, injectTape, surject.
    destruct t; cbn; f_equal; try rewrite retract_g_adjoint; auto; apply surject_inject'.
  Qed.

  Lemma surject_inject_tapes {n : nat} (t : Vector.t (tape sig) n) :
    surjectTapes g def (injectTapes f t) = t.
  Proof.
    unfold surjectTapes, injectTapes, mapTapes.
    apply Vector.eq_nth_iff. intros p ? <-. 
    erewrite !Vector.nth_map; eauto.
    apply surject_inject_tape.
  Qed.
  
End InjectSurject.

Section TranslateAct.
  Variable X Y : finType.
  Definition map_act : (X -> Y) -> option X * move -> option Y * move := fun f => map_left (map_opt f).
  Compute map_act.
End TranslateAct.

Section LiftSigmaTau.
  Variable sig tau : finType.
  Variable n : nat.
  Variable F : finType.
  Variable pMSig : { M : mTM sig n & states M -> F}.

  Variable (f : sig -> tau) (g : tau -> option sig).
  Hypothesis I : retract f g.
  Variable def : sig.
  Definition g' : tau -> sig := surject g def.


  Definition lift_trans :=
    fun '(q, symm) =>
      let (q', act) := trans (m := projT1 pMSig) (q, Vector.map (map_opt g') symm) in
      (q', Vector.map (map_act f) act).

  Definition liftM : mTM tau n.
  Proof.
    econstructor.
    exact lift_trans.
    exact (start (projT1 pMSig)).
    exact (halt (m := projT1 pMSig)).
  Defined.

  Definition Lift := (liftM; projT2 pMSig).

  Ltac dup H := let H' := fresh H in pose proof H as H'.

  Lemma surject_step :
    forall (tape : tape tau) (act : option sig * move),
      tape_move_mono (mapTape (surject g def) tape) act =
      mapTape (surject g def)
              (tape_move_mono tape (map_act f act)).
  Proof.
    intros tape. intros (w,m).
    unfold tape_move_mono, tape_move, tape_write, surject. cbn.
    destruct tape; cbn;
      try (destruct m, w; cbn; f_equal; now rewrite retract_g_adjoint).
    destruct m, w; cbn.
    - unfold mapTape. cbn. destruct l; cbn; f_equal; now rewrite retract_g_adjoint.
    - unfold mapTape. cbn. destruct l; cbn; f_equal; now rewrite retract_g_adjoint.
    - unfold mapTape. cbn. destruct l, l0; cbn; f_equal; now rewrite retract_g_adjoint.
    - unfold mapTape. cbn. destruct l, l0; cbn; f_equal; now rewrite retract_g_adjoint.
    - unfold mapTape. cbn. destruct l, l0; cbn; f_equal; now rewrite retract_g_adjoint.
    - unfold mapTape. cbn. destruct l, l0; cbn; f_equal; now rewrite retract_g_adjoint.
  Qed.

  Lemma sim_step (c1 c2 : mconfig tau (states (projT1 pMSig)) n) :
    step (M := liftM) c1 = c2 ->
    step (M := projT1 pMSig) (mk_mconfig (cstate c1) (surjectTapes g def (ctapes c1))) =
    (mk_mconfig (cstate c2) (surjectTapes g def (ctapes c2))).
  Proof.
    intros H. cbn.
    destruct c1 as [state1 tapes1] eqn:E1, c2 as [state2 tapes2] eqn:E2.
    cbv [step] in *. cbn -[map step] in *.
    destruct (trans (state1, Vector.map (map_opt g') (current_chars tapes1))) as (q, act) eqn:E3.
    inv H.
    destruct (trans (state1, current_chars (surjectTapes g def tapes1)))
      as (q', act') eqn:E4.
    enough ((state2, act) = (q', act')) as X.
    {
      inv X. f_equal.
      unfold surjectTapes, mapTapes. apply Vector.eq_nth_iff. intros p ? <-.
      erewrite !Vector.nth_map, !Vector.nth_map2, !Vector.nth_map; eauto.
      apply surject_step.
    }
    rewrite <- E3, <- E4. do 2 f_equal.
    apply Vector.eq_nth_iff. intros p ? <-.
    unfold surjectTapes, mapTapes, surject, current.
    autounfold with tape. erewrite !Vector.nth_map; eauto. cbn.
    destruct (tapes1[@p]) eqn:E5; cbn; auto.
  Qed.

  Lemma sim_loop (c1 c2 : mconfig tau (states liftM) n) (i : nat) :
    loopM (M := liftM) i c1 = Some c2 ->
    loopM (M := projT1 pMSig) i (mk_mconfig (cstate c1) (surjectTapes g def (ctapes c1))) =
    Some (mk_mconfig (cstate c2) (surjectTapes g def (ctapes c2))).
  Proof.
    unfold loopM in *. revert c2 c1. induction i; intros c2 c1 H; cbn in *.
    - destruct (halt _) eqn:E; now inv H.
    - destruct (halt _) eqn:E; inv H; auto.
      rewrite sim_step with (c1 := c1) (c2 := step (M := liftM) c1); [ | reflexivity]. apply IHi. apply H1.
  Qed.


  Lemma Lift_WRealise (R : Rel (tapes sig n) (F * tapes sig n)) :
    pMSig ⊫ R ->
    Lift ⊫ lift_sigma_tau_p g def R.
  Proof.
    intros H. intros t i outc Hloop. unfold lift_sigma_tau_p.
    apply (H (surjectTapes g def t) i (mk_mconfig (cstate outc) (surjectTapes g def (ctapes outc)))).
    now apply (@sim_loop (initc liftM t) outc i).
  Qed.

  Definition surjectConf : (mconfig tau (states liftM) n) -> (mconfig sig (states (projT1 pMSig)) n) :=
    fun c => mk_mconfig (cstate c) (surjectTapes g def (ctapes c)).

  Definition injectConf : (mconfig sig (states (projT1 pMSig)) n) -> (mconfig tau (states liftM) n) :=
    fun c => mk_mconfig (cstate c) (injectTapes f (ctapes c)).

  Lemma propagate_step (conf : (mconfig tau (states (projT1 pMSig)) n)) :
    surjectConf (step (M := liftM) conf) = step (surjectConf conf).
  Proof.
    cbv [surjectConf]. cbv [step]. cbn.
    replace (Vector.map (map_opt g') (current_chars (ctapes conf))) with (current_chars (surjectTapes g def (ctapes conf))).
    - cbn. destruct (trans (cstate conf, current_chars (surjectTapes g def (ctapes conf)))) eqn:E1; cbn.
      f_equal. unfold surjectTapes, mapTapes. apply Vector.eq_nth_iff. intros ? ? <-.
      unfold tape_move_multi, tape_move_mono.
      repeat first [erewrite !Vector.nth_map2; eauto | erewrite !Vector.nth_map; eauto].
      cbv [surject]. cbn.
      destruct (t[@p1]) eqn:E2; cbn. generalize ((ctapes conf)[@p1]) as t1. intros t1. cbn.
      destruct o; cbn.
      + destruct m; cbn; simpl_tape. destruct (left t1) eqn:E3; cbn.
        * retract_adjoint. auto.
        * f_equal. retract_adjoint. auto.
        * destruct (right t1) eqn:E3; cbn.
          -- retract_adjoint. cbn. auto.
          -- retract_adjoint. auto.
        * f_equal. now retract_adjoint.
      + destruct m; cbn; simpl_tape; auto.
    - eapply Vector.eq_nth_iff. intros ? ? <-. unfold current_chars, surjectTapes, mapTapes.
      erewrite !Vector.nth_map; simpl_tape; eauto. reflexivity.
  Qed.

  Lemma propagate_loop (k : nat) tin (conf : mconfig sig (states (projT1 pMSig)) n) :
    loopM k (initc (projT1 pMSig) (surjectTapes g def tin)) = Some conf ->
    exists oconf' : (mconfig tau (states liftM) n),
      loopM k (initc liftM tin) = Some oconf'.
  Proof.
    unfold loopM.
    enough (forall iconf : mconfig tau (states (projT1 pMSig)) n,
               loop k (step (M:=projT1 pMSig)) (fun c : mconfig sig (states (projT1 pMSig)) n => halt (cstate c))
                    (surjectConf iconf) = Some conf ->
               exists oconf' : mconfig tau (states liftM) n,
                 loop k (step (M:=liftM)) (fun c : mconfig tau (states liftM) n => halt (cstate c)) iconf = Some oconf')
           by auto.
    induction k as [ | k IH ]; intros iconf HLoop; cbn in *.
    - destruct (halt _); inv HLoop. unfold injectConf. cbn. eauto.
    - destruct (halt _) eqn:E1; eauto.
      replace (step (surjectConf iconf)) with (surjectConf (step (M := liftM) iconf)) in HLoop.
      + specialize (IH _ HLoop) as (oconf'&IH). eauto.
      + apply propagate_step.
  Qed.

  Lemma Lift_TerminatesIn (T : Rel (tapes sig n) nat) :
    projT1 pMSig ↓ T ->
    liftM ↓ lift_sigma_tau_T g def T.
  Proof.
    intros H. hnf. intros tin k HTerm. hnf in HTerm, H. specialize (H _ _ HTerm) as (oconf&HLoop).
    eapply propagate_loop; eauto.
  Qed.

  Lemma Lift_RealiseIn (R : Rel (tapes sig n) (F * tapes sig n)) (k : nat) :
    pMSig ⊨c(k) R ->
    Lift ⊨c(k) lift_sigma_tau_p g def R.
  Proof.
    intros [H1 H2] % Realise_total. eapply Realise_total. split; cbn in *.
    - now eapply Lift_WRealise.
    - eapply Lift_TerminatesIn in H2. auto.
  Qed.

End LiftSigmaTau.

Arguments Lift : simpl never.