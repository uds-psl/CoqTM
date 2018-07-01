Require Export TM Nop.
Require Import Shared.FiniteTypes.DepPairs EqdepFacts.

Section Match.

  Variable n : nat.
  Variable sig : finType.

  Variable F : finType.

  Variable pM1 : pTM sig F n.
  Variable F' : finType.
  Variable pMf : F -> pTM sig F' n.

  Notation "'M1'" := (projT1 pM1) (only parsing).
  Notation "'p1'":= (projT2 pM1) (only parsing).

  Notation "'Mf' f" := (projT1 (pMf f)) (only parsing, at level 10).
  Notation "'p2' f" := (projT2 (pMf f)) (only parsing, at level 10).

  Definition Match_trans :
    (TM.states M1 + { f : F & TM.states (Mf f) }) * Vector.t (option sig) n ->
    (TM.states M1 + { f : F & TM.states (Mf f) }) * Vector.t (option sig * move) n :=
    fun '(q, s) =>
        match q with
        | inl q =>
          if halt q
          then (inr (existT _ (p1 q) (start (Mf (p1 q)))), null_action)
          else let (q', a) := trans (q, s) in (inl q', a)
        | inr q =>
          let (q', a) := trans (projT2 q, s) in
          (inr (existT _ (projT1 q) q'), a)
        end.

  Definition Match_halt : (TM.states M1 + { f : F & TM.states (Mf f) }) -> bool :=
    fun q => 
      match q with
      | inl _ => false
      | inr q => halt (projT2 q)
      end.
  
  Definition Match : mTM sig n :=
    {|
      trans := Match_trans;
      halt  := Match_halt;
      start := inl (start M1);
    |}.

  
  Definition Match_p : (states Match) -> F' :=
    fun q => match q with
          | inl q => p2 (p1 q) (start (Mf (p1 q))) (* Canonical value *)
          | inr q => p2 (projT1 q) (projT2 q)
          end.
  
  Definition MATCH := (Match; Match_p).
  

  (** Lift configurations of [M1] to configurations of [Match] *)
  Definition lift_confL (c : mconfig sig (states M1) n) : mconfig sig (states Match) n :=
    mk_mconfig (inl (cstate c)) (ctapes c).


  (** Lift configuration of [M2] to configurations of [Match] *)
  Definition lift_confR (f : F) (c : mconfig sig (states (Mf f) ) n) : mconfig sig (states Match) n :=
    mk_mconfig (inr (existT (fun f0 : F => states (Mf f0)) f (cstate c))) (ctapes c).

  (** Lifted Steps of [M1] are compatible with steps in [M1], for non-halting states *)
  Lemma step_comp_liftL (c : mconfig sig (states M1) n) :
    halt (cstate c) = false -> lift_confL (step c) = step (lift_confL c).
  Proof.
    destruct c; cbn. unfold lift_confL, step. cbn. intros H. rewrite H.
    destruct (trans _) eqn:E. cbn. reflexivity.
  Qed.

  (** Lifted steps of case-machines [Mf f] are compatible with steps in [Mf f] *)
  Lemma step_comp_liftR f (c : mconfig sig (states (Mf f)) n) :
    lift_confR (step c) = step (lift_confR c).
  Proof.
    destruct c. unfold lift_confR, step. cbn.
    destruct (trans _) eqn:E. cbn. reflexivity.
  Qed.

  (** Lifted halting states of [M1] *)
  Definition halt_liftL (c : mconfig sig (states (Match)) n) :=
    match cstate c with
    | inl q => halt (m := M1) q
    | inr q => halt (m := Mf (projT1 q)) (projT2 q)
    end.


  (** Non-halting states of [M1] are non-halting states of [Match] *)
  Lemma halt_conf_liftL (c : mconfig sig (states Match) n) :
    halt_liftL c = false -> halt (cstate c) = false.
  Proof.
    intros H. cbn. unfold Match_halt.
    destruct c as [q t]; cbn.
    destruct q; cbn in *; auto.
  Qed.

  (** The "nop" transition jumps from a halting configuration of [M1] to the initial configuration of the corresponding case-machine. *)
  Lemma step_nop_transition (c : mconfig sig (states M1) n) :
    haltConf c = true ->
    step (lift_confL c) = lift_confR (initc (Mf (p1 (cstate c))) (ctapes c)).
  Proof.
    intros Halt.
    unfold lift_confL, lift_confR. cbn. unfold haltConf in Halt.
    unfold step at 1; cbn.
    rewrite Halt. f_equal.
    apply tape_move_null_action.
  Qed.

  (** The starting configuration of [Match] corresponds to the starting configuration of [M1]. *)
  Lemma lift_initc t :
    initc Match t = lift_confL (initc M1 t).
  Proof. reflexivity. Qed.

  (** This lemma is needed for the termination part. Suppose [M1] terminates in [c1].  The case machine [Mf f] starts with the tapes of [c1] and terminates in a configuration [c2]. Then, if we start [Match] with the same tapes as [M1], [Match] terminates in the lifted configuration of [c2]. *)
  Lemma Match_merge t (k1 k2 : nat)
        (c1 : mconfig sig (states M1) n)
        (c2 : mconfig sig (states (Mf (p1 (cstate c1)))) n) :
    loopM k1 (initc M1 t) = Some c1 ->
    loopM k2 (initc (Mf (p1 (cstate c1))) (ctapes c1)) = Some c2 ->
    loopM (k1 + (1 + k2)) (initc Match t) = Some (lift_confR c2).
  Proof.
    intros HLoop1 HLoop2. unfold loopM in *.
    apply loop_merge with (p := halt_liftL) (a2 := lift_confL c1).
    - apply halt_conf_liftL.
    - rewrite lift_initc.
      apply loop_lift with (h := haltConf (M := M1)) (f := step (M := M1)).
      + unfold haltConf. intros. cbn. reflexivity.
      + apply step_comp_liftL.
      + apply HLoop1.
    - (* execute one step *)
      change (loop (1 + k2) (step (M:=Match)) (haltConf (M:=Match)) (lift_confL c1))
        with (loop k2 (step (M:=Match)) (haltConf (M:=Match)) (step (lift_confL c1))).
      eapply loop_lift with (lift := lift_confR (f := p1 (cstate c1))) (g := step (M := Match)) (hlift := haltConf (M := Match)) in HLoop2.
      + rewrite <- HLoop2. f_equal. apply step_nop_transition. apply (loop_fulfills_p HLoop1).
      + intros. cbn. reflexivity.
      + intros. apply step_comp_liftR.
  Qed.


  (** The unlift functions map the configuration/state of [Match] to the corresponding states of either [M1] or some [Mf f]. *)
  Definition unlift_confL : mconfig sig (states Match) n -> option (mconfig sig (states M1) n) :=
    fun c =>
      match (cstate c) with
      | inl q => Some (mk_mconfig q (ctapes c))
      | inr _ => None
      end.

  Definition unlift_confR (f : F) : mconfig sig (states Match) n -> option (mconfig sig (states (Mf f)) n).
  Proof.
    cbn in *.
    refine (fun c =>
              match (cstate c) with
              | inl _ => None
              | inr q => _
              end).
    destruct q as [y q]. decide (y = f) as [e | _].
    - refine (Some (mk_mconfig _ (ctapes c))).
      rewrite <- e. apply q.
    - apply None.
  Defined.


  (** The lift and unlift functions are retracts. *)
  Lemma retract_L (c : mconfig sig (states Match) n) (c' : mconfig sig (states M1) n) :
    unlift_confL c = Some c' -> c = lift_confL c'.
  Proof.
    destruct c as [q t]. unfold unlift_confL, lift_confL. cbn. intros H.
    destruct q as [ q | ?]; inv H. cbn. reflexivity.
  Qed.

  Lemma retract_L' (f : F) (c : mconfig sig (states M1) n) :
    unlift_confL (lift_confL c) = Some c.
  Proof. destruct c as [q t]. unfold unlift_confL, lift_confL. cbn. reflexivity. Qed.
  

  Lemma retract_R (f : F) (c : mconfig sig (states Match) n) (c' : mconfig sig (states (Mf f)) n) :
    unlift_confR f c = Some c' -> c = lift_confR c'.
  Proof.
    destruct c as [q t]. unfold unlift_confR, lift_confR. cbn. intros H.
    destruct q as [ q | [y q]]. inv H.
    decide (y = f) as [ -> | ?]; inv H.
    cbn. reflexivity.
  Qed.

  Lemma retract_R' (f : F) (c : mconfig sig (states (Mf f)) n) :
    unlift_confR f (lift_confR c) = Some c.
  Proof.
    destruct c as [q t]. unfold unlift_confR, lift_confR. cbn. decide (f=f); try tauto.
    f_equal. f_equal.
    erewrite <- Eqdep_dec.eq_rect_eq_dec; auto. apply eqType_dec.
  Qed.


  (** If the configuration [c] of [Match] corresponds to the non-halting configuration [c'] of [M1], then [Match] simulates the step a step from [c']. *)
  Lemma unlift_confL_step (c : mconfig sig (states Match) n) (c' : mconfig sig (states M1) n) :
    unlift_confL c = Some c' ->
    haltConf c' = false ->
    unlift_confL (step c) = Some (step c').
  Proof.
    intros HUnlift HHalt. unfold haltConf in HHalt.
    destruct c as [q t]. cbn in *.
    unfold unlift_confL in *. cbn in *.
    destruct q; inv HUnlift.
    unfold step; cbn in *. rewrite HHalt.
    now destruct trans.
  Qed.
  
  (** If the configuration [c] of [Match] corresponds to the non-halting configuration [c'] of [Mf f], then [Match] simulates the step a step from [c']. *)
  Lemma unlift_confR_step f (c : mconfig sig (states Match) n) (c' : mconfig sig (states (Mf f)) n) :
    unlift_confR f c = Some c' ->
    haltConf c' = false ->
    unlift_confR f (step c) = Some (step c').
  Proof.
    intros HUnlift HHalt.
    destruct c as [q t]. cbn in *.
    unfold step. cbn [cstate ctapes].
    unfold unlift_confR in *. cbn [cstate ctapes] in HUnlift.
    destruct q as [q | [y q]]. inv HUnlift.
    decide (y=f) as [ -> | _].
    - inv HUnlift. cbn in *.
      destruct (trans (q, current_chars t)) as [nextq acts] eqn:E. cbn.
      decide (f=f); try tauto. f_equal. f_equal.
      erewrite <- Eqdep_dec.eq_rect_eq_dec; auto. apply eqType_dec.
    - inv HUnlift.
  Qed.


  (** Is the configuration [c] of [Match] a halting state of [M1] or no state of [M1] at all? *)
  Definition halt_unliftL : mconfig sig (states Match) n -> bool :=
    fun c =>
      match unlift_confL c with
      | Some c' => haltConf c'
      | None => default (* this is no configuration of [M1] *)
      end.


  Lemma halt_comp_unliftL (c : mconfig sig (states Match) n) :
    halt_unliftL c = false ->
    haltConf c = false.
  Proof.
    destruct c as [q t]. cbn. unfold halt_unliftL, unlift_confL. cbn.
    intros H. destruct q as [q | ?]; cbn in *; auto.
  Qed.

  (** If [c] is a state of [Match] that corresponds to a state [c'] of [M1], then the values of the halting functions are compatible. *)
  Lemma halt_sim_unliftL (c : mconfig sig (states Match) n) (c' : mconfig sig (states M1) n) :
    unlift_confL c = Some c' ->
    haltConf c' = halt_unliftL c.
  Proof. intros -> % retract_L. cbn. now destruct c'. Qed.


  (* XXX: Has it to be true or false? *)
  Arguments default : simpl never.

  Definition halt_unliftR (f : F) : mconfig sig (states Match) n -> bool :=
    fun c =>
      match unlift_confR f c with
      | Some c' => haltConf c'
      | None => default (* this is no configuration of [Mf f] *)
      end.

  Lemma halt_sim_unliftR (f : F) (c : mconfig sig (states Match) n) (c' : mconfig sig (states (Mf f)) n) :
    unlift_confR f c = Some c' ->
    haltConf c' = halt_unliftR f c.
  Proof.
    intros -> % retract_R.
    unfold halt_unliftR, unlift_confR. cbn.
    decide (f=f); try tauto.
    destruct c'; cbn. f_equal. f_equal.
    erewrite <- Eqdep_dec.eq_rect_eq_dec; auto. apply eqType_dec.
  Qed.
    

  (** The [Match] machine must take the "nop" action if it is in a final state of [M1]. *)
  Lemma step_nop_split (k2 : nat) (c2 : mconfig sig (states M1) n) (outc : mconfig sig (states Match) n) :
    haltConf c2 = true ->
    loop k2 (step (M:=Match)) (haltConf (M:=Match)) (lift_confL c2) = Some outc ->
    exists k2' c2',
      k2 = S k2' /\
      loopM (M := Mf (p1 (cstate c2))) k2' (initc _ (ctapes c2)) = Some c2' /\
      outc = lift_confR c2'.
  Proof.
    unfold loopM. intros HHalt HLoop2. unfold haltConf in HHalt.
    destruct k2 as [ | k2'].
    - inv HLoop2.
    - exists k2'. cbn in HLoop2.
      replace (step (lift_confL c2)) with (lift_confR (initc (Mf (p1 (cstate c2))) (ctapes c2))) in HLoop2; cycle 1.
      { cbv [step]. cbn -[tape_move_multi]. rewrite HHalt. rewrite tape_move_null_action. reflexivity. }
      apply loop_unlift with (unlift := @unlift_confR (p1 (cstate c2)))
                              (a := initc (Mf (p1 (cstate c2))) (ctapes c2))
                              (f := step (M := Mf (p1 (cstate c2))))
                              (p := haltConf (M := Mf (p1 (cstate c2)))) in HLoop2
        as (c2'&HLoop2&HLoop2').
      + apply retract_R in HLoop2' as ->.  exists c2'. repeat split; auto.
      + intros. now apply unlift_confR_step.
      + intros ? ? -> % retract_R. cbn. now destruct a.
      + apply retract_R'.
  Qed.


  Lemma Match_split i t (outc : mconfig sig (states Match) n) :
    loopM i (initc Match t) = Some outc ->
    exists k1 (c1 : mconfig sig (states M1) n) k2 (c2 : mconfig sig (states (Mf (p1 (cstate c1)))) n),
      loopM k1 (initc M1 t) = Some c1 /\
      loopM k2 (initc (Mf (p1 (cstate c1))) (ctapes c1)) = Some c2 /\
      outc = lift_confR c2.
  Proof.
    unfold loopM. intros H.
    apply loop_split with (p := halt_unliftL) in H as (k1&c1&k2&HLoop1&HLoop2&->).
    - eapply loop_unlift with (unlift := unlift_confL) (a := initc M1 t) (f := step (M := M1)) (p := haltConf (M := M1)) in HLoop1
        as (c1'&HLoop1&HLoop1').
      + apply retract_L in HLoop1' as ->.
        move HLoop2 at bottom.
        apply step_nop_split in HLoop2 as (k2'&c2'&->&HLoop2&->). 2: exact (loop_fulfills_p HLoop1).
        exists k1, c1', k2', c2'. auto.
      + intros. now apply unlift_confL_step.
      + intros. now apply halt_sim_unliftL.
      + reflexivity.
    - apply halt_comp_unliftL.
  Qed.


  
  (** Correctness *)
  Lemma Match_Realise (R1 : Rel _ (F * _)) (R2 : F -> Rel _ (F' * _)) :
    pM1 ⊨ R1 ->
    (forall f : F, pMf f ⊨ R2 f) -> MATCH ⊨ (⋃_f (R1 |_ f) ∘ R2 f).
  Proof.
    intros HRel1 HRel2. hnf in HRel1.
    hnf. intros t i outc HLoop.
    apply Match_split in HLoop as (k1&c1&k2&c2&HLoop1&HLoop2&->). cbn.
    exists (p1 (cstate c1)), (ctapes c1). split.
    - apply (HRel1 _ _ _ HLoop1).
    - apply (HRel2 _ _ _ _ HLoop2).
  Qed.


  (** Runtime *)
  Lemma Match_TerminatesIn (R1 : Rel _ (F * _)) T1 T2 :
    pM1 ⊨ R1 -> M1 ↓ T1 -> (forall f : F, Mf f ↓(T2 f)) ->
    projT1 MATCH ↓ (fun tin i => exists i1 i2, T1 tin i1 /\ 1 + i1 + i2 <= i /\ forall tout yout, R1 tin (yout, tout) -> T2 yout tout i2).
  Proof.
    unfold MATCH. intros HRel1 HTerm1 HTerm2. hnf in HRel1, HTerm1.
    hnf. intros t i (i1&i2&HT1&Hk&H).
    specialize HTerm1 with (1 := HT1) as (c1&HLoop1).
    specialize HRel1 with (1 := HLoop1).
    specialize H with (1 := HRel1).
    specialize (HTerm2 _ _ _ H) as (c2&HLoop2).
    pose proof Match_merge HLoop1 HLoop2 as HLoop.
    exists (lift_confR c2). eapply loop_ge. 2: apply HLoop. omega.
  Qed.


  (** Correct + constant runtime *)
  Lemma Match_RealiseIn (R1 : Rel _ (F * _)) (R2 : F -> Rel _ (F' * _)) k1 k2:
    pM1 ⊨c(k1) R1 ->
    (forall f : F, pMf f ⊨c(k2) R2 f) ->
    MATCH ⊨c(1 + k1 + k2) (⋃_f (R1 |_ f) ∘ R2 f).
  Proof.
    intros (H1&H2) % Realise_total H3. apply Realise_total. split.
    - eapply Match_Realise; eauto. intros ?. eapply Realise_total; eauto.
    - eapply TerminatesIn_monotone.
      + apply Match_TerminatesIn; eauto. intros ?. eapply Realise_total; eauto.
      + firstorder.
  Qed.


End Match.
(* Arguments MATCH {n} {sig} {F} pM1 {_} pMf : clear implicits. *)


Arguments MATCH : simpl never.