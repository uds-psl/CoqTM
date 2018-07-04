Require Import TM.Prelim TM.TM.


Section MirrorTM.
  Variable (n : nat) (sig : finType).

  Definition mirror_act : (option sig * move) -> (option sig * move) :=
    map_right mirror_move.

  Definition mirror_acts : Vector.t (option sig * move) n -> Vector.t (option sig * move) n :=
    Vector.map mirror_act.

  Lemma mirror_act_involution a : mirror_act (mirror_act a) = a.
  Proof. destruct a. cbn. rewrite mirror_move_involution. reflexivity. Qed.

  Lemma mirror_acts_involution acts :
    mirror_acts (mirror_acts acts) = acts.
  Proof.
    unfold mirror_acts. apply Vector.eq_nth_iff. intros ? ? ->.
    erewrite !Vector.nth_map; eauto. apply mirror_act_involution.
  Qed.
    
  
  Variable F : finType.
  Variable pM : { M : mTM sig n & states M -> F }.

  Definition Mirror_trans :
    states (projT1 pM) * Vector.t (option sig) n ->
    states (projT1 pM) *
    Vector.t (option sig * move) n :=
    fun qsym =>
      let (q', act) := trans qsym in
      (q', mirror_acts act).

  Definition MirrorTM : mTM sig n :=
    {|
      trans := Mirror_trans;
      start := start (projT1 pM);
      halt := halt (m := projT1 pM);
    |}.

  Definition Mirror : pTM sig F n :=
    (MirrorTM; projT2 pM).

  Definition mirrorConf : mconfig sig (states (projT1 pM)) n -> mconfig sig (states (projT1 pM)) n :=
    fun c => mk_mconfig (cstate c) (mirror_tapes (ctapes c)).

  Lemma mirrorConf_involution s : mirrorConf (mirrorConf s) = s.
  Proof.
    destruct s. unfold mirrorConf. cbn. f_equal. apply mirror_tapes_involution.
  Qed.

  Lemma mirror_step c1 c2 :
    step (M := projT1 Mirror) (mirrorConf c1) = mirrorConf c2 ->
    step (M := projT1 pM    ) (      c1) =       c2.
  Proof.
    intros H. unfold step in *. cbn in *. unfold Mirror_trans in *.
    destruct (trans (cstate c1, current_chars (ctapes c1))) as (q'&act') eqn:E.
    destruct (trans (cstate c1, current_chars (mirror_tapes (ctapes c1)))) as (q''&act'') eqn:E2.
    unfold mirrorConf in *. destruct c1 as (qi,ti), c2 as (qo, to). cbn in *. inv H.
    replace (current_chars (mirror_tapes ti)) with (current_chars ti) in E2.
    rewrite E2 in E. inv E. f_equal. 
    - apply Vector.eq_nth_iff. intros ? k ->. erewrite !Vector.nth_map2; eauto.
      eapply Vector.eq_nth_iff with (p1 := k) in H2; eauto. unfold tape_move_mono, mirror_tapes, mirror_acts in *.
      erewrite !Vector.nth_map2, !Vector.nth_map in H2; eauto. destruct (act'[@k]) eqn:E3. cbn in *.
      replace (tape_move (tape_write (mirror_tape ti[@k]) o) (mirror_move m)) with
          (mirror_tape ((tape_move (tape_write ti[@k] o)) m)) in H2.
      + now apply mirror_tape_injective in H2.
      + generalize (ti[@k]) as t. intros t. destruct o, m, t; cbn; auto; destruct l; cbn; auto; now destruct l0.
    - apply Vector.eq_nth_iff; intros ? k ->. autounfold with tape. now simpl_tape.
  Qed.
                                     
  Lemma mirror_step' c1 c2 :
    step (M := projT1 Mirror) (      c1) =       c2 ->
    step (M := projT1 pM    ) (mirrorConf c1) = mirrorConf c2.
  Proof.
    intros H. rewrite <- (mirrorConf_involution c1), <- (mirrorConf_involution c2). eapply mirror_step. now rewrite !mirrorConf_involution.
  Qed.

  Lemma mirror_loop k c1 c2 :
    loopM (M := projT1 Mirror) k c1         = Some c2 ->
    loopM (M := projT1 pM    ) k (mirrorConf c1) = Some (mirrorConf c2).
  Proof.
    unfold loopM, haltConf. revert c1. induction k; intros c1 H; cbn in *.
    - cbn in *. unfold haltConf. cbn. destruct (halt (cstate c1)); now inv H.
    - cbn in *. destruct (halt (cstate c1)) eqn:E.
      + congruence.
      + erewrite mirror_step'; eauto. 
  Qed.

  Lemma mirror_loop' k c1 c2 :
    loopM (M := projT1     pM) k (mirrorConf c1) = Some (mirrorConf c2) ->
    loopM (M := projT1 Mirror) k (      c1) = Some (      c2).
  Proof.
    unfold loopM, haltConf. destruct c2 as [q2 t2]. revert c1. induction k as [ | k' IH]; intros [q1 t1] H; cbn in *.
    - destruct (halt q1); inv H. f_equal. f_equal. now apply mirror_tapes_injective in H2.
    - destruct (halt q1) eqn:E; cbn in *.
      + inv H. f_equal. f_equal. now apply mirror_tapes_injective in H2.
      + erewrite mirror_step' in H; eauto.
  Qed.
  

  Definition Mirror_Rel (R : pRel sig F n) : pRel sig F n :=
    fun t '(f, t') => R (mirror_tapes t) (f, mirror_tapes t').
  
  Lemma Mirror_Realise R :
    pM ⊨ R -> Mirror ⊨ Mirror_Rel R.
  Proof.
    intros HRealise. intros t i outc HLoop.
    apply (HRealise (mirror_tapes t) i (mirrorConf outc)).
    now apply mirror_loop in HLoop.
  Qed.

  Definition Mirror_T (T : tRel sig n) : tRel sig n :=
    fun t k => T (mirror_tapes t) k.

  Lemma Mirror_Terminates T :
    projT1 pM ↓ T -> projT1 Mirror ↓ Mirror_T T.
  Proof.
    intros HTerm. hnf. intros t1 k H1. hnf in HTerm. specialize (HTerm (mirror_tapes t1) k H1) as (outc&H).
    exists (mirrorConf outc). apply mirror_loop'. cbn. now rewrite mirrorConf_involution.
  Qed.
  
  Lemma Mirror_RealiseIn R (k : nat) :
    pM ⊨c(k) R -> Mirror ⊨c(k) Mirror_Rel R.
  Proof.
    intros H.
    eapply Realise_total. split.
    - eapply Mirror_Realise. now eapply Realise_total.
    - eapply TerminatesIn_monotone.
      + eapply Mirror_Terminates. now eapply Realise_total.
      + firstorder.
  Qed.

End MirrorTM.

Arguments Mirror : simpl never.
Arguments Mirror_Rel { n sig F } R x y /.
Arguments Mirror_T { n sig } T x y /.


Ltac smpl_TM_Mirror :=
  match goal with
  | [ |- Mirror _ ⊨ _ ] => eapply Mirror_Realise
  | [ |- Mirror _ ⊨c(_) _ ] => eapply Mirror_RealiseIn
  | [ |- projT1 (Mirror _) ↓ _ ] => eapply Mirror_Terminates
  end.

Smpl Add smpl_TM_Mirror : TM_Correct.