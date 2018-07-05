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

  Lemma mirrorConf_involution c : mirrorConf (mirrorConf c) = c.
  Proof. destruct c as [q t]. unfold mirrorConf. cbn. f_equal. apply mirror_tapes_involution. Qed.

  Lemma mirrorConf_injective c1 c2 : mirrorConf c1 = mirrorConf c2 -> c1 = c2.
  Proof. destruct c1 as [q1 t1], c2 as [q2 t2]. unfold mirrorConf. cbn. intros H; inv H. f_equal. now apply mirror_tapes_injective. Qed.

  Lemma current_chars_mirror_tapes (t : tapes sig n) :
    current_chars (mirror_tapes t) = current_chars t.
  Proof. apply Vector.eq_nth_iff; intros i ? <-. autounfold with tape. now simpl_tape. Qed.

  Lemma tape_move_mono_mirror_act (t : tape sig) (act : option sig * move) :
    tape_move_mono (mirror_tape t) act = mirror_tape (tape_move_mono t (mirror_act act)).
  Proof. now destruct act as [ [ s | ] [ | | ]]; cbn; simpl_tape. Qed.

  Lemma tape_move_multi_mirror_acts (t : tapes sig n) (acts : Vector.t (option sig * move) n) :
    tape_move_multi (mirror_tapes t) acts = mirror_tapes (tape_move_multi t (mirror_acts acts)).
  Proof.
    apply Vector.eq_nth_iff; intros i ? <-. unfold tape_move_multi, mirror_acts, mirror_tapes. simpl_tape. apply tape_move_mono_mirror_act.
  Qed.

  Lemma mirror_step c :
    step (M := projT1 pM) (mirrorConf c) = mirrorConf (step (M := projT1 Mirror) c).
  Proof.
    unfold step; cbn -[tape_move_multi]. unfold Mirror_trans. cbn.
    destruct c as [q t]; cbn. rewrite current_chars_mirror_tapes.
    destruct (trans (q, current_chars t)) as [q' acts].
    unfold mirrorConf; cbn. f_equal. apply tape_move_multi_mirror_acts.
  Qed.

  Lemma mirror_split k c1 c2 :
    loopM (M := projT1 Mirror) k             c1  = Some             c2 ->
    loopM (M := projT1 pM    ) k (mirrorConf c1) = Some (mirrorConf c2).
  Proof.
    unfold loopM. intros HLoop.
    apply loop_lift with (lift := mirrorConf) (f' := step (M:=projT1 pM)) (h' := haltConf (M:=projT1 pM)) in HLoop; auto.
    - intros ? _. now apply mirror_step.
  Qed.

  Lemma mirror_merge k c1 c2 :
    loopM (M := projT1     pM) k (mirrorConf c1) = Some (mirrorConf c2) ->
    loopM (M := projT1 Mirror) k (           c1) = Some (           c2).
  Proof.
    unfold loopM. intros HLoop.
    apply loop_unlift with (lift := mirrorConf) (f := step (M:=MirrorTM)) (h := haltConf (M:=MirrorTM)) in HLoop
      as (? & HLoop & <- % mirrorConf_injective); auto.
    - intros ? _. now apply mirror_step.
  Qed.


  Definition Mirror_Rel (R : pRel sig F n) : pRel sig F n :=
    fun t '(f, t') => R (mirror_tapes t) (f, mirror_tapes t').

  Lemma Mirror_Realise R :
    pM ⊨ R -> Mirror ⊨ Mirror_Rel R.
  Proof.
    intros HRealise. intros t i outc HLoop.
    apply (HRealise (mirror_tapes t) i (mirrorConf outc)).
    now apply mirror_split in HLoop.
  Qed.

  Definition Mirror_T (T : tRel sig n) : tRel sig n :=
    fun t k => T (mirror_tapes t) k.

  Lemma Mirror_Terminates T :
    projT1 pM ↓ T -> projT1 Mirror ↓ Mirror_T T.
  Proof.
    intros HTerm. hnf. intros t1 k H1. hnf in HTerm. specialize (HTerm (mirror_tapes t1) k H1) as (outc&H).
    exists (mirrorConf outc). apply mirror_merge. cbn. now rewrite mirrorConf_involution.
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