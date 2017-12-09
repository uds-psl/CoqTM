Require Import TM.Prelim TM.TM.

Section MirrorTM.

  Variable (n : nat) (sig : finType).

  (* FIXME: This should go somewhere else *)
  Definition mirror_tape (t : tape sig) : tape sig :=
    match t with
    | niltape _ => niltape _
    | leftof r rs => rightof r rs
    | rightof l ls => leftof l ls
    | midtape ls m rs => midtape rs m ls
    end.

  Lemma mirror_tape_left (t : tape sig) :
    left (mirror_tape t) = right t.
  Proof. now destruct t. Qed.

  Lemma mirror_tape_right (t : tape sig) :
    right (mirror_tape t) = left t.
  Proof. now destruct t. Qed.

  Lemma mirror_tape_current (t : tape sig) :
    current (mirror_tape t) = current t.
  Proof. now destruct t. Qed.

  Lemma mirror_tape_involution (t : tape sig) :
    mirror_tape (mirror_tape t) = t.
  Proof. destruct t; cbn; congruence. Qed.

  Lemma mirror_tape_injective (t1 t2 : tape sig) :
    mirror_tape t1 = mirror_tape t2 ->
    t1 = t2.
  Proof. destruct t1, t2; intros H; cbn in *; congruence. Qed.

  Definition mirror_tapes (t : tapes sig n) : tapes sig n := Vector.map mirror_tape t.

  Lemma mirror_tapes_involution (t : tapes sig n) :
    mirror_tapes (mirror_tapes t) = t.
  Proof.
    unfold mirror_tapes. apply Vector.eq_nth_iff. intros ? ? ->.
    erewrite !Vector.nth_map; eauto. apply mirror_tape_involution.
  Qed.

  Lemma mirror_tapes_injective (t1 t2 : tapes sig n) :
    mirror_tapes t1 = mirror_tapes t2 ->
    t1 = t2.
  Proof.
    intros H. unfold mirror_tapes in *. apply Vector.eq_nth_iff. intros ? ? ->.
    eapply Vector.eq_nth_iff with (p1 := p2) in H; eauto.
    erewrite !Vector.nth_map in H; eauto. now apply mirror_tape_injective.
  Qed.
  

  Definition mirror_move (D : move) : move := match D with | N => N | L => R | R => L end.

  Lemma mirror_move_involution (D : move) : mirror_move (mirror_move D) = D.
  Proof. now destruct D. Qed.

  Definition mirror_act : (option sig * move) -> (option sig * move) := map_right mirror_move.

  Definition mirror_acts : Vector.t (option sig * move) n -> Vector.t (option sig * move) n := Vector.map mirror_act.

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

  Definition Mirror : { M : mTM sig n & states M -> F } :=
    (Build_mTM Mirror_trans (start (projT1 pM)) (halt (m := projT1 pM)); projT2 pM).
  

  Definition mlift : mconfig sig (states (projT1 pM)) n -> mconfig sig (states (projT1 pM)) n :=
    fun c => mk_mconfig (cstate c) (mirror_tapes (ctapes c)).

  Lemma mlift_involution s : mlift (mlift s) = s.
  Proof.
    destruct s. unfold mlift. cbn. f_equal. now rewrite mirror_tapes_involution.
  Qed.

  Definition mhlift : mconfig sig (states (projT1 pM)) n -> bool :=
    fun c : mconfig sig (states (projT1 pM)) n => halt (cstate c).


  Definition Mirror_R (R : Rel (tapes sig n) (F * tapes sig n)) : Rel (tapes sig n) (F * tapes sig n) :=
    fun t '(f, t') => R (mirror_tapes t) (f, mirror_tapes t').

  Lemma mirror_step ic oc :
    step (M := projT1 Mirror) (mlift ic) = mlift oc ->
    step (M := projT1 pM    ) (      ic) =       oc.
  Proof.
    intros H. unfold step in *. cbn in *. unfold Mirror_trans in *.
    destruct (trans (cstate ic, current_chars (ctapes ic))) as (q'&act') eqn:E.
    destruct (trans (cstate ic, Vector.map (current (sig:=sig)) (mirror_tapes (ctapes ic)))) as (q''&act'') eqn:E2.
    unfold mlift in *. destruct ic as (qi,ti), oc as (qo, to). cbn in *. inv H.
    replace (Vector.map (current (sig:=sig)) (Vector.map mirror_tape ti)) with (Vector.map (current (sig:=sig)) ti) in E2.
    rewrite E2 in E. inv E. f_equal. 
    - apply Vector.eq_nth_iff. intros ? k ->. erewrite !Vector.nth_map2; eauto.
      eapply Vector.eq_nth_iff with (p1 := k) in H2; eauto. unfold tape_move_mono, mirror_tapes, mirror_acts in *.
      erewrite !Vector.nth_map2, !Vector.nth_map in H2; eauto. destruct (act'[@k]) eqn:E3. cbn in *.
      replace (tape_move (tape_write (mirror_tape ti[@k]) o) (mirror_move m)) with
          (mirror_tape ((tape_move (tape_write ti[@k] o)) m)) in H2.
      + now apply mirror_tape_injective in H2.
      + generalize (ti[@k]) as t. intros t. destruct o, m, t; cbn; auto; destruct l; cbn; auto; now destruct l0.
    - apply Vector.eq_nth_iff. intros ? k ->. erewrite !Vector.nth_map; eauto. symmetry. apply mirror_tape_current.
  Qed.
                                     
  Lemma mirror_step' ic oc :
    step (M := projT1 Mirror) (      ic) =       oc ->
    step (M := projT1 pM    ) (mlift ic) = mlift oc.
  Proof.
    intros H. rewrite <- (mlift_involution ic), <- (mlift_involution oc). eapply mirror_step. now rewrite !mlift_involution.
  Qed.

  Lemma mirror_loop i ic oc :
    loop i (step (M := projT1 Mirror)) mhlift ic         = Some oc ->
    loop i (step (M := projT1 pM    )) mhlift (mlift ic) = Some (mlift oc).
  Proof.
    unfold loopM. revert ic. induction i; intros ic H.
    {
      unfold mhlift, mlift in *. cbn in *. destruct (halt (cstate ic)); now inv H.
    }
    {
      cbn [loop] in *. unfold mhlift in H at 1. unfold mhlift at 1. simpl.
      destruct (@halt sig n
                (@projT1 (mTM sig n) (fun M : mTM sig n => @states sig n M -> F) pM)
                (@cstate sig (@states sig n (@projT1 (mTM sig n) (fun M : mTM sig n => @states sig n M -> F) pM)) n ic)) eqn:E.
      + congruence.
      + erewrite mirror_step'; eauto. 
    }
  Qed.

  Lemma mirror_loop' i ic oc :
    loop i (step (M := projT1     pM)) mhlift (mlift ic) = Some (mlift oc) ->
    loop i (step (M := projT1 Mirror)) mhlift (      ic) = Some (      oc).
  Proof.
    unfold loopM. revert ic. induction i; intros ic H.
    {
      unfold mhlift, mlift in *. cbn in *. destruct (halt (cstate ic)); try congruence.
      inv H. apply mirror_tapes_injective in H2. destruct ic, oc; cbn in *; congruence.
    }
    {
      cbn [loop] in *. unfold mhlift in H at 1. unfold mhlift at 1. unfold mlift at 1 in H. simpl in H.
      destruct (@halt sig n
                (@projT1 (mTM sig n) (fun M : mTM sig n => @states sig n M -> F) pM)
                (@cstate sig (@states sig n (@projT1 (mTM sig n) (fun M : mTM sig n => @states sig n M -> F) pM)) n ic)) eqn:E.
      + inv H. simpl in H1. apply mirror_tapes_injective in H2. destruct ic, oc; cbn in *; congruence.
      + erewrite mirror_step' in H; eauto.
    }
  Qed.
  
  Lemma mirror_loopM k tin outc :
    loopM k (initc (projT1 pM)     (mirror_tapes tin)) = Some outc ->
    loopM k (initc (projT1 Mirror) tin               ) = Some (mlift outc).
  Proof.
    intros H. rewrite <- (mirror_tapes_involution tin).
    replace (initc (projT1 Mirror) (mirror_tapes (mirror_tapes tin))) with (mlift (initc (projT1 Mirror) (mirror_tapes tin))).
    - eapply mirror_loop'. now rewrite !mlift_involution.
    - unfold mlift. cbn. rewrite !mirror_tapes_involution in *. cbn. reflexivity.
  Qed.
    
  
  Lemma Mirror_WRealise (R : Rel _ (F * _)) :
    pM ⊫ R -> Mirror ⊫ Mirror_R R.
  Proof.
    intros H. intros t i outc H2. specialize (H (mirror_tapes t) i (mlift outc)).
    assert (loopM i (initc (projT1 pM) (mirror_tapes t)) = Some (mlift outc)) as L.
    {
      eapply (loop_lift (lift := fun x => x) (hlift := mhlift) (g := step (M := projT1 Mirror))) in H2; intros; auto.
      {
        unfold loopM. cbn.
        replace (initc (projT1 pM) (mirror_tapes t)) with (mlift (initc (projT1 pM) t)) by reflexivity.
        now eapply mirror_loop.
      }
    } specialize (H L). clear L. destruct outc as (q&t'). cbn in *. auto.
  Qed.
  
  Lemma Mirror_Terminates (T : Rel _ nat) :
    projT1 pM ↓ T -> projT1 Mirror ↓ (fun t n => T (mirror_tapes t) n).
  Proof.
    intros H. hnf. intros t1 k H1. hnf in H. specialize (H (mirror_tapes t1) k H1) as (outc&H).
    exists (mlift outc).
    rewrite <- (mirror_tapes_involution t1).
    replace (initc (projT1 Mirror) (mirror_tapes (mirror_tapes t1))) with (mlift (initc (projT1 Mirror) (mirror_tapes t1))).
    eapply mirror_loopM; cbn. unfold mlift. cbn. rewrite !mirror_tapes_involution in *. auto. cbn. reflexivity.
  Qed.
  
    
  Lemma Mirror_RealiseIn (R : Rel _ (F * _)) (k : nat) :
    pM ⊨c(k) R -> Mirror ⊨c(k) Mirror_R R.
  Proof.
    intros H.
    eapply Realise_total. split.
    - eapply Mirror_WRealise. now eapply Realise_total.
    - eapply TerminatesIn_monotone.
      + eapply Mirror_Terminates. now eapply Realise_total.
      + firstorder.
  Qed.

End MirrorTM.

Hint Rewrite mirror_tape_left : tape.
Hint Rewrite mirror_tape_right : tape.
Hint Rewrite mirror_tape_current : tape.
Hint Rewrite mirror_tape_involution : tape.
Hint Rewrite mirror_tapes_involution : tape.