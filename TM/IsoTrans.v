Require Import TM.Prelim TM.TM.
Require Import Shared.Extra.Bijection.

Section Bisim.
  Variable (n : nat) (sig : finType).
  Variable F : finType.
  Variable pM : { M : mTM sig n & states M -> F }.
  Variable pM' : { M : mTM sig n & states M -> F }.

  Variable f : states (projT1 pM) -> states (projT1 pM').
  Variable g : states (projT1 pM') -> states (projT1 pM).

  Hypothesis start_f_comp : f (start (projT1 pM)) = start (projT1 pM').
  Hypothesis start_g_comp : g (start (projT1 pM')) = start (projT1 pM).

  Hypothesis halt_f_comp : forall s, halt (f s) = halt s.
  Hypothesis halt_g_comp : forall s, halt (g s) = halt s.

  Hypothesis step_g_comp :
    forall (x : mconfig sig (states (projT1 pM')) n),
      halt (cstate x) = false ->
      mk_mconfig (g (cstate (step x))) (ctapes (step x)) =
      step (mk_mconfig (g (cstate x)) (ctapes x)).

  Hypothesis step_f_comp :
    forall (x : mconfig sig (states (projT1 pM)) n),
      halt (cstate x) = false ->
      mk_mconfig (f (cstate (step x))) (ctapes (step x)) =
      step (mk_mconfig (f (cstate x)) (ctapes x)).

  Hypothesis param_f_comp : forall s, projT2 pM s = projT2 pM' (f s).
  Hypothesis param_g_comp : forall s, projT2 pM' s = projT2 pM (g s).


  Definition lift : mconfig sig (states (projT1 pM')) n -> mconfig sig (states (projT1 pM)) n :=
    fun c => mk_mconfig (g (cstate c)) (ctapes c).

  Definition hlift : mconfig sig (states (projT1 pM)) n -> bool :=
    fun c : mconfig sig (states (projT1 pM)) n => halt (cstate c).

  Definition lift' : mconfig sig (states (projT1 pM)) n -> mconfig sig (states (projT1 pM')) n :=
    fun c => mk_mconfig (f (cstate c)) (ctapes c).

  Definition hlift' : mconfig sig (states (projT1 pM')) n -> bool :=
    fun c : mconfig sig (states (projT1 pM')) n => halt (cstate c).
    
  Lemma IsoTrans_WRealise (R : Rel _ (F * _)) :
    pM ⊫ R -> pM' ⊫ R.
  Proof.
    intros H. intros t i outc H2. specialize (H t i (lift outc)).
    assert (loopM i (initc (projT1 pM) t) = Some (lift outc)) as L.
    {
      eapply (loop_lift (lift := lift) (hlift := hlift) (g := step (M := projT1 pM))) in H2.
      unfold loopM in *. unfold lift, hlift in *. cbn in *. unfold initc in *.
      now rewrite start_g_comp in H2.
      all: firstorder.
    } specialize (H L). clear L.
    destruct outc as (q&t'). cbn in *.
    now replace (projT2 pM (g q)) with (projT2 pM' q) in H.
  Qed.

  Lemma IsoTrans_Terminates (T : Rel _ nat) :
    projT1 pM ⇓ T -> projT1 pM' ⇓ T.
  Proof.
    intros H. hnf. intros t1 k H1. hnf in H. specialize (H t1 k H1) as (outc&H).
    exists (lift' outc).
    eapply (loop_lift (lift := lift') (hlift := hlift') (g := step (M := projT1 pM'))) in H.
    unfold loopM in *. unfold lift', hlift' in *. cbn in *. unfold initc in *.
    rewrite start_f_comp in H. all: firstorder.
  Qed.
 
  Lemma IsoTrans_Realise (R : Rel _ (F * _)) :
    pM ⊨ R -> pM' ⊨ R.
  Proof.
    intros H. intros t.  specialize (H t) as (outc&i&H1&H2).
    exists (lift' outc), i.
    eapply (loop_lift (lift := lift') (hlift := hlift') (g := step (M := projT1 pM'))) in H1.
    unfold loopM in *. unfold lift', hlift' in *. cbn in *. unfold initc in *.
    rewrite start_f_comp in H1. all: firstorder. now rewrite <- param_f_comp.
  Qed.

End Bisim.


Section MirrorTM.

  Variable (n : nat) (sig : finType).

  Definition mirror_tape (t : tape sig) : tape sig :=
    match t with
    | niltape _ => niltape _
    | leftof r rs => rightof r rs
    | rightof l ls => leftof l ls
    | midtape ls m rs => midtape rs m ls
    end.

  Lemma mirror_tape_involution (t : tape sig) :
    mirror_tape (mirror_tape t) = t.
  Proof. destruct t; cbn; congruence. Qed.

  Definition mirror_tapes (t : tapes sig n) : tapes sig n := Vector.map mirror_tape t.

  Lemma mirror_tapes_involution (t : tapes sig n) :
    mirror_tapes (mirror_tapes t) = t.
  Proof.
    unfold mirror_tapes. apply Vector.eq_nth_iff. intros ? ? ->.
    erewrite !Vector.nth_map; eauto. apply mirror_tape_involution.
  Qed.

  Definition mirror_move (D : move) : move := match D with | N => N | L => R | R => L end.

  Lemma mirror_move_involution (D : move) : mirror_move (mirror_move D) = D. Proof. now destruct D. Qed.
  
  Variable F : finType.
  Variable pM : move -> { M : mTM sig n & states M -> F }.

  Notation "'pM1'" := (pM R).
  Notation "'pM2'" := (pM L).
            
  Variable f : states (projT1 pM1) -> states (projT1 pM2).
  Variable g : states (projT1 pM2) -> states (projT1 pM1).
  Hypothesis inv: inverse f g.
  Lemma inv1 : left_inverse f g. Proof. firstorder. Qed.
  Lemma inv2 : right_inverse f g. Proof. firstorder. Qed.

  Hypothesis start_f_comp : f (start (projT1 pM1)) = start (projT1 pM2).
  Hypothesis start_g_comp : g (start (projT1 pM2)) = start (projT1 pM1).

  Definition mlift_m : mconfig sig (states (projT1 pM2)) n -> mconfig sig (states (projT1 pM1)) n :=
    fun c => mk_mconfig (g (cstate c)) (mirror_tapes (ctapes c)).

  Definition mlift'_m : mconfig sig (states (projT1 pM1)) n -> mconfig sig (states (projT1 pM2)) n :=
    fun c => mk_mconfig (f (cstate c)) (mirror_tapes (ctapes c)).

  Definition mlift : mconfig sig (states (projT1 pM2)) n -> mconfig sig (states (projT1 pM1)) n :=
    fun c => mk_mconfig (g (cstate c)) (ctapes c).

  Definition mhlift : mconfig sig (states (projT1 pM1)) n -> bool :=
    fun c : mconfig sig (states (projT1 pM1)) n => halt (cstate c).

  Definition mlift' : mconfig sig (states (projT1 pM1)) n -> mconfig sig (states (projT1 pM2)) n :=
    fun c => mk_mconfig (f (cstate c)) (ctapes c).

  Definition mhlift' : mconfig sig (states (projT1 pM2)) n -> bool :=
    fun c : mconfig sig (states (projT1 pM2)) n => halt (cstate c).

  Hypothesis halt_f_comp : forall s, halt (f s) = halt s.
  Hypothesis halt_g_comp : forall s, halt (g s) = halt s.


  Definition liftstep1 : mconfig sig (states (projT1 pM1)) n -> mconfig sig (states (projT1 pM1)) n :=
    fun c => mlift_m (step (M := projT1 pM2) (mlift'_m c)).
  Definition liftstep2 : mconfig sig (states (projT1 pM2)) n -> mconfig sig (states (projT1 pM2)) n :=
    fun c => mlift'_m (step (M := projT1 pM1) (mlift_m c)).

  Hypothesis step_mirrored1 :
    forall c, halt (cstate c) = false ->
         step (M := projT1 pM1) c = mlift_m (step (M := projT1 pM2) (mlift'_m c)).

  Hypothesis step_mirrored2 :
    forall c, halt (cstate c) = false ->
         step (M := projT1 pM2) c = mlift'_m (step (M := projT1 pM1) (mlift_m c)).

  Hypothesis param_f_comp : forall s, projT2 pM1 s = projT2 pM2 (f s).
  Hypothesis param_g_comp : forall s, projT2 pM2 s = projT2 pM1 (g s).

  Lemma mlift_m_involution1 s : mlift_m (mlift'_m s) = s.
  Proof.
    destruct s. unfold mlift_m, mlift'_m. cbn. f_equal. now rewrite inv1.
    apply mirror_tapes_involution.
  Qed.

  Lemma mlift_m_involution2 s : mlift'_m (mlift_m s) = s.
  Proof.
    destruct s. unfold mlift_m, mlift'_m. cbn. f_equal. now rewrite inv2.
    apply mirror_tapes_involution.
  Qed.
  
  Definition Mirror_R (R : Rel (tapes sig n) (F * tapes sig n)) : Rel (tapes sig n) (F * tapes sig n) :=
    fun t '(f, t') => R (mirror_tapes t) (f, mirror_tapes t').

  
  Lemma Mirror_WRealise (R : Rel _ (F * _)) :
    pM1 ⊫ R -> pM2 ⊫ Mirror_R R.
  Proof.
    intros H. intros t i outc H2. specialize (H (mirror_tapes t) i (mlift_m outc)).
    assert (loopM i (initc (projT1 pM1) (mirror_tapes t)) = Some (mlift_m outc)) as L.
    {
      eapply (loop_lift (lift := mlift_m) (hlift := mhlift) (g := liftstep1)) in H2; intros.
      - unfold mhlift, mlift_m in *. cbn in *. rewrite start_g_comp in H2. rewrite <- H2. eapply loop_ext; firstorder.
      - unfold mhlift, mlift_m. cbn. apply halt_g_comp.
      - unfold liftstep1, mlift_m, mlift'_m. cbn. rewrite !mirror_tapes_involution.
        rewrite !inv2. rewrite step_mirrored2; auto. f_equal.
        + f_equal. f_equal. rewrite <- step_mirrored2; firstorder.
        + f_equal. f_equal. rewrite <- step_mirrored2; firstorder.
    } specialize (H L). clear L.
    destruct outc as (q&t'). cbn in *. now replace (projT2 pM1 (g q)) with (projT2 pM2 q) in H.
  Qed.
  
  Lemma Mirror_Terminates (T : Rel _ nat) :
    projT1 pM1 ⇓ T -> projT1 pM2 ⇓ (fun t n => T (mirror_tapes t) n).
  Proof.
    intros H. hnf. intros t1 k H1. hnf in H. specialize (H (mirror_tapes t1) k H1) as (outc&H).
    exists (mlift'_m outc). unfold loopM in H.
    eapply (loop_lift (lift := mlift'_m) (hlift := mhlift') (g := liftstep2)) in H; intros.
    - unfold mhlift', mlift'_m in *. cbn in *. rewrite start_f_comp in H. rewrite <- H.
      rewrite mirror_tapes_involution. eapply loop_ext; firstorder.
    - unfold mhlift, mlift_m. cbn. apply halt_f_comp.
    - unfold liftstep2, mlift'_m, mlift_m. cbn. rewrite !mirror_tapes_involution.
      rewrite !inv1. rewrite step_mirrored1; auto. f_equal.
      + f_equal. f_equal. rewrite <- step_mirrored1; firstorder.
      + f_equal. f_equal. rewrite <- step_mirrored1; firstorder.
  Qed.
  
  Lemma Mirror_Realise (R : Rel _ (F * _)) :
    pM1 ⊨ R -> pM2 ⊨ Mirror_R R.
  Proof.
    intros H. hnf. intros t1. hnf in H. specialize (H (mirror_tapes t1)) as (outc&k&H&H1).
    exists (mlift'_m outc), k. unfold loopM in H. split.
    - eapply (loop_lift (lift := mlift'_m) (hlift := mhlift') (g := liftstep2)) in H; intros.
      + unfold mhlift', mlift'_m in *. cbn in *. rewrite start_f_comp in H. rewrite <- H.
        rewrite mirror_tapes_involution. eapply loop_ext; firstorder.
      + unfold mhlift, mlift_m. cbn. apply halt_f_comp.
      + unfold liftstep2, mlift'_m, mlift_m. cbn. rewrite !mirror_tapes_involution.
        rewrite !inv1. rewrite step_mirrored1; auto. f_equal.
        * f_equal. f_equal. rewrite <- step_mirrored1; firstorder.
        * f_equal. f_equal. rewrite <- step_mirrored1; firstorder.
    - cbn. rewrite mirror_tapes_involution. now rewrite <- param_f_comp.
  Qed.

  Lemma Mirror_RealiseIn (R : Rel _ (F * _)) (k : nat) :
    pM1 ⊨c(k) R -> pM2 ⊨c(k) Mirror_R R.
  Proof.
    intros H. hnf. intros t1. hnf in H. specialize (H (mirror_tapes t1)) as (outc&H&H1).
    exists (mlift'_m outc). unfold loopM in H. split.
    - eapply (loop_lift (lift := mlift'_m) (hlift := mhlift') (g := liftstep2)) in H; intros.
      + unfold mhlift', mlift'_m in *. cbn in *. rewrite start_f_comp in H. rewrite <- H.
        rewrite mirror_tapes_involution. eapply loop_ext; firstorder.
      + unfold mhlift, mlift_m. cbn. apply halt_f_comp.
      + unfold liftstep2, mlift'_m, mlift_m. cbn. rewrite !mirror_tapes_involution.
        rewrite !inv1. rewrite step_mirrored1; auto. f_equal.
        * f_equal. f_equal. rewrite <- step_mirrored1; firstorder.
        * f_equal. f_equal. rewrite <- step_mirrored1; firstorder.
    - cbn. rewrite mirror_tapes_involution. now rewrite <- param_f_comp.
  Qed.

End MirrorTM.