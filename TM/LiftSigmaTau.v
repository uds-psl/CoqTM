Require Import Prelim TM.Relations TM Shared.Tactics.AutoIndTac Injection.

Section MapTape.
  Variable sig tau : finType.
  Variable g : tau -> sig.

  Definition mapTape : tape tau -> tape sig.
  Proof.
    destruct 1 eqn:E1.
    - apply niltape.
    - apply leftof.  apply (g e). apply (List.map g l).
    - apply rightof. apply (g e). apply (List.map g l).
    - apply midtape. apply (List.map g l). apply (g e). apply (List.map g l0).
  Defined.

  Definition mapTapes {n : nat} : Vector.t (tape tau) n -> Vector.t (tape sig) n := Vector.map mapTape.
End MapTape.

Section SujectTape.
  Variable sig tau : finType.
  Variable g : tau -> option sig.
  Variable def : sig.

  Definition surject : tau -> sig := fun t => match (g t) with Some s => s | None => def end.

  Definition surjectTape := mapTape surject.
  Definition surjectTapes {n : nat} := mapTapes (n := n) surject.

End SujectTape.


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
    fun x p => let (z,y) := p in R (surjectTapes g def x) (z, surjectTapes g def y).    

End lift_sigma_tau.
      

Section InjectTape.

  Variable sig tau : finType.
  Variable f : sig -> tau.

  Definition injectTape := mapTape f.
  Definition injectTapes {n: nat} := mapTapes (n := n) f.
End InjectTape.
    

Section InjectSurject.
  Variable sig tau : finType.
  Variable I : injection_fun sig tau.
  Variable def : sig.

  Lemma surject_inject' (l : list sig) :
    map (fun t : tau => match inj_g I t with
                     | Some s => s
                     | None => def
                     end) (map (inj_f I) l) = l.
  Proof.
    induction l; cbn.
    - reflexivity.
    - rewrite inj_g_adjoint. f_equal. assumption.
  Qed.
  
  Lemma surject_inject_tape (t : tape sig) :
    surjectTape (inj_g I) def (injectTape (inj_f I) t) = t.
  Proof.
    unfold surjectTape, injectTape, surject.
    destruct t; cbn; f_equal; try rewrite inj_g_adjoint; auto; apply surject_inject'.
  Qed.

  Lemma surject_inject_tapes {n : nat} (t : Vector.t (tape sig) n) :
    surjectTapes (inj_g I) def (injectTapes (inj_f I) t) = t.
  Proof.
    unfold surjectTapes, injectTapes, mapTapes.
    apply Vector.eq_nth_iff. intros p ? <-. 
    erewrite !Vector.nth_map; eauto.
    apply surject_inject_tape.
  Qed.
  
End InjectSurject.


Section LiftSigmaTau.
  Variable sig tau : finType.
  Variable n : nat.
  Variable F : finType.
  Variable pMSig : { M : mTM sig n & states M -> F}.

  Variable I : injection_fun sig tau.
  Variable def : sig.
  Definition f := inj_f I.
  Definition g : tau -> sig := fun t : tau => match (inj_g I t) with Some s => s | None => def end.

  Definition lift_trans :=
    fun '(q, symm) =>
      let (q', act) := trans (m := projT1 pMSig) (q, Vector.map (fun a => let try a' := a in Some (g a')) symm) in
      let act' := Vector.map (fun '(w, m) => (let try w' := w in Some (f w'), m)) act in
      (q', act').

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
      tape_move_mono (mapTape (surject (inj_g I) def) tape) act =
      mapTape (surject (inj_g I) def)
              (tape_move_mono tape
                              (let '(w, m) := act in (let try w' := w in Some (f w'), m))).
  Proof.
    intros tape. intros (w,m).
    unfold tape_move_mono, tape_move, tape_write, surject. cbn.
    destruct tape; cbn;
      try (destruct m, w; cbn; f_equal; now rewrite inj_g_adjoint).
    destruct m, w; cbn.
    - unfold mapTape. cbn. destruct l; cbn; f_equal; now rewrite inj_g_adjoint.
    - unfold mapTape. cbn. destruct l; cbn; f_equal; now rewrite inj_g_adjoint.
    - unfold mapTape. cbn. destruct l, l0; cbn; f_equal; now rewrite inj_g_adjoint.
    - unfold mapTape. cbn. destruct l, l0; cbn; f_equal; now rewrite inj_g_adjoint.
    - unfold mapTape. cbn. destruct l, l0; cbn; f_equal; now rewrite inj_g_adjoint.
    - unfold mapTape. cbn. destruct l, l0; cbn; f_equal; now rewrite inj_g_adjoint.
  Qed.

  Lemma sim_step (c1 c2 : mconfig tau (states (projT1 pMSig)) n) :
    step (M := liftM) c1 = c2 ->
    step (M := projT1 pMSig) (mk_mconfig (cstate c1) (surjectTapes (inj_g I) def (ctapes c1))) =
    (mk_mconfig (cstate c2) (surjectTapes (inj_g I) def (ctapes c2))).
  Proof.
    intros H. cbn.
    destruct c1 as [state1 tapes1] eqn:E1, c2 as [state2 tapes2] eqn:E2.
    unfold step in *. cbn in *.
    replace (fun a : option tau =>
                match a with
                | Some a0 => Some (g a0)
                | None => None
                end) with (fun a : option tau => let try a' := a in Some (g a')) in H by reflexivity.

    destruct (trans
                (state1, Vector.map (fun a : option tau => let try a' := a in Some (g a'))
                                    (Vector.map (current (sig:=tau)) tapes1))) as (q, act) eqn:E3.
    inv H.
    destruct (trans (state1, Vector.map (current (sig:=sig)) (surjectTapes (inj_g I) def tapes1)))
      as (q', act') eqn:E4.
    enough ((state2, act) = (q', act')) as X.
    {
      inv X. f_equal.
      unfold surjectTapes, mapTapes. apply Vector.eq_nth_iff. intros p ? <-.
      erewrite !Vector.nth_map, !Vector.nth_map2, !Vector.nth_map; eauto.
      (* again, stick to notations *)
      change (tape_move_mono (mapTape (surject (inj_g I) def) tapes1[@p]) act'[@p] =
              mapTape (surject (inj_g I) def)
                      (tape_move_mono tapes1[@p]
                                      (let '(w, m) := act'[@p] in (let try w' := w in Some (f w'), m)))).
      (* generalize (act'[@p]) as act. generalize (tapes1[@p]) as tape. *)
      apply surject_step.
    }
    rewrite <- E3, <- E4. do 2 f_equal.
    apply Vector.eq_nth_iff. intros p ? <-.
    unfold surjectTapes, mapTapes, surject, current. 
    erewrite !Vector.nth_map; eauto. cbn.
    destruct (tapes1[@p]) eqn:E5; cbn; auto.
  Qed.

  Lemma sim_loop (c1 c2 : mconfig tau (states liftM) n) (i : nat) :
    loopM (M := liftM) i c1 = Some c2 ->
    loopM (M := projT1 pMSig) i (mk_mconfig (cstate c1) (surjectTapes (inj_g I) def (ctapes c1))) =
    Some (mk_mconfig (cstate c2) (surjectTapes (inj_g I) def (ctapes c2))).
  Proof.
    unfold loopM in *. revert c2 c1. induction i; intros c2 c1 H; cbn in *.
    - destruct (halt _) eqn:E; now inv H.
    - destruct (halt _) eqn:E; inv H; auto.
      rewrite sim_step with (c1 := c1) (c2 := step (M := liftM) c1); [ | reflexivity]. apply IHi. apply H1.
  Qed.


  Lemma Lift_sem (R : Rel (tapes sig n) (F * tapes sig n)) :
    pMSig ⊫ R ->
    Lift ⊫ lift_sigma_tau_p (inj_g I) def R.
  Proof.
    intros H. intros t i outc Hloop. unfold lift_sigma_tau_p.
    apply (H (surjectTapes (inj_g I) def t) i (mk_mconfig (cstate outc) (surjectTapes (inj_g I) def (ctapes outc)))).
    now apply (@sim_loop (initc liftM t) outc i).
  Qed.
    

End LiftSigmaTau.
