Require Export TM Nop.
Require Import Shared.FiniteTypes.DepPairs EqdepFacts.

(* TODO: This is a mess. *)

Section Match.

  Variable n : nat.
  Variable sig : finType.

  Variable F : finType.

  Variable pM1 : { M1 : mTM sig n & states M1 -> F}.
  Variable F' : finType.
  Variable pMf : F -> { Mf : mTM sig n & states Mf -> F'}.

  Notation "'Mf' f" := (projT1 (pMf f)) (only parsing, at level 10).
  Notation "'p2' f" := (projT2 (pMf f)) (only parsing, at level 10).


  Notation "'M1'" := (projT1 pM1) (only parsing).
  Notation "'p1'":= (projT2 pM1) (only parsing).

  Definition match_trans :
    (TM.states M1 + { f : F & TM.states (Mf f) }) * Vector.t (option sig) n ->
    (TM.states M1 + { f : F & TM.states (Mf f) }) * Vector.t (option sig * move) n :=
    fun st => let (s,a) := st in
           match s with
           | inl s1 => if halt s1 then (inr (existT (fun f : F => states (Mf f)) (p1 s1) (start (Mf (p1 s1)))), null_action)
                      else let (news1,m) := trans (s1,a) in (inl news1, m)
           | inr s2 => let (f,s2) := s2 in let (news2, m) := trans (s2, a) in (inr (existT (fun f0 : F => states (Mf f0)) f news2), m)
           end.

  Definition Match : mTM sig n :=
    Build_mTM match_trans (inl (start M1))
              (fun s => match s with
                     | inl _ => false
                     | inr s0 => let (f, s0) := s0 in halt s0
                     end).

  Definition lift_confL (c : mconfig sig (states M1) n) : mconfig sig (states Match) n :=
    mk_mconfig (inl (cstate c)) (ctapes c).

  Definition lift_confR (f : F) (c : mconfig sig (states (Mf f) ) n) : mconfig sig (states Match) n :=
    mk_mconfig (inr (existT (fun f0 : F => states (Mf f0)) f (cstate c))) (ctapes c).
  (* Arguments lift_confR f c : clear implicits. *)

  Lemma step_seq_liftL c0 :
    halt (cstate c0) = false -> step (lift_confL c0) = lift_confL (step c0).
  Proof.
    destruct c0. unfold lift_confL, step. cbn. intros. destruct * eqn:_. now inv H1.
  Qed.

  Lemma step_seq_liftR f (c0 : mconfig sig (states (Mf f)) n) :
    step (lift_confR c0) = lift_confR (step c0).
  Proof.
    destruct c0. unfold lift_confR, step. cbn. destruct * eqn:_. now inv H0.
  Qed.

  Definition halt_liftL (c : mconfig sig (states (Match)) n) :=
    match cstate c with
    | inl s => halt (m := M1) s
    | inr s => let (f, s) := s in halt (m := Mf f) s
    end.

  Definition Match_p : (states Match) -> F'.
  Proof.
    intros s. 
    destruct s.
    - cbn in e. eapply (projT2 pM1) in e.
      eapply pMf in e.
      eapply (projT2 e).
      eapply start.
    - destruct s.
      destruct (pMf x).
      eapply e0. exact e.
      (* Show Proof. *)
      (* Show Proof. *)
      (* fun s => match s with *)
      (*     | inl _ => p2 (p (start M1)) (start (Mf (p (start M1)))) *)
      (*     | inr (existT _ f' s2) => p2 f' s2 *)
      (*     end. *)
  Defined.

  (* Definition lift_partR : (states Match) -> F' := *)
  (*   fun s => match s with *)
  (*         | inl e => (fun e0 : F => (fun (e1 : { Mff : mTM sig n & states Mff -> F'}) => projT2 e1 (start (projT1 e1))) (pMf e0))  *)
  (*      (p1 e) *)
  (*         | inr (existT _ f' s2) => p2 s2 *)
  (*         end. *)

  Lemma Match_merge x (x0 : mconfig sig (states M1) n) x1 x2 t:
    loopM x (initc M1 t) = Some x0 ->
    loopM x1 (initc (Mf (p1 (cstate x0))) (ctapes x0)) = Some x2 ->
    loopM (x + (1 + x1)) (initc Match t) = Some (lift_confR x2).
  Proof.
    intros H H1.
    unfold loopM.
    eapply (loop_merge (p := halt_liftL) (a2 := lift_confL x0)).
    - intros ? H3. cbn. unfold halt_liftL in H3. now destruct cstate.
    - unfold loopM in H. cbn.
      eapply loop_lift with (lift := lift_confL) (hlift := halt_liftL) in H; eauto.
      + firstorder. rewrite step_seq_liftL; eauto.
    - change (loop (1 + x1) (step (M:=Match)) (fun c : mconfig sig (states Match) n => halt (cstate c)) (lift_confL x0)) with (loop x1 (step (M:=Match)) (fun c : mconfig sig (states Match) n => halt (cstate c)) (step (lift_confL x0))).
      pose (M2 := (Mf (p1 (cstate x0)))).
      eapply loop_lift with (lift := @lift_confR (p1 (cstate x0))) (hlift := (fun x => halt (m := Match) (cstate x))) in H1;eauto.
      + cutrewrite  (step (lift_confL x0) = (lift_confR (initc M2 (ctapes x0)))); eauto.
        destruct x0. unfold lift_confL, lift_confR. unfold step.
        cbn -[null_action tape_move_multi]. cutrewrite (halt cstate = true). f_equal.
        eapply tape_move_null_action. eapply loop_fulfills_p in H.
        cbn in H; destruct (halt cstate); auto.
      + firstorder. now rewrite step_seq_liftR.
  Qed.

  Definition unlift_1 : mconfig sig (FinType (EqType (states M1 + { f : F & TM.states (Mf f) }))) n -> option (mconfig sig (states M1) n).
  Proof.
    intros m. destruct m. destruct cstate. left. econstructor. exact e. exact ctapes. right.
  Defined.

  Definition unlift_2 f : mconfig sig (FinType (EqType (states M1 + { f : F & TM.states (Mf f) }))) n -> option (mconfig sig (states (Mf f)) n).
  Proof.
    intros m. destruct m. destruct cstate.
    - right.
    - destruct s as [f' e].
      decide (f = f').
      + left. econstructor. symmetry in e0. rewrite <- e0. exact e. exact ctapes.
      + right.
  Defined.

  Lemma unlift_2_step f (a : mconfig sig (states Match) n)( a' : mconfig sig (states (Mf f)) n) :
    unlift_2 f a = Some a' -> halt (cstate a') = false -> unlift_2 f (step a) = Some (step a').
  Proof.
    destruct a. unfold unlift_2, step, trans. cbn. intros.
    destruct cstate eqn:E; inv H. cbn in *. destruct s. decide (f = x); subst; inv H2. cbn in *.
    destruct * eqn:E. rewrite <- Eqdep_dec.eq_rect_eq_dec;[ |apply eqType_dec].
    inv H. inv H1. inv H2.

    assert (((existT (fun f0 : F => states (Mf f0)) x0 e2), t1) =
            ((existT (fun f : F => states (Mf f)) x0 e0), t0)). congruence.
    assert (t1 = t0). congruence.
    assert (((existT (fun f0 : F => states (Mf f0)) x0 e2)) =
            ((existT (fun f : F => states (Mf f)) x0 e0))). congruence.
    eapply eq_sigT_iff_eq_dep in H2. eapply Eqdep_dec.eq_dep_eq_dec in H2; eauto.
    subst.
    revert H7 H5. clear. destruct (Mf x0).
    intros. unfold TM.trans in *. rewrite H7 in H5. congruence.
    intros. eapply eqType_dec.
  Qed.

  Lemma unlift_1_step (a : mconfig sig (states Match) n)
        ( a' : mconfig sig (states M1) n) : unlift_1 a = Some a' -> halt (cstate a') = false -> unlift_1 (step a) = Some (step a').
  Proof.
    destruct a. unfold unlift_1, step, trans. cbn. intros.
    destruct cstate eqn:E; inv H. cbn in *. rewrite H0. unfold trans.
    destruct M1. cbn in *. destruct trans. reflexivity.
  Qed.

  Lemma Match_split i res t:
    loopM i (initc Match t) = Some res ->
    (exists i1 x1 i2 x2,  loopM i1 (initc M1 t) = Some x1 /\
                     loopM i2 (initc (Mf (p1 (cstate x1))) (ctapes x1)) = Some x2 /\ i = 1 + i1 + i2 /\ res = (lift_confR x2)).
  Proof.
    intros.
    unfold loopM in H.
    eapply loop_split in H.
    destruct H as (i1 & x1 & i2 & H1 & H2 & Hi).
    eapply loop_unlift with (unlift := unlift_1)
                              (f' := step (M := M1))
                              (p' := fun c => halt (m := M1) (cstate c))

      in H1 as (x' & Hx' & Hu).
    exists i1, x'.
    - unfold loopM at 1. rewrite Hx'.
      destruct x1. unfold unlift_1 in Hu. cbn in Hu. destruct cstate; inv Hu.
      destruct i2; try now inv H2. cbn -[halt] in H2. unfold halt at 1 in H2. cbn -[halt] in H2.
      unfold step at 2 in H2. cbn -[halt] in H2.
      assert (halt e = true). eapply loop_fulfills_p in Hx'. cbn in Hx'. cbn in Hx'. destruct (halt e); auto. rewrite H in H2.
      remember (mk_mconfig (inr (existT (fun f : F => states (Mf f)) (p1 e) (start (Mf (p1 e)))))
                           (Vector.map2 (tape_move_mono (sig:=sig)) ctapes
                                        (repeatVector n (None, N)))) as x2.
      pose (M2 := (Mf (p1 e))).
      eapply loop_unlift with (unlift := unlift_2 (p1 e))
                                (f' := step (M := M2))
                                (p' := fun c => halt (m := M2) (cstate c))
                                (p := fun c => halt (m := Match) (cstate c))
        in H2 as (x'' & Hx'' & Hu').
      + exists i2. exists x''. intuition. eapply Hx''. omega. destruct x''. unfold lift_confR. cbn. destruct res. unfold unlift_2 in *. cbn in Hu'. destruct cstate0; inv Hu'. destruct s.  decide (p1 e = x); inv H1. reflexivity.
      + intuition. exists (step (M := M2) a'). intuition. now eapply unlift_2_step.
      + intuition. cbn. unfold halt. destruct a. unfold unlift_2 in H0.
        destruct cstate. inv H0. inv H0. cbn. destruct s.  decide (p1 e = x); inv H3. reflexivity.
      + subst. cbn. assert (T := tape_move_null_action ctapes). cbn in T. unfold tape_move_multi in T.
        rewrite T. decide (p1 e = p1 e); try tauto.
        unfold initc. f_equal. f_equal.
        (* assert (p e = eqType_X ( type (@states sig n (Mf (p e))))). *)
        rewrite <- Eqdep_dec.eq_rect_eq_dec;[ |apply eqType_dec].
        reflexivity.
    - intuition. exists (step (M := M1) a'). intuition. now eapply unlift_1_step.
    - intros. instantiate (1 := fun x => match cstate x with inl s => halt (m := M1) s | _ => true end).
      cbn. unfold unlift_1 in H. destruct a. destruct cstate. inv H. reflexivity. inv H.
    - cbn. reflexivity.
    - intros. cbn in *. destruct cstate. reflexivity. inv H0.
  Qed.

  (* Definition Match_p : (states (Match pM1 (fun f => projT1 (Mf f)))) -> F'. *)
  (* Proof. *)
  (*   intros s. *)
  (*   destruct s. *)
  (*   - destruct pM1. cbn in e. eapply e0 in e. eapply Mf in e. destruct e. *)
  (*     eapply e. *)
  (*     exact (start x0). *)
  (*   - destruct s. *)
  (*     destruct (Mf x). *)
  (*     eapply e0. exact e. *)
  (*     (* Show Proof. *) *)
  (*     (* fun s => match s with *) *)
  (*     (*     | inl _ => p2 (p (start M1)) (start (Mf (p (start M1)))) *) *)
  (*     (*     | inr (existT _ f' s2) => p2 f' s2 *) *)
  (*     (*     end. *) *)
  (* Defined. *)

  Definition MATCH := (Match; Match_p).

  Lemma Match_sem (R1 : Rel _ (F * _)) (R2 : F -> Rel _ (F' * _)) :
    pM1 ⊫ R1 ->
    (forall f : F, pMf f ⊫ R2 f) -> MATCH ⊫ (⋃_f (R1 |_ f) ∘ R2 f).
  Proof.
    intros HR1 HR2 t1 i1 oenc2 eq.
    apply Match_split in eq as (?&?&?&?&Eq1&Eq2&->&->).
    unfold WRealise in HR1.
    eapply HR1 in Eq1.
    eapply HR2 in Eq2.
    eapply finite_rel_union_spec.
    eexists _, _. split. eapply Eq1.
    eapply Eq2.
  Qed.

  Lemma Match_terminatesIn (R1 : Rel _ (F * _)) T1 T :
    functionalOn T1 R1 ->
    pM1 ⊫ R1 ->
    M1 ↓(T1) ->
    (forall f : F, Mf f ↓(T f)) ->
    projT1 MATCH ↓(⋃_f (fun (x : tapes sig n) (i : nat) => exists (j k : nat) (y : tapes sig n),
                     R1 x (f, y) /\ T1 x j /\ T f y k /\ j + k < i)).
  Proof.
    intros Func Real1 Term1 Term2 t i Hf.
    eapply finite_rel_union_spec in Hf as (f & j & k & y & ? & Term_t1 & Term_T & ?).
    edestruct (Term1 _ _ Term_t1) as [t'' ?].
    destruct (Term2 f _ _ Term_T) as [outc ?].
    exists (lift_confR outc).
    unfold loopM.
    eapply loop_ge with (k1:=j+(1+k)). omega.
    assert (HEq := Func _ _ Term_t1 _ _ H (Real1 _ _ _ H1)). inv HEq.
    eapply Match_merge.
    exact H1. rewrite <- H2. eapply Real1 in H1.
    repeat f_equal.
  Qed.

  Lemma Match_total
        (R1 : Rel _ (F * _)) (R2 : F -> Rel _ (F' * _)) k1 k2:
    projT1 pM1 ⊨(projT2 pM1, k1) R1 ->
    (forall f : F, Mf f ⊨(projT2 (pMf f), k2) R2 f) ->
    MATCH ⊨(1 + k1 + k2) (⋃_f (R1 |_ f) ∘ R2 f).
  Proof.
    intros HR1 HR2 t.
    edestruct (HR1 t) as (c' & ? & ?).
    edestruct (HR2 (projT2 pM1 (cstate c')) (ctapes c')) as (outc & ? & ?).
    exists (lift_confR outc). split.
    -  unfold loopM.
       eapply loop_ge with (k1:=k1+(1+k2)). omega.
       eapply Match_merge; eauto.
    - cbn.
      eapply finite_rel_union_spec.
      firstorder.      
  Qed.

End Match.
(* Arguments MATCH {n} {sig} {F} pM1 {_} pMf : clear implicits. *)
