(* FIXME: TM.Basic.Nop is deprecated *)
Require Export TM.TM TM.Basic.Nop.
Require Import Shared.FiniteTypes.DepPairs EqdepFacts.

Require Import Wellfounded.

Section While.

  Variable n : nat.
  Variable sig : finType.

  Variable F : finType.
  Variable pM : { M : mTM sig n & states M -> bool * F }.

  Definition while_trans :
    (TM.states (projT1 pM)) * Vector.t (option sig) n ->
    (TM.states (projT1 pM)) * Vector.t (option sig * move) n :=
    fun st => let (s,a) := st in
           if fst (projT2 pM s) && halt s then (start (projT1 pM),null_action) else trans st.

  Definition While : mTM sig n :=
    Build_mTM while_trans (start (projT1 pM))
              (fun s => halt s && negb (fst (projT2 pM s))).

  Definition WHILE := (While; fun s => snd (projT2 pM s)).

  Local Arguments loopM {_ _} _ _ _.
  Local Arguments halt {_ _} _ _.
  Local Arguments step {_ _} _ _.


  Definition unlift_1 : mconfig sig (states While) n -> option (mconfig sig (states (projT1 pM)) n).
  Proof.
    intros s. exact (if (halt (projT1 pM) (cstate s)) then Some s else None).
  Defined.
 
  Lemma While_split i res c:
    loopM While i c = Some res ->
    exists i1 x1 i2,
      loopM (projT1 pM) i1 c = Some x1 /\
      loopM While i2 x1 = Some res /\ i = i1 + i2.
  Proof.
    intros.
    unfold loopM in H.
    eapply loop_split with (p := fun c=> halt (projT1 pM) (cstate c)) in H.
    destruct H as (i1 & x1 & i2 & H1 & H2 & ->).
    - exists i1,x1,i2. split;[ |split;[exact H2|reflexivity]].
      eapply loop_lift with (lift:=id) in H1.
      + exact H1.
      + reflexivity.
      + unfold id.  intros. destruct x. unfold step. cbn in *. rewrite H. now rewrite andb_false_r.
    - intros b. unfold halt at 2. cbn. now intros ->. 
  Qed.

  Lemma While_true_split i (x : mconfig _ (states While) _) oenc (f : F) :
    halt (projT1 pM) (cstate x) = true  -> projT2 pM (cstate x) = (true, f) ->
    loopM While i x = Some oenc ->
    exists i', i = 1+i' /\ loopM While i' (initc While (ctapes x)) = Some oenc.
  Proof.
    intros hx px Eq.
    destruct i as [ |i'];cbn in Eq;cbn in Eq; change (states (projT1 pM)) with (states While) in Eq; rewrite hx,px in Eq;cbn in Eq; inv Eq.
    exists i'. split;[omega| ].
    destruct x. cbn in *. rewrite <- H0. unfold loopM. f_equal.
    unfold step. cbn -[tape_move_multi null_action]. 
    rewrite hx,px. cbn -[tape_move_multi null_action]. now rewrite tape_move_null_action.
  Qed.

  Lemma While_true_merge i1 i2 (t x1 : mconfig _ (states While) _) oenc (f : F) :
    loopM (projT1 pM) i1 t = Some x1 ->
    loopM While i2 (initc While (ctapes x1)) = Some oenc ->
    (projT2 pM) (cstate x1) = (true, f) ->
    loopM While (i1+(1+i2)) t = Some oenc.
  Proof.
    intros Eq1 Eq2 px1.
    eapply loop_merge with
    (p:= fun c => halt (projT1 pM) (cstate c)) (a2:=x1).
    {unfold While. cbn. intros. now destruct halt. }
    {change (states While) with (states (projT1 pM)) in *.
     eapply loop_lift with (g:= step While) in Eq1;[exact Eq1|reflexivity| ].
     intros. unfold step,While,while_trans. cbn. now rewrite H,andb_false_r.
    }
    cbn. assert (hx1:halt (projT1 pM) (cstate x1)=true) by (apply loop_fulfills_p in Eq1;now destruct halt).
    change (states While) with (states (projT1 pM)) in *.
    rewrite hx1;cbn.
    -rewrite <- Eq2. unfold loopM. cbn. f_equal. unfold step. cbn -[tape_move_multi null_action].
     rewrite hx1,px1;cbn -[tape_move_multi null_action]. now rewrite tape_move_null_action. 
  Qed.

   Lemma While_false_merge i1 (t : mconfig _ (states While) _) oenc (f : F) :
    loopM (projT1 pM) i1 t = Some oenc ->
    projT2 pM (cstate oenc) = (false, f) ->
    loopM While i1 t = Some oenc.
  Proof.
    intros Eq px1.
    eapply (loop_unlift (unlift := fun (x:mconfig sig (states While) n) => Some x))
      in Eq. destruct Eq as (?&H'&H1). inv H1.
    Focus 3. intros ? ? H. inv H. reflexivity.
    replace i1 with (i1+0) by omega.
    eapply (loop_merge (p:= fun c => halt (projT1 pM) (cstate c))). unfold halt at 2. cbn. 
    now intros ? ->. exact H'.
    apply loop_fulfills_p_0. unfold halt. cbn. rewrite px1.
    apply loop_fulfills_p in H'. now destruct halt.
    intros ? ? H ?. inv H. all: auto.
    cbn in H0. f_equal. unfold step at 2;cbn. rewrite H0. now rewrite andb_false_r.
  Qed.


  Lemma While_WRealise (R : Rel _ (bool * F * _)) :
    pM ⊫ R ->
    WHILE ⊫ ( (star (⋃_f R |_ (true, f))) ∘ (fun t '(f, t') => R t (false, f, t'))).
  Proof.
    intros HR t1 i1 oenc2 eq. unfold initc in eq.
    revert t1 eq; apply complete_induction with (x := i1); clear i1; intros i1 IH t1 eq.
    eapply While_split in eq as (i2&x0&i3&Eq1&Eq2&->).
    assert (halt (projT1 pM) (cstate x0) = true) as hx0.
    {
      eapply loop_fulfills_p in Eq1. destruct halt; auto.
    }
    assert (halt While (cstate oenc2) = true) as Hoenc2.
    {
      eapply loop_fulfills_p in Eq2. destruct halt; auto.
    }
    apply andb_true_iff in Hoenc2 as (Hoenc2&Hoenc2'). apply negb_true_iff in Hoenc2'.
    destruct (projT2 pM (cstate oenc2)) as [b f] eqn:Eoenc2.
    destruct b; cbn in Hoenc2'; auto; clear Hoenc2'.
    destruct (projT2 pM (cstate x0)) as [bx0 fx0] eqn:px0.
    destruct bx0.
    - eapply While_true_split in Eq2 as (i' & -> & Eq2); eauto.
      apply IH in Eq2; [ | omega]. hnf in Eq2.
      destruct Eq2 as (y&Eq2&Eq2'). hnf in Eq2, Eq2'.
      eapply use_subrel.
      rewrite <- star_rcomp_idem. rewrite rcomp_assoc. reflexivity.
      hnf. exists (ctapes x0). split.
      + apply R_in_star. apply HR in Eq1. cbn in Eq1. rewrite px0 in Eq1. hnf. eauto.
      + repeat (econstructor; hnf; eauto).
    - hnf. exists t1. split; [now apply starR | ]. hnf.
      unfold  loopM in Eq2. rewrite loop_fulfills_p_0 in Eq2; [ | cbn; now rewrite px0, hx0]. inv Eq2.
      apply HR in Eq1. cbn in Eq1. cbn. rewrite px0. cbn. auto. rewrite px0 in Eq1. auto.
  Qed.

  Section While_terminatesIn.
    Variable (R : Rel (tapes sig n) (bool * F * tapes sig n)).
    Variable (T : Rel (tapes sig n) nat).

    Inductive WhileT : Rel (tapes sig n) nat :=
    | WhileT_Stop t1 k1 t2 y k2 :
        R t1 (false, y, t2) -> T t1 k1 -> k1 <= k2 -> WhileT t1 k2
    | WhileT_Loop t1 k1 y t2 k2 k3 :
        R t1 (true, y, t2) -> T t1 k1 ->
        WhileT t2 k2 ->
        k1 + k2 < k3 ->
        WhileT t1 k3.

    Lemma WhileT_functionalOn :
      functionalOn T R ->
      functionalOn WhileT R.
    Proof.
      intros H. hnf in *. intros x k H1. induction H1; intros; eauto.
    Qed.

    Lemma While_terminatesIn :
      pM ⊫ R ->
      projT1 pM ↓(T) ->
      functionalOn T R ->
      While ↓ WhileT.
    Proof.
      intros HR Term_M Func.
      intros t i. revert t. apply complete_induction with (x:=i); clear i; intros i IH t T't.
      destruct T't as [ t1 k1 t2 y k2 R1 T1 Hk | l1 k1 y t2 k2 k3 R1 T1 HW Hk ].
      - hnf in Term_M. specialize (Term_M _ _ T1) as (oenc&Eq).
        specialize (HR _ _ _ Eq).
        specialize (Func _ _ T1 _ _ HR R1). inv Func.
        exists oenc. eapply While_false_merge; cbn; eauto.
        unfold loopM. eapply loop_ge; eauto.
      - specialize (Term_M _ _ T1) as (oenc&Eq).
        specialize (IH k2 ltac:(omega) _ HW) as (oenc2&Eq2).
        specialize (HR _ _ _ Eq).
        specialize (Func _ _ T1 _ _ HR R1). inv Func.
        exists oenc2. unfold loopM. apply (loop_ge (k1:= k1 + (1 + k2)));[omega| ].
        eapply While_true_merge; eauto.
    Qed.

  End While_terminatesIn.


  (* Termination with size function *)
  Section While_size.
    Variable size : tapes sig n -> nat.
    Variable (R : Rel (tapes sig n) (bool * F * tapes sig n)).
    Variable (k : nat).

    Hypothesis size_decreases :
      forall tin term f tout,
        R tin (term, f, tout) -> size tout < size tin. (* after each loop the size decreases *)

    Inductive WhileTSize : Rel (tapes sig n) nat :=
    | WhileTSize_Stop tin fout tout k' :
        R tin (false, fout, tout) -> k <= k' -> WhileTSize tin k'
    | WhileTSize_Loop tin fout tout1 k' k'' :
        R tin (true, fout, tout1) -> WhileTSize tout1 k' -> k + k' < k'' -> WhileTSize tin k''.

    Lemma While_TerminatesIn_size :
      functional R ->
      pM ⊨c(k) R ->
      While ↓ WhileTSize.
    Proof.
      intros HFunc HRealise tin k' sizeT.
      induction sizeT as [tin fout tout' k' HR Hk' | tin fout tout1 k' k'' HR1 sizeT IH Hk''].
      {
        hnf in HRealise. specialize (HRealise tin) as (outc&HLoop1&HR1).
        cbn in *. hnf in HFunc. specialize (HFunc tin _ _ HR HR1).
        inv HFunc. cbn in *. symmetry in H0.
        pose proof While_false_merge HLoop1 H0 as Merge. exists outc. eapply loop_ge; swap 1 2; eauto.
      }
      {
        destruct IH as (outc2&HLoop2).
        hnf in HRealise. specialize (HRealise tin) as (outc1&HLoop1'&HR1').
        cbn in *. hnf in HFunc. specialize (HFunc tin _ _ HR1 HR1'). inv HFunc. cbn in *. symmetry in H0.
        pose proof While_true_merge HLoop1' HLoop2 H0. cbn in *. exists outc2. eapply loop_ge; swap 1 2; eauto. omega.
      }
    Qed.

    (*
    Lemma While_TerminatesIn_size' :
      functional R ->
      pM ⊨c(k) R ->
      While ↓ (fun tin k' => k' >= (S k) * size tin).
    Proof.
      intros HFunc HRealise. eapply TerminatesIn_monotone'. now eapply While_TerminatesIn_size.
      refine (@size_induction _ size _ _); intros tin IH k' Hk'.

      hnf in HRealise. pose proof (HRealise tin) as (outc&HLoop&HR).
      destruct outc as [qout tout]; cbn in *.
      destruct (projT2 pM qout) as [term yout] eqn:E.
      destruct term; swap 1 2.
      {
        pose proof (size_decreases HR) as sd.
        exists k. split; swap 1 2.
        - econstructor 1. eauto. omega.
        - enough (k <= k * size tin) by omega. enough (k * 1 <= k * size tin) by omega. eapply Nat.mul_le_mono; omega.
      }
      {
        pose proof (size_decreases HR) as sd.
        specialize (IH _ sd (size tout + k * size tout)) as (k2&Hk2&whileTSize).
        {
          enough (k * size tout <= k * size tin) by omega.
          eapply Nat.mul_le_mono; omega.
        }
        {
          exists (size tin + k * size tin). split; swap 1 2.
          - econstructor 2. eapply HR. eapply whileTSize. admit.
          - omega.
        }
      }
      
      


      
      destruct k as [ | k' ]; cbn.
      - hnf in HRealise. admit.
      - 
*)
    End While_size.
      


End While.
(* Arguments While {n} {sig} M _. *)