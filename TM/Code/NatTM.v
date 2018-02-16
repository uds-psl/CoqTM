Require Import TM.Code.CodeTM TM.Code.MatchNat.
Require Import TM.Basic.Mono Basic.Nop Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.


Definition is_zero (n : nat) :=
  match n with
  | 0 => true
  | _ => false
  end.

Definition is_not_zero (n : nat) :=
  match n with
  | 0 => false
  | _ => true
  end.

Lemma is_zero_correct (n : nat) :
  is_not_zero n = true <-> n <> 0.
Proof. destruct n; cbn; split; congruence. Qed.


Lemma MatchNat_Computes_Pred :
  MatchNat ⊨c(5) Computes_Rel_p (Fin.F1) (Fin.F1) _ _ pred is_not_zero.
Proof.
  eapply RealiseIn_monotone. eapply MatchNat_Sem. omega.
  intros tin (yout,tout) H. hnf. intros n HEncN.
  destruct n; cbn in *.
  - destruct yout.
    + specialize (H _ HEncN) as (n'&?&?); auto.
    + specialize (H _ HEncN) as (n'&?); auto.
  - destruct yout.
    + specialize (H _ HEncN) as (n'&?&?). inv H. auto.
    + specialize (H _ HEncN) as (n'&?); auto.
Qed.



(* Tail recursive funktions over [nat] *)
Section FoldNat.

  Variable Y : finType.
  Variable f : nat -> nat.

  Fixpoint natTailRec (x y : nat) {struct x} : nat :=
    match x with
    | 0 => y
    | S x' => natTailRec x' (f y)
    end.

  Variable M1 : { M : mTM (bool^+) 1 & states M -> unit }.
  Hypothesis M1_computes : M1 ⊫ Computes_Rel Fin.F1 Fin.F1 _ _ f.

  Definition natTailRec_step (x y : nat) : nat :=
    match x with
    | 0 => y
    | S _ => f y
    end.


  Definition TailRec_step : { M : mTM _ 2 & states M -> bool * unit } :=
    If (Inject MatchNat [|Fin.F1|])
       (Inject M1 [|Fin.FS Fin.F1|];; Nop _ _ (true, tt))
       (Nop _ _ (false, tt)).
  

  Definition TailRec : { M : mTM _ 2 & states M -> unit } := WHILE TailRec_step.


  (** Correctness *)

  Definition tailRec_step_param : nat -> bool * unit := fun n => (is_not_zero n, tt).

  Lemma TailRec_step_Computes :
    TailRec_step ⊫ Computes_Rel_p (Fin.F1) (Fin.F1) _ _ pred tailRec_step_param ∩
                   Computes2_Rel (Fin.F1) (Fin.FS Fin.F1) (Fin.FS Fin.F1) _ _ _ natTailRec_step.
  Proof.
    eapply WRealise_monotone.
    {
      unfold TailRec_step. repeat TM_Correct.
      eapply  RealiseIn_WRealise. eapply MatchNat_Sem.
    }
    {
      intros tin (yout, tout). split.
      - intros n HEn. destruct H; hnf in H.
        + destruct H as (tmid&(H1&H2)&([]&t)&H3&->&->); hnf in H1, H2, H3. simpl_not_in.
          specialize (H1 n). spec_assert H1 as (n'&->&H1). { unfold reorder. now simpl_vector. } cbn in *. split; auto.
          destruct H3 as (H3&H4); hnf in H3, H4. simpl_not_in. rewrite <- H2, H4 in *; clear H2 H4. auto.
        + destruct H as (tmid&(H1&H2)&->&->); hnf in H1, H2. simpl_not_in. specialize (H1 n).
          spec_assert H1 as (->&H1). { unfold reorder. now simpl_vector. } cbn. auto.
      - intros n m HEn Hem. destruct H; hnf in H.
        + destruct H as (tmid&(H1&H2)&([]&t)&H3&->&->); hnf in H1, H2, H3. simpl_not_in.
          specialize (H1 n). spec_assert H1 as (n'&->&H1). { unfold reorder. now simpl_vector. } cbn in *. auto.
          destruct H3 as (H3&H4); hnf in H3, H4. simpl_not_in. rewrite <- H2, H4 in *; clear H2 H4. auto.
        + destruct H as (tmid&(H1&H2)&->&->); hnf in H1, H2. simpl_not_in. specialize (H1 n). spec_assert H1 as (->&H1).
          { unfold reorder. now simpl_vector. } cbn in *. rewrite H2 in *; clear H2. auto.
    }
  Qed.

  
  Lemma natTailRec_eta (x y : nat) :
    natTailRec (Init.Nat.pred x) (natTailRec_step x y) = natTailRec x y.
  Proof. destruct x, y; cbn; omega. Qed.


  Lemma TailRec_Computes :
    TailRec ⊫ Computes2_Rel (Fin.F1) (Fin.FS Fin.F1) (Fin.FS Fin.F1) _ _ _ natTailRec.
  Proof.
    eapply WRealise_monotone.
    {
      unfold TailRec. TM_Correct. eapply TailRec_step_Computes.
    }
    {
      hnf. intros tin ((), tout) H. destruct H as (tmid&H1&H2&H3).
      revert tout H2 H3. induction H1 as [ tin | tin tmid tout H1 H2 IH]; intros; hnf in *; intros.
      - specialize (H2 _ H) as (H2&H2'). specialize (H3 _ _ H H0). cbn in *.
        unfold tailRec_step_param in *. destruct x, y; cbn in *; inv H2'; auto.
      - cbn in *. destruct H1 as (()&H11&H12).
        hnf in H11, H12. specialize (H11 x H) as (H11&H11'). specialize (H12 x y H H4).
        specialize (IH _ H0 H3). specialize (IH _ _ H11 H12). rewrite natTailRec_eta in IH. auto.
    }
  Qed.


  (** Termination *)

  Variable M1_runtime : nat -> nat.
  Hypothesis M1_terminates : projT1 M1 ↓ (fun tin k => exists y, tin[@Fin.F1] ≂ y /\ M1_runtime y <= k).

  Lemma TailRec_step_terminates :
    projT1 TailRec_step ↓ (fun tin k => exists x y, tin[@Fin.F1] ≂ x /\ tin[@Fin.FS Fin.F1] ≂ y /\ 8 + M1_runtime y <= k).
  Proof.
    unfold TailRec_step.
    eapply TerminatesIn_monotone.
    {
      eapply If_TerminatesIn.
      - eapply Inject_WRealise. vector_dupfree. eapply RealiseIn_WRealise. eapply MatchNat_Computes_Pred.
      - eapply Inject_Terminates. vector_dupfree. eapply RealiseIn_terminatesIn. eapply MatchNat_Computes_Pred.
      - eapply Seq_TerminatesIn.
        + eapply Inject_WRealise. vector_dupfree. eapply M1_computes.
        + eapply Inject_Terminates. vector_dupfree. eapply M1_terminates.
        + eapply RealiseIn_terminatesIn. repeat TM_Correct.
      - eapply RealiseIn_terminatesIn. repeat TM_Correct.
    }
    {
      intros tin i (x&y&HT1&HT2&HT3).
      exists 5. exists (2 + M1_runtime y). repeat split.
      - omega.
      - hnf. omega.
      - intros tout b (H1&H2).
        hnf in H1. specialize (H1 x). cbn in H1. specialize (H1 ltac:(eauto)) as (H1&H1').
        hnf in H2. simpl_not_in.
        destruct b.
        + exists (M1_runtime y), 0. repeat split.
          * omega.
          * hnf. eexists. split. cbn. rewrite <- H2. eauto. omega.
          * intros. omega.
        + omega.
    }
  Qed.

  (* TODO weiter verallgemeinierte Version implementieren... *)

End FoldNat.




Definition Add_step : { M : mTM _ 2 & states M -> bool * unit } :=
  If (Inject MatchNat [|Fin.F1|])
     (Inject Constr_S [|Fin.FS Fin.F1|];; Nop _ _ (true, tt))
     (Nop _ _ (false, tt)).

Definition add_step__f : nat -> nat -> nat :=
  fun n m =>
    match n with
    | 0 => m
    | S _ => S m
    end.

Definition add_step__p1 : nat -> bool * unit := fun n => (is_not_zero n, tt).

Definition add_step__p2 : nat -> nat -> bool * unit := fun n m => (is_not_zero n, tt).

Lemma Add_step_Computes :
  Add_step ⊨c(12)
           Computes_Rel_p (Fin.F1) (Fin.F1) _ _ pred add_step__p1 ∩
           Computes2_Rel_p (Fin.F1) (Fin.FS Fin.F1) (Fin.FS Fin.F1) _ _ _ add_step__f add_step__p2.
Proof.
  eapply RealiseIn_monotone.
  {
    unfold Add_step. repeat TM_Correct.
    + eapply MatchNat_Sem.
    + eapply Constr_S_Sem.
  }
  { cbn. omega. }
  {
    intros tin (yout, tout). split.
    - intros n HEn. destruct H; hnf in H.
      + destruct H as (tmid&(H1&H2)&([]&t)&H3&->&->); hnf in H1, H2, H3. simpl_not_in.
        specialize (H1 n). spec_assert H1 as (n'&->&H1). { unfold reorder. now simpl_vector. } cbn in *. split; auto.
        destruct H3 as (H3&H4); hnf in H3, H4. simpl_not_in. rewrite <- H2, H4 in *; clear H2 H4. auto.
      + destruct H as (tmid&(H1&H2)&->&->); hnf in H1, H2. simpl_not_in. specialize (H1 n).
        spec_assert H1 as (->&H1). { unfold reorder. now simpl_vector. } cbn. auto.
    - intros n m HEn Hem. destruct H; hnf in H.
      + destruct H as (tmid&(H1&H2)&([]&t)&H3&->&->); hnf in H1, H2, H3. simpl_not_in.
        specialize (H1 n). spec_assert H1 as (n'&->&H1). { unfold reorder. now simpl_vector. } cbn in *. split; auto.
        destruct H3 as (H3&H4); hnf in H3, H4. simpl_not_in. rewrite <- H2, H4 in *; clear H2 H4. auto.
      + destruct H as (tmid&(H1&H2)&->&->); hnf in H1, H2. simpl_not_in. specialize (H1 n). spec_assert H1 as (->&H1).
        { unfold reorder. now simpl_vector. } cbn in *. rewrite H2 in *; clear H2. split; auto.
  }
Qed.

Lemma Add_step_Computes_ignoreParam :
  Add_step ⊨c(12)
           Computes_Rel (Fin.F1) (Fin.F1) _ _ pred ∩
           Computes2_Rel (Fin.F1) (Fin.FS Fin.F1) (Fin.FS Fin.F1) _ _ _ add_step__f.
Proof.
  eapply RealiseIn_monotone.
  - eapply Add_step_Computes.
  - omega.
  - apply subrel_and2. split.
    + apply Computes_Rel_ignore_param.
    + apply Computes2_Rel_ignore_param.
Qed.


Definition Add : { M : mTM _ 2 & states M -> unit } := WHILE Add_step.

Lemma add_tail_pred_step (x y : nat) :
  tail_plus (Init.Nat.pred x) (add_step__f x y) = tail_plus x y.
Proof. rewrite <- !plus_tail_plus. destruct x, y; cbn; omega. Qed.


Lemma Add_Sem' :
  Add ⊫ Computes2_Rel (Fin.F1) (Fin.FS Fin.F1) (Fin.FS Fin.F1) _ _ _ tail_plus.
Proof.
  eapply WRealise_monotone.
  {
    unfold Add. TM_Correct. eapply RealiseIn_WRealise. eapply Add_step_Computes.
  }
  {
    hnf. intros tin ((), tout) H. destruct H as (tmid&H1&H2&H3).
    revert tout H2 H3. induction H1 as [ tin | tin tmid tout H1 H2 IH]; intros; hnf in *; intros.
    - specialize (H2 _ H) as (H2&H2'). specialize (H3 _ _ H H0) as (H3&H3'). cbn in *.
      unfold add_step__p1, add_step__p2 in *. destruct x, y; cbn in *; inv H2'; inv H3'; auto.
    - cbn in *. destruct H1 as (()&H11&H12).
      hnf in H11, H12. specialize (H11 x H) as (H11&H11'). specialize (H12 x y H H4) as (H12&H12').
      specialize (IH _ H0 H3). specialize (IH _ _ H11 H12). now rewrite add_tail_pred_step in IH.
  }
Qed.

Lemma Add_Sem :
  Add ⊫ Computes2_Rel (Fin.F1) (Fin.FS Fin.F1) (Fin.FS Fin.F1) _ _ _ Nat.add.
Proof.
  eapply Computes2_Ext_WRealise.
  - apply plus_tail_plus.
  - apply Add_Sem'.
Qed.



(* * Termination *)

Fixpoint step_count (n : nat) : nat :=
  match n with
  | O => 12
  | S n' => 13 + step_count n'
  end.

Lemma step_count_ge_12 (n : nat) :
  12 <= step_count n.
Proof. induction n; cbn; omega. Qed.


Lemma step_count_pred_ge_13 (n : nat) :
  13 + step_count (Init.Nat.pred n) <= step_count n.
Proof.
  destruct n; cbn.
Abort.


Section Test.
  Let t0 := midtape [inl START] (inr false) (map inr [] ++ [inl STOP]).
  Let t1 := midtape [inl START] (inr true) (map inr [false] ++ [inl STOP]).
  Let t2 := midtape [inl START] (inr true) (map inr [true; false] ++ [inl STOP]).
  Let t3 := midtape [inl START] (inr true) (map inr [true; true; false] ++ [inl STOP]).
  Let t4 := midtape [inl START] (inr true) (map inr [true; true; true; false] ++ [inl STOP]).

  Compute execTM (projT1 Add) (step_count 0) [|t0; t0|].
  Compute execTM (projT1 Add) (step_count 0) [|t0; t4|].
  Compute execTM (projT1 Add) (step_count 1) [|t1; t3|].
  Compute execTM (projT1 Add) (step_count 2) [|t2; t3|].
  Compute execTM (projT1 Add) (step_count 3) [|t3; t3|].
  Compute execTM (projT1 Add) (step_count 3) [|t3; t4|].
  Compute execTM (projT1 Add) (step_count 4) [|t4; t0|].
End Test.



Lemma Add_terminatesIn :
  projT1 Add ↓ (fun tin steps => exists x y : nat, tin[@Fin.F1] ≂ x /\ tin[@Fin.FS Fin.F1] ≂ y /\ step_count x <= steps).
Proof.
  eapply While_TerminatesIn.
  {
    eapply RealiseIn_WRealise. eapply Add_step_Computes.
  }
  {
    eapply RealiseIn_terminatesIn. eapply Add_step_Computes.
  }
  {
    intros tin i (m&n&HEncM&HEncN&Hi). exists 12. split.
    - omega.
    - intros [ | ] () tout (HComp1&HComp2).
      + specialize (HComp1 _ HEncM) as (HComp1&HComp1'). specialize (HComp2 _ _ HEncM HEncN) as (HComp2&HComp2').
        unfold add_step__p1, add_step__p2, add_step__f, is_not_zero in *.
        destruct m as [ | m'].
        {
          (* m must have been [false], since [m] is [0]. *)
          exfalso. congruence.
        }
        {
          eexists. split.
          - do 2 eexists. split. eauto. split. eauto. eauto.
          - cbn -[plus]. cbn -[plus] in Hi. rewrite Hi. omega.
        }
      + rewrite <- Hi. eapply step_count_ge_12.
  }
Qed.