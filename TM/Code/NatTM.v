Require Import TM.Code.CodeTM TM.Code.MatchNat.
Require Import TM.Basic.Mono Basic.Nop Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.


(* Nat.add is not tail-recursive *)

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
Proof. destruct n; cbn; split; auto. Qed.


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
  projT1 Add ↓ (fun tin steps => exists x y : nat, tin[@Fin.F1] ≂ x /\ tin[@Fin.FS Fin.F1] ≂ y /\ step_count x = steps).
Proof.
  eapply While_terminatesIn.
  {
    eapply WRealise_strengthen.
    - eapply RealiseIn_WRealise. apply Add_step_Computes.
    - eapply WRealise_R_mTM.
  }
  {
    eapply RealiseIn_terminatesIn. eapply Add_step_Computes.
  }
  {
    eapply functionalOn_intersect. left. eapply functional_functionalOn. eapply R_canonical_functional.
  }
  {
    intros tin ? (m&n&HEncM&HEncN&<-).
    pose proof (Add_step_Computes tin) as (outc&H1&H2&H3).
    hnf in H1, H2, H3. specialize (H2 _ HEncM) as (H2&H2'); specialize (H3 _ _ HEncM HEncN) as (H3&H3').
    exists (ctapes outc), (fst (projT2 Add_step (cstate outc))), (snd (projT2 Add_step (cstate outc))), 12. do 2 split.
    - hnf. exists outc, 12. split; auto; split; auto. now rewrite <- surjective_pairing.
    - split.
      + hnf. intros ? <- % (tape_encodes_injective HEncM). split; auto. now rewrite <- surjective_pairing.
      + hnf. intros ? ? <- % (tape_encodes_injective HEncM) <- % (tape_encodes_injective HEncN). split; auto.
        now rewrite <- surjective_pairing.
    - omega.
    - destruct (fst _) eqn:E1.
      +
        destruct m as [ | m'].
        {
          (* m must have been [false]! *)
          exfalso. cbn in H2, H3, H3'. unfold add_step__p2 in H3'. cbn in H3'.
          enough (fst (projT2 Add_step (cstate outc)) = false) as L.
          { enough (true = false) by congruence. now rewrite <- E1, <- L. }
          unfold finType_CS in *; cbn in *. now rewrite H3'.
        }
        {
          replace (12 + 1) with 13 by reflexivity. eexists. split.
          * exists m', (add_step__f (S m') n). repeat split. eauto. eauto.
          * cbn. constructor.
        }
      + apply step_count_ge_12.
  }
Qed.