Require Import TM.Code.CodeTM TM.Code.MatchNat.
Require Import TM.Basic.Mono Basic.Nop Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.
Require Import TM.Code.Copy.
Require Import Coq.Init.Nat.


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


(*
 * This definition of [tail_plus] differs from the definition of [tail_plus] in the standard library,
 * only that it is recursive over the second number.
 *)

Search tail_plus.

Fixpoint tail_plus (m n : nat) { struct n } : nat :=
  match n with
  | O => m
  | S n' => tail_plus (S m) n'
  end.

Lemma plus_tail_plus (m n : nat) :
  m + n = tail_plus m n.
Proof.
  revert m. induction n as [ | n' IH ]; intros.
  - cbn. omega.
  - cbn.  rewrite <- IH. omega.
Qed.


Fixpoint tail_mult_acc (a m n : nat) {struct n} :=
  match n with
  | O => a
  | S n' => tail_mult_acc (tail_plus a m) m n'
  end.

Definition tail_mult (m n : nat) := tail_mult_acc 0 m n.

Lemma mult_tail_mult_aux (a m n : nat) :
  a + m * n = tail_mult_acc a m n.
Proof.
  revert a m. induction n as [ | n' IH]; intros.
  - cbn. omega.
  - cbn. rewrite <- IH. rewrite <- plus_tail_plus. rewrite Nat.mul_succ_r. omega.
Qed.

Lemma mult_tail_mult (m n : nat) :
  m * n = tail_mult m n.
Proof. pose proof (mult_tail_mult_aux 0 m n) as L. cbn in L. auto. Qed.


(* [tail_pow] is missing at all *)
Print pow.
Fixpoint tail_pow_acc (a m n : nat) {struct n} : nat :=
  match n with
  | O => a
  | S n' => tail_pow_acc (tail_mult a m) m n'
  end.

Definition tail_pow (m n : nat) := tail_pow_acc 1 m n.

Lemma pow_tail_pow_aux (a m n : nat) :
  a * pow m n = tail_pow_acc a m n.
Proof.
  revert a m. induction n as [ | n' IH]; intros.
  - cbn. omega.
  - cbn. rewrite <- IH. rewrite <- mult_tail_mult. eapply Nat.mul_assoc.
Qed.

Lemma pow_tail_pow (m n : nat) :
  pow m n = tail_pow m n.
Proof. pose proof (pow_tail_pow_aux 1 m n) as L. cbn in L. unfold tail_pow. omega. Qed.



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


(** * First-order [nat] iteration machines *)

Section Iter1.

  Variable f : nat -> nat.

  (* [x] is the accu. We iterate over [y]. *)
  Fixpoint iter (x y : nat) {struct y} : nat :=
    match y with
    | 0 => x
    | S y' => iter (f x) y'
    end.

  Variable M1 : { M : mTM (bool^+) 1 & states M -> unit }.
  Hypothesis M1_computes : M1 ⊫ Computes_Rel Fin.F1 Fin.F1 _ _ f.

  Definition iter_step (x y : nat) : nat :=
    match y with
    | 0 => x
    | S _ => f x
    end.


  Definition Iter_step : { M : mTM _ 2 & states M -> bool * unit } :=
    If (Inject MatchNat [|Fin.FS Fin.F1|])
       (Return (Inject M1 [|Fin.F1|]) (true, tt))
       (Nop _ _ (false, tt)).
  

  Definition Iter : { M : mTM _ 2 & states M -> unit } := WHILE Iter_step.


  (** Correctness *)

  Definition tailRec_step_param : nat -> bool * unit := fun n => (is_not_zero n, tt).

  Lemma Iter_step_Computes :
    Iter_step ⊫ Computes_Rel_p (Fin.FS Fin.F1) (Fin.FS Fin.F1) _ _ pred tailRec_step_param ∩
                   Computes2_Rel (Fin.F1) (Fin.FS Fin.F1) (Fin.F1) _ _ _ iter_step.
  Proof.
    eapply WRealise_monotone.
    {
      unfold Iter_step. repeat TM_Correct.
      eapply  RealiseIn_WRealise. eapply MatchNat_Sem.
    }
    {
      intros tin (yout, tout). split.
      - intros n HEn. destruct H; TMSimp.
        + specialize (H n HEn) as (n'&->&H). cbn. auto.
        + specialize (H n HEn) as (->&H). cbn. auto.
      - intros n m HEn HEm. destruct H; TMSimp.
        + specialize (H m HEm) as (n'&->&H). cbn. auto.
        + specialize (H m HEm) as (->&H). cbn. auto.
    }
  Qed.

  Lemma iter_eta (x y : nat) :
    iter (iter_step x y) (Init.Nat.pred y) = iter x y.
  Proof. destruct x, y; cbn; omega. Qed.


  Lemma Iter_Computes :
    Iter ⊫ Computes2_Rel (Fin.F1) (Fin.FS Fin.F1) (Fin.F1) _ _ _ iter.
  Proof.
    eapply WRealise_monotone.
    {
      unfold Iter. TM_Correct. eapply Iter_step_Computes.
    }
    {
      hnf. intros tin ((), tout) H. destruct H as (tmid&H1&H2&H3).
      induction H1 as [ tin | tin tmid1 tmid2 HStar _ IH]; intros; hnf in *; intros.
      - specialize (H2 _ H0) as (H2&H2'). specialize (H3 _ _ H H0).
        unfold tailRec_step_param in H2'. destruct y; cbn in H2'; try congruence.
        cbn. auto.
      - cbn in *. do 2 spec_assert IH; auto.
        destruct HStar as (() & HStar1&HStar2).
        specialize (HStar1 y H0) as (HStar1&HStar1').
        specialize (HStar2 x y H H0).
        specialize (IH _ _ HStar2 HStar1).
        now rewrite iter_eta in IH.
    }
  Qed.


  (** Termination *)

  Variable M1_runtime : nat -> nat.
  Hypothesis M1_terminates : projT1 M1 ↓ (fun tin k => exists y, tin[@Fin.F1] ≂ y /\ M1_runtime y <= k).

  Lemma Iter_step_terminates :
    projT1 Iter_step ↓
           (fun tin k => exists x y, tin[@Fin.F1] ≂ x /\ tin[@Fin.FS Fin.F1] ≂ y /\
                             match y with
                             | O => 6
                             | S y' => 6 + M1_runtime x
                             end <= k).
  Proof.
    unfold Iter_step.
    eapply TerminatesIn_monotone.
    {
      repeat TM_Correct.
      - eapply RealiseIn_WRealise, MatchNat_Computes_Pred.
      - eapply RealiseIn_terminatesIn, MatchNat_Computes_Pred.
    }
    {
      intros tin i (x&y&HT1&HT2&HT3).
      destruct y as [ | y' ].
      - exists 5, 0. repeat split.
        + omega.
        + cbn. omega.
        + intros tout b (HComp1&HComp2). cbn in HComp1, HComp2. specialize (HComp1 O HT2) as (HComp11&HComp12).
          cbn in HComp12. subst. omega.
      - exists 5, (M1_runtime x). repeat split.
        + omega.
        + hnf. omega.
        + intros tout b (H1&H2).
          hnf in H1. cbn -[add] in *. simpl_not_in. rewrite H2 in *; clear H2. specialize (H1 (S y') HT2) as (H1&->).
          cbn. exists x. split. assumption. auto.
    }
  Qed.


  Fixpoint Iter_steps (m n : nat) { struct n } : nat :=
    match n with
    | O => 6
    | S n' => 7 + M1_runtime m + Iter_steps (f m) n'
    end.

  Lemma Iter_steps_ge5 (m n : nat) :
    5 <= Iter_steps m n.
  Proof. destruct n; cbn; omega. Qed.


  Lemma Iter_steps_homogene (m n k : nat) :
    (forall x, M1_runtime x <= k) ->
    Iter_steps m n <= 6 + (7 + k) * n.
  Proof.
    revert m. induction n as [ | n' IH]; intros; cbn -[add mult] in *.
    - omega.
    - specialize (IH (f m) H). pose proof (H (f m)) as H1. pose proof (H m) as H2.
      rewrite !Nat.mul_succ_r.
      rewrite !Nat.mul_add_distr_r in *.
      rewrite !Nat.add_assoc in *.
      omega. (* Oh [omega], my dear [omega]! *)
  Qed.


  Lemma Iter_Terminates :
    projT1 Iter ↓ (fun tin k => exists x y, tin[@Fin.F1] ≂ x /\ tin[@Fin.FS Fin.F1] ≂ y /\ Iter_steps x y <= k).
  Proof.
    unfold Iter. eapply While_TerminatesIn.
    - eapply Iter_step_Computes.
    - eapply Iter_step_terminates.
    - intros tin k (x&y&HeX&HeY&Hk).
      destruct y as [ | y' ] eqn:Ey.
      + exists 6. repeat split.
        * exists x, y. subst. auto.
        * intros b () tout (HComp1&HComp2). specialize (HComp1 _ HeY) as (HComp11&HComp12). specialize (HComp2 _ _ HeX HeY).
          cbn -[plus add] in *. cbv in HComp12. inv HComp12. auto.
      + exists (6 + M1_runtime x). repeat split.
        * exists x, y. subst. repeat split; auto.
        * intros b () tout (HComp1&HComp2). specialize (HComp1 _ HeY) as (HComp11&HComp12). specialize (HComp2 _ _ HeX HeY).
          cbn -[plus add] in *. cbv in HComp12. inv HComp12.
          eexists. repeat split.
          -- eauto.
          -- rewrite <- Hk. omega.
  Qed.
  
End Iter1.


Lemma add_steps : forall m n, Iter_steps S (fun _ => 5) m n = 6 + 12 * n.
Proof.
  intros m n. revert m. induction n as [ | n' IH]; intros; cbn -[plus mult] in *.
  - omega.
  - rewrite IH. omega.
Qed.


Definition Add := Iter Constr_S.

Lemma tail_add_iter (m n : nat) :
  tail_plus m n = iter S m n.
Proof.
  revert m. induction n; intros; cbn in *.
  omega. rewrite IHn. omega.
Qed.

Lemma Add_WRealise' :
  Add ⊫ Computes2_Rel (Fin.F1) (Fin.FS Fin.F1) (Fin.F1) _ _ _ tail_plus.
Proof.
  eapply Computes2_Ext_WRealise.
  - refine tail_add_iter.
  - unfold Add. apply Iter_Computes.
    eapply WRealise_monotone. 
    + eapply RealiseIn_WRealise. apply Constr_S_Sem.
    + intros tin ((), tout) H. hnf in *. auto.
Qed.

Lemma Add_Terminates :
  projT1 Add ↓ (fun tin k => exists x y, tin[@Fin.F1] ≂ x /\ tin[@Fin.FS Fin.F1] ≂ y /\ 6 + 12 * y <= k).
Proof.
  eapply TerminatesIn_monotone.
  - unfold Add. apply Iter_Terminates.
    + eapply RealiseIn_WRealise. apply Constr_S_Sem.
    + eapply TerminatesIn_monotone. eapply RealiseIn_terminatesIn. apply Constr_S_Sem.
      instantiate (1 := fun _ => 5). intros. hnf.
      destruct H as (?&?&H). omega.
  - intros tin k. intros (x&y&HeX&HeY&Hk). exists x, y. repeat split; auto. rewrite <- Hk.
    pose proof add_steps x y as ->. omega.
Qed.


(*
Section Test.
  Let t0 := midtape [inl START] (inr false) (map inr [] ++ [inl STOP]).
  Let t1 := midtape [inl START] (inr true) (map inr [false] ++ [inl STOP]).
  Let t2 := midtape [inl START] (inr true) (map inr [true; false] ++ [inl STOP]).
  Let t3 := midtape [inl START] (inr true) (map inr [true; true; false] ++ [inl STOP]).
  Let t4 := midtape [inl START] (inr true) (map inr [true; true; true; false] ++ [inl STOP]).

  Let step_count n := 6 + 12 * n.

  Compute execTM_p Add (step_count 0) [|t0; t0|].
  Compute execTM_p Add (step_count 4) [|t0; t4|].
  Compute execTM_p Add (step_count 3) [|t1; t3|].
  Compute execTM_p Add (step_count 3) [|t2; t3|].
  Compute execTM_p Add (step_count 3) [|t3; t3|].
  Compute execTM_p Add (step_count 4) [|t3; t4|].
  Compute execTM_p Add (step_count 0) [|t4; t0|].
End Test.
*)