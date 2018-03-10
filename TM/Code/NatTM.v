Require Import TM.Code.CodeTM TM.Code.MatchNat.
Require Import TM.Basic.Mono Basic.Nop Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.
Require Import TM.Code.Copy.


(*** Machines that compte natural functions *)


Require Import Coq.Init.Nat.

(* Don't simplify [skipn (S n) xs]; only, if the number and the lists are constructors *)
Local Arguments skipn { A } !n !l.

Lemma nat_encode_length (n : nat) :
| encode n : list bool | = S n.
Proof. induction n; cbn; auto. Qed.


Lemma max_plus_minus_le (m n : nat) :
  n + (m - n) <= max m n.
Proof.
  assert (m <= n \/ n <= m) as [H|H] by omega.
  - rewrite <- Nat.le_max_r. omega.
  - rewrite <- Nat.le_max_l. omega.
Qed.

Lemma max_max_le (m n : nat) :
  max (max m n) n = max m n.
Proof.
  assert (m <= n \/ n <= m) as [H|H] by omega.
  - erewrite Nat.max_r.
    + symmetry. now eapply max_r.
    + eapply Nat.eq_le_incl. now eapply max_r.
  - erewrite Nat.max_l.
    + reflexivity.
    + apply Nat.le_max_r.
Qed.


(** * Addition *)


(*
 * In pseudocode:
 * while (m--) {
 *   n++;
 * }
 *)

Definition Add_Step : { M : mTM _ 2 & states M -> bool * unit } :=
  If (Inject MatchNat [|Fin0|])
     (Return (Inject Constr_S [|Fin1|]) (true, tt))
     (Nop _ _ (false, tt)).


Definition Add_Loop : { M : mTM _ 2 & states M -> unit } := WHILE Add_Step.

Definition Add : { M : mTM _ 3 & states M -> unit } :=
  Inject (CopyValue' _) [|Fin0; Fin2|];; (* save the counter *)
  Inject Add_Loop (app_tapes _ _);; (* Main loop *)
  Inject (RestoreValue _) [|Fin0; Fin2|]. (* restore the value *)


(** Correctness *)


Definition Add_Step_Rel : Rel (tapes (bool^+) 2) ((bool * unit) * tapes (bool^+) 2) :=
  fun tin '(yout, tout) =>
    forall m n s1 s2,
      tin [@Fin0] ≂{s1;s2} m ->
      tin [@Fin1] ≂ n ->
      match m with
      | O =>
        tout = tin /\
        yout = (false, tt)
      | S m' =>
        tout[@Fin0] ≂{S s1; s2} m' /\
        tout[@Fin1] ≂ S n /\
        yout = (true, tt)
      end.

Lemma Add_Step_Sem : Add_Step ⊨c(11) Add_Step_Rel.
Proof.
  eapply RealiseIn_monotone.
  {
    unfold Add_Step. repeat TM_Correct.
    - apply MatchNat_Sem.
    - apply Constr_S_Sem.
  }
  { cbn. omega. }
  {
    intros tin (yout, tout) H. cbn. intros m n s1 s2 HEncM HEncN. TMSimp.
    destruct HEncM as (r1&r2&Hs1&Hs2&HEncM).
    destruct H; TMSimp inv_pair; clear_trivial_eqs.
    - specialize (H _ _ _ HEncM). destruct m; TMSimp; try congruence. split.
      + do 2 eexists. split. shelve. split. shelve. eauto. Unshelve. all: cbn; omega.
      + eauto.
    - specialize (H _ _ _ HEncM). destruct m; TMSimp; try congruence. split.
      + pose proof tape_encodes_l_injective H HEncM. destruct_tapes. cbn in *. subst. f_equal; eauto.
      + eauto.
  }
Qed.


Definition Add_Loop_Rel : Rel (tapes bool^+ 2) (unit * tapes bool^+ 2) :=
  ignoreParam (
      fun tin tout =>
        forall m n s1 s2,
          tin [@Fin0] ≂{s1;s2} m ->
          tin [@Fin1] ≂ n ->
          tout[@Fin0] ≂{m+s1; s2} 0 /\
          tout[@Fin1] ≂ m + n
    ).

Lemma Add_Loop_WRealise : Add_Loop ⊫ Add_Loop_Rel.
Proof.
  eapply WRealise_monotone.
  { unfold Add_Loop. repeat TM_Correct. eapply RealiseIn_WRealise. apply Add_Step_Sem. }
  {
    intros tin ((), tout) (tmid&HStar&HLastStep).
    induction HStar as [ tin | tin tmid1 tmid2 HStar _ IH]; intros m n s1 s2 HEncM HEncN.
    - cbn in HLastStep. specialize (HLastStep _ _ _ _ HEncM HEncN). destruct m; TMSimp; inv_pair. eauto.
    - repeat (spec_assert IH; eauto). cbn in HLastStep, IH, HStar. destruct HStar as (()&HStar). cbn in HStar.
      specialize (HStar _ _ _ _ HEncM HEncN).
      destruct m; TMSimp; inv_pair.
      specialize (IH _ _ _ _ H H0) as (IH1&IH2).
      rewrite <- Nat.add_succ_comm in IH1, IH2. cbn in *. auto.
  }
Qed.


Lemma Add_Loop_Computes : Add_Loop ⊫ Computes2_Rel Fin0 Fin1 Fin1 _ _ _ plus.
Proof.
  eapply WRealise_monotone. apply Add_Loop_WRealise.
  intros tin ((), tout) H. intros m n HEncM HEncN. hnf in H.
  destruct HEncM as (r1 & r2 & HEncM % tape_encodes_l_encodes_size).
  now specialize (H _ _ _ _ HEncM HEncN) as (?&?).
Qed.


(* Save the counter; do the addition; restore the counter *)
Definition Add_Rel : Rel (tapes bool^+ 3) (unit * tapes bool^+ 3) :=
  ignoreParam (
      fun tin tout =>
        forall m n s2 s3,
          tin [@Fin0] ≂{0;s2} m ->
          tin [@Fin1] ≂ n ->
          isLeft tin[@Fin2] s3 ->
          tout[@Fin0] ≂{0;s2} m /\
          tout[@Fin1] ≂ m + n /\
          isLeft tout[@Fin2] (max s3 (S (S m)))
    ).



Lemma Add_WRealise : Add ⊫ Add_Rel.
Proof.
  Local Arguments Encode_Nat : simpl never.
  eapply WRealise_monotone.
  {
    unfold Add. repeat TM_Correct.
    - apply CopyValue'_WRealise with (X := nat).
    - apply Add_Loop_WRealise.
    - apply RestoreValue_WRealise_size with (X := nat).
  }
  {
    intros tin ((), tout) H. intros m n s2 s3 HEncM HEncN HEncM'. TMSimp.
    hnf in HEncM'. destruct HEncM' as (int3x&int3rest&Hint3rest&HEncM'). TMSimp. clear HEncM'.

    (* Rewrite Lift-N equations *)
    specialize (H1 Fin1 ltac:(vector_not_in)). TMSimp. clear H1.
    specialize (H3 Fin1 ltac:(vector_not_in)). TMSimp. clear H3.
    specialize (H4 Fin2 ltac:(vector_not_in)). TMSimp. clear H4.

    (* Instantiate computation relations *)
    destruct HEncM as (r1&r2&Hr1&Hr2&HEncM).
    specialize (H _ _ _ HEncM) as (H&H'). TMSimp. clear H.
    specialize (H0 _ _ _ _ ltac:(hnf;eauto) ltac:(eauto)) as (H0&H0').
    specialize H2 with (1 := H0) (2 := tape_encodes_l_encodes_size H') as (H2&H2').

    repeat split.
    - eapply tape_encodes_size_monotone. eapply H2. omega. rewrite !nat_encode_length. cbn. omega.
    - assumption.
    - eapply isLeft_monotone; eauto. rewrite !nat_encode_length. rewrite skipn_length. cbn.
      enough (S (S (m + (s3 - S (S m)))) <= max s3 (S (S m))) by omega.
      change ((2 + m) + (s3 - (2 + m)) <= max s3 (2 + m)).
      eapply max_plus_minus_le.
  }
Qed.


(** Termination *)

Definition Add_Loop_steps m := 11 + m * 12.

Lemma Add_Loop_Terminates :
  projT1 Add_Loop ↓
         (fun tin i => exists m n,
              tin[@Fin0] ≂ m /\
              tin[@Fin1] ≂ n /\
              Add_Loop_steps m <= i).
Proof.
  unfold Add_Loop, Add_Loop_steps. repeat TM_Correct.
  { eapply RealiseIn_WRealise. apply Add_Step_Sem. }
  { eapply RealiseIn_terminatesIn. apply Add_Step_Sem. }
  {
    intros tin i (m&n&HEncM&HEncN&Hi).
    destruct HEncM as (r1 & r2 & HEncM % tape_encodes_l_encodes_size).
    destruct m.
    - exists 11. repeat split.
      + omega.
      + intros b () tmid H. cbn in H. specialize (H _ _ _ _ HEncM HEncN). cbn in *. destruct H as (H1&H2); subst; inv H2. auto.
    - exists 11. repeat split.
      + omega.
      + intros b () tmid H. cbn in H. specialize (H _ _ _ _ HEncM HEncN). cbn -[plus mult] in *.
        destruct H as (H1&H2&H3). inv H3.
        exists (11 + m * 12). repeat split.
        * do 2 eexists. split. eapply tape_encodes_size_encodes; eauto. split. eauto. omega.
        * omega.
  }
Qed.


Definition Add_steps m := 139 + 52 * m.


Lemma Add_Terminates :
  projT1 Add ↓
         (fun tin i => exists m n s2 s3,
              tin[@Fin0] ≂{0; s2} m /\
              tin[@Fin1] ≂ n /\
              isLeft tin[@Fin2] s3 /\
              Add_steps m <= i).
Proof.
  unfold Add, Add_steps. eapply TerminatesIn_monotone.
  {
    repeat TM_Correct.
    - eapply CopyValue'_WRealise.
    - eapply CopyValue'_Terminates.
    - eapply Add_Loop_WRealise.
    - eapply Add_Loop_Terminates.
    - eapply RestoreValue_Terminates.
  }
  {
    intros tin i (m & n & s2 & s3 & HEncM & HEncN & HEncM' & Hi).
    destruct HEncM as (r1&r2&Hr1&Hr2&HEncM). destruct r1; cbn in Hr1; inv Hr1.
    destruct HEncM' as (int3x&int3rest&Hint3rest&HEncM').
    unfold finType_CS in *. cbn -[add mult] in *. rewrite HEncM' in *. clear HEncM'.

    exists (44 + 16 * m), (94 + 36 * m). repeat split.
    - omega.
    - cbn -[add mult]. eexists. split.
      + eapply tape_encodes_size_encodes; eauto using tape_encodes_l_encodes_size.
      + rewrite nat_encode_length. omega.
    - intros tmid1 () (H1&H2). cbn in H1, H2. unfold finType_CS in *. cbn -[add mult] in *.
      specialize (H2 Fin1 ltac:(vector_not_in)). rewrite H2 in *. clear H2.
      specialize (H1 _ _ _ HEncM) as (H1&H2). unfold finType_CS in *. rewrite <- H1 in *. clear H1.

      exists (11 + 12 * m), (82 + 24 * m). repeat split.
      + omega.
      + cbn -[add mult]. do 2 eexists. repeat split. eapply tape_encodes_l_encodes; eauto. eauto.
        unfold Add_Loop_steps. omega.
      + intros tmid2 () (H3&H4).
        specialize (H4 Fin2 ltac:(vector_not_in)). unfold finType_CS in *. cbn -[add mult] in *. try rewrite H4 in *. (* ??? *)
        specialize (H3 _ _ _ _ ltac:(eauto using tape_encodes_l_encodes_size) ltac:(eauto)) as (H5&H6). clear H6.
        do 5 eexists. repeat split. eauto. unfold finType_CS in *. cbn in tmid2, H4. cbn. rewrite <- H4.
        do 2 eexists. unshelve (repeat (split; [ shelve | eauto])). cbn. omega.
        rewrite !nat_encode_length. cbn [length]. omega.
  }
Qed.



(** * Multiplication *)

(*
 * t0: m  (counter for mult) (stays left)
 * t1: n  (m for add) (stays left)
 * t2: a  (n for add) (stays left)
 * t3: n' (copy of m for add) (stays left)
 * t4: m' (copy of m) (stays left)
 *)

Definition Mult_Step : { M : mTM _ 4 & states M -> bool * unit } :=
  If (Inject MatchNat [|Fin0|])
     (Return (Inject Add (add_tapes 3 1)) (true, tt))
     (Nop _ _ (false, tt)).


Definition Mult_Loop : { M : mTM _ 4 & states M -> unit } := WHILE Mult_Step.

Definition Mult : { M : mTM _ 5 & states M -> unit } :=
  Inject (CopyValue' _) [|Fin0; Fin4|];; (* save the counter *)
  Inject Mult_Loop (app_tapes 4 1);; (* Main loop *)
  Inject (RestoreValue _) [|Fin0; Fin4|]. (* restore the value *)


(** Correctness *)

Print Add_Step_Rel.
Print Add_Rel.

Definition Mult_Step_Rel : Rel (tapes (bool^+) 4) ((bool * unit) * tapes (bool^+) 4) :=
  fun tin '(yout, tout) =>
    forall (a m n s0 s0' s1 s3 : nat),
      tin [@Fin0] ≂{s0;s0'} m ->
      tin [@Fin1] ≂{0;s1} n ->
      tin [@Fin2] ≂ a ->
      isLeft tin[@Fin3] s3 ->
      match m with
      | O =>
        tout = tin /\ (* nothing changes *)
        yout = (false, tt) (* break *)
      | S m' =>
        tout[@Fin0] ≂{S s0; s0'} m' /\ (* m decrements *)
        tout[@Fin1] ≂{0;s1} n /\ (* n stays unchanged *)
        tout[@Fin2] ≂ n + a /\ (* a is incremented by n *)
        isLeft tout[@Fin3] (max s3 (S (S n))) /\ (* n' stays left and has not allocated more memory than needed to hold n *)
        yout = (true, tt) (* continue *)
      end.



Lemma Mult_Step_WRealise : Mult_Step ⊫ Mult_Step_Rel.
Proof.
  eapply WRealise_monotone.
  {
    unfold Mult_Step. repeat TM_Correct.
    - eapply RealiseIn_WRealise. eapply MatchNat_Sem.
    - eapply Add_WRealise.
  }
  {
    intros tin ((bout, ()), tout) H.
    intros a m n s0 s0' s1 s3 HEncM HEncN HEncA HEncN'.
    pose proof HEncM as (r1&r2&Hr1&Hr2&HEncM').
    TMSimp. destruct H; TMSimp; inv_pair.
    - (* Condition of if evaluated to [true] *)

      (* Lift-N rewritings *)
      pose proof (H2 Fin1 ltac:(vector_not_in)) as L2. TMSimp. clear L2.
      pose proof (H2 Fin2 ltac:(vector_not_in)) as L2. TMSimp. clear L2.
      pose proof (H2 Fin3 ltac:(vector_not_in)) as L2. TMSimp. clear L2. clear H2.
      specialize (H3 Fin0 ltac:(vector_not_in)). TMSimp. clear H3.

      (* Computation applications *)
      specialize (H _ _ _ ltac:(eauto)). destruct m; TMSimp; try congruence.
      specialize (H1 _ _ _ _ ltac:(eauto) ltac:(eauto) ltac:(eauto)) as (H1&H2&H3).

      repeat split.
      + hnf. do 2 eexists. unshelve (do 2 (split; [ shelve | eauto])). cbn. omega.
      + assumption.
      + assumption.
      + assumption.

    - (* Condition of if evaluated to [false] *)

      (* Computation applications *)
      specialize (H _ _ _ ltac:(eauto)). destruct m; TMSimp; try congruence.

      destruct_tapes; cbn in *.

      (* Lift-N rewritings *)
      pose proof (H1 Fin1 ltac:(vector_not_in)) as L1. TMSimp.
      pose proof (H1 Fin2 ltac:(vector_not_in)) as L1. TMSimp.
      pose proof (H1 Fin3 ltac:(vector_not_in)) as L1. TMSimp. clear H1.

      split; auto. f_equal. eapply tape_encodes_l_injective; eauto.
  }
Qed.


(*
 * t0: m  (counter for mult) (stays left)
 * t1: n  (m for add) (stays left)
 * t2: a  (n for add) (stays left)
 * t3: n' (copy of m for add) (stays left)
 *)

Definition Mult_Loop_Rel : Rel (tapes (bool^+) 4) (unit * tapes (bool^+) 4) :=
  ignoreParam (
      fun tin tout =>
        forall (a m n s0 s0' s1 s3 : nat),
          tin [@Fin0] ≂{s0;s0'} m ->
          tin [@Fin1] ≂{0;s1} n ->
          tin [@Fin2] ≂ a ->
          isLeft tin[@Fin3] s3 ->
          tout[@Fin0] ≂{m + s0; s0'} 0 /\ (* m is decremented to 0 *)
          tout[@Fin1] ≂{0;s1} n /\ (* n stays unchanged *)
          tout[@Fin2] ≂ m * n + a /\ (* a is m times incremented by n *)
          isLeft tout[@Fin3] (max s3 (S (S n))) (* n' stays left and has not allocated more memory than needed to hold n *)
    ).


Lemma Mult_Loop_WRealise : Mult_Loop ⊫ Mult_Loop_Rel.
Proof.
  eapply WRealise_monotone.
  { unfold Mult_Loop. repeat TM_Correct. apply Mult_Step_WRealise. }
  {
    intros tin ((), tout) (tmid&HStar&HLastStep).
    induction HStar as [ tin | tin tmid1 tmid2 HStar _ IH];
      intros a m n s0 s0' s1 s3 HEncM HEncN HEncA HEncN'.
    - cbn in HLastStep. specialize (HLastStep _ _ _ _ _ _ _ HEncM HEncN HEncA HEncN').
      destruct m; TMSimp; inv_pair. eauto using isLeft_monotone, Nat.le_max_l.
    - repeat (spec_assert IH; eauto). cbn in HLastStep, IH, HStar. destruct HStar as (()&HStar). cbn in HStar.
      specialize (HStar _ _ _ _ _ _ _ HEncM HEncN HEncA HEncN').
      destruct m; TMSimp; inv_pair.
      specialize (IH _ _ _ _ _ _ _ H H0 H1 H2) as (IH1&IH2&IH3&IH4).
      rewrite <- Nat.add_succ_comm in IH1. cbn in *.
      repeat split; cbn in *; auto.
      + enough (n + m * n + a = m * n + (n + a)) as -> by auto; omega.
      + eapply isLeft_monotone; eauto. apply Nat.eq_le_incl. apply max_max_le.
  }
Qed.