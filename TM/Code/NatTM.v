Require Import TM.Code.CodeTM TM.Code.MatchNat.
Require Import TM.Basic.Mono Basic.Nop Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.
Require Import TM.Code.Copy.


(*** Machines that compte natural functions *)


Require Import Coq.Init.Nat.

(* Don't simplify [skipn (S n) xs]; only, if the number and the lists are constructors *)
Local Arguments skipn { A } !n !l.

Fixpoint tail_plus (m n : nat) { struct m } : nat :=
  match m with
  | O => n
  | S m' => tail_plus m' (S n)
  end.

Lemma plus_tail_plus (m n : nat) :
  m + n = tail_plus m n.
Proof.
  revert n. induction m as [ | m' IH ]; intros.
  - cbn. omega.
  - cbn. rewrite <- IH. omega.
Qed.


Fixpoint tail_mult_acc (a m n : nat) {struct m} :=
  match m with
  | O => a
  | S m' => tail_mult_acc (a + n) m' n
  end.

Definition tail_mult (m n : nat) := tail_mult_acc 0 m n.

Lemma mult_tail_mult_aux (a m n : nat) :
  a + m * n = tail_mult_acc a m n.
Proof.
  revert a n. induction m as [ | m' IH]; intros.
  - cbn. omega.
  - cbn. rewrite <- IH. omega.
Qed.

Lemma mult_tail_mult (m n : nat) :
  m * n = tail_mult m n.
Proof. pose proof (mult_tail_mult_aux 0 m n) as L. cbn in L. auto. Qed.


(* [tail_pow] is missing at all *)
Fixpoint tail_pow_acc (a m n : nat) {struct n} : nat :=
  match n with
  | O => a
  | S n' => tail_pow_acc (a * m) m n'
  end.

Definition tail_pow (m n : nat) := tail_pow_acc 1 m n.

Lemma pow_tail_pow_aux (a m n : nat) :
  a * pow m n = tail_pow_acc a m n.
Proof.
  revert a m. induction n as [ | n' IH]; intros.
  - cbn. omega.
  - cbn. rewrite <- IH. eapply Nat.mul_assoc.
Qed.

Lemma pow_tail_pow (m n : nat) :
  pow m n = tail_pow m n.
Proof. pose proof (pow_tail_pow_aux 1 m n) as L. cbn in L. unfold tail_pow. omega. Qed.


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
          tout[@Fin1] ≂ tail_plus m n
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
      rewrite <- Nat.add_succ_comm in IH1.
      split; cbn in *; auto.
  }
Qed.


Lemma Add_Loop_Computes : Add_Loop ⊫ Computes2_Rel Fin0 Fin1 Fin1 _ _ _ tail_plus.
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
          tout[@Fin1] ≂ tail_plus m n /\
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


Definition Add_steps m := 139 + 48 * m.


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

    exists (44 + 16 * m), (94 + 32 * m). repeat split.
    - omega.
    - cbn -[add mult]. eexists. split.
      + eapply tape_encodes_size_encodes; eauto using tape_encodes_l_encodes_size.
      + rewrite nat_encode_length. omega.
    - intros tmid1 () (H1&H2). cbn in H1, H2. unfold finType_CS in *. cbn -[add mult] in *. 
      specialize (H2 Fin1 ltac:(vector_not_in)). rewrite H2 in *. clear H2.
      specialize (H1 _ _ _ HEncM) as (H1&H2). unfold finType_CS in *. rewrite <- H1 in *. clear H1.

      exists (11 + 12 * m), (82 + 20 * m). repeat split.
      + omega.
      + cbn -[add mult]. do 2 eexists. repeat split. eapply tape_encodes_l_encodes; eauto. eauto.
        unfold Add_Loop_steps. omega.
      + intros tmid2 () (H3&H4).
        specialize (H4 Fin2 ltac:(vector_not_in)). unfold finType_CS in *. cbn -[add mult] in *. try rewrite H4 in *. (* ??? *)
        specialize (H3 _ _ _ _ ltac:(eauto using tape_encodes_l_encodes_size) ltac:(eauto)) as (H5&H6). clear H6.
        do 5 eexists. repeat split. eauto. unfold finType_CS in *. cbn in tmid2, H4. cbn. rewrite <- H4.
        do 2 eexists. unshelve (repeat (split; [ shelve | eauto])). cbn. omega.
        rewrite !nat_encode_length. cbn [length].
        rewrite !Nat.mul_succ_l, !Nat.mul_succ_r. omega.
       

  }
Qed.