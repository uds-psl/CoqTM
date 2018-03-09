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



Section Computes2_Reset.
  Variable (sig : finType) (n : nat).
  Variable (i1 i2 : Fin.t n).
  Variable (X Y Z : Type) (encX : codeable sig X) (encY : codeable sig Y) (encZ : codeable sig Z).

  
  (* The 0th tape is the first input and the value doesn't change. The 1st tape is the second input and the output. *)
  Definition Computes2_Reset_Rel (f : X -> Y -> Z) : Rel (tapes (sig^+) n) (unit * tapes (sig^+) n) :=
    ignoreParam (
        fun tin tout =>
          forall (x : X) (y : Y),
            tin[@i1] ≂ x ->
            tin[@i2] ≂ y ->
            tout[@i1] ≂ x /\
            tout[@i2] ≂ f x y
      ).

  Section Computes2_Reset_Ext.
    Variable (f f' : X -> Y -> Z) (ext_fun : forall x y, f x y = f' x y).

    Lemma Computes2_Reset_ext :
      Computes2_Reset_Rel f' <<=2 Computes2_Reset_Rel f.
    Proof.
      intros tin (yout, tout) HRel. hnf. intros x y EncX EncY. hnf in HRel. specialize (HRel _ _ EncX EncY). congruence.
    Qed.

    Variable pM : { M : mTM sig^+ n & states M -> unit }.

    Lemma Computes2_Reset_Ext_WRealise :
      pM ⊫ Computes2_Reset_Rel f' ->
      pM ⊫ Computes2_Reset_Rel f.
    Proof.
      intros H. eapply WRealise_monotone.
      - eapply H.
      - eapply Computes2_Reset_ext.
    Qed.

  End Computes2_Reset_Ext.

End Computes2_Reset.



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


(** * First-order [nat] iteration machines *)


Section Iter1.

  Variable f : nat -> nat.

  (* [y] is the accu. We iterate over [x]. *)
  Fixpoint iter (x y : nat) {struct x} : nat :=
    match x with
    | 0 => y
    | S x' => iter x' (f y)
    end.

  Variable M1 : { M : mTM (bool^+) 1 & states M -> unit }.
  Hypothesis M1_computes : M1 ⊫ Computes_Rel Fin.F1 Fin.F1 _ _ f.

  Definition Iter_Step : { M : mTM _ 2 & states M -> bool * unit } :=
    If (Inject MatchNat [|Fin0|])
       (Return (Inject M1 [|Fin1|]) (true, tt))
       (Nop _ _ (false, tt)).

  
  Definition Iter_Loop : { M : mTM _ 2 & states M -> unit } := WHILE Iter_Step.

  Definition Iter : { M : mTM _ 3 & states M -> unit } :=
    Inject (CopyValue' _) [|Fin0; Fin2|];; (* save the counter *)
    Inject Iter_Loop (app_tapes _ _);; (* Main loop *)
    Inject (RestoreValue _) [|Fin0; Fin2|]. (* restore the value *)


  (** Correctness *)

  
  (*
  Definition Iter_Step_Rel : Rel (tapes (bool^+) 2) ((bool * unit) * tapes (bool^+) 2) :=
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
          tout[@Fin1] ≂ f n /\
          yout = (true, tt)
        end.
   *)

  Definition Iter_Step_Rel : Rel (tapes (bool^+) 2) ((bool * unit) * tapes (bool^+) 2) :=
    ignoreSecond (
        if? (fun tin tout =>
               forall m n s1 s2,
                 tin [@Fin0] ≂{s1;s2} m ->
                 tin [@Fin1] ≂ n ->
                 exists m', m = S m' /\
                       tout[@Fin0] ≂{S s1; s2} m' /\
                       tout[@Fin1] ≂ f n)
          ! (fun tin tout =>
               forall m n s1 s2,
                 tin [@Fin0] ≂{s1;s2} m ->
                 tin [@Fin1] ≂ n ->
                 m = 0 /\ tout = tin)
      ).

  (*
  Lemma Iter_Step_WRealise : Iter_Step ⊫ Iter_Step_Rel.
  Proof.
    eapply WRealise_monotone.
    {
      unfold Iter_Step. repeat TM_Correct.
      - eapply RealiseIn_WRealise. apply MatchNat_Sem.
    }
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
   *)

  Lemma Iter_Step_WRealise : Iter_Step ⊫ Iter_Step_Rel.
  Proof.
    eapply WRealise_monotone.
    {
      unfold Iter_Step. repeat TM_Correct.
      - eapply RealiseIn_WRealise. apply MatchNat_Sem.
    }
    {
      intros tin (yout, tout) H. cbn. TMSimp. destruct b.
      - intros m n s1 s2 (r1&r2&Hs1&Hs2&HEncM) HEncN. destruct H; TMSimp; TMSolve 1.
        specialize (H _ _ _ HEncM) as (m'&->&H). eexists. repeat split; eauto.
        hnf. do 2 eexists. do 2 (split; [ shelve | ]). eauto. Unshelve. all: cbn; omega.
      - intros m n s1 s2 (r1&r2&Hs1&Hs2&HEncM) HEncN. destruct H; TMSimp; try congruence.
        specialize (H _ _ _ HEncM) as (->&H). split; auto.
        destruct_tapes. cbn in *. subst. f_equal; eauto.
    }
  Qed.


  Definition Iter_Loop_Rel : Rel (tapes bool^+ 2) (unit * tapes bool^+ 2) :=
    ignoreParam (
        fun tin tout =>
          forall m n s1 s2,
            tin [@Fin0] ≂{s1;s2} m ->
            tin [@Fin1] ≂ n ->
            tout[@Fin0] ≂{m+s1; s2} 0 /\
            tout[@Fin1] ≂ iter m n
      ).

  Lemma Iter_Loop_WRealise : Iter_Loop ⊫ Iter_Loop_Rel.
  Proof.
    eapply WRealise_monotone.
    { unfold Iter_Loop. repeat TM_Correct. apply Iter_Step_WRealise. }
    {
      intros tin ((), tout) (tmid&HStar&HLastStep).
      induction HStar as [ tin | tin tmid1 tmid2 HStar _ IH]; intros m n s1 s2 HEncM HEncN.
      - cbn in HLastStep. specialize (HLastStep _ _ _ _ HEncM HEncN) as (->&->). split; cbn; hnf; eauto.
      - repeat (spec_assert IH; eauto). cbn in HLastStep, IH, HStar. destruct HStar as (()&HStar). cbn in HStar.
        specialize (HStar _ _ _ _ HEncM HEncN). unfold finType_CS in *. destruct HStar as (m'&->&HS1&HS2).
        specialize (IH _ _ _ _ HS1 HS2) as (IH1&IH2).
        rewrite <- Nat.add_succ_comm in IH1.
        split; cbn in *; auto.
    }
  Qed.

  Lemma Iter_Loop_Computes : Iter_Loop ⊫ Computes2_Rel Fin0 Fin1 Fin1 _ _ _ iter.
  Proof.
    eapply WRealise_monotone. apply Iter_Loop_WRealise.
    intros tin ((), tout) H. intros m n HEncM HEncN. hnf in H.
    destruct HEncM as (r1 & r2 & HEncM % tape_encodes_l_encodes_size).
    now specialize (H _ _ _ _ HEncM HEncN) as (?&?).
  Qed.


  Definition Iter_Rel : Rel (tapes bool^+ 3) (unit * tapes bool^+ 3) :=
    ignoreParam (
        fun tin tout =>
          forall m n s2 s3,
            tin [@Fin0] ≂{0;s2} m ->
            tin [@Fin1] ≂ n ->
            isLeft tin[@Fin2] s3 ->
            tout[@Fin0] ≂{0;s2} m /\
            tout[@Fin1] ≂ iter m n /\
            isLeft tout[@Fin2] (max s3 (S (S m)))
      ).

  

  Lemma Iter_WRealise : Iter ⊫ Iter_Rel.
  Proof.
    Local Arguments Encode_Nat : simpl never.
    eapply WRealise_monotone.
    {
      unfold Iter. repeat TM_Correct.
      - apply CopyValue'_WRealise with (X := nat).
      - apply Iter_Loop_WRealise.
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


  (*
  (** Termination *)

  Variable M1_runtime : nat -> nat.
  Hypothesis M1_terminates : projT1 M1 ↓ (fun tin k => exists y, tin[@Fin.F1] ≂ y /\ M1_runtime y <= k).

  Lemma Iter_Step_Terminates :
    projT1 Iter_Step ↓ (fun tin i => exists m m' n r1 r2,
                            counterIs_rest tin[@Fin0] m m' r1 r2 /\
                            tin[@Fin1] ≂ n /\
                            match m' with
                            | O => 4
                            | S y' => 4 + M1_runtime n
                            end <= i).
  Proof.
    eapply TerminatesIn_monotone.
    {
      unfold Iter_Step. repeat TM_Correct. 
      - eapply RealiseIn_WRealise. apply CountDown_Sem.
      - eapply RealiseIn_terminatesIn. apply CountDown_Sem.
    }
    {
      intros tin i. intros (m&m'&n&r1&r2&HEncM&HEncN&Hi).
      destruct m' as [ | n''] eqn:En'.
      - exists 3, 0. repeat split.
        + omega.
        + cbn. omega.
        + intros tout b H. cbn in H. destruct b; cbn.
          * destruct H as (H1&H2). simpl_not_in. rewrite <- H2 in *. specialize (H1 _ _ _ _ HEncM) as (?&?&_). exfalso; congruence.
          * omega.
      - exists 3, (M1_runtime n). repeat split.
        + omega.
        + cbn. omega.
        + intros tout b H. cbn in H. destruct b; cbn.
          * destruct H as (H1&H2). simpl_not_in. rewrite <- H2 in *. specialize (H1 _ _ _ _ HEncM) as (?&?&?H); inv H. eauto.
          * omega.
    }
  Qed.
  
  Fixpoint Iter_steps (m n : nat) { struct m } : nat :=
    match m with
    | O => 4
    | S m' => 5 + M1_runtime n + Iter_steps m' (f n)
    end.

  Lemma Iter_steps_ge4 (m n : nat) :
    4 <= Iter_steps m n.
  Proof. destruct m; cbn; omega. Qed.


  Lemma Iter_steps_homogene (m n k : nat) :
    (forall x, M1_runtime x <= k) ->
    Iter_steps m n <= 4 + (5 + k) * m.
  Proof.
    revert n. induction m as [ | m' IH]; intros; cbn -[add mult] in *.
    - omega.
    - specialize (IH (f n) H). pose proof (H (f n)) as H1. pose proof (H n) as H2.
      rewrite !Nat.mul_succ_r.
      rewrite !Nat.mul_add_distr_r in *.
      rewrite !Nat.add_assoc in *.
      omega. (* Oh [omega], my dear [omega]! *)
  Qed.

  Lemma Iter_Terminates' :
    projT1 Iter ↓ (fun tin i => exists m m' n r1 r2, 
                       counterIs_rest tin[@Fin0] m m' r1 r2 /\
                       tin[@Fin1] ≂ n /\
                       Iter_steps m' n <= i).
  Proof.
    unfold Iter. repeat TM_Correct.
    { apply Iter_Step_WRealise. }
    { eapply Iter_Step_Terminates. }
    {
      intros tin i (m&m'&n&r1&r2&HEncM&HEncN&Hi).
      destruct m'.
      - eexists. repeat split.
        + do 5 eexists. repeat split; cbn; eauto.
        + intros b () tout H. cbn in H; destruct b; cbn in *; auto.
          exfalso. specialize (H _ _ _ _ _ HEncM HEncN) as (n''&?&?). congruence.
      - eexists. repeat split.
        + do 5 eexists. repeat split; cbn -[add mult]; eauto.
        + intros b () tout H. cbn -[add mult] in H; destruct b; cbn -[add mult] in *; auto.
          * specialize (H _ _ _ _ _ HEncM HEncN) as (n''&H1&H2&H3). inv H1.
            eexists. repeat split.
            -- do 5 eexists. repeat split; eauto.
            -- omega.
          * specialize (H _ _ _ _ _ HEncM HEncN) as (H1&H2). inv H1.
    }
  Qed.

  Lemma Iter_Terminates :
    projT1 Iter ↓ (fun tin k => exists x y, tin[@Fin0] ≂ x /\ tin[@Fin1] ≂ y /\ Iter_steps x y <= k).
  Proof.
    eapply TerminatesIn_monotone. eapply Iter_Terminates'. intros tin i (m&n&HEncM&HEncN&Hi).
    destruct HEncM as (r1&r2&HEncM % tape_encodes_l_natCounterIsM). do 5 eexists. repeat split; eauto; omega.
  Qed.


  Lemma Iter_Reset_Terminates' :
    projT1 Iter_Reset ↓ (fun tin i => exists m m' n r1 r2, 
                             counterIs_rest tin[@Fin0] m m' r1 r2 /\
                             tin[@Fin1] ≂ n /\
                             11 + Iter_steps m' n + 4 * m <= i).
  Proof.
    eapply TerminatesIn_monotone.
    - unfold Iter_Reset. repeat TM_Correct.
      + apply Iter_WRealise.
      + apply Iter_Terminates'.
      + apply Reset_Terminates.
    - intros tin i (m&m'&n&r1&r2&HEncM&HEncN&Hi).
      exists (Iter_steps m' n), (10 + 4 * m). repeat split.
      + rewrite <- Hi. clear_all. apply Nat.eq_le_incl. omega.
      + do 5 eexists. repeat split. eauto. eauto. omega.
      + intros tout () H. cbn -[plus mult]. hnf in H. specialize (H _ _ _ _ _ HEncM HEncN) as (H1&H2).
        destruct H1 as (k&->&H1&H1'). do 5 eexists. repeat split. eauto. eauto. omega.
  Qed.

  Lemma Iter_Reset_Terminates :
    projT1 Iter_Reset ↓ (fun tin i => exists m n, tin[@Fin.F1] ≂ m /\ tin[@Fin.FS Fin.F1] ≂ n /\ 11 + Iter_steps m n + 4 * m <= i).
  Proof.
    eapply TerminatesIn_monotone. eapply Iter_Reset_Terminates'. intros tin i (m&n&HEncM&HEncN&Hi).
    destruct HEncM as (r1&r2&HEncM % tape_encodes_l_natCounterIsM). do 5 eexists. repeat split; eauto; omega.
  Qed.

   *)

End Iter1.


