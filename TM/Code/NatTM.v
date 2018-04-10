Require Import TM.Code.CodeTM TM.Code.MatchNat.
Require Import TM.Basic.Mono Basic.Nop Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.
Require Import TM.Code.Copy.

Require Import Lia.


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
 * Step machine
 *
 * if (b--) {
 *   a++;
 *   continue;
 * } else {
 *   break;
 * }
 *
 * Tapes:
 * t0: a
 * t1: b
 *)
Definition Add_Step : { M : mTM _ 2 & states M -> bool * unit } :=
  If (Inject MatchNat [|Fin1|])
     (Return (Inject Constr_S [|Fin0|]) (true, tt))
     (Nop _ _ (false, tt)).


Definition Add_Loop : { M : mTM _ 2 & states M -> unit } := WHILE Add_Step.

(*
 * Full machine in pseudocode:
 * a := n
 * b := m
 * while (b--) { // Loop
 *   a++;
 * }
 * return a;
 *
 * Tapes:
 * INP t0: m
 * INP t1: n
 * OUT t2: a
 * INT t3: b
 *)
(* Everything, but not reset *)
Definition Add_Main : { M : mTM (bool^+) 4 & states M -> unit } :=
  Inject (CopyValue' _) [|Fin1; Fin2|];; (* copy n to a *)
  Inject (CopyValue' _) [|Fin0; Fin3|];; (* copy m to b *)
  Inject Add_Loop [|Fin2; Fin3|]. (* Main loop *)


(*
 * Finally, reset tape b.
 * For technical reasons, it is convienient to define the machine for this last step seperately,
 * because it makes prooving the termination easier.
 *)
Definition Add :=
  Add_Main;; (* Initialisation and main loop *)
  Inject (MoveToLeft _) [|Fin3|]. (* Reset b *)


(** Correctness *)


Definition Add_Step_Rel : Rel (tapes (bool^+) 2) ((bool * unit) * tapes (bool^+) 2) :=
  fun tin '(yout, tout) =>
    forall a b s1 s2,
      tin [@Fin0] ≂ a ->
      tin [@Fin1] ≂{s1;s2} b ->
      match b with
      | O =>
        tout = tin /\
        yout = (false, tt)
      | S b' =>
        tout[@Fin0] ≂ S a /\
        tout[@Fin1] ≂{S s1; s2} b' /\
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
    intros tin (yout, tout) H. cbn. intros a b s1 s2 HEncA HEncB. TMSimp.
    destruct HEncB as (r1&r2&Hs1&Hs2&HEncB).
    destruct H; TMSimp inv_pair; clear_trivial_eqs.
    - specialize (H _ _ _ HEncB). destruct b; TMSimp; try congruence. repeat split; auto.
      do 2 eexists. split. shelve. split. shelve. eauto. Unshelve. all: cbn; omega.
    - specialize (H _ _ _ HEncB). destruct b; TMSimp; try congruence. split; auto.
      pose proof tape_encodes_l_injective H HEncB. destruct_tapes. cbn in *. subst. f_equal; eauto.
  }
Qed.


Definition Add_Loop_Rel : Rel (tapes bool^+ 2) (unit * tapes bool^+ 2) :=
  ignoreParam (
      fun tin tout =>
        forall a b s1 s2,
          tin [@Fin0] ≂ a ->
          tin [@Fin1] ≂{s1;s2} b ->
          tout[@Fin0] ≂ b + a /\
          tout[@Fin1] ≂{b+s1; s2} 0
    ).

Lemma Add_Loop_WRealise : Add_Loop ⊫ Add_Loop_Rel.
Proof.
  eapply WRealise_monotone.
  { unfold Add_Loop. repeat TM_Correct. eapply RealiseIn_WRealise. apply Add_Step_Sem. }
  {
    apply WhileInduction; intros; intros a b s1 s2 HEncA HEncB; cbn in *.
    - specialize (HLastStep _ _ _ _ HEncA HEncB). destruct b; TMSimp; inv_pair. auto.
    - specialize (HStar _ _ _ _ HEncA HEncB).
      destruct b; TMSimp; inv_pair.
      specialize (HLastStep _ _ _ _ H H0) as (IH1&IH2).
      rewrite <- Nat.add_succ_comm in IH1, IH2. cbn in *. auto.
  }
Qed.


(* TODO: This is good: *)
Global Arguments finType_CS (X) {_ _}.



(* Everything, but reset *)
Definition Add_Main_Rel : Rel (tapes bool^+ 4) (unit * tapes bool^+ 4) :=
  ignoreParam (
      fun tin tout =>
        forall m n s,
          tin [@Fin0] ≂ m ->
          tin [@Fin1] ≂ n ->
          isLeft_size (tin[@Fin3]) s ->
          tout[@Fin0] ≂ m /\
          tout[@Fin1] ≂ n /\
          tout[@Fin2] ≂ m + n /\
          tout[@Fin3] ≂{m; S (S s)} 0
    ).



Lemma Add_Main_WRealise : Add_Main ⊫ Add_Main_Rel.
Proof.
  Local Arguments Encode_Nat : simpl never.
  eapply WRealise_monotone.
  {
    unfold Add_Main. repeat TM_Correct.
    - apply CopyValue'_WRealise with (X := nat).
    - apply CopyValue'_WRealise with (X := nat).
    - apply Add_Loop_WRealise.
  }
  {
    intros tin ((), tout) H. cbn. intros m n s HEncM HEncN HInt.
    pose proof HEncM as (r1&r2&HEncM'). pose proof HEncN as (r3&r4&HEncN').
    pose proof tape_encodes_l_encodes_size HEncM' as HEncM''.
    pose proof tape_encodes_l_encodes_size HEncN' as HEncN''.

    TMSimp.
    specialize (H _ _ _ HEncN') as (H'&H). rewrite <- H' in *. clear H'.
    specialize (H0 _ _ _ HEncM') as (H0'&H0). rewrite <- H0' in *. clear H0'. TMSimp.
    apply tape_encodes_l_encodes in H; apply tape_encodes_l_encodes_size in H0.
    specialize (H1 _ _ _ _ H H0) as (H1&H1').
    repeat split; auto.

    eapply tape_encodes_size_monotone; eauto.
    - erewrite isLeft_size_left; eauto. cbn. omega.
    - rewrite skipn_length. rewrite nat_encode_length.
      (* Search (?a - ?b <= ?c - ?b). *)
      transitivity (s - S (S m)); [ | omega].
      apply Nat.sub_le_mono_r.
      now apply isLeft_size_right.
  }
Qed.

(* TODO: Put this in Base *)
Lemma fin_destruct_S (n : nat) (i : Fin.t (S n)) :
  { i' | i = Fin.FS i' } + { i = Fin0 }.
Proof.
  refine (match i in (Fin.t n')
          with
          | Fin.F1 => _
          | Fin.FS i' => _
          end); eauto.
  (*
  refine (match i as i0 in (Fin.t n') return
                match n' with
                | O => fun _ : Fin.t 0 => unit
                | S n'' => fun i0 : Fin.t (S n'') => { i' | i0 = Fin.FS i' } + { i0 = Fin0}
                end i0
          with
          | Fin.F1 => _
          | Fin.FS i' => _
          end); eauto.
   *)
Defined.

Lemma fin_destruct_O (i : Fin.t 0) : Empty_set.
Proof. refine (match i with end). Defined.

Ltac destruct_fin i :=
  match type of i with
  | Fin.t (S ?n) =>
    let i' := fresh i in
    pose proof fin_destruct_S i as [ (i'&->) | -> ];
    [ destruct_fin i'
    | idtac]
  | Fin.t O =>
    pose proof fin_destruct_O i as []
  end.

Goal True.
  assert (i : Fin.t 4) by repeat constructor.
  enough (i = i) by tauto.
  destruct_fin i.
  all: reflexivity.
Abort.



Lemma Add_Computes : Add ⊫ Computes2_Rel add.
Proof.
  eapply WRealise_monotone.
  {
    unfold Add. repeat TM_Correct.
    - apply Add_Main_WRealise.
    - apply MoveToLeft_WRealise' with (X := nat). (* Don't forget the type here! *)
  }
  {
    intros tin ((), tout) H. intros m n HEncM HEncN HInt. TMSimp. clear H2 H3 H4. 
    specialize (HInt Fin0); apply isLeft_isLeft_size in HInt.
    specialize (H _ _ _ HEncM HEncN HInt) as (H1&H2&H3&H4).
    destruct H4 as (r1&r2&Hr1&Hr2&H4).
    repeat split; eauto. intros i; destruct_fin i.
    eauto using tape_encodes_l_encodes.
  }
Qed.


(** Termination *)


Definition Add_Loop_steps b := 11 + 12 * b.

Lemma Add_Loop_Terminates :
  projT1 Add_Loop ↓
         (fun tin i => exists a b,
              tin[@Fin0] ≂ a /\
              tin[@Fin1] ≂ b /\
              Add_Loop_steps b <= i).
Proof.
  unfold Add_Loop, Add_Loop_steps. repeat TM_Correct.
  { eapply RealiseIn_WRealise. apply Add_Step_Sem. }
  { eapply RealiseIn_terminatesIn. apply Add_Step_Sem. }
  {
    intros tin i (a&b&HEncA&HEncB&Hi).
    destruct HEncB as (r1 & r2 & HEncB % tape_encodes_l_encodes_size).
    destruct b.
    - exists 11. repeat split.
      + omega.
      + intros y () tmid H. cbn in H. specialize (H _ _ _ _ HEncA HEncB). cbn in *.
        destruct H; TMSimp; inv_pair. omega.
    - exists 11. repeat split.
      + omega.
      + intros y () tmid H. cbn in H. specialize (H _ _ _ _ HEncA HEncB). cbn -[plus mult] in *.
        destruct H as (H1&H2&H3). inv H3.
        exists (11 + b * 12). repeat split.
        * do 2 eexists. repeat split. eauto. eapply tape_encodes_size_encodes; eauto. omega.
        * omega.
  }
Qed.


Definition Add_Main_steps m n := 101 + 16 * n + 38 * m.

Lemma Add_Main_Terminates :
  projT1 Add_Main ↓ Computes2_T Add_Main_steps.
Proof.
  Arguments add : simpl never. Arguments mult : simpl never.
  unfold Add_Main, Add_Main_steps. eapply TerminatesIn_monotone.
  {
    repeat TM_Correct.
    - apply CopyValue'_WRealise with (X := nat).
    - apply CopyValue'_Terminates with (X := nat).
    - apply CopyValue'_WRealise with (X := nat).
    - apply CopyValue'_Terminates with (X := nat).
    - apply Add_Loop_Terminates.
  }
  {
    intros tin k (m&n&HEncM&HEncN&HInt&Hk).
    pose proof HEncN as (r11&r12&HEncN').
    pose proof HEncM as (r21&r22&HEncM').
    exists (44 + 16 * n), (56 + 28 * m). repeat split.
    - rewrite <- Hk. omega.
    - cbn -[add mult]. exists n. rewrite nat_encode_length. split; auto. omega.
    - intros tmid ymid. intros (H1&H2). TMSimp.
      specialize (H1 _ _ _ HEncN'). TMSimp.
      specialize (HInt Fin0).
      exists (44 + 16 * m), (Add_Loop_steps m). repeat split.
      + unfold Add_Loop_steps. omega.
      + exists m. split. eauto. rewrite nat_encode_length. omega.
      + intros tmid2 () (HComp & HInj). TMSimp.
        specialize (HComp _ _ _ HEncM') as (HComp&HComp').
        do 2 eexists; repeat split; eauto; do 2 eexists; eassumption.
  }
Qed.


Definition Add_steps m n := 120 + 16 * n + 42 * m.

Lemma Add_Terminates :
  projT1 Add ↓ Computes2_T Add_steps.
Proof.
  Arguments add : simpl never. Arguments mult : simpl never.
  unfold Add, Add_steps. eapply TerminatesIn_monotone.
  {
    repeat TM_Correct.
    - apply Add_Main_WRealise.
    - apply Add_Main_Terminates.
    - apply MoveToLeft_Terminates.
  }
  {
    intros tin k (m&n&HEncM&HEncN&HInt&Hk).
    pose proof HEncM as (r11&r12&HEncM'); pose proof HEncN as (r21&r22&HEncN').
    exists (Add_Main_steps m n), (18 + 4 * m). repeat split.
    - unfold Add_Main_steps. omega.
    - cbn. exists m, n. repeat split; eauto.
    - intros tmid () HComp. cbn in *.
      specialize (HInt Fin0). apply isLeft_isLeft_size in HInt.
      specialize (HComp _ _ _ HEncM HEncN HInt) as (HComp1&HComp2&HComp3&HComp4).
      destruct HComp4 as (r31&r32&Hr31&_&HComp4).
      do 3 eexists. split; eauto. rewrite nat_encode_length.
      transitivity (14 + 4 * (m + 1)).
      + apply Nat.add_le_mono. omega. apply Nat.mul_le_mono. omega. apply Nat.add_le_mono. assumption. omega.
      + omega.
  }
Qed.


(*
(* TODO *)

(** * Multiplication *)

(*
 * t0: m  (counter for mult)
 * t1: n  (m for add) (stays left)
 * t2: a  (n for add) (stays left)
 * t3: n' (copy of m for add) (stays left)
 *)

Definition Mult_Step : { M : mTM _ 4 & states M -> bool * unit } :=
  If (Inject MatchNat (app_tapes 1 3))
     (Return (Inject Add (add_tapes 3 1)) (true, tt))
     (Nop _ _ (false, tt)).


Definition Mult_Loop : { M : mTM _ 4 & states M -> unit } := WHILE Mult_Step.

Definition Mult : { M : mTM _ 4 & states M -> unit } :=
  Inject (InitTape _ 0) [|Fin2|];; (* Initialise the accu to 0 *)
  Mult_Loop. (* Main loop *)


(** Correctness *)

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
      pose proof (H2 Fin1 ltac:(vector_not_in)) as L1. TMSimp. clear L1.
      pose proof (H2 Fin2 ltac:(vector_not_in)) as L1. TMSimp. clear L1.
      pose proof (H2 Fin3 ltac:(vector_not_in)) as L1. TMSimp. clear L1.
      specialize (H3 Fin0 ltac:(vector_not_in)). TMSimp.

      (* Computation applications *)
      specialize (H _ _ _ ltac:(eauto)). destruct m; TMSimp; try congruence.
      specialize (H1 _ _ _ _ ltac:(eauto) ltac:(eauto) ltac:(eauto)) as (HC1&HC2&HC3).

      repeat split.
      + hnf. do 2 eexists. unshelve (do 2 (split; [ shelve | eauto])). cbn. omega.
      + assumption.
      + assumption.
      + assumption.

    - (* Condition of if evaluated to [false] *)

      (* Lift-N rewritings *)
      pose proof (H1 Fin1 ltac:(vector_not_in)) as L1. TMSimp.
      pose proof (H1 Fin2 ltac:(vector_not_in)) as L2. TMSimp.
      pose proof (H1 Fin3 ltac:(vector_not_in)) as L3. TMSimp.

      (* Computation applications *)
      specialize (H _ _ _ ltac:(eauto)). destruct m; TMSimp; try congruence.

      destruct_tapes; cbn in *. split; auto.
      repeat f_equal; try congruence. eapply tape_encodes_l_injective; eauto.
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


(* We initialised [a] to [0] now, so the output on tape [t2] is [m*n] *)
Definition Mult_Rel : Rel (tapes (bool^+) 4) (unit * tapes (bool^+) 4) :=
  ignoreParam (
      fun tin tout =>
        forall (m n s0 s0' s1 s3 : nat),
          tin [@Fin0] ≂{s0;s0'} m ->
          tin [@Fin1] ≂{0;s1} n ->
          isLeft tin[@Fin3] s3 ->
          tout[@Fin0] ≂{m + s0; s0'} 0 /\ (* m is decremented to 0 *)
          tout[@Fin1] ≂{0;s1} n /\ (* n stays unchanged *)
          tout[@Fin2] ≂ m * n /\ (* a the output of the computation [m+n] *)
          isLeft tout[@Fin3] (max s3 (S (S n))) (* n' stays left and has not allocated more memory than needed to hold n *)
    ).

Lemma Mult_WRealsie : Mult ⊫ Mult_Rel.
Proof.
  eapply WRealise_monotone.
  {
    unfold Mult. repeat TM_Correct.
    - eapply RealiseIn_WRealise. apply InitTape_Sem.
    - apply Mult_Loop_WRealise.
  }
  {
    intros tin ((), tout) H. intros m n s0 s0' s1 s3 HEncM HEncN HEncN'. TMSimp.
    (* Lift-N rewriting *)
    pose proof (H1 Fin0 ltac:(vector_not_in)) as L1. TMSimp. clear L1.
    pose proof (H1 Fin1 ltac:(vector_not_in)) as L1. TMSimp. clear L1.
    pose proof (H1 Fin3 ltac:(vector_not_in)) as L1. TMSimp. clear L1. clear H1.
    (* Apply computations *)
    specialize (H0 _ _ _ _ _ _ _ ltac:(eauto) ltac:(eauto) ltac:(eauto) ltac:(eauto)) as (H1&H2&H3&H4).
    now rewrite Nat.add_0_r in H3.
  }
Qed.


(** Termination of Mult *)

(*
 * t0: m  (counter for mult) (stays left)
 * t1: n  (m for add) (stays left)
 * t2: a  (n for add) (stays left)
 * t3: n' (copy of m for add) (stays left)
 *)

(*
Definition Mult_Step : { M : mTM _ 4 & states M -> bool * unit } :=
  If (Inject MatchNat [|Fin0|])
     (Return (Inject Add (add_tapes 3 1)) (true, tt))
     (Nop _ _ (false, tt)).
*)
Check Add_Terminates.

Print Add_steps.

Definition Mult_Step_steps n := 145 + 52 * n. (* 5 additional steps for [MatchNat] and 1 additional step for [If] *)

Lemma Mult_Step_Terminates :
  projT1 Mult_Step ↓
         (fun tin i =>
            exists (m n a s1' s3 : nat),
              tin[@Fin0] ≂ m /\
              tin[@Fin1] ≂{0;s1'} n /\
              tin[@Fin2] ≂ a /\
              isLeft tin[@Fin3] s3 /\
              match m with
              | 0 => 6 <= i
              | _ => 6 + Mult_Step_steps n <= i
              end).
Proof.
  eapply TerminatesIn_monotone.
  {
    unfold Mult_Step. repeat TM_Correct.
    - eapply RealiseIn_WRealise. apply MatchNat_Sem.
    - eapply RealiseIn_terminatesIn. apply MatchNat_Sem.
    - apply Add_Terminates.
  }
  {
    intros tin i (m&n&a&s1'&s3&HEncM&HEncN&HEncA&HEncN'&Hi).
    destruct m as [ | m' ].
    {
      exists 5, 0. repeat split.
      - omega.
      - cbn. omega.
      - intros tmid b (HComp & HInject). cbn -[app_tapes] in HComp, HInject.
        destruct HEncM as (r1&r2&HEncM). cbn -[add mult] in *.
        specialize (HComp _ _ _ ltac:(eauto)). cbn in HComp. destruct HComp as (HComp&->).
        omega.
    }
    {
      exists 5, (Mult_Step_steps n). repeat split.
      - omega.
      - cbn. omega.
      - intros tmid b (HComp & HInject). cbn -[app_tapes] in HComp, HInject.
        destruct HEncM as (r1&r2&HEncM). cbn -[add mult] in *.
        cbn in tmid.
        pose proof (HInject Fin1 ltac:(vector_not_in)) as L1. rewrite L1 in *. clear L1.
        pose proof (HInject Fin2 ltac:(vector_not_in)) as L1. rewrite L1 in *. clear L1.
        pose proof (HInject Fin3 ltac:(vector_not_in)) as L1. rewrite L1 in *. clear L1.
        specialize (HComp _ _ _ ltac:(eauto)). cbn in HComp. destruct HComp as (HComp&->).
        do 4 eexists. repeat split.
        + eauto.
        + eauto.
        + eauto.
        + unfold Add_steps, Mult_Step_steps. omega.
    }
  }
Qed.


Definition Mult_Loop_steps m n := 6 + m * (152 + 52 * n).

Lemma Mult_Loop_Terminates :
  projT1 Mult_Loop ↓
         (fun tin i => exists a m n s1' s3,
              tin[@Fin0] ≂ m /\
              tin[@Fin1] ≂{0;s1'} n /\
              tin[@Fin2] ≂ a /\
              isLeft tin[@Fin3] s3 /\
              Mult_Loop_steps m n <= i).
Proof.
  unfold Mult_Loop, Mult_Loop_steps. repeat TM_Correct.
  { apply Mult_Step_WRealise. }
  { apply Mult_Step_Terminates. }
  {
    intros tin i (a & m & n & s1' & s3 & HEncM & HEncN & HEncA & HEncN' & Hi).
    pose proof HEncM as (r1 & r2 & HEncM' % tape_encodes_l_encodes_size).
    destruct m as [ | m'] eqn:Em; cbn -[add mult] in *.
    - exists 6. repeat split.
      + do 5 eexists. repeat split; eauto. cbn -[add mult]. omega.
      + intros b () tmid. intros H.
        specialize H with (1 := HEncM') (2 := HEncN) (3 := HEncA) (4 := HEncN'). cbn -[add mult] in *.
        destruct H as (->&?); inv_pair. omega.
    - exists (6 + Mult_Step_steps n). repeat split.
      + do 5 eexists. repeat split; eauto. cbn -[add mult]. unfold Mult_Step_steps, Mult_Loop_steps. omega.
      + intros b () tmid. intros H.
        specialize H with (1 := HEncM') (2 := HEncN) (3 := HEncA) (4 := HEncN'). cbn -[add mult] in *.
        destruct H as (H1&H2&H3&H4&H5); inv_pair.
        eexists (Mult_Loop_steps m' n). repeat split.
        * do 5 eexists. repeat split.
          -- eapply tape_encodes_size_encodes; eauto.
          -- eassumption.
          -- eassumption.
          -- eapply isLeft_monotone; eauto.
          -- unfold Mult_Step_steps. constructor.
        * unfold Mult_Step_steps, Mult_Loop_steps.
          rewrite <- Hi. clear_all. rewrite !Nat.mul_succ_l. omega. (* oh [omega] -- you come to your limits *)
  }
Qed.


(*
 * Mult writes [0] to tape [a] and executes the loop after that.
 * The runtime of [InitTape 0] is [12 + 4 * |encode 0| = 12 + 4 * 1 = 16
 *)

Definition Mult_steps m n := 24 + m * (152 + 52 * n).


Lemma Mult_Terminates :
  projT1 Mult ↓
         (fun tin i => exists m n s1' s3,
              tin[@Fin0] ≂ m /\
              tin[@Fin1] ≂{0;s1'} n /\
              isLeft tin[@Fin3] s3 /\
              Mult_steps m n <= i).
Proof.
  eapply TerminatesIn_monotone.
  {
    unfold Mult. repeat TM_Correct.
    - eapply RealiseIn_WRealise. apply InitTape_Sem.
    - eapply RealiseIn_terminatesIn. apply InitTape_Sem.
    - apply Mult_Loop_Terminates.
  }
  {
    intros tin i (m & n & s1' & s3 & HEncM & HEncN & HEncN' & Hi).
    exists 16, (Mult_Loop_steps m n). cbn -[add mult]. repeat split.
    - rewrite <- Hi. unfold Mult_Loop_steps, Mult_steps. omega.
    - rewrite nat_encode_length. omega.
    - intros tmid () (HEncA' & HInj).
      pose proof (HInj Fin0 ltac:(vector_not_in)) as L1. rewrite <- !L1 in *. clear L1.
      pose proof (HInj Fin1 ltac:(vector_not_in)) as L1. rewrite <- !L1 in *. clear L1.
      pose proof (HInj Fin3 ltac:(vector_not_in)) as L1. rewrite <- !L1 in *. clear L1. clear HInj.
      eauto 10.
  }
Qed.

*)