Require Import TM.Code.CodeTM TM.Code.MatchNat.
Require Import TM.Basic.Mono Basic.Nop Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.
Require Import TM.Code.Copy.

(* Require Import Lia. *)
(* Require Import Coq.Init.Nat. *)

(* This is good *)
Local Arguments finType_CS (X) {_ _}.


(** * Machines that compte natural functions *)

(* Don't simplify [skipn (S n) xs]; only, if the number and the lists are constructors *)
Local Arguments skipn { A } !n !l.


(*
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
*)


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
  Inject (CopyValue _) [|Fin1; Fin2|];; (* copy n to a *)
  Inject (CopyValue _) [|Fin0; Fin3|];; (* copy m to b *)
  Inject Add_Loop [|Fin2; Fin3|]. (* Main loop *)


(*
 * Finally, reset tape b.
 * For technical reasons, it is convienient to define the machine for this last step seperately,
 * because it makes prooving the termination easier.
 *)
Definition Add :=
  Add_Main;; (* Initialisation and main loop *)
  Inject (Reset _) [|Fin3|]. (* Reset b *)


(** ** Correctness of [Add] *)

Definition Add_Step_Rel : Rel (tapes (bool^+) 2) ((bool * unit) * tapes (bool^+) 2) :=
  fun tin '(yout, tout) =>
    forall a b,
      tin [@Fin0] ≃ a ->
      tin [@Fin1] ≃ b ->
      match b with
      | O =>
        tout[@Fin0] ≃ a /\
        tout[@Fin1] ≃ b /\
        yout = (false, tt)
      | S b' =>
        tout[@Fin0] ≃ S a /\
        tout[@Fin1] ≃ b' /\
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
    intros tin (yout, tout) H. cbn. intros a b HEncA HEncB. TMSimp.
    destruct H; TMSimp inv_pair; clear_trivial_eqs.
    - specialize (H _ HEncB). destruct b; TMSimp; try congruence. repeat split; auto.
    - specialize (H _ HEncB). destruct b; TMSimp; try congruence. split; auto.
  }
Qed.


Definition Add_Loop_Rel : Rel (tapes (bool^+) 2) (unit * tapes (bool^+) 2) :=
  ignoreParam (
      fun tin tout =>
        forall a b,
          tin [@Fin0] ≃ a ->
          tin [@Fin1] ≃ b ->
          tout[@Fin0] ≃ b + a /\
          tout[@Fin1] ≃ 0
    ).

Lemma Add_Loop_WRealise : Add_Loop ⊫ Add_Loop_Rel.
Proof.
  eapply WRealise_monotone.
  { unfold Add_Loop. repeat TM_Correct. eapply RealiseIn_WRealise. apply Add_Step_Sem. }
  {
    apply WhileInduction; intros; intros a b HEncA HEncB; cbn in *.
    - specialize (HLastStep _ _ HEncA HEncB). destruct b; TMSimp; inv_pair. auto.
    - specialize (HStar _ _ HEncA HEncB).
      destruct b; TMSimp; inv_pair.
      specialize (HLastStep _ _ H H0) as (IH1&IH2).
      rewrite <- Nat.add_succ_comm in IH1. cbn in *. auto.
  }
Qed.





(* Everything, but reset *)
Definition Add_Main_Rel : Rel (tapes (bool^+) 4) (unit * tapes (bool^+) 4) :=
  ignoreParam (
      fun tin tout =>
        forall m n,
          tin [@Fin0] ≃ m ->
          tin [@Fin1] ≃ n ->
          isRight tin[@Fin2] ->
          isRight tin[@Fin3] ->
          tout[@Fin0] ≃ m /\
          tout[@Fin1] ≃ n /\
          tout[@Fin2] ≃ m + n /\
          tout[@Fin3] ≃ 0
    ).


Lemma Add_Main_WRealise : Add_Main ⊫ Add_Main_Rel.
Proof.
  eapply WRealise_monotone.
  {
    unfold Add_Main. repeat TM_Correct.
    - apply CopyValue_WRealise with (X := nat).
    - apply CopyValue_WRealise with (X := nat).
    - apply Add_Loop_WRealise.
  }
  {
    intros tin ((), tout) H. cbn. intros m n HEncM HEncN HOut HInt.
    TMSimp.
    specialize (H _ HEncN HOut) as (H'&H).
    specialize (H0 _ HEncM HInt) as (H0'&H0).
    specialize (H1 _ _ H H0) as (H1&H1').
    repeat split; auto.
  }
Qed.


Lemma Add_Computes : Add ⊫ Computes2_Rel plus.
Proof.
  eapply WRealise_monotone.
  {
    unfold Add. repeat TM_Correct.
    - apply Add_Main_WRealise.
    - apply Reset_WRealise with (X := nat). (* Don't forget the type here! *)
  }
  {
    intros tin ((), tout) H. intros m n HEncM HEncN HOut HInt. TMSimp.
    specialize (HInt Fin0).
    specialize (H _ _ HEncM HEncN HOut HInt) as (H&H'&H''&H''').
    specialize (H0 _ H''').
    repeat split; eauto.
    intros. destruct_fin i. all: auto.
  }
Qed.


(** ** Termination of [Add] *)

(* TODO *)

(*

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


*)


(** * Multiplication *)


(*
 * Complete Machine:
 *
 * INP t0: m
 * INP t1: n  (for Add: INP t0)
 * OUT t2: c  (for Add: INP t1)
 * INT t3: c' (for Add: OUT t2)
 * INT t4:    (for Add: INT t3)
 * INT t5: m' (copy of m)
 *
 * Pseudocode:
 * c := 0
 * m' := m
 * while (m--) {
 *   ADD(n, c, c')
 *   c := c'
 *   reset c'
 * }
 * reset m'
 *)

(*
 * Step-Machine:
 * (Note that it only accesses the copy of m)
 *
 * t0: m' (counter)
 * t1: n  (for Add: INP t0)
 * t2: c  (for Add: INP t1)
 * t3: c' (for Add: OUT t2)
 * t4:    (for Add: INT t4)
 *
 * if (m'--) {
 *   Add(n, c, c')
 *   c := c
 *   reset c'
 *   continue
 * } else {
 *   break
 * }
 *)
Definition Mult_Step : { M : mTM _ 5 & states M -> bool * unit } :=
  If (Inject MatchNat [|Fin0|])
     (Return (
          Inject Add [|Fin1; Fin2; Fin3; Fin4|];; (* Add(n, c, c') *)
          Inject (Reset _) [|Fin2|];;
          Inject (CopyValue _) [|Fin3; Fin2|];; (* c := c' *)
          Inject (Reset _) [|Fin3|] (* Reset c' *)
        ) (true, tt)) (* continue *)
     (Nop _ _ (false, tt)). (* break *)


Definition Mult_Loop : { M : mTM _ 5 & states M -> unit } := WHILE Mult_Step.


(*
 * INP t0: m
 * INP t1: n  (for Mult_Loop: t1)
 * OUT t2: c  (for Mult_Loop: t2)
 * INT t3: c' (for Mult_Loop: t3)
 * INT t4:    (for Mult_Loop: t4)
 * INT t5: m' (for Mult_Loop: t0)
 *)
Definition Mult_Main : { M : mTM _ 6 & states M -> unit } :=
  Inject (CopyValue _) [|Fin0; Fin5|];; (* m' := m *)
  Inject (Constr_O) [|Fin2|];; (* c := 0 *)
  Inject Mult_Loop [|Fin5; Fin1; Fin2; Fin3; Fin4|]. (* Main loop *)


Definition Mult : { M : mTM _ 6 & states M -> unit } :=
  Mult_Main;;
  Inject (Reset _) [|Fin5|]. (* Reset m' *)


(** ** Correctness of [Mult] *)

Definition Mult_Step_Rel : Rel (tapes (bool^+) 5) ((bool * unit) * tapes (bool^+) 5) :=
  fun tin '(yout, tout) =>
    forall c m' n,
      tin[@Fin0] ≃ m' ->
      tin[@Fin1] ≃ n ->
      tin[@Fin2] ≃ c ->
      isRight tin[@Fin3] ->
      isRight tin[@Fin4] ->
      match m' with
      | O =>
        tout[@Fin0] ≃ m' /\
        tout[@Fin1] ≃ n /\
        tout[@Fin2] ≃ c /\
        isRight tout[@Fin3] /\
        isRight tout[@Fin4] /\
        yout = (false, tt) (* return *)
      | S m'' =>
        tout[@Fin0] ≃ m'' /\
        tout[@Fin1] ≃ n /\
        tout[@Fin2] ≃ n + c /\
        isRight tout[@Fin3] /\
        isRight tout[@Fin4] /\
        yout = (true, tt) (* contine *)
      end.

Lemma Mult_Step_WRealise : Mult_Step ⊫ Mult_Step_Rel.
Proof.
  eapply WRealise_monotone.
  {
    unfold Mult_Step. repeat TM_Correct.
    - eapply RealiseIn_WRealise. apply MatchNat_Sem.
    - apply Add_Computes.
    - apply Reset_WRealise with (X := nat).
    - apply CopyValue_WRealise with (X := nat).
    - apply Reset_WRealise with (X := nat).
  }
  {
    intros tin (yout, tout) H. intros c m' n HEncM' HEncN HEncC HInt3 HInt4. TMSimp.
    destruct H; TMSimp.
    - specialize (H _ HEncM').
      destruct m' as [ | m']; TMSimp; inv_pair; try congruence.
      specialize (H1 _ _ HEncN HEncC HInt3).
      spec_assert H1 as (HComp1&HComp2&HComp3&HComp4).
      { intros i; destruct_fin i; cbn; assumption. }
      specialize (HComp4 Fin0); cbn in HComp4.
      specialize (H2 _ HComp2).
      specialize (H3 _ HComp3 H2) as (H7&H7').
      repeat split; eauto.
    - specialize (H _ HEncM').
      destruct m' as [ | m']; TMSimp; inv_pair; try congruence.
      split; auto.
  }
Qed.

Definition Mult_Loop_Rel : Rel (tapes (bool^+) 5) (unit * tapes (bool^+) 5) :=
  ignoreParam (
      fun tin tout =>
        forall c m' n,
          tin[@Fin0] ≃ m' ->
          tin[@Fin1] ≃ n ->
          tin[@Fin2] ≃ c ->
          isRight tin[@Fin3] ->
          isRight tin[@Fin4] ->
          tout[@Fin0] ≃ 0 /\
          tout[@Fin1] ≃ n /\
          tout[@Fin2] ≃ m' * n + c /\
          isRight tout[@Fin3] /\
          isRight tout[@Fin4]
    ).


Lemma Mult_Loop_WRealise :
  Mult_Loop ⊫ Mult_Loop_Rel.
Proof.
  eapply WRealise_monotone.
  {
    unfold Mult_Loop. repeat TM_Correct. eapply Mult_Step_WRealise.
  }
  {
    eapply WhileInduction; intros; intros c m' n HEncM' HEncN HEncC HInt3 HInt4; TMSimp.
    - specialize (HLastStep _ _ _ HEncM' HEncN HEncC HInt3 HInt4).
      destruct m' as [ | m']; TMSimp; inv_pair; try congruence. auto.
    - specialize (HStar _ _ _ HEncM' HEncN HEncC HInt3 HInt4).
      destruct m' as [ | m']; TMSimp; inv_pair; try congruence.
      specialize (HLastStep _ _ _ ltac:(eauto) ltac:(eauto) ltac:(eauto) ltac:(eauto) ltac:(eauto)) as (HL1&HL2&HL3&HL4&HL).
      rewrite Nat.add_assoc in HL3. replace (n + m' * n + c) with (m' * n + n + c) by omega.
      repeat split; auto.
  }
Qed.

(*
 * Complete Machine:
 *
 * INP t0: m
 * INP t1: n  (from Add: INP t0)
 * OUT t2: c  (from Add: INP t1)
 * INT t3: c' (from Add: OUT t2)
 * INT t4:    (from Add: INT t3)
 * INT t5: m' (copy of m)
 *
 * Pseudocode:
 * c := 0
 * m' := m
 * while (m--) {
 *   ADD(n, c, c')
 *   c := c'
 *   reset c'
 * }
 * reset m'
 *)

Definition Mult_Main_Rel : Rel (tapes (bool^+) 6) (unit * tapes (bool^+) 6) :=
  ignoreParam (
      fun tin tout =>
        forall m n,
          tin[@Fin0] ≃ m ->
          tin[@Fin1] ≃ n ->
          isRight tin[@Fin2] ->
          isRight tin[@Fin3] ->
          isRight tin[@Fin4] ->
          isRight tin[@Fin5] ->
          tout[@Fin0] ≃ m /\
          tout[@Fin1] ≃ n /\
          tout[@Fin2] ≃ m * n /\
          isRight tout[@Fin3] /\
          isRight tout[@Fin4] /\
          tout[@Fin5] ≃ 0
    ).

Lemma Mult_Main_WRealise :
  Mult_Main ⊫ Mult_Main_Rel.
Proof.
  eapply WRealise_monotone.
  {
    unfold Mult_Main. repeat TM_Correct.
    - apply CopyValue_WRealise with (X := nat).
    - eapply RealiseIn_WRealise. apply Constr_O_Sem.
    - apply Mult_Loop_WRealise.
  }
  {
    intros tin ((), tout) H. intros m n HEncM HEncN Hout HInt3 HInt4 HInt5.
    TMSimp.
    specialize (H _ HEncM HInt5) as (H&H').
    specialize (H0 Hout).
    specialize H1 with (1 := H') (2 := HEncN) (3 := H0) (4 := HInt3) (5 := HInt4) as (H1&H2&H3&H4&H5).
    rewrite Nat.add_0_r in H3.
    repeat split; eauto.
  }
Qed.


Lemma Mult_Computes :
  Mult ⊫ Computes2_Rel mult.
Proof.
  eapply WRealise_monotone.
  {
    unfold Mult. repeat TM_Correct.
    - eapply Mult_Main_WRealise.
    - eapply Reset_WRealise with (X := nat).
  }
  {
    intros tin ((), tout) H. cbn. intros m n HEncM HEncN HOut HInt. TMSimp.
    specialize (HInt Fin0) as HInt3; specialize (HInt Fin1) as HInt4; specialize (HInt Fin2) as HInt5. clear HInt.
    specialize (H _ _ HEncM HEncN HOut HInt3 HInt4 HInt5) as (HComp1&HComp2&HComp3&HComp4&HComp5&HComp6).
    specialize (H0 _ HComp6).
    repeat split; auto.
    intros i. destruct_fin i; TMSimp; auto.
  }
Qed.


(*
(* TODO *)

(** ** Termination of Mult *)

Print Mult_Step.

Check CopyValue'_Terminates.

Definition Mult_Step_steps m' n c :=
  match m' with
  | O => 6
  | _ => 190 + 62 * n + 36 * c
  end.

Lemma Mult_Step_Terminates :
  projT1 Mult_Step ↓
         (fun tin k => exists m' n c,
              tin[@Fin0] ≂ m' /\
              tin[@Fin1] ≂ n /\
              tin[@Fin2] ≂ c /\
              isLeft tin[@Fin3] /\
              isLeft tin[@Fin4] /\
              Mult_Step_steps m' n c <= k).
Proof.
  Local Arguments add : simpl never. Local Arguments mult : simpl never.
  eapply TerminatesIn_monotone.
  {
    unfold Mult_Step. repeat TM_Correct.
    - eapply RealiseIn_WRealise. apply MatchNat_Sem.
    - eapply RealiseIn_terminatesIn. apply MatchNat_Sem.
    - apply Add_Computes.
    - apply Add_Terminates.
    - apply CopyValue'_WRealise with (X := nat).
    - apply CopyValue'_Terminates with (X := nat).
    - apply MoveToLeft_Terminates with (X := nat).
  }
  {
    intros tin k. intros (m'&n&c&HEncM'&HEncN&HEncC&HInt3&HInt4&Hk).
    pose proof HEncM' as (r11&r12&HEncM'').
    destruct m' as [ | m']; cbn.
    - exists 5, 0. cbn in *; repeat split.
      + omega.
      + omega.
      + intros tmid y (HComp&HInj). TMSimp.
        rewrite <- HInj0, <- HInj1, <- HInj2, <- HInj3 in *. clear HInj0 HInj1 HInj2 HInj3.
        specialize (HComp _ _ _ HEncM''). cbn in *. destruct HComp as (HComp&->). omega.
    - exists 5, (184 + 62 * n + 36 * c); cbn in *; repeat split.
      + omega.
      + omega.
      + intros tmid y (HComp&HInj). TMSimp.
        rewrite <- HInj0, <- HInj1, <- HInj2, <- HInj3 in *. clear HInj0 HInj1 HInj2 HInj3.
        specialize (HComp _ _ _ HEncM''). cbn in *. destruct HComp as (HComp&->).
        exists (120 + 42 * n + 16 * c), (63 + 20 * n + 20 * c); cbn in *; repeat split.
        * omega.
        * do 2 eexists. repeat split; eauto.
          -- intros i; destruct_fin i; cbn. eauto.
          -- unfold Add_steps. omega.
        * intros tmid0 () (HComp2&HInj). TMSimp. rewrite <- HInj0 in *. clear HInj0.
          specialize (HComp2 _ _ ltac:(eauto) ltac:(eauto)).
          spec_assert HComp2 as (HComp1&HComp2&HComp3&HComp4).
          { intros i; destruct_fin i; cbn; eauto. }
          specialize (HComp4 Fin0). cbn in HComp4.
          pose proof HComp3 as (r21&r22&HComp3').
          exists (44 + 16 * n + 16 * c), (18 + 4 * n + 4 * c). repeat split.
          -- omega.
          -- eexists. repeat split; eauto. rewrite nat_encode_length. omega.
          -- intros tmid1 () (HComp5&HInj). TMSimp. clear HInj0 HInj1 HInj2.
             specialize HComp5 with (1 := HComp3') as (->&HComp5).
             do 3 eexists. split. eauto. rewrite nat_encode_length.
             rewrite Nat.mul_add_distr_l, Nat.mul_succ_r, Nat.mul_add_distr_l, !Nat.add_assoc.
             enough (| r21 | <= 0) by omega.
             (* Problemma *)
             admit.
  }
Admitted.

*)