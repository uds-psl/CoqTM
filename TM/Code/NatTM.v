Require Import TM.Code.ProgrammingTools.
Require Import TM.Code.MatchNat.


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
Definition Add_Step : { M : mTM _ 2 & states M -> option unit } :=
  If (LiftTapes MatchNat [|Fin1|])
     (Return (LiftTapes Constr_S [|Fin0|]) None)
     (Return Nop (Some tt)).


Definition Add_Loop : { M : mTM _ 2 & states M -> unit } := WHILE Add_Step.

(*
 * Full machine in pseudocode:
 * a := n
 * b := m
 * while (b--) { // Loop
 *   a++;
 * }
 * reset b;
 * return a;
 *
 * Tapes:
 * INP t0: m
 * INP t1: n
 * OUT t2: a
 * INT t3: b
 *)
(* Everything, but not reset *)
Definition Add_Main : { M : mTM sigNat^+ 4 & states M -> unit } :=
  LiftTapes (CopyValue _) [|Fin1; Fin2|];; (* copy n to a *)
  LiftTapes (CopyValue _) [|Fin0; Fin3|];; (* copy m to b *)
  LiftTapes Add_Loop [|Fin2; Fin3|]. (* Main loop *)


(*
 * Finally, reset tape b.
 * For technical reasons, it is convienient to define the machine for this last step seperately,
 * because it makes prooving the termination easier.
 *)
Definition Add :=
  Add_Main;; (* Initialisation and main loop *)
  LiftTapes (Reset _) [|Fin3|]. (* Reset b *)


(** ** Correctness of [Add] *)

Definition Add_Step_Rel : Rel (tapes sigNat^+ 2) (option unit * tapes sigNat^+ 2) :=
  fun tin '(yout, tout) =>
    forall a b,
      tin [@Fin0] ≃ a ->
      tin [@Fin1] ≃ b ->
      match yout, b with
      | Some tt, O => (* break *)
        tout[@Fin0] ≃ a /\
        tout[@Fin1] ≃ b
      | None, S b' =>
        tout[@Fin0] ≃ S a /\
        tout[@Fin1] ≃ b'
      | _, _ => False
      end.

Lemma Add_Step_Sem : Add_Step ⊨c(9) Add_Step_Rel.
Proof.
  eapply RealiseIn_monotone.
  {
    unfold Add_Step. repeat TM_Correct.
  }
  { cbn. reflexivity. }
  {
    intros tin (yout, tout) H. cbn. intros a b HEncA HEncB. cbn in *.
    destruct H; TMSimp; clear_trivial_eqs.
    - modpon H. destruct b; auto.
    - modpon H. destruct b; auto.
  }
Qed.


Definition Add_Loop_Rel : Rel (tapes sigNat^+ 2) (unit * tapes sigNat^+ 2) :=
  ignoreParam (
      fun tin tout =>
        forall a b,
          tin [@Fin0] ≃ a ->
          tin [@Fin1] ≃ b ->
          tout[@Fin0] ≃ b + a /\
          tout[@Fin1] ≃ 0
    ).

Lemma Add_Loop_Realise : Add_Loop ⊨ Add_Loop_Rel.
Proof.
  eapply Realise_monotone.
  { unfold Add_Loop. repeat TM_Correct. eapply RealiseIn_Realise. apply Add_Step_Sem. }
  {
    apply WhileInduction; intros; intros a b HEncA HEncB; cbn in *; destruct_unit.
    - specialize (HLastStep _ _ HEncA HEncB). destruct b; auto.
    - specialize (HStar _ _ HEncA HEncB).
      destruct b; auto. destruct HStar as (HStar1&HStar2).
      specialize (HLastStep _ _ HStar1 HStar2) as (IH1&IH2).
      rewrite <- Nat.add_succ_comm in IH1. cbn in *. auto.
  }
Qed.





(* Everything, but reset *)
Definition Add_Main_Rel : Rel (tapes sigNat^+ 4) (unit * tapes sigNat^+ 4) :=
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


Lemma Add_Main_Realise : Add_Main ⊨ Add_Main_Rel.
Proof.
  eapply Realise_monotone.
  {
    unfold Add_Main. repeat TM_Correct.
    - apply CopyValue_Realise with (X := nat).
    - apply CopyValue_Realise with (X := nat).
    - apply Add_Loop_Realise.
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


Lemma Add_Computes : Add ⊨ Computes2_Rel plus.
Proof.
  eapply Realise_monotone.
  {
    unfold Add. repeat TM_Correct.
    - apply Add_Main_Realise.
    - apply Reset_Realise with (X := nat). (* Don't forget the type here! *)
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

Local Arguments plus : simpl never.
Local Arguments mult : simpl never.

Definition Add_Loop_steps b := 9 + 10 * b.

Lemma Add_Loop_Terminates :
  projT1 Add_Loop ↓
         (fun tin i => exists a b,
              tin[@Fin0] ≃ a /\
              tin[@Fin1] ≃ b /\
              Add_Loop_steps b <= i).
Proof.
  eapply TerminatesIn_monotone.
  { unfold Add_Loop. repeat TM_Correct.
    - eapply RealiseIn_Realise. apply Add_Step_Sem.
    - eapply RealiseIn_TerminatesIn. apply Add_Step_Sem. }
  {
    unfold Add_Loop_steps. apply WhileCoInduction. intros tin i (a&b&HEncA&HEncB&Hi).
    destruct b.
    (* (* In case I want to use the [WhileInduction] principle without [match] *)
    - exists 11. repeat split.
      + omega.
      + intros () ? _. omega.
      + intros tmid H. cbn in *. specialize (H _ _ HEncA HEncB). cbn in *. auto.
    - exists 11. repeat split.
      + omega.
      + intros () tmid H. cbn in H. specialize (H _ _ HEncA HEncB). now cbn in *.
      + intros tmid H. cbn in H. specialize (H _ _ HEncA HEncB). cbn in *. destruct H as (H1&H2).
        exists (11 + b * 12). repeat split.
        * exists (S a), b. repeat split; eauto. omega.
        * omega.
        *)
    - exists 9. repeat split.
      + omega.
      + intros o tmid H. cbn in H. specialize (H _ _ HEncA HEncB). cbn in *.
        destruct o; auto.
    - exists 9. repeat split.
      + omega.
      + intros o tmid H. cbn in H. specialize (H _ _ HEncA HEncB). cbn -[plus mult] in *.
        destruct o as [ () | ]; auto. destruct H.
        exists (9 + b * 10). repeat split.
        * do 2 eexists. repeat split; eauto. omega.
        * omega.
  }
Qed.


Definition Add_Main_steps m n := 85 + 12 * n + 22 * m.
(* [37 + 12 * n] for [CopyValue] (n) *)
(* [37 + 12 * m] for [CopyValue] (m) *)
(* [9 + 10 * m] for [Add_Loop] *)

Lemma Add_Main_Terminates :
  projT1 Add_Main ↓ Computes2_T Add_Main_steps.
Proof.
  unfold Add_Main, Add_Main_steps. eapply TerminatesIn_monotone.
  {
    repeat TM_Correct.
    - apply CopyValue_Realise with (X := nat).
    - apply CopyValue_Terminates with (X := nat).
    - apply CopyValue_Realise with (X := nat).
    - apply CopyValue_Terminates with (X := nat).
    - apply Add_Loop_Terminates.
  }
  {
    intros tin k (m&n&HEncM&HEncN&HOut&HInt&Hk).
    exists (37 + 12 * n), (47 + 22 * m). repeat split; cbn.
    - cbn. exists n. split; eauto. unfold CopyValue_steps. rewrite Encode_nat_hasSize. omega.
    - omega.
    - intros tmid ymid. intros (H1&H2). TMSimp.
      specialize (H1 _ HEncN HOut). TMSimp.
      specialize (HInt Fin0).
      exists (37 + 12 * m), (Add_Loop_steps m). repeat split.
      + exists m. split. eauto. unfold CopyValue_steps. rewrite Encode_nat_hasSize. omega.
      + unfold Add_Loop_steps. omega.
      + intros tmid2 () (HComp & HInj). TMSimp.
        specialize (HComp _ HEncM HInt) as (HComp&HComp').
        do 2 eexists; repeat split; eauto; do 2 eexists; eassumption.
  }
Qed.


Definition Add_steps m n := 98 + 12 * n + 22 * m.
(* Additional [12] steps for [Reset], and [1] for [Seq] *)

Lemma Add_Terminates :
  projT1 Add ↓ Computes2_T Add_steps.
Proof.
  unfold Add, Add_steps. eapply TerminatesIn_monotone.
  {
    repeat TM_Correct.
    - apply Add_Main_Realise.
    - apply Add_Main_Terminates.
    - apply Reset_Terminates with (X := nat).
  }
  {
    intros tin k (m&n&HEncM&HEncN&HOut&HInt&Hk).
    exists (Add_Main_steps m n), 12. repeat split.
    - cbn. exists m, n. repeat split; eauto.
    - unfold Add_Main_steps. omega.
    - intros tmid () HComp. cbn in *.
      specialize (HInt Fin0).
      specialize (HComp _ _ HEncM HEncN HOut HInt) as (HComp1&HComp2&HComp3&HComp4).
      exists 0. split. eauto. unfold MoveRight_steps. cbn. auto.
  }
Qed.



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
 * while (m--) {
 *   ADD(n, c, c')
 *   Reset c
 *   c := c'
 *   Reset c'
 * }
 * Reset m'
 *)

(*
 * Step-Machine:
 * (Note that it only accesses the copy of m)
 *
 * t0: m' (counter)
 * t1: n  (for Add: INP t0)
 * t2: c  (for Add: INP t1)
 * t3: c' (for Add: OUT t2)
 * t4:    (for Add: INT t3)
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
Definition Mult_Step : { M : mTM _ 5 & states M -> option unit } :=
  If (LiftTapes MatchNat [|Fin0|])
     (Return (
          LiftTapes Add [|Fin1; Fin2; Fin3; Fin4|];; (* Add(n, c, c') *)
          LiftTapes (Reset _) [|Fin2|];;
          LiftTapes (CopyValue _) [|Fin3; Fin2|];; (* c := c' *)
          LiftTapes (Reset _) [|Fin3|] (* Reset c' *)
        ) (None)) (* continue *)
     (Return Nop (Some tt)). (* break *)


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
  LiftTapes (CopyValue _) [|Fin0; Fin5|];; (* m' := m *)
  LiftTapes (Constr_O) [|Fin2|];; (* c := 0 *)
  LiftTapes Mult_Loop [|Fin5; Fin1; Fin2; Fin3; Fin4|]. (* Main loop *)


Definition Mult : { M : mTM _ 6 & states M -> unit } :=
  Mult_Main;;
  LiftTapes (Reset _) [|Fin5|]. (* Reset m' *)


(** ** Correctness of [Mult] *)

Definition Mult_Step_Rel : Rel (tapes sigNat^+ 5) (option unit * tapes sigNat^+ 5) :=
  fun tin '(yout, tout) =>
    forall c m' n,
      tin[@Fin0] ≃ m' ->
      tin[@Fin1] ≃ n ->
      tin[@Fin2] ≃ c ->
      isRight tin[@Fin3] ->
      isRight tin[@Fin4] ->
      match yout, m' with
      | (Some tt), O => (* return *)
        tout[@Fin0] ≃ m' /\
        tout[@Fin1] ≃ n /\
        tout[@Fin2] ≃ c /\
        isRight tout[@Fin3] /\
        isRight tout[@Fin4]
      | None, S m'' => (* continue *)
        tout[@Fin0] ≃ m'' /\
        tout[@Fin1] ≃ n /\
        tout[@Fin2] ≃ n + c /\
        isRight tout[@Fin3] /\
        isRight tout[@Fin4]
      | _, _ => False
      end.

Lemma Mult_Step_Realise : Mult_Step ⊨ Mult_Step_Rel.
Proof.
  eapply Realise_monotone.
  {
    unfold Mult_Step. repeat TM_Correct.
    - apply Add_Computes.
    - apply Reset_Realise with (X := nat).
    - apply CopyValue_Realise with (X := nat).
    - apply Reset_Realise with (X := nat).
  }
  {
    intros tin (yout, tout) H. intros c m' n HEncM' HEncN HEncC HInt3 HInt4. TMSimp.
    destruct H; TMSimp.
    - specialize (H _ HEncM').
      destruct m' as [ | m']; auto.
      specialize (H0 _ _ HEncN HEncC HInt3).
      spec_assert H0 as (HComp1&HComp2&HComp3&HComp4).
      { intros i; destruct_fin i; cbn; assumption. }
      specialize (HComp4 Fin0); cbn in HComp4.
      specialize (H1 _ HComp2).
      specialize (H2 _ HComp3 H1) as (H7&H7').
      repeat split; eauto.
    - specialize (H _ HEncM').
      destruct m' as [ | m']; auto.
  }
Qed.

Definition Mult_Loop_Rel : Rel (tapes sigNat^+ 5) (unit * tapes sigNat^+ 5) :=
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


Lemma Mult_Loop_Realise :
  Mult_Loop ⊨ Mult_Loop_Rel.
Proof.
  eapply Realise_monotone.
  {
    unfold Mult_Loop. repeat TM_Correct. eapply Mult_Step_Realise.
  }
  {
    eapply WhileInduction; intros; intros c m' n HEncM' HEncN HEncC HInt3 HInt4; TMSimp.
    - specialize (HLastStep _ _ _ HEncM' HEncN HEncC HInt3 HInt4).
      destruct m' as [ | m']; auto.
    - specialize (HStar _ _ _ HEncM' HEncN HEncC HInt3 HInt4).
      destruct m' as [ | m']; auto. destruct HStar as (HStar1&HStar2&HStar3&HStar4&HStar5).
      specialize (HLastStep _ _ _ ltac:(eauto) ltac:(eauto) ltac:(eauto) ltac:(eauto) ltac:(eauto)) as (HL1&HL2&HL3&HL4&HL).
      rewrite Nat.add_assoc in HL3. replace (n + m' * n + c) with (m' * n + n + c) by omega.
      repeat split; auto. apply tape_contains_ext with (1 := HL3). f_equal. rewrite Nat.mul_succ_l. omega.
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

Definition Mult_Main_Rel : Rel (tapes sigNat^+ 6) (unit * tapes sigNat^+ 6) :=
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

Lemma Mult_Main_Realise :
  Mult_Main ⊨ Mult_Main_Rel.
Proof.
  eapply Realise_monotone.
  {
    unfold Mult_Main. repeat TM_Correct.
    - apply CopyValue_Realise with (X := nat).
    - apply Mult_Loop_Realise.
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
  Mult ⊨ Computes2_Rel mult.
Proof.
  eapply Realise_monotone.
  {
    unfold Mult. repeat TM_Correct.
    - eapply Mult_Main_Realise.
    - eapply Reset_Realise with (X := nat).
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


(** ** Termination of Mult *)

Definition Mult_Step_steps m' n c :=
  match m' with
  | O => 6
  | _ => 168 + 33 * c + 39 * n
  end.
(* [5] for [If] and [1] for [MatchNat] *)
(* [98+12*n+22*c] for [Add] *)
(* [12+c] for [Reset] (c) *)
(* [36+12*(c+n)] for [CopyValue] (c' = c + n) *)
(* [12 + (c+n)] for [Reset] (c' = c + n) *)


Lemma Mult_Step_Terminates :
  projT1 Mult_Step ↓
         (fun tin k => exists m' n c,
              tin[@Fin0] ≃ m' /\
              tin[@Fin1] ≃ n /\
              tin[@Fin2] ≃ c /\
              isRight tin[@Fin3] /\
              isRight tin[@Fin4] /\
              Mult_Step_steps m' n c <= k).
Proof.
  eapply TerminatesIn_monotone.
  {
    unfold Mult_Step. repeat TM_Correct.
    - apply Add_Computes.
    - apply Add_Terminates.
    - apply Reset_Realise with (X := nat).
    - apply Reset_Terminates with (X := nat).
    - apply CopyValue_Realise with (X := nat).
    - apply CopyValue_Terminates with (X := nat).
    - apply Reset_Terminates with (X := nat).
  }
  {
    intros tin k. intros (m'&n&c&HEncM'&HEncN&HEncC&HInt3&HInt4&Hk).
    destruct m' as [ | m']; cbn.
    - exists 5, 0. cbn in *; repeat split; eauto.
      intros tmid y (HComp&HInj). TMSimp.
      specialize (HComp _ HEncM'). cbn in *.
      destruct y; auto.
    - exists 5, (162 + 33 * c + 39 * n); cbn in *; repeat split; eauto.
      intros tmid y (HComp&HInj). TMSimp.
      specialize (HComp _ HEncM'). cbn in *. destruct y; auto.
      exists (Add_steps n c), (63 + 21 * c + 17 * n); cbn in *; repeat split.
      do 2 eexists. repeat split; eauto. intros i; destruct_fin i; cbn. eauto.
      unfold Add_steps. omega.
      intros tmid0 () (HComp2&HInj). TMSimp.
      specialize HComp2 with (1 := HEncN) (2 := HEncC) (3 := HInt3).
      spec_assert HComp2 as (HComp2&HComp3&HComp4&HComp5) by (intros i; destruct_fin i; cbn; auto).
      specialize (HComp5 Fin0). cbn in *. TMSimp.
      exists (12 + 4 * c), (50 + 17 * (c + n)). repeat split; try omega.
      eexists. repeat split. eauto. unfold Reset_steps. rewrite Encode_nat_hasSize. omega.
      intros tmid1 () (HComp6&HInj). TMSimp.
      specialize HComp6 with (1 := HComp3).
      exists (37 + 12 * (c + n)), (12 + 4 * (c + n)). repeat split; try omega.
      eexists. repeat split. eauto. unfold CopyValue_steps. rewrite Encode_nat_hasSize. omega.
      intros tmid2 () (HComp7&HInj7); TMSimp. specialize HComp7 with (1 := HComp4) (2 := HComp6) as (HComp7&HComp8).
      eexists. repeat split. eauto. unfold Reset_steps. rewrite Encode_nat_hasSize. omega.
  }
Qed.


Fixpoint Mult_Loop_steps m' n c :=
  match m' with
  | O => S (Mult_Step_steps m' n c)
  | S m'' => S (Mult_Step_steps m' n c) + Mult_Loop_steps m'' n (n + c)
  end.


Lemma Mult_Loop_Terminates :
  projT1 Mult_Loop ↓
         (fun tin i => exists m' n c,
              tin[@Fin0] ≃ m' /\
              tin[@Fin1] ≃ n /\
              tin[@Fin2] ≃ c /\
              isRight tin[@Fin3] /\
              isRight tin[@Fin4] /\
              Mult_Loop_steps m' n c <= i).
Proof.
  eapply TerminatesIn_monotone.
  { unfold Mult_Loop. repeat TM_Correct.
    - apply Mult_Step_Realise.
    - apply Mult_Step_Terminates. }
  {
    apply WhileCoInduction. intros tin k (m'&n&c&HEncM'&HEncN&HEncC&HRight3&HRight4&Hk).
    destruct m' as [ | m''] eqn:E; cbn in *; exists (Mult_Step_steps m' n c).
    {
      repeat split.
      - do 3 eexists. repeat split; eauto. cbn. unfold Mult_Step_steps. destruct m'; omega.
      - intros o tmid H1.
        specialize H1 with (1 := HEncM') (2 := HEncN) (3 := HEncC) (4 := HRight3) (5 := HRight4).
        destruct o as [ () | ]; auto. destruct H1 as (HComp1&HComp2&HComp3&HComp4&HComp5).
        subst. cbn. omega.
    }
    {
      repeat split.
      - do 3 eexists. repeat split; eauto. cbn. unfold Mult_Step_steps. destruct m'; omega.
      - intros o tmid H1.
        specialize H1 with (1 := HEncM') (2 := HEncN) (3 := HEncC) (4 := HRight3) (5 := HRight4).
        destruct o as [ () | ]; auto. destruct H1 as (HComp1&HComp2&HComp3&HComp4&HComp5).
        cbn. eexists. repeat split.
        + do 3 eexists. repeat split; eauto.
        + cbn. rewrite <- Hk. subst. clear_all. unfold Mult_Step_steps. omega.
    }
  }
Qed.


Definition Mult_Main_steps m n := 44 + 12 * m + Mult_Loop_steps m n 0.
(* [2] steps for [Seq], in total *)
(* [37+12*m] for [CopyValue] (m) *)
(* [Mult_Loop_steps m n 0] for [Mult_Loop] *)



Lemma Mult_Main_Terminates : projT1 Mult_Main ↓ Computes2_T Mult_Main_steps.
Proof.
  eapply TerminatesIn_monotone.
  { unfold Mult_Main. repeat TM_Correct.
    - apply CopyValue_Realise with (X := nat).
    - apply CopyValue_Terminates with (X := nat).
    - apply Mult_Loop_Terminates.
  }
  {
    intros tin k (m&n&HEncM&HEncN&HOut&HInt&Hk). cbn in *. unfold Mult_Main_steps in Hk.
    exists (37 + 12 * m), (6 + Mult_Loop_steps m n 0). repeat split; try omega.
    eexists. repeat split; eauto. unfold CopyValue_steps. rewrite Encode_nat_hasSize; cbn. omega.
    intros tmid () (H1&H2); TMSimp. specialize H1 with (1 := HEncM) (2 := HInt _) as (H1&H1').
    exists 5, (Mult_Loop_steps m n 0). repeat split; try omega.
    unfold Constr_O_steps. omega.
    intros tmid2 () (H2&HInj2); TMSimp. specialize H2 with (1 := HOut).
    do 3 eexists. repeat split; eauto.
  }
Qed.


Definition Mult_steps m n := 13 + Mult_Main_steps m n.

Lemma Mult_Terminates : projT1 Mult ↓ Computes2_T Mult_steps.
Proof.
  eapply TerminatesIn_monotone.
  { unfold Mult. repeat TM_Correct.
    - apply Mult_Main_Realise.
    - apply Mult_Main_Terminates.
    - apply Reset_Terminates with (X := nat).
  }
  {
    intros tin k (m&n&HEncM&HEncN&HOut&HInt&Hk). cbn in *. unfold Mult_steps in Hk.
    exists (Mult_Main_steps m n), 12. repeat split; try omega.
    do 2 eexists; repeat split; eauto.
    intros tmid () H1; TMSimp.
    specialize H1 with (1 := HEncM) (2 := HEncN) (3 := HOut) (4 := HInt _) (5 := HInt _) (6 := HInt _) as (H1&H2&H3&H4&H5&H6).
    exists 0. split; auto.
  }
Qed.