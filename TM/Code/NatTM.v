Require Import TM.Code.CodeTM TM.Code.MatchNat TM.Code.NatCounter.
Require Import TM.Basic.Mono Basic.Nop Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.
Require Import TM.Code.Copy.
Require Import Coq.Init.Nat.



(*
 * This definition of [tail_plus] differs from the definition of [tail_plus] in the standard library,
 * only that it is recursive over the second number.
 *)

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
  | S n' => tail_mult_acc (a + m) m n'
  end.

Definition tail_mult (m n : nat) := tail_mult_acc 0 m n.

Lemma mult_tail_mult_aux (a m n : nat) :
  a + m * n = tail_mult_acc a m n.
Proof.
  revert a m. induction n as [ | n' IH]; intros.
  - cbn. omega.
  - cbn. rewrite <- IH. rewrite Nat.mul_succ_r. omega.
Qed.

Lemma mult_tail_mult (m n : nat) :
  m * n = tail_mult m n.
Proof. pose proof (mult_tail_mult_aux 0 m n) as L. cbn in L. auto. Qed.


(* [tail_pow] is missing at all *)
Print pow.
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

  
  (* The 0th tape is the first input and the output. The 1st tape is the second input and doesn't change. *)
  Definition Computes2_Reset_Rel (f : X -> Y -> Z) : Rel (tapes (sig^+) n) (unit * tapes (sig^+) n) :=
    ignoreParam (
        fun tin tout =>
          forall (x : X) (y : Y),
            tin[@i1] ≂ x ->
            tin[@i2] ≂ y ->
            tout[@i1] ≂ f x y /\
            tout[@i2] = tin[@i2]
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

  Definition Iter_Step : { M : mTM _ 2 & states M -> bool * unit } :=
    If (Inject CountDown [|Fin.FS Fin.F1|])
       (Return (Inject M1 [|Fin.F1|]) (true, tt))
       (Nop _ _ (false, tt)).

  
  Definition Iter : { M : mTM _ 2 & states M -> unit } := WHILE Iter_Step.

  Definition Iter_Reset := Iter;; Inject Reset [|Fin.FS Fin.F1|].
  

  (** Correctness *)

  
  Definition Iter_Step_Rel : Rel (tapes (bool^+) 2) ((bool * unit) * tapes (bool^+) 2) :=
    ignoreSecond (
        if? (fun tin tout =>
               forall m n n' r1 r2,
                 tin[@Fin.F1] ≂ m ->
                 counterIs_rest tin[@Fin.FS Fin.F1] n n' r1 r2 ->
                 exists n'', n' = S n'' /\
                        tout[@Fin.F1] ≂ f m /\
                        counterIs_rest tout[@Fin.FS Fin.F1] n n'' r1 r2)
            ! (fun tin tout =>
                 forall m n n' r1 r2,
                   tin[@Fin.F1] ≂ m ->
                   counterIs_rest tin[@Fin.FS Fin.F1] n n' r1 r2 ->
                   n' = 0 /\ tout = tin)
      ).


  Lemma Iter_Step_WRealise : Iter_Step ⊫ Iter_Step_Rel.
  Proof.
    eapply WRealise_monotone.
    {
      unfold Iter_Step. repeat TM_Correct.
      - eapply RealiseIn_WRealise. apply CountDown_Sem.
    }
    {
      intros tin (yout, tout) H. TMSimp. destruct H; TMSimp inv_pair; clear_trivial_eqs.
      - specialize (H _ _ _ _ H3) as (n''&->&H). eexists. repeat split; eauto.
      - specialize (H _ _ _ _ H2) as (->&H). eexists. repeat split. repeat f_equal. auto.
    }
  Qed.


  Definition Iter_Rel : Rel (tapes bool^+ 2) (unit * tapes bool^+ 2) :=
    ignoreParam (
        fun tin tout =>
          forall m n n' r1 r2,
            tin[@Fin.F1] ≂ m ->
            counterIs_rest tin[@Fin.FS Fin.F1] n n' r1 r2 ->
            tout[@Fin.F1] ≂ iter m n' /\
            counterIs_rest tout[@Fin.FS Fin.F1] n 0 r1 r2
      ).


  Lemma Iter_WRealise : Iter ⊫ Iter_Rel.
  Proof.
    eapply WRealise_monotone.
    { unfold Iter. repeat TM_Correct. apply Iter_Step_WRealise. }
    {
      intros tin ((), tout) (tmid&HStar&HLastStep).
      induction HStar as [ tin | tin tmid1 tmid2 HStar _ IH]; intros m n n' r1 r2 H1 H2.
      - specialize (HLastStep _ _ _ _ _ H1 H2) as (HLS1&HLS2). inv HLS2.
        replace (m + 0) with m by omega. auto.
      - repeat (spec_assert IH; eauto). cbn in HLastStep, IH, HStar. destruct HStar as (()&HStar). cbn in HStar.
        specialize (HStar _ _ _ _ _ H1 H2) as (n''&->&HS1&HS2).
        specialize (IH _ _ _ _ _ HS1 HS2) as (IH1&IH2).
        auto.
    }
  Qed.

  Lemma Iter_Computes : Iter ⊫ Computes2_Rel Fin.F1 (Fin.FS Fin.F1) Fin.F1 _ _ _ iter.
  Proof.
    eapply WRealise_monotone. apply Iter_WRealise.
    intros tin ((), tout) H. intros m n HEncM HEncN. hnf in H.
    destruct HEncN as (r1&r2&HEncN). apply tape_encodes_l_natCounterIsM in HEncN.
    now specialize (H m n n r1 r2 HEncM HEncN) as (?&?).
  Qed.

  Definition Iter_Reset_Rel : Rel (tapes bool^+ 2) (unit * tapes bool^+ 2) :=
    ignoreParam (
        fun tin tout =>
          forall m n n' r1 r2,
            tin[@Fin.F1] ≂ m ->
            counterIs_rest tin[@Fin.FS Fin.F1] n n' r1 r2 ->
            tout[@Fin.F1] ≂ iter m n' /\
            counterIs_rest tout[@Fin.FS Fin.F1] n n r1 r2
      ).

  Lemma Iter_Reset_WRealise : Iter_Reset ⊫ Iter_Reset_Rel.
  Proof.
    eapply WRealise_monotone.
    - unfold Iter_Reset. repeat TM_Correct.
      + apply Iter_WRealise.
      + apply Reset_WRealises.
    - intros tin ((), tout) H. intros m n n' r1 r2 HEncM HEncN. hnf in H.
      destruct H as ((()&tmid) & H1 & H2 & H3). cbn in *. simpl_not_in. rewrite H3 in *.
      specialize (H1 _ _ _ _ _ HEncM HEncN) as (H1&H1'). rewrite <- H3 in *.
      specialize (H2 _ _ _ _ H1'). split; auto.
  Qed.

  Lemma Iter_Reset_Computes : Iter_Reset ⊫ Computes2_Reset_Rel Fin.F1 (Fin.FS Fin.F1) _ _ _ iter.
  Proof.
    eapply WRealise_monotone. eapply Iter_Reset_WRealise.
    intros tin ((), tout) H. intros m n HEncM HEncN. hnf in H.
    destruct HEncN as (r1 & r2 & HEncN % tape_encodes_l_natCounterIsM).
    specialize (H _ _ _ _ _ HEncM HEncN) as (H1&H2). split; auto.
    eapply counterIs_rest_injective in H2; eauto.
  Qed.


  (** Termination *)

  Variable M1_runtime : nat -> nat.
  Hypothesis M1_terminates : projT1 M1 ↓ (fun tin k => exists y, tin[@Fin.F1] ≂ y /\ M1_runtime y <= k).

  Print Iter_Step.

  Lemma Iter_Step_Terminates :
    projT1 Iter_Step ↓ (fun tin i => exists m n n' r1 r2,
                            tin[@Fin.F1] ≂ m /\
                            counterIs_rest tin[@(Fin.FS Fin.F1)] n n' r1 r2 /\
                            match n' with
                            | O => 4
                            | S y' => 4 + M1_runtime m
                            end <= i).
  Proof.
    eapply TerminatesIn_monotone.
    {
      unfold Iter_Step. repeat TM_Correct. 
      - eapply RealiseIn_WRealise. apply CountDown_Sem.
      - eapply RealiseIn_terminatesIn. apply CountDown_Sem.
    }
    {
      intros tin i. intros (m&n&n'&r1&r2&HEncM&HEncN&Hi).
      destruct n' as [ | n''] eqn:En'.
      - exists 3, 0. repeat split.
        + omega.
        + cbn. omega.
        + intros tout b H. cbn in H. destruct b; cbn.
          * destruct H as (H1&H2). simpl_not_in. rewrite <- H2 in *. specialize (H1 _ _ _ _ HEncN) as (?&?&_). exfalso; congruence.
          * omega.
      - exists 3, (M1_runtime m). repeat split.
        + omega.
        + cbn. omega.
        + intros tout b H. cbn in H. destruct b; cbn.
          * destruct H as (H1&H2). simpl_not_in. rewrite <- H2 in *. specialize (H1 _ _ _ _ HEncN) as (?&?&?H); inv H. eauto.
          * omega.
    }
  Qed.
  
  Fixpoint Iter_steps (m n : nat) { struct n } : nat :=
    match n with
    | O => 4
    | S n' => 5 + M1_runtime m + Iter_steps (f m) n'
    end.

  Lemma Iter_steps_ge4 (m n : nat) :
    4 <= Iter_steps m n.
  Proof. destruct n; cbn; omega. Qed.


  Lemma Iter_steps_homogene (m n k : nat) :
    (forall x, M1_runtime x <= k) ->
    Iter_steps m n <= 4 + (5 + k) * n.
  Proof.
    revert m. induction n as [ | n' IH]; intros; cbn -[add mult] in *.
    - omega.
    - specialize (IH (f m) H). pose proof (H (f m)) as H1. pose proof (H m) as H2.
      rewrite !Nat.mul_succ_r.
      rewrite !Nat.mul_add_distr_r in *.
      rewrite !Nat.add_assoc in *.
      omega. (* Oh [omega], my dear [omega]! *)
  Qed.

  Lemma Iter_Terminates' :
    projT1 Iter ↓ (fun tin i => exists m n n' r1 r2, 
                       tin[@Fin.F1] ≂ m /\
                       counterIs_rest tin[@Fin.FS Fin.F1] n n' r1 r2 /\
                       Iter_steps m n' <= i).
  Proof.
    unfold Iter. repeat TM_Correct.
    { apply Iter_Step_WRealise. }
    { eapply Iter_Step_Terminates. }
    {
      intros tin i (m&n&n'&r1&r2&HEncM&HEncN&Hi).
      destruct n'.
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
    projT1 Iter ↓ (fun tin k => exists x y, tin[@Fin.F1] ≂ x /\ tin[@Fin.FS Fin.F1] ≂ y /\ Iter_steps x y <= k).
  Proof.
    eapply TerminatesIn_monotone. eapply Iter_Terminates'. intros tin i (m&n&HEncM&HEncN&Hi).
    destruct HEncN as (r1&r2&HEncN % tape_encodes_l_natCounterIsM). do 5 eexists. repeat split; eauto; omega.
  Qed.


  Lemma Iter_Reset_Terminates' :
    projT1 Iter_Reset ↓ (fun tin i => exists m n n' r1 r2, 
                             tin[@Fin.F1] ≂ m /\
                             counterIs_rest tin[@Fin.FS Fin.F1] n n' r1 r2 /\
                             11 + Iter_steps m n' + 4 * n <= i).
  Proof.
    eapply TerminatesIn_monotone.
    - unfold Iter_Reset. repeat TM_Correct.
      + apply Iter_WRealise.
      + apply Iter_Terminates'.
      + apply Reset_Terminates.
    - intros tin i (m&n&n'&r1&r2&HEncM&HEncN&Hi).
      exists (Iter_steps m n'), (10 + 4 * n). repeat split.
      + rewrite <- Hi. clear_all. apply Nat.eq_le_incl. omega.
      + do 5 eexists. repeat split. eauto. eauto. omega.
      + intros tout () H. cbn -[plus mult]. hnf in H. specialize (H _ _ _ _ _ HEncM HEncN) as (H1&H2).
        destruct H2 as (k&->&H2&H2'). do 5 eexists. repeat split. eauto. eauto. omega.
  Qed.

  Lemma Iter_Reset_Terminates :
    projT1 Iter_Reset ↓ (fun tin i => exists m n, tin[@Fin.F1] ≂ m /\ tin[@Fin.FS Fin.F1] ≂ n /\ 11 + Iter_steps m n + 4 * n <= i).
  Proof.
    eapply TerminatesIn_monotone. eapply Iter_Reset_Terminates'. intros tin i (m&n&HEncM&HEncN&Hi).
    destruct HEncN as (r1&r2&HEncN % tape_encodes_l_natCounterIsM). do 5 eexists. repeat split; eauto; omega.
  Qed.

End Iter1.


Lemma add_steps : forall m n, Iter_steps S (fun _ => 5) m n = 4 + 10 * n.
Proof.
  intros m n. revert m. induction n as [ | n' IH]; intros; cbn -[plus mult] in *.
  - omega.
  - rewrite IH. omega.
Qed.

Definition Add := Iter_Reset Constr_S.

Lemma tail_add_iter (m n : nat) :
  tail_plus m n = iter S m n.
Proof.
  revert m. induction n; intros; cbn in *.
  omega. rewrite IHn. omega.
Qed.

Lemma Add_WRealise' :
  Add ⊫ Computes2_Reset_Rel (Fin.F1) (Fin.FS Fin.F1) _ _ _ tail_plus.
Proof.
  eapply Computes2_Reset_Ext_WRealise.
  - refine tail_add_iter.
  - unfold Add. apply Iter_Reset_Computes.
    eapply WRealise_monotone. 
    + eapply RealiseIn_WRealise. apply Constr_S_Sem.
    + intros tin ((), tout) H. hnf in *. auto.
Qed.

Lemma Add_WRealise :
  Add ⊫ Computes2_Reset_Rel (Fin.F1) (Fin.FS Fin.F1) _ _ _ plus.
Proof.
  eapply Computes2_Reset_Ext_WRealise.
  - apply plus_tail_plus.
  - apply Add_WRealise'.
Qed.


Lemma Add_Terminates :
  projT1 Add ↓ (fun tin k => exists x y, tin[@Fin.F1] ≂ x /\ tin[@Fin.FS Fin.F1] ≂ y /\ 15 + 14 * y <= k).
Proof.
  eapply TerminatesIn_monotone.
  - unfold Add. apply Iter_Reset_Terminates.
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


(*


Section Iter2.

  Variable f : nat -> nat -> nat.

  Definition iter2 (s x y : nat) := iter (fun z => f z x) s y.

  Fixpoint tail_iter2 (s x y : nat) {struct y} : nat :=
    match y with
    | O => s
    | S y' => tail_iter2 (f s x) x y'
    end.

  Lemma tail_iter2_iter2 (s x y : nat) :
    iter2 s x y = tail_iter2 s x y.
  Proof. revert s. induction y as [ | y' IH]; intros; cbn in *; eauto. Qed.

  
  Variable n : nat.
  Variable M1 : { M : mTM (bool^+) n & states M -> unit }.
  Variable (i1 i2 : Fin.t n).
  Hypothesis i_disj: i1 <> i2.
  Hypothesis M1_computes : M1 ⊫ Computes2_Rel i1 i2 i1 _ _ _ f.

  (* step function of the accumulator *)
  Definition iter2_step (s x y : nat) : nat :=
    match y with
    | O => s
    | S y' => f s x
    end.


  Lemma tail_iter2_step_pred_eta s x y :
    tail_iter2 (iter2_step s x y) x (pred y) = tail_iter2 s x y.
  Proof. destruct y; cbn; auto. Qed.


  Notation "'injF' x" := (Fin.FS (Fin.FS x)) (at level 30).
  
  Local Definition indexes_M1 : Vector.t (Fin.t (S (S n))) n :=
    Vector.map (fun k => injF k) (Fin_initVect _).

  Local Lemma injF_injective (k1 k2 : Fin.t n) :
    injF k1 = injF k2 -> k1 = k2.
  Proof. now intros H % Fin.FS_inj % Fin.FS_inj. Qed.


  Local Lemma indexes_M1_dupfree : dupfree indexes_M1.
  Proof.
    apply dupfree_map_injective.
    - now intros k1 k2 H % injF_injective.
    - apply Fin_initVect_dupfree.
  Qed.

  Local Lemma indexes_M1_notIn0 : not_indexes indexes_M1 Fin.F1.
  Proof. unfold indexes_M1. intros (k&H1&H2) % vect_in_map_iff. inv H1. Qed.

  Local Lemma indexes_M1_notIn1 : not_indexes indexes_M1 (Fin.FS Fin.F1).
  Proof. unfold indexes_M1. intros (k&H1&H2) % vect_in_map_iff. inv H1. Qed.

  Local Lemma indexes_M1_reorder_nth (X : Type) (t1 t2 : X) ts k :
    (reorder indexes_M1 (t1 ::: t2 ::: ts))[@k] = ts[@k].
  Proof.
    unfold indexes_M1. unfold reorder. erewrite !VectorSpec.nth_map; eauto.
    cbn. now rewrite Fin_initVect_nth.
  Qed.

  Local Lemma i1_notIn_0_i2 : not_indexes [|Fin.F1; injF i2|] (injF i1).
  Proof.
    (* XXX: This should have been solved with the [vector_not_in] tactic *)
    intros H.
    apply In_cons in H as [? | ?]; try congruence.
    apply In_cons in H as [? | ?]; try congruence.
    apply injF_injective in H. eauto. inv H.
  Qed.

  Local Lemma i2_notIn_i1 : not_indexes [|injF i1|] (injF i2).
  Proof.
    intros [H % injF_injective | H] % In_cons; auto. inv H.
  Qed.
  
  
  (* XXX: This machine could be space-inefficient, as it may always appends new copies of [m] to tape [2+i2] *)
  (* Idea: Before executing the step machine, insert a special start marker to said tape and move to this marker after each use. *)
  (* Other idea: "destructing with remembering" ("overwritten" symbol) *)
  Definition Iter2_step : { M : mTM (bool^+) (S (S n)) & states M -> bool * unit } :=
    Inject (CopyValue' _) [| Fin.F1; injF i2 |];; (* Copy value [m] from tape 0 to tape 2+i2, where it is the second input of [M1] *)
    If (Inject MatchNat [|Fin.FS Fin.F1|]) (* Do pattern matching over [n] *)
       (Return (Inject M1 indexes_M1) (true, tt)) (* Execute [M1] *)
       (Nop _ _ (false, tt)). (* In case, [n] is [O], break. *)


  Definition Iter2_step_Rel :=
    fun tin '(yout, tout) =>
      forall (s x y : nat),
        tin[@injF i1] ≂ s ->
        tin[@Fin.F1] ≂ x ->
        tin[@Fin.FS Fin.F1] ≂ y ->
        yout = iter_step_param y /\
        tout[@Fin.F1] = tin[@Fin.F1] /\
        tout[@Fin.FS Fin.F1] ≂ pred y /\
        tout[@injF i1] ≂ iter2_step s x y.


  (* The step function has three inputs and two outputs. *)
  Lemma Iter2_step_Computes :
    Iter2_step ⊫ Iter2_step_Rel.
  Proof.
    unfold Iter2_step_Rel. eapply WRealise_monotone.
    {
      unfold Iter2_step. repeat TM_Correct.
      - apply CopyValue'_WRealise.
      - eapply RealiseIn_WRealise. apply MatchNat_Sem.
      - apply Inject_WRealise.
        + apply indexes_M1_dupfree.
        + apply M1_computes.
    }
    {
      intros tin (yout, tout) H.
      intros a x y HEncA HEncX HEncY.
      TMSimp.
      specialize (H _ HEncX) as (->&H).
      pose proof (H1 (Fin.FS Fin.F1)) as L1. spec_assert L1. intros ?. vector_not_in. cbn in L1. subst.
      pose proof (H1 (injF i1) i1_notIn_0_i2) as L1. cbn in L1. (* I use this later... *)
      destruct H0; TMSimp.
      - specialize (H0 _ HEncY) as (y'&->&HEncY'). unfold iter_step_param. split; auto.
        rewrite !indexes_M1_reorder_nth in H3.
        pose proof (H4 Fin.F1 ltac:(vector_not_in)) as L2. cbn in L2. rewrite <- L2 in *. clear L2.
        pose proof (H4 (injF i1) ltac:(vector_not_in)) as L2. cbn in L2. rewrite <- L2 in *. clear L2.
        pose proof (H4 (injF i2) ltac:(vector_not_in)) as L2. cbn in L2. rewrite <- L2 in *. clear L2.
        pose proof (H5 _ indexes_M1_notIn0) as L2. cbn in L2. rewrite <- L2 in *. clear L2.
        pose proof (H5 _ indexes_M1_notIn1) as L2. cbn in L2. rewrite <- L2 in *. clear L2.
        unfold finType_CS in *. rewrite L1 in *. now specialize (H3 a x HEncA H).
      - specialize (H0 _ HEncY) as (->&HencY').
        unfold iter_step_param. cbn.
        pose proof (H3 Fin.F1 ltac:(vector_not_in)) as L2. cbn in L2. rewrite <- L2 in *. clear L2.
        pose proof (H3 (injF i1) ltac:(vector_not_in)) as L2. cbn in L2. unfold finType_CS in *. rewrite <- L2 in *. clear L2.
        unfold finType_CS in *. now rewrite <- L1.
    }
  Qed.
  

  Definition Iter2_loop := WHILE Iter2_step.

  Definition Iter2_loop_Rel : Rel (tapes (bool^+) (S (S n))) (unit * tapes (bool^+) (S (S n))) :=
    ignoreParam (
        fun tin tout =>
          forall (s x y : nat),
            tin[@injF i1] ≂ s ->
            tin[@Fin.F1] ≂ x ->
            tin[@Fin.FS Fin.F1] ≂ y ->
            tout[@Fin.F1] = tin[@Fin.F1] /\
            tout[@injF i1] ≂ tail_iter2 s x y
      ).

  Lemma Iter2_loop_WRealise :
    Iter2_loop ⊫ Iter2_loop_Rel.
  Proof.
    eapply WRealise_monotone.
    {
      unfold Iter2_loop. repeat TM_Correct. apply Iter2_step_Computes.
    }
    {
      intros tin ((), tout) H. intros s x y HEncS HEncX HEncY.
      hnf in H. destruct H as (tmid2&HStar&HLastStep).
      revert s HEncS x HEncX y HEncY.
      induction HStar as [ tin | tin tmid1 tmid2 HStar _ IH]; intros.
      - hnf in HLastStep. specialize (HLastStep s x y HEncS HEncX HEncY) as (H1&H2&H3&H4).
        cbv in H1. destruct y; inv H1. auto.
      - hnf in HLastStep. spec_assert IH; eauto.
        hnf in HStar. destruct HStar as (()&HStar). hnf in HStar.
        specialize (HStar _ _ _ HEncS HEncX HEncY) as (H1&H2&H3&H4).
        specialize (IH _ H4). unfold finType_CS in *. rewrite H2 in *. specialize (IH _ HEncX). specialize (IH _ H3) as (IH1&IH2).
        now rewrite tail_iter2_step_pred_eta in IH2.
    }
  Qed.


  Definition Iter2 (s : nat) : { M : mTM (bool^+) (S (S n)) & states M -> unit } :=
    Inject (InitTape _ s) [|injF i1|];; (* Write [s] to tape [2+i1] *)
    Iter2_loop;; (* Execute the loop *)
    Inject (CopyValue' _) [|injF i1; Fin.F1|]. (* Copy the result (in tape [2+i1]) to tape [0] *)

  Lemma Iter2_Computes' (s : nat) :
    Iter2 s ⊫ Computes2_Rel Fin.F1 (Fin.FS Fin.F1) Fin.F1 _ _ _ (tail_iter2 s).
  Proof.
    eapply WRealise_monotone.
    {
      unfold Iter2. repeat TM_Correct.
      - eapply RealiseIn_WRealise. apply InitTape_Sem.
      - apply Iter2_loop_WRealise.
      - apply CopyValue'_WRealise.
    }
    {
      intros tin ((), tout) H. intros x y HEncX HEncY.
      hnf in H. destruct H as ((()&tmid)&(HEncS&HInject)&H). cbn in *.
      destruct H as ((()&tmid2)&HComp&(HCopy&HInject2)). cbn in *.
      pose proof HInject Fin.F1 ltac:(vector_not_in) as L1. cbn in L1. unfold finType_CS in *. try rewrite <- L1 in *.
      pose proof HInject (Fin.FS Fin.F1) ltac:(vector_not_in) as L2. cbn in L2. unfold finType_CS in *. try rewrite <- L2 in *.
      pose proof HInject _ i2_notIn_i1 as L3. cbn in L3. unfold finType_CS in *.
      specialize (HComp s x y HEncS HEncX HEncY) as (_&HRes).
      now specialize (HCopy _ HRes) as (_&Res').
    }
  Qed.

  Lemma Iter2_Computes (s : nat) :
    Iter2 s ⊫ Computes2_Rel Fin.F1 (Fin.FS Fin.F1) (Fin.F1) _ _ _ (iter2 s).
  Proof. eapply Computes2_Ext_WRealise. apply tail_iter2_iter2. apply Iter2_Computes'. Qed.


End Iter2.


(** Define and Instantiate Mult and Power now *)


Definition Mult := Iter2 Add ltac:(getFin 0) ltac:(getFin 1) 0.

Lemma iter2_mult s x y :
  iter2 plus s x y = tail_mult_acc s x y.
Proof. rewrite tail_iter2_iter2. revert s. induction y as [ | y' IH]; intros; cbn in *; auto. Qed.

Lemma mult_iter2 x y :
  x * y = iter2 plus 0 x y.
Proof. rewrite iter2_mult. rewrite <- mult_tail_mult_aux. cbn. omega. Qed.

Lemma Mult_WRealise :
  Mult ⊫ Computes2_Rel ltac:(getFin 0) ltac:(getFin 1) ltac:(getFin 0) _ _ _ mult.
Proof.
  eapply Computes2_Ext_WRealise.
  - apply mult_iter2.
  - unfold Mult. apply Iter2_Computes.
    + intros H. inv H.
    + apply Add_WRealise.
Qed.


Definition Power := Iter2 Mult ltac:(getFin 0) ltac:(getFin 1) 1.

Lemma iter2_power s x y :
  iter2 mult s x y = tail_pow_acc s x y.
Proof. rewrite tail_iter2_iter2. revert s. induction y as [ | y' IH]; intros; cbn in *; auto. Qed.

Lemma power_iter2 x y :
  x ^ y = iter2 mult 1 x y.
Proof. rewrite iter2_power. rewrite <- pow_tail_pow_aux. cbn. omega. Qed.


Lemma Power_WRealise :
  Power ⊫ Computes2_Rel ltac:(getFin 0) ltac:(getFin 1) ltac:(getFin 0) _ _ _ pow.
Proof.
  eapply Computes2_Ext_WRealise.
  - apply power_iter2.
  - unfold Power. apply Iter2_Computes.
    + intros H. inv H.
    + apply Mult_WRealise.
Qed.

*)