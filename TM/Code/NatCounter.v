(*
 * This machines differ from those of [MatchNat.v] only, that the tape content isn't altered,
 * only the position of the head changes.  The advantage is that we don't have to copy the value
 * if we want to use it again after destructing.
 *)

Require Import TM.Code.CodeTM.
Require Import TM.Code.MatchNat.
Require Import TM.Basic.Mono.
Require Import TM.Combinators.Combinators.
Require Import TM.Compound.TMTac.
Require Import TM.Code.Copy.
Require Import TM.LiftMN.


(** Basic stuff that has something to do with the encoding of natural numbers *)

Lemma app_comm_cons' (A : Type) (x y : list A) (a : A) :
  x ++ a :: y = (x ++ [a]) ++ y.
Proof. rewrite <- app_assoc. cbn. trivial. Qed.


Lemma map_repeat (X Y : Type) (f : X -> Y) (n : nat) (a : X) :
  map f (repeat a n) = repeat (f a) n.
Proof. induction n; cbn in *; f_equal; auto. Qed.

Lemma repeat_add_app (X : Type) (m n : nat) (a : X) :
  repeat a (m + n) = repeat a m ++ repeat a n.
Proof. induction m; cbn; f_equal; auto. Qed.

Lemma repeat_S_cons (X : Type) (n : nat) (a : X) :
  a :: repeat a n = repeat a n ++ [a].
Proof.
  replace (a :: repeat a n) with (repeat a (S n)) by trivial. replace (S n ) with (n+1) by omega.
  rewrite repeat_add_app. cbn. trivial.
Qed.

Lemma repeat_app_eq (X : Type) (m n : nat) (a : X) :
  repeat a n ++ repeat a m = repeat a m ++ repeat a n.
Proof. rewrite <- !repeat_add_app. f_equal. omega. Qed.

Lemma repeat_eq_iff (X : Type) (n : nat) (a : X) x :
  x = repeat a n <-> length x = n /\ forall y, y el x -> y = a.
Proof.
  split.
  {
    intros ->. split. apply repeat_length. apply repeat_spec.
  }
  {
    revert x. induction n; intros x (H1&H2); cbn in *.
    - destruct x; cbn in *; congruence.
    - destruct x; cbn in *; inv H1. f_equal.
      + apply H2. auto.
      + apply IHn. auto.
  }
Qed.

Lemma rev_repeat (X : Type) (n : nat) (a : X) :
  rev (repeat a n) = repeat a n.
Proof.
  apply repeat_eq_iff. split.
  - rewrite rev_length. rewrite repeat_length. auto.
  - intros y Hx % in_rev. eapply repeat_spec; eauto.
Qed.


Lemma encode_nat_correct (n : nat) :
  encode n = repeat true n ++ [false].
Proof. induction n; cbn in *; f_equal; auto. Qed.


Definition counterIs_rest' (t : tape (bool^+)) (m n k : nat) r1 r2 :=
  m = n + k /\
  left t = repeat (inr true) k ++ inl START :: r1 /\
  tape_local t = repeat (inr true) n ++ inr false :: inl STOP :: r2.

Definition counterIs_rest (t : tape (bool^+)) (m n : nat) r1 r2 :=
  exists k, counterIs_rest' t m n k r1 r2.

Definition counterIs (t : tape (bool^+)) (m n : nat) :=
  exists r1 r2, counterIs_rest t m n r1 r2.


Lemma counter_le (t : tape (bool^+)) (m n : nat) r1 r2 :
  counterIs_rest t m n r1 r2 -> n <= m.
Proof. intros (k&->&_&_). omega. Qed.

Lemma counterIs_rest_injective (t1 t2 : tape (bool^+)) (m n : nat) r1 r2 :
  counterIs_rest t1 m n r1 r2 -> counterIs_rest t2 m n r1 r2 -> t1 = t2.
Proof.
  intros (k&H1&H2&H3) (k'&H4&H5&H6). assert (k = k') as <- by omega. subst. clear H4.
  destruct n as [ | n'] eqn:En; cbn in *.
  - eapply midtape_tape_local_cons in H3 as ->. eapply midtape_tape_local_cons in H6 as ->.
    unfold finType_CS in *. now rewrite H2, H5.
  - eapply midtape_tape_local_cons in H3 as ->. eapply midtape_tape_local_cons in H6 as ->.
    unfold finType_CS in *. now rewrite H2, H5.
Qed.


Lemma tape_encodes_l_natCounterIsM (t : tape (bool^+)) (m : nat) r1 r2 :
  tape_encodes_l _ t m r1 r2 <-> counterIs_rest t m m r1 r2.
Proof.
  split.
  {
    intros (H1&H2). hnf. exists 0. repeat split.
    - omega.
    - cbn. auto.
    - cbn [Encode_Map encode] in H2. rewrite encode_nat_correct in H2.
      rewrite map_app, <- app_assoc, map_repeat in H2. cbn in H2. auto.
  }
  {
    intros (k&Hk&H1&H2). assert (k=0) as -> by omega. clear Hk.
    hnf. split.
    - cbn in H1. auto.
    - cbn [Encode_Map encode]. rewrite encode_nat_correct.
      rewrite map_app, map_repeat, <- app_assoc. cbn. auto.
  }
Qed.


Lemma tape_encodes_r_natCounterIs0 (t : tape (bool^+)) (m : nat) r1 r2 :
  tape_encodes_r _ t m r1 r2 <-> counterIs_rest t m 0 r1 r2.
Proof.
  split.
  {
    intros (H1&H2). hnf.
    cbn [Encode_Map encode] in H2. rewrite encode_nat_correct in H2.
    rewrite <- map_rev, rev_app_distr, rev_repeat, map_app, <- app_assoc, map_repeat in H2. cbn in H2.
    apply tape_local_l_cons_iff in H2 as (H2&H3).
    exists m. repeat split.
    - auto.
    - cbn. now apply tape_local_cons_iff.
  }
  {
    intros (k&Hk&H1&H2). assert (k=m) as -> by omega. clear Hk.
    apply tape_local_cons_iff in H2 as (H2&H3).
    hnf. split.
    - auto.
    - cbn [Encode_Map encode]. rewrite encode_nat_correct.
      rewrite <- map_rev, rev_app_distr, rev_repeat, map_app, <- app_assoc, map_repeat. cbn.
      now apply tape_local_l_cons_iff.
  }
Qed.


Definition CountDown_Rel : Rel (tapes bool^+ 1) (bool * tapes bool^+ 1) :=
  Mk_R_p (if? (fun tin tout =>
                 forall (m n : nat) r1 r2,
                   counterIs_rest tin m n r1 r2 ->
                   exists n' : nat, n = S n' /\
                             counterIs_rest tout m n' r1 r2)
              ! (fun tin tout =>
                   forall (m n : nat) r1 r2,
                     counterIs_rest tin m n r1 r2 ->
                     n = 0 /\ tout = tin)).

Definition CountDown : { M : mTM bool^+ 1 & states M -> bool } :=
  MATCH (Read_char _)
        (fun o => match o with
               | Some (inr  true) => Move _ R true  (* S *)
               | Some (inr false) => mono_Nop _ false (* O *)
               | _ => mono_Nop _ default (* undefined (pointer is on [START] or [STOP]) *)
               end).

Lemma CountDown_Sem : CountDown ⊨c(3) CountDown_Rel.
Proof.
  eapply RealiseIn_monotone.
  { unfold CountDown. repeat TM_Correct. }
  { Unshelve. 4,7: constructor. all: omega. }
  {
    intros tin (yout, tout) H. hnf. TMSimp. clear_trivial_eqs.
    destruct h1; TMSimp; clear_trivial_eqs.
    - hnf in H. TMSimp. hnf in H. TMSimp. now apply app_cons_not_nil in H.
    - hnf in H. TMSimp. hnf in H. TMSimp. now apply app_cons_not_nil in H.
    - hnf in H. TMSimp. hnf in H. TMSimp. now apply app_cons_not_nil in H0.
    - destruct e; TMSimp.
      + destruct b; TMSimp; hnf in H; TMSimp; hnf in H; TMSimp; destruct n as [ | n']; cbn in *; inv H0.
      + destruct b; TMSimp; hnf in H; TMSimp; hnf in H; TMSimp; destruct n as [ | n']; cbn in *; inv H0.
        * exists n'. split; auto. hnf. eexists. split. eauto. simpl_tape. eauto.
        * split; auto.
  }
Qed.

Definition Reset_Rel : Rel (tapes bool^+ 1) (unit * tapes bool^+ 1) :=
  Mk_R_p (ignoreParam (
              fun tin tout =>
                forall m n r1 r2,
                  counterIs_rest tin m n r1 r2 ->
                  counterIs_rest tout m m r1 r2
         )).

Local Definition stop : (bool^+) -> bool := stop (@dontStop _). (* halt only at [START] or [STOP] *)

Definition Reset : { M : mTM (bool^+) 1 & states M -> unit } :=
  MoveToSymbol_L stop;; Move _ R tt.

Lemma Reset_WRealises : Reset ⊫ Reset_Rel.
Proof.
  eapply WRealise_monotone.
  { unfold Reset. repeat TM_Correct. }
  {
    intros tin ((), tout) H. intros m n r1 r2 HCount. TMSimp. clear_trivial_eqs. clear H1.
    hnf. cbn. exists 0. split. omega. cbn.
    hnf in HCount. destruct HCount as (k&->&H1&H2) .
    unfold finType_CS in *. cbn in *.
    rewrite repeat_add_app, <- app_assoc.

    destruct n as [ | n'] eqn:En; cbn in *.
    - apply tape_local_cons_iff in H2 as (H2&H3).
      assert (tape_local_l h0 = (inr false :: repeat (inr true) k) ++ inl START :: r1) as L1
          by (cbn; eapply tape_local_l_cons_iff; eauto).
      unfold finType_CS in *.
      unshelve epose proof (MoveToSymbol_L_correct (stop := stop) _ _ L1) as L2.
      + intros ? [<- | -> % repeat_spec]; cbv; trivial.
      + cbv. trivial.
      + cbn in *. rewrite rev_repeat, <- !app_assoc in L2.
        unfold finType_CS in *. rewrite L2, H3. cbn. simpl_tape. auto.
    - apply tape_local_cons_iff in H2 as (H2&H3).
      assert (tape_local_l h0 = (inr true :: repeat (inr true) k) ++ inl START :: r1) as L1
          by (cbn; eapply tape_local_l_cons_iff; eauto).
      unfold finType_CS in *.
      unshelve epose proof (MoveToSymbol_L_correct (stop := stop) _ _ L1) as L2.
      + intros ? [<- | -> % repeat_spec]; cbv; trivial.
      + cbv. trivial.
      + cbn in *. rewrite rev_repeat, <- !app_assoc in L2.
        unfold finType_CS in *. rewrite L2, H3. cbn. simpl_tape. split; auto.
        rewrite !app_comm_cons. rewrite !app_assoc. f_equal.
        rewrite app_comm_cons'. rewrite <- repeat_S_cons. rewrite <- !app_comm_cons. f_equal. apply repeat_app_eq.
  }
Qed.


Lemma Reset_Terminates :
  projT1 Reset ↓ (fun tin i => exists m n k r1 r2, counterIs_rest' tin[@Fin.F1] m n k r1 r2 /\ 10 + 4 * k <= i).
Proof.
  eapply TerminatesIn_monotone.
  { unfold Reset. repeat TM_Correct. }
  {
    intros tin i (m&n&k&r1&r&(->&H1&H2)&Hi).
    destruct n as [ | n'] eqn:En; cbn [Nat.eqb] in Hi; cbn in H2; apply tape_local_cons_iff in H2 as (H2&H3).
    {
      exists (4 + 4 + 4 * k), 1. repeat split.
      - cbn. omega.
      - apply (conj H2) in H1. apply tape_local_l_cons_iff in H1. (* Nice trick, not? *)
        rewrite app_comm_cons in H1.
        epose proof MoveToSymbols_TermTime_local_l (stop := stop) H1 ltac:(auto).
        cbn [length] in H. rewrite repeat_length in H. omega.
      - intros ? ? ?. omega.
    }
    {
      exists (4 + 4 + 4 * k), 1. repeat split.
      - omega.
      - apply (conj H2) in H1. apply tape_local_l_cons_iff in H1. (* Nice trick, not? *)
        rewrite app_comm_cons in H1.
        epose proof MoveToSymbols_TermTime_local_l (stop := stop) H1 ltac:(auto).
        cbn [length] in H. rewrite repeat_length in H. omega.
      - intros ? ? ?. omega.
    }
  }
Qed.


(*
(** Tactical support *)
Arguments CountDown : simpl never.
Arguments Reset : simpl never.

Arguments CountDown_Rel x y /.
Arguments Reset_Rel x y /.
*)


(*** Machines that compte natural functions *)


Require Import Coq.Init.Nat.



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
  - cbn.  rewrite <- IH. omega.
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

  
  (* The 0th tape is the first input and doesn't change. The 1st tape is the second input and the output. *)
  Definition Computes2_Reset_Rel (f : X -> Y -> Z) : Rel (tapes (sig^+) n) (unit * tapes (sig^+) n) :=
    ignoreParam (
        fun tin tout =>
          forall (x : X) (y : Y),
            tin[@i1] ≂ x ->
            tin[@i2] ≂ y ->
            tout[@i1] = tin[@i1] /\
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


(** * First-order [nat] iteration machines *)

Section Iter1.

  Variable f : nat -> nat.

  (* [x] is the accu. We iterate over [y]. *)
  Fixpoint iter (x y : nat) {struct x} : nat :=
    match x with
    | 0 => y
    | S x' => iter x' (f y)
    end.

  Variable M1 : { M : mTM (bool^+) 1 & states M -> unit }.
  Hypothesis M1_computes : M1 ⊫ Computes_Rel Fin.F1 Fin.F1 _ _ f.

  Definition Iter_Step : { M : mTM _ 2 & states M -> bool * unit } :=
    If (Inject CountDown [|Fin0|])
       (Return (Inject M1 [|Fin1|]) (true, tt))
       (Nop _ _ (false, tt)).

  
  Definition Iter : { M : mTM _ 2 & states M -> unit } := WHILE Iter_Step.

  Definition Iter_Reset := Iter;; Inject Reset [|Fin0|].
  

  (** Correctness *)

  
  Definition Iter_Step_Rel : Rel (tapes (bool^+) 2) ((bool * unit) * tapes (bool^+) 2) :=
    ignoreSecond (
        if? (fun tin tout =>
               forall m m' n r1 r2,
                 counterIs_rest tin[@Fin0] m m' r1 r2 ->
                 tin[@Fin1] ≂ n ->
                 exists m'', m' = S m'' /\
                        counterIs_rest tout[@Fin0] m m'' r1 r2 /\
                        tout[@Fin1] ≂ f n)
            ! (fun tin tout =>
                 forall m m' n r1 r2,
                   counterIs_rest tin[@Fin0] m m' r1 r2 ->
                   tin[@Fin1] ≂ n ->
                   m' = 0 /\ tout = tin)
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
      - specialize (H _ _ _ _ H2) as (n''&->&H). eexists. repeat split; eauto.
      - specialize (H _ _ _ _ H0) as (->&H). eexists. repeat split. repeat f_equal. auto.
    }
  Qed.


  Definition Iter_Rel : Rel (tapes bool^+ 2) (unit * tapes bool^+ 2) :=
    ignoreParam (
        fun tin tout =>
          forall m m' n r1 r2,
            counterIs_rest tin[@Fin0] m m' r1 r2 ->
            tin[@Fin1] ≂ n ->
            counterIs_rest tout[@Fin0] m 0 r1 r2 /\
            tout[@Fin1] ≂ iter m' n
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

  Lemma Iter_Computes : Iter ⊫ Computes2_Rel Fin0 Fin1 Fin1 _ _ _ iter.
  Proof.
    eapply WRealise_monotone. apply Iter_WRealise.
    intros tin ((), tout) H. intros m n HEncM HEncN. hnf in H.
    destruct HEncM as (r1&r2&HEncM % tape_encodes_l_natCounterIsM).
    now specialize (H m m n r1 r2 HEncM HEncN) as (?&?).
  Qed.

  Definition Iter_Reset_Rel : Rel (tapes bool^+ 2) (unit * tapes bool^+ 2) :=
    ignoreParam (
        fun tin tout =>
          forall m m' n r1 r2,
            counterIs_rest tin[@Fin0] m m' r1 r2 ->
            tin[@Fin1] ≂ n ->
            counterIs_rest tout[@Fin0] m m r1 r2 /\
            tout[@Fin1] ≂ iter m' n
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
      specialize (H2 _ _ _ _ H1). split; auto.
  Qed.

  Lemma Iter_Reset_Computes : Iter_Reset ⊫ Computes2_Reset_Rel Fin0 Fin1 _ _ _ iter.
  Proof.
    eapply WRealise_monotone. eapply Iter_Reset_WRealise.
    intros tin ((), tout) H. intros m n HEncM HEncN. hnf in H.
    destruct HEncM as (r1 & r2 & HEncM % tape_encodes_l_natCounterIsM).
    specialize (H _ _ _ _ _ HEncM HEncN) as (H1&H2). split; auto.
    eapply counterIs_rest_injective in H1; eauto.
  Qed.


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

End Iter1.


Lemma add_steps : forall m n, Iter_steps S (fun _ => 5) m n = 4 + 10 * m.
Proof.
  intros m n. revert n. induction m as [ | m' IH]; intros; cbn -[plus mult] in *.
  - omega.
  - rewrite IH. omega.
Qed.

Definition Add := Iter_Reset Constr_S.

Lemma tail_add_iter (m n : nat) :
  tail_plus m n = iter S m n.
Proof.
  revert n. induction m; intros; cbn in *.
  omega. rewrite IHm. omega.
Qed.

Lemma Add_WRealise' :
  Add ⊫ Computes2_Reset_Rel Fin0 Fin1 _ _ _ tail_plus.
Proof.
  eapply Computes2_Reset_Ext_WRealise.
  - refine tail_add_iter.
  - unfold Add. apply Iter_Reset_Computes.
    eapply WRealise_monotone. 
    + eapply RealiseIn_WRealise. apply Constr_S_Sem.
    + intros tin ((), tout) H. hnf in *. auto.
Qed.

Lemma Add_WRealise :
  Add ⊫ Computes2_Reset_Rel Fin0 Fin1 _ _ _ plus.
Proof.
  eapply Computes2_Reset_Ext_WRealise.
  - apply plus_tail_plus.
  - apply Add_WRealise'.
Qed.


Definition add_step_count x := 15 + 14 * x.

Lemma Add_Terminates :
  projT1 Add ↓ (fun tin i => exists x y, tin[@Fin.F1] ≂ x /\ tin[@Fin.FS Fin.F1] ≂ y /\ add_step_count x <= i).
Proof.
  unfold add_step_count. eapply TerminatesIn_monotone.
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

  Compute execTM_p Add (add_step_count 0) [|t0; t0|].
  Compute execTM_p Add (add_step_count 0) [|t0; t4|].
  Compute execTM_p Add (add_step_count 1) [|t1; t3|].
  Compute execTM_p Add (add_step_count 2) [|t2; t3|].
  Compute execTM_p Add (add_step_count 3) [|t3; t3|].
  Compute execTM_p Add (add_step_count 3) [|t3; t4|].
  Compute execTM_p Add (add_step_count 4) [|t4; t0|].
End Test.
*)


Section Iter2.

  Variable f : nat -> nat -> nat.

  Definition iter2 (s x y : nat) := iter (fun z => f y z) x s.

  Fixpoint tail_iter2 (s x y : nat) {struct x} : nat :=
    match x with
    | O => s
    | S x' => tail_iter2 (f y s) x' y
    end.

  Lemma tail_iter2_iter2 (s x y : nat) :
    iter2 s x y = tail_iter2 s x y.
  Proof. revert s. induction x as [ | x' IH]; intros; cbn in *; eauto. Qed.

  
  Variable n : nat.
  Variable M1 : { M : mTM (bool^+) n & states M -> unit }.
  Variable (i1 i2 : Fin.t n).
  Hypothesis i_disj: i1 <> i2.
  Hypothesis M1_computes : M1 ⊫ Computes2_Reset_Rel i1 i2 _ _ _ f.

  Local Definition indexes_M1 : Vector.t (Fin.t (S n)) n :=
    Vector.map (fun k => Fin.FS k) (Fin_initVect _).


  (* TODO: automatisate these lemmas... *)

  Local Lemma indexes_M1_dupfree : dupfree indexes_M1.
  Proof.
    apply dupfree_map_injective.
    - now intros k1 k2 H % Fin.FS_inj.
    - apply Fin_initVect_dupfree.
  Qed.

  Local Lemma indexes_M1_notIn_Fin0 : not_indexes indexes_M1 Fin0.
  Proof. unfold indexes_M1. intros (k&H1&H2) % vect_in_map_iff. inv H1. Qed.

  Local Lemma indexes_M1_reorder_nth (X : Type) (ts : Vector.t X (S n)) k :
    (reorder indexes_M1 (ts))[@k] = ts[@Fin.FS k].
  Proof.
    unfold indexes_M1. unfold reorder. erewrite !VectorSpec.nth_map; eauto.
    cbn. now rewrite Fin_initVect_nth.
  Qed.

  Local Lemma i1_notIn_0_i2 : not_indexes [|Fin.F1; Fin.FS i2|] (Fin.FS i1).
  Proof.
    intros H.
    apply In_cons in H as [? | ?]; try congruence.
    apply In_cons in H as [? | ?]; try congruence.
    apply Fin.FS_inj in H. subst. auto. inv H.
  Qed.

  Local Lemma i1_notIn_i2 : not_indexes [|Fin.FS i2|] (Fin.FS i1).
  Proof.
    intros [H % Fin.FS_inj | H] % In_cons; auto. inv H.
  Qed.


  Definition Iter2_Step : { M : mTM (bool^+) (S n) & states M -> bool * unit } :=
    If (Inject CountDown [|Fin0|])
       (Return (Inject M1 indexes_M1) (true, tt))
       (Nop _ _ (false, tt)).


  (* The step function has three inputs and three outputs. *)
  Definition Iter2_Step_Rel : Rel (tapes (bool^+) (S n)) ((bool * unit) * tapes (bool^+) (S n)) :=
    ignoreSecond (
        if? (fun tin tout => (* case S *)
               forall (x x' y s : nat) r1 r2,
                 counterIs_rest tin[@Fin0] x x' r1 r2 ->
                 tin[@Fin.FS i1] ≂ y ->
                 tin[@Fin.FS i2] ≂ s ->
                 exists x'', x' = S x'' /\
                        counterIs_rest tout[@Fin0] x x'' r1 r2 /\ (* Tape 0 counted down *)
                        tout[@Fin.FS i1] = tin[@Fin.FS i1] /\ (* This tape never changes *)
                        tout[@Fin.FS i2] ≂ f y s
            )
          ! (fun tin tout => (* case O *)
               forall (x x' y s : nat) r1 r2,
                 counterIs_rest tin[@Fin0] x x' r1 r2 ->
                 tin[@Fin.FS i1] ≂ y ->
                 tin[@Fin.FS i2] ≂ s ->
                 x' = 0 /\
                 tout[@Fin0] = tin[@Fin0] /\
                 tout[@Fin.FS i1] = tin[@Fin.FS i1] /\ (* This tape never changes *)
                 tout[@Fin.FS i2] = tin[@Fin.FS i2]
            )
      ).

  Lemma Iter2_Step_WRealise :
    Iter2_Step ⊫ Iter2_Step_Rel.
  Proof.
    unfold Iter2_Step_Rel. eapply WRealise_monotone.
    {
      unfold Iter2_Step. repeat TM_Correct.
      - eapply RealiseIn_WRealise. apply CountDown_Sem.
      - apply Inject_WRealise.
        + apply indexes_M1_dupfree.
        + apply M1_computes.
    }
    {
      intros tin ((b, ()), tout) H. cbn in *. destruct H; cbn in *.
      - destruct H as (tmid & (H1 & H2) & H3 & H4). destruct H4 as (() & H4&H5). inv H3.
        intros x x' y s r1 r2 HEncX HEncY HEncS. 
        specialize (H1 _ _ _ _ HEncX) as (x''&->&H1). eexists. split. eauto.
        pose proof (H5 Fin0 indexes_M1_notIn_Fin0) as <-. split. auto.
        pose proof (H2 (Fin.FS i1) ltac:(vector_not_in)) as L. cbn in L. rewrite L in *. clear L.
        pose proof (H2 (Fin.FS i2) ltac:(vector_not_in)) as L. cbn in L. rewrite L in *. clear L.
        rewrite !indexes_M1_reorder_nth in H4. specialize (H4 y s HEncY HEncS) as (HComp1&HComp2). auto.
      - destruct H as (tmid & (H1 & H2) & H3 & ->). inv H3.
        intros x x' y s r1 r2 HEncX HEncY HEncS. 
        specialize (H1 _ _ _ _ HEncX) as (->&H1). split. auto. split. auto.
        pose proof (H2 (Fin.FS i1) ltac:(vector_not_in)) as L. cbn in L. rewrite L in *. clear L.
        pose proof (H2 (Fin.FS i2) ltac:(vector_not_in)) as L. cbn in L. rewrite L in *. clear L.
        auto.
    }
  Qed.
  

  Definition Iter2_Loop := WHILE Iter2_Step.

  Definition Iter2_Loop_Rel : Rel (tapes (bool^+) (S n)) (unit * tapes (bool^+) (S n)) :=
    ignoreParam (
        fun tin tout =>
          forall (x x' y s : nat) r1 r2,
            counterIs_rest tin[@Fin0] x x' r1 r2 ->
            tin[@Fin.FS i1] ≂ y ->
            tin[@Fin.FS i2] ≂ s ->
            counterIs_rest tout[@Fin0] x 0 r1 r2 /\
            tout[@Fin.FS i1] = tin[@Fin.FS i1] /\
            tout[@Fin.FS i2] ≂ tail_iter2 s x' y
      ).

  Lemma Iter2_Loop_WRealise :
    Iter2_Loop ⊫ Iter2_Loop_Rel.
  Proof.
    eapply WRealise_monotone.
    {
      unfold Iter2_Loop. repeat TM_Correct. apply Iter2_Step_WRealise.
    }
    {
      intros tin ((), tout) H. intros x x' y s r1 r2 HEncX HEncY HEncS .
      cbn in H. destruct H as (tmid2&HStar&HLastStep).
      revert s HEncS x' HEncX y HEncY.
      induction HStar as [ tin | tin tmid1 tmid2 HStar _ IH]; intros.
      - specialize (HLastStep _ _ _ _ _ _ HEncX HEncY HEncS) as (->&->&->&->). auto.
      - spec_assert IH; eauto. cbn in HStar. destruct HStar as (()&HStar).
        specialize (HStar _ _ _ _ _ _ HEncX HEncY HEncS) as (x''&->&HS1&HS2&HS3).
        specialize (IH _ HS3).
        unfold finType_CS in *. rewrite <- !HS2 in *.
        specialize (IH _ HS1).
        specialize (IH _ HEncY) as (IH1&IH2&IH3). cbn. auto.
    }
  Qed.

  Definition Iter2 (s : nat) : { M : mTM (bool^+) (S n) & states M -> unit } :=
    Inject (InitTape _ s) [|Fin.FS i2|];; (* Write [s] to the tape for [s] *)
    Iter2_Loop. (* Execute the loop. *)


  Lemma Iter2_Computes' (s : nat) : Iter2 s ⊫ Computes2_Rel Fin0 (Fin.FS i1) (Fin.FS i2) _ _ _ (tail_iter2 s).
  Proof.
    eapply WRealise_monotone.
    {
      unfold Iter2. repeat TM_Correct.
      - eapply RealiseIn_WRealise. apply InitTape_Sem.
      - apply Iter2_Loop_WRealise.
    }
    {
      intros tin ((), tout) H. intros x y HEncX HEncY.
      cbn in H. destruct H as ((()&tmid)&(HEncS&HInject)&H). cbn in *.
      pose proof (HInject Fin0 ltac:(vector_not_in)) as L1. rewrite <- L1 in *. clear L1.
      pose proof (HInject (Fin.FS i1) i1_notIn_i2) as L1. rewrite <- L1 in *. clear L1.
      destruct HEncX as (r1&r2&HEncX % tape_encodes_l_natCounterIsM).
      now specialize (H _ _ _ _ _ _ HEncX HEncY HEncS) as (HComp1&HComp2&HComp3).
    }
  Qed.

  Lemma Iter2_Computes (s : nat) : Iter2 s ⊫ Computes2_Rel Fin0 (Fin.FS i1) (Fin.FS i2) _ _ _ (iter2 s).
  Proof. eapply Computes2_Ext_WRealise. apply tail_iter2_iter2. apply Iter2_Computes'. Qed.


  (** Termination *)

  Variable M1_runtime : nat -> nat -> nat.
  Hypothesis M1_terminates : projT1 M1 ↓ (fun tin k => exists a b, tin[@i1] ≂ a /\ tin[@i2] ≂ b /\ M1_runtime a b <= k).


  Lemma Iter2_Step_Terminates :
    projT1 Iter2_Step ↓ (fun tin i => exists s x x' y r1 r2,
                             counterIs_rest tin[@Fin0] x x' r1 r2 /\
                             tin[@Fin.FS i1] ≂ y /\
                             tin[@Fin.FS i2] ≂ s /\
                             match x' with
                             | O => 4
                             | S _ => 4 + M1_runtime y s
                             end <= i).
  Proof.
    eapply TerminatesIn_monotone.
    {
      unfold Iter2_Step. repeat TM_Correct. 
      - eapply RealiseIn_WRealise. apply CountDown_Sem.
      - eapply RealiseIn_terminatesIn. apply CountDown_Sem.
      - apply Inject_Terminates.
        + apply indexes_M1_dupfree.
        + apply M1_terminates.
    }
    {
      intros tin i. intros (s&x&x'&y&r1&r2&HEncX&HEncY&HEncS&Hi).
      destruct x' as [ | x''] eqn:En'.
      - exists 3, 0. repeat split.
        + omega.
        + cbn. omega.
        + intros tout b H. cbn in H. destruct b; cbn.
          * destruct H as (HComp&HInject). rewrite !indexes_M1_reorder_nth.
            specialize (HComp _ _ _ _ HEncX) as (?&?&_). exfalso; congruence.
          * omega.
      - exists 3, (M1_runtime y s). repeat split.
        + omega.
        + cbn. omega.
        + intros tout b H. cbn in H. destruct b; cbn.
          * destruct H as (HComp&HInject). rewrite !indexes_M1_reorder_nth.
            specialize (HComp _ _ _ _ HEncX) as (?&H&_). inv H.
            pose proof (HInject (Fin.FS i1) ltac:(vector_not_in)) as L1; rewrite <- L1 in *; clear L1.
            pose proof (HInject (Fin.FS i2) ltac:(vector_not_in)) as L1; rewrite <- L1 in *; clear L1.
            eauto.
          * omega.
    }
  Qed.
  
  Fixpoint Iter2_steps (a x y : nat) { struct x } : nat :=
    match x with
    | O => 4
    | S x' => 5 + M1_runtime y a + Iter2_steps (f y a) x' y
    end.

  Lemma Iter2_steps_ge4 (a x y : nat) :
    4 <= Iter2_steps a x y.
  Proof. destruct x; cbn; omega. Qed.

  Lemma Iter2_steps_homogene (a x y k : nat) :
    (forall z, M1_runtime y z <= k) ->
    Iter2_steps a x y <= 4 + (5 + k) * x.
  Proof.
    revert a y. induction x as [ | x' IH]; intros; cbn -[add mult] in *.
    - omega.
    - specialize (IH (f y a) y H). pose proof (H (f y a)) as H1. pose proof (H a) as H2.
      rewrite !Nat.mul_succ_r.
      rewrite !Nat.mul_add_distr_r in *.
      rewrite !Nat.add_assoc in *.
      omega. (* Oh [omega], my dear [omega]! *)
  Qed.

  Lemma Iter2_steps_homogene' (a x y k : nat) :
    (forall z, M1_runtime y z = k) ->
    Iter2_steps a x y = 4 + (5 + k) * x.
  Proof.
    revert a y. induction x as [ | x' IH]; intros; cbn -[add mult] in *.
    - omega.
    - specialize (IH (f y a) y H). pose proof (H (f y a)) as H1. pose proof (H a) as H2.
      rewrite !Nat.mul_succ_r.
      rewrite !Nat.mul_add_distr_r in *.
      rewrite !Nat.add_assoc in *.
      omega. (* Oh [omega], my dear [omega]! *)
  Qed.

  Lemma Iter2_Loop_Terminates :
    projT1 Iter2_Loop ↓ (fun tin i => exists (s x x' y : nat) r1 r2, 
                        counterIs_rest tin[@Fin0] x x' r1 r2 /\
                        tin[@Fin.FS i1] ≂ y /\
                        tin[@Fin.FS i2] ≂ s /\
                        Iter2_steps s x' y <= i).
  Proof.
    unfold Iter2_Loop. repeat TM_Correct.
    { apply Iter2_Step_WRealise. }
    { eapply Iter2_Step_Terminates. }
    {
      intros tin i (s&x&x'&y&r1&r2&HEncM&HEncN&HEncS&Hi).
      destruct x'.
      - eexists. repeat split.
        + do 5 eexists. repeat split; cbn; eauto.
        + intros b () tout H. cbn in H; destruct b; cbn in *; auto.
          exfalso. specialize (H _ _ _ _ _ _ HEncM HEncN HEncS) as (n''&?&?). congruence.
      - eexists. repeat split.
        + do 5 eexists. repeat split; cbn -[add mult]; eauto.
        + intros b () tout H. cbn -[add mult] in H; destruct b; cbn -[add mult] in *; auto.
          * specialize (H _ _ _ _ _ _ HEncM HEncN HEncS) as (n''&H1&H2&H3&H4). inv H1. rewrite H3.
            eexists. repeat split.
            -- do 6 eexists. repeat split; eauto.
            -- omega.
          * specialize (H _ _ _ _ _ _ HEncM HEncN HEncS) as (H1&H2). inv H1.
    }
  Qed.


  Lemma Iter2_Terminates' (s : nat) : 
    projT1 (Iter2 s) ↓ (fun tin i => exists (x x' y : nat) r1 r2, 
                            counterIs_rest tin[@Fin0] x x' r1 r2 /\
                            tin[@Fin.FS i1] ≂ y /\
                            17 + 4 * s + Iter2_steps s x' y <= i).
  Proof.
    eapply TerminatesIn_monotone.
    {
      unfold Iter2. repeat TM_Correct.
      - eapply RealiseIn_WRealise. apply InitTape_Sem.
      - eapply RealiseIn_terminatesIn. apply InitTape_Sem.
      - apply Iter2_Loop_Terminates.
    }
    {
      intros tin i. intros (x&x'&y&r1&r2&HEncX&HEncY&Hi).
      exists (16 + 4 * s), (Iter2_steps s x' y). repeat split.
      - omega.
      - rewrite encode_nat_correct. cbn -[add mult]. rewrite app_length. rewrite repeat_length. cbn [length]. omega.
      - intros tout (). cbn. intros (HEncS&HInject).
        pose proof (HInject Fin0 ltac:(vector_not_in)) as L1. rewrite <- L1 in *. clear L1.
        pose proof (HInject (Fin.FS i1) i1_notIn_i2) as L1. rewrite <- L1 in *. clear L1.
        do 6 eexists. repeat split; eauto.
    }
  Qed.

  Lemma Iter2_Terminates (s : nat) :
    projT1 (Iter2 s) ↓ (fun tin k => exists x y, tin[@Fin0] ≂ x /\ tin[@Fin.FS i1] ≂ y /\ 17 + 4 * s + Iter2_steps s x y <= k).
  Proof.
    eapply TerminatesIn_monotone. eapply Iter2_Terminates'. intros tin i (x&y&HEncX&HEncY&Hi).
    destruct HEncX as (r1&r2&HEncX % tape_encodes_l_natCounterIsM). do 5 eexists. repeat split; eauto; omega.
  Qed.

End Iter2.


(** Define and Instantiate Mult *)


Definition Mult := Iter2 Add Fin1 0.

Lemma iter2_mult s x y :
  iter2 plus s x y = tail_mult_acc s x y.
Proof.
  rewrite tail_iter2_iter2.
  revert s. induction x as [ | x' IH]; intros; cbn in *; auto.
  rewrite IH. f_equal. omega.
Qed.

Lemma mult_iter2 x y :
  x * y = iter2 plus 0 x y.
Proof. rewrite iter2_mult. rewrite <- mult_tail_mult_aux. cbn. omega. Qed.

Lemma Mult_WRealise :
  Mult ⊫ Computes2_Rel Fin0 Fin1 Fin2 _ _ _ mult.
Proof.
  eapply Computes2_Ext_WRealise.
  - apply mult_iter2.
  - unfold Mult. apply Iter2_Computes with (i1 := Fin0) (i2 := Fin1).
    + intros H. inv H.
    + apply Add_WRealise.
Qed.


Definition mult_step_count x y := 21 + (20 + 14 * y) * x.

Lemma mult_steps x y :
  17 + 4 * 0 + Iter2_steps add (fun x0 _ : nat => add_step_count x0) 0 x y = mult_step_count x y.
Proof.
  rewrite Iter2_steps_homogene' with (k := 15 + 14 * y); swap 1 2.
  - intros. unfold add_step_count. trivial.
  - rewrite !Nat.add_assoc. cbn. omega. (* Thanks, [omega] ! *)
Qed.


Lemma Mult_Terminates :
  projT1 Mult ↓ (fun tin i => exists x y, tin[@Fin0] ≂ x /\ tin[@Fin1] ≂ y /\ mult_step_count x y <= i).
Proof.
  eapply TerminatesIn_monotone.
  - unfold Mult. eapply Iter2_Terminates with (i1 := Fin0).
    + congruence.
    + eapply Add_WRealise.
    + eapply Add_Terminates.
  - intros tin i (x&y&HEncX&HEncY&Hk). do 2 eexists. split. eauto. split. eauto. rewrite <- Hk. apply Nat.eq_le_incl.
    apply mult_steps.
Qed.





(* To define power, [Mult] has to reset the value [m], like [Add]; and the result must be copied to the tape of [n]. *)


(*
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