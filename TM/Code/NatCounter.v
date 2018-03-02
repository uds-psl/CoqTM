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



(** Addition *)


(* Adittion is basically just copying the second value onto the first value *)

Definition Add_Step : { M : mTM (bool^+) 2 & states M -> bool * unit } :=
  If (Inject CountDown [|Fin.FS Fin.F1|])
     (Return (Inject (Constr_S) [|Fin.F1|]) (true, tt))
     (Nop _ _ (false, tt)).

Definition Add_Step_Rel : Rel (tapes (bool^+) 2) ((bool * unit) * tapes (bool^+) 2) :=
  ignoreSecond (
      if? (fun tin tout =>
             forall m n n' r1 r2,
               tin[@Fin.F1] ≂ m ->
               counterIs_rest tin[@Fin.FS Fin.F1] n n' r1 r2 ->
               exists n'', n' = S n'' /\
                      tout[@Fin.F1] ≂ S m /\
                      counterIs_rest tout[@Fin.FS Fin.F1] n n'' r1 r2)
          ! (fun tin tout =>
               forall m n n' r1 r2,
                 tin[@Fin.F1] ≂ m ->
                 counterIs_rest tin[@Fin.FS Fin.F1] n n' r1 r2 ->
                 n' = 0 /\ tout = tin)
    ).


Lemma Add_Step_Sem : Add_Step ⊨c(9) Add_Step_Rel.
Proof.
  eapply RealiseIn_monotone.
  {
    unfold Add_Step. repeat TM_Correct.
    - apply CountDown_Sem.
    - apply Constr_S_Sem.
  }
  { cbn. omega. }
  {
    intros tin (yout, tout) H. TMSimp. destruct H; TMSimp inv_pair; clear_trivial_eqs.
    - specialize (H _ _ _ _ H3) as (n''&->&H). eexists. repeat split; eauto.
    - specialize (H _ _ _ _ H2) as (->&H). eexists. repeat split. repeat f_equal. auto.
  }
Qed.

Definition Add := WHILE Add_Step.

Definition Add_Rel : Rel (tapes bool^+ 2) (unit * tapes bool^+ 2) :=
  ignoreParam (
      fun tin tout =>
        forall m n n' r1 r2,
          tin[@Fin.F1] ≂ m ->
          counterIs_rest tin[@Fin.FS Fin.F1] n n' r1 r2 ->
          tout[@Fin.F1] ≂ m + n' /\
          counterIs_rest tout[@Fin.FS Fin.F1] n 0 r1 r2
    ).


Lemma Add_WRealise : Add ⊫ Add_Rel.
Proof.
  eapply WRealise_monotone.
  { unfold Add. repeat TM_Correct. eapply RealiseIn_WRealise. apply Add_Step_Sem. }
  {
    intros tin ((), tout) (tmid&HStar&HLastStep).
    induction HStar as [ tin | tin tmid1 tmid2 HStar _ IH]; intros m n n' r1 r2 H1 H2.
    - specialize (HLastStep _ _ _ _ _ H1 H2) as (HLS1&HLS2). inv HLS2.
      replace (m + 0) with m by omega. auto.
    - repeat (spec_assert IH; eauto). cbn in HLastStep, IH, HStar. destruct HStar as (()&HStar). cbn in HStar.
      specialize (HStar _ _ _ _ _ H1 H2) as (n''&->&HS1&HS2).
      specialize (IH _ _ _ _ _ HS1 HS2) as (IH1&IH2).
      clear HLastStep. rewrite <- plus_Snm_nSm. auto.
  }
Qed.

Lemma Add_Computes : Add ⊫ Computes2_Rel Fin.F1 (Fin.FS Fin.F1) Fin.F1 _ _ _ plus.
Proof.
  eapply WRealise_monotone. apply Add_WRealise.
  intros tin ((), tout) H. intros m n HEncM HEncN. hnf in H.
  destruct HEncN as (r1&r2&HEncN). apply tape_encodes_l_natCounterIsM in HEncN.
  now specialize (H m n n r1 r2 HEncM HEncN) as (?&?).
Qed.


Fixpoint Add_steps (n : nat) :=
  match n with
  | O => 9
  | S n' => 10 + Add_steps n'
  end.


Lemma Add_Terminates' :
  projT1 Add ↓ (fun tin i => exists m n n' r1 r2, 
                    tin[@Fin.F1] ≂ m /\
                    counterIs_rest tin[@Fin.FS Fin.F1] n n' r1 r2 /\
                    9 + 10 * n' <= i).
Proof.
  unfold Add. repeat TM_Correct.
  { eapply RealiseIn_WRealise. apply Add_Step_Sem. }
  { eapply RealiseIn_terminatesIn. apply Add_Step_Sem. }
  {
    intros tin i (m&n&n'&r1&r2&HEncM&HEncN&Hi).
    exists 9. repeat split. omega.
    intros b () tout H. hnf in H. destruct b.
    - specialize (H _ _ _ _ _ HEncM HEncN) as (n''&->&H1&H2).
      (* destruct H2 as (k'&H2). destruct H2 as (H2&HEncN1'&HEncN2'). assert (k' = S k) as -> by omega. clear H2. *)
      exists (9 + 10 * n''). repeat split.
      + do 6 eexists. repeat split. eauto. split. eauto. omega.
      + omega.
    - omega.
  }
Qed.


Lemma Add_Terminates :
  projT1 Add ↓ (fun tin i => exists m n, tin[@Fin.F1] ≂ m /\ tin[@Fin.FS Fin.F1] ≂ n /\ 9 + 10 * n <= i).
Proof.
  eapply TerminatesIn_monotone. eapply Add_Terminates'. intros tin i (m&n&HEncM&HEncN&Hi).
  destruct HEncN as (r1&r2&HEncN % tape_encodes_l_natCounterIsM). do 5 eexists. repeat split; eauto; omega.
Qed.




Definition Add_Reset := Add;; Inject Reset [|Fin.FS Fin.F1|].

Definition Add_Reset_Rel : Rel (tapes bool^+ 2) (unit * tapes bool^+ 2) :=
  ignoreParam (
      fun tin tout =>
        forall m n n' r1 r2,
          tin[@Fin.F1] ≂ m ->
          counterIs_rest tin[@Fin.FS Fin.F1] n n' r1 r2 ->
          tout[@Fin.F1] ≂ m + n' /\
          counterIs_rest tout[@Fin.FS Fin.F1] n n r1 r2
    ).

Lemma Add_Reset_WRealise : Add_Reset ⊫ Add_Reset_Rel.
Proof.
  eapply WRealise_monotone.
  - unfold Add_Reset. repeat TM_Correct.
    + apply Add_WRealise.
    + apply Reset_WRealises.
  - intros tin ((), tout) H. intros m n n' r1 r2 HEncM HEncN. hnf in H.
    destruct H as ((()&tmid) & H1 & H2 & H3). cbn in *. simpl_not_in. rewrite H3 in *.
    specialize (H1 _ _ _ _ _ HEncM HEncN) as (H1&H1'). rewrite <- H3 in *.
    specialize (H2 _ _ _ _ H1'). split; auto.
Qed.

Lemma Add_Reset_Terminates' :
  projT1 Add_Reset ↓ (fun tin i => exists m n n' r1 r2, 
                          tin[@Fin.F1] ≂ m /\
                          counterIs_rest tin[@Fin.FS Fin.F1] n n' r1 r2 /\
                          20 + 10 * n' + 4 * n <= i).
Proof.
  eapply TerminatesIn_monotone.
  - unfold Add_Reset. repeat TM_Correct.
    + apply Add_WRealise.
    + apply Add_Terminates'.
    + apply Reset_Terminates.
  - intros tin i (m&n&n'&r1&r2&HEncM&HEncN&Hi).
    exists (9 + 10 * n'), (10 + 4 * n). repeat split.
    + rewrite <- Hi. clear_all. apply Nat.eq_le_incl. omega.
    + do 5 eexists. repeat split. eauto. eauto. omega.
    + intros tout () H. cbn -[plus mult]. hnf in H. specialize (H _ _ _ _ _ HEncM HEncN) as (H1&H2).
      destruct H2 as (k&->&H2&H2'). do 5 eexists. repeat split. eauto. eauto. omega.
Qed.


Lemma Add_Reset_Terminates :
  projT1 Add_Reset ↓ (fun tin i => exists m n, tin[@Fin.F1] ≂ m /\ tin[@Fin.FS Fin.F1] ≂ n /\ 20 + 14 * n <= i).
Proof.
  eapply TerminatesIn_monotone. eapply Add_Reset_Terminates'. intros tin i (m&n&HEncM&HEncN&Hi).
  destruct HEncN as (r1&r2&HEncN % tape_encodes_l_natCounterIsM). do 5 eexists. repeat split; eauto; omega.
Qed.