Require Import TM.Prelim TM.TM TM.Code.Code TM.Code.CodeTM.
Require Import TM.Basic.Mono.
Require Import TM.Combinators.SequentialComposition TM.Combinators.Match.

Open Scope vector_scope.

(* Compute the [n]th (encoded as a [nat] on tape 1) value of a sequence [it f n x] and
 * terminate in state [inr (it f n x)]. *)
Section Fin_Seq_TM.

  Variable X : finType.
  Variable f : X -> X.
  Variable start : X.
  
  Lemma it_S (n : nat) (x : X) :
    it f n (f x) = f (it f n x).
  Proof. induction n; cbn; congruence. Qed.

  (* (inl start) is the initial state,
   * (inl _) are the internal states,
   * (inr _) are the final states, that stand for the corresponding decoding. *)
  Definition fin_seq_states := FinType (EqType (X + X))%type.

  Definition fin_seq_TM_trans_mono :
    fin_seq_states -> option bool_fin -> fin_seq_states * (option bool_fin * move).
  Proof.
    intros q. destruct q as [x | y] eqn:E.
    - (* inl x *)
      intros [ [ | ] | ].
      + (* Some true *)
        apply (inl (f x), (None, R)). (* continue *)
      + (* Some false *)
        apply (inr x, (None, R)). (* terminate *)
      + (* None *)
       apply (inl x, (None, N)). (* unexpected end of tape -> diverge *)
    - (* inr y *)
      intros _. apply (inr y, (None, N)). (* terminal state *)
  Defined.

  Definition fin_seq_fin : fin_seq_states -> bool.
  Proof.
    destruct 1 as [ _ | _ ]; [apply false | apply true].
  Defined.
  
  Definition Fin_Seq_TM : mTM bool_fin 1.
  Proof.
    apply Mk_Mono_TM with (states := fin_seq_states).
    - apply fin_seq_TM_trans_mono.
    - apply (inl start).
    - apply fin_seq_fin.
  Defined.

  Definition Fin_Seq : { M : mTM bool_fin 1 & states M -> option X }.
  Proof.
    exists Fin_Seq_TM. intros [ _ | x ]; [apply None | apply (Some x)].
  Defined.

  Lemma Fin_Seq_terminates_in_Strong :
    forall (tape1 : tape bool_fin) (rest : list bool_fin) (i : nat)
      (x : X),
      tape_local tape1 = encode i ++ rest ->
      exists tape2, tape_local tape2 = rest /\
               loopM (M := Fin_Seq_TM) (S i) (mk_mconfig (inl x) [|tape1|]) =
               Some (mk_mconfig (inr (it f i x)) [|tape2|]).
  Proof.
    intros tape1 rest i. revert tape1 rest. induction i; intros; cbn in *.
    - unfold step at 1. cbn.
      replace (current tape1) with (Some false); [ | erewrite tape_local_current_cons; now eauto]. cbn.
      unfold step at 1. cbn.
      replace (current tape1) with (Some false); [ | erewrite tape_local_current_cons; now eauto]. cbn.
      exists (tape_move_right tape1). split; auto. erewrite tape_local_move_right; eauto.
    - assert (current tape1 = Some true) as H' by (erewrite tape_local_current_cons; eauto).
      assert (tape_local (tape_move_right tape1) = encode_list encode_unit (repeat tt i) ++ rest)
        as H'' by (erewrite tape_local_move_right; eauto).
      unfold step at 1. cbn. rewrite !H'.
      unfold it. cbn.
      unfold step at 2. unfold step at 2. cbn. rewrite !H'. cbn.
      unfold step at 2. cbn. rewrite !H'. cbn.

      (* current (tape_move_right tape1) must not be None *)
      destruct (current (tape_move_right tape1)) eqn:E1.
      + destruct e eqn:E2; cbn in *.
        * edestruct (IHi (tape_move_right tape1) rest (f x)) as (tape2&IHi'&IHi'').
          eapply H''. cbn in *.
          unfold step at 2. cbn. rewrite H'. cbn.
          unfold step at 2 in IHi''. cbn in IHi''. rewrite E1 in IHi''. cbn in IHi''.
          eexists tape2. split; auto. cbn in *.
          now rewrite it_S in IHi''.
        * edestruct (IHi (tape_move_right tape1) rest (f x)) as (tape2&IHi'&IHi'').
          eapply H''. cbn in *.
          unfold step at 2. cbn. rewrite H'. cbn.
          unfold step at 2 in IHi''. cbn in IHi''. rewrite E1 in IHi''. cbn in IHi''.
          eexists tape2. split; auto. cbn in *.
          now rewrite it_S in IHi''.
      + exfalso. destruct i; cbn in *.
        * eapply tape_local_current_cons in H''. enough (None = Some false) by discriminate. rewrite <- E1. auto.
        * eapply tape_local_current_cons in H''. enough (None = Some  true) by discriminate. rewrite <- E1. auto.
  Qed.

  Lemma Fin_Seq_terminates_in :
    Fin_Seq_TM ↓ (fun tapes1 i => exists k, tape_encodes_locally _ (tapes1[@Fin.F1]) k /\ i = S k).
  Proof.
    hnf. intros tapes ? (k&(rest&H1)&->). destruct_tapes. cbn in *. hnf in *.
    destruct (@Fin_Seq_terminates_in_Strong h rest k start) as (?&?&?); eauto.
  Qed.

  Definition Fin_Seq_R_p : Rel (tapes bool_fin 1) (option X * tapes bool_fin 1) :=
    ignoreParam (@skip_locally_R 1 Fin.F1 nat _) ∩
                (fun tps1 '(ox, _) => forall n, tape_encodes_locally _ (tps1[@Fin.F1]) n -> ox = Some (it f n start)).

  Lemma Fin_Seq_WRealise : Fin_Seq ⊫ Fin_Seq_R_p.
    hnf. intros. destruct_tapes. cbn in *. split; hnf in *.
    - intros x rest HEnc.
      pose proof @Fin_Seq_terminates_in_Strong h rest _ start HEnc as (tape2&H1&H2).
      unfold loopM in *. pose proof (loop_functional H H2) as ->. cbn. auto.
    - intros x (rest&HEnc).
      pose proof @Fin_Seq_terminates_in_Strong h rest _ start HEnc as (tape2&H1&H2).
      unfold loopM in *. pose proof (loop_functional H H2) as ->. cbn. auto.
  Qed.

End Fin_Seq_TM.



(* TODO: Instanciate the above TM witch FinStep and Fin.F1 *)
Section FinMod.

  Definition modstep (n : nat) : nat -> nat :=
    fun m => if m =? n then 0 else S m.

  Lemma modstep_le (n m : nat) : m < S n -> modstep n m < S n.
  Proof.
    intros H. revert m H. unfold modstep. induction n; cbn in *; intros m H.
    - assert (m = 0) as -> by omega. cbn. omega.
    - destruct (m =? S n) eqn:E.
      + apply Nat.eqb_eq in E as ->. omega.
      + enough (m <> S n) by omega.
        intros ->. enough (S n =? S n = true) by congruence. apply Nat.eqb_eq. auto.
  Qed.

  Definition FinStep (n : nat) : Fin.t (S n) -> Fin.t (S n).
  Proof.
    intros x. destruct (Fin.to_nat x).
    apply (Fin.of_nat_lt (modstep_le l)).
  Defined.

  Lemma fin_next_correct_S (n : nat) (x : Fin.t (S n)) :
    proj1_sig (Fin.to_nat x) < n ->
    proj1_sig (Fin.to_nat (FinStep x)) = S (proj1_sig (Fin.to_nat x)).
  Proof.
    Set Printing Coercions.
    intros H. unfold FinStep.
    destruct (Fin.to_nat x). cbn in *.
    rewrite Fin.to_nat_of_nat. cbn in *.
    unfold modstep. destruct (x0 =? n) eqn:E; auto.
    apply Nat.eqb_eq in E.
    subst. omega.
    Unset Printing Coercions.
  Qed.

  Lemma fin_next_correct_n (n : nat) (x : Fin.t (S n)) :
    proj1_sig (Fin.to_nat x) >= n ->
    proj1_sig (Fin.to_nat (FinStep x)) = 0.
  Proof.
    Set Printing Coercions.
    intros H. unfold FinStep.
    destruct (Fin.to_nat x). cbn in *.
    rewrite Fin.to_nat_of_nat. cbn in *.
    unfold modstep. destruct (x0 =? n) eqn:E; auto.
    assert (x0 = n) by omega.
    apply Nat.eqb_eq in H0. exfalso. congruence.
    Unset Printing Coercions.
  Qed.

  (*
  Compute it (FinStep (n := 2)) 0 (Fin.F1).
  Compute it (FinStep (n := 2)) 1 (Fin.F1).
  Compute it (FinStep (n := 2)) 2 (Fin.F1).
  Compute it (FinStep (n := 2)) 3 (Fin.F1).
  *)

  Definition FinMod (n : nat) := Fin_Seq (@FinStep n) Fin.F1.
End FinMod.