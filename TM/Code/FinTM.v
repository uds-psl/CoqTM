Require Import TM.Prelim TM.TM TM.Code.Code TM.Code.CodeTM.
Require Import TM.Basic.Mono.
Require Import TM.Combinators.SequentialComposition TM.Combinators.Match.

Open Scope vector_scope.

Lemma fin_to_nat_proj1_S (n : nat) (x : Fin.t n) :
  S (proj1_sig (Fin.to_nat x)) = proj1_sig (Fin.to_nat (Fin.FS x)).
Proof.
  induction x.
  - cbn. reflexivity.
  - rewrite <- IHx. cbn. destruct (Fin.to_nat x). cbn. reflexivity.
Qed.

Lemma fin_encode_S (m : nat) (x : Fin.t m) :
  (@encode _ (I_Fin (S m)) (Fin.FS x) = true :: @encode _ (I_Fin m) x).
Proof.
  unfold encode. cbn. unfold encode_list. cbn.
  induction x.
  - cbn in *. reflexivity.
  - cbn in *. unfold encode_unit. cbn. unfold fin_to_nat.
    replace (proj1_sig (Fin.to_nat (Fin.FS (Fin.FS x)))) with
        (S (proj1_sig (Fin.to_nat (Fin.FS x)))).
    cbn. auto. now apply fin_to_nat_proj1_S.
Qed.

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

  Definition Fin_plus_mod (n : nat) : nat -> Fin.t (S n) -> Fin.t (S n) := it (@FinStep n).

  Compute Fin_plus_mod (n := 2) 0 (Fin.F1).
  Compute Fin_plus_mod (n := 2) 1 (Fin.F1).
  Compute Fin_plus_mod (n := 2) 2 (Fin.F1).
  Compute Fin_plus_mod (n := 2) 3 (Fin.F1).

  (* Property of it *)
  Lemma FinStep_S (n : nat) i x :
    FinStep (Fin_plus_mod (n := n) i x) = Fin_plus_mod (n := n) i (FinStep x).
  Proof.
    unfold Fin_plus_mod. induction i; cbn; eauto. now rewrite IHi.
  Qed.
    
  (* Todo: Show that Fin.t is a ring with Fin_plus_mod *)
End FinMod.


(* Stupid lemma *)
Section TM_terminates_in_final_state.
  Variable sig : finType.
  Variable n : nat.
  Variable M : mTM sig n.

  Lemma tm_terminates_in_final_state (c1 : mconfig sig (states M) n) (i : nat) :
    halt (cstate c1) = true ->
    exists c2 : mconfig sig (states M) n,
      loopM i c1 = Some c2.
  Proof. intros H1. exists c1. unfold loopM. Search loop. apply loop_ge with (k1 := 0). omega. cbn. now rewrite H1. Qed.
    
End TM_terminates_in_final_state.


(* Decode Fin.t *)
Section Modulo_TM.

  Variable n : nat.

  Print Mk_Mono_TM.

  (* (inl Fin.F1) is the initial state,
   * (inl _) are the internal states,
   * (inr _) are the final states, that stand for the corresponding decoding. *)
  Definition modulo_states := FinType (EqType (Fin.t (S n) + Fin.t (S n)))%type.

  Definition modulo_TM_trans_mono :
    modulo_states -> option bool_fin -> modulo_states * (option bool_fin * move).
  Proof.
    intros q. destruct q as [x | y] eqn:E.
    - (* inl x *)
      intros [ [ | ] | ].
      + (* Some true *)
        apply (inl (FinStep x), (None, R)). (* increase *)
      + (* Some false *)
        apply (inr x, (None, R)). (* terminate *)
      + (* None *)
       apply (inl x, (None, N)). (* unexpected end of tape -> diverge *)
    - (* inr y *)
      intros _. apply (inr y, (None, N)). (* terminal state *)
  Defined.

  Definition modulo_fin : modulo_states -> bool.
  Proof.
    destruct 1 as [ _ | _ ]; [apply false | apply true].
  Defined.
  
  Definition Modulo_TM : mTM bool_fin 0.
  Proof.
    apply Mk_Mono_TM with (states := modulo_states).
    - apply modulo_TM_trans_mono.
    - apply (inl (@Fin.F1 n)).
    - apply modulo_fin.
  Defined.

  Definition Modulo : { M : mTM bool_fin 0 & states M -> option (Fin.t (S n)) }.
  Proof.
    exists Modulo_TM. intros [ _ | x ]; [apply None | apply (Some x)].
  Defined.


  Lemma Modulo_Fin_terminates_in_Strong :
    forall (tape1 : tape bool_fin) (rest : list bool_fin) (i : nat)
      (x : Fin.t (S n)),
      tape_local tape1 = encode i ++ rest ->
      exists tape2, tape_local tape2 = rest /\
               loopM (M := Modulo_TM) (S i) (mk_mconfig (inl x) [|tape1|]) =
               Some (mk_mconfig (inr (Fin_plus_mod i x)) [|tape2|]).
  Proof.
    intros tape1 rest i. revert tape1 rest. induction i; intros; cbn in *.
    - unfold modulo_fin. cbn.
      unfold step at 1. cbn.
      replace (current tape1) with (Some false); [ | erewrite tape_local_current_cons; now eauto]. cbn.
      unfold step at 1. cbn.
      replace (current tape1) with (Some false); [ | erewrite tape_local_current_cons; now eauto]. cbn.
      exists (tape_move_right tape1). split; auto. erewrite tape_local_move_right; eauto.
    - assert (current tape1 = Some true) as H' by (erewrite tape_local_current_cons; eauto).
      assert (tape_local (tape_move_right tape1) = encode_list encode_unit (repeat tt i) ++ rest)
        as H'' by (erewrite tape_local_move_right; eauto).
      unfold step at 1. cbn. rewrite !H'.
      unfold modulo_fin at 1. cbn.
      unfold step at 2. unfold step at 2. cbn. rewrite !H'. cbn.
      unfold step at 2. cbn. rewrite !H'. cbn.

      (* current (tape_move_right tape1) must not be None *)
      destruct (current (tape_move_right tape1)) eqn:E1.
      + destruct e eqn:E2; cbn in *.
        * edestruct (IHi (tape_move_right tape1) rest ((FinStep x))) as (tape2&IHi'&IHi'').
          eapply H''. cbn in *.
          unfold step at 2. cbn. rewrite H'. cbn.
          unfold step at 2 in IHi''. cbn in IHi''. rewrite E1 in IHi''. cbn in IHi''.
          eexists tape2. split; auto. cbn in *.
          replace (Fin_plus_mod i (FinStep x)) with (FinStep (Fin_plus_mod i x)) in IHi''. apply IHi''.
          apply FinStep_S.
        * edestruct (IHi (tape_move_right tape1) rest (FinStep x)) as (tape2&IHi'&IHi'').
          eapply H''. cbn in *.
          unfold step at 2. cbn. rewrite H'. cbn.
          unfold step at 2 in IHi''. cbn in IHi''. rewrite E1 in IHi''. cbn in IHi''.
          eexists tape2. split; auto. cbn in *.
          replace (Fin_plus_mod i (FinStep x)) with (FinStep (Fin_plus_mod i x)) in IHi''. apply IHi''.
          apply FinStep_S.
      + exfalso. destruct i; cbn in *.
        * eapply tape_local_current_cons in H''. enough (None = Some false) by discriminate. rewrite <- E1. auto.
        * eapply tape_local_current_cons in H''. enough (None = Some  true) by discriminate. rewrite <- E1. auto.
  Qed.
  
End Modulo_TM.