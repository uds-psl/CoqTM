Require Export TM Shared.FiniteTypes Nop.

Section Fix_TM_do_2.

  Variable sig : finType.
  Variable tapes_no : nat.

  Variable tape_i : nat.
  Hypothesis i_is_a_tape : tape_i < S tapes_no.

  Variable tape_j : nat.
  Hypothesis j_is_a_tape : tape_j < S tapes_no.

  Definition do_on_tapes : option sig * move -> Vector.t (option sig * move) (S tapes_no) :=
    fun p => tabulate_vec (S tapes_no) (fun n => if Dec (n = tape_i) then p else
                                             if Dec (n = tape_j) then p else (None, TM.N)).
  
  Lemma get_at_do_on_tapes1a a:
    get_at i_is_a_tape (do_on_tapes a) = a.
  Proof.
    unfold do_on_tapes.
    erewrite get_at_tabulate.
    have (tape_i = tape_i).
  Qed.

  Lemma get_at_do_on_tapes1b a :
    get_at j_is_a_tape (do_on_tapes a) = a.
  Proof.
    unfold do_on_tapes.
    erewrite get_at_tabulate.
    decide _. reflexivity.
    have (tape_j = tape_j).
  Qed.


  Lemma get_at_do_on_tapes2 a i (itape : i < S tapes_no) : i <> tape_i -> i <> tape_j ->
                                                           get_at itape (do_on_tapes a) = (None, TM.N).
  Proof.
    unfold do_on_tapes.
    erewrite get_at_tabulate.
    intros. do 2 (decide _; try tauto). 
  Qed.

End Fix_TM_do_2.
Arguments do_on_tapes {sig tapes_no} _ _ _.

Section Fix_TM_do.

  Variable tapes_no : nat.
  Variable sig : finType.

  Variable on_tape : nat.
  Hypothesis is_a_tape : on_tape < S tapes_no.

  Definition do_on_tape : option sig * move -> Vector.t (option sig * move) (S tapes_no) :=
    let _ := is_a_tape in
    fun p => tabulate_vec (S tapes_no) (fun n => if Dec (n = on_tape) then p else (None, TM.N)).
  
  Lemma get_at_tape_move_multi(t : tapes sig (S tapes_no)) a i (itape : i < S tapes_no) : get_at itape (tape_move_multi t a) = tape_move_mono (get_at itape t) (get_at itape a).
  Proof.
    unfold tape_move_multi.
    unfold get_at.
    erewrite Vector.nth_map2; reflexivity.
  Qed.

  Lemma do_on_tape_nothing t : tape_move_multi t (do_on_tape (None, TM.N)) = t.
  Proof.
    unfold do_on_tape, tape_move_multi.
    admit.
  Admitted.
  
  Lemma get_at_do_on_tape1 a :
    get_at is_a_tape (do_on_tape a) = a.
  Proof.
    unfold do_on_tape.
    erewrite get_at_tabulate.
    have (on_tape = on_tape).
  Qed.

  Lemma get_at_do_on_tape2 a i (itape : i < S tapes_no) : i <> on_tape ->
                                                          get_at itape (do_on_tape a) = (None, TM.N).
  Proof.
    unfold do_on_tape.
    erewrite get_at_tabulate.
    intros. decide _; tauto.
  Qed.

End Fix_TM_do.

Section Single_TM.

  Variable sig : finType.
  Variable tapes_no : nat.

  Variable on_tape : nat.
  Variable is_a_tape : on_tape < S tapes_no.

  Variable states : finType.

  Variable act : states -> option sig -> states * (option sig * move).
  Variable start : states.
  Variable halt : states -> bool.

  (* Hypothesis halt_start : halt start = false. *)

  (* Hypothesis act_halts : forall s c, halt (fst (act s c)) = true. *)

  Variable F : finType.
  Variable p : states -> F.

  Definition one_tape_trans (p : states * Vector.t (option sig) (S tapes_no)) : states * Vector.t (option sig * move) (S tapes_no) :=
    let (s, a) := act (fst p) (get_at is_a_tape (snd p)) in
    (s, do_on_tape is_a_tape a).

  Definition one_tape := Build_mTM one_tape_trans start halt.

  (* Variable P : F -> sig -> Prop. *)
  (* Variable P2 : F -> Prop. *)

  (* Hypothesis P_hold : forall c, P (p (fst (act (Some c)))) c. *)
  (* Hypothesis P2_hold : P2 (p (fst (act None))). *)

  Lemma one_tape_sem :
    one_tape ⊫(p) ignoreParam(Eq_in (<> project is_a_tape)).
  Proof.
    (* intros t i (? & ?) H. *)
    (* induction i; intros j jtape Hj. *)
    (* - simpl_TM. *)
    (*   destruct _ eqn:E; now inv H. *)
    (* - simpl_TM. *)
    (*   destruct _ eqn:E; inv H. *)
    (*   + reflexivity. *)
    (*   + eapply IHi; eauto. *)
  Admitted.       
  
End Single_TM.


Section Eq_in.

  Variable sig : finType.
  Variable tapes_no : nat.

  Variable tape_i : nat.
  Hypothesis i_is_a_tape : tape_i < S tapes_no.

  Variable tape_j : nat.
  Hypothesis j_is_a_tape : tape_j < S tapes_no.
  

  Lemma Eq_in_tape_move_multi (t : tapes sig (S tapes_no)) A :
    Eq_in
      (not_indices
         (Vector.cons (Fin.t (S tapes_no)) i_is_a_tape 1
                      (Vector.cons (Fin.t (S tapes_no)) j_is_a_tape 0 (Vector.nil (Fin.t (S tapes_no)))))) t
      (tape_move_multi t (do_on_tapes tape_i tape_j A)).
  Proof.
  Admitted.

End Eq_in.


Ltac simpl_TM := repeat progress (
                          try match goal with
                          | [ |- context[ Vector.nth ?t (Fin.of_nat_lt ?pos) ] ] =>
                            change (Vector.nth t (Fin.of_nat_lt pos)) with (get_at pos t)
                          | [ H: context[ Vector.nth ?t (Fin.of_nat_lt ?pos)] |- _ ]  =>
                            change (Vector.nth t (Fin.of_nat_lt pos)) with (get_at pos t) in H
                          end;
  repeat try split;
  try match goal with [ |- exists _, _] => eexists end;
  cbn -[tape_move_multi null_action get_at do_on_tape do_on_tapes] in *;
  unfold step, trans, one_tape, one_tape_trans, Eq_in;
  cbn -[tape_move_multi null_action get_at do_on_tape do_on_tapes] in *;
  intuition;
  try eapply Eq_in_tape_move_multi;
  erewrite ?get_at_tape_move_multi,
  ?get_at_do_on_tape1,
  ?get_at_do_on_tape2,
  ?get_at_do_on_tapes1a,
  ?get_at_do_on_tapes1b,
  ?get_at_do_on_tapes2,
  ?get_at_map,
  ?tape_move_null_action,
  ?do_on_tape_nothing;
  eauto).
