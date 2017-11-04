Require Import TM.Prelim.
Require Import TM.Basic.Mono.
Require Import TM.Combinators.Match TM.Combinators.While TM.Combinators.SequentialComposition.

Section move_to_symbol.
  
  Variable sig : finType.
  Variable f : sig -> bool.

  Definition M1 D : { M : mTM sig 1 & states M -> bool * bool } :=
    MATCH (TEST_CHAR f)
          (fun b => match b with
                 | Some false => Move sig D ;; mono_Nop sig (true, false) (* Not found yet: move on and continue *)
                 | Some true => mono_Nop sig (false, true) (* Found: stop *)
                 | None => mono_Nop sig (false, false) (* Reached end of tape: stop *)
                 end).


  (* Returns true if symbol was found, false otherwise *)
  Definition move_to_symbol D : { M : mTM sig 1 & states M -> bool } := WHILE (M1 D).

  Fixpoint to_symbol_list_r l1 l2 :=
    match (l2,l1) with
    | ([],[]) => (false, niltape _)
    | ([], c :: l) => (false, rightof c l)
    | (c :: l, l1) => if f c then (true, midtape l1 c l) else to_symbol_list_r (c :: l1) l
    end.

  (* Careful: if the cursor is left of the tape, nothing will happen! *)
  Fixpoint to_symbol_r t :=
    match t with
    | niltape _ => (false, niltape _)
    | leftof c r => (false, leftof c r)
    | rightof c r => (false, rightof c r)
    | midtape l1 c l2 => to_symbol_list_r l1 (c :: l2)
    end.

  Definition R_move_to_symbol_r : Rel (tapes sig 1) (FinType (EqType bool) * tapes sig 1) :=
    Mk_R_p (fun t t' => t' = to_symbol_r t).


  Lemma to_symbol_r_current_Some t s :
    f s = true -> current t = Some s -> to_symbol_r t = (true, t).
  Proof.
    intros. destruct t; cbn in *; try congruence. inv H0. now rewrite H.
  Qed.

  Lemma to_symbol_r_current_None t :
    current t = None -> to_symbol_r t = (false, t).
  Proof.
    intros. destruct t; cbn in *; try congruence.
  Qed.

  Lemma to_symbol_r_move_false t t' s :
    current t = Some s -> f s = false -> t' = tape_move_mono t (None, R) -> to_symbol_r t = to_symbol_r t'.
  Proof.
    intros H1 H2 ->. destruct t; cbn in *; try congruence. inv H1. rewrite H2. cbn. destruct l0; cbn; auto.
  Qed.
  
  (* TODO: This proof should be monstly automatised *)
  Lemma move_to_symbol_r_WRealise :
    move_to_symbol R ⊫ R_move_to_symbol_r.
  Proof.
    eapply WRealise_monotone.
    - eapply While_WRealise. unfold M1. eapply Match_WRealise.
      eapply Realise_WRealise. eapply RealiseIn_Realise. eapply test_chr_Sem.
      instantiate (1 := fun o => match o with Some true => _ | Some false => _ | None => _ end).
      intros [ [ | ] | ].
      + eapply Realise_WRealise, RealiseIn_Realise. eapply mono_Nop_Sem.
      + eapply Realise_WRealise. eapply Seq_Realise; eapply RealiseIn_Realise. eapply Move_Sem. eapply mono_Nop_Sem.
      + eapply Realise_WRealise, RealiseIn_Realise. eapply mono_Nop_Sem.
    - intros tin (bout, tout). cbn in bout. intros H. hnf in *. destruct H as (t1&H1&f'&t2&(H2&H3)&H4). hnf in *.
      induction H1 as [x | x y z IH1 IH2 IH3].
      + destruct f'.
        * destruct H3 as (s&H3&H3'). subst. destruct (f s) eqn:E; hnf in *.
          -- destruct H4 as (H4&H4'). hnf in *. subst. inv H4. cbn. erewrite to_symbol_r_current_Some; eauto. now rewrite H2.
          -- destruct H4 as ((b2&t3)&H4&H4'). hnf in *. destruct b2 eqn:E2; hnf in *.
             ++ destruct H4 as (H41&c&H42). destruct H4' as (H4&->); hnf in *. congruence.
             ++ destruct H4 as (H41&H42); hnf in *. destruct H4' as (H4&->); hnf in *. congruence.
        * hnf in *. destruct H4 as (H4&->); hnf in *. inv H4. rewrite <- H2. now erewrite to_symbol_r_current_None; eauto.
      + hnf in *. rewrite H2 in *. clear H2.
        destruct IH1 as (b1&ob&t&(H1&H1')&H1''). hnf in *. rewrite H1 in *; clear H1. destruct ob as [ [ ] | ]; hnf in *.
        * destruct H1' as (s&H1&H1'). hnf in *. destruct H1'' as (H1''&->). hnf in *. congruence.
        * destruct H1' as (s&H1&H2). destruct H1'' as ((q&t3)&H5&H6). hnf in *. destruct H6 as (H6&H7). hnf in *. subst. inv H6. 
          specialize (IH3 eq_refl). destruct q; hnf in *.
          -- destruct H5 as (H5&s'&H6). hnf in *.
             destruct f'.
             ++ destruct H3 as (s''&H3&H3'); subst. rewrite IH3; [clear IH3 | eauto]. destruct (f s''); hnf in *.
                ** destruct H4 as (H4&->). hnf in *. inv H4. rewrite H1 in H6. inv H6. erewrite (to_symbol_r_move_false H1); eauto.
                ** destruct H4 as ((f2, t3)&H4&H7). hnf in *. destruct H7 as (H7&H8). hnf in *. congruence.
             ++ specialize (IH3 H3). rewrite IH3. hnf in *. destruct H4 as (H4&->). hnf in *. inv H4.
                rewrite H5. symmetry. eapply (to_symbol_r_move_false H1); eauto.
          -- destruct H5 as (H5&->). congruence.
        * destruct H1'' as (H1''&->). hnf in *. congruence.
  Qed.

  Fixpoint time_until_symbol_list (ls : list sig) :=
    match ls with
    | nil => 1
    | c :: ls => if f c then 1 else 1 + time_until_symbol_list ls
    end.
  
  Fixpoint time_until_symbol_r (t : tape sig) :=
    match t with
    | niltape _ => 2
    | leftof c r => 2
    | rightof c r => 2
    | midtape l1 c l2 => time_until_symbol_list (c :: l2)
    end.


  Lemma move_to_symbol_r_term :
    projT1 (move_to_symbol R) ⇓ (fun x i => i = 5 * time_until_symbol_r (x[@Fin.F1])).
  Proof.
    eapply TerminatesIn_monotone.
    - cbn -[M1]. eapply While_Terminates.
    - intros t k ->. destruct_tapes. destruct h.
      + unfold M1. econstructor; unfold MATCH; cbn [projT1]; cbn [projT2].
        * eapply Match_Terminates''.
          -- cbn. eauto.
          -- cbn. eauto.
        * cbn. eauto.
      + unfold M1. econstructor; unfold MATCH; cbn [projT1]; cbn [projT2].
        * eapply Match_Terminates''.
          -- cbn. eauto.
          -- cbn. eauto.
        * cbn. eauto.
      + unfold M1. econstructor; unfold MATCH; cbn [projT1]; cbn [projT2].
        * eapply Match_Terminates''.
          -- cbn. eauto.
          -- cbn. eauto.
        * cbn. eauto.
      + unfold M1. unfold MATCH; cbn [projT1]; cbn [projT2]. destruct (f e) eqn:E.
        * cbn. rewrite E. cbn. replace 5 with (3 + S 1) by omega.
          eapply term_false. eapply Match_Terminates''.
          -- cbn. rewrite E. cbn. eauto.
          -- cbn. eauto.
          -- cbn. eauto.
        * revert l e E. induction l0 as [ | r rs IH]; intros ls e E.
          -- simpl. rewrite E. cbn. replace 10 with (4 + S 5) by omega. eapply term_true.
             ++ simpl. cbn. rewrite E. cbn. eauto.
             ++ simpl. eauto.
             ++ simpl. eapply term_false.
                ** cbn. eauto.
                ** cbn. eauto.
          -- simpl time_until_symbol_r. rewrite E.
             assert (5 * S (if f r then 1 else S (time_until_symbol_list rs)) =
                     4 + (S (if f r then 5 else 5 + 5 * (time_until_symbol_list rs)))) as ->.
             {
               destruct (f r); simpl; omega.
             }
             eapply term_true.
             ++ cbn. rewrite E. cbn. eauto.
             ++ cbn. eauto.
             ++ destruct (f r) eqn:E2.
                ** replace 5 with (4 + S 0) by omega. eapply term_false.
                   --- cbn. rewrite E2. cbn. eauto.
                   --- cbn. eauto.
                ** specialize (IH (e :: ls) r E2). cbn in *. rewrite E2 in *.
                   replace (S (S (S (S (S (time_until_symbol_list rs + (time_until_symbol_list rs + (time_until_symbol_list rs + (time_until_symbol_list rs + (time_until_symbol_list rs + 0))))))))))
                     with (S (time_until_symbol_list rs) + (S (time_until_symbol_list rs) + (S (time_until_symbol_list rs) + (S (time_until_symbol_list rs) + (S (time_until_symbol_list rs) + 0)))))
                          by omega.
                   apply IH.
  
Qed.

                               (* TODO: Make this proof faster, by inserting counters in WhileTerm *)
                               (* It can also be made faster by replacing the read machine by a machine that reads and terminates in the right state. *)
                               (* TODO: Move to left *)
                               (* Idea: Tape-Reversierung *)

  
  Fixpoint to_symbol_list_l l1 l2 {struct l2} :=
    match (l2,l1) with
    | ([],[]) => (false, niltape _)
    | ([], c :: l) => (false, leftof c l)
    | (c :: l, l1) => if f c then (true, midtape l c l1) else to_symbol_list_l (c :: l1) l
    end.

  (* Careful: if the cursor is left of the tape, nothing will happen! *)
  Fixpoint to_symbol_l t :=
    match t with
    | niltape _ => (false, niltape _)
    | leftof c r => (false, leftof c r)
    | rightof c r => (false, rightof c r)
    | midtape l1 c l2 => to_symbol_list_l l2 (c :: l1)
    end.

  Lemma to_symbol_list_l_in_iff l1 l2 :
    (exists s, s el l2 /\ f s = true) <-> (exists t', to_symbol_list_l l1 l2 = (true, t')).
  Proof.
    split; revert l1; induction l2; intros; cbn in *.
    - destruct H as (s&H&H'). auto.
    - destruct H as (s&[->|H]&H').
      + rewrite H'. eauto.
      + destruct (IHl2 (a :: l1)) as (t'&Ht'); eauto. destruct (f a); eauto.
    - destruct H as (t'&H). destruct l1; congruence.
    - destruct H as (t'&H). destruct (f a) eqn:E.
      + inv H. eauto.
      + destruct (IHl2 (a :: l1)) as (s&IH&IH'); eauto.
  Qed.

  Lemma to_symbol_l_false t t' :
    to_symbol_l t = (false, t') ->
    forall s, current t = Some s \/ ((exists s', current t = Some s') /\ s el left t) -> f s = false.
  Proof.
    revert t'. intros H. destruct t eqn:E; cbn in *; intros; firstorder; (intuition; try congruence).
    - inv H1. destruct f eqn:E; auto. congruence.
    - inv H1. 
  Abort.

  Definition R_move_to_symbol_l : Rel (tapes sig 1) (FinType (EqType bool) * tapes sig 1) :=
    Mk_R_p (fun t t' => t' = to_symbol_l t).


End move_to_symbol.