Require Import TM.Prelim.
Require Import TM.Basic.Mono.
Require Import TM.Combinators.Match TM.Combinators.While TM.Combinators.SequentialComposition.
(* Require Import TM.IsoTrans. (* tape_mirror, this shoud probably be moved elsewhere *) *)
Require Import TM.Compound.Peek.

Require Import FunInd.
Require Import Recdef.

Ltac deq x := let H := fresh in destruct (Dec (x = x)) as [? | H]; [ | now contradiction H].

Section move_to_symbol.
  
  Variable sig : finType.
  Variable f : sig -> bool.

  Definition M1 D : { M : mTM sig 1 & states M -> bool * bool } :=
    MATCH (Peek f)
          (fun b => match b with
                 | inl false => Move sig D (true, false) (* Not found yet: move on and continue *)
                 | inl true => mono_Nop sig (false, true) (* Found: stop *)
                 | inr D' => if Dec (D'=D) || Dec (D'=N) then
                              (* Reached the other end of the tape or the tape is empty: stop *)
                              mono_Nop sig (false, false)
                            else
                              (* Continue *)
                              mono_Nop sig (true, false)
                 end).


  (* Returns true if symbol was found, false otherwise *)
  (* It stops and returns false if the pointer gets off the tape. *)
  Definition MoveToSymbol D : { M : mTM sig 1 & states M -> bool } := WHILE (M1 D).

  Definition rlength (t : tape sig) :=
    match t with
    | niltape _ => 0
    | rightof _ _ => 0
    | midtape ls m rs => 1 + length rs
    | leftof r rs => 2 + length rs
    end.

  Function moveToSymbol_R (t : tape sig) { measure rlength t } : tape sig :=
    match t with
    | niltape _ => niltape _
    | rightof l ls => t
    | midtape ls m rs => if f m then midtape ls m rs else moveToSymbol_R (tape_move_right t)
    | leftof r rs => moveToSymbol_R (tape_move_right t)
    end.
  Proof.
    all: (intros; try now (cbn; omega)). destruct rs; cbn; omega.
  Defined.

  Lemma moveToSymbol_tapeToList_R t : tapeToList t = tapeToList (moveToSymbol_R t).
  Proof.
    functional induction moveToSymbol_R t; try reflexivity.
    - pose proof (tapeToList_move (midtape ls m rs) R). cbn [tape_move] in H. rewrite <- H in IHt0. congruence.
    - pose proof (tapeToList_move (leftof r rs) R). cbn [tape_move] in H. rewrite <- H in IHt0. congruence.
  Qed.

(* (* Test *)
End move_to_symbol.
Compute moveToSymbol_R (fun b => b) (leftof false [false; false; true; false]). 
*)

  Lemma tape_move_niltape (t : tape sig) (D : move) : tape_move t D = niltape _ -> t = niltape _.
  Proof. destruct t, D; cbn; intros; try congruence. destruct l; congruence. destruct l0; congruence. Qed.

  Lemma moveToSymbol_nitape_R t : moveToSymbol_R t = niltape _ -> t = niltape _.
  Proof.
    intros H. remember (niltape sig) as N. functional induction moveToSymbol_R t; subst; try congruence.
    - specialize (IHt0 H). destruct rs; cbn in *; congruence.
    - specialize (IHt0 H). destruct rs; cbn in *; congruence.
  Qed.


  
  Definition MoveToSymbol_R_Rel : Rel (tapes sig 1) (FinType (EqType bool) * tapes sig 1) :=
    Mk_R_p ((if? (fun t t' => exists s, current t' = Some s /\ f s)
               ! (fun t t' => current t' = None)) ∩ ignoreParam (fun t t' => moveToSymbol_R t = t')).

  Lemma MoveToSymbol_R_WRealise :
     MoveToSymbol R ⊫ MoveToSymbol_R_Rel.
  Proof.
    intros HD. eapply WRealise_monotone.
    {
      eapply While_WRealise. unfold M1. eapply Match_WRealise.
      eapply Realise_WRealise. eapply RealiseIn_Realise. eapply Peek_RealisesIn.
      instantiate (1 := (fun o => match o with
                               | inl true => _
                               | inl false => _
                               | inr L => _ | inr _ => _
                               end)).
      intros r. cbn in r. destruct r as [ [ | ] | D' ] eqn:E.
      + eapply Realise_WRealise, RealiseIn_Realise. eapply mono_Nop_Sem.
      + eapply Realise_WRealise. eapply RealiseIn_Realise. eapply Move_Sem.
      + destruct D'; cbn; eapply Realise_WRealise, RealiseIn_Realise, mono_Nop_Sem.
    }
    {
      intros tin (bout, tout). cbn in bout. intros H. hnf in *. destruct H as (t1&H1&P&t2&(H2&H3)&H4). hnf in *.
      induction H1 as [x | x y z IH1 IH2 IH3].
      - {
          destruct P as [ [ | ] | ] eqn:Ep.
          - hnf in *. destruct H4 as (H4&->). inv H4. rewrite H2 in *. clear x H2.
            destruct (tout[@Fin.F1]) eqn:E; try congruence. inv H3. cbn. split; eauto.
            now rewrite moveToSymbol_R_equation, <- H0.
          - hnf in *. destruct H4 as (H4&->). congruence.
          - {
              destruct (x[@Fin.F1]); inv H3; cbn in *; destruct H4 as (H4&->); inv H4; cbn; auto.
              - rewrite <- H2. cbn. eauto.
              - rewrite <- H2. cbn. eauto.
            }
        }
      - {
          rewrite H2 in *. clear z H2 IH2.
          hnf in *. destruct IH1 as (b1&P'&t3&(->&IH1)&IH2); cbn in *; hnf in *.
          specialize (IH3 eq_refl).
          destruct (t2[@Fin.F1]) eqn:E1; subst; hnf in *; try (destruct H4 as (H4&->); inv H4); subst.
          + {
              specialize (IH3 eq_refl) as (IH3&IH4). rewrite E1 in *. inv IH4. 
              cbn. apply moveToSymbol_nitape_R in H0. rewrite H0 in *. cbn. split; auto.
              destruct P'; subst; cbn in *; auto.
              - destruct b; hnf in *; destruct IH2 as (IH2'&IH2); inv IH2'. rewrite H0 in *.
                symmetry in IH2. apply tape_move_niltape in IH2. rewrite IH2 in *. cbn. reflexivity.
              - destruct m; hnf in *; destruct IH2 as (IH2'&IH2); inv IH2'. rewrite H0 in *. cbn. reflexivity.
            }
          + {
              specialize (IH3 eq_refl) as (IH3&IH4). rewrite E1 in *. inv IH4. 
              cbn. rewrite H0 in *. destruct P'; subst; cbn in *; split; auto.
              - destruct b; hnf in *; destruct IH2 as (IH2'&IH2); inv IH2'. 
                destruct (t3[@Fin.F1]) eqn:E2; hnf in *; inv IH1. rewrite moveToSymbol_R_equation, <- H1.
                unfold tape_move in IH2. rewrite <- IH2. auto.
              - destruct m; hnf in *; destruct IH2 as (IH2'&IH2); inv IH2'. rewrite H0 in *. cbn. reflexivity.
            }
          + {
              specialize (IH3 eq_refl) as (IH3&IH4). split; auto. clear IH3.
              destruct (f e) eqn:E2; hnf in *; destruct H4 as (H4'&H4); inv H4'. rewrite <- IH4.
              destruct P'.
              - destruct b; hnf in *; destruct IH2 as (IH2'&IH2); inv IH2'.
                destruct (t3[@Fin.F1]) eqn:E3; hnf in *; inv IH1. rewrite IH2 in *. rewrite moveToSymbol_R_equation, <- H0. reflexivity.
              - destruct m; hnf in *; destruct IH2 as (IH2'&IH2); inv IH2'.
                destruct (y[@Fin.F1]) eqn:E3; hnf in *; inv IH1. reflexivity.
            }
        }
    }
  Qed.


  (* TODO: Termination *)
  (* FIXME *)

  Fixpoint time_until_symbol_list (ls : list sig) :=
    match ls with
    | nil => 1
    | c :: ls => if f c then 1 else 1 + time_until_symbol_list ls
    end.
  
  Fixpoint time_until_symbol_r (t : tape sig) :=
    match t with
    | niltape _ => 2
    | leftof c r => 1 + time_until_symbol_list (c :: r)
    | rightof c r => 2
    | midtape l1 c l2 => time_until_symbol_list (c :: l2)
    end.

  Fixpoint time_until_symbol_l (t : tape sig) :=
    match t with
    | niltape _ => 2
    | leftof c r => 2
    | rightof c r => 1 + time_until_symbol_list (c :: r)
    | midtape l1 c l2 => time_until_symbol_list (c :: l1)
    end.

  Definition time_until_symbol D (t : tape sig) :=
    match D with
    | L => time_until_symbol_l t
    | R => time_until_symbol_r t
    | N => 0
    end.
  

  (* TODO: Make this proof/excution faster, by inserting counters in WhileTerm *)
  (* It can also be made faster by replacing the read machine by a machine that reads and terminates in the right state. *)
  Lemma MoveToSymbol_R_Term :
    projT1 (MoveToSymbol R) ⇓ (fun x i => i = 11 * time_until_symbol_r (x[@Fin.F1])).
  Proof.
    (*
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
        * cbn. rewrite E. cbn. replace 4 with (2 + S 1) by omega.
          eapply term_false. eapply Match_Terminates''.
          -- cbn. rewrite E. cbn. eauto.
          -- cbn. eauto.
          -- cbn. eauto.
        * revert l e E. induction l0 as [ | r rs IH]; intros ls e E.
          -- simpl. rewrite E. cbn. replace 8 with (3 + S 4) by omega. eapply term_true.
             ++ simpl. cbn. rewrite E. cbn. eauto.
             ++ simpl. eauto.
             ++ simpl. eapply term_false.
                ** cbn. eauto.
                ** cbn. eauto.
          -- simpl time_until_symbol_r. rewrite E.
             assert (4 * S (if f r then 1 else S (time_until_symbol_list rs)) =
                     3 + (S (if f r then 4 else 4 + 4 * (time_until_symbol_list rs)))) as ->
                 by (destruct (f r); simpl; omega).
             eapply term_true.
             ++ cbn. rewrite E. cbn. eauto.
             ++ cbn. eauto.
             ++ destruct (f r) eqn:E2.
                ** replace 4 with (3 + S 0) by omega. eapply term_false.
                   --- cbn. rewrite E2. cbn. eauto.
                   --- cbn. eauto.
                ** specialize (IH (e :: ls) r E2). cbn -[mult] in *. rewrite E2 in *.
                   now replace (S (S (S (S (4 * time_until_symbol_list rs))))) with (4 * S (time_until_symbol_list rs)) by omega.
*)
  Admitted.


  Lemma MoveToSymbol_R_Realise : 
    MoveToSymbol R ⊨ MoveToSymbol_R_Rel.
  Proof.
    eapply WRealise_to_Realise.
    - cbn. eapply TerminatesIn_TerminatesAlways; auto. eapply MoveToSymbol_R_Term. eauto.
    - apply MoveToSymbol_R_WRealise.
  Qed.


  (** Move to left *)


  Definition llength (t : tape sig) :=
    match t with
    | niltape _ => 0
    | leftof _ _ => 0
    | midtape ls m rs => 1 + length ls
    | rightof l ls => 2 + length ls
    end.

  Function moveToSymbol_L (t : tape sig) { measure llength t } : tape sig :=
    match t with
    | niltape _ => niltape _
    | leftof r rs => t
    | midtape ls m rs => if f m then midtape ls m rs else moveToSymbol_L (tape_move_left t)
    | rightof l ls => moveToSymbol_L (tape_move_left t)
    end.
  Proof.
    all: (intros; try now (cbn; omega)). destruct ls; cbn; omega.
  Defined.

  Lemma moveToSymbol_tapeToList_L t : tapeToList t = tapeToList (moveToSymbol_L t).
  Proof.
    functional induction moveToSymbol_L t; try reflexivity.
    - pose proof (tapeToList_move (midtape ls m rs) L). cbn [tape_move] in H. rewrite <- H in IHt0. congruence.
    - pose proof (tapeToList_move (rightof l ls) L). cbn [tape_move] in H. rewrite <- H in IHt0. congruence.
  Qed.

  Lemma moveToSymbol_nitape_L t : moveToSymbol_L t = niltape _ -> t = niltape _.
  Proof.
    intros H. remember (niltape sig) as N. functional induction moveToSymbol_L t; subst; try congruence.
    - specialize (IHt0 H). destruct ls; cbn in *; congruence.
    - specialize (IHt0 H). destruct ls; cbn in *; congruence.
  Qed.

  Definition MoveToSymbol_L_Rel : Rel (tapes sig 1) (FinType (EqType bool) * tapes sig 1) :=
    Mk_R_p ((if? (fun t t' => exists s, current t' = Some s /\ f s)
               ! (fun t t' => current t' = None)) ∩ ignoreParam (fun t t' => moveToSymbol_L t = t')).

  Lemma MoveToSymbol_L_Realise : 
    MoveToSymbol L ⊨ MoveToSymbol_L_Rel.
  Proof.
  Admitted.

End move_to_symbol.