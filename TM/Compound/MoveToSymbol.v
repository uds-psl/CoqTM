Require Import TM.Prelim.
Require Import TM.Basic.Mono.
Require Import TM.Combinators.Match TM.Combinators.While TM.Combinators.SequentialComposition.
Require Import TM.Compound.Peek.
Require Import TM.Mirror.

Require Import FunInd.
Require Import Recdef.

Ltac deq x := let H := fresh in destruct (Dec (x = x)) as [? | H]; [ | now contradiction H].

Section move_to_symbol.
  
  Variable sig : finType.
  Variable f : sig -> bool.

  Print Mono.

  Check While.

  (*
   * One Step:
   * Read one symbol.  If there was no symbol, return [ None ].
   * If the read symbol fulfills [ f ], return [ Some true ].
   * Else move one to the right and return [ Some false ].
   *)
  Definition M1 : { M : mTM sig 1 & states M -> option bool } :=
    MATCH (Read_char _)
          (fun b : option sig =>
             match b with
             | Some x => if f x then
                          mono_Nop sig (Some true)
                        else
                          Move _ R (Some false)
             | _ => mono_Nop sig None
             end
          ).

  Definition M1_Fun : tape sig -> tape sig :=
    fun t1 =>
      match t1 with
      | midtape ls x rs => if (f x) then t1 else tape_move_right t1
      | _ => t1
      end.

  Definition M1_Rel : Rel (tapes sig 1) (option bool * tapes sig 1) :=
    Mk_R_p (fun tin '(yout, tout) =>
              tout = M1_Fun tin /\
              (
                (yout = Some true  /\ exists s, current tin = Some s /\ f s = true ) \/
                (yout = Some false /\ exists s, current tin = Some s /\ f s = false) \/
                (yout = None /\ current tout = None)
              )
           ).

  Tactic Notation "CertificateMyProgram" "before" tactic(T1) "after" tactic(T2) :=
    repeat progress
           (
             hnf in *;
             cbn in *;
             intros;
             destruct_tapes;
             simpl_tape in *;
             try T1;
             match goal with
             | [ H : _ ::: _ = [||]  |- _ ] => inv H
             | [ H : [||] = _ ::: _ |- _ ] => inv H
             | [ H : _ ::: _ = _ ::: _ |- _ ] => inv H

             | [ H : _ ::  _ = []  |- _ ] => inv H
             | [ H : [] = _ :: _ |- _ ] => inv H
             | [ H : _ ::  _ = _ :: _ |- _ ] => inv H

             | [ H : Some _ = Some _ |- _ ] => inv H
             | [ H : None   = Some _ |- _ ] => inv H
             | [ H : Some _ = None   |- _ ] => inv H

             | [ H : _ /\ _ |- _] => destruct H
             | [ H : _ \/ _ |- _] => destruct H
             | [ H : ex ?P |- _] => destruct H
             | [   |- _ /\ _    ] => split
             | [ x : option _ |- _ ] => destruct x
             | [ x : bool        |- _ ] => destruct x
             | [ x : _ * _    |- _ ] => destruct x

             | [ H : context [ match ?x with _ => _ end ] |- _ ] => let E := fresh "E" in destruct x eqn:E
             | [   |- context [ match ?x with _ => _ end ]     ] => let E := fresh "E" in destruct x eqn:E
               
             | _ => T2
             end
           ).

  Tactic Notation "CertificateMyProgram" := CertificateMyProgram before (idtac) after (idtac).
  Tactic Notation "CertificateMyProgram" "after" tactic(T2) := CertificateMyProgram before (idtac) after (T2).
  Tactic Notation "CertificateMyProgram" "before" tactic(T1) := CertificateMyProgram before (T1) after (idtac).

  Lemma M1_RealiseIn :
    M1 ⊨c(3) M1_Rel.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold M1. eapply Match_RealiseIn. eapply read_char_sem. cbn.
      instantiate (2 := fun o : option sig => match o with Some x => if f x then _ else _ | None => _ end).
      intros [ | ]; cbn.
      - destruct (f e). 
        + instantiate (1 := 1). eapply mono_Nop_Sem.
        + eapply Move_Sem.
      - eapply mono_Nop_Sem.
    }
    (cbn; omega).
    unfold M1_Rel, M1_Fun. CertificateMyProgram after (now eauto 6).
  Qed.

  (*
   * The main loop of the machine.
   * Execute M1 in a loop until M1 returned [ None ] or [ Some true ]
   *)
  Definition M2 : { M : mTM sig 1 & states M -> bool } :=
    WHILE
      (
        MATCH M1
              (fun o : option bool =>
                 match o with
                 | Some true  => mono_Nop _ (false,  true) (* found the symbol, break and return true *)
                 | Some false => mono_Nop _ (true,  false) (* not found the symbol yet, continue *)
                 | None       => mono_Nop _ (false, false) (* there is no such symbol, break and return false *)
                 end
              )
      ).
      
  Definition rlength (t : tape sig) :=
    match t with
    | niltape _ => 0
    | rightof _ _ => 0
    | midtape ls m rs => 1 + length rs
    | leftof r rs => 2 + length rs
    end.

  (* Function of M2 *)
  Function M2_Fun (t : tape sig) { measure rlength t } : tape sig :=
    match t with
    | midtape ls m rs => if f m then t else M2_Fun (tape_move_right t)
    | _ => t
    end.
  Proof.
    all: (intros; try now (cbn; omega)). destruct rs; cbn; omega.
  Qed.
  Hint Rewrite M2_Fun_equation : tapes.

  Lemma M1_Fun_M2_None t :
    current t = None ->
    M2_Fun t = M1_Fun t.
  Proof.
    intros H1. destruct t; cbn in *; inv H1; rewrite M2_Fun_equation; auto.
  Qed.

  Lemma M1_None t :
    current t = None ->
    M1_Fun t = t.
  Proof.
    intros H1. unfold M1_Fun. destruct t; cbn in *; inv H1; auto.
  Qed.

  Lemma M1_true t x :
    current t = Some x ->
    f x = true ->
    M1_Fun t = t.
  Proof.
    intros H1 H2. unfold M1_Fun. destruct t; cbn in *; inv H1. rewrite H2. auto.
  Qed.
  
  Lemma M1_Fun_M2_true t x :
    current t = Some x ->
    f x = true ->
    M2_Fun t = M1_Fun t.
  Proof.
    intros H1 H2. destruct t; cbn in *; inv H1. rewrite M2_Fun_equation, H2. auto.
  Qed.

  Lemma M2_M1_false t x :
    current t = Some x ->
    f x = false ->
    M2_Fun (M1_Fun t) = M2_Fun t.
  Proof.
    intros H1 H2. functional induction M2_Fun t; cbn.
    - rewrite e0. rewrite M2_Fun_equation. rewrite e0. reflexivity.
    - rewrite e0. destruct rs; auto.
    - destruct _x; rewrite M2_Fun_equation; cbn; auto.
  Qed.

  
  Definition M2_Rel : Rel (tapes sig 1) (bool * tapes sig 1) :=
    Mk_R_p (fun tin '(yout, tout) =>
              tout = M2_Fun tin /\
              (
                (yout = true  /\ exists s, current tout = Some s /\ f s = true ) \/
                (yout = false /\ current tout = None)
              )
           ).

  Lemma M2_WRealise :
    M2 ⊫ M2_Rel.
  Proof.
    eapply WRealise_monotone.
    {
      unfold M2. eapply While_WRealise. eapply Match_WRealise.
      - eapply Realise_WRealise. eapply RealiseIn_Realise. eapply M1_RealiseIn.
      - cbn in *. instantiate (1 := fun o => match o with Some true => _ | Some false => _ | None => _ end).
        intros [ [ | ] | ]. all: eapply Realise_WRealise. all: eapply RealiseIn_Realise. all: eapply mono_Nop_Sem.
    }
    {
      hnf. intros tin (y1&tout) H. hnf in *. destruct H as (t1&H&H2). hnf in *.
      induction H as [x | x y z IH1 _ IH2].
      {
        destruct H2 as (f2&H2). hnf in *. destruct H2 as (y&H2). hnf in *. destruct H2 as (H2&H3). hnf in *.
        repeat (intuition; hnf in *; subst).
        all: inv H0.
        all: try destruct H2 as (s&H2&H2'). all: hnf in *. all: intuition.
        all: destruct_tapes; cbn in *.
        - erewrite M1_Fun_M2_true; eauto.
        - left. split; auto. eexists. split; eauto. destruct h0; cbn in *; inv H2. rewrite H2'. cbn. reflexivity.
        - destruct h0; cbn in *; rewrite M2_Fun_equation; auto. destruct (f e); auto. cbn. rewrite M2_Fun_equation.
          destruct l0; cbn in *; subst; auto. cbn in *. congruence.
      }
      {
        Time CertificateMyProgram before
             (
               idtac "Before";
                 repeat progress (unfold M1_Rel, M2_Rel, Mk_R_p);
                 intuition; try congruence;
                   match goal with
                   | [ H : star _ _ _ |- _ ] =>
                     idtac H;
                       let x := fresh "x" in
                       let y := fresh "y" in
                       let z := fresh "z" in
                       let IH1 := fresh "IH1" in
                       let IH2 := fresh "IH2" in
                       induction H as [x | x y z IH1 _ IH2]
                   | _ => idtac
                   end
             )
             after
             (
               idtac "After";
                 eauto 6
             ); eauto 6.

        - rewrite H5. eapply M2_M1_false; eauto.
        - eapply M2_M1_false; eauto.

      }
    }

    (*
    {
      Time CertificateMyProgram before
           (
             idtac "Before";
               repeat progress (unfold M1_Rel, M2_Rel, Mk_R_p);
               intuition; try congruence;
                 match goal with
                 | [ H : star _ _ _ |- _ ] =>
                   idtac H;
                     let x := fresh "x" in
                     let y := fresh "y" in
                     let z := fresh "z" in
                     let IH1 := fresh "IH1" in
                     let IH2 := fresh "IH2" in
                     induction H as [x | x y z IH1 _ IH2]
                 | _ => idtac
                 end
           )
           after
           (
             idtac "After";
               eauto 6
           ); eauto 6.
      - admit.
      - admit.
      - left. split; auto. eexists; split; eauto. rewrite <- H3. f_equal. destruct h2; cbn in *; simpl_tape in *; try congruence.
        inv H3. rewrite H4. auto.


    } *)
  Qed.


  Lemma M2_Fun_tapesToList t : tapeToList (M2_Fun t) = tapeToList t .
  Proof.
    functional induction M2_Fun t; try reflexivity; simpl_tape in *; congruence.
  Qed.
  Hint Rewrite M2_Fun_tapesToList : tapes.

  Lemma tape_move_niltape (t : tape sig) (D : move) : tape_move t D = niltape _ -> t = niltape _.
  Proof. destruct t, D; cbn; intros; try congruence. destruct l; congruence. destruct l0; congruence. Qed.

  Lemma M2_Fun_niltape t : M2_Fun t = niltape _ -> t = niltape _.
  Proof.
    intros H. remember (niltape sig) as N. functional induction M2_Fun t; subst; try congruence.
    - specialize (IHt0 H). destruct rs; cbn in *; congruence.
    (* - specialize (IHt0 H). destruct rs; cbn in *; congruence. *)
  Qed.


  (* Now we combine M1 and M2 and get get the final Machine, MoveToSymbol.
   * It returns true iff it has found the symbol.
   *)


  Definition MoveToSymbol : { M : mTM sig 1 & states M -> bool } :=
    MATCH M1
          (fun o : option bool =>
             match o with
             | Some true => mono_Nop _ true
             | _ => Move _ R tt ;; M2
             end).

  Definition MoveToSymbol_Fun :=
    fun t =>
      match M1_Fun t with
      | midtape _ m _ as t' => if f m then t' else M2_Fun t'
      | _ as t' => M2_Fun (tape_move_right t')
      end.
  
  Lemma MoveToSymbol_true t x :
    current t = Some x ->
    f x = true ->
    MoveToSymbol_Fun t = t.
  Proof.
    intros H1 H2. unfold MoveToSymbol_Fun. erewrite M1_true; eauto.
    destruct t eqn:E; try rewrite M2_Fun_equation; auto; cbn in *; inv H1. now rewrite H2.
  Qed.

  Lemma M2_M2 t :
    M2_Fun (M2_Fun t) = M2_Fun t.
  Proof.
    functional induction M2_Fun t; auto.
    - rewrite M2_Fun_equation; cbn; now rewrite e0.
    - destruct t; now rewrite M2_Fun_equation.
  Qed.

  Lemma M1_M2 t :
    M1_Fun (M2_Fun t) = M2_Fun t.
  Proof.
    functional induction M2_Fun t; auto.
    - cbn. now rewrite e0.
    - destruct t; cbn; auto.
  Qed.

  (* TODO: Finish *)

  Definition MoveToSymbol_Rel : Rel (tapes sig 1) (FinType (EqType bool) * tapes sig 1) :=
    Mk_R_p ((if? (fun t t' => exists s, current t' = Some s /\ f s = true)
               ! (fun t t' => current t' = None)) ∩ ignoreParam (fun t t' => MoveToSymbol_Fun t = t')).

  Lemma MoveToSymbol_WRealise :
     MoveToSymbol ⊫ MoveToSymbol_Rel.
  Proof.
    eapply WRealise_monotone.
    {
      unfold MoveToSymbol. eapply Match_WRealise.
      - eapply Realise_WRealise. eapply RealiseIn_Realise. eapply M1_RealiseIn.
      - cbn in *. instantiate (1 := fun o : option bool => match o with Some true => _ | _ => _ end).
        intros [ [ | ] | ].
        1: eapply Realise_WRealise; eapply RealiseIn_Realise; eapply mono_Nop_Sem.
        1-2: eapply Seq_WRealise; [eapply Realise_WRealise; eapply RealiseIn_Realise; eapply Move_Sem | eapply M2_WRealise].
    }
    {
      CertificateMyProgram; eauto; subst.
      - erewrite M1_true; eauto.
      - erewrite MoveToSymbol_true, M1_true; eauto.
      - unfold MoveToSymbol_Fun.
        destruct h; cbn; try rewrite M2_Fun_equation at 1; auto; cbn in *. inv H2. admit. admit. admit.
      - destruct h; cbn in *; try congruence. inv H2. rewrite H3. unfold MoveToSymbol_Fun. cbn. rewrite H3 in *.
        destruct l0; cbn in *; auto. destruct (f e); cbn. rewrite M2_Fun_equation. admit. admit.
      - admit.
      - admit.
    }
  Admitted.


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
  Lemma MoveToSymbol_TerminatesIn :
    projT1 (MoveToSymbol) ↓ (fun x i => i = 11 * time_until_symbol_r (x[@Fin.F1])).
  Proof.
    (*
    unfold MoveToSymbol_R. simpl projT1.
    eapply While_terminatesIn.
    {
      unfold M_R. eapply Match_WRealise.
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
      unfold M_R. simpl. eapply Match_TerminatesIn. shelve.
      - eapply Realise_WRealise. eapply RealiseIn_Realise. eapply Peek_RealisesIn.
      - eapply Realise_total. eapply Peek_RealisesIn.
      - instantiate (1 := (fun o => match o with
                               | inl true => _
                               | inl false => _
                               | inr L => _ | inr _ => _
                               end)).
        intros r. cbn in r. destruct r as [ [ | ] | D' ] eqn:E.
        + eapply Realise_total. eapply mono_Nop_Sem.
        + eapply Realise_total. eapply Move_Sem.
        + destruct D'; eapply Realise_total; eapply mono_Nop_Sem.
          Unshelve.
          {
            (* TODO: Automatisation !!!! *)
            hnf. unfold Peek_Rel, Mk_R_p. intros.
            destruct z1, z2. destruct H0 as (H0&H0'). destruct H1 as (H1&H1').
            destruct_tapes. hnf in *. cbn in *. subst. destruct h1; congruence.
          }
    }
    {
      (* TODO: Automatisation !!!! *)
      hnf. admit.
    }
    {
      intros ? ? ?. hnf. destruct_tapes. hnf in *.
      exists ([| moveToSymbol_R h |]). unfold finType_CS. admit.
    }
    
    
    
      
    
    
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
*)
  Admitted.


  Lemma MoveToSymbol_Realise : 
    MoveToSymbol ⊨ MoveToSymbol_Rel.
  Proof.
    eapply WRealise_to_Realise.
    - cbn. eapply MoveToSymbol_TerminatesIn.
    - firstorder. eexists. eauto.
    - eapply MoveToSymbol_WRealise.
  Qed.


  (** Move to left *)

  (*


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

  Lemma moveToSymbol_mirror t t' :
    MoveToSymbol_Rel (mirror_tape t) = mirror_tape t' -> moveToSymbol_L t = t'.
  Proof.
    functional induction moveToSymbol_L t; intros H; cbn in *; try reflexivity;
      try rewrite moveToSymbol_R_equation in H; cbn; auto.
    - destruct t'; cbn in *; congruence.
    - destruct t'; cbn in *; try apply moveToSymbol_niltape_R in H; try congruence.
    - destruct t'; cbn in *; try apply moveToSymbol_niltape_R in H; try rewrite e0 in H; congruence.
    - rewrite e0 in H. cbn in H. apply IHt0. destruct ls; cbn; auto.
  Qed.


  Definition MoveToSymbol_L_Rel : Rel (tapes sig 1) (FinType (EqType bool) * tapes sig 1) :=
    Mk_R_p ((if? (fun t t' => exists s, current t' = Some s /\ f s = true)
               ! (fun t t' => current t' = None)) ∩ ignoreParam (fun t t' => moveToSymbol_L t = t')).


  Definition MoveToSymbol_L := Mirror MoveToSymbol_R.

  (* TODO: Reduce Termination, from termination of MoveTosymbol_R *)
  Lemma MoveToSymbol_L_WRealise :
    MoveToSymbol_L ⊫ MoveToSymbol_L_Rel.
  Proof.
    eapply WRealise_monotone.
    - eapply Mirror_WRealise. eapply MoveToSymbol_R_WRealise.
    - intros tin (y&tout) H. hnf in *. destruct_tapes; cbn in *. destruct H as (H1&H2); hnf in *.
      split; hnf.
      + now rewrite mirror_tape_current in H1.
      + clear H1. now apply moveToSymbol_mirror.
  Qed.

*)

End move_to_symbol.