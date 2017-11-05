Require Import TM.Prelim.
Require Import TM.Basic.Mono.
Require Import TM.Combinators.Match TM.Combinators.While TM.Combinators.SequentialComposition.
(* Require Import TM.IsoTrans. (* tape_mirror, this shoud probably be moved elsewhere *) *)
Require Import TM.Compound.Peek.

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

  Fixpoint to_symbol_list_r l1 l2 :=
    match (l2,l1) with
    | ([],[]) => (false, niltape _)
    | ([], c :: l) => (false, rightof c l)
    | (c :: l, l1) => if f c then (true, midtape l1 c l) else to_symbol_list_r (c :: l1) l
    end.

  Fixpoint to_symbol_r t :=
    match t with
    | niltape _ => (false, niltape _)
    | leftof c r => to_symbol_list_r [] (c :: r) (* first move R *)
    | rightof c r => (false, rightof c r)
    | midtape l1 c l2 => to_symbol_list_r l1 (c :: l2)
    end.

  Lemma to_symbol_r_current_Some t s :
    f s = true -> current t = Some s -> to_symbol_r t = (true, t).
  Proof.
    intros. destruct t; cbn in *; try congruence. inv H0. now rewrite H.
  Qed.

  Lemma to_symbol_r_move_false t t' s :
    current t = Some s -> f s = false -> t' = tape_move t R -> to_symbol_r t = to_symbol_r t'.
  Proof.
    intros H1 H2 ->. destruct t; cbn in *; try congruence. inv H1. rewrite H2. cbn. destruct l0; cbn; auto.
  Qed.

  (* Symmetric definitions *)

  Fixpoint to_symbol_list_l l1 l2 {struct l2} :=
    match (l2,l1) with
    | ([],[]) => (false, niltape _)
    | ([], c :: l) => (false, leftof c l)
    | (c :: l, l1) => if f c then (true, midtape l c l1) else to_symbol_list_l (c :: l1) l
    end.

  Fixpoint to_symbol_l t :=
    match t with
    | niltape _ => (false, niltape _)
    | leftof c r => (false, leftof c r)
    | rightof c r => to_symbol_list_l [] (c :: r) (* first move L *)
    | midtape l1 c l2 => to_symbol_list_l l2 (c :: l1)
    end.

  (*
  Lemma to_symbol_mirror t x :
    x = to_symbol_r (mirror_tape t) ->
    to_symbol_l t = (fst x, mirror_tape (snd x)).
  Proof.
    intros ->. destruct t; cbn; try congruence. destruct (f e) eqn:E; cbn; try congruence.
    - admit.
    - revert l0 e E. induction l as [ |r rs IH]; intros ls e E; cbn in *; auto. destruct (f r) eqn:E2; cbn; auto.
  Qed.
  *)

  Lemma to_symbol_l_current_Some t s :
    f s = true -> current t = Some s -> to_symbol_l t = (true, t).
  Proof.
    intros. destruct t; cbn in *; try congruence. inv H0. now rewrite H.
  Qed.

  Lemma to_symbol_l_move_false t t' s :
    current t = Some s -> f s = false -> t' = tape_move t L -> to_symbol_l t = to_symbol_l t'.
  Proof.
    intros H1 H2 ->. destruct t; cbn in *; try congruence. inv H1. rewrite H2. cbn. destruct l; cbn; auto.
  Qed.


  (* Wrapper Function *)

  Definition toSymbol D t :=
    match D with
    | R => to_symbol_r t
    | L => to_symbol_l t
    | N => (false, t)
    end.
  
  Definition MoveToSymbol_Rel D : Rel _ (bool * _) :=
    Mk_R_p (fun t t' => t' = toSymbol D t /\ tapeToList t = tapeToList (snd t')).

  Lemma to_symbol_current_Some D t s :
    D = L \/ D = R -> f s = true -> current t = Some s -> toSymbol D t = (true, t).
  Proof.
    destruct 1 as [-> | ->]; cbn.
    - apply to_symbol_l_current_Some.
    - apply to_symbol_r_current_Some.
  Qed.

  Lemma to_symbol_move_false D t t' s :
    D = L \/ D = R -> current t = Some s -> f s = false -> t' = tape_move t D -> toSymbol D t = toSymbol D t'.
  Proof.
    destruct 1 as [-> | ->]; cbn.
    - apply to_symbol_l_move_false.
    - apply to_symbol_r_move_false.
  Qed.
    
  (* TODO: This proof should be monstly automatised *)
  Lemma MoveToSymbol_R_WRealise :
     MoveToSymbol R ⊫ MoveToSymbol_Rel R.
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
      - destruct P as [ [ | ] | ] eqn:Ep.
        + hnf in *. destruct H4 as (H4&->). inv H4. rewrite H2 in *. clear x H2.
          destruct (tout[@Fin.F1]) eqn:E; try congruence. inv H3.
          cbn. rewrite <- H0; auto.
        + hnf in *. destruct H4 as (H4&->). congruence.
        + {
            destruct (x[@Fin.F1]); inv H3; cbn in *; destruct H4 as (H4&->); inv H4; cbn; auto.
            - rewrite <- H2. auto.
            - rewrite <- H2. auto.
          }
      - rewrite H2 in *. clear z H2 IH2.
        hnf in *. destruct IH1 as (b1&P'&t3&(->&IH1)&IH2); cbn in *; hnf in *.
        specialize (IH3 eq_refl).

        destruct (t2[@Fin.F1]) eqn:E1; subst; hnf in *; try (destruct H4 as (H4&->); inv H4); subst.
        + specialize (IH3 eq_refl) as (IH3&IH4). rewrite E1 in *. cbn in *.
          {
            destruct (t3[@Fin.F1]) eqn:E2; subst; hnf in *; try (destruct IH2 as (IH2&->); inv IH2).
            - cbn. destruct (f e); cbn.


              rewrite E1, IH4 in *.
          }
          
          
          admit. 
        + admit.
        + admit.
    }
  Admitted.
    

        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        


  (* TODO: This proof should be monstly automatised *)
  Lemma MoveToSymbol_WRealise D :
    D = L \/ D = R -> MoveToSymbol D ⊫ MoveToSymbol_Rel D.
  Proof.
    intros HD. eapply WRealise_monotone.
    - eapply While_WRealise. unfold M1. eapply Match_WRealise.
      eapply Realise_WRealise. eapply RealiseIn_Realise. eapply Peek_RealisesIn.
      instantiate (1 := (fun o => match o with
                               | inl true => _
                               | inl false => _
                               | inr D' => if Dec (D' = D) || Dec (D' = N) then _ else _
                               end)).
      intros r. cbn in r. destruct r as [ [ | ] | D' ] eqn:E.
      + eapply Realise_WRealise, RealiseIn_Realise. eapply mono_Nop_Sem.
      + eapply Realise_WRealise. eapply RealiseIn_Realise. eapply Move_Sem.
      + {
          decide (D' = D) as [ -> | ].
          - cbn. eapply Realise_WRealise, RealiseIn_Realise. eapply mono_Nop_Sem.
          - cbn. decide (D' = N).
            + cbn. eapply Realise_WRealise, RealiseIn_Realise. eapply mono_Nop_Sem.
            + cbn. eapply Realise_WRealise, RealiseIn_Realise. eapply mono_Nop_Sem.
        }
    - intros tin (bout, tout). cbn in bout. intros H. hnf in *. destruct H as (t1&H1&P&t2&(H2&H3)&H4). hnf in *.
      induction H1 as [x | x y z IH1 IH2 IH3].
      + destruct P as [ [ | ] | ] eqn:Ep.
        * hnf in *. destruct H4 as (H4&->). inv H4. rewrite H2 in *. clear x H2.
          destruct (tout[@Fin.F1]) eqn:E; try congruence. inv H3.
          cbn. destruct HD as [-> | ->]; cbn; rewrite <- H0; auto.
        * hnf in *. destruct H4 as (H4&->). congruence.
        * {
            decide (m = D) as [-> | D1]; cbn in *.
            - destruct H4 as (H4&->). inv H4. destruct (x[@Fin.F1]); cbn in *; try congruence.
              + inv H3. cbn in *. rewrite <- H2. auto.
              + inv H3. rewrite <- H2. cbn. auto.
              + inv H3. rewrite <- H2. cbn. auto.
            - decide (m = N) as [-> | D2]; cbn in *.
              + destruct H4 as (H4&->). inv H4. destruct (x[@Fin.F1]); cbn in *; try congruence. inv H3. rewrite <- H2.
                destruct HD as [-> | ->]; cbn; auto.
              + destruct H4 as (H4&->). congruence.
          }
      + hnf in *. rewrite H2 in *. specialize (IH3 eq_refl). clear z H2 IH2.
        destruct IH1 as (b1&ob&t&(->&H1')&H1''). hnf in *. cbn in *.

        (* (* Mache das später *) *)
        destruct (t[@Fin.F1]) eqn:E; hnf in *; subst.
        * deq N; cbn in *. destruct HD as [-> | ->]; cbn in *; destruct H1'' as (?&?); congruence.
        * destruct HD as [-> | ->].
          -- deq L. cbn in *. destruct H1'' as (?&?); congruence.
          -- cbn in *. destruct H1'' as (H&->). inv H.
             {
               destruct (t2[@Fin.F1]); cbn in *; subst.
               - deq N. cbn in *. destruct H4 as (H4&->). inv H4. specialize (IH3 eq_refl) as (IH1&IH2).
                 admit.
               - admit.
               - admit.
               - admit.
             }
        * cbn in *. destruct HD as [-> | ->]; cbn in *.
          -- destruct H1'' as (H&H'). inv H. admit.
          -- cbn in *. destruct H1'' as (H&->). inv H.
        * {
            destruct (f e) eqn:E2; cbn in *.
            - destruct H1'' as (H1&H1'). congruence.
            - destruct H1'' as (H1&H1'). inv H1. rewrite H1' in *. clear y H1'.
              destruct (t2[@Fin.F1]) eqn:E3; subst; cbn in *.
              + specialize (IH3 eq_refl) as (IH1&IH2). rewrite IH1.
          }
          
  Qed.

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
    MoveToSymbol R ⊨ MoveToSymbol_Rel R.
  Proof.
    eapply WRealise_to_Realise.
    - cbn. eapply TerminatesIn_TerminatesAlways; auto. eapply MoveToSymbol_R_Term. eauto.
    - apply MoveToSymbol_WRealise. tauto.
  Qed.


  (** Move to left *)

  Lemma MoveToSymbol_L_Realise : 
    MoveToSymbol L ⊨ MoveToSymbol_Rel L.
  Proof.
  Admitted.

End move_to_symbol.