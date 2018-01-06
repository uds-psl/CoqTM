Require Import TM.Prelim.
Require Import TM.Basic.Mono.
Require Import TM.Combinators.Match TM.Combinators.While TM.Combinators.SequentialComposition.
Require Import TM.Compound.Peek.
Require Import TM.Mirror.
Require Import TM.Compound.TMTac.

Require Import FunInd.
Require Import Recdef.

Ltac deq x := let H := fresh in destruct (Dec (x = x)) as [? | H]; [ | now contradiction H].

Section move_to_symbol.
  
  Variable sig : finType.
  Variable f : sig -> bool.

  (*
   * One Step:
   * Read one symbol.  If there was no symbol, return [ None ].
   * If the read symbol fulfills [ f ], return [ Some true ].
   * Else move one to the right and return [ Some false ].
   *)
  Definition M1 : { M : mTM sig 1 & states M -> bool * bool} :=
    MATCH (Read_char _)
          (fun b : option sig =>
             match b with
             | Some x => if f x
                        then mono_Nop _ (false, true) (* found the symbol, break and return true *)
                        else Move _ R (true, false) (* wrong symbol, move right and continue *)
             | _ => mono_Nop _ (false, false) (* there is no such symbol, break and return false *)
             end).

  Definition M1_Fun : tape sig -> tape sig :=
    fun t1 =>
      match t1 with
      | midtape ls x rs => if (f x) then t1 else tape_move_right t1
      | _ => t1
      end.

  Definition M1_Rel : Rel (tapes sig 1) (bool * bool * tapes sig 1) :=
    Mk_R_p (fun tin '(yout, tout) =>
              tout = M1_Fun tin /\
              (
                (yout = (false, true)  /\ exists s, current tin = Some s /\ f s = true ) \/
                (yout = (true, false)  /\ exists s, current tin = Some s /\ f s = false) \/
                (yout = (false, false) /\ current tout = None)
              )
           ).  

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
    {
      (cbn; omega).
    }
    {
      unfold M1_Rel, M1_Fun.
      TMCrush idtac; TMSolve 6.
    }
  Qed.

  (*** FIXME: DAS STIMMT NICHT!!!! Es muss ein anderer Weg gefunden werden, Terminierung zu zeigen! *)
  Lemma M1_Rel_functional : functional M1_Rel.
  Proof.
    hnf. intros tin (b1,o1) (b2,o2) (H1&H1') (H2&H2'). destruct_tapes; cbn in *. subst. f_equal.
    TMCrush idtac; auto. all:exfalso.
    - destruct h1; cbn in *; inv H0. rewrite H1 in H2. cbn in *. congruence.
    - destruct h1 eqn:E; cbn in *; inversion H. subst e. rewrite H0 in H1. destruct l0; cbn in *; inversion H1. admit.
    - destruct h1; cbn in *; inv H. rewrite H1 in H0. cbn in *. congruence.
    - destruct h1; cbn in *; inv H. rewrite H1 in H0. destruct l0; cbn in *; inv H0. admit.
  Admitted.

  (*
   * The main loop of the machine.
   * Execute M1 in a loop until M1 returned [ None ] or [ Some true ]
   *)
  Definition M2 : { M : mTM sig 1 & states M -> bool } := WHILE M1.
      
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
      unfold M2. eapply While_WRealise. eapply Realise_WRealise, RealiseIn_Realise. eapply M1_RealiseIn.
    }
    {

      hnf. intros tin (y1&tout) H. hnf in *. destruct H as (t1&H&H2). hnf in *.
      induction H as [x | x y z IH1 _ IH2].
      {
        TMCrush idtac; TMSolve 6.
        all: repeat progress (unfold M1_Fun, M1_Rel, M2_Rel, Mk_R_p in *).
        all: try rewrite M2_Fun_equation; auto.
        all: TMCrush idtac; TMSolve 6.
        now rewrite M2_Fun_equation.
      }
      {
        TMCrush idtac; TMSolve 6.
        all:
          try now
              (
                rewrite M2_Fun_equation; TMSimp; auto
              ).
        all: erewrite <- M2_M1_false; eauto.
      }
    }
  Qed.


  Lemma M2_Fun_tapesToList t : tapeToList (M2_Fun t) = tapeToList t .
  Proof.
    functional induction M2_Fun t; try reflexivity; simpl_tape in *; congruence.
  Qed.
  Hint Rewrite M2_Fun_tapesToList : tape.

  Lemma tape_move_niltape (t : tape sig) (D : move) : tape_move t D = niltape _ -> t = niltape _.
  Proof. destruct t, D; cbn; intros; try congruence. destruct l; congruence. destruct l0; congruence. Qed.

  Lemma M2_Fun_niltape t : M2_Fun t = niltape _ -> t = niltape _.
  Proof.
    intros H. remember (niltape sig) as N. functional induction M2_Fun t; subst; try congruence.
    - specialize (IHt0 H). destruct rs; cbn in *; congruence.
    (* - specialize (IHt0 H). destruct rs; cbn in *; congruence. *)
  Qed.


  (** Termination *)

  Function MoveToSymbol_TermTime (t : tape sig) { measure rlength t } : nat :=
    match t with
    | midtape ls m rs => if f m then 4 else S (S (S (S (MoveToSymbol_TermTime (tape_move_right t)))))
    | _ => 4
    end.
  Proof.
    all: (intros; try now (cbn; omega)). destruct rs; cbn; omega.
  Qed.
  Hint Rewrite MoveToSymbol_TermTime_equation : tape.


  (* Idee: Lösung des Problems kanonische Relation ranklatschen, damit die relation funktional wird. *)
  Lemma M2_terminates :
    projT1 M2 ↓ (fun tin k => k = MoveToSymbol_TermTime (tin[@Fin.F1])).
  Proof.
    eapply TerminatesIn_monotone.
    {
      cbn. eapply While_TerminatesIn_size; swap 1 2.
      - eapply M1_RealiseIn. (* hier *)
      - eapply M1_Rel_functional.
    }
    {
      intros tin k ->. destruct_tapes. cbn.
      destruct h; cbn.
      {
        rewrite MoveToSymbol_TermTime_equation.
        econstructor 1; autorewrite with tape. 2: omega.
        hnf. cbn. split. now instantiate (1 := [|niltape sig|]). cbn. auto.
      }
      {
        rewrite MoveToSymbol_TermTime_equation.
        econstructor 1; autorewrite with tape. 2: omega.
        hnf. cbn. split. now instantiate (1 := [|leftof e l|]). cbn. auto.
      }
      {
        rewrite MoveToSymbol_TermTime_equation.
        econstructor 1; autorewrite with tape. 2: omega.
        hnf. cbn. split. now instantiate (1 := [|rightof e l|]). cbn. auto.
      }
      {
        revert l e. induction l0 as [ | r rs IH]; intros.
        {
          rewrite MoveToSymbol_TermTime_equation.
          destruct (f e) eqn:E; cbn.
          - econstructor 1; autorewrite with tape. 2: omega.
            hnf. cbn. split. rewrite E. now instantiate (1 := [|midtape l e []|]). cbn; eauto 6.
          - autorewrite with tape.
            econstructor 2; autorewrite with tape. 3: instantiate (1 := 3); omega; swap 1 2.
            + hnf. split; cbn. rewrite E. now instantiate (1 := [|rightof e l|]). cbn. eauto 6.
            + econstructor. cbn. split. now instantiate (1 := [|rightof e l|]). eauto. omega.
        }
        {
          rewrite MoveToSymbol_TermTime_equation.
          destruct (f e) eqn:E.
          - econstructor 1. 2: omega. cbn. split. rewrite E. now instantiate (1 := [|midtape _ _ _|]). eauto.
          - econstructor 2. 2: now eapply IH. cbn. split. rewrite E. eauto. eauto 6. cbn. omega.
        }
      }
    }
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