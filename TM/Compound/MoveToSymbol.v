Require Import TM.Prelim.
Require Import TM.Basic.Mono.
Require Import TM.Combinators.Combinators.
Require Import TM.Compound.TMTac.
Require Import TM.Compound.Multi.

Require Import FunInd.
Require Import Recdef.

Section move_to_symbol.
  
  Variable sig : finType.

  (** Halt function *)
  Variable f : sig -> bool.

  (** Rewrite function *)
  Variable g : sig -> sig.

  

  (*
   * One Step:
   * Read one symbol.  If there was no symbol, return [ None ].
   * If the read symbol fulfills [ f ], return [ Some true ].
   * Else move one to the right and return [ Some false ].
   *)
  Definition M1 : { M : mTM sig 1 & states M -> option unit} :=
    MATCH (ReadChar)
          (fun b : option sig =>
             match b with
             | Some x => if f x
                        then Return (Nop) (Some tt) (* found the symbol, break *)
                        else Return (WriteMove (g x) R) (None) (* wrong symbol, move right and continue *)
             | _ => Return (Nop) (Some tt) (* there is no such symbol, break *)
             end).

  Definition M1_Fun : tape sig -> tape sig :=
    fun t1 =>
      match t1 with
      | midtape ls x rs => if (f x) then t1 else tape_move_mono t1 (Some (g x), R)
      | _ => t1
      end.

  Definition M1_Rel : Rel (tapes sig 1) (option unit * tapes sig 1) :=
    Mk_R_p (fun tin '(yout, tout) =>
              tout = M1_Fun tin /\
              match tin with
              | midtape _ m _ =>
                yout = if f m
                       then Some tt (* break *)
                       else None (* continue *) 
              | _ => yout = (Some tt) (* break *)
              end
           ).  

  Lemma M1_RealiseIn :
    M1 ⊨c(3) M1_Rel.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold M1. eapply Match_RealiseIn. eapply ReadChar_Sem. cbn.
      instantiate (2 := fun o : option sig => match o with Some x => if f x then _ else _ | None => _ end).
      intros [ | ]; cbn.
      - destruct (f e). 
        + instantiate (1 := 1). apply Return_RealiseIn. eapply Nop_Sem.
        + apply Return_RealiseIn. eapply WriteMove_Sem.
      - apply Return_RealiseIn. eapply Nop_Sem.
    }
    {
      (cbn; omega).
    }
    {
      unfold M1_Rel, M1_Fun. intros tin (yout, tout) H.
      TMCrush idtac; TMSolve 6.
    }
  Qed.

  (*
   * The main loop of the machine.
   * Execute M1 in a loop until M1 returned [ None ] or [ Some true ]
   *)
  Definition MoveToSymbol : { M : mTM sig 1 & states M -> unit } := WHILE M1.
  
  Definition rlength (t : tape sig) :=
    match t with
    | niltape _ => 0
    | rightof _ _ => 0
    | midtape ls m rs => 1 + length rs
    | leftof r rs => 2 + length rs
    end.

  (* Function of M2 *)
  Function MoveToSymbol_Fun (t : tape sig) { measure rlength t } : tape sig :=
    match t with
    | midtape ls m rs => if f m then t else MoveToSymbol_Fun (tape_move_mono t (Some (g m), R))
    | _ => t
    end.
  Proof.
    all: (intros; try now (cbn; omega)). destruct rs; cbn; omega.
  Qed.

  Lemma M1_Fun_M2_None t :
    current t = None ->
    MoveToSymbol_Fun t = M1_Fun t.
  Proof.
    intros H1. destruct t; cbn in *; inv H1; rewrite MoveToSymbol_Fun_equation; auto.
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
    MoveToSymbol_Fun t = M1_Fun t.
  Proof.
    intros H1 H2. destruct t; cbn in *; inv H1. rewrite MoveToSymbol_Fun_equation, H2. auto.
  Qed.

  Lemma MoveToSymbol_M1_false t x :
    current t = Some x ->
    f x = false ->
    MoveToSymbol_Fun (M1_Fun t) = MoveToSymbol_Fun t.
  Proof.
    intros H1 H2. functional induction MoveToSymbol_Fun t; cbn.
    - rewrite e0. rewrite MoveToSymbol_Fun_equation. rewrite e0. reflexivity.
    - rewrite e0. destruct rs; auto.
    - destruct _x; rewrite MoveToSymbol_Fun_equation; cbn; auto.
  Qed.

  
  Definition MoveToSymbol_Rel : Rel (tapes sig 1) (unit * tapes sig 1) :=
    Mk_R_p (ignoreParam (fun tin tout => tout = MoveToSymbol_Fun tin)).


  Lemma MoveToSymbol_skip ls m rs :
    f m = false ->
    MoveToSymbol_Fun (midtape ls m rs) = MoveToSymbol_Fun (tape_move_mono (midtape ls m rs) (Some (g m), R)).
  Proof. intros. cbn. now rewrite MoveToSymbol_Fun_equation, H. Qed.
  
  Lemma MoveToSymbol_Realise :
    MoveToSymbol ⊨ MoveToSymbol_Rel.
  Proof.
    eapply Realise_monotone.
    {
      unfold MoveToSymbol. eapply While_Realise. eapply RealiseIn_Realise. eapply M1_RealiseIn.
    }
    {
      eapply WhileInduction; intros; hnf in *.
      - destruct HLastStep as (H1&H2); TMSimp.
        destruct tin[@Fin0]; cbn in *; inv H2; rewrite MoveToSymbol_Fun_equation; auto.
        destruct (f e); cbn in *; auto. congruence.
      - destruct HStar as (H1&H2); TMSimp.
        destruct tin[@Fin0]; cbn in *; inv H2.
        assert (f e = false) as E. destruct (f e); cbn in *; inv H0; auto. rewrite E in *.
        now rewrite MoveToSymbol_skip.
    }
  Qed.


  Lemma MoveToSymbol_Fun_niltape t : MoveToSymbol_Fun t = niltape _ -> t = niltape _.
  Proof.
    intros H. remember (niltape sig) as N. functional induction MoveToSymbol_Fun t; subst; try congruence.
    - specialize (IHt0 H). destruct rs; cbn in *; congruence.
      (* - specialize (IHt0 H). destruct rs; cbn in *; congruence. *)
  Qed.


  (** Termination *)

  Function MoveToSymbol_TermTime (t : tape sig) { measure rlength t } : nat :=
    match t with
    | midtape ls m rs => if f m then 4 else 4 + (MoveToSymbol_TermTime (tape_move_mono t (Some (g m), R)))
    | _ => 4
    end.
  Proof.
    all: (intros; try now (cbn; omega)). destruct rs; cbn; omega.
  Qed.


  Local Arguments plus : simpl never. Local Arguments mult : simpl never.

  Lemma MoveToSymbol_Terminates :
    projT1 MoveToSymbol ↓ (fun tin k => MoveToSymbol_TermTime (tin[@Fin.F1]) <= k).
  Proof.
    eapply While_TerminatesIn.
    1-2: eapply Realise_total; eapply M1_RealiseIn.
    {
      intros tin k Hk. destruct tin[@Fin0] eqn:E; rewrite MoveToSymbol_TermTime_equation in *; cbn in *; try rewrite E.
      - eexists. split. eauto. intros o tmid (H1&H2); inv H2. omega.
      - eexists. split. eauto. intros o tmid (H1&H2); inv H2. omega.
      - eexists. split. eauto. intros o tmid (H1&H2); inv H2. omega.
      - destruct (f e) eqn:E2.
        + eexists. split. eauto. intros o tmid (H1&H2); inv H2. omega.
        + eexists. split. eauto. intros o tmid (H1&H2); inv H2; TMSimp.
          exists (MoveToSymbol_TermTime (tape_move_mono (midtape l e l0) (Some (g e), R))). cbn. repeat split; auto.
    }
  Qed.
  
  
  

  (** Move to left *)

  Definition MoveToSymbol_L := Mirror MoveToSymbol.

  
  Definition llength (t : tape sig) :=
    match t with
    | niltape _ => 0
    | leftof _ _ => 0
    | midtape ls m rs => 1 + length ls
    | rightof l ls => 2 + length ls
    end.

  Function MoveToSymbol_L_Fun (t : tape sig) { measure llength t } : tape sig :=
    match t with
    | midtape ls m rs => if f m then t else MoveToSymbol_L_Fun (tape_move_mono t (Some (g m), L))
    | _ => t
    end.
  Proof.
    all: (intros; try now (cbn; omega)). destruct ls; cbn; omega.
  Qed.

  Lemma MoveToSymbol_mirror t t' :
    MoveToSymbol_Fun (mirror_tape t) = mirror_tape t' -> MoveToSymbol_L_Fun t = t'.
  Proof.
    functional induction MoveToSymbol_L_Fun t; intros H; cbn in *; try reflexivity;
      rewrite MoveToSymbol_Fun_equation in H; cbn; auto.
    - rewrite e0 in *; cbn in *; destruct t'; cbn in *; congruence.
    - rewrite e0 in *; cbn in *. destruct ls; cbn in *; rewrite MoveToSymbol_Fun_equation, MoveToSymbol_L_Fun_equation in *.
      + destruct t'; cbn in *; now inv H.
      + destruct (f e) eqn:E1; cbn in *; eauto.
    - destruct t, t'; cbn in *; auto; congruence.
  Qed.


  Lemma MoveToSymbol_mirror' t t' :
    MoveToSymbol_L_Fun (mirror_tape t) = mirror_tape t' -> MoveToSymbol_Fun t = t'.
  Proof.
    functional induction MoveToSymbol_Fun t; intros H; cbn in *; try reflexivity;
      rewrite MoveToSymbol_L_Fun_equation in H; cbn; auto.
    - rewrite e0 in *; cbn in *; destruct t'; cbn in *; congruence.
    - rewrite e0 in *; cbn in *. destruct rs; cbn in *; rewrite MoveToSymbol_Fun_equation, MoveToSymbol_L_Fun_equation in *.
      + destruct t'; cbn in *; now inv H.
      + destruct (f e) eqn:E1; cbn in *; eauto.
    - destruct t, t'; cbn in *; auto; congruence.
  Qed.

  Definition MoveToSymbol_L_Rel : Rel (tapes sig 1) (unit * tapes sig 1) :=
    Mk_R_p (ignoreParam (fun tin tout => tout = MoveToSymbol_L_Fun tin)).

  Lemma MoveToSymbol_L_Realise :
    MoveToSymbol_L ⊨ MoveToSymbol_L_Rel.
  Proof.
    eapply Realise_monotone.
    - eapply Mirror_Realise. eapply MoveToSymbol_Realise.
    - intros tin (y&tout) H. hnf in *. destruct_tapes; cbn in *. rewrite mirror_tapes_nth in H. cbn in H.
      symmetry in H. apply MoveToSymbol_mirror in H as ->. TMCrush simpl_tape in *; TMSolve 6.
  Qed.


  Function MoveToSymbol_L_TermTime (t : tape sig) { measure llength t } : nat :=
    match t with
    | midtape ls m rs => if f m then 4 else 4 + (MoveToSymbol_L_TermTime (tape_move_mono t (Some (g m), L)))
    | _ => 4
    end.
  Proof.
    all: (intros; try now (cbn; omega)). destruct ls; cbn; omega.
  Qed.

  Lemma MoveToSymbol_TermTime_mirror t :
    MoveToSymbol_L_TermTime t = MoveToSymbol_TermTime (mirror_tape t).
  Proof.
    functional induction MoveToSymbol_L_TermTime t; cbn; auto;
      simpl_tape in *; cbn in *;
        rewrite MoveToSymbol_TermTime_equation.
    - now rewrite e0.
    - rewrite e0, IHn. cbn. now simpl_tape.
    - destruct t; cbn; auto.
  Qed.

  Lemma MoveToSymbol_L_Terminates :
    projT1 MoveToSymbol_L ↓ (fun tin k => MoveToSymbol_L_TermTime (tin[@Fin.F1]) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    - eapply Mirror_Terminates. eapply MoveToSymbol_Terminates.
    - cbn. intros tin k Hk. destruct_tapes; cbn. rewrite <- Hk. unfold mirror_tapes. rewrite MoveToSymbol_TermTime_mirror. cbn. auto.
  Qed.

End move_to_symbol.

Ltac smpl_TM_MoveToSymbol :=
  match goal with
  | [ |- MoveToSymbol   _ _ ⊨ _ ] => eapply MoveToSymbol_Realise
  | [ |- MoveToSymbol_L _ _ ⊨ _ ] => eapply MoveToSymbol_L_Realise
  | [ |- projT1 (MoveToSymbol   _ _) ↓ _ ] => eapply MoveToSymbol_Terminates
  | [ |- projT1 (MoveToSymbol_L _ _) ↓ _ ] => eapply MoveToSymbol_L_Terminates
  end.

Smpl Add smpl_TM_MoveToSymbol : TM_Correct.