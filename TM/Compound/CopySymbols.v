Require Import TM.Prelim.
Require Import TM.Basic.Mono.
Require Import TM.Combinators.Combinators.
Require Import TM.Compound.TMTac TM.Compound.Multi.
Require Import TM.Lifting.LiftTapes.

Require Import FunInd.
Require Import Recdef.


(* This two-tape Turing machine copies the symbols from tape 0 to tape 1, until it reads a symbol x on tape 0 such that f(x)=true. *)
(* This machine is similar to MoveToSymbol, with the only difference, that it copies the read symbols to another tape. *)


Section CopySymbols.

  Variable sig : finType.
  (* Termination check *)
  Variable f : sig -> bool.

  Definition CopySymbols_Step : { M : mTM sig 2 & states M -> option unit} :=
    MATCH (ReadChar_at Fin0)
          (fun b : option sig =>
             match b with
             | Some x =>
               (* First write the read symbol to tape 1 *)
               if f x
               then (* found the symbol: write it to tape 1; break and return *)
                 Return (LiftTapes (Write x) [|Fin1|]) (Some tt)
               else (* wrong symbol: write it to tape 1 and move both tapes right and continue *)
                 Return (LiftTapes (Write x) [|Fin1|];;
                         MovePar R R) (None)
             | _ => Return Nop (Some tt) (* there is no such symbol, break and return *)
             end).

  Definition CopySymbols_Step_Rel : pRel sig (option unit) 2 :=
    fun tin '(yout, tout) =>
      match current tin[@Fin0] with
      | Some x =>
        if (f x)
        then tout[@Fin0] = tin[@Fin0] /\
             tout[@Fin1] = tape_write tin[@Fin1] (Some x) /\
             yout = Some tt (* break *)
        else tout[@Fin0] = tape_move_right tin[@Fin0] /\
             tout[@Fin1] = tape_move_mono tin[@Fin1] (Some x, R) /\
             yout = None (* continue *)
      | _ => tout = tin /\
            yout = Some tt
      end.

  Lemma CopySymbols_Step_Sem :
    CopySymbols_Step ⊨c(7) CopySymbols_Step_Rel.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold CopySymbols_Step. eapply Match_RealiseIn. cbn. eapply LiftTapes_RealiseIn; [vector_dupfree| eapply ReadChar_Sem].
      instantiate (2 := fun o : option sig => match o with Some x => if f x then _ else _ | None => _ end).
      intros [ | ]; cbn.
      - destruct (f e); swap 1 2.
        + apply Return_RealiseIn. eapply Seq_RealiseIn. eapply LiftTapes_RealiseIn; [vector_dupfree | eapply Write_Sem]. eapply MovePar_Sem.
        + apply Return_RealiseIn, LiftTapes_RealiseIn; [vector_dupfree | eapply Write_Sem].
      - cbn. eapply RealiseIn_monotone'. apply Return_RealiseIn. eapply Nop_Sem. omega.
    }
    { cbn. reflexivity. }
    {
      intros tin (yout, tout) H. TMCrush destruct_tapes; TMSolve 6.
    }
  Qed.

  (*
   * The main loop of the machine.
   * Execute CopySymbols_Step in a loop until CopySymbols_Step returned [ Some tt ]
   *)
  Definition CopySymbols : pTM sig unit 2 := WHILE CopySymbols_Step.

  Definition rlength (t : tape sig) :=
    match t with
    | niltape _ => 0
    | rightof _ _ => 0
    | midtape ls m rs => 1 + length rs
    | leftof r rs => 2 + length rs
    end.

  Definition rlength' (tin : tape sig * tape sig) : nat := rlength (fst tin).

  (* Function of CopySymbols *)
  Function CopySymbols_Fun (tin : tape sig * tape sig) { measure rlength' tin } : tape sig * tape sig :=
    match tin with
      (midtape ls m rs as t1, t2) =>
      if f m
      then (t1, tape_write t2 (Some m))
      else CopySymbols_Fun (tape_move_right t1, tape_move_mono t2 (Some m, R))
    |  (t1, t2) => (t1, t2)
    end.
  Proof.
    all: (intros; try now (cbn; omega)).
    all: (intros; try now (cbn; omega)).
    destruct rs; cbn. omega.
    destruct rs; cbn. omega. omega.
  Qed.


  Definition CopySymbols_Rel : Rel (tapes sig 2) (unit * tapes sig 2) :=
    ignoreParam (fun tin tout => ((tout[@Fin.F1], tout[@Fin.FS Fin.F1]) = CopySymbols_Fun (tin[@Fin.F1], tin[@Fin.FS Fin.F1]))).

  Lemma CopySymbols_skip ls m rs t2 :
    f m = false ->
    CopySymbols_Fun (midtape ls m rs, t2) = CopySymbols_Fun (tape_move_right (midtape ls m rs),
                                                             tape_move_mono t2 (Some m, R)).
  Proof. intros H. now rewrite CopySymbols_Fun_equation, H. Qed.


  Lemma CopySymbols_Realise :
    CopySymbols ⊨ CopySymbols_Rel.
  Proof.
    eapply Realise_monotone.
    {
      unfold CopySymbols. eapply While_Realise. eapply RealiseIn_Realise. eapply CopySymbols_Step_Sem.
    }
    {
      apply WhileInduction; intros; TMSimp.
      - destruct tin[@Fin0] eqn:E0; TMSimp; rewrite CopySymbols_Fun_equation; auto.
        destruct (f e); cbn in *; auto; destruct HLastStep as (HLS1&HLS2&HLS3); TMSimp; auto.
      - destruct tin[@Fin0] eqn:E; TMSimp; auto.
        destruct (f e) eqn:Ee; destruct HStar as (HS1&HS2&HS3); TMSimp.
        now rewrite CopySymbols_skip.
    }
  Qed.


  (** Termination *)

  Function CopySymbols_Steps (t : tape sig) { measure rlength t } : nat :=
    match t with
    | midtape ls m rs => if f m then 8 else 8 + CopySymbols_Steps (tape_move_right t)
    | _ => 8
    end.
  Proof.
    all: (intros; try now (cbn; omega)). destruct rs; cbn; omega.
  Qed.


  Lemma CopySymbols_Terminates :
    projT1 CopySymbols ↓ (fun tin k => CopySymbols_Steps (tin[@Fin.F1]) <= k).
  Proof.
    eapply While_TerminatesIn.
    1-2: eapply Realise_total; eapply CopySymbols_Step_Sem.
    {
      intros tin k Hk. destruct tin[@Fin0] eqn:E; rewrite CopySymbols_Steps_equation in *; cbn in *; try rewrite E.
      - eexists. split. eauto. intros o tmid (H1&H2); inv H2. omega.
      - eexists. split. eauto. intros o tmid (H1&H2); inv H2. omega.
      - eexists. split. eauto. intros o tmid (H1&H2); inv H2. omega.
      - destruct (f e) eqn:E2.
        + eexists. split. eauto. cbn. rewrite E2. intros o tmid (H1&H2); inv H2. omega.
        + eexists. split. eauto. cbn. rewrite E2. intros o tmid (H1&H2&->). TMSimp.
          exists (CopySymbols_Steps (tape_move_right' l e l0)). repeat split; auto.
    }
  Qed.


  (** Move to left *)

  Definition CopySymbols_L := Mirror CopySymbols.

  Definition llength (t : tape sig) :=
    match t with
    | midtape ls m rs => 1 + length ls
    | _ => 0
    end.

  Definition llength' (tin : tape sig * tape sig) : nat := llength (fst tin).

  Function CopySymbols_L_Fun (tin : tape sig * tape sig) { measure llength' tin } : tape sig * tape sig :=
    match tin with
      (midtape ls m rs as t1, t2) =>
      if f m
      then (t1, tape_write t2 (Some m))
      else CopySymbols_L_Fun (tape_move_left t1, tape_move_mono t2 (Some m, L))
    | (t1, t2) => (t1, t2)
    end.
  Proof.
    all: (intros; try now (cbn; omega)).
    destruct ls; cbn. omega. omega.
  Qed.


  Lemma CopySymbols_mirror t t' :
    CopySymbols_Fun (mirror_tape (fst t), mirror_tape (snd t)) =
    (mirror_tape (fst t'), mirror_tape (snd t')) ->
    CopySymbols_L_Fun t = t'.
  Proof.
    functional induction CopySymbols_L_Fun t; intros H; cbn in *; try reflexivity;
      rewrite CopySymbols_Fun_equation in H; cbn; auto.
    - rewrite e0 in H. cbn in *.
      destruct t' as (t1',t2'); cbn in *. inv H.
      apply mirror_tape_inv_midtape' in H1. subst.
      apply mirror_tape_inv_midtape' in H2. subst.
      simpl_tape. reflexivity.
    - rewrite e0 in H. cbn in *.
      destruct t' as (t1',t2'); cbn in *.
      destruct ls; cbn in *; simpl_tape in *.
      + rewrite CopySymbols_Fun_equation in H. inv H.
        apply mirror_tape_inv_rightof' in H1. subst.
        eapply IHp; clear IHp. rewrite CopySymbols_Fun_equation. f_equal. f_equal.
        destruct (left t2); cbn.
        * apply mirror_tape_inv_rightof' in H2. subst. reflexivity.
        * apply mirror_tape_inv_midtape' in H2. subst. reflexivity.
      + eapply IHp; clear IHp. now rewrite <- H; clear H.
    - destruct t' as (t1',t2'). destruct t1; cbn in *; inv H; auto.
      1: apply mirror_tape_inv_niltape' in H1.
      2: apply mirror_tape_inv_rightof' in H1.
      3: apply mirror_tape_inv_leftof' in H1.
      all: apply mirror_tape_injective in H2.
      all: congruence.
  Qed.


  Lemma CopySymbols_mirror' t t' :
    CopySymbols_L_Fun (mirror_tape (fst t), mirror_tape (snd t)) =
    (mirror_tape (fst t'), mirror_tape (snd t')) ->
    CopySymbols_Fun t = t'.
  Proof.
    functional induction CopySymbols_Fun t; intros H; cbn in *; try reflexivity;
      rewrite CopySymbols_L_Fun_equation in H; cbn; auto.
    - rewrite e0 in H. inv H.
      destruct t' as (t1',t2'). cbn in *.
      apply mirror_tape_inv_midtape' in H1.
      apply mirror_tape_inv_midtape' in H2.
      subst. simpl_tape. reflexivity.
    - rewrite e0 in H.
      destruct t' as (t1',t2'). cbn in *.
      eapply IHp; clear IHp. rewrite <- H; clear H.
      f_equal. f_equal; simpl_tape.
      + destruct rs; cbn; reflexivity.
      + destruct (right t2); cbn; reflexivity.
    - destruct t' as (t1',t2'). cbn in *.
      destruct t1; cbn in *; inv H; auto.
      1: apply mirror_tape_inv_niltape' in H1.
      2: apply mirror_tape_inv_rightof' in H1.
      3: apply mirror_tape_inv_leftof' in H1.
      all: apply mirror_tape_injective in H2.
      all: congruence.
  Qed.


  Definition CopySymbols_L_Rel : Rel (tapes sig 2) (unit * tapes sig 2) :=
    ignoreParam (fun tin tout => ((tout[@Fin.F1], tout[@Fin.FS Fin.F1]) = CopySymbols_L_Fun (tin[@Fin.F1], tin[@Fin.FS Fin.F1]))).

  Lemma CopySymbols_L_Realise : CopySymbols_L ⊨ CopySymbols_L_Rel.
  Proof.
    eapply Realise_monotone.
    { eapply Mirror_Realise. eapply CopySymbols_Realise. }
    { intros tin ((), tout) H. cbn in *.
      symmetry in H; symmetry. simpl_tape in H.
      apply CopySymbols_mirror; eauto.
    }
  Qed.


  Function CopySymbols_L_TermTime (t : tape sig) { measure llength t } : nat :=
    match t with
    | midtape ls m rs => if f m then 8 else 8 + CopySymbols_L_TermTime (tape_move_left t)
    | _ => 8
    end.
  Proof.
    all: (intros; try now (cbn; omega)). destruct ls; cbn; omega.
  Qed.


  Lemma CopySymbols_Steps_mirror t :
    CopySymbols_L_TermTime t = CopySymbols_Steps (mirror_tape t).
  Proof.
    functional induction CopySymbols_L_TermTime t; cbn; auto;
      simpl_tape in *; cbn in *;
        rewrite CopySymbols_Steps_equation.
    - now rewrite e0.
    - now rewrite e0, IHn.
    - destruct t; cbn; auto.
  Qed.

  Lemma CopySymbols_L_Terminates :
    projT1 CopySymbols_L ↓ (fun tin k => CopySymbols_L_TermTime (tin[@Fin.F1]) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    - eapply Mirror_Terminates. eapply CopySymbols_Terminates.
    - cbn. intros tin k Hk. destruct_tapes; cbn. rewrite <- Hk. unfold mirror_tapes.
      rewrite CopySymbols_Steps_mirror. cbn. auto.
  Qed.


End CopySymbols.


Ltac smpl_TM_CopySymbols :=
  match goal with
  | [ |- CopySymbols _ ⊨ _ ] => eapply CopySymbols_Realise
  | [ |- projT1 (CopySymbols _) ↓ _ ] => eapply CopySymbols_Terminates
  | [ |- CopySymbols_L _ ⊨ _ ] => eapply CopySymbols_L_Realise
  | [ |- projT1 (CopySymbols_L _) ↓ _ ] => eapply CopySymbols_L_Terminates
  end.

Smpl Add smpl_TM_CopySymbols : TM_Correct.