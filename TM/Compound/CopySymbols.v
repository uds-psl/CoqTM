Require Import TM.Prelim.
Require Import TM.Basic.Mono TM.Basic.Multi.
Require Import TM.Combinators.Combinators.
Require Import TM.Mirror.
Require Import TM.Compound.TMTac.
Require Import TM.LiftMN.

Require Import FunInd.
Require Import Recdef.


(* This two-tape Turing machine copies the symbols from tape 0 to tape 1, until it reads a symbol x on tape 0 such that f(x)=true. *)
(* This machine is similar to MoveToSymbol, with the only difference, that it copies the read symbols to another tape. *)


Section CopySymbols.
  
  Variable sig : finType.
  (* Termination check *)
  Variable f : sig -> bool.
  (* translation *)
  Variable g : sig -> sig.

  Definition M1 : { M : mTM sig 2 & states M -> bool * unit} :=
    MATCH (ReadChar_multi _ Fin.F1)
          (fun b : option sig =>
             match b with
             | Some x =>
               (* First write the read symbol to tape 1 *)
               if f x
               then (* found the symbol: write it to tape 1; break and return true *)
                 Inject (Write (g x) (false, tt)) [|Fin.FS Fin.F1|]
               else (* wrong symbol: write it to tape 1 and move both tapes right and continue *)
                 Inject (Write (g x) tt) [|Fin.FS Fin.F1|];;
                 MovePar _ R R (true, tt)
             | _ => Nop _ _ (false, tt) (* there is no such symbol, break and return false *)
             end).

  Definition M1_Fun : tape sig * tape sig -> tape sig * tape sig :=
    fun '(t1, t2) =>
      match t1, t2 with
      | midtape ls x rs as t1, t2 =>
        if (f x)
        then (t1, tape_write t2 (Some (g x)))
        else (tape_move_right t1, tape_move_mono t2 (Some (g x), R))
      | t1, t2 => (t1, t2)
      end.

(*
End CopySymbols.
Section Test.
  Let f := fun x => Dec (x = L) : bool.
  Compute it (M1_Fun f) 0 (midtape [L; N; R] N [R; N; L; N], niltape _).
  Compute it (M1_Fun f) 1 (midtape [L; N; R] N [R; N; L; N], niltape _).
  Compute it (M1_Fun f) 2 (midtape [L; N; R] N [R; N; L; N], niltape _).
  Compute it (M1_Fun f) 3 (midtape [L; N; R] N [R; N; L; N], niltape _).
  Compute it (M1_Fun f) 4 (midtape [L; N; R] N [R; N; L; N], niltape _).
  Compute it (M1_Fun f) 5 (midtape [L; N; R] N [R; N; L; N], niltape _).

  (* Actually simulating the machine... :-) *)
  Let M' := projT1 (M1 f).
  Compute map_opt (@ctapes _ _ _) (loopM (M := M') 7 (initc M' [|midtape [L; N; R] N [R; N; L; N]; niltape _|])).
  Compute map_opt (@ctapes _ _ _) (loopM (M := M') 7 (initc M' [|midtape [N; L; N; R] R [N; L; N]; rightof N []|])).
  Compute map_opt (@ctapes _ _ _) (loopM (M := M') 7 (initc M' [|midtape [R; N; L; N; R] N [L; N]; rightof R [N]|])).
  Compute map_opt (@ctapes _ _ _) (loopM (M := M') 7 (initc M' [|midtape [N; R; N; L; N; R] L [N]; rightof N [R; N]|])).
  Compute map_opt (@ctapes _ _ _) (loopM (M := M') 7 (initc M' [|midtape [N; R; N; L; N; R] L [N]; midtape [N; R; N] L []|])).

End Test.
*)

  Definition M1_Rel : Rel (tapes sig 2) (bool * unit * tapes sig 2) :=
    (fun tin '(yout, tout) =>
       (tout[@Fin.F1], tout[@Fin.FS Fin.F1]) = M1_Fun (tin[@Fin.F1], tin[@Fin.FS Fin.F1]) /\
       (
         (yout = (false, tt) /\ exists s, current tin[@Fin.F1] = Some s /\ f s = true ) \/
         (yout = (true,  tt) /\ exists s, current tin[@Fin.F1] = Some s /\ f s = false) \/
         (yout = (false, tt) /\ current tin[@Fin.F1] = None)
       )
    ).

  Lemma M1_Rel_functional : functional M1_Rel.
  Proof. hnf. unfold M1_Rel, M1_Fun. TMCrush destruct_tapes; TMSolve 1. Qed.
  
  Lemma M1_RealiseIn :
    M1 ⊨c(7) M1_Rel.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold M1. eapply Match_RealiseIn. cbn. eapply Inject_RealisesIn; [vector_dupfree| eapply read_char_sem].
      instantiate (2 := fun o : option sig => match o with Some x => if f x then _ else _ | None => _ end).
      intros [ | ]; cbn.
      - destruct (f e); swap 1 2.
        + eapply Seq_RealiseIn. eapply Inject_RealisesIn; [vector_dupfree | eapply Write_Sem]. eapply MovePar_Sem.
        + cbn. eapply Inject_RealisesIn; [vector_dupfree | eapply Write_Sem].
      - cbn. eapply RealiseIn_monotone'. eapply Nop_total. omega.
    }
    {
      (cbn; omega).
    }
    {
      intros tin (yout, tout) H. TMCrush destruct_tapes; TMSolve 6.
    }
  Qed.

  (*
   * The main loop of the machine.
   * Execute M1 in a loop until M1 returned [ None ] or [ Some true ]
   *)
  Definition CopySymbols : { M : mTM sig 2 & states M -> unit } := WHILE M1.
  
  Definition rlength (t : tape sig) :=
    match t with
    | niltape _ => 0
    | rightof _ _ => 0
    | midtape ls m rs => 1 + length rs
    | leftof r rs => 2 + length rs
    end.

  Definition rlength' (tin : tape sig * tape sig) : nat := rlength (fst tin).

  (* Function of M2 *)
  Function CopySymbols_Fun (tin : tape sig * tape sig) { measure rlength' tin } : tape sig * tape sig :=
    match tin with
      (midtape ls m rs as t1, t2) =>
      if f m
      then (t1, tape_write t2 (Some (g m)))
      else CopySymbols_Fun (tape_move_right t1, tape_move_mono t2 (Some (g m), R))
    |  (t1, t2) => (t1, t2)
    end.
  Proof.
    all: (intros; try now (cbn; omega)).
    all: (intros; try now (cbn; omega)).
    destruct rs; cbn. omega.
    destruct rs; cbn. omega. omega.
  Qed.

  (* (* Test *)
End CopySymbols.
Section Test.
  Let f := fun x => Dec (x = L) : bool.
  Compute CopySymbols_Fun f (midtape [L; N; R] N [R; N; L; N], niltape _).
  Compute it (M1_Fun f) 4 (midtape [L; N; R] N [R; N; L; N], niltape _).
End Test.
   *)

  (*
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

   *)
  
  Definition CopySymbols_Rel : Rel (tapes sig 2) (unit * tapes sig 2) :=
    ignoreParam (fun tin tout => ((tout[@Fin.F1], tout[@Fin.FS Fin.F1]) = CopySymbols_Fun (tin[@Fin.F1], tin[@Fin.FS Fin.F1]))).

  Lemma CopySymbols_WRealise :
    CopySymbols ⊫ CopySymbols_Rel.
  Proof.
    eapply WRealise_monotone.
    {
      unfold CopySymbols. eapply While_WRealise. eapply Realise_WRealise, RealiseIn_Realise. eapply M1_RealiseIn.
    }
    {
      hnf. intros tin (y1&tout) H. hnf in *. destruct H as (t1&H&H2). hnf in *.
      induction H as [x | x y z IH1 _ IH2].
      {
        TMCrush destruct_tapes; TMSolve 6.
        all: cbn in *; rewrite CopySymbols_Fun_equation in *; auto. inv H0. cbn. now rewrite E.
      }
      {
        TMSimp destruct_tapes. destruct h3; cbn in *; TMSimp repeat inv_pair.
        - destruct H2 as [ [H2 (s&H2')] | [ [H2 (s&H2'&H2'')] | [ H2 ] ] ]; congruence.
        - destruct H2 as [ [H2 (s&H2')] | [ [H2 (s&H2'&H2'')] | [ H2 ] ] ]; congruence.
        - destruct H2 as [ [H2 (s&H2')] | [ [H2 (s&H2'&H2'')] | [ H2 ] ] ]; congruence.
        - destruct H2 as [ [H2 (s&H2')] | [ [H2 (s&H2'&H2'')] | [ H2 ] ] ]; try congruence.
          clear H2. inv H2'. rewrite H2'' in *. spec_assert IH2; [now auto| ]. clear H0.
          destruct h; cbn in *.
          + inv H. inv H1. rewrite CopySymbols_Fun_equation. rewrite H2''. cbn. auto.
          + inv H. inv H1. rewrite CopySymbols_Fun_equation. rewrite H2''. cbn. auto.
          + inv H. inv H1. rewrite CopySymbols_Fun_equation. rewrite H2''. cbn. auto.
          + destruct (f e) eqn:E; cbn in *.
            * inv H. destruct l0; cbn in *; inv H1; auto; rewrite CopySymbols_Fun_equation; cbn; rewrite H2''; cbn; auto.
            * inv H. destruct l0; cbn in *; inv H1; auto; rewrite CopySymbols_Fun_equation; cbn; rewrite H2''; cbn; auto.
      }
    }
  Qed.


  (** Termination *)

  Function CopySymbols_TermTime (t : tape sig) { measure rlength t } : nat :=
    match t with
    | midtape ls m rs => if f m then 8 else 8 + CopySymbols_TermTime (tape_move_right t)
    | _ => 8
    end.
  Proof.
    all: (intros; try now (cbn; omega)). destruct rs; cbn; omega.
  Qed.


  Lemma CopySymbols_terminates :
    projT1 CopySymbols ↓ (fun tin k => CopySymbols_TermTime (tin[@Fin.F1]) <= k).
  Proof.
    eapply While_terminatesIn.
    1-2: eapply Realise_total; eapply M1_RealiseIn.
    {
      eapply functional_functionalOn. apply M1_Rel_functional.
    }
    {
      intros tin k Hk. destruct_tapes. cbn.
      destruct h eqn:E; cbn in *; rewrite CopySymbols_TermTime_equation in *.
      - exists [|h;h0|], false. cbn. do 2 eexists; repeat split; eauto 6. congruence. omega.
      - exists [|h;h0|], false. cbn. do 2 eexists; repeat split; eauto 6. congruence. omega.
      - exists [|h;h0|], false. cbn. do 2 eexists; repeat split; eauto 6. congruence. omega.
      - destruct (f e) eqn:E2; cbn.
        + exists [|h; tape_write h0 (Some (g e))|], false. cbn.
          do 2 eexists; repeat split; eauto 7; try congruence. omega.
        + exists [|tape_move_right h; tape_move_mono h0 (Some (g e), R)|], true. cbn.
          destruct l0; rewrite E; cbn in *; do 2 eexists; repeat split; eauto 7.
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
      then (t1, tape_write t2 (Some (g m)))
      else CopySymbols_L_Fun (tape_move_left t1, tape_move_mono t2 (Some (g m), L))
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
      + eapply IHp; clear IHp. rewrite <- H; clear H.
        f_equal. f_equal.
        destruct (left t2); cbn; auto.
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

  Lemma CopySymbols_L_WRealise : CopySymbols_L ⊫ CopySymbols_L_Rel.
  Proof.
    eapply WRealise_monotone.
    { eapply Mirror_WRealise. eapply CopySymbols_WRealise. }
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

  
  Lemma CopySymbols_TermTime_mirror t :
    CopySymbols_L_TermTime t = CopySymbols_TermTime (mirror_tape t).
  Proof.
    functional induction CopySymbols_L_TermTime t; cbn; auto;
      simpl_tape in *; cbn in *;
        rewrite CopySymbols_TermTime_equation.
    - now rewrite e0.
    - now rewrite e0, IHn.
    - destruct t; cbn; auto.
  Qed.

  Lemma CopySymbols_L_terminates :
    projT1 CopySymbols_L ↓ (fun tin k => CopySymbols_L_TermTime (tin[@Fin.F1]) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    - eapply Mirror_Terminates. eapply CopySymbols_terminates.
    - cbn. intros tin k Hk. destruct_tapes; cbn. rewrite <- Hk. unfold mirror_tapes.
      rewrite CopySymbols_TermTime_mirror. cbn. auto.
  Qed.
  

End CopySymbols.


Ltac smpl_TM_CopySymbols :=
  match goal with
  | [ |- CopySymbols  _ _ ⊫ _ ] => eapply CopySymbols_WRealise
  | [ |- projT1 (CopySymbols _ _) ↓ _ ] => eapply CopySymbols_terminates
  | [ |- CopySymbols_L  _ _ ⊫ _ ] => eapply CopySymbols_L_WRealise
  | [ |- projT1 (CopySymbols_L _ _) ↓ _ ] => eapply CopySymbols_L_terminates
  end.

Smpl Add smpl_TM_CopySymbols : TM_Correct.