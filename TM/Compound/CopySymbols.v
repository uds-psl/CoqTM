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
  Variable stop : sig -> bool.
  (* translation *)
  Variable g : sig -> sig.

  Definition M1 : { M : mTM sig 2 & states M -> bool * unit} :=
    MATCH (ReadChar_multi _ Fin.F1)
          (fun b : option sig =>
             match b with
             | Some x =>
               (* First write the read symbol to tape 1 *)
               if stop x
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
        if (stop x)
        then (t1, tape_write t2 (Some (g x)))
        else (tape_move_right t1, tape_move_mono t2 (Some (g x), R))
      | t1, t2 => (t1, t2)
      end.

(*
End CopySymbols.
Section Test.
  Let stop := fun x => Dec (x = L) : bool.
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
         (yout = (false, tt) /\ exists s, current tin[@Fin.F1] = Some s /\ stop s = true ) \/
         (yout = (true,  tt) /\ exists s, current tin[@Fin.F1] = Some s /\ stop s = false) \/
         (yout = (false, tt) /\ current tin[@Fin.F1] = None)
       )
    ).

  Lemma M1_Rel_functional : functional M1_Rel.
  Proof. hnf. unfold M1_Rel, M1_Fun. TMCrush (cbn [Vector.nth] in *); TMSolve 1. Qed.

  Lemma M1_RealiseIn :
    M1 ⊨c(7) M1_Rel.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold M1. eapply Match_RealiseIn. cbn. eapply Inject_RealisesIn; [vector_dupfree| eapply read_char_sem].
      instantiate (2 := fun o : option sig => match o with Some x => if stop x then _ else _ | None => _ end).
      intros [ | ]; cbn.
      - destruct (stop e); swap 1 2.
        + eapply Seq_RealiseIn. eapply Inject_RealisesIn; [vector_dupfree | eapply Write_Sem]. eapply MovePar_Sem.
        + cbn. eapply Inject_RealisesIn; [vector_dupfree | eapply Write_Sem].
      - cbn. eapply RealiseIn_monotone'. eapply Nop_total. omega.
    }
    {
      (cbn; omega).
    }
    {
      TMCrush repeat simpl_not_in; TMSolve 1.
      all: cbn in *; try congruence; eauto; subst.
      all: TMCrush idtac; TMSolve 6.
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
      if stop m
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
  Let stop := fun x => Dec (x = L) : bool.
  Compute CopySymbols_Fun stop (midtape [L; N; R] N [R; N; L; N], niltape _).
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
    stop x = true ->
    M1_Fun t = t.
  Proof.
    intros H1 H2. unfold M1_Fun. destruct t; cbn in *; inv H1. rewrite H2. auto.
  Qed.
  
  Lemma M1_Fun_M2_true t x :
    current t = Some x ->
    stop x = true ->
    MoveToSymbol_Fun t = M1_Fun t.
  Proof.
    intros H1 H2. destruct t; cbn in *; inv H1. rewrite MoveToSymbol_Fun_equation, H2. auto.
  Qed.

  Lemma MoveToSymbol_M1_false t x :
    current t = Some x ->
    stop x = false ->
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
        TMCrush idtac; TMSolve 6.
        all: cbn in *; rewrite CopySymbols_Fun_equation in *; auto. inv H0. cbn. now rewrite E.
      }
      {
        TMSimp. destruct x as [], y1 as [].
        destruct h3; cbn in *; TMSimp repeat inv_pair.
        - destruct H2 as [ [H2 (s&H2')] | [ [H2 (s&H2'&H2'')] | [ H2 ] ] ]; congruence.
        - destruct H2 as [ [H2 (s&H2')] | [ [H2 (s&H2'&H2'')] | [ H2 ] ] ]; congruence.
        - destruct H2 as [ [H2 (s&H2')] | [ [H2 (s&H2'&H2'')] | [ H2 ] ] ]; congruence.
        - destruct H2 as [ [H2 (s&H2')] | [ [H2 (s&H2'&H2'')] | [ H2 ] ] ]; try congruence.
          clear H2. inv H2'. rewrite H2'' in *. spec_assert IH2; [now auto| ]. clear H0.
          destruct h; cbn in *.
          + inv H. inv H1. rewrite CopySymbols_Fun_equation. rewrite H2''. cbn. auto.
          + inv H. inv H1. rewrite CopySymbols_Fun_equation. rewrite H2''. cbn. auto.
          + inv H. inv H1. rewrite CopySymbols_Fun_equation. rewrite H2''. cbn. auto.
          + destruct (stop e) eqn:E; cbn in *.
            * inv H. destruct l0; cbn in *; inv H1; auto; rewrite CopySymbols_Fun_equation; cbn; rewrite H2''; cbn; auto.
            * inv H. destruct l0; cbn in *; inv H1; auto; rewrite CopySymbols_Fun_equation; cbn; rewrite H2''; cbn; auto.
      }
    }
  Qed.


  (** Termination *)

  Function CopySymbols_TermTime (t : tape sig) { measure rlength t } : nat :=
    match t with
    | midtape ls m rs => if stop m then 8 else 8 + CopySymbols_TermTime (tape_move_right t)
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
      destruct h eqn:E; rewrite CopySymbols_TermTime_equation in *; cbn in *.
      - exists [|h;h0|], false. cbn. do 2 eexists; repeat split; eauto 6; try congruence. omega.
      - exists [|h;h0|], false. cbn. do 2 eexists; repeat split; eauto 6; try congruence. omega.
      - exists [|h;h0|], false. cbn. do 2 eexists; repeat split; eauto 6; try congruence. omega.
      - destruct (stop e) eqn:E2; cbn.
        + exists [|h; tape_write h0 (Some (g e))|], false. cbn.
          do 2 eexists; repeat split; eauto 7; try congruence. omega.
        + exists [|tape_move_right h; tape_move_mono h0 (Some (g e), R)|], true. cbn.
          destruct l0; rewrite E; cbn in *; do 2 eexists; repeat split; eauto 7.
    }
  Qed.
  
    
  (** Move to left *)

  Definition CopySymbols_L := Mirror CopySymbols.


  
  (** * Alternative correctness statements *)


  Lemma CopySymbols_first tltr str1 x str2 tl' tr':
    (forall x', List.In x' str1 -> stop x' = false) ->
    (stop x = true) ->
    tape_local (fst tltr) = str1 ++ x :: str2 ->
    (tl', tr') = CopySymbols_Fun tltr ->
    tape_local tl' = x :: str2.
  Proof.
    intros H H0. destruct tltr as [tl tr]. intros H1 E0.
    destruct tl as [ | r rs | l ls | ls m rs]; cbn in *.
    1-3: rewrite CopySymbols_Fun_equation in E0; inv H1; exfalso; destruct str1; cbn in *; congruence.
    revert rs tr ls H ls m H1 tl' tr' E0. revert str1; intros str1.
    induction str1 as [ | s' str1' IHstr1]; (* cbn in *; *) intros.
    - cbn in *. inv H1. rewrite CopySymbols_Fun_equation in E0. rewrite H0 in E0. inv E0. cbn. auto.
    - rewrite CopySymbols_Fun_equation in E0. destruct (stop m) eqn:E1.
      + inv E0. cbn in *. inv H1. enough (stop s' = false)  by congruence; eauto.
      + cbn in H1. inv H1. cbn in *. destruct str1'; cbn in *; eapply IHstr1; eauto.
  Qed.

  Lemma CopySymbols_second tltr str1 x str2 tl' tr':
    (forall x', List.In x' str1 -> stop x' = false) ->
    (stop x = true) ->
    tape_local (fst tltr) = str1 ++ x :: str2 ->
    (tl', tr') = CopySymbols_Fun tltr ->
    left tr' = rev (map g str1) ++ left (snd tltr).
  Proof.
    intros H H0. destruct tltr as [tl tr]. intros H1 E0.
    destruct tl as [ | r rs | l ls | ls m rs]; cbn in *.
    1-3: rewrite CopySymbols_Fun_equation in E0; inv H1; exfalso; destruct str1; cbn in *; congruence.
    revert rs tr ls H ls m H1 tl' tr' E0. revert str1; intros str1.
    induction str1 as [ | s' str1' IHstr1]; (* cbn in *; *) intros.
    - cbn in *. inv H1. rewrite CopySymbols_Fun_equation in E0. rewrite H0 in E0. inv E0. cbn. auto.
    - rewrite CopySymbols_Fun_equation in E0. destruct (stop m) eqn:E1.
      + inv E0. cbn in *. inv H1. enough (stop s' = false)  by congruence; eauto.
      + cbn in H1. inv H1. cbn in *.
        simpl_list; cbn.
        destruct str1'; cbn in *.
        * clear H. erewrite IHstr1; eauto. destruct tr; cbn; eauto. destruct l0; cbn; auto.
        * simpl_list; cbn.
          erewrite IHstr1; eauto. destruct tr; simpl_list; cbn; eauto. destruct l0; cbn; auto.
  Qed.

  Definition CopySymbols_Rel' : Rel (tapes sig 2) (unit * tapes sig 2) :=
    ignoreParam (
        fun tin tout =>
          forall str1 x str2,
            (forall x', List.In x' str1 -> stop x' = false) ->
            stop x = true ->
            tape_local (tin[@Fin.F1]) = str1 ++ x :: str2 ->
            tape_local (tout[@Fin.F1]) = x :: str2 /\
            left (tout[@Fin.FS Fin.F1]) = rev (map g str1) ++ left (tin[@Fin.FS Fin.F1])
      ).

  Corollary CopySymbols_WRealise' :
    CopySymbols ⊫ CopySymbols_Rel'.
  Proof.
    eapply WRealise_monotone. eapply CopySymbols_WRealise.
    hnf. intros tin (? & tout). destruct_tapes. cbn. intros H.
    hnf. intros str1 str2 x Hstr1 Hx HEnc. split.
    - eapply CopySymbols_first; cbn; eauto. cbn. eauto.
    - epose proof CopySymbols_second (tltr := (_, _)) Hstr1 Hx as L. spec_assert L; cbn; eauto.
  Qed.

  Lemma CopySymbols_TermTime_local t r1 sym r2 :
    tape_local t = r1 ++ sym :: r2 ->
    stop sym = true ->
    CopySymbols_TermTime t <= 8 + 8 * length r1.
  Proof.
    revert t sym r2. induction r1; intros t sym r2 HEnc HStop; cbn -[plus mult] in *.
    - destruct t; cbn in HEnc; inv HEnc. rewrite CopySymbols_TermTime_equation. rewrite HStop. cbn. omega.
    - destruct t; cbn in HEnc; try congruence. inv HEnc.
      rewrite CopySymbols_TermTime_equation. destruct (stop a).
      + omega.
      + apply Nat.add_le_mono_l. replace (8 * S (|r1|)) with (8 + 8 * |r1|) by omega.
        eapply IHr1; eauto. cbn. now simpl_tape.
  Qed.


  Corollary CopySymbols_terminates' :
    projT1 CopySymbols ↓
           (fun tin k => exists r1 r2 sym, tape_local (tin[@Fin.F1]) = r1 ++ sym :: r2 /\ stop sym = true /\ 8 + 8 * length r1 <= k).
  Proof.
    eapply TerminatesIn_monotone. eapply CopySymbols_terminates.
    intros tin k. intros (r1&r2&x&Hx&HEnc&Hk). rewrite <- Hk. eapply CopySymbols_TermTime_local; eauto.
  Qed.

  
End CopySymbols.

Arguments CopySymbols : simpl never.
Arguments CopySymbols_L : simpl never.

Ltac smpl_TM_CopySymbols :=
  match goal with
  | [ |- CopySymbols  _ _ ⊫ _ ] => eapply CopySymbols_WRealise'
  | [ |- projT1 (CopySymbols _ _) ↓ _ ] => eapply CopySymbols_terminates'
  end.

Smpl Add smpl_TM_CopySymbols : TM_Correct.