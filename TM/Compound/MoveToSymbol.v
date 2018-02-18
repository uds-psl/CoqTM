Require Import TM.Prelim.
Require Import TM.Basic.Mono.
Require Import TM.Combinators.Match TM.Combinators.While TM.Combinators.SequentialComposition.
Require Import TM.Mirror.
Require Import TM.Compound.TMTac.

Require Import FunInd.
Require Import Recdef.

Section move_to_symbol.
  
  Variable sig : finType.
  Variable stop : sig -> bool.

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
             | Some x => if stop x
                        then mono_Nop _ (false, true) (* found the symbol, break and return true *)
                        else Move _ R (true, false) (* wrong symbol, move right and continue *)
             | _ => mono_Nop _ (false, false) (* there is no such symbol, break and return false *)
             end).

  Definition M1_Fun : tape sig -> tape sig :=
    fun t1 =>
      match t1 with
      | midtape ls x rs => if (stop x) then t1 else tape_move_right t1
      | _ => t1
      end.

  Definition M1_Rel : Rel (tapes sig 1) (bool * bool * tapes sig 1) :=
    Mk_R_p (fun tin '(yout, tout) =>
              tout = M1_Fun tin /\
              (
                (yout = (false, true)  /\ exists s, current tin = Some s /\ stop s = true ) \/
                (yout = (true, false)  /\ exists s, current tin = Some s /\ stop s = false) \/
                (yout = (false, false) /\ current tin = None)
              )
           ).  

  Lemma M1_Rel_functional : functional M1_Rel.
  Proof. hnf. TMCrush cbn [Vector.nth] in *; auto. Qed.

  Lemma M1_RealiseIn :
    M1 ⊨c(3) M1_Rel.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold M1. eapply Match_RealiseIn. eapply read_char_sem. cbn.
      instantiate (2 := fun o : option sig => match o with Some x => if stop x then _ else _ | None => _ end).
      intros [ | ]; cbn.
      - destruct (stop e). 
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

  (*
   * The main loop of the machine.
   * Execute M1 in a loop until M1 returned [ None ] or [ Some true ]
   *)
  Definition MoveToSymbol : { M : mTM sig 1 & states M -> bool } := WHILE M1.
      
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
    | midtape ls m rs => if stop m then t else MoveToSymbol_Fun (tape_move_right t)
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

  
  Definition MoveToSymbol_Rel : Rel (tapes sig 1) (bool * tapes sig 1) :=
    Mk_R_p (fun tin '(yout, tout) =>
              tout = MoveToSymbol_Fun tin /\
              (
                (yout = true  /\ exists s, current tout = Some s /\ stop s = true ) \/
                (yout = false /\ current tout = None)
              )
           ).

  Lemma MoveToSymbol_WRealise :
    MoveToSymbol ⊫ MoveToSymbol_Rel.
  Proof.
    eapply WRealise_monotone.
    {
      unfold MoveToSymbol. eapply While_WRealise. eapply Realise_WRealise, RealiseIn_Realise. eapply M1_RealiseIn.
    }
    {

      hnf. intros tin (y1&tout) H. hnf in *. destruct H as (t1&H&H2). hnf in *.
      induction H as [x | x y z IH1 _ IH2].
      {
        TMCrush idtac; TMSolve 6.
        all: repeat progress (unfold M1_Fun, M1_Rel, MoveToSymbol_Rel, Mk_R_p in *).
        all: try rewrite MoveToSymbol_Fun_equation; auto.
        all: TMCrush idtac; TMSolve 6.
      }
      {
        TMCrush (cbn [Vector.nth] in *); TMSolve 6.
        all:
          try now
              (
                rewrite MoveToSymbol_Fun_equation; TMSimp; auto
              ).
        all: erewrite <- MoveToSymbol_M1_false; eauto.
      }
    }
  Qed.


  Lemma MoveToSymbol_Fun_tapesToList t : tapeToList (MoveToSymbol_Fun t) = tapeToList t .
  Proof.
    functional induction MoveToSymbol_Fun t; auto; simpl_tape in *; cbn in *; congruence.
  Qed.
  Hint Rewrite MoveToSymbol_Fun_tapesToList : tape.

  Lemma tape_move_niltape (t : tape sig) (D : move) : tape_move t D = niltape _ -> t = niltape _.
  Proof. destruct t, D; cbn; intros; try congruence. destruct l; congruence. destruct l0; congruence. Qed.

  Lemma MoveToSymbol_Fun_niltape t : MoveToSymbol_Fun t = niltape _ -> t = niltape _.
  Proof.
    intros H. remember (niltape sig) as N. functional induction MoveToSymbol_Fun t; subst; try congruence.
    - specialize (IHt0 H). destruct rs; cbn in *; congruence.
    (* - specialize (IHt0 H). destruct rs; cbn in *; congruence. *)
  Qed.


  (** Termination *)

  Function MoveToSymbol_TermTime (t : tape sig) { measure rlength t } : nat :=
    match t with
    | midtape ls m rs => if stop m then 4 else 4 + (MoveToSymbol_TermTime (tape_move_right t))
    | _ => 4
    end.
  Proof.
    all: (intros; try now (cbn; omega)). destruct rs; cbn; omega.
  Qed.


  (* Idee: Lösung des Problems kanonische Relation ranklatschen, damit die relation funktional wird. *)
  Lemma MoveToSymbol_terminates :
    projT1 MoveToSymbol ↓ (fun tin k => MoveToSymbol_TermTime (tin[@Fin.F1]) <= k).
  Proof.
    eapply While_terminatesIn.
    1-2: eapply Realise_total; eapply M1_RealiseIn.
    {
      eapply functional_functionalOn. apply M1_Rel_functional.
    }
    {
      intros tin k Hk. destruct_tapes. cbn in *.
      destruct h eqn:E; rewrite MoveToSymbol_TermTime_equation in *; cbn in *.
      - exists [|h|], false. do 2 eexists. cbn. split; eauto.
      - exists [|h|], false. do 2 eexists. cbn. split; eauto.
      - exists [|h|], false. do 2 eexists. cbn. split; eauto.
      - destruct (stop e) eqn:E2; cbn.
        + exists [|h|], false. cbn. do 2 eexists; split; eauto 6.
        + exists [|tape_move_right h|], true. cbn.
          destruct l0; rewrite E; cbn in *; do 2 eexists; split; eauto 7.
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
    | midtape ls m rs => if stop m then t else MoveToSymbol_L_Fun (tape_move_left t)
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
      + destruct (stop e) eqn:E1; cbn in *; eauto.
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
      + destruct (stop e) eqn:E1; cbn in *; eauto.
    - destruct t, t'; cbn in *; auto; congruence.
  Qed.

  Definition MoveToSymbol_L_Rel : Rel (tapes sig 1) (FinType (EqType bool) * tapes sig 1) :=
    Mk_R_p (fun tin '(yout, tout) =>
              tout = MoveToSymbol_L_Fun tin /\
              (
                (yout = true  /\ exists s, current tout = Some s /\ stop s = true ) \/
                (yout = false /\ current tout = None)
              )
           ).

  Lemma MoveToSymbol_L_WRealise :
    MoveToSymbol_L ⊫ MoveToSymbol_L_Rel.
  Proof.
    eapply WRealise_monotone.
    - eapply Mirror_WRealise. eapply MoveToSymbol_WRealise.
    - intros tin (y&tout) H. hnf in *. destruct_tapes; cbn in *. destruct H as (H1&H2); hnf in *.
      symmetry in H1. apply MoveToSymbol_mirror in H1 as ->. TMCrush simpl_tape in *; TMSolve 6.
  Qed.

  (* TODO: Reduce Termination, from termination of MoveTosymbol_R *)

  Function MoveToSymbol_L_TermTime (t : tape sig) { measure llength t } : nat :=
    match t with
    | midtape ls m rs => if stop m then 4 else 4 + (MoveToSymbol_L_TermTime (tape_move_left t))
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
    - now rewrite e0, IHn.
    - destruct t; cbn; auto.
  Qed.

  Lemma MoveToSymbol_L_terminates :
    projT1 MoveToSymbol_L ↓ (fun tin k => MoveToSymbol_L_TermTime (tin[@Fin.F1]) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    - eapply Mirror_Terminates. eapply MoveToSymbol_terminates.
    - cbn. intros tin k Hk. destruct_tapes; cbn. rewrite <- Hk. unfold mirror_tapes. rewrite MoveToSymbol_TermTime_mirror. cbn. auto.
  Qed.


  (** Alternative correctness statements, that is more useable for encodings *)

  Lemma MoveToSymbol_right t str1 str2 x :
    (forall x, List.In x str1 -> stop x = false) ->
    (stop x = true) ->
    tape_local t = str1 ++ x :: str2 ->
    tape_local (MoveToSymbol_Fun t) = x :: str2.
  Proof.
    intros H H0. destruct t as [ | r rs | l ls | ls m rs]; cbn in *.
    1,3: rewrite MoveToSymbol_Fun_equation; cbn; destruct str1; cbn in *; try congruence.
    1: destruct str1; cbn in *; congruence.
    revert m ls str1 H. revert rs.
    refine (@size_induction _ (@length sig) _ _); intros [ | s rs'] IH; intros.
    - rewrite MoveToSymbol_Fun_equation; cbn. destruct str1; cbn in *; inv H1.
      + rewrite H0. cbn. auto.
      + destruct str1; cbn in *; congruence.
    - rewrite MoveToSymbol_Fun_equation; cbn.
      destruct (stop m) eqn:E1.
      + cbn. destruct str1; cbn in *; inv H1; eauto. specialize (H _ ltac:(eauto)). congruence.
      + destruct str1; cbn in *; inv H1.
        * congruence.
        * eapply IH; cbn; eauto.
  Qed.

  Lemma MoveToSymbol_left t str1 str2 x :
    (forall x', List.In x' str1 -> stop x' = false) ->
    (stop x = true) ->
    tape_local t = str1 ++ x :: str2 ->
    left (MoveToSymbol_Fun t) = rev str1 ++ left t.
  Proof.
    intros H H0. destruct t as [ | r rs | l ls | ls m rs]; cbn in *.
    1,3: rewrite MoveToSymbol_Fun_equation; cbn; destruct str1; cbn in *; try congruence.
    1: destruct str1; cbn in *; congruence.
    revert m ls str1 H. revert rs.
    refine (@size_induction _ (@length sig) _ _); intros [ | s rs'] IH; intros.
    - rewrite MoveToSymbol_Fun_equation; cbn. destruct str1; cbn in *; inv H1.
      + rewrite H0. cbn. auto.
      + destruct str1; cbn in *; congruence.
    - rewrite MoveToSymbol_Fun_equation; cbn.
      destruct (stop m) eqn:E1.
      + cbn. destruct str1; cbn in *; inv H1; eauto. specialize (H _ ltac:(eauto)). congruence.
      + destruct str1; cbn in *; inv H1.
        * congruence.
        * simpl_list. eapply IH; cbn; eauto.
  Qed.

  Definition MoveToSymbol_Rel' : Rel (tapes sig 1) (bool * tapes sig 1) :=
    Mk_R_p (
        ignoreParam (
        fun tin tout =>
          forall str1 str2 x,
            (forall x', List.In x' str1 -> stop x' = false) ->
            stop x = true ->
            tape_local tin = str1 ++ x :: str2 ->
            tape_local tout = x :: str2 /\
            left tout = rev str1 ++ left tin
      )).

  Corollary MoveToSymbol_WRealise' :
    MoveToSymbol ⊫ MoveToSymbol_Rel'.
  Proof.
    eapply WRealise_monotone. eapply MoveToSymbol_WRealise.
    hnf. intros tin (? & tout). cbn. intros (->&_).
    hnf. intros str1 str2 x Hstr1 Hx HEnc. split.
    - eapply MoveToSymbol_right; eauto.
    - eapply MoveToSymbol_left; eauto.
  Qed.

  
  Corollary MoveToSymbol_L_left t str1 str2 x :
    (forall x', List.In x' str1 -> stop x' = false) ->
    (stop x = true) ->
    tape_local_l t = str1 ++ x :: str2 ->
    tape_local_l (MoveToSymbol_L_Fun t) = x :: str2.
  Proof.
    intros. pose proof (@MoveToSymbol_right (mirror_tape t) str1 str2 x) as L.
    simpl_tape in L. repeat spec_assert L by auto.
    erewrite MoveToSymbol_mirror' in L. simpl_tape. rewrite <- tape_local_mirror'. eapply L.
    now simpl_tape.
  Qed.

  Corollary MoveToSymbol_L_right t str1 str2 x :
    (forall x, List.In x str1 -> stop x = false) ->
    (stop x = true) ->
    tape_local_l t = str1 ++ x :: str2 ->
    right (MoveToSymbol_L_Fun t) = rev str1 ++ right t.
  Proof.
    intros. pose proof (@MoveToSymbol_left (mirror_tape t) str1 str2 x) as L.
    simpl_tape in L. repeat spec_assert L by auto.
    erewrite MoveToSymbol_mirror' in L. simpl_tape. rewrite <- mirror_tape_right in L.
    erewrite mirror_tape_involution in L. eapply L. now simpl_tape.
  Qed.


  Definition MoveToSymbol_L_Rel' : Rel (tapes sig 1) (bool * tapes sig 1) :=
    Mk_R_p (
        ignoreParam (
        fun tin tout =>
          forall str1 str2 x,
            (forall x', List.In x' str1 -> stop x' = false) ->
            stop x = true ->
            tape_local_l tin = str1 ++ x :: str2 ->
            tape_local_l tout = x :: str2 /\
            right tout = rev str1 ++ right tin
      )).

  Corollary MoveToSymbol_L_WRealise' :
    MoveToSymbol_L ⊫ MoveToSymbol_L_Rel'.
  Proof.
    eapply WRealise_monotone. eapply MoveToSymbol_L_WRealise.
    hnf. intros tin (? & tout). cbn. intros (->&_).
    hnf. intros str1 str2 x Hstr1 Hx HEnc. split.
    - eapply MoveToSymbol_L_left; eauto.
    - eapply MoveToSymbol_L_right; eauto.
  Qed.
  
  Lemma MoveToSymbol_TermTime_local t r1 sym r2 :
    tape_local t = r1 ++ sym :: r2 ->
    stop sym = true ->
    MoveToSymbol_TermTime t <= 4 + 4 * length r1.
  Proof.
    revert t sym r2. induction r1; intros t sym r2 HEnc HStop; cbn -[plus mult] in *.
    - destruct t; cbn in HEnc; inv HEnc. rewrite MoveToSymbol_TermTime_equation. rewrite HStop. cbn. omega.
    - destruct t; cbn in HEnc; try congruence. inv HEnc.
      rewrite MoveToSymbol_TermTime_equation. destruct (stop a).
      + omega.
      + apply Nat.add_le_mono_l. replace (4 * S (|r1|)) with (4 + 4 * |r1|) by omega.
        eapply IHr1; eauto. cbn. now simpl_tape.
  Qed.

  Corollary MoveToSymbol_terminates' :
    projT1 MoveToSymbol ↓
           (fun tin k => exists r1 r2 sym, tape_local (tin[@Fin.F1]) = r1 ++ sym :: r2 /\ stop sym = true /\ 4 + 4 * length r1 <= k).
  Proof.
    eapply TerminatesIn_monotone. eapply MoveToSymbol_terminates.
    intros tin k. intros (r1&r2&x&Hx&HEnc&Hk). rewrite <- Hk. eapply MoveToSymbol_TermTime_local; eauto.
  Qed.

  Lemma MoveToSymbol_L_TermTime_local t r1 sym r2 :
    tape_local_l t = r1 ++ sym :: r2 ->
    stop sym = true ->
    MoveToSymbol_L_TermTime t <= 4 + 4 * length r1.
  Proof.
    revert t sym r2. induction r1; intros t sym r2 HEnc HStop; cbn -[plus mult] in *.
    - destruct t; cbn in HEnc; inv HEnc. rewrite MoveToSymbol_L_TermTime_equation. rewrite HStop. cbn. omega.
    - destruct t; cbn in HEnc; try congruence. inv HEnc.
      rewrite MoveToSymbol_L_TermTime_equation. destruct (stop a).
      + omega.
      + apply Nat.add_le_mono_l. replace (4 * S (|r1|)) with (4 + 4 * |r1|) by omega.
        eapply IHr1; eauto. cbn. now simpl_tape.
  Qed.

  Corollary MoveToSymbol_L_terminates' :
    projT1 MoveToSymbol_L ↓
           (fun tin k => exists r1 r2 sym, tape_local_l (tin[@Fin.F1]) = r1 ++ sym :: r2 /\ stop sym = true /\ 4 + 4 * length r1 <= k).
  Proof.
    eapply TerminatesIn_monotone. eapply MoveToSymbol_L_terminates.
    intros tin k. intros (r1&r2&x&Hx&HEnc&Hk). rewrite <- Hk. eapply MoveToSymbol_L_TermTime_local; eauto.
  Qed.


End move_to_symbol.

Arguments MoveToSymbol : simpl never.
Arguments MoveToSymbol_L : simpl never.


Ltac smpl_TM_MoveToSymbol :=
  match goal with
  | [ |- MoveToSymbol   _ ⊫ _ ] => eapply MoveToSymbol_WRealise'
  | [ |- MoveToSymbol_L _ ⊫ _ ] => eapply MoveToSymbol_L_WRealise'
  | [ |- projT1 (MoveToSymbol   _) ↓ _ ] => eapply MoveToSymbol_terminates'
  | [ |- projT1 (MoveToSymbol_L _) ↓ _ ] => eapply MoveToSymbol_L_terminates'
  end.

Smpl Add smpl_TM_MoveToSymbol : TM_Correct.