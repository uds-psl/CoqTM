(* List destruct and construction *)

Require Import TM.Code.CodeTM.
Require Import TM.Basic.Mono TM.Basic.Nop TM.Basic.Multi.
Require Import TM.Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.
Require Import TM.Compound.CopySymbols TM.Compound.MoveToSymbol.
Require Import TM.Code.Copy.


(* This is good *)
Arguments finType_CS (X) {_ _}.



(* TODO: -> base *)
Lemma rev_eq_nil (Z: Type) (l: list Z) :
  rev l = nil -> l = nil.
Proof. intros. destruct l; cbn in *. reflexivity. symmetry in H. now apply app_cons_not_nil in H. Qed.

Lemma map_eq_nil (Y Z: Type) (f: Y->Z) (l: list Y) :
  map f l = nil -> l = nil.
Proof. intros. destruct l; cbn in *. reflexivity. congruence. Qed.

Lemma map_eq_cons (A B: Type) (f: A->B) (ls: list A) (y: B) (ys: list B) :
  map f ls = y :: ys ->
  exists x xs, ls = x :: xs /\
          y = f x /\
          ys = map f xs.
Proof. induction ls; intros H; cbn in *; inv H; eauto. Qed.

Lemma map_eq_app (A B: Type) (f: A -> B) (ls : list A) (xs ys : list B) :
  map f ls = xs ++ ys ->
  exists ls1 ls2, ls = ls1 ++ ls2 /\
             xs = map f ls1 /\
             ys = map f ls2.
Proof.
  revert xs ys. induction ls; intros; cbn in *.
  - symmetry in H. apply app_eq_nil in H as (->&->). exists nil, nil. cbn. tauto.
  - destruct xs; cbn in *.
    + exists nil. eexists. repeat split. cbn. now subst.
    + inv H. specialize IHls with (1 := H2) as (ls1&ls2&->&->&->).
      repeat econstructor. 2: instantiate (1 := a :: ls1). all: reflexivity.
Qed.
  

Lemma rev_eq_cons (A: Type) (ls: list A) (x : A) (xs: list A) :
  rev ls = x :: xs ->
  ls = rev xs ++ [x].
Proof. intros H. rewrite <- rev_involutive at 1. rewrite H. cbn. reflexivity. Qed.



Section MatchList.

  (** ** Definition *)


  Variable X : Type.
  Variable (sigX : finType).
  Hypothesis (codX : codable sigX X).

  Definition stop (s: (bool+sigX)^+) :=
    match s with
    | inr (inl _) => true
    | inl _ => true
    | _ => false
    end.
  

  Definition Skip_cons : { M : mTM (bool + sigX)^+ 1 & states M -> unit } :=
    Move _ R tt;;
    Return (MoveToSymbol stop) tt.


  Definition M1 : { M : mTM (bool + sigX)^+ 2 & states M -> unit } :=
    Inject Skip_cons [|Fin0|];;
    Inject (Write (inl STOP) tt) [|Fin1|];;
    MovePar _ L L tt;;
    CopySymbols_L stop id;;
    Inject (Write (inl START) tt) [|Fin1|].

  Definition MatchList : { M : mTM (bool + sigX)^+ 2 & states M -> bool } :=
    Inject (Move _ R tt) [|Fin0|];;
    MATCH (Inject (Read_char _) [|Fin0|])
          (fun s => match s with
                 | Some (inr (inl false)) => (* nil *)
                   Inject (Move _ L false) [|Fin0|]
                 | Some (inr (inl true)) => (* cons *)
                   M1;; 
                   Inject Skip_cons [|Fin0|];;
                   Inject (Move _ L tt;; Write (inl START) true) [|Fin0|]
                 | _ => Nop _ _ true (* invalid input *)
                 end).


  (** ** Corectness *)

  Definition Skip_cons_Rel : Rel (tapes (bool+sigX)^+ 1) (unit * tapes (bool+sigX)^+ 1) :=
    Mk_R_p (
        ignoreParam (
            fun tin tout =>
              forall ls rs (x : X) (l : list X),
                tin = midtape (inl START :: ls) (inr (inl true))
                              (map inr (encode x) ++ map inr (encode l) ++ inl STOP :: rs) ->
                match l with
                | nil =>
                  tout = midtape (rev (map inr (encode x)) ++ inr (inl true) :: inl START :: ls)
                                 (inr (inl false)) (inl STOP :: rs)
                | x'::l' =>
                  tout = midtape (rev (map inr (encode x)) ++ inr (inl true) :: inl START :: ls)
                                 (inr (inl true)) (map inr (encode x') ++ map inr (encode l') ++ inl STOP :: rs)
                end)).

  
  Lemma stop_lemma x :
    forall x0 : boundary + (bool + sigX), x0 el map inr (map inr (encode x)) -> stop x0 = false.
  Proof.
    rewrite List.map_map. intros ? (?&<-&?) % in_map_iff. cbn. reflexivity.
  Qed.


  Lemma Skip_cons_WRealise : Skip_cons ⊫ Skip_cons_Rel.
  Proof.
    eapply WRealise_monotone.
    { unfold Skip_cons. repeat TM_Correct. }
    {
      intros tin ((), tout) H. intros ls rs x l HTin. TMSimp. clear_trivial_eqs. clear H3 HTin H1 H2.
      destruct l as [ | x' l']; cbn.
      - rewrite MoveToSymbol_correct_moveright; cbn; auto.
        + apply stop_lemma.
      - rewrite MoveToSymbol_correct_moveright; cbn; auto.
        + rewrite map_app, <- app_assoc. reflexivity.
        + apply stop_lemma.
    }
  Qed.
  

  Definition M1_Rel : Rel (tapes (bool+sigX)^+ 2) (unit * tapes (bool+sigX)^+ 2) :=
    ignoreParam (
        fun tin tout =>
          forall ls rs (x : X) (l : list X),
            isRight tin[@Fin1] ->
            tin[@Fin0] = midtape (inl START :: ls) (inr (inl true))
                                 (map inr (encode x) ++ map inr (encode l) ++ inl STOP :: rs) ->
            tout[@Fin0] = tin[@Fin0] /\
            tout[@Fin1] ≃ x).
            

  Lemma M1_WRealise : M1 ⊫ M1_Rel.
  Proof.
    eapply WRealise_monotone.
    { unfold M1. repeat TM_Correct. eapply Skip_cons_WRealise. }
    {
      intros tin ((), tout) H. intros ls rs x l HRight HTin0. TMSimp; clear_trivial_eqs.
      rename H3 into HCopy.
      clear HIndex_H1 HIndex_H2 HIndex_H7.
      destruct HRight as (r1&r2&HRight). TMSimp. clear HRight.

      specialize H with (1 := eq_refl).
      destruct l as [ | x' l']; TMSimp.
      - rewrite CopySymbols_L_correct_moveleft in HCopy; cbn; auto.
        2: setoid_rewrite <- in_rev; apply stop_lemma.
        inv HCopy. TMSimp.
        cbn. rewrite !map_id, !rev_involutive. repeat econstructor. cbn. f_equal. simpl_tape. reflexivity.
      - rewrite CopySymbols_L_correct_moveleft in HCopy; cbn; auto.
        2: setoid_rewrite <- in_rev; apply stop_lemma.
        inv HCopy. TMSimp.
        cbn. rewrite !map_id, !rev_involutive. repeat econstructor.
        + f_equal. rewrite map_app, <- app_assoc. reflexivity.
        + cbn. f_equal. simpl_tape. reflexivity.
    }
  Qed.


  Definition MatchList_Rel : Rel (tapes (bool+sigX)^+ 2) (bool * tapes (bool+sigX)^+ 2) :=
    fun tin '(yout, tout) =>
      forall (l : list X),
        tin[@Fin0] ≃ l ->
        isRight tin[@Fin1] ->
        match l with
        | nil =>
          tin = tout /\
          yout = false
        | x :: l' =>
          tout[@Fin0] ≃ l' /\
          tout[@Fin1] ≃ x /\
          yout = true
        end.


  Lemma MatchList_WRealise : MatchList ⊫ MatchList_Rel.
  Proof.
    eapply WRealise_monotone.
    { unfold MatchList. repeat TM_Correct. eapply M1_WRealise. eapply Skip_cons_WRealise. }
    {
      intros tin (yout, tout) H. intros l HEncL HRight.
      destruct HEncL as (ls&HEncL). TMSimp; clear_trivial_eqs.
      destruct HRight as (ls'&rs'&HRight). TMSimp.

      rewrite <- H1, <- H0 in *. (* clear H0 H1 HRight HIndex_H1 HIndex_H3. *)

      destruct l as [ | x l'] in *; cbn in *; TMSimp; clear_trivial_eqs.
      { (* nil *)
        split; auto. destruct_tapes; cbn in *; subst. cbn; simpl_tape. reflexivity.
      }
      { (* cons *)
        rewrite map_app, <- app_assoc in H1. symmetry in H1.
        specialize (H _ _ _ _ ltac:(now repeat econstructor) H1) as (H&H'). TMSimp.
        specialize H2 with (1 := eq_refl).
        destruct l' as [ | x' l'']; TMSimp.
        - repeat split; auto. repeat econstructor. f_equal. simpl_tape. cbn. reflexivity.
        - repeat split; auto. repeat econstructor. f_equal. simpl_tape. cbn. now rewrite map_app, <- app_assoc.
      }
    }
  Qed.


  (** ** Termination *)


  Arguments plus : simpl never. Arguments mult : simpl never.


  Lemma Skip_cons_Terminates :
    projT1 (Skip_cons) ↓
           (fun tin k =>
              exists ls rs (x : X) (l : list X),
                tin[@Fin0] = midtape (inl START :: ls) (inr (inl true))
                                     (map inr (encode x) ++ map inr (encode l) ++ inl STOP :: rs) /\
                 6 + 4 * length (encode x : list sigX) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Skip_cons. repeat TM_Correct. }
    {
      intros tin k (ls&rs&x&l&HTin&Hk). TMSimp. clear HTin.
      exists 1, (4 + 4 * length (encode x : list sigX)). repeat split. 1-2: omega.
      intros tmid () (_&H). TMSimp. clear H.
      destruct l as [ | x' l]; cbn.
      - rewrite MoveToSymbol_TermTime_moveright; cbn; auto. rewrite !map_length. omega.
      - rewrite MoveToSymbol_TermTime_moveright; cbn; auto. rewrite !map_length. omega.
    }
  Qed.


  Lemma M1_Terminates :
    projT1 M1 ↓
           (fun tin k =>
              exists ls rs (x : X) (l : list X),
                tin[@Fin0] = midtape (inl START :: ls) (inr (inl true))
                                     (map inr (encode x) ++ map inr (encode l) ++ inl STOP :: rs) /\
                 23 + 12 * length (encode x : list sigX) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold M1. repeat TM_Correct. eapply Skip_cons_WRealise. eapply Skip_cons_Terminates. }
    {
      intros tin k (ls&rs&x&l&HTin&Hk). TMSimp. clear HTin.
      exists (6 + 4 * length (encode x)), (16 + 8 * length (encode x)). repeat split; try omega. eauto 6.
      intros tmid (). intros (H&HInj); TMSimp. specialize H with (1 := eq_refl).
      destruct l as [ | x' l']; TMSimp. (* Both cases are identical *)
      1-2: exists 1, (14 + 8 * length (encode x)); repeat split; try omega.
      - intros tmid2 (). intros (_&HInj2); TMSimp.
        exists 3, (10 + 8 * length (encode x)). repeat split; try omega.
        intros tmid3 (). intros (_&H3&H3'); TMSimp.
        exists (8+8*length(encode x)), 1. repeat split; cbn; try omega.
        + rewrite <- HIndex_HInj2. cbn.
          rewrite CopySymbols_L_TermTime_moveleft; auto.
          rewrite rev_length, !map_length. omega.
        + intros tmid4 () _. omega.
      - intros tmid2 (). intros (_&HInj2); TMSimp.
        exists 3, (10 + 8 * length (encode x)). repeat split; try omega.
        intros tmid3 (). intros (_&H3&H3'); TMSimp.
        exists (8+8*length(encode x)), 1. repeat split; cbn; try omega.
        + rewrite <- HIndex_HInj2. cbn.
          rewrite CopySymbols_L_TermTime_moveleft; auto.
          rewrite rev_length, !map_length. omega.
        + intros tmid4 () _. omega.
    }
  Qed.



  Lemma MatchList_Terminates :
    projT1 MatchList ↓
           (fun tin k =>
              exists l : list X,
                tin[@Fin0] ≃ l /\
                isRight tin[@Fin1] /\
                match l with
                | nil => 5 <= k
                | x::l' =>
                  42 + 16 * length (encode x) <= k
                end).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold MatchList. repeat TM_Correct.
      - eapply M1_WRealise.
      - eapply M1_Terminates.
      - eapply Skip_cons_WRealise.
      - eapply Skip_cons_Terminates.
    }
    {
      cbn. intros tin k (l&HEncL&HRight&Hk).
      destruct HEncL as (ls&HEncL); TMSimp.
      destruct l as [ | x l']; cbn.
      {
        exists 1, 3. repeat split; try omega.
        intros tmid (). intros ((_&H1)&HInj1); TMSimp.
        exists 1, 1. repeat split; try omega.
        intros tmid2 ymid2 ((H2&H2')&HInj2). apply Vector.cons_inj in H2' as (H2'&_). TMSimp.
        omega.
      }
      {
        exists 1, (40 + 16 * length (encode x)). repeat split; try omega.
        intros tmid (). intros ((_&H1)&HInj1); TMSimp.
        exists 1, (38 + 16 * length (encode x)). repeat split; try omega.
        intros tmid2 ymid2 ((H2&H2')&HInj2). apply Vector.cons_inj in H2' as (H2'&_). TMSimp. rewrite <- H2'.
        exists (23 + 12 * length (encode x)), (14 + 4 * length (encode x)). repeat split; try omega.
        { rewrite map_app, <- app_assoc. eauto 6. }
        intros tmid3 () H3'. 
        rewrite map_app, <- app_assoc in H3'. specialize H3' with (1 := HRight) (2 := eq_refl). TMSimp.
        exists (6 + 4 * length (encode x)), 3. repeat split; try omega. eauto 6.
        intros tmid4 () (H4&HInj4); TMSimp. specialize H4 with (1 := eq_refl).
        destruct l' as [ | x' l'']; TMSimp. (* both cases are equal *)
        - exists 1, 1. repeat split; try omega. intros ? _ _. omega.
        - exists 1, 1. repeat split; try omega. intros ? _ _. omega.
      }
    }
  Qed.



  (** ** Constructors *)


  (** *** [nil] *)
  
  Definition Constr_nil : { M : mTM (bool + sigX)^+ 1 & states M -> unit } :=
    WriteMove (Some (inl STOP), L) tt;; WriteMove (Some (inr (inl false)), L) tt;; Write (inl START) tt.


  Definition Constr_nil_Rel : Rel (tapes (bool+sigX)^+ 1) (unit * tapes (bool+sigX)^+ 1) :=
    Mk_R_p (ignoreParam (fun tin tout => isRight tin -> tout ≃ nil)).


  Lemma Constr_nil_Sem : Constr_nil ⊨c(5) Constr_nil_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold Constr_nil. repeat TM_Correct. }
    { reflexivity. }
    {
      intros tin ((), tout) H. intros HRight. TMSimp.
      repeat econstructor. f_equal. simpl_tape. cbn. rewrite isRight_right; auto.
    }
  Qed.
  

  (** *** [cons] *)

  

  Definition Constr_cons : { M : mTM (bool + sigX)^+ 2 & states M -> unit } :=
    Inject (MoveRight' _) [|Fin1|];;
    Inject (CopySymbols_L stop id) [|Fin1;Fin0|];;
    Inject (WriteMove (Some (inr (inl true)), L) tt;; Write (inl START) tt) [|Fin0|].

  Definition Constr_cons_Rel : Rel (tapes (bool+sigX)^+ 2) (unit * tapes (bool+sigX)^+ 2) :=
    ignoreParam (
        fun tin tout =>
          forall l y,
            tin[@Fin0] ≃ l ->
            tin[@Fin1] ≃ y ->
            tout[@Fin0] ≃ y :: l /\
            tout[@Fin1] ≃ y
      ).

  
  Lemma Constr_cons_WRealise : Constr_cons ⊫ Constr_cons_Rel.
  Proof.
    eapply WRealise_monotone.
    { unfold Constr_cons. repeat TM_Correct. apply MoveRight'_WRealise with (X := X). }
    {
      intros tin ((), tout) H. intros l y HEncL HEncY.
      TMSimp; clear_trivial_eqs. specialize (H y HEncY) as (ls&HEncY1&HEncY2).
      destruct HEncL as (ls2&HEncL). TMSimp.
      erewrite CopySymbols_L_correct in H0. 4: cbn; eauto. all: cbn; auto. 2: setoid_rewrite <- in_rev; apply stop_lemma.
      inv H0. TMSimp.
      repeat econstructor.
      - f_equal. cbn. rewrite map_id, map_app, <- app_assoc, rev_involutive. simpl_tape. reflexivity.
      - rewrite rev_involutive. cbn. reflexivity.
    }
  Qed.
            

  Lemma Constr_cons_Terminates :
    projT1 Constr_cons ↓
           (fun tin k =>
              exists (l: list X) (y: X),
                tin[@Fin0] ≃ l /\
                tin[@Fin1] ≃ y /\
                23 + 12 * length (encode y) <= k).
  Proof.
    eapply TerminatesIn_monotone.
    { unfold Constr_cons. repeat TM_Correct.
      - apply MoveRight'_WRealise with (X := X).
      - apply MoveRight'_Terminates with (X := X).
    }
    {
      intros tin k (l&y&HEncL&HEncY&Hk).
      exists (10 + 4 * length (encode y)), (12 + 8 * length (encode y)). repeat split; try omega.
      - cbn. eexists. split. eauto. rewrite map_length. omega.
      - intros tmid () (H&HInj). TMSimp.
        specialize (H _ HEncY) as (ls&HEncY1&HEncY2). TMSimp.
        exists (8 + 8 * length (encode y)), 3. repeat split; try omega.
        + erewrite CopySymbols_L_TermTime_local; eauto. rewrite rev_length, !map_length. omega.
        + intros tmid2 (). intros (H2&HInj2). TMSimp.
          exists 1, 1. repeat split; try omega. intros ? _ _. omega.
    }
  Qed.

End MatchList.
