(* List destruct and construction *)

Require Import TM.Code.CodeTM.
Require Import TM.Basic.Mono TM.Basic.Nop TM.Basic.Multi.
Require Import TM.Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.
Require Import TM.Compound.CopySymbols TM.Compound.MoveToSymbol.
Require Import TM.Code.Copy.


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
          tout[@Fin0] ≃ nil /\
          isRight tout[@Fin1] /\
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
      TMSimp; clear_trivial_eqs.
      destruct HEncL as (ls&HEncL). destruct HRight as (ls'&rs'&HRight). TMSimp.
      rewrite <- H0 in *.
      destruct l as [ | x l'] in *; cbn in *; TMSimp; clear_trivial_eqs.
      { (* nil *)
        rewrite <- H0. split; auto.
        - repeat econstructor; cbn; simpl_tape.
        - repeat econstructor.
      }
      { (* cons *)
        rewrite map_app, <- app_assoc in H0. symmetry in H0.
        specialize (H _ _ _ _ ltac:(now repeat econstructor) H0).
        TMSimp.
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
        + rewrite CopySymbols_L_TermTime_moveleft; auto.
          rewrite rev_length, !map_length. omega.
        + intros tmid4 () _. omega.
      - intros tmid2 (). intros (_&HInj2); TMSimp.
        exists 3, (10 + 8 * length (encode x)). repeat split; try omega.
        intros tmid3 (). intros (_&H3&H3'); TMSimp.
        exists (8+8*length(encode x)), 1. repeat split; cbn; try omega.
        + rewrite CopySymbols_L_TermTime_moveleft; auto.
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
    Inject (MoveRight _;; Move _ L tt) [|Fin1|];;
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
    { unfold Constr_cons. repeat TM_Correct. apply MoveRight_WRealise with (X := X). }
    {
      intros tin ((), tout) H. intros l y HEncL HEncY.
      TMSimp; clear_trivial_eqs.
      specialize (H y HEncY) as (ls&H). TMSimp.
      destruct HEncL as (ls2&HEncL). TMSimp.
      rewrite CopySymbols_L_correct_moveleft in H0; swap 1 2; auto.
      { intros ? (?&<-& (?&<-&?) % in_rev % in_map_iff) % in_map_iff. cbn. reflexivity. }
      inv H0. TMSimp.
      repeat econstructor.
      - cbn. f_equal. simpl_tape. rewrite map_id. rewrite !map_rev, rev_involutive. f_equal.
        now rewrite !List.map_map, map_app, <- app_assoc, List.map_map.
      - f_equal. now rewrite !map_rev, rev_involutive.
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
      - apply MoveRight_WRealise with (X := X).
      - apply MoveRight_WRealise with (X := X).
      - apply MoveRight_Terminates with (X := X).
    }
    {
      intros tin k (l&y&HEncL&HEncY&Hk).
      exists (10 + 4 * length (encode y)), (12 + 8 * length (encode y)). repeat split; try omega.
      - cbn. do 2 eexists. split; eauto. rewrite map_length. omega.
      - intros tmid () (H&HInj). TMSimp.
        specialize (H _ HEncY) as (ls&HEncY'). TMSimp.
        exists (8 + 8 * length (encode y)), 3. repeat split; try omega.
        + erewrite CopySymbols_L_TermTime_moveleft; eauto. rewrite map_length, rev_length, map_length. omega.
        + intros tmid2 (). intros (H2&HInj2). TMSimp.
          exists 1, 1. repeat split; try omega. intros ? _ _. omega.
    }
  Qed.

End MatchList.
