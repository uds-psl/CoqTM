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
  Hypothesis (codX : codeable sigX X).

  Definition stop (s: (bool+sigX)^+) :=
    match s with
    | inr (inl _) => true
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


  Lemma Skip_cons_WRealise : Skip_cons ⊫ Skip_cons_Rel.
  Proof.
    eapply WRealise_monotone.
    { unfold Skip_cons. repeat TM_Correct. }
    {
      intros tin ((), tout) H. intros ls rs x l HTin. TMSimp. clear_trivial_eqs. clear H3 HTin H1 H2.
      destruct l as [ | x' l']; cbn.
      - destruct (encode x : list sigX) eqn:E; cbn.
        + rewrite MoveToSymbol_Fun_equation; cbn. reflexivity.
        + rewrite MoveToSymbol_correct_midtape; cbn; eauto.
          * now rewrite <- !app_assoc.
          * rewrite List.map_map. intros [ | ] (?&H1&H2) % in_map_iff; now inv H1.
      - destruct (encode x : list sigX) eqn:E; cbn.
        + destruct l'; cbn.
          * rewrite MoveToSymbol_Fun_equation. cbn. f_equal. now rewrite !List.map_app, <- List.app_assoc.
          * rewrite MoveToSymbol_Fun_equation.
            cbn. f_equal. rewrite !List.map_map, !List.map_app, !List.map_map, <- List.app_assoc. cbn. f_equal.
            now rewrite List.map_app, !List.map_map.
        + rewrite MoveToSymbol_correct_midtape; cbn; eauto.
          * rewrite <- app_assoc. f_equal. now rewrite map_app, <- app_assoc.
          * rewrite List.map_map. intros ? (?&?&?) % in_map_iff; subst. cbn. reflexivity.
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
      - destruct (encode x : list sigX) as [ | ex exs] eqn:E; cbn in *.
        + rewrite CopySymbols_L_Fun_equation in HCopy. cbn in HCopy. inv HCopy; TMSimp.
          split; auto. repeat econstructor. f_equal. cbn. rewrite E. cbn. simpl_tape. reflexivity.
        + unfold tape_move_left' at 1 in HCopy. 
          rewrite <- app_assoc in HCopy. cbn in HCopy.
          destruct (rev (map inr (map inr exs))) eqn:E2; cbn in *.
          * apply rev_eq_nil, map_eq_nil, map_eq_nil in E2 as ->; cbn in *.
            do 2 ( rewrite CopySymbols_L_Fun_equation in HCopy; cbn in * ). inv HCopy; TMSimp.
            split; auto.
            repeat econstructor. f_equal. simpl_tape. cbn. rewrite E. reflexivity.
          * replace (l ++ inr (inr ex) :: inr (inl true) :: inl START :: ls) with ((l ++ [inr (inr ex)]) ++ inr (inl true) :: inl START :: ls) in HCopy by now rewrite <- app_assoc.
            rewrite CopySymbols_L_correct_midtape in HCopy; cbn; auto.
            -- inv HCopy; TMSimp. split.
               ++ f_equal. rewrite rev_app_distr. cbn. f_equal.
                  rewrite app_comm_cons'. replace (rev l ++ [s]) with (rev (s :: l)) by reflexivity. rewrite <- E2.
                  now rewrite rev_involutive.
               ++ repeat econstructor. f_equal. cbn. rewrite E.
                  rewrite map_id. cbn. rewrite rev_app_distr. cbn. f_equal. cbv [id]. simpl_tape.
                  rewrite app_comm_cons'. replace (rev l ++ [s]) with (rev (s :: l)) by reflexivity. rewrite <- E2.
                  now rewrite rev_involutive.
            -- apply rev_eq_cons in E2. rewrite List.map_map in E2.
               apply map_eq_app in E2 as (ls1&ls2&->&E2&E2').
               destruct ls2; cbn in *; inv E2'. cbn. reflexivity.
            -- apply rev_eq_cons in E2. rewrite List.map_map in E2.
               apply map_eq_app in E2 as (ls1&ls2&->&E2&E2').
               destruct ls2; cbn in *; inv E2'. symmetry in H3. apply map_eq_nil in H3 as ->.
               intros s [Hs % in_rev | Hs] % in_app_iff.
               ++ rewrite E2 in Hs. apply in_map_iff in Hs as (s'&<-&?). cbn. reflexivity.
               ++ destruct Hs as [<-|[]]. cbn. reflexivity.
      - destruct  (encode x : list sigX) as [ | ex exs] eqn:E; cbn in *.
        + rewrite CopySymbols_L_Fun_equation in HCopy. cbn in HCopy. inv HCopy; TMSimp.
          split. f_equal. f_equal. now rewrite !List.map_app, List.map_map, <- List.app_assoc.
          repeat econstructor. cbn. rewrite E. cbn. f_equal. simpl_tape. reflexivity.
        + rewrite <- app_assoc in HCopy. cbn in HCopy. 
          destruct (rev (map inr (map inr exs))) eqn:E2; cbn in *.
          * apply rev_eq_nil, map_eq_nil, map_eq_nil in E2 as ->; cbn in *.
            do 2 ( rewrite CopySymbols_L_Fun_equation in HCopy; cbn in * ). inv HCopy; TMSimp.
            split. now rewrite map_app, <- app_assoc.
            repeat econstructor. f_equal. simpl_tape. cbn. rewrite E. reflexivity.
          * replace (l ++ inr (inr ex) :: inr (inl true) :: inl START :: ls) with ((l ++ [inr (inr ex)]) ++ inr (inl true) :: inl START :: ls) in HCopy by now rewrite <- app_assoc.
            rewrite CopySymbols_L_correct_midtape in HCopy; cbn; auto.
            -- inv HCopy; TMSimp. split.
               ++ rewrite map_app, <- app_assoc. f_equal. rewrite rev_app_distr. cbn. f_equal.
                  rewrite app_comm_cons'. replace (rev l ++ [s]) with (rev (s :: l)) by reflexivity. rewrite <- E2.
                  now rewrite rev_involutive.
               ++ repeat econstructor. f_equal. cbn. rewrite E.
                  rewrite map_id. cbn. rewrite rev_app_distr. cbn. f_equal. cbv [id]. simpl_tape.
                  rewrite app_comm_cons'. replace (rev l ++ [s]) with (rev (s :: l)) by reflexivity. rewrite <- E2.
                  now rewrite rev_involutive.
            -- apply rev_eq_cons in E2. rewrite List.map_map in E2.
               apply map_eq_app in E2 as (ls1&ls2&->&E2&E2').
               destruct ls2; cbn in *; inv E2'. cbn. reflexivity.
            -- apply rev_eq_cons in E2. rewrite List.map_map in E2.
               apply map_eq_app in E2 as (ls1&ls2&->&E2&E2').
               destruct ls2; cbn in *; inv E2'. symmetry in H3. apply map_eq_nil in H3 as ->.
               intros s [Hs % in_rev | Hs] % in_app_iff.
               ++ rewrite E2 in Hs. apply in_map_iff in Hs as (s'&<-&?). cbn. reflexivity.
               ++ destruct Hs as [<-|[]]. cbn. reflexivity.
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



  (* TODO: Constructors *)



End MatchList.