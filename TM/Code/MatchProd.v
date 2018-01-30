(* Product destruct and construction *)

Require Import TM.Code.CodeTM.
Require Import TM.Basic.Mono TM.Basic.Nop TM.Basic.Multi.
Require Import TM.Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.
Require Import TM.Compound.CopySymbols TM.Compound.MoveToSymbol.
Require Import TM.Code.Copy.

Section Projection.

  Variable X Y : Type.
  Variable (sigX sigY : finType).
  Hypothesis (codX : codeable sigX X) (codY : codeable sigY Y).


  Definition stop_X :=
    fun (x : (sigX+sigY)^+) =>
      match x with
      | (inr (inl _)) => false
      | _ => true (* Stop at symbol from Y or halt/stop symbol *)
      end.

  Definition stop_Y :=
    fun (x : (sigX+sigY)^+) =>
      match x with
        inr (inr _) => false
      | _ => true (* Stop at symbol from X or halt/stop symbol *)
      end.


  Local Lemma CopySymbols_pair_first' (inputX : list sigX) (inputY : list sigY) tltr tl' tr' rs' :
    tape_local (fst tltr) = map inr (map inl inputX ++ map inr inputY) ++ (inl STOP :: rs') ->
    (tl', tr') = CopySymbols_Fun stop_X id tltr ->
    tape_local (tl') = map inr (map inr inputY) ++ (inl STOP :: rs').
  Proof.
    intros. destruct inputY as [ | csy inputY'] eqn:E1; cbn in *.
    - eapply CopySymbols_pair_first; cbn; eauto.
      + rewrite app_nil_r. intuition. eapply in_map_iff in H1 as (?&<-& (?&<-&?)%in_map_iff). trivial.
      + trivial.
    - eapply CopySymbols_pair_first with (str1 := map inr (map inl inputX)); cbn; eauto.
      + intros x. rewrite !List.map_map. intros (?&<-&?) % in_map_iff. cbn. trivial.
      + simpl_list. intuition.
      + now rewrite map_app, <- app_assoc in H.
  Qed.

  Local Lemma CopySymbols_pair_first'' (inputX : list sigX) (inputY : list sigY) ls m rs tr tl' tr' rs' :
    m :: rs = map inr (map inl inputX ++ map inr inputY) ++ inl STOP :: rs' ->
    (tl', tr') = CopySymbols_Fun stop_X id (midtape ls m rs, tr) ->
    tape_local tl' = map inr (map inr inputY) ++ inl STOP :: rs'.
  Proof.
    intros H1 H2. apply (CopySymbols_pair_first' (tltr := (midtape ls m rs, tr)) ltac:(cbn; eapply H1) H2).
  Qed.

  Local Lemma CopySymbols_pair_second' (inputX : list sigX) (inputY : list sigY) tltr tl' tr' rs' :
    tape_local (fst tltr) = map inr (map inl inputX ++ map inr inputY) ++ (inl STOP :: rs') ->
    (tl', tr') = CopySymbols_Fun stop_X id tltr ->
    left tr' = map inr (map inl (rev inputX)) ++ left (snd tltr).
  Proof.
    intros. rewrite !map_rev. destruct inputY as [ | csy inputY'] eqn:E1; cbn in *.
    - rewrite app_nil_r in H.
      eapply CopySymbols_pair_second; cbn; eauto.
      + intros ? (? & <- & (? & <- & ?) % in_map_iff) % in_map_iff. cbn. trivial.
      + cbn. trivial.
    - eapply CopySymbols_pair_second with (str1 := map inr (map inl inputX)); cbn; eauto; swap 2 3.
      + intros x. rewrite !List.map_map. intros (?&<-&?) % in_map_iff. cbn. trivial.
      + rewrite map_app, <- app_assoc in H. eapply H.
      + trivial.
  Qed.
  
  Local Lemma CopySymbols_pair_second'' (inputX : list sigX) (inputY : list sigY) ls m rs tr tl' tr' rs' :
    m :: rs = map inr (map inl inputX ++ map inr inputY) ++ inl STOP :: rs' ->
    (tl', tr') = CopySymbols_Fun stop_X id (midtape ls m rs, tr) ->
    left tr' = map inr (map inl (rev inputX)) ++ left tr.
  Proof.
    intros H1 H2. apply (CopySymbols_pair_second' (tltr := (midtape ls m rs, tr)) ltac:(cbn; eapply H1) H2).
  Qed.


  Let M1 : { M : mTM (sigX+sigY)^+ 2 & states M -> unit } :=
    CopySymbols stop_X id;;
    Inject (
      (Move _ L tt);;
      WriteMove (Some (inl START), R) tt
    ) [|Fin.F1|].

  
  (* Copy the symbols from tape 0 to tape 1, finish tape 0 but not don't initialise tape 1 *)
  Let R1 : Rel (tapes (sigX+sigY)^+ 2) (unit * tapes (sigX+sigY)^+ 2) :=
    ignoreParam (
        fun (tin tout : tapes (sigX+sigY)^+ 2) =>
          forall (xy : X * Y),
            tin [@Fin.F1] ≂ xy ->
            tout[@Fin.F1] ≂ snd xy /\
            left (tout[@Fin.FS Fin.F1]) = rev (map inr (map inl (encode (fst xy)))) ++ left (tin[@Fin.FS Fin.F1])
      ).

  
  Local Lemma M1_WRealise : M1 ⊫ R1.
  Proof.
    subst M1 R1.
    eapply WRealise_monotone.
    {
      do 1 try eapply Seq_WRealise.
      all: try (eapply Inject_WRealise; [vector_dupfree| ]).
      2: eapply Seq_WRealise.
      all: try (eapply Realise_WRealise, RealiseIn_Realise;
                first [ eapply Move_Sem | eapply WriteMove_Sem | eapply Write_Sem ]).
      - eapply CopySymbols_WRealise.
    }
    {
      hnf. intros. hnf. destruct y. intros (inputX, inputY).
      TMSimp repeat progress simpl_not_in || cbn [Vector.nth] in *. destruct u.
      destruct h1; cbn in *; inv H0; [ do 2 destruct (encode _); cbn in H2; congruence | ]. clear H1.
      (*
      erewrite List.map_app, !List.map_map, <- app_assoc in H3; cbn in H3.
       *)
      split.
      - pose proof CopySymbols_pair_first'' H2 H as L1.
        destruct h3; cbn in *; try (destruct (encode inputY); cbn in L1; congruence).
        destruct l; cbn in *.
        + hnf. do 2 eexists. split; cbn; eauto.
        + hnf. do 2 eexists. split; cbn; eauto.
      - pose proof (CopySymbols_pair_second'' H2 H) as ->. now rewrite !map_rev.
    }
  Qed.
  
  Definition Proj : { M : mTM (sigX+sigY)^+ 2 & states M -> unit } :=
    Inject (WriteMove (Some (inl START), R) tt) [|Fin.FS Fin.F1|];;
    M1;;
    Inject (
      WriteMove (Some (inl STOP), L) tt;;
      MoveToSymbol_L stop_X;;
      Move _ R tt
    ) [|Fin.FS Fin.F1|].

  
  Definition Proj_Rel : Rel (tapes (sigX+sigY)^+ 2) (unit * tapes (sigX+sigY)^+ 2) :=
    ignoreParam (
        fun (tin tout : tapes (sigX+sigY)^+ 2) =>
          forall (xy : X * Y),
            tin [@Fin.F1] ≂ xy ->
            tout[@Fin.F1] ≂ snd xy /\
            tout[@Fin.FS Fin.F1] ≂ fst xy
      ).

  (* Θ (18 + (4+?)*(?+1)*|enocode (fst x)|) *)

  (* TODO: add the above lemmas to Prelim.v bzw. CodeTM.v and add them to the tape database *)

  Lemma Proj_WRealise : Proj ⊫ Proj_Rel.
  Proof.
    eapply WRealise_monotone.
    {
      unfold Proj. do 2 try eapply Seq_WRealise.
      all: try (eapply Inject_WRealise; [vector_dupfree| ]).
      3: repeat eapply Seq_WRealise.
      all: try (eapply Realise_WRealise, RealiseIn_Realise;
                first [ eapply Move_Sem | eapply WriteMove_Sem | eapply Write_Sem ]).
      - eapply M1_WRealise.
      - eapply MoveToSymbol_L_WRealise.
    }
    {
      hnf. intros. hnf. destruct y. intros (inputX, inputY).
      TMSimp repeat progress simpl_not_in || cbn [Vector.nth] in *. destruct u.
      destruct h3; cbn in *; inv H0; [do 2 destruct (encode _); cbn in H3; congruence | ]. clear H1. clear M1 R1. 
      specialize (H (inputX, inputY)). spec_assert H by (hnf; do 2 eexists; hnf; split; cbn; eauto). destruct H as (H1&H1').
      split; eauto. hnf; unfold tape_encodes_r; cbn in *. clear b H2 H1 h H3.
      rewrite tape_match_left_right in *. unfold finType_CS in *; rewrite H1'.

      destruct (encode inputX) as [ | cs cX'] eqn:E1; cbn in *.
      - do 2 eexists; hnf; split; cbn; hnf; rewrite MoveToSymbol_L_Fun_equation; cbn; eauto.
      - repeat ( rewrite <- !app_assoc in *; cbn in * ).

        assert (tape_local_l (tape_move_mono h4 (Some (inl STOP), L)) =
                (rev (map inr (map inl cX')) ++ [inr (inl cs)]) ++ inl START :: left h2) as L1.
        {
          repeat ( rewrite <- !app_assoc in *; cbn in * ).
          destruct h4; cbn in *; try (destruct cX'; cbn in *; congruence). subst. apply tape_match_symbols_tape_local_l.
        }
        
        (* TODO: This is a little mess! *)
        epose proof MoveToSymbol_L_left (stop := stop_X) _ _ L1 as (L2&L3). Unshelve. all: eauto.
        Focus 2.
        rewrite <- !map_rev, List.map_map. intros x [ (?&<-&?) % in_map_iff | [ <- | H]] % in_app_iff; cbn; auto.
        epose proof MoveToSymbol_L_right (stop := stop_X) _ _ L1 as L4. Unshelve. all: eauto.
        Focus 2.
        rewrite <- !map_rev, List.map_map. intros x [ (?&<-&?) % in_map_iff | [ <- | H]] % in_app_iff; cbn; auto.
        cbn in *. rewrite H1' in *. cbn in *.
        do 2 eexists; hnf; split; cbn; eauto.
        + erewrite tape_left_move_right; eauto.
        + erewrite tape_local_move_right; eauto.
          eapply tape_local_iff. do 2 eexists. split; eauto. split.
          eapply L3. unfold finType_CS in *. rewrite L4. cbn.
          rewrite tape_match_symbols_right. cbn.
          rewrite rev_app_distr; cbn. rewrite <- !map_rev, rev_involutive. eauto.
    }
  Qed.


  (* TODO Termination *)

  (* TODO: Konstruktor *)
  

End Projection.

