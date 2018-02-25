(* Product destruct and construction *)

Require Import TM.Code.CodeTM.
Require Import TM.Basic.Mono TM.Basic.Nop TM.Basic.Multi.
Require Import TM.Combinators.Combinators.
Require Import TM.LiftMN TM.LiftSigmaTau.
Require Import TM.Compound.TMTac.
Require Import TM.Compound.CopySymbols TM.Compound.MoveToSymbol.
Require Import TM.Code.Copy.

Section MatchList.

  (*
  Section Test.

    Let f {tau : Type} (x : (bool + (tau + (bool + tau)))) : (bool + tau) :=
      match x with
      | inl x => inl x
      | inr (inl y) => inr y
      | inr (inr (inl y)) => inl y
      | inr (inr (inr y)) => inr y
      end.

    Let g {tau : Type} (x: bool + tau) : option (bool + (tau + (bool + tau))) :=
      match x with
      | inl y => Some (inl y)
      | inr y => Some (inr (inl y))
      end.

    Section Test.
      (* The encoding of a list is a concatenation of encoding of options *)

      Compute encode [].
      Compute encode None.
      Compute encode [1;2;3] : list (bool + bool).
      Compute encode (true, (1, [2;3])).
      Compute encode (true, (1, [2;3])) : list (bool + (bool + (bool + bool))).
      Compute encode (true, (tt, [tt;tt])) : list (bool + (unit + (bool + unit))).
      Compute map f (encode (true, (tt, [tt;tt])) : list (bool + (unit + (bool + unit)))).

      Goal encode [1;2;3] = encode (Some 1) ++ encode (Some 2) ++ encode (Some 3) ++ encode None.
      Proof. cbn. trivial. Qed.

      Goal encode [1;2;3] = map f (encode (true, (1, [2; 3]))).
      Proof. cbn. trivial. Qed.

      Goal encode [tt;tt;tt] = map f (encode (true, (tt, [tt;tt]))).
      Proof. cbn. trivial. Qed.
      
    End Test.

    Variable X : Type.
    Variable (sigX : finType).
    Hypothesis (codX : codeable sigX X).

    Lemma encode_f_cons (x : X) (xs : list X) :
      map f (encode (true, (x, xs))) = encode (x :: xs).
    Proof.
      cbn. f_equal. repeat rewrite !map_app, !List.map_map. cbn. f_equal.
      erewrite map_ext.
      - eapply map_id.
      - intuition.
    Qed.

    Lemma retr' (tau : Type) : retract (@f tau) (@g tau).
    Proof.
      hnf. intros x. intuition; cbn; auto.
    Abort.

  End Test.
   *)


  Variable X : Type.
  Variable (sigX : finType).
  Hypothesis (codX : codeable sigX X).

  Definition M1 : { M : mTM (bool + sigX)^+ 1 & states M -> bool } :=
    MATCH (Read_char _)
          (fun o => match o with
                 | Some (inr (inl true))  => mono_Nop _ true  (* inl *)
                 | Some (inr (inl false)) => mono_Nop _ false (* inr *)
                 | _ => mono_Nop _ true (* invalid input *)
                 end).

  Let R1 : Rel (tapes (bool+sigX)^+ 1) (bool * tapes (bool+sigX)^+ 1) :=
    Mk_R_p (
        (if? (fun (tin tout : tape (bool+sigX)^+) =>
                   forall (lst : list X),
                     tin ≂ lst ->
                     exists (head : X) (tail : list X),
                       lst = head :: tail)
              ! (fun (tin tout : tape (bool+sigX)^+) =>
                   forall (lst : list X),
                     tin ≂ lst ->
                     lst = nil)
        ) ∩ ignoreParam (@IdR _)). 

  Lemma M1_Sem : M1 ⊨c(5) R1.
  Proof.
    eapply RealiseIn_monotone.
    {
      eapply Match_RealiseIn. cbn. eapply read_char_sem.
      instantiate (2 := fun o : option (bool + sigX)^+ =>
                          match o with Some (inr (inl true)) => _ | Some (inr (inl false)) => _ | _ => _ end).
      cbn. intros [ s | ]; cbn.
      - destruct s as [ start | s]; cbn.
        + eapply RealiseIn_monotone'. eapply mono_Nop_Sem. omega.
        + destruct s as [cons | xy]; swap 1 2; cbn.
          * eapply RealiseIn_monotone'. eapply mono_Nop_Sem. omega.
          * destruct cons; cbn; eapply mono_Nop_Sem.
      - eapply RealiseIn_monotone'. eapply mono_Nop_Sem. omega.
    }
    { cbn. omega. }
    {
      subst R1.
      intros tin (yout&tout) H. destruct H as (H1&(t&(H2&H3)&H4)); hnf in *. subst.
      split.
      {
        destruct_tapes; cbn in *.
        destruct h; cbn in *; TMSimp hnf in *; eauto. destruct (map _) in H0; cbn in H0; congruence.
        destruct e; swap 1 2; cbn in *; TMSimp hnf in *.
        - destruct s; swap 1 2; cbn in *; TMSimp hnf in *.
          + destruct lst; cbn in *; inv H0.
          + destruct b; cbn in *; TMSimp; unfold encode_list in *.
            * destruct lst; TMSimp hnf in *. eauto.
            * destruct lst; TMSimp hnf in *. eexists; split; eauto.
        - destruct lst; cbn in *; inv H0; eauto.
      }
      {
        destruct_tapes; cbn in *.
        destruct h; cbn in *; TMSimp; eauto. destruct e; cbn in *; TMSimp; auto.
        destruct s; cbn in *; TMSimp; auto.
        destruct b; cbn in *; TMSimp; auto.
      }
    }
  Qed.

  Definition stop_X' :=
    fun (x : (bool+sigX)^+) =>
      match x with
      | inr (inr x) => false
      | _ => true (* Stop at the next constructor or start/end symbol *)
      end.

  (* Copy the head encoding to tape 1 and set new start token on tape 0. *)
  Let M2 : { M : mTM (bool+sigX)^+ 2 & states M -> unit } :=
    Inject (Move _ R tt) [|Fin.F1|];;
    CopySymbols stop_X' id;;
    Inject (
      Move _ L tt;;
      WriteMove (Some (inl START), R) tt (* write the start symbol *)
    ) [|Fin.F1|].

  (* Copy the symbols from tape 0 to tape 1, finish tape 0 but not don't initialise tape 1 *)
  Let R2 : Rel (tapes (bool + sigX)^+ 2) (unit * tapes (bool + sigX)^+ 2) :=
    ignoreParam (
        fun (tin tout : tapes (bool + sigX)^+ 2) =>
          forall (head : X) (tail : list X),
            tin [@Fin.F1] ≂ head :: tail ->
            tout[@Fin.F1] ≂ tail /\
            left (tout[@Fin.FS Fin.F1]) =
            rev (map inr (map inr (encode head : list sigX))) ++ left (tin[@Fin.FS Fin.F1])
      ).


  Lemma CopySymbols_cons_first (head : X) (tail : list X) tltr tl' tr' rs' :
    (tl', tr') = CopySymbols_Fun stop_X' id tltr ->
    tape_local (fst tltr) = map inr (map inr (encode head)) ++ map inr (encode tail) ++ (inl STOP :: rs') ->
    tape_local (tl') = map inr (encode tail) ++ (inl STOP :: rs').
  Proof.
    intros. destruct tail as [ | ctail tail'] eqn:E1; cbn in *.
    - unshelve erewrite (CopySymbols_pair_first (stop := stop_X') (tltr := tltr) (x := inr (inl false)) _ _ H0 H); eauto.
      + rewrite List.map_map. intros x (? & <- & ?) % in_map_iff. cbn. trivial.
    - unshelve erewrite (CopySymbols_pair_first (stop := stop_X') (tltr := tltr) (x := inr (inl true)) _ _ H0 H); eauto.
      + rewrite List.map_map. intros x (? & <- & ?) % in_map_iff. cbn. trivial.
  Qed.

  Lemma CopySymbols_cons_second (head : X) (tail : list X) tltr tl' tr' rs' :
    (tl', tr') = CopySymbols_Fun stop_X' id tltr ->
    tape_local (fst tltr) = map inr (map inr (encode head)) ++ map inr (encode tail) ++ (inl STOP :: rs') ->
    left tr' = map inr (map inr (rev (encode head : list sigX))) ++ left (snd tltr).
  Proof.
    intros. rewrite !map_rev. destruct tail as [ | ctail tail'] eqn:E1; cbn in *.
    - unshelve epose proof (CopySymbols_pair_second (stop := stop_X') (tltr := tltr) (x := inr (inl false)) _ _ H0 H) as L; eauto.
      + intuition. eapply in_map_iff in H1 as (?&<-& (?&<-&?)%in_map_iff). trivial.
      + apply tape_local_l_cons_iff in L as (L1&L2). rewrite L2. trivial.
    - unshelve epose proof (CopySymbols_pair_second (stop := stop_X') (tltr := tltr) (x := inr (inl true)) _ _ H0 H) as L; eauto.
      + intuition. eapply in_map_iff in H1 as (?&<-& (?&<-&?)%in_map_iff). trivial.
      + apply tape_local_l_cons_iff in L as (L1&L2). rewrite L2. trivial.
  Qed.
  
  Lemma M2_WRealise : M2 ⊫ R2.
  Proof.
    subst M2 R1 R2.
    eapply WRealise_monotone.
    {
      do 2 try eapply Seq_WRealise.
      all: try (eapply Inject_WRealise; [vector_dupfree| ]).
      3: do 1 eapply Seq_WRealise.
      all: try (eapply Realise_WRealise, RealiseIn_Realise;
                first [ eapply Move_Sem | eapply WriteMove_Sem | eapply Write_Sem ]).
      - eapply CopySymbols_WRealise.
    }
    {
      hnf. intros. hnf. destruct y. intros head tail.
      TMSimp.
      destruct H0 as (r1&r2&HE1&HE2). cbn in *.
      destruct h1; cbn in *; inv HE1; [ do 2 destruct (map _); cbn in H3; congruence | inv H3]. clear H. 
      split.
      - 
        epose proof CopySymbols_cons_first H1 (head := head) (tail := tail) (rs' := r2) as L1. cbn in *.
        simpl_tape in L1. spec_assert L1.
        {
          inv HE2. now simpl_list.
        }
        hnf.
        do 2 eexists; split; cbn.
        + eapply tape_match_left_right.
        + erewrite <- L1. destruct h2; cbn in *; auto. destruct (encode_list _); cbn in *; congruence. destruct l; cbn; auto.
      -
        epose proof CopySymbols_cons_second H1 (head := head) (tail := tail) (rs' := r2) as L1. cbn in *.
        spec_assert L1.
        {
          inv HE2. simpl_tape. now simpl_list.
        }
        hnf. now rewrite !map_rev, List.map_map in *.
    }
  Qed.

  Let M3 : { M : mTM (bool+sigX)^+ 2 & states M -> unit } :=
    Inject (WriteMove (Some (inl START), R) tt) [|Fin.FS Fin.F1|];;
    M2;;
    Inject (
      WriteMove (Some (inl STOP), L) tt;;
      MoveToSymbol_L stop_X';;
      Move _ R tt
    ) [|Fin.FS Fin.F1|].

  Let R3 : Rel (tapes (bool+sigX)^+ 2) (unit * tapes (bool+sigX)^+ 2) :=
    ignoreParam (
        fun (tin tout : tapes (bool+sigX)^+ 2) =>
          forall (head : X) (tail : list X),
            tin [@Fin.F1] ≂ head :: tail ->
            tout[@Fin.F1] ≂ tail /\
            tout[@Fin.FS Fin.F1] ≂ head
      ).


  Lemma M3_WRealise : M3 ⊫ R3.
  Proof.
    eapply WRealise_monotone.
    {
      do 2 try eapply Seq_WRealise.
      all: try (eapply Inject_WRealise; [vector_dupfree| ]).
      3: repeat eapply Seq_WRealise.
      all: try (eapply Realise_WRealise, RealiseIn_Realise;
                first [ eapply Move_Sem | eapply WriteMove_Sem | eapply Write_Sem ]).
      - eapply M2_WRealise.
      - eapply MoveToSymbol_L_WRealise.
    }
    {
      subst R1 M2 R2 M3 R3. hnf. intros. hnf. destruct y. intros head tail.
      TMSimp. clear_trivial_eqs.
      destruct H0 as (r1&r2&HE1&HE2). cbn in *.
      destruct h1; cbn in *; inv HE1; [destruct (encode _); cbn in HE2; congruence | inv HE2]. clear H.
      specialize (H1 head tail). spec_assert H1 by (hnf; do 2 eexists; hnf; split; cbn; eauto). destruct H1 as (H1&H1').
      split; eauto. hnf; unfold tape_encodes_r; cbn in *. clear b H5.
      rewrite tape_match_left_right in *. unfold finType_CS in *; rewrite H1' in *.

      assert (tape_local_l (tape_move_mono h4 (Some (inl STOP), L)) =
              rev (map inr (map inr (encode head))) ++ inl START :: left h2) as L1.
      {
        repeat ( rewrite <- !app_assoc in *; cbn in * ).
        destruct h4; cbn in *; try congruence. subst. apply tape_match_symbols_tape_local_l.
      }

      epose proof (MoveToSymbol_L_correct (stop := stop_X') _ _ L1) as L2.
      simpl_tape in L2. 
      cbn in *. rewrite H1' in *.
      progress unfold finType_CS in *.
      do 2 eexists; hnf; split; cbn in *; eauto.
      + rewrite L2. cbn. simpl_tape. eauto.
      + rewrite L2. cbn. simpl_tape. rewrite rev_involutive. eauto.

      Unshelve.
      2,3,4: cbn; trivial.
      1,2: intros x; rewrite !List.map_map, <- map_rev; intros (? & <- & ?) % in_map_iff; cbn; trivial.
    }
  Qed.

  Definition MatchList : { M : mTM (bool+sigX)^+ 2 & states M -> bool } :=
    If (Inject M1 [|Fin.F1|])
       (M3;; Nop _ _ true)
       (Nop _ _ false).

  Definition MatchList_Rel : Rel (tapes (bool+sigX)^+ 2) (bool * tapes (bool+sigX)^+ 2) :=
    (if? (fun (tin tout : tapes (bool+sigX)^+ 2) =>
          forall (lst : list X),
            tin[@Fin.F1] ≂ lst ->
            exists (head : X) (tail : list X),
              lst = head :: tail /\
              tout[@Fin.F1] ≂ tail /\
              tout[@Fin.FS Fin.F1] ≂ head)
       ! (fun (tin tout : tapes (bool+sigX)^+ 2) =>
            forall (lst : list X),
            tin[@Fin.F1] ≂ lst ->
              lst = nil /\
              tout[@Fin.F1] ≂ nil)).

  Lemma MatchList_Sem :
    MatchList ⊫ MatchList_Rel.
  Proof.
    eapply WRealise_monotone.
    {
      unfold MatchList. eapply If_WRealise.
      - eapply Inject_WRealise. vector_dupfree. eapply Realise_WRealise, RealiseIn_Realise. eapply M1_Sem.
      - eapply Seq_WRealise.
        + eapply M3_WRealise.
        + eapply Realise_WRealise, RealiseIn_Realise. eapply Nop_total.
      - eapply Realise_WRealise, RealiseIn_Realise. eapply Nop_total.
    }
    {
      subst R1 M2 R2 M3 R3. cbn.
      intros tin (yout&tout).
      TMSimp repeat progress simpl_not_in.
      destruct yout, H; TMSimp.
      - specialize (H _ H0) as (head&tail&->).
        destruct H0 as (r1&r2&HE1&HE2).
        specialize (H1 head tail).
        spec_assert H1 as (H1&H1').
        {
          hnf. do 2 eexists; split; cbn in *; eauto.
        }
        do 2 eexists; repeat split; eauto.
      - auto.
      - congruence.
      - now assert (lst = nil) as -> by auto.
    }
  Qed.

  (* TODO: Termination *)

End MatchList.