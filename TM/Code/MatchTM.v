Require Import TM.Code.CodeTM.

Require Import TM.Basic.Mono TM.Basic.Nop TM.Basic.Multi.
Require Import TM.Combinators.Combinators.
Require Import TM.LiftMN.

Require Import TM.Compound.TMTac.
Require Import TM.Compound.CopySymbols TM.Compound.MoveToSymbol.

(* Basic pattern matching *)
Section MatchSum.
  Variable X Y : Type.
  Variable (sigX sigY : finType).
  Hypothesis (codX : codeable sigX X) (codY : codeable sigY Y).

  Definition MatchSum_Rel : Rel (tapes (bool + (sigX+sigY))^+ 1) (bool * tapes (bool + (sigX+sigY))^+ 1) :=
    Mk_R_p (if? (fun (tin tout : tape (bool + (sigX+sigY))^+) =>
                   forall v : X + Y,
                     tape_encodes (Encode_Sum codX codY) tin v ->
                     exists x : X, v = inl x /\
                              tape_encodes (Encode_Map codX (@retract_r_l sigX sigY)) tout x)
              ! (fun (tin tout : tape ((bool + (sigX+sigY))^+)) =>
                   forall v : X + Y,
                     tape_encodes (Encode_Sum codX codY) tin v ->
                     exists y : Y, v = inr y /\
                              tape_encodes (Encode_Map codY (@retract_r_r sigX sigY)) tout y)).

  Definition MatchSum : { M : mTM (bool + (sigX+sigY))^+ 1 & states M -> bool } :=
    MATCH (Read_char _)
          (fun o => match o with
                 | Some (inr (inl true))  => Write (inl START) tt;; Move _ R true  (* inl *)
                 | Some (inr (inl false)) => Write (inl START) tt;; Move _ R false (* inr *)
                 | _ => mono_Nop _ true (* invalid input *)
                 end).

  Lemma MatchSum_Sem : MatchSum ⊨c(5) MatchSum_Rel.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold MatchSum. eapply Match_RealiseIn. cbn. eapply read_char_sem.
      instantiate (2 := fun o : option (bool + (sigX+sigY))^+ =>
                          match o with Some (inr (inl true)) => _ | Some (inr (inl false)) => _ | _ => _ end).
      cbn. intros [ s | ]; cbn.
      - destruct s as [ start | s]; cbn.
        + eapply RealiseIn_monotone'. eapply mono_Nop_Sem. omega.
        + destruct s as [cons | xy]; swap 1 2; cbn.
          * eapply RealiseIn_monotone'. eapply mono_Nop_Sem. omega.
          * destruct cons; (eapply Seq_RealiseIn; [eapply Write_Sem | eapply Move_Sem]).
      - eapply RealiseIn_monotone'. eapply mono_Nop_Sem. omega.
    }
    {
      cbn. omega.
    }
    {
      intros tin (yout&tout) H. destruct H as (H1&(t&(H2&H3)&H4)); hnf in *. subst.
      destruct_tapes; cbn in *.
      destruct h; cbn in *; TMSimp; eauto. destruct (map _) in H0; cbn in H0; congruence.
      destruct e; swap 1 2; cbn in *; TMSimp.
      - destruct s; swap 1 2; cbn in *; TMSimp.
        + destruct v; cbn in *; destruct (map _) in H0; cbn in *; congruence.
        + destruct b; cbn in *; TMSimp cbn in *; unfold encode_sum in *.
          * destruct v; TMSimp cbn in *. eexists; split; eauto.
            hnf. destruct (encode x1) eqn:E; cbn; do 2 eexists; split; hnf; cbn; eauto. all: rewrite E; cbn; eauto.
          * destruct v; TMSimp cbn in *. eexists; split; eauto.
            hnf. destruct (encode y) eqn:E; cbn; do 2 eexists; split; hnf; cbn; eauto. all: rewrite E; cbn; eauto.
      - destruct v; cbn in *.
        + destruct (map _) in H0; cbn in H0; inv H0.
        + destruct (map _) in H0; cbn in H0; inv H0.
    }
  Qed.

  (* Constructors *)
  Section SumConstr.

    Definition ConstrSum_Rel (is_left:bool) : Rel (tapes (bool + (sigX+sigY))^+ 1) (unit * tapes (bool + (sigX+sigY))^+ 1) :=
      Mk_R_p (
          ignoreParam
            (fun tin tout =>
               if is_left
               then forall x : X, tape_encodes (Encode_Map codX (@retract_r_l sigX sigY)) tin x ->
                             tape_encodes (Encode_Sum codX codY) tout (inl x)
               else forall y : Y, tape_encodes (Encode_Map codY (@retract_r_r sigX sigY)) tin y ->
                             tape_encodes (Encode_Sum codX codY) tout (inr y))).

    Definition ConstrSum (is_left:bool) : { M : mTM (bool + (sigX+sigY))^+ 1 & states M -> unit } :=
      Move _ L tt;; Write (inr (inl is_left)) tt;; Move _ L tt;; Write (inl START) tt;; Move _ R tt.

    Lemma ConstrSum_Sem (is_left:bool) : (ConstrSum is_left) ⊨c(9) (ConstrSum_Rel is_left).
    Proof.
      eapply RealiseIn_monotone.
      {
        eapply Seq_RealiseIn. eapply Move_Sem. eapply Seq_RealiseIn.
        eapply Write_Sem. eapply Seq_RealiseIn. eapply Move_Sem.
        eapply Seq_RealiseIn. eapply Write_Sem. eapply Move_Sem.
      }
      {
        cbn. omega.
      }
      {
        TMSimp ( cbn [Vector.nth] in * ). destruct is_left; cbn in *; subst; TMSimp.
        {
          destruct h; cbn in *; TMSimp; cbn in *.
          - destruct (encode _) in H0; cbn in *; congruence.
          - destruct (encode x) as [ | eX eXs] eqn:E;
              cbn in *; inv H0; cbv [tape_encodes_r]; cbn; rewrite E; cbn;
                (destruct x0; cbn; eauto).
        }
        {
          destruct h; cbn in *; TMSimp; cbn in *.
          - destruct (encode _) in H0; cbn in *; congruence.
          - destruct (encode y) as [ | eX eXs] eqn:E;
              cbn in *; inv H0; cbv [tape_encodes_r]; cbn; rewrite E; cbn;
                (destruct x; cbn; eauto).
        }
      }
    Qed.
                
      
  End SumConstr.

End MatchSum.


Section Copy.

  (*
  Section Test.

    Let inputX := encode (4, 3).
    Compute inputX.

    Let t : tape (Bool_Fin + Bool_Fin)^+ :=
      midtape [inr START] (inl (inl true))
              (map inl [inl true; inl true; inl true; inl false; 
                          inr true; inr true; inr true; inr false] ++ [inr STOP; inl (inl true)]).

    Compute tape_local t.
    Let stop_X :=
      fun (x : (Bool_Fin+Bool_Fin)^+) =>
        match x with
        | (inl (inl _)) => false
        | _ => true (* Stop at symbol from Y or halt/stop symbol *)
        end.

    Ltac re x := assert (x = x) by reflexivity.

    (* CopySymbols_Fun is not computable!  Use the equational rewriting to "execute"
     * (CopSymbols_Fun can be made computable by changing the termination proof to Qed.)
     *)
    Goal True.
      re (tape_local (fst (CopySymbols_Fun stop_X id (t, rightof (inr START) [])))).
      re (snd (CopySymbols_Fun stop_X id (t, rightof (inr START) []))).
      re ((left (snd (CopySymbols_Fun stop_X id (t, rightof (inr START) []))))).
      subst t; repeat ( rewrite CopySymbols_Fun_equation in *; cbn in * ); cbv [id] in *.
    Abort.


    Goal True.
      re (right (MoveToSymbol_Fun stop_X t)).
      re (left (MoveToSymbol_Fun stop_X t)).
      re (current (MoveToSymbol_Fun stop_X t)).
      re (tape_local (MoveToSymbol_Fun stop_X t)).
      Compute t.
      subst t; repeat ( rewrite MoveToSymbol_Fun_equation in *; cbn in * ).
    Abort.
    
  End Test.
   *)
  
  Variable sig : finType.
  Variable stop : sig -> bool.

  Lemma CopySymbols_pair_first tltr str1 x str2 tl' tr':
    (forall x, List.In x str1 -> stop x = false) ->
    (stop x = true) ->
    tape_local (fst tltr) = str1 ++ [x] ++ str2 ->
    (tl', tr') = CopySymbols_Fun stop id tltr ->
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

  Lemma CopySymbols_pair_second tltr str1 x str2 tl' tr':
    (forall x, List.In x str1 -> stop x = false) ->
    (stop x = true) ->
    tape_local (fst tltr) = str1 ++ [x] ++ str2 ->
    (tl', tr') = CopySymbols_Fun stop id tltr ->
    left tr' = rev str1 ++ left (snd tltr).
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

  Lemma MoveToSymbol_right t str1 str2 x :
    (forall x, List.In x str1 -> stop x = false) ->
    (stop x = true) ->
    tape_local t = str1 ++ x :: str2 ->
    right (MoveToSymbol_Fun stop t) = str2 /\
    current (MoveToSymbol_Fun stop t) = Some x.
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
    (forall x, List.In x str1 -> stop x = false) ->
    (stop x = true) ->
    tape_local t = str1 ++ x :: str2 ->
    left (MoveToSymbol_Fun stop t) = rev str1 ++ left t.
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

  Corollary MoveToSymbol_L_left t str1 str2 x :
    (forall x, List.In x str1 -> stop x = false) ->
    (stop x = true) ->
    tape_local_l t = str1 ++ x :: str2 ->
    left (MoveToSymbol_L_Fun stop t) = str2 /\
    current (MoveToSymbol_L_Fun stop t) = Some x.
  Proof.
    intros. pose proof (@MoveToSymbol_right (Mirror.mirror_tape t) str1 str2 x).
    rewrite !tape_local_mirror' in H2. repeat spec_assert H2 by eauto. 
    erewrite MoveToSymbol_mirror; swap 1 2. symmetry; now eapply Mirror.mirror_tape_involution.
    now simpl_tape in *.
  Qed.

  Corollary MoveToSymbol_L_right t str1 str2 x :
    (forall x, List.In x str1 -> stop x = false) ->
    (stop x = true) ->
    tape_local_l t = str1 ++ x :: str2 ->
    right (MoveToSymbol_L_Fun stop t) = rev str1 ++ right t.
  Proof.
    intros. pose proof (@MoveToSymbol_left (Mirror.mirror_tape t) str1 str2 x).
    rewrite !tape_local_mirror' in H2. repeat spec_assert H2 by eauto. 
    erewrite MoveToSymbol_mirror; swap 1 2. symmetry; now eapply Mirror.mirror_tape_involution.
    now simpl_tape in *.
  Qed.
  
End Copy.


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
            tape_encodes (Encode_Pair' codX codY) tin[@Fin.F1] xy ->
            tape_encodes (Encode_Map codY (@retract_inr sigX sigY)) tout[@Fin.F1] (snd xy) /\
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
            tape_encodes (Encode_Pair' codX codY) tin[@Fin.F1] xy ->
            tape_encodes (Encode_Map codY (@retract_inr sigX sigY)) tout[@Fin.F1] (snd xy) /\
            tape_encodes (Encode_Map codX (@retract_inl sigX sigY)) tout[@Fin.FS Fin.F1] (fst xy)
      ).

  (* Θ (18 + (4+?)*(?+1)*|enocode (fst x)|) *)

  Lemma tape_match_right_left (tau : finType) (t : tape tau) (x : tau) :
    right
      match left t with
      | [] => leftof x (right t)
      | a :: rs => midtape rs a (x :: right t)
      end =
    x :: right t.
  Proof. destruct t; cbn; auto. destruct l; cbn; auto. Qed.

  Lemma tape_match_left_right (tau : finType) (t : tape tau) (x : tau) :
    left
      match right t with
      | [] => rightof x (left t)
      | a :: rs => midtape (x :: left t) a rs
      end =
    x :: left t.
  Proof. destruct t; cbn; auto. destruct l0; cbn; auto. Qed.

  Lemma tape_match_symbols_right (tau : finType) (r : tau) (rs : list tau) (xs : list tau) :
    right
      match xs with
      | [] => leftof r rs
      | a :: ls' => midtape ls' a (r :: rs)
      end = r :: rs.
  Proof. destruct xs; cbn; auto. Qed.

  Lemma tape_match_symbols_tape_local_l (tau : finType) (r : tau) (rs : list tau) (xs : list tau) :
  tape_local_l
    match xs with
    | [] => leftof r rs
    | a :: ls' => midtape ls' a (r :: rs)
    end = xs.
  Proof. destruct xs; cbn; auto. Qed.
  
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
  

End Projection.



Section MatchList.


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
                     tape_encodes (Encode_List codX) tin lst ->
                     exists (head : X) (tail : list X),
                       lst = head :: tail)
              ! (fun (tin tout : tape (bool+sigX)^+) =>
                   forall (lst : list X),
                     tape_encodes (Encode_List codX) tin lst ->
                     lst = nil)
        ) ∩ ignoreParam (@IdR _)). 

  Lemma M1_Sem : M1 ⊨c(5) R1.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold MatchSum. eapply Match_RealiseIn. cbn. eapply read_char_sem.
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
        destruct h; cbn in *; TMSimp; eauto. destruct (map _) in H0; cbn in H0; congruence.
        destruct e; swap 1 2; cbn in *; TMSimp.
        - destruct s; swap 1 2; cbn in *; TMSimp.
          + destruct lst; cbn in *; inv H0.
          + destruct b; cbn in *; TMSimp cbn in *; unfold encode_list in *.
            * destruct lst; TMSimp cbn in *. eauto.
            * destruct lst; TMSimp cbn in *. eexists; split; eauto.
        - destruct lst; cbn in *; inv H0; eauto.
      }
      {
        destruct_tapes; cbn in *.
        destruct h; cbn in *; TMSimp; eauto. destruct e; cbn in *; TMSimp; auto.
        destruct s; cbn in *; TMSimp; auto.
        destruct b; cbn in *; TMSimp cbn in *; auto.
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
            tape_encodes (Encode_List codX)  tin[@Fin.F1] (head :: tail) ->
            tape_encodes (Encode_List codX) tout[@Fin.F1] tail /\
            left (tout[@Fin.FS Fin.F1]) = rev (map inr (map inr (encode head : list sigX))) ++ left (tin[@Fin.FS Fin.F1])
      ).


  Local Lemma CopySymbols_cons_first (head : X) (tail : list X) tltr tl' tr' rs' :
    (tl', tr') = CopySymbols_Fun stop_X' id tltr ->
    tape_local (fst tltr) = map inr (map inr (encode head)) ++ map inr (encode tail) ++ (inl STOP :: rs') ->
    tape_local (tl') = map inr (encode tail) ++ (inl STOP :: rs').
  Proof.
    intros. destruct tail as [ | ctail tail'] eqn:E1; cbn in *.
    - refine (CopySymbols_pair_first _ _ H0 H).
      + rewrite List.map_map. intros x (? & <- & ?) % in_map_iff. cbn. trivial.
      + cbn. trivial.
    - refine (CopySymbols_pair_first _ _ H0 H).
      + rewrite List.map_map. intros x (? & <- & ?) % in_map_iff. cbn. trivial.
      + cbn. trivial.
  Qed.

  Local Lemma CopySymbols_cons_second (head : X) (tail : list X) tltr tl' tr' rs' :
    (tl', tr') = CopySymbols_Fun stop_X' id tltr ->
    tape_local (fst tltr) = map inr (map inr (encode head)) ++ map inr (encode tail) ++ (inl STOP :: rs') ->
    left tr' = map inr (map inr (rev (encode head : list sigX))) ++ left (snd tltr).
  Proof.
    intros. rewrite !map_rev. destruct tail as [ | ctail tail'] eqn:E1; cbn in *.
    - refine (CopySymbols_pair_second _ _ H0 H).
      + rewrite List.map_map. intros x (? & <- & ?) % in_map_iff. cbn. trivial.
      + cbn. trivial.
    - refine (CopySymbols_pair_second _ _ H0 H).
      + rewrite List.map_map. intros x (? & <- & ?) % in_map_iff. cbn. trivial.
      + cbn. trivial.
  Qed.
  
  Local Lemma M2_WRealise : M2 ⊫ R2.
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
      TMSimp repeat progress simpl_not_in || cbn [Vector.nth] in *. destruct u.
      destruct h1; cbn in *; inv H0; [ do 2 destruct (map _); cbn in H3; congruence | inv H3]. clear H1. 
      split.
      - 
        epose proof CopySymbols_cons_first H (head := head) (tail := tail) (rs' := x1) as L1. cbn in *.
        spec_assert L1.
        {
          destruct (encode head); cbn.
          - destruct (encode_list codX tail); cbn; auto.
          - f_equal. now rewrite !List.map_app, <- app_assoc.
        }
        hnf.
        do 2 eexists; split; cbn.
        + eapply tape_match_left_right.
        + erewrite <- L1. destruct h2; cbn in *; auto. destruct (encode_list _); cbn in *; congruence. destruct l; cbn; auto.
      -
        epose proof CopySymbols_cons_second H (head := head) (tail := tail) (rs' := x1) as L1. cbn in *.
        spec_assert L1.
        {
          destruct (encode head); cbn.
          - destruct (encode_list codX tail); cbn; auto.
          - f_equal. now rewrite !List.map_app, <- app_assoc.
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
            tape_encodes (Encode_List codX) tin[@Fin.F1] (head :: tail) ->
            tape_encodes (Encode_List codX) tout[@Fin.F1] tail /\
            tape_encodes (Encode_Map codX (@retract_inr _ _)) tout[@Fin.FS Fin.F1] head
      ).


  Lemma M3_WRealise : M3 ⊫ R3.
  Proof.
    eapply WRealise_monotone.
    {
      unfold Proj. do 2 try eapply Seq_WRealise.
      all: try (eapply Inject_WRealise; [vector_dupfree| ]).
      3: repeat eapply Seq_WRealise.
      all: try (eapply Realise_WRealise, RealiseIn_Realise;
                first [ eapply Move_Sem | eapply WriteMove_Sem | eapply Write_Sem ]).
      - eapply M2_WRealise.
      - eapply MoveToSymbol_L_WRealise.
    }
    {
      subst R1 M2 R2 M3 R3. hnf. intros. hnf. destruct y. intros head tail.
      TMSimp repeat progress simpl_not_in || cbn [Vector.nth] in *. destruct u.
      destruct h3; cbn in *; inv H0; [destruct (encode _); cbn in H3; congruence | inv H3]. clear H1.
      specialize (H head tail). spec_assert H by (hnf; do 2 eexists; hnf; split; cbn; eauto). destruct H as (H1&H1').
      split; eauto. hnf; unfold tape_encodes_r; cbn in *. clear b H2 H1.
      rewrite tape_match_left_right in *. unfold finType_CS in *; rewrite H1' in *.

      assert (tape_local_l (tape_move_mono h4 (Some (inl STOP), L)) =
              rev (map inr (map inr (encode head))) ++ inl START :: left h2) as L1.
      {
        repeat ( rewrite <- !app_assoc in *; cbn in * ).
        destruct h4; cbn in *; try congruence. subst. apply tape_match_symbols_tape_local_l.
      }

      epose proof (MoveToSymbol_L_left (stop := stop_X') _ _ L1) as (L2&L3).
      epose proof (MoveToSymbol_L_right (stop := stop_X') _ _ L1) as L4.

      cbn in *. rewrite H1' in *.
      progress unfold finType_CS in *.
      do 2 eexists; hnf; split; cbn in *; eauto.
      + erewrite tape_left_move_right; eauto.
      + erewrite tape_local_move_right; eauto.
        eapply tape_local_iff. do 2 eexists. split; eauto. split.
        eapply L3. rewrite L4. cbn. rewrite tape_match_symbols_right. cbn. now rewrite rev_involutive.

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
            tape_encodes (Encode_List codX) tin[@Fin.F1] lst ->
            exists (head : X) (tail : list X),
              lst = head :: tail /\
              tape_encodes _ (tout[@Fin.F1]) tail /\
              tape_encodes (Encode_Map codX (@retract_inr _ _)) tout[@Fin.FS Fin.F1] head)
       ! (fun (tin tout : tapes (bool+sigX)^+ 2) =>
            forall (lst : list X),
              tape_encodes (Encode_List codX) tin[@Fin.F1] lst ->
              tape_encodes (Encode_List codX) tout[@Fin.F1] nil /\
              lst = nil)).

  Lemma MatchList_Sem :
    MatchList ⊫ MatchList_Rel.
  Proof.
    eapply WRealise_monotone.
    {
      unfold MatchList. eapply If_WRealsie.
      - eapply Inject_WRealise. vector_dupfree. eapply Realise_WRealise, RealiseIn_Realise. eapply M1_Sem.
      - eapply Seq_WRealise.
        + eapply M3_WRealise.
        + eapply Realise_WRealise, RealiseIn_Realise. eapply Nop_total.
      - eapply Realise_WRealise, RealiseIn_Realise. eapply Nop_total.
    }
    {
      subst R1 M2 R2 M3 R3. cbn.
      TMSimp repeat progress simpl_not_in || cbn [Vector.nth] in *.
      destruct b, H; TMSimp repeat progress simpl_not_in || cbn [Vector.nth] in *.
      - specialize (H lst). spec_assert H as (head&tail&->) by (do 2 eexists; split; cbn; eauto).
        specialize (H1 head tail).
        spec_assert H1 as (H1&H1').
        {
          hnf. do 2 eexists; split; cbn in *; eauto.
        }
        do 2 eexists; repeat split; eauto.
      - auto.
      - congruence.
      - assert (lst = nil) as ->.
        {
          eapply H. cbn. hnf; do 2 eexists; split; cbn; eauto.
        }
        split; eauto. hnf. do 2 eexists; split; cbn in *; eauto.
    }
  Qed.

  (* TODO: Termination *)

End MatchList.




(** * Reductions for derived types *)

Require ChangeAlphabet.

Section MatchOption.

  (* Matching of option reduces to matching of sums with [Empty_set] *)

  Variable X : Type.
  Variable (sigX : finType).
  Hypothesis (codX : codeable sigX X).

  Compute encode None.
  Compute encode (Some 42).

  Definition MatchOption_Rel : Rel (tapes (bool + sigX)^+ 1) (bool * tapes (bool + sigX)^+ 1) :=
    Mk_R_p (if? (fun (tin tout : tape (bool + sigX)^+) =>
                   forall v : option X,
                     tape_encodes (Encode_Option codX ) tin v ->
                     exists x : X, v = Some x)
              ! (fun (tin tout : tape (bool + sigX)^+) =>
                   forall v : option X,
                     tape_encodes (Encode_Option codX ) tin v ->
                     v = None)).

  Let retr' : TRetract (bool + (sigX + Empty_set)) (bool + sigX) .
  Proof. econstructor. eapply tretract_sum; auto_inj. Defined.
    
  Definition MatchOption : { M : mTM (bool + sigX)^+ 1 & states M -> bool }.
  Proof.
    eapply ChangeAlphabet.ChangeAlphabet. 3: eapply (@MatchSum sigX (FinType (EqType Empty_set))).
    - eapply retr'.
    - cbn. do 2 constructor.
  Defined.


  
  Lemma MatchOption_Sem :
    MatchOption ⊨c(5) MatchOption_Rel.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold MatchOption. eapply LiftSigmaTau.Lift_RealiseIn.
      - eapply tight_retract_strong. cbn. eapply (ChangeAlphabet.retr' retr').
      - eapply (MatchSum_Sem codX Encode_Unit).
    }
    { omega. }
    {
      hnf. intros tin (yout&tout). intros H. destruct_tapes; cbn in *.
      hnf in *. destruct yout; cbn in *.
      {
        intros [ v | ] Hv; cbn in *.
        - specialize (H (inl v)).
          spec_assert H as (x&H).
          {
            destruct Hv as (r1&r2&Hv1&Hv2); cbn in *.
            eapply (ChangeAlphabet.encodeTranslate_tau1 (inl true) (retr := retr')).
            hnf. do 2 eexists. split. exact Hv1. exact Hv2.
          }
          inv H. eauto.
        - specialize (H (inr tt)).
          spec_assert H as (x&H1&H2).
          {
            destruct Hv as (r1&r2&Hv1&Hv2); cbn in *.
            eapply (ChangeAlphabet.encodeTranslate_tau1 (inl true) (retr := retr')).
            hnf. do 2 eexists. split. exact Hv1. exact Hv2.
          }
          inv H1.
      }
      {
        intros [ v | ] Hv; cbn in *.
        - specialize (H (inl v)).
          spec_assert H as (x&H1&H2).
          {
            destruct Hv as (r1&r2&Hv1&Hv2); cbn in *.
            eapply (ChangeAlphabet.encodeTranslate_tau1 (inl true) (retr := retr')).
            hnf. do 2 eexists. split. exact Hv1. exact Hv2.
          }
          inv H1.
        - specialize (H (inr tt)).
          spec_assert H as (x&H).
          {
            destruct Hv as (r1&r2&Hv1&Hv2); cbn in *.
            eapply (ChangeAlphabet.encodeTranslate_tau1 (inl true) (retr := retr')).
            hnf. do 2 eexists. split. exact Hv1. exact Hv2.
          }
          inv H. eauto.
      }
    }
  Qed.

End MatchOption.


(* TODO: Konstruktor für Listen und Tupel *)


(* TODO: Match für Zahlen: von Listen-Match ableiten *)


Section MapSum.

  Variable n : nat.
  Variable (sigX sigY sigZ : finType).
  Variable (X Y Z : Type) (codX : codeable sigX X) (codY : codeable sigY Y) (codZ : codeable sigZ Z).

  Variable (inputTape outputTape : Fin.t n).
  
  Local Definition sig_add_sum : finType := FinType(EqType((bool+(sigX+sigY))+sigZ)).
  Local Definition sig_add_X : finType := FinType(EqType(sigX+sigZ)).
  Local Definition sig_add_Y : finType := FinType(EqType(sigY+sigZ)).

  Local Definition retr1 : TRetract (bool+(sigX+sigY)) (bool+(sigX+sigY)+sigZ).
  Proof. econstructor. eapply retract_inl. Defined.

  Local Definition retr2 : TRetract sigZ (bool+(sigX+sigY)+sigZ).
  Proof. econstructor. eapply retract_inr. Defined.

  Local Definition retr3 : TRetract (sigX+sigZ) ((bool+(sigX+sigY))+sigZ).
  Proof.
    econstructor. eapply tretract_sum.
    - eapply retract_r_l.
    - eapply inversion_retract, inverse_id.
  Defined.

  Local Definition retr4 : TRetract (sigY+sigZ) ((bool+(sigX+sigY))+sigZ).
  Proof.
    econstructor. eapply tretract_sum.
    - eapply retract_r_r.
    - eapply inversion_retract, inverse_id.
  Defined.

  Instance enc_X' : codeable sig_add_X X := Encode_Map codX (@retract_inl _ _).
  Instance enc_Z_X : codeable sig_add_X Z := Encode_Map codZ (@retract_inr _ _).
  Instance enc_Y' : codeable sig_add_Y Y := Encode_Map codY (@retract_inl _ _).
  Instance enc_Z_Y : codeable sig_add_Y Z := Encode_Map codZ (@retract_inr _ _).
  Instance enc_XY : codeable sig_add_sum (X+Y) := Encode_Map (Encode_Sum codX codY) (Build_TRetract retr1).
  Instance enc_Z' : codeable sig_add_sum Z := Encode_Map codZ (@retract_inr _ _).

  Variable f : X -> Z.
  Variable g : Y -> Z.

  Variable M1 : { M : mTM (sig_add_X ^+) n & states M -> unit }.
  Variable M2 : { M : mTM (sig_add_Y ^+) n & states M -> unit }.

  Hypothesis M1_Computes : M1 ⊫ Computes_Rel inputTape outputTape enc_X' enc_Z_X f.
  Hypothesis M2_Computes : M2 ⊫ Computes_Rel inputTape outputTape enc_Y' enc_Z_Y g.

  Definition map_sum : X + Y -> Z :=
    fun s => match s with
          | inl x => f x
          | inr y => g y
          end.
  
  Variable (defX : sigX) (defY : sigY) (defZ : sigZ).

  Definition MapSum : { M : mTM (sig_add_sum ^+) n & states M -> unit } :=
    If (ChangeAlphabet.ChangeAlphabet retr1 (inr (inl defX)) (Inject (MatchSum sigX sigY) [|inputTape|]))
      (ChangeAlphabet.ChangeAlphabet retr3 (inl defX) M1)
      (ChangeAlphabet.ChangeAlphabet retr4 (inl defY) M2).

  Hypothesis DefX : forall x : X, ~ defX el encode x \/ (forall t' : sigX + sigZ, exists s' : sigX, retract_inl_g t' = Some s').
  Hypothesis DefY : forall y : Y, ~ defY el encode y \/ (forall t' : sigY + sigZ, exists s' : sigY, retract_inl_g t' = Some s').

  Lemma MapSum_Computes : MapSum ⊫ Computes_Rel inputTape outputTape enc_XY enc_Z' map_sum.
  Proof.
    eapply WRealise_monotone.
    {
      unfold MapSum. eapply If_WRealsie.
      - eapply LiftSigmaTau.Lift_WRealise.
        + eapply tight_retract_strong. cbn. refine (ChangeAlphabet.retr' _). apply retr1.
        + eapply Inject_WRealise.
          * vector_dupfree.
          * eapply Realise_WRealise, RealiseIn_Realise. apply (MatchSum_Sem codX codY).
      - apply (ChangeAlphabet.ChangeAlphabet_Computes_WRealise retr3 (inl defX) f).
        + left. intros. cbn. intros (?&?&?) % in_map_iff. congruence.
        + eapply M1_Computes.
      - apply (ChangeAlphabet.ChangeAlphabet_Computes_WRealise retr4 (inl defY) g).
        + left. intros. cbn. intros (?&?&?) % in_map_iff. congruence.
        + eapply M2_Computes.
    }
    { clear M1_Computes M2_Computes M1 M2.
      hnf. intros tin (()&tout). intros H. destruct_tapes; cbn in *.
      intros s H4. destruct H; destruct H as (tmid&H1&H2); hnf in H1, H2; cbn in H1, H2.
      {
        destruct H1 as (H1&H0); hnf in H0, H1. specialize (H1 s). spec_assert H1 as (x&->&H1).
        {
          eapply ChangeAlphabet.encodeTranslate_tau1 in H4. cbn in H4.
          unfold LiftSigmaTau.surjectTapes, LiftSigmaTau.surjectTape, LiftSigmaTau.mapTapes in *. cbn in *.
          erewrite VectorSpec.nth_map; eauto.
        } subst; cbn. specialize (H2 x). spec_assert H2.
        { clear H4 H2. unfold enc_X'.
          eapply (ChangeAlphabet.encodeTranslate_tau1) in H1. eapply (ChangeAlphabet.encodeTranslate_tau2 (def := inr _)).
          - left. cbn. intros (?&?&?)%in_map_iff. congruence.
          - eapply (ChangeAlphabet.encodeTranslate_tau2 (def := defX)).
            + cbn. auto.
            + destruct H1 as (r1&r2&HE1&HE2). hnf. cbn in *. exists r1, r2. split; cbn.
              * rewrite <- HE1. f_equal. cbn. f_equal. clear HE1 HE2.
                unfold ChangeAlphabet.surjectTape, LiftSigmaTau.surjectTapes, LiftSigmaTau.surjectTape, LiftSigmaTau.mapTapes in *.
                erewrite !VectorSpec.nth_map; eauto. unfold TRetr_f, TRetr_g. cbn.
                rewrite !LiftSigmaTau.mapTape_mapTape.
                eapply LiftSigmaTau.mapTape_ext; intros. destruct a; cbn; auto. do 3 (destruct s; cbn; auto).
              * rewrite <- HE2. f_equal. cbn. f_equal. clear HE1 HE2.
                unfold ChangeAlphabet.surjectTape, LiftSigmaTau.surjectTapes, LiftSigmaTau.surjectTape, LiftSigmaTau.mapTapes in *.
                erewrite !VectorSpec.nth_map; eauto. unfold TRetr_f, TRetr_g. cbn.
                rewrite !LiftSigmaTau.mapTape_mapTape.
                eapply LiftSigmaTau.mapTape_ext; intros. destruct a; cbn; auto. do 3 (destruct s; cbn; auto).
        } 
        clear H4 H1. progress unfold finType_CS in *. destruct H2 as (r1&r2&HE1&HE2). hnf. cbn in *. exists r1, r2; split; cbn; eauto.
        cbn in *. clear HE1 r1. progress unfold finType_CS in *. unfold sig_add_sum.
        unfold finType_CS. rewrite HE2. clear HE2. cbn. rewrite !List.map_map. cbn. auto.
      }
      {
        destruct H1 as (H1&H0); hnf in H0, H1. specialize (H1 s). spec_assert H1 as (y&->&H1).
        {
          eapply ChangeAlphabet.encodeTranslate_tau1 in H4.
          unfold LiftSigmaTau.surjectTapes, LiftSigmaTau.surjectTape, LiftSigmaTau.mapTapes in *. cbn in *.
          erewrite VectorSpec.nth_map; eauto.
        } subst; cbn. specialize (H2 y). spec_assert H2.
          { clear H4 H2. unfold enc_Y'. 
            eapply (ChangeAlphabet.encodeTranslate_tau1) in H1. eapply (ChangeAlphabet.encodeTranslate_tau2 (def := inr _)).
            - left. cbn. intros (?&?&?)%in_map_iff. congruence.
            - eapply (ChangeAlphabet.encodeTranslate_tau2 (def := defY)).
              + cbn. auto.
              + destruct H1 as (r1&r2&HE1&HE2). hnf. cbn in *. exists r1, r2. split; cbn.
                * rewrite <- HE1. f_equal. cbn. f_equal. clear HE1 HE2.
                  unfold ChangeAlphabet.surjectTape, LiftSigmaTau.surjectTapes, LiftSigmaTau.surjectTape, LiftSigmaTau.mapTapes in *.
                  erewrite !VectorSpec.nth_map; eauto. unfold TRetr_f, TRetr_g. cbn.
                  rewrite !LiftSigmaTau.mapTape_mapTape.
                  eapply LiftSigmaTau.mapTape_ext; intros. destruct a; cbn; auto. do 3 (destruct s; cbn; auto).
                * rewrite <- HE2. f_equal. cbn. f_equal. clear HE1 HE2.
                  unfold ChangeAlphabet.surjectTape, LiftSigmaTau.surjectTapes, LiftSigmaTau.surjectTape, LiftSigmaTau.mapTapes in *.
                  erewrite !VectorSpec.nth_map; eauto. unfold TRetr_f, TRetr_g. cbn.
                  rewrite !LiftSigmaTau.mapTape_mapTape.
                  eapply LiftSigmaTau.mapTape_ext; intros. destruct a; cbn; auto. do 3 (destruct s; cbn; auto).
          } 
          clear H4 H1. progress unfold finType_CS in *. destruct H2 as (r1&r2&HE1&HE2). hnf. cbn in *. exists r1, r2. split; cbn; auto.
          cbn in *. clear HE1 r1. progress unfold finType_CS in *. unfold sig_add_sum. unfold finType_CS. rewrite HE2. clear HE2.
          cbn. rewrite !List.map_map. cbn. auto.
      }
    }
    Unshelve. all: eauto.
  Qed.
  
End MapSum.