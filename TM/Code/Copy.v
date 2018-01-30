(* Helper functions for verifying machines using CopySymbols and MoveToSymbol *)

Require Import TM.Code.CodeTM.
Require Import TM.Compound.CopySymbols TM.Compound.MoveToSymbol.

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