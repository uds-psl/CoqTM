Require Import Prelim.
Require Import TM.Combinators.If TM.Combinators.SequentialComposition.
Require Import TM.TM TM.Basic.Mono.
Require Import TM.Compound.MoveToSymbol.


Section FindSymbol.
  
  Variable sig : finType.
  Variable f : sig -> bool.

  Definition FindSymbol : { M : mTM sig 1 & states M -> FinType (EqType bool)} :=
    If (MoveToSymbol f L)
       (mono_Nop _ true)
       (Move _ R tt ;; MoveToSymbol f R).

  Definition to_symbol t :=
    match to_symbol_l f t with
    | (true,  t') => (true, t')
    | (false, t') => to_symbol_r f (tape_move_mono t' (None, R))
    end.

  Definition FindSymbol_Rel := Mk_R_p (fun t t' => t' = to_symbol t /\ tapeToList t = tapeToList (snd t')).

  Lemma FindSymbol_Realise :
    FindSymbol ⊨ FindSymbol_Rel.
  Proof.
    eapply Realise_monotone.
    - unfold FindSymbol. eapply If_Realise.
      + eapply MoveToSymbol_L_Realise.
      + eapply RealiseIn_Realise. eapply mono_Nop_Sem.
      + eapply Seq_Realise.
        * eapply RealiseIn_Realise. eapply Move_Sem.
        * eapply MoveToSymbol_R_Realise.
    - hnf. intros tin (yout, tout). intros H. hnf in H.
      destruct H as [H | H]; hnf in *.
      + destruct H as (t1&H1&->&->). unfold to_symbol. cbn in H1. destruct H1 as (H1&H2). now rewrite <- H1.
      + destruct H as(t1&(H1&H1')&((b&t2)&H2&H3&H4)); hnf in *. destruct b. destruct H2 as (_&H2).
        unfold to_symbol. cbn in H1. rewrite <- H1. cbn. rewrite H2 in *; clear H2. destruct_tapes. cbn in *. split; auto.
        rewrite <- H4. rewrite H1'. cbn. apply (@tapeToList_move _ _ R).
  Qed.

  Lemma to_symbol_r_true t t' :
    to_symbol_r f t = (true, t') ->
    exists m ls rs, t' = midtape ls m rs /\ f m = true. 
  Proof.
    intros H. destruct t; cbn in *; try congruence.
    destruct (f e) eqn:E; cbn in *.
    - inv H. eauto.
    - revert l e E H. induction l0 as [ | r rs IH ]; intros ls e E H; cbn in *. congruence.
      destruct (f r) eqn:E2.
      + inv H. eauto.
      + specialize (IH _ _ E2 H) as (m&ls'&rs'&->&IH). eauto.
  Qed.

  Lemma to_symbol_l_true t t' :
    to_symbol_l f t = (true, t') ->
    exists m ls rs, t' = midtape ls m rs /\ f m = true. 
  Proof.
    intros H. destruct t; cbn in *; try congruence.
    destruct (f e) eqn:E; cbn in *.
    - inv H. eauto.
    - revert l0 e E H. induction l as [ | l ls IH ]; intros rs e E H; cbn in *. congruence.
      destruct (f l) eqn:E2.
      + inv H. eauto.
      + specialize (IH _ _ E2 H) as (m&ls'&rs'&->&IH). eauto.
  Qed.

  Lemma to_symbol_true t t' :
    to_symbol t = (true, t') ->
    exists m ls rs, t' = midtape ls m rs /\ f m = true.
  Proof.
    intros H. unfold to_symbol in H.
    destruct (to_symbol_l f t) eqn:E.
    - destruct b eqn:E2.
      + inv H. eapply to_symbol_l_true; eauto.
      + cbn in H. eapply to_symbol_r_true in H as (m&ls&rs&->&H). eauto.
  Qed.

  Lemma to_symbol_r_false t t' :
    to_symbol_r f t = (false, t') ->
    (exists s, current t = Some s) -> forall x, x el (right t) -> f x = false.
  Proof.
    intros H (s&Hs) x Hx. destruct t eqn:E; cbn in *; auto.
    - congruence.
    - inv Hs. destruct (f s) eqn:E. congruence.
      revert s l E H. induction l0 as [ | r rs IH]; intros s ls E H; cbn in *; auto.
      destruct (f r) eqn:E2. congruence. destruct Hx as [-> | Hx]; eauto.
  Qed.
    
  Lemma to_symbol_l_false t t' :
    to_symbol_l f t = (false, t') ->
    (exists s, current t = Some s) -> forall x, x el (left t) -> f x = false.
  Proof.
    intros H (s&Hs) x Hx. destruct t eqn:E; cbn in *; auto.
    - congruence.
    - inv Hs. destruct (f s) eqn:E. congruence.
      revert s l0 E H. induction l as [ | l ls IH]; intros s rs E H; cbn in *; auto.
      destruct (f l) eqn:E2. congruence. destruct Hx as [-> | Hx]; eauto.
  Qed.

  Lemma to_symbol_false t t':
    to_symbol t = (false, t') ->
    forall x, x el (tapeToList t) -> f x = false.
  Proof.
    unfold to_symbol. destruct (to_symbol_l f t) eqn:E1. destruct b eqn:E1'; intros. congruence.
    cbn in *. destruct t eqn:E2; cbn in *; auto.
    - inv E1. cbn in *. destruct (f e) eqn:E3. congruence. destruct H0 as [-> | H0]; auto.
      eapply to_symbol_r_false; eauto. erewrite <- H.
      instantiate (1 := midtape [] e l). cbn. rewrite E3. reflexivity. all: cbn; eauto.
    - admit. (* BUG! *)
    - destruct (f e) eqn:E3. congruence. eapply to_symbol_l_false. erewrite <- E1.
      apply in_app_iff in H0 as [H0|H0].
      + instantiate (1 := midtape l e l0). cbn. rewrite E3. reflexivity.
      + destruct H0 as [-> | H0]; eauto.
        * cbn. rewrite E3. auto.
        * cbn. rewrite E3. auto.
  Admitted.

End FindSymbol.


Section FindUniqueSymbol.

  Variable sig : finType.
  Variable x : sig.


  Definition FindUniqueSymbol := FindSymbol (fun s => Dec (s = x)).

  Definition FindUniqueSymbol_Rel :=
    Mk_R_p
      (
        if?(fun t t' =>
              count (tapeToList t) x = 1 ->
              forall r1 r2,
                tapeToList t = rev r1 ++ [x] ++ r2 ->
                t' = midtape r1 x r2)
           ! (fun t _ => count (tapeToList t) x = 0)
      ).

  Lemma found r1 r2 s1 s2 :
    count (rev r1 ++ x :: r2) x = 1 -> rev r1 ++ x :: r2 = rev s1 ++ x :: s2 ->
    r1 = s1 /\ r2 = s2.
  Proof.
    intros H1 H2. revert s1 s2 r2 H1 H2. induction r1; cbn; intros.
    - decide (x = x) as [ | ?]; try tauto. inv H1. destruct s2; cbn in *.
      + inv H2. destruct s1; cbn in *. inv H1. auto.
  Admitted.

  Lemma FindUniqueSymbol_Realise : FindUniqueSymbol ⊨ FindUniqueSymbol_Rel.
  Proof.
    eapply Realise_monotone.
    - unfold FindUniqueSymbol. eapply FindSymbol_Realise.
    - hnf. intros tin (bout&tout) (H1&H2). hnf in *. destruct bout.
      + intros U r1 r2 H3. hnf in *. symmetry in H1. eapply to_symbol_true in H1 as (m&s1&s2&H&H').
        decide (m = x) as [->| ]; cbn in *; try congruence. clear H'.
        rewrite H in H2. cbn in *. rewrite H. clear tout H.
        rewrite H3 in H2, U. clear H3. clear tin. cbn in U.
        now pose proof (@found _ _ _ _ U H2) as [-> ->].
      + eapply notInZero. intros H3.
  Admitted.

End FindUniqueSymbol.