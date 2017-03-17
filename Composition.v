Require Export TM.

Import TuringMachine.
Import FinSet.FinSet.
Import Loop.Loop.
Import Vector.Vector.

Module Composition.
  Section Composition.
    Variables (numTapes : nat) (alpha : finSet).
    Variables (A B : turingMachine numTapes alpha).
    Notation gamma1 := (@tm_transitions numTapes alpha A).
    Notation gamma2 := (@tm_transitions numTapes alpha B).
    Notation sigma1 := (@tm_states      numTapes alpha A).
    Notation sigma2 := (@tm_states      numTapes alpha B).
    Notation init1  := (@tm_initial     numTapes alpha A).
    Notation init2  := (@tm_initial     numTapes alpha B).
    Notation final1 := (@tm_final       numTapes alpha A).
    Notation final2 := (@tm_final       numTapes alpha B).


    (* Definition sigma3 := sigma1 ⊕ sigma2. *)
    Definition sigma3 := finSet_union sigma1 sigma2.

    Definition gamma3 : Transitions alpha sigma3 numTapes.
    Proof.
      unfold Transitions.
      intros [x|y] vec.
      - destruct (final1 x).
        + apply (inr init2, null_action vec).
        + pose proof (gamma1 x vec) as [nextState actions]; apply (inl nextState, actions).
      - pose proof (gamma2 y vec) as [nextState actions]; apply (inr nextState, actions).
    Defined.

    Definition final3 : sigma3 -> bool :=
      fun state =>
        match state with
        | inl _ => false
        | inr s => final2 s
        end.

    Definition Composition : turingMachine numTapes alpha.
    Proof.
      apply TuringMachine with (sigma := sigma3).
      - exact (inl init1).
      - exact final3.
      - exact gamma3.
    Defined.

    (* Composition of two Relations *)
    Definition R_comp (R1 R2 : Relation numTapes alpha) : Relation numTapes alpha :=
      fun a b => exists c, R1 a c /\ R2 c b.

    Notation "R1 '∘' R2" := (R_comp R1 R2) (at level 70).


    Definition liftConfL  (config : configuration numTapes alpha sigma1) : configuration numTapes alpha sigma3 :=
      let (state, tapes) := config in @Configuration numTapes alpha sigma3 (inl state) tapes.

    Definition liftConfR  (config : configuration numTapes alpha sigma2) : configuration numTapes alpha sigma3 :=
      let (state, tapes) := config in @Configuration numTapes alpha sigma3 (inr state) tapes.


    Definition liftFinalL : sigma3 -> bool :=
      fun s => match s with
            | inl s1 => final1 s1
            | inr s2 => true
            end.

    Definition liftFinalR : sigma3 -> bool :=
      fun s => match s with
            | inl s1 => false
            | inr s2 => final2 s2
            end.
    

    Lemma p_final_liftL conf :
      final1 (conf_state conf) = liftFinalL (conf_state (numTapes := numTapes) (alphabet := alpha) (liftConfL conf)).
    Proof. destruct conf. reflexivity. Qed.
      
    Lemma trans_seq_liftL state symbols newstate actions :
      final1 state = false ->
      gamma1 state       symbols = (newstate, actions) ->
      gamma3 (inl state) symbols = (inl newstate, actions).
    Proof.
      intros H1 H2. unfold gamma3. destruct (final1 state); [discriminate|clear H1].
      destruct (gamma1 state symbols). congruence.
    Qed.

    Lemma trans_seq_liftR state symbols newstate actions :
      final2 state = false ->
      gamma2 state       symbols = (newstate, actions) ->
      gamma3 (inr state) symbols = (inr newstate, actions).
    Proof.
      intros H1 H2. unfold gamma3. destruct (final2 state); [discriminate|clear H1].
      destruct (gamma2 state symbols). congruence.
    Qed.


    Lemma step_seq_liftL c :
      final1 (conf_state c) = false ->
      Step (numTapes := numTapes) (alpha := alpha) (A := Composition) (liftConfL c) =
      liftConfL (Step (numTapes := numTapes) (alpha := alpha) (A := A) c).
    Proof.
      intros H. destruct c as [state tapes]. cbn. destruct (final1 state) eqn:H'; [|clear H H'].
      - enough (false = true) by discriminate. rewrite <- H, <- H'. reflexivity.
      - destruct (gamma1 state (vector_map (Tape.symbolAt (alphabet:=alpha)) tapes)) as [state' tapes'].
        unfold liftConfL, doTapesActions_multi. cbn. reflexivity.
    Qed.

    Lemma step_seq_liftR c :
      final2 (conf_state c) = false ->
      Step (numTapes := numTapes) (alpha := alpha) (A := Composition) (liftConfR c) =
      liftConfR (Step (numTapes := numTapes) (alpha := alpha) (A := B) c).
    Proof.
      intros H. destruct c as [state tapes]. cbn. destruct (final2 state) eqn:H'; [|clear H H'].
      - enough (false = true) by discriminate. rewrite <- H, <- H'. reflexivity.
      - destruct (gamma2 state (vector_map (Tape.symbolAt (alphabet:=alpha)) tapes)) as [state' tapes'].
        unfold liftConfL, doTapesActions_multi. cbn. reflexivity.
    Qed.


    Lemma trans_liftL_true state symbols :
      final1 state = true ->
      gamma3 (inl state) symbols = (inr init2, null_action symbols).
    Proof.
      intros H. unfold gamma3. destruct (final1 state); [reflexivity|congruence].
    Qed.

    Lemma eq_ctape_lift_conf_L outc :
      conf_tapes (liftConfL outc) = conf_tapes outc.
    Proof.
      destruct outc as [state tapes]. unfold liftConfL. reflexivity.
    Qed.

    
    Theorem Composition_seq (R1 R2 : Relation numTapes alpha) :
      @Realize numTapes alpha A R1 -> Realize B R2 -> Realize Composition (R1 ∘ R2).
    Proof.
      intros H1 H2. intros initTape.
      specialize (H1 initTape)  as (numSteps1&fin1&finTapes1&finFinal1&Exec1&HR1).
      specialize (H2 finTapes1) as (numSteps2&fin2&finTapes2&finFinal2&Exec2&HR2).
      exists (numSteps1 + numSteps2). exists (inr fin2). exists (finTapes2). repeat split; unfold R_comp; eauto.

      unfold execute in *.
      apply loop_merge with (p := fun conf => liftFinalL (conf_state conf))
                            (q := fun conf => final3 (conf_state conf))
                            (a2 := (Configuration (sigma := sigma3) (inl fin1) finTapes1))
                            (a3 := (Configuration (sigma := sigma3) (inr init2) finTapes1)).
      - unfold liftFinalL. intros [state tapes] H2. destruct (conf_state (Configuration state tapes)); [reflexivity|congruence].
      - 
        pose proof (loop_lift (liftConfL)
                              (fun conf => final1 (conf_state conf))
                              (fun conf => liftFinalL (conf_state conf))
                              (Configuration init1 initTape)
                              (Configuration fin1  finTapes1)
                              (Step (A := A))
                              (Step (A := Composition))
                              (numSteps1)) as Wonder.
        cbn in Wonder. rewrite Wonder.
        + cbn. f_equal.
        + intros [state tapes]. unfold liftConfL. cbn. reflexivity.
        + intros [state tapes]. intros H. symmetry. now apply step_seq_liftL.
        + assumption.
      - unfold Step. cbn. unfold bool2Prop in finFinal1. destruct (final1 fin1); auto.
        pose proof (exec_null_action (numTapes := numTapes)
                                     (alpha    := alpha)
                                     (A        := Composition)
                                     (Configuration (sigma := sigma3) (inr init2) finTapes1)) as Wonder.
        simpl in Wonder. assumption.
      - reflexivity.
      - symmetry.
        pose proof (loop_lift (liftConfR)
                              (fun conf => final2 (conf_state conf))
                              (fun conf => final3 (conf_state conf))
                              (Configuration init2 finTapes1)
                              (Configuration fin2  finTapes2)
                              (Step (A := B))
                              (Step (A := Composition))
                              (numSteps2)) as Wonder.
        apply Wonder.
        + intros [state tapes]. reflexivity.
        + intros [state tapes]. intros H. symmetry. now apply step_seq_liftR.
        + assumption.
   Qed. (* Hooray!!! *)

    
  End Composition.
End Composition.