Require Export Shared.Base.
Require Export Datatypes.
Require Export Tape.
Require Export Relations.
Require Export Loop.

Require Export FinSet.
Require Export Vector.

Import FinSet.FinSet.
Import Vector.Vector.
Import Tape.Tape.
Import Loop.Loop.

Global Open Scope set_scope.

Module TuringMachine.

  Delimit Scope turing_scope with turing.
  Open Scope turing_scope.

  Definition Symbol (alphabet : finSet) := option (alphabet).

  Instance eq_dec_symbol (alphabet : finSet) : eq_dec (Symbol alphabet).
  Proof. unfold Symbol. intros a b. unfold dec. decide equality. decide (a0 = e); auto. Qed.
                                                  

  Definition Transitions (alphabet states : finSet) (numTapes : nat) :=
    states ->
    vector (Symbol alphabet) (S numTapes) ->
    states * vector (Tape.move * @Symbol alphabet) (S numTapes).

  
  (* numTapes is the number of tapes minus one *)
  Structure turingMachine (numTapes : nat) (alphabet : finSet) := TuringMachine
    {
      tm_states  : finSet;
      tm_initial : tm_states;
      tm_final   : tm_states -> bool;
      tm_transitions : Transitions alphabet tm_states numTapes
    }.
  Arguments TuringMachine numTapes alpha sigma initial final gamma : rename.

  Canonical Structure turingMachine_CS numTapes alpha sigma initial final gamma :=
    @TuringMachine numTapes alpha sigma initial final gamma.

  Record configuration (numTapes : nat) (alphabet states : finSet) := Configuration
    {
      conf_state : states;
      conf_tapes : vector (Tape.tape alphabet) (S numTapes)
    }.
  Arguments Configuration numTapes alpha sigma state tapes : rename.


  Section Semantics.
    Variables (numTapes : nat) (alpha : finSet).
    Variables (A : turingMachine numTapes alpha).
    Notation gamma := (@tm_transitions numTapes alpha A).
    Notation sigma := (@tm_states      numTapes alpha A).
    Notation init  := (@tm_initial     numTapes alpha A).
    Notation final := (@tm_final       numTapes alpha A).

    (** Step **)
    Definition doTapeAction' (tape : Tape.tape alpha) (move : Tape.move) (symbol : Symbol alpha) :=
        Tape.moveTape (Tape.write tape symbol) move.

    Definition doTapeAction (tuple : Tape.move * Symbol alpha) tape :=
      let (move, symbol) := tuple in doTapeAction' tape move symbol.
    
    Definition doTapesActions_multi (newState : sigma) tapes actions :=
      Configuration (numTapes := numTapes)
        newState
        (Vector.vector_map2 (fun action => fun tape => doTapeAction action tape ) actions tapes).

    Definition Step (conf : configuration numTapes alpha sigma) : configuration numTapes alpha sigma :=
      let (state, tapes) := conf in
      let (newState, actions) := gamma state (Vector.vector_map (Tape.symbolAt (alphabet := alpha)) tapes) in
      doTapesActions_multi newState tapes actions.

      
    Definition endConf : configuration numTapes alpha sigma -> bool := fun conf => final(conf_state conf).

    Definition execute
               (conf : configuration numTapes alpha sigma)
               (steps : nat) :=
      loop Step endConf (Incomplete conf) steps.


    Lemma execute_endConf conf conf' steps :
      execute conf steps = Complete conf' -> endConf conf' = true.
    Proof. apply loop_completed. Qed.
    
      
    Definition Execution (startconf endconf : configuration numTapes alpha sigma) :=
      { numSteps | execute startconf numSteps = Complete endconf }.

    
    Definition Relation := relation (vector (Tape.tape alpha) (S numTapes)).


    Definition initC tapes := @Configuration numTapes alpha sigma init tapes.

    (* Strongly realize a Relation *)
    Definition Realize (R : Relation) : Prop :=
      forall (inittape : vector (Tape.tape alpha) (S numTapes)),
      exists numSteps, exists finalState, exists finalTapes, final finalState = true /\
            execute (initC inittape) numSteps = Complete (Configuration finalState finalTapes) /\
            R inittape finalTapes.
                                  

    (* Just terminate *)
    Definition Terminates : Prop :=
      forall inittape,
      exists numSteps, exists endConf,
          execute (initC inittape) numSteps = Complete endConf.
    

    (* Week Realize a Relation *)
    Definition WRealize (R : Relation) : Prop :=
      forall inittape numSteps,
        match execute (initC inittape) numSteps with
        | Incomplete _ => True
        | Complete conf => R inittape (conf_tapes conf)
        end.

    (* Lemma WRealize_Realize R : Realize R <-> (Terminates /\ WRealize R). *)
    Lemma WRealize_Realize R : WRealize R /\ Terminates -> Realize R.
      intros (H1&H2). intros initTape.
      specialize (H1 initTape). specialize (H2 initTape) as (numSteps&(finalState&finalTapes)&H).
      exists numSteps. exists finalState. exists finalTapes. rewrite H. repeat split; auto.
      - rewrite <- execute_endConf with (conf := initC initTape)
                                       (conf' := Configuration finalState finalTapes) (steps := numSteps); auto.
      - specialize (H1 numSteps). rewrite H in H1. exact H1.
    Qed.

    (* Canonical Relation *)
    Definition CanoncialR : Relation :=
      fun initTape finalTape =>
        exists numSteps, exists endState, execute (initC initTape) numSteps = Complete (Configuration endState finalTape).

    Lemma WRealize_CanoncialR : WRealize CanoncialR.
    Proof.
      intros initTape numSteps. unfold CanoncialR. destruct (execute _ _) as [(endState&finitTapes)|] eqn:H; [|tauto]; eauto.
    Qed.

    Lemma WRealize_CanoncialR_R R initTape finalTape :
      WRealize R -> CanoncialR initTape finalTape -> R initTape finalTape.
    Proof.
      unfold WRealize, CanoncialR. intros H1 (numSteps&endState&H). specialize (H1 initTape numSteps). now rewrite H in H1.
    Qed.
    
  End Semantics.

  Section NullAction.
    Variable (numTapes : nat) (alpha : finSet) (A : turingMachine numTapes alpha).
    Notation sigma := (tm_states A).

    
    Definition null_action (symbols : Vector.vector (Symbol alpha) (S numTapes)) :
      Vector.vector (Tape.move * Symbol alpha) (S numTapes) :=
      (Vector.vector_map (fun x => (Tape.Stay, x)) symbols).
    Lemma exec_null_action (conf : configuration numTapes alpha sigma) :
      doTapesActions_multi
        (numTapes := numTapes) (alpha := alpha) (A := A)
        (conf_state conf)
        (conf_tapes conf)
        (null_action (Vector.vector_map (Tape.symbolAt (alphabet := alpha)) (conf_tapes conf))) =
      conf.
    Proof.
      destruct conf as [state tapes]. cbn in *.
      unfold doTapesActions_multi, doTapeAction, doTapeAction', null_action. f_equal.
      rewrite Vector.Vector.vector_map_map_eq.
      rewrite vector_map2_mapL_eq_id.
      unfold Tape.moveTape.
      rewrite vector_map2_simple_map.
      apply Vector.vector_map_eq_id.
      intros tapes'.
      apply Tape.read_write.
    Qed.
  End NullAction.
  


  (* Class of Turing Machines that do nothing *)
  Section DoNothingMachine.
    Variables (numTapes : nat) (alpha : finSet) (A : turingMachine numTapes alpha).
    Notation sigma := (tm_states A).
    Variable start : sigma.

    Definition gamma : Transitions alpha sigma numTapes :=
      fun state => fun symbols => (state, null_action (numTapes := numTapes) symbols).

    Definition final : sigma -> bool := fun _ => true.

    Definition doNothingMachine : @turingMachine numTapes alpha := TuringMachine (sigma := sigma) start final gamma.

    Definition R_nothing : @Relation numTapes alpha := fun tapes1 => fun tapes2 => tapes1 = tapes2.

    Theorem doNothingMachinesDoesNothing :
      Realize doNothingMachine R_nothing.
    Proof.
      intros initTape. exists 1. exists start. exists initTape. repeat split; cbn; auto.
    Qed.

  End DoNothingMachine.
  

End TuringMachine.