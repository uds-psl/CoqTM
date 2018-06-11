Require Import HeapTM.
Require Import LookupTM JumpTargetTM.
Require Import MatchList TokTM.


(** ** Step semantics *)


Section Semantics.

  Implicit Types H : Heap.
  Implicit Types T V : list HClos.
  Implicit Types a b c : HAd.
  Implicit Types g : HClos.
  Implicit Types (P Q : Pro).

  Definition put H e := (H++[e],|H|).
  Definition get H a := nth_error H a.

  Definition tailRecursion P a T : list HClos :=
    match P with
    | [] => T
    |  _ => (P, a) :: T
    end.


  Definition state : Type := list HClos * list HClos * Heap.
  

  Inductive step : state -> state -> Prop :=
  | step_pushVal P P' Q a T V H :
      jumpTarget O [] P = Some (Q, P') ->
      step (((lamT :: P), a) :: T, V, H) (tailRecursion P' a T, (Q, a) :: V, H)
  | step_beta a b g P Q H H' c T V :
      put H (Some (g, b)) = (H', c) ->
      step (((appT :: P), a) :: T, g :: (Q, b) :: V, H) ((Q, c) :: tailRecursion P a T, V, H')
  | step_load P a x g T V H :
      lookup H a x = Some g ->
      step (((varT x :: P), a) :: T, V, H) (tailRecursion P a T, g :: V, H)
  .

  Definition step_fun : state -> option state :=
    fun '(T, V, H) =>
      match T with
      | ((lamT :: P), a) :: T =>
        match jumpTarget O [] P with
        | Some (Q, P') =>
          Some (tailRecursion P' a T, (Q, a) :: V, H)
        | _ => None
        end
      | ((appT :: P), a) :: T =>
        match V with
        | g :: (Q, b) :: V =>
          let (H', c) := put H (Some (g, b)) in
          Some ((Q, c) :: tailRecursion P a T, V, H')
        | _ => None
        end
      | ((varT x :: P), a) :: T =>
        match lookup H a x with
        | Some g => Some (tailRecursion P a T, g :: V, H)
        | _ => None
        end
      | _ => None
      end.

  Goal forall s s', step s s' -> step_fun s = Some s'.
  Proof.
    induction 1; cbn; TMSimp; auto.
    unfold put in *. now inv_pair.
  Qed.

End Semantics.
      



(** ** Step Machine *)


Section StepMachine.

(** Here we compose the [Lookup] and [JumpTarget] machines, together with some matches.
The semantics of the step machine are only defined, similarly to [Lookup] and [JumpTarget], when the simulated heap machine steps.

The machine operates on lists of closures and on a heap.
However, because [Lookup] requires an additional [sigOption sigHEnt], the alphabet also has to be extended by [sigOption sigHEnt].
*)

  Variable sigStep : finType.
  Variable retr_closures_step : Retract (sigList sigHClos) sigStep.
  Variable retr_heap_step : Retract sigHeap sigStep.
  Variable retr_optHEnt_step : Retract (sigOption sigHEnt) sigStep.


  Local Definition retr_clos_step : Retract sigHClos sigStep := ComposeRetract _ retr_closures_step.
  Local Definition retr_pro_step : Retract sigPro sigStep := ComposeRetract _ retr_closures_step.
  Local Definition retr_tok_step : Retract sigTok sigStep := ComposeRetract _ retr_closures_step.


  (** Instance of the [Lookup] and [JumpTarget] machine *)
  Local Definition Step_Lookup := Lookup retr_heap_step retr_optHEnt_step.
  Local Definition Step_JumpTarget := ChangeAlphabet JumpTarget retr_pro_step.




  Definition Step_lam : pTM sigStep^+ unit 11.
  Admitted.

  Definition Step_app : pTM sigStep^+ unit 11.
  Admitted.

  Definition Step_var : pTM sigStep^+ unit 11.
  Admitted.


  Definition Step : pTM sigStep^+ unit 11 :=
    If (MatchList sigHClos_fin ⇑ _ @ [|Fin0; Fin3|])
       (MatchPair sigPro_fin sigHAd_fin ⇑ retr_clos_step @ [|Fin3; Fin4|];;
        If (MatchList sigTok_fin ⇑ retr_pro_step @ [|Fin4; Fin5|])
           (MATCH (MatchTok ⇑ retr_tok_step @ [|Fin5|])
                  (fun t : option ATok =>
                     match t with
                     | Some lamAT =>
                       Step_lam
                     | Some appAT =>
                       Step_app
                     | Some retAT =>
                       Nop default
                     | None (* Variable *) =>
                       Step_var
                     end)
           )
           (Nop default)
       )
       (Nop default)
  .
  


  Definition Step_Rel : pRel sigStep^+ unit 11 :=
    ignoreParam (
        fun tin tout =>
          forall (T : list HClos) (V : list HClos) (H : Heap) (T' : list HClos) (V' : list HClos) (H' : Heap),
            step (T, V, H) (T', V', H') ->
            tin[@Fin0] ≃ T ->
            tin[@Fin1] ≃ V ->
            tin[@Fin2] ≃ H ->
            (forall i : Fin.t 8, isRight tin[@Fin.R 3 i]) ->
            tout[@Fin0] ≃ T' /\
            tout[@Fin1] ≃ V' /\
            tout[@Fin2] ≃ H' /\
            (forall i : Fin.t 8, isRight tout[@Fin.R 3 i])
      ).


  Lemma Step_Realise : Step ⊨ Step_Rel.
  Admitted.


End StepMachine.