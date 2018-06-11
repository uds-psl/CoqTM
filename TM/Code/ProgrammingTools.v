Require Export CodeTM Copy ChangeAlphabet WriteValue.
Require Export TMTac.
Require Export Basic.Mono.


(** This tactic automatically solves/instantiates hypothesises. *)



Ltac modpon H :=
  simpl_surject;
  lazymatch type of H with
  | forall (x : ?X), ?P =>
    lazymatch type of X with
    | Prop =>
      tryif spec_assert H by (simpl_surject; eauto)
      then idtac (* "solved premise of type" X *);
           modpon H
      else (spec_assert H;
            [ idtac (* "could not solve premise" X *) (* new goal for the user *)
            | modpon H (* continue after the user has proved the premise manually *)
            ]
           )
    | _ =>
      (* instantiate variable [x] with evar *)
      let x' := fresh "x" in
      evar (x' : X); specialize (H x'); subst x';
      modpon H
    end
  | ?X /\ ?Y =>
    let H' := fresh H in
    destruct H as [H H']; modpon H; modpon H'
  | _ => idtac
  end.



(** Machine Notations *)

Notation "pM @ ts" := (Inject pM ts) (at level 41, only parsing).
Notation "pM ⇑ R" := (ChangeAlphabet pM R) (at level 40, only parsing).