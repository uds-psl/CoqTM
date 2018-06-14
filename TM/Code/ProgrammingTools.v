Require Export CodeTM Copy ChangeAlphabet WriteValue.
Require Export TMTac.
Require Export Basic.Mono.



(** This tactic applys [tape_contains_ext] *)

Local Ltac contains_ext' H :=
  apply (tape_contains_ext H);
  try solve [cbn; now rewrite !List.map_map] .
  
Ltac contains_ext :=
  lazymatch goal with
  | [ H : ?t[@?i] ≃    _ |- ?t[@?i]    ≃ _] => contains_ext' H
  | [ H : ?t[@?i] ≃(_) _ |- ?t[@?i]    ≃ _] => contains_ext' H
  | [ H : ?t[@?i] ≃    _ |- ?t[@?i] ≃(_) _] => contains_ext' H
  | [ H : ?t[@?i] ≃(_) _ |- ?t[@?i] ≃(_) _] => contains_ext' H
  end.


(** This tactic automatically solves/instantiates premises of a hypothesis. If the hypothesis is a conjunction, it is destructed. *)
Ltac modpon H :=
  simpl_surject;
  lazymatch type of H with
  | forall (i : Fin.t _), ?P => idtac
  | forall (x : ?X), ?P =>
    lazymatch type of X with
    | Prop =>
      tryif spec_assert H by
          (simpl_surject;
           solve [ eauto
                 | contains_ext
                 ]
          )
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



(** To get rid of all those uggly tape rewriting hypothesises. *)
Ltac clear_tape_eqs :=
  repeat match goal with
         | [ H: ?t'[@ ?x] = ?t[@ ?x] |- _ ] => clear H
         end.



(** Machine Notations *)

Notation "pM @ ts" := (Inject pM ts) (at level 41, only parsing).
Notation "pM ⇑ R" := (ChangeAlphabet pM R) (at level 40, only parsing).