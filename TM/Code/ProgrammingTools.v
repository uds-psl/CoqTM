Require Export CodeTM Copy ChangeAlphabet WriteValue.
Require Export TMTac.
Require Export Basic.Mono.


(** This tactic automatically solves/instantiates hypothesises. *)

Ltac modpon_step H :=
  match type of H with
  | forall (x : ?X), ?P =>
    match type of X with
    | Prop => spec_assert H; simpl_surject;
          [ now eauto
          | TMSimp simpl_surject
          ]
    | _ => let x' := fresh "x" in
          evar (x' : X);
          specialize (H x');
          subst x'
    end
  end.

Ltac modpon H := repeat modpon_step H.



(** Machine Notations *)

Notation "pM @ ts" := (Inject pM ts) (at level 41, only parsing).
Notation "pM ⇑ R" := (ChangeAlphabet pM R) (at level 40, only parsing).