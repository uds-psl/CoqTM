Require Import Prelim TM.TM.
Require Import TM.LiftMN.

Ltac dec_pos P := let H := fresh in destruct (Dec P) as [_ | H]; [ | now contradiction H].
Ltac dec_neg P := let H := fresh in destruct (Dec P) as [H | _]; [now contradiction H | ].

Ltac simpl_dec :=
  match goal with
  | [ H : context [ Dec (?x = ?x) ] |- _ ] => dec_pos (x=x)
  | [ |- context [ Dec (?x = ?x) ]] => dec_pos (x=x)
  | [ _ : ?H |- context [ Dec ?H ]] => dec_pos H
  | [ _ : ~ ?H |- context [ Dec ?H ]] => dec_neg H
  | [ _ : ?H, _ : context [ Dec ?H ] |- _] => dec_pos H
  | [ _ : ~ ?H, _ : context [ Dec ?H ] |- _] => dec_neg H
  | _ => fail "could not match goal"
  end.

Section test.
  Variable P : Prop.
  Variable dec_P : dec P.
  Goal if Dec (1 = 1) then True else False.
  Proof.
    intros. deq 1. tauto.
  Qed.
  Goal P -> if (Dec P) then True else False.
  Proof.
    intros. simpl_dec. tauto.
  Qed.
  Goal ~ P -> if (Dec P) then False else True.
  Proof.
    intros. simpl_dec. tauto.
  Qed.
  Goal P -> (if (Dec P) then False else True) -> False.
  Proof.
    intros. simpl_dec. tauto.
  Qed.
  Goal ~ P -> (if (Dec P) then True else False) -> False.
  Proof.
    intros. simpl_dec. tauto.
  Qed.
End test.

Ltac inv_pair :=
  match goal with
  | [ H : (_, _) = (_, _) |- _] => inv H
  | [ |- (_, _) = (_, _) ] => f_equal
  end.


Lemma simpl_not_in_helper1 :
  not_indices (n := 2) [|Fin.F1|] (Fin.FS Fin.F1).
Proof. vector_not_in. Qed.

Lemma simpl_not_in_helper2 :
  not_indices (n := 2) [|Fin.FS Fin.F1|] (Fin.F1).
Proof. vector_not_in. Qed.

  
Ltac simpl_not_in :=
  match goal with
  | [ H1: forall i : Fin.t 2, not_indices [|Fin.F1|] i -> _ |- _] =>
    specialize (H1 (Fin.FS Fin.F1) simpl_not_in_helper1)
  | [ H1: forall i : Fin.t 2, not_indices [|Fin.FS Fin.F1|] i -> _ |- _] =>
    specialize (H1 Fin.F1 simpl_not_in_helper2)
  end.


(* Simplifies the goal without making any decissions *)
Tactic Notation "TMSimp" tactic(T) :=
  repeat progress
         (
           hnf in *;
           cbn -[Vector.nth] in *;
           intros;
           subst;
           destruct_tapes;
           try T;
           match goal with
           | [ H : _ ::: _ = [||]  |- _ ] => inv H
           | [ H : [||] = _ ::: _ |- _ ] => inv H
           | [ H : _ ::: _ = _ ::: _ |- _ ] => inv H
           | [ |- (_ ::: _) = (_ ::: _) ] => f_equal

           | [ H : _ ::  _ = []  |- _ ] => inv H
           | [ H : [] = _ :: _ |- _ ] => inv H
           | [ H : _ ::  _ = _ :: _ |- _ ] => inv H


           | [ H : Some _ = Some _ |- _ ] => inv H
           | [ H : None   = Some _ |- _ ] => inv H
           | [ H : Some _ = None   |- _ ] => inv H
           | [ |- Some _ = Some _ ] => f_equal

           | [ H : _ /\ _ |- _] => destruct H
           | [ H : ex ?P |- _] => destruct H
           | [ x : _ * _    |- _ ] => destruct x

           | [ H1: ?X = _, H2: context [ ?X ] |- _ ] => rewrite H1 in H2
           | [ H1: ?X = _    |- context [ ?X ]     ] => rewrite H1

           | _ => idtac
           end
         ).

Tactic Notation "TMBranche" :=
  (
    match goal with
    | [ H : context [ match ?x with _ => _ end ] |- _ ] => let E := fresh "E" in destruct x eqn:E
    | [   |- context [ match ?x with _ => _ end ]     ] => let E := fresh "E" in destruct x eqn:E
    | [ H : _ \/ _ |- _] => destruct H
    | [ IH : ?P -> ?Q |- _] =>
      match type of P with
      | Prop => spec_assert IH; [ clear IH | ]
      end

    | [ x : bool        |- _ ] => destruct x
    | [ x : option _ |- _ ] => destruct x

    | [   |- ex ?P    ] => eexists
    | [ H : _ \/ _ |- _] => destruct H
    end
  ).

Tactic Notation "TMSimp" := TMSimp idtac.

Tactic Notation "TMSolve" int_or_var(k) :=
  repeat progress first [
           match goal with
           | [ |- _ /\ _ ] => split
           end
           || congruence
           || eauto k
         ].

Tactic Notation "TMCrush" tactic(T) :=
  repeat progress
         (
           TMSimp T;
           try TMBranche
         ).

Tactic Notation "TMCrush" := TMCrush idtac.