(** * Base Library for ICL

   - Version: 3 October 2016
   - Author: Gert Smolka, Saarland University
   - Acknowlegments: Sigurd Schneider, Dominik Kirst, Yannick Forster, Fabian Kunze, Maximilian Wuttke
 *)

Require Export Bool Omega List Setoid Morphisms Tactics.

Global Set Implicit Arguments. 
Global Unset Strict Implicit.
Global Unset Printing Records.
Global Unset Printing Implicit Defensive.
Global Set Regular Subst Tactic.

Hint Extern 4 => exact _.  (* makes auto use type class inference *)

(** De Morgan laws *)

Lemma DM_or (X Y : Prop) :
  ~ (X \/ Y) <-> ~ X /\ ~ Y.
Proof.
  tauto.
Qed.

Lemma DM_exists X (p : X -> Prop) :
  ~ (exists x, p x) <-> forall x, ~ p x.
Proof.
  firstorder.
Qed.

(** ** Boolean propositions and decisions *)

Coercion bool2Prop (b : bool) := if b then True else False.

Lemma bool_Prop_true b :
  b = true -> b.
Proof.
  intros A. rewrite A. exact I.
Qed.

Lemma bool_Prop_false b :
  b = false -> ~ b.
Proof.
  intros A. rewrite A. cbn. auto.
Qed.

Lemma bool_Prop_true' (b : bool) :
  b -> b = true.
Proof.
  intros A. cbv in A. destruct b; tauto.
Qed.

Lemma bool_Prop_false' (b : bool) :
  ~ b -> b = false.
Proof.
  intros A. cbv in A. destruct b; tauto.
Qed.


Hint Resolve bool_Prop_true bool_Prop_false.
Hint Resolve bool_Prop_true' bool_Prop_false'.


Definition bool2nat := fun b : bool => if b then 1 else 0.
Coercion bool2nat : bool >-> nat.
Definition nat2bool := fun n : nat => match n with 0 => false | _ => true end.
Coercion nat2bool : nat >-> bool.
Lemma bool_nat (b : bool) :
  1 = b -> b.
Proof. intros; cbv in *. destruct b. auto. congruence. Qed.
Lemma nat_bool (b : bool) :
  b = 1 -> b.
Proof. intros; cbv in *. destruct b. auto. congruence. Qed.
Hint Resolve bool_nat nat_bool.

Ltac simpl_coerce :=
  match goal with
  | [ H: False |- _ ] => destruct H
  | [ H: ~ bool2Prop true |- _ ] => destruct H
  | [ H: bool2Prop false |- _ ] => destruct H
  end.


Ltac simpl_congruence :=
  match goal with
  | [ H : 0 = S _ |- _] => congruence
  | [ H : S _ = 0 |- _] => congruence
  | [ H : S _ = 0 |- _] => congruence
  | [ H : true = false |- _] => congruence
  | [ H : false = true |- _] => congruence
  end.

Hint Extern 1 => simpl_coerce.
Hint Extern 1 => simpl_congruence.