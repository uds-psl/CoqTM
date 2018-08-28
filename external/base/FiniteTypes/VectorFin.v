Require Import Shared.FiniteTypes.FinTypes.
Require Import Shared.Vectors.Vectors.
Require Import Shared.Vectors.VectorDupfree.


Definition Fin_initVect (n : nat) : Vector.t (Fin.t n) n :=
  tabulate (fun i : Fin.t n => i).

Lemma Fin_initVect_dupfree n :
  dupfree (Fin_initVect n).
Proof.
  unfold Fin_initVect.
  apply dupfree_tabulate_injective.
  firstorder.
Qed.

Lemma Fin_initVect_full n k :
  Vector.In k (Fin_initVect n).
Proof.
  unfold Fin_initVect.
  apply in_tabulate. eauto.
Qed.

Definition Fin_initVect_nth (n : nat) (k : Fin.t n) :
  Vector.nth (Fin_initVect n) k = k.
Proof. unfold Fin_initVect. apply nth_tabulate. Qed.

Instance Fin_finTypeC n : finTypeC (EqType (Fin.t n)).
Proof.
  constructor 1 with (enum := Fin_initVect n).
  intros x. cbn in x.
  eapply dupfreeCount.
  - eapply tolist_dupfree. apply Fin_initVect_dupfree.
  - eapply tolist_In. apply Fin_initVect_full.
Qed.