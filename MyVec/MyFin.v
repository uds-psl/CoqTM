(* Require Import Shared.Base. *)
Require Import Lt Omega.
Ltac inv H := inversion H; subst; try clear H.


(* Idea: Make [t] opaque. *)

Fixpoint t (n : nat) : Type :=
  match n with
  | 0 => Empty_set
  | S n => unit + t n
  end.

Definition F1 {n:nat} : t (S n) := inl tt.
Definition FS {n:nat} : t n -> t (S n) := inr.

Lemma elim_O : (t 0) -> forall X : Type, X.
Proof. intros H X. exfalso. destruct H. Defined.

Lemma elim_S {n : nat} (x : t (S n)) : x = F1 \/ exists x', x = FS x'. 
Proof. unfold F1, FS. destruct x as [ [] | x']; eauto. Qed.


(** Tactical support *)

Tactic Notation "destruct_fin" ident(x) :=
  match type of x with
  | (t 0) => destruct x
  | (t (S ?n)) => destruct x as [ [] | x]
  end.

Tactic Notation "destruct_fin" ident(x) ident(E) :=
  match type of x with
  | (t 0) => destruct x eqn:E
  | (t (S ?n)) => let x' := fresh x in destruct x as [ [] | x'] eqn:E
  end.

Ltac destruct_fins :=
  repeat
    match goal with
    | [ x : t 0 |- _ ] => destruct_fin x
    | [ x : t (S ?n) |- _ ] => destruct_fin x
    end.

Goal forall (x : t 3), True.
  intros x. destruct_fins. all:tauto.
Abort.

(** [to_nat f = p] iff [f] is the p{^ th} element of [fin m]. *)
Fixpoint to_nat {n : nat} (x : t n) {struct n} : { i | i < n}.
Proof.
  destruct n; cbn in *.
  - now apply elim_O.
  - destruct x as [ [] | x].
    + exists 0. apply lt_0_Sn.
    + pose proof to_nat n x as (i&Hi). exists (S i). now apply lt_n_S.
Defined.

(** [of_nat p n] answers the p{^ th} element of [fin n] if p < n or a proof of p >= n else *)
Fixpoint of_nat (p n : nat) : (t n) + { exists m, p = n + m}.
Proof.
  destruct n as [ | n'].
  - right. exists p. reflexivity.
  - destruct p as [ | p'].
    + left. apply F1.
    + destruct (of_nat p' n') as [f | arg].
      * left. apply (FS f).
      * right. destruct arg as (m&->). exists m. cbn. reflexivity.
Qed.

(** [of_nat_lt p n H] answers the p{^ th} element of [fin n] it behaves much better than [of_nat p n] on open term *)
Fixpoint of_nat_lt {p n : nat} : p < n -> t n.
Proof.
  destruct n as [ | n']; intros H.
  - exfalso. apply (lt_n_O p H).
  - destruct p as [ | p'].
    + apply F1.
    + apply FS. apply (of_nat_lt p'). now apply lt_S_n.
Defined.

Lemma of_nat_ext {p}{n} (h h' : p < n) : of_nat_lt h = of_nat_lt h'.
Proof.
  revert p h h'. unfold of_nat_lt.
  induction n as [ | n']; cbn; intros.
  - exfalso. apply (lt_n_O p h).
  - destruct p as [ | p']; f_equal. erewrite IHn'; eauto. Unshelve. omega.
Qed.

Lemma of_nat_to_nat_inv {m} (p : t m) : of_nat_lt (proj2_sig (to_nat p)) = p.
Proof.
  revert p. induction m as [ | m']; intros; cbn in *.
  - destruct p.
  - destruct p as [ [] | p']; cbn; auto.
    destruct (to_nat p') eqn:E. cbn. unfold FS. f_equal. erewrite <- IHm'.
    rewrite E. cbn. apply of_nat_ext.
Qed.

Lemma to_nat_of_nat {p}{n} (h : p < n) : to_nat (of_nat_lt h) = exist _ p h.
Proof.
  revert p h. induction n as [ | n']; cbn; intros.
  - exfalso. apply (lt_n_O p h).
  - destruct (of_nat_lt h) as [[] | H] eqn:E; cbn.
    + unfold of_nat_lt in E. cbn in E. destruct p; cbn in *.
      * f_equal. apply Peano_dec.le_unique.
      * unfold FS in E. congruence.
    + destruct p; cbn in *.
      * destruct (to_nat H) eqn:E2. unfold F1 in E. inv E.
      * destruct (to_nat H) eqn:E2. unfold FS in E. inv E.
        specialize (IHn' _ (lt_S_n _ _ h)). rewrite IHn' in E2.
        inv E2. f_equal. apply Peano_dec.le_unique.
Qed.


(* Generate a [t] using a number *)
Ltac getFin n k := apply (of_nat_lt (ltac:(omega) : n < k)).

Goal True.
  Compute ltac:(getFin 1 10).
  Compute ltac:(getFin 5 10).
Abort.



Lemma to_nat_inj {n} (p q : t n) :
  proj1_sig (to_nat p) = proj1_sig (to_nat q) -> p = q.
Proof.
  induction n as [ | n']; cbn in *; intros.
  - destruct p.
  - destruct p as [() | p'], q as [() | q']; cbn in *; auto.
    + destruct (to_nat q'). cbn in H. omega.
    + destruct (to_nat p'). cbn in H. omega.
    + destruct (to_nat p') eqn:E1, (to_nat q') eqn:E2. cbn in H. inv H. f_equal.
      eapply IHn'. rewrite E1, E2. cbn. reflexivity.
Qed.

Lemma to_nat_1 {n:nat} : proj1_sig (to_nat (F1 (n := n))) = 0.
Proof. cbn. reflexivity. Qed.

Lemma to_nat_S {n:nat} (i:t n) :
  proj1_sig (to_nat (FS i)) = S (proj1_sig (to_nat i)).
Proof.
  destruct n; destruct_fin i E1; cbn; auto.
  destruct (to_nat i0); cbn in *. omega.
Qed.



(* Remove one [FS] and decrement the value. *)
Fixpoint pred' {n:nat} (i : t (S n)) {struct n} : t (S n).
Proof.
  destruct n as [ | n'] eqn:E1.
  - apply i.
  - destruct_fin i E2.
    + apply F1.
    + destruct_fin i0 E3.
      * apply F1.
      * apply FS. apply (pred' n' i0).
Defined.

Compute ltac:(getFin 2 3).
Compute pred' (ltac:(getFin 2 3)).
Compute pred' (ltac:(getFin 1 3)).
Compute pred' (ltac:(getFin 0 3)).

Definition pred {n:nat} (i : t n) : t n.
Proof.
  destruct n as [ | n'] eqn:E0.
  - destruct_fins.
  - apply (pred' i).
Defined.

Compute ltac:(getFin 2 3).
Compute pred (ltac:(getFin 2 3)).
Compute pred (ltac:(getFin 1 3)).
Compute pred (ltac:(getFin 0 3)).


(* Don't change the value. *)
Fixpoint coerceS {n:nat} (i:t n) {struct n}: t (S n).
Proof.
  destruct n as [ |n'] eqn:E.
  - apply F1.
  - destruct_fin i.
    + apply F1.
    + apply FS. apply coerceS, i.
Defined.

Compute (ltac:(getFin 2 3)).
Compute coerceS (ltac:(getFin 2 3)).

Compute (ltac:(getFin 1 3)).
Compute coerceS (ltac:(getFin 1 3)).

Compute (ltac:(getFin 0 3)).
Compute coerceS (ltac:(getFin 0 3)).


Compute proj1_sig (to_nat (ltac:(getFin 0 3))).
Compute proj1_sig (to_nat (coerceS (ltac:(getFin 0 3)))).

Compute proj1_sig (to_nat (ltac:(getFin 1 3))).
Compute proj1_sig (to_nat (coerceS (ltac:(getFin 1 3)))).

Compute proj1_sig (to_nat (ltac:(getFin 2 3))).
Compute proj1_sig (to_nat (coerceS (ltac:(getFin 2 3)))).

Lemma coerceS_correct {n:nat} (i:t n) :
  proj1_sig (to_nat (coerceS i)) = proj1_sig (to_nat i).
Proof.
  induction n as [ | n' IH]; destruct_fin i E1; try now (cbn; auto).
  specialize (IH i0). cbn [coerceS].
  replace (inr i0) with (FS i0) by reflexivity. rewrite !to_nat_S.
  rewrite IH. reflexivity.
Qed.


Fixpoint sub {n:nat} (i j : t n) {struct n} : t n.
Proof.
  destruct n; destruct_fin i E1; destruct_fin j E2.
  - apply F1.
  - apply F1.
  - apply i.
  - apply coerceS. apply sub. apply i0. apply j0.
Defined.

Compute (ltac:(getFin 2 3)).
Compute sub (ltac:(getFin 2 3)) (ltac:(getFin 0 3)).
Compute sub (ltac:(getFin 2 3)) (ltac:(getFin 1 3)).
Compute sub (ltac:(getFin 2 3)) (ltac:(getFin 2 3)).

Lemma sub_correct {n:nat} (i j : t n) :
  proj1_sig (to_nat (sub i j)) = proj1_sig (to_nat i) - proj1_sig (to_nat j).
Proof.
  revert i j. induction n as [ | n' IH]; intros; destruct_fin i E1; destruct_fin j E2; auto.
  - cbn [sub]. 
    (* TODO: This is somehow annoying! I don't want to fold every time *)
    (* Set Printing Implicit. *)
    fold (FS i0). replace (@inl unit (t n') tt) with (F1 (n := n')) by reflexivity.
    rewrite !to_nat_1, !to_nat_S. cbn. omega.
  - specialize (IH i0 j0). cbn [sub]. rewrite coerceS_correct.
    fold (FS i0). fold (FS j0). rewrite !to_nat_S. cbn. omega.
Qed.


Fixpoint full (n:nat) : t (S n).
Proof.
  destruct n as [ | n'].
  - apply F1.
  - apply FS. apply full.
Defined.

Compute full 10.
Compute proj1_sig (to_nat (full 0)).
Compute proj1_sig (to_nat (full 5)).
Compute proj1_sig (to_nat (full 10)).
Compute proj1_sig (to_nat (full 42)).


Lemma full_correct (n : nat) :
  proj1_sig (to_nat (full n)) = n.
Proof.
  induction n as [ | n' IH]; cbn in *; auto.
  destruct (full n') eqn:E1; cbn in *.
  - destruct u. cbn in *. omega.
  - destruct (to_nat t0) eqn:E2; cbn in *. omega.
Qed.


Definition inv {n : nat} (i : t (S n)) : t (S n) := sub (full n) i.

Compute (ltac:(getFin 2 3)).
Compute inv (ltac:(getFin 2 3)).
Compute inv (inv (ltac:(getFin 2 3))).

Compute (3 - (3 - 0)).
Compute (3 - (3 - 1)).
Compute (3 - (3 - 2)).
Compute (3 - (3 - 3)).
Compute (3 - (3 - 4)).

Lemma minus_inv (n m : nat) :
  m <= n -> n - (n - m) = m.
Proof. intros H. omega. (* Rock! *) Qed.

Lemma inv_correct' {n : nat} (i : t (S n)) :
  proj1_sig (to_nat (inv (inv i))) = proj1_sig (to_nat i).
Proof.
  unfold inv. rewrite !sub_correct, full_correct.
  apply minus_inv. destruct (to_nat i); cbn. omega.
Qed.

Lemma inv_correct {n : nat} (i : t (S n)) :
  inv (inv i) = i.
Proof. eapply to_nat_inj. apply inv_correct'. Qed.