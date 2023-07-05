(** * Addendum for Vectors ([Vector.t]) *)
(* Author: Maxi Wuttke *)


Require Import Shared.Prelim Shared.Tactics.Tactics Shared.EqDec.
Require Import Coq.Vectors.Fin Coq.Vectors.Vector.
Require Import Shared.Vectors.FinNotation.
Require Export Shared.Vectors.Fin.


(* Vector.nth should not reduce with simpl, except the index is given with a constructor *)
Arguments Vector.nth {A} {m} (v') !p.
Arguments Vector.map {A B} f {n} !v /.
Arguments Vector.map2 {A B C} g {n} !v1 !v2 /.

Tactic Notation "dependent" "destruct" constr(V) :=
  match type of V with
  | Vector.t ?Z (S ?n) =>
    revert all except V;
    pattern V; revert n V;
    eapply caseS; intros
  | Vector.t ?Z 0 =>
    revert all except V;
    pattern V; revert V;
    eapply case0; intros
  | Fin.t 0 => inv V
  | Fin.t (S ?n) =>
    let pos := V in
    revert all except pos;
    pattern pos; revert n pos;
    eapply Fin.caseS; intros
  | _ => fail "Wrong type"
  end.

Delimit Scope vector_scope with vector.
Local Open Scope vector.

Notation "[||]" := (nil _) : vector_scope.
Notation "h ':::' t" := (cons _ h _ t) (at level 60, right associativity) : vector_scope.

Notation " [| x |] " := (x ::: [||]) : vector_scope.
Notation " [| x ; y ; .. ; z |] " := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..)) : vector_scope.
Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]") : vector_scope.


Ltac existT_eq :=
  match goal with
  | [ H: existT ?X1 ?Y1 ?Z1 = existT ?X2 ?Y2 ?Z2 |- _] =>
    apply EqdepFacts.eq_sigT_iff_eq_dep in H; inv H
  end.

Ltac existT_eq' :=
  match goal with
  | [ H: existT ?X1 ?Y1 ?Z1 = existT ?X2 ?Y2 ?Z2 |- _] =>
    apply EqdepFacts.eq_sigT_iff_eq_dep in H; induction H
  end.


Lemma vect_map_injective X Y n (f : X -> Y) (v1 v2 : Vector.t X n) :
  (forall x y, f x = f y -> x = y) ->
  map f v1 = map f v2 -> v1 = v2.
Proof.
  intros Inj Eq.
  induction n; cbn in *.
  - dependent destruct v1. dependent destruct v2; reflexivity.
  - dependent destruct v1. dependent destruct v2. cbn in *.
    eapply cons_inj in Eq as (-> % Inj &?). f_equal. now apply IHn.
Qed.



Lemma replace_nth X n (v : Vector.t X n) i (x : X) :
  (Vector.replace v i x) [@i] = x.
Proof.
  induction i; dependent destruct v; cbn; auto.
Qed.

Lemma replace_nth2 X n (v : Vector.t X n) i j (x : X) :
  i <> j -> (Vector.replace v i x) [@j] = v[@j].
Proof.
  revert v. pattern i, j. revert n i j.
  eapply Fin.rect2; intros; try congruence.
  - revert f H. pattern v. revert n v.
    eapply Vector.caseS. 
    cbn. reflexivity.
  - revert f H. pattern v. revert n v.
    eapply Vector.caseS. 
    cbn. reflexivity.
  - revert g f H H0. pattern v. revert n v.
    eapply Vector.caseS. firstorder congruence.
Qed.

Lemma destruct_vector_nil (X : Type) :
  forall v : Vector.t X 0, v = [||].
Proof.
  now apply case0.
Qed.

Lemma destruct_vector_cons (X : Type) (n : nat) :
  forall v : Vector.t X (S n), { h : X & { v' : Vector.t X n | v = h ::: v' }}.
Proof.
  revert n. apply caseS. eauto.
Qed.


Lemma In_nil (X : Type) (x : X) :
  ~ In x [||].
Proof. intros H. inv H. Qed.

Lemma In_cons (X : Type) (n : nat) (x y : X) (xs : Vector.t X n) :
  In y (x ::: xs) -> x = y \/ In y xs.
Proof.
  intros H. inv H; existT_eq'; tauto.
Qed.

Search Vector.map Vector.In.

Ltac destruct_vector_in :=
  match goal with
  | [ H: Vector.In _ [||] |- _ ] => now apply In_nil in H
  | [ H: Vector.In _ (_ ::: _) |- _ ] => apply In_cons in H as [-> | H] (* Try replacing it first *)
  | [ H: Vector.In _ (_ ::: _) |- _ ] => apply In_cons in H as [H | H]
  end.

(*
Goal ~ Vector.In 10 [|1;2;4|].
Proof.
  intros H. repeat destruct_vector_in; congruence.
Qed.
*)


Section In_Dec.
  Variable X : Type.
  Hypothesis X_dec : eq_dec X.

  Fixpoint in_dec (n : nat) (x : X) (xs : Vector.t X n) { struct xs } : bool :=
    match xs with
    | [||] => false
    | y ::: xs' => if Dec (x = y) then true else in_dec x xs'
    end.

  Lemma in_dec_correct (n : nat) (x : X) (xs : Vector.t X n) :
    in_dec x xs = true <-> In x xs.
  Proof.
    split; intros.
    {
      induction xs; cbn in *.
      - congruence.
      - decide (x = h) as [ -> | D].
        + constructor.
        + constructor. now apply IHxs.
    }
    {
      induction H; cbn.
      - have (x = x).
      - decide (x = x0).
        + reflexivity.
        + apply IHIn.
    }
  Qed.

  Global Instance In_dec (n : nat) (x : X) (xs : Vector.t X n) : dec (In x xs).
  Proof. eapply dec_transfer. eapply in_dec_correct. auto. Defined.

End In_Dec.

  

(* Destruct a vector of known size *)
Ltac destruct_vector :=
  repeat match goal with
         | [ v : Vector.t ?X 0 |- _ ] =>
           let H  := fresh "Hvect" in
           pose proof (@destruct_vector_nil X v) as H;
           subst v
         | [ v : Vector.t ?X (S ?n) |- _ ] =>
           let h  := fresh "h" in
           let v' := fresh "v'" in
           let H  := fresh "Hvect" in
           pose proof (@destruct_vector_cons X n v) as (h&v'&H);
           subst v; rename v' into v
         end.



Section In_nth.
  Variable (A : Type) (n : nat).

  Lemma vect_nth_In (v : Vector.t A n) (i : Fin.t n) (x : A) :
    Vector.nth v i = x -> Vector.In x v.
  Proof.
    induction n; cbn in *.
    - inv i.
    - dependent destruct v. dependent destruct i; cbn in *; subst; econstructor; eauto.
  Qed.

  Lemma vect_nth_In' (v : Vector.t A n) (x : A) :
    Vector.In x v -> exists i : Fin.t n, Vector.nth v i = x.
  Proof.
    induction n; cbn in *.
    - inversion 1.
    - dependent destruct v. destruct_vector_in.
      + exists Fin.F1. auto.
      + specialize (IHn0 _ H) as (i&<-). exists (Fin.FS i). auto.
  Qed.

End In_nth.



Section tabulate_vec.
  Variable X : Type.

  Fixpoint tabulate (n : nat) (f : Fin.t n -> X) {struct n} : Vector.t X n.
  Proof.
    destruct n.
    - apply Vector.nil.
    - apply Vector.cons.
      + apply f, Fin.F1.
      + apply tabulate. intros m. apply f, Fin.FS, m.
  Defined.

  Lemma nth_tabulate n (f : Fin.t n -> X) (m : Fin.t n) :
    Vector.nth (tabulate f) m = f m.
  Proof.
    induction m.
    - cbn. reflexivity.
    - cbn. rewrite IHm. reflexivity.
  Qed.

  Lemma in_tabulate n (f : Fin.t n -> X) (x : X) :
    In x (tabulate (n := n) f) <-> exists i : Fin.t n, x = f i.
  Proof.
    split.
    {
      revert f x. induction n; intros f x H.
      - cbn in *. inv H.
      - cbn in *. apply In_cons in H as [ <- | H ].
        + eauto.
        + specialize (IHn (fun m => f (Fin.FS m)) _ H) as (i&IH). eauto.
    }
    {
      intros (i&Hi). induction i; cbn in *; subst; econstructor; eauto.
    }
  Qed.

End tabulate_vec.

(*
Lemma vec_replace_nth X x n (t : Vector.t X n) (i : Fin.t n) :
  x = Vector.nth (Vector.replace t i x) i.
Proof.
  induction i; dependent destruct t; simpl; auto.
Qed.

Lemma vec_replace_nth_nochange X x n (t : Vector.t X n) (i j : Fin.t n) :
  Fin.to_nat i <> Fin.to_nat j -> Vector.nth t i = Vector.nth (Vector.replace t j x) i.
Proof.
  revert j. induction i; dependent destruct t; dependent destruct j; simpl; try tauto.
  apply IHi. contradict H. cbn. now rewrite !H.
Qed.
 *)


Instance Fin_eq_dec n : eq_dec (Fin.t n).
Proof.
  intros; hnf.
  destruct (Fin.eqb x y) eqn:E.
  - left. now eapply Fin.eqb_eq.
  - right. intros H. eapply Fin.eqb_eq in H. congruence.
Defined.


Lemma vect_in_map (X Y : Type) (n : nat) (f : X -> Y) (V : Vector.t X n) (x : X) :
  In x V -> In (f x) (map f V).
Proof. induction 1; cbn; constructor; auto. Qed.

Lemma vect_in_map_iff (X Y : Type) (n : nat) (f : X -> Y) (V : Vector.t X n) (y : Y) :
  In y (map f V) <-> (exists x : X, f x = y /\ In x V).
Proof.
  split.
  - intros H. induction V; cbn in *.
    + inv H.
    + apply In_cons in H as [ <- | H].
      * exists h. split; auto. now constructor 1.
      * specialize (IHV H) as (x&Hx1&Hx2). exists x. split; auto. now constructor 2.
  - intros (x&<-&H). now apply vect_in_map.
Qed.


Lemma In_replace (X : Type) (n : nat) (xs : Vector.t X n) (i : Fin.t n) (x y : X) :
  In y (replace xs i x) -> (x = y \/ In y xs).
Proof.
  revert i x y. induction xs; intros; cbn in *.
  - inv i.
  - dependent destruct i; cbn in *; apply In_cons in H as [-> | H]; auto; try now (right; constructor).
    specialize (IHxs _ _ _ H) as [-> | IH]; [ now left | right; now constructor ].
Qed.

Lemma In_replace' (X : Type) (n : nat) (xs : Vector.t X n) (i : Fin.t n) (x y : X) :
  In y (replace xs i x) -> x = y \/ exists j, i <> j /\ xs[@j] = y.
Proof.
  revert i x y. induction xs; intros; cbn -[nth] in *.
  - inv i.
  - dependent destruct i; cbn -[nth] in *.
    + apply In_cons in H as [->|H].
      * tauto.
      * apply vect_nth_In' in H as (j&H). right. exists (Fin.FS j). split. discriminate. cbn. assumption.
    + apply In_cons in H as [->|H].
      * right. exists Fin.F1. split. discriminate. cbn. reflexivity.
      * specialize (IHxs _ _ _ H) as [-> | (j&IH1&IH2)]; [ tauto | ].
        right. exists (Fin.FS j). split. now intros -> % Fin.FS_inj. cbn. assumption.
Qed.




(** Tactic for simplifying a hypothesis of the form [In x v] *)


Ltac simpl_vector_inv :=
  repeat match goal with
         | [ H : [||] = (_ ::: _) |- _ ] => now inv H
         | [ H : (_ ::: _) = [||]  |- _ ] => now inv H
         | [ H : Fin.F1 = Fin.FS _ |- _] => now inv H
         | [ H : Fin.FS _ = Fin.F1 |- _] => now inv H
         | [ H : Fin.FS _ = Fin.FS _ |- _] =>
           first
             [ apply Fin.FS_inj in H as ->
             | apply Fin.FS_inj in H as <-
             | apply Fin.FS_inj in H
             ]
         end.


Ltac simpl_vector_in :=
  repeat
    match goal with
    | _ => first
            [ progress destruct_vector_in
            | progress simpl_vector_inv
            | progress auto
            | congruence
            ]
    | [ H : Vector.In _ (Vector.map _ _) |- _] =>
      let x := fresh "x" in
      eapply vect_in_map_iff in H as (x&<-&H)
    | [ H : Vector.In _ (Vector.map _ _) |- _] =>
      let x := fresh "x" in
      let H' := fresh H in
      eapply vect_in_map_iff in H as (x&H&H')
    | [ H : Vector.In _ (tabulate _) |- _ ] =>
      let i := fresh "i" in
      apply in_tabulate in H as (i&->)
    | [ H : Vector.In _ (tabulate _) |- _ ] =>
      let i := fresh "i" in
      let H := fresh "H" in
      apply in_tabulate in H as (i&H)
    end.

Ltac vector_not_in :=
  let H := fresh "H" in
  intros H; simpl_vector_in.

Goal Vector.In (Fin.F1 (n := 10)) [|Fin1; Fin2; Fin3 |] -> False.
Proof. intros H. simpl_vector_in. Qed.
  
Goal Vector.In (Fin.F1 (n := 10)) (map (Fin.FS) [|Fin0; Fin1; Fin2|]) -> False.
Proof. intros H. simpl_vector_in. Qed.



(** Conversion between vectors and lists *)

Coercion Vector.to_list : Vector.t >-> list.

Lemma tolist_In (X : Type) (n : nat) (xs : Vector.t X n) (x : X) :
  Vector.In x xs <-> List.In x xs.
Proof.
  split; intros H.
  - induction H; cbn; auto.
  - induction xs; cbn in *; auto. destruct H as [-> | H]; econstructor; eauto.
Qed.
