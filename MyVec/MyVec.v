Require Import Shared.Base.
Require Import MyFin.
Require Import Recdef.

Section VecDef.

  Variable X : Type.

  Inductive Nil : Type :=
  | nil : Nil.

  Inductive Cons (X Y : Type) : Type :=
  |  cons : forall (x : X) (y : Y), Cons X Y.

  Fixpoint t (n : nat) : Type :=
    match n with
    | 0 => Nil
    | S n => Cons X (t n)
    end.

  (** The first element of a non-empty vector *)
  Definition head (X Y : Type) : Cons X Y -> X := fun '(cons x y) => x.
  
  (** Remove the first element of a non-empty vector *)
  Definition tail (X Y : Type) : Cons X Y -> Y := fun '(cons x y) => y.

  Lemma eta {n : nat} (xs : t (S n)) :
    cons (head xs) (tail xs) = xs.
  Proof. induction n as [ | n' IH]; intros; cbn in *; destruct xs; cbn in *; auto. Qed.
  
    
  (** Return the last element of a non-empyt vector *)
  Fixpoint last {n:nat} (xs : t (S n)) : X.
  Proof.
    destruct n; cbn in *.
    - apply (head xs).
    - apply (last n (tail xs)).
  Defined.

  (** Return the [n]-th element of the vector *)
  Fixpoint nth {n:nat} (xs : t n) (i : MyFin.t n) {struct n} : X.
  Proof.
    destruct n as [ | n']; destruct_fin i; cbn in *.
    - apply (head xs).
    - apply (nth n' (tail xs) i).
  Defined.

  Lemma eq_nth_iff (n : nat) (v1 v2 : t n) :
    (forall p1 p2 : MyFin.t n, p1 = p2 -> nth v1 p1 = nth v2 p2) <-> v1 = v2.
  Proof.
    split; [intros H | firstorder congruence].
    induction n; destruct v1, v2; auto.
    pose proof (H MyFin.F1 MyFin.F1 eq_refl) as L; cbn in L; subst. f_equal.
    eapply IHn. intros ? p ->. pose proof (H (MyFin.FS p) _ eq_refl) as L. assumption.
  Qed.
  

  (** Add an element to the right end of the vector *)
  Fixpoint put {n:nat} (xs:t n) (x:X) {struct n} : t (S n).
  Proof.
    destruct n as [ | n']; cbn in *.
    - apply (cons x nil).
    - apply (cons (head xs) (put _ (tail xs) x)).
  Defined.

  Fixpoint app {n m:nat} (xs:t n) (ys:t m) {struct n} : t (n+m).
  Proof.
    destruct n as [ | n']; cbn in *.
    - apply ys.
    - apply (cons (head xs) (app _ _ (tail xs) ys)).
  Defined.


  Fixpoint rev {n:nat} (xs:t n) {struct n} : t n.
  Proof.
    destruct n as [ | n']; cbn in *.
    - apply nil.
    - apply (put (rev _ (tail xs)) (head xs)).
  Defined.

  (* Problem: [rev (app xs ys)] and [app (rev ys) (rev xs)] don't have the same type! *)
  Definition rev_app {n m:nat} (xs:t n) (ys:t m) : t (m + n) :=
    app (rev ys) (rev xs).

  (* TODO: Can we somehow show, that [rev] is an involution? *)
  (* TODO: Read CPDDT/Equality *)


  (** Put [a] at the p{^th} place of [v] *)
  Fixpoint replace {n} (v : t n) (p : MyFin.t n) (a : X) {struct n} : t n.
  Proof.
    destruct n; destruct_fin p.
    - apply (cons a (tail v)).
    - apply (cons (head v) (replace _ (tail v) p a)).
  Defined.

  Lemma replace_nth x n (t : t n) (i : MyFin.t n) :
    x = nth (replace t i x) i.
  Proof.
    induction n; destruct_fin i; auto. destruct t. cbn. auto.
  Qed.

  Lemma replace_nth2 n (v : t n) i j (x : X) :
    i <> j -> nth (replace v i x) j = nth v j.
  Proof.
    revert v. induction n as [ | n' IH]; intros; destruct_fin i; destruct_fin j; cbn; try congruence; auto.
    eapply IH. intros ->. auto.
  Qed.
  
  (* Create a vector [f 0; f 1; ...; f (n-1)] *)
  Fixpoint tabulate (n : nat) (f : MyFin.t n -> X) {struct n} : t n.
  Proof.
    destruct n.
    - apply nil.
    - apply cons.
      + apply f, MyFin.F1.
      + apply tabulate. intros m. apply f, MyFin.FS, m.
  Defined.

  Lemma nth_tabulate n (f : MyFin.t n -> X) (m : MyFin.t n) :
    nth (tabulate f) m = f m.
  Proof.
    induction n as [ | n' IH]; destruct_fin m; cbn; auto. now rewrite IH.
  Qed.

  (*
  (* TODO: In als Type und als Prop definieren. *)
  Lemma in_tabulate n (f : Fin.t n -> X) (x : X) :
    In x (tabulate_vec (n := n) f) <-> exists i : Fin.t n, x = f i.
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
   *)

  (** Revert a vector *)

  Definition revert {n:nat} (xs : t n) : t n.
  Proof.
    destruct n.
    - apply nil.
    - apply (tabulate (fun i => nth xs (MyFin.inv i))).
  Defined.


  Lemma revert_involutive {n:nat} (xs : t n) :
    revert (revert xs) = xs.
  Proof.
    apply eq_nth_iff. intros ? p ->. destruct n; destruct_fin p.
    - cbn [revert]. rewrite !nth_tabulate. now rewrite MyFin.inv_correct.
    - cbn [revert]. rewrite !nth_tabulate. now rewrite MyFin.inv_correct.
  Qed.
    

End VecDef.

Module VectorNotations.
  Delimit Scope vector_scope with vector.
  Notation "[| |]" := nil (format "[| |]") : vector_scope.
  Notation "h ':::' t" := (cons h t) (at level 60, right associativity) : vector_scope.

  Notation "[| x |]" := (cons x nil) : vector_scope.
  Notation "[| x ; y ; .. ; z |]" := (cons x (cons y .. (cons z nil) ..)) : vector_scope.

  Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]") : vector_scope.
  Open Scope vector_scope.
End VectorNotations.


(* Doof ist nur noch, dass die Länge explizit annotiert werden muss. *)

(* Test *)

(*
Include VectorNotations.

Check [| |].
Check (cons 4 nil) : t nat 1.
Check 4 ::: [| |].


Check nil.
Compute [|1|].
Compute [|1;2|].
Compute [|1;2;3|].
Compute [|1;2;3;4|].
Compute ([|1;2;3;4|] : t _ 4).
Compute ([|1;2;3;4|] : t _ 4)[@MyFin.FS (MyFin.FS MyFin.F1)].

Compute put ([|1;2;3;4|] : t _ 4) 5.
Compute app ([|1;2;3;4|] : t _ 4) ([|5;6;7;8|] : t _ 4).
Compute rev ([|1;2;3;4|] : t _ 4).

Compute revert ([|4;8;15;16;23;42|] : t _ 6).
Compute revert ([|42;23;16;15;8;4|] : t _ 6).
*)