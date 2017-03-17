(** * Base Library for ICL

   - Version: 7 January 2017
   - Author: Gert Smolka, Saarland University
   - Acknowlegments: Sigurd Schneider, Dominik Kirst, Yannick Forster
 *)

Require Export Bool Omega List Setoid Morphisms.

Global Set Implicit Arguments. 
Global Unset Strict Implicit.
Global Unset Printing Records.
Global Unset Printing Implicit Defensive.
Global Set Warnings "-notation-overridden".

Export ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "x 'nel' A" := (~ x el A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).
Notation "| A |" := (length A) (at level 65).
Definition equi X (A B : list X) : Prop := incl A B /\ incl B A.
Notation "A === B" := (equi A B) (at level 70).
Hint Unfold equi.

Ltac inv H := inversion H; subst; try clear H.

Ltac contra XM A :=  (* proof by contradiction *)
  match goal with
  |[ |- ?t] => destruct (XM t) as [A|A]; [exact A|exfalso]
  end.

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

Hint Resolve bool_Prop_true bool_Prop_false.

Hint Extern 4 => 
match goal with
|[ H: False |- _ ] => destruct H
|[ H: ?s <> ?s |- _ ] => contradict H; reflexivity
|[ H: ~ bool2Prop true |- _ ] => destruct H
|[ H: bool2Prop false |- _ ] => destruct H
|[ H: true=false |- _ ] => discriminate H
|[ H: false=true |- _ ] => discriminate H
|[ H: ?b=false, H': bool2Prop(?b) |- _ ] => rewrite H in H'; destruct H'
|[ H: _ el nil |- _ ] => destruct H
end.

Definition dec (X: Prop) : Type := {X} + {~ X}.

Coercion dec2bool P (d: dec P) := if d then true else false.

Existing Class dec.

Definition Dec (X: Prop) (d: dec X) : dec X := d.
Arguments Dec X {d}.

Lemma Dec_reflect (X: Prop) (d: dec X) :
  Dec X <-> X.
Proof.
  destruct d as [A|A]; cbn; tauto.
Qed.

Notation Decb X := (dec2bool (Dec X)).

Lemma Dec_reflect_eq (X Y: Prop) (d: dec X) (e: dec Y) :
 Decb X = Decb Y <->  (X <-> Y).
Proof.
  destruct d as [D|D], e as [E|E]; cbn; intuition congruence.
Qed.

Lemma Dec_auto (X: Prop) (d: dec X) :
  X -> Dec X.
Proof.
  destruct d as [A|A]; cbn; tauto.
Qed.

Lemma Dec_auto_not (X: Prop) (d: dec X) :
  ~ X -> ~ Dec X.
Proof.
  destruct d as [A|A]; cbn; tauto.
Qed.

Hint Resolve Dec_auto Dec_auto_not.

Hint Extern 4 =>  (* Improves type class inference *)
match goal with
  | [  |- dec ((fun _ => _) _) ] => cbn
end : typeclass_instances.

Tactic Notation "decide" constr(p) := 
  destruct (Dec p).
Tactic Notation "decide" constr(p) "as" simple_intropattern(i) := 
  destruct (Dec p) as i.

(** Decided propositions behave classically *)

Ltac contra_dec A :=  (* proof by contradiction *)
  match goal with
  |[ |- ?t] => decide t as [A|A]; [exact A|exfalso]
  end.

Lemma dec_DN X : 
  dec X -> ~~ X -> X.
Proof. 
  unfold dec; tauto. 
Qed.

Lemma dec_DM_and X Y :  
  dec X -> dec Y -> ~ (X /\ Y) -> ~ X \/ ~ Y.
Proof. 
  unfold dec; tauto. 
Qed.

Lemma dec_DM_impl X Y :  
  dec X -> dec Y -> ~ (X -> Y) -> X /\ ~ Y.
Proof. 
  unfold dec; tauto. 
Qed.

(** Propagation rules for decisions *)

Fact dec_transfer P Q :
  P <-> Q -> dec P -> dec Q.
Proof.
  unfold dec. tauto.
Qed.

Instance bool_dec (b: bool) :
  dec b.
Proof. 
  unfold dec. destruct b; cbn; auto.
Defined.

Instance True_dec :
  dec True.
Proof. 
  unfold dec; tauto.
Defined.

Instance False_dec :
  dec False.
Proof. 
  unfold dec; tauto. 
Defined.

Instance impl_dec (X Y : Prop) :  
  dec X -> dec Y -> dec (X -> Y).
Proof. 
  unfold dec; tauto. 
Defined.

Instance and_dec (X Y : Prop) :  
  dec X -> dec Y -> dec (X /\ Y).
Proof. 
  unfold dec; tauto. 
Defined.

Instance or_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X \/ Y).
Proof. 
  unfold dec; tauto. 
Defined.

(* Coq standard modules make "not" and "iff" opaque for type class inference, 
   can be seen with Print HintDb typeclass_instances. *)

Instance not_dec (X : Prop) : 
  dec X -> dec (~ X).
Proof. 
  unfold not. auto.
Defined.

Instance iff_dec (X Y : Prop) : 
  dec X -> dec Y -> dec (X <-> Y).
Proof. 
  unfold iff. auto.
Defined.

(** ** Discrete types *)

Notation "'eq_dec' X" := (forall x y : X, dec (x=y)) (at level 70).

Structure eqType := EqType {
  eqType_X :> Type;
  eqType_dec : eq_dec eqType_X }.

Arguments EqType X {_} : rename.

Canonical Structure eqType_CS X (A: eq_dec X) := EqType X.

Existing Instance eqType_dec.

Instance bool_eq_dec : 
  eq_dec bool.
Proof.
  unfold dec. decide equality. 
Defined.

Instance nat_eq_dec : 
  eq_dec nat.
Proof.
  unfold dec. decide equality.
Defined.

Instance prod_eq_dec X Y :  
  eq_dec X -> eq_dec Y -> eq_dec (X * Y).
Proof.
  unfold dec. decide equality. 
Defined.

Instance list_eq_dec X :  
  eq_dec X -> eq_dec (list X).
Proof.
  unfold dec. decide equality. 
Defined.

(** ** Numbers **)

Instance nat_le_dec (x y : nat) : dec (x <= y) := 
  le_dec x y.

Lemma size_recursion (X : Type) (sigma : X -> nat) (p : X -> Type) :
  (forall x, (forall y, sigma y < sigma x -> p y) -> p x) -> 
  forall x, p x.
Proof.
  intros D x. apply D. revert x.
  enough (forall n y, sigma y < n -> p y) by eauto.
  intros n. induction n; intros y E. 
  - exfalso; omega.
  - apply D. intros x F.  apply IHn. omega.
Qed.

Arguments size_recursion {X} sigma {p} _ _.

Section Iteration.
  Variables (X: Type) (f: X -> X).

  Fixpoint it (n : nat) (x : X) : X := 
    match n with
      | 0 => x
      | S n' => f (it n' x)
    end.

  Lemma it_ind (p : X -> Prop) x n :
    p x -> (forall z, p z -> p (f z)) -> p (it n x).
  Proof.
    intros A B. induction n; cbn; auto.
  Qed.

  Definition FP (x : X) : Prop := f x = x.

  Lemma it_fp (sigma : X -> nat) x :
    (forall n, FP (it n x) \/ sigma (it n x) > sigma (it (S n) x)) ->
    FP (it (sigma x) x).
  Proof.
    intros A.
    assert (B: forall n, FP (it n x) \/ sigma x >= n + sigma (it n x)).
    { intros n; induction n; cbn.
      - auto. 
      - destruct IHn as [B|B].
        + left. now rewrite B. 
        + destruct (A n) as [C|C].
          * left. now rewrite C. 
          * right. cbn in C. omega. }
    destruct (A (sigma x)), (B (sigma x)); auto; exfalso; omega.
  Qed.
End Iteration.

(** ** Lists *)

(* Register additional simplification rules with autorewrite / simpl_list *)
(* Print Rewrite HintDb list. *)
Hint Rewrite <- app_assoc : list.
Hint Rewrite rev_app_distr map_app prod_length : list.

Lemma list_cycle  (X : Type) (A : list X) x :
  x::A <> A.
Proof.
  intros B.
  assert (C: |x::A| <> |A|) by (cbn; omega).
  apply C. now rewrite B.
Qed.

(** *** Decisions for lists *)

Instance list_in_dec X (x : X) (A : list X) :  
  eq_dec X -> dec (x el A).
Proof.
  intros D. apply in_dec. exact D.
Defined.

(* Certifying find *)

Lemma cfind X A (p: X -> Prop) (p_dec: forall x, dec (p x)) :
  {x | x el A /\ p x} + {forall x, x el A -> ~ p x}.
Proof.
  induction A as [|x A]; cbn.
  - tauto.
  - destruct IHA as [[y [D E]]|D].
    + eauto. 
    + decide (p x) as [E|E].
      * left. eauto.
      * right. intros y [[]|F]; auto. 
Qed.

Arguments cfind {X} A p {p_dec}.

Instance list_forall_dec X A (p : X -> Prop) :
  (forall x, dec (p x)) -> dec (forall x, x el A -> p x).
Proof.
  intros p_dec.
  destruct (cfind A (fun x => ~ p x)) as [[x [D E]]|D].
  - right. auto.
  - left. intros x E. apply dec_DN; auto.
Defined.

Instance list_exists_dec X A (p : X -> Prop) :
  (forall x, dec (p x)) -> dec (exists x, x el A /\ p x).
Proof.
  intros p_dec.
  destruct (cfind A p) as [[x [D E]]|D].
  - unfold dec. eauto.
  - right. intros [x [E F]]. exact (D x E F).
Defined.

Lemma list_exists_DM X A  (p : X -> Prop) : 
  (forall x, dec (p x)) ->
  ~ (forall x, x el A -> ~ p x) -> exists x, x el A /\ p x.
Proof. 
  intros D E. 
  destruct (cfind A p) as [F|F].
  + destruct F as [x F]. eauto.
  + contradiction (E F).
Qed.

Lemma list_exists_not_incl (X: eqType) (A B : list X) :
  ~ A <<= B -> exists x, x el A /\ ~ x el B.
Proof.
  intros E.
  apply list_exists_DM; auto.
  intros F. apply E. intros x G.
  apply dec_DN; auto.
Qed.

Lemma list_cc X (p : X -> Prop) A : 
  (forall x, dec (p x)) -> 
  (exists x, x el A /\ p x) -> {x | x el A /\ p x}.
Proof.
  intros D E. 
  destruct (cfind A p) as [[x [F G]]|F].
  - eauto.
  - exfalso. destruct E as [x [G H]]. apply (F x); auto.
Qed.

(** *** Membership

We use the following lemmas from Coq's standard library List.
- [in_eq :  x el x::A]
- [in_nil :  ~ x el nil]
- [in_cons :  x el A -> x el y::A]
- [in_or_app :  x el A \/ x el B -> x el A++B]
- [in_app_iff :  x el A++B <-> x el A \/ x el B]
- [in_map_iff :  y el map f A <-> exists x, f x = y /\ x el A]
*)

Hint Resolve in_eq in_nil in_cons in_or_app.

Section Membership.
  Variable X : Type.
  Implicit Types (x y: X) (A B: list X).

  Lemma in_sing x y :
    x el [y] -> x = y.
  Proof. 
    cbn. intros [[]|[]]. reflexivity. 
  Qed.

  Lemma in_cons_neq x y A :
    x el y::A -> x <> y -> x el A.
  Proof. 
    cbn. intros [[]|D] E; congruence. 
  Qed.

  Lemma not_in_cons x y A :
    ~ x el y :: A -> x <> y /\ ~ x el A.
  Proof.
    intuition; subst; auto.
  Qed.

(** *** Disjointness *)

  Definition disjoint A B :=
    ~ exists x, x el A /\ x el B.

  Lemma disjoint_forall A B :
    disjoint A B <-> forall x, x el A -> ~ x el B.
  Proof.
    split.
    - intros D x E F. apply D. exists x. auto.
    - intros D [x [E F]]. exact (D x E F).
  Qed.

  Lemma disjoint_symm A B :
    disjoint A B -> disjoint B A.
  Proof.
    firstorder.
  Qed.

  Lemma disjoint_incl A B B' :
    B' <<= B -> disjoint A B -> disjoint A B'.
  Proof.
    firstorder.
  Qed.

  Lemma disjoint_nil B :
    disjoint nil B.
  Proof.
    firstorder.
  Qed.

  Lemma disjoint_nil' A :
    disjoint A nil.
  Proof.
    firstorder.
  Qed.
  
  Lemma disjoint_cons x A B :
    disjoint (x::A) B <-> ~ x el B /\ disjoint A B.
  Proof.
    split.
    - intros D. split.
      + intros E. apply D. eauto.
      + intros [y [E F]]. apply D. eauto.
    - intros [D E] [y [[F|F] G]]. 
      + congruence.
      + apply E. eauto.
  Qed.

  Lemma disjoint_app A B C :
    disjoint (A ++ B) C <-> disjoint A C /\ disjoint B C.
  Proof.
    split.
    - intros D. split.
      + intros [x [E F]]. eauto 6.
      + intros [x [E F]]. eauto 6.
    - intros [D E] [x [F G]]. 
      apply in_app_iff in F as [F|F]; eauto.
  Qed.

End Membership.

Hint Resolve disjoint_nil disjoint_nil'.

(** *** Inclusion

We use the following lemmas from Coq's standard library List.
- [incl_refl :  A <<= A]
- [incl_tl :  A <<= B -> A <<= x::B]
- [incl_cons : x el B -> A <<= B -> x::A <<= B]
- [incl_appl : A <<= B -> A <<= B++C]
- [incl_appr : A <<= C -> A <<= B++C]
- [incl_app : A <<= C -> B <<= C -> A++B <<= C]
*)

Hint Resolve incl_refl incl_tl incl_cons incl_appl incl_appr incl_app.

Lemma incl_nil X (A : list X) :
  nil <<= A.

Proof. intros x []. Qed.

Hint Resolve incl_nil.

Lemma incl_map X Y A B (f : X -> Y) :
  A <<= B -> map f A <<= map f B.

Proof.
  intros D y E. apply in_map_iff in E as [x [E E']].
  subst y. apply in_map_iff. eauto.
Qed.

Section Inclusion.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma incl_nil_eq A :
    A <<= nil -> A=nil.

  Proof.
    intros D. destruct A as [|x A].
    - reflexivity.
    - exfalso. apply (D x). auto.
  Qed.

  Lemma incl_shift x A B :
    A <<= B -> x::A <<= x::B.

  Proof. auto. Qed.

  Lemma incl_lcons x A B :
    x::A <<= B <-> x el B /\ A <<= B.
  Proof. 
    split. 
    - intros D. split; hnf; auto.
    - intros [D E] z [F|F]; subst; auto.
  Qed.

  Lemma incl_sing x A y :
    x::A <<= [y] -> x = y /\ A <<= [y].
  Proof.
    rewrite incl_lcons. intros [D E].
    apply in_sing in D. auto.
  Qed.

  Lemma incl_rcons x A B :
    A <<= x::B -> ~ x el A -> A <<= B.

  Proof. intros C D y E. destruct (C y E) as [F|F]; congruence. Qed.

  Lemma incl_lrcons x A B :
    x::A <<= x::B -> ~ x el A -> A <<= B.

  Proof.
    intros C D y E.
    assert (F: y el x::B) by auto.
    destruct F as [F|F]; congruence.
  Qed.

  Lemma incl_app_left A B C :
    A ++ B <<= C -> A <<= C /\ B <<= C.
  Proof.
    firstorder.
  Qed.

End Inclusion.

Hint Resolve incl_nil_eq.

Definition inclp (X : Type) (A : list X) (p : X -> Prop) : Prop :=
  forall x, x el A -> p x.

(** *** Setoid rewriting with list inclusion and list equivalence *)

Instance incl_preorder X : 
  PreOrder (@incl X).
Proof. 
  constructor; hnf; unfold incl; auto. 
Qed.

Instance equi_Equivalence X : 
  Equivalence (@equi X).
Proof. 
  constructor; hnf; firstorder. 
Qed.

Instance incl_equi_proper X : 
  Proper (@equi X ==> @equi X ==> iff) (@incl X).
Proof. 
  hnf. intros A B D. hnf. firstorder. 
Qed.

Instance cons_incl_proper X x : 
  Proper (@incl X ==> @incl X) (@cons X x).
Proof.
  hnf. apply incl_shift.
Qed.

Instance cons_equi_proper X x : 
  Proper (@equi X ==> @equi X) (@cons X x).
Proof. 
  hnf. firstorder.
Qed.

Instance in_incl_proper X x : 
  Proper (@incl X ==> Basics.impl) (@In X x).
Proof.
  intros A B D. hnf. auto.
Qed.

Instance in_equi_proper X x : 
  Proper (@equi X ==> iff) (@In X x).
Proof. 
  intros A B D. firstorder. 
Qed.

Instance app_incl_proper X : 
  Proper (@incl X ==> @incl X ==> @incl X) (@app X).
Proof. 
  intros A B D A' B' E. auto.
Qed.

Instance app_equi_proper X : 
  Proper (@equi X ==> @equi X ==> @equi X) (@app X).
Proof. 
  hnf. intros A B D. hnf. intros A' B' E.
  destruct D, E; auto.
Qed.

Section Equi.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma equi_push x A :
    x el A -> A === x::A.
  Proof.
    auto.
  Qed.

  Lemma equi_dup x A :
    x::A === x::x::A.

  Proof.
    auto.
  Qed.

  Lemma equi_swap x y A:
    x::y::A === y::x::A.
  Proof.
    split; intros z; cbn; tauto.
  Qed.

  Lemma equi_shift x A B :
    x::A++B === A++x::B.
  Proof. 
    split; intros y.
    - intros [D|D].
      + subst; auto.
      + apply in_app_iff in D as [D|D]; auto.
    - intros D. apply in_app_iff in D as [D|D].
      + auto.
      + destruct D; subst; auto.
  Qed.

  Lemma equi_rotate x A :
    x::A === A++[x]. 
  Proof. 
    split; intros y; cbn.
    - intros [D|D]; subst; auto.
    - intros D. apply in_app_iff in D as [D|D].
      + auto.
      + apply in_sing in D. auto.
  Qed.
  
End Equi.

(** *** Filter *)

Section Filter.
  Variable X : Type.
  Implicit Types (x y: X) (A B C: list X) (p q: X -> bool).
  
  Fixpoint filter p A : list X :=
    match A with
    | nil => nil
    | x::A' => if p x then x :: filter p A' else filter p A'
    end.

  Lemma in_filter_iff x p A :
    x el filter p A <-> x el A /\ p x.
  Proof. 
    induction A as [|y A]; cbn.
    - tauto.
    - destruct (p y) eqn:E; cbn;
      rewrite IHA; intuition; subst; auto.
  Qed.

  Lemma filter_incl p A :
    filter p A <<= A.  
  Proof.
    intros x D. apply in_filter_iff in D. apply D.
  Qed.

  Lemma filter_mono p A B :
    A <<= B -> filter p A <<= filter p B.
  Proof.
    intros D x E. apply in_filter_iff in E as [E E'].
    apply in_filter_iff. auto.
  Qed.

  Lemma filter_id p A :
    (forall x, x el A -> p x) -> filter p A = A.
  Proof.
    intros D.
    induction A as [|x A]; cbn.
    - reflexivity.
    - destruct (p x) eqn:E.
      + f_equal; auto.
      + exfalso. apply bool_Prop_false in E. auto.
  Qed.

  Lemma filter_app p A B :
    filter p (A ++ B) = filter p A ++ filter p B.
  Proof.
    induction A as [|y A]; cbn.
    - reflexivity.
    - rewrite IHA. destruct (p y); reflexivity.  
  Qed.

  Lemma filter_fst p x A :
    p x -> filter p (x::A) = x::filter p A.
  Proof.
    cbn. destruct (p x); auto.
  Qed.

  Lemma filter_fst' p x A :
    ~ p x -> filter p (x::A) = filter p A.
  Proof.
    cbn. destruct (p x); auto.
  Qed.

  Lemma filter_pq_mono p q A :
    (forall x, x el A -> p x -> q x) -> filter p A <<= filter q A.
  Proof. 
    intros D x E. apply in_filter_iff in E as [E E'].
    apply in_filter_iff. auto.
  Qed.

  Lemma filter_pq_eq p q A :
    (forall x, x el A -> p x = q x) -> filter p A = filter q A.
  Proof. 
    intros C; induction A as [|x A]; cbn.
    - reflexivity.
    - destruct (p x) eqn:D, (q x) eqn:E.
      + f_equal. auto.
      + exfalso. enough (p x = q x) by congruence. auto.
      + exfalso. enough (p x = q x) by congruence. auto.
      + auto.
  Qed.

  Lemma filter_and p q A :
    filter p (filter q A) = filter (fun x => p x && q x) A.
  Proof.
    induction A as [|x A]; cbn. reflexivity.
    destruct (p x) eqn:E, (q x); cbn;
      try rewrite E; now rewrite IHA.
  Qed.

  Lemma filter_comm p q A :
    filter p (filter q A) = filter q (filter p A).
  Proof.
    rewrite !filter_and. apply filter_pq_eq.
    intros x _. now destruct (p x), (q x).
  Qed.
  
End Filter.

(** *** Element removal *)

Section Removal.
  Variable X : eqType.
  Implicit Types (x y: X) (A B: list X).

  Definition rem A x : list X :=
    filter (fun z => Dec (z <> x)) A.

  Lemma in_rem_iff x A y :
    x el rem A y <-> x el A /\ x <> y.
  Proof.
    unfold rem. rewrite in_filter_iff, Dec_reflect. tauto.
  Qed.

  Lemma rem_not_in x y A :
    x = y \/ ~ x el A -> ~ x el rem A y.
  Proof.
    unfold rem. rewrite in_filter_iff, Dec_reflect. tauto.
  Qed.

  Lemma rem_incl A x :
    rem A x <<= A.
  Proof.
    apply filter_incl.
  Qed.

  Lemma rem_mono A B x :
    A <<= B -> rem A x <<= rem B x.
  Proof.
    apply filter_mono.
  Qed.

  Lemma rem_cons A B x :
    A <<= B -> rem (x::A) x <<= B.
  Proof.
    intros E y F. apply E. apply in_rem_iff in F.
    destruct F as [[|]]; congruence.
  Qed.

  Lemma rem_cons' A B x y :
    x el B -> rem A y <<= B -> rem (x::A) y <<= B.
  Proof.
    intros E F u G. 
    apply in_rem_iff in G as [[[]|G] H]. exact E.
    apply F. apply in_rem_iff. auto.
  Qed.

  Lemma rem_in x y A :
    x el rem A y -> x el A.
  Proof.
    apply rem_incl.
  Qed.

  Lemma rem_neq x y A :
    x <> y -> x el A -> x el rem A y.
  Proof.
    intros E F. apply in_rem_iff. auto.
  Qed.

  Lemma rem_app x A B :
    x el A -> B <<= A ++ rem B x.
  Proof.
    intros E y F. decide (x=y) as [[]|]; auto using rem_neq.
  Qed.

  Lemma rem_app' x A B C :
    rem A x <<= C -> rem B x <<= C -> rem (A ++ B) x <<= C.
  Proof.
    unfold rem; rewrite filter_app; auto.
  Qed.

  Lemma rem_equi x A :
    x::A === x::rem A x.
  Proof.
    split; intros y; 
    intros [[]|E]; decide (x=y) as [[]|D]; 
    eauto using rem_in, rem_neq. 
  Qed.

  Lemma rem_comm A x y :
    rem (rem A x) y = rem (rem A y) x.
  Proof.
    apply filter_comm.
  Qed.

  Lemma rem_fst x A :
    rem (x::A) x = rem A x.
  Proof.
    unfold rem. rewrite filter_fst'; auto.
  Qed.

  Lemma rem_fst' x y A :
    x <> y -> rem (x::A) y = x::rem A y.
  Proof.
    intros E. unfold rem. rewrite filter_fst; auto.
  Qed.

  Lemma rem_id x A :
    ~ x el A -> rem A x = A.
  Proof.
    intros D. apply filter_id. intros y E.
    apply Dec_reflect. congruence.
  Qed.

  Lemma rem_reorder x A :
    x el A -> A === x :: rem A x.
  Proof.
    intros D. rewrite <- rem_equi. apply equi_push, D.
  Qed.

  Lemma rem_inclr A B x :
    A <<= B -> ~ x el A -> A <<= rem B x.
  Proof.
    intros D E y F. apply in_rem_iff.
    intuition; subst; auto. 
  Qed.

End Removal.

Hint Resolve rem_not_in rem_incl rem_mono rem_cons rem_cons' rem_app rem_app' rem_in rem_neq rem_inclr.

(** *** Cardinality *)

Section Cardinality.
  Variable X : eqType.
  Implicit Types A B : list X.

  Fixpoint card A :=
    match A with
      | nil => 0
      | x::A => if Dec (x el A) then card A else 1 + card A
    end.

  Lemma card_cons x A :
    x el A -> card (x::A) = card A.
  Proof.
    intros H. cbn. decide (x el A) as [H1|H1]; tauto.
  Qed.

  Lemma card_cons' x A :
    ~ x el A -> card (x::A) = 1 + card A.
  Proof.
    intros H. cbn. decide (x el A) as [H1|H1]; tauto.
  Qed.
  
  Lemma card_in_rem x A :
    x el A -> card A = 1 + card (rem A x).
  Proof.
    intros D. 
    induction A as [|y A].
    - contradiction D.
    - decide (y = x) as [->|H].
      + clear D. rewrite rem_fst.
        cbn. decide (x el A) as [H1|H1].
        * auto.
        * now rewrite (rem_id H1).
      + assert (x el A) as H1 by (destruct D; tauto). clear D.
        rewrite (rem_fst' _ H). specialize (IHA H1).
        simpl card at 2. 
        decide (y el rem A x) as [H2|H2].
        * rewrite card_cons. exact IHA.
          apply in_rem_iff in H2. intuition.
        * rewrite card_cons'. now rewrite IHA.
          contradict H2.  now apply in_rem_iff.
  Qed.
  
  Lemma card_not_in_rem A x :
    ~ x el A -> card A = card (rem A x).
  Proof.
    intros D; rewrite rem_id; auto.
  Qed.

  Lemma card_le A B :
    A <<= B -> card A <= card B.
  Proof.
  revert B. 
  induction A as [|x A]; intros B D; cbn.
  - omega.
  - apply incl_lcons in D as [D D1].
    decide (x el A) as [E|E].
    + auto.
    + rewrite (card_in_rem D).
      enough (card A <= card (rem B x)) by omega.
      apply IHA. auto.
  Qed.

  Lemma card_eq A B :
    A === B -> card A = card B.
  Proof.
    intros [E F]. apply card_le in E. apply card_le in F. omega.
  Qed.

  Lemma card_cons_rem x A :
    card (x::A) = 1 + card (rem A x).
  Proof.
    rewrite (card_eq (rem_equi x A)). cbn.
    decide (x el rem A x) as [D|D].
    - exfalso. apply in_rem_iff in D; tauto.
    - reflexivity.
  Qed.

  Lemma card_0 A :
    card A = 0 -> A = nil.
  Proof.
    destruct A as [|x A]; intros D.
    - reflexivity.
    - exfalso. rewrite card_cons_rem in D. omega.
  Qed.

  Lemma card_ex A B :
    card A < card B -> exists x, x el B /\ ~ x el A.
  Proof.
    intros D.
    decide (B <<= A) as [E|E].
    - exfalso. apply card_le in E. omega.
    - apply list_exists_not_incl; auto.
  Qed.

  Lemma card_equi A B :
    A <<= B -> card A = card B -> A === B.
  Proof.
    revert B. 
    induction A as [|x A]; cbn; intros B D E.
    - symmetry in E. apply card_0 in E. now rewrite E.
    - apply incl_lcons in D as [D D1].
      decide (x el A) as [F|F].
      + rewrite (IHA B); auto.
      + rewrite (IHA (rem B x)).
        * symmetry. apply rem_reorder, D.
        * auto.
        * apply card_in_rem in D. omega.
  Qed.

  Lemma card_lt A B x :
    A <<= B -> x el B -> ~ x el A -> card A < card B.
  Proof.
    intros D E F.
    decide (card A = card B) as [G|G].
    + exfalso. apply F. apply (card_equi D); auto.
    + apply card_le in D. omega.
  Qed.

  Lemma card_or A B :
    A <<= B -> A === B \/ card A < card B.
  Proof.
    intros D.
    decide (card A = card B) as [F|F].
    - left. apply card_equi; auto.
    - right. apply card_le in D. omega.
  Qed.

End Cardinality.

Instance card_equi_proper (X: eqType) : 
  Proper (@equi X ==> eq) (@card X).
Proof. 
  hnf. apply card_eq.
Qed.

(** *** Duplicate-free lists *)

Inductive dupfree (X : Type) : list X -> Prop :=
| dupfreeN : dupfree nil
| dupfreeC x A : ~ x el A -> dupfree A -> dupfree (x::A).

Section Dupfree.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma dupfree_cons x A :
    dupfree (x::A) <-> ~ x el A /\ dupfree A.
  Proof. 
    split; intros D.
    - inv D; auto.
    - apply dupfreeC; tauto.
  Qed.

  Lemma dupfree_app A B :
    disjoint A B -> dupfree A -> dupfree B -> dupfree (A++B).
  Proof.
    intros D E F. induction E as [|x A E' E]; cbn.
    - exact F.
    - apply disjoint_cons in D as [D D'].
      constructor; [|exact (IHE D')].
      intros G. apply in_app_iff in G; tauto.
  Qed.

  Lemma dupfree_map Y A (f : X -> Y) :
    (forall x y, x el A -> y el A -> f x = f y -> x=y) -> 
    dupfree A -> dupfree (map f A).
  Proof.
    intros D E. induction E as [|x A E' E]; cbn.
    - constructor.
    - constructor; [|now auto].
      intros F. apply in_map_iff in F as [y [F F']].
      rewrite (D y x) in F'; auto.
  Qed.

  Lemma dupfree_filter p A :
    dupfree A -> dupfree (filter p A).
  Proof.
    intros D. induction D as [|x A C D]; cbn.
    - left.
    - destruct (p x) eqn:E; [|exact IHD].
      right; [|exact IHD].
      rewrite in_filter_iff, E. intuition.
   Qed.

End Dupfree.

Section Undup.
  Variable X : eqType.
  Implicit Types A B : list X.

  Lemma dupfree_dec A :
    dec (dupfree A).
  Proof.
    induction A as [|x A].
    - left. left.
    - decide (x el A) as [E|E].
      + right. intros F. inv F; tauto.
      + destruct (IHA) as [F|F].
        * unfold dec. auto using dupfree.
        * right. intros G. inv G; tauto.
  Qed.

  Lemma dupfree_card A :
    dupfree A -> card A = |A|.
  Proof.
    induction 1 as [|x A D _ IH]; cbn.
    - reflexivity.
    - decide (x el A) as [G|].
      + exfalso; auto.
      + omega.
  Qed.

  Fixpoint undup (A : list X) : list X :=
    match A with
      | nil => nil
      | x::A' => if Dec (x el A') then undup A' else  x :: undup A'
    end.

  Lemma undup_id_equi A :
    undup A === A.
  Proof.
    induction A as [|x A]; cbn.
    - reflexivity.
    - decide (x el A) as [E|E]; rewrite IHA; auto.
  Qed.

  Lemma dupfree_undup A :
    dupfree (undup A).
  Proof.
    induction A as [|x A]; cbn.
    - left.
    - decide (x el A) as [E|E]; auto.
      right; auto. now rewrite undup_id_equi. 
  Qed.

  Lemma undup_incl A B :
    A <<= B <-> undup A <<= undup B.
  Proof.
    now rewrite !undup_id_equi.
  Qed.

  Lemma undup_equi A B :
    A === B <-> undup A === undup B.
  Proof.
    now rewrite !undup_id_equi.
  Qed.

  Lemma undup_id A :
    dupfree A -> undup A = A.
  Proof.
    intros E. induction E as [|x A E F]; cbn.
    - reflexivity.
    - rewrite IHF. decide (x el A) as [G|G]; tauto.
  Qed.

  Lemma undup_idempotent A :
    undup (undup A) = undup A.

  Proof. apply undup_id, dupfree_undup. Qed.

End Undup.

(** *** Power lists *)

Section Power.
  Variable X : Type.

  Fixpoint power (U: list X ) : list (list X) :=
    match U with
    | nil => [nil]
    | x :: U' => power U' ++ map (cons x) (power U')
    end.
  
  Lemma power_incl A U :
    A el power U -> A <<= U.
  Proof.
    revert A; induction U as [|x U]; cbn; intros A D.
    - destruct D as [[]|[]]; auto.
    - apply in_app_iff in D as [E|E]. now auto.
      apply in_map_iff in E as [A' [E F]]. subst A.
      auto.
  Qed.

  Lemma power_nil U :
    nil el power U.
  Proof.
    induction U; cbn; auto.
  Qed.

End Power.

Section PowerRep.
  Variable X : eqType.
  Implicit Types A U : list X.

  Definition rep (A U : list X) : list X :=
    filter (fun x => Dec (x el A)) U.

  Lemma rep_cons A x U :
    x el A -> rep A (x::U) = x :: rep A U.
  Proof.
    intros H. apply filter_fst. auto.
  Qed.

  Lemma rep_cons' A x U :
    ~ x el A -> rep A (x::U) = rep A U.
  Proof.
    intros H. apply filter_fst'. auto.
  Qed.

  Lemma rep_cons_eq x A U :
    ~ x el U -> rep (x::A) U = rep A U.
  Proof.
    intros D. apply filter_pq_eq. intros y E.
    apply Dec_reflect_eq. split.
    - intros [<-|F]; tauto.
    - auto.
  Qed.

  Lemma rep_power A U :
    rep A U el power U.
  Proof.
    revert A; induction U as [|x U]; intros A.
    - cbn; auto.
    - decide (x el A) as [H|H].
      + rewrite (rep_cons _ H). cbn. auto using in_map.
      + rewrite (rep_cons' _ H). cbn. auto.
  Qed.

  Lemma rep_incl A U :
    rep A U <<= A.
  Proof.
    intros x. unfold rep. rewrite in_filter_iff, Dec_reflect.
    intuition.
  Qed.

  Lemma rep_in x A U :
    A <<= U -> x el A -> x el rep A U.
  Proof.
    intros D E. apply in_filter_iff; auto.
  Qed.

  Lemma rep_equi A U :
    A <<= U -> rep A U === A.
  Proof.
    intros D. split. now apply rep_incl.
    intros x. apply rep_in, D.
  Qed.

  Lemma rep_mono A B U :
    A <<= B -> rep A U <<= rep B U.
  Proof.
    intros D. apply filter_pq_mono.
    intros E; rewrite !Dec_reflect; auto.
  Qed.

  Lemma rep_eq' A B U :
    (forall x, x el U -> (x el A <-> x el B)) -> rep A U = rep B U.
  Proof.
    intros D. apply filter_pq_eq. intros x E.
    apply Dec_reflect_eq. auto.
  Qed.

  Lemma rep_eq A B U :
    A === B -> rep A U = rep B U.
  Proof.
    intros D. apply filter_pq_eq. intros x E.
    apply Dec_reflect_eq. firstorder.
  Qed.

  Lemma rep_injective A B U :
    A <<= U -> B <<= U -> rep A U = rep B U -> A === B.
  Proof.
    intros D E F. transitivity (rep A U). 
    - symmetry. apply rep_equi, D.
    - rewrite F. apply rep_equi, E.
  Qed.

  Lemma rep_idempotent A U :
    rep (rep A U) U = rep A U.
  Proof. 
    unfold rep at 1 3. apply filter_pq_eq.
    intros x D. apply Dec_reflect_eq. split.
    + apply rep_incl.
    + intros E. apply in_filter_iff. auto.
  Qed.
    
  Lemma dupfree_power U :
    dupfree U -> dupfree (power U).
  Proof.
    intros D. induction D as [|x U E D]; cbn.
    - constructor. now auto. constructor.
    - apply dupfree_app.
      + intros [A [F G]]. apply in_map_iff in G as [A' [G G']].
        subst A. apply E. apply (power_incl F). auto.
      + exact IHD.
      + apply dupfree_map; congruence.
  Qed.

  Lemma dupfree_in_power U A :
    A el power U -> dupfree U -> dupfree A.
  Proof.
    intros E D. revert A E.
    induction D as [|x U D D']; cbn; intros A E.
    - destruct E as [[]|[]]. constructor.
    - apply in_app_iff in E as [E|E].
      + auto.
      + apply in_map_iff in E as [A' [E E']]. subst A.
        constructor.
        * intros F; apply D. apply (power_incl E'), F.
        * auto.
  Qed.

  Lemma rep_dupfree A U :
    dupfree U -> A el power U -> rep A U = A.
  Proof.
    intros D; revert A. 
    induction D as [|x U E F]; intros A G.
    - destruct G as [[]|[]]; reflexivity.
    - cbn in G. apply in_app_iff in G as [G|G]. 
      + rewrite rep_cons'. now auto.
        contradict E. apply (power_incl G), E.
      + apply in_map_iff in G as [A' [<- H]].
        specialize (IHF _ H).
        rewrite rep_cons. Focus 2. now auto.
        rewrite rep_cons_eq. now rewrite IHF. exact E.
   Qed.

  Lemma power_extensional A B U :
    dupfree U -> A el power U -> B el power U -> A === B -> A = B.
  Proof.
    intros D E F G. 
    rewrite <- (rep_dupfree D E). rewrite <- (rep_dupfree D F).
    apply rep_eq, G.
  Qed.

End PowerRep.

(** ** Finite inductive predicates *)

Section Fip.
  Variables (X: eqType) (sigma: list X -> X -> bool) (R: list X).
  
  Inductive fip : X -> Prop :=
  | fip_intro A x : (forall x, x el A -> fip x) -> sigma A x -> x el R -> fip x.

  Definition fip_monotone := forall A B x, A <<= B -> sigma A x -> sigma B x.
  Definition fip_closed A := forall x, x el R -> sigma A x -> x el A.

  Lemma fip_least A x :
    fip_monotone -> fip_closed A -> fip x -> x el A.
  Proof.
    intros C D. induction 1 as [B x _ IH F G].
    apply (D _ G). revert F. apply C. exact IH.
  Qed.

  Fixpoint fip_it n A : list X :=
    match n, cfind R (fun x => ~ x el A /\ sigma A x)  with
    | S n', inleft (exist _ x _) => fip_it n' (x::A)
    | _, _ =>  A
    end.
 
  Lemma fip_it_sound n A :
    inclp A fip -> inclp (fip_it n A) fip.
  Proof.
    revert A; induction n as [|n IH]; cbn; intros A H.
    - exact H.
    - destruct (cfind R _) as [(y&H2)|_].
      + apply IH. intros z [<-|H3].
        * apply fip_intro with (A:= A); intuition.
        * apply H, H3.
      + apply H.
  Qed.

  Lemma fip_it_closed n A :
    A <<= R -> card R <= n + card A -> fip_closed (fip_it n A).
  Proof.
    revert A. induction n as [|n IH]; cbn; intros A H H1.
    - enough (A === R) as (H2&H3) by (hnf; auto).
      apply card_or in H as [H|H]. exact H. omega.
    - destruct (cfind R _) as [(y&H2)|H2].
      + apply (IH (y::A)). now intuition.
        rewrite card_cons'. omega. intuition.
       + intros x H3 H4. apply dec_DN. now auto.
        specialize (H2 _ H3). now contradict H2.
  Qed.

  Theorem fip_dec x :
    fip_monotone -> dec (fip x).
  Proof.
    intros D.
    apply dec_transfer with (P:= x el fip_it (card R) nil).
    Focus 2. now auto.
    split.
    - revert x. apply fip_it_sound. hnf. auto.
    - apply (fip_least D). apply fip_it_closed. now auto. omega.
  Qed.

End Fip.

(** ** Finite closure iteration *)

Module FCI.
Section FCI.
  Variables (X: eqType) (sigma: list X -> X -> bool) (R: list X).

  Lemma pick (A : list X) :
    { x | x el R /\ sigma A x /\ ~ x el A } + { forall x, x el R -> sigma A x -> x el A }.
  Proof.
    destruct (cfind R (fun x => sigma A x /\ ~ x el A)) as [E|E].
    - auto.
    - right. intros x F G.
      decide (x el A). assumption. exfalso.
      eapply E; eauto.
  Qed.

  Definition F (A : list X) : list X.
    destruct (pick A) as [[x _]|_].
    - exact (x::A).
    - exact A.
  Defined.

  Definition C := it F (card R) nil.
  
  Lemma it_incl n : 
    it F n nil <<= R.
  Proof.
    apply it_ind. now auto.
    intros A E. unfold F. 
    destruct (pick A) as [[x G]|G]; intuition.
  Qed.
  
  Lemma incl :
    C <<= R.
  Proof.
    apply it_incl.
  Qed.

  Lemma ind p :
    (forall A x, inclp A p -> x el R -> sigma A x -> p x) -> inclp C p.
  Proof.
    intros B. unfold C. apply it_ind.
    + intros x [].
    + intros D G x. unfold F.
      destruct (pick D) as [[y E]|E].
      * intros [[]|]; intuition; eauto.
      * intuition.
  Qed.

  Lemma fp : 
    F C = C.
  Proof.
    pose (size (A : list X) := card R - card A).
    replace C with (it F (size nil) nil).
    - apply it_fp. intros n. cbn. 
      set (J:= it F n nil). unfold FP, F.
      destruct (pick J) as [[x B]|B].
      + right.
        assert (G: card J < card (x :: J)).
        { apply card_lt with (x:=x); intuition. }
        assert (H: card (x :: J) <= card R).
        { apply card_le, incl_cons. apply B. apply it_incl. }
        unfold size. omega.
      + auto.
    - unfold C, size. f_equal. change (card nil) with 0. omega.
  Qed.
  
  Lemma closure x :
    x el R -> sigma C x -> x el C.
  Proof.
    assert (A2:= fp).
    unfold F in A2.
    destruct (pick C) as [[y C]| B].
    + contradiction (list_cycle A2). 
    + apply B.
  Qed.

  Theorem fip_dec x :  (* Proof using FCI *)
    fip_monotone sigma -> dec (fip sigma R x).
  Proof.
    intros D.
    apply dec_transfer with (P:= x el C). Focus 2. now auto.
    split.
    - revert x. apply FCI.ind. intros A x IH E F.
      apply fip_intro with (A:=A); auto.
    - apply (fip_least D). intros z. apply FCI.closure.
  Qed.

End FCI.
End FCI.

(* Print Graph. (* prints transitive closure of coercions *) *)

