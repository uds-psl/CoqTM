(** * Proofs and definitions obtained from external sources

This file contains proofs and definitions from external sources. Specifically from thr base library used in IC
by Prof. Gert Smolka in the version from 15. February 2016. Some other definitions are taken from the preliminary file of then
development of Heriditarily finite sets by Prof. Gert Smolka and Kathrin Stark. Mainly these are newer versions of the definitions from the base library from ICL.
 *)


Global Set Implicit Arguments. 
Global Unset Strict Implicit.
Global Unset Printing Records.
Global Unset Printing Implicit Defensive.
Global Set Regular Subst Tactic.
Hint Extern 4 => exact _.  (* make auto use type class inference *)
Require Export Setoid Morphisms.
Require Export Omega List Morphisms.

Set Implicit Arguments.
(* Set Universe Polymorphism. *)

(* exists-style notation for Sigma-types *)
Notation "'Sigma' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'Sigma'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Ltac inv A := inversion A; subst; try clear A.


(** * De Morgan laws *)

Lemma DM_or (X Y : Prop) :
  ~ (X \/ Y) <-> ~ X /\ ~ Y.
Proof.
  tauto.
Qed.

Lemma DM_not_exists X (p : X -> Prop) :
  ~ (exists x, p x) <-> forall x, ~ p x.
Proof.
  firstorder.
Qed.

(** Decidable propositions *)

Definition dec (P : Prop) := {P} + {~ P}.
Existing Class dec.

Definition decision (P : Prop) (d : dec P) : dec P := d.
Arguments decision P {d}.

Tactic Notation "decide" constr(p) := 
  destruct (decision p).

Tactic Notation "decide" constr(p) "as" simple_intropattern(i) := 
  destruct (decision p) as i.

Fact dec_trans P Q :
  dec P -> P <-> Q -> dec Q.
Proof.
  unfold dec. tauto.
Qed.

Instance True_dec :
  dec True.
Proof. 
  unfold dec; auto. 
Qed.

Instance False_dec :
  dec False.
Proof. 
  unfold dec; auto. 
Qed.

Instance impl_dec (P Q : Prop) :  
  dec P -> dec Q -> dec (P -> Q).
Proof. 
  unfold dec; tauto. 
Qed.

Instance and_dec (P Q : Prop) :  
  dec P -> dec Q -> dec (P /\ Q).
Proof. 
  unfold dec; tauto. 
Qed.

Instance or_dec (P Q : Prop) : 
  dec P -> dec Q -> dec (P \/ Q).
Proof. 
  unfold dec; tauto. 
Qed.

Instance not_dec (P : Prop) : 
  dec P -> dec (~P).
Proof. 
  unfold not. auto.
Qed.

Instance iff_dec (P Q : Prop) : 
  dec P -> dec Q -> dec (P <-> Q).
Proof. 
  unfold iff. auto.
Qed.

Notation "'eq_dec' X" := (forall x y : X, dec (x=y)) (at level 70).

(** Discrete types and decidable predicates *)
 
Structure eqType := EqType {
  eqtype :> Type;
  decide_eq : eq_dec eqtype }.

Arguments EqType eqtype {decide_eq}.
(** This is like defined and not like Qed *)
Existing Instance decide_eq. 

Structure decPred X := DecPred {
  predicate :> X -> Prop;
  decide_pred x : dec (predicate x) }.

Arguments DecPred {X} predicate {decide_pred}.

Existing Instance decide_pred.
Instance decp_dec X (p : decPred X) x :
  dec (p x).
Proof.
  apply decide_pred.
Qed.

(** Decidable relations *)

Structure decRel X := DecRel {
  relation :> X -> X -> Prop;
  decide_rel x y : dec (relation x y) }.

Arguments DecRel {X} relation {decide_rel}.

Instance decRel_dec X (R : decRel X) x y :
  dec (R x y).
Proof.
  apply decide_rel.
Qed.

Lemma dec_DN X : 
  dec X -> ~~ X -> X.
Proof. 
  unfold dec; tauto. 
Qed.

Lemma dec_DM_and X Y :  
  dec X -> ~ (X /\ Y) -> ~ X \/ ~ Y.
Proof. 
  unfold dec; tauto. 
Qed.

Lemma dec_DM_and' X Y :  
  dec Y -> ~ (X /\ Y) -> ~ X \/ ~ Y.
Proof. 
  unfold dec; tauto. 
Qed.

Lemma dec_DM_impl X Y :  
  dec X -> dec Y -> ~ (X -> Y) -> X /\ ~ Y.
Proof. 
  unfold dec; tauto. 
Qed.

Lemma dec_DM_all X (p: X -> Prop) (_:forall x, dec (p x)):
  (forall x, p x) <-> ~ exists x, ~ p x.
Proof.
  firstorder.
Qed.

Lemma dec_prop_iff (X Y : Prop) : 
  (X <-> Y) -> dec X -> dec Y.
Proof.
  unfold dec; tauto.
Qed.

Instance bool_eq_dec : 
  eq_dec bool.
Proof.
  intros x y. hnf. decide equality.
Qed.

Instance nat_eq_dec : 
  eq_dec nat.
Proof.
  intros x y. hnf. decide equality.
Qed.

Hint Resolve dec_prop_iff.

Instance nat_le_dec (x y : nat) : dec (x <= y) := 
  le_dec x y.

Instance list_eq_dec X :  
  eq_dec X -> eq_dec (list X).
Proof.
  intros D. apply list_eq_dec. exact D. 
Qed.

Instance list_in_dec (X : Type) (x : X) (A : list X) :  
  eq_dec X -> dec (In x A).
Proof.
  intros D. apply in_dec. exact D.
Qed.

(** * Lists *)

Definition equi X (A B : list X) : Prop :=
  incl A B /\ incl B A.

Hint Unfold equi.

Export ListNotations.
Notation "| A |" := (length A) (at level 65).
Notation "x 'el' A" := (In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).
Notation "A === B" := (equi A B) (at level 70).

(* The following comments are for coqdoc *)
(** printing el #∊# *)
(** printing <<= #⊆# *)
(** printing === #≡# *)

(** Register additional simplification rules with autorewrite / simpl_list *)

Hint Rewrite <- app_assoc : list.
Hint Rewrite rev_app_distr map_app prod_length : list.
(* Print Rewrite HintDb list. *)

Lemma list_cycle  (X : Type) (A : list X) x :
  x::A <> A.
Proof.
  intros B.
  assert (C: |x::A| <> |A|) by (simpl; omega).
  apply C. now rewrite B.
Qed.

(** * Decidability laws for lists *)

Lemma list_sigma_forall X A (p : X -> Prop) (p_dec : forall x, dec (p x)) :
  {x | x el A /\ p x} + {forall x, x el A -> ~ p x}.
Proof.
  induction A as [|x A]; simpl.
  - tauto.
  - destruct IHA as [[y [D E]]|D].
    + eauto. 
    + destruct (p_dec x) as [E|E].
      * eauto.
      * right. intros y [[]|F]; auto. 
Defined.

Arguments list_sigma_forall {X} A p {p_dec}.

Instance list_forall_dec X A (p : X -> Prop) :
  (forall x, dec (p x)) -> dec (forall x, x el A -> p x).
Proof.
  intros p_dec.
  destruct (list_sigma_forall A (fun x => ~ p x)) as [[x [D E]]|D].
  - right. auto.
  - left. intros x E. apply dec_DN; auto.
Qed.

Instance list_exists_dec X A (p : X -> Prop) :
  (forall x, dec (p x)) -> dec (exists x, x el A /\ p x).
Proof.
  intros p_dec.
  destruct (list_sigma_forall A p) as [[x [D E]]|D].
  - unfold dec. eauto.
  - right. intros [x [E F]]. exact (D x E F).
Qed.

Lemma list_exists_DM X A  (p : X -> Prop) : 
  (forall x, dec (p x)) ->
  ~ (forall x, x el A -> ~ p x) -> exists x, x el A /\ p x.
Proof. 
  intros D E. 
  destruct (list_sigma_forall A p) as [F|F].
  + destruct F as [x F]. eauto.
  + contradiction (E F).
Qed.

Lemma list_exists_not_incl X (A B : list X) :
  eq_dec X -> 
  ~ A <<= B -> exists x, x el A /\ ~ x el B.
Proof.
  intros D E.
  apply list_exists_DM; auto.
  intros F. apply E. intros x G.
  apply dec_DN; auto.
Qed.

Lemma list_cc X (p : X -> Prop) A : 
  (forall x, dec (p x)) -> 
  (exists x, x el A /\ p x) -> {x | x el A /\ p x}.
Proof.
  intros D E. 
  destruct (list_sigma_forall A p) as [[x [F G]]|F].
  - eauto.
  - exfalso. destruct E as [x [G H]]. apply (F x); auto.
Defined.

(** * Membership

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
  Implicit Types (x y : X) (A B : list X).

  Lemma in_sing x y :
    x el [y] -> x = y.
  Proof. 
    simpl. intros [[]|[]]. reflexivity. 
  Qed.

  Lemma in_cons_neq x y A :
    x el y::A -> x <> y -> x el A.
  Proof. 
    simpl. intros [[]|D] E; congruence. 
  Qed.

  Lemma not_in_cons x y A :
    ~ x el y :: A -> x <> y /\ ~ x el A.
  Proof.
    intuition; subst; auto.
  Qed.

(** * Disjointness *)

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

(** * Inclusion

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

Definition inclp (X : Type) (A : list X) (p : X -> Prop) : Prop :=
  forall x, x el A -> p x.

(** * Setoid rewriting with list inclusion and list equivalence *)

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

(** * Equivalence *)

Section Equi.
  Variable X : Type.
  Implicit Types A B : list X.

  Lemma equi_push x A :
    x el A -> A === x::A.

  Proof. auto. Qed.

  Lemma equi_dup x A :
    x::A === x::x::A.

  Proof. auto. Qed.

  Lemma equi_swap x y A:
    x::y::A === y::x::A.

  Proof. split; intros z; simpl; tauto. Qed.

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
    split; intros y; simpl.
    - intros [D|D]; subst; auto.
    - intros D. apply in_app_iff in D as [D|D].
      + auto.
      + apply in_sing in D. auto.
  Qed.
End Equi.

(** * Filter *)

Fixpoint filter X (p : decPred X) (A : list X) : list X :=
  match A with
  | nil => nil
  | x::A' => if decision (p x) then x :: filter p A' else filter p A'
  end.

Section FilterLemmas.
  Variable X : Type.
  Variable p : decPred X.

  Lemma in_filter_iff x A :
    x el filter p A <-> x el A /\ p x.
  Proof.
    induction A as [|y A]; cbn.
    - tauto.
    - decide (p y) as [C|C]; cbn;
        rewrite IHA; intuition; subst; tauto.
  Qed.

  Lemma filter_incl A :
    filter p A <<= A.
  Proof.
    intros x D. apply in_filter_iff in D. apply D.
  Qed.

  Lemma filter_mono A B :
    A <<= B -> filter p A <<= filter p B.

  Proof.
    intros D x E. apply in_filter_iff in E as [E E'].
    apply in_filter_iff. auto.
  Qed.

  Lemma filter_id A :
    (forall x, x el A -> p x) -> filter p A = A.
  Proof.
    intros D.
    induction A as [|x A]; simpl.
    - reflexivity.
    - decide (p x) as [E|E].
      + f_equal; auto.
      + exfalso. auto.
  Qed.

  Lemma filter_app A B :
    filter p (A ++ B) = filter p A ++ filter p B.
  Proof.
    induction A as [|y A]; simpl.
    - reflexivity.
    - rewrite IHA. decide (p y); reflexivity.  
  Qed.

  Lemma filter_fst x A :
    p x -> filter p (x::A) = x::filter p A.
  Proof.
    simpl. decide (p x); tauto.
  Qed.

  Lemma filter_fst' x A :
    ~ p x -> filter p (x::A) = filter p A.
  Proof.
    simpl. decide (p x); tauto.
  Qed.

End FilterLemmas.


Ltac filter_case p x A H :=
  decide (p x) as [H|H];
  [rewrite (filter_fst A H) | rewrite (filter_fst' A H)].


Section FilterLemmas_pq.
  Variable X : Type.
  Variable p q : decPred X.
  
  Lemma filter_pq_mono A :
    (forall x, x el A -> p x -> q x) -> filter p A <<= filter q A.
  Proof. 
    intros D x.
    rewrite !in_filter_iff. intuition.
  Qed.

  Lemma filter_pq_eq A :
    (forall x, x el A -> (p x <-> q x)) -> filter p A = filter q A.
  Proof. 
    intros C; induction A as [|x A]; cbn.
    - reflexivity.
    - decide (p x) as [D|D]; decide (q x) as [E|E].
      + f_equal; auto.
      + exfalso. apply E, C; auto.
      + exfalso. apply D, C; auto.
      + auto.
  Qed.

  Lemma filter_and A :
    filter p (filter q A) = filter (DecPred (fun x => p x /\ q x)) A.
  Proof.
    induction A as [|x A]; cbn.
    - reflexivity.
    - rewrite <- IHA.
      decide (q x) as [D|D]; decide (p x /\ q x) as [E|E].
      + apply filter_fst. intuition.
      + apply filter_fst'. intuition.
      + tauto.
      + reflexivity.
  Qed.
End FilterLemmas_pq.

Lemma filter_comm X p q (A :list X) :
  filter p (filter q A) = filter q (filter p A).
Proof.
  rewrite !filter_and. apply filter_pq_eq. cbn. tauto.
Qed.
(** * Element removal *)

Section Removal.
  Variable X : eqType.
  Implicit Types x y : X.

 (*  Definition neq (x : X) := decp (fun y => y <> x). *)

  Definition rem A x := filter (DecPred (fun y => y <> x)) A.

  Lemma in_rem_iff x A y :
    x el rem A y <-> x el A /\ x <> y.
  Proof.
    apply in_filter_iff.
  Qed.

  Lemma rem_not_in x y A :
    x = y \/ ~ x el A -> ~ x el rem A y.
  Proof.
    intros D E. apply in_rem_iff in E. tauto.
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
    intros E y F.
    decide (x=y) as [<-|G]; auto using rem_neq.
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
    intros D. apply filter_id.
    intros y E F. subst. auto.
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

(** * Cardinality *)

Section Cardinality.
  Variable X : eqType.
  Implicit Types A B : list X.

  Fixpoint card A : nat :=
    match A with
      | nil => 0
      | x::A => if decision (x el A) then card A else 1 + card A
    end.
 
  Lemma card_in_rem x A :
    x el A -> card A = 1 + card (rem A x).
  Proof.
    intros D. 
    induction A as [|y A]; simpl.
    - contradiction D.
    - decide (y <> x) as [E|E]; simpl.
      + rewrite IHA. 
        * { rewrite (rem_fst' _ E).
            decide (y el A) as [G|G]; simpl; f_equal;
              decide (y el rem A x) as [K|K]; simpl; try reflexivity.
            - exfalso. apply K. apply in_rem_iff; auto.
            - exfalso. apply in_rem_iff in K. tauto. }
        * destruct D; tauto.
      + apply dec_DN in E.
        * { subst y. rewrite rem_fst.
            decide (x el A) as [E|E].
            - auto.
            - rewrite rem_id; auto. }
        * auto.
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
  induction A as [|x A]; intros B D; simpl.
  - omega.
  - apply incl_lcons in D as [D D1].
    decide (x el A) as [E|E].
    + auto.
    + rewrite (card_in_rem D).
      cut (card A <= card (rem B x)). omega.
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
    rewrite (card_eq (rem_equi x A)). simpl.
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
    induction A as [|x A]; simpl; intros B D E.
    - symmetry in E. now apply card_0 in E as ->. 
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

Instance card_equi_proper (X : eqType) : 
  Proper (@equi X ==> eq) (@card X).
Proof. 
  hnf. apply card_eq.
Qed.

(** * Duplicate-free lists *)

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
    intros D E F. induction E as [|x A E' E]; simpl.
    - exact F.
    - apply disjoint_cons in D as [D D'].
      constructor; [|exact (IHE D')].
      intros G. apply in_app_iff in G; tauto.
  Qed.

  Lemma dupfree_map Y A (f : X -> Y) :
    (forall x y, x el A -> y el A -> f x = f y -> x=y) -> 
    dupfree A -> dupfree (map f A).

  Proof.
    intros D E. induction E as [|x A E' E]; simpl.
    - constructor.
    - constructor; [|now auto].
      intros F. apply in_map_iff in F as [y [F F']].
      rewrite (D y x) in F'; auto.
  Qed.

  Lemma dupfree_filter p A :
    dupfree A -> dupfree (filter p A).

  Proof.
    intros D. induction D as [|x A C D]; simpl.
    - left.
    - decide (p x) as [E|E]; auto.
      right; auto. rewrite in_filter_iff. tauto.
  Qed.

End Dupfree.

Section DupFreeDis.
  Variable X : eqType.
  Implicit Types A : list X.

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
    intros D.
    induction D as [|x A E F]; simpl.
    - reflexivity.
    - decide (x el A) as [G|].
      + contradiction (E G).
      + omega.
  Qed.
End DupFreeDis.

Section Undup.
  Variable X : eqType.
  Implicit Types A B : list X.

  Fixpoint undup A : list X :=
    match A with
      | nil => nil
      | x::A' => if decision (x el A') then undup A' else  x :: undup A'
    end.

  Lemma undup_id_equi A :
    undup A === A.
  Proof.
    induction A as [|x A]; simpl.
    - reflexivity.
    - decide (x el A) as [E|E]; rewrite IHA; auto.
  Qed.

  Lemma dupfree_undup A :
    dupfree (undup A).
  Proof.
    induction A as [|x A]; simpl.
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
    intros E. induction E as [|x A E F]; simpl.
    - reflexivity.
    - rewrite IHF. decide (x el A) as [G|G]; tauto.
  Qed.

  Lemma undup_idempotent A :
    undup (undup A) = undup A.

  Proof. apply undup_id, dupfree_undup. Qed.

End Undup.

(** * Power lists *)

Section PowerRep.
  Variable X : eqType.

  Implicit Types A U : list X.

  Fixpoint power (U : list X ) : list (list X) :=
    match U with
      | nil => [nil]
      | x :: U' => power U' ++ map (cons x) (power U')
    end.
  
  Lemma power_incl A U :
    A el power U -> A <<= U.

  Proof.
    revert A; induction U as [|x U]; simpl; intros A D.
    - destruct D as [[]|[]]; auto.
    - apply in_app_iff in D as [E|E]. now auto.
      apply in_map_iff in E as [A' [E F]]. subst A.
      auto.
  Qed.

  Lemma power_nil U :
    nil el power U.

  Proof. induction U; simpl; auto. Qed.

(*  Definition member A := decp (fun x => x el A). *)

  Definition rep (A U : list X) : list X :=
    filter (DecPred (fun x => x el A)) U.

  Lemma rep_power A U :
    rep A U el power U.

  Proof.
    unfold rep.
    induction U as [|x U].
    - simpl; auto.
    - simpl power.
      decide (x el A) as [D|D].
      + rewrite filter_fst; simpl;  auto using in_map.
      + rewrite filter_fst'; simpl;  auto using in_map.
  Qed.

  Lemma rep_incl A U :
    rep A U <<= A.

  Proof.
    unfold rep. intros x D. apply in_filter_iff in D. apply D.
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

  Proof. intros D. apply filter_pq_mono. simpl. auto. Qed.

  Lemma rep_eq' A B U :
    (forall x, x el U -> (x el A <-> x el B)) -> rep A U = rep B U.

  Proof. intros D. apply filter_pq_eq. auto. Qed.

  Lemma rep_eq A B U :
    A === B -> rep A U = rep B U.

  Proof. intros D. apply filter_pq_eq; simpl. firstorder. Qed.

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
    intros x D. split.
    + apply rep_incl.
    + intros E. apply in_filter_iff. auto.
  Qed.

  Lemma dupfree_power U :
    dupfree U -> dupfree (power U).

  Proof.
    intros D. induction D as [|x U E D]; simpl.
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
    induction D as [|x U D D']; simpl; intros A E.
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
    unfold rep.
    intros D; revert A. 
    induction D as [|x U E F]; intros A G.
    - destruct G as [[]|[]]; reflexivity.
    - simpl in G. apply in_app_iff in G as [G|G]. 
      + decide (x el A) as [H|H].
        * exfalso. apply E. apply (power_incl G), H.
        * rewrite filter_fst'; simpl; auto.
      + apply in_map_iff in G as [A' [G H]]. subst A.
        rewrite filter_fst.
        * f_equal. pattern A' at 3. rewrite <- (IHF _ H).
          apply filter_pq_eq. simpl. intuition subst; intuition.
        * simpl; auto.
  Qed.

  Lemma power_extensional A B U :
    dupfree U -> A el power U -> B el power U -> A === B -> A = B.

  Proof.
    intros D E F G. 
    rewrite <- (rep_dupfree D E). rewrite <- (rep_dupfree D F).
    apply rep_eq, G.
  Qed.

End PowerRep.


(** Size induction from ICL *)

Lemma size_induction X (f : X -> nat) (p : X -> Prop) :
  (forall x, (forall y, f y < f x -> p y) -> p x) -> 
  forall x, p x.
Proof. 
  intros step x. apply step. 
  assert (G: forall n y, f y < n -> p y).
  { intros n. induction n.
    - intros y B. exfalso. omega.
    - intros y B. apply step. intros z C. apply IHn. omega. }
  apply G.
Qed.