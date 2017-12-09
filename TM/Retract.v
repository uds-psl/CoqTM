(* Library for injections, bijections, retracts and tight retracts *)
Require Import Shared.Base.

(*
 * This tactic tries to prove derived injectivity or (tight) retracts
 *)
Tactic Notation "auto_inj" := repeat (eauto with inj).
Tactic Notation "auto_inj" integer(k) := repeat (eauto k with inj).

(* Hint database for injections, bijections, retracts and tight retracts *)
Create HintDb inj.


Section Bijection.
  Variable X Y : Type.
  Variable (f : X -> Y) (g : Y -> X).

  Definition left_inverse  := forall x : X, g (f x) = x.
  Definition right_inverse := forall y : Y, f (g y) = y.
  Definition inverse := left_inverse /\ right_inverse.

  Existing Class inverse.

  Hypothesis I : inverse.
  Definition Inverse : inverse := I.
  Definition Inverse_left  : left_inverse  := ltac:(now apply I).
  Definition Inverse_right : right_inverse := ltac:(now apply I).

End Bijection.

(* With the help of the Inverse* functions, the inversion proof should be automaticly infered *)
Arguments Inverse       { X } { Y } f g { I }.
Arguments Inverse_left  { X } { Y } f g { I }.
Arguments Inverse_right { X } { Y } f g { I }.

Class Inversion (X Y : Type) :=
  {
    Inv_f : X -> Y;
    Inv_g : Y -> X;
    Inv_inv :> inverse Inv_f Inv_g;
  }.
Coercion Inv_inv : Inversion >-> inverse.

(* Replace [ f (g x) ] with [ x ], etc. *)
Ltac inverse :=
  match goal with
  | [ H : context [ ?f (?g _ ) ] |- _] =>
    first [
        (erewrite Inverse_left in H ; [ | now auto_inj ])
        ||
        (erewrite Inverse_right in H; [ | now auto_inj ])
      ]
  | [   |- context [ ?f (?g _ ) ]    ] =>
    first [
        (erewrite Inverse_left      ; [ | now auto_inj ])
        ||
        (erewrite Inverse_right     ; [ | now auto_inj ])
      ]
  end.


Section Bijection_Test.
  Variable X Y : Type.
  Variable (f : X -> Y) (g : Y -> X).
  Hypothesis I : inverse f g.
  Goal forall x, g (f x) = x.
  Proof.
    intros x. inverse. reflexivity.
  Qed.

  Goal forall y, f (g y) = y.
  Proof.
    intros y. inverse. reflexivity.
  Qed.

End Bijection_Test.



Section Useful_Inversions.

  Variable A B C D : Type.

  (* Bijectivity is a euqivialance relation. *)
  Section Inverse_Equivialence.
    Instance inverse_id : inverse (@id A) (@id A).
    Proof. hnf. firstorder. Qed.

    Section Inverse_Comp.

      Variable (f1 : A -> B) (g1 : B -> A) (f2 : B -> C) (g2 : C -> B).

      Definition inverse_comp_f : A -> C := fun a => f2 (f1 a).
      Definition inverse_comp_g : C -> A := fun c => g1 (g2 c).

      Instance inverse_comp  :
        inverse f1 g1 ->
        inverse f2 g2 ->
        inverse inverse_comp_f inverse_comp_g.
      Proof.
        unfold inverse_comp_f, inverse_comp_g.
        intros (H1&H1') (H2&H2'). hnf in *. split; hnf.
        - intros x. rewrite H2. rewrite H1. reflexivity.
        - intros c. rewrite H1'. rewrite H2'. reflexivity.
      Qed.

    End Inverse_Comp.
    
    Instance inverse_symmetric (f : A -> B) (g : B -> A) :
      inverse f g ->
      inverse g f.
    Proof. firstorder. Qed.

  End Inverse_Equivialence.

  Section Inverse_Sum.
    Variable (f1 : A -> C) (g1 : C -> A) .
    Variable (f2 : B -> D) (g2 : D -> B) .

    Definition inverse_sum_f : A + B -> C + D :=
      fun x => match x with
            | inl a => inl (f1 a)
            | inr c => inr (f2 c)
            end.

    Definition inverse_sum_g : C + D -> A + B :=
      fun y => match y with
            | inl c => inl (g1 c)
            | inr d => inr (g2 d)
            end.

    Instance inverse_sum :
      inverse f1 g1 -> 
      inverse f2 g2 ->
      inverse inverse_sum_f inverse_sum_g.
    Proof. intros H1 H2. unfold inverse_sum_f, inverse_sum_g. hnf. split; hnf; intros [a|b]; now inverse. Qed.

  End Inverse_Sum.

  Section Inverse_Sum_Swap.

    Definition inverse_sum_swap_f : A + B -> B + A :=
      fun x =>
        match x with
        | inl a => inr a
        | inr b => inl b
        end.

    Definition inverse_sum_swap_g : B + A -> A + B :=
      fun x =>
        match x with
        | inl b => inr b
        | inr a => inl a
        end.

    Instance inverse_sum_swap : inverse inverse_sum_swap_f inverse_sum_swap_g.
    Proof. unfold inverse_sum_swap_f, inverse_sum_swap_g. hnf. split; hnf; intros [a|b]; reflexivity. Qed.

  End Inverse_Sum_Swap.
  
  Section Inverse_Sum_Empty_set.

    Definition inverse_sum_Empty_set_f : A + Empty_set -> A :=
      fun x =>
        match x with
        | inl a => a
        | inr b => match b with end
        end.

    Definition inverse_sum_Empty_set_g : A -> A + Empty_set := inl.
    
    Global Instance inverse_sum_Empty_set : inverse inverse_sum_Empty_set_f inverse_sum_Empty_set_g.
    Proof. unfold inverse_sum_Empty_set_f, inverse_sum_Empty_set_g. hnf. split; hnf. now intros [ a | [] ]. tauto. Qed.

  End Inverse_Sum_Empty_set.

  Section Inverse_Option_unit.

    Definition inverse_option_unit_f : option A -> A + unit :=
      fun x =>
        match x with
        | Some y => inl y
        | None => inr tt
        end.

    Definition inverse_option_unit_g : A + unit -> option A :=
      fun y =>
        match y with
        | inl a => Some a
        | inr _ => None
        end.

    Global Instance inverse_option_unit : inverse inverse_option_unit_f inverse_option_unit_g.
    Proof.
      unfold inverse_option_unit_f, inverse_option_unit_g. hnf. split; hnf.
      - intros [ a | ]; reflexivity.
      - intros [ a | [ ] ]; reflexivity.
    Qed.

  End Inverse_Option_unit.

  Section Inverse_involutive.
    Variable f : A -> A.
    Hypothesis f_inv : forall a, f (f a) = a.

    Global Instance inverse_involutive : inverse f f.
    Proof. hnf. split; hnf; auto. Qed.

  End Inverse_involutive.
  
  Definition swap (X Y : Type) : X * Y -> Y * X := fun '(a,b) => (b, a).

  Global Instance inverse_swap : inverse (@swap A B) (@swap B A).
  Proof. unfold swap. hnf. split; hnf; intros [x y]; reflexivity. Qed.

End Useful_Inversions.

Hint Resolve inverse_comp          : inj.
Hint Resolve inverse_id            : inj.
Hint Resolve inverse_symmetric     : inj.
Hint Resolve inverse_sum_Empty_set : inj.
Hint Resolve inverse_sum_swap      : inj.
Hint Resolve inverse_symmetric     : inj.
Hint Resolve inverse_option_unit   : inj.
Hint Resolve inverse_involutive    : inj.
Hint Resolve inverse_swap          : inj.


Section Retract.

  Variable X Y : Type.
  Variable (f : X -> Y) (g : Y -> option X).

  Definition retract := forall x, g (f x) = Some x.
  Existing Class retract.

  Hypothesis I : retract.

  Definition retract_g_adjoint : forall x, g (f x) = Some x := I.

  Lemma retract_g_surjective : forall x, { y | g y = Some x }.
  Proof. intros x. pose proof (I x). eauto. Defined.

  Lemma retract_f_injective : forall x1 x2, f x1 = f x2 -> x1 = x2.
  Proof.
    intros x1 x2 H. enough (Some x1 = Some x2) as HE by now inv HE.
    erewrite <- !I; eauto. now rewrite H.
  Qed.
End Retract.

Hint Resolve retract_g_adjoint : inj.

Class Retract (X Y : Type) :=
  {
    Retr_f : X -> Y;
    Retr_g : Y -> option X;
    Retr_adj :> retract Retr_f Retr_g;
  }.
Coercion Retr_adj : Retract >-> retract.

Ltac retract_adjoint :=
  match goal with
  | [   |- context [ ?g (?f ?X) ]     ] => rewrite retract_g_adjoint;      [ | now auto_inj]
  | [ H : context [ ?g (?f ?X) ] |- _ ] => rewrite retract_g_adjoint in H; [ | now auto_inj]
  end.

Section TightRetract.

  Variable X Y : Type.
  Variable (f : X -> Y) (g : Y -> option X).

  Definition tight_retract := forall x y, g y = Some x <-> y = f x.
  Existing Class tight_retract.

  Variable I : tight_retract.

  Instance tight_retract_strong : retract f g := ltac:(firstorder).

  Definition tretract_g_inv : forall x y, g y = Some x <-> y = f x := I.
  Definition tretract_g_inv' : forall x y, g y = Some x -> y = f x := ltac:(apply tretract_g_inv; auto).
  Definition tretract_g_adjoint : forall x, g (f x) = Some x := retract_g_adjoint _.

  Lemma tretract_g_surjective : forall x, { y | g y = Some x }.
  Proof. intros x. pose proof (tretract_g_adjoint x). eauto. Defined.

  Definition tretract_f_injective : forall x1 x2, f x1 = f x2 -> x1 = x2 := retract_f_injective _.
    
End TightRetract.

Hint Unfold tight_retract         : inj.
Hint Resolve tight_retract_strong : inj.
Hint Resolve tretract_g_inv       : inj.
Hint Resolve tretract_g_inv'      : inj.

Class TRetract (X Y : Type) :=
  {
    TRetr_f : X -> Y;
    TRetr_g : Y -> option X;
    TRetr_inv :> tight_retract TRetr_f TRetr_g;
  }.
Coercion TRetr_inv : TRetract >-> tight_retract.


Section Retract_Compose.
  Variable (X Y Z : Type).
  Variable (f1 : X -> Y) (g1 : Y -> option X).
  Variable (f2 : Y -> Z) (g2 : Z -> option Y).

  Definition retract_comp_f := fun x => f2 (f1 x).
  Definition retract_comp_g :=
    fun z =>
      match g2 z with
      | Some y => g1 y
      | None => None
      end.

  Instance retract_compose (retr1 : retract f1 g1) (retr2 : retract f2 g2) :
    retract retract_comp_f retract_comp_g.
  Proof.
    hnf. unfold retract_comp_f, retract_comp_g. intros x. retract_adjoint. rewrite retract_g_adjoint; eauto.
  Qed.

  Instance tretract_compose (retr1 : tight_retract f1 g1) (retr2 : tight_retract f2 g2) :
    tight_retract retract_comp_f retract_comp_g.
  Proof.
    unfold retract_comp_f, retract_comp_g. hnf.
    split.
    - intros H. destruct (g2 y) eqn:E.
      + eapply tretract_g_inv in E as ->. eapply tretract_g_inv in H as ->. all:auto.
      + congruence.
    - hnf. intros ->. unfold retract_comp_f, retract_comp_g. rewrite tretract_g_adjoint; auto with inj.
  Qed.

End Retract_Compose.

Hint Resolve tretract_compose : inj.

Section Inversion_Retract.
  Variable A B : Type.
  Variable (f : A -> B) (g : B -> A).
  
  Instance inversion_retract :
    inverse f g ->
    tight_retract f (fun b => Some (g b)).
  Proof.
    intros H. hnf. intros a b. split.
    - intros H2. inv H2.  now inverse.
    - intros ->. f_equal. now inverse.
  Qed.
  
End Inversion_Retract.

Hint Resolve inversion_retract : inj.

Section Usefull_Retracts.

  Variable (A B C D : Type).

  (*
  Instance retract_id : tight_retract (@id A) (@Some A) := ltac:(unfold id; firstorder congruence).
  *)

  (* This can be derived, because [ id ] is a inversion with itself. *)
  Instance retract_id : tight_retract (@id A) (@Some A) := ltac:(now auto_inj).

  Instance retract_option : tight_retract (@Some A) id := ltac:(now auto_inj).

  Definition retract_inl_g := fun z : A + B => match z with inl x => Some x | inr _ => None end.

  Instance retract_inl : tight_retract inl retract_inl_g.
  Proof. hnf. intros x z. unfold retract_inl_g. destruct z; firstorder congruence. Qed.

  Definition retract_inr_g := fun z : A + B => match z with inr x => Some x | inl _ => None end.

  Instance retract_inr : tight_retract inr retract_inr_g.
  Proof. hnf. intros x z. unfold retract_inr_g. destruct z; firstorder congruence. Qed.

  Definition retract_empty_f : Empty_set -> A := fun x : Empty_set => match x with end.
  Definition retract_empty_g : A -> option Empty_set := fun y => None.
  
  Instance retract_empty : tight_retract retract_empty_f retract_empty_g.
  Proof.
    hnf. unfold retract_empty_f, retract_empty_g. firstorder.
    - congruence.
    - destruct x.
  Qed.

  Section RetractSum.

    Variable (f1 : A -> C) (g1 : C -> option A) .
    Variable (f2 : B -> D) (g2 : D -> option B) .

    Definition retract_sum_f : A + B -> C + D :=
      fun x => match x with
            | inl a => inl (f1 a)
            | inr c => inr (f2 c)
            end.

    Definition retract_sum_g : C + D -> option (A + B) :=
      fun y => match y with
            | inl c => match g1 c with
                      | Some a => Some (inl a)
                      | None => None
                      end
            | inr d => match g2 d with
                      | Some b => Some (inr b)
                      | None => None
                      end
            end.

    Instance retract_sum :
      retract f1 g1 -> 
      retract f2 g2 ->
      retract retract_sum_f retract_sum_g.
    Proof.
      intros H1 H2. intros [a|b]; hnf; cbn; retract_adjoint; auto.
    Qed.

    Instance tretract_sum :
      tight_retract f1 g1 -> 
      tight_retract f2 g2 ->
      tight_retract retract_sum_f retract_sum_g.
    Proof.
      intros H1 H [a|b] [c|d]; hnf; cbn;
        (split; [intros H3; f_equal; first [destruct (g1 _) eqn:E | destruct (g2 _) eqn:E];
                 inv H3; repeat retract_adjoint; auto_inj | intros H3; inv H3; try retract_adjoint; auto_inj ]).
    Qed.

  End RetractSum.

End Usefull_Retracts.

Hint Resolve retract_id        : inj.
Hint Resolve retract_option    : inj.
Hint Resolve retract_inl       : inj.
Hint Resolve retract_inr       : inj.
Hint Resolve tretract_sum      : inj.

Section RetractCons.

  Variable A : eqType.
  Variable a : A.

  Definition retract_cons_g : list A -> option (list A) :=
    fun xs =>
      match xs with
      | x :: xs' => if Dec (x = a) then Some xs' else None
      | nil => None
      end.
  
  Instance retract_cons : tight_retract (cons a) retract_cons_g.
  Proof.
    unfold retract_cons_g. hnf. intros xs ys. split.
    - destruct ys; intros H; inv H. decide (e = a); now inv H1.
    - intros ->. decide (a = a); tauto.
  Qed.

  Variable B : Type.
  Definition retract_pair_g : A * B -> option B :=
    fun '(x, b) => if Dec (a = x) then Some b else None.

  Instance retract_pair : tight_retract (pair a) retract_pair_g.
  Proof. unfold retract_pair_g. hnf. intros b (x&y). decide (a = x); firstorder congruence. Qed.

End RetractCons.
Hint Resolve retract_cons.

Section Injection.

  Variable X Y : Type.

  Definition injective (f : X -> Y) := forall x1 x2, f x1 = f x2 -> x1 = x2.
  Existing Class injective.

  Definition inj_injective {f : X -> Y} {I : injective f} : forall x1 x2, f x1 = f x2 -> x1 = x2 := I.

End Injection.

Class Injection (X Y : Type) :=
  {
    Inj_f : X -> Y;
    Inj_inj :> injective  Inj_f;
  }.
Coercion Inj_inj : Injection >-> injective.

Ltac inj_subst :=
  match goal with
  | [ H : ?t ?x = ?t ?y |- _] => eapply inj_injective in H; [ subst | now auto_inj]
  end.

Instance injection_id (X : Type) : injective (@id X) := ltac:(unfold id; firstorder).

Section Injection_Compose.
  Variable X Y Z : Type.
  Variable (f : X -> Y) (g : Y -> Z).
  Hypothesis (f_inj : injective f) (g_inj : injective g).

  Definition compose_inj : X -> Z := fun x => g (f x).

  Instance compose_inj_injective : injective compose_inj := ltac:(firstorder).

End Injection_Compose.


Section Map_Injective.
  Variable (sig tau : Type) (t : sig -> tau).
  Hypothesis t_injective : injective t.

  Instance map_injective :
    injective (map t).
  Proof.
    hnf. intros xs. induction xs; intros ys H; cbn in *.
    - erewrite map_eq_nil; eauto.
    - destruct ys; cbn in *; inv H. inj_subst. f_equal. auto.
  Qed.

End Map_Injective.

Instance retract_injective (A B : Type) (f : A -> B) (g : B -> option A) :
  retract f g -> injective f.
Proof.
  intros H. intros x1 x2 H2. eapply retract_f_injective; eauto.
Qed.
Hint Resolve retract_injective : inj.

Section Injection_Corollaries.
  Variable A B : Type.
  
  Instance injective_id : injective (@id A) := ltac:(now auto_inj).
  Instance injective_inl : injective (@inl A B) := ltac:(now auto_inj).
  Instance injective_inr : injective (@inr A B) := ltac:(now auto_inj).
  
End Injection_Corollaries.

Hint Resolve injective_id : inj.
Hint Resolve injective_inl : inj.
Hint Resolve injective_inr : inj.


(* TODO: Can any injection between decidable types be made a retract? *)
Section Dec_Retract.
End Dec_Retract.


Section Retract_TightRetract.
  Variable (X : Type) (Y : eqType) (f : X -> Y) (g : Y -> option X).
  Hypothesis retr : retract f g.

  Global Instance retract_dec_image :
    forall y, dec (exists x, f x = y).
  Proof.
    intros y. destruct (g y) as [x | ] eqn:E.
    - decide (f x = y) as [<- | D].
      + left. eauto.
      + right. intros (x'&<-). enough (Some x' = Some x) by congruence.
        erewrite <- retract_g_adjoint; eauto.
    - right. intros (x&<-). rewrite retract_g_adjoint in E; eauto. congruence.
  Qed.

  Definition make_tight_retract_g : Y -> option X :=
    fun y => if Dec (exists x, f x = y) then g y else None.

  Global Instance make_tight_retract : tight_retract f make_tight_retract_g.
  Proof.
    unfold make_tight_retract_g. split.
    - intros H. decide (exists x, f x = y) as [ (x'&<-) | D].
      + rewrite retract_g_adjoint in H; auto. congruence.
      + congruence.
    - intros ->. decide (exists x', f x' = f x) as [ (x'&Hx') | D].
      + rewrite retract_g_adjoint; auto.
      + contradict D. eauto.
  Qed.

End Retract_TightRetract.

Hint Resolve make_tight_retract : inj.