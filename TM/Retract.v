Require Import Shared.Base.

Ltac simpl_inj := repeat (eauto with inj; autorewrite with inj).

Tactic Notation "simpl_inj" "in" ident(H) := repeat (eauto with inj; autorewrite with inj in H).
Tactic Notation "simpl_inj" "in" "*" := repeat (eauto with inj; autorewrite with inj in *).

Section Injection.

  Variable X Y : Type.

  Definition injective (f : X -> Y) := forall x1 x2, f x1 = f x2 -> x1 = x2.
  Existing Class injective.

  Definition inj_injective {f : X -> Y} {I : injective f} : forall x1 x2, f x1 = f x2 -> x1 = x2 := I.

End Injection.

Hint Unfold injective : inj.
Hint Rewrite inj_injective using now simpl_inj : inj.

Hint Extern 5 => match goal with
                | [ H : ?t ?x = ?t ?y |- _] => eapply inj_injective in H; [ subst | now eauto]
                end : inj.

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

  Lemma map_injective :
    injective (map t).
  Proof.
    hnf. intros xs. induction xs; intros ys H; cbn in *.
    - erewrite map_eq_nil; eauto.
    - destruct ys; cbn in *; inv H. simpl_inj in H1.
      eapply inj_injective in H1; eauto. subst. f_equal. auto.
  Qed.

End Map_Injective.


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

Hint Unfold retract            : inj.
Hint Resolve retract_g_adjoint : inj.
Hint Rewrite retract_g_adjoint using now simpl_inj : inj.

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

Hint Unfold tight_retract        : inj.
Hint Resolve tight_retract_strong : inj.
Hint Resolve tretract_g_inv       : inj.
Hint Resolve tretract_g_inv'      : inj.
Hint Rewrite tretract_g_adjoint using now simpl_inj : inj.


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
    hnf. unfold retract_comp_f, retract_comp_g. intros x. rewrite retract_g_adjoint; eauto.
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


Section Usefull_Retracts.

  Variable (A B C D : Type).

  Instance retract_id : tight_retract (@id A) (@Some A) := ltac:(unfold id; firstorder congruence).

  Instance retract_option : tight_retract (@Some A) id := ltac:(hnf; firstorder).

  Instance retract_injective (f : A -> B) (g : B -> option A) :
    retract f g -> injective f.
  Proof.
    intros H. intros x1 x2 H2. eapply retract_f_injective; eauto.
  Qed.

  Definition retract_inl_f := @inl A B.
  Definition retract_inl_g := fun z : A + B => match z with inl x => Some x | inr _ => None end.

  Instance retract_inl : tight_retract retract_inl_f retract_inl_g.
  Proof. hnf. intros x z. unfold retract_inl_f, retract_inl_g. destruct z; firstorder congruence. Qed.

  Definition retract_inr_f := @inr A B.
  Definition retract_inr_g := fun z : A + B => match z with inr x => Some x | inl _ => None end.

  Instance retract_inr : tight_retract retract_inr_f retract_inr_g.
  Proof. hnf. intros x z. unfold retract_inr_f, retract_inr_g. destruct z; firstorder congruence. Qed.

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
      intros H1 H2. intros [a|b]; hnf; cbn; now simpl_inj.
    Qed.

    Instance tretract_sum :
      tight_retract f1 g1 -> 
      tight_retract f2 g2 ->
      tight_retract retract_sum_f retract_sum_g.
    Proof.
      intros H1 H [a|b] [c|d]; hnf; cbn;
        (split; [intros H3; f_equal; first [destruct (g1 _) eqn:E | destruct (g2 _) eqn:E];
                 inv H3; simpl_inj | intros H3; inv H3; simpl_inj]).
    Qed.

  End RetractSum.
    
End Usefull_Retracts.

Hint Resolve retract_injective : inj.
Hint Resolve retract_id        : inj.
Hint Resolve retract_option    : inj.
Hint Resolve retract_inl       : inj.
Hint Resolve retract_inr       : inj.
Hint Resolve tretract_sum      : inj.


Section Injection_Corollaries.
  Variable A B : Type.
  
  Instance injective_inl : injective (@inl A B) := ltac:(now simpl_inj).
  Instance injective_inr : injective (@inr A B) := ltac:(now simpl_inj).
  
End Injection_Corollaries.

Hint Resolve injective_inl : inj.
Hint Resolve injective_inr : inj.