Require Import Shared.Base.

Section Injection.

  Variable X Y : Type.

  Definition injective (f : X -> Y) := forall x1 x2, f x1 = f x2 -> x1 = x2.

End Injection.

Section Injection_Compose.
  Variable X Y Z : Type.
  Variable (f : X -> Y) (g : Y -> Z).
  Hypothesis (f_inj : injective f) (g_inj : injective g).

  Definition compose_inj : X -> Z := fun x => g (f x).

  Lemma compose_inj_injective : injective compose_inj.
  Proof. firstorder. Qed.
End Injection_Compose.


Section Retract.

  Variable X Y : Type.

  Record retract :=
    {
      retract_f : X -> Y;
      retract_g : Y -> option X;
      retract_g_adjoint : forall x, retract_g (retract_f x) = Some x;
    }.

  Variable I : retract.

  Lemma retract_g_surjective : forall x, { y | (retract_g I) y = Some x }.
  Proof. intros x. pose proof (retract_g_adjoint I x). eauto. Defined.

  Lemma retract_f_injective : forall x1 x2, retract_f I x1 = retract_f I x2 -> x1 = x2.
  Proof.
    intros x1 x2 H. enough (Some x1 = Some x2) as HE by now inv HE.
    erewrite <- !retract_g_adjoint; eauto. now rewrite H.
  Qed.
End Retract.

Section TightRetract.

  Variable X Y : Type.

  Record tight_retract :=
    {
      tretract_f : X -> Y;
      tretract_g : Y -> option X;
      tretract_inv : forall x y, tretract_g y = Some x <-> y = tretract_f x;
    }.

  Variable I : tight_retract.

  Lemma tretract_g_adjoint : forall x, tretract_g I (tretract_f I x) = Some x.
  Proof. intros. now apply tretract_inv. Qed.

  Lemma tretract_g_surjective : forall x, { y | (tretract_g I) y = Some x }.
  Proof. intros x. pose proof (tretract_g_adjoint x). eauto. Defined.

  Lemma tretract_f_injective : forall x1 x2, tretract_f I x1 = tretract_f I x2 -> x1 = x2.
  Proof.
    intros x1 x2 H. enough (Some x1 = Some x2) as HE by now inv HE.
    erewrite <- !tretract_g_adjoint; eauto. now rewrite H.
  Qed.
    
End TightRetract.


Section Retract_Compose.
  Variable (X Y Z : Type).
  Hypothesis (inj1 : retract X Y) (inj2 : retract Y Z).

  Definition retract_comp_f := fun x => retract_f inj2 (retract_f inj1 x).

  Definition retract_comp_g :=
    fun z =>
      match retract_g inj2 z with
      | Some y => retract_g inj1 y
      | None => None
      end.

  Lemma retract_comp_adjoint : forall (x : X), retract_comp_g (retract_comp_f (x)) = Some x.
  Proof.
    unfold retract_comp_f, retract_comp_g. intros x. now do 2 rewrite retract_g_adjoint.
  Qed.

  Definition retract_compse := Build_retract retract_comp_adjoint.

End Retract_Compose.

Section TightRetract_Compose.

  Variable (X Y Z : Type).
  Hypothesis (inj1 : tight_retract X Y) (inj2 : tight_retract Y Z).

  Definition tretract_comp_f := fun x => tretract_f inj2 (tretract_f inj1 x).

  Definition tretract_comp_g :=
    fun z =>
      match tretract_g inj2 z with
      | Some y => tretract_g inj1 y
      | None => None
      end.

  Lemma tretract_comp_inv : forall x z, tretract_comp_g z = Some x <-> z = tretract_comp_f x.
  Proof.
    unfold tretract_comp_f, tretract_comp_g. intros x z. split.
    - intros H. destruct (tretract_g inj2 z) eqn:E.
      + apply tretract_inv in E as ->. apply tretract_inv in H as ->. reflexivity.
      + congruence.
    - intros ->. now do 2 rewrite tretract_g_adjoint.
  Qed.

  Definition tretract_compose := Build_tight_retract tretract_comp_inv.

End TightRetract_Compose.