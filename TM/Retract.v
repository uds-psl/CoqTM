Require Import Shared.Base.

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

  Definition retract_tight : Prop := forall x y, retract_g I y = Some x -> y = retract_f I x.

End Retract.


Section Retract_Compose.
  Variable (X Y Z : Type).
  Hypothesis (inj1 : retract X Y) (inj2 : retract Y Z).

  Definition retract_comp_f := fun x => retract_f inj2 (retract_f inj1 x).

  Definition retract_comp_g :=
    fun z =>
      match retract_g inj2 z with
      | Some y =>retract_g inj1 y
      | None => None
      end.

  Lemma retract_comp_inv : forall (x : X), retract_comp_g (retract_comp_f (x)) = Some x.
  Proof.
    unfold retract_comp_f, retract_comp_g. intros x. now do 2 rewrite retract_g_adjoint.
  Qed.

  Hypothesis (tight1 : retract_tight inj1) (tight2 : retract_tight inj2).

  Definition retract_compose : retract X Z := Build_retract retract_comp_inv.

  Lemma retract_comp_tight : retract_tight retract_compose.
  Proof.
    hnf. intros x y H. unfold retract_compose in *. cbn in *. unfold retract_comp_g, retract_comp_f in *.
    destruct (retract_g inj2 y) eqn:E.
    - apply tight2 in E as ->. apply tight1 in H as ->. reflexivity.
    - congruence.
  Qed.
  
End Retract_Compose.