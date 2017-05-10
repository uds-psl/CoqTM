Require Import Basic.Mono Basic  Compound Combinators.SequentialComposition.

Section write_string.

  Variable sig : finType.
  Variable tapes_no : nat.

  Variable on_tape : nat.
  Hypothesis is_a_tape : on_tape < S tapes_no.

  Fixpoint Write_string (l : list sig) : {M :  mTM sig tapes_no & states M -> unit} :=
    match l with
    | [] => Nop tapes_no sig tt
    | e :: l0 => Write is_a_tape e;; Move _ is_a_tape R;; Write_string l0
    end.

  Definition Write_string_R l :=
    fun (t t' : tape sig) => exists R,
        t' = mk_rtape (rev l ++ left t) R.
  
  Lemma Write_string_sem x l :
    Write_string (x :: l) ⊨(4 + 4 * |l|) ⇑[is_a_tape] ignoreParam (Write_string_R (x :: l)).
  Proof.
    revert x. induction l; intros.
    - unfold Write_string.
      TMstep. eapply Seq_total. eapply write_sem. eapply Seq_total.
      eapply move_sem. eapply Nop_total. omega.
      autorewrite lift.
      repeat setoid_rewrite lift_hideParam.
      rewrite ignore_hideParam; try now econstructor. TMcorrect.
      intros ? ([] & ?) ?. TMnormalise. subst. cbn in *.
      destruct x2; TMnormalise. unfold MoveR, Write_string_R in *.
      cbn in *. destruct b; TMnormalise; subst.
      + inv H0. destruct _. exists nil; eauto. now exists (e :: l).
      + inv H.
    - unfold Write_string. TMstep.
      eapply Seq_total. eapply write_sem.
      eapply Seq_total. eapply move_sem.
      eapply IHl. cbn. omega.
      autorewrite lift.
      repeat setoid_rewrite lift_hideParam.
      rewrite ignore_hideParam; try now econstructor. TMcorrect.
      intros ? ([] & ?) ?.
      repeat TMnormaliseH1. subst. cbn in x2; destruct x2.
      unfold MoveR in H0. unfold Write_string_R in H1.
      unfold Write_string_R. cbn -[Write_string] in *.
      destruct b; subst.
      + destruct H0. destruct H0. destruct H1. subst. inv H0.
        destruct _; cbn; exists x2; now autorewrite with list.
      + exfalso. clear IHl. TMnormalise. inv H.
  Qed.

End write_string.
