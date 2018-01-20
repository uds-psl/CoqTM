Require Import TM.Prelim TM.TM TM.Code.Code TM.Code.CodeTM.
Require Import TM.Basic.Mono TM.Basic.Nop.
Require Import TM.Combinators.Match TM.Combinators.SequentialComposition.
Require Import TM.LiftMN.

Section FinTM1.
  Variable sig : finType.
  Variable f : sig -> sig.

  Definition UnaryFinTM : { M : mTM (sig^+) 1 & states M -> unit } :=
    MATCH (Read_char _)
          (fun r1 =>
             match r1 with
             | Some (inr r1') => Write (inr (f r1')) tt
             | _ => mono_Nop _ tt
             end).
  
  Lemma UnaryFinTM_Computes :
    UnaryFinTM ⊨c(3) Computes_Rel Fin.F1 Fin.F1 _ _ f.
  Proof.
    eapply RealiseIn_monotone.
    - unfold UnaryFinTM. eapply Match_RealiseIn.
      + eapply read_char_sem.
      + instantiate (2 := fun r1 => match r1 with Some (inr r1') => _ | _ => _ end).
        intros y. cbn in y. destruct y as [ [ | ] | ]; swap 1 2. cbn in *.
        * eapply Write_Sem.
        * eapply mono_Nop_Sem.
        * eapply mono_Nop_Sem.
    - cbn. omega.
    - hnf. intros tin (yout, tout) H x (r1&r2&H3&H4). hnf in H.
      destruct H as (y&t2&H1&H2). hnf in *. destruct y as [ [ | ] | ]; swap 1 2; hnf in *.
      + (* valid input *) destruct H1 as (H&H'). hnf in *. destruct H2 as (->&H2). subst.
        destruct_tapes. cbn in *. subst. cbn.
        pose proof tape_local_current_cons H4 as H4'; rewrite H4' in H; inv H; clear H4'.
        do 2 eexists. hnf; cbn. split; eauto. f_equal. eapply tape_local_right; eauto.
      + (* invalid input *) destruct H1 as (H&H'). hnf in *. destruct H2 as (->&->). subst. cbn in *.
        apply tape_local_current_cons in H4. destruct_tapes. cbn in *. congruence.
      + (* invalid input *) destruct H1 as (H&H'). hnf in *. destruct H2 as (->&->). subst. cbn in *.
        apply tape_local_current_cons in H4. destruct_tapes. cbn in *. congruence.
  Qed.
  
End FinTM1.

Section FinTM2.
  Variable sig : finType.
  Variable f : sig -> sig -> sig.

  Definition ReadAt1 : { M : mTM (sig^+) 2 & states M -> option (sig^+) } :=
    Inject (Read_char _) [| Fin.F1 |].

  Definition Nop2 : { M : mTM (sig^+) 2 & states M -> FinType (EqType unit) } := Nop 2 _ tt.

  Definition UnaryFinTM2 : sig -> { M : mTM (sig^+) 2 & states M -> unit } :=
    fun s : sig =>
      Inject (UnaryFinTM (f s)) [| Fin.FS (Fin.F1) |].

  Definition DualFinTM : { M : mTM (sig^+) 2 & states M -> unit } :=
    MATCH (ReadAt1)
          (fun r1 =>
             match r1 with
             | Some (inr r1') => UnaryFinTM2 r1'
             | _ => Nop2
             end).
  
  Lemma DualFinTM_Computes :
    DualFinTM ⊨c(5)
              Computes_Rel Fin.F1 Fin.F1 _ _ (@id sig) ∩
              Computes2_Rel (F := FinType (EqType unit)) Fin.F1 (Fin.FS Fin.F1) (Fin.FS Fin.F1) _ _ _ f.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold DualFinTM. eapply Match_RealiseIn.
      - unfold ReadAt1. cbn. eapply Inject_RealisesIn. vector_dupfree. eapply read_char_sem.
      - instantiate (2 := fun r1 => match r1 with Some (inl r1') => _ | _ => _ end).
        intros y. cbn in y. destruct y as [ [ | ] | ]; swap 1 2; cbn in *.
        + unfold UnaryFinTM2. eapply Inject_RealisesIn. vector_dupfree. eapply UnaryFinTM_Computes.
        + eapply RealiseIn_monotone'. eapply Nop_total. omega.
        + eapply RealiseIn_monotone'. eapply Nop_total. omega.
    }
    {
      cbn. omega.
    }
    {
      intros tapein (yout, tapeout) H. hnf in *.
      destruct H as (y1&t1&((H1&H2)&H3)&H4); hnf in *. subst.
      specialize (H3 (Fin.FS Fin.F1) ltac:(vector_not_in)). subst; cbn in *.
      destruct_tapes. cbn in *. inv H2; subst. split; hnf.
      {
        hnf. intros x. destruct_tapes. cbn. intros C1. destruct C1 as (r1&r2&C1&C1'). cbn in *.
        erewrite tape_local_current_cons in H4; eauto. cbn in *. hnf in H4. destruct H4 as (H4&H5). hnf in H4, H5.
        specialize (H5 Fin.F1 ltac:(vector_not_in)). cbn in H5. subst. repeat (hnf; econstructor; cbn); eauto.
      }
      {
        intros x y C1 C2. cbn in *.
        destruct C1 as (r1&r2&C1&C1'). destruct C2 as (r1'&r2'&C2&C2'). cbn in C1, C2, C1', C2'.
        erewrite tape_local_current_cons in H4; eauto.
        hnf in H4. cbn in H4. destruct H4 as (H4&H5). hnf in *. subst.
        specialize (H5 Fin.F1 ltac:(vector_not_in)). cbn in *. subst.
        specialize (H4 y ltac:(repeat (hnf; econstructor; cbn); eauto)). eauto.
      }
    }
  Qed.
  
End FinTM2.


Section FinTM2'.
  Variable sig : finType.
  Variable (f1 f2 : sig -> sig).

  Definition UnaryParallelTM := 
    Inject (UnaryFinTM f1) [|Fin.F1 (n := 1) |] ;;
    Inject (UnaryFinTM f2) [|Fin.FS Fin.F1   |].

  Lemma UnaryParallelTM_Computes :
    UnaryParallelTM ⊨c(7)
         Computes_Rel (F := FinType (EqType unit)) (Fin.F1       ) (Fin.F1       ) _ _ f1 ∩
         Computes_Rel (F := FinType (EqType unit)) (Fin.FS Fin.F1) (Fin.FS Fin.F1) _ _ f2.
  Proof.
    eapply RealiseIn_monotone.
    {
      unfold UnaryParallelTM. eapply Seq_RealiseIn.
      all: (eapply Inject_RealisesIn; [ vector_dupfree | eapply UnaryFinTM_Computes ]).
    }
    {
      cbn. omega.
    }
    {
      hnf. intros tin (yout&tout) H. hnf in *.
      destruct H as ((() & t') & (H1 & H2) & H3 & H4). hnf in H1, H2, H3, H4. destruct_tapes.
      split.
      {
        hnf. intros x HE1.
        specialize (H2 (Fin.FS Fin.F1) ltac:(vector_not_in)). specialize (H4 (Fin.F1) ltac:(vector_not_in)).
        cbn in *. subst. specialize (H1 _ HE1). congruence.
      }
      {
        hnf. intros y HE2.
        specialize (H2 (Fin.FS Fin.F1) ltac:(vector_not_in)). specialize (H4 (Fin.F1) ltac:(vector_not_in)).
        cbn in *. subst. specialize (H3 _ HE2). congruence.
      }
    }
  Qed.

End FinTM2'.