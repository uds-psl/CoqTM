Require Import TM.Prelim TM.TM.
Require Import TM.Basic.Mono.
Require Import TM.Combinators.Match TM.Combinators.SequentialComposition.


Section Peek.

  Variable sig : finType.
  Variable F : finType.
  Variable f : sig -> F.

  Definition peek_state := FinType (EqType (option (F + move))) % type.
  Definition peek_start : peek_state := None.
  Definition peek_Some (y : F) : peek_state := Some (inl y).
  Definition peek_None (d : move) : peek_state := Some (inr d).


  Definition Peek : { M : mTM sig 1 & states M -> F + move } :=
    MATCH (Read_char _)
          (fun r1 =>
             match r1 with
             | Some r1' => mono_Nop sig (inl (f r1'))
             | None =>
               Move sig L tt ;;
                    MATCH (Read_char _)
                    (fun r2 =>
                       match r2 with
                       | Some r2' => Move sig R (inr R)
                       | None =>
                         Move sig R tt ;;
                              MATCH (Read_char _)
                              (fun r3 =>
                                 match r3 with
                                 | Some r3' => Move sig L (inr L)
                                 | None => mono_Nop sig (inr N)
                                 end)
                       end)
             end).

  Definition Peek_Rel : Rel (tapes sig 1) (FinType(EqType(F + move)) * tapes sig 1) :=
    Mk_R_p (fun tin '(y, tout) => tin = tout /\
                               match tin with
                               | niltape _ => y = inr N
                               | leftof _ _ => y = inr L
                               | rightof _ _ => y = inr R
                               | midtape _ m _ => y = inl (f m)
                               end).

  Definition Peek_Steps := 11.

  Lemma Peek_RealisesIn :
    Peek ⊨c(Peek_Steps) Peek_Rel.
  Proof.
    unfold Peek_Steps. eapply RealiseIn_monotone.
    - unfold Peek. eapply Match_RealiseIn.
      {
        eapply read_char_sem.
      }
      {
        intros r1. cbn in r1. instantiate (2 := fun (b : option sig) => match b with Some r1' => _ | None => _ end).
        destruct r1 as [ r1' | ].
        {
          eapply RealiseIn_monotone. eapply mono_Nop_Sem. omega. intros x y H. apply H.
        }
        {
          eapply Seq_RealiseIn.
          {
            eapply Move_Sem.
          }
          {
            eapply Match_RealiseIn.
            {
              eapply read_char_sem.
            }
            {
              intros r2. cbn in r2. instantiate (2 := fun (b : option sig) => match b with Some r2' => _ | None => _ end).
              destruct r2 as [ r2' | ].
              {
                eapply RealiseIn_monotone. eapply Move_Sem. shelve. intros x y H. apply H.
              }
              {
                eapply Seq_RealiseIn.
                {
                  eapply Move_Sem.
                }
                {
                  eapply Match_RealiseIn.
                  {
                    eapply read_char_sem.
                  }
                  {
                    intros r3. cbn in r3. instantiate (2 := fun (b : option sig) => match b with Some r3' => _ | None => _ end).
                    destruct r3 as [ r3' | ].
                    {
                      eapply Move_Sem.
                    }
                    {
                      eapply RealiseIn_monotone. eapply mono_Nop_Sem. omega. intros x y H. apply H.
                    }
                  }
                }
              }
            }
          }
        }
      }
    - Unshelve. all: (cbn; omega).
    - hnf. intros tin (yout&tout). intros H. hnf in H. destruct H as (r1&t1&(He&He')&H2); hnf in *; subst.
      destruct (current _) eqn:E1; hnf in *.
      {
        destruct H2 as (->&->). split; auto. destruct (tout[@Fin.F1]); cbn in *; congruence.
      }
      {
        destruct H2 as ((u1&t2)&H2&H3); hnf in *. destruct H2 as (->&H2); hnf in *; subst.
        destruct H3 as (r1&H3); hnf in *. destruct H3 as (t3&(He&He')&H4); hnf in *; subst.
        destruct (current (t3[@Fin.F1])) eqn:E2; hnf in *.
        {
          destruct H4 as (->&->). rewrite H2 in *. destruct (t1[@Fin.F1]); cbn in *; split; auto; congruence.
        }
        {
          destruct H4 as ((u1&t2)&H4&H5); hnf in *. destruct H4 as (->&H4); hnf in *; subst.
          destruct H5 as (r2&H5); hnf in *. destruct H5 as (t4&(He&He')&H5); hnf in *; subst.
          destruct (current (t4[@Fin.F1])) eqn:E3; hnf in *.
          {
            destruct H5 as (->&H5). rewrite H2,H4,H5 in *. destruct (t1[@Fin.F1]); cbn in *; split; auto; congruence.
          }
          {
            destruct H5 as (->&->). rewrite H2, H4 in *. destruct (t1[@Fin.F1]); cbn in *; split; auto; congruence.
          }
        }
      }
  Qed.

End Peek.
