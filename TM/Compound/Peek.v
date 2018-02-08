Require Import TM.Prelim TM.TM.
Require Import TM.Basic.Mono.
Require Import TM.Combinators.Match TM.Combinators.SequentialComposition.
Require Import TM.Compound.TMTac.


Section Peek.

  Variable sig : finType.
  Variable F : finType.
  Variable f : sig -> F.

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



  Print Implicit Match_WRealise.

  Ltac destruct_refine :=
    match goal with [ |- ?H ] => idtac H end;
    destruct _; refine _.

  Ltac destruct_shelve e :=
    cbn in e;
    first
      [
        match type of e with
        | ?A + ?B =>
          destruct e as [?X | ?Y]; [destruct_shelve X | destruct_shelve Y]
        | option ?A =>
          destruct e as [?X | ]; [destruct_shelve X | shelve]
        end
      | shelve
      ].

  Ltac print_goal :=
    match goal with
    | [ |- ?H ] => idtac H
    end.

  Ltac print_type e := first [ let x := type of e in idtac x | idtac "Untyped:" e ].

  Ltac smpl_match_case_solve_RealiseIn :=
    eapply RealiseIn_monotone'; [smpl_RealiseIn | shelve].

  Ltac smpl_match_RealiseIn :=
      match goal with
      | [ |- MATCH ?M1 ?M2 ⊨c(?k1) ?R] =>
        is_evar R;
          let tM2 := type of M2 in
          match tM2 with
          | ?F -> _ =>
            eapply (Match_RealiseIn
                      (F := FinType(EqType F))
                      (R2 := ltac:(now (intros ?e; destruct_shelve e))));
              [
                try smpl_match_case_solve_RealiseIn
              | intros ?e; repeat destruct _; try smpl_match_case_solve_RealiseIn
              ]
          end
      end.

  Smpl Add smpl_match_RealiseIn : TM_RealiseIn.

  Lemma Peek_RealisesIn :
    Peek ⊨c(Peek_Steps) Peek_Rel.
  Proof.
    unfold Peek_Steps. eapply RealiseIn_monotone.
    {
      unfold Peek. smpl_RealiseIn.

      (* The automatic generated proof script could look like this: *)
      (*
      unfold Peek. eapply Match_RealiseIn.
      {
        eapply RealiseIn_monotone'. eapply read_char_sem. shelve.
      }
      {
        intros r1. cbn in r1. instantiate (2 := fun (b : option sig) => match b with Some r1' => _ | None => _ end).
        destruct r1 as [ r1' | ]; (eapply RealiseIn_monotone'; [ | shelve]).
        {
          eapply mono_Nop_Sem.
        }
        {
          eapply Seq_RealiseIn.
          {
            eapply Move_Sem.
          }
          {
            eapply Match_RealiseIn.
            {
              eapply RealiseIn_monotone'. eapply read_char_sem. shelve.
            }
            {
              intros r2. cbn in r2. instantiate (2 := fun (b : option sig) => match b with Some r2' => _ | None => _ end).
              destruct r2 as [ r2' | ]; (eapply RealiseIn_monotone'; [ | shelve]).
              {
                eapply RealiseIn_monotone'. eapply Move_Sem. shelve.
              }
              {
                eapply Seq_RealiseIn.
                {
                  eapply Move_Sem.
                }
                {
                  eapply Match_RealiseIn.
                  {
                    eapply RealiseIn_monotone'. eapply read_char_sem. shelve.
                  }
                  {
                    intros r3. cbn in *.
                    instantiate (2 := fun (b : option sig) => match b with Some r3' => _ | None => _ end).
                    destruct r3 as [ r3' | ]; (eapply RealiseIn_monotone'; [ | shelve]).
                    {
                      eapply Move_Sem.
                    }
                    {
                      eapply mono_Nop_Sem.
                    }
                  }
                }
              }
            }
          }
        }
      }
       *)
    }
    {
      (* We have some shelved goals... *)
      Unshelve.
      11-12: constructor 1. all: cbn.
      all: try omega.
      4-7: constructor 1.
      cbn. omega.
    }
    { (* The final proof is easy and can indeed be automated. *)
      TMCrush; TMSolve 1.
    }
  Qed.

End Peek.
