Require Import TM.Prelim TM.TM.
Require Import TM.Basic.Mono.
Require Import TM.Combinators.Combinators.
Require Import TM.Compound.TMTac.


Section Peek.

  Variable sig : finType.
  Variable F : finType.
  Variable f : sig -> F.

  Definition Peek : { M : mTM sig 1 & states M -> F + move } :=
    MATCH (Read_char)
          (fun r1 =>
             match r1 with
             | Some r1' => mono_Nop (inl (f r1'))
             | None =>
               Move L tt ;;
                    MATCH (Read_char)
                    (fun r2 =>
                       match r2 with
                       | Some r2' => Move R (inr R)
                       | None =>
                         Move R tt ;;
                              MATCH (Read_char)
                              (fun r3 =>
                                 match r3 with
                                 | Some r3' => Move L (inr L)
                                 | None => mono_Nop (inr N)
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
    - unfold Peek. repeat TM_Correct.
    - Unshelve. 6,9: constructor 1. all: cbn. all: try omega. 4-7: constructor. cbn. constructor.
    - intros tin (yout,tout) H. now TMCrush; TMSolve 1.
      (*
      Undo.
      TMSimp. destruct (current _) eqn:E1.
      + TMCrush; TMSolve 1.
      + TMSimp. destruct (current (tape_move_left _)) eqn:E2.
        * TMCrush; TMSolve 1.
        * TMSimp.
          destruct (current (tape_move_right (tape_move_left _))) eqn:E3.
          -- TMCrush; TMSolve 1.
          -- TMSimp idtac. destruct (tmid[@_]) eqn:E4; TMCrush; TMSolve 1.
       *)
  Qed.

End Peek.