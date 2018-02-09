Require Import TM.Prelim TM.TM.
Require Import TM.Basic.Mono.
Require Import TM.Combinators.Combinators.
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


  Lemma Peek_RealisesIn :
    Peek ⊨c(Peek_Steps) Peek_Rel.
  Proof.
    unfold Peek_Steps. eapply RealiseIn_monotone.
    - unfold Peek. repeat TM_Correct.
    - Unshelve. 6,9: constructor 1. all: cbn. all: try omega. 4-7: constructor. cbn. constructor.
    - TMCrush; TMSolve 1.
  Qed.

End Peek.
