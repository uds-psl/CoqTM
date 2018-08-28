(** * Constructors and Deconstructors for Finite Types *)

Require Import ProgrammingTools.

Section MatchFin.

  Variable sig : finType.
  Hypothesis defSig : inhabitedC sig.

  Definition MatchFin : pTM sig^+ sig 1 :=
    Move R;;
    Match (ReadChar)
    (fun s => match s with
           | Some (inr x) => Return (Move R) x
           | _ => Return (Nop) default
           end).

  (** Note that [Encode_Finite] is not globally declared as an instance, because that would cause ambiguity. For example, [bool+bool] is finite, but we might want to encode it with [Encode_sum Encode_bool Encode_bool]. *)
  Local Existing Instance Encode_Finite.

  Definition MatchFin_Rel : pRel sig^+ sig 1 :=
    fun tin '(yout, tout) => forall x : sig, tin[@Fin0] ≃ x -> isRight tout[@Fin0] /\ yout = x.

  Lemma MatchFin_Sem : MatchFin ⊨c(5) MatchFin_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold MatchFin. TM_Correct. }
    { Unshelve. 4,8:reflexivity. all:omega. }
    {
      intros tin (yout, tout) H. intros x HEncX.
      destruct HEncX as (ls&HEncX).
      TMSimp. repeat econstructor.
    }
  Qed.

  (** There is no need for a constructor, just use [WriteValue] *)

End MatchFin.


Arguments MatchFin : simpl never.
Arguments MatchFin sig {_}. (** Default element is infered and inserted automatically *)



Ltac smpl_TM_MatchFin :=
  lazymatch goal with
  | [ |- MatchFin _ ⊨ _ ] => eapply RealiseIn_Realise; apply MatchFin_Sem
  | [ |- MatchFin _ ⊨c(_) _ ] => apply MatchFin_Sem
  | [ |- projT1 (MatchFin _) ↓ _ ] => eapply RealiseIn_TerminatesIn; apply MatchFin_Sem
  end.

Smpl Add smpl_TM_MatchFin : TM_Correct.