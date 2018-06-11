(** * Matching and constructors for finite types *)

Require Import ProgrammingTools.

Section MatchFin.

  Variable sig : finType.
  Hypothesis defSig : inhabitedC sig.

  (* This instance is not declared globally, because of overlaps *)
  Local Instance Encode_Fin : codable sig sig :=
    {|
      encode x := [x];
    |}.
  
  Definition MatchFin : pTM sig^+ sig 1 :=
    Move R tt;;
    MATCH (Read_char)
    (fun s => match s with
           | Some (inr x) => Move R x
           | _ => mono_Nop default
           end).

  Definition MatchFin_Rel : pRel sig^+ sig 1 :=
    fun tin '(yout, tout) => forall x : sig, tin[@Fin0] ≃ x -> isRight tout[@Fin0] /\ yout = x.

  Lemma MatchFin_Sem : MatchFin ⊨c(5) MatchFin_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold MatchFin. repeat TM_Correct. }
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
Arguments MatchFin sig {_}. (* Default element is infered automatically *)



Ltac smpl_TM_MatchFin :=
  match goal with
  | [ |- MatchFin _ ⊨ _ ] => eapply RealiseIn_Realise; apply MatchFin_Sem
  | [ |- MatchFin _ ⊨c(_) _ ] => apply MatchFin_Sem
  | [ |- projT1 (MatchFin _) ↓ _ ] => eapply RealiseIn_terminatesIn; apply MatchFin_Sem
  end.

Smpl Add smpl_TM_MatchFin : TM_Correct.