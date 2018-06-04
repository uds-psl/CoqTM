(** * Matching and constructors for finite types *)

Require Import CodeTM.
Require Import TM.Basic.Mono.
Require Import TM.Combinators.Combinators.

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
           | Some (inr x) => Move L x
           | _ => mono_Nop default
           end).

  Definition MatchFin_Rel : pRel sig^+ sig 1 :=
    fun tin '(yout, tout) => forall x : sig, tin[@Fin0] ≃ x -> tout[@Fin0]≃x /\ yout = x.

  Lemma MatchFin_Sem : MatchFin ⊨c(5) MatchFin_Rel.
  Proof.
    eapply RealiseIn_monotone.
    { unfold MatchFin. repeat TM_Correct. }
    { Unshelve. 4,8:reflexivity. all:omega. }
    {
      intros tin (yout, tout) H. intros x HEncX.
      destruct HEncX as (ls&HEncX); TMSimp.
      repeat econstructor.
    }
  Qed.


  (** There is no need for a constructor, just use [WriteValue] *)

End MatchFin.


Arguments MatchFin : simpl never.
Arguments MatchFin sig {_}. (* Default element is infered automatically *)