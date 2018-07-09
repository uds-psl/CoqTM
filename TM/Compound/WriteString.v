Require Import TM.TM TM.Basic.Mono TM.Combinators.Combinators TM.Compound.Multi.
Require Import List.
Require Import TMTac.

(* Useful for runtime stuff *)
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.


(** The correctness and definition of [WriteString] is uncommon, because it is defined (and verified) by recursion (or induction) over the string *)
Section Write_String.

  Variable sig : finType.
  Variable D : move.

  Fixpoint WriteString (l : list sig) : pTM sig unit 1 :=
    match l with
    | [] => Nop
    | x :: xs => WriteMove x D;; WriteString xs
    end.

  Fixpoint WriteString_Fun (sig' : Type) (t : tape sig') (str : list sig') :=
    match str with
    | nil => t
    | s :: str' => WriteString_Fun (tape_move_mono t (Some s, D)) str'
    end.
  
  Lemma Write_String_nil (sig' : Type) (t : tape sig') :
    WriteString_Fun t nil = t.
  Proof. destruct t; cbn; auto. Qed.

  Fixpoint WriteString_sem_fix (str : list sig) : pRel sig unit 1 :=
    match str with
    | nil => Nop_Rel
    | s :: str' =>
      WriteMove_Rel s D |_tt ∘ WriteString_sem_fix str'
    end.
    
  Lemma WriteString_fix_Sem (str : list sig) :
    WriteString str ⊨c(3 * |str|) (WriteString_sem_fix str).
  Proof.
    induction str; cbn; eapply RealiseIn_monotone; cbn.
    - repeat TM_Correct.
    - omega.
    - firstorder.
    - repeat TM_Correct.
    - omega.
    - intros tin (y, tout) H. TMSimp. exists tmid. repeat split; auto. 
  Qed.
  
  Definition WriteString_Rel str : Rel (tapes sig 1) (unit * tapes sig 1) :=
    Mono.Mk_R_p (ignoreParam (fun tin tout => tout = WriteString_Fun tin str)).

  Lemma WriteString_Sem str :
    WriteString str ⊨c(3 * |str|) (WriteString_Rel str).
  Proof.
    eapply RealiseIn_monotone with (k1 := 3 * (|str|)).
    - apply WriteString_fix_Sem.
    - reflexivity.
    - induction str as [ | s str' IH]; intros tin (yout, tout) H; cbn in *.
      + now TMSimp.
      + TMSimp; clear_trivial_eqs. hnf in IH. specialize IH with (1 := H0). now TMSimp.
  Qed.

End Write_String.

Arguments WriteString : simpl never.
Arguments WriteString_Rel {sig} (D) (str) x y/.