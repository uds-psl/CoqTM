Require Import TM.TM TM.Basic.Mono TM.Combinators.SequentialComposition.
Require Import List.

Section Write_String.

  Variable sig : finType.
  Variable D : move.
  Variable (F : finType) (f : F).

  Fixpoint Write_String (l : list sig) : {M : mTM sig 1 & states M -> F} :=
    match l with
    | [] => mono_Nop sig f
    | x :: xs => Write x tt ;; Move _ D tt ;; Write_String xs
    end.

  Fixpoint Tape_Write_String (t : tape sig) (str : list sig) :=
    match str with
    | nil => t
    | s :: str' => Tape_Write_String (tape_move_mono t (Some s, D)) str'
    end.
  
  Lemma Tape_Write_String_nil (t : tape sig) :
    Tape_Write_String t nil = t.
  Proof. destruct t; cbn; auto. Qed.

  Fixpoint Write_string_sem_fix (str : list sig) : Rel (tapes sig 1) (F * tapes sig 1) :=
    match str with
    | nil => mono_Nop_R f
    | s :: str' => Write_R s tt ∘ hideParam (Move_R D tt ∘ hideParam (Write_string_sem_fix str'))
    end.
    
  Lemma Write_string_fix_Sem (str : list sig) :
    Write_String str ⊨c(4 * |str|) (Write_string_sem_fix str).
  Proof.
    induction str.
    - cbn. apply mono_Nop_Sem.
    - cbn.
      replace (S ((| str |) + S ((| str |) + S ((| str |) + S ((| str |) + 0)))))
        with (1 + 1 + (1 + 1 + (4 * (|str|)))); [ | cbn; omega].
      apply Seq_RealiseIn.
      + apply Write_Sem.
      + apply Seq_RealiseIn.
        * apply Move_Sem.
        * apply IHstr.
  Qed.
  
  Definition Write_String_R str :=
    Mono.Mk_R_p (fun tin '(yout, tout) => tout = Tape_Write_String tin str /\ yout = f).
  Lemma Write_string_Sem str :
    Write_String str ⊨c(4 * |str|) (Write_String_R str).
  Proof.
    eapply RealiseIn_monotone with (k1 := 4 * (|str|)); [now apply Write_string_fix_Sem | omega | ]. 
    induction str.
    - hnf. intros x (f', y) (H1 & H2). hnf in *. subst. now rewrite Tape_Write_String_nil.
    - intros t1 (f', t2) (([]&t3)&H1&((b&t4)&H2&H3)). hnf in *. destruct H1 as [_ H1]. destruct H2 as [_ H2]. hnf in *.
      destruct_tapes. cbn in *. cbn. subst. specialize (IHstr _ _ H3). clear H3. cbn in IHstr. hnf in IHstr. auto.
  Qed.

End Write_String.