Require Import TM.TM TM.Basic.Mono TM.Combinators.SequentialComposition.

(*
Fixpoint stroverwrite (sig : Type) (str1 str2 : list sig) : list sig :=
  match str1, str2 with
  | str1, nil => str1
  | nil, str2 => str2
  | s1::str1', s2::str2' => s2 :: stroverwrite str1' str2'
  end.

  Lemma stroverwrite_nil (str1 : list sig) :
    stroverwrite str1 [] = str1.
  Proof. destruct str1; cbn; reflexivity. Qed.
*)

Section Write_String.

  Variable sig : finType.
  
  Fixpoint Write_String (l : list sig) : {M : mTM sig 0 & states M -> unit} :=
    match l with
    | [] => mono_Nop sig tt
    | e :: l0 => Write e ;; Move _ R ;; Write_String l0
    end.

  (*
  Fixpoint Tape_Write_String (t : tape sig) (str : list sig) :=
    match t, str with
    | t, nil => t
    | niltape _, s :: str' => Tape_Write_String (rightof s []) str'
    | leftof l rs, s :: str' => Tape_Write_String (midtape [s] l rs) str'
    | midtape ls m nil, s :: str' => Tape_Write_String (rightof s ls) str'
    | midtape ls m (r :: rs), s :: str' => Tape_Write_String (midtape (s :: ls) r rs) str'
    | rightof r ls, s :: str' => Tape_Write_String (rightof s (r :: ls)) str'
    end.
   *)

  Fixpoint Tape_Write_String (t : tape sig) (str : list sig) :=
    match str with
    | nil => t
    | s :: str' => Tape_Write_String (tape_move_mono t (Some s, R)) str'
    end.
  
  
  Lemma Tape_Write_String_nil (t : tape sig) :
    Tape_Write_String t nil = t.
  Proof. destruct t; cbn; auto. Qed.

(*
End write_string.
Section Test.
  Inductive Digit := zero | one | two | three | four | five | six | seven | eight | nine.
  Instance digit_eq : eq_dec Digit.
  Proof. unfold dec. intros x y. decide equality. Defined.
  Instance digit_fin : finTypeC (EqType Digit).
  Proof.
    apply FinTypeC with (enum := [zero; one; two; three; four; five; six; seven; eight; nine]).
    intros. destruct x; cbn; reflexivity.
  Defined.
  Compute Tape_Write_String (rightof three [two; one]) [].
  Compute Tape_Write_String (rightof two [one]) [three].
  Compute Tape_Write_String (rightof one []) [two; three].
  Compute Tape_Write_String (niltape _) [zero; one; two].
  Compute Tape_Write_String (niltape _) [zero; one].
  Compute Tape_Write_String (niltape _) [zero].
  Compute Tape_Write_String (midtape [zero;one] two [three;four;five]) [].
  Compute Tape_Write_String (midtape [zero;one] two [three;four;five]) [six].
  Compute Tape_Write_String (midtape [zero;one] two [three;four;five]) [six;seven].
  Compute Tape_Write_String (midtape [zero;one] two [three;four;five]) [six;seven;eight].
  Compute Tape_Write_String (midtape [zero;one] two [three;four;five]) [six;seven;eight;nine].
End Test.
*)

  Fixpoint Write_string_sem_fix (str : list sig) : Rel (tapes sig 1) (unit * tapes sig 1) :=
    match str with
    | nil => mono_Nop_R tt
    | s :: str' => Write_R s ∘ hideParam (Move_R R ∘ hideParam (Write_string_sem_fix str'))
    end.
    
  Lemma Write_string_fix_Sem (str : list sig) :
    Write_String str ⊨(4 * |str|) (Write_string_sem_fix str).
  Proof.
    induction str.
    - cbn. apply mono_Nop_Sem.
    - cbn.
      replace (S ((| str |) + S ((| str |) + S ((| str |) + S ((| str |) + 0)))))
        with (1 + 1 + (1 + 1 + (4 * (|str|)))); [ | cbn; omega].
      apply Seq_total.
      + apply Write_Sem.
      + apply Seq_total.
        * apply Move_Sem.
        * apply IHstr.
  Qed.
  
  Definition Write_String_R str :=
    Mono.Mk_R_p (F := FinType (EqType unit))
                (ignoreParam (fun (t t' : tape sig) => t' = Tape_Write_String t str)).

  Lemma Write_string_Sem str :
    Write_String str ⊨(4 * |str|) (Write_String_R str).
  Proof.
    eapply RealiseIn_monotone with (k1 := 4 * (|str|)); [now apply Write_string_fix_Sem | omega | ]. 
    induction str.
    - hnf. intros x ([], y) (H1 & H2). hnf in *. subst. now rewrite Tape_Write_String_nil.
    - intros t1 ([], t2) (([]&t3)&H1&((b&t4)&H2&H3)). hnf in H1, H2, H3. destruct_tapes. cbn in H1, H2, H3. cbn. subst.
      specialize (IHstr _ _ H3). clear H3. cbn in IHstr. hnf in IHstr. hnf. subst.
      destruct b.
      + destruct H2 as (H2&(c&H2')). cbn in H2, H2'. injection H2'. intros ->. clear H2'. subst.
        destruct h eqn:E1, str eqn:E2; cbn; auto.
      + destruct H2 as (H2&_). cbn in H2. congruence.
  Qed.

End Write_String.