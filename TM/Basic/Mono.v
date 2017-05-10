Require Import Basic.

Section test_char.

  Variable sig : finType.
  Variable tapes_no : nat.

  Variable on_tape : nat.
  Hypothesis is_a_tape : on_tape < S tapes_no.
  
  Variable f : sig -> bool.

  Definition states := Fin.t 3.
  Definition tc_start : states := Fin.F1.
  Definition tc_true : states := Fin.FS (Fin.F1).
  Definition tc_false: states := Fin.FS (Fin.FS (Fin.F1)).

  Definition test_chr :=
    one_tape is_a_tape (fun s c => (match c with Some e => if f e then tc_true else tc_false | None => tc_false end , (None, TM.N) )) tc_start (fun x => negb (Fin.eqb x tc_start)).
  
  Lemma test_chr_sem :
    test_chr ⊨(fun x : states => Fin.eqb x tc_true,1)
             ⇑[is_a_tape] (if? (@IdR _ ∩ (fun t t' => exists c, current t = Some c /\ f c = true)) ! (@IdR _ ∩ ((fun t t' => current t = None) ∪ (fun t t' => exists c, current t = Some c /\ f c = false)))).
 Proof.
    intros t.
    destruct (current (get_at is_a_tape t)) eqn:E.
    destruct (f e) eqn:Ef.
    - exists (mk_mconfig tc_true t). simpl_TM.
      now rewrite E, Ef.
    - exists (mk_mconfig tc_false t). simpl_TM. rewrite E, Ef. reflexivity. firstorder.
    - exists (mk_mconfig tc_false t). simpl_TM. rewrite E. reflexivity. firstorder.
  Qed.

  Definition Test_chr := (test_chr ; fun x : states => Fin.eqb x tc_true).                            

End test_char.

Section write.

  Variable sig : finType.
  Variable tapes_no : nat.

  Variable on_tape : nat.
  Hypothesis is_a_tape : on_tape < S tapes_no.

  Variable c : sig.

  Definition w_start : states := Fin.F1.
  Definition w_halt : states := Fin.FS (Fin.F1).

  Definition write_trans (p : states * Vector.t (option sig) (S tapes_no)) : states * Vector.t (option sig * move) (S tapes_no) := (w_halt, do_on_tape is_a_tape (Some c, TM.N)).

  Definition write : mTM sig tapes_no :=
    Build_mTM write_trans w_start (fun x => negb (Fin.eqb x w_start)).

  Definition Write := (write ; fun x : states => tt).

  Lemma write_sem :
    Write ⊨(1) ⇑[is_a_tape] ignoreParam (fun t t' => t' = midtape (left t) c (right t)).
  Proof.
    intros t.
    exists (mk_mconfig w_halt (tape_move_multi t (do_on_tape is_a_tape (Some c, TM.N)))).
    simpl_TM.
  Qed.

End write.

Section move.

  Variable sig : finType.
  Variable tapes_no : nat.

  Variable on_tape : nat.
  Hypothesis is_a_tape : on_tape < S tapes_no.

  Variable D : TM.move.

  Definition m_start : states := Fin.F1.
  Definition m_true : states := Fin.FS (Fin.F1).
  Definition m_false : states := Fin.FS (Fin.FS (Fin.F1)).

  Definition move_trans : states -> option sig -> states * (option sig * move) :=
    fun s p => match p with None => (m_false, (None, TM.N)) | Some c => (m_true, (None, D)) end.
  
  Definition moveM : mTM sig tapes_no :=
    one_tape is_a_tape move_trans m_start (fun x => negb (Fin.eqb x m_start)).

  Definition Move := (moveM; (fun x : states => Fin.eqb x m_true)).
  
  Definition MoveR :=  (
                         if? (fun (t t' : tape sig) => t' = tape_move_mono t (None, D) /\ exists c, current t = Some c)
                           ! ( (fun t t' => current t = None)) ∩ @IdR _ ).

  Lemma move_sem :
    Move ⊨(1) ⇑[is_a_tape] MoveR.
  Proof.
    unfold MoveR.
    eapply RealiseIn_strengthen.
    eapply one_tape_sem.

    intros t.
    destruct (current (get_at is_a_tape t)) eqn:E.
    - exists (mk_mconfig m_true (tape_move_multi t (do_on_tape is_a_tape (None, D)))).
      simpl_TM. rewrite E. reflexivity.
    - exists (mk_mconfig m_false t).
      simpl_TM. rewrite E. simpl_TM.
  Qed.

End move.

Section test_null.
  
  Variable tapes_no : nat.
  Variable sig : finType.
  
  Variable on_tape : nat.
  Hypothesis is_a_tape : on_tape < S tapes_no.

  Definition test_null := test_chr is_a_tape (fun _ : sig => true).
  
  Lemma test_null_sem :
    test_null ⊨(fun x : states => Fin.eqb x tc_true,1)
              (fun t p =>
                 let (b, t') := p in
                 t = t' /\
                 ( (current (get_at is_a_tape t) = None /\ b = false) \/
                   exists c : sig, current (get_at is_a_tape t) = Some c /\ b = true)).
  Proof.
    intros t.
    destruct (current (get_at is_a_tape t)) eqn:E.
    - exists (mk_mconfig tc_true t).
      simpl_TM. now rewrite E.
    - exists (mk_mconfig tc_false t). simpl_TM. now rewrite E.
  Qed.

  Definition Test_null := ( test_null ; fun x : states => Fin.eqb x tc_true).

End test_null.

Section read_char.

  Variable tapes_no : nat.
  Variable sig : finType.
  
  Variable on_tape : nat.
  Hypothesis is_a_tape : on_tape < S tapes_no.
  
  Definition rc_states : finType := FinType (EqType ((bool + sig)%type)).

  Definition read_char : mTM sig tapes_no :=
    one_tape is_a_tape (fun _ sym => match sym with None => (inl false, (None, TM.N)) | Some c => (inr c, (None,TM.N)) end) (inl true) (fun s => match s with inl true => false | _ => true end).

  Definition read_char_R :=
    (fun (t : tape sig) '(s,t') => s = current t) ∩ ignoreParam (@IdR _).

  Definition Read_char := (read_char; fun s : rc_states => match s with inl _ => None | inr s => Some s end).

  Lemma read_char_sem :
    Read_char ⊨(1) ⇑[is_a_tape] read_char_R.
  Proof.
    intros t.
    destruct (current (get_at is_a_tape t)) eqn:E.
    - exists (mk_mconfig (inr e) t).
      simpl_TM. rewrite E. simpl_TM.
    - exists (mk_mconfig (inl false) t).
      simpl_TM. rewrite E. simpl_TM.
  Qed.

End read_char.
