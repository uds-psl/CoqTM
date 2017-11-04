Require Import TM.TM.

Open Scope vector_scope.

Definition threeStates := FinType (EqType (Fin.t 3)).
Definition fourStates := FinType (EqType (Fin.t 4)).

Section Mk_Mono.
  Variable (sig states : finType).
  Variable mono_trans : states -> option sig -> states * (option sig * move).
  Variable (init : states) (fin : states -> bool).

  Definition Mk_Mono_TM : mTM sig 1.
  Proof.
    split with (states := states).
    - intros (q&tape).
      pose proof (mono_trans q (tape[@Fin.F1])) as (q', act).
      apply (q', [| act |]).
    - apply init.
    - apply fin.
  Defined.

  Variable (F : finType) (R : Rel (tape sig) (F * tape sig)).
  
  Definition Mk_R_p : Rel (tapes sig 1) (F * tapes sig 1) :=
      fun tps1 '(p, tps2) => R (tps1[@Fin.F1]) (p, tps2[@Fin.F1]).

End Mk_Mono.

Section test_char.

  Variable sig : finType.
  Variable f : sig -> bool.

  Definition tc_start : fourStates := Fin.F1.
  Definition tc_true  : fourStates := Fin.FS (Fin.F1).
  Definition tc_false : fourStates := Fin.FS (Fin.FS (Fin.F1)).
  Definition tc_None  : fourStates := Fin.FS (Fin.FS (Fin.FS Fin.F1)).

  Definition Test_Char_TM :=
    Mk_Mono_TM (states := fourStates)
      (fun s c => (match c with Some e => if f e then tc_true else tc_false | None => tc_None end , (None, TM.N) ))
      tc_start (fun x => negb (Fin.eqb x tc_start)).

  Definition Test_Char_p : fourStates -> option bool :=
    fun x => if Fin.eqb x tc_true then Some true else
            if Fin.eqb x tc_false then Some false else
              None.

  Definition TEST_CHAR := (Test_Char_TM; Test_Char_p).

  Lemma test_chr_Sem :
    TEST_CHAR ⊨c(1)
                 Mk_R_p
                 (ignoreParam (@IdR _) ∩
                              (fun (t : tape sig) (Y : option bool * tape sig) =>
                                 match Y with
                                   (Some b, t2) => exists c, current t = Some c /\ f c = b
                                 | (None, t2) => current t = None
                                 end
                              )
                 ).
  Proof.
    hnf. intros intapes. destruct_tapes. cbn.
    destruct (current h) eqn:E; cbn.
    - destruct (f e) eqn:Ef; cbn.
      + exists (mk_mconfig tc_true  [| h |]). cbn in *. repeat split; hnf; eauto.
      + exists (mk_mconfig tc_false [| h |]). cbn in *. repeat split; hnf; eauto.
    - exists (mk_mconfig tc_None [| h |]). cbn in *. repeat split; hnf; eauto.
  Qed.

End test_char.


Section Write.

  Variable sig : finType.
  Variable c : sig.
  Variable (F : finType) (f : F).

  Definition Write_TM : mTM sig 1.
  Proof.
    apply Mk_Mono_TM with (states := FinType (EqType bool)).
    - intros [ | ] _.
      + (* final state *)
        apply (true, (None, N)).
      + (* write c *)
        apply (true, (Some c, N)).
    - apply false.
    - apply id.
  Defined.
  
  Definition Write := (Write_TM; fun _ => f).

  Definition Write_R :=
    Mk_R_p (F := F)
           (fun t '(y, t') => y = f /\ t' = midtape (left t) c (right t)).

  Lemma Write_Sem :
    Write ⊨c(1) Write_R.
  Proof.
    intros t. destruct_tapes. cbn in *. eauto.
  Qed.

End Write.

Section Move.

  Variable sig : finType.
  Variable D : TM.move.
  Variable (F : finType) (f : F).

  Definition move_trans : bool -> option sig -> bool * (option sig * move) := fun _ _ => (true, (None, D)).
  
  Definition Move_TM : mTM sig 1 :=
    Mk_Mono_TM move_trans false (fun q => q).

  Definition Move := (Move_TM; (fun x => f)).

  Definition isLeftOf  (t : tape sig) := match t with leftof  _ _ =>  True | _ => False end.
  Definition isRightOf (t : tape sig) := match t with rightof _ _ => True  | _ => False end.
  Definition isNiltape (t : tape sig) := match t with niltape _ =>   True  | _ => False end.
  
  Definition Move_R :=
    Mk_R_p (F := F)
           (fun t '(y, t') => y = f /\ t' = tape_move (sig := sig) t D).
  
  Lemma Move_Sem :
    Move ⊨c(1) Move_R.
  Proof.
    unfold Mk_R_p, Move_R. hnf. intros tapes. destruct_tapes. cbn in *. eauto.
  Qed.

End Move.

(*
Section test_null.
  
  Variable tapes_no : nat.
  Variable sig : finType.
  
  Variable on_tape : nat.
  Hypothesis is_a_tape : on_tape < S tapes_no.

  Definition test_null := test_chr is_a_tape (fun _ : sig => true).
  
  Lemma test_null_sem :
    test_null ⊨(fun x : threeStates => Fin.eqb x tc_true,1)
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

  Definition Test_null := ( test_null ; fun x : threeStates => Fin.eqb x tc_true).

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
*)

Section Mono_Nop.

  Variable sig : finType.

  Definition mono_nop_trans : unit -> option sig -> unit * (option sig * move) :=
    fun u s => (u, (None, N)).

  Definition mono_nop : mTM sig 1 := Mk_Mono_TM mono_nop_trans tt (fun _ => true).

  Variable F : finType.
  Variable f : F.

  Definition mono_Nop := (mono_nop; fun _ => f).

  Definition mono_Nop_R := (fun (t : tapes sig 1) '(y, t') => y = f /\ t = t').

  Lemma mono_Nop_Sem: mono_Nop ⊨c(0) mono_Nop_R.
  Proof.
    intros ?. exists (initc mono_nop input). cbn. firstorder.
  Qed.

End Mono_Nop.