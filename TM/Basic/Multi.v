Require Import TM.Prelim.
Require Import TM.TM.
Require Import TM.Basic.Mono.
Require Import TM.LiftMN.


(* n-tape versions of the machines from TM.Basic.Mono *)

Section Write.

  Variable sig : finType.
  Variable c : sig.
  Variable (F : finType) (f : F).
  Variable (n : nat) (k : Fin.t n).

  Definition Write_multi : { M : mTM sig n & states M -> F} :=
    Inject (Write c f) [|k|].
    
  Definition Write_multi_R : Rel (tapes sig n) (F * tapes sig n) :=
    (fun t '(y, t') => y = f /\ t'[@k] = midtape (left t[@k]) c (right t[@k])).

  Lemma Write_multi_Sem :
    Write_multi ⊨c(1) Write_multi_R.
  Proof.
    eapply RealiseIn_monotone. eapply Inject_RealisesIn. vector_dupfree. eapply Write_Sem. omega.
    hnf. intros tin (yout,tout) (H1&H2); hnf in *. intuition.
  Qed.

End Write.

Section Move.

  Variable sig : finType.
  Variable D : TM.move.
  Variable (F : finType) (f : F).
  Variable (n : nat) (k : Fin.t n).

  Definition Move_multi : { M : mTM sig n & states M -> F} :=
    Inject (Move _ D f) [|k|].

  Definition Move_multi_R : Rel (tapes sig n) (F * tapes sig n) :=
    (fun t '(y, t') => y = f /\ t'[@k] = tape_move (sig := sig) t[@k] D).
  
  Lemma Move_multi_Sem :
    Move_multi ⊨c(1) Move_multi_R.
  Proof.
    eapply RealiseIn_monotone. eapply Inject_RealisesIn. vector_dupfree. eapply Move_Sem. omega.
    hnf. intros tin (yout,tout) (H1&H2); hnf in *. intuition.
  Qed.

End Move.

Section ReadChar.

  Variable sig : finType.
  Variable (n : nat) (k : Fin.t n).

  Definition ReadChar_multi : { M : mTM sig n & states M -> option sig} :=
    Inject (Read_char _) [|k|].

  Definition ReadChar_multi_R  : Rel (tapes sig n) (option sig * tapes sig n) :=
    (fun (t : tapes sig n) '(s,t') => s = current t[@k]) ∩ ignoreParam (@IdR _).

  Lemma ReadChar_multi_Sem :
    ReadChar_multi ⊨c(1) ReadChar_multi_R.
  Proof.
    eapply RealiseIn_monotone. eapply Inject_RealisesIn. vector_dupfree. eapply read_char_sem. omega.
    hnf. intros tin (yout,tout) (H1&H2); hnf in *. intuition. hnf in *. cbn in *.
    eapply VectorSpec.eq_nth_iff. intros p ? <-.
    decide (p = k) as [->|d].
    - now inv H0.
    - eapply H2. vector_not_in. tauto.
  Qed.

End ReadChar.