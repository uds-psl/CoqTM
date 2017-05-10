Require Import TM Relations Shared.FiniteTypes Nop If TM.Combinators.Combinators Basic.Basic Basic.Mono Basic.Multi Fin.

Section Injective.
  Variable (X Y : Type).

  Definition injective (f : X -> Y) := forall (x x' : X), f x = f x' -> x = x'.
  Definition injection_inverse (f : X -> Y) (f' : Y -> option X) :=
    forall y : Y, match (f' y) with Some x => f x = y | None => forall x : X, f x <> y end.
  
  Record injection := Injection
  {
    f :> X -> Y;
    f_injective : injective f;
    f' : Y -> option X;
    f'_inversion : injection_inverse f f'
  }.

End Injective.

Module Test.
  Definition f x := x + 2.

  Lemma f_injective : injective f.
  Proof.
    intros x x'. unfold f. omega.
  Qed.

  Definition f' (y : nat) : option nat.
  Proof.
    decide (y < 2).
    - exact None.
    - exact (Some (y - 2)).
  Defined.

  Lemma f'_inversion : injection_inverse f f'.
  Proof.
    intros y. unfold f'.
    decide (y < 2).
    - intros x. unfold f. omega.
    - unfold f. omega.
  Qed.

  Definition f_injection := @Injection nat nat f f_injective f' f'_inversion.
  
End Test.

  
Section ReduceInjVect.
  Variable X : Type.
  Variable n m : nat.
  Variable inj : injection (Fin.t (S n)) (Fin.t (S (n+m))).

  Definition reduce_inj_vect (vect : Vector.t X (S (n+m))) : Vector.t X (S n).
  Proof.
    pose proof List.seq 0 n as seq. (* [0, ..., n-1] *)
  Admitted.
  
End ReduceInjVect.


Section LiftSigma.
  Variable num_tapes : nat.
  Variable (sigma sigma' : finType).
  Hypothesis inj : injection sigma sigma'.
  Variable A : mTM sigma num_tapes.

  Definition lift_sigma : mTM sigma' num_tapes.  
  Proof.
    destruct A as [states trans start halt], inj as [f f_inj f' f_inv].
    apply (Build_mTM (states := states)).
    - intros (q & vect).
      pose proof Vector.map (fun x => match x with Some y => f' y | None => None end) vect as vect'.
      pose proof trans (q, vect') as (q', actvect').
      pose proof (Vector.map
                    (fun (act : option sigma * move) =>
                       let (s, move) := act in
                       ((match s with Some y => Some (inj y) | None => None end), move))
                    actvect') as actvect.
      exact (q, actvect).
    - exact start.
    - exact halt.
  Defined.

End LiftSigma.


Section LiftNumTapes.
  Variable n m : nat.
  Variable inj : injection (Fin.t (S n)) (Fin.t (S (n+m))).
  Variable sigma : finType.
  Variable A : mTM sigma n.

  Definition lift_tapes : mTM sigma (n+m).
  Proof.
    destruct A as [states trans start halt], inj as [f f_inj f' f_inv].
    apply (Build_mTM (states := states)).
    - intros (q & vect).
      pose proof (reduce_inj_vect inj vect) as vect'.
      pose proof trans (q, vect') as (q', actvect').
      admit.
    - exact start.
    - exact halt.
  Admitted.


End LiftNumTapes.