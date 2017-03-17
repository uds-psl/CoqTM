(** Loop Operator **)
Require Import Omega.

Module Loop.
  Section Loop.

    Inductive Result {X : Type} : Type :=
    | Complete   (x : X) : Result
    | Incomplete (x : X) : Result.

    Fixpoint iter {X : Type} (f : X -> X) (s : X) (n : nat) :=
      match n with
      | O    => s
      | S n' => iter f (f s) n'
      end.
    
    Fixpoint loop {X : Type} (f : X -> X) (p : X -> bool) (s : @Result X) n :=
      match s with
      | Complete _ => s
      | Incomplete s' =>
        match n with
        | O => s
        | S n' => if p s' then Complete s'
                 else loop f p (Incomplete (f s')) n'
        end
      end.

    (* Just for fun *)
    Definition loop_iter {X : Type} (f : X -> X) (p : X -> bool) :=
      fun t =>
        match t with
        | Incomplete s => if p s then Complete s
                         else Incomplete (f s)
        | Complete s => Complete s
        end.

    Lemma loop_loop_iter_Complete {X: Type} (f : X -> X) (s : X) (p : X -> bool) (n : nat) :
      iter (loop_iter f p) (Complete s) n = Complete s.
    Proof. induction n; cbn; auto. Qed.
    
    Lemma loop_loop_iter {X: Type} (f : X -> X) (s : @Result X) (p : X -> bool) (n : nat) :
      loop f p s n = iter (loop_iter f p) s n.
    Proof.
      revert s. induction n as [|n' IHn].
      - intros [s|s]; cbn; reflexivity.
      - intros [s|s].
        + cbn. now rewrite loop_loop_iter_Complete.
        + cbn. destruct (p s) eqn:E.
          * symmetry. apply loop_loop_iter_Complete.
          * auto.
    Qed.
    
    Lemma iter_S {X : Type} (f : X -> X) (s : X) (n : nat) :
      iter f s (S n) = f (iter f s n).
    Proof.
      revert s. induction n as [|n' IHn]; intros s; cbn; auto.
      rewrite <- IHn. reflexivity.
    Qed.

    Lemma loop_continue {X : Type} (f : X -> X) (s : @Result X) (p : X -> bool) (n m : nat) :
      loop f p s (n + m) = loop f p (loop f p s n) m.
    Proof.
      revert s m. induction n; intros [s|s] m; cbn; auto.
      - destruct m; reflexivity.
      - destruct (p s) eqn:H.
        + destruct m; reflexivity.
        + rewrite IHn. reflexivity.
    Qed.


    Lemma loop_completed {X: Type} (f : X -> X) (p : X -> bool) (s s' : X) (steps : nat) :
      loop f p (Incomplete s) steps = Complete s' -> p s' = true.
    Proof.
      revert s. induction steps as [|steps' IH]; intros s H; cbn in *; [congruence|].
      destruct (p s) eqn:H'; cbn in *.
      - injection H. intros ->. assumption.
      - now apply IH with (s := f s).
    Qed.
    
    (** Lifting **)

    Lemma loop_lift_strong {X Y : Type} (lift : X -> Y) (p : X -> bool) (lp : Y -> bool) (s : X)
          (f : X -> X) (g : Y -> Y) (numSteps : nat) :
      (forall x : X, p x = lp (lift x)) ->
      (forall x : X, p x = false -> lift (f x) = g (lift x)) ->
      match loop f p (Incomplete s) numSteps with
      | Complete   x => Complete   (lift x)
      | Incomplete x => Incomplete (lift x)
      end = loop g lp (Incomplete (lift s)) numSteps.
    Proof.
      intros H1 H2. revert s.
      induction numSteps as [|numSteps' IHn]; intros s.
      - reflexivity.
      - destruct (loop f p (Incomplete s) numSteps') eqn:H.
        + cbn. specialize (IHn (f s)).
          destruct (p s) eqn:H', (lp (lift s)) eqn:H''; try reflexivity.
          * enough (true=false) by discriminate. rewrite <- H', <- H''. auto.
          * enough (true=false) by discriminate. rewrite <- H', <- H''. auto.
          * destruct (loop f p (Incomplete (f s)) numSteps') eqn:H'''; auto.
            -- rewrite IHn. f_equal. f_equal. now rewrite H2.
            -- rewrite IHn. f_equal. f_equal. now rewrite H2.
        + cbn. specialize (IHn (f s)).
          destruct (p s) eqn:H', (lp (lift s)) eqn:H''; auto.
          * enough (true=false) by discriminate. rewrite <- H', <- H''. auto.
          * enough (true=false) by discriminate. rewrite <- H', <- H''. auto.
          * destruct (loop f p (Incomplete (f s)) numSteps') eqn:H'''; auto.
            -- rewrite IHn. f_equal. f_equal. now rewrite H2.
            -- rewrite IHn. f_equal. f_equal. now rewrite H2.
    Qed.

    Lemma loop_lift {X Y : Type} (lift : X -> Y) (p : X -> bool) (lp : Y -> bool) (s y : X)
          (f : X -> X) (g : Y -> Y) (numSteps : nat) :
      (forall x : X, p x = lp (lift x)) ->
      (forall x : X, p x = false -> lift (f x) = g (lift x)) ->
      loop f p (Incomplete s) numSteps = Complete y ->
      Complete   (lift y) = loop g lp (Incomplete (lift s)) numSteps.
    Proof.
      intros H1 H2 H3.
      pose proof loop_lift_strong lift p lp s f g numSteps H1 H2 as Lift.
      rewrite H3 in Lift. assumption.
    Qed.


    (** Loop Merge **)

    Lemma loop_incr {X : Type} (f : X -> X) (p : X -> bool) numSteps addNumSteps (s : @Result X) (r : X) :
      loop f p s numSteps = Complete r -> loop f p s (addNumSteps + numSteps) = Complete r.
    Proof.
      revert s addNumSteps; induction numSteps; intros s addNumSteps H.
      - destruct addNumSteps, s; cbn in *; auto; congruence.
      - assert (addNumSteps + S numSteps = S (addNumSteps + numSteps)) as -> by omega.
        cbn. destruct s; cbn in *; auto. destruct (p x); cbn in *; auto.
    Qed.
    
    Lemma loop_merge {X : Type} (f : X -> X) (p q : X -> bool) numSteps1 numSteps2 a1 a2 a3 a4 :
      (forall b, p b = false -> q b = false) ->
      loop f p (Incomplete a1) numSteps1 = Complete a2 ->
      f a2 = a3 -> q a2 = false ->
      loop f q (Incomplete a3) numSteps2 = Complete a4 ->
      loop f q (Incomplete a1) (numSteps1 + numSteps2) = Complete a4.
    Proof.
      revert a1 a2 a3 a4. induction numSteps1 as [|numSteps1' IH]; intros a1 a2 a3 a4 H1 H2 H3 H4 H5.
      - cbn. destruct numSteps2; cbn in *; congruence.
      - cbn in *. destruct (p a1) eqn:H.
        + injection H2; intros ->; clear H2. destruct (q a2) eqn:H'; try congruence. clear H4.
          apply loop_incr. congruence.
        + rewrite (H1 a1 H) in *. apply IH with (a2 := a2) (a3 := a3); auto.
    Qed.

  End Loop.
End Loop.