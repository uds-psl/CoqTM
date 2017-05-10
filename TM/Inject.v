Require Import Prelim Relations TM Shared.Tactics.AutoIndTac Compound.

Fixpoint inject m n Z (indices : Vector.t ((Fin.t m)) n) (def : Z) (V : Vector.t Z n) : Vector.t Z m.
Proof.
  destruct indices.
  - eapply (Vector.const def).
  - remember (S n) as Sn. destruct V eqn:E; inversion HeqSn; subst.
    pose (x := inject _ _ _ indices def t).
    exact (Vector.replace x h h0).
Defined.


Inductive dupfree X : forall n, Vector.t X n -> Prop :=
  dupfreeVN : dupfree (@Vector.nil X)
| dupfreeVC n (x : X) (V : Vector.t X n) : ~ Vector.In x V -> dupfree V -> (dupfree (x ::: V))%vector_scope.


Lemma Vector_nth_In (X : Type) (n : nat) (p : Fin.t n) (m : nat) (new_pos : X) (V : Vector.t X n) :
    V[@p] = new_pos -> Vector.In (new_pos) V.
Proof.
  intros. induction V;dependent destruct p; cbn in *; subst; econstructor; eauto.
Qed.
  
Lemma inject_correct_Some m n Z (indices : Vector.t ((Fin.t m)) n) (def : Z) (V : Vector.t Z n) pos new_pos :
  dupfree indices ->
  indices[@pos] = new_pos -> V[@pos] = (inject indices def V) [@new_pos].
Proof.
  intros. induction H; cbn in *.
  - inv pos.
  - dependent destruct V.
    dependent destruct pos; cbn in *; subst.
    + now rewrite Vector_replace_nth.
    + decide (x = V0[@p]); subst.
      * exfalso. eapply H. eapply Vector_nth_In; eauto.
      * erewrite Vector_replace_nth2; eauto.
Qed.

Section Injection.

  Variable sig : finType.

  Variable m n : nat.

  Variable F : finType.
  
  Variable pM : { M : mTM sig m & states M -> F}.

  Variable I : Vector.t ((Fin.t (S n))) (S m).
  Definition M := projT1 pM.

  Definition trans_inj :=
    fun '(q, sym ) =>
      let (q', act) := trans (m := M) (q, reorder I sym) in
      (q', inject I (None, N) act).

  Definition injectM : mTM sig n.
  Proof.
    econstructor.
    exact trans_inj.
    exact (start M).
    exact (halt (m := M)).
  Defined.

  Definition Inject := (injectM; projT2 pM).

  Ltac double H := let H' := fresh H in assert (H' := H).

  Lemma sim q q' t t' t2 t2' :
    perm I t t2 ->
    perm I t' t2' ->
    step (M := M) (mk_mconfig q t) = mk_mconfig q' t' <->
    step (M := injectM) (mk_mconfig q t2) = mk_mconfig q' t2'.
  Proof.
    Require Import Coq.Program.Equality.
  Admitted.
      
    

    
  Lemma Inject_sem (R : Rel (tapes sig (S m)) (F * tapes sig (S m))) :
    pM ⊫ R ->
    Inject ⊫ lift_gen_eq_p I R.
  Proof.
    intros ***.
    general induction i.
    - double H0.
      cbn in H0.
      destruct (halt (start M)) eqn:E; inv H0.
      cbn. firstorder. unfold lift_gen_p. cbn in H1.      
      eapply (H (reorder I t) 0 (initc M (reorder I t))).
      cbn. unfold M in *; destruct _; now inv H1.
  Admitted.

  Lemma Inject_term T :
    M ↓ T ->
    projT1 Inject ↓ liftT_gen I T.
  Proof.
  Admitted.

End 


















  
