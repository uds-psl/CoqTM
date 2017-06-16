Require Import Prelim Relations TM Shared.Tactics.AutoIndTac Compound.
Require Import TM.Relations.

Fixpoint inject m n Z (indices : Vector.t ((Fin.t n)) m) (def : Z) (V : Vector.t Z m) : Vector.t Z n.
Proof.
  destruct indices.
  - apply (Vector.const def).
  - rename n0 into m. remember (S m) as Sn. destruct V eqn:E; inversion HeqSn; subst.
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

Lemma inject_correct_Some m n Z (indices : Vector.t (Fin.t n) m) (def : Z) (V : Vector.t Z m) pos new_pos :
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

Lemma inject_correct m n Z (indices : Vector.t (Fin.t n) m) (def : Z) (V : Vector.t Z m) :
  dupfree indices -> reorder indices (inject indices def V) = V.
Proof.
  intros H. unfold reorder. apply Vector.eq_nth_iff. intros p ? <-.
  erewrite Vector.nth_map; eauto. erewrite <- inject_correct_Some; eauto.
Qed.
  
Section Map_Algebra.
  
  Lemma typecheck (m n : nat) (A I X Y Z : Type)
        (x : Vector.t X n) (y : Vector.t Y n) (i : Vector.t I m)
        (f : Vector.t A n -> I -> Z)
        (g : X -> Y -> A) :
    Vector.map (f (Vector.map2 g x y)) i =
    Vector.map (f (Vector.map2 g x y)) i.
  Abort.

  Lemma map_map (A B I : Type) (n : nat) (g : A -> B)  (f : I -> A) (i : Vector.t I n) :
    Vector.map g (Vector.map f i) = Vector.map (fun x => g (f x)) i.
  Proof.
    general induction i.
    - reflexivity.
    - cbn. f_equal. auto.
  Qed.

  Lemma map_eq (n : nat) (A B : Type) (f1 f2 : A -> B) (x : Vector.t A n) :
    (forall k : Fin.t n, f1 (x[@k]) = f2 (x[@k])) ->
    Vector.map f1 x = Vector.map f2 x.
  Proof.
    intros H. apply Vector.eq_nth_iff. intros k ? <-.
    erewrite Vector.nth_map. erewrite Vector.nth_map.
    apply H. reflexivity. reflexivity.
  Qed.

  Lemma map_map_nth (A X : Type) (m n : nat)
        (g : X -> A)
        (x : Vector.t X m)
        (i : Vector.t (Fin.t m) n) :
    Vector.map (Vector.nth (Vector.map g x)) i =
    Vector.map g (Vector.map (Vector.nth x) i).
  Proof.
    rewrite map_map. apply map_eq. intros k. now apply Vector.nth_map.
  Qed.

  Lemma map2_map_nth (A X Y : Type) (m n : nat)
        (g : X -> Y -> A)
        (x : Vector.t X n)
        (y : Vector.t Y n)
        (i : Vector.t (Fin.t n) m) :
    Vector.map (Vector.nth (Vector.map2 g x y)) i =
    Vector.map2 g
                (Vector.map (Vector.nth x) i)
                (Vector.map (Vector.nth y) i).
  Proof.
    apply Vector.eq_nth_iff. intros k ? <-.
    erewrite !Vector.nth_map2; eauto. erewrite !Vector.nth_map; eauto. erewrite !Vector.nth_map2; eauto.
  Qed.
  
End Map_Algebra.

    
Section Injection.

  Variable sig : finType.

  Variable m n : nat.

  Variable F : finType.
  
  Variable pM : { M : mTM sig m & states M -> F}.

  Variable I : Vector.t ((Fin.t (S n))) (S m).
  Variable I_dupfree : dupfree I.

  Definition trans_inj :=
    fun '(q, sym ) =>
      let (q', act) := trans (m := projT1 pM) (q, reorder I sym) in
      (q', inject I (None, N) act).

  Definition injectM : mTM sig n.
  Proof.
    econstructor.
    exact trans_inj.
    exact (start (projT1 pM)).
    exact (halt (m := projT1 pM)).
  Defined.

  Definition Inject := (injectM; projT2 pM).

  Ltac double H := let H' := fresh H in assert (H' := H).



  Lemma sim_step (c1 c2 : mconfig sig (states (projT1 pM)) n) :
    step (M := injectM) c1 = c2 ->
    step (M := projT1 pM) (mk_mconfig (cstate c1) (reorder I (ctapes c1))) =
    (mk_mconfig (cstate c2) (reorder I (ctapes c2))).
  Proof.
    intros H.
    Set Printing Implicit.
    unfold injectM in *.
    Unset Printing Implicit.
    destruct c1 as [state1 tapes1] eqn:E1, c2 as [state2 tapes2] eqn:E2.
    unfold step in *. cbn in *.
    unfold reorder in *. cbn in *.

    destruct (trans
                (state1,
                 Vector.map (Vector.nth (Vector.map (current (sig:=sig)) tapes1)) I))
             as (q, act) eqn:E3.
    injection H; clear H; intros H1 H2; subst.

    destruct (trans (state1, Vector.map (current (sig:=sig)) (Vector.map (Vector.nth tapes1) I)))
             as (q', act') eqn:E4.

    enough ((state2, act) = (q', act')) as X.
    {
      inv X. f_equal.
      rewrite map2_map_nth. f_equal.
      symmetry. pose proof inject_correct as Lemma. unfold reorder in Lemma. now apply Lemma.
    }
    rewrite <- E3, <- E4. f_equal. f_equal. now apply map_map_nth.
  Qed.

  Lemma sim_loop (c1 c2 : mconfig sig (states (projT1 pM)) n) (i : nat) :
    loopM (M := injectM) i c1 = Some c2 ->
    loopM (M := projT1 pM) i (mk_mconfig (cstate c1) (reorder I (ctapes c1))) =
    Some (mk_mconfig (cstate c2) (reorder I (ctapes c2))).
  Proof.
    unfold loopM in *. general induction i; cbn in *.
    - destruct (halt _) eqn:E; now inv H.
    - destruct (halt _) eqn:E; inv H; try rewrite E in *; auto.
      rewrite sim_step with (c2 := step (M := injectM) c1); auto.
  Qed.
  
  Lemma Inject_sem (R : Rel (tapes sig (S m)) (F * tapes sig (S m))) :
    pM ⊫ R ->
    Inject ⊫ lift_gen_eq_p I R.
  Proof.
    intros H.
    split.
    - apply (H (reorder I t) i (mk_mconfig (cstate outc) (reorder I (ctapes outc)))).
      pose proof (@sim_loop (initc injectM t) outc i) as Lemma. cbn in Lemma. now apply Lemma.
    - 
  Admitted.

  Lemma Inject_term T :
    projT1 pM ↓ T ->
    projT1 Inject ↓ liftT_gen I T.
  Proof.
  Admitted.

End.