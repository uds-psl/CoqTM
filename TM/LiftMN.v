Require Import TM.Prelim TM.Relations TM.TM.

Inductive dupfree X : forall n, Vector.t X n -> Prop :=
  dupfreeVN : dupfree (@Vector.nil X)
| dupfreeVC n (x : X) (V : Vector.t X n) : ~ Vector.In x V -> dupfree V -> (dupfree (x ::: V))%vector_scope.


Definition reorder m n Z (indices : Vector.t (Fin.t n) m) (V : Vector.t Z n) : Vector.t Z m :=
  Vector.map (Vector.nth V) indices.

Lemma reorder_nth m n Z (indices : Vector.t (Fin.t n) m) (V : Vector.t Z n) (k : Fin.t m) :
  (reorder indices V) [@ k] = V [@ (indices [@ k])].
Proof. now apply Vector.nth_map. Qed.

Section lift_gen.

  Variable n : nat.
  Variable X Z : Type.
  Variable m : nat.
  Variable indices : Vector.t (Fin.t n) m.

  Definition lift_gen (R : Rel (Vector.t X m) (Vector.t X m)) : Rel (Vector.t X n) (Vector.t X n) :=
    fun x y => R (reorder indices x) (reorder indices y).

  Definition lift_gen_p (R : Rel (Vector.t X m) (Z * Vector.t X m)) : Rel (Vector.t X n) (Z * Vector.t X n) :=
    fun x p => let (z,y) := p in R (reorder indices x) (z, reorder indices y).

  Definition not_indices :=
    (fun x : Fin.t n => ~ Vector.In x indices).

  Definition lift_gen_eq (R : Rel (Vector.t X m) (Vector.t X m)) : Rel (Vector.t X n) (Vector.t X n) :=
    lift_gen R ∩ Eq_in (not_indices).

  Definition lift_gen_eq_p (R : Rel (Vector.t X m) (Z * Vector.t X m)) : Rel (Vector.t X n) (Z * Vector.t X n) :=
    lift_gen_p R ∩ ignoreParam (Eq_in not_indices).

  Variable (sig : finType).
  Variable (M1 : mTM sig m).
  Variable T : (tapes sig m) -> nat -> Prop.

  Definition liftT_gen_eq : (tapes sig n) -> nat -> Prop := fun t k => T (reorder indices t) k.
  
End lift_gen.



Lemma Vector_nth_In (X : Type) (n : nat) (p : Fin.t n) (m : nat) (new_pos : X) (V : Vector.t X n) :
    V[@p] = new_pos -> Vector.In (new_pos) V.
Proof.
  intros. induction V;dependent destruct p; cbn in *; subst; econstructor; eauto.
Qed.

Definition vect_zip (X Y : Type) (m : nat) (vx : Vector.t X m) (vy : Vector.t Y m) : Vector.t (X * Y) m := Vector.map2 pair vx vy.

Fixpoint inject m n Z (indices : Vector.t ((Fin.t n)) m) (init : Vector.t Z n) (V : Vector.t Z m)
           : Vector.t Z n.
  destruct indices.
  - apply init.
  - rename n0 into m. remember (S m) as Sm. destruct V eqn:E; inversion HeqSm; subst.
    pose (x := inject _ _ _ indices init t). exact (Vector.replace x h h0).
Defined.

(*
Section Test.
  Definition Z := nat.
  Definition n := 6.
  Definition m := 4.
  
  Definition indicies : Vector.t ((Fin.t n)) m.
  Proof.
    unfold n, m.
    constructor. do 2 apply Fin.FS. apply Fin.F1.
    constructor. do 1 apply Fin.FS. apply Fin.F1.
    constructor. do 3 apply Fin.FS. apply Fin.F1.
    constructor. do 4 apply Fin.FS. apply Fin.F1.
    constructor.
  Defined.

  Definition init : Vector.t Z n.
  Proof.
    unfold n, m.
    constructor. exact 4.
    constructor. exact 8.
    constructor. exact 15.
    constructor. exact 16.
    constructor. exact 23.
    constructor. exact 42.
    constructor.
  Defined.

  Definition V : Vector.t Z m.
  Proof.
    unfold n, m.
    constructor. exact 1.
    constructor. exact 2.
    constructor. exact 3.
    constructor. exact 4.
    constructor.
  Defined.

  Check inject.
  Compute inject indicies init V.
  
End Test.
*)


Lemma inject_correct_Some m n Z (indices : Vector.t (Fin.t n) m) (init : Vector.t Z n) (V : Vector.t Z m) pos new_pos :
  dupfree indices ->
  indices[@pos] = new_pos -> (inject indices init V) [@new_pos] = V[@pos].
Proof.
  intros. induction H; cbn in *.
  - inv pos.
  - dependent destruct V.
    dependent destruct pos; cbn in *; subst.
    + now rewrite Vector_replace_nth.
    + decide (x = V0[@p]); subst.
      * exfalso. eapply H. eapply Vector_nth_In; eauto.
      * erewrite Vector_replace_nth2; auto.
Qed.

Lemma inject_correct m n Z (indices : Vector.t (Fin.t n) m) (init : Vector.t Z n) (V : Vector.t Z m) :
  dupfree indices -> reorder indices (inject indices init V) = V.
Proof.
  intros H. unfold reorder. apply Vector.eq_nth_iff. intros p ? <-.
  erewrite Vector.nth_map; eauto. erewrite inject_correct_Some; eauto.
Qed.


Definition inject_default m n Z (indices : Vector.t ((Fin.t n)) m) (def : Z) (V : Vector.t Z m) :=
  inject indices (Vector.const def n) V.


Lemma inject_correct_id_Some m n Z (indices : Vector.t (Fin.t n) m) (init : Vector.t Z n) pos :
  dupfree indices ->
  init[@pos] = (inject indices init (reorder indices init))[@pos].
Proof.
  intros. induction H as [ | m index indices H1 H2 IH]; cbn in *.
  - reflexivity.
  - decide (index = pos) as [->|d].
    + now rewrite Vector_replace_nth.
    + rewrite IH. now rewrite Vector_replace_nth2.
Qed.

Lemma inject_correct_id m n Z (indices : Vector.t (Fin.t n) m) (init : Vector.t Z n) :
  dupfree indices -> init = (inject indices init (reorder indices init)).
Proof.
  intros H. apply Vector.eq_nth_iff. intros p ? <-. now apply inject_correct_id_Some.
Qed.

Lemma inject_not_index m n Z (indices : Vector.t (Fin.t n) m) (init : Vector.t Z n) (V : Vector.t Z m) (k : Fin.t n) :
  dupfree indices ->
  not_indices indices k -> (inject indices init V)[@k] = init[@k].
Proof.
  intros H. revert V k. induction H as [ | m index indices H1 H2 IH]; intros V0 k HI.
  - cbn in *. reflexivity.
  - dependent destruct V0. unfold not_indices in *. cbn in *.
    decide (index = k) as [->|H]. rewrite Vector_replace_nth.
    + exfalso. apply HI. constructor.
    + rewrite Vector_replace_nth2; auto. apply IH; auto. intros ?. apply HI; auto. constructor; auto.
Qed.

Lemma inject_default_not_index m n Z (indices : Vector.t (Fin.t n) m) (def : Z) (V : Vector.t Z m) (k : Fin.t n) :
  dupfree indices ->
  not_indices indices k -> (inject_default indices def V)[@k] = def.
Proof.
  intros. unfold inject_default. rewrite inject_not_index; auto. apply Vector.const_nth.
Qed.

Section Map_Algebra.
  
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

Lemma inject_execute_step
      (m n : nat)
      (pos : Fin.t n)
      (indices : Vector.t (Fin.t n) m)
      (Act : Type)
      (acts : Vector.t Act m)
      (Tape  : Type)
      (tapes : Vector.t Tape n)
      (step : Tape -> Act -> Tape)
      (nop : Act) :
  dupfree indices ->
  (forall t : Tape, step t nop = t) ->
  step (tapes[@pos]) ((inject_default indices nop acts)[@pos]) =
  (inject indices tapes
          (Vector.map2 step (reorder indices tapes) acts))[@pos].
Proof.
  intros H_dupfree nop_fix. 
  induction H_dupfree as [ | m index indices H1 H2 IH].
  - simpl. rewrite <- nop_fix. f_equal. now apply Vector.const_nth.
  - dependent destruct acts. rename h into act. rename t into acts. cbn. 
    decide (index = pos) as [->|d].
    + now rewrite !Vector_replace_nth.
    + rewrite !Vector_replace_nth2; auto. now apply IH.
Qed.


Section Loop_Propagate.
  Variable (A B : Type).
  Variable (ha : A -> bool) (hb : B -> bool).
  Variable (inj : A -> B -> B) (sur : B -> A).
  Variable (f : A -> A) (g : B -> B).
      
  Variable (Inj1   : forall a b, sur (inj a b) = a).
  Variable (Inj2   : forall a, inj (sur a) a = a).
  Variable (Ha     : forall a b, ha a = hb (inj a b)).
  Variable (Hb     : forall b, hb b = ha (sur b)).
  Variable (step_1 : forall b, sur (g b) = f (sur b)).
  Variable (step_2 : forall b, g b = inj (f (sur b)) b).

  Lemma loop_propagate (k : nat) (b0 : B) (a__k : A) :
      loop k f ha (sur b0) = Some a__k ->
      { b__k | loop k g hb b0 = Some (inj a__k b__k) }.
  Proof.
    revert b0 a__k. induction k as [ |k IH]; intros b0 a__k Sim; cbn in *.
    - exists b0. rewrite <- !(Hb b0) in Sim. destruct (hb b0) eqn:E; inv Sim. now rewrite Inj2.
    - rewrite <- (Hb b0) in Sim. destruct (hb b0) eqn:E; inv Sim; cbn in *.
      + exists b0. now rewrite Inj2.
      + rename H0 into Sim. rewrite <- step_1 in Sim. apply IH in Sim.
        destruct Sim as (b__k&Sim). eexists. eapply Sim.
  Qed.

End Loop_Propagate.


Section LiftNM.

  Variable sig : finType.

  Variable m n : nat.

  Variable F : finType.
  
  Variable pM : { M : mTM sig m & states M -> F}.

  Variable I : Vector.t ((Fin.t n)) m.
  Variable I_dupfree : dupfree I.

  Definition trans_inj :=
    fun '(q, sym ) =>
      let (q', act) := trans (m := projT1 pM) (q, reorder I sym) in
      (q', inject_default I (None, N) act).

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

  Lemma sim_loop (c1 c2 : mconfig sig (states injectM) n) (i : nat) :
    loopM (M := injectM) i c1 = Some c2 ->
    loopM (M := projT1 pM) i (mk_mconfig (cstate c1) (reorder I (ctapes c1))) =
    Some (mk_mconfig (cstate c2) (reorder I (ctapes c2))).
  Proof.
    unfold loopM in *. revert c2 c1. induction i; intros c2 c1 H; cbn in *.
    - destruct (halt _) eqn:E; now inv H.
    - destruct (halt _) eqn:E; inv H; auto.
      rewrite sim_step with (c1 := c1) (c2 := step (M := injectM) c1); [ | reflexivity]. apply IHi. apply H1.
  Qed.

  Lemma sim_eq_step (c1 c2 : mconfig sig (states injectM) n) (k : Fin.t n) :
    not_indices I k -> 
    step (M := injectM) c1 = c2 ->
    (ctapes c1)[@k] = (ctapes c2)[@k].
  Proof.
    intros HI H. unfold injectM in *.
    destruct c1 as [state1 tapes1] eqn:E1, c2 as [state2 tapes2] eqn:E2.
    unfold step, reorder in *. cbn in *.
    destruct (trans (state1, reorder I (Vector.map (current (sig:=sig)) tapes1))) as (q, act) eqn:E3.
    inv H.
    erewrite Vector.nth_map2; eauto.
    replace ((inject_default I (None, N) act)[@k]) with (@None sig, N).
    cbn. reflexivity.
    symmetry. now apply inject_default_not_index.
  Qed.

  Lemma sim_eq_loop (c1 c2 : mconfig sig (states injectM) n) (i : nat) (k : Fin.t n) :
    not_indices I k -> 
    loopM (M := injectM) i c1 = Some c2 ->
    (ctapes c1)[@k] = (ctapes c2)[@k].
  Proof.
    unfold loopM in *. revert c2 c1. induction i; intros c2 c1 H; cbn in *.
    - destruct (halt _) eqn:E; inversion 1; auto.
    - destruct (halt _) eqn:E; inversion 1; auto.
      rewrite sim_eq_step with (c1 := c1) (c2 := step (M := injectM) c1); auto.
  Qed.

  
  Lemma Inject_WRealise (R : Rel (tapes sig m) (F * tapes sig m)) :
    pM ⊫ R ->
    Inject ⊫ lift_gen_eq_p I R.
  Proof.
    intros H.
    split.
    - apply (H (reorder I t) i (mk_mconfig (cstate outc) (reorder I (ctapes outc)))).
      pose proof (@sim_loop (initc injectM t) outc i) as Lemma. cbn in Lemma. now apply Lemma.
    - hnf. intros k HI. unfold get_at.
      pose proof (@sim_eq_loop (initc injectM t) outc i k HI) as Lemma. cbn in Lemma. now apply Lemma.
  Qed.

  Lemma propagate_step
        (c1 : mconfig sig (states (projT1 pM)) n)
        (c2 : mconfig sig (states (injectM)) m) :
    step (M := projT1 pM) (mk_mconfig (cstate c1) (reorder I (ctapes c1))) = c2 ->
    step (M := injectM) c1 = mk_mconfig (cstate c2) (inject I (ctapes c1) (ctapes c2)).
  Proof.
    intros H. unfold injectM in *. cbn in *.
    destruct c1 as [state1 tapes1] eqn:E1, c2 as [state2 tapes2] eqn:E2. cbn in *.
    unfold step in *. cbn in *.
    unfold reorder in *. cbn in *.
    destruct (trans (state1, Vector.map (current (sig:=sig)) (Vector.map (Vector.nth tapes1) I))) as (q, act) eqn:E3.
    injection H. intros <- ->. cbn in *. clear H.
    destruct (trans
                (state1,
                 Vector.map
                   (Vector.nth (Vector.map (current (sig:=sig)) tapes1)) I)) as (q', act') eqn:E4.
    enough ((state2, act) = (q', act')) as X.
    {
      inversion X. subst. f_equal. apply Vector.eq_nth_iff. intros pos ? <-.
      erewrite Vector.nth_map2; eauto.
      unfold tape_move_mono.
      apply (@inject_execute_step m n pos I
                                  (prod (option sig) move) act' (tape sig) tapes1 (@tape_move_mono sig) (None, N));
        firstorder.
    }
    rewrite <- E3, <- E4. f_equal. f_equal. now rewrite map_map_nth.
  Qed.


  Lemma propagate_loop (i : nat)
        (c1 : mconfig sig (states (injectM)) n)
        (c2 : mconfig sig (states (injectM)) m) :
    loopM (M := projT1 pM) i (mk_mconfig (cstate c1) (reorder I (ctapes c1))) = Some c2 ->
    { b__k : mconfig sig (states (injectM)) n |
      loopM (M := injectM) i c1 = Some (mk_mconfig (cstate c2) (inject I (ctapes b__k) (ctapes c2))) }.
  Proof.
    unfold loopM in *. intros H.

    apply (@loop_propagate
             (mconfig sig (states (projT1 pM)) m) (mconfig sig (states injectM) n)
             (fun c : mconfig sig (states (projT1 pM)) m => halt (cstate c))
             (fun c : mconfig sig (states injectM) n => halt (cstate c))
             (fun c2 c1 => mk_mconfig (cstate c2) (inject I (ctapes c1) (ctapes c2)))
             (fun c : mconfig sig (states (projT1 pM)) n => mk_mconfig (cstate c) (reorder I (ctapes c)))
             (step (M := projT1 pM))
             (step (M := injectM))
          ); cbn; firstorder.
    (* - erewrite inject_correct. now destruct a. assumption. *)
    - destruct a. cbn. f_equal. now erewrite inject_correct_id.
    - now erewrite sim_step.
    (* - now erewrite propagate_step. *)
  Qed.

  Lemma Inject_RealisesIn R i :
    pM ⊨c(i) R ->
    Inject ⊨c(i) lift_gen_eq_p I R.
  Proof.
    intros H initTapes. hnf in *.
    specialize (H (reorder I initTapes)) as (outc&H1&H2). cbn in *.
    pose proof (@propagate_loop i (initc injectM initTapes) outc H1) as (X&X').
    eexists. split. eassumption. cbn. hnf. split.
    - hnf. cbn in *. now rewrite inject_correct.
    - hnf. intros k ik1. pose proof (@sim_eq_loop _ _ i k ik1 X') as H. now inv H.
  Qed.

  Lemma Inject_Realises R :
    pM ⊨ R ->
    Inject ⊨ lift_gen_eq_p I R.
  Proof.
    intros H initTapes. hnf in *.
    specialize (H (reorder I initTapes)) as (outc&i&H1&H2).
    pose proof (@propagate_loop i (initc injectM initTapes) outc H1) as (X&X').
    eexists. exists i. split. eassumption. cbn. hnf. split.
    - hnf. cbn in *. now rewrite inject_correct.
    - hnf. intros k ik1. pose proof (@sim_eq_loop _ _ i k ik1 X') as H. now inv H.
  Qed.

  Lemma Inject_Terminates T :
    projT1 pM ↓ T ->
    projT1 Inject ↓ liftT_gen_eq I T.
  Proof.
    intros H initTapes k Term. hnf in *.
    specialize (H (reorder I initTapes) k Term) as (outc&H).
    pose proof (@propagate_loop k (initc injectM initTapes) outc H) as (X&X'). eauto.
  Qed.

End LiftNM.