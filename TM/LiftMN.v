Require Import TM.Prelim TM.Relations TM.TM.

Definition reorder m n Z (indexes : Vector.t (Fin.t n) m) (V : Vector.t Z n) : Vector.t Z m :=
  Vector.map (Vector.nth V) indexes.


Lemma reorder_nth m n Z (indexes : Vector.t (Fin.t n) m) (V : Vector.t Z n) (k : Fin.t m) :
  (reorder indexes V) [@ k] = V [@ (indexes [@ k])].
Proof. now apply Vector.nth_map. Qed.

Section lift_gen.

  Variable n : nat.
  Variable X Z : Type.
  Variable m : nat.
  Variable indexes : Vector.t (Fin.t n) m.

  Definition lift_gen (R : Rel (Vector.t X m) (Vector.t X m)) : Rel (Vector.t X n) (Vector.t X n) :=
    fun x y => R (reorder indexes x) (reorder indexes y).

  Definition lift_gen_p (R : Rel (Vector.t X m) (Z * Vector.t X m)) : Rel (Vector.t X n) (Z * Vector.t X n) :=
    fun x p => let (z,y) := p in R (reorder indexes x) (z, reorder indexes y).

  Definition not_indexes :=
    (fun x : Fin.t n => ~ Vector.In x indexes).

  Definition lift_gen_eq (R : Rel (Vector.t X m) (Vector.t X m)) : Rel (Vector.t X n) (Vector.t X n) :=
    lift_gen R ∩ Eq_in (not_indexes).

  Definition lift_gen_eq_p (R : Rel (Vector.t X m) (Z * Vector.t X m)) : Rel (Vector.t X n) (Z * Vector.t X n) :=
    lift_gen_p R ∩ ignoreParam (Eq_in not_indexes).
End lift_gen.

Arguments not_indexes : simpl never.
Arguments lift_gen { n X m } ( indexes R ) x y /.
Arguments lift_gen_eq { n X m } ( indexes R ) x y /.
Arguments lift_gen_eq_p { n X Z m } ( indexes R ) x y /.


Section liftT_gen.
  Variable n m : nat.
  Variable indexes : Vector.t (Fin.t n) m.
  Variable (sig : finType).
  Variable T : (tapes sig m) -> nat -> Prop.

  Definition liftT_gen : Rel (tapes sig n) nat := fun t k => T (reorder indexes t) k.
End liftT_gen.

Arguments liftT_gen { n m } ( indexes ) { sig } ( T ) x y /.



Lemma Vector_nth_In (X : Type) (n : nat) (p : Fin.t n) (m : nat) (new_pos : X) (V : Vector.t X n) :
    V[@p] = new_pos -> Vector.In (new_pos) V.
Proof.
  intros. induction V;dependent destruct p; cbn in *; subst; econstructor; eauto.
Qed.

Definition vect_zip (X Y : Type) (m : nat) (vx : Vector.t X m) (vy : Vector.t Y m) : Vector.t (X * Y) m := Vector.map2 pair vx vy.

Fixpoint inject m n Z (indexes : Vector.t ((Fin.t n)) m) (init : Vector.t Z n) (V : Vector.t Z m)
           : Vector.t Z n.
  destruct indexes.
  - apply init.
  - rename n0 into m. remember (S m) as Sm. destruct V eqn:E; inversion HeqSm; subst.
    pose (x := inject _ _ _ indexes init t). exact (Vector.replace x h h0).
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


Lemma inject_correct_Some m n Z (indexes : Vector.t (Fin.t n) m) (init : Vector.t Z n) (V : Vector.t Z m) pos new_pos :
  dupfree indexes ->
  indexes[@pos] = new_pos -> (inject indexes init V) [@new_pos] = V[@pos].
Proof.
  intros. induction H; cbn in *.
  - inv pos.
  - dependent destruct V.
    dependent destruct pos; cbn in *; subst.
    + now rewrite replace_nth.
    + decide (x = V0[@p]); subst.
      * exfalso. eapply H. eapply Vector_nth_In; eauto.
      * erewrite replace_nth2; auto.
Qed.

Lemma inject_correct m n Z (indexes : Vector.t (Fin.t n) m) (init : Vector.t Z n) (V : Vector.t Z m) :
  dupfree indexes -> reorder indexes (inject indexes init V) = V.
Proof.
  intros H. unfold reorder. apply Vector.eq_nth_iff. intros p ? <-.
  erewrite Vector.nth_map; eauto. erewrite inject_correct_Some; eauto.
Qed.


Definition inject_default m n Z (indexes : Vector.t ((Fin.t n)) m) (def : Z) (V : Vector.t Z m) :=
  inject indexes (Vector.const def n) V.


Lemma inject_correct_id_Some m n Z (indexes : Vector.t (Fin.t n) m) (init : Vector.t Z n) pos :
  dupfree indexes ->
  init[@pos] = (inject indexes init (reorder indexes init))[@pos].
Proof.
  intros. induction H as [ | m index indexes H1 H2 IH]; cbn in *.
  - reflexivity.
  - decide (index = pos) as [->|d].
    + now rewrite replace_nth.
    + rewrite IH. now rewrite replace_nth2.
Qed.

Lemma inject_correct_id m n Z (indexes : Vector.t (Fin.t n) m) (init : Vector.t Z n) :
  dupfree indexes -> init = (inject indexes init (reorder indexes init)).
Proof.
  intros H. apply Vector.eq_nth_iff. intros p ? <-. now apply inject_correct_id_Some.
Qed.

Lemma inject_not_index m n Z (indexes : Vector.t (Fin.t n) m) (init : Vector.t Z n) (V : Vector.t Z m) (k : Fin.t n) :
  dupfree indexes ->
  not_indexes indexes k -> (inject indexes init V)[@k] = init[@k].
Proof.
  intros H. revert V k. induction H as [ | m index indexes H1 H2 IH]; intros V0 k HI.
  - cbn in *. reflexivity.
  - dependent destruct V0. unfold not_indexes in *. cbn in *.
    decide (index = k) as [->|H]. rewrite replace_nth.
    + exfalso. apply HI. constructor.
    + rewrite replace_nth2; auto. apply IH; auto. intros ?. apply HI; auto. constructor; auto.
Qed.

Lemma inject_default_not_index m n Z (indexes : Vector.t (Fin.t n) m) (def : Z) (V : Vector.t Z m) (k : Fin.t n) :
  dupfree indexes ->
  not_indexes indexes k -> (inject_default indexes def V)[@k] = def.
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
      (indexes : Vector.t (Fin.t n) m)
      (Act : Type)
      (acts : Vector.t Act m)
      (Tape  : Type)
      (tapes : Vector.t Tape n)
      (step : Tape -> Act -> Tape)
      (nop : Act) :
  dupfree indexes ->
  (forall t : Tape, step t nop = t) ->
  step (tapes[@pos]) ((inject_default indexes nop acts)[@pos]) =
  (inject indexes tapes
          (Vector.map2 step (reorder indexes tapes) acts))[@pos].
Proof.
  intros H_dupfree nop_fix. 
  induction H_dupfree as [ | m index indexes H1 H2 IH].
  - simpl. rewrite <- nop_fix. f_equal. now apply Vector.const_nth.
  - dependent destruct acts. rename h into act. rename t into acts. cbn. 
    decide (index = pos) as [->|d].
    + now rewrite !replace_nth.
    + rewrite !replace_nth2; auto. now apply IH.
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

    destruct (trans (state1, Vector.map (Vector.nth (current_chars tapes1)) I)) as (q, act) eqn:E3.
    injection H; clear H; intros H1 H2; subst.

    destruct (trans (state1, current_chars (Vector.map (Vector.nth tapes1) I))) as (q', act') eqn:E4.

    enough ((state2, act) = (q', act')) as X.
    {
      inv X. f_equal.
      rewrite map2_map_nth. f_equal.
      symmetry. pose proof inject_correct as L. unfold reorder in L. now apply L.
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
    not_indexes I k -> 
    step (M := injectM) c1 = c2 ->
    (ctapes c1)[@k] = (ctapes c2)[@k].
  Proof.
    intros HI H. unfold injectM in *.
    destruct c1 as [state1 tapes1] eqn:E1, c2 as [state2 tapes2] eqn:E2.
    unfold step, reorder in *. cbn in *.
    destruct (trans (state1, reorder I (current_chars tapes1))) as (q, act) eqn:E3.
    inv H.
    erewrite Vector.nth_map2; eauto.
    replace ((inject_default I (None, N) act)[@k]) with (@None sig, N).
    cbn. reflexivity.
    symmetry. now apply inject_default_not_index.
  Qed.

  Lemma sim_eq_loop (c1 c2 : mconfig sig (states injectM) n) (i : nat) (k : Fin.t n) :
    not_indexes I k -> 
    loopM (M := injectM) i c1 = Some c2 ->
    (ctapes c1)[@k] = (ctapes c2)[@k].
  Proof.
    unfold loopM in *. revert c2 c1. induction i; intros c2 c1 H; cbn in *.
    - destruct (halt _) eqn:E; inversion 1; auto.
    - destruct (halt _) eqn:E; inversion 1; auto.
      rewrite sim_eq_step with (c1 := c1) (c2 := step (M := injectM) c1); auto.
  Qed.

  
  Lemma Inject_Realise (R : Rel (tapes sig m) (F * tapes sig m)) :
    pM ⊨ R ->
    Inject ⊨ lift_gen_eq_p I R.
  Proof.
    intros H.
    split.
    - apply (H (reorder I t) i (mk_mconfig (cstate outc) (reorder I (ctapes outc)))).
      pose proof (@sim_loop (initc injectM t) outc i) as L. cbn in L. now apply L.
    - hnf. intros k HI. 
      pose proof (@sim_eq_loop (initc injectM t) outc i k HI) as L. cbn in L. symmetry. now apply L.
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
    destruct (trans (state1, current_chars (Vector.map (Vector.nth tapes1) I))) as (q, act) eqn:E3.
    injection H. intros <- ->. cbn in *. clear H.
    destruct (trans
                (state1,
                 Vector.map
                   (Vector.nth (current_chars tapes1)) I)) as (q', act') eqn:E4.
    enough ((state2, act) = (q', act')) as X.
    {
      inversion X. subst. f_equal. apply Vector.eq_nth_iff. intros pos ? <-.
      erewrite Vector.nth_map2; eauto.
      unfold tape_move_mono.
      apply (@inject_execute_step m n pos I
                                  (prod (option sig) move) act' (tape sig) tapes1 (@tape_move_mono sig) (None, N));
        firstorder.
    }
    rewrite <- E3, <- E4. f_equal. f_equal. autounfold with tape. now rewrite map_map_nth.
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

  Lemma Inject_Terminates T :
    projT1 pM ↓ T ->
    projT1 Inject ↓ liftT_gen I T.
  Proof.
    intros H initTapes k Term. hnf in *.
    specialize (H (reorder I initTapes) k Term) as (outc&H).
    pose proof (@propagate_loop k (initc injectM initTapes) outc H) as (X&X'). eauto.
  Qed.

End LiftNM.

Arguments Inject : simpl never.



(* Indexes vector for adding a fixed number [m] of additional tapes at the begin. *)
Section AddTapes.

  Variable n : nat.

  Eval simpl in Fin.L 4 (Fin1 : Fin.t 10).
  Check @Fin.L.
  Search Fin.L.
  Eval simpl in Fin.R 4 (Fin1 : Fin.t 10).
  Check @Fin.R.
  Search Fin.R.

  Lemma Fin_L_injective (m : nat) (i1 i2 : Fin.t n) :
    Fin.L m i1 = Fin.L m i2 -> i1 = i2.
  Proof.
    induction n as [ | n' IH].
    - dependent destruct i1.
    - dependent destruct i1; dependent destruct i2; cbn in *; auto; try congruence.
      apply Fin.FS_inj in H. now apply IH in H as ->.
  Qed.

  Lemma Fin_R_injective (m : nat) (i1 i2 : Fin.t n) :
    Fin.R m i1 = Fin.R m i2 -> i1 = i2.
  Proof.
    induction m as [ | n' IH]; cbn.
    - auto.
    - intros H % Fin.FS_inj. auto.
  Qed.


  Definition add_tapes (m : nat) : Vector.t (Fin.t (m + n)) n :=
    Vector.map (fun k => Fin.R m k) (Fin_initVect _).


  Lemma add_tapes_dupfree (m : nat) : dupfree (add_tapes m).
  Proof.
    apply dupfree_map_injective.
    - apply Fin_R_injective.
    - apply Fin_initVect_dupfree.
  Qed.

  Lemma add_tapes_reorder_nth (X : Type) (m : nat) (ts : Vector.t X (m + n)) k :
    (reorder (add_tapes m) ts)[@k] = ts[@Fin.R m k].
  Proof.
    unfold add_tapes. unfold reorder. erewrite !VectorSpec.nth_map; eauto.
    cbn. now rewrite Fin_initVect_nth.
  Qed.
  

  Definition app_tapes (m : nat) : Vector.t (Fin.t (n + m)) n :=
    Vector.map (Fin.L _) (Fin_initVect _).

  Lemma app_tapes_dupfree (m : nat) : dupfree (app_tapes m).
  Proof.
    apply dupfree_map_injective.
    - apply Fin_L_injective.
    - apply Fin_initVect_dupfree.
  Qed.

  Lemma app_tapes_reorder_nth (X : Type) (m : nat) (ts : Vector.t X (n + m)) k :
    (reorder (app_tapes m) ts)[@k] = ts[@Fin.L m k].
  Proof.
    unfold app_tapes. unfold reorder. erewrite !VectorSpec.nth_map; eauto.
    cbn. now rewrite Fin_initVect_nth.
  Qed.


End AddTapes.



(** * Tactical support *)


Lemma smpl_dupfree_helper1 (n : nat) :
  dupfree [|Fin.F1 (n := n)|].
Proof. vector_dupfree. Qed.

Lemma smpl_dupfree_helper2 (n : nat) :
  dupfree [|Fin.FS (Fin.F1 (n := n))|].
Proof. vector_dupfree. Qed.


Ltac smpl_dupfree :=
  match goal with
  | [ |- dupfree [|Fin.F1 |] ] => apply smpl_dupfree_helper1
  | [ |- dupfree [|Fin.FS |] ] => apply smpl_dupfree_helper2
  | [ |- dupfree (add_tapes _ _)] => apply add_tapes_dupfree
  | [ |- dupfree (app_tapes _ _)] => apply app_tapes_dupfree
  | [ |- dupfree _ ] => now vector_dupfree (* fallback tactic *)
  end.


Ltac smpl_TM_LiftN :=
  match goal with
  | [ |- Inject _ _ ⊨ _] => apply Inject_Realise; [ smpl_dupfree | ]
  | [ |- Inject _ _ ⊨c(_) _] => apply Inject_RealisesIn; [ smpl_dupfree | ]
  | [ |- projT1 (Inject _ _) ↓ _] => apply Inject_Terminates; [ smpl_dupfree | ]
  end.
Smpl Add smpl_TM_LiftN : TM_Correct.


Ltac is_num_const n :=
  lazymatch n with
  | O => idtac
  | S ?n => is_num_const n
  | _ => fail "Not a number"
  end.


(*
Section Test_Is_Num_Const.
  Variable n : nat.
  Eval cbn in ltac:(is_num_const 42).
  Fail Eval cbn in ltac:(is_num_const n).
  Fail Eval cbn in ltac:(is_num_const (S n)).
End Test_Is_Num_Const.
*)


(* This tactical executes [t 0], ..., [t (n-1)]. *)
Ltac do_n_times n t :=
  match n with
  | O => idtac
  | (S ?n') =>
    t 0;
    do_n_times n' ltac:(fun i => let next := constr:(S i) in t next)
  end.
(*
Eval cbn in ltac:(do_n_times 42 ltac:(fun a => idtac a)).
*)

(* This similiar tactical executes [t Fin0], ..., [t Fin_(n-1)]. *)
Ltac do_n_times_fin_rect n m t :=
  lazymatch n with
  | O => idtac
  | S ?n' =>
    let m' := eval simpl in (pred m) in
    let one := eval simpl in (@Fin.F1 _ : Fin.t m) in
    t one;
    do_n_times_fin_rect n' m' ltac:(fun i => let next := eval simpl in (Fin.FS i) in t next)
  end.

Ltac do_n_times_fin n t := do_n_times_fin_rect n n t.

(*
Eval cbn in ltac:(do_n_times_fin 3 ltac:(fun a => idtac a)).
Eval cbn in ltac:(do_n_times_fin 3 ltac:(fun a => let x := eval simpl in (a : Fin.t 3) in idtac x)).
*)




(* Support for [app_tapes] *)

(*
 * The tactic [simpl_not_in_add_tapes] specialises hypothesises of the form 
 * [H : forall i : Fin.t _, not_indexes (add_tapes _ m) i -> _]
 * with [i := Fin0], ..., [i := Fin(m-1)] and proves [not_index (add_tapes _ m) i.
 *)

Ltac simpl_not_in_add_tapes_step H m' :=
  let H' := fresh "HIndex_" H in
  unshelve epose proof (H ltac:(getFin m') _) as H';
  [ hnf; unfold add_tapes, Fin_initVect; cbn [tabulate Vector.map Fin.L Fin.R]; vector_not_in
  | cbn [Fin.L Fin.R] in H'
  ].
 
Ltac simpl_not_in_add_tapes_loop H m :=
  do_n_times m ltac:(simpl_not_in_add_tapes_step H); clear H.

Ltac simpl_not_in_add_tapes_one :=
  lazymatch goal with
  | [ H : forall i : Fin.t _, not_indexes (add_tapes _ ?m) i -> _ |- _] =>
    simpl_not_in_add_tapes_loop H m; clear H
  | [ H : context [ (reorder (add_tapes _ ?m) _)[@_]] |- _ ] =>
    rewrite ! (add_tapes_reorder_nth (m := m)) in H; cbn in H
  | [ |- context [ (reorder (add_tapes _ ?m) _)[@_]] ] =>
    rewrite ! (add_tapes_reorder_nth (m := m)); cbn
  end.

Ltac simpl_not_in_add_tapes := repeat simpl_not_in_add_tapes_one.

(* Test *)
Goal True.
  assert (forall i : Fin.t 3, not_indexes (add_tapes _ 2) i -> i = i) by firstorder.
  simpl_not_in_add_tapes. (* :-) *)
Abort.

Goal True.
  assert (n : nat) by constructor.
  assert (forall i : Fin.t (S n), not_indexes (add_tapes n 1) i -> True) by firstorder.
  simpl_not_in_add_tapes.
Abort.


(* Support for [app_tapes] *)


Ltac simpl_not_in_app_tapes_step H n m' :=
  let H' := fresh "HIndex_" H in
  unshelve epose proof (H (Fin.R n ltac:(getFin m')) _) as H';
  [ hnf; unfold app_tapes, Fin_initVect; cbn [tabulate Vector.map Fin.L Fin.R]; vector_not_in
  | cbn [Fin.L Fin.R] in H'
  ].

Ltac simpl_not_in_app_tapes_loop H n m :=
  do_n_times m ltac:(fun m' => simpl_not_in_app_tapes_step H n m'); clear H.

Ltac simpl_not_in_app_tapes_one :=
  lazymatch goal with
  | [ H : forall i : Fin.t _, not_indexes (app_tapes ?n ?m) i -> _ |- _] =>
    simpl_not_in_app_tapes_loop H n m; clear H
  | [ H : context [ (reorder (app_tapes ?n ?m) _)[@_]] |- _ ] =>
    rewrite ! (app_tapes_reorder_nth (n := n) (m := m)) in H; cbn in H
  | [ |- context [ (reorder (app_tapes ?n ?m) _)[@_]] ] =>
    rewrite ! (app_tapes_reorder_nth (n := n) (m := m)); cbn
  end.


Ltac simpl_not_in_app_tapes := repeat simpl_not_in_app_tapes_one.

Goal True.
  assert (forall i : Fin.t 10, not_indexes (app_tapes 8 _) i -> i = i) as Inj by firstorder.
  simpl_not_in_app_tapes.
  Check HIndex_Inj : Fin8 = Fin8.
  Check HIndex_Inj0 : Fin9 = Fin9.
  Fail Check HInj.
Abort.



(* Check whether a vector (syntactically) contains an element *)
Ltac vector_contains a vect :=
  lazymatch vect with
  | @Vector.nil ?A => fail "Vector doesn't contain" a
  | @Vector.cons ?A a ?n ?vect' => idtac
  | @Vector.cons ?A ?b ?n ?vect' => vector_contains a vect'
  | _ => fail "No vector" vect
  end.

Fail Check ltac:(vector_contains 42 (@Vector.nil nat); idtac "yes!").
Check ltac:(vector_contains 42 [|4;8;15;16;23;42|]; idtac "yes!").

Ltac vector_doesnt_contain a vect :=
  tryif vector_contains a vect then fail "Vector DOES contain" a else idtac.


Check ltac:(vector_doesnt_contain 42 (@Vector.nil nat); idtac "yes!").
Check ltac:(vector_doesnt_contain 9 [|4;8;15;16;23;42|]; idtac "yes!").
Fail Check ltac:(vector_doesnt_contain 42 [|4;8;15;16;23;42|]; idtac "yes!").



(*
 * The tactic [simpl_not_in_vector] tries to specialise hypothesises of the form 
 * [H : forall i : Fin.t n, not_indexes [F1; ...; Fk] i -> _]
 * with [i := Fin0], ..., [i := Fin(n-1)] to new assumptions [H_0].
 *)

Ltac simpl_not_in_vector_step H vect n m' :=
  let H' := fresh H "_" in
  tryif vector_contains m' vect
  then idtac (* skip m' *)
  else pose proof (H m' ltac:(vector_not_in)) as H'.

Ltac simpl_not_in_vector_loop H vect n :=
  let H' := fresh H "_" in
  pose proof I as H';
  do_n_times_fin n ltac:(fun m' => simpl_not_in_vector_step H vect n m');
  clear H'.
  
Ltac simpl_not_in_vector_one :=
  lazymatch goal with
  | [ H : forall i : Fin.t ?n, not_indexes ?vect i -> _ |- _ ] =>
    simpl_not_in_vector_loop H vect n; clear H
  end.

Ltac simpl_not_in_vector := repeat simpl_not_in_vector_one.


(* Test *)
Goal True.
  assert (forall i : Fin.t 10, not_indexes [|Fin8; Fin1; Fin2; Fin3|] i -> i = i) as HInj by firstorder.
  simpl_not_in_vector_one.
  Fail Check HInj.
  Show Proof.
  Check (HInj_0 : Fin0 = Fin0).
  Check (HInj_1 : Fin4 = Fin4).
  Check (HInj_2 : Fin5 = Fin5).
  Check (HInj_3 : Fin6 = Fin6).
  Check (HInj_4 : Fin7 = Fin7).
  Check (HInj_5 : Fin9 = Fin9).
Abort.



Ltac simpl_not_in :=
  repeat match goal with
         | _ => progress simpl_not_in_add_tapes
         | _ => progress simpl_not_in_app_tapes
         | _ => progress simpl_not_in_vector
         end.