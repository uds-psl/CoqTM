Require Import TM.Prelim TM.Relations TM.TM.

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
End lift_gen.

Arguments not_indices : simpl never.
Arguments lift_gen { n X m } ( indices R ) x y /.
Arguments lift_gen_eq { n X m } ( indices R ) x y /.
Arguments lift_gen_eq_p { n X Z m } ( indices R ) x y /.


Section liftT_gen.
  Variable n m : nat.
  Variable indices : Vector.t (Fin.t n) m.
  Variable (sig : finType).
  Variable T : (tapes sig m) -> nat -> Prop.

  Definition liftT_gen : Rel (tapes sig n) nat := fun t k => T (reorder indices t) k.
End liftT_gen.

Arguments liftT_gen { n m } ( indices ) { sig } ( T ) x y /.


Fixpoint inject {m n: nat} {A: Type} (indices : Vector.t (Fin.t n) m) : forall (init : Vector.t A n) (V : Vector.t A m), Vector.t A n :=
  match indices with
  | Vector.nil _ => fun init V => init
  | Vector.cons _ i m' indices' =>
    fun init V =>
    Vector.replace (inject indices' init (Vector.tl V)) i (Vector.hd V)
  end.


Lemma inject_correct_Some m n Z (indices : Vector.t (Fin.t n) m) (init : Vector.t Z n) (V : Vector.t Z m) pos new_pos :
  dupfree indices ->
  indices[@pos] = new_pos -> (inject indices init V) [@new_pos] = V[@pos].
Proof.
  intros. induction H; cbn in *.
  - inv pos.
  - dependent destruct V.
    dependent destruct pos; cbn in *; subst.
    + now rewrite replace_nth.
    + decide (x = V0[@p]); subst.
      * exfalso. eapply H. eapply vect_nth_In; eauto.
      * erewrite replace_nth2; auto.
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
  (inject indices init (reorder indices init))[@pos] = init[@pos].
Proof.
  intros. induction H as [ | m index indices H1 H2 IH]; cbn in *.
  - reflexivity.
  - decide (index = pos) as [->|d].
    + now rewrite replace_nth.
    + rewrite <- IH. now rewrite replace_nth2.
Qed.

Lemma inject_correct_id m n Z (indices : Vector.t (Fin.t n) m) (t : Vector.t Z n) :
  dupfree indices ->
  inject indices t (reorder indices t) = t.
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
    decide (index = k) as [->|H]. rewrite replace_nth.
    + exfalso. apply HI. constructor.
    + rewrite replace_nth2; auto. apply IH; auto. intros ?. apply HI; auto. constructor; auto.
Qed.

Lemma inject_default_not_index m n Z (indices : Vector.t (Fin.t n) m) (def : Z) (V : Vector.t Z m) (k : Fin.t n) :
  dupfree indices ->
  not_indices indices k -> (inject_default indices def V)[@k] = def.
Proof.
  intros. unfold inject_default. rewrite inject_not_index; auto. apply Vector.const_nth.
Qed.


Section loop_map.
  Variable A B : Type.
  Variable (f : A -> A) (h : A -> bool) (g : A -> B).
  Hypothesis step_map_comp : forall a, g (f a) = g a.

  Lemma loop_map k a1 a2 :
    loop f h k a1 = Some a2 ->
    g a2 = g a1.
  Proof.
    revert a1 a2. induction k as [ | k' IH]; intros; cbn in *.
    - destruct (h a1); now inv H.
    - destruct (h a1).
      + now inv H.
      + apply IH in H. now rewrite step_map_comp in H.
  Qed.

End loop_map.


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

  Definition injectM : mTM sig n :=
    {|
      trans := trans_inj;
      start := start (projT1 pM);
      halt := halt (m := projT1 pM);
    |}.

  Definition Inject := (injectM; projT2 pM).

  Definition reorderConf : mconfig sig (states (projT1 Inject)) n -> mconfig sig (states (projT1 pM)) m :=
    fun c => mk_mconfig (cstate c) (reorder I (ctapes c)).

  Lemma current_chars_reorder (t : tapes sig n) :
    current_chars (reorder I t) = reorder I (current_chars t).
  Proof. unfold current_chars, reorder. apply Vector.eq_nth_iff; intros i ? <-. now simpl_tape. Qed.

  Lemma tape_move_multi_reorder (t : tapes sig n) act :
    tape_move_multi (reorder I t) act = reorder I (tape_move_multi t (inject_default I (None, N) act)).
  Proof.
    unfold tape_move_multi, reorder. apply Vector.eq_nth_iff; intros i ? <-. simpl_tape.
    unfold inject_default. now erewrite inject_correct_Some.
  Qed.

  Lemma sim_step (c1 : mconfig sig (states (projT1 pM)) n) :
    step (M := projT1 pM) (reorderConf c1) = reorderConf (step (M := injectM) c1).
  Proof.
    unfold reorderConf. unfold injectM in *.
    destruct c1 as [q t] eqn:E1.
    unfold step in *. cbn -[current_chars tape_move_multi] in *.
    rewrite current_chars_reorder.
    destruct (trans (q, reorder I (current_chars t))) as (q', act) eqn:E; cbn.
    f_equal. apply tape_move_multi_reorder.
  Qed.

  Lemma sim_loop (c1 c2 : mconfig sig (states injectM) n) (i : nat) :
    loopM (M := injectM) i c1 = Some c2 ->
    loopM (M := projT1 pM) i (reorderConf c1) = Some (reorderConf c2).
  Proof.
    intros HLoop.
    eapply loop_lift with (f := step (M := injectM)) (h := haltConf (M := injectM)).
    - cbn. auto.
    - intros ? _. now apply sim_step.
    - apply HLoop.
  Qed.

  Lemma sim_eq_step (c1 c2 : mconfig sig (states injectM) n) (k : Fin.t n) :
    not_indices I k ->
    step (M := injectM) c1 = c2 ->
    (ctapes c2)[@k] = (ctapes c1)[@k].
  Proof.
    intros HI H. unfold injectM in *.
    destruct c1 as [state1 tapes1] eqn:E1, c2 as [state2 tapes2] eqn:E2.
    unfold step, reorder in *. cbn in *.
    destruct (trans (state1, reorder I (current_chars tapes1))) as (q, act) eqn:E3.
    inv H. erewrite Vector.nth_map2; eauto. now rewrite inject_default_not_index.
  Qed.

  Lemma sim_eq_loop (c1 c2 : mconfig sig (states injectM) n) (i : nat) (k : Fin.t n) :
    not_indices I k ->
    loopM (M := injectM) i c1 = Some c2 ->
    (ctapes c2)[@k] = (ctapes c1)[@k].
  Proof.
    intros Hi HLoop. unfold loopM in HLoop.
    eapply loop_map with (g := fun c => (ctapes c)[@k]); eauto.
    intros. now apply sim_eq_step.
  Qed.

  Lemma Inject_Realise (R : Rel (tapes sig m) (F * tapes sig m)) :
    pM ⊨ R ->
    Inject ⊨ lift_gen_eq_p I R.
  Proof.
    intros H. split.
    - apply (H (reorder I t) i (mk_mconfig (cstate outc) (reorder I (ctapes outc)))).
      now apply (@sim_loop (initc injectM t) outc i).
    - hnf. intros k HI. now apply (@sim_eq_loop (initc injectM t) outc i k HI).
  Qed.


  Definition injectConf (c1 : mconfig sig (states (projT1 pM)) n) (c2 : mconfig sig (states (injectM)) m) : mconfig sig (states (injectM)) n :=
    mk_mconfig (cstate c2) (inject I (ctapes c1) (ctapes c2)).

  Lemma injectConf_reorderConf_id (c1 : mconfig sig (states (projT1 pM)) n) :
    injectConf c1 (reorderConf c1) = c1.
  Proof. destruct c1 as [q t]; cbn. unfold injectConf, reorderConf. f_equal. cbn. now apply inject_correct_id. Qed.

  Lemma reorderConf_injectConf (c1 : mconfig sig (states (projT1 pM)) n) (c2 : mconfig sig (states (injectM)) m) :
    reorderConf (injectConf c1 c2) = c2.
  Proof. destruct c1 as [q1 t1], c2 as [q2 t2]; cbn. unfold injectConf, reorderConf. f_equal. cbn. now apply inject_correct. Qed.

  Lemma propagate_loop (i : nat)
        (c1 : mconfig sig (states (injectM)) n)
        (c2 : mconfig sig (states (injectM)) m) :
    loopM (M := projT1 pM) i (reorderConf c1) = Some c2 ->
    exists c' : mconfig sig (states (injectM)) n,
      loopM (M := injectM) i c1 = Some (injectConf c' c2) /\
      c2 = reorderConf c'.
  Proof.
    intros HLoop. unfold loopM in *. cbn in *.
    apply loop_unlift with (lift:=reorderConf) (f:=step (M:=injectM)) (h:=haltConf (M:=injectM)) in HLoop as (c'&HLoop&->).
    - exists c'. split; auto. now rewrite injectConf_reorderConf_id.
    - auto.
    - intros ? _. apply sim_step.
  Qed.

  Lemma Inject_Terminates T :
    projT1 pM ↓ T ->
    projT1 Inject ↓ liftT_gen I T.
  Proof.
    intros H initTapes k Term. hnf in *.
    specialize (H (reorder I initTapes) k Term) as (outc&H).
    pose proof (@propagate_loop k (initc injectM initTapes) outc H) as (X&X'&->). eauto.
  Qed.

  Lemma Inject_RealiseIn R i :
    pM ⊨c(i) R ->
    Inject ⊨c(i) lift_gen_eq_p I R.
  Proof.
    intros (H1&H2) % Realise_total. apply Realise_total. split.
    - now apply Inject_Realise.
    - eapply TerminatesIn_monotone.
      + apply Inject_Terminates; eauto.
      + firstorder.
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
  | [ |- Inject _ _ ⊨c(_) _] => apply Inject_RealiseIn; [ smpl_dupfree | ]
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
 * [H : forall i : Fin.t _, not_indices (add_tapes _ m) i -> _]
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
  | [ H : forall i : Fin.t _, not_indices (add_tapes _ ?m) i -> _ |- _] =>
    simpl_not_in_add_tapes_loop H m; clear H
  | [ H : context [ (reorder (add_tapes _ ?m) _)[@_]] |- _ ] =>
    rewrite ! (add_tapes_reorder_nth (m := m)) in H; cbn in H
  | [ |- context [ (reorder (add_tapes _ ?m) _)[@_]] ] =>
    rewrite ! (add_tapes_reorder_nth (m := m)); cbn
  end.

Ltac simpl_not_in_add_tapes := repeat simpl_not_in_add_tapes_one.

(* Test *)
Goal True.
  assert (forall i : Fin.t 3, not_indices (add_tapes _ 2) i -> i = i) by firstorder.
  simpl_not_in_add_tapes. (* :-) *)
Abort.

Goal True.
  assert (n : nat) by constructor.
  assert (forall i : Fin.t (S n), not_indices (add_tapes n 1) i -> True) by firstorder.
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
  | [ H : forall i : Fin.t _, not_indices (app_tapes ?n ?m) i -> _ |- _] =>
    simpl_not_in_app_tapes_loop H n m; clear H
  | [ H : context [ (reorder (app_tapes ?n ?m) _)[@_]] |- _ ] =>
    rewrite ! (app_tapes_reorder_nth (n := n) (m := m)) in H; cbn in H
  | [ |- context [ (reorder (app_tapes ?n ?m) _)[@_]] ] =>
    rewrite ! (app_tapes_reorder_nth (n := n) (m := m)); cbn
  end.


Ltac simpl_not_in_app_tapes := repeat simpl_not_in_app_tapes_one.

Goal True.
  assert (forall i : Fin.t 10, not_indices (app_tapes 8 _) i -> i = i) as Inj by firstorder.
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
 * [H : forall i : Fin.t n, not_indices [F1; ...; Fk] i -> _]
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
  | [ H : forall i : Fin.t ?n, not_indices ?vect i -> _ |- _ ] =>
    simpl_not_in_vector_loop H vect n; clear H
  end.

Ltac simpl_not_in_vector := repeat simpl_not_in_vector_one.


(* Test *)
Goal True.
  assert (forall i : Fin.t 10, not_indices [|Fin8; Fin1; Fin2; Fin3|] i -> i = i) as HInj by firstorder.
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