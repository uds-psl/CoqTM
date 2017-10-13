Require Import Match.

Section Composition.
  
  Variable n : nat.
  Variable sig : finType.

  
  Variable F : finType.
  Variable pM1 : {M1 : mTM sig n & states M1 -> F}.

  Variable F2 : finType.
  Variable pM2 : { M2 : mTM sig n & states M2 -> F2}.
  
  Definition Seq := MATCH pM1 (fun _ => pM2).

  Lemma Seq_sem (R1 : Rel _ (_ * _)) (R2 : Rel _ (F2 * _)) :
    pM1 ⊫ R1 ->
    pM2 ⊫ R2 ->
    Seq ⊫ (R1 ∘ hideParam R2).
  Proof.
    intros.
    eapply WRealise_monotone. eapply (Match_sem (R1 := R1) (R2 := (fun _ => R2))); destruct pM2; eauto.
    intros ? ? ?. eapply finite_rel_union_spec in H1. firstorder.
  Qed.

  Lemma Seq_terminatesIn (R1 : Rel _ (F * _)) T1 T2:
    functionalOn T1 R1 ->
    pM1 ⊫ R1 ->
    projT1 pM1 ↓(T1) ->
    projT1 pM2 ↓(T2) ->
    projT1 Seq ↓(fun (x : tapes sig n) (i : nat) =>
            exists (j k : nat) (y : tapes sig n) (f : F),
              R1 x (f, y) /\ T1 x j /\ T2 y k /\ j + k < i).
  Proof.
    intros.
    eapply terminatesIn_monotone. eapply (Match_terminatesIn (R1 := R1) (T := fun _ => T2) ); eauto.
    intros ? ? (? & ? & ? & ? & ? & ? & ? & ?). eapply finite_rel_union_spec.
    eauto 10.
  Qed.

  Lemma Seq_total (R1 : Rel _ _) (R2 : Rel _ (F2 * _)) k1 k2:
    pM1 ⊨(k1) R1 ->
    pM2 ⊨(k2) R2 ->
    Seq ⊨(1 + k1 + k2) (R1 ∘ hideParam R2).
  Proof.
    intros.
    eapply RealiseIn_monotone.
    eapply (Match_total (R2 := fun _ => R2)) ; destruct pM1, pM2; eauto.
    - omega.
    - intros ? ? ?. eapply finite_rel_union_spec in H1. firstorder.
  Qed.

End Composition.

Notation "A ;; B" := (Seq A B) (right associativity, at level 65).

(* Section Composition. *)

(*   Variable n : nat. *)
(*   Variable sig : finType. *)

(*   Variable M1 : mTM sig n. *)
(*   Variable M2 : mTM sig n. *)

(*   Definition null_action m := repeatVector m (@None sig, N). *)

(*   Lemma tape_move_null_action m tapes : *)
(*     tape_move_multi tapes (null_action m) = tapes. *)
(*   Proof. *)
(*     clear M1 M2. induction tapes; cbn in *; eauto using f_equal. *)
(*   Qed. *)

(*   Definition seq_trans := *)
(*     fun (p : (TM.states M1 + TM.states M2) * Vector.t (option sig) (S n)) => let (s,a) := p in *)
(*           match s with *)
(*           | inl s1 => if halt s1 then (inr (start M2), null_action (S n)) *)
(*                      else let (news1,m) := trans (s1,a) in (inl news1, m) *)
(*           | inr s2 => let (news2, m) := trans (s2, a) in (inr news2, m) *)
(*           end. *)

(*   Definition Seq : mTM sig n := *)
(*     Build_mTM seq_trans (inl (start M1)) *)
(*               (fun s => match s with *)
(*                      | inl _ => false *)
(*                      | inr s0 => halt s0 *)
(*                      end). *)

(*   Definition lift_confL (c : mconfig sig (states M1) n) : mconfig sig (states Seq) n := *)
(*     mk_mconfig (inl (cstate c)) (ctapes c).  *)


(*   Definition lift_confR (c : mconfig sig (states M2) n) : mconfig sig (states Seq) n := *)
(*     mk_mconfig (inr (cstate c)) (ctapes c). *)

(*   Lemma step_seq_liftL c0 : *)
(*     halt (cstate c0) = false -> step (lift_confL c0) = lift_confL (step c0). *)
(*   Proof. *)
(*     destruct c0. unfold lift_confL, step. cbn. intros. destruct * eqn:_. now inv H1. *)
(*   Qed. *)

(*   Lemma step_seq_liftR c0 : *)
(*     step (lift_confR c0) = lift_confR (step c0). *)
(*   Proof. *)
(*     destruct c0. unfold lift_confR, step. cbn. destruct * eqn:_. now inv H0. *)
(*   Qed. *)

(*   Definition halt_liftL (c : mconfig sig _ n) := *)
(*     match cstate c with *)
(*     | inl s => halt (m := M1) s *)
(*     | inr s => halt (m := M2) s *)
(*     end. *)

(*   Definition lift_partR F (p : (states M2) -> F) : (states Seq) -> F:= *)
(*      fun s => match s with *)
(*            | inl _ => p (start M2) (* garbage *) *)
(*            | inr s => p s *)
(*            end. *)

(*   Lemma Seq_merge x (x0 : mconfig sig (states M1) n) x1 x2 t: *)
(*     loopM x (initc M1 t) = Some x0 -> *)
(*     loopM x1 (initc M2 (ctapes x0)) = Some x2 -> loopM (x + (1 + x1)) (initc Seq t) = Some (lift_confR x2).  *)
(*   Proof. *)
(*     intros H H1. *)
(*     unfold loopM. *)
(*     eapply (loop_merge (p := halt_liftL) (a2 := lift_confL x0)). *)
(*     - intros ? H3. cbn. unfold halt_liftL in H3. now destruct cstate.  *)
(*     - unfold loopM in H. cbn. *)
(*       eapply loop_lift with (lift := lift_confL) (hlift := halt_liftL) in H; eauto. *)
(*       + firstorder. rewrite step_seq_liftL; eauto.  *)
(*     - change (loop (1 + x1) (step (M:=Seq)) (fun c : mconfig sig (states Seq) n => halt (cstate c)) (lift_confL x0)) with (loop x1 (step (M:=Seq)) (fun c : mconfig sig (states Seq) n => halt (cstate c)) (step (lift_confL x0))). *)
(*       eapply loop_lift with (lift := lift_confR) (hlift := (fun x => halt (m := Seq) (cstate x))) in H1;eauto. *)
(*       + cutrewrite  (step (lift_confL x0) = (lift_confR (initc M2 (ctapes x0)))); eauto. *)
(*         destruct x0. unfold lift_confL, lift_confR. unfold step. *)
(*         cbn -[null_action tape_move_multi]. cutrewrite (halt cstate = true). f_equal. *)
(*         eapply tape_move_null_action. eapply loop_fulfills_p in H. *)
(*         cbn in H; destruct (halt cstate); auto. *)
(*       + firstorder. now rewrite step_seq_liftR. *)
(*   Qed. *)

(*   Definition unlift_1 : mconfig sig (FinType (EqType (states M1 + states M2))) n -> option (mconfig sig (states M1) n). *)
(*   Proof. *)
(*     intros m. destruct m. destruct cstate. left. econstructor. exact e. exact ctapes. right. *)
(*   Defined. *)

(*   Definition unlift_2 : mconfig sig (FinType (EqType (states M1 + states M2))) n -> option (mconfig sig (states M2) n). *)
(*   Proof. *)
(*     intros m. destruct m. destruct cstate. right. left. econstructor. exact e. exact ctapes.  *)
(*   Defined. *)

(*   Lemma unlift_2_step (a : mconfig sig (states Seq) n)( a' : mconfig sig (states M2) n) : *)
(*     unlift_2 a = Some a' -> halt (cstate a') = false -> unlift_2 (step a) = Some (step a'). *)
(*   Proof. *)
(*     destruct a. unfold unlift_2, step, trans. cbn. intros. *)
(*     destruct cstate eqn:E; inv H. cbn in *. destruct M2. cbn. *)
(*     destruct trans. reflexivity. *)
(*   Qed. *)

(*   Lemma unlift_1_step (a : mconfig sig (states Seq) n) *)
(*      ( a' : mconfig sig (states M1) n) : unlift_1 a = Some a' -> halt (cstate a') = false -> unlift_1 (step a) = Some (step a'). *)
(*   Proof. *)
(*     destruct a. unfold unlift_1, step, trans. cbn. intros. *)
(*     destruct cstate eqn:E; inv H. cbn in *. rewrite H0. unfold trans.  *)
(*     destruct M1. cbn in *. destruct trans. reflexivity. *)
(*   Qed. *)

(*   Lemma Seq_split i res t: *)
(*     loopM i (initc Seq t) = Some res -> *)
(*     (exists i1 x1 i2 x2,  loopM i1 (initc M1 t) = Some x1 /\ *)
(*                      loopM i2 (initc M2 (ctapes x1)) = Some x2 /\ i = 1 + i1 + i2 /\ res = (lift_confR x2)). *)
(*   Proof. *)
(*     intros. *)
(*     unfold loopM in H. *)
(*     eapply loop_split in H. *)
(*     destruct H as (i1 & x1 & i2 & H1 & H2 & Hi). *)
(*     eapply loop_unlift with (unlift := unlift_1) *)
(*                             (f' := step (M := M1)) *)
(*                             (p' := fun c => halt (m := M1) (cstate c)) *)

(*       in H1 as (x' & Hx' & Hu). *)
(*     exists i1, x'. *)
(*     - unfold loopM at 1. rewrite Hx'. *)
(*       destruct x1. unfold unlift_1 in Hu. cbn in Hu. destruct cstate; inv Hu. *)
(*       destruct i2; try now inv H2. cbn -[halt] in H2. unfold halt at 1 in H2. cbn -[halt] in H2. *)
(*       unfold step at 2 in H2. cbn -[halt] in H2. *)
(*       assert (halt e = true). eapply loop_fulfills_p in Hx'. cbn in Hx'. cbn in Hx'. destruct (halt e); auto. rewrite H in H2. *)
(*       remember ((mk_mconfig (inr (start M2)) *)
(*             (Vector.map2 (tape_move_mono (sig:=sig)) ctapes *)
(*                (Vector.cons (option sig * move) (None, N) n (repeatVector n (None, N)))))) as x2. *)
(*       eapply loop_unlift with (unlift := unlift_2) *)
(*                               (f' := step (M := M2)) *)
(*                               (p' := fun c => halt (m := M2) (cstate c)) *)
(*                               (p := fun c => halt (m := Seq) (cstate c)) *)
(*         in H2 as (x'' & Hx'' & Hu'). *)
(*       + exists i2. exists x''. intuition. eapply Hx''. omega. destruct x''. unfold lift_confR. cbn. destruct res. unfold unlift_2 in *. cbn in Hu'. destruct cstate0; inv Hu'. reflexivity. *)
(*       + intuition. exists (step (M := M2) a'). intuition. now eapply unlift_2_step. *)
(*       + intuition. cbn. unfold halt. destruct a. unfold unlift_2 in H0. *)
(*         destruct cstate. inv H0. inv H0. cbn. reflexivity. *)
(*       + subst. cbn. assert (T := tape_move_null_action ctapes). cbn in T. unfold tape_move_multi in T. *)
(*         rewrite T. reflexivity. *)
(*     - intuition. exists (step (M := M1) a'). intuition. now eapply unlift_1_step.  *)
(*     - intros. instantiate (1 := fun x => match cstate x with inl s => halt (m := M1) s | _ => true end). *)
(*       cbn. unfold unlift_1 in H. destruct a. destruct cstate. inv H. reflexivity. inv H. *)
(*     - cbn. reflexivity. *)
(*     - intros. cbn in *. destruct cstate. reflexivity. inv H0. *)
(*   Qed. *)

(*   Lemma Seq_sem (F1 F2:finType) p1 p2 (R1 : PRel _ F1) (R2 : PRel _ F2) : *)
(*     WRealise M1 p1 R1 -> WRealise M2 p2 R2 -> WRealise Seq (lift_partR p2) (prcomp R1 R2). *)
(*   Proof. *)
(*     intros HR1 HR2 t1 i1 oenc2 eq. *)
(*     apply Seq_split in eq as (?&?&?&?&Eq1&Eq2&->&->). *)
(*     apply HR1 in Eq1. apply HR2 in Eq2. *)
(*     eexists _,_. unfold lift_partR. cbn. eauto. *)
(*   Qed. *)

(*   Definition termComp X F (R1: PRel X F) (T1 T2 :X -> nat -> Prop) : X -> nat -> Prop:= *)
(*     (fun x i => (exists j k y f , R1 x f y /\ T1 x j /\ T2 y k /\ j + k < i)). *)

(*   Definition functionalOn X F (T : X -> nat -> Prop) (R : PRel X F) := *)
(*     forall x i, T x i -> forall f1 f2 y1 y2, R x f1 y1 -> R x f2 y2 -> y1 = y2. *)

(*   Lemma Seq_terminatesIn (F : finType) (R1 : PRel _ F) T1 T2 f: *)
(*     functionalOn T1 R1 -> *)
(*     WRealise M1 f R1 -> terminatesIn M1 T1 -> terminatesIn M2 T2 -> terminatesIn Seq (termComp R1 T1 T2) . *)
(*   Proof. *)
(*     intros Func Real1 Term1 Term2 t i (?&?&t'&?&?&Term_t1&Term_t2&?). *)
(*     destruct (Term1 _ _ Term_t1) as [t'' ?]. *)
(*     destruct (Term2 _ _ Term_t2) as [outc ?]. *)
(*     exists (lift_confR outc). *)
(*     unfold loopM. *)
(*     eapply loop_ge with (k1:=x+(1+x0)). omega. *)
(*     eapply Seq_merge. *)
(*     exact H1. rewrite <- H2. eapply Real1 in H1. *)
(*     repeat f_equal. eapply Func; eauto. *)
(*   Qed. *)

(* End Composition. *)

(* Notation "A ; B" := (Seq A B) (right associativity, at level 65). *)

