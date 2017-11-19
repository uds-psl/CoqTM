Require Import TM.Prelim TM.TM TM.Code.Code.
Require Import TM.Combinators.SequentialComposition.
Require Import TM.Relations.
Require Export TM.Retract.
Require Import TM.LiftSigmaTau.

Section Tape_Local.

  Variable sig : finType.

  Definition tape_local (t : tape sig) : list sig :=
    match t with
    | niltape _ => nil
    | leftof a l => nil
    | rightof _ _ => nil
    | midtape _ a l => a :: l
    end.

  Lemma tape_local_current_cons (x : sig) (xs : list sig) (t : tape sig) :
    tape_local t = x :: xs -> current t = Some x.
  Proof. destruct t eqn:E; cbn; congruence. Qed.

  Lemma tape_local_right (x : sig) (xs : list sig) (t : tape sig) :
    tape_local t = x :: xs -> right t = xs.
  Proof. destruct t eqn:E; cbn; congruence. Qed.

  Lemma tape_local_iff (t : tape sig) (xs : list sig) :
    (tape_local t = xs /\ xs <> nil) <-> (exists x xs', xs = x :: xs' /\ current t = Some x /\ right t = xs').
  Proof.
    split.
    - intros (H1&H2). destruct t eqn:E; cbn in *; try congruence. eauto.
    - intros (x&xs'&->&H1&<-). split. destruct t eqn:E; cbn in *; congruence. discriminate.
  Qed.

  Lemma tape_local_nil (t : tape sig) :
    tape_local t = nil <-> current t = None.
  Proof.
    destruct t; cbn; intuition; auto; congruence.
  Qed.

  Lemma tape_local_move_right (t : tape sig) (x : sig) (xs : list sig) :
    tape_local t = x :: xs -> tape_local (tape_move_right t) = xs.
  Proof.
    intro H. destruct t eqn:E; cbn in *; try congruence.
    inv H. destruct xs; cbn; auto.
  Qed.

  Lemma tape_left_move_right (t : tape sig) (x : sig) :
    current t = Some x -> left (tape_move_right t) = x :: left t.
  Proof. intros H. destruct t; cbn in *; try congruence. inv H. destruct l0; cbn; reflexivity. Qed.

  Lemma tape_right_move_left (t : tape sig) (x : sig) :
    current t = Some x -> right (tape_move_left t) = x :: right t.
  Proof. intros H. destruct t; cbn in *; try congruence. inv H. destruct l; cbn; reflexivity. Qed.

End Tape_Local.

Hint Rewrite tape_local_current_cons using auto : tape.
Hint Rewrite tape_local_right        using auto : tape.
Hint Rewrite tape_left_move_right    using auto : tape.
Hint Rewrite tape_right_move_left    using auto : tape.


Lemma mapTape_local (sig tau : finType) (f : sig -> tau) t :
  tape_local (mapTape f t) = map f (tape_local t).
Proof. destruct t; cbn; reflexivity. Qed.

Hint Rewrite mapTape_local : tape.


Section Fix_Sig.
  
  Variable (sig : finType).


  Section Tape_Encodes.

    Variable (X : Type) (cX : codeable sig X).

    (* Extend sig with a start end a end symbol *)
    Definition sig' : finType := FinType(EqType((sig + bool))) % type.

    Definition START : bool := false.
    Definition STOP  : bool := true.

    Instance codeX : codeable sig' X := Encode_Map cX          (@retract_inl sig bool).
    Instance codeS : codeable sig' bool := Encode_Map Encode_Bool (@retract_inr sig bool).

    Definition tape_encodes_r (t : tape sig') (x : X) (r1 r2 : list sig) :=
      left t = encode START ++ map inl r1 /\ tape_local t = encode x ++ encode STOP ++ map inl r2.

    Definition tape_encodes (t : tape sig') (x : X) : Prop :=
      exists r1 r2 : list sig, tape_encodes_r t x r1 r2.

    Lemma tape_encodes_r_injective (t : tape sig') (x1 x2 : X) (r1 r2 s1 s2 : list sig) :
      tape_encodes_r t x1 r1 r2 -> tape_encodes_r t x2 s1 s2 -> x1 = x2 /\ r1 = s1 /\ r2 = s2.
    Proof.
      intros (H2&H2') (H1&H1'). rewrite H2 in H1; clear H2. rewrite H2' in H1'. clear H2'. cbn in *.
      eapply (encode_map_injective) in H1' as (->&H1').
      inv H1. inv H1'.
      apply map_injective in H0 as ->. apply map_injective in H1 as ->.
      tauto. 1-2: auto_inj. eapply retract_inl.
    Qed.

    Lemma tape_encodes_injective (t : tape sig') (x1 x2 : X) :
      tape_encodes t x1 -> tape_encodes t x2 -> x1 = x2.
    Proof.
      intros (r1&r2&H2) (s1&s2&H1). eapply tape_encodes_r_injective; eauto.
    Qed.

  End Tape_Encodes.


  Section Computes.
    Variable n_tapes : nat.
    Variable (i j : Fin.t n_tapes).
    Variable (X Y : Type) (cX : codeable sig X) (cY : codeable sig Y).
    Variable F : finType.

    Definition Computes (f : X -> Y) : relation (tapes sig' n_tapes) :=
      fun tin tout =>
        forall (x : X),
          tape_encodes _ ( tin[@i]) x ->
          tape_encodes _ (tout[@j]) (f x).

    Definition Computes_Rel (f : X -> Y) : Rel (tapes sig' n_tapes) (F * tapes sig' n_tapes) :=
      ignoreParam (Computes f).

    Lemma Computes_ext (f f' : X -> Y) :
      (forall x, f x = f' x) -> Computes f =2 Computes f'.
    Proof.
      intros H. split.
      - intros t t' H1. hnf in *. intros x. specialize (H1 x). rewrite (H x) in H1. eauto.
      - intros t t' H1. hnf in *. intros x. specialize (H1 x). rewrite (H x). eauto.
    Qed.

  End Computes.


  Section Computes_Composes.
    Variable (X Y Z : Type) (cX : codeable sig X) (cY : codeable sig Y) (cZ : codeable sig Z).
    Variable (f : X -> Y) (g : Y -> Z).
    Variable (n_tapes : nat).
    Variable (i1 i2 i3 : Fin.t n_tapes).
    Variable (F1 F2 : finType).
    Variable (pM : {M : mTM sig' n_tapes & states M -> F1}).
    Variable (pN : {N : mTM sig' n_tapes & states N -> F2}).

    Lemma compose_Computes_Realise (iin iout : Fin.t n_tapes) :
      pM ⊨ Computes_Rel (F := F1) i1 i2 _ _ f ->
      pN ⊨ Computes_Rel (F := F2) i2 i3 _ _ g ->
      (pM ;; pN) ⊨ Computes_Rel (F := F2) i1 i3 _ _ (fun x => g (f x)).
    Proof.
      intros H1 H2. eapply Realise_monotone.
      - cbn. eapply Seq_Realise; eauto.
      - intros tx (tam, tz) H. hnf in H. destruct H as ((tam'&ty)&H&H'). hnf in H. hnf in H, H'. hnf. intros x Hx. auto.
    Qed.

    Lemma compose_Computes_WRealise (iin iout : Fin.t n_tapes) :
      pM ⊫ Computes_Rel (F := F1) i1 i2 _ _ f ->
      pN ⊫ Computes_Rel (F := F2) i2 i3 _ _ g ->
      (pM ;; pN) ⊫ Computes_Rel (F := F2) i1 i3 _ _ (fun x => g (f x)).
    Proof.
      intros H1 H2. eapply WRealise_monotone.
      - cbn. eapply Seq_WRealise; eauto.
      - intros tx (tam, tz) H. hnf in H. destruct H as ((tam'&ty)&H&H'). hnf in H. hnf in H, H'. hnf. intros x Hx. auto.
    Qed.
    
    Lemma compose_computes_RealiseIn (iin iout : Fin.t (S n_tapes)) (k1 k2 : nat) :
      pM ⊨c(k1) Computes_Rel (F := F1) i1 i2 _ _ f ->
      pN ⊨c(k2) Computes_Rel (F := F2) i2 i3 _ _ g ->
      (pM ;; pN) ⊨c(k1 + S k2) Computes_Rel (F := F2) i1 i3 _ _ (fun x => g (f x)).
    Proof.
      intros H1 H2. eapply RealiseIn_monotone.
      - cbn. eapply Seq_RealiseIn; eauto.
      - omega.
      - intros tx (tam, tz) H. hnf in H. destruct H as ((tam'&ty)&H&H'). hnf in H. hnf in H, H'. hnf. intros x Hx. auto.
    Qed.

  End Computes_Composes.

  Section Computes2.
    Variable n_tapes : nat.
    Variable (i j k : Fin.t n_tapes).
    Variable (X Y Z : Type) (cX : codeable sig X) (cY : codeable sig Y) (cZ : codeable sig Z).
    Variable f : X -> Y -> Z.
    Variable F : finType.

    Definition Computes2 : relation (tapes sig' n_tapes) :=
      fun tin tout =>
        forall (x : X) (y : Y),
          tape_encodes _ ( tin[@i]) x ->
          tape_encodes _ ( tin[@j]) y ->
          tape_encodes _ (tout[@k]) (f x y).

    Definition Computes2_Rel : Rel (tapes sig' n_tapes) (F * tapes sig' n_tapes) :=
      ignoreParam (Computes2).

  End Computes2.

End Fix_Sig.

Section Map_Dep.

  Inductive In' (X : Type) (x : X) : list X -> Type :=
  | In'_found xs   : In' x (x :: xs)
  | In'_skip x' xs : In' x xs -> In' x (x' :: xs).
  Hint Constructors In'.

  Lemma In'_dec (X : eqType) : forall (x : X) (xs : list X), ( In' x xs ) + ( In' x xs -> Empty_set ).
  Proof.
    intros x xs. revert x. induction xs as [ | s str IH ]; intros.
    - right. intros H. inv H.
    - decide (x = s) as [ -> | D].
      + left. constructor 1.
      + specialize (IH x) as [ IH | IH ].
        * left. constructor 2. assumption.
        * right. intros H. inv H; tauto.
  Qed.

  Lemma map_ext_in' :
    forall (A B : Type)(f g:A->B) l, (forall a, In' a l -> f a = g a) -> map f l = map g l.
  Proof.
    induction l; simpl; auto.
    intros; rewrite H by intuition; rewrite IHl; eauto using In'.
  Qed.

  Fixpoint map_dep (A B : Type) (l : list A) (f : forall a, In' a l -> B) { struct l } : list B.
  Proof.
    destruct l as [ | l ls ].
    - apply nil.
    - pose proof map_dep A B ls.
      spec_assert X.
      + intros a Ha. eapply f. constructor 2. apply Ha.
      + apply cons. eapply f. constructor 1. apply X.
  Defined.
  
  Lemma map_dep_ext (A B : Type) (l : list A) (f g : forall a, In' a l -> B) :
    (forall (a : A) (Ha : In' a l), f _ Ha = g _ Ha) ->
    map_dep (l := l) f = map_dep (l := l) g.
  Proof.
    revert f g. induction l as [ | l ls IH ]; cbn; intros; f_equal; auto.
  Qed.

  Lemma map_dep_nondep (A B : Type) (l : list A) (f : A -> B) :
    map_dep (l := l) (fun a _ => f a) = map f l.
  Proof.
    revert f. induction l as [ | l ls IH ]; cbn; intros.
    - reflexivity.
    - f_equal. rewrite IH. cbn. apply map_ext. auto.
  Qed.

  Lemma map_map_dep (A B C : Type) (l : list A) (f : forall b, In' b l -> B) (g : B -> C) :
      map g (map_dep f) = map_dep (fun x H => g (f x H)).
  Proof.
    induction l; simpl; auto. rewrite IHl; auto.
  Qed.

End Map_Dep.

    

Section MapSplit.

  Variable sig tau : finType.
  Variable (f : sig -> tau) (g : tau -> option sig).
  Hypothesis retr : tight_retract f g.
  Variable def : sig.
    
  Fixpoint map_split (str : list tau) :
    ({ x : list sig * tau * list tau |
       let '(r1,t,r2) := x in str = map f r1 ++ t :: r2 /\ g t = None }) +
    (forall t, In' t str -> { s | g t = Some s }).
  Proof.
    destruct str as [ | s str ]; cbn.
    - right. intros t H. inv H.
    - pose proof map_split str as [ (((r1&r2)&t)&->&IH) | IH ]; cbn in *.
      + destruct (g s) eqn:E1.
        * left. eexists (_,_,_); cbn. repeat split; eauto.
          instantiate (2 := e :: r1). cbn. f_equal. eapply tretract_g_inv'; eauto.
        * left. eexists (_,_,_); cbn. instantiate (4 := nil). cbn. eauto.
      + destruct (g s) eqn:E1.
        * right. intros t H. inv H; eauto.
        * left. eexists (_,_,_). instantiate (4 := nil). cbn. split; f_equal; eauto.
          (* instantiate (1 := map_dep (fun a H => proj1_sig (IH _ H))).
          rewrite map_map_dep. erewrite map_dep_ext. erewrite map_dep_nondep. rewrite map_id. reflexivity.
          intros a' Ha'. cbn. destruct (IH a' Ha') eqn:E'; cbn. symmetry. eapply tretract_g_inv'; eauto. *)
  Defined.

End MapSplit.

Section Test.
  (* Retract between [ move ] and [ move * move ], that just prepends N *)
  Let sig := FinType(EqType(move)).
  Let tau := FinType(EqType(move * move)).
  Let f := pair (B := FinType(EqType(move))) N.
  Let g := retract_pair_g (B := FinType(EqType(move))) N.
  Instance retract_f_g : tight_retract f g.
  Proof. unfold f, g. eapply retract_pair. Qed.

  Let def : sig := N.
  Compute f (R).
  Compute f (L).
  Compute g (R, L).
  Compute g (N, L).
  Compute g (N, R).

  Let str : list (tau + bool) := [inl (N,R); inr START; inl (R,N); inr STOP].
  Compute map (surject (retract_sum_g g Some) (inl def)) str.

  (*
  (* BUG: Derived function can't be Reseted. *)
  Require Coq.derive.Derive.
  Derive f'g' SuchThat (tight_retract (fst f'g') (snd f'g')) As retr'.
  Proof.
    instantiate (1 := sig' sig). instantiate (1 := sig' tau). cbn in *. subst f'g'.
    instantiate (1 := ( _ , _ )). cbn. eapply tretract_sum; auto_inj.
  Qed.

  Check map_split retr' str.
  *)

End Test.

Section Computes_Change_Alphabet.

  Variable sig tau : finType.
  Variable (f : sig -> tau) (g : tau -> option sig).
  Hypothesis retr : tight_retract f g.
  Variable def : sig.

  Variable (X Y Z : Type) (cX : codeable sig X) (cY : codeable sig Y).
  Variable (func : X -> Y).
  Variable (n_tapes : nat).
  Variable (i1 i2 : Fin.t n_tapes).
  Variable (F : finType).
  Variable (pM : {M : mTM (sig' sig) n_tapes & states M -> F}).

  Local Instance cX' : codeable tau X.
  Proof. eapply Encode_Map; eauto. Defined.

  Local Instance cY' : codeable tau Y.
  Proof. eapply Encode_Map; eauto. Defined.

  (*
  (* The following retract can be derived automatically. *)
  Let f' := @retract_sum_f sig bool tau bool f (@id bool).
  Let g' := @retract_sum_g sig bool tau bool g (@Some bool).
  Local Instance retr' : tight_retract f' g'.
  Proof. eapply tretract_sum; auto_inj. Qed.
*)

  Require Coq.derive.Derive.
  Derive f'g' SuchThat (tight_retract (fst f'g') (snd f'g')) As retr'.
  Proof.
    instantiate (1 := sig' sig). instantiate (1 := sig' tau). cbn in *. subst f'g'.
    instantiate (1 := ( _ , _ )). cbn. eapply tretract_sum; auto_inj.
  Qed.
  (*
  Set Printing Implicit. Print f'g'.
   *)
  Notation "'f''" := (fst f'g').
  Notation "'g''" := (snd f'g').


  Definition LiftCodeTM : { M : mTM (sig' tau) n_tapes & states M -> F } :=
    LiftSigmaTau.Lift pM (f') (g') (inl def).


  Lemma LiftCodeTM_Computes :
    pM ⊫ Computes_Rel i1 i2 cX cY func ->
    LiftCodeTM ⊫ Computes_Rel i1 i2 cX' cY' func.
  Proof.
    intros H. eapply WRealise_monotone.
    - unfold LiftCodeTM. eapply Lift_sem. apply tight_retract_strong. eapply retr'. eassumption.
    - hnf. intros tin (yout&tout) HComp. hnf in *. intros x. specialize (HComp x). intros HEnc.
      unfold surjectTapes in HComp.
      revert HEnc. intros HEnc.
      spec_assert HComp; [ | clear HEnc].
      + hnf in HEnc. hnf. destruct HEnc as (r1&r2&HEnc1&HEnc2).
        exists (map (surject g def) r1), (map (surject g def) r2). hnf. cbn.
        unfold mapTapes. erewrite !Vector.nth_map; eauto. simpl_tape. split.
        * rewrite HEnc1. cbn. f_equal.
          rewrite !map_map. eapply map_ext. intros a. unfold surject. cbn. destruct (g a); reflexivity.
        * rewrite HEnc2. cbn. simpl_list. rewrite !map_map. cbn. f_equal; [ | f_equal].
          -- apply map_ext. intros a. unfold surject. cbn. retract_adjoint. reflexivity.
          -- rewrite !map_map. apply map_ext. intros a. unfold surject. cbn. destruct (g a); reflexivity.
      +

        hnf in HComp. destruct HComp as (r1&r2&HComp1&HComp2). hnf in *.
        unfold mapTapes in *.
        repeat (
            erewrite !Vector.nth_map in HComp1, HComp2; eauto; simpl_tape in *; cbn in *
          ).
        (* Wahrheit bis hierhin *)

        (*
        revert HComp1 HComp2. generalize (tout[@i2]) as out. clear tout. intros out HEnc1 HEnc2.
        unfold tape_encodes_r. cbn in *.

        destruct (left out) eqn:E1; cbn in *; try congruence.
        unfold surject, retract_sum_g in HEnc1. destruct e; cbn in *.
        * destruct (g e) eqn:E2; congruence.
        * inv HEnc1.
          unfold surject, retract_sum_g in HEnc2. cbn in *.
          destruct (tape_local out) eqn:E2; cbn in *.
          -- destruct (encode (func x)); cbn in *; congruence.
          -- destruct e; cbn in *. destruct (g e) eqn:E3; cbn in *.
             ++ eexists. eexists. split. f_equal. admit. rewrite map_map; cbn. admit.
             ++ admit.
             ++ admit.
*)

        (*
        exists (map f r1), (map f r2). hnf in *. cbn in *. rewrite !map_map.
        apply (@surject_retract_sum_g_cons (left tout[@i2]) START nil r1) in  HComp1 as ->.
        apply surject_retract_sum_g_cons in HComp2 as ->. cbn.
        rewrite !map_map. cbn. split; reflexivity.
*)
  Admitted.

End Computes_Change_Alphabet.