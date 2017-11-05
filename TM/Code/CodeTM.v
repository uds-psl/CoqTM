Require Import TM.Prelim TM.TM TM.Code.Code.
Require Import TM.Combinators.SequentialComposition.
Require Import TM.Relations.

Require Import TM.Basic.Mono.
Require Import TM.Compound.FindSymbol.

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

End Tape_Local.


Section Fix_Sig.
  
  Variable (sig : finType).


  Section Tape_Encodes.

    Variable (X : Type) (cX : codeable sig X).

    (* Extend sig with a start end a end symbol *)
    Definition sig' : finType := FinType(EqType((sig + bool))) % type.

    Definition START : bool := false.
    Definition STOP  : bool := true.

    Instance codeX : codeable sig' X := Encode_Map cX (inl_inj sig bool).
    Instance codeS : codeable sig' bool := Encode_Map Encode_Bool (inr_inj sig bool).

    Definition tape_encodes_r (t : tape sig') (x : X) (r1 r2 : list sig) :=
      tapeToList t = map inl r1 ++ encode START ++ encode x ++ encode STOP ++ map inl r2.

    Definition tape_encodes (t : tape sig') (x : X) : Prop :=
      exists r1 r2 : list sig, tape_encodes_r t x r1 r2.

    Lemma tape_encodes_r_injective (t : tape sig') (x1 x2 : X) (r1 r2 s1 s2 : list sig) :
      tape_encodes_r t x1 r1 r2 -> tape_encodes_r t x2 s1 s2 -> x1 = x2 /\ r1 = s1 /\ r2 = s2.
    Proof.
      intros H2 H1. hnf in H1, H2. rewrite H2 in H1; clear H2. cbn in H1.
      pose proof (map_map_app_eq_None_None (inj := inl_inj sig bool)) as L1.
      specialize (L1 r1 s1 (inr START) (inr START) _ _ eq_refl eq_refl H1) as (L1&L2&L3).
      cbn in *. apply (encode_injective (codeable := codeX)) in L3 as (->&L4). inv L4; rename H0 into L4.
      apply map_injective in L1 as ->. apply map_injective in L4 as ->. tauto. all: firstorder congruence.
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


  (* Move the pointer to the start of the encoding *)
  Section InitTape1.

    Variable (X : Type) (cX : codeable sig X).

    Definition isStart := fun b : sig' => match b with inr true => true | _ => false end.

    Definition TapeInit : { M : mTM sig' 1 & states M -> unit } :=
      FindSymbol isStart ;; Move _ R tt.

    Definition TapeInit_Rel : Rel (tapes sig' 1) (unit * tapes sig' 1) :=
      Mk_R_p (fun t '(_, t') =>
                forall r1 r2 (x : X),
                  tape_encodes_r _ t x r1 r2 ->
                  left t' = inr START :: map inl r1 /\
                  tape_local t' = encode (codeable := codeX _) x ++ [inr STOP] ++ map inl r2
             ).

    Lemma TapeInit_Realise : TapeInit ⊨ TapeInit_Rel.
    Proof.
      eapply Realise_monotone.
      - unfold TapeInit. eapply Seq_Realise.
        + eapply FindSymbol_Realise.
        + eapply RealiseIn_Realise. eapply Move_Sem.
      - hnf. intros tin ((), tout). intros H. hnf in H. destruct H as ((t,y)&H1&H2&H3). hnf in *. intros r1 r2 x Hx. rewrite H3 in *; clear H3; subst.
    Admitted.
    

  End InitTape1.
  

End Fix_Sig.