Require Export TM.Prelim TM.TM TM.Code.Code.
Require Import TM.Combinators.SequentialComposition.
Require Import TM.Relations.
Require Export TM.Retract.
Require Import TM.LiftSigmaTau.
Require Import TM.Basic.Mono TM.Basic.WriteString.
Require Import TM.Compound.TMTac.
Require Import TM.Mirror.

Section Tape_Local.

  Variable sig : finType.

  Definition tape_local (t : tape sig) : list sig :=
    match t with
    | niltape _ => nil
    | leftof a l => nil
    | rightof _ _ => nil
    | midtape _ a l => a :: l
    end.

  Definition tape_local_l (t : tape sig) : list sig :=
    match t with
    | niltape _ => nil
    | leftof a l => nil
    | rightof _ _ => nil
    | midtape r a l => a :: r
    end.

  Lemma tape_local_mirror (t : tape sig) :
    tape_local_l (mirror_tape t) = tape_local t.
  Proof. destruct t; cbn; auto. Qed.

  Lemma tape_local_mirror' (t : tape sig) :
    tape_local (mirror_tape t) = tape_local_l t.
  Proof. destruct t; cbn; auto. Qed.
    
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

Hint Rewrite tape_local_mirror  : tape.
Hint Rewrite tape_local_mirror' : tape.
Hint Rewrite tape_local_current_cons using auto : tape.
Hint Rewrite tape_local_right        using auto : tape.
Hint Rewrite tape_left_move_right    using auto : tape.
Hint Rewrite tape_right_move_left    using auto : tape.


Lemma mapTape_local (sig tau : finType) (f : sig -> tau) t :
  tape_local (mapTape f t) = map f (tape_local t).
Proof. destruct t; cbn; reflexivity. Qed.

Hint Rewrite mapTape_local : tape.


Notation "sig '^+'" := (FinType(EqType(sig + bool))) (at level 0) : type_scope.

Section Fix_Sig.
  
  Variable (sig : finType).


  Section Tape_Encodes.

    Variable (X : Type) (cX : codeable sig X).

    (* Extend sig with a start end a end symbol *)

    (*
    Check sig^+.
    Check tapes sig^+ 42.
    Check (sig + bool) % type.
    *)

    Definition START : bool := false.
    Definition STOP  : bool := true.

    Instance codeX : codeable sig^+ X := Encode_Map cX          (@retract_inl sig bool).
    Instance codeS : codeable sig^+ bool := Encode_Map Encode_Bool (@retract_inr sig bool).

    Definition tape_encodes_r (t : tape sig^+) (x : X) (r1 r2 : list sig^+) :=
      left t = encode START ++ r1 /\ tape_local t = encode x ++ encode STOP ++ r2.

    Definition tape_encodes (t : tape sig^+) (x : X) : Prop :=
      exists r1 r2 : list sig^+, tape_encodes_r t x r1 r2.

    Lemma tape_encodes_r_injective (t : tape sig^+) (x1 x2 : X) (r1 r2 s1 s2 : list sig^+) :
      tape_encodes_r t x1 r1 r2 -> tape_encodes_r t x2 s1 s2 -> x1 = x2 /\ r1 = s1 /\ r2 = s2.
    Proof.
      intros (H2&H2') (H1&H1'). rewrite H2 in H1; clear H2. rewrite H2' in H1'. clear H2'. cbn in *.
      eapply encode_map_injective in H1' as (->&H2). inv H1. inv H2. tauto. eapply retract_inl.
    Qed.

    Lemma tape_encodes_injective (t : tape sig^+) (x1 x2 : X) :
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

    Definition Computes (f : X -> Y) : relation (tapes (sig ^+) n_tapes) :=
      fun tin tout =>
        forall (x : X),
          tape_encodes _ ( tin[@i]) x ->
          tape_encodes _ (tout[@j]) (f x).

    Definition Computes_Rel (f : X -> Y) : Rel (tapes sig^+ n_tapes) (F * tapes sig^+ n_tapes) :=
      ignoreParam (Computes f).

    Section Computes_Ext.

      Variable (f f' : X -> Y).
      Hypothesis (ext : forall x, f x = f' x).

      Lemma Computes_ext  :
        Computes f =2 Computes f'.
      Proof.
        split.
        - intros t t' H1. hnf in *. intros x. specialize (H1 x). rewrite (ext x) in H1. eauto.
        - intros t t' H1. hnf in *. intros x. specialize (H1 x). rewrite (ext x). eauto.
      Qed.

      Variable pM : { M : mTM sig^+ n_tapes & states M -> F }.

      Lemma Computes_Ext_WRealise :
        pM ⊫ Computes_Rel f' ->
        pM ⊫ Computes_Rel f.
      Proof.
        intros H. eapply WRealise_monotone.
        - eapply H.
        - hnf. intros tin (yout&tout) C. intros x e. specialize (C x e). rewrite ext. auto.
      Qed.

      Lemma Computes_Ext_Realise :
        pM ⊨ Computes_Rel f' ->
        pM ⊨ Computes_Rel f.
      Proof.
        intros H. eapply Realise_monotone.
        - eapply H.
        - hnf. intros tin (yout&tout) C. intros x e. specialize (C x e). rewrite ext. auto.
      Qed.

      Lemma Computes_Ext_RealiseIn (k : nat) :
        pM ⊨c(k) Computes_Rel f' ->
        pM ⊨c(k) Computes_Rel f.
      Proof.
        intros H. eapply RealiseIn_monotone.
        - eapply H.
        - omega.
        - hnf. intros tin (yout&tout) C. intros x e. specialize (C x e). rewrite ext. auto.
      Qed.

    End Computes_Ext.
  End Computes.

  Section Computes_Composes.
    Variable (X Y Z : Type) (cX : codeable sig X) (cY : codeable sig Y) (cZ : codeable sig Z).
    Variable (f : X -> Y) (g : Y -> Z).
    Variable (n_tapes : nat).
    Variable (i1 i2 i3 : Fin.t n_tapes).
    Variable (F1 F2 : finType).
    Variable (pM : {M : mTM sig^+ n_tapes & states M -> F1}).
    Variable (pN : {N : mTM sig^+ n_tapes & states N -> F2}).

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
    Variable F : finType.

    Definition Computes2 (f : X -> Y -> Z) : relation (tapes sig^+ n_tapes) :=
      fun tin tout =>
        forall (x : X) (y : Y),
          tape_encodes _ ( tin[@i]) x ->
          tape_encodes _ ( tin[@j]) y ->
          tape_encodes _ (tout[@k]) (f x y).

    Definition Computes2_Rel (f : X -> Y -> Z) :
      Rel (tapes sig^+ n_tapes) (F * tapes sig^+ n_tapes) := ignoreParam (Computes2 f).

  End Computes2.

End Fix_Sig.



Section Computes_Gen.

  Variable sig : finType.
  Variable n : nat.
  Variable F : finType.

  Variable (Res : Type).
  Hypothesis (codRes : codeable sig Res).
  Variable resTape : Fin.t n.

  (* Make a type for a curried function *)
  Fixpoint paramVectCoerce {k:nat} (paramTypes : Vector.t Type k) : Type :=
    match paramTypes with
    | Vector.nil _ => Res
    | t ::: paramTypes' => t -> paramVectCoerce paramTypes'
    end.

  Definition param_genT k := Vector.t ({ t : Type & codeable sig t} * Fin.t n) k.

  Definition param_genF k (params : param_genT k) :=
    paramVectCoerce (Vector.map (fun x => projT1 (fst x)) params).

  Fixpoint Computes_Gen {k:nat}
           (params : param_genT k)
           (f : param_genF params)
           {struct params} : relation (tapes (sig^+) n).
  Proof.
    intros tin tout. destruct params as [ | ((X&codX)&tapeX) k]; cbn in f.
    - apply (tape_encodes _ (tout[@resTape]) f).
    - specialize (Computes_Gen k).
      assert (IH : forall x : X,relation (tapes (sig^+) n)).
      {
        intros x. eapply Computes_Gen with (params := params). apply (f x).
      }
      apply ((forall x : X, tape_encodes codX (tin [@tapeX]) x -> IH x tin tout)).
  Defined.

  Variable (k : nat)
           (params : param_genT k)
           (f : param_genF params).

  Definition Computes_Gen_Rel : Rel (tapes (sig^+) n) (F * (tapes (sig^+) n)) :=
    ignoreParam (@Computes_Gen k params f).


End Computes_Gen.

Arguments Computes_Gen {sig} {n} {Res} (codRes) (resTape) {k} (params) (f).
Arguments Computes_Gen_Rel {sig} {n} F {Res} (codRes) (resTape) {k} (params) (f).

(* Check, that Computes_Gen coincises with Computes for [k := 1] *)
Section Test_Computes_Gen1.

  Variable sig : finType.
  Variable n_tapes : nat.
  Variable (i j : Fin.t n_tapes).
  Variable (X Y : Type) (cX : codeable sig X) (cY : codeable sig Y).
  Variable (f : X -> Y).
  Variable F : finType.

  Let gen1 := Computes_Gen cY j [| (existT _ _ cX, i) |] f.
  
  Lemma Computes_Gen_Computes : gen1 =2 Computes i j cX cY f.
  Proof.
    split; cbn; hnf; intuition.
  Qed.
  
End Test_Computes_Gen1.

(* Check, that Computes_Gen coincises with Computes2 for [k := 2] *)
Section Test_Computes_Gen2.
  Variable sig : finType.
  Variable n_tapes : nat.
  Variable (i j k : Fin.t n_tapes).
  Variable (X Y Z : Type) (cX : codeable sig X) (cY : codeable sig Y) (cZ : codeable sig Z).
  Variable (f : X -> Y -> Z).
  Variable F : finType.

  Let gen2 := Computes_Gen cZ k [| (existT _ _ cX, i); (existT _ _ cY, j) |] f.

  Lemma Computes_Gen_Computes2 : gen2 =2 Computes2 i j k cX cY cZ f.
  Proof.
    split; cbn; hnf.
    - intuition. hnf. intuition.
    - intuition.
  Qed.

End Test_Computes_Gen2.


(* Write a value to a tape *)
Section InitTape.

  Section Write_String_Rev.
    Variable sig : finType.

    (* This should go directly to WriteString.  It is a better definition *)
    
    Definition WriteStr_Rev_Rel (str:list sig) : Rel (tapes sig 1) (unit * tapes sig 1) :=
      Mk_R_p (ignoreParam (fun tin tout => right tout = str ++ right tin)).

    (*
    Section Test.
      Let t : tape (FinType(EqType(move))) := midtape [N;N;N;N;N] N [N;N;N;N;N].
      Let str := [R;R;R;R;R;R;N].
      Compute rev str ++ right t.
      Compute right (Tape_Write_String L t str).
      Compute right (Tape_Write_String L t (str ++ [L;R])).
      Compute Tape_Write_String L t (rev str).
      Compute Tape_Write_String L (Tape_Write_String L t [L;R]) str.
      Compute Tape_Write_String L t ([L;R] ++ str).
    End Test.
     *)

    Lemma Tape_Write_String_L_cont (str str' : list sig) (t : tape sig) :
      Tape_Write_String L t (str ++ str') = Tape_Write_String L (Tape_Write_String L t str) str'.
    Proof. revert t str'. induction str; intros; cbn in *; auto. Qed.

    Lemma Tape_Write_String_L_right' (str : list sig) : forall t : tape sig,
        right (Tape_Write_String L t str) = rev str ++ right t.
    Proof.
      induction str; intros; cbn in *; auto.
      destruct t; cbn; simpl_list; rewrite IHstr; cbn; auto.
      destruct l; cbn; auto.
    Qed.

    Lemma Tape_Write_String_L_right (str : list sig) : forall t : tape sig,
        right (Tape_Write_String L t (rev str)) = str ++ right t.
    Proof. intros. rewrite <- (rev_involutive str) at 2. apply Tape_Write_String_L_right'. Qed.

    Lemma WriteStr_Rev_Sem (str:list sig) :
      Write_String L tt (rev str) ⊨c(4 * |str|) WriteStr_Rev_Rel str.
    Proof.
      eapply RealiseIn_monotone.
      - eapply Write_string_Sem.
      - simpl_list. omega.
      - intros tin (()&tout); TMSimp; cbn in *; subst. clear H0. rename h0 into t. apply Tape_Write_String_L_right.
    Qed.

  End Write_String_Rev.
  

  Variable sig : finType.
  Variable X : Type.
  Hypothesis codX : codeable sig X.


  Definition InitTape_Rel (x : X) : Rel (tapes sig^+ 1) (unit * tapes sig^+ 1) :=
    Mk_R_p (ignoreParam (fun _ tout => tape_encodes _ tout x)).

  Definition InitTape (x : X) : { M : mTM sig^+ 1 & states M -> unit } :=
    Write_String L tt (rev (inr START :: map inl (encode (codeable := codX) x) ++ [inr STOP]));; Move _ R tt;; Move _ R tt.
                 

  Lemma InitTape_Sem (x : X) :
    InitTape x ⊨c(12 + 4 * |encode x|) InitTape_Rel x.
  Proof.
    eapply RealiseIn_monotone.
    - eapply Seq_RealiseIn. eapply WriteStr_Rev_Sem.
      eapply Seq_RealiseIn; eapply Move_Sem.
    - cbn. simpl_list. cbn. omega.
    - intros tin (()&tout). hnf. TMSimp; cbn in *; subst. destruct u, H1.
      destruct h1; cbn in *; inv H; cbn.
      + destruct (encode x) eqn:E; cbn; do 2 eexists; split; hnf; cbn; try rewrite E; simpl_list; cbn; eauto.
      + destruct (encode x) eqn:E; cbn; do 2 eexists; split; hnf; cbn; try rewrite E; simpl_list; cbn; eauto.
  Qed.

End InitTape.


(* Check, that Computes_Gen coincises with InitTape for [k := 0] *)

Section Test_InitTape_Gen0.
  Variable sig : finType.
  Variable (X : Type) (cX : codeable sig X).
  Variable x : X.

  Let gen0 := Computes_Gen cX (Fin.F1 (n := 0)) [||] x.

  Lemma Computes_Gen_InitTape :
    gen0 =2 InitTape_Rel cX x |_tt.
  Proof.
    hnf. split.
    - TMSimp cbn in *. do 2 eexists. split; hnf; cbn; eauto.
    - TMSimp cbn in *. do 2 eexists. split; hnf; cbn; eauto.
  Qed.
  
End Test_InitTape_Gen0.