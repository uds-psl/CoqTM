Require Export TM.Prelim TM.TM TM.Code.Code.
Require Import TM.Combinators.SequentialComposition.
Require Import TM.Relations.
Require Import TM.LiftSigmaTau.
Require Import TM.Basic.Mono TM.Basic.WriteString.
Require Import TM.Compound.TMTac.


Notation "sig '^+'" := (FinType(EqType(bool + sig))) (at level 0) : type_scope.


(* Tape proposition that says that the pointer is on (but not off) the left-most symbol *)
Section IsLeft.

  Definition isLeft (sig : finType) (t : tape sig) :=
    exists x rs, t = midtape nil x rs.

   Definition isLeft_size (sig : finType) (t : tape sig) (s : nat) :=
    exists x rs, |rs| <= s /\ t = midtape nil x rs.


   Lemma isLeft_size_isLeft (sig : finType) (t : tape sig) (s : nat) :
     isLeft_size t s -> isLeft t.
   Proof. intros (x&rs&_&->). hnf. eauto. Qed.

  Lemma isLeft_size_monotone (sig : finType) (t : tape sig) (s1 s2 : nat) :
    isLeft_size t s1 -> s1 <= s2 -> isLeft_size t s2.
  Proof. intros (x&rs&Hrs&->) Hs. exists x, rs. split. omega. auto. Qed.

  Lemma mapTape_isLeft (sig tau : finType) (t : tape sig) (f : sig -> tau) :
    isLeft (mapTape f t) <-> isLeft t.
  Proof.
    split.
    - intros (r1&r2&H). destruct t; cbn in *; inv H.
      apply map_eq_nil in H1 as ->. hnf. eauto.
    - intros (r1&r2&->). hnf. cbn. eauto.
  Qed.

  Lemma isLeft_left (sig : finType) (t : tape sig) :
    isLeft t -> left t = nil.
  Proof. now intros (x&rs&->). Qed.

  Lemma isLeft_size_left (sig : finType) (t : tape sig) (s1 : nat) :
    isLeft_size t s1 -> left t = nil.
  Proof. eauto using isLeft_left, isLeft_size_isLeft. Qed.

  Lemma isLeft_size_right (sig : finType) (t : tape sig) (s1 : nat) :
    isLeft_size t s1 -> length (right t) <= s1.
  Proof. now intros (x&r1&H1&->). Qed.

  Lemma isLeft_isLeft_size (sig : finType) (t : tape sig) :
    isLeft t -> isLeft_size t (| tape_local t|).
  Proof. intros (x&r2&->). cbn. hnf. eauto. Qed.

End IsLeft.

(*
Hint Resolve isLeft_size_isLeft isLeft_size_monotone mapTape_isLeft : tape.
Hint Resolve isLeft_left isLeft_size_left isLeft_size_right isLeft_isLeft_size : tape.
*)



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

    Definition tape_encodes_l (t : tape sig^+) (x : X) (r1 r2 : list sig^+) :=
      left t = inl START :: r1 /\ tape_local t = encode x ++ inl STOP :: r2.

    Definition tape_encodes_r (t : tape sig^+) (x : X) (r1 r2 : list sig^+) :=
      right t = inl STOP :: r2 /\ tape_local_l t = rev (encode x) ++ inl START :: r1.

    Definition tape_encodes_size (t : tape sig^+) (x : X) (size1 size2 : nat) :=
      exists (r1 r2 : list (sig^+)), length r1 <= size1 /\ length r2 <= size2 /\ tape_encodes_l t x r1 r2.

    Definition tape_encodes'_size (t : tape sig^+) (x : X) (size1 size2 : nat) :=
      exists (r1 r2 : list (sig^+)), length r1 <= size1 /\ length r2 <= size2 /\ tape_encodes_r t x r1 r2.

    Definition tape_encodes (t : tape sig^+) (x : X) : Prop :=
      exists r1 r2 : list (sig^+), tape_encodes_l t x r1 r2.

    Definition tape_encodes' (t : tape sig^+) (x : X) : Prop :=
      exists r1 r2 : list (sig^+), tape_encodes_r t x r1 r2.


    Lemma tape_encodes_l_injective (t1 t2 : tape sig^+) (x : X) (r1 r2 : list sig^+) :
      tape_encodes_l t1 x r1 r2 ->
      tape_encodes_l t2 x r1 r2 ->
      t1 = t2.
    Proof.
      intros (HE1&HE2) (HE1'&HE2').
      destruct t1; cbn in *; try congruence.
      now apply app_cons_not_nil in HE2.
      destruct t2; cbn in *; congruence.
    Qed.

    Lemma tape_encodes_r_injective (t1 t2 : tape sig^+) (x : X) (r1 r2 : list sig^+) :
      tape_encodes_r t1 x r1 r2 ->
      tape_encodes_r t2 x r1 r2 ->
      t1 = t2.
    Proof.
      intros (HE1&HE2) (HE1'&HE2').
      destruct t1; cbn in *; try congruence.
      now apply app_cons_not_nil in HE2.
      destruct t2; cbn in *; congruence.
    Qed.

    Lemma tape_encodes_l_functional (t : tape sig^+) (x1 x2 : X) (r1 r2 s1 s2 : list sig^+) :
      tape_encodes_l t x1 r1 r2 -> tape_encodes_l t x2 s1 s2 -> x1 = x2 /\ r1 = s1 /\ r2 = s2.
    Proof.
      intros (H2&H2') (H1&H1'). rewrite H2 in H1; clear H2. rewrite H2' in H1'. clear H2'. cbn in *.
      eapply encode_map_injective in H1' as (->&H2). inv H1. inv H2. tauto. eapply retract_inr.
    Qed.

    Notation "t '≂' x" := (tape_encodes t x) (at level 70, no associativity).

    Lemma tape_encodes_functional (t : tape sig^+) (x1 x2 : X) :
      t ≂ x1 -> t ≂ x2 -> x1 = x2.
    Proof.
      intros (r1&r2&H2) (s1&s2&H1). eapply tape_encodes_l_functional; eauto.
    Qed.

    Lemma tape_encodes_size_monotone (t : tape sig^+) (x : X) (size1 size1' size2 size2' : nat) :
      tape_encodes_size t x size1 size2 ->
      size1 <= size1' ->
      size2 <= size2' ->
      tape_encodes_size t x size1' size2'.
    Proof. intros (r1&r2&H1&H2&H3) H4 H5. hnf. exists r1, r2. split; [ | split; auto]; omega. Qed.

    Lemma tape_encodes_l_encodes (t : tape sig^+) (x : X) r1 r2 :
      tape_encodes_l t x r1 r2 -> tape_encodes t x.
    Proof. intros. hnf. eauto. Qed.

    Lemma tape_encodes_r_encodes' (t : tape sig^+) (x : X) r1 r2 :
      tape_encodes_r t x r1 r2 -> tape_encodes' t x.
    Proof. intros. hnf. eauto. Qed.

    Lemma tape_encodes_size_encodes (t : tape sig^+) (x : X) s1 s2 :
      tape_encodes_size t x s1 s2 -> tape_encodes t x.
    Proof. intros (r1&r2&HS1&HS2&HE). eauto using tape_encodes_l_encodes. Qed.

    Lemma tape_encodes'_size_encodes' (t : tape sig^+) (x : X) s1 s2 :
      tape_encodes'_size t x s1 s2 -> tape_encodes' t x.
    Proof. intros (r1&r2&HS1&HS2&HE). eauto using tape_encodes_r_encodes'. Qed.

    Lemma tape_encodes_l_encodes_size (t : tape sig^+) (x : X) r1 r2 :
      tape_encodes_l t x r1 r2 -> tape_encodes_size t x (|r1|) (|r2|).
    Proof. intros (H1&H2). hnf. exists r1, r2. repeat split; auto. Qed.

    Lemma tape_encodes_r_encodes'_size (t : tape sig^+) (x : X) r1 r2 :
      tape_encodes_r t x r1 r2 -> tape_encodes'_size t x (|r1|) (|r2|).
    Proof. intros (H1&H2). hnf. exists r1, r2. repeat split; auto. Qed.

  End Tape_Encodes.

  Arguments tape_encodes : simpl never.

  Notation "t '≂' x" := (tape_encodes _ t x) (at level 70, no associativity).
  Notation "t '≂[' c ']' x" := (tape_encodes c t x) (at level 70, no associativity, only parsing).

  Section Encodes_Ext.
    Variable X : Type.
    Variable (cod1 cod2 : codeable sig X).

    Lemma tape_encodes_ext (t : tape sig^+) (x : X) :
      encode (codeable := cod1) x = encode (codeable := cod2) x ->
      t ≂[cod1] x -> t ≂[cod2] x.
    Proof.
      Set Printing Implicit.
      intros HExt (r1&r2&HE1&HE2). exists r1, r2. split; cbn.
      - exact HE1.
      - rewrite HE2. cbn. f_equal. erewrite map_ext. f_equal. eapply HExt. auto.
        Unset Printing Implicit.
    Qed.

    Lemma tape_encodes_ext' (t1 t2 : tape sig^+) (x : X) :
      encode (codeable := cod1) x = encode (codeable := cod2) x ->
      t1 = t2 ->
      t1 ≂[cod1] x -> t2 ≂[cod2] x.
    Proof. intros ? ->. now eapply tape_encodes_ext; eauto. Qed.

  End Encodes_Ext.




  (** Definition of the computation relations *)

  Section Computes.
    Variable n : nat.
    Variable (X Y : Type) (cX : codeable sig X) (cY : codeable sig Y).

    (*
     * Tape [t0] is the input tapes, [t2] is the output tape.
     * All further tapes are "internal tapes", i.e. they pointer is left before and after the execution.
     *)
    Definition Computes_Rel (f : X -> Y) :
      Rel (tapes (sig ^+) (S (S n))) (unit * tapes sig^+ (S (S n))) :=
      ignoreParam (
          fun tin tout =>
            forall (x : X),
              tin[@Fin0] ≂ x ->
              (forall i : Fin.t n, isLeft tin[@Fin.FS(Fin.FS i)]) ->
              tout[@Fin0] ≂ x /\ (* Input value stayes unchanged *)
              tout[@Fin1] ≂ f x /\
              forall i : Fin.t n, isLeft tin[@Fin.FS(Fin.FS i)]
        ).

    Definition Computes_T (r : X -> nat) : Rel (tapes (sig ^+) (S (S n))) nat :=
      fun tin k =>
        exists x : X,
          tin[@Fin0] ≂ x /\
          (forall i : Fin.t n, isLeft tin[@Fin.FS(Fin.FS i)]) /\
          r x <= k.



    (* The computes relation must be extensional *)
    Section Computes_Ext.
      Variable (f f' : X -> Y) (ext_fun : forall x, f x = f' x).

      Lemma Computes_ext :
        Computes_Rel f' <<=2 Computes_Rel f.
      Proof.
        intros tin (yout, tout) HRel. hnf. intros x EncX. specialize (HRel _ EncX). intuition congruence.
      Qed
.

      Variable pM : { M : mTM sig^+ (S (S n)) & states M -> unit }.

      Lemma Computes_Ext_WRealise :
        pM ⊫ Computes_Rel f' ->
        pM ⊫ Computes_Rel f.
      Proof.
        intros H. eapply WRealise_monotone.
        - eapply H.
        - eapply Computes_ext.
      Qed.

      Lemma Computes_Ext_Realise :
        pM ⊨ Computes_Rel f' ->
        pM ⊨ Computes_Rel f.
      Proof.
        intros H. eapply Realise_monotone.
        - eapply H.
        - eapply Computes_ext.
      Qed.

      Lemma Computes_Ext_RealiseIn (k : nat) :
        pM ⊨c(k) Computes_Rel f' ->
        pM ⊨c(k) Computes_Rel f.
      Proof.
        intros H. eapply RealiseIn_monotone.
        - eapply H.
        - auto.
        - eapply Computes_ext.
      Qed.


      Variable (r1 r2 : X -> nat).
      Hypothesis mon : forall x, r2 x <= r1 x.

      Lemma Computes_Monotone  :
        Computes_T r1 <<=2 Computes_T r2.
      Proof.
        intros tin k H. hnf in H.
        destruct H as (x&H1&H2&H3).
        hnf. exists x. repeat split; eauto. rewrite <- H3. apply mon.
      Qed.

      Lemma Computes_T_Monotone :
        projT1 pM ↓ Computes_T r2 ->
        projT1 pM ↓ Computes_T r1.
      Proof.
        intros H. eapply TerminatesIn_monotone.
        - apply H.
        - apply Computes_Monotone.
      Qed.

    End Computes_Ext.
  End Computes.


  (** Computes relation with two arguments *)
  Section Computes2.
    Variable n : nat.
    Variable (X Y Z : Type) (cX : codeable sig X) (cY : codeable sig Y) (cZ : codeable sig Z).

    (*
     * Tapes [t0] and [t1] are input tapes, [t2] is the output tape.
     * All further tapes are "internal tapes", i.e. they pointer is left before and after the execution.
     *)
    Definition Computes2_Rel (f : X -> Y -> Z) :
      Rel (tapes (sig ^+) (S (S (S n)))) (unit * tapes sig^+ (S (S (S n)))) :=
      ignoreParam (
          fun tin tout =>
            forall (x : X) (y : Y),
              tin[@Fin0] ≂ x ->
              tin[@Fin1] ≂ y ->
              (forall i : Fin.t n, isLeft tin[@Fin.FS(Fin.FS (Fin.FS i))]) ->
              tout[@Fin0] ≂ x /\ (* First input value stayes unchanged *)
              tout[@Fin1] ≂ y /\ (* Second input value stayes unchanged *)
              tout[@Fin2] ≂ f x y /\
              forall i : Fin.t n, isLeft tin[@Fin.FS(Fin.FS (Fin.FS i))]
        ).


    Definition Computes2_T (r : X -> Y -> nat) : Rel (tapes (sig ^+) (S (S (S n)))) nat :=
      fun tin k =>
        exists (x : X) (y : Y),
          tin[@Fin0] ≂ x /\
          tin[@Fin1] ≂ y /\
          (forall i : Fin.t n, isLeft tin[@Fin.FS(Fin.FS (Fin.FS i))]) /\
          r x y <= k.

    Section Computes2_Ext.
      Variable (f f' : X -> Y -> Z) (ext_fun : forall x y, f x y = f' x y).

      Lemma Computes2_ext :
        Computes2_Rel f' <<=2 Computes2_Rel f.
      Proof.
        intros tin (yout, tout) HRel. hnf. intros x EncX y EncY. specialize (HRel x EncX y EncY). intuition congruence.
      Qed.

      Variable pM : { M : mTM sig^+ (S (S (S n))) & states M -> unit }.

      Lemma Computes2_Ext_WRealise :
        pM ⊫ Computes2_Rel f' ->
        pM ⊫ Computes2_Rel f.
      Proof.
        intros H. eapply WRealise_monotone.
        - eapply H.
        - eapply Computes2_ext.
      Qed.

      Lemma Computes2_Ext_Realise :
        pM ⊨ Computes2_Rel f' ->
        pM ⊨ Computes2_Rel f.
      Proof.
        intros H. eapply Realise_monotone.
        - eapply H.
        - eapply Computes2_ext.
      Qed.

      Lemma Computes2_Ext_RealiseIn (l : nat) :
        pM ⊨c(l) Computes2_Rel f' ->
        pM ⊨c(l) Computes2_Rel f.
      Proof.
        intros H. eapply RealiseIn_monotone.
        - eapply H.
        - auto.
        - eapply Computes2_ext.
      Qed.


      Variable (r1 r2 : X -> Y -> nat).
      Hypothesis mon : forall x y, r2 x y <= r1 x y.


      Lemma Computes2_Monotone  :
        Computes2_T r1 <<=2 Computes2_T r2.
      Proof.
        intros tin k H. hnf in H.
        destruct H as (x&y&H1&H2&H3&H4).
        hnf. exists x, y. repeat split; eauto. rewrite <- H4. apply mon.
      Qed.

      Lemma Computes2_T_Monotone :
        projT1 pM ↓ Computes2_T r2 ->
        projT1 pM ↓ Computes2_T r1.
      Proof.
        intros H. eapply TerminatesIn_monotone.
        - apply H.
        - eapply Computes2_Monotone.
      Qed.


    End Computes2_Ext.


  End Computes2.

End Fix_Sig.

Notation "t '≂' x" := (tape_encodes _ t x) (at level 70, no associativity).
Notation "t '≂[' r1 ';' r2 ] x" := (tape_encodes_l _ t x r1 r2) (at level 70, no associativity, format "t  '≂[' r1 ;  r2 ]  x").
Notation "t '≂{' r1 ';' r2 } x" := (tape_encodes_size _ t x r1 r2) (at level 70, no associativity, format "t  '≂{' r1 ;  r2 }  x").
Notation "t '≃[' r1 ';' r2 ] x" := (tape_encodes_r _ t x r1 r2) (at level 70, no associativity, format "t  '≃[' r1 ;  r2 ]  x").
Notation "t '≃{' r1 ';' r2 } x" := (tape_encodes'_size _ t x r1 r2) (at level 70, no associativity, format "t  '≃{' r1 ;  r2 }  x").



(*
Section Computes_Gen.

  Variable sig : finType.
  Variable n : nat.
  Variable F : finType.


  Variable (Res : Type).
  Hypothesis (codRes : codeable sig Res).
  Variable resTape : Fin.t n.


  (* Make a type for a curried function *)
  Fixpoint paramVectCoerce (paramTypes : list Type) : Type :=
    match paramTypes with
    | nil => Res
    | t :: paramTypes' => t -> paramVectCoerce paramTypes'
    end.


  Record comp_gen_param :=
    mk_param
      {
        par_tape :> Fin.t n;
        par_type : Type;
        par_code :> codeable sig par_type;
      }.

  Definition param_genF (params : list comp_gen_param) :=
    paramVectCoerce (map par_type params).


  Fixpoint Computes_Gen
           (params : list comp_gen_param)
           (f : param_genF params)
           {struct params} : relation (tapes (sig^+) n).
  Proof.
    intros tin tout. destruct params as [ | (tapeX, X, codX) params']; cbn in f.
    - apply (tape_encodes _ (tout[@resTape]) f).
    - apply (forall x : X, tape_encodes codX (tin[@tapeX]) x -> @Computes_Gen params' (f x) tin tout).
  Defined.

  Definition Computes_Gen_Rel
             (params : list comp_gen_param)
             (f : param_genF params) : Rel (tapes (sig^+) n) (F * (tapes (sig^+) n)) :=
    ignoreParam (@Computes_Gen params f).

  Definition params_tapes (params : list comp_gen_param) : list (Fin.t n) := map par_tape params.

  Lemma Computes_Gen_Ext
        (params : list comp_gen_param)
        (f : param_genF params)
        tin tin' tout :
    (forall param, List.In param params ->
              forall x : par_type param,
                tape_encodes (par_code param) tin'[@par_tape param] x ->
                tape_encodes (par_code param) tin [@par_tape param] x) ->
    @Computes_Gen params f tin tout -> @Computes_Gen params f tin' tout.
  Proof.
    intros H HComp.
    induction params as [ | (tapeX, X, codX) params' IH]; cbn in *; intros; auto.
    apply IH; eauto. apply HComp. cbn in *. specialize (H _ ltac:(eauto) ltac:(eauto)). auto.
  Qed.

End Computes_Gen.

Arguments Computes_Gen {sig} {n} {Res} (codRes) (resTape) (params) (f).
Arguments Computes_Gen_Rel {sig} {n} F {Res} (codRes) (resTape) (params) (f).

(* Check, that Computes_Gen coincises with Computes for [k := 1] *)
Section Test_Computes_Gen1.

  Variable sig : finType.
  Variable n_tapes : nat.
  Variable (i j : Fin.t n_tapes).
  Variable (X Y : Type) (cX : codeable sig X) (cY : codeable sig Y).
  Variable (f : X -> Y).
  Variable F : finType.

  Definition gen1 := Computes_Gen cY j [| (mk_param i cX) |] f.

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

  Definition gen2 := Computes_Gen cZ k [| mk_param i cX; mk_param j cY |] f.

  Lemma Computes_Gen_Computes2 : gen2 =2 Computes2 i j k cX cY cZ f.
  Proof.
    split; cbn; hnf.
    - intuition. hnf. intuition.
    - intuition.
  Qed.

End Test_Computes_Gen2.
 *)


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
        right (Tape_Write_String L t str) = List.rev str ++ right t.
    Proof.
      induction str; intros; cbn in *; auto.
      destruct t; cbn; simpl_list; rewrite IHstr; cbn; auto.
      destruct l; cbn; auto.
    Qed.

    Lemma Tape_Write_String_L_right (str : list sig) : forall t : tape sig,
        right (Tape_Write_String L t (List.rev str)) = str ++ right t.
    Proof. intros. rewrite <- (rev_involutive str) at 2. apply Tape_Write_String_L_right'. Qed.

    Lemma WriteStr_Rev_Sem (str:list sig) :
      Write_String L tt (List.rev str) ⊨c(4 * |str|) WriteStr_Rev_Rel str.
    Proof.
      eapply RealiseIn_monotone.
      - eapply Write_string_Sem.
      - simpl_list. omega.
      - intros tin (()&tout); TMSimp; subst. clear H0. apply Tape_Write_String_L_right.
    Qed.

  End Write_String_Rev.


  Variable sig : finType.
  Variable X : Type.
  Hypothesis codX : codeable sig X.

  Definition InitTape_Rel (x : X) : Rel (tapes sig^+ 1) (unit * tapes sig^+ 1) :=
    Mk_R_p (ignoreParam (fun _ tout => tape_encodes _ tout x)).

  Definition InitTape (x : X) : { M : mTM sig^+ 1 & states M -> unit } :=
    Write_String L tt (List.rev (inl START :: List.map inr (encode (codeable := codX) x) ++ [inl STOP]));; Move _ R tt;; Move _ R tt.


  Lemma InitTape_Sem (x : X) :
    InitTape x ⊨c(12 + 4 * |encode x|) InitTape_Rel x.
  Proof.
    eapply RealiseIn_monotone.
    - eapply Seq_RealiseIn. eapply WriteStr_Rev_Sem.
      eapply Seq_RealiseIn; eapply Move_Sem.
    - cbn. simpl_list. cbn. omega.
    - intros tin (()&tout). hnf. TMSimp; clear_trivial_eqs; subst.
      destruct_tapes; cbn in *. subst.
      destruct h0; cbn in *; inv H; cbn.
      + simpl_tape. destruct (encode x) eqn:E; cbn; do 2 eexists; split; hnf; cbn; try rewrite E; simpl_list; cbn; eauto.
      + destruct (encode x) eqn:E; cbn; do 2 eexists; split; hnf; cbn; try rewrite E; simpl_list; cbn; eauto.
  Qed.

End InitTape.


(*
(* Check, that Computes_Gen coincises with InitTape for [k := 0] *)

Section Test_InitTape_Gen0.
  Variable sig : finType.
  Variable (X : Type) (cX : codeable sig X).
  Variable x : X.

  Definition gen0 := Computes_Gen cX (Fin.F1 (n := 0)) [||] x.

  Lemma Computes_Gen_InitTape :
    gen0 =2 InitTape_Rel cX x |_tt.
  Proof.
    hnf. split.
    - TMSimp. do 2 eexists. split; hnf; cbn; eauto.
    - TMSimp. do 2 eexists. split; hnf; cbn; eauto.
  Qed.

End Test_InitTape_Gen0.
 *)