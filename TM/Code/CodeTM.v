Require Export TM.Prelim TM.TM TM.Code.Code.
Require Import TM.Combinators.SequentialComposition.
Require Import TM.Relations.
Require Import TM.LiftSigmaTau.
Require Import TM.Basic.Mono TM.Basic.WriteString.
Require Import TM.Compound.TMTac.


(* Tape proposition that says that the pointer is on (but not off) the right-most symbol *)
Section IsRight.

  Definition isRight (sig : finType) (t : tape sig) :=
    exists x rs, t = midtape rs x nil.

   Definition isRight_size (sig : finType) (t : tape sig) (s : nat) :=
    exists x rs, t = midtape rs x nil /\ |rs| <= s.


   Lemma isRight_size_isRight (sig : finType) (t : tape sig) (s : nat) :
     isRight_size t s -> isRight t.
   Proof. intros (x&rs&->&_). hnf. eauto. Qed.

  Lemma isRight_size_monotone (sig : finType) (t : tape sig) (s1 s2 : nat) :
    isRight_size t s1 -> s1 <= s2 -> isRight_size t s2.
  Proof. intros (x&rs&->&Hr) Hs. exists x, rs. split. eauto. omega. Qed.

  Lemma mapTape_isRight (sig tau : finType) (t : tape sig) (f : sig -> tau) :
    isRight (mapTape f t) <-> isRight t.
  Proof.
    split.
    - intros (r1&r2&H). destruct t; cbn in *; inv H.
      apply map_eq_nil in H3 as ->. hnf. eauto.
    - intros (r1&r2&->). hnf. cbn. eauto.
  Qed.

  Lemma isRight_right (sig : finType) (t : tape sig) :
    isRight t -> right t = nil.
  Proof. now intros (x&rs&->). Qed.

  Lemma isRight_size_left (sig : finType) (t : tape sig) (s1 : nat) :
    isRight_size t s1 -> right t = nil.
  Proof. eauto using isRight_right, isRight_size_isRight. Qed.

  Lemma isRight_size_right (sig : finType) (t : tape sig) (s1 : nat) :
    isRight_size t s1 -> length (left t) <= s1.
  Proof. now intros (x&r1&->&H1). Qed.

  Lemma isRight_isRight_size (sig : finType) (t : tape sig) :
    isRight t -> isRight_size t (| tape_local_l t|).
  Proof. intros (x&r2&->). cbn. hnf. eauto. Qed.

End IsRight.

(*
Hint Resolve isLeft_size_isLeft isLeft_size_monotone mapTape_isLeft : tape.
Hint Resolve isLeft_left isLeft_size_left isLeft_size_right isLeft_isLeft_size : tape.
*)


(** Start symbol, isomorphic to unit *)

Inductive start : Type :=
| START : start.

Instance start_eq : eq_dec start.
Proof. intros. unfold dec. decide equality. Defined.

Instance start_fin : finTypeC (EqType start).
Proof. split with (enum := [START]). cbn. intros []. cbn. reflexivity. Defined.

Canonical Structure eqType_start : eqType := EqType start.
Canonical Structure finType_start : finType := FinType eqType_start.


Notation "sig '^+'" := (FinType(EqType(start + sig))) (at level 20) : type_scope.


Generalizable Variable X Y Z sig tau.

Section Fix_Sig.

  Variable (sig : finType).


  (** ** Value Containing *)

  Section Tape_Contains.

    Context `{cx : codeable sig X}.

    Definition tape_contains_r (t: tape (sig^+)) (x : X) (r1: list (sig^+)) :=
      exists y ys, encode x = (y :: ys : list sig) /\
              t = midtape (inl START :: r1) (inr y) (map inr ys).
              
    Definition tape_contains (t: tape (sig^+)) (x : X) :=
      exists y ys r1, encode x = (y :: ys : list sig) /\
                 t = midtape (inl START :: r1) (inr y) (map inr ys).

    Lemma tape_contains_r_contains (t: tape (sig^+)) (x : X) (r1: list (sig^+)) :
      tape_contains_r t x r1 -> tape_contains t x.
    Proof. unfold tape_contains, tape_contains_r. firstorder. Qed.


    Lemma tape_encodes_r_injective (t1 t2 : tape (sig^+)) (x : X) (r1 r2 : list (sig^+)) :
      tape_contains_r t1 x r1 ->
      tape_contains_r t2 x r2 ->
      r1 = r2 ->
      t1 = t2.
    Proof. intros (y&ys&H1&H2) (y'&ys'&H1'&H2'). congruence. Qed.

  End Tape_Contains.

  Arguments tape_contains : simpl never.
  Arguments tape_contains_r : simpl never.

  Notation "t '≃' x" := (tape_contains t x) (at level 70, no associativity).
  Notation "t '≃[' c ']' x" := (tape_contains (cx := c) t x) (at level 70, no associativity, only parsing).

  Section Encodes_Ext.
    Variable X : Type.
    Variable (cod1 cod2 : codeable sig X).

    Lemma tape_contains_ext (t : tape (sig^+)) (x : X) :
      encode (codeable := cod1) x = encode (codeable := cod2) x ->
      t ≃[cod1] x -> t ≃[cod2] x.
    Proof.
      Set Printing Implicit.
      intros HExt (y&ys&r1&HE&->). hnf. exists y, ys, r1. split; congruence.
    Qed.

    Lemma tape_encodes_ext' (t1 t2 : tape (sig^+)) (x : X) :
      encode (codeable := cod1) x = encode (codeable := cod2) x ->
      t1 = t2 ->
      t1 ≃[cod1] x -> t2 ≃[cod2] x.
    Proof.
      Set Printing Implicit.
      intros Heq -> (y&ys&r1&HE&->). hnf. exists y, ys, r1. split; congruence.
    Qed.

  End Encodes_Ext.




  (** ** Definition of the computation relations *)

  Section Computes.
    Variable n : nat.
    Context `{cX: codeable sig X} `{cY: codeable sig Y}.
    Variable F : finType.

    (*
     * Tape [t0] is the input tapes, [t2] is the output tape.
     * All further tapes are "internal tapes", i.e. they pointer is right before and after the execution.
     *)
    Definition Computes_Rel (f : X -> Y) :
      Rel (tapes (sig ^+) (S (S n))) (F * tapes (sig^+) (S (S n))) :=
      ignoreParam (
          fun tin tout =>
            forall (x : X),
              tin[@Fin0] ≃ x ->
              isRight tin[@Fin1] ->
              (forall i : Fin.t n, isRight tin[@Fin.FS(Fin.FS i)]) ->
              tout[@Fin0] ≃ x /\ (* Input value stayes unchanged *)
              tout[@Fin1] ≃ f x /\ (* output of the computation *)
              forall i : Fin.t n, isRight tout[@Fin.FS(Fin.FS i)]
        ).

    Definition Computes_T (r : X -> nat) : Rel (tapes (sig ^+) (S (S n))) nat :=
      fun tin k =>
        exists x : X,
          tin[@Fin0] ≃ x /\
          isRight tin[@Fin1] /\
          (forall i : Fin.t n, isRight tin[@Fin.FS(Fin.FS i)]) /\
          r x <= k.



    (** The computes relation is extensional *)
    Section Computes_Ext.
      Variable (f f' : X -> Y) (ext_fun : forall x, f x = f' x).

      Lemma Computes_ext :
        Computes_Rel f' <<=2 Computes_Rel f.
      Proof.
        intros tin (yout, tout) HRel. hnf. intros x EncX. specialize (HRel _ EncX). intuition congruence.
      Qed
.

      Variable pM : { M : mTM (sig^+) (S (S n)) & states M -> F }.

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
        destruct H as (x&H1&H2&H3&H4).
        hnf. exists x. repeat split; eauto. rewrite <- H4. apply mon.
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


  (** ** Computes relation with two arguments *)
  Section Computes2.
    Variable n : nat.
    (* WARNING: [Z] is overloaded in Coq with the type of integer numbers! *)
    Context `{cX: codeable sig X} `{cY: codeable sig Y} Z `{cZ: codeable sig Z}.
    Variable F : finType.

    (*
     * Tapes [t0] and [t1] are input tapes, [t2] is the output tape.
     * All further tapes are "internal tapes", i.e. they pointer is right before and after the execution.
     *)
    Definition Computes2_Rel (f : X -> Y -> Z) :
      Rel (tapes (sig ^+) (S (S (S n)))) (F * tapes (sig^+) (S (S (S n)))) :=
      ignoreParam (
          fun tin tout =>
            forall (x : X) (y : Y),
              tin[@Fin0] ≃ x ->
              tin[@Fin1] ≃ y ->
              isRight tin[@Fin2] ->
              (forall i : Fin.t n, isRight tin[@Fin.FS(Fin.FS (Fin.FS i))]) ->
              tout[@Fin0] ≃ x /\ (* First input value stayes unchanged *)
              tout[@Fin1] ≃ y /\ (* Second input value stayes unchanged *)
              tout[@Fin2] ≃ f x y /\
              forall i : Fin.t n, isRight tout[@Fin.FS(Fin.FS (Fin.FS i))]
        ).


    Definition Computes2_T (r : X -> Y -> nat) : Rel (tapes (sig ^+) (S (S (S n)))) nat :=
      fun tin k =>
        exists (x : X) (y : Y),
          tin[@Fin0] ≃ x /\
          tin[@Fin1] ≃ y /\
          isRight tin[@Fin2] /\
          (forall i : Fin.t n, isRight tin[@Fin.FS(Fin.FS (Fin.FS i))]) /\
          r x y <= k.

    Section Computes2_Ext.
      Variable (f f' : X -> Y -> Z) (ext_fun : forall x y, f x y = f' x y).

      Lemma Computes2_ext :
        Computes2_Rel f' <<=2 Computes2_Rel f.
      Proof.
        intros tin (yout, tout) HRel. hnf. intros x EncX y EncY. specialize (HRel x EncX y EncY). intuition congruence.
      Qed.

      Variable pM : { M : mTM (sig^+) (S (S (S n))) & states M -> F }.

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
        destruct H as (x&y&H1&H2&H3&H4&H5).
        hnf. exists x, y. repeat split; eauto. rewrite <- H5. apply mon.
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



Arguments Computes_Rel {sig n X cX Y cY F} f x y/.
Arguments Computes_T {sig n X cX} r x y/.

Arguments Computes2_Rel {sig n X cX Y cY Z cZ F} f x y/.
Arguments Computes2_T {sig n X cX Y cY} r x y/.


Notation "t ≃ x" := (tape_contains t x) (at level 70, no associativity, format "t  ≃  x").
Notation "t '≃(' c ')' x" := (tape_contains (cx := c) t x) (at level 70, no associativity, only parsing).


Notation "t ≃[ r1 ] x" := (tape_contains_r t x r1) (at level 70, no associativity, format "t  ≃[ r1 ]  x").
Notation "t '≃[' c ']' x" := (tape_contains (cx := c) t x) (at level 70, no associativity, only parsing).



(* begin hide *)
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
(* end hide *)


(* TODO *)

(*

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

*)


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