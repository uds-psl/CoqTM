Require Export TM.Prelim TM.TM TM.Code.Code.
Require Export TM.Lifting.Lifting.
Require Export TM.Combinators.Combinators.

(** * Value-Containing *)


Generalizable Variable X Y.


(** ** Right tapes *)

(** Tape proposition that says that the pointer is on (but not off) the right-most symbol *)
Section IsRight.

  Definition isRight (sig : Type) (t : tape sig) :=
    exists x rs, t = midtape rs x nil.

   Definition isRight_size (sig : Type) (t : tape sig) (s : nat) :=
    exists x rs, t = midtape rs x nil /\ |rs| <= s.


   Lemma isRight_size_isRight (sig : Type) (t : tape sig) (s : nat) :
     isRight_size t s -> isRight t.
   Proof. intros (x&rs&->&_). hnf. eauto. Qed.

  Lemma isRight_size_monotone (sig : Type) (t : tape sig) (s1 s2 : nat) :
    isRight_size t s1 -> s1 <= s2 -> isRight_size t s2.
  Proof. intros (x&rs&->&Hr) Hs. exists x, rs. split. eauto. omega. Qed.

  Lemma mapTape_isRight (sig tau : Type) (t : tape sig) (f : sig -> tau) :
    isRight (mapTape f t) <-> isRight t.
  Proof.
    split.
    - intros (r1&r2&H). destruct t; cbn in *; inv H.
      apply map_eq_nil in H3 as ->. hnf. eauto.
    - intros (r1&r2&->). hnf. cbn. eauto.
  Qed.

  Lemma isRight_right (sig : Type) (t : tape sig) :
    isRight t -> right t = nil.
  Proof. now intros (x&rs&->). Qed.

  Lemma isRight_size_left (sig : Type) (t : tape sig) (s1 : nat) :
    isRight_size t s1 -> right t = nil.
  Proof. eauto using isRight_right, isRight_size_isRight. Qed.

  Lemma isRight_size_right (sig : Type) (t : tape sig) (s1 : nat) :
    isRight_size t s1 -> length (left t) <= s1.
  Proof. now intros (x&r1&->&H1). Qed.

  Lemma isRight_isRight_size (sig : Type) (t : tape sig) :
    isRight t -> isRight_size t (| tape_local_l t|).
  Proof. intros (x&r2&->). cbn. hnf. eauto. Qed.

End IsRight.


(** We add these three symbols the alphabets of every machine. [START] is the first symbol of the encoding and [END] is always the right-most symbol. [UNKNOWN] is always ignored (it is needed for the alphabet-lift). *)
Inductive boundary : Type :=
| START   : boundary
| STOP    : boundary
| UNKNOWN : boundary.

(** Declare discreteness of [boundary] *)
Instance boundary_eq : eq_dec boundary.
Proof. unfold dec. decide equality. Defined.

(** Declare finiteness of [boundary] *)
Instance boundary_fin : finTypeC (EqType boundary).
Proof. split with (enum := [START; STOP; UNKNOWN]). cbn. intros []; cbn; reflexivity. Defined.


(** In this section, we define value-containing (≃). It is defined on tapes over arbitrary [Type]s (even infinite types), not [finType]. *)
Section Fix_Sig.

  Variable (sig : Type).

  Notation "sig '^+'" := ((boundary + sig) % type) (at level 0) : type_scope.


  (** A tape [t] contains a value [x], if [t=midtape rs (inl START) (map inr (encode x) ++ [inl STOP])] for some [rs : list (sig^+)]. This means, the pointer is on the start symbol, right to the pointer is the encoding of [x], which is terminated by the stop symbol [inl STOP]. We write [t ≃ x] for tape [t] contains [x]. *)

  (** We also define a dual predicate for value-containing: reversed value containing. It is, however, only used internally. The difference is, that the pointer is on the stop symbol, instead of the start symbol. This predicate is useful for intermediate states of a machine, for example in the machine [CopyValue], which first has to move the head to the stop symbol. We write [t ≂ x] for [t] reversedly contains [x]. *)

  Section Tape_Contains.
    Context `{cX : codable sig X}.

    Definition tape_contains' (t: tape sig^+) (x : X) :=
      exists r1, t = midtape r1 (inl START) (map inr (encode x) ++ [inl STOP]).
    Definition tape_contains := tape_contains'.

    Definition tape_contains_rev' (t: tape sig^+) (x : X) :=
      exists r1, t = midtape (map inr (rev (encode x)) ++ inl START :: r1) (inl STOP) nil.
    Definition tape_contains_rev := tape_contains_rev'.

    Lemma tape_contains_rev_isRight t x :
      tape_contains_rev t x ->
      isRight t.
    Proof. intros (r1&->). repeat econstructor. Qed.

  End Tape_Contains.

  Arguments tape_contains : simpl never.
  Arguments tape_contains_rev : simpl never.

  Arguments tape_contains' {X} (cX).
  Arguments tape_contains_rev' {X} (cX).

  (** The variant of the containing relations with prime allow to explicitely give and print the encoding of the type. *)
  Notation "t ≃ x" := (tape_contains t x) (at level 70, no associativity).
  Notation "t ≃( c ) x" := (tape_contains' c t x) (at level 70, no associativity).
  Notation "t ≂ x" := (tape_contains_rev t x) (at level 70, no associativity).
  Notation "t ≂( c ) x" := (tape_contains_rev' c t x) (at level 70, no associativity).


  Section Encodes_Ext.
    Context `{cX : codable sig X} `{cY : codable sig Y}.

    Lemma tape_contains_ext (t : tape (sig^+)) (x : X) (y : Y) :
      t ≃(cX) x ->
      cX x = cY y ->
      t ≃(cY) y.
    Proof. intros (r1&->) ->. now repeat econstructor. Qed.

    Lemma tape_contains_rev_ext (t : tape (sig^+)) (x : X) (y : Y) :
      t ≃(cX) x ->
      cX x = cY y ->
      t ≃(cY) y.
    Proof. intros (r1&->) ->. now repeat econstructor. Qed.

  End Encodes_Ext.


  (** Define tapes that contain a value or are right. *)
  Section InitTape.
    Context `{cX : codable sig X}.
    
    Definition initValue (x : X) :=
      midtape nil (inl START) (encode x ++ [inl STOP]).

    Lemma initValue_contains (x : X) :
      initValue x ≃ x.
    Proof. repeat econstructor. Qed.

    Definition initRight : tape sig^+ := midtape nil (inl STOP) nil.

    Lemma initRight_isRight : isRight initRight.
    Proof. repeat econstructor. Qed.

  End InitTape.



  (** ** Definition of the computation relations *)

  Section Computes.
    Variable n : nat.
    Context `{cX: codable sig X} `{cY: codable sig Y}.
    Variable F : Type.

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

    End Computes_Ext.
  End Computes.


  (** ** Computes relation with two arguments *)
  Section Computes2.
    Variable n : nat.
    (* WARNING: [Z] is overloaded in Coq with the type of integer numbers! *)
    Context `{cX: codable sig X} `{cY: codable sig Y} Z `{cZ: codable sig Z}.
    Variable F : Type.

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

      Variable (r1 r2 : X -> Y -> nat).
      Hypothesis mon : forall x y, r2 x y <= r1 x y.

      Lemma Computes2_Monotone  :
        Computes2_T r1 <<=2 Computes2_T r2.
      Proof.
        intros tin k H. hnf in H.
        destruct H as (x&y&H1&H2&H3&H4&H5).
        hnf. exists x, y. repeat split; eauto. rewrite <- H5. apply mon.
      Qed.

    End Computes2_Ext.
  End Computes2.
End Fix_Sig.



Arguments tape_contains : simpl never.
Arguments tape_contains_rev : simpl never.

(** In the ['] version, the encodings are explicit. With [unfold tape_contains in *], the encodings can be displayed. *)
Arguments tape_contains' {sig X} (cX).
Arguments tape_contains_rev' {sig X} (cX).

Notation "t ≃ x" := (tape_contains t x) (at level 70, no associativity).
Notation "t ≃( cX ) x" := (tape_contains' cX t x) (at level 70, no associativity, format "t  ≃( cX )  x").

Notation "t ≂ x" := (tape_contains_rev t x) (at level 70, no associativity).
Notation "t ≂( cX ) x" := (tape_contains_rev' cX t x) (at level 70, no associativity, format "t  ≂( cX )  x").



Arguments Computes_Rel {sig n X cX Y cY F} f x y/.
Arguments Computes_T {sig n X cX} r x y/.

Arguments Computes2_Rel {sig n X cX Y cY Z cZ F} f x y/.
Arguments Computes2_T {sig n X cX Y cY} r x y/.


(** Because every machine is defined on an alphabet [Σ^+], the notation adds the discreteness and finiteness constructors, to case [Σ^+ : finType]. *)
Notation "sig '^+'" := (FinType (EqType (boundary + sig) % type)) (at level 0) : type_scope.
