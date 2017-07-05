Require Import Prelim.

Lemma nth_error_nil (X : Type) (x : X) (i : nat) :
  nth_error (@nil X) i <> Some x.
Proof.
  assert (|@nil X| <= i) by (cbn; omega). apply List.nth_error_None in H. congruence.
Qed.

Inductive dupfree X : forall n, Vector.t X n -> Prop :=
  dupfreeVN : dupfree (@Vector.nil X)
| dupfreeVC n (x : X) (V : Vector.t X n) : ~ Vector.In x V -> dupfree V -> (dupfree (x ::: V))%vector_scope.

Section Def_Vector.

  Variable X Y : finType.

  Definition injection_vect := { v : Vector.t Y (|elem X|) | dupfree v }.

End Def_Vector.

Section Fin_finType.
  Instance Fin_eqType (k : nat) : eq_dec (Fin.t k).
  Proof. intros m n. unfold dec. apply Fin.eq_dec. Qed.
  
  Fixpoint fin_enum (n : nat) : list (Fin.t n) :=
    match n with
    | O => nil
    | S n' => Fin.F1 :: (map Fin.FS (fin_enum n'))
    end.

  Lemma fin_enum_dupfree (n : nat) : Dupfree.dupfree (fin_enum n).
  Proof.
    induction n.
    - cbn. constructor.
    - cbn. constructor.
      + intros (x&H1&H2) % in_map_iff. congruence.
      + apply dupfree_map; auto. firstorder. now apply Fin.FS_inj in H1.
  Qed.

  Lemma fin_enum_complete (n : nat) : forall k : Fin.t n, k el (fin_enum n).
  Proof.
    induction n; intros k; cbn.
    - inv k.
    - dependent destruct k. now left. right. apply in_map_iff. eauto.
  Qed.

  Instance Fin_finType (k : nat) : finTypeC (EqType (Fin.t k)).
  Proof.
    apply FinTypeC with (enum := fin_enum k). intros x.
    apply dupfreeCount. apply fin_enum_dupfree. apply fin_enum_complete.
  Qed.

End Fin_finType.



Section Def_Function.

  Variable X Y : Type.

  Record injection_fun :=
    {
      inj_f : X -> Y;
      inj_g : Y -> option X;
      inj_f_injective : forall x1 x2, inj_f x1 = inj_f x2 -> x1 = x2;
      inj_g_adjoint : forall x, inj_g (inj_f x) = Some x;
    }.

  Lemma inj_g_surjective (I : injection_fun) :
    forall x, { y | (inj_g I) y = Some x }.
  Proof. intros x. pose proof (inj_g_adjoint I x). eauto. Defined.
  
End Def_Function.


Section find_i.
  Variable (X : Type) (P : X -> Prop) (H_P : forall x, dec(P x)).

  Fixpoint find_i (xs : list X) : option nat :=
    match xs with
    | nil => None
    | x :: xs' => if Dec (P x) then Some O else let try i := find_i xs' in Some (S i)
    end.

  Lemma find_i_correct_Some (xs : list X) (i : nat) :
    find_i xs = Some i -> { x : X | P x /\ List.nth_error xs i = Some x }.
  Proof.
    revert i. induction xs; intros i; cbn.
    - discriminate.
    - decide (P a) as [H|H].
      + inversion 1; subst. eauto.
      + destruct (find_i xs) as [b| ] eqn:E.
        * inversion 1; subst. destruct (IHxs b) as (y&Hy&Hy2). reflexivity. eauto.
        * discriminate.
  Qed.
  
  Lemma find_i_correct_None (xs : list X) :
    find_i xs = None -> forall x, In x xs -> ~ P x.
  Proof.
    induction xs as [ | x xs IH]; intros H1 y. intros []. intros [-> | H2] H3; cbn in *.
    - decide (P y). discriminate. firstorder.
    - decide (P x). discriminate. 
      destruct (find_i xs) eqn:E.
      + discriminate.
      + firstorder.
  Qed.

  Lemma find_i_correct_Some_first (xs : list X) (i : nat) :
    find_i xs = Some i -> forall j e, j < i -> nth_error xs j = Some e -> ~ (P e).
  Proof.
    revert i. induction xs; intros i H1 j e H2 H3 H4; cbn in *.
    - now apply nth_error_nil in H3.
    - decide (P a) as [H|H].
      + inv H1. omega.
      + destruct (find_i xs) as [ b | ].
        * inv H1. pose proof H3 as H3'.
          apply nth_error_In in H3. cbn in H3. destruct H3 as [->|H3].
          -- tauto.
          -- intuition. destruct j; cbn in *.
             ++ inv H3'. tauto.
             ++ eapply IHxs; eauto. omega.
        * discriminate.
  Qed.
  
End find_i.
Arguments find_i {_} _ {_} _ : rename.


(* Convert a vector-defined injection into a function-defined injection *)
Section Convertion1.

  Variable X Y : finType.


  Variable I : injection_vect X Y.

  Definition conv_f : X -> Y.
  Proof.
    destruct I as [V HV]. intros x.
    destruct (find_i (fun x' => x = x') (elem X)) as [n | ] eqn:E.
    - apply find_i_correct_Some in E as (?&<-&H2).
      eapply Vector.nth. apply V. eapply Fin.of_nat_lt.
      eapply List.nth_error_Some. rewrite H2. congruence.
    - pose proof (find_i_correct_None E) as E2. cbn in E2. specialize (E2 x). contradiction E2; auto.
  Defined.

  Definition conv_g : Y -> option X.
  Proof.
    destruct I as [V HV]. intros y.
    apply find.
    - intros x. decide (conv_f x = y); [exact true|exact false].
    - apply elem.
  Defined.

  (* TODO *)
  Lemma conv_injective : forall x1 x2, conv_f x1 = conv_f x2 -> x1 = x2.
  Proof.
  Admitted.

  Lemma conv_adjoint : forall x, conv_g (conv_f x) = Some x.
  Proof.
    destruct I as [V HV] eqn:E. intros x. cbn.
    unfold conv_g. subst.
    unfold conv_f. subst.
  Admitted.
    
  Definition inj_conv_vec_to_fun : injection_fun X Y.
    econstructor. apply conv_injective. apply conv_adjoint.
  Defined.
  
End Convertion1.
