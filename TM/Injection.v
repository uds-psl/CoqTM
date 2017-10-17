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
      inj_inv : forall x y, inj_g y = Some x <-> y = inj_f x;
    }.

  Variable I : injection_fun.

  Lemma inj_g_adjoint : forall x, inj_g I (inj_f I x) = Some x.
  Proof. intros. now apply inj_inv. Qed.

  Lemma inj_g_surjective : forall x, { y | (inj_g I) y = Some x }.
  Proof. intros x. pose proof (inj_g_adjoint x). eauto. Defined.

  Lemma inj_f_injective : forall x1 x2, inj_f I x1 = inj_f I x2 -> x1 = x2.
  Proof.
    intros x1 x2 H. enough (Some x1 = Some x2) as HE by now inv HE.
    erewrite <- !inj_g_adjoint; eauto. now rewrite H.
  Qed.

End Def_Function.

Section Injection_Fun_Compose.
  Variable (X Y Z : Type).
  Hypothesis (inj1 : injection_fun X Y) (inj2 : injection_fun Y Z).

  Definition inj_comp_f := fun x => inj_f inj2 (inj_f inj1 x).

  Definition inj_comp_g :=
    fun z =>
      match inj_g inj2 z with
      | Some y =>inj_g inj1 y
      | None => None
      end.

  Lemma inj_comp_inv : forall (x : X) (y : Z), inj_comp_g y = Some x <-> y = inj_comp_f x.
  Proof.
    unfold inj_comp_f, inj_comp_g. firstorder.
    - destruct (inj_g _) eqn:E1.
      + apply inj_inv in E1 as ->. apply inj_inv in H as ->. reflexivity.
      + congruence.
    - destruct (inj_g inj2 y) eqn:E1.
      + apply inj_inv in E1 as ->. apply inj_inv. now apply inj_f_injective in H.
      + exfalso. apply inj_inv in H. congruence.
  Qed.

  Definition injection_fun_compose : injection_fun X Z := Build_injection_fun inj_comp_inv.

End Injection_Fun_Compose.


Section find_i.
  Variable (X : Type) (P : X -> bool).

  Definition find_i (xs : list X) : {p : nat * X & List.nth_error xs (fst p) = Some (snd p) /\ P (snd p) = true} + (forall x, In x xs -> ~ P x).
  Proof.
    induction xs as [ | x xs IH]; cbn.
    - eauto.
    - destruct (P x) eqn:E.
      + left. exists (0, x). cbn. auto.
      + destruct IH as [((n,y),H)|H]; cbn in *.
        * left. exists (S n, y). cbn. assumption.
        * right. intros y [<- | ]; auto.
  Defined.

End find_i.

Lemma nth_error_Some' (A : Type) (x : A) (l : list A) (n : nat) :
  nth_error l n = Some x -> n < | l |.
Proof.
  rewrite <- nth_error_Some. congruence.
Qed.

Definition nth_no_error (A : Type) (xs : list A) (n : nat) : { y : A & nth_error xs n = Some y } + (n >= |xs|).
Proof.
  revert n. induction xs as [ | x xs IH]; intros n; cbn in *.
  - right. omega.
  - destruct n; cbn.
    + left. eauto.
    + specialize (IH n) as [(y,H) | H].
      * left. eauto.
      * right. omega.
Qed.

Lemma vect_to_list_orig_size (A : Type) (n : nat) (I : Vector.t A n) :
  n = | Vector.to_list I |.
Proof. induction I. cbn. reflexivity. cbn. f_equal. now unfold Vector.to_list in *. Qed.

Lemma vect_to_list_nth (A : Type) (n : nat) (i : nat) (Hi : i < n) (xv : Vector.t A n) :
  nth_error (Vector.to_list xv) i =
  Some xv[@Fin.of_nat_lt Hi].
Proof.
  revert n Hi xv. induction i; cbn in *; intros.
  - destruct xv; cbn in *. omega. reflexivity.
  - destruct xv; cbn in *. omega. now unfold Vector.to_list in *.
Qed.

Lemma vect_to_list_nth_el (A : Type) (n : nat) (i : nat) (Hi : i < n) (xv : Vector.t A n) :
  (Vector.nth xv (Fin.of_nat_lt Hi)) el Vector.to_list xv.
Proof. apply nth_error_In with (n := i). apply vect_to_list_nth. Qed.

Lemma dupfree_error_nth (A : Type) (xs : list A) (n m : nat) (x : A) :
  Dupfree.dupfree xs -> nth_error xs m = Some x -> nth_error xs n = Some x -> n = m.
Proof.
  intros H. revert n m x. induction H; intros; cbn in *.
  - now apply nth_error_nil in H.
  - destruct m, n; cbn in *; try inv H1; try inv H2; auto; try congruence.
    + apply nth_error_In in H3. tauto.
    + apply nth_error_In in H4. tauto.
    + f_equal. eapply IHdupfree; eauto.
Qed.

Lemma vect_to_list_In (A : Type) (n : nat) (x : A) (xv : Vector.t A n) :
  Vector.In x xv <-> List.In x (Vector.to_list xv).
Proof.
  split.
  - induction 1; cbn in *; auto.
  - revert x; induction xv; cbn in *; auto. intros x [<-|H]. constructor. unfold Vector.to_list in *. constructor. auto.
Qed.

Lemma dupfree_vect_to_list (A : Type) (n : nat) (xv : Vector.t A n) :
  dupfree xv -> Dupfree.dupfree (Vector.to_list xv).
Proof.
  induction 1; cbn in *.
  - constructor.
  - constructor; auto. intros H1. apply H. now apply vect_to_list_In.
Qed.


(* TODO: Unmess and/or make useful *)
(*
(* Convert a vector-defined injection into a function-defined injection *)
Section Convertion1.

  Variable X Y : eqType.
  Variable (elem_X : list X).
  Variable (elem_Y : list Y).
  Variable (count_X : nat).
  Variable (enum : forall x : X, In x elem_X).
  Variable (X_dupfree : Dupfree.dupfree elem_X).

  Variable I : Vector.t Y (|elem_X|).
  Variable (I_dupfree : dupfree I).

  Lemma nat_lt_ge (m n : nat) : n < m -> n >= m -> False. Proof. intros. omega. Qed.

  Definition conv_f : X -> Y.
  Proof.
    intros x.
    destruct (find_i (fun x' => Dec (x = x')) elem_X) as [(n&Hn) | H].
    - eapply Vector.nth. apply I. eapply Fin.of_nat_lt. eapply nth_error_Some'. eapply Hn.
    - specialize (H x). contradiction H; auto.
  Defined.

  Definition conv_g : Y -> option X.
  Proof.
    intros y.
    destruct (find_i (fun y' => Dec (y = y')) (Vector.to_list I)) as [((n,y')&Hn&Hn') | H]; cbn in *.
    - apply Some. apply nth_error_Some' in Hn.
      destruct (nth_no_error elem_X n) as [x | ].
      + apply x.
      + replace (| Vector.to_list I |) with (| elem_X |) in *. exfalso. eapply nat_lt_ge; eauto. apply vect_to_list_orig_size.
    - apply None.
  Defined.

  Lemma conv_adjoint : forall x, conv_g (conv_f x) = Some x.
  Proof.
    intros x. unfold conv_f in *.
    destruct (find_i (fun x' : X => Dec (x = x')) elem_X) as [((n&yn)&H1&H2) | H]; cbn in *.
    - unfold conv_g. cbn.
      destruct (find_i (fun y' : Y => Dec (I[@Fin.of_nat_lt (nth_error_Some' H1)] = y')) (Vector.to_list I))
               as [((m&ym)&H3&H4) | H'].
      + f_equal. destruct (nth_no_error elem_X m) as [(y'&Hy') | H'].
        * decide (x = yn); cbn in *; try congruence; subst.
          decide (I[@Fin.of_nat_lt (nth_error_Some' H1)] = ym); cbn in *; try congruence.
          enough (n = m) as <- by congruence.
          eapply dupfree_error_nth. eapply dupfree_vect_to_list. eapply I_dupfree. eapply H3.
          erewrite vect_to_list_nth. f_equal. eauto.
        * exfalso. pose proof (nth_error_Some' H1). decide (I[@Fin.of_nat_lt (nth_error_Some' H1)] = snd (m, ym)); cbn in *; try congruence.
          decide (x = yn); cbn in *; try congruence. subst. pose proof (nth_error_Some' H3).
          replace (| Vector.to_list I |) with (|elem_X|) in *. omega. apply vect_to_list_orig_size.
      + exfalso. eapply H'; eauto. apply vect_to_list_nth_el.
    - exfalso. specialize (H x). contradict H. auto.
  Qed.
    
  Definition inj_conv_vec_to_fun : injection_fun X Y.
    econstructor. intros. split; eapply conv_adjoint.
  Defined.
  
End Convertion1.
*)