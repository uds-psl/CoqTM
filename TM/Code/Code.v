Require Import Prelim.

(** * Suffix *)

Inductive suffix (X : Type) : list X -> list X -> Type :=
| suffix_full (xs : list X) : suffix xs xs
| suffix_skip (xs ys : list X) (y : X) : suffix xs ys -> suffix xs (y :: ys).
Hint Constructors suffix.

Goal suffix [1;2;3] [4;5;6;1;2;3]. Proof. repeat constructor. Qed.

Lemma suffix_skip' (X : Type) (x : X) (xs : list X) :
  suffix xs (x :: xs).
Proof. do 2 constructor. Qed.

Lemma suffix_nil (X : Type) (xs : list X) : suffix [] xs.
Proof. induction xs; auto. Qed.

Lemma suffix_from_nil (X : Type) (xs : list X) : suffix xs [] -> xs = [].
Proof. inversion 1; now subst. Qed.

Lemma suffix_transitive (X : Type) (xs ys zs : list X) :
  suffix ys xs -> suffix zs ys -> suffix zs xs.
Proof. intros H. revert zs. induction H; auto. Qed.

Lemma suffix_app (X : Type) (xs ys zs : list X) :
  suffix xs ys -> suffix xs (zs ++ ys).
Proof.
  induction zs; intros H.
  - now rewrite app_nil_l.
  - cbn. apply suffix_skip. auto.
Qed.

Lemma list_con_neq (X : Type) (xs : list X) (x : X) :
  xs <> x :: xs.
Proof.
  induction xs as [ | x' xs IH]; cbn.
  - congruence.
  - intros H. injection H. intros H' ->. congruence.
Qed.

Lemma list_app_neq (X : Type) (xs ys : list X) (y : X) :
  xs <> y :: ys ++ xs.
Proof. intros H. assert (|xs| = |y :: ys ++ xs|) as H' by congruence. cbn in *. rewrite app_length in H'. omega. Qed.

Lemma suffix_length (X : Type) (xs : list X) (ys : list X) :
  suffix xs ys -> |xs| <= |ys|.
Proof. induction 1; cbn; omega. Qed.

Lemma suffix_size_decrease (X : eqType) (xs ys : list X) :
  xs <> ys -> suffix xs ys -> |xs| < |ys|.
Proof.
  intros H. induction 1.
  - tauto.
  - cbn. decide (xs = ys) as [->|E].
    + omega.
    + rewrite IHX0. omega. assumption.
Qed.

Lemma suffix_put_app (X : eqType) (xs : list X) (ys : list X) :
  ys <> nil -> suffix (ys ++ xs) xs -> False.
Proof.
  intros H H'. eapply suffix_size_decrease in H'.
  assert ((|ys|) + (|xs|) < |xs|) as H'' by now rewrite <- app_length.
  assert (|ys| > 0). destruct ys; cbn; omega. omega.
  destruct ys; cbn in *. tauto. intros H''. eapply list_app_neq; eauto.
Qed.

Lemma suffix_put (X : eqType) (xs : list X) (y : X) :
  suffix (y :: xs) xs -> False.
Proof.
  intros H. eapply suffix_size_decrease in H. cbn in *. omega.
  intros H'. eapply list_con_neq; eauto.
Qed.


(** Suffix Induction *)

Inductive size_ind (X : Type) (f : X -> nat) : X -> Type :=
| size_ind_intro (x : X) : (forall y, f y < f x -> size_ind f y) -> size_ind f x.

Inductive suffix_induction (X : Type) (ys : list X) : Type :=
| suffix_induction_con : (forall xs: list X, suffix xs ys -> xs <> ys -> suffix_induction xs) ->
                         suffix_induction ys.

(* Opaque proofes for size_Ind *)
Lemma nat_lt_0 (n : nat) : ~n < 0. Proof. omega. Qed.
Lemma nat_lt_tran_S (a b c : nat) : b < S c -> a < b -> a < c. Proof. omega. Qed.

Lemma size_Ind (X : Type) (f : X -> nat) (x : X) : size_ind f x.
Proof.
  constructor.
  generalize (f x) as n.
  induction n; intros y B.
  - now apply nat_lt_0 in B.
  - constructor. intros z C. apply IHn. eapply nat_lt_tran_S; eauto.
Defined.

Lemma suffix_induction_provider (X : eqType) (ys : list X) : suffix_induction ys.
Proof.
  pose proof (size_Ind (@List.length X) ys) as H. induction H as [ys _ IH].
  constructor. intros xs H1 H2. apply IH. now apply (suffix_size_decrease H2 H1).
Defined.


(** * Codeable Class **)

Definition encoding_function (X : Type) := X -> list bool.

Definition decoding_output (X : Type) (string : list bool) :=
  option (X * {rest : list bool & suffix rest string}).

Definition decoding_output_proj (X : Type) :=
  option (X * list bool).

Definition decoding_function (X : Type) :=
  forall string : list bool, decoding_output X string.

Definition decoding_output_project (X : Type) (string : list bool) : decoding_output X string -> decoding_output_proj X.
Proof. destruct 1; [ | apply None]. destruct p. apply Some. constructor. apply x. apply (projT1 s). Defined.

Class codeable (X : Type) :=
  {
    encode : encoding_function X;
    encode_injective : forall (v1 v2 : X) (r1 r2 : list bool), encode v1 ++ r1 = encode v2 ++ r2 -> v1 = v2 /\ r1 = r2;
  }.


(** * Basic Encoding Functions *)

Fixpoint encode_list (X : Type) (encode_entries : encoding_function X) (xs : list X) : list bool.
Proof.
  destruct xs.
  - apply (false :: nil).
  - apply (cons true). apply app. apply (encode_entries x). apply (encode_list X encode_entries xs).
Defined.

Definition encode_sum (X Y : Type) (encode_left : encoding_function X) (encode_right : encoding_function Y) (v : X + Y) : list bool.
Proof.
  destruct v.
  - apply (true  :: encode_left  x).
  - apply (false :: encode_right y).
Defined.

Definition encode_pair (X Y : Type) (encode_left : encoding_function X) (encode_right : encoding_function Y) (v : X * Y) : list bool.
Proof. destruct v as (a,b). apply (encode_left a ++ encode_right b). Defined.
  
Definition encode_unit := fun _ : unit => @nil bool.


(** * Basic Coding Instances *) 

(** Lists **)

Lemma encode_injective_list (X : Type) (e1 : codeable X) :
  forall (v1 v2 : list X) (r1 r2 : list bool), encode_list encode v1 ++ r1 = encode_list encode v2 ++ r2 -> v1 = v2 /\ r1 = r2.
Proof.
  intros xs. induction xs as [ | x xs IH]; intros y2 r1 r2 H; cbn in *.
  + destruct y2; cbn in *; try congruence. now inv H.
  + destruct y2 as [ | y ys]; cbn in *; auto.
    * congruence.
    * inv H. rewrite <- !app_assoc in H1. apply encode_injective in H1. destruct H1 as (->&H1). apply IH in H1. intuition; congruence.
Qed.

Instance I_list (X : Type) (e1 : codeable X) : codeable (list X).
Proof.
  split with (encode := encode_list encode).
  - apply encode_injective_list.
Defined.


(** Pair *)

Lemma encode_injective_pair (X Y : Type) (e1 : codeable X) (e2 : codeable Y) :
  forall (v1 v2 : X * Y) (r1 r2 : list bool), encode_pair encode encode v1 ++ r1 = encode_pair encode encode v2 ++ r2 -> v1 = v2 /\ r1 = r2.
Proof.
  intros (a1, b1) (a2, b2) r1 r2 H. unfold encode_pair in *. rewrite <- !app_assoc in H.
  apply encode_injective in H as (->&H). apply encode_injective in H as (->&->). auto.
Qed.

Instance I_pair (X Y : Type) (e1 : codeable X) (e2 : codeable Y) : codeable (X * Y).
Proof.
  split with (encode := encode_pair encode encode).
  - apply encode_injective_pair.
Defined.


(** Sum **)

Lemma encode_injective_sum (X Y : Type) (e1 : codeable X) (e2 : codeable Y) :
  forall (v1 v2 : X + Y) (r1 r2 : list bool), encode_sum encode encode v1 ++ r1 = encode_sum encode encode v2 ++ r2 -> v1 = v2 /\ r1 = r2.
Proof.
  intros [v1|v1] [v2|v2] r1 r2; unfold encode_sum; intros H1; cbn in *; inv H1; apply encode_injective in H0; intuition; congruence.
Qed.

Instance I_sum (X Y : Type) (e1 : codeable X) (e2 : codeable Y) : codeable (X + Y).
Proof.
  split with (encode := encode_sum encode encode).
  - apply encode_injective_sum.
Defined.


(** Unit **)

Lemma encode_injective_unit :
  forall (v1 v2 : unit) (r1 r2 : list bool), encode_unit v1 ++ r1 = encode_unit v2 ++ r2 -> v1 = v2 /\ r1 = r2.
Proof. intros () () r1 r2. auto. Qed.

Instance I_unit : codeable unit.
Proof.
  split with (encode := encode_unit).
  - apply encode_injective_unit.
Defined.

(** Empty Set **)
Instance I_empty : codeable Empty_set.
Proof.
  split with (encode := fun x : Empty_set => match x with end).
  - intros v1. exfalso. destruct v1.
Defined.


(** * Castings **)

Class Cast (X Y : Type) :=
  {
    cast : Y -> X;
    cast_injective : forall x1 x2, cast x1 = cast x2 -> x1 = x2;
  }.

Section I_Cast.
  Variable (X Y : Type) (castXY : Cast X Y) (e : codeable X).

  Lemma I_cast : codeable Y.
  Proof.
    esplit with (encode := fun y => encode (cast y)).
    - intros v1 v2 r1 r2 H. apply encode_injective in H as (H&->). split; auto. now apply cast_injective in H.
  Defined.

End I_Cast.

Instance cast_bool : Cast (unit + unit) bool.
Proof.
  split with (cast := fun (b : bool) => if b then inl tt else inr tt).
  - intros x1 x2 H. destruct x1, x2; auto; congruence.
Defined.

Instance I_bool : codeable bool.
Proof. eapply I_cast. eapply cast_bool. auto. Defined.

Instance cast_option (X : Type) : Cast (X + unit) (option X).
Proof.
  split with (cast := fun p => match p with Some x => inl x | None => inr tt end).
  - intros [x|  ] [y| ] H; auto; congruence.
Defined.

Instance I_option (X : Type) : codeable X -> codeable (option X).
Proof. intros H. eapply I_cast. eapply cast_option. auto. Defined.

Lemma repeat_surjective (X : Type) (x : X) (n m : nat) :
  repeat x n = repeat x m -> n = m.
Proof.
  revert m. induction n; intros m H.
  - destruct m; cbn in *; congruence.
  - cbn in *. destruct m; cbn in *. congruence. f_equal. apply IHn. congruence.
Qed.

Instance cast_nat : Cast (list unit) nat.
Proof.
  split with (cast := @List.repeat unit tt).
  - apply repeat_surjective.
Defined.

Instance I_nat : codeable nat.
Proof. eapply I_cast. eapply cast_nat. auto. Defined.


(* Non decodeable version *)
Section Fin.
  Variable (n : nat).

  Definition fin_to_nat : (Fin.t n) -> nat :=
    fun i :  (Fin.t n) => proj1_sig (Fin.to_nat i).
  
  Lemma fin_to_nat_injective:
    forall x1 x2 : (Fin.t n),
      fin_to_nat x1 = fin_to_nat x2 -> x1 = x2.
  Proof.
    intros x1 x2. unfold fin_to_nat. intros H.
    f_equal. now apply Fin.to_nat_inj.
  Qed.
  
  Instance cast_Fin : Cast nat (Fin.t n).
  Proof.
    split with (cast := fin_to_nat).
    apply fin_to_nat_injective.
  Defined.

  Instance I_Fin : codeable (Fin.t n).
  Proof. eapply I_cast. eapply cast_Fin. auto. Defined.
End Fin.

(* Decodeable version *)
Section Fin2.

  Fixpoint cast_fin (n : nat) : Type :=
    match n with
    | 0 => Empty_set
    | S n' => option (cast_fin n')
    end.

  Fixpoint cast_fin_codeable (n : nat) : codeable (cast_fin n) :=
    match n with
    | 0 => I_empty
    | S n' => I_option (cast_fin_codeable n')
    end.

  Fixpoint fin_to_cast_fin (n : nat) (x : Fin.t n) : cast_fin n :=
    match x with
    | Fin.F1 => None
    | @Fin.FS n' t => Some (@fin_to_cast_fin n' t)
    end.

  (* Compute cast_fin 2.
  Compute fin_to_cast_fin (n := 3) (Fin.F1).
  Compute fin_to_cast_fin (n := 3) (Fin.FS Fin.F1).
  Compute fin_to_cast_fin (n := 3) (Fin.FS (Fin.FS Fin.F1)). *)

  Fixpoint cast_fin_to_fin (n : nat) (x : cast_fin n) {struct n} : Fin.t n.
  Proof.
    destruct n; cbn in *; destruct x eqn:E.
    - apply Fin.FS. apply (cast_fin_to_fin n c).
    - apply Fin.F1.
  Defined.

  (* Compute cast_fin_to_fin (fin_to_cast_fin (n := 3) (Fin.FS Fin.F1)). *)

  Lemma fin_to_cast_None (n : nat) (x : Fin.t (S n)) :
    fin_to_cast_fin x = None -> x = Fin.F1.
  Proof.
    intros H. dependent induction x; auto. cbn in *. congruence.
  Qed.

  Lemma fin_to_cast_injective (n : nat) (x1 x2 : Fin.t n) :
    fin_to_cast_fin x1 = fin_to_cast_fin x2 -> x1 = x2.
  Proof.
    revert x2. induction x1; intros x2 H; cbn in *.
    - symmetry in H. eapply fin_to_cast_None in H. auto.
    - dependent induction x2; cbn in *; auto; try congruence.
      clear IHx2. inv H. f_equal. apply IHx1. assumption.
  Qed.

  Instance cast_fin2 (n : nat) : Cast (cast_fin n) (Fin.t n).
  Proof.
    split with (cast := fin_to_cast_fin (n := n)).
    - apply fin_to_cast_injective.
  Defined.

  Instance I_Fin2 (n : nat) : codeable (Fin.t n).
  Proof.
    eapply I_cast. apply cast_fin2. apply cast_fin_codeable.
  Defined.

End Fin2.

(** Test Playground *)

(*
Compute (encode (X := list unit * (unit + unit) * (unit + unit)) ([tt;tt;tt], inr tt, inl tt)).

Compute encode [true; false].
Compute encode [inl (Some (true)); inl None; inr tt].

Compute (encode (Some [inl (Some (true)); inl None; inr 42])).

Compute (@encode _ (I_Fin 10) (Fin.FS (Fin.FS (Fin.FS (Fin.F1))))).
Compute (@encode _ (I_Fin2 10) (Fin.FS (Fin.FS (Fin.FS (Fin.F1))))).
*)