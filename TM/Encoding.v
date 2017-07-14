Require Import Prelim.
Require Import Recdef.

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
    decode : decoding_function X;
    encode_injective : forall (v1 v2 : X) (r1 r2 : list bool), encode v1 ++ r1 = encode v2 ++ r2 -> v1 = v2 /\ r1 = r2;
    encode_decode : forall (string : list bool) v rest, decode string = Some (v, rest) -> encode v ++ (projT1 rest) = string;
    decode_encode : forall (v : X) (rest : list bool),
        match (decode (encode v ++ rest)) with
        | Some (v', rest') => v = v' /\ projT1 rest' = rest
        | None => False
        end;
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


(** * Basic Decoding Functions *)

Ltac invalid_encoding := apply None.

(** List decoding *)

Lemma decode_list'_helper1 (x : bool) (string : list bool) (ss : list bool)
      (Rest1 : {rest : list bool & suffix rest ss}) :
  string = x :: ss -> suffix (projT1 Rest1) string.
Proof. intros ->. destruct Rest1; cbn. now apply suffix_skip. Qed.

Lemma decode_list'_helper2 (x : bool) (string : list bool) (ss : list bool)
      (Rest2 : {rest : list bool & suffix rest ss}) :
      string = x :: ss -> projT1 Rest2 <> string.
Proof. intros ->. destruct Rest2; cbn. intros ->. eapply suffix_put; eauto. Qed.

Lemma decode_list'_helper3 (x : bool) (string : list bool) (ss : list bool)
      (Rest1 : {rest : list bool & suffix rest ss})
      (Rest2 : {rest : list bool & suffix rest (projT1 Rest1)}) :
  {rest : list bool & suffix rest (x :: ss)}.
Proof.
  destruct Rest1 as (rest1, HRest1). destruct Rest2 as (rest2, HRest2). cbn in *.
  exists rest2. apply suffix_skip. eapply suffix_transitive; eauto.
Defined.

Function decode_list (X : Type) (decodeEntries : decoding_function X) (string : list bool) {measure length string} :
  option (list X * {rest : list bool & suffix rest string }) :=
  match string with
   | nil =>  None
   | true  :: ss => 
     match (decodeEntries ss) with
     | None => None
     | Some (dec1, Rest1) =>
       match
         @decode_list X decodeEntries (projT1 Rest1) with
       | None => None
       | Some (dec2, Rest2) =>
         Some (dec1 :: dec2, @decode_list'_helper3 true string ss Rest1 Rest2)
       end
     end
   | false :: ss =>  Some (nil, existT _ ss (suffix_skip' _ _))
   end.
Proof.
  intros X decodeEntries string b ss E2 E1 _ dec1 Rest1 _ H.
  eapply suffix_size_decrease. eapply decode_list'_helper2; eauto. eapply decode_list'_helper1; eauto.
Defined.

(** Pair decoding *)

Definition decode_pair (X Y : Type) (decode1 : decoding_function X) (decode2 : decoding_function Y) (string : list bool) :
  option ((X * Y) * {rest : list bool & suffix rest string}).
Proof.
  destruct (decode1 string) as [ (dec1, (rest1, HRest1)) | ]; [ | invalid_encoding].
  destruct (decode2 rest1)  as [ (dec2, (rest2, Hrest2)) | ]; [ | invalid_encoding].
  do 2 constructor. constructor. apply dec1. apply dec2. exists rest2. eapply suffix_transitive; eauto.
Defined.

(** Sum decoding *)

Definition decode_sum (X Y : Type) (decode1 : decoding_function X) (decode2 : decoding_function Y) (string : list bool) :
  option ((X + Y) * {rest : list bool & suffix rest string}).
Proof.
  destruct string as [ | s ss].
  - invalid_encoding.
  - destruct s eqn:E.
    + (* Inl = true *)
      destruct (decode1 ss) as [ (dec, (rest, HRest)) | ]; [ | invalid_encoding].
      constructor. constructor. left.  apply dec. exists rest. now apply suffix_skip.
    + (* Inr = false *)
      destruct (decode2 ss) as [ (dec, (rest, HRest)) | ]; [ | invalid_encoding].
      constructor. constructor. right. apply dec. exists rest. now apply suffix_skip.
Defined.

Definition decode_unit (string : list bool) : option (unit * {rest : list bool & suffix rest string}).
  do 2 constructor. constructor. exists string. apply suffix_full.
Defined.


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

Lemma encode_decode_list (X : Type) (e : codeable X) (string : list bool) ls rest :
  decode_list decode string = Some (ls, rest) -> encode_list encode ls ++ (projT1 rest) = string.
Proof.
  revert ls rest.
  pose proof (suffix_induction_provider string) as ind.
  induction ind as [ xs H IH]; rewrite !decode_list_equation; intros ls rest H1; rewrite <- decode_list_equation in *.
  destruct xs as [ | x ss] eqn:E; try discriminate.
  destruct x; rewrite !decode_list_equation in *.
  - destruct (decode ss) as [(dec1, Rest1)| ] eqn:E2; try discriminate; simpl in *.
    destruct (decode_list decode (projT1 Rest1))
      as [(dec2, Rest2)| ] eqn:E3; try discriminate. inv H1.
    apply IH in E3; auto.
    + destruct Rest1, Rest2. simpl in *. f_equal.
      rewrite <- app_assoc. rewrite E3.
      erewrite <- encode_decode; eauto.
      cbn. reflexivity.
    + eapply decode_list'_helper1; eauto.
    + eapply decode_list'_helper2; eauto.
  - inv H1. cbn. reflexivity.
Qed.

Lemma decode_encode_list (X : Type) (e : codeable X) :
  forall (v : list X) (rest : list bool),
    match (decode_list decode (encode_list encode v ++ rest)) with
    | Some (v', rest') => v = v' /\ projT1 rest' = rest
    | None => False
    end.
Proof.
  intros v rest.
  revert rest.
  induction v as [ | v vs IH]; intros rest; rewrite !decode_list_equation; simpl.
  - auto.
  - rewrite <- !app_assoc in *.
    pose proof (decode_encode v (encode_list encode vs ++ rest)) as E1'.
    destruct (decode (encode v ++ encode_list encode vs ++ rest)) as [(dec1&rest1&Hrest1)| ] eqn:E1; auto.
    simpl in *. destruct E1' as (->&->).
    specialize (IH rest).
    destruct (decode_list decode (encode_list encode vs ++ rest)) as [(dec2&rest2&Hrest2)| ]; auto.
    simpl in *. destruct IH as (->&->). auto.
Qed.


Instance I_list (X : Type) (e1 : codeable X) : codeable (list X).
Proof.
  split with (encode := encode_list encode) (decode := decode_list decode).
  - apply encode_injective_list.
  - apply encode_decode_list.
  - apply decode_encode_list.
Defined.


(** Pair *)

Lemma encode_injective_pair (X Y : Type) (e1 : codeable X) (e2 : codeable Y) :
  forall (v1 v2 : X * Y) (r1 r2 : list bool), encode_pair encode encode v1 ++ r1 = encode_pair encode encode v2 ++ r2 -> v1 = v2 /\ r1 = r2.
Proof.
  intros (a1, b1) (a2, b2) r1 r2 H. unfold encode_pair in *. rewrite <- !app_assoc in H.
  apply encode_injective in H as (->&H). apply encode_injective in H as (->&->). auto.
Qed.

Lemma encode_decode_pair (X Y : Type) (e1 : codeable X) (e2 : codeable Y) (string : list bool) (v : X * Y) rest :
  decode_pair decode decode string = Some (v, rest) -> encode_pair encode encode v ++ (projT1 rest) = string.
Proof.
  intros H. destruct v as (a, b).
  unfold encode_pair, decode_pair in *.
  destruct (decode string) as [(cod1, (rest1, HRest1))| ] eqn:E1; cbn in *; try discriminate.
  destruct (decode rest1) as [(cod2, (rest2, HRest2))| ] eqn:E2; cbn in *; try discriminate.
  inv H. cbn in *.
  pose proof (@encode_decode X e1) as IH1. pose proof (@encode_decode Y e2) as IH2.
  specialize (IH1 _ _ _ E1). cbn in *. specialize (IH2 _ _ _ E2). cbn in *.
  subst. symmetry. now apply app_assoc.
Qed.

Lemma decode_encode_pair (X Y : Type) (e1 : codeable X) (e2 : codeable Y) :
  forall (v : X * Y) (rest : list bool),
    match (decode_pair decode decode (encode_pair encode encode v ++ rest)) with
    | Some (v', rest') => v = v' /\ projT1 rest' = rest
    | None => False
    end.
Proof.
  intros (a, b) rest. unfold decode_pair, encode_pair.
  rewrite <- app_assoc in *.
  pose proof (decode_encode a (encode b ++ rest)) as E'.
  destruct (decode (encode a ++ encode b ++ rest)) as [(dec1&rest1&Hrest1)| ] eqn:E; cbn in *.
  - destruct E' as (->&->).
    pose proof (decode_encode b rest) as E2'.
    destruct (decode (encode b ++ rest) ) as [(dec2&rest2&Hrest2)| ] eqn:E2; cbn in *.
    + destruct E2' as (->&->). auto.
    + auto.
  - auto.
Qed.

Instance I_pair (X Y : Type) (e1 : codeable X) (e2 : codeable Y) : codeable (X * Y).
Proof.
  split with (encode := encode_pair encode encode) (decode := decode_pair decode decode).
  - apply encode_injective_pair.
  - apply encode_decode_pair.
  - apply decode_encode_pair.
Defined.


(** Sum **)

Lemma encode_injective_sum (X Y : Type) (e1 : codeable X) (e2 : codeable Y) :
  forall (v1 v2 : X + Y) (r1 r2 : list bool), encode_sum encode encode v1 ++ r1 = encode_sum encode encode v2 ++ r2 -> v1 = v2 /\ r1 = r2.
Proof.
  intros [v1|v1] [v2|v2] r1 r2; unfold encode_sum; intros H1; cbn in *; inv H1; apply encode_injective in H0; intuition; congruence.
Qed.

Lemma encode_decode_sum (X Y : Type) (e1 : codeable X) (e2 : codeable Y) (string : list bool) (v : X + Y) rest :
  decode_sum decode decode string = Some (v, rest) -> encode_sum encode encode v ++ (projT1 rest) = string.
Proof.
  intros H. destruct v as [v1|v2].
  + destruct string; try discriminate; cbn in *.
    destruct b; try discriminate.
    * destruct (decode string) eqn:E; cbn in *; try discriminate.
      destruct p, s. inv H.
      apply encode_decode in E. cbn in *. congruence.
    * destruct (decode string) eqn:E; cbn in *; try discriminate.
      destruct p, s. inv H.
  + destruct string; try discriminate; cbn in *.
    destruct b; try discriminate.
    * destruct (decode string) eqn:E; cbn in *; try discriminate.
      destruct p, s. inv H.
    * destruct (decode string) eqn:E; cbn in *; try discriminate.
      destruct p, s. inv H. apply encode_decode in E. cbn in *. congruence.
Qed.

Lemma decode_encode_sum (X Y : Type) (e1 : codeable X) (e2 : codeable Y) :
  forall (v : X + Y) (rest : list bool),
    match (decode_sum decode decode (encode_sum encode encode v ++ rest)) with
    | Some (v', rest') => v = v' /\ projT1 rest' = rest
    | None => False
    end.
Proof.
  intros [a|a] rest.
  - unfold decode_sum, encode_sum. cbn in *.
    pose proof (decode_encode a rest) as E'.
    destruct (decode (encode a ++ rest)) as [(dec1&rest1&Hreset1) | ]; auto.
    intuition; congruence.
  - unfold decode_sum, encode_sum. cbn in *.
    pose proof (decode_encode a rest) as E'.
    destruct (decode (encode a ++ rest)) as [(dec1&rest1&Hreset1) | ]; auto.
    intuition; congruence.
Qed.

Instance I_sum (X Y : Type) (e1 : codeable X) (e2 : codeable Y) : codeable (X + Y).
Proof.
  split with (encode := encode_sum encode encode) (decode := decode_sum decode decode).
  - apply encode_injective_sum.
  - apply encode_decode_sum.
  - apply decode_encode_sum.
Defined.


(** Unit **)

Lemma encode_injective_unit :
  forall (v1 v2 : unit) (r1 r2 : list bool), encode_unit v1 ++ r1 = encode_unit v2 ++ r2 -> v1 = v2 /\ r1 = r2.
Proof. intros () () r1 r2. auto. Qed.

Lemma encode_decode_unit (string : list bool) (v : unit) rest :
  decode_unit string = Some (v, rest) -> encode_unit v ++ (projT1 rest) = string.
Proof.
  destruct v, rest. unfold decode_unit, encode_unit in *. intros H. inv H; cbn. reflexivity.
Qed.

Lemma decode_encode_unit :
  forall (v : unit) (rest : list bool),
    match (decode_unit (encode_unit v ++ rest)) with
    | Some (v', rest') => v = v' /\ projT1 rest' = rest
    | None => False
    end.
Proof.
  destruct v, rest; unfold decode_unit, encode_unit in *; auto.
Qed.

Instance I_unit : codeable unit.
Proof.
  split with (encode := encode_unit) (decode := decode_unit).
  - apply encode_injective_unit.
  - apply encode_decode_unit.
  - apply decode_encode_unit.
Defined.



(** Test Playground *)

(*
Compute decoding_output_project (decode (X := unit) (encode tt)).
Compute decoding_output_project (decode (X := unit) (encode (tt, tt))).

Compute (encode (X := list unit * (unit + unit) * (unit + unit)) ([tt;tt;tt], inr tt, inl tt)).
Compute decoding_output_project (decode (X := list unit * (unit + unit) * (unit + unit)) (encode ([tt;tt;tt], inr tt, inl tt))).
*)