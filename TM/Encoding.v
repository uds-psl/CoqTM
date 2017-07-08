Require Import Prelim LiftNM Compound.

(** * Coding Alphabet *)
Definition codsig : Type := bool.

Instance codsig_dec : eq_dec codsig.
Proof. intros x y. hnf. decide equality. Defined.

(** * Coding Types **)

Inductive codtype : Type :=
| codtuple : forall (t1 t2 : codtype), codtype
| codlist  : forall (t : codtype), codtype
| codsum   : forall (t1 t2 : codtype), codtype
| codunit  : codtype.

Instance codtype_dec : eq_dec codsig.
Proof. intros x y. hnf. decide equality. Defined.

(** Compound Types *)
Definition codnat := codlist codunit.
Definition codbool := codsum codunit codunit.
Definition codopt (t : codtype) := codsum t codunit.
Definition codtriple (t1 t2 t3 : codtype) := codtuple (codtuple t1 t2) t3.

Fixpoint codtype_to_type (t : codtype) : Type :=
  match t with
  | codtuple t1 t2 => prod (codtype_to_type t1) (codtype_to_type t2)
  | codlist  t     => list (codtype_to_type t)
  | codsum   t1 t2 => sum  (codtype_to_type t1) (codtype_to_type t2)
  | codunit        => unit
  end.


(** * Encoding *)

Definition encoding_function (t : codtype) :=
  forall v : codtype_to_type t, list codsig.

Fixpoint encode_list (t : codtype) (encode_entries : encoding_function t) (xs : list (codtype_to_type t)) : list codsig.
Proof.
  destruct xs.
  - apply (false :: nil).
  - apply (cons true). apply app. apply (encode_entries c). apply (encode_list t encode_entries xs).
Defined.
    
Fixpoint encode (t : codtype) : codtype_to_type t -> list codsig.
Proof.
  destruct t; cbn.
  - intros (a,b). apply (encode t1 a ++ encode t2 b).
  - apply encode_list. intros v. apply (encode t v).
  - intros [a|b].
    + apply (true  :: encode t1 a).
    + apply (false :: encode t2 b).
  - intros _. apply nil.
Defined.

(** * Convert from Coq Type *)

Definition from_bool (b : bool) := if b then inl tt else inr tt.
Definition from_option (t : codtype) (o : option (codtype_to_type t)) :=
  match o with Some d => inl d | None => inr tt end.
Fixpoint from_nat n : (codtype_to_type codnat) :=
  match n with
  | S n' => tt :: from_nat n'
  | O => nil
  end.


(** Test *)
Compute @encode (codtuple (codopt codbool) codnat) (@from_option codbool (Some (from_bool false)), from_nat 3).
Compute @encode (codtuple (codopt codbool) codnat) (@from_option codbool None, from_nat 3).


(** * Suffix *)

Definition suffix (X : Type) (xs ys : list X) :=
  exists n : nat, List.skipn n ys = xs.

Lemma suffix_nil (X : Type) (xs : list X) : suffix [] xs.
Proof.
  induction xs.
  - exists 0. reflexivity.
  - destruct IHxs as (n&H). exists (S n). assumption.
Qed.

Lemma skipn_nil (X : Type) (n : nat) : skipn n (@nil X) = [].
Proof. induction n; cbn in *; auto. Qed.

Lemma suffix_from_nil (X : Type) (xs : list X) : suffix xs [] -> xs = [].
Proof. intros (n&H). rewrite skipn_nil in H. congruence. Qed.

Lemma skipn_plus (X : Type) (xs : list X) (n1 n2 : nat) :
  skipn (n1 + n2) xs = skipn n2 (skipn n1 xs).
Proof.
  revert n2 xs. induction n1; intros n2 xs; cbn in *.
  - reflexivity.
  - destruct xs as [ | x xs]; cbn; auto. now rewrite skipn_nil.
Qed.

Lemma suffix_transitive (X : Type) (xs ys zs : list X) :
  suffix ys xs -> suffix zs ys -> suffix zs xs.
Proof.
  intros (n1&H1) (n2&H2). subst. eexists. now eapply skipn_plus.
Qed.

Lemma suffix_skip (X : Type) (xs ys : list X) (y : X) :
  suffix xs ys -> suffix xs (y :: ys).
Proof. intros (n&<-). exists (S n). cbn. reflexivity. Qed.

Lemma suffix_app (X : Type) (xs ys zs : list X) :
  suffix xs ys -> suffix xs (zs ++ ys).
Proof.
  induction zs; intros H.
  - now rewrite app_nil_l.
  - cbn. apply suffix_skip. auto.
Qed.

Lemma suffix_full (X : Type) (xs : list X) :
  suffix xs xs.
Proof. now exists 0. Qed.


Lemma list_con_neq (X : Type) (xs : list X) (x : X) :
  xs <> x :: xs.
Proof.
  induction xs as [ | x' xs IH]; cbn.
  - congruence.
  - intros H. injection H. intros H' ->. congruence.
Qed.


Lemma skipn_size (X : Type) (xs : list X) (n : nat) : xs <> nil -> n > 0 -> | skipn n xs | < | xs |.
Proof.
  revert xs. induction n; intros xs H1; cbn in *.
  - omega.
  - destruct xs; cbn in *.
    + tauto.
    + decide (n = 0) as [-> | H3]; cbn in *.
      * omega.
      * assert (n > 0) as H4 by omega.
        intros H.
        assert (xs = [] \/ xs <> []) as [-> | H5].
        { destruct xs; [left|right]; congruence. }
        -- rewrite skipn_nil. cbn. omega.
        -- specialize (IHn xs H5 H4). omega.
Qed.

Lemma suffix_put (X : Type) (xs : list X) (y : X) :
  suffix (y :: xs) xs -> False.
Proof.
  intros (n&H). destruct n; cbn in *.
  - now apply list_con_neq in H.
  - destruct xs as [ | a xs ].
    + congruence.
    + assert ( | skipn (S n) (a :: xs ) | < | a :: xs |).
      { apply skipn_size; subst. congruence. omega. }
      cbn in H0. rewrite H in H0. cbn in *. omega.
Qed.

Lemma skipn_0 (X : Type) (n : nat) (xs : list X) :
  skipn n xs = xs -> xs = nil \/ n = 0.
Proof.
  revert xs. induction n; intros xs H; cbn in *.
  - auto.
  - destruct xs.
    + left. reflexivity.
    + exfalso. eapply suffix_put; eexists. eauto.
Qed.

Lemma suffix_size_decrease (X : eqType) (xs ys : list X) :
  xs <> ys -> suffix xs ys -> |xs| < |ys|.
Proof.
  intros H (n&H2). revert xs ys H H2.
  induction n; intros xs ys H H2; cbn in *.
  - subst. tauto.
  - destruct ys.
    + subst. tauto.
    + subst. cbn in *.
      decide (n = 0) as [-> | H1]; cbn in *.
      * omega.
      * decide (skipn n ys = ys) as [H2 | H2].
        -- subst. specialize (IHn (skipn n ys) ys). destruct (skipn_0 H2) as [-> | ->]; cbn in *; auto.
           rewrite skipn_nil. cbn. omega.
        -- specialize (IHn (skipn n ys) ys H2). rewrite IHn. omega. reflexivity.
Qed.


Inductive suffix_induction (ys : list codsig) : Type :=
| suffix_induction_con : (forall xs: list codsig, suffix xs ys -> xs <> ys -> suffix_induction xs) ->
                         suffix_induction ys.

Inductive size_ind (X : Type) (f : X -> nat) : X -> Type :=
| size_ind_intro (x : X) : (forall y, f y < f x -> size_ind f y) -> size_ind f x.


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

Lemma suffix_induction_provider (ys : list codsig) : suffix_induction ys.
Proof.
  pose proof (size_Ind (@List.length codsig) ys) as X. induction X as [ys _ IH].
  constructor. intros xs H1 H2. apply IH. now apply (suffix_size_decrease H2 H1).
Defined.


(** * Prefix *)

Definition prefix (X : Type) (xs ys : list X) :=
  exists n : nat, firstn n ys = xs.

Lemma prefix_full (X : Type) (xs : list X) :
  prefix xs xs.
Proof. exists (|xs|). apply List.firstn_all. Qed.

Lemma prefix_app (X : Type) (xs ys zs : list X) :
  prefix xs ys -> prefix xs (ys ++ zs).
Proof.
  intros (n&<-).
  decide (n < length ys) as [E|E'].
  - exists (n). rewrite List.firstn_app.
    replace (n - (| ys |)) with 0 by omega. cbn. rewrite List.app_nil_r. reflexivity.
  - assert (|ys| <= n) as E by omega.
    rewrite List.firstn_all2; auto. exists (|ys|). rewrite List.firstn_app.
    replace ((| ys |) - (| ys |)) with 0 by omega. cbn. rewrite List.app_nil_r. apply List.firstn_all.
Qed.

Lemma prefix_transitive (X : Type) (xs ys zs : list X) :
  prefix xs ys -> prefix ys zs -> prefix xs zs.
Proof. intros (n1&H1) (n2&H2). subst. exists (Nat.min n1 n2). now rewrite List.firstn_firstn. Qed.


(** * Decoding *)

Ltac invalid_encoding := apply None.


Definition decoding_output (e : codtype) (string : list codsig) :=
  option (codtype_to_type e * {rest : list codsig & suffix rest string}).

Definition decoding_function (e : codtype) :=
  forall string : list codsig, decoding_output e string.

Inductive my_induction : nat -> Type :=
| my_induction_intro (m : nat) (H: forall n, n < m -> my_induction n) : my_induction m.

Fixpoint my_induction_test (m : nat) (e : my_induction m) {struct e} : nat.
Proof.
  destruct e as [m H].
  destruct m.
  - apply 0.
  - assert (my_induction m). apply H. do 2 constructor. apply (my_induction_test m H0).
Abort. 

Fixpoint my_induction_test (m : nat) (e : my_induction m) {struct e} : nat :=
  match e with
    @my_induction_intro m H => 0
  end.

Lemma suffix_skip' (X : Type) (x : X) (xs : list X) :
  suffix xs (x :: xs).
Proof. apply suffix_skip, suffix_full. Qed.

Lemma tam (xs : list nat) : True.
Proof.
  destruct xs as [ | x xs'] eqn:E.
  Show Proof.

Abort.


Check (
(fun xs : list nat =>
 let E := eq_refl : xs = xs in
 match xs as l0 return (xs = l0 -> nat) with
 | [] => fun E0 : xs = [] => 0
 | x :: xs' => fun E0 : xs = x :: xs' => 0
 end E)
  [1]).

Lemma decode_list'_helper1 (e : codtype) (x : codsig) (string : list codsig) (ss : list codsig) :
      string = x :: ss -> suffix ss string.
Proof. intros ->. apply suffix_skip'. Qed.

Lemma decode_list'_helper2 (e : codtype) (x : codsig) (string : list codsig) (ss : list codsig) :
      string = x :: ss -> ss <> string.
Proof. intros ->. intros H. now apply list_con_neq in H. Qed.

Lemma decode_list'_helper3 (e : codtype) (x : codsig) (string : list codsig) (ss : list codsig)
      (Rest2 : {rest : list codsig & suffix rest ss}) :
  suffix (projT1 Rest2) (x :: ss).
Proof. cbn. destruct Rest2. cbn. subst. now apply suffix_skip. Qed.

(* Dont ask how long this took *)
Fixpoint decode_list' (e : codtype) (decodeEntries : decoding_function e) (string : list codsig)
         (ind : suffix_induction string) { struct ind } :
  option (list (codtype_to_type e) * {rest : list codsig & suffix rest string }) :=
  let E := eq_refl : string = string in
  (match string as string'
         return
         (string = string' ->
          option (list (codtype_to_type e) * {rest : list codsig & suffix rest string' })) with
   | nil => fun E0 : string = [] => None
   | true  :: ss => fun E0 : string = true :: ss =>
                     match (decodeEntries ss) with
                     | None => None
                     | Some (dec1, Rest1) =>
                       match ind with
                       | suffix_induction_con H => 
                         match (@decode_list' e decodeEntries ss (H _ (decode_list'_helper1 e E0) (decode_list'_helper2 e E0))) with
                         | None => None
                         | Some (dec2, Rest2) =>
                           Some (dec1 :: dec2, existT _ (projT1 Rest2) (decode_list'_helper3 e true string Rest2))
                         end
                       end
                     end
   | false :: ss => fun E0 : string = false :: ss => Some (nil, existT _ ss (suffix_skip' _ _))
   end) E.

Definition decode_list (e : codtype) (decodeEntries : decoding_function e)
           (string : list codsig) :=
  @decode_list' e decodeEntries string (suffix_induction_provider string).


Fixpoint decode (t : codtype) (string : list codsig) :
  option (codtype_to_type t * {rest : list codsig & suffix rest string}).
Proof.
  destruct t; cbn in *.
  - (* tuple *)
    pose proof (decode t1) as decode1. pose proof (decode t2) as decode2.
    destruct (decode1 string) as [ (dec1, (rest1, HRest1)) | ]; [ | invalid_encoding].
    destruct (decode2 rest1)  as [ (dec2, (rest2, Hrest2)) | ]; [ | invalid_encoding].
    do 2 constructor. constructor. apply dec1. apply dec2. exists rest2. eapply suffix_transitive; eauto.
  - (* list *)
    apply (decode_list'). unfold decoding_function. hnf. now apply decode. apply suffix_induction_provider.
  - (* sum *)
    pose proof (decode t1) as decode1. pose proof (decode t2) as decode2.
    destruct string as [ | s ss].
    + invalid_encoding.
    + destruct s eqn:E.
      * (* Inl = true *)
        destruct (decode1 ss) as [ (dec, (rest, HRest)) | ]; [ | invalid_encoding].
        constructor. constructor. left.  apply dec. exists rest. now apply suffix_skip.
      * (* Inr = false *)
        destruct (decode2 ss) as [ (dec, (rest, HRest)) | ]; [ | invalid_encoding].
        constructor. constructor. right. apply dec. exists rest. now apply suffix_skip.
  - (* unit *)
    do 2 constructor. constructor. exists string. apply suffix_full.
Defined.


(** * Encode and decode *) 

(** Test *)

Compute decode (codunit) [].
Compute decode (codtuple codunit codunit) [].
Compute decode (codtriple codunit codunit codunit) [].
Compute (@from_option codbool (Some (from_bool false)), from_nat 3).
Compute decode (codtuple (codopt codbool) codnat) (@encode (codtuple (codopt codbool) codnat)
                                                           (@from_option codbool (Some (from_bool false)), from_nat 3)).
Compute decode (codtuple (codopt codbool) codnat) (@encode (codtuple (codopt codbool) codnat)
                                                           (@from_option codbool None, from_nat 3)).

Lemma decode_monoton (t : codtype) (string1 string2 : list codsig) :
  match decode t (string1) with
  | Some (v, rest) => match decode t (string1 ++ string2) with
                     | Some (v', rest') => v = v' /\ prefix (projT1 rest) (projT1 rest')
                     | None => False
                     end
  | None => True
  end.
Proof.
  revert string1 string2. induction t; intros string1 string2; cbn in *.
  - destruct (decode t1 string1) as [(v1, (rest1, Hrest1))| ] eqn:E1; auto.
    destruct (decode t1 (string1 ++ string2)) as [(vt, (restt, Hrestt))| ] eqn:E2.
    + destruct (decode t2 rest1) as [(v2, (rest2, Hrest2))| ] eqn:E3; cbn in *; auto.
      destruct (decode t2 restt) as [(v2',(rest2',Hrest2'))| ]eqn:E4; cbn in *.
      * pose proof (IHt1 string1 string2) as IHt1'.
        rewrite E1 in IHt1'. rewrite E2 in IHt1'. destruct IHt1' as (->&IHt1'). cbn in *.
        pose proof (IHt2 rest1 rest2') as IHt2'.
        rewrite E3 in IHt2'. cbn in *.
        destruct (decode t2 (rest1 ++ rest2')) as [(v3, (rest3, Hrest3))| ] eqn:E5; cbn in *; auto.
        destruct IHt2' as (->&IHt2'). admit.
      *
        specialize (IHt1 string1 string2). rewrite E1 in IHt1. rewrite E2 in IHt1.
        destruct IHt1 as (->&IHt1).
        specialize (IHt2 rest1 rest2). rewrite E3 in IHt2.
        destruct (decode t2 (rest1 ++ rest2)) eqn:E5; cbn in *; auto.
        destruct p. destruct IHt2 as (->&IHt2).
        admit.
    + specialize (IHt1 string1 string2). specialize (IHt2 string1 string2).
      now erewrite E2, E1 in *.
  - admit.
  - destruct string1 eqn:E; auto; cbn in *. destruct c eqn:E2; cbn in *; auto.
    + destruct (decode t1 l) as [(v1, (rest1, Hrest1))| ] eqn:E3; auto.
      destruct (decode t1 (l ++ string2)) as [(v2, (rest2, Hrest2))| ] eqn:E4; cbn in *; auto.
      * specialize (IHt1 l string2). rewrite E3 in IHt1. rewrite E4 in IHt1. destruct IHt1 as (->&IHt1); cbn in *.
        split; auto.
      * specialize (IHt1 l string2). rewrite E3 in IHt1. rewrite E4 in IHt1; auto.
    + destruct (decode t2 l) as [(v1, (rest1, Hrest1))| ] eqn:E3; cbn in *; auto.
      destruct (decode t2 (l ++ string2)) as [(v2, (rest2, Hrest2))| ] eqn:E4; cbn in *; auto.
      * specialize (IHt2 l string2). rewrite E3 in IHt2. rewrite E4 in IHt2. destruct IHt2 as (->&IHt2); cbn in *.
        split; auto.
      * specialize (IHt2 l string2). rewrite E3 in IHt2. rewrite E4 in IHt2; auto.
  - split. reflexivity. apply prefix_app, prefix_full.
Admitted.


Lemma encode_decode_list (t : codtype) (ls : list (codtype_to_type t))
      (decode_entries : decoding_function t)
      (encode_entries : encoding_function t) :
  (forall v : (codtype_to_type t),
      match decode_entries (encode_entries v) with
      | Some (v', rest) => v = v' /\ projT1 rest = []
      | None => False
      end) ->
  match decode_list decode_entries (@encode_list t encode_entries ls) with
  | Some (ls', rest) => ls = ls' /\ projT1 rest = []
  | None => False
  end.
Proof.
  intros H. unfold decode_list.
  induction ls as [ | l ls IH].
  - cbn. auto.
  - cbn.
    destruct (decode_entries (encode_entries l ++ encode_list encode_entries ls)) as [(vt, (restt, Hrestt))| ] eqn:E1; cbn in *; auto.
    + destruct restt eqn:E2; cbn in *; auto.
      * admit.
      * destruct c eqn:E3; cbn in *; auto. admit. admit.
    + admit.
Abort.

Lemma encode_decode_list (t : codtype) (string : list codsig) ls rest
      (decode_entries : decoding_function t)
      (encode_entries : encoding_function t) :
  (forall string' v' rest',
      decode_entries string' = Some (v', rest') -> encode_entries v' ++ (projT1 rest') = string'
  ) ->
  decode_list decode_entries string = Some (ls, rest) -> encode_list encode_entries ls ++ (projT1 rest) = string.
Proof.
  intros encode_decode_entries. unfold decode_list.
  generalize (suffix_induction_provider string) as ind. induction ind as [xs H IH].
  cbn in *.
  destruct xs eqn:E; intros H1; try discriminate.
  destruct c.
  - destruct (decode_entries l) eqn:E2; try discriminate.
    destruct p, s. unfold suffix_induction_rect in *. cbn in *.
Admitted.


  
Lemma encode_decode (t : codtype) (string : list codsig) v rest :
  decode t string = Some (v, rest) -> encode v ++ (projT1 rest) = string.
Proof.
  revert string v rest. induction t; intros string v rest H.
  - cbn in *. destruct v as (v1, v2).
    destruct (decode t1 string) as [(cod1, (rest1, HRest1))| ] eqn:E1; cbn in *; try discriminate.
    destruct (decode t2 rest1) as [(cod2, (rest2, HRest2))| ] eqn:E2; cbn in *; try discriminate.
    inv H.
    specialize (IHt1 _ _ _ E1). cbn in *.
    specialize (IHt2 _ _ _ E2). cbn in *.
    subst. now rewrite app_assoc.
  - eapply encode_decode_list; eauto.
  - cbn in *. destruct v as [v1|v2].
    + destruct string; try discriminate; cbn in *.
      destruct c; try discriminate.
      * destruct (decode t1 string) eqn:E; cbn in *; try discriminate.
        destruct p, s. inv H. specialize (IHt1 _ _ _ E). cbn in *. subst. reflexivity.
      * destruct (decode t2 string) eqn:E; cbn in *; try discriminate.
        destruct p, s. inv H.
    + destruct string; try discriminate; cbn in *.
      destruct c; try discriminate.
      * destruct (decode t1 string) eqn:E; cbn in *; try discriminate.
        destruct p, s. inv H.
      * destruct (decode t2 string) eqn:E; cbn in *; try discriminate.
        destruct p, s. inv H. specialize (IHt2 _ _ _ E). cbn in *. subst. reflexivity.
  - cbn in *. destruct rest. cbn in *. now inv H.
Qed.

Lemma encode_decode_nil (t : codtype) (v : codtype_to_type t) (string : list codsig) :
  match decode t (encode v) with
  | Some (v', rest) => v = v' /\ projT1 rest = []
  | None => False
  end.
Proof.
  induction t; cbn in *.
  - destruct v as (v1, v2); cbn in *.
    destruct (decode t1 (encode v1 ++ encode v2)) as [(dec1, (rest1, HRest1)) | ] eqn:E1; cbn in *.
    + destruct (decode t2 rest1) as [(dec2, (rest2, HRest2)) | ] eqn:E2; cbn in *.
      *
        specialize (IHt2 dec2).
        destruct (decode t2 (encode dec2)) as [(v2',Rest2')| ] eqn:E3; auto.
        destruct IHt2 as (->&IHt2).
        admit.
      * admit.
    + admit.
  - apply encode_decode_list. auto.
  - destruct v as [v|v].
    + destruct (decode t1 (encode v)) as [(v1, (rest1, Hrest1))| ] eqn:E; cbn in *; auto.
      * specialize (IHt1 v). rewrite E in IHt1. cbn in *. intuition; subst; auto.
      * specialize (IHt1 v). rewrite E in IHt1. cbn in *. intuition; subst; auto.
    + destruct (decode t2 (encode v)) as [(v2, (rest2, Hrest2))| ] eqn:E; cbn in *; auto.
      * specialize (IHt2 v). rewrite E in IHt2. cbn in *. intuition; subst; auto.
      * specialize (IHt2 v). rewrite E in IHt2. cbn in *. intuition; subst; auto.
  - destruct v. auto.
Restart.
Proof.
  