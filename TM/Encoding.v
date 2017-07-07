Require Import Prelim LiftNM Compound.

(** * Coding Alphabet *)
Inductive codsig : Type :=
| Tup : codsig
| Con : codsig
| Nil : codsig
| Inl : codsig
| Inr : codsig.

Instance codsig_dec : eq_dec codsig.
Proof. intros x y. hnf. decide equality. Qed.

(** * Coding Types **)

Inductive codtype : Type :=
| enctuple : forall (t1 t2 : codtype), codtype
| enclist  : forall (t : codtype), codtype
| encsum   : forall (t1 t2 : codtype), codtype
| encunit  : codtype.

Instance codtype_dec : eq_dec codsig.
Proof. intros x y. hnf. decide equality. Qed.

(** Compound Types *)
Definition encnat := enclist encunit.
Definition encbool := encsum encunit encunit.
Definition encopt (t : codtype) := encsum t encunit.
Definition enctriple (t1 t2 t3 : codtype) := enctuple t1 (enctuple t2 t3).

Fixpoint codtype_to_type (t : codtype) : Type :=
  match t with
  | enctuple t1 t2 => prod (codtype_to_type t1) (codtype_to_type t2)
  | enclist  t     => list (codtype_to_type t)
  | encsum   t1 t2 => sum  (codtype_to_type t1) (codtype_to_type t2)
  | encunit        => unit
  end.


(** * Encoding *)
Fixpoint encode_list (t : codtype) (xs : list (codtype_to_type t)) : list codsig.
Proof.
  destruct xs.
  - apply (Nil :: nil).
  - apply (cons Con). apply (encode_list t xs).
Defined.
    
Fixpoint encode (t : codtype) : codtype_to_type t -> list codsig.
Proof.
  destruct t; cbn.
  - intros (a,b). apply (Tup :: encode t1 a ++ encode t2 b).
  - apply encode_list.
  - intros [a|b].
    + apply (Inl :: encode t1 a).
    + apply (Inr :: encode t2 b).
  - intros _. apply nil.
Defined.


(** * Decoding *)

Ltac invalid_encoding := apply None.

Print codtype.

Inductive decoding_tree : codtype -> list codsig -> Type :=
| tree_prod (e1 e2 : codtype) (t1 t2 : list codsig) :
    decoding_tree e1 t1 -> decoding_tree e2 t2 ->
    decoding_tree (enctuple e1 e2) (Tup :: t1 ++ t2)
| tree_unit : decoding_tree encunit []
| tree_invalid (e : codtype) (t : list codsig) : decoding_tree e t.




Definition suffix (X : Type) (xs ys : list X) :=
  { n : nat | List.skipn n ys = xs }.

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



Inductive suffix_induction : list codsig -> Type :=
| suffix_induction_nil : suffix_induction []
| suffix_induction_con (ys : list codsig) : (forall xs: list codsig, suffix xs ys -> xs <> ys -> suffix_induction xs) ->
                                            suffix_induction ys.

Inductive size_ind (X : Type) (f : X -> nat) : X -> Type :=
| size_ind_intro (x : X) : (forall y, f y < f x -> size_ind f y) -> size_ind f x.

Lemma size_Ind (X : Type) (f : X -> nat) (x : X) : size_ind f x.
Proof.
  constructor.
  assert (G: forall n y, f y < n -> size_ind f y).
  { intros n. induction n.
    - intros y B. exfalso. omega.
    - intros y B. constructor. intros z C. apply IHn. omega. }
  apply G.
Qed.

Lemma suffix_induction_provider (ys : list codsig) : suffix_induction ys.
Proof.
  pose proof (size_Ind (@List.length codsig) ys) as X.
  induction X as [ys _ IH].
  destruct ys.
  - constructor.
  - constructor. intros xs H1 H2. apply IH. cbn. pose proof (suffix_size_decrease H2 H1). cbn in *. omega.
Qed.


Definition decoding_function (e : codtype) :=
  forall string : list codsig, option (codtype_to_type e * {rest : list codsig & suffix rest string}).

(* TODO: Make this a fixpoint *)
Definition decode_list' (e : codtype)
         (decodeEntries : decoding_function e)
         (string : list codsig)
         (ind : suffix_induction string) :
  option (list (codtype_to_type e) * {rest : list codsig & suffix rest string }).
Proof.
  induction ind as [ | string T IH]; cbn in *.
  - invalid_encoding.
  - destruct string as [ | s ss].
    + invalid_encoding.
    + destruct s eqn:E.
      * invalid_encoding.
      * destruct (decodeEntries ss) as [ (dec1, (rest1, HRest1)) | ]; [ | invalid_encoding].
        (* assert (IH : forall xs : list codsig,
                   suffix xs (Con :: ss) ->
                   xs <> Con :: ss ->
                   option
                     (list (codtype_to_type e) *
                      {rest : list codsig & suffix rest xs})).
        {
          intros ***. apply decode_list'. exact decodeEntries. now apply T.
        } *)
        destruct (IH rest1) as [ (dec2, (rest2, HRest2)) | ]; [ | | | invalid_encoding].
        -- now apply suffix_skip.
        -- intros ->. now apply suffix_put in HRest1.
        -- do 2 constructor. apply (dec1 :: dec2). exists rest2. apply suffix_skip. eapply suffix_transitive; eauto.
      * invalid_encoding. * invalid_encoding. * invalid_encoding.
Defined.


Fixpoint decode' (Provider : forall (ys : list codsig), suffix_induction ys) (t : codtype)
         (string : list codsig) : option (codtype_to_type t * {rest : list codsig & suffix rest string}).
Proof.
  destruct t eqn:E; cbn in *.
  - pose proof (decode' Provider c1) as decode1. pose proof (decode' Provider c2) as decode2.
    destruct string as [ | s ss].
    + invalid_encoding.
    + destruct s.
      * destruct (decode1 ss)    as [ (dec1, (rest1, HRest1)) | ]; [ | invalid_encoding].
        destruct (decode2 rest1) as [ (dec2, (rest2, Hrest2)) | ]; [ | invalid_encoding].
        do 2 constructor. constructor. apply dec1. apply dec2. exists rest2. apply suffix_skip. eapply suffix_transitive; eauto.
      * invalid_encoding. * invalid_encoding. * invalid_encoding. * invalid_encoding.
  - apply (decode_list'). unfold decoding_function. hnf. now apply (decode' Provider). apply Provider.
  - pose proof (decode' Provider c1) as decode1. pose proof (decode' Provider c2) as decode2.
    destruct string as [ | s ss].
    + invalid_encoding.
    + destruct s.
      * invalid_encoding. * invalid_encoding. * invalid_encoding.
      * destruct (decode1 ss) as [ (dec, (rest, HRest)) | ]; [ | invalid_encoding].
        constructor. constructor. left.  apply dec. exists rest. now apply suffix_skip.
      * destruct (decode2 ss) as [ (dec, (rest, HRest)) | ]; [ | invalid_encoding].
        constructor. constructor. right. apply dec. exists rest. now apply suffix_skip.
  - do 2 constructor. constructor. exists string. apply suffix_full.
Defined.

Definition decode (t : codtype) : decoding_function t.
Proof. intros string. apply decode'. apply suffix_induction_provider. Defined.



(** * Encode and decode *)