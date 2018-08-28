Require Import TM.Prelim.
Require Import Coq.Lists.List.

(** * Codable Class **)


(** Class of codable types *)
Class codable (sig: Type) (X: Type) := {
  encode : X -> list sig;
}.
Arguments encode {sig} {X} {_}.

Hint Extern 4 (codable (FinType(EqType ?sigX)) ?X) => cbn : typeclass_instances.

(** We often use the above coercion to write [cX x] instead of [encode x], because [encode x] can be ambigious, see [Encode_map] *)
Coercion encode : codable >-> Funclass.

Definition size (sig X : Type) (cX : codable sig X) (x : X) := length (cX x).
Arguments size {sig X} (cX x).



Instance Encode_unit : codable Empty_set unit :=
  {|
    encode x := nil
  |}.

Lemma Encode_unit_hasSize t :
  size Encode_unit t = 0.
Proof. cbn. reflexivity. Qed.


Instance Encode_bool : codable bool bool:=
  {|
    encode x := [x]
  |}.

Lemma Encode_bool_hasSize b :
  size Encode_bool b = 1.
Proof. cbn. reflexivity. Qed.

Instance Encode_Fin n : codable (Fin.t n) (Fin.t n):=
  {|
    encode i := [i]
  |}.

Lemma Encode_Fin_hasSize n i :
  size (Encode_Fin n) i = 1.
Proof. cbn. reflexivity. Qed.

(*
Compute encode true.
(* This works thanks to the coercion above *)
Compute Encode_bool true.
Compute encode tt.
Check encode Fin0.
Compute encode Fin0 : list (Fin.t 10).
*)


Section Encode_Finite.
  Variable sig : finType.

  (* This instance is not declared globally, because of overlaps *)
  Local Instance Encode_Finite : codable sig sig :=
    {|
      encode x := [x];
    |}.

  Lemma Encode_Finite_hasSize f :
    size Encode_Finite f = 1.
  Proof. reflexivity. Qed.

End Encode_Finite.
  

(** We restrict mapping of encodings to injective/retractable mappings. *)
Section Encode_map.
  Variable (X : Type).
  Variable (sig tau : Type).
  Hypothesis (cX : codable sig X).

  Variable inj : Retract sig tau.

  Global Instance Encode_map : codable tau X | 100 :=
    {
      encode x := map Retr_f (encode x);
    }.

  Lemma Encode_map_hasSize x :
    size Encode_map x = size cX x.
  Proof. cbn. now rewrite map_length. Qed.

End Encode_map.


Section Encode_map_comp.
  Variable (X : Type).
  Variable (sig1 sig2 sig3 : Type).
  Variable (cX : codable sig1 X).
  Variable (I1 : Retract sig1 sig2) (I2 : Retract sig2 sig3).

  Lemma Encode_map_comp x :
    Encode_map (Encode_map cX I1) I2 x = Encode_map cX (ComposeRetract I1 I2) x.
  Proof. cbn. rewrite List.map_map. reflexivity. Qed.
  
End Encode_map_comp.



(** Builds simple retract functions like [sigSum -> option sigX] in the form
[fun x => match x with constructor_name y => Retr_g y | _ => None] *)

Ltac build_simple_retract_g :=
  lazymatch goal with
  | [ |- ?Y -> option ?X ] =>
    (* idtac "Retract function" X Y; *)
    let x := fresh "x" in
    intros x; destruct x; intros; try solve [now apply Retr_g ]; right
  end.


Ltac build_simple_retract :=
  lazymatch goal with
  | [ |- Retract ?X ?Y ] =>
    (* idtac "Retract from" X "to" Y; *)
    let x := fresh "x" in
    let y := fresh "y" in
    let f := (eval simpl in (ltac:(intros x; constructor; now apply Retr_f) : X -> Y)) in
    (* idtac "f:" f; *)
    let g := (eval simpl in (ltac:(build_simple_retract_g) : Y -> option X)) in
    (* idtac "g:" g; *)
    apply Build_Retract with (Retr_f := f) (Retr_g := g);
    abstract now hnf; intros x y; split;
    [ destruct y; try congruence; now intros -> % retract_g_inv
    | now intros ->; now retract_adjoint
    ]
  end
.

Ltac build_eq_dec :=
  let x := fresh "x" in
  let y := fresh "y" in
  intros x y; hnf; decide equality;
  apply Dec; auto.


Lemma countMap_injective (X Y : eqType) (x : X) (A : list X) (f : X -> Y) :
  (forall x y, f x = f y -> x = y) ->
  BasicDefinitions.count (map f A) (f x) = BasicDefinitions.count A x.
Proof.
  intros HInj. revert x. induction A as [ | a A IH]; intros; cbn in *; auto.
  decide (f x = f a) as [ -> % HInj | He].
  - decide (a = a) as [_ | Ha]; auto. congruence.
  - decide (x = a) as [-> | Hx]; auto. congruence.
Qed.


Lemma countMap_zero (X Y : eqType) (A : list X) (y : Y) (f : X -> Y) :
  (forall x, f x <> y) ->
  BasicDefinitions.count (map f A) y = 0.
Proof.
  revert y. induction A as [ | a A IH]; intros; cbn in *; auto.
  decide (y = f a) as [-> | ?]; auto. now contradiction (H a).
Qed.
  

Section Encode_sum.
  Variable (X Y : Type).
  Inductive sigSum (sigX sigY : Type) : Type :=
  | sigSum_X (s : sigX)
  | sigSum_Y (s : sigY)
  | sigSum_inl
  | sigSum_inr
  .

  Arguments sigSum_inl {sigX sigY}. Arguments sigSum_inr {sigX sigY}. Arguments sigSum_X {sigX sigY}. Arguments sigSum_Y {sigX sigY}.

  Global Instance Retract_sigSum_X (sigX sigY tau : Type) (f : Retract sigX tau) : Retract sigX (sigSum tau sigY).
  Proof. build_simple_retract. Defined.
  Global Instance Retract_sigSum_Y (sigX sigY tau : Type) (f : Retract sigY tau) : Retract sigY (sigSum sigX tau).
  Proof. build_simple_retract. Defined.

  
  Global Instance sigSum_dec (sigX sigY : Type) (decX: eq_dec sigX) (decY: eq_dec sigY) :
    eq_dec (sigSum sigX sigY) := ltac:(build_eq_dec).

  Global Instance sigSum_fin (sigX sigY : finType) : finTypeC (EqType (sigSum sigX sigY)).
  Proof.
    split with (enum := sigSum_inl :: sigSum_inr :: map sigSum_X enum ++ map sigSum_Y enum). intros [x|y| | ]; cbn; f_equal.
    - rewrite <- !countSplit.
      erewrite countMap_injective.
      + rewrite enum_ok. rewrite countMap_zero. omega. congruence.
      + eapply (retract_f_injective) with (I := Retract_sigSum_X sigY (Retract_id _)).
    - rewrite <- !countSplit.
      erewrite countMap_injective.
      + rewrite enum_ok. rewrite countMap_zero. omega. congruence.
      + eapply (retract_f_injective) with (I := Retract_sigSum_Y sigX (Retract_id _)).
    - rewrite <- !countSplit. rewrite !countMap_zero. omega. all: congruence.
    - rewrite <- !countSplit. rewrite !countMap_zero. omega. all: congruence.
  Qed.

  
  Variable (sigX sigY : Type).
  Hypothesis (cX : codable sigX X) (cY : codable sigY Y).

  Global Instance Encode_sum : codable (sigSum sigX sigY) (X+Y) :=
    {|
      encode s := match s with
                  | inl x => sigSum_inl :: encode x
                  | inr y => sigSum_inr :: encode y
                  end
    |}.


  Definition Encode_sum_size s :=
    match s with
       | inl x => S (size cX x)
       | inr y => S (size cY y)
    end.
  
  Lemma Encode_sum_hasSize s :
    size Encode_sum s = Encode_sum_size s.
  Proof. cbn. destruct s; cbn; cbv [Encode_sum_size]; rewrite map_length; reflexivity. Qed.

End Encode_sum.

Arguments sigSum_inl {sigX sigY}. Arguments sigSum_inr {sigX sigY}. Arguments sigSum_X {sigX sigY}. Arguments sigSum_Y {sigX sigY}.
Hint Extern 4 (finTypeC (EqType (sigSum _ _))) => eapply sigSum_fin : typeclass_instances.
Check FinType (EqType (sigSum bool bool)).



(** If [X] is encodable over [sigX] and [Y] over [sigY]. *)
Section Encode_pair.

  Inductive sigPair (sigX sigY : Type) : Type :=
  | sigPair_X (s : sigX)
  | sigPair_Y (s : sigY)
  .

  Arguments sigPair_X {sigX sigY}. Arguments sigPair_Y {sigX sigY}.

  Global Instance Retract_sigPair_X (sigX sigY tau : Type) (f : Retract sigX tau) : Retract sigX (sigPair tau sigY).
  Proof. build_simple_retract. Defined.
  Global Instance Retract_sigPair_Y (sigX sigY tau : Type) (f : Retract sigY tau) : Retract sigY (sigPair sigX tau).
  Proof. build_simple_retract. Defined.


  Global Instance sigPair_dec (sigX sigY : Type) (decX: eq_dec sigX) (decY: eq_dec sigY) :
    eq_dec (sigPair sigX sigY) := ltac:(build_eq_dec).
  
  Global Instance sigPair_fin (sigX sigY : finType) : finTypeC (EqType (sigPair sigX sigY)).
  Proof.
    split with (enum := map sigPair_X enum ++ map sigPair_Y enum). intros [x|y]; cbn; f_equal.
    - rewrite <- !countSplit.
      erewrite countMap_injective.
      + rewrite enum_ok. rewrite countMap_zero. omega. congruence.
      + eapply (retract_f_injective) with (I := Retract_sigPair_X sigY (Retract_id _)).
    - rewrite <- !countSplit.
      erewrite countMap_injective.
      + rewrite enum_ok. rewrite countMap_zero. omega. congruence.
      + eapply (retract_f_injective) with (I := Retract_sigPair_Y sigX (Retract_id _)).
  Qed.

  Variable (sigX sigY: Type) (X Y: Type) (cX : codable sigX X) (cY : codable sigY Y).
  
  Global Instance Encode_pair : codable (sigPair sigX sigY) (X*Y) :=
    {|
      encode '(x,y) := encode x ++ encode y;
    |}.

  Definition Encode_pair_size (p : X * Y) := let (x, y) := p in size cX x + size cY y.

  Lemma Encode_pair_hasSize p : size Encode_pair p = Encode_pair_size p.
  Proof. destruct p; cbn; now rewrite app_length, !map_length. Qed.
  
End Encode_pair.

Arguments sigPair_X {sigX sigY}. Arguments sigPair_Y {sigX sigY}.

Hint Extern 4 (finTypeC (EqType (sigPair _ _))) => eapply sigPair_fin : typeclass_instances.
Check FinType (EqType (sigPair bool bool)).


Compute Encode_pair Encode_bool (Encode_sum Encode_unit Encode_bool) (true, inl tt).

Check _ : codable (sigPair bool (sigSum Empty_set bool)) unit.




Section Encode_option.

  Inductive sigOption (sigX: Type) : Type :=
  | sigOption_X (s : sigX)
  | sigOption_None
  | sigOption_Some
  .

  Arguments sigOption_Some {sigX}. Arguments sigOption_None {sigX}. Arguments sigOption_X {sigX}.

  Global Instance Retract_sigOption_X (sig tau : Type) (retr : Retract sig tau) : Retract sig (sigOption tau).
  Proof. build_simple_retract. Defined.

  Global Instance sigOption_dec sigX (decX : eq_dec sigX) :
    eq_dec (sigOption sigX) := ltac:(build_eq_dec).

  Global Instance sigOption_fin (sigX : finType) : finTypeC (EqType (sigOption sigX)).
  Proof.
    split with (enum := sigOption_Some :: sigOption_None :: map sigOption_X enum).
    intros [x| | ]; cbn; f_equal.
    - rewrite countMap_injective. 2: apply retract_f_injective with (I := Retract_sigOption_X (Retract_id _)).
      now apply enum_ok.
    - rewrite countMap_zero. omega. congruence.
    - rewrite countMap_zero. omega. congruence.
  Qed.


  Variable (sigX: Type) (X: Type) (cX : codable sigX X).

  Global Instance Encode_option : codable (sigOption sigX) (option X) :=
    {|
      encode o := match o with
                  | None => [sigOption_None]
                  | Some x => sigOption_Some :: encode x
                  end;
    |}.

  Definition Encode_option_size (o : option X) :=
    match o with
    | None => 1
    | Some x => S (size cX x)
    end.

  Lemma Encode_option_hasSize o : size _ o = Encode_option_size o.
  Proof. destruct o; cbn; f_equal; now rewrite map_length. Qed.
  
End Encode_option.

Arguments sigOption_Some {sigX}. Arguments sigOption_None {sigX}. Arguments sigOption_X {sigX}.


Hint Extern 4 (finTypeC (EqType (sigOption _))) => eapply sigOption_fin : typeclass_instances.
Check FinType (EqType (sigOption bool)).


Compute Encode_option Encode_bool None.
Compute Encode_option Encode_bool (Some false).



Section Encode_list.

  Inductive sigList (sigX : Type) : Type :=
  | sigList_X (s : sigX)
  | sigList_nil
  | sigList_cons
  .

  Arguments sigList_nil {sigX}. Arguments sigList_cons {sigX}. Arguments sigList_X {sigX}.

  Global Instance Retract_sigList_X (sig tau : Type) (retr : Retract sig tau) : Retract sig (sigList tau).
  Proof. build_simple_retract. Defined.

  Global Instance sigList_dec sigX (decX : eq_dec sigX) :
    eq_dec (sigList sigX) := ltac:(build_eq_dec).

  Global Instance sigList_fin (sigX : finType) : finTypeC (EqType (sigList sigX)).
  Proof.
    split with (enum := sigList_nil :: sigList_cons :: map sigList_X enum).
    intros [x| | ]; cbn; f_equal.
    - rewrite countMap_injective. 2: apply retract_f_injective with (I := Retract_sigList_X (Retract_id _)).
      now apply enum_ok.
    - rewrite countMap_zero. omega. congruence.
    - rewrite countMap_zero. omega. congruence.
  Qed.


  Variable sigX: Type.
  Variable (X : Type) (cX : codable sigX X).

  Fixpoint encode_list (xs : list X) : list (sigList sigX) :=
    match xs with
    | nil => [sigList_nil]
    | x :: xs' => sigList_cons :: encode x ++ encode_list xs'
    end.

  Global Instance Encode_list : codable (sigList sigX) (list X) :=
    {|
      encode := encode_list;
    |}.

  Lemma encode_list_app (xs ys : list X) :
    encode_list (xs ++ ys) = removelast (encode_list xs) ++ encode_list ys.
  Proof.
    revert ys. induction xs; intros; cbn in *; f_equal.
    rewrite IHxs. rewrite app_assoc, app_comm_cons; f_equal.
    destruct (map (fun x : sigX => sigList_X x) (cX a)) eqn:E; cbn.
    - destruct xs; cbn; auto.
    - f_equal. destruct (cX a) eqn:E2; cbn in E. congruence.
      rewrite removelast_app.
      + destruct (l ++ encode_list xs) eqn:E3; cbn; auto.
        apply app_eq_nil in E3 as (E3&E3'). destruct xs; inv E3'.
      + destruct xs; cbn; congruence.
  Qed.

  Corollary Encode_list_app (xs ys : list X) :
    Encode_list (xs ++ ys) = removelast (Encode_list xs) ++ Encode_list ys.
  Proof. cbn. now apply encode_list_app. Qed.

  Lemma encode_list_neq_nil (xs : list X) :
    encode_list xs <> nil.
  Proof. destruct xs; cbn; congruence. Qed.

  Corollary Encode_list_neq_nil (xs : list X) :
    Encode_list xs <> nil.
  Proof. cbn. apply encode_list_neq_nil. Qed.


  Fixpoint Encode_list_size (xs : list X) : nat :=
    match xs with
    | nil => 1
    | x :: xs' => S (size cX x + Encode_list_size xs')
    end.
  
  Lemma Encode_list_hasSize (xs : list X) : size _ xs = Encode_list_size xs.
  Proof.
    induction xs as [ | x xs IH]; cbn; f_equal.
    rewrite app_length, !map_length. fold (size cX x). now rewrite <- IH.
  Qed.
  
End Encode_list.

Arguments sigList_nil {sigX}. Arguments sigList_cons {sigX}. Arguments sigList_X {sigX}.

Hint Extern 4 (finTypeC (EqType (sigList _))) => eapply sigList_fin : typeclass_instances.
Check FinType(EqType (sigList bool)).


Compute Encode_list Encode_bool (nil).
(* This cannot reduce to [sigList_cons :: sigList_X true :: Encode_list _] *)
Eval cbn in Encode_list Encode_bool (true :: _).
Compute Encode_list Encode_bool (true :: false :: nil).


Section Encode_nat.

  Inductive sigNat : Type :=
  | sigNat_O
  | sigNat_S.

  Global Instance sigNat_eq : eq_dec sigNat.
  Proof. unfold dec. decide equality. Defined.

  Global Instance sigNat_fin : finTypeC (EqType sigNat).
  Proof. split with (enum := [sigNat_O; sigNat_S]). intros [ | ]; cbn; reflexivity. Qed.

  Global Instance Encode_nat : codable sigNat nat :=
    {|
      encode n := repeat sigNat_S n ++ [sigNat_O];
    |}.


  Lemma Encode_nat_hasSize n : size _ n = S n.
  Proof. cbn. rewrite app_length, repeat_length. cbn. omega. Qed.
  
  Corollary Encode_nat_eq_nil n :
    Encode_nat n <> nil.
  Proof. intros H % length_zero_iff_nil. fold (size _ n) in H. rewrite Encode_nat_hasSize in H. omega. Qed.

End Encode_nat.

Check FinType(EqType sigNat).



    
(** Test Playground *)

(*
Compute encode (Some true).
Eval cbv in encode None.

Compute encode false.
Compute encode true.

Compute encode (repeat tt 42).
Compute encode 42.

Compute encode (tt, tt).

Compute encode (inl 42).
Compute encode (inr 42).

Compute Encode_pair Encode_nat Encode_nat (1, 2).
Compute encode (1,2).

Compute encode [4;5].
Compute encode (Some 4) ++ encode (Some 5) ++ encode None.

Compute encode ([tt;tt;tt], tt).
*)