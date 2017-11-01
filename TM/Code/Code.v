Require Import Prelim.
Require Import Retract.

Definition Bool_Fin := FinType (EqType bool).


(** * Codeable Class **)

Section Codeable.

  Variable (sigma : finType).
  Variable (X : Type).

  Definition encoding_function := X -> list sigma.

  Class codeable :=
    mk_codeable
      {
        encode : encoding_function;
        encode_injective : forall (v1 v2 : X) (r1 r2 : list sigma), encode v1 ++ r1 = encode v2 ++ r2 -> v1 = v2 /\ r1 = r2;
      }.

  Hypothesis codeable_X : codeable.

  Lemma encode_injective' : forall v1 v2 : X, encode v1 = encode v2 -> v1 = v2.
  Proof.
    intros v1 v2 H.
    assert (encode v1 ++ [] = encode v2 ++ []) by now rewrite !app_nil_r.
    now apply encode_injective in H0.
  Qed.

End Codeable.
Arguments encode { _ } { _ } { _ }.

Section Encode_Finite.
  Variable X : finType.

  Lemma encode_finite_injective :
    forall (v1 v2 : X) (r1 r2 : list X),
      [v1] ++ r1 = [v2] ++ r2 -> v1 = v2 /\ r1 = r2.
  Proof. firstorder; now inv H. Qed.

  Instance Encode_Finite : codeable X X.
  Proof. apply mk_codeable with (encode := fun x => [x]). apply encode_finite_injective. Defined.
End Encode_Finite.

Instance Encode_Bool : codeable (FinType (EqType bool)) bool := Encode_Finite (FinType (EqType bool)).


Section RListInduction.
  Variable X : Type.

  Inductive rlist : list X -> Type :=
  | rnil  : rlist []
  | rcons : forall xs x, rlist xs -> rlist (xs ++ [x]).

  Lemma rlist_cons (xs : list X) (x : X) :
    rlist xs -> rlist (x :: xs).
  Proof.
    intros H. induction H.
    - replace ([x]) with ([] ++ [x]). constructor. constructor. apply app_nil_l.
    - replace (x :: xs ++ [x0]) with ((x :: xs) ++ [x0]) by reflexivity. now constructor.
  Qed.

  Lemma rlist_induction : forall xs : list X, rlist xs.
  Proof.
    intros xs. induction xs.
    - constructor.
    - now apply rlist_cons.
  Qed.

End RListInduction.

Section DoubleListInduction.
  Variable (X Y : Type).

  Inductive dlistInd : list X -> list Y -> Prop :=
  | dlist_nil_nil   : dlistInd nil nil
  | dlist_nil_cons  : forall y ys, dlistInd nil ys -> dlistInd nil (y :: ys)
  | dlist_cons_nil  : forall x xs, dlistInd xs nil -> dlistInd (x :: xs) nil
  | dlist_cons_cons : forall x xs y ys, dlistInd xs ys -> dlistInd (x :: xs) ys -> dlistInd xs (y :: ys) -> dlistInd (x :: xs) (y :: ys).

  Lemma doublelistinduction_xs_nil xs : dlistInd xs nil.
  Proof. induction xs; now constructor. Qed.

  Lemma doublelistinduction_nil_ys ys : dlistInd nil ys.
  Proof. induction ys; now constructor. Qed.

  Lemma doubleListInduction xs ys : dlistInd xs ys.
  Proof.
    revert ys. induction xs; intros ys.
    - apply doublelistinduction_nil_ys.
    - destruct ys.
      + constructor. apply doublelistinduction_xs_nil.
      + constructor; auto. induction ys; constructor; auto.
  Qed.

End DoubleListInduction.


Section Map_Injective.
  Variable (sig tau : Type) (t : sig -> tau).
  Hypothesis t_injective : forall s1 s2, t s1 = t s2 -> s1 = s2.

  Lemma map_injective (xs ys : list sig) :
    map t xs = map t ys -> xs = ys.
  Proof.
    revert ys. induction xs; intros ys H; cbn in *.
    - erewrite map_eq_nil; eauto.
    - destruct ys; cbn in *; inv H.
      rewrite (t_injective H1). f_equal. auto.
  Qed.

End Map_Injective.


Section Usefull_Injections.

  Variable (sig tau : Type).

  Definition option_inj : tight_retract sig (option sig).
  Proof. apply Build_tight_retract with (tretract_f := Some) (tretract_g := id). firstorder. Defined.

  Lemma inl_inj' : forall (x : sig) (y : sig + tau), match y with | inl x0 => Some x0 | inr _ => None end = Some x <-> y = inl x.
  Proof. firstorder; destruct y; inv H; firstorder. Qed.

  Definition inl_inj : tight_retract sig (sig + tau) := Build_tight_retract inl_inj'.

  Lemma inr_inj' : forall (x : tau) (y : sig + tau), match y with | inl _ => None | inr x0 => Some x0 end = Some x <-> y = inr x.
  Proof. firstorder; destruct y; inv H; firstorder. Qed.

  Definition inr_inj : tight_retract tau (sig + tau) := Build_tight_retract inr_inj'.

  Lemma empty_left_inj' :
    forall (x : Empty_set + sig) (y : sig),
      Some (inr y) = Some x <-> y = match x with | inl devil => match devil return sig with end | inr x0 => x0 end.
  Proof.
    firstorder.
    - now inversion H.
    - destruct x as [ [] | ]. congruence.
  Qed.
  Definition empty_left_inj : tight_retract (Empty_set + sig) sig := Build_tight_retract empty_left_inj'.
  Lemma empty_right_inj' :
    forall (x : sig + Empty_set) (y : sig),
      Some (inl y) = Some x <-> y = match x with | inr devil => match devil return sig with end | inl x0 => x0 end.
  Proof.
    firstorder.
    - now inversion H.
    - destruct x as [ | [] ]. congruence.
  Qed.
  Definition empty_right_inj : tight_retract (sig + Empty_set) sig := Build_tight_retract empty_right_inj'.

End Usefull_Injections.


Section Encode_Map.
  Variable (X : Type).
  Variable (sig tau : finType).
  Hypothesis (code_sig : codeable sig X).
  Hypothesis (inj : tight_retract sig tau).
  Notation "'f'" := (tretract_f inj). Notation "'g'" := (tretract_g inj).

  Lemma map_map_app_eq_None_None (ss1 ss2 : list sig) (t1 t2 : tau) (ts1 ts2 : list tau) :
    g t1 = None -> g t2 = None ->
    map f ss1 ++ [t1] ++ ts1 = map f ss2 ++ [t2] ++ ts2 ->
    map f ss1 = map f ss2 /\ t1 = t2 /\ ts1 = ts2.
  Proof.
    intros H1 H2 H. induction (doubleListInduction ss1 ss2); cbn in *.
    - now inv H.
    - exfalso. inv H. clear H2 ys d IHd. enough (g (f y) = Some y) by congruence. apply tretract_g_adjoint.
    - exfalso. inv H. clear H1 xs d IHd. enough (g (f x) = Some x) by congruence. apply tretract_g_adjoint.
    - inv H.
      enough (map f xs = map f ys /\ t1 = t2 /\ ts1 = ts2) as (HE1&HE2).
      { split; now f_equal. }
      now apply IHd1.
  Qed.

  Lemma map_map_app_eq (ss1 ss2 : list sig) (ts : list tau) :
    map f ss1 = map f ss2 ++ ts ->
    exists ss3, map f ss1 = map f ss2 ++ map f ss3.
  Proof.
    revert ss2 ts. induction ss1; intros ss2 ts H; cbn in *.
    - symmetry in H. apply appendNil in H as (H&->). apply map_eq_nil in H as ->. exists nil. reflexivity.
    - destruct ss2; cbn in *.
      + destruct ts.
        * congruence.
        * exists (a :: ss1). reflexivity.
      + inv H. specialize (IHss1 _ _ H2) as (ss3&IH). eexists. f_equal. rewrite IH. f_equal.
  Qed.

  Lemma map_app_eq_nil_None (ss1 ss2 : list sig) (t : tau) (ts : list tau) :
    g t = None -> map f ss1 <> map f ss2 ++ [t] ++ ts.
  Proof.
    intros H C.
    assert (forall x, x el (map f ss1) -> g x <> None) as Contra.
    {
      intros x (x'&Hx&_) % in_map_iff. symmetry in Hx. apply tretract_inv in Hx. congruence.
    }
    rewrite C in Contra. apply (Contra t); auto.
  Qed.

  Lemma encode_map_injective':
    forall (v1 v2 : X) (r1 r2 : list sig) (R1 R2 : list tau),
      map f (encode v1 ++ r1) ++ R1 = map f (encode v2 ++ r2) ++ R2 -> v1 = v2 /\ map f r1 ++ R1 = map f r2 ++ R2.
  Proof.
    intros. revert r1 r2 H.
    induction (doubleListInduction R1 R2); intros r1 r2 H; cbn in *.
    - rewrite !app_nil_r in H. apply map_injective in H. apply encode_injective in H. intuition. congruence. apply tretract_f_injective.
    - destruct (g y) eqn:E.
      + apply tretract_inv in E as ->.
        replace (f e :: ys) with (map f [e] ++ ys) in H by reflexivity.
        rewrite app_assoc in H. rewrite <- map_app in H. rewrite <- app_assoc in H.
        pose proof (IHd _ _ H) as (->&IH). rewrite !app_nil_r in *.
        rewrite map_app in IH. rewrite <- app_assoc in IH. auto.
      + rewrite !app_nil_r in *. exfalso. replace (y :: ys) with ([y] ++ ys) in H by reflexivity. eapply map_app_eq_nil_None; eauto.
    - destruct (g x) eqn:E.
      + apply tretract_inv in E as ->.
        replace (f e :: xs) with (map f [e] ++ xs) in H by reflexivity.
        rewrite app_assoc in H. rewrite <- map_app in H. rewrite <- app_assoc in H.
        pose proof (IHd _ _ H) as (->&IH). rewrite !app_nil_r in *.
        rewrite map_app in IH. rewrite <- app_assoc in IH. auto.
      + rewrite !app_nil_r in *. exfalso. replace (x :: xs) with ([x] ++ xs) in H by reflexivity. eapply map_app_eq_nil_None; eauto.
    - destruct (g x) eqn:E1, (g y) eqn:E2.
      + apply tretract_inv in E1 as ->. apply tretract_inv in E2 as ->.
        replace (f e  :: xs) with (map f [e ] ++ xs) in H by reflexivity.
        replace (f e0 :: ys) with (map f [e0] ++ ys) in H by reflexivity.
        rewrite app_assoc in H. rewrite <- map_app in H. rewrite <- app_assoc in H. symmetry in H.
        rewrite app_assoc in H. rewrite <- map_app in H. rewrite <- app_assoc in H. symmetry in H.
        pose proof (IHd1 _ _ H) as (->&IH). rewrite !map_app in IH. rewrite <- !app_assoc in IH. split; auto.
      + apply tretract_inv in E1 as ->.
        replace (f e  :: xs) with (map f [e ] ++ xs) in H by reflexivity.
        rewrite app_assoc in H. rewrite <- map_app in H. rewrite <- app_assoc in H.
        pose proof (IHd3 _ _ H) as (->&IH). rewrite !map_app in IH. rewrite <- !app_assoc in IH. split; auto.
      + apply tretract_inv in E2 as ->.
        replace (f e  :: ys) with (map f [e ] ++ ys) in H by reflexivity.
        rewrite app_assoc in H. rewrite <- map_app in H. rewrite <- app_assoc in H.
        pose proof (IHd2 _ _ H) as (->&IH). rewrite !map_app in IH. rewrite <- !app_assoc in IH. split; auto.
      + replace (x :: xs) with ([x] ++ xs) in H by reflexivity. replace (y :: ys) with ([y] ++ ys) in H by reflexivity.
        pose proof (map_map_app_eq_None_None E1 E2 H) as (L&->&->). apply map_injective in L. now apply encode_injective in L as (->&->).
        apply tretract_f_injective.
  Qed.


  Lemma encode_map_injective :
    forall (v1 v2 : X) (r1 r2 : list tau),
      map f (encode v1) ++ r1 = map f (encode v2) ++ r2 -> v1 = v2 /\ r1 = r2.
  Proof.
    intros. pose proof (@encode_map_injective' v1 v2 nil nil r1 r2) as L. cbn in L. rewrite !app_nil_r in L. auto.
  Qed.

  Instance Encode_Map : codeable tau X.
  Proof.
    apply mk_codeable with (encode := fun x => map f (encode (codeable := code_sig) x)).
    now apply encode_map_injective.
  Defined.
  
End Encode_Map.


(* TODO: Injectivity of the X coding is enough. *)
Section Stop.

  Variable X : Type.
  Variable sig : finType.
  (*
  Variable enc : encoding_function sig X.
  Hypothesis enc_injective : forall x y : X, enc x = enc y -> x = y.
  *)
  Hypothesis (code_X : codeable sig X).

  Definition encode_stop (x : X) : list (option sig) := encode (codeable := Encode_Map code_X (option_inj _)) x ++ [None].

  Lemma encode_stop_injective :
    forall (v1 v2 : X) (r1 r2 : list finType_CS),
      encode_stop v1 ++ r1 = encode_stop v2 ++ r2 -> v1 = v2 /\ r1 = r2.
  Proof.
    intros. unfold encode_stop in H. cbn in *. rewrite <- !app_assoc in H.
    apply (encode_injective (codeable := Encode_Map code_X (option_inj _))) in H as [H1 H2]. now (inv H1; inv H2).
  Qed.
  
  Instance Encode_Stop : codeable (FinType (EqType (option sig))) X := mk_codeable encode_stop_injective.
  
End Stop.


Section Encode_Sum.
  Variable (X Y : Type).
  Variable (sig tau : finType).
  Hypothesis (code_X : codeable sig X) (code_Y : codeable tau Y).

  Definition retract_l_l := tretract_compose (inl_inj sig tau) (inl_inj _ bool).
  Definition retract_l_r := tretract_compose (inr_inj sig tau) (inl_inj _ bool).

  Definition encode_sum (a : X + Y) : list (sig + tau + bool) :=
    match a with
    | inl x => inr true  :: encode (codeable := Encode_Map code_X retract_l_l) x
    | inr y => inr false :: encode (codeable := Encode_Map code_Y retract_l_r) y
    end.

  Lemma encode_sum_injective :
    forall (v1 v2 : X + Y) (r1 r2 : list (sig + tau + bool)),
      encode_sum v1 ++ r1 = encode_sum v2 ++ r2 -> v1 = v2 /\ r1 = r2.
  Proof.
    intros [x1|y1] [x2|y2] r1 r2; cbn; intros H; inv H.
    - now pose proof (@encode_map_injective _ sig _ code_X retract_l_l x1 x2 r1 r2 H1) as (->&->).
    - now pose proof (@encode_map_injective _ tau _ code_Y retract_l_r y1 y2 r1 r2 H1) as (->&->).
  Qed.

  Instance Encode_Sum : codeable (FinType (EqType (sig + tau + bool))) (X + Y) := mk_codeable encode_sum_injective.
End Encode_Sum.


Section Encode_List.
  Variable sig: finType.
  Variable (X : Type) (code_X : codeable sig X).

  Fixpoint encode_list (xs : list X) : list (sig + bool) :=
    match xs with
    | nil => [inr false]
    | x :: xs' => inr true :: encode (codeable := Encode_Map code_X (inl_inj _ _)) x ++ encode_list xs'
    end.

  Lemma encode_injective_list :
    forall (v1 v2 : list X) (r1 r2 : list (sig + bool)), encode_list v1 ++ r1 = encode_list v2 ++ r2 -> v1 = v2 /\ r1 = r2.
  Proof.
    intros xs. induction xs as [ | x xs IH]; intros y2 r1 r2 H; cbn in *.
    + destruct y2; cbn in *; try congruence; cbn in *; try now inv H.
    + destruct y2 as [ | y ys]; cbn in *; auto.
      * congruence.
      * inv H. rewrite <- !app_assoc in H1.
        pose proof (@encode_map_injective _ sig _ code_X (inl_inj sig bool) x y _ _ H1) as (->&L).
        now specialize (IH _ _ _ L) as (->&->).
  Qed.

  Instance Encode_List : codeable (FinType (EqType (sig + bool)))%type (list X) := mk_codeable encode_injective_list.

End Encode_List.


Section Encode_Pair.
  Variable (X Y : Type) (sig : finType).
  Hypothesis (code_X : codeable sig X) (code_Y : codeable sig Y).

  Definition encode_pair (v : X * Y) : list sig.
  Proof. destruct v as (a,b). apply (encode (codeable := code_X) a ++ encode (codeable := code_Y) b). Defined.

  Lemma encode_pair_injective :
    forall (v1 v2 : X * Y) (r1 r2 : list sig), encode_pair v1 ++ r1 = encode_pair v2 ++ r2 -> v1 = v2 /\ r1 = r2.
  Proof.
    intros (a1, b1) (a2, b2) r1 r2 H. unfold encode_pair in *. rewrite <- !app_assoc in H.
    apply encode_injective in H as (->&H). apply encode_injective in H as (->&->). auto.
  Qed.

  Instance Encode_Pair : codeable sig (X * Y) := mk_codeable encode_pair_injective.
End Encode_Pair.

Section Encode_Pair'.
  Variable (X Y : Type) (sig tau : finType).

  Hypothesis (code_X : codeable sig X) (code_Y : codeable tau Y).

  Instance Encode_Pair' : codeable (FinType (EqType (sig + tau)%type)) (X * Y).
  Proof.
    apply Encode_Pair.
    - apply (Encode_Map _ (inl_inj _ _)).
    - apply (Encode_Map _ (inr_inj _ _)).
  Defined.
      
End Encode_Pair'.


Section Encode_Unit.
  Definition encode_unit : encoding_function (FinType (EqType Empty_set)) unit := fun _ : unit => [].

  Lemma encode_unit_injective :
    forall (v1 v2 : unit) (r1 r2 : list (FinType (EqType Empty_set))), encode_unit v1 ++ r1 = encode_unit v2 ++ r2 -> v1 = v2 /\ r1 = r2.
  Proof. intros () () r1 r2. auto. Qed.

  Instance Encode_Unit : codeable (FinType (EqType Empty_set)) unit := mk_codeable encode_unit_injective.

End Encode_Unit.

Section Encode_Empt.
  Definition encode_empty : encoding_function (FinType (EqType Empty_set)) Empty_set := fun devil => match devil with end.

  Lemma encode_empty_injective :
    forall (v1 v2 : Empty_set) (r1 r2 : list (FinType (EqType Empty_set))), encode_empty v1 ++ r1 = encode_empty v2 ++ r2 -> v1 = v2 /\ r1 = r2.
  Proof. intros v1. destruct v1. Qed.
    
  Instance I_empty : codeable (FinType (EqType Empty_set)) Empty_set := mk_codeable encode_empty_injective.
End Encode_Empt.

Class Cast (X Y : Type) : Type :=
  mk_cast
    {
      cast_f : Y -> X;
      cast_injective : forall x1 x2, cast_f x1 = cast_f x2 -> x1 = x2;
    }.

Instance cast_reflexive (X : Type) : Cast X X.
Proof. hnf. apply mk_cast with (cast_f := id). firstorder. Defined.

Instance cast_transitive (X Y Z : Type) : Cast X Y -> Cast Y Z -> Cast X Z.
Proof.
  intros C1 C2. apply mk_cast with (cast_f := fun z => cast_f (Cast := C1) (cast_f (Cast := C2) z)).
  firstorder. now do 2 apply cast_injective.
Defined.

Section Encode_Cast.
  Variable sig : finType.
  Variable (X Y : Type) (castXY : Cast X Y) (e : codeable sig X).

  Lemma Encode_Cast : codeable sig Y.
  Proof.
    esplit with (encode := fun y => encode (cast_f y)).
    - intros v1 v2 r1 r2 H. apply encode_injective in H as (H&->). split; auto. now apply cast_injective in H.
  Defined.

End Encode_Cast.

Instance cast_option (X : Type) : Cast (X + unit) (option X).
Proof.
  split with (cast_f := fun p => match p with Some x => inl x | None => inr tt end).
  - intros [x|  ] [y| ] H; auto; congruence.
Defined.

Instance Encode_Option (X : Type) (sig : finType) : codeable sig X -> codeable (FinType (EqType (sig + Empty_set + bool))) (option X).
Proof.
  intros H. eapply Encode_Cast. eapply cast_option.
  eapply Encode_Sum.
  - apply H.
  - apply Encode_Unit.
Defined.

Lemma repeat_surjective (X : Type) (x : X) (n m : nat) :
  repeat x n = repeat x m -> n = m.
Proof.
  revert m. induction n; intros m H.
  - destruct m; cbn in *; congruence.
  - cbn in *. destruct m; cbn in *. congruence. f_equal. apply IHn. congruence.
Qed.

Instance cast_nat : Cast (list unit) nat.
Proof.
  split with (cast_f := @List.repeat unit tt).
  - apply repeat_surjective.
Defined.

Instance Encode_Nat : codeable Bool_Fin nat.
Proof.
  eapply Encode_Map.
  - eapply Encode_Cast. Focus 2. apply Encode_List. apply Encode_Unit. apply cast_nat.
  - cbn. apply empty_left_inj.
Defined.

Section Encode_Fin'.
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
    split with (cast_f := fin_to_nat).
    apply fin_to_nat_injective.
  Defined.

  Instance Encode_Fin' : codeable Bool_Fin (Fin.t n).
  Proof. eapply Encode_Cast. eapply cast_Fin. auto. Defined.
End Encode_Fin'.

(** Test Playground *)

(*
Compute encode false.
Compute encode true.
Compute encode 42.

Compute encode
        (codeable := Encode_Pair' (Encode_List (Encode_Unit)) _)
        ([tt;tt;tt], true).

Compute encode
        (codeable := Encode_Pair (Encode_Unit) (Encode_Unit))
        (tt, tt).

Print FinType.
Search finTypeC Fin.t.
Search Fin.t FinType.

(* TODO: How to instanciate Fin.t to finType? *)
(*
Check Encode_Fin (FinType (Fin_finType 10)).
*)
Check Encode_Fin' 10.

Compute
  encode
  (codeable := Encode_Fin' 10)
  (Fin.FS (Fin.FS (Fin.FS (Fin.F1)))).

Check Encode_Pair' (Encode_List (Encode_Unit)) Encode_Unit.

Compute encode
        (codeable := Encode_Pair' (Encode_List (Encode_Unit)) Encode_Unit)
        ([tt;tt;tt], tt).

*)