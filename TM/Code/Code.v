Require Import TM.Prelim.
Require Import Coq.Lists.List.

(** * Codable Class **)


Section Codable.

  Context (sig: finType).
  Variable (X: Type).

  Class codable :=
    mk_codable
      {
        encode :> X -> list sig
      }.

  Hypothesis codable_X : codable.

End Codable.
Arguments encode { sig } { X } { _ }.

Coercion encode : codable >-> Funclass.


Instance Encode_unit : codable (FinType(EqType(Empty_set))) unit :=
  {|
    encode x := nil
  |}.

Instance Encode_bool : codable (FinType(EqType(bool))) bool:=
  {|
    encode x := [x]
  |}.

Instance Encode_Fin n : codable (FinType(EqType(Fin.t n))) (Fin.t n):=
  {|
    encode i := [i]
  |}.
  

Compute encode true.
(* This works thanks to the coercion above *)
Compute Encode_bool true.
Compute encode tt.
Check encode Fin0.
Compute encode Fin0 : list (Fin.t 10).


(** We restrict mapping of encodings to injective/retractable mappings. *)
Section Encode_map.
  Variable (X : Type).
  Variable (sig tau : finType).
  Hypothesis (code_sig : codable sig X).

  Variable inj : Retract sig tau.

  Global Instance Encode_map : codable tau X | 100 :=
    {
      encode x := map Retr_f (encode x);
    }.
  
End Encode_map.



(** Builds simple retract functions like [sigSum -> option sigX] in the form
[fun x => match x with constructor_name y => Some y | _ => None] *)

Ltac build_simple_retract_g :=
  match goal with
  | [ |- ?Y -> option ?X ] =>
    idtac "Retract function" X Y;
    let x := fresh "x" in
    intros x; destruct x; intros; try solve [now left]; right
  end.


Ltac build_simple_retract :=
  match goal with
  | [ |- Retract ?X ?Y ] =>
    idtac "Retract from" X "to" Y;
    let x := fresh "x" in
    let y := fresh "y" in
    let f := (eval simpl in (ltac:(intros x; now constructor) : X -> Y)) in
    idtac "f:" f;
    let g := (eval simpl in (ltac:(build_simple_retract_g) : Y -> option X)) in
    idtac "g:" g;
    apply Build_Retract with (Retr_f := f) (Retr_g := g);
    hnf; intros x y; split;
    [ destruct y; congruence
    | now intros ->
    ]
  end
.

Ltac build_eq_dec :=
  let x := fresh "x" in
  let y := fresh "y" in
  intros x y; hnf; decide equality; apply eqType_dec.


Lemma countMap_injective (X Y : eqType) (x : X) (A : list X) (f : X -> Y) :
  (forall x y, f x = f y -> x = y) ->
  BasicDefinitions.count (map f A) (f x) = BasicDefinitions.count A x.
Proof.
  intros HInj. revert x. induction A as [ | a A IH]; intros; cbn in *; auto.
  decide (f x = f a) as [ -> % HInj | He].
  - have (a=a).
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
  Variable (sigX sigY : finType).
  Hypothesis (cX : codable sigX X) (cY : codable sigY Y).

  Inductive sigSum : Type :=
  | sigSum_X (s : sigX)
  | sigSum_Y (s : sigY)
  | sigSum_inl
  | sigSum_inr
  .

  Global Instance Retract_sigSum_X : Retract sigX sigSum := ltac:(build_simple_retract).
  Global Instance Retract_sigSum_Y : Retract sigY sigSum := ltac:(build_simple_retract).
  Global Instance sigSum_dec : eq_dec sigSum := ltac:(build_eq_dec).
  Global Instance sigSum_fin : finTypeC (EqType sigSum).
  Proof.
    split with (enum := sigSum_inl :: sigSum_inr :: map sigSum_X enum ++ map sigSum_Y enum). intros [x|y| | ]; cbn; f_equal.
    - rewrite <- !countSplit.
      erewrite countMap_injective. 2: eapply (retract_f_injective) with (I := Retract_sigSum_X).
      rewrite enum_ok.
      rewrite countMap_zero. omega. congruence.
    - rewrite <- !countSplit.
      erewrite countMap_injective. 2: eapply (retract_f_injective) with (I := Retract_sigSum_Y).
      rewrite enum_ok.
      rewrite countMap_zero. omega. congruence.
    - rewrite <- !countSplit. rewrite !countMap_zero. omega. all: congruence.
    - rewrite <- !countSplit. rewrite !countMap_zero. omega. all: congruence.
  Qed.

  
  Global Instance Encode_sum : codable (FinType(EqType(sigSum))) (X+Y) :=
    {|
      encode s := match s with
                  | inl x => sigSum_inl :: encode x
                  | inr y => sigSum_inr :: encode y
                  end
    |}.
  
End Encode_sum.

Arguments sigSum_inl {sigX sigY}. Arguments sigSum_inr {sigX sigY}. Arguments sigSum_X {sigX sigY}. Arguments sigSum_Y {sigX sigY}.

Compute Encode_sum Encode_bool Encode_unit (inl true).


(** If [X] is encodable over [sigX] and [Y] over [sigY]. *)
Section Encode_pair.
  Variable (sig tau: finType) (X Y: Type) (cX : codable sig X) (cY : codable tau Y).

  Global Instance Encode_pair : codable (FinType (EqType (sig+tau))) (X*Y) :=
    {|
      encode '(x,y) := encode x ++ encode y;
    |}.

End Encode_pair.

Section Encode_option.
  Variable (sigX: finType) (X: Type) (cX : codable sigX X).

  Inductive sigOption : Type :=
  | sigOption_X (s : sigX)
  | sigOption_None
  | sigOption_Some
  .

  Global Instance Retract_sigOption_X : Retract sigX sigOption := ltac:(build_simple_retract).
  Global Instance sigOption_dec : eq_dec sigOption := ltac:(build_eq_dec).
  Global Instance sigOption_fin : finTypeC (EqType sigOption).
  Proof.
    split with (enum := sigOption_Some :: sigOption_None :: map sigOption_X enum).
    intros [x| | ]; cbn; f_equal.
    - rewrite countMap_injective. 2: apply retract_f_injective with (I := Retract_sigOption_X).
      now apply enum_ok.
    - rewrite countMap_zero. omega. congruence.
    - rewrite countMap_zero. omega. congruence.
  Qed.


  Global Instance Encode_option : codable (FinType(EqType sigOption)) (option X) :=
    {|
      encode o := match o with
                  | None => [sigOption_None]
                  | Some x => sigOption_Some :: encode x
                  end;
    |}.

End Encode_option.

Arguments sigOption_Some {sigX}. Arguments sigOption_None {sigX}. Arguments sigOption_X {sigX}.

Compute Encode_option Encode_bool None.
Compute Encode_option Encode_bool (Some false).



Section Encode_list.
  Variable sigX: finType.
  Variable (X : Type) (cX : codable sigX X).

  Inductive sigList : Type :=
  | sigList_X (s : sigX)
  | sigList_nil
  | sigList_cons
  .
  Global Instance Retract_sigList_X : Retract sigX sigList := ltac:(build_simple_retract).
  Global Instance sigList_dec : eq_dec sigList := ltac:(build_eq_dec).
  Global Instance sigList_fin : finTypeC (EqType sigList).
  Proof.
    split with (enum := sigList_nil :: sigList_cons :: map sigList_X enum).
    intros [x| | ]; cbn; f_equal.
    - rewrite countMap_injective. 2: apply retract_f_injective with (I := Retract_sigList_X).
      now apply enum_ok.
    - rewrite countMap_zero. omega. congruence.
    - rewrite countMap_zero. omega. congruence.
  Qed.


  Fixpoint encode_list (xs : list X) : list sigList :=
    match xs with
    | nil => [sigList_nil]
    | x :: xs' => sigList_cons :: encode x ++ encode_list xs'
    end.

  Global Instance Encode_list : codable (FinType(EqType sigList)) (list X) :=
    {|
      encode := encode_list;
    |}.

End Encode_list.

Arguments sigList_nil {sigX}. Arguments sigList_cons {sigX}. Arguments sigList_X {sigX}.

Compute Encode_list Encode_bool (nil).
Eval cbn in Encode_list Encode_bool (true :: _).
Compute Encode_list Encode_bool (true :: false :: nil).


Section Encode_nat.

  Inductive sigNat : Type :=
  | sigNat_O
  | sigNat_S.

  Instance sigNat_eq : eq_dec sigNat.
  Proof. unfold dec. decide equality. Defined.

  Instance sigNat_fin : finTypeC (EqType sigNat).
  Proof. split with (enum := [sigNat_O; sigNat_S]). intros [ | ]; cbn; reflexivity. Qed.

  Global Instance Encode_nat : codable (FinType(EqType sigNat)) nat :=
    {|
      encode n := repeat sigNat_S n ++ [sigNat_O];
    |}.

End Encode_nat.



    
(** Test Playground *)

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