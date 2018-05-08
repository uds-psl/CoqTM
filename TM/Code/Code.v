Require Import TM.Prelim.
Require Import Coq.Lists.List.

(** * Codable Class **)


Generalizable Variables X Y Z sigma sig tau.


Section Codable.

  Variable (sig: finType).
  Variable (X: Type).

  Definition encoding_function := X -> list sig.

  Class codable :=
    mk_codable
      {
        encode : encoding_function;
      }.

  Hypothesis codable_X : codable.

End Codable.
Arguments encode { sig } { X } { _ }.


Section Encode_Finite.
  (* HACK: [encode true] would not work if we just define [Variable X:finType] *)
  Context `{fX: finTypeC X}.

  Global Instance Encode_Finite : codable (FinType X) (FinType X) :=
    {
      encode := fun x => [x];
    }.

End Encode_Finite.

(*
Global Instance Encode_Bool : codable (FinType (EqType bool)) bool := Encode_Finite (FinType (EqType bool)).
*)

Compute encode true.
Compute encode (Fin10: Fin.t 11).


Section Encode_Map.
  Variable (X : Type).
  Variable (sig tau : finType).
  Hypothesis (code_sig : codable sig X).
  Variable (f : sig -> tau).

  Global Instance Encode_Map : codable tau X :=
    {
      encode x := map f (encode x);
    }.
  
End Encode_Map.


Section Encode_Sum.
  Variable (X Y : Type).
  Variable (sig tau : finType).
  Hypothesis (cX : codable sig X) (cY : codable tau Y).

  Global Instance Encode_Sum : codable (FinType(EqType(bool+(sig+tau)))) (X+Y) :=
    {
      encode s := match s with
                  | inl x => inl true :: Encode_Map

  


  Global Instance retract_r_l : TRetract sig (bool + (sig + tau)) := Build_TRetract (tretract_compose _ _).
  Global Instance retract_r_r : TRetract tau (bool + (sig + tau)) := Build_TRetract (tretract_compose _ _).

  Definition encode_sum (a : X + Y) : list (bool + (sig + tau)) :=
    match a with
    | inl x => inl true  :: encode x
    | inr y => inl false :: encode y
    end.

  Lemma encode_sum_injective :
    forall (v1 v2 : X + Y) (r1 r2 : list (bool + (sig + tau))),
      encode_sum v1 ++ r1 = encode_sum v2 ++ r2 -> v1 = v2 /\ r1 = r2.
  Proof.
    intros [x1|y1] [x2|y2] r1 r2; cbn; intros H; inv H.
    - eapply encode_map_injective in H1 as (->&->). tauto.
      apply retract_r_l.
    - eapply encode_map_injective in H1 as (->&->). tauto. apply retract_r_r.
  Qed.

  Global Instance Encode_Sum : codable (FinType (EqType (bool + (sig + tau)))) (X + Y) := mk_codable encode_sum_injective.
End Encode_Sum.


Section Encode_Pair.
  Variable (X Y : Type) (sig : finType).
  Hypothesis (code_X : codable sig X) (code_Y : codable sig Y).

  Definition encode_pair (v : X * Y) : list sig.
  Proof. destruct v as (a,b). apply (encode (codable := code_X) a ++ encode (codable := code_Y) b). Defined.

  Lemma encode_pair_injective :
    forall (v1 v2 : X * Y) (r1 r2 : list sig), encode_pair v1 ++ r1 = encode_pair v2 ++ r2 -> v1 = v2 /\ r1 = r2.
  Proof.
    intros (a1, b1) (a2, b2) r1 r2 H. unfold encode_pair in *. rewrite <- !app_assoc in H.
    apply encode_injective in H as (->&H). apply encode_injective in H as (->&->). auto.
  Qed.

  Global Instance Encode_Pair : codable sig (X * Y) := mk_codable encode_pair_injective.
End Encode_Pair.

Section Encode_Pair'.
  Variable (X Y : Type) (sig tau : finType).

  Hypothesis (code_X : codable sig X) (code_Y : codable tau Y).

  Global Instance Encode_Pair' : codable (FinType (EqType (sig + tau)%type)) (X * Y).
  Proof.
    apply Encode_Pair; apply (Encode_Map _ _).
  Defined.
      
End Encode_Pair'.


Section Encode_Unit.
  Definition encode_unit : encoding_function (FinType (EqType Empty_set)) unit := fun _ : unit => [].

  Lemma encode_unit_injective :
    forall (v1 v2 : unit) (r1 r2 : list (FinType (EqType Empty_set))), encode_unit v1 ++ r1 = encode_unit v2 ++ r2 -> v1 = v2 /\ r1 = r2.
  Proof. intros () () r1 r2. auto. Qed.

  Global Instance Encode_Unit : codable (FinType (EqType Empty_set)) unit := mk_codable encode_unit_injective.

End Encode_Unit.

Section Encode_Empt.
  Definition encode_empty : encoding_function (FinType (EqType Empty_set)) Empty_set := fun devil => match devil with end.

  Lemma encode_empty_injective :
    forall (v1 v2 : Empty_set) (r1 r2 : list (FinType (EqType Empty_set))), encode_empty v1 ++ r1 = encode_empty v2 ++ r2 -> v1 = v2 /\ r1 = r2.
  Proof. intros v1. destruct v1. Qed.
    
  Global Instance I_empty : codable (FinType (EqType Empty_set)) Empty_set := mk_codable encode_empty_injective.
End Encode_Empt.

Section Encode_Cast.
  Variable sig : finType.
  Variable (X Y : Type) (f : Y -> X).
  Hypothesis (codeX : codable sig X).
  Hypothesis (inj : injective f).

  Lemma Encode_Cast : codable sig Y.
  Proof.
    esplit with (encode := fun y => encode (f y)).
    - intros v1 v2 r1 r2 H. apply encode_injective in H as (H&->). split; eauto.
  Defined.

End Encode_Cast.

Lemma Encode_Option' (X : Type) (sig : finType) : codable sig X -> codable (FinType (EqType (bool + (sig + Empty_set)))) (option X).
Proof.
  intros H. eapply Encode_Cast. eapply Encode_Sum.
  - apply H.
  - unfold finType_CS. apply Encode_Unit.
  - now auto_inj.
    (* eapply retract_injective. eapply tight_retract_strong.
    eapply inversion_retract. eapply inverse_option_unit. *)
Defined.

(* Eleminate the Empty_set from above *)
Global Instance Encode_Option (X : Type) (sig : finType) : codable sig X -> codable (FinType (EqType (bool + sig))) (option X).
Proof.
  intros H. eapply Encode_Map. eapply Encode_Option'; auto. eapply inversion_retract. 
  (* (* Just for cosmetics *) Unshelve. all: unfold finType_CS. 2-3: cbn; shelve. Show Existentials. *)
  eapply inverse_sum.
  - auto_inj. (* eapply inverse_sum_Empty_set. *)
  - auto_inj. (* apply inverse_id. *)
Defined.


Section Encode_List.
  Variable sig: finType.
  Variable (X : Type) (code_X : codable sig X).

  Fixpoint encode_list (xs : list X) : list (bool + sig) :=
    match xs with
    | nil => [inl false]
    | x :: xs' => inl true :: encode (codable := Encode_Map code_X (@retract_inr _ _)) x ++ encode_list xs'
    end.

  Lemma encode_injective_list :
    forall (v1 v2 : list X) (r1 r2 : list (bool + sig)), encode_list v1 ++ r1 = encode_list v2 ++ r2 -> v1 = v2 /\ r1 = r2.
  Proof.
    intros xs. induction xs as [ | x xs IH]; intros y2 r1 r2 H; cbn in *.
    + destruct y2; cbn in *; try congruence; cbn in *; try now inv H.
    + destruct y2 as [ | y ys]; cbn in *; auto.
      * congruence.
      * inv H. rewrite <- !app_assoc in H1.
        eapply encode_map_injective in H1 as (->&H1). now specialize (IH _ _ _ H1) as (->&->). apply retract_inr.
  Qed.

  Global Instance Encode_List : codable (FinType (EqType (bool + sig))) (list X) := mk_codable encode_injective_list.

End Encode_List.





Section Encode_Nat.
  Instance cast_nat : injective (fun n => @List.repeat unit tt n).
  Proof.
    hnf. intros m n. revert m. induction n; intros m H.
    - destruct m; cbn in *; congruence.
    - cbn in *. destruct m; cbn in *. congruence. f_equal. apply IHn. congruence.
  Qed.

  Global Instance Encode_Nat : codable (FinType (EqType bool)) nat.
  Proof.
    eapply Encode_Map.
    - eapply Encode_Cast.
      + apply Encode_List. apply Encode_Unit.
      + apply cast_nat; auto_inj.
    - auto_inj.
  Defined.
End Encode_Nat.


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
  
  Local Instance cast_Fin : injective fin_to_nat.
  Proof.
    hnf. intros x1 x2. apply fin_to_nat_injective.
  Qed.

  Local Instance Encode_Fin' : codable (FinType (EqType bool)) (Fin.t n).
  Proof.
    eapply Encode_Cast; [ | eapply cast_Fin ]. apply Encode_Nat.
  Defined.
  
End Encode_Fin'.

(** Test Playground *)

(*
Compute encode (Some true).
Compute encode None.


Compute encode false.
Compute encode true.

Compute encode 42.

Compute encode (tt, tt).

Compute ([tt;tt;tt], true).

Print FinType.
Search finTypeC Fin.t.
Search Fin.t FinType.

Require Import TM.TM.
Check (FinType (EqType move)).

Check encode (X := list (FinType (EqType move))).
Compute encode (X := list (FinType (EqType move))) [L; N; R].

Compute encode (X := FinType (EqType (Fin.t 10))) (Fin.FS (Fin.FS (Fin.FS (Fin.F1)))).
Compute encode (codable := Encode_Fin' 10) (Fin.FS (Fin.FS (Fin.FS (Fin.F1)))).

Check Encode_Pair' (Encode_List (Encode_Unit)) Encode_Unit.

Compute encode ([tt;tt;tt], tt).

Compute encode ([tt;tt;tt], tt, 42).


Compute encode (inl 42).
Compute encode (inr 42).
Compute encode (1, 2).
Compute encode [4;5].
Compute encode (Some 4) ++ encode (Some 5) ++ encode None.
*)