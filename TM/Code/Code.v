Require Import Prelim.

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

Section Encode_Fin.
  Variable X : finType.

  Lemma encode_fin_injective :
    forall (v1 v2 : X) (r1 r2 : list X),
      [v1] ++ r1 = [v2] ++ r2 -> v1 = v2 /\ r1 = r2.
  Proof. firstorder; now inv H. Qed.

  Instance Encode_Fin : codeable X X.
  Proof. apply mk_codeable with (encode := fun x => [x]). apply encode_fin_injective. Defined.

End Encode_Fin.


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


Require Export Injection.

Section Remap.

  Variable (X : Type).
  Variable (sig tau : Type).

  Fixpoint remap (g : tau -> option sig) (str : list tau) : list sig * list tau :=
    match str with
    | nil => (nil, nil)
    | y :: str' => match g y with
                  | Some x => let (res1, res2) := remap g str' in (x :: res1, res2)
                  | None => ([], str)
                  end
    end.

  Hypothesis (inj : injection_fun sig tau).
  Notation "'f'" := (inj_f inj). Notation "'g'" := (inj_g inj).

  Lemma map_app_remap :
    forall (str : list sig) (R : list tau),
      let (str', r2) := remap g (map f str ++ R) in
      { r1 : list sig | R = map f r1 ++ r2 /\ str' = str ++ r1}.
  Proof.
    intros str. induction str; intros; cbn in *.
    - induction R; cbn.
      + exists []. cbn. tauto.
      + destruct (g a) eqn:E; cbn.
        * destruct (remap g R). destruct IHR as (r1&->&->).
          eexists. split; eauto. cbn. f_equal. now apply inj_inv.
        * eexists. split; eauto. cbn. reflexivity.
    - rewrite inj_g_adjoint.
      specialize (IHstr R). destruct (remap g (map f str ++ R)). destruct IHstr as (r1&->&->).
      eexists. split; eauto. 
  Qed.
End Remap.

Section Map.
  Variable (X : Type).
  Variable (sig tau : finType).
  Hypothesis (code_sig : codeable sig X).
  Hypothesis (inj : injection_fun sig tau).
  Notation "'f'" := (inj_f inj). Notation "'g'" := (inj_g inj).


  Lemma encode_map_injective :
    forall (v1 v2 : X) (r1 r2 : list tau),
      map f (encode v1) ++ r1 = map f (encode v2) ++ r2 -> v1 = v2 /\ r1 = r2.
  Proof.
    intros.
    pose proof (map_app_remap inj (encode v1) r1) as L1.
    pose proof (map_app_remap inj (encode v2) r2) as L2.
    destruct (remap g (map f (encode v1) ++ r1)). destruct (remap g (map f (encode v2) ++ r2)).
    destruct L1 as (R1&L1&L1'). destruct L2 as (R2&L2&L2').
    subst.
  Admitted.
    
  Instance Encode_Map : codeable tau X.
  Proof.
    apply mk_codeable with (encode := fun x => map f (encode (codeable := code_sig) x)).
    now apply encode_map_injective.
  Defined.
  
End Map.


(* TODO: Injectivity of the X coding should be enough to show that. *)
Section Stop.

  Variable X : Type.
  Variable sig : finType.
  (*
  Variable enc : encoding_function sig X.
  Hypothesis enc_injective : forall x y : X, enc x = enc y -> x = y.
  *)
  Hypothesis (code_X : codeable sig X).

  Definition option_inj : injection_fun sig (option sig).
  Proof.
    apply Build_injection_fun with (inj_f := Some) (inj_g := id). firstorder.
  Defined.
  
  Definition encode_stop (x : X) : list (option sig) := encode (codeable := Encode_Map code_X option_inj) x ++ [None].

  Lemma encode_stop_injective :
    forall (v1 v2 : X) (r1 r2 : list finType_CS),
      encode_stop v1 ++ r1 = encode_stop v2 ++ r2 -> v1 = v2 /\ r1 = r2.
  Proof.
    intros. unfold encode_stop in H. cbn in *. rewrite <- !app_assoc in H.
    apply (encode_injective (codeable := Encode_Map code_X option_inj)) in H as [H1 H2]. now (inv H1; inv H2).
  Qed.
  
  Instance Encode_Stop : codeable (FinType (EqType (option sig))) X.
  Proof.
    apply mk_codeable with (encode := encode_stop). now apply encode_stop_injective.
  Qed.
  
End Stop.



Section Encode_Bool.
  Lemma encode_bool_injective : forall (v1 v2 : bool) r1 r2, [v1] ++ r1 = [v2] ++ r2 -> v1 = v2 /\ r1 = r2.
  Proof. intros v1 v2 r1 r2 H. now inv H. Qed.
  Instance Encode_Bool : codeable (FinType (EqType bool)) bool := mk_codeable encode_bool_injective.
End Encode_Bool.


Section Encode_Sum.
  Variable (X Y : Type).
  Variable (sig tau : finType).
  Hypothesis (code_X : codeable sig X) (code_Y : codeable tau Y).

  
  Definition encode_sum (a : X + Y) : list (sig + tau + bool) :=
    match a with
    | inl x => inr true  :: map (fun sig' => inl (inl sig')) (encode (codeable := code_X) x) ++ [inr  true]
    | inr y => inr false :: map (fun tau' => inl (inr tau')) (encode (codeable := code_Y) y) ++ [inr false]
    end.

  Fixpoint undo_encode_sum_X (str : list (sig + tau + bool)) : option (list sig) * list (sig + tau + bool) :=
    match str with
    | nil => (None, str)
    | inl (inl x) :: rest =>
      match undo_encode_sum_X rest with
      | (Some x', rest') => (Some (x :: x'), rest')
      | (None,    rest') => (Some [x],       rest')
      end
    | inl (inr x) :: rest => (None, str)
    | inr true  :: rest => (Some [], rest)
    | inr false :: rest => (None,    str)
    end.
      
  Fixpoint undo_encode_sum_Y (str : list (sig + tau + bool)) : option (list tau) * list (sig + tau + bool). Admitted.

  Definition undo_encode_sum (str : list (sig + tau + bool)) : option (list (sig + tau)) * list (sig + tau + bool) :=
    match str with
    | inr true  :: str => match undo_encode_sum_X str with
                         | (Some x, rest') => (Some (map inl x), rest')
                         | (None,   rest') => (None, rest')
                         end
    | inr false :: str => match undo_encode_sum_Y str with
                         | (Some y, rest') => (Some (map inr y), rest')
                         | (None,   rest') => (None, rest')
                         end
    | _ => (None, str)
    end.

  (*
  Lemma encode_sum_inv (v : X + Y) (r1 r2 : list (sig + tau + bool)) :
    encode_sum v = r1 -> undo_encode_sum (r1 ++ r2) = (Some (map inl r1), r2).
*)
  

  Lemma encode_sum_injective :
    forall (v1 v2 : X + Y) (r1 r2 : list (sig + tau + bool)),
      encode_sum v1 ++ r1 = encode_sum v2 ++ r2 -> v1 = v2 /\ r1 = r2.
  Proof.
    (*
    intros [v1|v1] [v2|v2] r1 r2; intros H1; cbn in *; inv H1.
    - 

      remember (encode v1) as e1. remember (encode v2) as e2.
      revert r1 r2 H0.
      induction e1; intros; cbn in *.
      + destruct e2; cbn in *.
        * split; auto. f_equal. eapply encode_injective'. congruence.
        * split.
          -- f_equal. eapply encode_injective'.
*)
  Admitted.

  Instance Encode_Sum : codeable (FinType (EqType (sig + tau + bool))) (X + Y) := mk_codeable encode_sum_injective.
End Encode_Sum.


Section Encode_List.
  Variable sigma : finType.
  Variable (X : Type) (code_X : codeable sigma X).

  Fixpoint encode_list (xs : list X) : list (sigma + bool) :=
    match xs with
    | nil => [inr false]
    | x :: xs' => inr true :: map inl (encode x (codeable := code_X)) ++ encode_list xs'
    end.

  Lemma encode_injective_list :
    forall (v1 v2 : list X) (r1 r2 : list (sigma + bool)), encode_list v1 ++ r1 = encode_list v2 ++ r2 -> v1 = v2 /\ r1 = r2.
  Proof.
    intros xs. induction xs as [ | x xs IH]; intros y2 r1 r2 H; cbn in *.
    + destruct y2; cbn in *; try congruence; cbn in *; try now inv H.
    + destruct y2 as [ | y ys]; cbn in *; auto.
      * congruence.
      * inv H.
        (*
        apply encode_injective in H1.
        rewrite <- !app_assoc in H1. apply encode_injective in H1. destruct H1 as (->&H1). apply IH in H1. intuition; congruence.
         *)
  Admitted.

  Instance Encode_List : codeable (FinType (EqType (sigma + bool)))%type (list X) := mk_codeable encode_injective_list.

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

  Definition inl_inj : injection_fun sig (sig + tau).
  Proof.
    apply Build_injection_fun with (inj_f := inl) (inj_g := fun z => match z with inl x => Some x | _ => None end).
    firstorder; destruct y; inv H; firstorder.
  Defined.

  Definition inr_inj : injection_fun tau (sig + tau).
  Proof.
    apply Build_injection_fun with (inj_f := inr) (inj_g := fun z => match z with inr x => Some x | _ => None end).
    firstorder; destruct y; inv H; firstorder.
  Defined.

  Hypothesis (code_X : codeable sig X) (code_Y : codeable tau Y).

  Instance Encode_Pair' : codeable (FinType (EqType (sig + tau)%type)) (X * Y).
  Proof.
    apply Encode_Pair.
    - apply (Encode_Map _ inl_inj).
    - apply (Encode_Map _ inr_inj).
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

Instance cast_bool : Cast (unit + unit) bool.
Proof.
  split with (cast_f := fun (b : bool) => if b then inl tt else inr tt).
  - intros x1 x2 H. destruct x1, x2; auto; congruence.
Defined.

Instance I_bool : codeable (FinType (EqType bool)) bool.
Proof. eapply Encode_Cast. shelve. eapply Encode_Bool. Unshelve. auto. Defined.

Instance cast_option (X : Type) : Cast (X + unit) (option X).
Proof.
  split with (cast_f := fun p => match p with Some x => inl x | None => inr tt end).
  - intros [x|  ] [y| ] H; auto; congruence.
Defined.

Instance I_option (X : Type) (sig : finType) : codeable sig X -> codeable (FinType (EqType (sig + Empty_set + bool))) (option X).
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

Instance I_nat : codeable (FinType (EqType (Empty_set + bool))) nat.
Proof. eapply Encode_Cast. apply cast_nat. apply Encode_List. apply Encode_Unit. Defined.

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

  Instance Encode_Fin' : codeable (FinType (EqType (Empty_set + bool))) (Fin.t n).
  Proof. eapply Encode_Cast. eapply cast_Fin. auto. Defined.
End Encode_Fin'.

(** Test Playground *)

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
  (codeable := Encode_Fin 10)
  (Fin.FS (Fin.FS (Fin.FS (Fin.F1)))).

Check Encode_Pair' (Encode_List (Encode_Unit)) Encode_Unit.

Compute encode
        (codeable := Encode_Pair' (Encode_List (Encode_Unit)) Encode_Unit)
        ([tt;tt;tt], tt).

Check Encode_Bool.

Compute encode true.

Compute encode
        (codeable := Encode_Pair' (Encode_List (Encode_Unit)) _)
        ([tt;tt;tt], true).